"""PayrollPath India - compact Telegram bot.
Every calculator replies with a table IMAGE + an EXCEL file (live formulas, Excel Table)."""
import asyncio, html, json, logging, math, os, re
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from io import BytesIO
from pathlib import Path
from urllib.parse import quote_plus

import httpx
from matplotlib.figure import Figure
from openpyxl import Workbook
from openpyxl.styles import Alignment, Font, PatternFill
from openpyxl.worksheet.table import Table, TableStyleInfo
from telegram import InlineKeyboardButton as Btn, InlineKeyboardMarkup as Kb, LinkPreviewOptions, Update
from telegram.error import BadRequest, Forbidden
from telegram.ext import (ApplicationBuilder, CallbackQueryHandler, CommandHandler,
                          ContextTypes, MessageHandler, TypeHandler, filters)

logging.basicConfig(level=logging.INFO)
logging.getLogger("httpx").setLevel(logging.WARNING)
log = logging.getLogger("payrollpath")

BOT_TOKEN = os.environ.get("BOT_TOKEN")
ADMIN_IDS = {int(x) for x in os.environ.get("ADMIN_IDS", "").split(",") if x.strip().isdigit()}
IST = timezone(timedelta(hours=5, minutes=30))
OPEN_H, CLOSE_H = int(os.environ.get("OFFICE_START_HOUR", 10)), int(os.environ.get("OFFICE_END_HOUR", 18))
DAILY_H = int(os.environ.get("DAILY_UPDATE_HOUR_IST", 9))
DATA = Path(os.environ.get("DATA_DIR", "bot_data"))
SUBS, CACHE, MW = DATA / "subscribers.json", DATA / "updates_cache.json", DATA / "minimum_wages.json"
NOPREV = LinkPreviewOptions(is_disabled=True)
NOTE = ("⚠️ Indicative FY 2026–27 estimate only. Actual payroll depends on wage components, EPF "
        "membership, employer policy, state rules, tax declarations & current notifications. Verify before payroll use.")
QUERIES = ["labour codes India payroll", "Code on Wages rules notification", "EPFO circular notification",
           "ESIC notification circular", "minimum wages revision notification", "minimum wages hike state government",
           "VDA revision minimum wages", "TDS salary CBDT circular", "professional tax labour welfare fund"]
STATES = ("Andhra Pradesh,Arunachal Pradesh,Assam,Bihar,Chhattisgarh,Goa,Gujarat,Haryana,Himachal Pradesh,"
          "Jharkhand,Karnataka,Kerala,Madhya Pradesh,Maharashtra,Manipur,Meghalaya,Mizoram,Nagaland,Odisha,"
          "Punjab,Rajasthan,Sikkim,Tamil Nadu,Telangana,Tripura,Uttar Pradesh,Uttarakhand,West Bengal,Delhi,"
          "Jammu and Kashmir,Chandigarh,Puducherry,Ladakh").split(",")

# ======================= CALCULATION ENGINE =======================
# One formula string drives BOTH the python value and the Excel formula.
# {name} = another row/input. Use only: + - * / <= >= < > MIN MAX IF ROUND CEILING.
R = lambda x, n=0: math.floor(x * 10 ** n + 0.5) / 10 ** n
FUNCS = {"__builtins__": {}, "MIN": min, "MAX": max, "ROUND": R,
         "IF": lambda c, a, b: a if c else b, "CEILING": lambda x, s: math.ceil(x / s) * s}
REF = re.compile(r"\{(\w+)\}")


def run(spec, inp):
    v = dict(inp)
    for n, _, f, _ in spec["rows"]:
        if f:
            v[n] = eval(REF.sub(r"V['\1']", f), FUNCS, {"V": v})
    return v


def taxrows(p, gx, new):
    """Income-tax rows (slab, rebate, surcharge, cess) for one regime; gx = annual gross formula."""
    t = "{%sti}" % p
    bands = ([(4e5, 8e5, .05), (8e5, 12e5, .1), (12e5, 16e5, .15), (16e5, 20e5, .2), (20e5, 24e5, .25), (24e5, 1e12, .3)]
             if new else [("{%sex}" % p, 5e5, .05), (5e5, 10e5, .2), (10e5, 1e12, .3)])
    fmt = lambda x: x if isinstance(x, str) else int(x)
    slab = "+".join(f"MAX(0,MIN({t},{fmt(h)})-{fmt(l)})*{r}" for l, h, r in bands)
    sl = "{%ssl}" % p
    reb = (f"IF({t}<=1200000,MAX(0,{sl}-60000),MIN({sl},{t}-1200000))" if new
           else f"IF({t}<=500000,MAX(0,{sl}-12500),{sl})")
    sr = f"IF({t}>20000000,0.25,IF({t}>10000000,0.15,IF({t}>5000000,0.1,0)))"
    if not new:
        sr = f"IF({t}>50000000,0.37,{sr})"
    L = "New: " if new else "Old: "
    rows = [(p + "ti", L + "Taxable income", f"MAX(0,{gx}-{75000 if new else 50000}" + ("" if new else "-{ded}") + ")",
             "After std deduction" + ("" if new else " + deductions")),
            (p + "sl", L + "Slab tax", slab, ""),
            (p + "rb", L + "Tax after rebate", reb, "Sec 87A rebate / marginal relief"),
            (p + "sr", L + "Surcharge rate", sr, ""),
            (p + "tax", L + "Annual tax (+4% cess)", "{%srb}*(1+{%ssr})*1.04" % (p, p), "No surcharge marginal relief"),
            (p + "mt", L + "Monthly TDS", "{%stax}/12" % p, "Average per month")]
    if not new:
        rows.insert(0, (p + "ex", L + "Basic exemption limit", "IF({age}<=0,250000,IF({age}<=1,300000,500000))", "By age band"))
    return rows


GB = [("gross", "Monthly gross remuneration", None), ("basic", "Basic+DA", None)]
TAXIN = [("ded", "Old-regime deductions (annual)", 0), ("age", "Age band (0=<60, 1=60-79, 2=80+)", 0)]
WB = [("wb", "Wage base (50% rule)", "MAX({basic},{gross}*0.5)", "Basic+DA, min 50% of gross"),
      ("pfw", "PF wage (25,000 ceiling)", "MIN({wb},25000)", "")]
ESIC_OK = ("ok", "ESIC eligible? (1=yes)", "IF({wb}<=21000,1,0)", "Wage base <= 21,000")
SEC = lambda t: (None, "— " + t + " —", None, "")

SPECS = {
    "pf": dict(title="PF Calculation", ex="30000,15000", inputs=GB, chk=lambda v: v["basic"] <= v["gross"],
               rows=WB + [("ee", "Employee PF 12%", "ROUND({pfw}*0.12,0)", ""),
                          ("er", "Employer total 12%", "ROUND({pfw}*0.12,0)", ""),
                          ("eps", "Employer EPS 8.33%", "ROUND({pfw}*0.0833,0)", ""),
                          ("epf", "Employer EPF balance", "{er}-{eps}", "")], res=["ee", "er"]),
    "esic": dict(title="ESIC Calculation", ex="18000,9000", inputs=GB, chk=lambda v: v["basic"] <= v["gross"],
                 rows=WB[:1] + [ESIC_OK, ("ee", "Employee 0.75%", "ROUND({wb}*0.0075,0)*{ok}", ""),
                                ("er", "Employer 3.25%", "ROUND({wb}*0.0325,0)*{ok}", ""),
                                ("tot", "Total contribution", "{ee}+{er}", "")], res=["ee", "er"]),
    "ctc_new": dict(title="CTC Breakup (New Wage Code, Basic+DA >= 50%)", ex="600000  or  600000,12000,9000", solve=True,
                    inputs=[("ctc", "Annual CTC", None), ("ins", "Annual insurance/benefits", 0), ("mw", "State minimum wage (for bonus ceiling)", 0), ("gross", "Monthly gross (auto-solved)", 0)],
                    chk=lambda v: v["ctc"] >= 50000 and v["ins"] < v["ctc"] * .5,
                    rows=[SEC("Earnings (monthly)"), ("basic", "Basic+DA (>=50%)", "CEILING({gross}/2,1)", ""),
                          ("hra", "HRA (50% of Basic)", "ROUND({basic}*0.5,0)", "Illustrative"),
                          ("spl", "Special allowance", "{gross}-{basic}-{hra}", ""),
                          SEC("Employer cost (monthly)")] + WB[:1] + [WB[1],
                          ("er", "Employer EPF 12%", "ROUND({pfw}*0.12,0)", "EPS 8.33% + EPF"),
                          ("adm", "EPF admin + EDLI 1%", "ROUND({pfw}*0.01,0)", ""), ESIC_OK,
                          ("eer", "Employer ESIC 3.25%", "ROUND({wb}*0.0325,0)*{ok}", ""),
                          ("grat", "Gratuity provision", "ROUND({basic}*15/26/12,0)", "4.81% of Basic"),
                          ("bon", "Bonus provision 8.33%", "IF({wb}<=21000,ROUND(MIN({wb},MAX(7000,{mw}))*0.0833,0),0)", "On ceiling = max(7,000, min wage)"),
                          ("insm", "Insurance/benefits", "{ins}/12", ""),
                          ("total", "Total monthly cost (<= CTC/12)", "{gross}+{er}+{adm}+{eer}+{grat}+{bon}+{insm}", "Gross + employer side"),
                          ("tgt", "Monthly CTC", "{ctc}/12", ""),
                          SEC("Employee side (monthly)"), ("eee", "Employee PF 12%", "ROUND({pfw}*0.12,0)", ""),
                          ("ees", "Employee ESIC 0.75%", "ROUND({wb}*0.0075,0)*{ok}", ""),
                          ("net", "Net before TDS/PT", "{gross}-{eee}-{ees}", "PT/LWF state-specific")]
                    + taxrows("n_", "{gross}*12", True) + [("inh", "In-hand after TDS", "{net}-{n_mt}", "")],
                    res=["gross", "net", "inh"]),
    "tds": dict(title="TDS: Old vs New Regime", ex="900000  or  900000,150000,0",
                inputs=[("gross", "Annual gross salary", None)] + TAXIN,
                rows=[SEC("New regime")] + taxrows("n_", "{gross}", True) + [SEC("Old regime")] + taxrows("o_", "{gross}", False)
                     + [("save", "Saving with New (- = Old better)", "{o_tax}-{n_tax}", "")],
                res=["n_mt", "o_mt", "save"]),
    "salary": dict(title="Net Salary Estimate", ex="30000,15000  or  60000,30000,150000,0", inputs=GB + TAXIN,
                   chk=lambda v: v["basic"] <= v["gross"],
                   rows=WB + [("epf", "Employee PF 12%", "ROUND({pfw}*0.12,0)", ""), ESIC_OK,
                              ("esic", "Employee ESIC 0.75%", "ROUND({wb}*0.0075,0)*{ok}", "")]
                        + [SEC("New regime")] + taxrows("n_", "{gross}*12", True)
                        + [SEC("Old regime")] + taxrows("o_", "{gross}*12", False)
                        + [SEC("Net pay"), ("net_n", "Net pay - New regime", "{gross}-{epf}-{esic}-{n_mt}", "PT not included"),
                           ("net_o", "Net pay - Old regime", "{gross}-{epf}-{esic}-{o_mt}", "PT not included")],
                   res=["net_n", "net_o"]),
    "gratuity": dict(title="Gratuity (Code on Social Security)", ex="40000,20000,6,0", chk=lambda v: v["basic"] <= v["gross"],
                     inputs=GB + [("years", "Years of service", None), ("ft", "Fixed-term employee? (1=yes, 0=no)", 0)],
                     rows=WB[:1] + [("ok", "Eligible? (1=yes)", "IF({ft}<=0,IF({years}>=5,1,0),IF({years}>=1,1,0))", "Permanent 5 yrs; fixed-term 1 yr (pro-rata)"),
                                    ("yrs", "Completed years", "ROUND({years},0)", "Part-year over 6 months = 1 year"),
                                    ("amt", "Gratuity (max 20,00,000)", "MIN({wb}*15/26*{yrs}*{ok},2000000)", "Wages x 15 / 26 x Years")], res=["amt"]),
    "bonus": dict(title="Statutory Bonus (Code on Wages)", ex="20000,10000,9000", chk=lambda v: v["basic"] <= v["gross"],
                  inputs=GB + [("mw", "State minimum wage (monthly)", 0)],
                  rows=WB[:1] + [("ok", "Eligible? (1=yes, wage <= 21,000)", "IF({wb}<=21000,1,0)", "Eligibility ceiling"),
                                 ("cw", "Bonus calculation wage", "MIN({wb},MAX(7000,{mw}))", "Ceiling: higher of 7,000 or min wage"),
                                 ("mn", "Minimum bonus 8.33% (annual)", "{cw}*12*0.0833*{ok}", ""),
                                 ("mx", "Maximum bonus 20% (annual)", "{cw}*12*0.2*{ok}", "")], res=["mn", "mx"]),
    "leave": dict(title="Leave Encashment", ex="40000,20000,15", chk=lambda v: v["basic"] <= v["gross"],
                  inputs=GB + [("days", "EL days to encash", None)],
                  rows=WB[:1] + [("pd", "Per day rate (wages / 30)", "{wb}/30", "30-day divisor; follow company policy"),
                                 ("amt", "Encashment amount", "{pd}*{days}", "")], res=["amt"]),
    "ot": dict(title="Overtime Pay (2x wages)", ex="30000,15000,10", chk=lambda v: v["basic"] <= v["gross"],
               inputs=GB + [("hrs", "Overtime hours", None)],
               rows=WB[:1] + [("hr", "Normal hourly rate", "{wb}/26/8", "Wages / 26 days / 8 hrs; follow policy"),
                              ("amt", "Overtime pay (2x rate)", "{hr}*2*{hrs}", "Beyond 8 hrs/day or 48 hrs/week")], res=["amt"]),
}


def labels(spec):
    return {n: l for n, l, *_ in spec["inputs"]} | {n: l for n, l, f, _ in spec["rows"] if f}


def prompt(key):
    s = SPECS[key]
    ins = s["inputs"][:-1] if s.get("solve") else s["inputs"]
    return (f"📥 {s['title']}\nBhejo (comma se alag): " + ", ".join(l if d is None else f"[{l}]" for _, l, d in ins)
            + f"\nExample: {s['ex']}\n([ ] wale optional hain; numbers me thousand comma mat lagao)")


def parse(spec, text):
    ins = spec["inputs"][:-1] if spec.get("solve") else spec["inputs"]
    parts = [text.replace(",", "")] if len(ins) == 1 else text.split(",")
    if len(parts) > len(ins):
        raise ValueError
    vals = {}
    for i, (n, _, d) in enumerate(ins):
        if i < len(parts):
            x = float(parts[i].strip().replace("₹", ""))
        elif d is None:
            raise ValueError
        else:
            x = d
        if not math.isfinite(x) or x < 0:
            raise ValueError
        vals[n] = x
    if not spec.get("chk", lambda v: True)(vals):
        raise ValueError
    if spec.get("solve"):  # highest whole-rupee gross whose total cost fits the CTC
        cost = lambda g: run(spec, {**vals, "gross": g})["total"]
        tgt, top = vals["ctc"] / 12, 42000
        lo, hi = (1, top) if tgt <= cost(top) else (top + 1, max(top + 1, int(tgt)))
        while lo < hi:
            mid = (lo + hi + 1) // 2
            lo, hi = (mid, hi) if cost(mid) <= tgt else (lo, mid - 1)
        vals["gross"] = lo
    return vals


# ======================= EXCEL + IMAGE OUTPUT =======================
def hdr_style(ws, row=1):
    for c in ws[row]:
        c.font, c.fill = Font(bold=True, color="FFFFFF"), PatternFill("solid", fgColor="1F4E78")
        c.alignment = Alignment(horizontal="center", vertical="center")


def as_table(ws, name, ref=None, widths=None):
    if ws.max_row > 1:
        ws.add_table(Table(displayName=name, ref=ref or ws.dimensions,
                           tableStyleInfo=TableStyleInfo(name="TableStyleMedium2", showRowStripes=True)))
    for i, col in enumerate(ws.columns):
        w = widths[i] if widths else min(60, max(len(str(c.value or "")) for c in col) + 2)
        ws.column_dimensions[col[0].column_letter].width = w
    ws.freeze_panes = "A2" if not widths else "A5"


def make_xlsx(spec, v):
    wb = Workbook(); ws = wb.active; ws.title = "Calculation"
    ws["A1"], ws["A1"].font = spec["title"] + " (FY 2026–27)", Font(bold=True, size=14)
    ws["A2"] = "Yellow = input (badlo, formulas auto-update). Indicative estimate; verify before payroll use."
    ws.append([]); ws.append(["Item", "Value", "How calculated", "Note"]); hdr_style(ws, 4)
    cell, lab, r = {}, {}, 5
    sub_ref = lambda f: REF.sub(lambda m: cell[m[1]], f)
    sub_lab = lambda f: REF.sub(lambda m: "[" + lab[m[1]] + "]", f)
    for n, l, d in spec["inputs"]:
        ws.cell(r, 1, l); c = ws.cell(r, 2, v[n]); c.fill = PatternFill("solid", fgColor="FFF2CC")
        c.number_format = "#,##0.00"; ws.cell(r, 3, "Input"); cell[n], lab[n] = f"B{r}", l; r += 1
    for n, l, f, note in spec["rows"]:
        ws.cell(r, 1, l)
        if f:
            ws.cell(r, 2, "=" + sub_ref(f)).number_format = "#,##0.00"
            ws.cell(r, 3, "ƒ " + sub_lab(f)); ws.cell(r, 4, note); cell[n], lab[n] = f"B{r}", l
        else:
            ws.cell(r, 1).font = Font(bold=True, color="1F4E78")
        r += 1
    for row in ws.iter_rows(min_row=5, max_row=r - 1, min_col=1, max_col=4):
        for c in row:
            c.alignment = Alignment(wrap_text=True, vertical="top")
    as_table(ws, "Calc", f"A4:D{r - 1}", widths=[40, 18, 55, 38])
    out = BytesIO(); wb.save(out); out.seek(0)
    return out


def make_png(spec, v):
    num = lambda x: f"{x:,.0f}" if abs(x - round(x)) < 1e-9 else f"{x:,.2f}"
    rows = [(l, num(v[n]), "Input") for n, l, _ in spec["inputs"]]
    rows += [(l, num(v[n]), note) if f else (l, "", "") for n, l, f, note in spec["rows"]]
    fig = Figure(figsize=(9, 0.4 * len(rows) + 1.3))
    ax = fig.subplots(); ax.axis("off"); ax.set_title(spec["title"] + " – FY 2026–27", fontweight="bold", color="#1F4E78")
    t = ax.table(cellText=rows, colLabels=["Item", "Value (₹)", "Note"], loc="upper center", cellLoc="left", colWidths=[.5, .16, .34])
    t.auto_set_font_size(False); t.set_fontsize(9); t.scale(1, 1.5)
    for (r, c), cl in t.get_celld().items():
        if r == 0:
            cl.set_facecolor("#1F4E78"); cl.set_text_props(color="white", fontweight="bold")
        elif rows[r - 1][2] == "Input":
            cl.set_facecolor("#FFF2CC")
        elif not rows[r - 1][1]:
            cl.set_facecolor("#D9E1F2"); cl.set_text_props(fontweight="bold")
        elif r % 2 == 0:
            cl.set_facecolor("#F2F2F2")
    out = BytesIO(); fig.savefig(out, format="png", dpi=150, bbox_inches="tight"); out.seek(0)
    return out


async def calc_reply(msg, key, text):
    spec = SPECS[key]; v = run(spec, parse(spec, text)); lab = labels(spec)
    cap = f"📊 {spec['title']}\n" + "\n".join(f"{lab[n]}: ₹{v[n]:,.0f}" for n in spec["res"])
    cap += "\n\n📎 Neeche Excel bhi hai (formulas + table).\n" + NOTE
    await msg.reply_photo(make_png(spec, v), caption=cap[:1024])
    await msg.reply_document(make_xlsx(spec, v), filename=f"{key}_calculation.xlsx")


# ======================= INFO TEXTS / MENU =======================
INFO = {
    "info_compliance": (
        "📆 *Compliance Calendar — HR Teams*\n\n*🗓 Monthly*\n- 7th: Salary processing, pay slip, TDS deposit\n"
        "- 15th: EPF & ESIC payment\n- Professional Tax / LWF: state-wise\n\n*📅 Annual*\n"
        "- Bonus Act: within 8 months of FY-end\n- Shop & Establishment renewal\n"
        "- Annual returns: POSH, Child Labour, Gratuity, Maternity Benefit, Equal Remuneration, CLRA\n\n"
        "*📚 Registers (monthly)*\nMuster Roll, Wages, Overtime, Accident, Deduction/Fine/Advance, Leave, Employee Master\n\n"
        "*📌 Also*\n- TDS 24Q return: 31 Jul, 31 Oct, 31 Jan, 31 May\n- Form 16: by 15 June\n\n"
        "_State dates (PT, LWF, S&E) alag hote hain — state labour portal check karo._\n\n" + NOTE),
    "info_taxsave": (
        "💡 *Tax Saver*\n\n*1️⃣ Sahi regime chuno* — New: ₹75,000 std deduction, ₹12L taxable tak rebate. "
        "Old tab jeetta hai jab HRA, home loan, 80C, 80D zyada ho. Neeche button se compare karo.\n\n"
        "*2️⃣ Dono regime me* — Employer NPS 80CCD(2): Basic+DA ka 14% tak; employer PF+NPS+superannuation ₹7.5L/yr tak tax-free.\n\n"
        "*3️⃣ Sirf Old regime me* — 80C ₹1.5L, NPS extra ₹50,000, 80D, HRA (rent receipts; ₹1L+ rent par landlord PAN), "
        "home loan interest ₹2L, education loan, 80G, LTA.\n\n"
        "*4️⃣ Payroll checklist* — April me declaration, Dec–Jan me proofs; pichhle employer ka Form 12B lo; "
        "extra TDS ka refund ITR se.\n\n" + NOTE),
    "info_templates": "📁 *HR Templates*\n\nComing soon: offer/appointment letters, payslip, FnF settlement formats.",
    "info_premium": "⭐ *Premium*\n\nPlanned: bulk payroll reports, state-wise compliance tracker, auto payslips.",
}
MENU = [("🏦 PF", "calc_pf"), ("🏥 ESIC", "calc_esic"), ("📊 CTC Breakup (New Wage)", "calc_ctc_new"),
        ("💵 Net Salary", "calc_salary"), ("🎁 Gratuity", "calc_gratuity"), ("🎯 Bonus", "calc_bonus"),
        ("🏖 Leave Encashment", "calc_leave"), ("🧾 TDS Old vs New", "calc_tds"), ("⏰ Overtime", "calc_ot"),
        ("💰 State Min Wages", "mw_menu"), ("📆 Compliance Calendar", "info_compliance"), ("📰 Updates", "info_updates"),
        ("💡 Tax Saver", "info_taxsave"), ("🔔 Daily Alerts", "info_subscribe"), ("📁 HR Templates", "info_templates"),
        ("⭐ Premium", "info_premium")]
menu = lambda: Kb([[Btn(t, callback_data=c) for t, c in MENU[i:i + 2]] for i in range(0, len(MENU), 2)])


# ======================= STORAGE + MIN WAGES =======================
def load(p, d):
    try:
        return json.loads(Path(p).read_text("utf-8"))
    except (OSError, ValueError):
        return d


def save(p, data):
    try:
        p.parent.mkdir(parents=True, exist_ok=True)
        tmp = p.with_suffix(".tmp"); tmp.write_text(json.dumps(data, ensure_ascii=False), "utf-8"); os.replace(tmp, p)
    except OSError:
        log.exception("save failed %s", p)


def mw_data():
    d = load(MW, {}); d = d if isinstance(d, dict) else {}
    d.setdefault("states", {}); d.setdefault("changes", [])
    return d


def mw_kb():
    return Kb([[Btn(s, callback_data=f"mw_{i}") for i, s in enumerate(STATES) if i // 2 == j] for j in range((len(STATES) + 1) // 2)])


def mw_text(state):
    rec, e = mw_data()["states"].get(state), html.escape
    if not rec:
        return f"💰 <b>{e(state)}</b>\nIs state ka verified data abhi add nahi hua. Official labour department notification check karo."
    r = rec["rates"]
    src = f'\n<a href="{e(rec["source"], quote=True)}">Official source</a>\n' if rec.get("source") else ""
    return (f"💰 <b>Minimum Wages — {e(state)}</b>\nEffective from: {e(rec['effective'])}\n\n"
            f"Unskilled: ₹{r[0]:,.0f}/month\nSemi-skilled: ₹{r[1]:,.0f}/month\nSkilled: ₹{r[2]:,.0f}/month\n"
            f"Highly skilled: ₹{r[3]:,.0f}/month\n{src}\n<i>Last verified: {e(rec.get('verified', 'n/a'))}. Zone/industry/VDA "
            "alag ho sakte hain — notification se confirm karo.</i>")


admin = lambda u: bool(u.effective_user and u.effective_user.id in ADMIN_IDS)


async def setwage_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """/setwage State | YYYY-MM-DD | unskilled,semi,skilled,highly | source_url(optional)"""
    if not admin(update):
        return await update.message.reply_text("Not authorised.")
    try:
        p = [x.strip() for x in update.message.text.split(maxsplit=1)[1].split("|")]
        state = next(s for s in STATES if s.lower() == p[0].lower())
        eff = datetime.strptime(p[1], "%Y-%m-%d").date().isoformat()
        rates = [float(x) for x in p[2].replace("₹", "").split(",")]
        if len(rates) != 4 or any(not math.isfinite(x) or x <= 0 for x in rates):
            raise ValueError
    except (IndexError, StopIteration, ValueError):
        return await update.message.reply_text("Format:\n/setwage State | YYYY-MM-DD | unskilled,semi,skilled,highly | source_url(optional)")
    d, today = mw_data(), datetime.now(IST).date().isoformat()
    old = d["states"].get(state)
    d["states"][state] = dict(effective=eff, rates=rates, source=p[3] if len(p) > 3 else "", verified=today)
    changed = not old or old["rates"] != rates
    if changed:
        d["changes"] = (d["changes"] + [dict(id=f"{state}|{eff}|{today}", state=state, effective=eff,
                                              old=old and old["rates"], new=rates, announced=today)])[-100:]
    save(MW, d)
    await update.message.reply_text(f"✅ {state} saved." + (" Next daily alert me jayega." if changed else " (Rates same, sirf verified date update hui.)"))


async def mwstatus_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    if not admin(update):
        return await update.message.reply_text("Not authorised.")
    st = mw_data()["states"]
    lines = [f"Data added: {len(st)}/{len(STATES)}"] + [f"✅ {s} — effective {r['effective']}, verified {r.get('verified', 'n/a')}" for s, r in st.items()]
    await update.message.reply_text("\n".join(lines + ["\nPending: " + ", ".join(s for s in STATES if s not in st)])[:4000])


# ======================= NEWS / DAILY UPDATES =======================
async def fetch_news(client, q):
    r = await client.get("https://news.google.com/rss/search?q=" + quote_plus(q + " when:7d") + "&hl=en-IN&gl=IN&ceid=IN:en")
    r.raise_for_status(); out = []
    for it in ET.fromstring(r.content).iter("item"):
        title, link = (it.findtext("title") or "").strip(), (it.findtext("link") or "").strip()
        if not (title and link):
            continue
        try:
            pub = parsedate_to_datetime(it.findtext("pubDate")).astimezone(timezone.utc)
        except (TypeError, ValueError):
            pub = datetime.now(timezone.utc)
        out.append(dict(title=title, link=link, source=(it.findtext("source") or "").strip(), published=pub.isoformat()))
    return out[:6]


async def refresh(force=False):
    cache = load(CACHE, {})
    if not force and cache.get("fetched_at") and datetime.now(timezone.utc) - datetime.fromisoformat(cache["fetched_at"]) < timedelta(hours=6):
        return cache
    try:
        async with httpx.AsyncClient(timeout=15, follow_redirects=True) as c:
            res = await asyncio.gather(*(fetch_news(c, q) for q in QUERIES), return_exceptions=True)
    except Exception:
        log.exception("news fetch failed"); return cache
    seen, items = set(), []
    for r in res:
        for i in [] if isinstance(r, Exception) else r:
            if i["title"].lower() not in seen:
                seen.add(i["title"].lower()); items.append(i)
    if items:
        cache["items"] = sorted(items, key=lambda i: i["published"], reverse=True)[:30]
        cache["fetched_at"] = datetime.now(timezone.utc).isoformat()
        save(CACHE, cache)
    return cache


def news_lines(items, limit=8, extra=lambda i: ""):
    return "\n".join(f'• <a href="{html.escape(i["link"], quote=True)}">{html.escape(i["title"])}</a>{extra(i)} — '
                     f'{html.escape(i.get("source") or "news")}, {datetime.fromisoformat(i["published"]).astimezone(IST):%d %b}'
                     for i in items[:limit])


def mw_news(items):
    out = []
    for it in items:
        t = it["title"].lower()
        if "minimum wage" in t or re.search(r"\bvda\b", t) or "dearness allowance" in t:
            out.append((it, [s for s in STATES if re.search(rf"\b{re.escape(s.lower())}\b", t)]))
    return out


def due_block(today=None, days=10):
    today, due = today or datetime.now(IST).date(), []
    for o in range(days + 1):
        d = today + timedelta(days=o); s = f"{d:%d %b} ({'today' if o == 0 else f'in {o}d'})"
        if d.day == 7: due.append(f"{s}: Salary processing, pay slips, TDS deposit")
        if d.day == 15: due.append(f"{s}: EPF & ESIC payment")
        if (d.month, d.day) in {(7, 31), (10, 31), (1, 31), (5, 31)}: due.append(f"{s}: TDS 24Q quarterly return")
        if (d.month, d.day) == (6, 15): due.append(f"{s}: Form 16 to employees")
    return "<b>⏳ Upcoming due dates</b>\n" + "\n".join("• " + html.escape(x) for x in due) + "\n\n" if due else ""


def mw_alerts(changes, news):
    L = ["<b>💰 Minimum Wage Alerts</b>"]
    for c in changes:
        n = c["new"]
        L.append(f"• <b>{html.escape(c['state'])}</b> — effective {html.escape(c['effective'])}: Unskilled ₹{n[0]:,.0f}, "
                 f"Semi ₹{n[1]:,.0f}, Skilled ₹{n[2]:,.0f}, Highly ₹{n[3]:,.0f}")
    if news:
        L.append(news_lines([i for i, _ in news], 99, lambda i: next((f" [{html.escape(', '.join(s))}]" for x, s in news if x is i and s), "")))
    return "\n".join(L + ["<i>Headlines auto-fetch hoti hain; rates /minwage me verify hone ke baad update hote hain.</i>"])


def cut(text, limit=4000):
    if len(text) <= limit:
        return text
    t = text[:limit]; i = t.rfind("\n")
    return t[:i] if i > 0 else t


async def updates_text():
    cache = await refresh(); items = cache.get("items", [])
    t = ("📰 <b>Payroll &amp; Compliance Updates</b>\n\n<b>Labour Codes:</b> 4 Labour Codes 21 Nov 2025 se national level par lagu hain. "
         "States rules phase-wise la rahe hain — apne state labour department ka status check karo.\n\n" + due_block())
    if items:
        mw = mw_news(items)[:4]
        if mw:
            t += "<b>💰 Minimum wage headlines</b> (rates: /minwage)\n" + news_lines([i for i, _ in mw], 4) + "\n\n"
        f = datetime.fromisoformat(cache["fetched_at"]).astimezone(IST)
        t += f"<b>🗞 Latest headlines</b> (updated {f:%d %b, %H:%M} IST)\n" + news_lines(items) + "\n\n<i>Auto-fetched — official circular se verify karo.</i>\n\n"
    else:
        t += "<i>Abhi live headlines fetch nahi ho payi. Thodi der baad try karo.</i>\n\n"
    return cut(t + "<b>Sources:</b> labour.gov.in • epfindia.gov.in • esic.gov.in • incometax.gov.in\n" + html.escape(NOTE))


async def broadcast(app):
    subs = set(load(SUBS, []))
    if not subs:
        return
    cache = await refresh(True); items = cache.get("items", []); sent = set(cache.get("sent", []))
    new = [i for i in items if i["link"] not in sent and datetime.fromisoformat(i["published"]) >= datetime.now(timezone.utc) - timedelta(days=2)]
    mw = mw_data(); chg = [c for c in mw["changes"] if c["id"] not in set(cache.get("mw_sent", []))]; mwn = mw_news(new)
    now = datetime.now(IST)
    t = f"🔔 <b>Daily Payroll &amp; Compliance Update — {now:%d %b %Y}</b>\n\n" + due_block(now.date())
    if chg or mwn:
        t += mw_alerts(chg, mwn) + "\n\n"
    t += ("<b>🗞 Naye headlines</b>\n" + news_lines(new) + "\n\n") if new else "Aaj koi naye headlines nahi mile.\n\n"
    t = cut(t + "<i>Official notification se verify karo. /updates, /minwage</i>")
    for cid in list(subs):
        try:
            await app.bot.send_message(cid, t, parse_mode="HTML", link_preview_options=NOPREV)
        except (Forbidden, BadRequest):
            subs.discard(cid)
        except Exception:
            log.exception("broadcast to %s failed", cid)
        await asyncio.sleep(0.05)
    save(SUBS, sorted(subs))
    cache.update(sent=[i["link"] for i in items], mw_sent=[c["id"] for c in mw["changes"]]); save(CACHE, cache)


async def daily_loop(app):
    while True:
        now = datetime.now(IST); nxt = now.replace(hour=DAILY_H, minute=0, second=0, microsecond=0)
        await asyncio.sleep(((nxt + timedelta(days=1) if nxt <= now else nxt) - now).total_seconds())
        try:
            await broadcast(app)
        except Exception:
            log.exception("daily broadcast failed")


# ======================= HANDLERS =======================
send_html = lambda msg, text, **kw: msg.reply_text(text, parse_mode="HTML", link_preview_options=NOPREV, **kw)


async def toggle_sub(msg, force=None):
    subs = set(load(SUBS, [])); on = (msg.chat_id not in subs) if force is None else force
    (subs.add if on else subs.discard)(msg.chat_id); save(SUBS, sorted(subs))
    await msg.reply_text(f"🔔 Daily alerts ON. Roz subah {DAILY_H}:00 IST par headlines, min wage changes aur due dates milenge. Band: /unsubscribe"
                         if on else "🔕 Daily alerts OFF. Dobara chalu: /subscribe")


async def route(key, msg, ctx):
    if key.startswith("calc_"):
        ctx.user_data["calc"] = key[5:]; await msg.reply_text(prompt(key[5:]))
    elif key == "mw_menu":
        await msg.reply_text("💰 State chuno (minimum wages):", reply_markup=mw_kb())
    elif key.startswith("mw_"):
        await send_html(msg, mw_text(STATES[int(key[3:])]))
    elif key in ("info_subscribe", "sub_on", "sub_off"):
        await toggle_sub(msg, {"sub_on": True, "sub_off": False}.get(key))
    elif key == "info_updates":
        subd = msg.chat_id in set(load(SUBS, []))
        await send_html(msg, await updates_text(), reply_markup=Kb([[Btn("🔕 Daily alerts band karo" if subd else "🔔 Daily alerts chalu karo", callback_data="info_subscribe")]]))
    elif key in INFO:
        kb = Kb([[Btn("🧮 Compare Old vs New", callback_data="calc_tds")]]) if key == "info_taxsave" else None
        await msg.reply_text(INFO[key], parse_mode="Markdown", reply_markup=kb)


def cmd_for(key):
    async def h(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
        await route(key, update.message, ctx)
    return h


async def start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    ctx.user_data.pop("calc", None)
    await update.message.reply_text("👋 *Welcome to PayrollPath India!*\n\nFree HR & payroll compliance assistant.\n"
                                    "Har calculator ka result *table image + Excel (formulas ke saath)* me milega.",
                                    parse_mode="Markdown", reply_markup=menu())


async def help_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text("ℹ️ /start = menu\nCalculators: " + " ".join("/" + k for k in SPECS) + " /regime\n"
                                    "Info: /taxsave /compliance /updates /minwage /templates /premium\n"
                                    "Alerts: /subscribe /unsubscribe   Data: /export   Cancel: /cancel")


async def cancel(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    ctx.user_data.pop("calc", None); await update.message.reply_text("Cancelled. /start se dobara shuru karo.")


async def on_button(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    await update.callback_query.answer(); await route(update.callback_query.data, update.callback_query.message, ctx)


async def on_text(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    key = ctx.user_data.get("calc")
    if not key:
        return await update.message.reply_text("Samajh nahi aaya. /start karke menu se try karo, ya /help dekho.")
    try:
        await calc_reply(update.message, key, update.message.text)
        ctx.user_data.pop("calc", None)
    except (ValueError, OverflowError, ZeroDivisionError):
        await update.message.reply_text("⚠️ Input sahi format me bhejo.\n\n" + prompt(key))


async def export_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    wb = Workbook(); ws = wb.active; ws.title = "Updates"; ws.append(["Title", "Source", "Published", "Link"])
    for i in load(CACHE, {}).get("items", []):
        ws.append([i["title"], i.get("source", ""), i["published"][:10], i["link"]])
    w2 = wb.create_sheet("Minimum Wages")
    w2.append(["State", "Effective", "Unskilled", "Semi-skilled", "Skilled", "Highly skilled", "Verified", "Source"])
    for s, r in mw_data()["states"].items():
        w2.append([s, r["effective"], *r["rates"], r.get("verified", ""), r.get("source", "")])
    for w, n in ((ws, "UpdatesTbl"), (w2, "MinWageTbl")):
        hdr_style(w); as_table(w, n)
    out = BytesIO(); wb.save(out); out.seek(0)
    await update.message.reply_document(out, filename="PayrollPath_Data.xlsx", caption="📊 Updates + Minimum Wages (Excel table)")


async def after_hours(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    now = datetime.now(timezone.utc); last = ctx.user_data.get("ah")
    if OPEN_H <= datetime.now(IST).hour < CLOSE_H or not (update.message or update.callback_query) or (last and now - last < timedelta(hours=6)):
        return
    ctx.user_data["ah"] = now
    await ctx.bot.send_message(update.effective_chat.id, f"🕙 Support timing {OPEN_H % 12 or 12}:00 AM – {CLOSE_H % 12 or 12}:00 PM (IST). "
                               "Is time ke baad reply late aa sakta hai. Calculators 24x7 chalte hain.")


def main():
    if not BOT_TOKEN:
        raise RuntimeError("BOT_TOKEN not set. Add it in Replit Secrets.")

    async def post_init(app):
        DATA.mkdir(parents=True, exist_ok=True); app.bot_data["task"] = asyncio.create_task(daily_loop(app))

    async def post_shutdown(app):
        if app.bot_data.get("task"):
            app.bot_data["task"].cancel()

    app = ApplicationBuilder().token(BOT_TOKEN).post_init(post_init).post_shutdown(post_shutdown).build()
    app.add_handler(TypeHandler(Update, after_hours), group=-1)
    for name, fn in (("start", start), ("help", help_cmd), ("cancel", cancel), ("setwage", setwage_cmd),
                     ("mwstatus", mwstatus_cmd), ("export", export_cmd)):
        app.add_handler(CommandHandler(name, fn))
    for k in SPECS:
        app.add_handler(CommandHandler(k, cmd_for("calc_" + k)))
    for name, key in [("regime", "calc_tds"), ("ctc", "calc_ctc_new"), ("minwage", "mw_menu"), ("subscribe", "sub_on"), ("unsubscribe", "sub_off")] + \
                     [(k, "info_" + k) for k in ("compliance", "updates", "taxsave", "templates", "premium")]:
        app.add_handler(CommandHandler(name, cmd_for(key)))
    app.add_handler(CallbackQueryHandler(on_button, pattern="^(calc_|info_|mw_)"))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_text))
    app.add_handler(MessageHandler(filters.COMMAND, on_text))
    print("Bot is running..."); app.run_polling()


if __name__ == "__main__":
    main()
