import os
import asyncio
import html
import json
import logging
import math
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from pathlib import Path
from urllib.parse import quote_plus

import httpx
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.error import Forbidden, BadRequest
from telegram.ext import (
    ApplicationBuilder,
    CommandHandler,
    MessageHandler,
    CallbackQueryHandler,
    ConversationHandler,
    ContextTypes,
    TypeHandler,
    filters,
)

try:  # python-telegram-bot >= 21
    from telegram import LinkPreviewOptions
except ImportError:  # older versions
    LinkPreviewOptions = None

logging.basicConfig(level=logging.INFO)
logging.getLogger("httpx").setLevel(logging.WARNING)
logger = logging.getLogger("payrollpath")

BOT_TOKEN = os.environ.get("BOT_TOKEN")

DISCLAIMER = (
    "\n\n⚠️ Indicative FY 2026–27 estimate only. Actual payroll depends on "
    "eligible wage components, EPF membership, employer policy, state rules, "
    "tax declarations and current notifications. Verify before payroll use."
)

# Conversation states
AMOUNT = 1
TAX_REGIME = 2
OLD_DEDUCTIONS = 3
OLD_AGE = 4

# ---------------- STATUTORY PARAMETERS ----------------
EPF_WAGE_CEILING = 25000
ESIC_WAGE_CEILING = 21000  # ESIC coverage ceiling, tested on monthly GROSS wages

# New-wage CTC components (employer side)
EPF_ADMIN_RATE = 0.005  # EPF admin charges
EDLI_RATE = 0.005  # EDLI contribution
GRATUITY_MONTHLY_FACTOR = 15 / 26 / 12  # 15 days wages per year, accrued monthly
BONUS_RATE_MIN = 0.0833  # statutory minimum bonus
BONUS_ELIGIBILITY_WAGE = 21000  # Basic+DA limit for bonus eligibility
BONUS_CALC_CEILING = 7000  # bonus calculation ceiling (or min wage, if higher)

GRATUITY_CAP = 2000000  # statutory gratuity ceiling (₹20 lakh)
NEW_WAGE_BASIC_SHARE = 0.50  # Basic+DA minimum share of gross (Code on Wages)

# Overtime: ordinary rate = Basic+DA / (26 days x 8 hours); OT paid at 2x
OT_DIVISOR_DAYS = 26
OT_HOURS_PER_DAY = 8

# Support hours (IST). Outside this window users get a "late reply" notice.
IST = timezone(timedelta(hours=5, minutes=30))
OFFICE_START_HOUR = int(os.environ.get("OFFICE_START_HOUR", "10"))  # 10:00 AM
OFFICE_END_HOUR = int(os.environ.get("OFFICE_END_HOUR", "18"))  # 06:00 PM
AFTER_HOURS_NOTICE_GAP_HOURS = 6  # don't repeat the notice more often than this

# Daily updates
DAILY_UPDATE_HOUR_IST = int(os.environ.get("DAILY_UPDATE_HOUR_IST", "9"))
DATA_DIR = Path(os.environ.get("DATA_DIR", "bot_data"))
SUBSCRIBERS_FILE = DATA_DIR / "subscribers.json"
UPDATES_CACHE_FILE = DATA_DIR / "updates_cache.json"
UPDATES_CACHE_TTL_HOURS = 6
MAX_UPDATE_ITEMS = 15
UPDATE_QUERIES = [
    "labour codes India payroll",
    "Code on Wages rules notification",
    "EPFO circular notification",
    "ESIC notification circular",
    "minimum wages revision notification",
    "TDS salary CBDT circular",
    "professional tax labour welfare fund",
]

# ---------------- MAIN MENU ----------------


def main_menu_keyboard():
    buttons = [
        [
            InlineKeyboardButton("🏦 PF Calculator", callback_data="calc_pf"),
            InlineKeyboardButton("🏥 ESIC Calculator", callback_data="calc_esic"),
        ],
        [
            InlineKeyboardButton("📊 CTC Breakup", callback_data="calc_ctc"),
            InlineKeyboardButton("🆕 New Wage CTC", callback_data="calc_ctc_new"),
        ],
        [
            InlineKeyboardButton("💵 Net Salary", callback_data="calc_salary"),
            InlineKeyboardButton("🎁 Gratuity", callback_data="calc_gratuity"),
        ],
        [
            InlineKeyboardButton("🎯 Bonus", callback_data="calc_bonus"),
            InlineKeyboardButton("🏖 Leave Encashment", callback_data="calc_leave"),
        ],
        [
            InlineKeyboardButton("🧾 TDS (old/new)", callback_data="calc_tds"),
            InlineKeyboardButton("⏰ Overtime", callback_data="calc_ot"),
        ],
        [
            InlineKeyboardButton("🧮 Old vs New Regime", callback_data="calc_regime"),
            InlineKeyboardButton("💡 Tax Saver", callback_data="info_taxsave"),
        ],
        [
            InlineKeyboardButton(
                "📆 Compliance Calendar", callback_data="info_compliance"
            ),
            InlineKeyboardButton("📰 Updates", callback_data="info_updates"),
        ],
        [
            InlineKeyboardButton("🔔 Daily Alerts", callback_data="info_subscribe"),
        ],
    ]
    return InlineKeyboardMarkup(buttons)


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    clear_calc_state(context)
    text = (
        "👋 *Welcome to PayrollPath India!*\n\n"
        "Aapka free HR, payroll aur compliance assistant.\n"
        "Neeche se calculator ya information option chuniye:"
    )
    await update.message.reply_text(
        text, parse_mode="Markdown", reply_markup=main_menu_keyboard()
    )


async def help_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    text = (
        "ℹ️ *Help*\n\n"
        "/start se main menu kholiye, ya seedha command use kijiye:\n\n"
        "*Calculators*\n"
        "/pf — Basic+DA se PF\n"
        "/esic — Gross se ESIC\n"
        "/ctc /ctc_new — CTC breakup\n"
        "/salary — Gross se net salary\n"
        "/gratuity /bonus /leave /ot — Basic+DA se\n"
        "/tds /regime — Annual gross se tax\n\n"
        "*Information*\n"
        "/taxsave /compliance /updates\n"
        "/subscribe /unsubscribe — daily compliance alerts\n\n"
        "/cancel — chalta hua calculator band karne ke liye"
    )
    await update.message.reply_text(text, parse_mode="Markdown")


async def menu_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    return await route(query.data, update, context, via_button=True)


# ---------------- INFO SECTIONS ----------------

INFO_TEXT = {
    "info_compliance": (
        "📆 *Compliance Calendar — HR Teams*\n\n"
        "*🗓 Monthly*\n"
        "- 7th: Salary Processing\n"
        "- 7th: Pay Slip\n"
        "- 7th: TDS (24Q) deposit\n"
        "- 15th: EPF payment\n"
        "- 15th: ESIC payment\n"
        "- Professional Tax: varies by state\n"
        "- LWF: varies by state\n\n"
        "*📅 Annual Returns / Renewals*\n"
        "- Bonus Act: within 8 months of FY-end\n"
        "- Shop & Establishment Act: annual renewal, as per mentioned date\n"
        "- POSH: annual return\n"
        "- Child Labour Act: annual return\n"
        "- Gratuity Act: annual return\n"
        "- Maternity Benefit Act: annual return\n"
        "- Equal Remuneration Act: annual return\n"
        "- CLRA Act: annual return\n\n"
        "*📚 Auditable Registers (monthly update)*\n"
        "- Muster Roll\n"
        "- Wages Register\n"
        "- Overtime Register\n"
        "- Accident Register\n"
        "- Deduction, Fine & Advance Register\n"
        "- Leave Register\n"
        "- Employee Master / Workmen Register\n\n"
        "*📌 Also remember*\n"
        "- TDS 24Q return filing is quarterly: 31 Jul, 31 Oct, 31 Jan, 31 May\n"
        "- Form 16 to employees: by 15 June\n"
        "- GST returns (finance team): 20th/22nd/24th depending on turnover/state\n\n"
        "_State-specific dates (PT, LWF, S&E, annual returns) differ — confirm on "
        "your state labour department portal._" + DISCLAIMER
    ),
    "info_updates": "Loading updates...",  # built dynamically, see build_updates_message()
    "info_taxsave": (
        "💡 *Tax Saver — employee ka TDS legally kaise kam karein*\n\n"
        "*1️⃣ Pehle sahi regime chuno*\n"
        "- New regime (default): ₹75,000 standard deduction, taxable income "
        "₹12L tak rebate (salary ~₹12.75L tak zero tax)\n"
        "- Old regime tab jeetta hai jab HRA, home loan, 80C, 80D jaise "
        "deductions kaafi ho. Niche button se compare karo.\n\n"
        "*2️⃣ Dono regime me kaam aata hai*\n"
        "- Employer NPS contribution (80CCD(2)): Basic+DA ka 14% tak "
        "(new regime me bhi) — salary structure me add karwao\n"
        "- Employer PF + NPS + superannuation: ₹7.5L/yr tak tax-free\n\n"
        "*3️⃣ Sirf Old regime me*\n"
        "- 80C: ₹1.5L (PPF, ELSS, LIC, tuition fee, home loan principal, "
        "employee PF)\n"
        "- NPS extra (80CCD(1B)): ₹50,000\n"
        "- 80D health insurance: ₹25,000 self/family (senior ₹50,000) + "
        "parents ₹25,000/₹50,000\n"
        "- HRA exemption: rent receipts; metro 50% / non-metro 40% of Basic+DA; "
        "rent > ₹1L/yr par landlord PAN\n"
        "- Home loan interest ₹2L (self-occupied), education loan interest "
        "(80E), donations (80G), savings interest ₹10,000 (80TTA), LTA\n\n"
        "*4️⃣ Payroll team ke liye checklist*\n"
        "- April me regime + investment declaration lo, Dec–Jan me proofs\n"
        "- Pichhle employer ki salary/TDS details (Form 12B) lo, warna TDS "
        "kam katega aur March me shock lagega\n"
        "- Proof late aaye to tax hold na kare — time pe correction run karo\n"
        "- Zyada TDS kat gaya ho to ITR me refund claim hota hai\n"
        "- Income-tax Act 2025 me section numbers badle hain (80C → 123, "
        "80D → 126, NPS → 124); limits lagbhag same. Form 16 me naye numbers "
        "dikhenge.\n" + DISCLAIMER
    ),
}


INFO_KEYBOARDS = {
    "info_taxsave": InlineKeyboardMarkup(
        [[InlineKeyboardButton("🧮 Compare Old vs New", callback_data="calc_regime")]]
    ),
}


def get_message(update):
    if update.callback_query:
        return update.callback_query.message
    return update.message


async def send_html(message, text, **kwargs):
    if LinkPreviewOptions is not None:
        kwargs["link_preview_options"] = LinkPreviewOptions(is_disabled=True)
    else:
        kwargs["disable_web_page_preview"] = True
    return await message.reply_text(text, parse_mode="HTML", **kwargs)


async def send_info(key, update, context, via_button):
    message = get_message(update)
    if key == "info_updates":
        text = await build_updates_message()
        await send_html(
            message,
            text,
            reply_markup=subscribe_keyboard(update.effective_chat.id),
        )
        return
    await message.reply_text(
        INFO_TEXT[key],
        parse_mode="Markdown",
        reply_markup=INFO_KEYBOARDS.get(key),
    )


# ---------------- CALCULATORS (conversation-based) ----------------
# Input policy: every calculator asks only for the figure it actually needs.
#   Gross wages  -> ESIC, Net Salary, TDS / Regime comparison, CTC
#   Basic + DA   -> PF, Gratuity, Bonus, Leave Encashment, Overtime

CALC_PROMPTS = {
    "calc_pf": (
        "Employee ka monthly *Basic + DA* (PF wages) bhejo — sirf number, "
        "e.g. `18000`.\n"
        "_LOP ho to us month ki earned Basic+DA bhejo._"
    ),
    "calc_esic": (
        "Employee ki monthly *Gross wages* bhejo (OT/variable pay included) — "
        "sirf number, e.g. `19500`:"
    ),
    "calc_ctc": "Apna *Annual CTC* bhejo (sirf number, e.g. `600000`):",
    "calc_ctc_new": (
        "New Wage CTC breakup ke liye apna *Annual CTC* bhejo "
        "(sirf number, e.g. `600000`).\n"
        "Optional: employer-paid *annual insurance/other benefit* comma ke "
        "baad (e.g. `600000,12000`):"
    ),
    "calc_regime": (
        "Format me bhejo: *AnnualGross,OldRegimeDeductions* — deductions me "
        "80C + 80D + NPS + HRA exemption + home loan interest etc. ka total "
        "(e.g. `1200000,350000`). Deductions nahi ho to `1200000,0`:"
    ),
    "calc_salary": (
        "Employee ki monthly *Gross salary* bhejo — sirf number, e.g. `30000`.\n"
        "_Basic+DA gross ka 50% maana jayega (Code on Wages ka minimum)._"
    ),
    "calc_gratuity": (
        "Format me bhejo: *Basic+DA,Years* (e.g. `20000,6`).\n"
        "_Months ho to years decimal me likho: 6 saal 8 mahine = `6.67`. "
        "6 mahine se zyada ka period poora saal gina jata hai._"
    ),
    "calc_bonus": (
        "Monthly *Basic + DA* bhejo (e.g. `18000`).\n"
        "_State minimum wage ₹7,000 se zyada ho to comma ke baad likho: "
        "`18000,9500`._"
    ),
    "calc_tds": (
        "Apni *annual gross salary* bhejo (before tax; standard deduction "
        "calculator apply karega, e.g. `900000`):"
    ),
    "calc_leave": "Format me bhejo: *MonthlyBasic+DA,ELDays* (e.g. `24000,15`):",
    "calc_ot": (
        "Format me bhejo: *MonthlyBasic+DA,OTHours* (e.g. `18000,10`).\n"
        "_Rate = Basic+DA ÷ 26 din ÷ 8 ghante, OT 2x pe._"
    ),
}


async def calc_entry(key, update, context, via_button):
    context.user_data["calc"] = key
    context.user_data.pop("calc_data", None)
    context.user_data["calc_step"] = "amount"
    prompt = CALC_PROMPTS[key]
    if via_button:
        await update.callback_query.message.reply_text(prompt, parse_mode="Markdown")
    else:
        await update.message.reply_text(prompt, parse_mode="Markdown")
    return AMOUNT


# ---------------- INPUT PARSING ----------------


def parse_amount(value, allow_zero=False):
    normalized = value.strip().replace("₹", "").replace(",", "").replace(" ", "")
    amount = float(normalized)
    if not math.isfinite(amount) or amount < 0 or (amount == 0 and not allow_zero):
        raise ValueError("Enter a valid non-negative amount.")
    return amount


def split_values(value, min_count, max_count=None):
    """Split a comma-separated input into trimmed, non-empty parts."""
    max_count = max_count or min_count
    parts = [p.strip() for p in value.split(",")]
    if not (min_count <= len(parts) <= max_count) or any(p == "" for p in parts):
        raise ValueError("Unexpected number of values.")
    return parts


# ---------------- ROUNDING ----------------


def round_contribution(amount):
    """EPF-style rounding: 50 paise and above goes up to the next rupee."""
    return math.floor(amount + 0.5)


def round_esic(amount):
    """ESIC rounds any fraction of a rupee up to the next higher rupee."""
    return math.ceil(round(amount, 6))


# ---------------- PF / ESIC ----------------


def calc_pf(v):
    basic_da = parse_amount(v)
    pf_wage = min(basic_da, EPF_WAGE_CEILING)
    employee = round_contribution(pf_wage * 0.12)
    employer_total = round_contribution(pf_wage * 0.12)
    eps = round_contribution(pf_wage * 0.0833)
    epf_employer = employer_total - eps
    admin_edli = round_contribution(pf_wage * (EPF_ADMIN_RATE + EDLI_RATE))
    return (
        f"🏦 *PF Calculation (FY 2026–27)*\n"
        f"Basic+DA: ₹{basic_da:,.0f}\n"
        f"PF contribution wage (₹{EPF_WAGE_CEILING:,.0f} ceiling): "
        f"₹{pf_wage:,.0f}\n\n"
        f"*Employee*\n"
        f"Employee PF (12%): ₹{employee:,.0f}\n\n"
        f"*Employer*\n"
        f"EPS (8.33%): ₹{eps:,.0f}\n"
        f"EPF balance (3.67%): ₹{epf_employer:,.0f}\n"
        f"Total employer contribution (12%): ₹{employer_total:,.0f}\n"
        f"EPF admin + EDLI (0.5% + 0.5%): ₹{admin_edli:,.0f}\n\n"
        f"*Total PF remittance (employee + employer 12%): "
        f"₹{employee + employer_total:,.0f}*\n\n"
        f"_PF wages = Basic + DA + retaining allowance. Code on Wages ke "
        f"hisaab se Basic+DA total remuneration ka kam se kam 50% hona "
        f"chahiye. Assumes a covered EPF member and full-month wages from Oct "
        f"2026 onward. September 2026 had a mid-month ceiling change; "
        f"voluntary contributions above the statutory ceiling may differ. "
        f"EPF admin charge ka minimum ₹500 per establishment alag se lagta "
        f"hai._" + DISCLAIMER
    )


def calc_esic(v):
    gross = parse_amount(v)
    if gross > ESIC_WAGE_CEILING:
        return (
            f"🏥 *ESIC Calculation (FY 2026–27)*\n"
            f"Gross wages: ₹{gross:,.0f}\n"
            f"Gross wages monthly coverage ceiling ₹{ESIC_WAGE_CEILING:,.0f} se "
            f"upar hain — *new ESIC contribution applicable nahi*.\n\n"
            f"_Pehle se ESIC-covered employee ki wages contribution period ke "
            f"beech me ceiling cross karein to us period ke end tak "
            f"contribution jaari rehta hai._" + DISCLAIMER
        )
    emp = round_esic(gross * 0.0075)
    empr = round_esic(gross * 0.0325)
    return (
        f"🏥 *ESIC Calculation (FY 2026–27)*\n"
        f"Gross wages: ₹{gross:,.0f}\n"
        f"Employee contribution (0.75%): ₹{emp:,.0f}\n"
        f"Employer contribution (3.25%): ₹{empr:,.0f}\n"
        f"*Total contribution: ₹{emp + empr:,.0f}*\n\n"
        f"_Coverage ₹{ESIC_WAGE_CEILING:,.0f} monthly gross wages par check "
        f"hota hai (OT included). Contribution ka fraction agle rupee tak "
        f"round-up hota hai. Daily average wage ₹176 ya kam ho to employee "
        f"contribution nahi katta (sirf employer share)._" + DISCLAIMER
    )


# ---------------- CTC ----------------


def calc_ctc(v):
    ctc = parse_amount(v)
    monthly_ctc = ctc / 12
    basic = monthly_ctc * 0.40
    hra = basic * 0.50
    pf_employer = round_contribution(min(basic, EPF_WAGE_CEILING) * 0.12)
    other_allow = monthly_ctc - basic - hra - pf_employer
    return (
        f"📊 *Standard CTC Breakup (annual ₹{ctc:,.0f})*\n"
        f"Monthly CTC: ₹{monthly_ctc:,.2f}\n"
        f"Basic+DA (illustrative 40%): ₹{basic:,.2f}\n"
        f"HRA (50% of Basic): ₹{hra:,.2f}\n"
        f"Employer PF (12%, ₹{EPF_WAGE_CEILING:,.0f} ceiling): "
        f"₹{pf_employer:,.2f}\n"
        f"Other Allowances (balance): ₹{other_allow:,.2f}\n\n"
        f"_Conventional example only; this option does not enforce the new "
        f"50% wage rule. Use New Wage CTC for that calculation._" + DISCLAIMER
    )


def new_wage_components(gross, insurance_monthly=0.0):
    """All monthly components for a given whole-rupee gross under the 50% wage rule."""
    gross = int(gross)
    basic = math.ceil(gross * NEW_WAGE_BASIC_SHARE)  # Basic+DA never below 50%
    hra = round_contribution(basic * 0.50)
    special = gross - basic - hra
    pf_wage = min(basic, EPF_WAGE_CEILING)

    employee_pf = round_contribution(pf_wage * 0.12)
    employer_pf = round_contribution(pf_wage * 0.12)
    employer_eps = round_contribution(pf_wage * 0.0833)
    employer_epf = employer_pf - employer_eps
    edli_admin = round_contribution(pf_wage * (EPF_ADMIN_RATE + EDLI_RATE))

    esic_applicable = gross <= ESIC_WAGE_CEILING  # tested on gross wages
    employee_esic = round_esic(gross * 0.0075) if esic_applicable else 0
    employer_esic = round_esic(gross * 0.0325) if esic_applicable else 0

    gratuity = round_contribution(basic * GRATUITY_MONTHLY_FACTOR)
    bonus = (
        round_contribution(basic * BONUS_RATE_MIN)
        if basic <= BONUS_ELIGIBILITY_WAGE
        else 0
    )
    total_cost = (
        gross
        + employer_pf
        + edli_admin
        + employer_esic
        + gratuity
        + bonus
        + insurance_monthly
    )
    return {
        "gross": gross,
        "basic": basic,
        "hra": hra,
        "special": special,
        "pf_wage": pf_wage,
        "employee_pf": employee_pf,
        "employer_pf": employer_pf,
        "employer_eps": employer_eps,
        "employer_epf": employer_epf,
        "edli_admin": edli_admin,
        "esic_applicable": esic_applicable,
        "employee_esic": employee_esic,
        "employer_esic": employer_esic,
        "gratuity": gratuity,
        "bonus": bonus,
        "insurance": insurance_monthly,
        "total_cost": total_cost,
    }


def solve_new_wage_gross(monthly_ctc, insurance_monthly=0.0):
    """Highest whole-rupee monthly gross whose total employer cost fits the CTC.

    Employer cost drops at two thresholds (ESIC coverage ends above the ESIC
    ceiling; bonus ends when Basic+DA crosses the bonus-eligibility limit), so
    cost is not monotonic overall. It is monotonic inside each band, so each
    band is searched separately, highest band first.
    """

    def cost(g):
        return new_wage_components(g, insurance_monthly)["total_cost"]

    def highest_fit(lo, hi):
        if hi < lo or cost(lo) > monthly_ctc:
            return None
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if cost(mid) <= monthly_ctc:
                lo = mid
            else:
                hi = mid - 1
        return lo

    cliffs = sorted(
        {
            ESIC_WAGE_CEILING,
            int(BONUS_ELIGIBILITY_WAGE / NEW_WAGE_BASIC_SHARE),
        }
    )
    bands = []
    start = 1
    for cliff in cliffs:
        bands.append((start, cliff))
        start = cliff + 1
    bands.append((start, max(start, int(monthly_ctc))))

    for lo, hi in reversed(bands):
        found = highest_fit(lo, hi)
        if found is not None:
            return found
    return 1


def calc_ctc_new(v):
    parts = split_values(v, 1, 2)
    ctc = parse_amount(parts[0])
    if ctc < 50000:
        raise ValueError("Enter the ANNUAL CTC in rupees.")
    insurance_annual = parse_amount(parts[1], allow_zero=True) if len(parts) == 2 else 0.0
    if insurance_annual >= ctc * 0.5:
        raise ValueError("Insurance/benefit amount is too large for this CTC.")

    monthly_ctc = ctc / 12
    insurance_monthly = insurance_annual / 12
    gross = solve_new_wage_gross(monthly_ctc, insurance_monthly)
    c = new_wage_components(gross, insurance_monthly)

    total_employer = (
        c["employer_pf"]
        + c["edli_admin"]
        + c["employer_esic"]
        + c["gratuity"]
        + c["bonus"]
        + insurance_monthly
    )
    net_before_tds = c["gross"] - c["employee_pf"] - c["employee_esic"]
    tds = calculate_salary_tax(c["gross"] * 12, "new")["annual_tax"] / 12
    unallocated = monthly_ctc - c["total_cost"]

    lines = [
        "🆕 *New Wage CTC Breakup (FY 2026–27)*",
        f"Annual CTC: ₹{ctc:,.0f}  |  Monthly CTC: ₹{monthly_ctc:,.2f}",
        "",
        "*💰 Earnings (monthly)*",
        f"Basic+DA (≥50% of gross): ₹{c['basic']:,.0f}",
        f"HRA (illustrative, 50% of Basic): ₹{c['hra']:,.0f}",
        f"Special/Other allowance: ₹{c['special']:,.0f}",
        f"*Gross remuneration: ₹{c['gross']:,.0f}*",
        "",
        "*🏢 Employer cost (monthly)*",
        f"EPF total 12%: ₹{c['employer_pf']:,.0f} "
        f"(EPS ₹{c['employer_eps']:,.0f} + EPF ₹{c['employer_epf']:,.0f})",
        f"EPF admin + EDLI (0.5% + 0.5%): ₹{c['edli_admin']:,.0f}",
    ]
    if c["esic_applicable"]:
        lines.append(f"ESIC 3.25%: ₹{c['employer_esic']:,.0f}")
    else:
        lines.append(f"ESIC: ₹0 (gross above ₹{ESIC_WAGE_CEILING:,.0f})")
    lines.append(f"Gratuity provision (4.81% of Basic): ₹{c['gratuity']:,.0f}")
    if c["bonus"]:
        lines.append(f"Statutory bonus provision (8.33% min): ₹{c['bonus']:,.0f}")
    else:
        lines.append(
            f"Statutory bonus: not applicable (Basic+DA above "
            f"₹{BONUS_ELIGIBILITY_WAGE:,.0f})"
        )
    if insurance_monthly:
        lines.append(f"Insurance/other benefits: ₹{insurance_monthly:,.0f}")
    lines += [
        f"Total employer-side: ₹{total_employer:,.0f}",
        f"CTC check (gross + employer-side): ₹{c['total_cost']:,.0f}"
        + (f" (rounding balance ₹{unallocated:,.0f})" if unallocated >= 1 else ""),
        "",
        "*👤 Employee deductions (monthly)*",
        f"Employee PF 12%: ₹{c['employee_pf']:,.0f}",
        (
            f"Employee ESIC 0.75%: ₹{c['employee_esic']:,.0f}"
            if c["esic_applicable"]
            else "Employee ESIC: ₹0"
        ),
        f"*Net before TDS/PT: ₹{net_before_tds:,.0f}*",
        f"Est. TDS (new regime, avg): ₹{tds:,.0f}",
        f"*Est. in-hand after TDS: ₹{net_before_tds - tds:,.0f}*",
        "",
        "_Annual view: "
        f"Gross ₹{c['gross'] * 12:,.0f} + employer-side ₹{total_employer * 12:,.0f}. "
        "Professional Tax and LWF are state-specific and not included. Bonus is "
        "shown at the statutory minimum on actual Basic+DA (the Bonus Act "
        "calculation ceiling of ₹7,000 / state minimum wage may reduce it). "
        "Companies that pay variable pay, NPS, meal/LTA or other benefits will "
        "have a different split._",
    ]
    return "\n".join(lines) + DISCLAIMER


# ---------------- TAX ----------------


def calc_regime(v):
    parts = split_values(v, 2)
    gross = parse_amount(parts[0])
    deductions = parse_amount(parts[1], allow_zero=True)
    new = calculate_salary_tax(gross, "new")
    old = calculate_salary_tax(gross, "old", deductions)
    new_tax, old_tax = new["annual_tax"], old["annual_tax"]

    # Smallest old-regime deduction total at which Old tax <= New tax.
    def old_tax_with(d):
        return calculate_salary_tax(gross, "old", d)["annual_tax"]

    if old_tax_with(0) <= new_tax:
        breakeven = 0.0
    else:
        lo, hi = 0.0, gross
        for _ in range(50):
            mid = (lo + hi) / 2
            if old_tax_with(mid) <= new_tax:
                hi = mid
            else:
                lo = mid
        breakeven = math.ceil(hi / 1000) * 1000

    diff = abs(new_tax - old_tax)
    if diff < 1:
        verdict = "✅ Dono regime me tax lagbhag same hai."
    elif new_tax < old_tax:
        verdict = f"✅ *New regime better* — ₹{diff:,.0f}/year bachega."
    else:
        verdict = f"✅ *Old regime better* — ₹{diff:,.0f}/year bachega."

    result = (
        f"🧮 *Old vs New Regime — FY 2026–27*\n"
        f"Annual gross: ₹{gross:,.0f}\n\n"
        f"*New regime*\n"
        f"Taxable: ₹{new['taxable_income']:,.0f}\n"
        f"Tax: ₹{new_tax:,.0f} (≈ ₹{new_tax / 12:,.0f}/month)\n\n"
        f"*Old regime* (std ₹50,000 + deductions ₹{deductions:,.0f})\n"
        f"Taxable: ₹{old['taxable_income']:,.0f}\n"
        f"Tax: ₹{old_tax:,.0f} (≈ ₹{old_tax / 12:,.0f}/month)\n\n"
        f"{verdict}\n"
    )
    if breakeven > 0:
        result += (
            f"Old regime ko jeetne ke liye total deductions/exemptions kam se "
            f"kam ≈ ₹{breakeven:,.0f} chahiye.\n"
        )
    else:
        result += "Bina kisi deduction ke bhi old regime new se sasta hai.\n"
    result += (
        "\n_Assumes resident individual under 60, salary income only, 12 months. "
        "Employer NPS (80CCD(2)) can reduce taxable salary in both regimes — "
        "deduct it from gross before using this tool._"
    )
    return result + DISCLAIMER


def slab_tax(taxable_income, regime, age_band="under_60"):
    if regime == "new":
        slabs = [
            (400000, 0.00),
            (800000, 0.05),
            (1200000, 0.10),
            (1600000, 0.15),
            (2000000, 0.20),
            (2400000, 0.25),
            (float("inf"), 0.30),
        ]
    else:
        exemption_limit = {
            "under_60": 250000,
            "60_to_79": 300000,
            "80_plus": 500000,
        }.get(age_band, 250000)
        slabs = [(exemption_limit, 0.00)]
        if exemption_limit < 500000:
            slabs.append((500000, 0.05))
        slabs.extend(
            [
                (1000000, 0.20),
                (float("inf"), 0.30),
            ]
        )

    tax = 0.0
    lower = 0.0
    for upper, rate in slabs:
        amount_in_slab = max(0.0, min(taxable_income, upper) - lower)
        tax += amount_in_slab * rate
        if taxable_income <= upper:
            break
        lower = upper
    return tax


def tax_after_rebate(taxable_income, regime, age_band="under_60"):
    tax = slab_tax(taxable_income, regime, age_band)
    if regime == "new":
        if taxable_income <= 1200000:
            return max(0.0, tax - 60000)
        # Marginal relief just above ₹12 lakh of taxable income.
        return min(tax, taxable_income - 1200000)
    if taxable_income <= 500000:
        return max(0.0, tax - 12500)
    return tax


def tax_with_surcharge(taxable_income, regime, age_band="under_60"):
    tax = tax_after_rebate(taxable_income, regime, age_band)
    if regime == "new":
        surcharge_bands = [
            (5000000, 0.10),
            (10000000, 0.15),
            (20000000, 0.25),
        ]
    else:
        surcharge_bands = [
            (5000000, 0.10),
            (10000000, 0.15),
            (20000000, 0.25),
            (50000000, 0.37),
        ]

    selected_threshold = None
    previous_rate = 0.0
    selected_rate = 0.0
    for threshold, rate in surcharge_bands:
        if taxable_income > threshold:
            selected_threshold = threshold
            previous_rate = selected_rate
            selected_rate = rate
        else:
            break

    if selected_threshold is None:
        return tax

    with_surcharge = tax * (1 + selected_rate)
    threshold_tax = tax_after_rebate(selected_threshold, regime, age_band)
    marginal_relief_cap = (
        threshold_tax * (1 + previous_rate) + taxable_income - selected_threshold
    )
    return min(with_surcharge, marginal_relief_cap)


def calculate_salary_tax(annual_gross, regime, old_deductions=0, age_band="under_60"):
    standard_deduction = 75000 if regime == "new" else 50000
    other_deductions = old_deductions if regime == "old" else 0
    taxable_income = max(0.0, annual_gross - standard_deduction - other_deductions)
    tax_before_cess = tax_with_surcharge(taxable_income, regime, age_band)
    cess = tax_before_cess * 0.04
    return {
        "annual_gross": annual_gross,
        "standard_deduction": standard_deduction,
        "other_deductions": other_deductions,
        "taxable_income": taxable_income,
        "annual_tax": tax_before_cess + cess,
        "age_band": age_band,
    }


AGE_TEXT = {
    "under_60": "under 60",
    "60_to_79": "60–79",
    "80_plus": "80+",
}


def build_tds_result(annual_gross, regime, old_deductions=0, age_band="under_60"):
    tax = calculate_salary_tax(annual_gross, regime, old_deductions, age_band)
    regime_name = "New" if regime == "new" else "Old"
    age_text = AGE_TEXT[age_band]
    result = (
        f"🧾 *TDS Estimate — {regime_name} Regime (FY 2026–27)*\n"
        f"Annual gross salary: ₹{tax['annual_gross']:,.0f}\n"
        f"Standard deduction: ₹{tax['standard_deduction']:,.0f}\n"
    )
    if regime == "old":
        result += (
            f"Other eligible deductions/exemptions entered: "
            f"₹{tax['other_deductions']:,.0f}\n"
        )
    result += (
        f"Estimated taxable salary: ₹{tax['taxable_income']:,.0f}\n"
        f"Estimated annual tax (rebate, marginal relief, surcharge and "
        f"4% cess included): "
        f"₹{tax['annual_tax']:,.0f}\n"
        f"*Average monthly TDS: ₹{tax['annual_tax'] / 12:,.0f}*\n\n"
        f"_Assumes a resident individual age {age_text} with salary income for "
        f"12 months. For the old regime, enter only eligible deductions/"
        f"exemptions in addition to the standard deduction._" + DISCLAIMER
    )
    return result


def build_net_salary_result(
    monthly_gross, regime, old_deductions=0, age_band="under_60"
):
    # Only gross is asked; Basic+DA is taken at the 50% statutory minimum.
    basic_da = monthly_gross * NEW_WAGE_BASIC_SHARE
    pf_wage = min(basic_da, EPF_WAGE_CEILING)
    pf_employee = round_contribution(pf_wage * 0.12)
    esic_employee = (
        round_esic(monthly_gross * 0.0075) if monthly_gross <= ESIC_WAGE_CEILING else 0
    )
    tax = calculate_salary_tax(monthly_gross * 12, regime, old_deductions, age_band)
    monthly_tds = tax["annual_tax"] / 12
    net = monthly_gross - pf_employee - esic_employee - monthly_tds
    regime_name = "New" if regime == "new" else "Old"
    age_text = AGE_TEXT[age_band]
    esic_line = (
        f"ESIC employee contribution (0.75%): ₹{esic_employee:,.0f}"
        if esic_employee
        else f"ESIC: not applicable (gross above ₹{ESIC_WAGE_CEILING:,.0f})"
    )
    old_deduction_line = (
        f"\nOld-regime deductions/exemptions: ₹{old_deductions:,.0f}"
        if regime == "old"
        else ""
    )
    return (
        f"💵 *Net Salary Estimate — {regime_name} Regime*\n"
        f"Monthly gross salary: ₹{monthly_gross:,.0f}\n"
        f"Basic+DA (assumed 50% of gross): ₹{basic_da:,.0f}\n"
        f"Employee PF (12%): ₹{pf_employee:,.0f}\n"
        f"{esic_line}\n"
        f"Taxable annual salary: ₹{tax['taxable_income']:,.0f}"
        f"{old_deduction_line}\n"
        f"Average monthly TDS: ₹{monthly_tds:,.0f}\n"
        f"Professional Tax: not included (state-specific)\n"
        f"*Estimated monthly net pay: ₹{net:,.0f}*\n\n"
        f"_PF is worked out on Basic+DA assumed at 50% of gross; if your actual "
        f"Basic+DA is higher, PF will be higher (up to the ₹{EPF_WAGE_CEILING:,.0f} "
        f"wage ceiling). TDS includes the regime's standard deduction, applicable "
        f"rebate, marginal relief, surcharge and 4% cess. Assumes a resident "
        f"individual age {age_text}, salary income for 12 months, and no other "
        f"income._" + DISCLAIMER
    )


# ---------------- OTHER BENEFITS ----------------


def calc_gratuity(v):
    parts = split_values(v, 2)
    basic = parse_amount(parts[0])
    years = parse_amount(parts[1], allow_zero=True)
    if years < 5:
        return (
            f"Years of service ({years:g}) < 5 — generally *not eligible* "
            f"for gratuity (death/disablement me 5 saal ki shart nahi; fixed-term "
            f"employee ko new codes me 1 saal ke baad eligibility)." + DISCLAIMER
        )
    # Service beyond 6 months in the last year counts as a full year.
    whole = math.floor(years)
    counted_years = whole + (1 if years - whole > 0.5 else 0)
    gratuity = (basic * 15 * counted_years) / 26
    capped = min(gratuity, GRATUITY_CAP)
    cap_note = (
        f"\n⚠️ Statutory ceiling ₹{GRATUITY_CAP:,.0f} lagu hua "
        f"(calculated ₹{gratuity:,.2f})."
        if gratuity > GRATUITY_CAP
        else ""
    )
    return (
        f"🎁 *Gratuity Calculation*\n"
        f"Last drawn Basic+DA: ₹{basic:,.0f}\n"
        f"Service entered: {years:g} years → counted as {counted_years} years\n"
        f"Formula: Basic+DA × 15 × years ÷ 26\n"
        f"*Gratuity amount: ₹{capped:,.2f}*{cap_note}\n\n"
        f"_Establishments not covered by the 26-day formula (seasonal) use "
        f"7 days per season. Check your employer's applicable policy._" + DISCLAIMER
    )


def calc_bonus(v):
    parts = split_values(v, 1, 2)
    wage = parse_amount(parts[0])
    min_wage = parse_amount(parts[1]) if len(parts) == 2 else 0.0
    if wage > BONUS_ELIGIBILITY_WAGE:
        return (
            f"Basic+DA ₹{wage:,.0f} > ₹{BONUS_ELIGIBILITY_WAGE:,.0f} — "
            f"*statutory bonus ke liye eligible nahi*." + DISCLAIMER
        )
    ceiling = max(BONUS_CALC_CEILING, min_wage)
    calc_wage = min(wage, ceiling)
    min_bonus = calc_wage * 12 * 0.0833
    max_bonus = calc_wage * 12 * 0.20
    return (
        f"🎯 *Statutory Bonus (annual)*\n"
        f"Monthly Basic+DA: ₹{wage:,.0f}\n"
        f"Calculation wage (ceiling ₹{ceiling:,.0f}): ₹{calc_wage:,.0f}\n"
        f"Minimum bonus (8.33%): ₹{min_bonus:,.2f}\n"
        f"Maximum bonus (20%): ₹{max_bonus:,.2f}\n\n"
        f"_Eligibility: Basic+DA ₹{BONUS_ELIGIBILITY_WAGE:,.0f} tak aur saal me "
        f"kam se kam 30 working days. Bonus ₹{BONUS_CALC_CEILING:,.0f} ya state "
        f"minimum wage (jo zyada ho) tak ke wage par nikalta hai. Pro-rata bonus "
        f"ke liye working months ke hisaab se adjust karein._" + DISCLAIMER
    )


def calc_leave(v):
    parts = split_values(v, 2)
    monthly_basic = parse_amount(parts[0])
    days = parse_amount(parts[1], allow_zero=True)
    per_day = monthly_basic / 30
    amount = per_day * days
    return (
        f"🏖 *Leave Encashment*\n"
        f"Monthly Basic+DA: ₹{monthly_basic:,.2f}\n"
        f"Per day rate (Basic+DA ÷ 30): ₹{per_day:,.2f}\n"
        f"EL days to encash: {days:g}\n"
        f"*Encashment amount: ₹{amount:,.2f}*\n\n"
        f"_Uses the 30-day divisor. Some employers use 26 days or actual "
        f"calendar days, so follow your company leave policy. Retirement/"
        f"resignation par tax treatment alag hota hai (Sec 10(10AA))._"
        + DISCLAIMER
    )


def calc_ot(v):
    parts = split_values(v, 2)
    basic_da = parse_amount(parts[0])
    hours = parse_amount(parts[1], allow_zero=True)
    hourly = basic_da / (OT_DIVISOR_DAYS * OT_HOURS_PER_DAY)
    amount = hourly * 2 * hours
    return (
        f"⏰ *Overtime Pay*\n"
        f"Monthly Basic+DA: ₹{basic_da:,.2f}\n"
        f"Ordinary hourly rate (÷ {OT_DIVISOR_DAYS} days ÷ {OT_HOURS_PER_DAY} hrs): "
        f"₹{hourly:,.2f}\n"
        f"Overtime hours: {hours:g}\n"
        f"Rate applied: 2x ordinary rate (₹{hourly * 2:,.2f}/hr)\n"
        f"*Overtime pay: ₹{amount:,.2f}*\n\n"
        f"_OT par PF nahi katta; ESIC wages me OT included hota hai. Divisor "
        f"(26 ya 30 din) aur OT limits state rules / company policy ke hisaab "
        f"se alag ho sakte hain._" + DISCLAIMER
    )


CALC_FUNCS = {
    "calc_pf": calc_pf,
    "calc_esic": calc_esic,
    "calc_ctc": calc_ctc,
    "calc_ctc_new": calc_ctc_new,
    "calc_regime": calc_regime,
    "calc_gratuity": calc_gratuity,
    "calc_bonus": calc_bonus,
    "calc_leave": calc_leave,
    "calc_ot": calc_ot,
}


def tax_regime_keyboard():
    return InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton(
                    "New regime (default)", callback_data="taxreg_new"
                ),
                InlineKeyboardButton("Old regime", callback_data="taxreg_old"),
            ]
        ]
    )


def old_regime_age_keyboard():
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("Under 60", callback_data="taxage_under_60")],
            [InlineKeyboardButton("60–79", callback_data="taxage_60_to_79")],
            [InlineKeyboardButton("80+", callback_data="taxage_80_plus")],
        ]
    )


def clear_calc_state(context):
    for key in (
        "calc",
        "calc_data",
        "calc_step",
        "tax_regime",
        "tax_age_band",
    ):
        context.user_data.pop(key, None)


def build_selected_calculation(context, regime, old_deductions=0):
    key = context.user_data.get("calc")
    data = context.user_data.get("calc_data", {})
    age_band = context.user_data.get("tax_age_band", "under_60")
    if key == "calc_tds":
        return build_tds_result(data["annual_gross"], regime, old_deductions, age_band)
    if key == "calc_salary":
        return build_net_salary_result(
            data["monthly_gross"],
            regime,
            old_deductions,
            age_band,
        )
    raise ValueError("Calculator session expired.")


async def receive_amount(update: Update, context: ContextTypes.DEFAULT_TYPE):
    key = context.user_data.get("calc")
    value = update.message.text.strip()
    if key not in CALC_PROMPTS:
        await update.message.reply_text(
            "Calculator session expired. /start karke calculator dobara chuno."
        )
        return ConversationHandler.END
    try:
        if key == "calc_salary":
            monthly_gross = parse_amount(value)
            context.user_data["calc_data"] = {"monthly_gross": monthly_gross}
            context.user_data["calc_step"] = "tax_regime"
            await update.message.reply_text(
                "TDS ke liye tax regime chuno:",
                reply_markup=tax_regime_keyboard(),
            )
            return TAX_REGIME

        if key == "calc_tds":
            annual_gross = parse_amount(value)
            context.user_data["calc_data"] = {"annual_gross": annual_gross}
            context.user_data["calc_step"] = "tax_regime"
            await update.message.reply_text(
                "FY 2026–27 ke liye tax regime chuno:",
                reply_markup=tax_regime_keyboard(),
            )
            return TAX_REGIME

        result = CALC_FUNCS[key](value)
    except (ValueError, TypeError, OverflowError):
        await update.message.reply_text(
            "⚠️ Input sahi format me bhejo.\n\n" + CALC_PROMPTS[key],
            parse_mode="Markdown",
        )
        return AMOUNT
    clear_calc_state(context)
    await update.message.reply_text(result, parse_mode="Markdown")
    return ConversationHandler.END


async def select_tax_regime(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    regime = query.data.rsplit("_", 1)[1]
    if not context.user_data.get("calc_data"):
        clear_calc_state(context)
        await query.message.reply_text(
            "Calculator session expired. /start karke dobara chuno."
        )
        return ConversationHandler.END

    context.user_data["tax_regime"] = regime
    if regime == "old":
        context.user_data["calc_step"] = "old_age"
        await query.message.reply_text(
            "Old regime ke liye age group chuno:",
            reply_markup=old_regime_age_keyboard(),
        )
        return OLD_AGE

    result = build_selected_calculation(context, regime)
    clear_calc_state(context)
    await query.message.reply_text(result, parse_mode="Markdown")
    return ConversationHandler.END


async def select_old_regime_age(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    age_band = query.data.removeprefix("taxage_")
    if age_band not in AGE_TEXT:
        return OLD_AGE
    context.user_data["tax_age_band"] = age_band
    context.user_data["calc_step"] = "old_deductions"
    await query.message.reply_text(
        "Standard deduction ke alawa total *eligible annual "
        "deductions/exemptions* bhejo (jaise eligible 80C, 80D, HRA; "
        "₹50,000 standard deduction alag se apply hogi). "
        "Koi deduction nahi ho to `0` bhejo:",
        parse_mode="Markdown",
    )
    return OLD_DEDUCTIONS


async def receive_old_deductions(update: Update, context: ContextTypes.DEFAULT_TYPE):
    try:
        deductions = parse_amount(update.message.text, allow_zero=True)
        result = build_selected_calculation(context, "old", deductions)
    except (ValueError, TypeError, OverflowError, KeyError):
        await update.message.reply_text(
            "⚠️ Eligible annual deductions/exemptions ka valid number bhejo, "
            "ya kuch nahi ho to `0`.",
            parse_mode="Markdown",
        )
        return OLD_DEDUCTIONS
    clear_calc_state(context)
    await update.message.reply_text(result, parse_mode="Markdown")
    return ConversationHandler.END


async def remind_tax_regime(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text("Old ya New regime ke button ko tap karo.")
    return TAX_REGIME


async def remind_old_regime_age(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text("Age group ke button ko tap karo.")
    return OLD_AGE


async def pending_amount_fallback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if (
        context.user_data.get("calc_step") == "amount"
        and context.user_data.get("calc") in CALC_PROMPTS
    ):
        return await receive_amount(update, context)


async def cancel(update: Update, context: ContextTypes.DEFAULT_TYPE):
    clear_calc_state(context)
    await update.message.reply_text("Cancelled. /start se dobara shuru karo.")
    return ConversationHandler.END


async def restart_conversation(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await start(update, context)
    return ConversationHandler.END


# ---------------- DAILY UPDATES (news feed + subscriptions) ----------------


def load_json(path, default):
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError, OSError):
        return default


def save_json(path, data):
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        tmp = path.with_suffix(".tmp")
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False)
        os.replace(tmp, path)
    except OSError:
        logger.exception("Could not save %s", path)


def get_subscribers():
    return set(load_json(SUBSCRIBERS_FILE, []))


def subscribe_keyboard(chat_id):
    subscribed = chat_id in get_subscribers()
    label = (
        "🔕 Daily alerts band karo" if subscribed else "🔔 Daily alerts chalu karo"
    )
    return InlineKeyboardMarkup(
        [[InlineKeyboardButton(label, callback_data="info_subscribe")]]
    )


async def toggle_subscription(update, context, force=None):
    """force: 'on', 'off' or None (toggle)."""
    chat_id = update.effective_chat.id
    subs = get_subscribers()
    turn_on = (chat_id not in subs) if force is None else (force == "on")
    if turn_on:
        subs.add(chat_id)
        text = (
            f"🔔 Daily alerts *ON*. Roz subah {DAILY_UPDATE_HOUR_IST}:00 IST par "
            "labour code/compliance headlines aur upcoming due dates milenge. "
            "Band karne ke liye /unsubscribe."
        )
    else:
        subs.discard(chat_id)
        text = "🔕 Daily alerts *OFF*. Dobara chalu karne ke liye /subscribe."
    save_json(SUBSCRIBERS_FILE, sorted(subs))
    await get_message(update).reply_text(text, parse_mode="Markdown")


async def subscribe_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await toggle_subscription(update, context, force="on")


async def unsubscribe_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await toggle_subscription(update, context, force="off")


async def fetch_news_query(client, query):
    url = (
        "https://news.google.com/rss/search?q="
        + quote_plus(query + " when:7d")
        + "&hl=en-IN&gl=IN&ceid=IN:en"
    )
    resp = await client.get(url)
    resp.raise_for_status()
    root = ET.fromstring(resp.content)
    items = []
    for it in root.iter("item"):
        title = (it.findtext("title") or "").strip()
        link = (it.findtext("link") or "").strip()
        if not title or not link:
            continue
        try:
            published = parsedate_to_datetime(it.findtext("pubDate")).astimezone(
                timezone.utc
            )
        except (TypeError, ValueError):
            published = datetime.now(timezone.utc)
        items.append(
            {
                "title": title,
                "link": link,
                "source": (it.findtext("source") or "").strip(),
                "published": published.isoformat(),
            }
        )
    return items[:6]


async def refresh_updates(force=False):
    cache = load_json(UPDATES_CACHE_FILE, {})
    fetched_at = cache.get("fetched_at")
    if not force and fetched_at:
        age = datetime.now(timezone.utc) - datetime.fromisoformat(fetched_at)
        if age < timedelta(hours=UPDATES_CACHE_TTL_HOURS):
            return cache

    try:
        async with httpx.AsyncClient(timeout=15, follow_redirects=True) as client:
            results = await asyncio.gather(
                *(fetch_news_query(client, q) for q in UPDATE_QUERIES),
                return_exceptions=True,
            )
    except Exception:
        logger.exception("Updates fetch failed")
        return cache

    merged, seen = [], set()
    for res in results:
        if isinstance(res, Exception):
            logger.warning("News query failed: %s", res)
            continue
        for item in res:
            key = item["title"].lower()
            if key not in seen:
                seen.add(key)
                merged.append(item)
    if not merged:
        return cache  # keep whatever we had

    merged.sort(key=lambda i: i["published"], reverse=True)
    cache["items"] = merged[:MAX_UPDATE_ITEMS]
    cache["fetched_at"] = datetime.now(timezone.utc).isoformat()
    save_json(UPDATES_CACHE_FILE, cache)
    return cache


def format_news_items(items, limit=8):
    lines = []
    for it in items[:limit]:
        title = html.escape(it["title"])
        link = html.escape(it["link"], quote=True)
        source = html.escape(it.get("source") or "news")
        day = datetime.fromisoformat(it["published"]).astimezone(IST).strftime("%d %b")
        lines.append(f'• <a href="{link}">{title}</a> — {source}, {day}')
    return "\n".join(lines)


def upcoming_deadlines(today=None, window_days=10):
    """Recurring due dates falling in the next `window_days` days."""
    today = today or datetime.now(IST).date()
    due = []
    for offset in range(window_days + 1):
        d = today + timedelta(days=offset)
        label = "today" if offset == 0 else f"in {offset}d"
        stamp = f"{d.strftime('%d %b')} ({label})"
        if d.day == 7:
            due.append(f"{stamp}: Salary processing, pay slips, TDS deposit (24Q)")
        if d.day == 15:
            due.append(f"{stamp}: EPF & ESIC payment")
        if (d.month, d.day) in {(7, 31), (10, 31), (1, 31), (5, 31)}:
            due.append(f"{stamp}: TDS 24Q quarterly return")
        if (d.month, d.day) == (6, 15):
            due.append(f"{stamp}: Form 16 to employees")
    return due


async def build_updates_message():
    cache = await refresh_updates()
    items = cache.get("items", [])
    text = (
        "📰 <b>Payroll &amp; Compliance Updates</b>\n\n"
        "<b>Labour Codes:</b> 4 Labour Codes (Wages, IR, Social Security, OSH) "
        "21 Nov 2025 se national level par lagu hain. States apne rules "
        "phase-wise la rahe hain — apne state labour department ka status "
        "check karo.\n\n"
    )
    due = upcoming_deadlines()
    if due:
        text += (
            "<b>⏳ Upcoming due dates</b>\n"
            + "\n".join("• " + html.escape(d) for d in due)
            + "\n\n"
        )
    if items:
        fetched = datetime.fromisoformat(cache["fetched_at"]).astimezone(IST)
        text += (
            f"<b>🗞 Latest headlines</b> (updated {fetched.strftime('%d %b, %H:%M')} IST)\n"
            + format_news_items(items)
            + "\n\n<i>Headlines news feeds se auto-fetch hoti hain — official "
            "notification/circular se verify karke hi payroll me apply karo.</i>\n\n"
        )
    else:
        text += "<i>Abhi live headlines fetch nahi ho payi. Thodi der baad try karo.</i>\n\n"
    text += (
        "<b>Official sources:</b> labour.gov.in • epfindia.gov.in • esic.gov.in • "
        "incometax.gov.in\n" + html.escape(DISCLAIMER.strip())
    )
    return text[:4000]


async def broadcast_daily(app):
    subs = get_subscribers()
    if not subs:
        return
    cache = await refresh_updates(force=True)
    items = cache.get("items", [])
    sent_ids = set(cache.get("broadcast_ids", []))
    cutoff = datetime.now(timezone.utc) - timedelta(days=2)
    new_items = [
        i
        for i in items
        if i["link"] not in sent_ids
        and datetime.fromisoformat(i["published"]) >= cutoff
    ]

    today = datetime.now(IST)
    text = f"🔔 <b>Daily Payroll &amp; Compliance Update — {today.strftime('%d %b %Y')}</b>\n\n"
    due = upcoming_deadlines(today.date())
    if due:
        text += (
            "<b>⏳ Upcoming due dates</b>\n"
            + "\n".join("• " + html.escape(d) for d in due)
            + "\n\n"
        )
    if new_items:
        text += "<b>🗞 Naye headlines</b>\n" + format_news_items(new_items) + "\n\n"
    else:
        text += "Aaj labour code/compliance ke koi naye headlines nahi mile.\n\n"
    text += "<i>Official notification se verify karo. /updates se poori list dekho.</i>"
    text = text[:4000]

    for chat_id in list(subs):
        try:
            kwargs = {"parse_mode": "HTML"}
            if LinkPreviewOptions is not None:
                kwargs["link_preview_options"] = LinkPreviewOptions(is_disabled=True)
            else:
                kwargs["disable_web_page_preview"] = True
            await app.bot.send_message(chat_id=chat_id, text=text, **kwargs)
        except (Forbidden, BadRequest):
            subs.discard(chat_id)  # blocked the bot / chat gone
        except Exception:
            logger.exception("Broadcast to %s failed", chat_id)
        await asyncio.sleep(0.05)  # stay under Telegram rate limits

    save_json(SUBSCRIBERS_FILE, sorted(subs))
    cache["broadcast_ids"] = [i["link"] for i in items]
    save_json(UPDATES_CACHE_FILE, cache)


async def daily_loop(app):
    while True:
        now = datetime.now(IST)
        target = now.replace(
            hour=DAILY_UPDATE_HOUR_IST, minute=0, second=0, microsecond=0
        )
        if target <= now:
            target += timedelta(days=1)
        await asyncio.sleep((target - now).total_seconds())
        try:
            await broadcast_daily(app)
        except Exception:
            logger.exception("Daily broadcast failed")


async def post_init(app):
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    app.bot_data["daily_task"] = asyncio.create_task(daily_loop(app))


async def post_shutdown(app):
    task = app.bot_data.get("daily_task")
    if task:
        task.cancel()


# ---------------- AFTER-HOURS NOTICE ----------------


def is_office_hours(now=None):
    now = now or datetime.now(IST)
    return OFFICE_START_HOUR <= now.hour < OFFICE_END_HOUR


async def after_hours_notice(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Runs before every other handler (group -1); never blocks them."""
    if is_office_hours() or not update.effective_chat:
        return
    # Only react to real user actions (messages / button taps)
    if not (update.message or update.callback_query):
        return
    last = context.user_data.get("after_hours_notice_at")
    now = datetime.now(timezone.utc)
    if last and now - datetime.fromisoformat(last) < timedelta(
        hours=AFTER_HOURS_NOTICE_GAP_HOURS
    ):
        return
    context.user_data["after_hours_notice_at"] = now.isoformat()
    try:
        await context.bot.send_message(
            chat_id=update.effective_chat.id,
            text=(
                f"🕙 Hamari support timing {OFFICE_START_HOUR % 12 or 12}:00 AM – "
                f"{OFFICE_END_HOUR % 12 or 12}:00 PM (IST) hai. Is time ke baad "
                "message karne par reply late aa sakta hai. Calculators phir bhi "
                "kaam karte rahenge."
            ),
        )
    except Exception:
        logger.exception("After-hours notice failed")


# ---------------- ROUTER ----------------


async def route(key, update, context, via_button):
    if key in CALC_PROMPTS:
        return await calc_entry(key, update, context, via_button)
    elif key == "info_subscribe":
        await toggle_subscription(update, context)
        return ConversationHandler.END
    elif key in INFO_TEXT:
        await send_info(key, update, context, via_button)
        return ConversationHandler.END
    # Old/removed menu buttons (e.g. from earlier chats) land here.
    await get_message(update).reply_text(
        "Yeh option ab available nahi hai. /start se naya menu kholiye."
    )
    return ConversationHandler.END


# Direct command versions (e.g. /pf) also open the same calculator flow
async def direct_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    cmd = update.message.text.split()[0][1:].split("@")[0]  # strip "/" and @botname
    key = f"calc_{cmd}"
    if key in CALC_PROMPTS:
        return await calc_entry(key, update, context, via_button=False)
    info_key = f"info_{cmd}"
    if info_key in INFO_TEXT:
        await send_info(info_key, update, context, via_button=False)
        return ConversationHandler.END
    return ConversationHandler.END


async def unknown(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(
        "Sorry, samajh nahi aaya. /start karke menu se try karo, ya /help dekho."
    )


def main():
    if not BOT_TOKEN:
        raise RuntimeError("BOT_TOKEN not set. Add it in Replit Secrets.")

    app = (
        ApplicationBuilder()
        .token(BOT_TOKEN)
        .post_init(post_init)
        .post_shutdown(post_shutdown)
        .build()
    )

    calc_commands = [
        "pf",
        "esic",
        "ctc",
        "ctc_new",
        "regime",
        "salary",
        "gratuity",
        "bonus",
        "tds",
        "leave",
        "ot",
    ]
    info_commands = ["compliance", "updates", "taxsave"]

    conv = ConversationHandler(
        entry_points=(
            [CallbackQueryHandler(menu_callback, pattern="^(calc_|info_)")]
            + [CommandHandler(c, direct_command) for c in calc_commands]
        ),
        states={
            AMOUNT: [MessageHandler(filters.TEXT & ~filters.COMMAND, receive_amount)],
            TAX_REGIME: [
                CallbackQueryHandler(select_tax_regime, pattern="^taxreg_(new|old)$"),
                MessageHandler(filters.TEXT & ~filters.COMMAND, remind_tax_regime),
            ],
            OLD_AGE: [
                CallbackQueryHandler(
                    select_old_regime_age,
                    pattern="^taxage_(under_60|60_to_79|80_plus)$",
                ),
                MessageHandler(filters.TEXT & ~filters.COMMAND, remind_old_regime_age),
            ],
            OLD_DEDUCTIONS: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_old_deductions)
            ],
        },
        fallbacks=[
            CommandHandler("cancel", cancel),
            CommandHandler("start", restart_conversation),
        ],
        allow_reentry=True,
    )

    app.add_handler(TypeHandler(Update, after_hours_notice), group=-1)
    app.add_handler(conv)
    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("help", help_cmd))
    app.add_handler(CommandHandler("cancel", cancel))
    app.add_handler(CommandHandler("subscribe", subscribe_cmd))
    app.add_handler(CommandHandler("unsubscribe", unsubscribe_cmd))
    for c in info_commands:
        app.add_handler(CommandHandler(c, direct_command))
    app.add_handler(
        MessageHandler(filters.TEXT & ~filters.COMMAND, pending_amount_fallback)
    )
    app.add_handler(MessageHandler(filters.COMMAND, unknown))

    print("Bot is running...")
    app.run_polling()


if __name__ == "__main__":
    main()
