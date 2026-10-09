import os
import asyncio
import hashlib
import html
import json
import logging
import math
import xml.etree.ElementTree as ET
from contextlib import asynccontextmanager
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from pathlib import Path
from urllib.parse import quote, quote_plus

import httpx
import uvicorn
from starlette.applications import Starlette
from starlette.requests import Request
from starlette.responses import PlainTextResponse
from starlette.routing import Route
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.error import Forbidden, BadRequest
from telegram.ext import (
    ApplicationBuilder,
    BasePersistence,
    CommandHandler,
    MessageHandler,
    CallbackQueryHandler,
    ConversationHandler,
    ContextTypes,
    PersistenceInput,
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

# Comma-separated Telegram user IDs allowed to run /setwage (set in Replit Secrets)
ADMIN_IDS = {
    int(x) for x in os.environ.get("ADMIN_IDS", "").split(",") if x.strip().isdigit()
}

YOUTUBE_URL = "https://www.youtube.com/@PayrollPathIndia"

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

EPF_WAGE_CEILING = 25000
ESIC_WAGE_CEILING = 21000

# New-wage CTC components (employer side)
EPF_ADMIN_RATE = 0.005  # EPF admin charges
EDLI_RATE = 0.005  # EDLI contribution
GRATUITY_MONTHLY_FACTOR = 15 / 26 / 12  # 15 days wages per year, accrued monthly
BONUS_RATE_MIN = 0.0833  # statutory minimum bonus
BONUS_ELIGIBILITY_WAGE = 21000

IST = timezone(timedelta(hours=5, minutes=30))

# ---------------- STORAGE ----------------
# Autoscale ka filesystem/memory persist nahi hota. Isliye Replit Database
# (REPLIT_DB_URL) use hota hai. Agar wo env var na ho to local files use hongi.
DATA_DIR = Path(os.environ.get("DATA_DIR", "bot_data"))
SUBSCRIBERS_FILE = DATA_DIR / "subscribers.json"
UPDATES_CACHE_FILE = DATA_DIR / "updates_cache.json"
MINWAGE_FILE = DATA_DIR / "minimum_wages.json"
USERDATA_FILE = DATA_DIR / "ptb_user_data.json"
CONVERSATIONS_FILE = DATA_DIR / "ptb_conversations.json"
UPDATES_CACHE_TTL_HOURS = 6
MAX_UPDATE_ITEMS = 30
UPDATE_QUERIES = [
    "labour codes India payroll",
    "Code on Wages rules notification",
    "EPFO circular notification",
    "ESIC notification circular",
    "TDS salary CBDT circular",
    "professional tax labour welfare fund",
]

STATES = [
    "Andhra Pradesh",
    "Arunachal Pradesh",
    "Assam",
    "Bihar",
    "Chhattisgarh",
    "Goa",
    "Gujarat",
    "Haryana",
    "Himachal Pradesh",
    "Jharkhand",
    "Karnataka",
    "Kerala",
    "Madhya Pradesh",
    "Maharashtra",
    "Manipur",
    "Meghalaya",
    "Mizoram",
    "Nagaland",
    "Odisha",
    "Punjab",
    "Rajasthan",
    "Sikkim",
    "Tamil Nadu",
    "Telangana",
    "Tripura",
    "Uttar Pradesh",
    "Uttarakhand",
    "West Bengal",
    "Delhi",
    "Jammu and Kashmir",
    "Chandigarh",
    "Puducherry",
    "Ladakh",
]


def _kv_url():
    return os.environ.get("REPLIT_DB_URL")


def load_json(path, default):
    base = _kv_url()
    if base:
        try:
            r = httpx.get(f"{base}/{quote(path.name)}", timeout=10)
            if r.status_code == 200 and r.text:
                return json.loads(r.text)
            return default
        except (httpx.HTTPError, json.JSONDecodeError):
            logger.exception("KV read failed for %s", path.name)
            return default
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError, OSError):
        return default


def save_json(path, data):
    payload = json.dumps(data, ensure_ascii=False, default=str)
    base = _kv_url()
    if base:
        try:
            httpx.post(base, data={path.name: payload}, timeout=10).raise_for_status()
        except httpx.HTTPError:
            logger.exception("KV write failed for %s", path.name)
        return
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        tmp = path.with_suffix(".tmp")
        with open(tmp, "w", encoding="utf-8") as f:
            f.write(payload)
        os.replace(tmp, path)
    except OSError:
        logger.exception("Could not save %s", path)


class StoragePersistence(BasePersistence):
    """Saves user_data + conversation states in the same storage, so a
    calculator step survives when the Autoscale instance sleeps."""

    def __init__(self):
        super().__init__(
            store_data=PersistenceInput(
                bot_data=False, chat_data=False, callback_data=False, user_data=True
            )
        )
        self._user_data = None
        self._conversations = None

    # --- user data ---
    def _load_users(self):
        if self._user_data is None:
            raw = load_json(USERDATA_FILE, {})
            self._user_data = {int(k): v for k, v in raw.items()}
        return self._user_data

    def _save_users(self):
        save_json(
            USERDATA_FILE,
            {str(k): v for k, v in self._load_users().items() if v},
        )

    async def get_user_data(self):
        return {k: dict(v) for k, v in self._load_users().items()}

    async def update_user_data(self, user_id, data):
        self._load_users()[user_id] = json.loads(json.dumps(data, default=str))
        self._save_users()

    async def refresh_user_data(self, user_id, user_data):
        pass

    async def drop_user_data(self, user_id):
        self._load_users().pop(user_id, None)
        self._save_users()

    # --- conversations ---
    def _load_convs(self):
        if self._conversations is None:
            self._conversations = load_json(CONVERSATIONS_FILE, {})
        return self._conversations

    async def get_conversations(self, name):
        out = {}
        for k, v in self._load_convs().get(name, {}).items():
            chat_id, user_id = k.split(",")
            out[(int(chat_id), int(user_id))] = v
        return out

    async def update_conversation(self, name, key, new_state):
        convs = self._load_convs().setdefault(name, {})
        k = ",".join(str(x) for x in key)
        if new_state is None:
            convs.pop(k, None)
        else:
            convs[k] = new_state
        save_json(CONVERSATIONS_FILE, self._load_convs())

    # --- unused (disabled via store_data) ---
    async def get_bot_data(self):
        return {}

    async def update_bot_data(self, data):
        pass

    async def refresh_bot_data(self, bot_data):
        pass

    async def get_chat_data(self):
        return {}

    async def update_chat_data(self, chat_id, data):
        pass

    async def refresh_chat_data(self, chat_id, chat_data):
        pass

    async def drop_chat_data(self, chat_id):
        pass

    async def get_callback_data(self):
        return None

    async def update_callback_data(self, data):
        pass

    async def flush(self):
        if self._user_data is not None:
            self._save_users()


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
            InlineKeyboardButton(
                "📆 Compliance Calendar", callback_data="info_compliance"
            ),
            InlineKeyboardButton("📰 Updates", callback_data="info_updates"),
        ],
        [
            InlineKeyboardButton("💡 Tax Saver", callback_data="info_taxsave"),
            InlineKeyboardButton("🔔 Min Wage Alerts", callback_data="info_subscribe"),
        ],
        [
            InlineKeyboardButton("📁 HR Templates", callback_data="info_templates"),
            InlineKeyboardButton("⭐ Premium", callback_data="info_premium"),
        ],
    ]
    return InlineKeyboardMarkup(buttons)


def no_preview_kwargs(kwargs=None):
    kwargs = kwargs if kwargs is not None else {}
    if LinkPreviewOptions is not None:
        kwargs["link_preview_options"] = LinkPreviewOptions(is_disabled=True)
    else:
        kwargs["disable_web_page_preview"] = True
    return kwargs


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    clear_calc_state(context)
    text = (
        "👋 *Welcome to PayrollPath India!*\n\n"
        "Your free HR & payroll compliance assistant.\n"
        "Choose a calculator or info option below:\n\n"
        "▶️ Payroll, PF, ESIC aur labour code ke videos ke liye hamara "
        f"YouTube channel subscribe karo: [PayrollPath India]({YOUTUBE_URL})"
    )
    await update.message.reply_text(
        text,
        parse_mode="Markdown",
        reply_markup=main_menu_keyboard(),
        **no_preview_kwargs(),
    )


async def help_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    text = (
        "ℹ️ *Help*\n\n"
        "Use /start to open the main menu, or type a command directly:\n"
        "/pf /esic /ctc /ctc_new /salary /gratuity /bonus /tds /leave /ot\n"
        "/regime /taxsave /compliance /updates /templates /premium\n"
        "/subscribe /unsubscribe (state minimum wage change alerts)"
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
    "info_templates": (
        "📁 *HR Templates*\n\n"
        "Coming soon: offer letters, appointment letters, payslip "
        "formats, FnF settlement templates. (This section is still "
        "being built.)"
    ),
    "info_premium": (
        "⭐ *Premium Tools*\n\n"
        "Planned premium features: bulk payroll reports, state-wise "
        "compliance tracker, auto-generated payslips. Payment system "
        "coming in a later update."
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
    no_preview_kwargs(kwargs)
    return await message.reply_text(text, parse_mode="HTML", **kwargs)


def truncate_html(text, limit=4000):
    """Cut at a line boundary so we never split an HTML tag in half."""
    if len(text) <= limit:
        return text
    cut = text[:limit]
    idx = cut.rfind("\n")
    return cut[:idx] if idx > 0 else cut


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

CALC_PROMPTS = {
    "calc_pf": (
        "Monthly *gross remuneration, Basic+DA* bhejo — comma-separated, "
        "without thousands commas (e.g. `30000,15000`):"
    ),
    "calc_esic": (
        "Monthly *gross remuneration, Basic+DA* "
        "bhejo — comma-separated, "
        "without thousands commas (e.g. `30000,15000`):"
    ),
    "calc_ctc": "Apna *Annual CTC* bhejo (sirf number, e.g. 600000):",
    "calc_ctc_new": (
        "New Wage CTC breakup ke liye apna *Annual CTC* bhejo "
        "(sirf number, e.g. `600000`).\n"
    ),
    "calc_regime": (
        "Format me bhejo: *AnnualGross,OldRegimeDeductions* — deductions me "
        "80C + 80D + NPS + HRA exemption + home loan interest etc. ka total "
        "(e.g. `1200000,350000`). Deductions nahi ho to `1200000,0`:"
    ),
    "calc_salary": (
        "Monthly *gross salary, Basic+DA* "
        "bhejo — comma-separated, "
        "without thousands commas (e.g. `30000,15000`):"
    ),
    "calc_gratuity": "Format me bhejo: *BasicDA,YearsOfService* (e.g. 20000,6):",
    "calc_bonus": "Apna *monthly wage* bhejo (sirf number, max ₹21000 tak eligible):",
    "calc_tds": (
        "Apni *annual gross salary* bhejo (before tax; standard deduction "
        "calculator apply karega, e.g. `900000`):"
    ),
    "calc_leave": ("Format me bhejo: *MonthlyBasic+DA,ELDays* (e.g. `24000,15`):"),
    "calc_ot": "Format me bhejo: *HourlyRate,OvertimeHours* (e.g. 150,10):",
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


def parse_monthly_wages(v):
    parts = v.split(",")
    if len(parts) != 2:
        raise ValueError("Enter gross remuneration and Basic+DA separated by a comma.")
    gross = float(parts[0].strip().replace("₹", ""))
    basic_da = float(parts[1].strip().replace("₹", ""))
    if not math.isfinite(gross) or not math.isfinite(basic_da):
        raise ValueError("Amounts must be finite numbers.")
    if gross <= 0 or basic_da < 0 or basic_da > gross:
        raise ValueError("Basic+DA must be between zero and gross remuneration.")
    return gross, basic_da


def code_wage_base(gross, basic_da):
    # Add back excluded allowances above 50% of total remuneration.
    return max(basic_da, gross * 0.50)


def round_contribution(amount):
    return math.floor(amount + 0.5)


def calc_pf(v):
    gross, basic_da = parse_monthly_wages(v)
    wage_base = code_wage_base(gross, basic_da)
    pf_wage = min(wage_base, EPF_WAGE_CEILING)
    emp = round_contribution(pf_wage * 0.12)
    employer_total = round_contribution(pf_wage * 0.12)
    eps = round_contribution(pf_wage * 0.0833)
    epf_employer = employer_total - eps
    return (
        f"🏦 *PF Calculation (FY 2026–27)*\n"
        f"Gross remuneration: ₹{gross:,.0f}\n"
        f"Basic+DA: ₹{basic_da:,.0f}\n"
        f"Wage base after 50% rule: ₹{wage_base:,.2f}\n"
        f"PF contribution wage (₹{EPF_WAGE_CEILING:,.0f} ceiling): "
        f"₹{pf_wage:,.2f}\n"
        f"Employee PF (12%): ₹{emp:,.0f}\n"
        f"Employer EPS (8.33%): ₹{eps:,.0f}\n"
        f"Employer EPF balance: ₹{epf_employer:,.0f}\n"
        f"Total employer contribution (12%): ₹{employer_total:,.0f}\n\n"
        f"_Assumes a covered EPF member and full-month wages from Oct 2026 "
        f"onward. September 2026 had a mid-month ceiling change; voluntary "
        f"contributions above the statutory ceiling may differ._" + DISCLAIMER
    )


def calc_esic(v):
    gross, basic_da = parse_monthly_wages(v)
    wage_base = code_wage_base(gross, basic_da)
    if wage_base > ESIC_WAGE_CEILING:
        return (
            f"🏥 *ESIC Calculation (FY 2026–27)*\n"
            f"Gross remuneration: ₹{gross:,.0f}\n"
            f"Basic+DA: ₹{basic_da:,.0f}\n"
            f"Wage base after 50% rule: ₹{wage_base:,.2f}\n"
            f"Wage base is above the ₹{ESIC_WAGE_CEILING:,.0f} monthly "
            f"coverage ceiling — *not eligible for a new ESIC contribution "
            f"estimate*." + DISCLAIMER
        )
    emp = round_contribution(wage_base * 0.0075)
    empr = round_contribution(wage_base * 0.0325)
    return (
        f"🏥 *ESIC Calculation (FY 2026–27)*\n"
        f"Gross remuneration: ₹{gross:,.0f}\n"
        f"Basic+DA: ₹{basic_da:,.0f}\n"
        f"Wage base after 50% rule: ₹{wage_base:,.2f}\n"
        f"Employee contribution (0.75%): ₹{emp:,.0f}\n"
        f"Employer contribution (3.25%): ₹{empr:,.0f}\n"
        f"Total contribution: ₹{emp + empr:,.0f}\n\n"
        f"_Eligibility uses the ₹{ESIC_WAGE_CEILING:,.0f} monthly wage "
        f"ceiling. If an already-covered employee crosses it mid-period, "
        f"continuation rules may apply._" + DISCLAIMER
    )


def calc_ctc(v):
    ctc = float(v)
    if not math.isfinite(ctc) or ctc <= 0:
        raise ValueError("CTC must be a positive number.")
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
    basic = math.ceil(gross / 2)  # Basic+DA never below 50% of remuneration
    hra = round_contribution(basic * 0.50)
    special = gross - basic - hra
    wage_base = code_wage_base(gross, basic)
    pf_wage = min(wage_base, EPF_WAGE_CEILING)

    employee_pf = round_contribution(pf_wage * 0.12)
    employer_pf = round_contribution(pf_wage * 0.12)
    employer_eps = round_contribution(pf_wage * 0.0833)
    employer_epf = employer_pf - employer_eps
    edli_admin = round_contribution(pf_wage * (EPF_ADMIN_RATE + EDLI_RATE))

    esic_applicable = wage_base <= ESIC_WAGE_CEILING
    employee_esic = round_contribution(wage_base * 0.0075) if esic_applicable else 0
    employer_esic = round_contribution(wage_base * 0.0325) if esic_applicable else 0

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
        "wage_base": wage_base,
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
    """Highest whole-rupee monthly gross whose total employer cost fits the CTC."""

    def cost(g):
        return new_wage_components(g, insurance_monthly)["total_cost"]

    esic_top = 2 * ESIC_WAGE_CEILING  # gross at which Basic+DA hits the ESIC ceiling
    if monthly_ctc <= cost(esic_top):
        lo, hi = 1, esic_top  # ESIC-covered range
    else:
        lo, hi = esic_top + 1, max(esic_top + 1, int(monthly_ctc))
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if cost(mid) <= monthly_ctc:
            lo = mid
        else:
            hi = mid - 1
    return lo


def calc_ctc_new(v):
    parts = [p.strip() for p in v.split(",")]
    if len(parts) not in (1, 2):
        raise ValueError("Enter CTC, optionally followed by annual insurance.")
    ctc = parse_annual_amount(parts[0])
    if ctc < 50000:
        raise ValueError("Enter the ANNUAL CTC in rupees.")
    insurance_annual = (
        parse_annual_amount(parts[1], allow_zero=True) if len(parts) == 2 else 0.0
    )
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
        f"🆕 *New Wage CTC Breakup (FY 2026–27)*",
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
        lines.append(f"ESIC: ₹0 (wage base above ₹{ESIC_WAGE_CEILING:,.0f})")
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
        "shown at the statutory minimum (calculation ceiling per Bonus Act/state "
        "minimum wage may apply). Companies that pay variable pay, NPS, meal/LTA "
        "or other benefits will have a different split._",
    ]
    return "\n".join(lines) + DISCLAIMER


def calc_regime(v):
    parts = v.split(",")
    if len(parts) != 2:
        raise ValueError("Enter annual gross and old-regime deductions.")
    gross = parse_annual_amount(parts[0])
    deductions = parse_annual_amount(parts[1], allow_zero=True)
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


def calc_gratuity(v):
    basic_str, years_str = v.split(",")
    basic = float(basic_str.strip())
    years = float(years_str.strip())
    if years < 5:
        return (
            f"Years of service ({years}) < 5 — generally *not eligible* "
            f"for gratuity (unless fixed-term employee under new codes)." + DISCLAIMER
        )
    gratuity = (basic * 15 * years) / 26
    return (
        f"🎁 *Gratuity Calculation*\n"
        f"Last drawn Basic+DA: ₹{basic:,.0f}\n"
        f"Years of service: {years}\n"
        f"*Gratuity amount: ₹{gratuity:,.2f}*" + DISCLAIMER
    )


def calc_bonus(v):
    wage = float(v)
    if wage > 21000:
        return (
            f"Wage ₹{wage:,.0f} > ₹21,000 — *not eligible* for statutory bonus."
            + DISCLAIMER
        )
    min_bonus = wage * 12 * 0.0833
    max_bonus = wage * 12 * 0.20
    return (
        f"🎯 *Bonus Range (annual)*\n"
        f"Monthly wage: ₹{wage:,.0f}\n"
        f"Minimum bonus (8.33%): ₹{min_bonus:,.2f}\n"
        f"Maximum bonus (20%): ₹{max_bonus:,.2f}" + DISCLAIMER
    )


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
    monthly_gross, basic_da, regime, old_deductions=0, age_band="under_60"
):
    wage_base = code_wage_base(monthly_gross, basic_da)
    pf_wage = min(wage_base, EPF_WAGE_CEILING)
    pf_employee = round_contribution(pf_wage * 0.12)
    esic_employee = (
        round_contribution(wage_base * 0.0075) if wage_base <= ESIC_WAGE_CEILING else 0
    )
    tax = calculate_salary_tax(monthly_gross * 12, regime, old_deductions, age_band)
    monthly_tds = tax["annual_tax"] / 12
    net = monthly_gross - pf_employee - esic_employee - monthly_tds
    regime_name = "New" if regime == "new" else "Old"
    age_text = AGE_TEXT[age_band]
    esic_line = (
        f"ESIC employee contribution: ₹{esic_employee:,.0f}"
        if esic_employee
        else f"ESIC: not included (wage base exceeds ₹{ESIC_WAGE_CEILING:,.0f})"
    )
    old_deduction_line = (
        f"\nOld-regime deductions/exemptions: ₹{old_deductions:,.0f}"
        if regime == "old"
        else ""
    )
    return (
        f"💵 *Net Salary Estimate — {regime_name} Regime*\n"
        f"Monthly gross remuneration: ₹{monthly_gross:,.0f}\n"
        f"Basic+DA: ₹{basic_da:,.0f}\n"
        f"Wage base after 50% rule: ₹{wage_base:,.2f}\n"
        f"Employee PF: ₹{pf_employee:,.0f}\n"
        f"{esic_line}\n"
        f"Taxable annual salary: ₹{tax['taxable_income']:,.0f}"
        f"{old_deduction_line}\n"
        f"Average monthly TDS: ₹{monthly_tds:,.0f}\n"
        f"Professional Tax: not included (state-specific)\n"
        f"*Estimated monthly net pay: ₹{net:,.0f}*\n\n"
        f"_TDS includes the regime's standard deduction, applicable rebate, "
        f"marginal relief, surcharge and 4% cess. Assumes a resident individual age "
        f"{age_text}, salary income for 12 months, and no other income._"
        + DISCLAIMER
    )


def calc_leave(v):
    parts = v.split(",")
    if len(parts) != 2:
        raise ValueError("Enter monthly basic and EL days separated by a comma.")
    monthly_basic = float(parts[0].strip().replace("₹", ""))
    days = float(parts[1].strip())
    if (
        not math.isfinite(monthly_basic)
        or not math.isfinite(days)
        or monthly_basic <= 0
        or days < 0
    ):
        raise ValueError("Enter valid positive amounts.")
    per_day = monthly_basic / 30
    amount = per_day * days
    return (
        f"🏖 *Leave Encashment*\n"
        f"Monthly Basic+DA: ₹{monthly_basic:,.2f}\n"
        f"Per day rate (Basic ÷ 30): ₹{per_day:,.2f}\n"
        f"EL days to encash: {days:g}\n"
        f"*Encashment amount: ₹{amount:,.2f}*\n\n"
        f"_Uses the 30-day divisor. Some employers use 26 days or actual "
        f"calendar days, so follow your company leave policy._" + DISCLAIMER
    )


def calc_ot(v):
    rate_str, hours_str = v.split(",")
    rate = float(rate_str.strip())
    hours = float(hours_str.strip())
    amount = rate * 2 * hours
    return (
        f"⏰ *Overtime Pay*\n"
        f"Hourly rate: ₹{rate:,.2f}\n"
        f"Overtime hours: {hours}\n"
        f"Rate applied: 2x normal\n"
        f"*Overtime pay: ₹{amount:,.2f}*" + DISCLAIMER
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


def parse_annual_amount(value, allow_zero=False):
    normalized = value.strip().replace("₹", "").replace(",", "").replace(" ", "")
    amount = float(normalized)
    if not math.isfinite(amount) or amount < 0 or (amount == 0 and not allow_zero):
        raise ValueError("Enter a valid non-negative amount.")
    return amount


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
            data["basic_da"],
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
            gross, basic_da = parse_monthly_wages(value)
            context.user_data["calc_data"] = {
                "monthly_gross": gross,
                "basic_da": basic_da,
            }
            context.user_data["calc_step"] = "tax_regime"
            await update.message.reply_text(
                "TDS ke liye tax regime chuno:",
                reply_markup=tax_regime_keyboard(),
            )
            return TAX_REGIME

        if key == "calc_tds":
            annual_gross = parse_annual_amount(value)
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
            "⚠️ Input sahi format me bhejo. " + CALC_PROMPTS[key],
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
    if age_band not in {"under_60", "60_to_79", "80_plus"}:
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
        deductions = parse_annual_amount(update.message.text, allow_zero=True)
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


# ---------------- STATE MINIMUM WAGES (admin + alerts) ----------------


def load_minwages():
    data = load_json(MINWAGE_FILE, {})
    if not isinstance(data, dict):
        data = {}
    data.setdefault("states", {})
    data.setdefault("changes", [])
    return data


def get_subscribers():
    return set(load_json(SUBSCRIBERS_FILE, []))


async def notify_minwage_change(bot, state, effective, rates, old_rates, source):
    """Send a minimum wage change alert to subscribers only."""
    subs = get_subscribers()
    if not subs:
        return 0
    lines = [
        "🔔 <b>Minimum Wage Alert</b>",
        f"<b>{html.escape(state)}</b> me minimum wages revise hue hain.",
        f"Effective from: {html.escape(effective)}\n",
        f"Unskilled: ₹{rates[0]:,.0f}/month",
        f"Semi-skilled: ₹{rates[1]:,.0f}/month",
        f"Skilled: ₹{rates[2]:,.0f}/month",
        f"Highly skilled: ₹{rates[3]:,.0f}/month",
    ]
    if old_rates:
        lines.append(
            f"\n<i>Pehle: ₹{old_rates[0]:,.0f} / ₹{old_rates[1]:,.0f} / "
            f"₹{old_rates[2]:,.0f} / ₹{old_rates[3]:,.0f}</i>"
        )
    if source:
        lines.append(
            f'\n<a href="{html.escape(source, quote=True)}">Official source</a>'
        )
    lines.append(
        "\n<i>Zone/industry-wise rates aur VDA alag ho sakte hain — "
        "notification se confirm karo.</i>"
    )
    text = "\n".join(lines)
    kwargs = no_preview_kwargs({"parse_mode": "HTML"})

    async def send_one(chat_id):
        try:
            await bot.send_message(chat_id=chat_id, text=text, **kwargs)
            return chat_id, True, False
        except (Forbidden, BadRequest):
            return chat_id, False, True  # blocked the bot / chat gone
        except Exception:
            logger.exception("Min wage alert to %s failed", chat_id)
            return chat_id, False, False

    sent = 0
    ids = list(subs)
    for i in range(0, len(ids), 25):  # stay under Telegram's ~30 msg/sec limit
        results = await asyncio.gather(*(send_one(c) for c in ids[i : i + 25]))
        for chat_id, ok, remove in results:
            if ok:
                sent += 1
            if remove:
                subs.discard(chat_id)
        if i + 25 < len(ids):
            await asyncio.sleep(1)
    save_json(SUBSCRIBERS_FILE, sorted(subs))
    return sent


async def setwage_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Admin only. Usage:
    /setwage Haryana | 2026-10-01 | 13000,14000,15500,17000 | https://source
    (rates = unskilled, semi-skilled, skilled, highly skilled; per month;
    source URL is optional)"""
    user = update.effective_user
    if not user or user.id not in ADMIN_IDS:
        await update.message.reply_text("Not authorised.")
        return
    try:
        raw = update.message.text.split(maxsplit=1)[1]
        parts = [p.strip() for p in raw.split("|")]
        state = next(s for s in STATES if s.lower() == parts[0].lower())
        effective = datetime.strptime(parts[1], "%Y-%m-%d").date().isoformat()
        rates = [float(x) for x in parts[2].replace("₹", "").split(",")]
        if len(rates) != 4 or any(not math.isfinite(r) or r <= 0 for r in rates):
            raise ValueError
        source = parts[3] if len(parts) > 3 else ""
    except (IndexError, StopIteration, ValueError):
        await update.message.reply_text(
            "Format:\n/setwage State | YYYY-MM-DD | "
            "unskilled,semi,skilled,highly | source_url(optional)"
        )
        return

    data = load_minwages()
    old = data["states"].get(state)
    today = datetime.now(IST).date().isoformat()
    data["states"][state] = {
        "effective": effective,
        "rates": rates,
        "source": source,
        "verified": today,
    }
    changed = (not old) or old["rates"] != rates
    if changed:
        data["changes"].append(
            {
                "id": f"{state}|{effective}|{today}",
                "state": state,
                "effective": effective,
                "old": old["rates"] if old else None,
                "new": rates,
                "announced": today,
            }
        )
        data["changes"] = data["changes"][-100:]
    save_json(MINWAGE_FILE, data)  # save first, so a retry never double-sends

    sent = 0
    if changed:
        sent = await notify_minwage_change(
            context.bot,
            state,
            effective,
            rates,
            old["rates"] if old else None,
            source,
        )
    await update.message.reply_text(
        f"✅ {state} minimum wages saved."
        + (
            f" Alert {sent} subscribers ko bhej diya."
            if changed
            else " (Rates same the, koi alert nahi gaya.)"
        )
    )


async def mwstatus_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Admin only: which states have data and which are still missing."""
    user = update.effective_user
    if not user or user.id not in ADMIN_IDS:
        await update.message.reply_text("Not authorised.")
        return
    data = load_minwages()["states"]
    have = [s for s in STATES if s in data]
    missing = [s for s in STATES if s not in data]
    lines = [f"Data added: {len(have)}/{len(STATES)}"]
    for s in have:
        lines.append(
            f"✅ {s} — effective {data[s]['effective']}, "
            f"verified {data[s].get('verified', 'n/a')}"
        )
    if missing:
        lines.append("\nPending: " + ", ".join(missing))
    await update.message.reply_text("\n".join(lines)[:4000])


# ---------------- SUBSCRIPTIONS ----------------


def subscribe_keyboard(chat_id):
    subscribed = chat_id in get_subscribers()
    label = "🔕 Alerts band karo" if subscribed else "🔔 Min wage alerts chalu karo"
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
            "🔔 Min wage alerts *ON*. Jab bhi kisi state ka minimum wage "
            "change hoga, aapko turant alert milega. Band karne ke liye /unsubscribe."
        )
    else:
        subs.discard(chat_id)
        text = "🔕 Min wage alerts *OFF*. Dobara chalu karne ke liye /subscribe."
    save_json(SUBSCRIBERS_FILE, sorted(subs))
    await get_message(update).reply_text(text, parse_mode="Markdown")


async def subscribe_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await toggle_subscription(update, context, force="on")


async def unsubscribe_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await toggle_subscription(update, context, force="off")


# ---------------- UPDATES (news feed, fetched only when user asks) ----------------


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
    return truncate_html(text)


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


async def error_handler(update, context: ContextTypes.DEFAULT_TYPE):
    logger.error("Unhandled error", exc_info=context.error)


# ---------------- APPLICATION (webhook mode) ----------------


def build_application():
    if not BOT_TOKEN:
        raise RuntimeError("BOT_TOKEN not set. Add it in Replit Secrets.")

    app = (
        ApplicationBuilder()
        .token(BOT_TOKEN)
        .updater(None)  # no polling; updates arrive via webhook
        .persistence(StoragePersistence())
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
    info_commands = ["compliance", "updates", "taxsave", "templates", "premium"]

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
        name="calc_conversation",
        persistent=True,
    )

    app.add_handler(conv)
    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("help", help_cmd))
    app.add_handler(CommandHandler("subscribe", subscribe_cmd))
    app.add_handler(CommandHandler("unsubscribe", unsubscribe_cmd))
    app.add_handler(CommandHandler("setwage", setwage_cmd))
    app.add_handler(CommandHandler("mwstatus", mwstatus_cmd))
    for c in info_commands:
        app.add_handler(CommandHandler(c, direct_command))
    app.add_handler(
        MessageHandler(filters.TEXT & ~filters.COMMAND, pending_amount_fallback)
    )
    app.add_handler(MessageHandler(filters.COMMAND, unknown))
    app.add_error_handler(error_handler)
    return app


# ---------------- WEB SERVER (Autoscale) ----------------

PORT = int(os.environ.get("PORT", "8080"))
WEBHOOK_SECRET = (
    hashlib.sha256(BOT_TOKEN.encode()).hexdigest()[:32] if BOT_TOKEN else ""
)


def webhook_base_url():
    explicit = os.environ.get("WEBHOOK_URL", "").strip().rstrip("/")
    if explicit:
        return explicit
    domains = os.environ.get("REPLIT_DOMAINS", "").split(",")
    domain = domains[0].strip() if domains else ""
    return f"https://{domain}" if domain else ""


ptb_app = build_application()


@asynccontextmanager
async def lifespan(_app):
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    await ptb_app.initialize()
    try:
        base = webhook_base_url()
        if base:
            target = f"{base}/telegram"
            info = await ptb_app.bot.get_webhook_info()
            if info.url != target:
                await ptb_app.bot.set_webhook(
                    url=target,
                    secret_token=WEBHOOK_SECRET,
                    allowed_updates=["message", "callback_query"],
                )
                logger.info("Webhook set to %s", target)
        else:
            logger.warning(
                "WEBHOOK_URL / REPLIT_DOMAINS not set — webhook not registered."
            )
        yield
    finally:
        await ptb_app.shutdown()


async def health(request: Request):
    return PlainTextResponse("PayrollPath bot is running")


async def telegram_webhook(request: Request):
    if request.headers.get("X-Telegram-Bot-Api-Secret-Token") != WEBHOOK_SECRET:
        return PlainTextResponse("forbidden", status_code=403)
    try:
        data = await request.json()
        update = Update.de_json(data, ptb_app.bot)
        # Handle inside the request so the instance stays awake until done.
        await ptb_app.process_update(update)
    except Exception:
        logger.exception("Update processing failed")
    return PlainTextResponse("ok")  # always 200, so Telegram doesn't retry


web = Starlette(
    routes=[
        Route("/", health, methods=["GET", "HEAD"]),
        Route("/health", health, methods=["GET", "HEAD"]),
        Route("/telegram", telegram_webhook, methods=["POST"]),
    ],
    lifespan=lifespan,
)

if __name__ == "__main__":
    uvicorn.run(web, host="0.0.0.0", port=PORT)
