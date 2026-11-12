#!/usr/bin/env python3
"""
parse.py (v3) — extract transactions from credit card / bank statement PDFs into
one clean CSV, and prove the extraction was right.

Why v3 exists
-------------
A statement is the only ground truth available: it prints its own totals. v2
computed a purchases check, printed it and threw it away, so nothing downstream
could tell a clean month from a mangled one. v3 stores the check on the
Statement (``reconciled`` / ``reconcile_diff`` / ``reconcile_note``) and ends
every run with a trust rate, which turns "the parser is probably fine" into a
number that either goes up or goes down when the extraction rules change.

Making the contract real then exposed the extraction bugs it was meant to catch:

* ``\\bapr\\b`` in the noise filter (meant for APR tables) was eating every
  Capital One line dated "Apr ..". It is case-sensitive now.
* Bank ledgers print the amount signed the other way round (a withdrawal is
  negative). The running-balance column settles it: when
  ``balance[i] - balance[i-1]`` equals the printed amount, positive means money
  in, and the whole column is flipped to the house convention.
* Amex wraps long merchant names onto the line *above* the date, leaving a
  date-and-amount line with no description. Those rows were dropped entirely.
* A section header naming the debit column ("DATE PURCHASES MERCHANT CATEGORY
  AMOUNT") did not register, so a whole page of Discover purchases stayed in the
  "payments and credits" section and came out negative.
* Chase prints a second, rewards-only ledger of points-earning events. Those
  rows are not account activity and are now skipped.
* Statement periods that straddle New Year assigned December to the wrong year.
  Transaction years are now chosen to land inside the statement period.

Sign convention: money OUT (purchases, fees) is POSITIVE.
Money IN (payments, refunds, credits) is NEGATIVE.

Usage
-----
    pip install pdfplumber
    finances parse ./statements -o transactions.csv
    finances parse ./statements -o transactions.csv --password 1234
    finances parse ./statements -o transactions.csv --strict   # fail on mismatch
    finances parse one_bad_file.pdf --dump-columns             # diagnose
    finances parse one_bad_file.pdf --dump-text ./raw          # diagnose
"""

import argparse
import csv
import os
import re
import sys
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed
from datetime import date, datetime, timedelta

try:
    import pdfplumber
except ImportError:
    sys.exit("Missing dependency. Run:  pip install pdfplumber")

# Shared foundation: one definition of money/date parsing, the row schema and
# the SQLite store, used by every tool in the package.
from finances.utils import MONTHS, file_sha256, parse_date, parse_money  # noqa: E402
from finances.models import Statement, Transaction                        # noqa: E402
from finances.database import DEFAULT_DB, FinanceDB                        # noqa: E402

# The shared engine decides categories. If it isn't next to this script the
# built-in rules below are used instead, so nothing hard-fails.
try:
    from finances.categorizer import Categorizer as _Categorizer
    _CZ = _Categorizer()
    SHARED_CATEGORIZER = True
except Exception:
    _CZ = None
    SHARED_CATEGORIZER = False

# The same taxonomy the engine uses, so the end-of-run summary and the
# dashboard do not disagree about what counts as spending. A card payment made
# from checking is money out of the account but not consumption, and counting
# it here made "Payment" look like a $3.3k spending category.
try:
    from finances.categorizer import NON_SPEND
except Exception:
    NON_SPEND = {"Payment", "Credits/Refunds", "Transfers/Cash", "Income"}


# --------------------------------------------------------------------------
# Patterns
# --------------------------------------------------------------------------

# MONTHS lives in utils (shared with the date parser).
DATE_NUM = r"\d{1,2}[/-]\d{1,2}(?:[/-]\d{2,4})?"
DATE_ABBR = r"(?:%s)[a-z]*\.?\s+\d{1,2}(?:,?\s+\d{4})?" % "|".join(MONTHS)
DATE_DMY = r"\d{1,2}\s+(?:%s)[a-z]*\.?(?:\s+\d{2,4})?" % "|".join(MONTHS)
DATE_ANY = r"(?:%s|%s|%s)" % (DATE_NUM, DATE_ABBR, DATE_DMY)
DATE_ANY_RX = re.compile(DATE_ANY, re.I)   # compiled once; hot in leading_dates()

# A single word that is a money value. Chase drops the leading zero on amounts
# under a dollar (".99"), so the integer part has to be optional.
MONEY_TOKEN = re.compile(r"^[-+]?[\$\u20b9\u00a3\u20ac]?\(?-?\d{1,3}(?:,\d{3})*\.\d{2}\)?-?$"
                         r"|^[-+]?[\$\u20b9\u00a3\u20ac]?\(?-?\d*\.\d{2}\)?-?$")
# Capital One prints "Payments - $1,200.00", i.e. a space between the sign and
# the currency symbol, so both are optional and separable.
MONEY_INLINE = r"[-+]?\s?\$?\s?\(?-?\d{1,3}(?:,\d{3})*\.\d{2}\)?-?"

# Only ever consulted for lines that already look like a transaction, so it can
# afford to be narrow. "minimum payment" on its own is not here: Discover names
# a real payment "DIRECTPAY MINIMUM PAYMENT", and the summary box that this was
# meant to skip says "payment due" anyway.
NOISE = re.compile(
    r"previous balance|new balance|payment due|credit limit"
    r"|available credit|cash advance limit|annual percentage rate|balance subject"
    r"|interest charge calculation|total fees charged|total interest charged"
    r"|year[- ]to[- ]date|totals? for this period|days in billing"
    r"|account summary|page \d+ of \d+|rewards? (balance|summary|earned)"
    r"|purchases?\s+balance|corresponding apr|opening balance|closing balance"
    r"|brought forward|carried forward|statement balance|total debits|total credits",
    re.IGNORECASE)
# "APR" only ever means the rate when it is shouted. Matched case-sensitively
# because the abbreviation is indistinguishable from the month "Apr", and every
# Capital One line dated "Apr .." used to be discarded as an APR table row.
NOISE_APR = re.compile(r"\bAPR\b")

SEC_CREDIT = re.compile(
    r"payments?\s*(and|&)?\s*(other\s*)?credits|payments?\s*/\s*credits"
    r"|credits\s*(and|&)\s*adjustments|refunds?\s*(and|&)\s*credits",
    re.IGNORECASE)
SEC_DEBIT = re.compile(
    r"^\s*(new\s+)?charges?\s*$|^\s*detail\s*$"
    r"|purchases?\s*(and|&)?\s*(other\s*)?(debits|adjustments)?$|transactions?$"
    r"|fees\s*charged|interest\s*charged|cash\s*advances|new\s+charges"
    # A table header that names the debit column, e.g. Discover's
    # "DATE PURCHASES MERCHANT CATEGORY AMOUNT".
    r"|\bpurchases\b[^\n]{0,40}\bamount\b",
    re.IGNORECASE)
# Rewards ledgers list points-earning events, not account activity: the same
# purchase can appear here a cycle late, or not at all. Chase prints one under a
# header whose last column is "Rewards". Everything after it on the page is
# skipped, so section changes inside it do not pull us back out.
SEC_SKIP = re.compile(
    r"\bamounts?\s+rewards?\s*$|purchases?\s+and\s+redemptions"
    r"|rewards?\s+(detail|activity|ledger)",
    re.IGNORECASE)

# Charges the statement itemises but excludes from its own purchases total, so
# the reconciliation has to exclude them too.
FEE_OR_INTEREST = re.compile(
    r"interest charge|finance charge|annual (membership )?fee|late fee"
    r"|membership fee|returned payment|foreign transaction fee"
    r"|cash advance fee|over ?limit fee|balance transfer fee",
    re.IGNORECASE)

# Column header keywords -> role
HEADER_ROLES = [
    ("balance", r"^balance$|^bal$|^running\s*balance$|^closing\s*balance$"),
    ("credit",  r"^credit$|^credits$|^deposits?$|^deposit\s*\(cr\)$|^cr$|^payments?$|^money\s*in$"),
    ("debit",   r"^debit$|^debits$|^withdrawals?$|^withdrawal\s*\(dr\)$|^dr$|^charges?$|^money\s*out$"),
    ("amount",  r"^amount$|^amt$|^transaction\s*amount$|^value$"),
]
HEADER_ROLES = [(r, re.compile(p, re.I)) for r, p in HEADER_ROLES]

# Which bank a statement is from: one file per bank in finances/banks/, so a
# new bank is a new file rather than an edit here.
from finances.banks import investment_issuers as _investment_issuers  # noqa: E402
from finances.banks import issuers as _issuers                        # noqa: E402

ISSUERS = _issuers()

PERIOD_PATTERNS = [
    r"opening/closing date\s*:?\s*(?P<a>%s)\s*[-\u2013]\s*(?P<b>%s)" % (DATE_ANY, DATE_ANY),
    r"open to close date\s*:?\s*(?P<a>%s)\s*(?:[-\u2013]|to|through)\s*(?P<b>%s)" % (DATE_ANY, DATE_ANY),
    r"billing (?:period|cycle)\s*:?\s*(?P<a>%s)\s*(?:[-\u2013]|to|through)\s*(?P<b>%s)" % (DATE_ANY, DATE_ANY),
    r"statement period\s*:?\s*(?P<a>%s)\s*(?:[-\u2013]|to|through)\s*(?P<b>%s)" % (DATE_ANY, DATE_ANY),
    r"(?:for the period|period)\s*:?\s*(?P<a>%s)\s*(?:[-\u2013]|to|through)\s*(?P<b>%s)" % (DATE_ANY, DATE_ANY),
    r"(?P<a>%s)\s*[-\u2013]\s*(?P<b>%s)\s*(?:statement period|billing period)" % (DATE_ANY, DATE_ANY),
    # A bare date range on its own line: Chase checking's "December 04, 2025
    # through January 06, 2026", Capital One's "Jan 13, 2026 - Feb 09, 2026 |
    # 28 days in Billing Cycle". Last, so a labelled range always wins.
    r"^\s*(?P<a>%s)\s*(?:[-\u2013]|to|through|thru)\s*(?P<b>%s)\s*(?:$|\|)" % (DATE_ANY, DATE_ANY),
    r"closing date\s*:?\s*(?P<b>%s)" % DATE_ANY,
    r"statement (?:closing )?date\s*:?\s*(?P<b>%s)" % DATE_ANY,
]
# The filename is the last resort for a period, and often the only place the
# start date appears at all ("Amex-Apr_10_-_May_10_2026.pdf").
FILE_PERIOD = re.compile(r"(?P<a>%s)\s*[-\u2013]\s*(?P<b>%s)" % (DATE_ANY, DATE_ANY), re.I)

# The figures reconciliation is built on. These are matched against the *label
# cell* in front of each printed figure, not against running text, so the label
# has to open its own cell: "Interest Charge on Purchases" is one cell and
# never reads as the purchases total, and "Minimum Payment Due" never reads as
# the payments total.
SUMMARY_LABELS = [
    # A deposit account opens and closes rather than carrying a balance
    # forward, so it prints "Beginning Balance" and "Ending Balance" where a
    # card prints "Previous Balance" and "New Balance". Same two quantities.
    ("previous_balance", r"(?:previous|beginning|opening)\s+balance\b"),
    ("new_balance",      r"(?:new|ending|closing)\s+balance(?:\s*total)?\b"
                         r"|balance\s+(?:on|as of)\b"),
    ("payments",         r"(?:total\s+)?payments?(?:\s*(?:and|&|/|,)\s*"
                         r"(?:other\s*)?credits)?\b"),
    ("purchases",        r"(?:total\s+)?(?:purchases?(?:\s+and\s+adjustments)?"
                         r"|new charges|transactions)\b"),
    ("interest_charged", r"(?:total\s+)?interest charge[ds]?\b"),
    ("fees_charged",     r"(?:total\s+)?fees charged\b"),
]
SUMMARY_LABELS = [(k, re.compile(r"\s*" + p, re.I)) for k, p in SUMMARY_LABELS]
# A checking account prints a withdrawals breakdown instead of a purchases
# total. Summed, it is the same quantity: everything that left the account.
BANK_OUT = re.compile(r"\s*(?:atm & debit card withdrawals|electronic withdrawals"
                      r"|other withdrawals|checks paid|fees)\s*$", re.I)
BANK_IN = re.compile(r"\s*deposits and additions\b", re.I)

LOOSE_FIELDS = [
    ("minimum_payment",  r"minimum payment(?:\s*due)?\s*:?\s*(%s)"),
    ("credit_limit",     r"(?:total\s+)?credit (?:access )?(?:line|limit)\s*:?\s*(%s)"),
    ("available_credit", r"available credit(?:\s*line)?\s*:?\s*(%s)"),
    ("cash_advances",    r"(?:total\s+)?cash advances?\s*:?\s*(%s)"),
]
LOOSE_FIELDS = [(k, p % MONEY_INLINE) for k, p in LOOSE_FIELDS]

# (weight, pattern). The first three name an account or a card explicitly. The
# last does not, and a wallet token is written the same way \u2014 Discover prints
# "APPLE PAY ENDING IN 3702" under most of its transactions, far more often
# than it prints its own card number \u2014 so it only gets a say when nothing
# stronger was found.
LAST4_PATTERNS = [
    (2, r"(?:account|card)\s*(?:number|#)?\s*ending\s*(?:in)?\s*[:#]?\s*([\dxX*\u2022-]{4,})"),
    (2, r"(?:account|card)\s*(?:number|#)\s*[:#]?\s*([\dxX*\u2022 -]{8,})"),
    (2, r"((?:x{4,}|\*{4,}|\u2022{4,})\s*\d{4})"),
    (1, r"ending\s*(?:in)?\s*([\d-]{4,})"),
]

# --------------------------------------------------------------------------
# Categorization — edit freely, first match wins
# --------------------------------------------------------------------------

CATEGORIES = [
    ("Income",         r"direct dep(osit)?\b|payroll|ach credit|\bsalary\b|wages|"
                       r"irs treas|tax ref(und)?|state refund|dividend|"
                       r"interest (paid|earned)|mobile deposit|remote deposit|"
                       r"atm deposit|deposit from|zelle from|venmo from|"
                       r"cash ?app from|reimbursement|rebate"),
    ("Payment",        r"payment[\s\-–—]*thank[\s\-–—]*you|thank you for your payment|"
                       r"autopay|auto[\s\-]?pay|online payment|payment received|"
                       r"electronic payment|pymt|direct debit|payment - web|"
                       r"mobile payment|payment posted"),
    ("Credits/Refunds", r"statement credit|reward(?:s)? credit|cash ?back (?:credit|bonus)|"
                        r"credit adjustment|chargeback"),
    ("Groceries",      r"whole ?foods|trader ?joe|safeway|kroger|publix|wegmans|aldi|"
                       r"stop ?& ?shop|shoprite|h-?e-?b|sprouts|food ?lion|giant|ralphs|albertsons|"
                       r"fairway|key ?food|c-?town|grocer|supermarket|instacart|market"),
    ("Dining",         r"restaurant|cafe|coffee|starbucks|dunkin|chipotle|mcdonald|burger|pizza|"
                       r"sushi|taco|bar ?& ?grill|kitchen|bakery|deli|diner|steakhouse|panera|"
                       r"shake shack|subway|wendy|popeyes|chick-?fil|five guys|noodle|ramen|bbq|"
                       r"sweetgreen|cava |dig inn|halal|shawarma|poke|thai|indian|"
                       r"doordash|uber ?eats|grubhub|seamless|postmates|caviar|resy|opentable"),
    ("Big Box",        r"target|walmart|costco|sam'?s club|bj'?s wholesale"),
    ("Transport",      r"uber(?! ?eats)|lyft|taxi|mta|njt|nj transit|path |amtrak|metro|transit|"
                       r"parking|e-?zpass|toll|via |curb|revel"),
    ("Gas/Auto",       r"shell|exxon|mobil|chevron|bp\b|sunoco|wawa|speedway|citgo|gulf|76 |"
                       r"valero|texaco|auto ?zone|jiffy lube|midas|pep boys|geico|progressive|"
                       r"state farm|allstate|dmv"),
    ("Travel",         r"airlines?|delta air|united air|american air|jetblue|southwest|spirit air|"
                       r"alaska air|frontier|hotel|marriott|hilton|hyatt|airbnb|vrbo|booking\.com|"
                       r"expedia|priceline|kayak|hostel|resort|inn\b|tsa|clear|global entry|"
                       r"rental car|hertz|avis|enterprise rent|budget rent|turo"),
    ("Subscriptions",  r"netflix|spotify|hulu|disney ?\+|disneyplus|hbo|max\.com|paramount|peacock|"
                       r"apple\.com/bill|apple music|itunes|icloud|google storage|youtube ?premium|"
                       r"amazon prime|prime video|audible|kindle|patreon|substack|nyt|new york times|"
                       r"wsj|washington post|medium|dropbox|notion|adobe|microsoft 365|chatgpt|openai|"
                       r"anthropic|claude|midjourney|github|linkedin premium|duolingo|masterclass|"
                       r"peloton|strava|calm|headspace|xbox|playstation|nintendo|steam|twitch"),
    ("Utilities",      r"con ?ed|pse&?g|national grid|electric|utility|water dept|verizon|at&?t|"
                       r"t-?mobile|sprint|xfinity|comcast|spectrum|optimum|fios|internet|wireless|"
                       r"mint mobile|google fi"),
    ("Rent/Housing",   r"rent|landlord|property mgmt|hoa|mortgage|zillow rental|apartments"),
    ("Health",         r"pharmacy|cvs|walgreens|rite ?aid|duane reade|doctor|dental|dentist|medical|"
                       r"hospital|clinic|urgent care|labcorp|quest diag|optical|vision|therapy|"
                       r"psycholog|one ?medical|zocdoc|goodrx|health"),
    ("Fitness",        r"gym|fitness|equinox|planet fit|crunch|blink|soulcycle|yoga|pilates|"
                       r"climbing|crossfit|lifetime ath"),
    ("Shopping",       r"amazon|amzn|ebay|etsy|best ?buy|apple store|home depot|lowe'?s|ikea|"
                       r"wayfair|macy|nordstrom|uniqlo|zara|h&m|gap\b|old navy|nike|adidas|"
                       r"lululemon|sephora|ulta|shein|temu|wish\.com|newegg|b&h photo|"
                       r"micro ?center|staples|office depot|container store|marshalls|tj ?maxx|"
                       r"ross stores|nordstrom rack"),
    ("Entertainment",  r"cinema|theatre|theater|amc |regal|movie|ticketmaster|stubhub|"
                       r"live nation|eventbrite|museum|zoo|aquarium|bowling|arcade|golf|concert|dice\.fm"),
    ("Alcohol/Bars",   r"liquor|wine|brewery|brewing|tavern|pub\b|lounge|cocktail|spirits|beer"),
    ("Fees/Interest",  r"annual fee|late fee|interest charge|finance charge|foreign transaction|"
                       r"cash advance fee|returned payment|over ?limit|service charge|atm fee|"
                       r"balance transfer fee|membership fee|maintenance fee|overdraft"),
    ("Transfers/Cash", r"venmo|cash ?app|zelle|paypal|wise|remitly|western union|atm withdrawal|"
                       r"cash advance|coinbase|robinhood|fidelity|vanguard|schwab|betterment|"
                       r"wealthfront|acorns|transfer to|transfer from|wire "),
    ("Education",      r"tuition|university|college|coursera|udemy|edx|school|bookstore|student loan"),
    ("Pets",           r"petco|petsmart|chewy|veterinar|vet clinic|pet "),
    ("Personal Care",  r"barber|salon|spa\b|nails|haircut|massage|supercuts"),
    ("Insurance",      r"insurance|lemonade|policy premium"),
    ("Charity",        r"donation|charit|gofundme|red cross|unicef|foundation"),
]
CATEGORIES = [(name, re.compile(pat, re.IGNORECASE)) for name, pat in CATEGORIES]


# --------------------------------------------------------------------------
# Small helpers
# --------------------------------------------------------------------------

def clean_merchant(desc):
    if _CZ is not None:
        from finances.categorizer import normalize as _normalize
        cleaned, _ = _normalize(desc)
        if cleaned:
            return cleaned
    s = re.sub(r"\s{2,}", " ", desc).strip()
    s = re.sub(r"^(purchase|pos debit|debit card purchase|recurring|sale)\s+", "", s, flags=re.I)
    s = re.sub(r"\b\d{6,}\b", " ", s)
    s = re.sub(r"\b(?=[A-Z0-9]*\d)[A-Z0-9]{8,}\b", " ", s)
    s = re.sub(r"\b(\d{3}-\d{3}-\d{4}|\(\d{3}\)\s?\d{3}-\d{4})\b", " ", s)
    s = re.sub(r"\s+(?:[A-Z]{2}|[A-Z][a-z]+)\s*$", "", s)
    s = re.sub(r"[#*]{2,}", " ", s)
    s = re.sub(r"\s{2,}", " ", s).strip(" -.,*#")
    return s or desc.strip()


def categorize(desc):
    if _CZ is not None:
        return _CZ.categorize(desc).category
    for name, rx in CATEGORIES:          # fallback: legacy built-in rules
        if rx.search(desc):
            return name
    return "Uncategorized"


_BLANK_DESC = re.compile(r"[\d\s.,/$*#-]*$")


def _is_blank_desc(desc):
    """True when a descriptor carries no name — empty, or only punctuation and
    reference numbers."""
    return len(desc) < 2 or _BLANK_DESC.fullmatch(desc) is not None


def detect_issuer(text):
    low = text.lower()
    best, best_pos = "Unknown", len(low) + 1
    for name, pat in ISSUERS:
        m = re.search(pat, low)
        if m and m.start() < best_pos:
            best, best_pos = name, m.start()
    return best


def detect_last4(text):
    """Which account this statement is about.

    Taking the first account-shaped number was wrong twice over. A statement
    names its own account in the header of every page, but a transaction can
    name somebody else's exactly once — "Payment To Chase Card Ending IN 0682"
    on a checking statement — and that one line was enough to file two months
    of checking activity under the credit card.

    So transactions do not get a vote (a line that opens with a date is
    activity, not identity), and among what is left the most-repeated number
    wins, earliest mention breaking a tie.
    """
    body = "\n".join(ln for ln in text.split("\n")
                     if not re.match(r"^\s*%s\s" % DATE_ANY, ln, re.I))
    tier, votes, first_at, seen = defaultdict(int), defaultdict(int), {}, set()
    for weight, pat in LAST4_PATTERNS:
        for m in re.finditer(pat, body, re.IGNORECASE):
            digits = re.sub(r"\D", "", m.group(1))
            if len(digits) < 4:
                continue
            last4, at = digits[-4:], m.start(1)
            if (last4, at) in seen:       # several patterns, one mention
                continue
            seen.add((last4, at))
            tier[last4] = max(tier[last4], weight)
            votes[last4] += 1
            first_at.setdefault(last4, at)
    if not votes:
        return ""
    return max(votes, key=lambda k: (tier[k], votes[k], -first_at[k]))


def _range_from_match(gd, fallback_year):
    """Turn a matched (a, b) date pair into real dates, closing the year gap.

    Statements print "Dec 04 - Jan 06" without repeating the year, so a start
    that lands after its own end belongs to the previous year.
    """
    b = parse_date(gd.get("b") or "", fallback_year)
    a = parse_date(gd.get("a") or "", (b.year if b else fallback_year)) if gd.get("a") else None
    if a and b and a > b:
        a = parse_date(gd["a"], b.year - 1)
    return a, b


def period_from_filename(path):
    """Read a period out of a filename like ``Amex-Apr_10_-_May_10_2026.pdf``."""
    name = os.path.splitext(os.path.basename(path))[0].replace("_", " ")
    m = FILE_PERIOD.search(name)
    if not m:
        return None, None
    return _range_from_match(m.groupdict(), year_from_filename(path))


def detect_period(text, fallback_year, path=None):
    """Return ``(period_string, start, end)`` for the statement.

    The string is the human-readable "start to end" other tools already store;
    the two dates are what the year-rollover fix and the coverage report need.
    Either end may be None when the statement genuinely does not say.
    """
    a = b = None
    for pat in PERIOD_PATTERNS:
        m = re.search(pat, text, re.IGNORECASE | re.MULTILINE)
        if not m:
            continue
        a, b = _range_from_match(m.groupdict(), fallback_year)
        if b:
            break
        a = b = None
    if path and (a is None or b is None):
        fa, fb = period_from_filename(path)
        # Trust the text's closing date over the filename's, but take the start
        # date the text never printed.
        if b is None:
            a, b = fa, fb
        elif a is None and fa and fa < b:
            a = fa
    if a and b and a > b:
        a = None
    if not b:
        return "", None, None
    return (f"{a.isoformat()} to {b.isoformat()}" if a else b.isoformat()), a, b


def year_from_filename(path):
    m = re.search(r"(20\d{2})", os.path.basename(path))
    return int(m.group(1)) if m else None


def year_in_period(d, start, end, slack=5):
    """Re-year a date so it falls inside the statement period.

    Most statements print transaction dates without a year. Across New Year
    that makes "12/04" ambiguous, and guessing the closing year turns a
    December charge into one twelve months in the future.
    """
    if d is None or end is None:
        return d
    lo = (start or end) - timedelta(days=slack + 40)
    hi = end + timedelta(days=slack)
    years = [end.year, end.year - 1, end.year + 1]
    if start:
        years.insert(1, start.year)
    for y in years:
        try:
            cand = d.replace(year=y)
        except ValueError:           # 29 Feb in a non-leap year
            continue
        if lo <= cand <= hi:
            return cand
    return d


def cluster(values, gap=14.0):
    """Group right-edge x positions into columns."""
    if not values:
        return []
    vals = sorted(values)
    groups, cur = [], [vals[0]]
    for v in vals[1:]:
        if v - cur[-1] <= gap:
            cur.append(v)
        else:
            groups.append(cur)
            cur = [v]
    groups.append(cur)
    return [sum(g) / len(g) for g in groups]


def nearest(centers, x):
    return min(range(len(centers)), key=lambda i: abs(centers[i] - x)) if centers else None


# --------------------------------------------------------------------------
# Page / line extraction with positions
# --------------------------------------------------------------------------

def page_lines(page):
    words = page.extract_words(x_tolerance=1.5, y_tolerance=3) or []
    rows = defaultdict(list)
    for w in words:
        rows[round(w["top"] / 3.0)].append(w)
    return [strip_layout_markers(sorted(rows[k], key=lambda w: w["x0"]))
            for k in sorted(rows)]


LAYOUT_MARKER = re.compile(r"\*(?:start|end)\*", re.I)
# The section tags Chase embeds in the text layer. Their letters are known, so
# the digits they swallow can be recovered.
MARKER_PHRASES = {
    "transactiondetail", "posttransactiondetailmessage",
    "afteraddressmessagearea", "summary", "messagearea",
    "dreportraitdisclosuremessagearea",
}


def strip_layout_markers(ws):
    """Pull Chase's layout tags back out of the first row of a page.

    A Chase PDF lays "*end*transaction detail" into the same text run as the
    data, so the first transaction on each page arrives fused with it:
    ``*end*transac0tion detail1/20 Zelle Payment ... -77.00 2,133.22``. Note
    the date: the tag has swallowed "0" and "1/20". Deleting the tag's own
    letters and keeping everything else puts "01/20" back together, which is
    worth doing — one such row goes missing per page otherwise.
    """
    hit = next(((i, m) for i, w in enumerate(ws[:2])
                if (m := LAYOUT_MARKER.search(w["text"]))), None)
    if hit is None:
        return ws
    i, m = hit
    head, tail = ws[i]["text"][:m.start()], ws[i]["text"][m.end():]
    letters, kept, j = "", [], i
    while True:
        for pos, ch in enumerate(tail):
            if ch.isalpha():
                letters += ch.lower()
                if letters in MARKER_PHRASES:
                    tail = tail[pos + 1:]
                    break
                if len(letters) > 40:
                    return ws          # not a tag we recognise; leave it alone
            elif not ch.isspace():
                kept.append(ch)        # a digit the tag interleaved
        else:
            j += 1
            if j >= len(ws):
                return ws
            tail = ws[j]["text"]
            continue
        break
    text = (head + "".join(kept) + tail).strip()
    out = []
    if text:
        out.append(dict(ws[j], text=text))
    out.extend(ws[j + 1:])
    return out or ws


def words_text(ws):
    return " ".join(w["text"] for w in ws)


def money_in_line(ws):
    """Return [(index, value, right_edge_x)] for money-looking words."""
    out = []
    for i, w in enumerate(ws):
        t = w["text"]
        if not MONEY_TOKEN.match(t):
            continue
        val = parse_money(t)
        if val is None:
            continue
        nxt = ws[i + 1]["text"] if i + 1 < len(ws) else ""
        if nxt in ("-", "CR", "Cr", "cr"):
            val = -abs(val)
        elif nxt in ("DR", "Dr", "dr"):
            val = abs(val)
        out.append((i, val, w["x1"]))
    return out


def leading_dates(ws):
    """Match one or two dates at the start of a line. Returns (d1, d2, idx_after).

    A trailing asterisk is part of the footnote, not the date: Amex writes
    ``03/25/26*`` and explains "*Indicates posting date" further down.
    """
    texts = [w["text"] for w in ws]
    d1 = None
    idx = 0
    for n in (3, 2, 1):
        if n > len(texts):
            continue
        cand = " ".join(texts[:n]).rstrip("*")
        if DATE_ANY_RX.fullmatch(cand):
            d1, idx = cand, n
            break
    if d1 is None:
        return None
    for n in (3, 2, 1):
        if idx + n > len(texts):
            continue
        cand = " ".join(texts[idx:idx + n]).rstrip("*")
        if DATE_ANY_RX.fullmatch(cand):
            return d1, cand, idx + n
    return d1, None, idx


CELL_GAP = 12.0     # pt: wider than word spacing, narrower than a column gap


def summary_pairs(all_lines):
    """Read the statement summary as (label, figure) cells.

    Page 1 is a two-column layout and flattening it to text runs the columns
    together, so Capital One's "Payments - $1,200.00" arrives as
    "on the statement closing date when Payments - $1,200.00" and reading
    labels out of running text picks up whatever prose happens to precede the
    number. The word positions still carry the cell boundaries, so the label is
    taken from the cell in front of each figure instead.

    Returns pairs in document order, so page 1's summary box wins over the
    interest-calculation table at the back.
    """
    pairs = []
    for _, ws in all_lines:
        if leading_dates(ws):
            continue                       # a transaction row, not a summary row
        cells = []
        for i, w in enumerate(ws):
            if cells and w["x0"] - ws[i - 1]["x1"] <= CELL_GAP:
                cells[-1].append(w)
            else:
                cells.append([w])
        for j, cell in enumerate(cells):
            text = " ".join(w["text"] for w in cell)
            m = re.search(r"(%s)\s*$" % MONEY_INLINE, text)
            if not m:
                continue
            head = text[:m.start()].strip()
            if not re.search(r"[A-Za-z]", head):
                if j == 0:
                    continue               # a bare figure with nothing to name it
                head = " ".join(w["text"] for w in cells[j - 1])
            pairs.append((head, parse_money(m.group(1))))
    return pairs


def column_model(rows, headers, amount_col="auto"):
    """Work out which money column on a page is the transaction amount.

    A running-balance column only exists if most transaction lines actually
    carry two or more amounts. Card statements print one amount per line, so
    nothing is ever dropped there.
    """
    centers = cluster([m[2] for c in rows for m in c["monies"]])
    n = max(len(rows), 1)
    coverage = [0] * len(centers)
    multi = 0
    for c in rows:
        seen = set()
        for _, _, x in c["monies"]:
            k = nearest(centers, x)
            if k is not None:
                seen.add(k)
        for k in seen:
            coverage[k] += 1
        if len(seen) >= 2:
            multi += 1
    coverage = [v / n for v in coverage]
    multi = multi / n

    balance = credit = debit = amount = None
    if len(centers) < 2:
        # One column of figures. There is no separate credit column to read a
        # sign from, so leave sign to the section and keyword rules.
        return {"centers": centers, "coverage": coverage, "multi": multi,
                "balance": None, "credit": None, "debit": None,
                "amount": 0 if centers else None, "polarity": None}
    if centers:
        if "balance" in headers:
            balance = nearest(centers, headers["balance"])
        if "credit" in headers:
            credit = nearest(centers, headers["credit"])
        if "debit" in headers:
            debit = nearest(centers, headers["debit"])
        if "amount" in headers:
            amount = nearest(centers, headers["amount"])
        # No header row to go on: infer a balance column only when the lines
        # themselves look like a ledger — two amounts on most rows, the
        # rightmost present on nearly all of them.
        if balance is None and len(centers) >= 2 and multi >= 0.6 \
                and coverage[-1] >= 0.85:
            balance = len(centers) - 1

    if credit is not None and credit == debit:
        credit = debit = None
    if credit is not None and credit == amount:
        credit = None

    if amount_col == "last":
        balance = None
    elif amount_col == "second-last":
        balance = len(centers) - 1 if len(centers) >= 2 else None

    return {"centers": centers, "coverage": coverage, "multi": multi,
            "balance": balance, "credit": credit, "debit": debit, "amount": amount,
            "polarity": balance_polarity(rows, centers, balance)}


def balance_polarity(rows, centers, balance_col):
    """Decide which way the amount column's printed sign points.

    Card statements print a purchase as a positive number; bank ledgers print a
    withdrawal as a negative one. Guessing from the issuer is fragile, but a
    running balance settles it arithmetically: the change in balance from one
    row to the next equals the printed amount only if positive means money
    *in*. Returns -1 when the column has to be flipped to the house convention
    (out positive), +1 when it is already right, None when there is nothing to
    measure against.
    """
    if balance_col is None or len(rows) < 4:
        return None
    seq = []
    for c in rows:
        bal = amt = None
        for _, val, x in c["monies"]:
            k = nearest(centers, x)
            if k == balance_col:
                bal = val
            else:
                amt = val          # rightmost non-balance figure, as pass 2 picks
        seq.append((amt, bal))

    money_in = money_out = 0
    for i in range(1, len(seq)):
        amt, bal = seq[i]
        prev_bal = seq[i - 1][1]
        if amt is None or bal is None or prev_bal is None:
            continue
        delta = bal - prev_bal
        if abs(delta - amt) <= 0.011:
            money_in += 1          # printed positive raised the balance
        elif abs(delta + amt) <= 0.011:
            money_out += 1
    if money_in >= 3 and money_in > money_out * 2:
        return -1
    if money_out >= 3 and money_out > money_in * 2:
        return 1
    return None


# --------------------------------------------------------------------------
# Core parse
# --------------------------------------------------------------------------

def ocr_copy(path, out_dir, password=None):
    """A copy of a scanned PDF with a text layer added by OCR, or None.

    ocrmypdf (Tesseract underneath) runs on this machine, like everything
    else; nothing is uploaded. Without it installed there is nothing to do.
    """
    import shutil
    import subprocess
    exe = shutil.which("ocrmypdf")
    if not exe:
        return None
    out = os.path.join(out_dir, os.path.basename(path))
    cmd = [exe, "--quiet", "--skip-text", "--output-type", "pdf", path, out]
    if password:
        return None                     # ocrmypdf cannot open encrypted files
    proc = subprocess.run(cmd, capture_output=True, text=True)
    return out if proc.returncode == 0 and os.path.exists(out) else None


def _parse_scan(path, password, amount_col, dump_columns, want_text):
    """A statement with no text layer: OCR it, then parse it like any other.

    OCR misreads digits, so its rows are held to the same test as a text PDF's:
    they must add up to the totals the statement prints. When they do not, they
    are kept but the statement says plainly that they were read from a scan and
    need checking, rather than passing them off as read.
    """
    import tempfile
    with tempfile.TemporaryDirectory(prefix="finances-ocr-") as tmp:
        copy = ocr_copy(path, tmp, password)
        if copy is None:
            raise RuntimeError(
                "no text layer: this is a scan. Install OCR to read it "
                "(macOS: brew install ocrmypdf; Linux: apt install ocrmypdf), "
                "or download the statement again as a text PDF")
        txns, meta = parse_statement(copy, None, amount_col, dump_columns, want_text)
    name = os.path.basename(path)
    for t in txns:
        t.source_file = name
    st = meta["statement"]
    st.source_file, st.source_format = name, "pdf+ocr"
    if st.reconciled == 1:
        st.reconcile_note = ("Read from a scan by OCR; the rows add up to the printed "
                             "totals. " + (st.reconcile_note or "")).strip()
    elif st.checkable:
        st.reconcile_note = ("Read from a scan by OCR and not confirmed by the printed "
                             "totals: check these rows against the statement. "
                             + (st.reconcile_note or "")).strip()
    return txns, meta


def parse_statement(path, password=None, amount_col="auto",
                    dump_columns=False, want_text=False):
    """Extract transactions + a statement summary from one PDF.

    Returns ``(txns, meta)`` where ``txns`` is a list of :class:`Transaction`
    and ``meta`` carries the :class:`Statement` summary plus diagnostics. Pure
    and picklable, so it runs unchanged inside a process pool.
    """
    unmatched = []
    kwargs = {"password": password} if password else {}
    all_lines, pages = [], 0
    with pdfplumber.open(path, **kwargs) as pdf:
        pages = len(pdf.pages)
        for pi, page in enumerate(pdf.pages):
            for ws in page_lines(page):
                all_lines.append((pi, ws))

    full = "\n".join(words_text(ws) for _, ws in all_lines)
    if not full.strip():
        return _parse_scan(path, password, amount_col, dump_columns, want_text)

    fallback_year = year_from_filename(path) or datetime.fromtimestamp(
        os.path.getmtime(path)).year
    issuer = detect_issuer(full)
    last4 = detect_last4(full)
    period, opening, closing = detect_period(full, fallback_year, path)
    ref_year = closing.year if closing else fallback_year
    ref_month = closing.month if closing else 12

    # Column headers are per page: page 1 of a card statement is often a
    # two-column summary while page 3 is the transaction table.
    page_headers = defaultdict(dict)
    for pi, ws in all_lines:
        hits = {}
        for w in ws:
            for role, rx in HEADER_ROLES:
                if rx.match(w["text"].strip()):
                    hits.setdefault(role, w["x1"])
        if len(hits) >= 2:
            for role, x in hits.items():
                page_headers[pi].setdefault(role, x)
    headers = {}
    for pi in page_headers:
        for role, x in page_headers[pi].items():
            headers.setdefault(role, x)

    # ---- pass 1: collect candidate transaction lines ----
    cands = []
    section = None
    last_page = None
    carry = ""            # previous line, kept for descriptions that wrap
    for pi, ws in all_lines:
        text = words_text(ws).strip()
        if not text:
            continue
        if pi != last_page:
            section, last_page, carry = None, pi, ""   # tables restart per page
        if len(text) < 80 and not money_in_line(ws) and section != "skip":
            if SEC_SKIP.search(text):
                section = "skip"                       # sticky for the page
            elif SEC_CREDIT.search(text):
                section = "credit"
            elif SEC_DEBIT.search(text):
                section = "debit"
        if NOISE.search(text) or NOISE_APR.search(text) or section == "skip":
            continue

        ld = leading_dates(ws)
        if not ld:
            carry = text
            continue
        d1, d2, idx = ld
        monies = money_in_line(ws)
        monies = [m for m in monies if m[0] >= idx]
        prev, carry = carry, text
        if not monies:
            unmatched.append((os.path.basename(path), text))
            continue
        desc_words = [w["text"] for w in ws[idx:monies[0][0]]]
        while desc_words and desc_words[-1] in ("-", "+"):
            desc_words.pop()
        desc = " ".join(desc_words).strip()
        if _is_blank_desc(desc):
            # Amex wraps a long merchant name onto the line above the date,
            # leaving "03/15/26 $10.00" with nothing in between. The name is
            # still on the page, one line up.
            desc = prev if not _is_blank_desc(prev) else ""
        if _is_blank_desc(desc):
            unmatched.append((os.path.basename(path), text))
            continue
        cands.append({"d1": d1, "d2": d2, "desc": desc, "monies": monies,
                      "section": section, "text": text, "page": pi})

    # ---- decide which money column is the amount, one page at a time ----
    models = {}
    for pi in sorted({c["page"] for c in cands}):
        rows = [c for c in cands if c["page"] == pi]
        models[pi] = column_model(rows, page_headers.get(pi) or headers, amount_col)

    # Which way the amount column's sign points is a property of the statement,
    # not of the page. A last page carrying three rows has too little balance
    # movement to prove it on its own, so it inherits what the rest agreed on.
    votes = {m["polarity"] for m in models.values() if m["polarity"]}
    if len(votes) == 1:
        agreed = votes.pop()
        for m in models.values():
            if m["polarity"] is None and m["balance"] is not None:
                m["polarity"] = agreed

    if dump_columns:
        print(f"\n  columns for {os.path.basename(path)}:")
        for pi in sorted(models):
            m = models[pi]
            rows = [c for c in cands if c["page"] == pi]
            pol = {None: "sign not readable from the balance column",
                   1: "printed positive = money out (card)",
                   -1: "printed positive = money in (bank ledger, flipped)"}[m["polarity"]]
            print(f"    page {pi + 1}: {len(rows)} transaction-like lines, "
                  f"{m['multi'] * 100:.0f}% carry two or more amounts; {pol}")
            print(f"      headers: {page_headers.get(pi) or 'none on this page'}")
            for i, (cx, cov) in enumerate(zip(m["centers"], m["coverage"])):
                tags = []
                if i == m["balance"]: tags.append("BALANCE(ignored)")
                if i == m["credit"]: tags.append("CREDIT")
                if i == m["debit"]: tags.append("DEBIT")
                if i == m["amount"]: tags.append("AMOUNT")
                print(f"      col {i}: x={cx:7.1f}  on {cov * 100:5.1f}% of lines"
                      f"  {' '.join(tags) or '(used)'}")
            for c in rows[:4]:
                print(f"      e.g. {c['text'][:88]}")
                print(f"           amounts on the line: {[m2[1] for m2 in c['monies']]}")

    # ---- pass 2: emit ----
    txns, refs = [], []
    for c in cands:
        model = models[c["page"]]
        centers = model["centers"]
        balance_col, credit_col = model["balance"], model["credit"]
        debit_col = model["debit"]
        picks = []
        for _, val, x in c["monies"]:
            k = nearest(centers, x)
            if k is not None and k == balance_col:
                continue
            picks.append((k, val))
        if not picks:
            continue
        k, amount = picks[-1]          # rightmost non-balance value
        if amount is None or amount == 0:
            continue

        d = parse_date(c["d1"], ref_year)
        if d is None:
            continue
        # A year is printed only when there is a third component ("03/25/26",
        # "Jan 13 2026"). The old test accepted "12/04" as year-bearing, which
        # is exactly the case that needs re-yearing across New Year.
        printed_year = re.search(r"[/-]\d{1,2}[/-]\d{2,4}$|\s\d{4}$", c["d1"].strip())
        if not printed_year:
            if closing:
                # The period is the authority: a December line on a January
                # statement belongs to the year before the closing date.
                d = year_in_period(d, opening, closing)
            elif d.month > ref_month:
                d = d.replace(year=ref_year - 1)
            # Statements are never about the future. If the period couldn't be
            # read and we guessed a year that hasn't happened, walk it back.
            if d > date.today() + timedelta(days=45):
                d = d.replace(year=d.year - 1)
        pd_ = parse_date(c["d2"], d.year) if c["d2"] else None
        if pd_ and (pd_ - d).days < -300:      # posted in January, dated in December
            pd_ = pd_.replace(year=pd_.year + 1)

        desc = c["desc"]
        cat = categorize(desc)

        # sign: the running balance first (it is arithmetic, not a guess), then
        # the column, then the section, then keywords.
        if model["polarity"] is not None:
            amount = amount * model["polarity"]
        elif credit_col is not None and k == credit_col:
            amount = -abs(amount)
        elif debit_col is not None and k == debit_col:
            amount = abs(amount)
        else:
            if c["section"] == "credit" and amount > 0:
                amount = -amount
            if cat in ("Payment", "Credits/Refunds", "Income") and amount > 0:
                amount = -amount
            if re.search(r"\b(refund|reversal|return|cashback|cash back|"
                         r"statement credit|adjustment)\b", desc, re.I) \
                    and amount > 0 and c["section"] != "debit":
                amount = -amount

        txns.append(Transaction(
            date=d.isoformat(),
            post_date=pd_.isoformat() if pd_ else "",
            description=desc,
            merchant=clean_merchant(desc),
            amount=round(amount, 2),
            category=cat,
            issuer=issuer,
            account_last4=last4,
            statement_period=period,
            source_file=os.path.basename(path),
            page=c["page"] + 1,
            line=c["text"][:200],
        ))
        # Where on the page this row was read, for finances.verify's evidence.
        refs.append({"page": c["page"] + 1, "line": c["text"],
                     "raw": {"amount": next((str(v) for kk, v in picks if kk == k), "")}})

    # only consider non-transaction lines when looking for statement totals
    summary_text = "\n".join(
        ln for ln in full.split("\n")
        if not re.match(r"^\s*%s\s" % DATE_ANY, ln, re.I))

    fields = {}
    pairs = summary_pairs(all_lines)
    for key, rx in SUMMARY_LABELS:
        for label, value in pairs:
            if value is not None and rx.match(label):
                # Totals are magnitudes, but a balance is a position and its
                # sign is real: a checking account can close overdrawn and a
                # card can close in credit. Forcing abs() on those quietly
                # moves the account the wrong side of zero.
                if key in ("previous_balance", "new_balance"):
                    fields[key] = value
                else:
                    fields[key] = abs(value) if key != "payments" else -abs(value)
                break
    # Capital One splits money in over two labels; both are payments to us.
    if "payments" in fields:
        for label, value in pairs:
            if value and re.match(r"\s*other credits\b", label, re.I):
                fields["payments"] -= abs(value)
                break

    # A checking account has no purchases total, it has a withdrawals
    # breakdown; summed, that is the same quantity. Folding it into the same
    # two fields lets a bank statement be reconciled on the same terms as a
    # card statement.
    if "purchases" not in fields:
        outs = [v for label, v in pairs if v is not None and BANK_OUT.match(label)]
        if outs:
            fields["purchases"] = round(sum(abs(v) for v in outs), 2)
    if "payments" not in fields:
        ins = [v for label, v in pairs if v is not None and BANK_IN.match(label)]
        if ins:
            fields["payments"] = -abs(ins[0])

    for key, pat in LOOSE_FIELDS:
        if key in fields:
            continue
        m = re.search(pat, summary_text, re.IGNORECASE)
        if m:
            v = parse_money(m.group(1))
            if v is not None:
                fields[key] = abs(v)
    balance_note = _check_balances(fields)      # needs cash_advances, read above

    m = re.search(r"purchases?[^\n%]{0,70}?(\d{1,2}\.\d{2})\s*%", summary_text, re.I)
    if m:
        fields["purchase_apr"] = float(m.group(1))
    m = re.search(r"interest charged in \d{4}\s*:?\s*(%s)" % MONEY_INLINE, summary_text, re.I)
    if m:
        fields["ytd_interest"] = abs(parse_money(m.group(1)) or 0)
    m = re.search(r"fees charged in \d{4}\s*:?\s*(%s)" % MONEY_INLINE, summary_text, re.I)
    if m:
        fields["ytd_fees"] = abs(parse_money(m.group(1)) or 0)
    m = re.search(r"(?:rewards?|cash ?back|points?|miles)\s*(?:balance|available|earned)"
                  r"\s*:?\s*\$?([\d,]+(?:\.\d{2})?)", summary_text, re.I)
    if m:
        fields["rewards_balance"] = parse_money(m.group(1))

    if fields.get("credit_limit") and fields.get("new_balance") is not None:
        fields["utilization_pct"] = round(
            fields["new_balance"] / fields["credit_limit"] * 100, 1)

    n_in = sum(1 for t in txns if t.amount < 0)
    credit_share = n_in / len(txns) if txns else 0.0

    n_cols = max((len(m["centers"]) for m in models.values()), default=0)
    dropped = any(m["balance"] is not None for m in models.values())

    out_total = round(sum(t.amount for t in txns if t.amount > 0), 2)
    in_total = round(sum(-t.amount for t in txns if t.amount < 0), 2)
    statement = Statement(source_file=os.path.basename(path), issuer=issuer,
                          account_last4=last4, statement_period=period,
                          period_start=opening.isoformat() if opening else "",
                          period_end=closing.isoformat() if closing else "",
                          charges_extracted=out_total, credits_extracted=in_total,
                          source_format="pdf",
                          account_type="card" if (fields.get("credit_limit")
                                                  or fields.get("purchase_apr")) else "",
                          **fields)
    statement.payment_due = payment_due(full, closing)
    value = None if fields.get("minimum_payment") else investment_value(full)
    if value is not None:
        # A brokerage statement's activity is trades and dividends, not
        # spending: what it is read for is what the account is worth.
        txns, refs = [], []
        statement.account_type = "investment"
        statement.issuer = investment_issuer(full) or (issuer if issuer != "Unknown"
                                                       else "Investment")
        statement.previous_balance, statement.new_balance = value
        statement.charges_extracted = statement.credits_extracted = None
        statement.reconcile_note = ("Investment account: its value is read, not its "
                                    "trades, so there is nothing to reconcile.")
    else:
        reconcile(statement, txns, extra_note=balance_note)

    meta = {"statement": statement, "fields": fields,
            "pages": pages, "issuer": issuer, "last4": last4, "period": period,
            "columns": n_cols,
            "credit_share": credit_share,
            "balance_col_dropped": dropped,
            "unmatched": unmatched,
            "refs": refs,
            "raw_text": full if want_text else None}
    return txns, meta


# --------------------------------------------------------------------------
# Reconciliation — the only ground truth a statement offers is its own totals
# --------------------------------------------------------------------------

_DUE = re.compile(r"payment\s+due\s+date\s*:?\s*(\d{1,2}/\d{1,2}(?:/\d{2,4})?"
                  r"|[A-Z][a-z]{2,8}\.?\s+\d{1,2}(?:,?\s+\d{4})?)", re.I)


_VALUE = r"\$?\s*(-?[\d,]+\.\d{2})"
_ENDING_VALUE = re.compile(
    r"(?:(?:total|ending|closing|net)\s+(?:account|portfolio)\s+value"
    r"|your\s+(?:account|portfolio)\s+value|(?:ending|closing)\s+market\s+value)"
    r"\s*(?:as\s+of\s+[\w/ ,]+?)?:?\s*" + _VALUE, re.I)
_STARTING_VALUE = re.compile(
    r"(?:beginning|opening|starting)\s+(?:account\s+|portfolio\s+|market\s+)?value"
    r"\s*:?\s*" + _VALUE, re.I)
_BROKERAGE = re.compile(r"\b(brokerage|investment|portfolio|securities|holdings|"
                        r"ira|401\(?k\)?|roth)\b", re.I)
INVESTMENT_ISSUERS = _investment_issuers()


def investment_value(text: str):
    """(starting, ending) value of a brokerage statement, or None if it is not one.

    Only a statement that names an account or portfolio *value* counts: a
    checking statement prints an ending balance, never an account value, so
    this cannot claim a bank account.
    """
    m = _ENDING_VALUE.search(text or "")
    if not m or not _BROKERAGE.search(text):
        return None
    start = _STARTING_VALUE.search(text)
    num = lambda g: float(g.replace(",", ""))           # noqa: E731
    return (num(start.group(1)) if start else None), num(m.group(1))


def investment_issuer(text: str) -> str:
    low = (text or "").lower()
    hits = [(m.start(), name) for name, pat in INVESTMENT_ISSUERS
            for m in [re.search(pat, low)] if m]
    return min(hits)[1] if hits else ""


def payment_due(text: str, closing) -> str:
    """The card's payment due date, as ISO, or "" when none is printed.

    Card statements print it beside the minimum payment ("Payment Due Date
    12/22/25"). Without a printed year it is the first such date after the
    statement closes, which is how a January due date on a December statement
    lands in the right year.
    """
    m = _DUE.search(text or "")
    if not m:
        return ""
    ref = closing.year if closing else date.today().year
    d = parse_date(m.group(1), ref)
    if d is None:
        return ""
    has_year = re.search(r"\d{4}|\d{1,2}/\d{1,2}/\d{2}", m.group(1))
    if closing and not has_year and d < closing:
        d = d.replace(year=d.year + 1)
    return d.isoformat()


def read_payment_due(path, closing, password=None) -> str:
    """The due date printed on a statement PDF already in the store.

    Statements imported before due dates were read can get one without a full
    re-parse, which would also re-read and re-reconcile every transaction.
    """
    kwargs = {"password": password} if password else {}
    with pdfplumber.open(path, **kwargs) as pdf:
        full = "\n".join(words_text(ws) for page in pdf.pages for ws in page_lines(page))
    return payment_due(full, closing)


def _check_balances(fields):
    """Drop a previous balance that the statement's own arithmetic disowns.

    A statement is a closed system: the opening balance plus what happened
    equals the closing balance. Which way round depends on the account — a card
    balance goes *up* when you spend, a deposit balance goes down — so either
    identity is accepted. The check is worth running because "Previous Balance"
    is not a unique label: Discover prints one for the card and another, in the
    same box, for the cashback rewards pot, and the wrong one is off by
    thousands. A missing number is honest; a plausible wrong one is not.
    """
    prev, new = fields.get("previous_balance"), fields.get("new_balance")
    if prev is None or new is None:
        return ""
    out = fields.get("purchases") or 0.0
    extra = (fields.get("interest_charged") or 0.0) + (fields.get("fees_charged") or 0.0) \
        + (fields.get("cash_advances") or 0.0)
    money_in = abs(fields.get("payments") or 0.0)
    card = prev + out + extra - money_in          # a card balance grows as you spend
    bank = prev - out + money_in                  # a deposit balance shrinks
    if _agrees(card, new) or _agrees(bank, new):
        return ""
    del fields["previous_balance"]
    return (f"previous balance ${prev:,.2f} does not carry to ${new:,.2f}; "
            f"dropped rather than stored wrong")


def _agrees(extracted, printed):
    """Two cents, or half a percent of the printed figure, whichever is larger.

    Half a percent covers the rounding a statement does on a four-figure month
    without waving through a missing $30 charge on a small one.
    """
    return abs(extracted - printed) <= max(0.02, abs(printed) * 0.005)


def reconcile(statement, txns, extra_note=""):
    """Check the extraction against the statement's own totals, in place.

    Sets ``reconciled`` (1 pass, 0 fail, None nothing to compare),
    ``reconcile_diff`` (extracted purchases minus printed purchases) and
    ``reconcile_note``. Interest and fees are held out of both sides: every
    issuer here reports them separately from the purchases total, so counting
    them would make a correct parse look wrong by exactly the interest charge.

    ``extra_note`` carries anything the summary reader already knows about a
    figure it could not trust, so one field explains the whole statement.
    """
    purchases = statement.purchases
    payments = statement.payments
    charges = round(sum(t.amount for t in txns
                        if t.amount > 0 and not FEE_OR_INTEREST.search(t.description)), 2)
    credits = round(sum(-t.amount for t in txns if t.amount < 0), 2)

    results, notes = [], []
    if purchases is None:
        notes.append("statement prints no purchases or charges total")
    else:
        printed = abs(purchases)
        statement.reconcile_diff = round(charges - printed, 2)
        if _agrees(charges, printed):
            results.append(True)
        else:
            results.append(False)
            notes.append(f"purchases off by ${statement.reconcile_diff:+,.2f} "
                         f"(statement ${printed:,.2f}, extracted ${charges:,.2f})")

    if payments is None:
        if purchases is None:
            notes.append("and no payments total either")
    else:
        printed = abs(payments)
        if _agrees(credits, printed):
            results.append(True)
        else:
            results.append(False)
            notes.append(f"credits off by ${credits - printed:+,.2f} "
                         f"(statement ${printed:,.2f}, extracted ${credits:,.2f})")

    if extra_note:
        notes.append(extra_note)
    if not results:
        statement.reconciled = None
    elif all(results):
        statement.reconciled = 1
    else:
        statement.reconciled = 0
    statement.reconcile_note = "; ".join(notes)
    return statement


# --------------------------------------------------------------------------
# Driver
# --------------------------------------------------------------------------

def _find_pdfs(inp):
    if os.path.isdir(inp):
        return sorted(os.path.join(dp, f)
                      for dp, _, fs in os.walk(inp)
                      for f in fs if f.lower().endswith(".pdf"))
    return [inp]


def _ensure_writable(*targets):
    for target in targets:
        if not target:
            continue
        d = os.path.dirname(os.path.abspath(target))
        if os.path.isdir(d):
            continue
        try:
            os.makedirs(d, exist_ok=True)
            print(f"Created output folder {d}")
        except OSError as e:
            hint = ""
            if target.startswith("/"):
                hint = (f"\n  '{target}' starts with a slash, so it points at the top of "
                        f"the filesystem.\n  For a folder next to the script, drop the "
                        f"leading slash: -o {target.lstrip('/')}")
            sys.exit(f"Can't write to {target}: {e}{hint}")


def _parse_job(job):
    """Top-level (picklable) worker: parse one PDF, never raise."""
    path, password, amount_col, dump_columns, want_text = job
    try:
        txns, meta = parse_statement(path, password, amount_col, dump_columns, want_text)
        return path, txns, meta, None
    except Exception as e:
        msg = f"{type(e).__name__}: {e}".strip().rstrip(":")
        if any(w in msg.lower() for w in ("password", "encrypt", "pdfminer")):
            msg += "  -> looks encrypted; try --password YOURPASSWORD"
        return path, None, None, msg


def _report_file(name, txns, meta):
    """The per-file reconciliation block."""
    st = meta["statement"]
    out = sum(t.amount for t in txns if t.amount > 0)
    inn = sum(-t.amount for t in txns if t.amount < 0)
    print(f"  {name}")
    print(f"    {meta['issuer']} ****{meta['last4'] or '????'} | {meta['period'] or 'period ?'}"
          f" | {meta['pages']}p | {meta['columns']} money column(s)"
          f"{' | balance column dropped' if meta['balance_col_dropped'] else ''}")
    print(f"    {len(txns)} transactions | charges ${out:,.2f} | credits ${inn:,.2f}")
    if meta["credit_share"] > 0.6 and len(txns) >= 5:
        print(f"    !! {meta['credit_share'] * 100:.0f}% of these are credits — on a card "
              f"statement that is almost always a sign error, not a real month.")
        print(f"       Check --dump-columns for this file before trusting the output.")
    _print_reconcile(st)
    print()


def _print_reconcile(st):
    if st.reconciled == 1:
        print("    reconciles: OK" + (f" — but {st.reconcile_note}"
                                      if st.reconcile_note else ""))
    elif st.reconciled == 0:
        print(f"    reconciles: MISMATCH — {st.reconcile_note}")
        print("      re-run with --dump-columns for just this file to see why")
    else:
        print(f"    reconciles: cannot check — {st.reconcile_note or 'no totals printed'}")


def _statements_path(args):
    if args.statements:
        return args.statements
    if "transactions" in args.output:
        return os.path.splitext(args.output)[0].replace(
            "transactions", "statements") + "_statements.csv"
    return os.path.join(os.path.dirname(args.output) or ".", "statements.csv")


def main():
    ap = argparse.ArgumentParser(description="Extract transactions from statement PDFs into a CSV.")
    ap.add_argument("input", help="PDF file or folder of PDFs")
    ap.add_argument("-o", "--output", default="transactions.csv")
    ap.add_argument("--password", help="password for encrypted PDFs")
    ap.add_argument("--dump-text", metavar="DIR", help="write raw extracted text per PDF")
    ap.add_argument("--dump-columns", action="store_true",
                    help="show detected money columns per file (diagnostic)")
    ap.add_argument("--amount-col", choices=["auto", "last", "second-last"], default="auto",
                    help="override which money column is the transaction amount")
    ap.add_argument("--statements", metavar="CSV",
                    help="where to write per-statement summaries "
                         "(balances, interest, APR, credit limit)")
    ap.add_argument("--keep-duplicates", action="store_true")
    ap.add_argument("--db", default=DEFAULT_DB,
                    help=f"SQLite store for parsed data + parse cache (default {DEFAULT_DB})")
    ap.add_argument("--no-db", action="store_true",
                    help="don't read or write the SQLite store")
    ap.add_argument("--force", action="store_true",
                    help="re-parse every PDF even if it's unchanged in the cache")
    ap.add_argument("-j", "--jobs", type=int, default=0,
                    help="parallel worker processes (0 = auto, 1 = sequential)")
    ap.add_argument("--strict", action="store_true",
                    help="exit non-zero if any statement fails to reconcile "
                         "against its own printed totals")
    ap.add_argument("--llm", action="store_true", default=None,
                    help="when a statement's layout is not understood, have a local "
                         "model read it; kept only if it matches the printed totals "
                         "(also FINANCES_LLM_FALLBACK=1)")
    ap.add_argument("--llm-model", help="local model to use (default: largest that fits)")
    ap.add_argument("--llm-endpoint", help="OpenAI-compatible local server URL")
    ap.add_argument("--llm-accept-unverified", action="store_true",
                    help="keep the model's rows even when they do not reconcile "
                         "(labelled unverified)")
    args = ap.parse_args()
    if args.llm is None:
        from finances.llm_parse import enabled_by_env
        args.llm = enabled_by_env()

    pdfs = _find_pdfs(args.input)
    if not pdfs:
        sys.exit(f"No PDFs found in {args.input}")
    if args.dump_text:
        os.makedirs(args.dump_text, exist_ok=True)
    _ensure_writable(args.output, args.statements)

    db = None if args.no_db else FinanceDB(args.db)
    print(f"Found {len(pdfs)} PDF(s)"
          + ("" if SHARED_CATEGORIZER else
             "  (categorizer.py not found — using built-in rules)") + "\n")

    # --- split into cached (skip) and fresh (parse), keyed on content hash ---
    fresh, cached = [], []
    for path in pdfs:
        sha = file_sha256(path)
        if db is not None and not args.force and db.is_cached(path, sha):
            cached.append(path)
        else:
            fresh.append((path, sha))

    all_txns, unmatched, seen, periods, statements = [], [], set(), defaultdict(list), []

    def absorb(name, txns, statement):
        """Fold one file's results into the run-wide aggregates + CSV."""
        for t in txns:
            if not args.keep_duplicates and t.dedup_key in seen:
                continue
            seen.add(t.dedup_key)
            all_txns.append(t)
        periods[(statement.issuer, statement.account_last4,
                 statement.statement_period)].append(name)
        statements.append(statement)

    # --- cached files: pull straight from the store, no re-parse -----------
    for path in cached:
        name = os.path.basename(path)
        txns = db.transactions_for(name)
        srow = db.statement_for(name) or {"source_file": name}
        st = Statement.from_row(srow) if srow.get("source_file") else Statement(name)
        absorb(name, txns, st)
        print(f"  {name}\n    cached — {len(txns)} transactions (unchanged since last run)")
        _print_reconcile(st)
        print()

    # --- fresh files: parse (in parallel unless diagnosing) ----------------
    want_text = bool(args.dump_text)
    jobs = args.jobs or min(len(fresh), os.cpu_count() or 1)
    run_parallel = len(fresh) > 1 and jobs > 1 and not args.dump_columns

    def handle(path, txns, meta, err):
        name = os.path.basename(path)
        if err:
            print(f"  !! {name}: {err}")
            return
        if want_text and meta.get("raw_text") is not None:
            try:
                with open(os.path.join(args.dump_text, name + ".txt"), "w") as fh:
                    fh.write(meta["raw_text"])
            except OSError:
                pass
        _report_file(name, txns, meta)
        unmatched.extend(meta["unmatched"])
        statement = meta["statement"]
        if args.llm:
            from finances import llm_parse
            if llm_parse.needs_help(txns, statement):
                better = llm_parse.fallback(
                    path, statement, endpoint=args.llm_endpoint, model=args.llm_model,
                    password=args.password,
                    accept_unverified=args.llm_accept_unverified)
                if better:
                    txns, statement = better
                    _print_reconcile(statement)
                    print()
        if db is not None:
            db.upsert_transactions(txns)
            db.upsert_statements([statement])
            db.mark_parsed(path, sha_by_path[path], os.path.getmtime(path), len(txns))
        absorb(name, txns, statement)

    sha_by_path = dict(fresh)
    if run_parallel:
        joblist = [(p, args.password, args.amount_col, False, want_text) for p, _ in fresh]
        with ProcessPoolExecutor(max_workers=min(len(joblist), jobs)) as ex:
            for fut in as_completed(ex.submit(_parse_job, j) for j in joblist):
                handle(*fut.result())
    else:
        for path, _ in fresh:
            handle(*_parse_job((path, args.password, args.amount_col,
                                args.dump_columns, want_text)))

    if db is not None:
        db.close()

    if not all_txns:
        sys.exit("No transactions extracted. Try --dump-text ./raw to inspect the text layer.")

    for key, files in periods.items():
        if len(files) > 1 and key[2]:
            print(f"  ! duplicate statements for {key[0]} ****{key[1]} {key[2]}: {', '.join(files)}")

    all_txns.sort(key=lambda t: (t.date, t.source_file))
    _write_rows(args.output, Transaction.columns(), [t.to_row() for t in all_txns])

    if statements:
        spath = _statements_path(args)
        _write_rows(spath, Statement.columns(), [s.to_row() for s in statements])
        print(f"Wrote {len(statements)} statement summaries -> {spath}")

    if unmatched:
        log = os.path.splitext(args.output)[0] + "_unparsed.txt"
        with open(log, "w") as fh:
            for src, line in unmatched:
                fh.write(f"{src}\t{line}\n")
        print(f"{len(unmatched)} date-leading line(s) didn't parse -> {log}")

    _print_summary(all_txns, args.output, db_path=None if args.no_db else args.db)
    failed = _print_trust(statements)
    if args.strict and failed:
        sys.exit(f"\n--strict: {len(failed)} statement(s) do not reconcile.")


def _print_trust(statements):
    """The run-wide trust rate. Returns the statements that failed."""
    checked = [s for s in statements if s.reconciled is not None]
    good = [s for s in checked if s.reconciled == 1]
    bad = [s for s in checked if s.reconciled == 0]
    unchecked = [s for s in statements if s.reconciled is None]

    pct = (len(good) / len(checked) * 100) if checked else 0.0
    print(f"\nReconciliation: {len(good)} of {len(checked)} statements reconcile "
          f"({pct:.0f}%) — {len(statements)} parsed, {len(unchecked)} had no "
          f"printed total to check against")

    if bad:
        print("Worst mismatches — the dollar gap between the statement and what "
              "came out of it:")
        for s in sorted(bad, key=lambda s: -abs(s.reconcile_diff or 0))[:10]:
            gap = f"${abs(s.reconcile_diff):>10,.2f}" if s.reconcile_diff is not None \
                else "         ?"
            print(f"  {gap}  {s.source_file[:40]:<40} {s.reconcile_note}")
    if unchecked:
        print("Not checked: " + ", ".join(sorted(s.source_file for s in unchecked)[:8])
              + (" ..." if len(unchecked) > 8 else ""))
    return bad


def _write_rows(path, columns, rows):
    with open(path, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=columns, extrasaction="ignore")
        w.writeheader()
        w.writerows(rows)


def _print_summary(all_txns, output, db_path=None):
    out = [t for t in all_txns if t.amount > 0]
    moved = sum(t.amount for t in out)
    credit = sum(-t.amount for t in all_txns if t.amount < 0)
    # Spending is money out minus the money that only moved between accounts,
    # which is what the engine reports. Counting a card payment made from
    # checking as spending double-counts the purchases it settles.
    spend_txns = [t for t in out if t.category not in NON_SPEND]
    spend = sum(t.amount for t in spend_txns)
    by_cat = defaultdict(float)
    for t in spend_txns:
        by_cat[t.category] += t.amount

    print(f"\nWrote {len(all_txns)} transactions -> {output}"
          + (f"  (also stored in {db_path})" if db_path else ""))
    print(f"Total out ${moved:,.2f} (of which ${spend:,.2f} is spending, the rest "
          f"transfers and card payments) | total in ${credit:,.2f}")
    if spend_txns:
        print(f"Average charge ${spend / len(spend_txns):,.2f}  "
              f"(if this looks too high, run with --dump-columns)")

    print("\n10 largest charges — sanity check these against your statements:")
    for t in sorted(out, key=lambda t: -t.amount)[:10]:
        print(f"  {t.date}  ${t.amount:>10,.2f}  {t.merchant[:42]:<42} {t.source_file}")

    print("\nSpend by category:")
    for cat, amt in sorted(by_cat.items(), key=lambda x: -x[1]):
        print(f"  {cat:<18} ${amt:>12,.2f}  ({amt / spend * 100:4.1f}%)" if spend else f"  {cat}")


if __name__ == "__main__":
    main()