"""
Banks: one file per bank, a made-up statement per bank, and the scrambled
layout people attach when their bank does not read.

Every layout in tests/fixtures/banks/ is invented by hand (see its header). Each
one is rendered to a PDF and parsed the way a real statement is: it has to be
read as its bank, find the number of transactions its header says, and
reconcile against its own printed totals.
"""

from __future__ import annotations

import glob
import io
import os
import random
import re
import unittest
from contextlib import redirect_stdout

import support

FIXTURES = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fixtures", "banks")
LAYOUTS = sorted(glob.glob(os.path.join(FIXTURES, "*.txt")))

if support.has_pdfplumber():
    from finances import banks, layout, parse


@unittest.skipUnless(support.has_pdfplumber(), "pdfplumber is not installed")
class BankFilesTest(unittest.TestCase):
    def test_every_bank_file_is_well_formed(self):
        names, allowed = set(), {"name", "statements", "investments", "notes", "guide", "slug"}
        for b in banks.load():
            with self.subTest(bank=b["slug"]):
                self.assertTrue(b.get("name"))
                self.assertNotIn(b["name"], names, "two files name the same bank")
                names.add(b["name"])
                self.assertLessEqual(set(b), allowed, "unknown keys")
                self.assertTrue(b.get("statements") or b.get("investments") or b.get("guide"))
                for key in ("statements", "investments"):
                    if b.get(key):
                        re.compile(b[key])
                        # Searched in lowercased text, so an uppercase letter never matches.
                        self.assertEqual(re.sub(r"\\.", "", b[key]),
                                         re.sub(r"\\.", "", b[key]).lower())
                if b.get("guide"):
                    self.assertLessEqual(set(b["guide"]), set(banks.GUIDE_KEYS))
                    self.assertTrue(b["guide"].get("url", "").startswith("https://"))

    def test_the_parser_reads_its_bank_list_from_the_files(self):
        self.assertEqual(parse.ISSUERS, banks.issuers())
        self.assertEqual(parse.detect_issuer("statement from americanexpress.com"), "Amex")
        self.assertEqual(parse.detect_issuer("Visit capitalone.com"), "Capital One")
        self.assertEqual(parse.investment_issuer("Fidelity Brokerage Services"), "Fidelity")

    def test_guides_come_from_the_same_files(self):
        from finances import sources
        g = sources.guide("Chase")
        self.assertEqual(g["bank"], "Chase")
        self.assertTrue(g["steps"])


@unittest.skipUnless(support.has_pdfplumber(), "pdfplumber is not installed")
class FixturesTest(unittest.TestCase):
    def test_there_are_fixtures(self):
        self.assertGreaterEqual(len(LAYOUTS), 5)

    def test_every_fixture_is_read_as_its_bank_and_reconciles(self):
        known = {b["name"] for b in banks.load()}
        for path in LAYOUTS:
            with self.subTest(fixture=os.path.basename(path)):
                with open(path, encoding="utf-8") as fh:
                    text = fh.read()
                want = layout.header(text)
                self.assertIn(want.get("bank"), known, "the header names a bank with no file")
                self.assertTrue(want.get("transactions", "").isdigit())
                r = layout.check(text, path)
                self.assertEqual(r["problems"], [])
                for t in r["txns"]:
                    self.assertTrue(t.description.strip(), "a row with no description")

    def test_capital_one_payment_description_has_no_trailing_sign(self):
        """Capital One prints credits as '- $640.00'; the lone sign must not stay in the description."""
        path = os.path.join(FIXTURES, "capital-one.txt")
        with open(path, encoding="utf-8") as fh:
            text = fh.read()
        r = layout.check(text, path)
        self.assertEqual(r["problems"], [])
        payment = next(t for t in r["txns"] if "CAPITAL ONE ONLINE PYMT" in t.description)
        self.assertEqual(payment.description, "CAPITAL ONE ONLINE PYMT")
        self.assertLess(payment.amount, 0)  # credit / money in

    def test_fixtures_are_named_after_their_bank(self):
        slugs = {b["name"]: b["slug"] for b in banks.load()}
        for path in LAYOUTS:
            with open(path, encoding="utf-8") as fh:
                bank = layout.header(fh.read())["bank"]
            self.assertTrue(os.path.basename(path).startswith(slugs[bank]),
                            f"{os.path.basename(path)} should start with {slugs[bank]}")


def lines(text: str) -> list[str]:
    """A layout's text lines; blank lines are spacing and do not survive a PDF."""
    return [ln for page in layout.body_pages(text) for ln in page + [layout.PAGE_BREAK] if ln]


@unittest.skipUnless(support.has_pdfplumber(), "pdfplumber is not installed")
class LayoutTest(support.TempDirMixin, unittest.TestCase):
    def amex(self) -> str:
        with open(os.path.join(FIXTURES, "amex.txt"), encoding="utf-8") as fh:
            return fh.read()

    def pdf(self, text: str, name: str = "statement.pdf") -> str:
        path = os.path.join(self.tmpdir, name)
        with open(path, "wb") as fh:
            fh.write(layout.to_pdf(text))
        return path

    def test_a_pdf_turns_back_into_the_same_layout(self):
        text = self.amex()
        again = layout.from_pdf(self.pdf(text), scramble=False)
        self.assertEqual(lines(again), lines(text))

    def test_scrambling_keeps_the_layout_and_drops_the_details(self):
        path = self.pdf(self.amex())
        out = layout.from_pdf(path, rng=random.Random(3))
        body = "\n".join("\n".join(p) for p in layout.body_pages(out))
        for secret in ("Jordan", "JORDAN", "Example Street", "BLUE BOTTLE", "NETFLIX",
                       "1,204.18", "54.31", "41005"):
            self.assertNotIn(secret, body)
        for kept in ("American Express", "Previous Balance", "New Balance",
                     "Payments/Credits", "03/12/26", "03/15/26*"):
            self.assertIn(kept, body)
        # Same columns, same rows read, same bank: only the content changed.
        self.assertEqual([len(ln) for ln in lines(out)], [len(ln) for ln in lines(self.amex())])
        r = layout.check(out, path)
        self.assertEqual((r["bank"], r["transactions"]), ("Amex", 7))

    def test_a_repeated_value_is_scrambled_the_same_way(self):
        out = layout.from_pdf(self.pdf(self.amex()), rng=random.Random(5))
        prev = next(ln for ln in lines(out) if "Previous Balance" in ln).split()[-1]
        paid = next(ln for ln in lines(out) if "Payments/Credits" in ln).split()[-1]
        self.assertEqual("-" + prev, paid)

    def test_the_header_says_what_was_read(self):
        out = layout.from_pdf(self.pdf(self.amex()), rng=random.Random(1))
        h = layout.header(out)
        self.assertEqual(h["bank"], "Amex")
        self.assertEqual(h["transactions"], "7")
        self.assertEqual(h["verdict on the original"], "reconciles")
        self.assertIn("new_balance", h["summary figures found"])

    def test_report_bank_writes_a_file_and_check_reads_it(self):
        src = self.pdf(self.amex(), "Amex-March.pdf")
        out = os.path.join(self.tmpdir, "layout.txt")
        with redirect_stdout(io.StringIO()) as buf:
            self.assertEqual(layout.main([src, "-o", out]), 0)
        self.assertIn("Amex: 7 transactions read, reconciles", buf.getvalue())
        with redirect_stdout(io.StringIO()):
            # Scrambled amounts no longer add up, which --check reports.
            self.assertEqual(layout.main(["--check", out]), 1)
            self.assertEqual(layout.main(["--check", os.path.join(FIXTURES, "amex.txt")]), 0)


if __name__ == "__main__":
    unittest.main()
