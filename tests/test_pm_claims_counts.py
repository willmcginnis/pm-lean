"""The totals in docs/PM_CLAIMS.md's "Counts" paragraph equal a recount of the table rows.

When rows were added or changed status, the totals had to be recounted by hand (a merge left two
versions of the paragraph, 26 and 28 checked, where a recount gave 27). Here each clause of the paragraph
("29 checked (...)", "and 2 more partly checked with the rest in progress", ...) is matched to the
statuses it counts, every row's status must be counted by exactly one clause, and the numbers must
agree. A new kind of status fails until the paragraph says how it is counted.
"""
import os
import re
import sys
import unittest
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # for `common`, however the tests are run
from common import ROOT

CLAIMS = ROOT / "docs" / "PM_CLAIMS.md"

# (pattern of a clause of the Counts paragraph, the row statuses it counts), first match wins.
CLAUSES = [
    (r"checked for ✱10's method, with ✱9's in progress", lambda s: s == "checked for ✱10's method; in progress for ✱9's"),
    (r"checked for one part and not attempted for the other", lambda s: s == "checked (use); not attempted (necessity)"),
    (r"in progress for one part and not attempted for the other", lambda s: s == "in progress (use); not attempted (necessity)"),
    (r"more partly checked with the rest in progress", lambda s: s == "partly checked; in progress"),
    (r"partly checked", lambda s: s == "partly checked"),
    (r"does not hold as stated", lambda s: s == "does not hold as stated"),
    (r"checked", lambda s: s == "checked" or s.startswith("checked, ")),
    (r"assumed", lambda s: s == "assumed"),
    (r"not attempted", lambda s: s == "not attempted"),
    (r"in progress", lambda s: s == "in progress"),
]


def rows():
    """{row id: status} of every table row of PM_CLAIMS.md."""
    out = {}
    for line in CLAIMS.read_text(encoding="utf-8").splitlines():
        if re.match(r"\| [A-Z]\d+ \|", line):
            cells = [c.strip() for c in line.split("|")]
            out[cells[1]] = cells[4]
    return out


def counts_paragraph():
    """(total, [(number, clause text)]) from the paragraph starting "Of the N rows:"."""
    text = " ".join(CLAIMS.read_text(encoding="utf-8").split())
    m = re.search(r"Of the (\d+) rows: (.*?)\.(?: \(|$)", text)
    if not m:
        raise AssertionError("docs/PM_CLAIMS.md: the paragraph 'Of the N rows: ...' was not found")
    parts = []
    # split on ";" and on ", and N more": each part starts with its number
    for part in re.split(r";\s*|,\s*and (?=\d+ more)", m.group(2)):
        n = re.match(r"\s*(\d+) (.*)", part)
        if not n:
            raise AssertionError(f"PM_CLAIMS.md counts: a clause without a number: {part!r}")
        parts.append((int(n.group(1)), n.group(2)))
    return int(m.group(1)), parts


class PMClaimsCounts(unittest.TestCase):
    def test_total(self):
        total, parts = counts_paragraph()
        self.assertEqual(total, len(rows()), "the number of rows")
        self.assertEqual(sum(n for n, _ in parts), total, "the clauses add up to the total")

    def test_clauses(self):
        statuses = rows()
        _, parts = counts_paragraph()
        counted = Counter()
        for n, text in parts:
            with self.subTest(clause=text):
                kind = next((i for i, (pat, _) in enumerate(CLAUSES) if re.match(pat, text)), None)
                self.assertIsNotNone(kind, f"no rule for the clause {text!r}")
                self.assertNotIn(kind, counted, f"two clauses of the same kind: {text!r}")
                ids = sorted(r for r, s in statuses.items() if CLAUSES[kind][1](s))
                counted[kind] = len(ids)
                self.assertEqual(n, len(ids), f"{text!r} counts {ids}")
        for r, s in statuses.items():
            with self.subTest(row=r):
                kinds = [k for k in counted if CLAUSES[k][1](s)]
                self.assertEqual(len(kinds), 1, f"row {r}: status {s!r} is counted by {len(kinds)} clauses")

    def test_examples_named_in_the_paragraph(self):
        """Rows the paragraph names in parentheses, e.g. "(B4)", "(A11)", have the status of their clause."""
        statuses = rows()
        _, parts = counts_paragraph()
        for n, text in parts:
            kind = next(i for i, (pat, _) in enumerate(CLAUSES) if re.match(pat, text))
            for r in re.findall(r"\b([A-F]\d+)\b", text):
                with self.subTest(clause=text, row=r):
                    self.assertIn(r, statuses)
                    self.assertTrue(CLAUSES[kind][1](statuses[r]), f"{r} has status {statuses[r]!r}")


if __name__ == "__main__":
    unittest.main()
