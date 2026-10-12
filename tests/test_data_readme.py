"""The row counts data/README.md gives for each ledger file equal the files' own counts.

An external review found that data/README.md gave the ✱20 and ✱21 ledgers 51 and 44 rows (49 and 42
assertions) after rows had been added: the files have 53 and 46 (51 and 44 assertions, 2 rules each).
Here the "Rows per file" sentence is read entry by entry, `name` N or `name` N (A assertions, R rules),
and every number is compared with the ledger; every ledger of the second schema must be listed. Unlike
test_proved_counts.py, a sentence that is no longer found fails: it is this file's own documentation.
"""
import os
import re
import sys
import unittest
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # for `common`, however the tests are run
from common import DATA, STAR_LEDGERS, ledger

README = DATA / "README.md"
ENTRY = re.compile(r"`(\w+)` (\d+)(?: \((\d+) assertions, (\d+) rules\)| \((the primitive propositions))?")


def rows_per_file():
    """The sentence's entries: {name: (rows, assertions, rules, whether all rows are primitive)}."""
    text = " ".join(README.read_text(encoding="utf-8").split())
    m = re.search(r"Rows per file: (.*?)\. There is no ledger", text)
    if not m:
        raise AssertionError("data/README.md: the sentence 'Rows per file: ...' was not found")
    out = {}
    for e in ENTRY.finditer(m.group(1)):
        name, n, a, r, p = e.groups()
        out[name] = (int(n), a and int(a), r and int(r), p is not None)
    return out


class DataReadmeCounts(unittest.TestCase):
    def test_every_ledger_listed(self):
        self.assertEqual(sorted(rows_per_file()), sorted(["replay2"] + STAR_LEDGERS))

    def test_counts(self):
        for name, (n, a, r, p) in rows_per_file().items():
            rows = ledger(name)
            c = Counter(row.get("category") for row in rows)
            with self.subTest(name):
                self.assertEqual(n, len(rows), "rows")
                if a is not None:
                    self.assertEqual((a, r), (c["assertion"], c["rule/prose"]), "assertions, rules")
                    self.assertEqual(a + r, n, "assertions + rules")
                if p:
                    self.assertEqual(c["primitive"], n, "primitive propositions")

    def test_replay_ledger_rows(self):
        m = re.search(r"\*\*`replay_ledger\.json`\*\* \((\d+) rows", README.read_text(encoding="utf-8"))
        self.assertIsNotNone(m, "data/README.md: the replay_ledger.json heading was not found")
        self.assertEqual(int(m.group(1)), len(ledger("replay")))


if __name__ == "__main__":
    unittest.main()
