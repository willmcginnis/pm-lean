"""The ledgers' fidelity fields are consistent, and the Fidelity table shows what they count.

A review found ledger rows that listed chain glue or their own tacit steps in extra_used.
fidelity_counts.py reports such rows (and rows whose fidelity disagrees with extra_used) as indented
lines; there must be none. The table of the three counts (README.md, Fidelity, or wherever the docs
move it) must equal the script's output.
"""
import os
import re
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # for `common`, however the tests are run
from common import COUNTED, docs_text, find_script, run

LINE = re.compile(r"^(star\d+): (\d+) proofs; pm-lines strict (\d+), as recorded (\d+), glue tacit (\d+)$")
ROW = re.compile(r"^\|\s*✱(\d+) \((\d+)\)\s*\|\s*(\d+) / (\d+)\s*\|\s*(\d+) / (\d+)\s*\|\s*(\d+) / (\d+)\s*\|\s*$")


def script_output():
    code, out = run([sys.executable, str(find_script("fidelity_counts.py"))])
    if code != 0:
        raise AssertionError(out)
    return out.splitlines()


class FidelityCounts(unittest.TestCase):
    def test_no_inconsistency_lines(self):
        bad = [l for l in script_output() if not LINE.match(l)]
        self.assertEqual(bad, [], "fidelity_counts.py reports inconsistent rows")

    def test_every_chapter_counted(self):
        chapters = [LINE.match(l).group(1) for l in script_output() if LINE.match(l)]
        self.assertEqual(chapters, COUNTED)

    def test_table_matches_script(self):
        counts = {}
        for l in script_output():
            m = LINE.match(l)
            if m:
                counts[m.group(1)] = tuple(int(g) for g in m.groups()[1:])
        table = {}
        for l in docs_text().splitlines():
            m = ROW.match(l.strip())
            if m:
                n, a, b, c, d, e, f = (int(g) for g in m.groups()[1:])
                key = f"star{m.group(1)}"
                self.assertNotIn(key, table, f"two table rows for ✱{m.group(1)}")
                for pm, extra in [(a, b), (c, d), (e, f)]:
                    self.assertEqual(pm + extra, n, f"table row {l.strip()!r}: columns do not add up")
                table[key] = (n, a, c, e)
        self.assertEqual(table, counts, "the Fidelity table (proofs, strict, as recorded, glue tacit)")


if __name__ == "__main__":
    unittest.main()
