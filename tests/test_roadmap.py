"""The roadmap's charts and generated text equal what data/roadmap.json gives, and the charts pass check_svg.py.

The roadmap is written once, as data, and drawn and listed from it by scripts/roadmap_chart.py: the SVG
charts in docs/roadmap/, the overview and nested lists of README.md, and the tables, milestones and lists
of docs/ROADMAP.md (the text between `<!-- generated:… -->` markers), with the counts its notes cite read
from docs/PROGRESS.md, docs/PM_CLAIMS.md and data/star9f_ledger.json. A hand edit of any of them, or a
change to the data or to those counts without regenerating, would let the files drift apart.

Here `roadmap_chart.py --check` regenerates everything in memory and fails if a committed file differs, or
if docs/roadmap/ holds a chart the data does not give; and scripts/check_svg.py checks every committed chart
on its own terms (well-formed XML, a dark-mode block, no scripts or external references, no text outside the
image, no two texts overlapping, with width estimates independent of the drawing code's).
"""
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # for `common`, however the tests are run
from common import ROOT, run

CHARTS = ROOT / "docs" / "roadmap"


class Roadmap(unittest.TestCase):
    def test_generated_files_are_up_to_date(self):
        code, out = run([sys.executable, "scripts/roadmap_chart.py", "--check"], timeout=300)
        self.assertEqual(code, 0, out)
        self.assertIn("up to date", out)

    def test_charts_pass_the_independent_check(self):
        svgs = sorted(str(p.relative_to(ROOT)) for p in CHARTS.glob("*.svg"))
        self.assertTrue(svgs, "no charts in docs/roadmap/")
        code, out = run([sys.executable, "scripts/check_svg.py", *svgs], timeout=300)
        self.assertEqual(code, 0, out)
        self.assertEqual(out.count("ok   "), len(svgs), out)
        for p in CHARTS.glob("*.svg"):
            self.assertIn("@media (prefers-color-scheme: dark)", p.read_text(encoding="utf-8"), p.name)


if __name__ == "__main__":
    unittest.main()
