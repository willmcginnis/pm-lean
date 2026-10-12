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

The prose of docs/ROADMAP.md states gates in words ("the finite core gates pm.mm beyond ✱5"). Each such
sentence carries a comment `<!-- gates: A > B C; … -->`; here every pair it names must be a gate in the
data (A among the hard dependencies of B, directly or through other tasks), and every item of the "Waits
for a dependency" list must carry one, so that prose cannot name a gate the graph does not have.
"""
import os
import re
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # for `common`, however the tests are run
from common import ROOT, run

sys.path.insert(0, str(ROOT / "scripts"))
import roadmap_chart  # noqa: E402

CHARTS = ROOT / "docs" / "roadmap"
GATES = re.compile(r"<!-- gates: (.*?) -->")


def stated_gates(text):
    """The (needed, needing) pairs named by the gates comments of a text."""
    pairs = []
    for body in GATES.findall(text):
        for clause in body.split(";"):
            before, _, after = clause.partition(">")
            for a in before.split():
                pairs += [(a, b) for b in after.split()]
    return pairs


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

    def test_gates_named_in_prose_are_gates_in_the_data(self):
        _, leaves, _ = roadmap_chart.load()
        text = (ROOT / "docs" / "ROADMAP.md").read_text(encoding="utf-8")
        pairs = stated_gates(text)
        self.assertTrue(pairs, "no gates comments in docs/ROADMAP.md")
        for a, b in pairs:
            self.assertIn(a, leaves, f"gates comment names an unknown task {a}")
            self.assertIn(b, leaves, f"gates comment names an unknown task {b}")
            self.assertIn(a, roadmap_chart.ancestors(leaves, b),
                          f"the prose says {a} gates {b}, but {a} is not a hard dependency of {b} in the data")

    def test_every_dependency_item_states_its_gates(self):
        text = (ROOT / "docs" / "ROADMAP.md").read_text(encoding="utf-8")
        section = text.split("### Waits for a dependency", 1)[1].split("\n### ", 1)[0]
        items = re.split(r"\n(?=- \*\*)", section)[1:]
        self.assertTrue(items, "no items under 'Waits for a dependency'")
        for item in items:
            self.assertRegex(item, GATES, f"item without a gates comment: {item[:60]!r}")

    def test_the_check_catches_a_gate_the_data_does_not_have(self):
        # The finding that started this test: the core (adq-2) was said to gate ✱8 and Appendix A (e2-8a),
        # where the data makes it a soft dependency only.
        _, leaves, _ = roadmap_chart.load()
        (a, b), = stated_gates("<!-- gates: adq-2 > e2-8a -->")
        self.assertNotIn(a, roadmap_chart.ancestors(leaves, b))


if __name__ == "__main__":
    unittest.main()
