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

Dependencies are also stated in words in docs/ROADMAP.md ("the second stage gates pm.mm beyond ✱5", "are
helped by the finite core"). `roadmap_chart.prose_deps_errors` reads every sentence of the page's hand-written
prose: each one that uses a gate word (needs, gates, waits for, requires, ...) or a soft word (helps,
benefits) must end with a `<!-- deps: ... -->` comment naming its dependencies as task ids; each `gates`
pair must be a hard dependency in the data, each `helps` pair a soft one, each `not` pair no hard one; and
gate wording may carry only gates clauses, soft wording only helps clauses. The mutation tests below change
the page's own wording and annotations and check that the check fails, so that prose cannot say "gated by"
where the graph has "helped by", or the reverse, or name an edge the graph does not have.
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
PAGE = ROOT / "docs" / "ROADMAP.md"


def mutated(old, new):
    """docs/ROADMAP.md with its one occurrence of `old` replaced by `new`."""
    text = PAGE.read_text(encoding="utf-8")
    assert text.count(old) == 1, f"expected one occurrence of {old!r}"
    return text.replace(old, new)


class Roadmap(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        _, cls.leaves, _ = roadmap_chart.load()

    def errors(self, text):
        return roadmap_chart.prose_deps_errors(text, self.leaves)

    def assertFails(self, text, fragment):
        errs = self.errors(text)
        self.assertTrue(any(fragment in e for e in errs), f"expected an error with {fragment!r}, got {errs}")

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

    def test_dependencies_stated_in_the_prose_match_the_data(self):
        text = PAGE.read_text(encoding="utf-8")
        self.assertEqual(self.errors(text), [])
        notes = [n for _, n in roadmap_chart.prose_sentences(text) if n is not None]
        self.assertGreater(sum("gates" in n for n in notes), 10, "too few gates annotations; is the parser reading the page?")
        self.assertTrue(any("helps" in n for n in notes), "no helps annotation on the page")

    def test_every_dependency_item_states_its_gates(self):
        text = PAGE.read_text(encoding="utf-8")
        section = text.split("### Waits for a dependency", 1)[1].split("\n### ", 1)[0]
        items = re.split(r"\n(?=- \*\*)", section)[1:]
        self.assertTrue(items, "no items under 'Waits for a dependency'")
        for item in items:
            self.assertRegex(item, r"<!-- deps: gates ", f"item without a gates annotation: {item[:60]!r}")

    # Mutations of the page: each must make the check fail.

    def test_helped_by_changed_to_gated_by_fails(self):
        self.assertFails(mutated("are helped by the finite core", "are gated by the finite core"),
                         "a helps clause, but no soft word")

    def test_helped_by_changed_to_gated_by_with_its_annotation_fails(self):
        # The finding that started this test: the core (adq-2) was said to gate ✱8 and Appendix A (e2-8a),
        # where the data makes it a soft dependency only.
        text = mutated("are helped by the finite core", "are gated by the finite core")
        text = text.replace("v1-9-14 > e2-c; helps adq-2 > e2-8a", "v1-9-14 > e2-c; adq-2 > e2-8a")
        self.assertFails(text, "says adq-2 gates e2-8a, but adq-2 is not a hard dependency of e2-8a")

    def test_gates_changed_to_helps_fails(self):
        self.assertFails(mutated("first-order core) gates pm.mm", "first-order core) helps pm.mm"),
                         "but the annotation has no helps clause")

    def test_does_not_gate_changed_to_gates_fails(self):
        self.assertFails(mutated("but does not gate it", "but gates it"), "but the annotation has no gates clause")

    def test_an_annotation_naming_an_edge_the_data_does_not_have_fails(self):
        self.assertFails(mutated("gates v1-rep > v1-both", "gates v1-both > v1-rep"),
                         "says v1-both gates v1-rep, but v1-both is not a hard dependency of v1-rep")
        self.assertFails(mutated("gates v1-rep > v1-both", "gates v1-rep > v1-nonesuch"),
                         "names an unknown task")
        self.assertFails(mutated("helps adq-2 > e2-8a; not", "helps v1-9eq > e2-8a; not"),
                         "says v1-9eq helps e2-8a, but v1-9eq is not a soft dependency of e2-8a")

    def test_a_dependency_sentence_without_an_annotation_fails(self):
        self.assertFails(mutated("<!-- deps: gates v1-rep > v1-both -->", ""), "has no deps annotation")
        self.assertFails("A needs B, and C is helped by D.\n", "has no deps annotation")


if __name__ == "__main__":
    unittest.main()
