"""✱9 under its four readings: docs/STAR9_READINGS.md is up to date, its numbers are pinned, every
step PM justifies by definitions is checked under the working reading C except the one that C takes by
✱8·13, and where C uses ✱8·13 and L uses Switch is pinned.

An external review found that ✱9's disjunction did not follow ✱9·07·08 as printed; with the printed
definitions, the step (3)–(4) of PM's proof of ✱9·31, cited as definitional, is not a definitional
rewrite. Landini (2000, §4) had published the flaw. The repair (docs/REPAIRS.md) keeps the printed
reading (A), makes the definitions as printed with Russell's own rule ✱8·13 of the second edition
carried over to ✱9 (C) the working reading, keeps Landini's ✱9+ (L: ✱9·yy, ✱9·zz and his rule Switch)
as a published variant and cross-check, and keeps an alternative convention of our own (B) as a
cross-check. These tests pin the results of each reading, so that a change of a definition or a proof
that moves them fails until the docs say so.
"""
import importlib.util
import os
import re
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # for `common`, however the tests are run
from common import ROOT, run

spec = importlib.util.spec_from_file_location("star9_readings", ROOT / "scripts" / "star9_readings.py")
star9_readings = importlib.util.module_from_spec(spec)
spec.loader.exec_module(star9_readings)

DOC = ROOT / "docs" / "STAR9_READINGS.md"

# The summary of docs/STAR9_READINGS.md: row label prefix -> cells for A, C, L, B.
PINNED = {
    "numbered ✱9 propositions": ["27 of 28", "28 of 28", "28 of 28", "28 of 28"],
    "not derived": ["✱9·31", "none", "none", "none"],
    "✱10·01, ✱10·1, ✱10·11, ✱10·12": ["4 of 4", "4 of 4", "4 of 4", "4 of 4"],
    "p. 142, one apparent variable per letter": ["50 of 70", "65 of 70", "63 of 70", "67 of 70"],
    "\"by definitions\" steps": ["1", "1", "1", "0"],
    "exchange rule; steps of PM's own proofs": ["none (no rule)", "✱8·13: 1 (✱9·31, (3)–(4))",
                                                "Switch: 1 (✱9·31, (3)–(4))", "none (no rule)"],
    "results whose proofs use the rule": ["—", "✱9·31; 15 combinations of p. 142",
                                          "✱9·31, ✱10·1; 15 combinations of p. 142", "—"],
}
# The column heads, in this order.
HEADS = ["A, as printed", "C, as printed + ✱8·13 (working, default)",
         "L, Landini's ✱9+ (published variant, cross-check)", "B, alternative convention (cross-check)"]
# The steps PM justifies by definitions that are definitional rewrites under one reading only.
ONE_READING_STEPS = [("f9_31", "[(3).(✱9·03·02)] (4)", "only:B")]
# Where C uses ✱8·13 and L uses Switch (section "Where the exchange rule is used").
RULES = [
    r"- C, ✱8·13: 1\. ✱9·31, step \(3\)–\(4\), in `f9_31_russell` \(1 occurrence, 1 of \(x\)\(∃y\)\)\.",
    r"- L, Switch: 1\. ✱9·31, step \(3\)–\(4\), in `f9_31_switch` \(1 occurrence, 1 of \(x\)\(∃y\)\)\.",
    r"\| ✱9·31 \| `f9_31_russell` \| no \| 1 \| 1 \| `f9_31_switch` \| A does not derive it \| 1 \| 1 \| `f9_31_switch` \|",
    r"\| ✱10·1 \| for every reading \| yes \| 0 \| 0 \| for every reading \| no \| 0 \| 1 \| `exDrinker_plus` \|",
    r"Of 70 combinations, C proves 65: 50 without ✱8·13\n\(exactly those derived under A, the same propositions\), and 15 with it; 5 are\nnot covered\. L proves 63: 48 without Switch",
    r"that need ✱8·13 at all are ✱9·31, and, of the 70 combinations of p\. 142, 15,\nwith 1–2 steps each \(16 of \(x\)\(∃y\), 3 of \(∃x\)\(∃y\)\); 5 combinations are not covered in C",
]


def summary():
    rows = {}
    for line in DOC.read_text(encoding="utf-8").splitlines():
        if line.startswith("| "):
            cells = [c.strip() for c in line.strip("|").split("|")]
            rows[cells[0]] = cells[1:]
    return rows


class Star9Readings(unittest.TestCase):
    def test_report_up_to_date(self):
        code, out = run([sys.executable, "scripts/star9_readings.py", "--check"])
        self.assertEqual(code, 0, out)

    def test_column_order(self):
        """The columns are A, C, L, B: as printed, the working reading, Landini's variant, the
        cross-check."""
        text = DOC.read_text(encoding="utf-8")
        self.assertIn("| | " + " | ".join(HEADS) + " |", text)

    def test_pinned_numbers(self):
        rows = summary()
        for prefix, cells in PINNED.items():
            with self.subTest(row=prefix):
                hits = [k for k in rows if k.startswith(prefix)]
                self.assertEqual(len(hits), 1, f"rows starting with {prefix!r}: {hits}")
                self.assertEqual(rows[hits[0]][:4], cells)

    def test_by_defs_steps_exact_under_working_reading(self):
        """Every line of ✱9's proofs that PM justifies by definitions (✱1·01, ✱9·01–✱9·08) is checked
        by Lean as a definitional rewrite under the working reading C, with `by_defs` in a proof for
        every reading (checked under the definitions as printed, which A and C share, and those of L
        and B), except the step (3)–(4) of ✱9·31, which is a definitional rewrite under B only and
        which C takes by ✱8·13."""
        steps = star9_readings.definitional_steps()
        self.assertGreater(len(steps), 40)
        for thm, line, cite, how in steps:
            with self.subTest(theorem=thm, line=line, cite=cite):
                self.assertIn(how, ("ACLB", "only:B"), "a definitional step not checked under C")
        self.assertEqual([(t, c, h) for t, _, c, h in steps if h != "ACLB"], ONE_READING_STEPS)

    def test_disagreeing_step_is_proved_different_and_taken_by_the_rule(self):
        """The step checked under B only is shown to fail under the definitions as printed and those of
        L by theorems (`f9_31_step`, `f9_31_step_plus`), cited in the report; C takes it by ✱8·13 in
        `f9_31_russell`, L by Switch in `f9_31_switch`."""
        text = DOC.read_text(encoding="utf-8")
        self.assertRegex(text, r"\| `f9_31` \| \d+ \| `\[\(3\)\.\(✱9·03·02\)\] \(4\)` \| B \| different propositions in A and C \(`f9_31_step`\) and in L \(`f9_31_step_plus`\); in C the step is taken by ✱8·13 \(`f9_31_russell`\), in L by Switch \(`f9_31_switch`\) \|")
        star9 = (ROOT / "PM" / "Found9" / "Star9.lean").read_text(encoding="utf-8")
        self.assertRegex(star9, r"theorem f9_31_step \(d : ∀ τ, V τ\)")
        self.assertRegex(star9, r"theorem f9_31_step_plus \(d : ∀ τ, V τ\)")
        self.assertRegex(star9, r"Thm9\.exch rfl \(k₁ := true\) \(k₂ := false\)\n\s+\(\.all fun x => \.here")
        self.assertRegex(star9, r"Thm9\.switch rfl \(\.all fun x => \.here")

    def test_where_the_rule_is_used(self):
        """The measured uses of ✱8·13 in C and of Switch in L are pinned (docs/STAR9_READINGS.md,
        "Where the exchange rule is used")."""
        text = DOC.read_text(encoding="utf-8")
        for pattern in RULES:
            with self.subTest(pattern=pattern):
                self.assertRegex(text, pattern)


if __name__ == "__main__":
    unittest.main()
