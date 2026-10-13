"""The source editor of scripts/mutation/mutate.py, and its list of examined findings.

`mutate.py --full` recompiles theorems with one hypothesis replaced by `True` (a class argument removed),
editing a copy of the source file (docs/STATEMENT_MUTATION.md). An edit that hit the wrong binder, or
none, would make a needed hypothesis look needed for the wrong reason, or skip it silently. These tests
pin the edit on each binder form the repository uses, without running Lean; and every finding listed in
scripts/mutation/expected.json has a class the file explains.
"""
import importlib.util
import json
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # for `common`, however the tests are run
from common import ROOT

spec = importlib.util.spec_from_file_location("mutate", ROOT / "scripts" / "mutation" / "mutate.py")
mutate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mutate)

SOURCE = """namespace X
/-- a docstring -/
theorem foo {a : Nat} (p q : F) (h1 h2 : Thm p) {h3 : Thm q} [Reducibility S]
    (h4 : n < 3 := by decide) : Thm p → Thm q :=
  bar h1 h2
theorem after : True := trivial
"""


def record(binder, kind="premise", ty=""):
    return {"module": "X", "decl": "PM.X.foo", "line": 3, "endLine": 5, "binder": binder, "kind": kind,
            "type": ty}


def edit(binder, kind="premise", ty=""):
    return mutate.drop_hypothesis(record(binder, kind, ty), SOURCE.split("\n"))


class SourceEditor(unittest.TestCase):
    def signature(self, text):
        return text.split("\n")[2] + "\n" + text.split("\n")[3]

    def test_grouped_binder(self):
        text, why = edit("h2")
        self.assertIsNone(why)
        self.assertIn("(h1 : Thm p) (h2 : True) {h3 : Thm q}", self.signature(text))

    def test_bracket_kept(self):
        text, _ = edit("h3")
        self.assertIn("{h3 : True}", self.signature(text))

    def test_default_value_dropped(self):
        text, _ = edit("h4")
        self.assertIn("(h4 : True) :", self.signature(text))

    def test_class_removed(self):
        text, why = edit("inst", "class", "PM.Reducibility S")
        self.assertIsNone(why)
        self.assertNotIn("Reducibility", text)

    def test_cut_after_the_theorem(self):
        text, _ = edit("h1")
        self.assertNotIn("theorem after", text)
        self.assertIn("bar h1 h2", text)

    def test_only_the_binder_changes(self):
        text, _ = edit("h1")
        self.assertEqual(text.replace("(h1 : True) (h2 : Thm p)", "(h1 h2 : Thm p)"),
                         "\n".join(SOURCE.split("\n")[:5]) + "\n")

    def test_anonymous_premise_not_editable(self):
        text, why = edit("a._@._internal._hyg.0")
        self.assertIsNone(text)
        self.assertEqual(why, "binder not in the signature's text")

    def test_repository_file(self):
        """A theorem of the repository: `syl`'s first premise in PM/Derived.lean."""
        lines = (ROOT / "PM" / "Derived.lean").read_text(encoding="utf-8").split("\n")
        n = next(i for i, x in enumerate(lines) if x.startswith("theorem syl ")) + 1
        h = {"module": "PM.Derived", "decl": "PM.syl", "line": n, "endLine": n + 1, "binder": "h1",
             "kind": "premise", "type": ""}
        text, why = mutate.drop_hypothesis(h, lines)
        self.assertIsNone(why)
        self.assertIn("theorem syl {a b c : F} (h1 : True) (h2 : Thm (imp b c))", text)


class Expected(unittest.TestCase):
    def test_classes_and_ids(self):
        e = json.loads((ROOT / "scripts" / "mutation" / "expected.json").read_text(encoding="utf-8"))
        ids = []
        for cat in ("unusedHypotheses", "termSurvivors", "scriptSurvivors", "droppableHypotheses"):
            for x in e[cat]:
                self.assertIn(x["class"], e["classes"], x["id"])
                ids.append(x["id"])
        self.assertEqual(len(ids), len(set(ids)))


if __name__ == "__main__":
    unittest.main()
