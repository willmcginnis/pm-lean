"""The source editor of scripts/mutation/mutate.py, and its list of examined findings.

`mutate.py --full` recompiles theorems with one hypothesis replaced by `True` (a class argument removed),
editing a copy of the source file (docs/STATEMENT_MUTATION.md). An edit that hit the wrong binder, or
none, would make a needed hypothesis look needed for the wrong reason, or skip it silently. These tests
pin the edit on each binder form the repository uses, without running Lean; the driver runs `lake build`
before it analyses anything, and stops if the build fails; and every finding listed in
scripts/mutation/expected.json has a class the file explains.
"""
import contextlib
import importlib.util
import io
import json
import os
import subprocess
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


class BuildFirst(unittest.TestCase):
    """The driver builds before it analyses: run against oleans older than the sources, it would report
    on proofs that are no longer there. `subprocess.run` is replaced, so no Lean runs."""

    def run_main(self, build_rc):
        calls = []

        def fake_run(cmd, **kw):
            calls.append(cmd)
            if cmd[:2] == ["lake", "build"]:
                return subprocess.CompletedProcess(cmd, build_rc, "", "error: stale" if build_rc else "")
            raise RuntimeError("analysed")   # the meta-program would run here

        saved, argv = mutate.subprocess.run, sys.argv
        mutate.subprocess.run, sys.argv = fake_run, ["mutate.py", "--quick"]
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                mutate.main()
        except (SystemExit, RuntimeError) as e:
            return calls, e
        finally:
            mutate.subprocess.run, sys.argv = saved, argv
        return calls, None

    def test_targets_are_the_imports(self):
        self.assertEqual(mutate.build_targets(), ["PM", "Checks.PinnedStatements"])

    def test_build_before_analysis(self):
        calls, e = self.run_main(0)
        self.assertEqual(calls[0], ["lake", "build", "PM", "Checks.PinnedStatements"])
        self.assertEqual(calls[1][:3], ["lake", "env", "lean"])
        self.assertIsInstance(e, RuntimeError)

    def test_failed_build_stops_the_run(self):
        calls, e = self.run_main(1)
        self.assertEqual(len(calls), 1)
        self.assertIsInstance(e, SystemExit)
        self.assertIn("lake build failed", str(e.code))


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
