"""The source editor of scripts/mutation/mutate.py, and its list of examined findings.

`mutate.py --full` recompiles theorems with one hypothesis replaced by `True` (a class argument removed),
editing a copy of the source file (docs/STATEMENT_MUTATION.md). An edit that hit the wrong binder, or
none, would make a needed hypothesis look needed for the wrong reason, or skip it silently. These tests
pin the edit on each binder form the repository uses, without running Lean; the driver runs `lake build`
before it analyses anything, and stops if the build fails; the quick tier is a step of tests/run_all.sh
and a check an export must pass before upload, the full tier a step of scripts/release_check.sh; and every
finding listed in scripts/mutation/expected.json has a class the file explains.
"""
import contextlib
import importlib.util
import inspect
import io
import json
import os
import pathlib
import subprocess
import sys
import tempfile
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


class Wiring(unittest.TestCase):
    """Where the tiers run (docs/STATEMENT_MUTATION.md, "Where it runs"): --quick in tests/run_all.sh and
    as check 0 of scripts/prove2me/verify.py, which an export must pass before upload; --full in
    scripts/release_check.sh. Check 0 runs with stand-in tools, so no Lean runs."""

    def test_run_all_and_release_check(self):
        run_all = (ROOT / "tests" / "run_all.sh").read_text(encoding="utf-8")
        self.assertRegex(run_all, r"\npython3 scripts/mutation/mutate\.py --quick \|\| fail ")
        release = (ROOT / "scripts" / "release_check.sh").read_text(encoding="utf-8")
        self.assertRegex(release, r"\npython3 scripts/mutation/mutate\.py --full \|\| fail ")

    def test_export_check_fails_with_the_tool(self):
        spec = importlib.util.spec_from_file_location("verify", ROOT / "scripts" / "prove2me" / "verify.py")
        verify = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(verify)
        self.assertIn('rep["mutation"], ok = mutation_check(P["repo"], skip=no_mutation)',
                      inspect.getsource(verify.main))
        self.assertIn('no_mutation = "--no-mutation" in argv', inspect.getsource(verify.main))
        self.assertIn('failed.append("mutation")', inspect.getsource(verify.main))
        with tempfile.TemporaryDirectory() as d:
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertFalse(verify.mutation_check(d)[1], "a commit without the tool passed")
            tool = pathlib.Path(d) / "scripts" / "mutation" / "mutate.py"
            tool.parent.mkdir(parents=True)
            for rc, passes in ((0, True), (1, False)):
                tool.write_text("import sys\nassert sys.argv[1:] == ['--quick']\n"
                                f"print('statement mutation: stand-in')\nsys.exit({rc})\n")
                with contextlib.redirect_stdout(io.StringIO()):
                    rep, ok = verify.mutation_check(d)
                self.assertEqual((ok, rep["rc"]), (passes, rc))

    def test_no_mutation_only_for_a_commit_without_the_tool(self):
        """--no-mutation (a commit that predates scripts/mutation, such as the 1.0.0 export): the check is
        skipped and the report says so and why; given for a commit that has the tool, the check fails and
        the tool is not run."""
        spec = importlib.util.spec_from_file_location("verify", ROOT / "scripts" / "prove2me" / "verify.py")
        verify = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(verify)
        with tempfile.TemporaryDirectory() as d:
            with contextlib.redirect_stdout(io.StringIO()) as out:
                rep, ok = verify.mutation_check(d, skip=True)
            self.assertTrue(ok)
            self.assertEqual((rep["rc"], rep["skipped"]), (None, True))
            self.assertIn("--no-mutation", rep["reason"])
            self.assertIn("no scripts/mutation/mutate.py", rep["reason"])
            self.assertIn("SKIPPED", out.getvalue())
            json.dumps(rep)
            tool = pathlib.Path(d) / "scripts" / "mutation" / "mutate.py"
            tool.parent.mkdir(parents=True)
            ran = pathlib.Path(d) / "ran"
            tool.write_text(f"open({str(ran)!r}, 'w').close()\n")
            with contextlib.redirect_stdout(io.StringIO()):
                rep, ok = verify.mutation_check(d, skip=True)
            self.assertFalse(ok, "--no-mutation skipped a commit that has the tool")
            self.assertFalse(rep["skipped"])
            self.assertFalse(ran.exists(), "the tool ran under --no-mutation")


class MethodsAgree(unittest.TestCase):
    """The comparison by normal forms gives the same verdicts as the direct one (docs/STATEMENT_MUTATION.md,
    "How a mutant is compared"), on a fixed sample: one statement of each module with mutants, each among
    the quicker ones for the direct comparison. ✱1·4 carries the seeded slip; ✱9·401's normal forms are
    flagged by the audit, so its comparisons fall back to the direct one. Runs Lean (about 20 s); the full
    comparison is `mutate.py --compare-methods`."""

    SAMPLE = ["PM.Thm.perm", "PM.t2_06", "PM.pm2_75", "PM.t4_87", "PM.QL.t4_87", "PM.F9.f9_401",
              "PM.q10_413", "PM.q11_4", "PM.q13_182", "PM.q14_144", "PM.q20_23", "PM.q21_24", "PM.q22_49",
              "PM.q23_73", "PM.q24_482", "PM.q25_402"]

    def test_a_disagreement_fails(self):
        """The report the run fails on, without Lean: one mutant and one control that differ, one fallback."""
        stmt = {"part": "stmt", "decl": "PM.x", "module": "PM.M", "defeqMs": 0, "normalMs": 0,
                "controlDirect": True, "controlNormal": True}
        mut = {"part": "mut", "decl": "PM.x", "op": "negate", "i": 0, "survivesDirect": False}
        recs = [dict(stmt, controlNormal=False), dict(mut, survivesNormal=True), dict(mut, i=1, survivesNormal=None),
                dict(mut, i=2, survivesNormal=False)]
        with contextlib.redirect_stdout(io.StringIO()) as out:
            problems = mutate.compare_report(recs)
        self.assertEqual(len(problems), 2)
        self.assertIn("2 disagreements, 1 fallbacks", out.getvalue())

    recs = None

    @classmethod
    def sample_run(cls):
        if cls.recs is None:
            with contextlib.redirect_stdout(io.StringIO()):
                cls.recs = mutate.run_meta("part2", "both", only=",".join(cls.SAMPLE), name="compare-test")
        return cls.recs

    def test_witness_routed_to_direct(self):
        """The case the audit once missed (docs/STATEMENT_MUTATION.md, "How a mutant is compared"): two
        statements equal for the direct comparison by proof irrelevance, whose normal forms differ
        because a recursor on a proof-valued projection is stuck. With the audit bypassed the two
        comparisons disagree; the audit flags the projection, so `direct` decides and they agree. The
        meta-program fails if the projection is not flagged; this pins the record."""
        w = next(r for r in self.sample_run() if r["part"] == "selfTest")["witness"]
        self.assertEqual((w["direct"], w["normalAuditBypassed"]), (True, False))
        self.assertFalse(w["auditClean"])
        self.assertIn("projection PMNfTest.ProofBox.1", w["proofs"])
        self.assertEqual(w["verdict"], w["direct"])
        unit = next(r for r in self.sample_run() if r["part"] == "selfTest")["unitProjection"]
        self.assertIn("projection PMNfTest.UnitBox.1", unit)

    def test_identical_verdicts(self):
        recs = self.sample_run()
        with contextlib.redirect_stdout(io.StringIO()):
            problems = mutate.compare_report(recs)
        self.assertEqual(problems, [])
        stmts = {r["decl"]: r for r in recs if r["part"] == "stmt"}
        muts = [r for r in recs if r["part"] == "mut"]
        self.assertEqual(sorted(stmts), sorted(self.SAMPLE))
        compared = [m for m in muts if m["survivesNormal"] is not None]
        self.assertGreater(len(compared), 300)
        # every statement but ✱9·401 is decided by its normal forms, mutants and control alike
        for d, s in stmts.items():
            self.assertEqual(s["fallbacks"] == 0, d != "PM.F9.f9_401", d)
            self.assertTrue(s["control"] and s["controlDirect"], d)
        slip = [m for m in muts if m["decl"] == "PM.Thm.perm" and m["src"] == "(PM.F.imp (PM.F.or p q) (PM.F.or p p))"]
        self.assertEqual([(m["survivesDirect"], m["survivesNormal"]) for m in slip], [(False, False)])


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
