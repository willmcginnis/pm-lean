"""The kernel features the PM derivations rely on change only deliberately (docs/KERNEL_CENSUS.md).

A ratchet: `scripts/kernel_census/census.py --ratchet` walks every declaration of the derivation modules,
of their closure and of the closure of the derivation theorems, and fails if the set of kernel features
found differs from tests/expected_kernel_features.txt (a new inductive kind, a quotient, an axiom, an
`@[implemented_by]` constant, a universe `imax`, ... reaching a derivation), or if the declarations
that depend on an axiom differ from tests/expected_axiom_users.txt. The other tests run the driver's
parts without Lean: the copy that turns `example`s into theorems, the merge of the examples' results,
and the ratchet's comparison on a synthetic census. Runs `lake env lean`, so the project must be built.
"""
import importlib.util
import os
import pathlib
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # for `common`, however the tests are run
from common import ROOT, run

spec = importlib.util.spec_from_file_location("census", ROOT / "scripts" / "kernel_census" / "census.py")
census = importlib.util.module_from_spec(spec)
spec.loader.exec_module(census)


class Ratchet(unittest.TestCase):
    def test_features_and_axiom_users_as_expected(self):
        code, out = run(["python3", "scripts/kernel_census/census.py", "--ratchet"])
        self.assertEqual(code, 0, out)
        self.assertRegex(out, r"kernel census ratchet: \d+ features of the PM derivations, 0 problems")


def synthetic(features, users=None):
    cols = {k: {"declarations": 1, "features": {f: {"count": 1, "examples": ["PM.x"], "path": ["PM.t", "PM.x"]}
                                                 for f in features}}
            for k in census.RATCHET_COLUMNS}
    if users is None:
        users = census.expected_axiom_users()
    by_axiom = {}
    for u, axs in users.items():
        for a in axs:
            by_axiom.setdefault(a, {"repository": [], "meta": []})["repository"].append(u)
    return {"columns": cols, "axiomUsers": by_axiom}


class RatchetComparison(unittest.TestCase):
    def setUp(self):
        self.expected = census.read_expected()
        self.features = sorted({x.split(" ", 1)[1] for x in self.expected if x.startswith("proofClosure ")})

    def test_expected_file_has_every_ratchet_column(self):
        cols = {x.split(" ", 1)[0] for x in self.expected}
        self.assertEqual(cols, set(census.RATCHET_COLUMNS))

    def test_new_feature_fails_with_its_path(self):
        problems = census.check_ratchet(synthetic(self.features + ["quot.Quot.lift"]))
        self.assertTrue(any("new kernel feature: proofClosure quot.Quot.lift" in p and "PM.t → PM.x" in p
                            for p in problems), problems)

    def test_vanished_feature_fails(self):
        gone = self.features[0]
        problems = census.check_ratchet(synthetic(self.features[1:]))
        self.assertTrue(any("no longer used" in p and f"proofClosure {gone}" in p for p in problems), problems)

    def test_new_axiom_user_fails(self):
        users = dict(census.expected_axiom_users(), **{"PM.t2_08": ["propext"]})
        problems = census.check_ratchet(synthetic(self.features, users))
        self.assertTrue(any("axiom user PM.t2_08" in p for p in problems), problems)

    def test_internal_and_meta_users_are_not_compared(self):
        users = dict(census.expected_axiom_users(), **{"PM.instReprF.repr._f": ["propext"],
                                                      "PMCanon.deps": ["propext"]})
        problems = [p for p in census.check_ratchet(synthetic(self.features, users)) if "axiom" in p]
        self.assertEqual(problems, [])


class ExamplesCopy(unittest.TestCase):
    def test_examples_become_theorems_named_by_line(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        src = pathlib.Path(tmp.name) / "X.lean"
        src.write_text("import PM.Basic\nnamespace PM\nexample : 1 = 1 := rfl\n-- example in a comment\n"
                       "example (n : Nat) :\n    n = n := rfl\nend PM\n", encoding="utf-8")
        text, n = census.examples_copy(src)
        self.assertEqual(n, 2)
        lines = text.split("\n")
        self.assertEqual(lines[0], "import Lean")
        self.assertEqual(lines[1], "import PM.Basic")
        self.assertIn("theorem _kernelCensusExample_3 : 1 = 1 := rfl", lines)
        self.assertIn("theorem _kernelCensusExample_5 (n : Nat) :", lines)
        self.assertIn("-- example in a comment", lines)
        self.assertIn("namespace KernelCensus", text)
        self.assertIn("#eval show CommandElabM Unit", text)

    def test_file_without_examples(self):
        text, n = census.examples_copy(ROOT / "PM" / "Basic.lean")
        self.assertEqual((text, n), (None, 0))

    def test_same_line_in_two_files_counted_twice(self):
        r = {"examples": ["PM._kernelCensusExample_7"], "direct": {"lit.nat": ["PM._kernelCensusExample_7"]},
             "closure": {"lit.nat": ["PM._kernelCensusExample_7", "Nat"]}, "checked": ["PM._kernelCensusExample_7"],
             "failed": [], "unfoldSets": {}, "unfoldConsts": {}, "totals": {"PM._kernelCensusExample_7": 3}}
        c = census.merge_examples({"columns": {}, "recheck": {"derivations": {}}}, {"A.lean": r, "B.lean": r})
        self.assertEqual(c["columns"]["examples"]["declarations"], 2)
        self.assertEqual(c["columns"]["examples"]["features"]["lit.nat"]["count"], 2)
        self.assertEqual(c["columns"]["examplesClosure"]["features"]["lit.nat"]["count"], 3)
        self.assertEqual(c["recheck"]["examples"]["totalUnfoldings"], 6)


if __name__ == "__main__":
    unittest.main()
