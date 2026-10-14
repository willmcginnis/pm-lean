"""The kernel features the PM derivations rely on change only deliberately (docs/KERNEL_CENSUS.md).

A ratchet: `scripts/kernel_census/census.py --ratchet` walks every declaration of the derivation modules,
of their closure and of the closure of the derivation theorems, and fails if the set of kernel features
found differs from tests/expected_kernel_features.txt (a new inductive kind, a quotient, an axiom, an
`@[implemented_by]` constant, a universe `imax`, ... reaching a derivation), or if the declarations
that depend on an axiom differ from tests/expected_axiom_users.txt. The other tests run the driver's
parts without Lean: its refusal of an `example` (every check is a theorem `check_…`, which the census
reads), and the ratchet's comparison on a synthetic census. Runs `lake env lean`, so the project must be built.
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


class NoExamples(unittest.TestCase):
    """Every check in the build is a named theorem `check_…` (docs/NAMING.md), which the census reads;
    an `example` is checked by the kernel but not kept, so the census refuses one."""

    def test_no_example_in_the_library(self):
        self.assertEqual(census.examples_left(), [])

    def test_an_example_is_found_with_its_line(self):
        (ROOT / ".lake").mkdir(exist_ok=True)
        tmp = tempfile.TemporaryDirectory(dir=ROOT / ".lake")
        self.addCleanup(tmp.cleanup)
        src = pathlib.Path(tmp.name) / "X.lean"
        src.write_text("import PM.Basic\nnamespace PM\nexample : 1 = 1 := rfl\n-- example in a comment\n"
                       "theorem check_one : 1 = 1 := rfl\n  example (n : Nat) :\n    n = n := rfl\nend PM\n",
                       encoding="utf-8")
        rel = src.relative_to(ROOT)
        self.assertEqual(census.examples_left([src]), [f"{rel}:3", f"{rel}:6"])


if __name__ == "__main__":
    unittest.main()
