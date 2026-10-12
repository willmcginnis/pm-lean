"""The declarations that use an axiom are exactly those of tests/expected_axiom_users.txt, each with its
known axioms, and the docs give their number.

Guards against a new axiom user going unnoticed (e.g. a PM derivation picking up `propext` or
`Classical.choice` through a library lemma): AllAxioms.lean's report must equal
tests/expected_axiom_users.txt, and every declaration AxiomCheck.lean prints as depending on axioms
must be one of them, with the same axioms. When the ✱9 foundation added eight `injEq` lemmas, the count
cited in README.md, CONTRIBUTING.md and docs/ stayed at 25: each place that gives it is read here and
compared with the list. Runs `lake env lean`, so the project must be built.
"""
import os
import re
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # for `common`, however the tests are run
from common import ROOT, run


# Where the docs give the number of axiom users, and of compiler-generated `injEq` lemmas among them.
COUNT_CITED = [
    ("README.md", r"An exhaustive check finds (\d+) declarations that use"),
    ("README.md", r"lists the (\d+) that use one"),
    ("CONTRIBUTING.md", r"still (\d+) declarations using an axiom"),
    ("docs/VERIFICATION.md", r"it lists the (\d+) that use one of Lean's axioms"),
    ("docs/VERIFICATION.md", r"finds (\d+) declarations that use Lean's standard axioms"),
    ("docs/TYPES_DESIGN.md", r"Exactly (\d+) use an axiom"),
]
INJEQ_CITED = [
    ("docs/VERIFICATION.md", r"(\d+) `injEq` lemmas"),
    ("docs/TYPES_DESIGN.md", r"`injEq` lemmas of [^|]*\((\d+)\)"),
]


def expected():
    out = {}
    for line in (ROOT / "tests/expected_axiom_users.txt").read_text(encoding="utf-8").splitlines():
        line = line.split("#")[0].split()
        if line:
            out[line[0]] = sorted(line[1:])
    return out


class AxiomUsers(unittest.TestCase):
    def test_axiom_users_as_expected(self):
        code, out = run(["lake", "env", "lean", "AllAxioms.lean"])
        self.assertEqual(code, 0, out)
        m = re.search(r"(\d+) use an axiom: \[(.*)\]\s*$", out, re.S)
        self.assertIsNotNone(m, f"unexpected AllAxioms output:\n{out}")
        found = {name: sorted(axs.replace(",", " ").split())
                 for name, axs in re.findall(r"\(([^\s,()]+),\s*\[([^\]]*)\]\)", m.group(2))}
        self.assertEqual(int(m.group(1)), len(found), "could not parse every entry of the report")
        self.assertEqual(found, expected())

    def test_axiomcheck_within_expected(self):
        code, out = run(["lake", "env", "lean", "AxiomCheck.lean"])
        self.assertEqual(code, 0, out)
        free = len(re.findall(r"does not depend on any axioms", out))
        deps = {name: sorted(axs.replace(",", " ").split())
                for name, axs in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out)}
        self.assertGreater(free, 0, out)
        exp = expected()
        for name, axs in deps.items():
            self.assertEqual(exp.get(name), axs, f"AxiomCheck: {name} depends on {axs}")

    def test_docs_cite_the_count(self):
        exp = expected()
        injeq = sum(1 for n in exp if n.endswith(".injEq"))
        for cited, n in [(COUNT_CITED, len(exp)), (INJEQ_CITED, injeq)]:
            for f, pat in cited:
                with self.subTest(file=f, pattern=pat):
                    text = " ".join((ROOT / f).read_text(encoding="utf-8").split())
                    m = re.findall(pat, text)
                    self.assertTrue(m, f"{f}: the sentence matching {pat!r} was not found")
                    self.assertEqual([int(x) for x in m], [n] * len(m))


if __name__ == "__main__":
    unittest.main()
