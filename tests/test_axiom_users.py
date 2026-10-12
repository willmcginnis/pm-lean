"""The declarations that use an axiom are exactly the known 25, each with its known axioms.

Guards against a new axiom user going unnoticed (e.g. a PM derivation picking up `propext` or
`Classical.choice` through a library lemma): AllAxioms.lean's report must equal
tests/expected_axiom_users.txt, and every declaration AxiomCheck.lean prints as depending on axioms
must be one of them, with the same axioms. Runs `lake env lean`, so the project must be built.
"""
import os
import re
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # for `common`, however the tests are run
from common import ROOT, run


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


if __name__ == "__main__":
    unittest.main()
