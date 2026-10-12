"""AxiomCheck.lean covers every file under PM/ and is what scripts/gen_axiomcheck.py generates.

The generator used to list its files by name, so the ✱9 foundation (PM/Found9/) was added without
AxiomCheck.lean printing any of its theorems; and it ignored `namespace` blocks, so the lemmas of
`namespace ClsExpr` were printed as `PM.and`, `PM.imp`, ..., which do not exist. Here: the generator
globs every PM/**/*.lean file; every file under PM/ that declares a public theorem has each of them in
AxiomCheck.lean, under its full name; and AxiomCheck.lean is up to date with the generator.
"""
import importlib.util
import os
import re
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # for `common`, however the tests are run
from common import ROOT


def generator():
    spec = importlib.util.spec_from_file_location("gen_axiomcheck", ROOT / "scripts" / "gen_axiomcheck.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


class AxiomCheckCoverage(unittest.TestCase):
    def test_generator_reads_every_file(self):
        on_disk = sorted(str(p.relative_to(ROOT)) for p in (ROOT / "PM").rglob("*.lean"))
        self.assertEqual(generator().files(), on_disk)

    def test_up_to_date(self):
        self.assertEqual((ROOT / "AxiomCheck.lean").read_text(encoding="utf-8"), generator().generate(),
                         "AxiomCheck.lean is out of date: run python3 scripts/gen_axiomcheck.py")

    def test_every_public_theorem_printed(self):
        printed = set(re.findall(r"^#print axioms (\S+)$", (ROOT / "AxiomCheck.lean").read_text(encoding="utf-8"), re.M))
        gen = generator()
        for p in sorted((ROOT / "PM").rglob("*.lean")):
            text = p.read_text(encoding="utf-8")
            names = [n if n.startswith("PM.") else f"PM.{n}" for n, thm in gen.declared(text) if thm]
            # an independent count of the file's public theorems, by a plainer pattern
            self.assertEqual(len(names), len(re.findall(r"^(?:protected )?theorem ", text, re.M)), p.name)
            with self.subTest(file=str(p.relative_to(ROOT))):
                self.assertEqual([n for n in names if n not in printed], [])


if __name__ == "__main__":
    unittest.main()
