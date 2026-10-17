"""scripts/kernel_census/type_as_term.lean measures the closure of the kernel census's derivation
theorems, so its copies of the census's module groups (`derivationModules`, `foundationModules`,
`metatheoryModules`) must equal those of scripts/kernel_census/KernelCensus.lean. Both files are read as
text; no Lean run is needed. A unit test feeds the comparison a seeded difference.
"""
import os
import re
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # for `common`, however the tests are run
from common import ROOT

CENSUS = ROOT / "scripts" / "kernel_census" / "KernelCensus.lean"
TYPE_AS_TERM = ROOT / "scripts" / "kernel_census" / "type_as_term.lean"
GROUPS = ["derivationModules", "foundationModules", "metatheoryModules"]


def module_lists(text):
    """Each `def <name>Modules : List Name := [...]` of a Lean file, as name → list of modules."""
    return {m.group(1): re.findall(r"`([\w.]+)", m.group(2))
            for m in re.finditer(r"^def (\w+Modules) : List Name := \[(.*?)\]", text, re.M | re.S)}


def compare(census_text, type_as_term_text):
    """The differences between the two files' groups, as lines; empty if none."""
    census, copy = module_lists(census_text), module_lists(type_as_term_text)
    problems = []
    for g in GROUPS:
        if g not in census:
            problems.append(f"{g}: not found in {CENSUS.name}")
            continue
        if g not in copy:
            problems.append(f"{g}: not found in {TYPE_AS_TERM.name}")
            continue
        for m in census[g]:
            if m not in copy[g]:
                problems.append(f"{g}: {m} is in {CENSUS.name}, not in {TYPE_AS_TERM.name}")
        for m in copy[g]:
            if m not in census[g]:
                problems.append(f"{g}: {m} is in {TYPE_AS_TERM.name}, not in {CENSUS.name}")
        if len(set(copy[g])) != len(copy[g]):
            problems.append(f"{g}: a module is listed twice in {TYPE_AS_TERM.name}")
    return problems


class ModuleLists(unittest.TestCase):
    def setUp(self):
        self.census = CENSUS.read_text(encoding="utf-8")
        self.copy = TYPE_AS_TERM.read_text(encoding="utf-8")

    def test_type_as_term_lists_equal_the_census_groups(self):
        self.assertEqual(compare(self.census, self.copy), [])

    def test_every_group_is_parsed(self):
        for text in (self.census, self.copy):
            lists = module_lists(text)
            for g in GROUPS:
                self.assertIn(g, lists)
                self.assertTrue(lists[g])

    def test_a_seeded_difference_fails(self):
        removed = self.copy.replace("`PM.Star25,", "", 1)
        self.assertNotEqual(removed, self.copy)
        self.assertIn("derivationModules: PM.Star25 is in KernelCensus.lean, not in type_as_term.lean",
                      compare(self.census, removed))
        added = self.copy.replace("`PM.Basic,", "`PM.Basic, `PM.Star99,", 1)
        self.assertIn("foundationModules: PM.Star99 is in type_as_term.lean, not in KernelCensus.lean",
                      compare(self.census, added))
        moved = self.copy.replace("`PM.Trap,", "", 1).replace("`PM.Chain,", "`PM.Chain, `PM.Trap,", 1)
        self.assertEqual(len(compare(self.census, moved)), 2, compare(self.census, moved))


if __name__ == "__main__":
    unittest.main()
