"""Export names (docs/NAMING.md): data/export_names.json is up to date and passes every rule of
scripts/export_names.py, and each rule catches a name that breaks it.

Each mutation below breaks one rule. It must be reported by that rule, and must not be reported when
that rule is skipped: so the test fails if the rule is switched off, rather than passing because some
other rule happens to catch the same name.
"""
import copy
import importlib.util
import json
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # for `common`, however the tests are run
from common import ROOT, run

spec = importlib.util.spec_from_file_location("export_names", ROOT / "scripts" / "export_names.py")
export_names = importlib.util.module_from_spec(spec)
spec.loader.exec_module(export_names)


def entries():
    return json.loads((ROOT / "data" / "export_names.json").read_text(encoding="utf-8"))


def find(es, pm, reading=None):
    return next(e for e in es if e["pm"] == pm and e["reading"] == reading and not e.get("meta"))


def rename(e, name):
    e["export"], e["slug"] = name, name.replace(".", "_")


def m_pattern(es, ctx):
    rename(find(es, "*2.01"), "PM.star2_01_abs_Not_of_imp_not")


def m_pattern_ascii(es, ctx):
    rename(find(es, "*2.01"), "PM.star2_01_abs_not_of_imp_nöt")


def m_unique_name(es, ctx):
    e = copy.deepcopy(find(es, "*2.01"))
    e["slug"] = "PM_other"            # so that only the full name repeats
    es.append(e)


def m_unique_slug(es, ctx):
    # a top-level name whose slug is that of an existing card, e.g. PM_star2_01_... beside PM.star2_01_...
    e = copy.deepcopy(find(es, "*2.08"))
    rename(e, "PM.star2_08.id_imp_self")
    es.append(e)


def m_vocabulary(es, ctx):
    rename(find(es, "*2.01"), "PM.star2_01_abs_negation_of_imp_not")


def m_pm_name_first(es, ctx):
    rename(find(es, "*2.01"), "PM.star2_01_not_of_imp_not_abs")


def m_readings(es, ctx):
    e = find(es, "*9.31", "landini")
    rename(e, e["export"].replace("_reading_landini", "_reading_switch"))
    e["reading"] = "switch"


def m_no_top_level(es, ctx):
    e = find(es, "*2.08")
    e["export"] = "PM_star2_08_id_imp_self"


def m_frozen(es, ctx):
    ctx["lock"] = ["PM.star2_01_abs_not_of_imp_not"]
    rename(find(es, "*2.01"), "PM.star2_01_abs_not_of_imp_not_imp")


MUTATIONS = [("pattern", m_pattern), ("pattern", m_pattern_ascii), ("unique_name", m_unique_name),
             ("unique_slug", m_unique_slug), ("vocabulary", m_vocabulary),
             ("pm_name_first", m_pm_name_first), ("readings", m_readings),
             ("no_top_level", m_no_top_level), ("frozen", m_frozen)]


class TestExportNames(unittest.TestCase):
    def test_up_to_date_and_clean(self):
        code, out = run(["python3", "scripts/export_names.py", "--check"])
        self.assertEqual(code, 0, out)

    def test_committed_file_passes(self):
        problems = export_names.check(entries(), export_names.context())
        self.assertEqual({k: v for k, v in problems.items() if v}, {})

    def test_every_check_has_a_mutation(self):
        self.assertEqual({k for k, _ in MUTATIONS}, set(export_names.CHECKS))

    def test_mutations(self):
        for rule, mutate in MUTATIONS:
            with self.subTest(rule=rule, mutation=mutate.__name__):
                es, ctx = entries(), export_names.context()
                mutate(es, ctx)
                self.assertTrue(export_names.check(es, ctx)[rule], f"{rule} missed {mutate.__name__}")
                # with the rule switched off, the assertion above would fail
                real = export_names.CHECKS[rule]
                export_names.CHECKS[rule] = lambda es, ctx: []
                try:
                    self.assertFalse(export_names.check(es, ctx)[rule])
                finally:
                    export_names.CHECKS[rule] = real

    def test_version_suffix(self):
        # a superseded statement's replacement is name_v2 (docs/VERSIONING.md): allowed by every rule
        es, ctx = entries(), export_names.context()
        e = find(es, "*9.31", "landini")
        rename(e, e["export"] + "_v2")
        self.assertEqual({k: v for k, v in export_names.check(es, ctx).items() if v}, {})

    def test_lock_file_exists(self):
        # filled at the first public release; every name in it must then stay
        self.assertTrue((ROOT / "data" / "export_names.lock").exists())

    def test_star1_5_cards(self):
        # the private pilot's 196 theorems: ✱1·2–✱1·6, the 188 theorems of ✱2–✱5, and three results
        # about the system
        es = entries()
        sel = [e for e in es if e.get("meta") or int(e["pm"][1:].split(".")[0]) <= 5]
        self.assertEqual(len(sel), 196)
        self.assertEqual(sum(1 for e in sel if e.get("meta")), 3)

    def test_descriptors(self):
        es = entries()
        self.assertEqual(find(es, "*2.01")["export"], "PM.star2_01_abs_not_of_imp_not")
        self.assertEqual(find(es, "*1.4")["export"], "PM.star1_4_perm_or_comm")
        self.assertEqual(find(es, "*3.26")["export"], "PM.star3_26_simp_left_of_and")
        self.assertEqual(find(es, "*3.27")["export"], "PM.star3_27_simp_right_of_and")
        self.assertEqual(find(es, "*2.08")["export"], "PM.star2_08_id_imp_self")
        self.assertEqual(find(es, "*9.31", "russell")["export"],
                         "PM.star9_31_exists_of_exists_or_self_reading_russell")

    def test_pm_names_not_keys(self):
        names = json.loads((ROOT / "data" / "naming" / "pm_names.json").read_text(encoding="utf-8"))["names"]
        nums = [r["number"] for r in names]
        self.assertEqual(len(nums), len(set(nums)))
        self.assertEqual(sum(r["name"] == "Transp" for r in names), 7)


if __name__ == "__main__":
    unittest.main()
