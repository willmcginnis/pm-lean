"""Export names (docs/NAMING.md): data/export_names.json is up to date and passes every rule of
scripts/export_names.py, and each rule catches a name that breaks it.

Each mutation below breaks one rule. It must be reported by that rule, and must not be reported when
that rule is skipped: so the test fails if the rule is switched off, rather than passing because some
other rule happens to catch the same name. The lock and the reading lock are empty until the first
release, so their rules are tested under a scratch lock made from the current names.
"""
import copy
import importlib.util
import json
import os
import pathlib
import sys
import tempfile
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


def scratch_lock(es, ctx):
    """ctx as after a release of es: every name locked, every reading meaning locked."""
    ctx["lock"] = export_names.lock_rows(es, ctx)
    ctx["readings_lock"] = {t: {"word": r["word"], "meaning": r["meaning"]} for t, r in ctx["readings"].items()}


def counterpart(ctx, pm):
    return next(r for r in ctx["counterparts"]["counterparts"] if r["pm"] == pm)


# ---- pattern: lower-case ASCII, PM's number matching the item

def m_pattern_case(es, ctx):
    rename(find(es, "*2.01"), "PM.star2_01_Abs")


def m_pattern_ascii(es, ctx):
    rename(find(es, "*2.01"), "PM.star2_01_äbs")


def m_pattern_number(es, ctx):
    rename(find(es, "*2.01"), "PM.star2_1_abs")       # ✱2·01 and ✱2·1 are different propositions


# ---- suffix_order: [_<pmname>][_df|_rule][_reading_<word>][_v<N>], _v<N> last

def m_suffix_version_before_reading(es, ctx):
    e = find(es, "*9.31", "landini")
    rename(e, "PM.star9_31_v2_reading_landini")


def m_suffix_reading_before_slot(es, ctx):
    e = find(es, "*9.12", "russell")
    rename(e, "PM.star9_12_reading_russell_rule")


# ---- pm_name_only: PM's own name when it gives one, and no other word

def m_descriptor_in_name(es, ctx):
    rename(find(es, "*2.01"), "PM.star2_01_abs_not_of_imp_not")


def m_mathlib_word_in_name(es, ctx):
    rename(find(es, "*2.16"), "PM.star2_16_transp_mt")


def m_pm_name_missing(es, ctx):
    rename(find(es, "*3.26"), "PM.star3_26")


def m_pm_name_invented(es, ctx):
    rename(find(es, "*2.14"), "PM.star2_14_dneg")


# ---- slots: _df exactly for definitions, _rule exactly for inference rules

def m_rule_without_slot(es, ctx):
    e = find(es, "*9.12")
    rename(e, "PM.star9_12")
    e["slot"] = None


def m_df_on_assertion(es, ctx):
    e = find(es, "*2.01")
    rename(e, "PM.star2_01_abs_df")
    e["slot"] = "df"


def m_pp_rule_not_pp(es, ctx):
    ctx["slots"] = copy.deepcopy(ctx["slots"])
    ctx["slots"]["pp_rules"]["*2.01"] = "not a primitive proposition"


# ---- readings: from the closed list, matching the entry

def m_reading_unknown(es, ctx):
    e = find(es, "*9.31", "landini")
    rename(e, e["export"].replace("_reading_landini", "_reading_switch"))
    e["reading"] = "switch"


# ---- readings_frozen: a locked reading keeps its word and meaning

def m_reading_meaning_changed(es, ctx):
    scratch_lock(es, ctx)
    ctx["readings"] = copy.deepcopy(ctx["readings"])
    ctx["readings"]["C"]["meaning"] = "the definitions as printed with Landini's Switch"


def m_reading_removed(es, ctx):
    scratch_lock(es, ctx)
    ctx["readings"] = {t: r for t, r in ctx["readings"].items() if t != "P"}


# ---- unique_name, unique_slug, no_top_level

def m_unique_name(es, ctx):
    e = copy.deepcopy(find(es, "*2.01"))
    e["slug"] = "PM_other"            # so that only the full name repeats
    es.append(e)


def m_slug_collision(es, ctx):
    # PM.star2.08_id is another name whose slug is that of PM.star2_08_id
    e = copy.deepcopy(find(es, "*2.08"))
    rename(e, "PM.star2.08_id")
    es.append(e)


def m_slug_collision_case(es, ctx):
    e = copy.deepcopy(find(es, "*2.08"))
    rename(e, "PM.Star2_08_id")
    es.append(e)


def m_top_level(es, ctx):
    e = find(es, "*2.08")
    e["export"] = "PM_star2_08_id"


# ---- vocabulary: the descriptor field (not part of the name)

def m_vocabulary(es, ctx):
    find(es, "*2.01")["descriptor"] = "negation_of_imp_not"


# ---- lock: a released name keeps its statement, definitions and reading

def m_lock_statement_changed(es, ctx):
    scratch_lock(es, ctx)
    find(es, "*2.16")["statement_digest"] = export_names.sha256("another statement")


def m_lock_definitions_changed(es, ctx):
    scratch_lock(es, ctx)
    find(es, "*2.16")["definitions_digest"] = export_names.sha256("another definition of ⊃")


def m_lock_name_gone(es, ctx):
    scratch_lock(es, ctx)
    rename(find(es, "*2.01"), "PM.star2_01_abs_v2")


def m_lock_reading_changed(es, ctx):
    scratch_lock(es, ctx)
    e = find(es, "*9.1", "russell")
    e["reading"] = "landini"


# ---- versions: a _v<N> name has its row in data/changes.tsv

def m_version_without_row(es, ctx):
    e = find(es, "*9.31", "landini")
    rename(e, e["export"] + "_v2")


# ---- counterparts: pinned, well formed, exact for the statement exported now

def m_counterpart_commit(es, ctx):
    counterpart(ctx, "*2.16")["commit"] = "819816b"


def m_counterpart_source(es, ctx):
    counterpart(ctx, "*2.16")["source"] = "src/Init/Core.lean"


def m_counterpart_source_escapes(es, ctx):
    counterpart(ctx, "*2.16")["source"] = "../src/Init/Core.lean:833"


def m_counterpart_export(es, ctx):
    counterpart(ctx, "*2.16")["export"] = "PM.star2_16_transp_mt"


def m_counterpart_not_exact(es, ctx):
    # an implication reversed: never allowed by the criterion
    counterpart(ctx, "*2.16")["statement"] = "((¬q → ¬p) → (p → q))"


def m_counterpart_iff_flag(es, ctx):
    counterpart(ctx, "*4.13")["iff_reversed"] = False


def m_counterpart_classical(es, ctx):
    counterpart(ctx, "*2.11")["classical"] = "yes"


def m_counterpart_statement_changed(es, ctx):
    # the PM statement it was matched against is no longer the one exported
    counterpart(ctx, "*2.16")["pm_formula"] = "((p → q) → (¬p → ¬q))"


MUTATIONS = [
    ("pattern", m_pattern_case), ("pattern", m_pattern_ascii), ("pattern", m_pattern_number),
    ("suffix_order", m_suffix_version_before_reading), ("suffix_order", m_suffix_reading_before_slot),
    ("pm_name_only", m_descriptor_in_name), ("pm_name_only", m_mathlib_word_in_name),
    ("pm_name_only", m_pm_name_missing), ("pm_name_only", m_pm_name_invented),
    ("slots", m_rule_without_slot), ("slots", m_df_on_assertion), ("slots", m_pp_rule_not_pp),
    ("readings", m_reading_unknown),
    ("readings_frozen", m_reading_meaning_changed), ("readings_frozen", m_reading_removed),
    ("unique_name", m_unique_name), ("unique_slug", m_slug_collision), ("unique_slug", m_slug_collision_case),
    ("no_top_level", m_top_level), ("vocabulary", m_vocabulary),
    ("lock", m_lock_statement_changed), ("lock", m_lock_definitions_changed), ("lock", m_lock_name_gone),
    ("lock", m_lock_reading_changed), ("versions", m_version_without_row),
    ("counterparts", m_counterpart_commit), ("counterparts", m_counterpart_source),
    ("counterparts", m_counterpart_source_escapes), ("counterparts", m_counterpart_export),
    ("counterparts", m_counterpart_not_exact), ("counterparts", m_counterpart_iff_flag),
    ("counterparts", m_counterpart_classical), ("counterparts", m_counterpart_statement_changed),
]


def context():
    ctx = export_names.context()
    ctx["counterparts"] = copy.deepcopy(ctx["counterparts"])
    return ctx


def clean(problems):
    return {k: v for k, v in problems.items() if v}


class TestExportNames(unittest.TestCase):
    def test_up_to_date_and_clean(self):
        code, out = run(["python3", "scripts/export_names.py", "--check"])
        self.assertEqual(code, 0, out)

    def test_committed_file_passes(self):
        self.assertEqual(clean(export_names.check(entries(), context())), {})

    def test_every_check_has_a_mutation(self):
        self.assertEqual({k for k, _ in MUTATIONS}, set(export_names.CHECKS))

    def test_mutations(self):
        for rule, mutate in MUTATIONS:
            with self.subTest(rule=rule, mutation=mutate.__name__):
                es, ctx = entries(), context()
                mutate(es, ctx)
                self.assertTrue(export_names.check(es, ctx)[rule], f"{rule} missed {mutate.__name__}")
                # with the rule switched off, the assertion above would fail
                real = export_names.CHECKS[rule]
                export_names.CHECKS[rule] = lambda es, ctx: []
                try:
                    self.assertFalse(export_names.check(es, ctx)[rule])
                finally:
                    export_names.CHECKS[rule] = real

    def test_scratch_lock_is_clean(self):
        es, ctx = entries(), context()
        scratch_lock(es, ctx)
        self.assertEqual(clean(export_names.check(es, ctx)), {})

    def test_changed_statement_points_to_version_and_changes(self):
        es, ctx = entries(), context()
        m_lock_statement_changed(es, ctx)
        (msg,) = export_names.check(es, ctx)["lock"]
        self.assertIn("PM.star2_16_transp_v<N>", msg)
        self.assertIn("data/changes.tsv", msg)

    def test_lock_sees_changes_in_lean(self):
        # change the elaborated statement of ✱2·16, then the definition of ⊃, as Lean would print them
        es, ctx = entries(), context()
        scratch_lock(es, ctx)
        rows, defs = export_names.lean_output()
        rows2 = copy.deepcopy(rows)
        r = next(r for r in rows2 if r["name"] == "PM.t2_16")
        r["canon"] = r["canon"].replace("(C PM.F.neg []) #0", "(C PM.F.neg []) #1", 1)
        bad = export_names.check(export_names.build(rows2, defs, ctx)[0], ctx)["lock"]
        self.assertEqual(len(bad), 1)
        self.assertTrue(bad[0].startswith("PM.star2_16_transp: its statement changed"))
        defs2 = {**defs, "PM.F.imp": defs["PM.F.imp"].replace("PM.F.or", "PM.F.and")}
        bad = export_names.check(export_names.build(rows, defs2, ctx)[0], ctx)["lock"]
        uses = [r for r in rows if "PM.F.imp" in r["deps"] and r["name"] in {e["lean"] for e in es}]
        self.assertGreater(len(uses), 180)
        self.assertEqual(len(bad), len(uses))
        self.assertTrue(all("definitions it uses changed" in b for b in bad))

    def test_version_with_its_row(self):
        # a superseded statement's replacement is name_v2 with a row of data/changes.tsv: every rule passes
        es, ctx = entries(), context()
        e = find(es, "*9.31", "landini")
        old = e["export"]
        rename(e, old + "_v2")
        ctx["changes"] = [{"date": "2026-10-13", "old": old, "new": old + "_v2", "reason": "test",
                           "statement_id": e["statement_digest"]}]
        self.assertEqual(clean(export_names.check(es, ctx)), {})

    def test_write_lock_round_trip(self):
        # --write-lock at a release: the names regenerated under the lock are the same, and every rule passes
        es = entries()
        with tempfile.TemporaryDirectory() as d:
            lock, rlock = pathlib.Path(d) / "export_names.lock", pathlib.Path(d) / "readings.lock"
            export_names.write_lock(es, export_names.context(lock, rlock), lock, rlock)
            ctx = export_names.context(lock, rlock)
            self.assertEqual(len(ctx["lock"]), len(es))
            self.assertEqual(set(ctx["readings_lock"]), set(ctx["readings"]))
            rows, defs = export_names.lean_output()
            self.assertEqual(export_names.build(rows, defs, ctx)[0], es)
            self.assertEqual(clean(export_names.check(es, ctx)), {})

    def test_working_reading_change_renames_nothing_released(self):
        # statements valid under every reading are exported under the working reading; after a release, a
        # new working reading must not rename them
        es, ctx = entries(), context()
        every = [e for e in es if e.get("reading_from", "").startswith("every reading")]
        self.assertTrue(every)
        rows, defs = export_names.lean_output()
        export_names.WORKING_READING = "L"
        try:
            unlocked = {e["lean"]: e["export"] for e in export_names.build(rows, defs, ctx)[0]}
            scratch_lock(es, ctx)
            locked = {e["lean"]: e for e in export_names.build(rows, defs, ctx)[0]}
        finally:
            export_names.WORKING_READING = "C"
        for e in every:
            self.assertTrue(unlocked[e["lean"]].endswith("_reading_landini"))   # what an unlocked change does
            self.assertEqual(locked[e["lean"]]["export"], e["export"])
            self.assertEqual(locked[e["lean"]]["reading"], "russell")

    def test_new_reading_can_be_added(self):
        es, ctx = entries(), context()
        scratch_lock(es, ctx)
        ctx["readings"] = {**ctx["readings"], "Z": {"word": "zermelo", "lean": "PM.F9.Reading.z",
                                                    "meaning": "a later reading", "why": "test"}}
        self.assertEqual(export_names.check(es, ctx)["readings_frozen"], [])

    def test_lock_files_exist(self):
        # filled at the first public release; every name in them must then stay
        self.assertEqual(export_names.read_tsv(export_names.LOCK, export_names.LOCK_COLUMNS), [])
        self.assertEqual(json.loads(export_names.READINGS_LOCK.read_text(encoding="utf-8")), {})

    def test_star1_5_cards(self):
        # the private pilot's 196 theorems: ✱1·2–✱1·6, the 188 theorems of ✱2–✱5, and three results
        # about the system
        es = entries()
        sel = [e for e in es if e.get("meta") or int(e["pm"][1:].split(".")[0]) <= 5]
        self.assertEqual(len(sel), 196)
        self.assertEqual(sum(1 for e in sel if e.get("meta")), 3)

    def test_names(self):
        es = entries()
        self.assertEqual(find(es, "*2.01")["export"], "PM.star2_01_abs")
        self.assertEqual(find(es, "*1.4")["export"], "PM.star1_4_perm")
        self.assertEqual(find(es, "*2.14")["export"], "PM.star2_14")
        self.assertEqual(find(es, "*2.17")["export"], "PM.star2_17_transp")
        self.assertEqual(find(es, "*3.26")["export"], "PM.star3_26_simp")
        self.assertEqual(find(es, "*9.31", "russell")["export"], "PM.star9_31_reading_russell")
        self.assertEqual(find(es, "*9.12")["export"], "PM.star9_12_rule")
        self.assertEqual(find(es, "*10.01", "russell")["export"], "PM.star10_01_df_reading_russell")
        # the descriptor stays, as a field for titles and search
        self.assertEqual(find(es, "*2.01")["descriptor"], "not_of_imp_not")

    def test_counterparts(self):
        cp = context()["counterparts"]
        self.assertEqual(len(cp["counterparts"]), 68)
        self.assertEqual(counterpart({"counterparts": cp}, "*2.16")["declaration"], "mt")

    def test_formula_reader(self):
        f = export_names.parse_formula
        self.assertEqual(f("((p ∨ q) → ¬¬q)"), ("→", ("∨", "p", "q"), ("¬", ("¬", "q"))))
        self.assertEqual(export_names.reverse_iffs(f("(q → (p ↔ r))"), ["2"]), f("(q → (r ↔ p))"))
        with self.assertRaises(ValueError):
            export_names.reverse_iffs(f("(p → q)"), ["root"])      # an implication is never reversed
        with self.assertRaises(ValueError):
            f("(p → q")

    def test_pm_names_not_keys(self):
        names = json.loads((ROOT / "data" / "naming" / "pm_names.json").read_text(encoding="utf-8"))["names"]
        nums = [r["number"] for r in names]
        self.assertEqual(len(nums), len(set(nums)))
        self.assertEqual(sum(r["name"] == "Transp" for r in names), 7)


if __name__ == "__main__":
    unittest.main()
