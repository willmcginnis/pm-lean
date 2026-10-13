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
import re
import shutil
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


def supersede(es, ctx, pm="*9.31", reading="landini"):
    """Two generations, as after a release and a superseded statement: the old entry deprecated and
    pointing to the new `_v2` one, which has its own digest; the row of data/changes.tsv; the new one."""
    scratch_lock(es, ctx)
    old = find(es, pm, reading)
    new = copy.deepcopy(old)
    rename(new, old["export"] + "_v2")
    new.update(lean=old["lean"] + "_v2", supersedes=old["export"],
               statement_digest=export_names.sha256("the corrected statement"))
    old.update(deprecated=True, superseded_by=new["export"], deprecated_since="2026-10-13")
    es.insert(es.index(old) + 1, new)
    ctx["changes"] = [{"date": "2026-10-13", "old": old["export"], "new": new["export"], "reason": "test",
                       "statement_id": new["statement_digest"]}]
    return old, new


def m_version_row_for_unchanged(es, ctx):
    # a row of data/changes.tsv for a released card that was not superseded: its name stays, so the row's
    # new name is not exported and the old one is not deprecated
    scratch_lock(es, ctx)
    e = find(es, "*9.31", "landini")
    ctx["changes"] = [{"date": "2026-10-13", "old": e["export"], "new": e["export"] + "_v2", "reason": "test",
                       "statement_id": e["statement_digest"]}]


def m_deprecated_without_row(es, ctx):
    supersede(es, ctx)
    ctx["changes"] = []


def m_deprecated_unreleased(es, ctx):
    old, _ = supersede(es, ctx)
    ctx["lock"] = [r for r in ctx["lock"] if r["export"] != old["export"]]


def m_version_skips(es, ctx):
    old, new = supersede(es, ctx)
    rename(new, old["export"] + "_v3")
    old["superseded_by"] = new["export"]
    ctx["changes"][0]["new"] = new["export"]


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


def m_counterpart_false_match(es, ctx):
    # another real declaration, with its real signature and line, under the recorded formulas
    # (more in tests/test_counterparts.py, which also has Lean check them)
    counterpart(ctx, "*1.3").update(declaration="Or.inl", signature="∀ {a b : Prop}, a → a ∨ b",
                                    source="src/Init/Prelude.lean:622")


def m_counterpart_signature(es, ctx):
    counterpart(ctx, "*1.3")["signature"] = "NOT A LEAN TYPE"


# ---- bundle_names: PM_core_<words>, a platform definition name, unique

def bundle(ctx, module):
    ctx["bundles"] = copy.deepcopy(ctx["bundles"])
    return next(b for b in ctx["bundles"]["bundles"] if b["module"] == module)


def m_bundle_module_style(es, ctx):
    bundle(ctx, "PM.Basic")["name"] = "PM_Basic"           # a name in the style of a module, not PM_core_


def m_bundle_dotted(es, ctx):
    bundle(ctx, "PM.Basic")["name"] = "PM.core_star1_system"


def m_bundle_collides(es, ctx):
    bundle(ctx, "PM.Derived")["name"] = "PM_core_STAR1_system"


def m_bundle_card_slug(es, ctx):
    rename(find(es, "*2.01"), "PM.core_star1_system")


def m_bundle_no_module(es, ctx):
    bundle(ctx, "PM.Complete")["module"] = "PM.Kalmar"


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
    ("versions", m_version_row_for_unchanged), ("versions", m_deprecated_without_row),
    ("versions", m_deprecated_unreleased), ("versions", m_version_skips),
    ("bundle_names", m_bundle_module_style), ("bundle_names", m_bundle_dotted),
    ("bundle_names", m_bundle_collides), ("bundle_names", m_bundle_card_slug), ("bundle_names", m_bundle_no_module),
    ("counterparts", m_counterpart_commit), ("counterparts", m_counterpart_source),
    ("counterparts", m_counterpart_source_escapes), ("counterparts", m_counterpart_export),
    ("counterparts", m_counterpart_not_exact), ("counterparts", m_counterpart_iff_flag),
    ("counterparts", m_counterpart_classical), ("counterparts", m_counterpart_statement_changed),
    ("counterparts", m_counterpart_false_match), ("counterparts", m_counterpart_signature),
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
        self.assertIn("PM/Deprecated/", msg)
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
        # both generations, linked by @[deprecated] and a row of data/changes.tsv: every rule passes, the
        # lock included (the end-to-end version, with Lean, is tests/test_versioning.py)
        es, ctx = entries(), context()
        supersede(es, ctx)
        self.assertEqual(clean(export_names.check(es, ctx)), {})

    def test_row_does_not_rename_a_released_declaration(self):
        # a row of data/changes.tsv never renames a declaration: the locked one keeps its name (the
        # replacement is a different declaration, `<lean>_v<N>`)
        es, ctx = entries(), context()
        m_version_row_for_unchanged(es, ctx)
        rows, defs = export_names.lean_output()
        built = export_names.build(rows, defs, ctx)[0]
        self.assertEqual([e["export"] for e in built], [e["export"] for e in es])
        bad = export_names.check(built, ctx)["versions"]
        self.assertIn("data/changes.tsv: PM.star9_31_reading_landini_v2 is not exported", bad)

    def test_replacement_named_from_the_lock(self):
        # `<lean>_v<N>` is exported as the locked name of `<lean>` with `_v<N>`, whatever the generator
        # would now call `<lean>`
        es, ctx = entries(), context()
        scratch_lock(es, ctx)
        rows, defs = export_names.lean_output()
        row = copy.deepcopy(next(r for r in rows if r["name"] == "PM.q21_71"))
        row["name"] += "_v2"
        for r in ctx["lock"]:
            if r["lean"] == "PM.q21_71":
                r["export"] = "PM.star21_71_as_released"
        e = next(e for e in export_names.build(rows + [row], defs, ctx)[0] if e["lean"] == "PM.q21_71_v2")
        self.assertEqual((e["export"], e["supersedes"]), ("PM.star21_71_as_released_v2", "PM.star21_71_as_released"))

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

    def lock_fixed_point(self, rows, defs, d):
        """generate → --write-lock → generate (→ --write-lock) in the directory d: the same entries, and the
        same lock written twice. Returns the entries."""
        lock, rlock = pathlib.Path(d) / "export_names.lock", pathlib.Path(d) / "readings.lock"
        ctx = export_names.context(lock, rlock)
        es = export_names.build(rows, defs, ctx)[0]
        export_names.write_lock(es, ctx, lock, rlock)
        written = lock.read_bytes(), rlock.read_bytes()
        ctx = export_names.context(lock, rlock)
        again = export_names.build(rows, defs, ctx)[0]
        self.assertEqual(again, es)
        export_names.write_lock(again, ctx, lock, rlock)
        self.assertEqual((lock.read_bytes(), rlock.read_bytes()), written)
        return es

    def test_lock_is_a_fixed_point(self):
        # for the declarations as Lean has them now, whatever is locked already: locking changes no entry
        rows, defs = export_names.lean_output()
        with tempfile.TemporaryDirectory() as d:
            shutil.copy2(export_names.LOCK, pathlib.Path(d) / "export_names.lock")
            shutil.copy2(export_names.READINGS_LOCK, pathlib.Path(d) / "readings.lock")
            self.lock_fixed_point(rows, defs, d)

    def test_locked_replacements_keep_their_chain(self):
        # q21_71 → q21_71_v2 → q21_71_v3, each generation locked in turn: every replacement keeps the link
        # to the one it replaces (end to end, with Lean and data/changes.tsv: tests/test_versioning.py)
        rows, defs = export_names.lean_output()
        q = next(r for r in rows if r["name"] == "PM.q21_71")
        with tempfile.TemporaryDirectory() as d:
            for n in (2, 3):
                rows = rows + [{**copy.deepcopy(q), "name": f"PM.q21_71_v{n}"}]
                es = {e["lean"]: e for e in self.lock_fixed_point(rows, defs, d)}
            self.assertNotIn("supersedes", es["PM.q21_71"])
            self.assertEqual(es["PM.q21_71_v2"]["supersedes"], "PM.star21_71")
            self.assertEqual(es["PM.q21_71_v3"]["supersedes"], "PM.star21_71_v2")
            self.assertEqual(es["PM.q21_71_v3"]["export"], "PM.star21_71_v3")

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

    def test_release_1_0_0_lock(self):
        # release 1.0.0 locked exactly the names of ✱1–✱5 and the three results about the system, with the
        # digests they have now, and no reading (✱1–✱5 have none)
        lock = export_names.read_tsv(export_names.LOCK, export_names.LOCK_COLUMNS)
        sel = export_names.select_chapters(entries(), (1, 5))
        self.assertEqual(len(lock), 196)
        self.assertEqual({(r["export"], r["lean"], r["statement_digest"], r["definitions_digest"]) for r in lock},
                         {(e["export"], e["lean"], e["statement_digest"], e["definitions_digest"]) for e in sel})
        self.assertTrue(all(r["reading"] == "" for r in lock))
        self.assertEqual(json.loads(export_names.READINGS_LOCK.read_text(encoding="utf-8")), {})

    def test_release_version_names_the_root(self):
        # the documented version of 1.0.0 carries the Merkle root of the lock
        root = export_names.merkle_root(export_names.read_tsv(export_names.LOCK, export_names.LOCK_COLUMNS))
        for doc in ("docs/VERSIONING.md", "docs/EXPORT_LOG.md", "CHANGELOG.md"):
            text = (ROOT / doc).read_text(encoding="utf-8")
            self.assertIn(f"1.0.0+m.{root[:12]}", text, doc)
            self.assertEqual(set(re.findall(r"1\.0\.0\+m\.([0-9a-f]+)", text)), {root[:12]}, doc)

    def test_merkle_tree_hash_ct_vectors(self):
        # the test vectors of Certificate Transparency's reference implementation, for 1 to 8 leaves:
        # test_vector_leaves and test_vector_hashes in python/ct/crypto/merkle_test.py of
        # github.com/google/certificate-transparency (RFC 6962 itself publishes none)
        leaves = [bytes.fromhex(h) for h in ["", "00", "10", "2021", "3031", "40414243", "5051525354555657",
                                             "606162636465666768696a6b6c6d6e6f"]]
        roots = ["6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d",
                 "fac54203e7cc696cf0dfcb42c92a1d9dbaf70ad9e621f4bd8d98662f00e3c125",
                 "aeb6bcfe274b70a14fb067a5e5578264db0fa9b51af5e0ba159158f329e06e77",
                 "d37ee418976dd95753c1c73862b9398fa2a2cf9b4ff0fdfe8b30cd95209614b7",
                 "4e3bbb1f7b478dcfe71fb631631519a3bca12c9aefca1612bfce4c13a86264d4",
                 "76e67dadbcdf1e10e1b74ddc608abd2f98dfb16fbce75277b5232a127f2087ef",
                 "ddb89be403809e325750d3d263cd78929c2942b7942a34b77e122c9594a74c8c",
                 "5dc9da79a70659a9ad559cb701ded9a2ab9d823aad2f4960cfe370eff4604328"]
        for n, want in enumerate(roots, 1):
            self.assertEqual(export_names.merkle_tree_hash(leaves[:n]).hex(), want)

    def test_root_binds_names_and_digests(self):
        lock = export_names.read_tsv(export_names.LOCK, export_names.LOCK_COLUMNS)
        root = export_names.merkle_root(lock)
        self.assertEqual(export_names.merkle_root(list(reversed(lock))), root)     # the order of rows: none
        for k in ("export", "statement_digest", "definitions_digest"):
            changed = copy.deepcopy(lock)
            changed[7][k] += "x"
            self.assertNotEqual(export_names.merkle_root(changed), root, k)

    def test_rules_proved_as_theorems_table(self):
        # docs/NAMING.md lists exactly the exported _rule names, each at a line that declares its theorem
        text = (ROOT / "docs" / "NAMING.md").read_text(encoding="utf-8")
        sec = text.split("### Rules proved as theorems", 1)[1].split("\n## ", 1)[0]
        rows = re.findall(r"^\| ✱[^|]*\| `([^`]+)` \| `([^`]+)`, \[([^\]:]+):(\d+)\]", sec, re.M)
        self.assertEqual(sorted(r[0] for r in rows), sorted(e["export"] for e in entries() if e["slot"] == "rule"))
        by = {e["export"]: e for e in entries()}
        for export, lean, path, line in rows:
            self.assertEqual(by[export]["lean"], lean)
            src = (ROOT / path).read_text(encoding="utf-8").splitlines()[int(line) - 1]
            self.assertRegex(src, rf"^theorem {re.escape(lean.rsplit('.', 1)[1])}\b", f"{path}:{line}")

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
