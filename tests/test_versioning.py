"""Superseding a released statement (docs/VERSIONING.md), end to end, in a scratch copy of the repository.

The whole life cycle, twice. After a release (every name locked by `export_names.py --write-lock`),
✱21·71 is superseded as the workflow says: its declaration `PM.q21_71` moves unchanged to
PM/Deprecated/Star21.lean, marked `@[deprecated PM.q21_71_v2]`; the new statement is `PM.q21_71_v2` in
PM/Star21.lean (here the same formula with its two arguments in the other order, a different statement
for the digest); and data/changes.tsv gets the row. Then both generations are exported: the old name with
its locked digest, deprecated and pointing to its replacement, and the new one as `_v2` with its own
digest; every check passes, the lock included. Without the row of data/changes.tsv the check fails.

Then `_v2` is released: `--check --write-lock` locks it, and the regenerated files are byte for byte the
same and pass every check (locking is a fixed point). Then `_v2` is itself superseded by `PM.q21_71_v3`
(the types of the two arguments swapped), released and regenerated the same way: the chain
`PM.star21_71` → `PM.star21_71_v2` → `PM.star21_71_v3` stays intact, each deprecated card pointing to its
direct replacement and each replacement to the card it replaces. Last, without the old declarations, the
check fails.

The copy is built with `lake build` (only PM/Star21.lean and what imports it are rebuilt).
"""
import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # for `common`, however the tests are run
from common import ROOT

OLD_HEAD = "theorem q21_71 [Reducibility S] (ψ χ : V a → V b → QF V) :"
V2_HEAD = "theorem q21_71_v2 [Reducibility S] (χ ψ : V a → V b → QF V) :"
# _v3: the types of the arguments swapped, a statement different from both before it
V3_BLOCK = """theorem q21_71_v3 [Reducibility S] (ψ χ : V b → V a → QF V) :
    QThm S (iff (relEq ψ χ) (.all (τ := Ty.pred1 (Ty.pred2 b a)) fun g =>
      imp (rel ψ fun φ => .app1 g φ) (rel χ fun φ => .app1 g φ))) :=
  q21_19 ψ χ                                                                      -- ✱21·19"""
DEPRECATED_HEAD = """import PM.Star21

namespace PM
open QF
variable {V : Ty → Type} {S : Sys} {a b : Ty}
"""


def sh(cmd, cwd):
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=3600)
    return p.returncode, p.stdout + p.stderr


def deprecated(block, new):
    """A superseded declaration, unchanged, marked as replaced by `new`."""
    return f'\n@[deprecated {new} (since := "2026-10-13")]\n{block}\n'


class TestSupersede(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        cls.root = pathlib.Path(cls.tmp.name) / "repo"
        files = subprocess.run(["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"],
                               cwd=ROOT, capture_output=True, text=True, check=True).stdout.split("\0")
        for f in filter(None, files):
            if (ROOT / f).is_file():
                (cls.root / f).parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(ROOT / f, cls.root / f)
        shutil.copytree(ROOT / ".lake" / "build", cls.root / ".lake" / "build")

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def export(self, *args):
        return sh(["python3", "scripts/export_names.py", *args], self.root)

    def build(self):
        code, out = sh(["lake", "build"], self.root)
        self.assertEqual(code, 0, out[-3000:])

    def entries(self):
        return json.loads((self.root / "data" / "export_names.json").read_text(encoding="utf-8"))

    def generated(self):
        """The bytes of the generated files and of the locks."""
        r = self.root
        return {p: (r / p).read_bytes() for p in ("data/export_names.json", "Checks/Counterparts.lean",
                                                  "data/export_names.lock", "data/naming/readings.lock")}

    def add_change(self, old, new, reason):
        changes = self.root / "data" / "changes.tsv"
        digest = {e["export"]: e for e in self.entries()}[new]["statement_digest"]
        changes.write_text(changes.read_text(encoding="utf-8") +
                           "\t".join(["2026-10-13", old, new, reason, digest]) + "\n", encoding="utf-8")

    def release(self, name):
        """--check --write-lock: `name` is locked; then the lock is a fixed point: regenerated, locked again
        and checked, every generated file is byte for byte the same."""
        code, out = self.export("--check", "--write-lock")
        self.assertEqual(code, 0, out)
        e = {e["export"]: e for e in self.entries()}[name]
        lock = (self.root / "data" / "export_names.lock").read_text(encoding="utf-8")
        self.assertIn(f"{name}\t{e['lean']}\t\t{e['statement_digest']}", lock)
        released = self.generated()
        code, out = self.export()
        self.assertEqual(code, 0, out)
        self.assertEqual(self.generated(), released)
        code, out = self.export("--check", "--write-lock")
        self.assertEqual(code, 0, out)
        self.assertEqual(self.generated(), released)
        code, out = self.export("--check")
        self.assertEqual(code, 0, out)
        self.assertIn("lock ok", out)
        self.assertIn("versions ok", out)

    def test_supersede(self):
        r = self.root
        star21_path, dep_path = r / "PM" / "Star21.lean", r / "PM" / "Deprecated" / "Star21.lean"
        # a release: every name locked
        code, out = self.export("--check", "--write-lock")
        self.assertEqual(code, 0, out)
        lock = (r / "data" / "export_names.lock").read_text(encoding="utf-8")
        n_entries = len(self.entries())   # the exports before any change; each superseding adds one
        before = next(e for e in self.entries() if e["lean"] == "PM.q21_71")
        self.assertEqual(before["export"], "PM.star21_71")
        self.assertIn("PM.star21_71\tPM.q21_71\t\t" + before["statement_digest"], lock)

        # supersede ✱21·71: the old declaration to PM/Deprecated/ unchanged, the new one as q21_71_v2
        star21 = star21_path.read_text(encoding="utf-8")
        i = star21.index(OLD_HEAD)
        j = star21.index("\n\n", i)
        old_block = star21[i:j]
        v2_block = old_block.replace(OLD_HEAD, V2_HEAD)
        star21_path.write_text(star21[:i] + v2_block + star21[j:], encoding="utf-8")
        dep_path.parent.mkdir()
        dep_path.write_text(DEPRECATED_HEAD + deprecated(old_block, "q21_71_v2") + "\nend PM\n", encoding="utf-8")
        pm = (r / "PM.lean").read_text(encoding="utf-8")
        (r / "PM.lean").write_text(pm + "-- superseded declarations, kept (docs/VERSIONING.md)\n"
                                        "import PM.Deprecated.Star21\n", encoding="utf-8")
        self.build()

        # the generator names both; the check wants the row of data/changes.tsv
        code, out = self.export()
        self.assertNotEqual(code, 0)
        self.assertIn("PM.star21_71_v2: no row of data/changes.tsv gives this name as new", out)
        self.assertIn("PM.star21_71: deprecated with no row of data/changes.tsv giving it as old", out)
        changes = r / "data" / "changes.tsv"
        self.add_change("PM.star21_71", "PM.star21_71_v2", "test: arguments in the other order")
        code, out = self.export()
        self.assertEqual(code, 0, out)
        code, out = self.export("--check")
        self.assertEqual(code, 0, out)
        self.assertIn("lock ok", out)
        self.assertIn("versions ok", out)

        # both generations: the old one keeps its name and digest, deprecated, pointing to the new one
        es = {e["export"]: e for e in self.entries()}
        old, new = es["PM.star21_71"], es["PM.star21_71_v2"]
        self.assertEqual(old["lean"], "PM.q21_71")
        self.assertEqual(old["source"], "PM/Deprecated/Star21.lean")
        self.assertEqual(old["statement_digest"], before["statement_digest"])
        self.assertEqual(old["definitions_digest"], before["definitions_digest"])
        self.assertTrue(old["deprecated"])
        self.assertEqual(old["superseded_by"], "PM.star21_71_v2")
        self.assertEqual(old["deprecated_since"], "2026-10-13")
        self.assertEqual(new["lean"], "PM.q21_71_v2")
        self.assertEqual(new["supersedes"], "PM.star21_71")
        self.assertNotIn("deprecated", new)
        self.assertNotEqual(new["statement_digest"], old["statement_digest"])
        self.assertEqual(len(es), n_entries + 1)

        # without the row of data/changes.tsv: fails
        with_row = changes.read_text(encoding="utf-8")
        changes.write_text(with_row.rsplit("2026-10-13", 1)[0], encoding="utf-8")
        code, out = self.export("--check")
        self.assertNotEqual(code, 0)
        self.assertIn("versions FAILED", out)
        changes.write_text(with_row, encoding="utf-8")
        self.assertEqual(self.export("--check")[0], 0)

        # _v2 released: locking it changes nothing, and it keeps its link to the card it replaces
        self.release("PM.star21_71_v2")
        self.assertEqual({e["export"]: e for e in self.entries()}, es)

        # _v2 superseded in turn: it moves unchanged to PM/Deprecated/ (before q21_71, whose @[deprecated]
        # names it), q21_71_v3 replaces it
        star21 = star21_path.read_text(encoding="utf-8")
        star21_path.write_text(star21.replace(v2_block, V3_BLOCK), encoding="utf-8")
        dep_path.write_text(DEPRECATED_HEAD + deprecated(v2_block, "q21_71_v3")
                            + deprecated(old_block, "q21_71_v2") + "\nend PM\n", encoding="utf-8")
        self.build()
        code, out = self.export()
        self.assertNotEqual(code, 0)
        self.assertIn("PM.star21_71_v3: no row of data/changes.tsv gives this name as new", out)
        self.add_change("PM.star21_71_v2", "PM.star21_71_v3", "test: argument types swapped")
        code, out = self.export()
        self.assertEqual(code, 0, out)
        self.release("PM.star21_71_v3")

        # three generations, each deprecated one pointing to its direct replacement
        es = {e["export"]: e for e in self.entries()}
        v1, v2, v3 = es["PM.star21_71"], es["PM.star21_71_v2"], es["PM.star21_71_v3"]
        self.assertEqual(len(es), n_entries + 2)
        self.assertEqual([e["lean"] for e in (v1, v2, v3)], ["PM.q21_71", "PM.q21_71_v2", "PM.q21_71_v3"])
        self.assertEqual([e.get("supersedes") for e in (v1, v2, v3)], [None, "PM.star21_71", "PM.star21_71_v2"])
        self.assertEqual([e.get("superseded_by") for e in (v1, v2, v3)],
                         ["PM.star21_71_v2", "PM.star21_71_v3", None])
        self.assertEqual([e.get("deprecated", False) for e in (v1, v2, v3)], [True, True, False])
        self.assertEqual(v2["source"], "PM/Deprecated/Star21.lean")
        self.assertEqual((v1["statement_digest"], v2["statement_digest"]),
                         (before["statement_digest"], new["statement_digest"]))
        self.assertEqual(len({e["statement_digest"] for e in (v1, v2, v3)}), 3)

        # without the old declarations: fails (the released names are gone)
        dep_path.unlink()
        (r / "PM.lean").write_text(pm, encoding="utf-8")
        self.build()
        code, out = self.export("--check")
        self.assertNotEqual(code, 0)
        self.assertIn("data/export_names.json is not up to date", out)
        code, out = self.export()             # regenerated: the old names are gone
        self.assertNotEqual(code, 0)
        self.assertIn("PM.star21_71: in data/export_names.lock but no longer exported", out)
        self.assertIn("PM.star21_71_v2: in data/export_names.lock but no longer exported", out)
        self.assertIn("lock FAILED", out)
        self.assertFalse({"PM.star21_71", "PM.star21_71_v2"} & {e["export"] for e in self.entries()})


if __name__ == "__main__":
    unittest.main()
