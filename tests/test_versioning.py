"""Superseding a released statement (docs/VERSIONING.md), end to end, in a scratch copy of the repository.

After a release (every name locked by `export_names.py --write-lock`), ✱21·71 is superseded as the
workflow says: its declaration `PM.q21_71` moves unchanged to PM/Deprecated/Star21.lean, marked
`@[deprecated PM.q21_71_v2]`; the new statement is `PM.q21_71_v2` in PM/Star21.lean (here the same
formula with its two arguments in the other order, a different statement for the digest); and
data/changes.tsv gets the row. Then both generations are exported: the old name with its locked digest,
deprecated and pointing to its replacement, and the new one as `_v2` with its own digest; every check
passes, the lock included. Without the row of data/changes.tsv, or without the old declaration, the check
fails.

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
NEW_HEAD = "theorem q21_71_v2 [Reducibility S] (χ ψ : V a → V b → QF V) :"
DEPRECATED = """import PM.Star21

namespace PM
open QF
variable {V : Ty → Type} {S : Sys} {a b : Ty}

@[deprecated q21_71_v2 (since := "2026-10-13")]
%s
  q21_71_v2 χ ψ

end PM
"""


def sh(cmd, cwd):
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=3600)
    return p.returncode, p.stdout + p.stderr


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

    def test_supersede(self):
        r = self.root
        # a release: every name locked
        code, out = self.export("--check", "--write-lock")
        self.assertEqual(code, 0, out)
        lock = (r / "data" / "export_names.lock").read_text(encoding="utf-8")
        before = next(e for e in self.entries() if e["lean"] == "PM.q21_71")
        self.assertEqual(before["export"], "PM.star21_71")
        self.assertIn("PM.star21_71\tPM.q21_71\t\t" + before["statement_digest"], lock)

        # supersede ✱21·71: the old declaration to PM/Deprecated/, the new one as q21_71_v2
        star21 = (r / "PM" / "Star21.lean").read_text(encoding="utf-8")
        i = star21.index(OLD_HEAD)
        j = star21.index("\n\n", i)
        old_block = star21[i:j]
        old_statement = old_block[:old_block.rindex(":=") + 2]
        (r / "PM" / "Star21.lean").write_text(star21[:i] + old_block.replace(OLD_HEAD, NEW_HEAD) + star21[j:],
                                              encoding="utf-8")
        (r / "PM" / "Deprecated").mkdir()
        (r / "PM" / "Deprecated" / "Star21.lean").write_text(DEPRECATED % old_statement, encoding="utf-8")
        pm = (r / "PM.lean").read_text(encoding="utf-8")
        (r / "PM.lean").write_text(pm + "-- superseded declarations, kept (docs/VERSIONING.md)\n"
                                        "import PM.Deprecated.Star21\n", encoding="utf-8")
        self.build()

        # the generator names both; the check wants the row of data/changes.tsv
        code, out = self.export()
        self.assertNotEqual(code, 0)
        self.assertIn("PM.star21_71_v2: no row of data/changes.tsv gives this name as new", out)
        self.assertIn("PM.star21_71: deprecated with no row of data/changes.tsv giving it as old", out)
        es = {e["export"]: e for e in self.entries()}
        old, new = es["PM.star21_71"], es["PM.star21_71_v2"]
        changes = r / "data" / "changes.tsv"
        changes.write_text(changes.read_text(encoding="utf-8") +
                           "\t".join(["2026-10-13", "PM.star21_71", "PM.star21_71_v2",
                                      "test: arguments in the other order", new["statement_digest"]]) + "\n",
                           encoding="utf-8")
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
        self.assertEqual(len(es), 524)

        # without the row of data/changes.tsv: fails
        with_row = changes.read_text(encoding="utf-8")
        changes.write_text(with_row.rsplit("2026-10-13", 1)[0], encoding="utf-8")
        code, out = self.export("--check")
        self.assertNotEqual(code, 0)
        self.assertIn("versions FAILED", out)
        changes.write_text(with_row, encoding="utf-8")
        self.assertEqual(self.export("--check")[0], 0)

        # without the old declaration: fails (the released name is gone)
        (r / "PM" / "Deprecated" / "Star21.lean").unlink()
        (r / "PM.lean").write_text(pm, encoding="utf-8")
        self.build()
        code, out = self.export("--check")
        self.assertNotEqual(code, 0)
        self.assertIn("data/export_names.json is not up to date", out)
        code, out = self.export()             # regenerated: the old name is gone
        self.assertNotEqual(code, 0)
        self.assertIn("PM.star21_71: in data/export_names.lock but no longer exported", out)
        self.assertIn("lock FAILED", out)
        self.assertNotIn("PM.star21_71", {e["export"] for e in self.entries()})


if __name__ == "__main__":
    unittest.main()
