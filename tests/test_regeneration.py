"""Every generated source is what its generator writes, byte for byte (scripts/README.md).

The statements of ✱1–✱5 are tied to PM's text only by the generator from data/vol1.jsonl
(docs/STATEMENT_MUTATION.md): a hand edit of PM/Statements.lean, or of another generated file, would
otherwise go unnoticed, since the proofs and the truth-table checks would still pass. Here the
generators run, as they are run by hand, in a scratch copy of the repository (its tracked and
untracked files, and the build outputs Lean reads), in the order of scripts/README.md, and each file
they write must equal the one in the repository, and they write nothing else. Two planted differences
must be found: a line added by hand to each generated file, and a formula of data/vol1.jsonl changed,
which PM/Statements.lean, regenerated, must follow. Every Lean file whose head says it is generated must
be listed here with its generator.
"""
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # for `common`, however the tests are run
from common import ROOT

# generator, in the order they must run (gen_quant_lift.py reads PM/Statements.lean), and what it writes
GENERATORS = [
    (["scripts/vol1_items.py"], ["data/vol1_items.json"]),
    (["scripts/gen_lean.py"], ["PM/Statements.lean"]),
    (["scripts/gen_quant_lift.py"], ["PM/QuantLift.lean"]),
    (["scripts/gen_axiomcheck.py"], ["AxiomCheck.lean"]),
    (["scripts/export_names.py"], ["data/export_names.json", "Checks/Counterparts.lean",
                                   "Checks/MathlibCounterparts/MathlibCounterparts.lean"]),
]
GENERATED = [p for _, ps in GENERATORS for p in ps]
# the head of a generated Lean file says so
MARK = re.compile(r"\A(?:--[^\n]*\n){0,3}--[^\n]*\b(?:Generated|Written) by scripts/")


def tracked():
    """The repository's files, tracked or not ignored."""
    out = subprocess.run(["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"], cwd=ROOT,
                         capture_output=True, text=True, check=True).stdout.split("\0")
    return [f for f in out if f and (ROOT / f).is_file()]


def files(root):
    """Every file of a scratch copy outside .lake and Python's caches."""
    return sorted(str(p.relative_to(root)) for p in root.rglob("*")
                  if p.is_file() and not {".lake", "__pycache__"} & set(p.relative_to(root).parts))


def scratch_copy(dest):
    for f in tracked():
        (dest / f).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / f, dest / f)
    shutil.copytree(ROOT / ".lake" / "build", dest / ".lake" / "build")


def regenerate(root):
    """Run every generator in `root`; return {path: (bytes before, bytes after)} for the files they write,
    and the paths of other files that they added or changed."""
    before = {f: (root / f).read_bytes() for f in files(root)}
    for cmd, _ in GENERATORS:
        r = subprocess.run([sys.executable, *cmd], cwd=root, capture_output=True, text=True, timeout=1800)
        if r.returncode != 0:
            raise AssertionError(f"{' '.join(cmd)} failed:\n{r.stdout[-2000:]}\n{r.stderr[-2000:]}")
    gen = {p: (before.get(p), (root / p).read_bytes()) for p in GENERATED}
    others = [f for f in files(root) if f not in gen and before.get(f) != (root / f).read_bytes()]
    return gen, others


def differ(gen):
    return sorted(p for p, (a, b) in gen.items() if a != b)


class TestRegeneration(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        cls.base = pathlib.Path(cls.tmp.name)

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def copy(self, name):
        root = self.base / name
        scratch_copy(root)
        return root

    def test_every_generated_file_is_listed(self):
        # a Lean file whose head says it is generated has its generator above, and every file listed exists
        marked = sorted(f for f in tracked() if f.endswith(".lean")
                        and MARK.match((ROOT / f).read_text(encoding="utf-8")))
        self.assertEqual(marked, sorted(p for p in GENERATED if p.endswith(".lean")))
        for p in GENERATED:
            self.assertTrue((ROOT / p).is_file(), p)

    def test_committed_files_are_regenerated_byte_for_byte(self):
        gen, others = regenerate(self.copy("clean"))
        self.assertEqual(differ(gen), [], "a generated file differs from its regeneration: run its generator")
        self.assertEqual(others, [], "a generator wrote a file it is not listed for")

    def test_planted_edit_of_each_generated_file_is_found(self):
        root = self.copy("edited")
        for p in GENERATED:
            f = root / p
            f.write_bytes(f.read_bytes() + (b"\n" if p.endswith(".json") else b"-- edited by hand\n"))
        gen, _ = regenerate(root)
        self.assertEqual(differ(gen), sorted(GENERATED))

    def test_planted_change_of_the_transcription_is_found(self):
        # ✱2·02 (q ⊃ p ⊃ q) read as q ⊃ q ⊃ q in data/vol1.jsonl: PM/Statements.lean, regenerated, differs
        root = self.copy("source")
        src = root / "data" / "vol1.jsonl"
        lines = src.read_text(encoding="utf-8").splitlines(keepends=True)
        k = next(i for i, l in enumerate(lines) if json.loads(l)["id"] == "*2.02")
        rec = json.loads(lines[k])
        old = rec["statement"]
        rec["statement"] = old.replace(". p \\supset q", ". q \\supset q")
        self.assertNotEqual(rec["statement"], old)
        lines[k] = json.dumps(rec, ensure_ascii=False) + "\n"
        src.write_text("".join(lines), encoding="utf-8")
        gen, _ = regenerate(root)
        self.assertIn("PM/Statements.lean", differ(gen))
        self.assertIn("def s2_02 (q : F) : F", gen["PM/Statements.lean"][1].decode("utf-8"))


if __name__ == "__main__":
    unittest.main()
