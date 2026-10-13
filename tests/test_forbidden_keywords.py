"""The search for forbidden keywords (tests/forbidden_keywords.sh, a step of run_all.sh) exempts one line of
one file only: `unsafe def main` in scripts/prove2me/extract_commands.lean.

Each case is a scratch tree outside the repository, so no fixture lies in the tree the search scans: the
exempt line in its own file passes; the same line in another file under scripts/, or outside scripts/,
fails; another `unsafe` line in the exempt file fails. The repository itself passes.
"""
import os
import pathlib
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # for `common`, however the tests are run
from common import ROOT

SCRIPT = ROOT / "tests" / "forbidden_keywords.sh"
EXEMPT = "scripts/prove2me/extract_commands.lean"
MAIN = "unsafe def main (args : List String) : IO UInt32 := do"


def scan(files):
    """Run the search on a scratch tree with the given files (path -> text); return (exit code, output)."""
    with tempfile.TemporaryDirectory() as tmp:
        for path, text in files.items():
            p = pathlib.Path(tmp) / path
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text, encoding="utf-8")
        r = subprocess.run(["bash", str(SCRIPT), tmp], capture_output=True, text=True, timeout=120)
        return r.returncode, r.stdout + r.stderr


class TestForbiddenKeywords(unittest.TestCase):
    def test_exempt_line_in_its_file(self):
        code, out = scan({EXEMPT: f"import Lean\n\n{MAIN}\n  return 0\n"})
        self.assertEqual((code, out.strip()), (0, "none"))

    def test_same_line_in_another_file_under_scripts(self):
        for other in ("scripts/other_tool.lean", "scripts/prove2me/other_tool.lean",
                      "scripts/other/extract_commands.lean", "scripts/prove2me/extract_commands.lean.lean"):
            with self.subTest(other=other):
                code, out = scan({EXEMPT: f"{MAIN}\n  return 0\n", other: f"{MAIN}\n  return 0\n"})
                self.assertEqual(code, 1, out)
                self.assertIn(f"./{other}:1:{MAIN}", out)
                self.assertNotIn(f"./{EXEMPT}:", out)

    def test_same_line_outside_scripts(self):
        code, out = scan({"PM/Tool.lean": f"{MAIN}\n  return 0\n"})
        self.assertEqual(code, 1, out)
        self.assertIn("./PM/Tool.lean:1:", out)

    def test_other_unsafe_line_in_the_exempt_file(self):
        code, out = scan({EXEMPT: f"{MAIN}\n  return 0\n\nunsafe def helper : IO Unit := pure ()\n"})
        self.assertEqual(code, 1, out)
        self.assertIn(f"./{EXEMPT}:4:unsafe def helper", out)
        self.assertNotIn(f"./{EXEMPT}:1:", out)

    def test_repository_passes(self):
        r = subprocess.run(["bash", str(SCRIPT), str(ROOT)], capture_output=True, text=True, timeout=600)
        self.assertEqual((r.returncode, r.stdout.strip()), (0, "none"), r.stdout + r.stderr)


if __name__ == "__main__":
    unittest.main()
