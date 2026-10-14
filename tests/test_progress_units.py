"""docs/PROGRESS.md's paragraph on the checks' unit is generated, and its figures are the checks'.

A release review found that the paragraph, then written by hand, kept the counts of an earlier revision
(485 declarations, 276 numbered assertions from ✱9 on, 272 proved, 460 proved in all) under tables of a
later one (629, 420, 416, 604), while it said that its figures were for the commit named with the tables.
scripts/progress.py now generates it with the tables, from the same files at the same commit."""
import importlib.util
import re
import subprocess
import unittest

from common import ROOT, run

DOC = ROOT / "docs" / "PROGRESS.md"


def progress():
    spec = importlib.util.spec_from_file_location("progress", ROOT / "scripts" / "progress.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


class TestProgressUnits(unittest.TestCase):
    def test_regions_are_their_regeneration(self):
        """Both generated regions are what progress.py generates at the commit the tables name."""
        p = progress()
        t = DOC.read_text(encoding="utf-8")
        m = re.search(r"from the files at commit `([0-9a-f]+)`", p.region(t, p.REGION))
        self.assertIsNotNone(m, "the tables do not name their commit")
        p.LEAN_REF = m.group(1)
        d = p.compute()
        self.assertEqual(p.region(t, p.REGION_UNITS), p.markdown_units(d),
                         "the paragraph on the checks' unit is not progress.py's: run scripts/progress.py --update")
        self.assertEqual(p.region(t, p.REGION), p.markdown(d),
                         "the tables are not progress.py's at their commit: run scripts/progress.py --update")

    def test_figures_are_the_checks(self):
        """The total progress.py computes for the working tree is the count RedCheck and StyleCheck print."""
        snap = subprocess.run(["git", "-C", str(ROOT), "stash", "create"], capture_output=True, text=True,
                              check=True).stdout.strip() or "HEAD"   # the tracked working tree, as a commit
        p = progress()
        p.LEAN_REF = snap
        total = p.compute()["check_unit"]["total"]
        rc, out = run(["lake", "env", "lean", "RedCheck.lean"])
        self.assertEqual(rc, 0, out[-2000:])
        red = re.search(r"\((\d+) PM propositions\)", out)
        rc, out = run(["lake", "env", "lean", "StyleCheck.lean"])
        self.assertEqual(rc, 0, out[-2000:])
        style = re.search(r"^(\d+) PM propositions;", out, re.M)
        self.assertIsNotNone(red, "RedCheck's count not found")
        self.assertIsNotNone(style, "StyleCheck's count not found")
        self.assertEqual((int(red.group(1)), int(style.group(1))), (total, total))


if __name__ == "__main__":
    unittest.main()
