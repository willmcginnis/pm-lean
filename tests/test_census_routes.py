"""docs/KERNEL_CENSUS.md's requirements for a restricted checker name every auto-param route the census finds.

A release review found the requirements still saying that the auto-param of `PM.Pf.hy` was "the only route"
of `Lean.Syntax` into the derivations, after ✱24's `PM.qclsEqCongr` had added a second one that the generated
tables of the same page list. This test reads every `<declaration>._auto_<n>` in the generated part and
requires its declaration to be named, in backquotes, both in the hand-written summary and in the section
"What it implies for a restricted checker"."""
import re
import unittest

from common import ROOT

DOC = ROOT / "docs" / "KERNEL_CENSUS.md"
BEGIN = "<!-- BEGIN GENERATED"
END = "<!-- END GENERATED -->"


def parts():
    text = DOC.read_text(encoding="utf-8")
    i, j = text.index(BEGIN), text.index(END)
    return text[:i], text[i:j]


class TestCensusRoutes(unittest.TestCase):
    def test_every_route_is_named(self):
        written, generated = parts()
        routes = sorted(set(re.findall(r"(PM\.[\w.]+?)\._auto_\d+", generated)))
        self.assertTrue(routes, "the generated tables name no auto-param")
        start = written.index("## What it implies for a restricted checker")
        rest = written[start + 1:]
        section = rest[: rest.index("\n## ")] if "\n## " in rest else rest
        summary = written[:start]
        for decl in routes:
            with self.subTest(route=decl):
                self.assertIn(f"`{decl}`", summary, f"the summary does not name {decl}'s auto-param")
                self.assertIn(f"`{decl}`", section, f"the restricted-checker requirements do not name {decl}")


if __name__ == "__main__":
    unittest.main()
