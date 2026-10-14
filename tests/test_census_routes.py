"""docs/KERNEL_CENSUS.md's summary and requirements for a restricted checker agree with the auto-params the
census finds reaching the derivations.

A release review found the requirements still saying that the auto-param of `PM.Pf.hy` was "the only route"
of `Lean.Syntax` into the derivations, after ✱24's `PM.qclsEqCongr` had added a second one that the generated
tables of the same page list (✱25's `PM.qrelEqCongr` added a third). Since the maintainer's ruling of
2026-10-14 no auto-param reaches them (the three premises are explicit arguments). This test reads every `<declaration>._auto_<n>` in the generated part. If
there are any, it requires each declaration to be named, in backquotes, both in the hand-written summary and
in the section "What it implies for a restricted checker"; if there are none, it requires both to say that
no auto-param reaches the derivations."""
import re
import unittest

from common import ROOT

DOC = ROOT / "docs" / "KERNEL_CENSUS.md"
BEGIN = "<!-- BEGIN GENERATED"
END = "<!-- END GENERATED -->"
NONE_SAID = "no auto-param reaches the derivations"


def parts(text):
    i, j = text.index(BEGIN), text.index(END)
    return text[:i], text[i:j]


def problems(text):
    """What the hand-written part fails to say about the auto-params of the generated part."""
    written, generated = parts(text)
    routes = sorted(set(re.findall(r"(PM\.[\w.]+?)\._auto_\d+", generated)))
    start = written.index("## What it implies for a restricted checker")
    rest = written[start + 1:]
    section = rest[: rest.index("\n## ")] if "\n## " in rest else rest
    summary = written[:start]
    out = []
    for decl in routes:
        if f"`{decl}`" not in summary:
            out.append(f"the summary does not name {decl}'s auto-param")
        if f"`{decl}`" not in section:
            out.append(f"the restricted-checker requirements do not name {decl}")
    if not routes:
        for where, part in [("the summary", summary), ("the restricted-checker requirements", section)]:
            if NONE_SAID not in " ".join(part.lower().split()):
                out.append(f"no auto-param in the tables, and {where} does not say '{NONE_SAID}'")
    return out


class TestCensusRoutes(unittest.TestCase):
    def test_doc_agrees_with_the_tables(self):
        self.assertEqual(problems(DOC.read_text(encoding="utf-8")), [])

    def test_a_route_the_docs_do_not_name_fails(self):
        text = DOC.read_text(encoding="utf-8").replace(END, "`PM.Pf.other._auto_1`\n" + END)
        found = problems(text)
        self.assertIn("the summary does not name PM.Pf.other's auto-param", found)
        self.assertIn("the restricted-checker requirements do not name PM.Pf.other", found)

    def test_no_route_needs_the_docs_to_say_so(self):
        text = DOC.read_text(encoding="utf-8")
        written, _ = parts(text)
        self.assertIn(NONE_SAID, " ".join(written.lower().split()))
        silent = re.sub(r"(?i)no\s+auto-param\s+reaches\s+the\s+derivations", "x", written) + text[len(written):]
        self.assertEqual(len(problems(silent)), 2, problems(silent))


if __name__ == "__main__":
    unittest.main()
