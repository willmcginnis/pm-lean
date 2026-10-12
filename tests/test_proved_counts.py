"""The docs' counts of proved propositions and of fidelity labels equal the ledgers' counts.

A review found a count of "proved" propositions that included primitive propositions (✱12·1 and
✱12·11 are taken as primitive, not proved). Here a chapter's proved count is its ledger rows less
those of category `primitive`. Each claim is found in README.md or docs/ by a pattern; a claim the
docs no longer state in this form is skipped (reported as a skip), not failed.
"""
import os
import re
import sys
import unittest
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # for `common`, however the tests are run
from common import docs_text, ledger


def proved(ch):
    return sum(1 for r in ledger(ch) if r["category"] != "primitive")


def fidelity(ch, category=None):
    c = Counter(r["fidelity"] for r in ledger(ch) if category in (None, r["category"]))
    return c["pm-lines"], c["pm-lines+extra"]


def claims():
    """(name, pattern, the numbers the ledgers give for its groups)."""
    star11 = Counter(r["category"] for r in ledger("star11"))
    r2 = Counter(r["fidelity"] for r in ledger("replay2"))
    return [
        ("✱2–✱5 propositions", r"all (\d+) ✱2–✱5 propositions", (len(ledger("replay")),)),
        ("✱11 assertions", r"\*\*✱11\*\* \((\d+) assertions; `star11_ledger\.json`\)", (star11["assertion"],)),
        ("✱11 rules", r"✱11 is counted without its (\w+) numbered rules \(✱11·07",
         ({4: "four"}.get(star11["rule/prose"], str(star11["rule/prose"])),)),
        ("✱13, ✱14 proved", r"\| ✱13, ✱14 \| (\d+) of \d+; (\d+) of \d+", (proved("star13"), proved("star14"))),
        ("✱20, ✱21 proved", r"\| ✱20, ✱21 \| (\d+) of \d+; (\d+) of \d+", (proved("star20"), proved("star21"))),
        ("✱13–✱21 formalized", r"Of the (\d+) formalized ✱13, ✱14, ✱20 and ✱21 propositions \(counting one variant of ✱14·21\)",
         (sum(proved(c) for c in ["star13", "star14", "star20", "star21"]) + 1,)),
        ("✱11 fidelity", r"All \d+ follow PM's Dem\. lines or bracketed hint: (\d+)\s+`pm-lines`, (\d+) `pm-lines\+extra`",
         fidelity("star11", "assertion")),
        ("✱13 fidelity", r"✱13 (\d+) / (\d+) of (\d+)", fidelity("star13") + (proved("star13"),)),
        ("✱14 fidelity", r"✱14\s+(\d+) / (\d+) of (\d+)", fidelity("star14") + (proved("star14"),)),
        ("✱20 fidelity", r"✱20 (\d+) / (\d+) of (\d+)", fidelity("star20") + (proved("star20"),)),
        ("✱21 fidelity", r"✱21 (\d+) / (\d+) of (\d+)", fidelity("star21") + (proved("star21"),)),
        ("Replay2 follows PM", r"The other (\d+) were first proved with derived rules \(`PM/Derived\.lean`\)\. (\d+) of these",
         (sum(r2.values()), r2["pm-lines"] + r2["pm-lines+extra"])),
        ("Replay2 pm-lines", r"Of the (\d+) that are `pm-lines`", (r2["pm-lines"],)),
        ("Replay2 pm-lines+extra", r"The (\d+) `pm-lines\+extra` proofs need", (r2["pm-lines+extra"],)),
        ("Replay2 unchanged", r"(\d+) are `unchanged`: the transcription", (r2["unchanged"],)),
    ]


class ProvedCounts(unittest.TestCase):
    def test_star12_is_primitive(self):
        rows = ledger("star12")
        self.assertEqual(sorted(r["id"] for r in rows), ["*12.1", "*12.11"])
        self.assertTrue(all(r["category"] == "primitive" for r in rows))
        self.assertRegex(docs_text(), r"✱12 \| no assertions: ✱12·1, ✱12·11 are rules")

    def test_claims(self):
        text = docs_text()
        for name, pattern, want in claims():
            with self.subTest(name):
                found = re.findall(pattern, text)
                if not found:
                    self.skipTest(f"claim not found in the docs: {pattern}")
                for f in found:
                    got = f if isinstance(f, tuple) else (f,)
                    self.assertEqual(tuple(str(x) for x in want), got, f"docs claim {pattern!r}")


if __name__ == "__main__":
    unittest.main()
