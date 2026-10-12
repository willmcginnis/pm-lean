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
        ("✱11 assertions", r"all (\d+) numbered ✱11 assertions", (star11["assertion"],)),
        ("✱11 rules", r"and so are the (\w+) numbered rules ✱11·07",
         ({4: "four"}.get(star11["rule/prose"], str(star11["rule/prose"])),)),
        ("✱13 proved", r"all (\d+) numbered ✱13 propositions", (proved("star13"),)),
        ("✱14 proved", r"all (\d+) numbered ✱14 propositions", (proved("star14"),)),
        ("✱20 proved", r"(\d+) of the \d+ numbered ✱20 propositions", (proved("star20"),)),
        ("✱21 proved", r"(\d+) of the \d+ numbered ✱21 propositions", (proved("star21"),)),
        ("✱13–✱21 formalized", r"Of the (\d+) formalized ✱13, ✱14, ✱20 and ✱21 propositions \(counting one variant of ✱14·21\)",
         (sum(proved(c) for c in ["star13", "star14", "star20", "star21"]) + 1,)),
        ("✱11 fidelity", r"Fidelity of ✱11[^\n]*? (\d+) are `pm-lines`:[^\n]*? (\d+) are `pm-lines\+extra`",
         fidelity("star11", "assertion")),
        ("✱13 fidelity", r"✱13: (\d+) of the (\d+) proofs are `pm-lines`, (\d+) `pm-lines\+extra`",
         (fidelity("star13")[0], proved("star13"), fidelity("star13")[1])),
        ("✱14 fidelity", r"✱14: (\d+) and (\d+) of (\d+)[;.]", fidelity("star14") + (proved("star14"),)),
        ("✱20 fidelity", r"✱20: (\d+) and (\d+) of (\d+)[;.]", fidelity("star20") + (proved("star20"),)),
        ("✱21 fidelity", r"✱21: (\d+) and (\d+) of (\d+)[;.]", fidelity("star21") + (proved("star21"),)),
        ("Replay2 follows PM", r"In `PM/Replay2.lean`, (\d+) of the (\d+) proofs follow PM's own proof",
         (r2["pm-lines"] + r2["pm-lines+extra"], sum(r2.values()))),
        ("Replay2 fidelity", r"`fidelity` field is `pm-lines` for (\d+) proofs\. It is `pm-lines\+extra` for (\d+) proofs"
         r"[^\n]*?It is `unchanged` for (\d+) proofs", (r2["pm-lines"], r2["pm-lines+extra"], r2["unchanged"])),
    ]


class ProvedCounts(unittest.TestCase):
    def test_star12_is_primitive(self):
        rows = ledger("star12")
        self.assertEqual(sorted(r["id"] for r in rows), ["*12.1", "*12.11"])
        self.assertTrue(all(r["category"] == "primitive" for r in rows))
        self.assertIn("✱12·1 and ✱12·11 (primitive)", docs_text())

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
