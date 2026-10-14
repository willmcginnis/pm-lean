"""docs/FIDELITY.md names the proofs whose strict count differs from the recorded one; they are the ledgers'.

A release review found the sentence "The strict count differs from the recorded one only at ✱14·25" still
standing, with no chapter range, after ✱24 had added two more such proofs (✱24·33 and ✱24·561). This test
computes, from the ledgers data/fidelity_counts.py reads, every proof that is `pm-lines` in one of the two
readings and not in the other. Each sentence of FIDELITY.md of the form "[In ✱A(–✱B)] the strict count
differs from the recorded one (only) at …" must name exactly those proofs of its chapters: of ✱A to ✱B when
it gives a range, of every chapter when it gives none."""
import re
import unittest

from common import COUNTED, ROOT, ledger

DOC = ROOT / "docs" / "FIDELITY.md"
SENTENCE = re.compile(r"(?:In ✱(\d+)(?:–✱(\d+))? )?[Tt]he strict count differs from the recorded one (?:only )?at "
                      r"((?:✱\d+·\d+(?:, | and )?)+)")


def differing():
    """{chapter: {PM numbers}} of the proofs whose strict and recorded readings differ."""
    out = {}
    for ch in COUNTED:
        for r in ledger(ch):
            if r["category"] != "assertion":
                continue
            strict = not r["extra_used"] and not r["glue"]
            recorded = r["fidelity"] == "pm-lines"
            if strict != recorded:
                out.setdefault(int(ch[len("star"):]), set()).add("✱" + r["id"].lstrip("*").replace(".", "·"))
    return out


class TestFidelityStrictRows(unittest.TestCase):
    def test_named_rows_are_the_ledgers(self):
        text = " ".join(DOC.read_text(encoding="utf-8").split())
        diff = differing()
        sentences = list(SENTENCE.finditer(text))
        self.assertTrue(sentences, "FIDELITY.md has no sentence naming where the strict count differs")
        covered = set()
        for m in sentences:
            lo = int(m.group(1)) if m.group(1) else None
            hi = int(m.group(2)) if m.group(2) else lo
            chapters = [c for c in diff if lo is None or lo <= c <= hi]
            expected = set().union(*(diff[c] for c in chapters)) if chapters else set()
            named = set(re.findall(r"✱\d+·\d+", m.group(3)))
            with self.subTest(sentence=m.group(0)):
                self.assertEqual(named, expected)
            covered |= named
        self.assertEqual(covered, set().union(*diff.values()), "a differing proof is named nowhere")


if __name__ == "__main__":
    unittest.main()
