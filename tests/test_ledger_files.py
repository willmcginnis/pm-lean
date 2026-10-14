"""Every ledger file parses, ends with a newline, and every row has the fields of its ledger.

A review found that four ledger files had lost their final newline in a rewrite. The schemas below
are the fields each ledger's rows have (required, and optional with their types); a row missing a
field, with a field of the wrong type, or with a field no row of that ledger has, fails.
"""
import json
import os
import re
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # for `common`, however the tests are run
from common import DATA

STAR = {"id": str, "page": int, "category": str, "method": str, "cited_used": list, "extra_used": list,
        "cited_unused": list, "note": str, "fidelity": str, "pm_text": str, "tacit": list, "reason": str}
GLUE = {"glue": list, "glue_kind": list}

# file stem: (required fields, optional fields)
SCHEMA = {
    "replay": ({"id": str, "tag": str, "cited": list},
               {"extra": list, "uses_unresolved": list, "in_lean": bool, "repair_src": list}),
    "replay2": ({k: STAR[k] for k in STAR if k not in ("page", "category", "tacit")},
                {"tacit": list, "scan_check": dict}),
    "star11": ({**STAR, **GLUE}, {}),
    "star12": (STAR, {}),
    "star13": ({**STAR, **GLUE}, {}),
    "star14": ({**STAR, **GLUE}, {}),
    "star20": ({**STAR, **GLUE}, {}),
    "star21": ({**STAR, **GLUE}, {}),
    "star22": ({**STAR, **GLUE}, {}),
    "star23": ({**STAR, **GLUE}, {}),
    "star24": ({**STAR, **GLUE}, {}),
    "star25": ({**STAR, **GLUE}, {}),
    "star9f": ({**STAR, **GLUE}, {}),
}
VALUES = {"fidelity": {"pm-lines", "pm-lines+extra", "unchanged"},
          "category": {"assertion", "rule/prose", "primitive", "type"},
          "pm_text": {"dem", "hint", "none", "analogue"},
          "tag": {"FAITHFUL", "REPAIRED", "UNRESOLVED"}}
GLUE_KINDS = {"chain", "order", "under-exists"}


class LedgerFiles(unittest.TestCase):
    def files(self):
        fs = sorted(DATA.glob("*_ledger.json"))
        self.assertTrue(fs, "no ledger files found")
        return fs

    def test_every_ledger_has_a_schema(self):
        self.assertEqual(sorted(f.name[: -len("_ledger.json")] for f in self.files()), sorted(SCHEMA))

    def test_final_newline(self):
        for f in self.files():
            with self.subTest(f.name):
                self.assertTrue(f.read_bytes().endswith(b"\n"), f"{f.name} does not end with a newline")

    def test_rows(self):
        for f in self.files():
            req, opt = SCHEMA[f.name[: -len("_ledger.json")]]
            rows = json.loads(f.read_text(encoding="utf-8"))
            self.assertIsInstance(rows, list, f.name)
            ids = [r.get("id") for r in rows]
            self.assertEqual(len(ids), len(set(ids)), f"{f.name}: duplicate ids")
            for r in rows:
                with self.subTest(file=f.name, id=r.get("id")):
                    self.assertEqual(sorted(set(req) - set(r)), [], "missing fields")
                    self.assertEqual(sorted(set(r) - set(req) - set(opt)), [], "unknown fields")
                    for k, v in r.items():
                        self.assertIsInstance(v, {**req, **opt}[k], k)
                        if k in VALUES:
                            self.assertIn(v, VALUES[k], k)
                    self.assertRegex(r["id"], r"^\*\d+\.\d+$")
                    for k in ("cited_used", "extra_used", "cited_unused", "glue", "cited", "extra"):
                        for x in r.get(k, []):
                            self.assertTrue(isinstance(x, str) and re.fullmatch(r"\*\d+\.\d+|\w+ \(\*\d+\.\d+\)", x),
                                            f"{k}: {x!r}")
                    if "glue" in r:
                        self.assertEqual(len(r["glue"]), len(r["glue_kind"]), "glue and glue_kind differ in length")
                        self.assertLessEqual(set(r["glue_kind"]), GLUE_KINDS)


if __name__ == "__main__":
    unittest.main()
