#!/usr/bin/env python3
"""Fidelity counts per chapter from the ledgers (star11/13/14/20/21), in the three readings of README.md
(Fidelity): `strict` counts every glue proposition as extra; `as recorded` is the ledger's `fidelity` field
(chaining under a hypothesis tacit, other glue extra); `glue tacit` counts no glue as extra. A proof is
`pm-lines` in a reading when nothing it needs beyond PM's citations and the tacit steps is counted as
extra. The numbered rules (four in ✱11, two each in ✱20 and ✱21) are left out, as in README.md."""
import json, pathlib

root = pathlib.Path(__file__).resolve().parent
for ch in ["star11", "star13", "star14", "star20", "star21"]:
    rows = [r for r in json.loads((root / f"{ch}_ledger.json").read_text()) if r["category"] == "assertion"]
    strict = sum(1 for r in rows if not r["extra_used"] and not r["glue"])
    recorded = sum(1 for r in rows if r["fidelity"] == "pm-lines")
    lenient = sum(1 for r in rows if set(r["extra_used"]) <= set(r["glue"]))
    n = len(rows)
    print(f"{ch}: {n} proofs; pm-lines strict {strict}, as recorded {recorded}, glue tacit {lenient}")
    for r in rows:
        if (r["fidelity"] == "pm-lines") != (not r["extra_used"]):
            print(f"  {r['id']}: fidelity {r['fidelity']} but extra_used {r['extra_used']}")
