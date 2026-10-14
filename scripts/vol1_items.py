#!/usr/bin/env python3
"""List of PM Vol I's numbered items, by range and category, from data/vol1.jsonl: writes data/vol1_items.json,
the denominator of docs/PROGRESS.md and docs/FORMALIZATION_COMPARISON.md.
Categories: Df, Pp, rule/prose (no assertion sign, stated in words; ✱1–✱14 only), assertion.

Usage: python3 scripts/vol1_items.py"""
import collections, json, pathlib

root = pathlib.Path(__file__).resolve().parent.parent


def rng(c):
    if c == 1: return "1"
    if 2 <= c <= 5: return "2-5"
    if c == 9: return "9"
    if c == 10: return "10"
    if 11 <= c <= 14: return "11-14"
    if 20 <= c <= 56: return "20-56"
    return "60-97"


# vol1.jsonl flags that are wrong against the printed page
FORCE_PP = {"*1.11", "*3.03"}   # rules stated as Pp in PM
# items printed in 1910 that the transcription omits, each placed after the item it follows in the print:
# ✱24·51 (p. 239), whose Dem. the transcription prints under ✱24·5
MISSING = {"*24.5": {"id": "*24.51", "range": "20-56", "chapter": 24, "page": 239, "cat": "assertion"}}

out = []
for line in open(root / "data/vol1.jsonl", encoding="utf-8"):
    r = json.loads(line)
    s, i = r["statement"], r["id"]
    if r["is_def"] or "\\text{Df" in s: cat = "Df"
    elif r["is_pp"] or "\\text{Pp" in s or i in FORCE_PP: cat = "Pp"
    elif "vdash" not in s and r["chapter"] <= 14: cat = "rule/prose"
    else: cat = "assertion"
    out.append({"id": i, "range": rng(r["chapter"]), "chapter": r["chapter"], "page": r["page"], "cat": cat})
    if i in MISSING:
        out.append(MISSING[i])

with open(root / "data/vol1_items.json", "w", encoding="utf-8") as f:
    f.write("[\n" + ",\n".join(json.dumps(o, ensure_ascii=False) for o in out) + "\n]\n")
C = collections.defaultdict(collections.Counter)
for o in out: C[o["range"]][o["cat"]] += 1
for k in ["1", "2-5", "9", "10", "11-14", "20-56", "60-97"]:
    print(k, dict(C[k]), sum(C[k].values()))
print("items", len(out), dict(collections.Counter(o["cat"] for o in out)))
