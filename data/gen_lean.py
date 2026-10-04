#!/usr/bin/env python3
"""Generate lean/PM/Statements.lean: every parsed ✱1–✱5 assertion as a PM.F term, with a kernel-checked
truth-table test. Statements are the scan-verified readings (Gutenberg errata overridden)."""
import json, re
import dots
SCAN_FIX = {"*1.4": r"\vdash \colon p \lor q.\supset.q \lor p"}   # Gutenberg body typo; 1910 scan reads q ∨ p
def lean(t):
    if isinstance(t, str): return t
    op, *a = t
    if op == "~": return f"(.neg {lean(a[0])})"
    f = {"∨": ".or", "⊃": "F.imp", "∧": "F.and", "≡": "F.iff"}[op]
    return f"({f} {lean(a[0])} {lean(a[1])})"
def vars_of(t): return {t} if isinstance(t, str) else set().union(*[vars_of(x) for x in t[1:]])
out, n, skipped = ["import PM.Basic", "namespace PM", "open F", ""], 0, []
for line in open("data/vol1.jsonl"):
    r = json.loads(line)
    m = re.match(r"\*(\d+)\.(\d+)$", r["id"])
    if not m or not 1 <= int(m.group(1)) <= 5 or r.get("is_def"): continue
    src = SCAN_FIX.get(r["id"], r["statement"])
    if "vdash" not in src: skipped.append(r["id"] + "(rule)"); continue
    try: ast = dots.parse(dots.tokenize(src))
    except Exception: skipped.append(r["id"]); continue
    name = f"s{m.group(1)}_{m.group(2)}"
    vs = sorted(vars_of(ast))
    binders = " ".join(f"({v} : F)" for v in vs)
    app = " ".join(f'(.var "{v}")' for v in vs)
    out += [f"/-- {r['id']} -/", f"def {name} {binders} : F := {lean(ast)}", f"example : ({name} {app}).isTaut = true := by decide", ""]
    n += 1
out.append("end PM")
open("lean/PM/Statements.lean", "w").write("\n".join(out))
print("statements:", n, "skipped:", skipped)
