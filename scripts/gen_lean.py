#!/usr/bin/env python3
"""Generate PM/Statements.lean: every parsed ✱1–✱5 assertion of data/vol1.jsonl as a PM.F term, with a
kernel-checked truth-table test. Statements are the scan-verified readings (Gutenberg errata overridden).

Usage: python3 scripts/gen_lean.py   (reads data/vol1.jsonl, writes PM/Statements.lean; see scripts/README.md)

The dot-notation parser below (norm, tokenize, parse, expr) is copied from scripts/dots.py of the companion
repository github.com/willmcginnis/principia-mathematica-text-audit (same author, MIT), so that this script
needs nothing outside this repository."""
import json, pathlib, re

root = pathlib.Path(__file__).resolve().parent.parent

# --- PM dot-notation parser for propositional formulas (Gutenberg LaTeX) ---
DOT = {".": 1, ":": 2, ":.": 3, ".:": 3, "::": 4}
def norm(s):
    s = re.sub(r'\\begin\{align\*?\}|\\end\{align\*?\}', '', s)
    s = re.sub(r'&?\s*\[\\text\{[^\]]*\]\s*$', '', s.strip())          # trailing [refs] in align
    s = s.replace('\\\\', ' ').replace('&', ' ')
    s = re.sub(r'\\text\{[^}]*\}\.?', '', s)                 # Pp, Df, refs
    s = re.sub(r'\\quad.*$', '', s)
    s = s.replace(r'\colon\ldotp', ':.').replace(r'\ldotp', '.').replace(r'\colon', ':')
    s = re.sub(r'\\(left|right)\b', '', s)
    s = re.sub(r'\{\\sim\}', '~', s).replace(r'\sim', '~')
    s = s.replace(r'\vdash', '⊢').replace(r'\supset', '⊃').replace(r'\equiv', '≡').replace(r'\lor', '∨')
    s = re.sub(r'\\[,;! ]|\\quad|\\qquad', ' ', s)
    s = s.replace('\\{', '(').replace('\\}', ')')   # PM's curly brackets are grouping brackets
    s = s.replace('{', '').replace('}', '')
    return s
def tokenize(s):
    s = norm(s); out = []; i = 0
    while i < len(s):
        c = s[i]
        if c.isspace(): i += 1; continue
        if c in '.:':
            j = i; grp = ''
            while j < len(s) and (s[j] in '.:' or s[j].isspace()):
                if not s[j].isspace(): grp += s[j]
                j += 1
            if grp not in DOT: raise ValueError(f"dot group {grp!r}")
            out.append(('D', DOT[grp])); i = j; continue
        if c in '⊃≡∨': out.append(('B', c)); i += 1; continue
        if c == '~': out.append(('N', c)); i += 1; continue
        if c in '()': out.append((c, c)); i += 1; continue
        if c == '⊢': out.append(('T', c)); i += 1; continue
        if c.isalpha(): out.append(('V', c)); i += 1; continue
        raise ValueError(f"char {c!r} in {s!r}")
    return out
def parse(toks):
    # strip assertion sign and its punctuation
    if toks and toks[0][0] == 'T':
        toks = toks[1:]
        if toks and toks[0][0] == 'D': toks = toks[1:]
    return expr(toks)
def expr(toks):
    toks = list(toks)
    while toks and toks[0][0] == 'D': toks = toks[1:]          # stray leading punctuation
    while toks and toks[-1][0] == 'D': toks = toks[:-1]
    if not toks: raise ValueError("empty")
    # find split candidates at paren depth 0
    best = None; depth = 0
    for i, (k, v) in enumerate(toks):
        if k == '(': depth += 1; continue
        if k == ')': depth -= 1; continue
        if depth: continue
        if k == 'B':
            l = toks[i-1][1] if i > 0 and toks[i-1][0] == 'D' else 0
            r = toks[i+1][1] if i+1 < len(toks) and toks[i+1][0] == 'D' else 0
            rank = 2*max(l, r) + 1 if max(l, r) else (0.6 if v in '⊃≡' else 0.3)
            cand = (rank, i if v == '∨' else -i, i, v)          # *2.33: p v q v r = (p v q) v r (left-grouped)
        elif k == 'D':
            prevB = i > 0 and toks[i-1][0] in 'B'
            nextB = i+1 < len(toks) and toks[i+1][0] == 'B'
            if prevB or nextB: continue
            cand = (2*v, i, i, '∧')                             # conjunction dots, weaker than punctuation; p.q.r = (p.q).r (left-grouped, as Metamath)
        else: continue
        if best is None or cand[:2] > best[:2]: best = cand
    if best is None:
        if toks[0][0] == 'N': return ('~', expr(toks[1:]))
        if toks[0][0] == '(' and toks[-1][0] == ')': return expr(toks[1:-1])
        if len(toks) == 1 and toks[0][0] == 'V': return toks[0][1]
        # juxtaposition without dots (e.g. "~p~q" or "pq") -> conjunction is NOT PM; treat negation chains
        raise ValueError(f"unparsed {toks}")
    _, _, i, op = best
    if op in '⊃≡':   # *3.02 / *4.02 Df: a chain p ⊃ q ⊃ r (equal punctuation) means p ⊃ q . q ⊃ r
        ties = []; depth = 0
        for k2, (kk, vv) in enumerate(toks):
            if kk == '(': depth += 1; continue
            if kk == ')': depth -= 1; continue
            if depth or kk != 'B' or vv != op: continue
            l2 = toks[k2-1][1] if k2 > 0 and toks[k2-1][0] == 'D' else 0
            r2 = toks[k2+1][1] if k2+1 < len(toks) and toks[k2+1][0] == 'D' else 0
            rk = 2*max(l2, r2) + 1 if max(l2, r2) else (0.6 if vv in '⊃≡' else 0.3)
            if rk == best[0]: ties.append(k2)
        if len(ties) > 1:
            segs, prev = [], 0
            for k2 in ties: segs.append(toks[prev:k2]); prev = k2 + 1
            segs.append(toks[prev:])
            segs = [sg[:-1] if sg and sg[-1][0] == 'D' else sg for sg in segs]
            segs = [sg[1:] if sg and sg[0][0] == 'D' else sg for sg in segs]
            parts = [expr(sg) for sg in segs]
            res = (op, parts[0], parts[1])
            for a, b in zip(parts[1:-1], parts[2:]): res = ('∧', res, (op, a, b))
            return res
    L, R = toks[:i], toks[i+1:]
    if op != '∧':
        if L and L[-1][0] == 'D': L = L[:-1]
        if R and R[0][0] == 'D': R = R[1:]
    return (op, expr(L), expr(R))

# --- Lean output ---
SCAN_FIX = {"*1.4": r"\vdash \colon p \lor q.\supset.q \lor p"}   # Gutenberg body typo; 1910 scan reads q ∨ p
def lean(t):
    if isinstance(t, str): return t
    op, *a = t
    if op == "~": return f"(.neg {lean(a[0])})"
    f = {"∨": ".or", "⊃": "F.imp", "∧": "F.and", "≡": "F.iff"}[op]
    return f"({f} {lean(a[0])} {lean(a[1])})"
def vars_of(t): return {t} if isinstance(t, str) else set().union(*[vars_of(x) for x in t[1:]])
out, n, skipped = ["-- Generated by scripts/gen_lean.py from data/vol1.jsonl; do not edit.",
                   "import PM.Basic", "namespace PM", "open F", ""], 0, []
for line in open(root / "data/vol1.jsonl", encoding="utf-8"):
    r = json.loads(line)
    m = re.match(r"\*(\d+)\.(\d+)$", r["id"])
    if not m or not 1 <= int(m.group(1)) <= 5 or r.get("is_def"): continue
    src = SCAN_FIX.get(r["id"], r["statement"])
    if "vdash" not in src: skipped.append(r["id"] + "(rule)"); continue
    try: ast = parse(tokenize(src))
    except Exception: skipped.append(r["id"]); continue
    name = f"s{m.group(1)}_{m.group(2)}"
    vs = sorted(vars_of(ast))
    binders = " ".join(f"({v} : F)" for v in vs)
    app = " ".join(f'(.var "{v}")' for v in vs)
    out += [f"/-- {r['id']} -/", f"def {name} {binders} : F := {lean(ast)}", f"theorem check_{name}_tautology : ({name} {app}).isTaut = true := by decide", ""]
    n += 1
out.append("end PM")
open(root / "PM/Statements.lean", "w", encoding="utf-8").write("\n".join(out))
print("statements:", n, "skipped:", skipped)
