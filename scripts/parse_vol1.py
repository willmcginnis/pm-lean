#!/usr/bin/env python3
"""Parse Project Gutenberg eBook #78050 (PM Vol I, HTML edition) into proposition records: statement,
inline hint, Dem. lines with hints. Writes data/vol1.jsonl (one JSON record per numbered item).

Usage: python3 scripts/parse_vol1.py PATH/TO/pg78050-images.html [OUT]
The HTML is not in this repository; download it from
https://www.gutenberg.org/cache/epub/78050/pg78050-images.html (see scripts/README.md)."""
import re, html, json, collections, pathlib, sys

root = pathlib.Path(__file__).resolve().parent.parent
if len(sys.argv) not in (2, 3):
    sys.exit(__doc__)
SRC = sys.argv[1]
OUT = pathlib.Path(sys.argv[2]) if len(sys.argv) == 3 else root / "data/vol1.jsonl"
t = open(SRC, encoding="utf-8").read()
# Labels: PM's centred dot; 28 labels in #78050 use a full stop instead (e.g. *11.521., *64.01.), so accept both.
LABEL = re.compile(r'<p class="nind">\s*<b>(?:<a id="[^"]*">)?\*?(\d+)[·.](\d+)(?:</a>)?\s*\.?\s*</b>')
labels = list(LABEL.finditer(t))
PAGE = [(m.start(), int(m.group(1))) for m in re.finditer(r'id="Page_(\d+)"', t)]
def page_at(pos):
    p = None
    for s, n in PAGE:
        if s > pos: break
        p = n
    return p
def texs(seg): return [html.unescape(x) for x in re.findall(r'data-tex="([^"]*)"', seg)]
def strip_delims(s): return re.sub(r'^\s*\\[\(\[]\s*|\s*\\[\)\]]\s*$', '', s)
def inline_hint(stmt):
    m = re.search(r'\\quad\s*\\left\[(.*)\\right\]\s*$', stmt, re.S) or re.search(r'\\quad\s*\[(.*)\]\s*$', stmt, re.S)
    return (stmt[:m.start()].strip(), m.group(1).strip()) if m else (stmt, None)
def rows(tex):
    m = re.search(r'\\begin\s*\{array\}\{[^}]*\}(.*)\\end\s*\{array\}', tex, re.S)  # some are set `\begin {array}`
    if not m: return []
    out = []
    for r in [x.strip() for x in re.split(r'\\\\', m.group(1)) if x.strip()]:
        parts = r.split('&')
        hint, rest = (parts[0].strip(), '&'.join(parts[1:])) if len(parts) > 1 else ('', parts[0])
        lab = re.search(r'\\text\{\((\d+)\)\}', rest)
        rest = re.sub(r'\\qquad\s*\\text\{\(\d+\)\}', '', rest).replace('&', ' ').strip()
        if hint and not rest:  # the row's only `&` comes before its label: the first cell is the line itself
            hint, rest = '', hint
        out.append({"hint": hint, "formula": rest, "label": lab.group(1) if lab else None})
    return out
HINT = re.compile(r'\[.*\]|\\left\s*\[.*\\right\s*\]|\\text\{\[.*\]\}', re.S)
def display_rows(tex):
    """A Dem. set as align, align* or aligned, or as one displayed line. Their columns are placed for the eye,
    so cells are not split by position: a first cell in brackets is the hint, a last cell (n) the label, and
    the other cells joined are the formula."""
    body = strip_delims(tex)
    m = re.fullmatch(r'\\begin\{(align\*?|aligned)\}(.*)\\end\{\1\}', body, re.S)
    if not m and '\\begin' in body: return []
    out = []
    for r in re.split(r'\\\\', m.group(2)) if m else [body]:
        cells = [c.strip() for c in r.split('&') if c.strip()]
        if not cells: continue
        lab = re.fullmatch(r'(?:\\text\{)?\((\d+)\)\}?', cells[-1])
        if lab: cells.pop()
        hint = cells.pop(0) if len(cells) > 1 and HINT.fullmatch(cells[0]) else ''
        out.append({"hint": hint, "formula": re.sub(r'\s*\\quad$', '', ' '.join(cells)), "label": lab.group(1) if lab else None})
    return out
cands = collections.defaultdict(list)
for i, m in enumerate(labels):
    end = labels[i+1].start() if i+1 < len(labels) else len(t)
    seg = t[m.end():end]
    nxt_label = re.search(r'<b>(?:<a[^>]*>)?\*\d+[·.]\d+', seg)  # a few labels in the source use '.' for '·'
    seg = seg[:nxt_label.start()] if nxt_label else seg
    tx = texs(seg)
    if not tx: continue
    stmt, ih = inline_hint(strip_delims(tx[0]))
    has_dem = bool(re.search(r'<i>Dem\.</i>', seg))
    proof = [r for x in tx[1:] for r in rows(x)] if has_dem else []
    if has_dem and not proof:  # no array: read the display the Dem. opens with, if it opens with one
        after = texs(seg[seg.find('<i>Dem.</i>'):])
        proof = display_rows(after[0]) if after and after[0].lstrip().startswith('\\[') else []
    is_def = bool(re.search(r'\bDf\b', stmt)) or bool(re.search(r'\bDf\.?\s*</p>', seg[:600]))
    is_pp = bool(re.search(r'\bPp\b', seg[:800]))
    cands[f"*{m.group(1)}.{m.group(2)}"].append({
        "id": f"*{m.group(1)}.{m.group(2)}", "chapter": int(m.group(1)), "page": page_at(m.start()),
        "statement": stmt, "inline_hint": ih, "has_dem": has_dem, "is_def": is_def, "is_pp": is_pp,
        "proof": proof, "pos": m.start()})
recs = []
for k, cs in cands.items():
    best = max(cs, key=lambda c: (c["has_dem"] or bool(c["inline_hint"]) or c["is_def"] or c["is_pp"], c["pos"]))
    best["occurrences"] = len(cs); recs.append(best)
recs.sort(key=lambda r: (r["chapter"], r["pos"]))
with open(OUT, "w") as f:
    for r in recs: f.write(json.dumps(r, ensure_ascii=False) + "\n")
p = [r for r in recs if 1 <= r["chapter"] <= 5]
kind = collections.Counter("def" if r["is_def"] else "pp" if r["is_pp"] else "dem" if r["has_dem"] else "inline" if r["inline_hint"] else "bare" for r in p)
print("records", len(recs), "| ✱1–✱5:", len(p), dict(kind),
      "| proof lines", sum(len(r["proof"]) for r in p),
      "| dem w/o parsed lines", sum(1 for r in p if r["has_dem"] and not r["proof"]))
