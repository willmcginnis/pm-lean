#!/usr/bin/env python3
"""Draw the roadmap charts and write the roadmap's generated text, from data/roadmap.json.

Python 3 standard library only. Run from anywhere:

    python3 scripts/roadmap_chart.py            write docs/roadmap/*.svg and the generated
                                                regions of README.md and docs/ROADMAP.md
    python3 scripts/roadmap_chart.py --check    write nothing; exit 1 if any of those files
                                                differs from what the data gives
    python3 scripts/roadmap_chart.py --lists    print the README's nested lists
    python3 scripts/roadmap_chart.py --tables   print the per-subgroup tables

Charts:
  overview.svg       the four groups and the milestones
  group-<id>.svg     one per group: its subgroups and tasks
  deps.svg           every task, the hard dependencies (gates), and the places
                     where a task waits by choice

Every SVG carries its own light and dark colours (prefers-color-scheme).
Before writing, the script checks the data (ids, dependencies, cycles, "by
choice" placements, evidence levels of prior work, a source for every
measured entry, each source pinned to a full commit or a version, recorded
moves) and the
drawing: every text box is estimated and must not overlap another, must stay
inside its box and inside the image; each file is re-parsed as XML. Any
failure stops the script with a message.

Notes in the data may cite the repository's own counts instead of copying
them, so that they cannot drift: {progress:✱20} (proved of assertions, from
the tables of docs/PROGRESS.md; also a range such as {progress:✱9–✱14} or a
volume, {progress:Vol I}), {progress-commit}, {claims:B4} (a row's status in
docs/PM_CLAIMS.md), {claims-counts} (that page's Counts paragraph) and
{star9f} (numbered ✱9 propositions proved by ✱9's own method, from
data/star9f_ledger.json).
"""

import json
import os
import re
import sys
import xml.dom.minidom
from xml.sax.saxutils import escape

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATA = os.path.join(ROOT, "data", "roadmap.json")
OUTDIR = os.path.join(ROOT, "docs", "roadmap")
README = os.path.join(ROOT, "README.md")
ROADMAP = os.path.join(ROOT, "docs", "ROADMAP.md")

# Evidence levels of a prior-work entry, and what a search found it is good for.
EVIDENCE = {
    "measured": "measured",          # its source was inspected at a pinned commit, given in "source" (not built unless said)
    "documented": "documented",      # a paper or README says so ("cite" gives where, when recorded)
    "unverified": "unverified",      # reported, not checked
    "from memory": "from memory",    # listed before the search reached this task
}
GENERIC = {"A", "An", "The", "No", "Not", "Nothing", "Two"}
EFFECTS = ("reuse", "ideas", "check against", "nothing found", "not yet searched")

FONT = "system-ui, -apple-system, 'Segoe UI', Helvetica, Arial, sans-serif"

# Group colours: categorical slots 1-4 of a palette validated for colour-vision
# deficiency, stepped separately for the light and the dark surface. Group
# identity is also carried by names and position, never by colour alone.
LIGHT = {
    "bg": "#fcfcfb", "card": "#ffffff", "band": "#f3f3f0", "line": "#d6d5cf",
    "t1": "#0b0b0b", "t2": "#52514e", "t3": "#62615c", "edge": "#55544f",
    "choice": "#8a5a00", "groups": ["#2a78d6", "#eb6834", "#1baf7a", "#eda100"],
}
DARK = {
    "bg": "#1a1a19", "card": "#232322", "band": "#2b2b29", "line": "#45443f",
    "t1": "#ffffff", "t2": "#c3c2b7", "t3": "#b0afa5", "edge": "#b8b7ad",
    "choice": "#e3b04b", "groups": ["#3987e5", "#d95926", "#199e70", "#c98500"],
}


def css():
    def block(p):
        rules = [
            f".bg{{fill:{p['bg']}}}", f".card{{fill:{p['card']};stroke:{p['line']};stroke-width:1}}",
            f".band{{fill:{p['band']}}}", f".rule{{stroke:{p['line']};stroke-width:1}}",
            f".t1{{fill:{p['t1']}}}", f".t2{{fill:{p['t2']}}}", f".t3{{fill:{p['t3']}}}",
            f".st{{fill:{p['t2']};stroke:{p['t2']}}}", f".sto{{fill:none;stroke:{p['t2']};stroke-width:1.5}}",
            f".edge{{fill:none;stroke:{p['edge']};stroke-width:1.3}}",
            f".choice{{fill:none;stroke:{p['choice']};stroke-width:1.5;stroke-dasharray:5 3}}",
            f".ah{{fill:{p['edge']}}}", f".ahc{{fill:{p['choice']}}}",
            f".ms{{fill:{p['t1']}}}",
        ]
        for i, c in enumerate(p["groups"]):
            rules.append(f".g{i}{{fill:{c}}}")
            rules.append(f".gs{i}{{stroke:{c};stroke-width:2;fill:none}}")
        return "\n".join(rules)
    return (f"text{{font-family:{FONT}}}\n" + block(LIGHT) +
            "\n@media (prefers-color-scheme: dark) {\n" + block(DARK) + "\n}")


# ---------------------------------------------------------------- text metrics

def char_em(c):
    """A deliberately generous estimate of a character's advance, in em."""
    if c == " ":
        return 0.30
    if c in "il.,:;'|!·":
        return 0.30
    if c in "()[]{}fjrt-/":
        return 0.40
    if c in "mw":
        return 0.86
    if c in "MW":
        return 0.95
    if c.isascii() and c.isupper():
        return 0.72
    if c.isdigit():
        return 0.58
    if c.isascii():
        return 0.56
    if c in "₀₁₂⁰¹²":
        return 0.45
    if c in "–":
        return 0.6
    if c in "✱⟷⊢≡—→":
        return 1.0
    return 0.8


def text_w(s, size, bold=False):
    # Never narrower than 0.62 em (0.68 em bold) per character, so that the
    # layout also holds with wide fallback fonts such as DejaVu Sans.
    floor = 0.68 if bold else 0.62
    return sum(max(char_em(c) * (1.08 if bold else 1.0), floor) for c in s) * size


def wrap(s, maxw, size, bold=False):
    lines, cur = [], ""
    for w in s.split(" "):
        t = f"{cur} {w}" if cur else w
        if text_w(t, size, bold) <= maxw or not cur:
            cur = t
        else:
            lines.append(cur)
            cur = w
    if cur:
        lines.append(cur)
    return lines


class LayoutError(Exception):
    pass


class Canvas:
    """Collects SVG elements and an estimated box for every text."""

    def __init__(self, name, width, title, desc):
        self.name, self.w, self.title, self.desc = name, width, title, desc
        self.back, self.front, self.texts = [], [], []
        self.h = 0

    def add(self, s, back=False):
        (self.back if back else self.front).append(s)

    def rect(self, x, y, w, h, cls, rx=6, back=False):
        self.add(f'<rect x="{x:.1f}" y="{y:.1f}" width="{w:.1f}" height="{h:.1f}" rx="{rx}" class="{cls}"/>', back)

    def text(self, x, y, s, size, cls="t1", bold=False, anchor="start", inside=None):
        w = text_w(s, size, bold)
        x0 = x if anchor == "start" else (x - w / 2 if anchor == "middle" else x - w)
        self.texts.append({"box": (x0, y - 0.8 * size, x0 + w, y + 0.24 * size), "s": s, "inside": inside})
        weight = ' font-weight="700"' if bold else ""
        a = f' text-anchor="{anchor}"' if anchor != "start" else ""
        self.add(f'<text x="{x:.1f}" y="{y:.1f}" font-size="{size}"{weight}{a} class="{cls}">{escape(s)}</text>')
        return w

    def para(self, x, y, s, size, maxw, cls="t1", bold=False, inside=None, lh=1.32):
        """Wrapped text whose first baseline is y; returns the y below it."""
        lines = wrap(s, maxw, size, bold)
        for i, ln in enumerate(lines):
            self.text(x, y + i * size * lh, ln, size, cls, bold, inside=inside)
        return y + (len(lines) - 1) * size * lh + 0.24 * size

    def glyph(self, x0, y0, x1, y1, label):
        """Register a non-text mark that text must not overlap."""
        self.texts.append({"box": (x0, y0, x1, y1), "s": f"[{label}]", "inside": None})

    def status_mark(self, cx, cy, status, r=5):
        if status == "done":
            self.add(f'<circle cx="{cx:.1f}" cy="{cy:.1f}" r="{r}" class="st"/>')
        elif status == "in progress":
            self.add(f'<circle cx="{cx:.1f}" cy="{cy:.1f}" r="{r}" class="sto"/>')
            self.add(f'<path d="M{cx:.1f},{cy - r:.1f} A{r},{r} 0 0 0 {cx:.1f},{cy + r:.1f} Z" class="st"/>')
        else:
            self.add(f'<circle cx="{cx:.1f}" cy="{cy:.1f}" r="{r}" class="sto"/>')
        self.glyph(cx - r - 1, cy - r - 1, cx + r + 1, cy + r + 1, status)

    def check(self):
        errs = []
        for t in self.texts:
            x0, y0, x1, y1 = t["box"]
            if x0 < 0 or y0 < 0 or x1 > self.w or y1 > self.h:
                errs.append(f"outside the image: {t['s']!r}")
            if t["inside"]:
                bx0, by0, bx1, by1 = t["inside"]
                if x0 < bx0 or x1 > bx1 or y0 < by0 or y1 > by1:
                    errs.append(f"outside its box: {t['s']!r}")
        ts = sorted(self.texts, key=lambda t: t["box"][0])
        for i, a in enumerate(ts):
            ax0, ay0, ax1, ay1 = a["box"]
            for b in ts[i + 1:]:
                bx0, by0, bx1, by1 = b["box"]
                if bx0 >= ax1:
                    break
                if ay0 < by1 and by0 < ay1:
                    errs.append(f"overlap: {a['s']!r} and {b['s']!r}")
        if errs:
            raise LayoutError(f"{self.name}:\n  " + "\n  ".join(errs))

    def svg(self):
        h = round(self.h)
        defs = ('<defs>'
                '<marker id="ah" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" '
                'orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" class="ah"/></marker>'
                '<marker id="ahc" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" '
                'orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" class="ahc"/></marker>'
                '</defs>')
        return "\n".join([
            f'<svg xmlns="http://www.w3.org/2000/svg" width="{self.w}" height="{h}" '
            f'viewBox="0 0 {self.w} {h}" role="img" aria-labelledby="title desc">',
            f'<title id="title">{escape(self.title)}</title>',
            f'<desc id="desc">{escape(self.desc)}</desc>',
            f"<style>\n{css()}\n</style>", defs,
            f'<rect x="0" y="0" width="{self.w}" height="{h}" class="bg"/>',
            *self.back, *self.front, "</svg>", ""])


# ---------------------------------------------------------------- data

def read(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


def repo_facts():
    """The counts that notes may cite, read from the repository's own files."""
    prog = read(os.path.join(ROOT, "docs", "PROGRESS.md"))
    facts = {}
    m = re.search(r"from the files at commit `([0-9a-f]+)`", prog)
    facts["progress-commit"] = f"`{m.group(1)}`" if m else None
    for line in prog.splitlines():
        c = [x.strip() for x in line.strip().strip("|").split("|")]
        if len(c) == 7 and re.fullmatch(r"✱\d+", c[0]) and c[4].isdigit():      # a chapter
            facts[f"progress:{c[0]}"] = f"{c[4]} of {c[6]}"
        elif len(c) == 7 and re.fullmatch(r"✱\d+–✱\d+", c[0]) and c[2].isdigit():  # a range
            facts[f"progress:{c[0]}"] = f"{c[2]} of {c[4]}"
        elif len(c) == 6 and c[0].startswith("**Vol") and c[2].isdigit():
            vol = re.match(r"\*\*(Vol [IV]+)\*\*", c[0]).group(1)
            total = re.match(r"([\d,]+) assertions", c[4])
            if total:
                facts[f"progress:{vol}"] = f"{c[2]} of {total.group(1)}"
    claims = read(os.path.join(ROOT, "docs", "PM_CLAIMS.md"))
    for line in claims.splitlines():
        mm = re.match(r"\| ([A-F]\d+) \|", line)
        if mm:
            facts[f"claims:{mm.group(1)}"] = [x.strip() for x in line.split("|")][4]
    m = re.search(r"## Counts\n\n(.*?)\n\n", claims + "\n\n", re.S)
    facts["claims-counts"] = " ".join(re.sub(r"\s*\(`tests/[^)]*\)", "", m.group(1)).split()) if m else None
    rows = json.loads(read(os.path.join(ROOT, "data", "star9f_ledger.json")))
    star9 = [r for r in rows if r["category"] == "assertion" and r["id"].startswith("*9.")]
    facts["star9f"] = f"{sum(r['method'] != 'open' for r in star9)} of {len(star9)}"
    return facts


def fill(s, facts, where):
    def sub(m):
        v = facts.get(m.group(1))
        if v is None:
            raise SystemExit(f"roadmap.json, {where}: {{{m.group(1)}}} is not found in the repository's files")
        return v
    return re.sub(r"\{([a-z0-9-]+(?::[^{}]+)?)\}", sub, s)


def fill_all(obj, facts, where="data"):
    if isinstance(obj, str):
        return fill(obj, facts, where)
    if isinstance(obj, list):
        return [fill_all(x, facts, where) for x in obj]
    if isinstance(obj, dict):
        return {k: (v if k == "id" else fill_all(v, facts, f"{where}/{obj.get('id', k)}")) for k, v in obj.items()}
    return obj


def load(path=DATA):
    d = fill_all(json.loads(read(path)), repo_facts())
    leaves, owner = {}, {}
    for gi, g in enumerate(d["groups"]):
        for sg in g["subgroups"]:
            for lf in sg["leaves"]:
                if lf["id"] in leaves:
                    raise SystemExit(f"duplicate leaf id {lf['id']}")
                leaves[lf["id"]] = lf
                owner[lf["id"]] = (gi, g, sg)
    validate(d, leaves)
    return d, leaves, owner


def validate(d, leaves):
    errs = []
    for lid, lf in leaves.items():
        for k in ("name", "short", "size", "size_reason", "status", "hard_deps", "soft_deps", "order", "prior_work"):
            if k not in lf:
                errs.append(f"{lid}: missing {k}")
        if lf.get("size") not in ("S", "M", "L"):
            errs.append(f"{lid}: size")
        if lf.get("status") not in ("done", "in progress", "not started"):
            errs.append(f"{lid}: status")
        for k in ("hard_deps", "soft_deps", "placed_after"):
            for dep in lf.get(k, []):
                if dep not in leaves:
                    errs.append(f"{lid}: unknown {k} {dep}")
        if lf.get("order") == "by choice":
            if not lf.get("placed_after") or not lf.get("order_reason"):
                errs.append(f"{lid}: 'by choice' needs placed_after and order_reason")
        elif lf.get("order") == "by dependency":
            if lf.get("placed_after"):
                errs.append(f"{lid}: placed_after on a 'by dependency' leaf")
        else:
            errs.append(f"{lid}: order")
        pw = lf.get("prior_work", {})
        for e in pw.get("effect", []):
            if e not in EFFECTS:
                errs.append(f"{lid}: prior-work effect {e!r}")
        if not pw.get("effect"):
            errs.append(f"{lid}: prior work has no effect")
        for kn in pw.get("known", []):
            what = f"{lid}: prior work {kn.get('work', '')[:40]!r}"
            if kn.get("evidence") not in EVIDENCE:
                errs.append(f"{what} has no evidence level")
            if kn.get("evidence") == "measured" and not kn.get("source"):
                errs.append(f"{what} is measured but names no source (repository, commit, file)")
            for ref in kn.get("source", []):
                if ref.get("in") not in d.get("sources", {}) or not ref.get("path"):
                    errs.append(f"{what}: a source needs 'in' (a key of 'sources') and 'path'")
        mv = lf.get("moved")
        if mv is not None and not (mv.get("from") and mv.get("why")):
            errs.append(f"{lid}: a move needs 'from' and 'why'")
    for key, r in d.get("sources", {}).items():
        if not r.get("url", "").startswith("https://") or not r.get("name"):
            errs.append(f"source {key}: needs 'name' and an https 'url'")
        if not (re.fullmatch(r"[0-9a-f]{40}", r.get("commit", "")) and r.get("date")) and not r.get("version"):
            errs.append(f"source {key}: needs a full 40-hex 'commit' with its 'date', or a 'version'")
    for m in d["milestones"]:
        for r in m["reached_by"]:
            if r not in leaves:
                errs.append(f"milestone {m['id']}: unknown leaf {r}")
    # cycles, over hard dependencies and over hard + choice edges together
    for kinds in (("hard_deps",), ("hard_deps", "placed_after")):
        state = {}

        def visit(n, stack):
            if state.get(n) == 1:
                errs.append(f"cycle through {' -> '.join(stack + [n])} ({'+'.join(kinds)})")
                return
            if state.get(n) == 2:
                return
            state[n] = 1
            for k in kinds:
                for m in leaves[n].get(k, []):
                    if m in leaves:
                        visit(m, stack + [n])
            state[n] = 2
        for n in leaves:
            visit(n, [])
    # "by choice" must really be later than the dependencies require
    for lid, lf in leaves.items():
        anc = ancestors(leaves, lid)
        for p in lf.get("placed_after", []):
            if p in anc:
                errs.append(f"{lid}: placed_after {p} is already a hard dependency")
    if errs:
        raise SystemExit("roadmap.json:\n  " + "\n  ".join(errs))


def ancestors(leaves, lid):
    seen, todo = set(), list(leaves[lid]["hard_deps"])
    while todo:
        n = todo.pop()
        if n not in seen:
            seen.add(n)
            todo.extend(leaves[n]["hard_deps"])
    return seen


def levels(leaves):
    lv = {}

    def f(n):
        if n not in lv:
            lv[n] = 1 + max((f(m) for m in leaves[n]["hard_deps"]), default=-1)
        return lv[n]
    for n in leaves:
        f(n)
    return lv


def counts(items):
    c = {"done": 0, "in progress": 0, "not started": 0}
    for lf in items:
        c[lf["status"]] += 1
    return c


def all_leaves(g):
    return [lf for sg in g["subgroups"] for lf in sg["leaves"]]


def status_row(cv, x, y, c, size=12.5, inside=None):
    """Draw '● 1 done   ◐ 4 in progress   ○ 7 not started' starting at x; baseline y."""
    for st in ("done", "in progress", "not started"):
        cv.status_mark(x + 5, y - 0.33 * size, st)
        x += 14
        x += cv.text(x, y, f"{c[st]} {st}", size, "t2", inside=inside) + 16
    return x


# ---------------------------------------------------------------- overview

def overview(d, leaves, owner, W=900):
    M = 24
    cv = Canvas("overview.svg", W, "Roadmap overview",
                "The four groups of work, with their status, and the five milestones.")
    y = 42
    cv.text(M, y, "Roadmap", 24, bold=True)
    y = cv.para(M, y + 26, "Four groups of work run side by side. Each is split into subgroups and "
                "chapter-sized or stage-sized tasks; every task starts with a search for prior work.",
                14, W - 2 * M, "t2") + 20
    colw, gap = (W - 2 * M - 16) / 2, 16
    groups = d["groups"]
    for row in range(2):
        cards = []
        for col in range(2):
            gi = row * 2 + col
            g = groups[gi]
            x = M + col * (colw + gap)
            cards.append((gi, g, x))
        # measure heights first
        hs = []
        for gi, g, x in cards:
            hs.append(card_height(g, colw))
        h = max(hs)
        for gi, g, x in cards:
            box = (x, y, x + colw, y + h)
            cv.rect(x, y, colw, h, "card", back=True)
            cv.rect(x, y, 6, h, f"g{gi}", rx=2, back=True)
            tx, maxw = x + 20, colw - 34
            yy = y + 30
            cv.text(tx, yy, f"{gi + 1}  {g['name']}", 18, bold=True, inside=box)
            yy = cv.para(tx, yy + 24, g["description"], 13.5, maxw, "t2", inside=box) + 12
            subs = " · ".join(sg["name"] for sg in g["subgroups"])
            yy = cv.para(tx, yy + 13, subs, 13, maxw, "t1", inside=box) + 14
            status_row(cv, tx, yy + 13, counts(all_leaves(g)), 12.5, inside=box)
        y += h + gap
    # milestones
    y += 18
    cv.text(M, y, "Milestones", 18, bold=True)
    y = cv.para(M, y + 22, "Each is named by what is true when it is reached. They are not walls between "
                "phases: the gates are dependencies between individual tasks, shown in the dependency view.",
                13, W - 2 * M, "t2") + 30
    ms = d["milestones"]
    n = len(ms)
    cw = (W - 2 * M) / n
    line_y = y
    cv.add(f'<line x1="{M}" y1="{line_y}" x2="{W - M}" y2="{line_y}" class="rule"/>', back=True)
    bottom = y
    for i, m in enumerate(ms):
        cx = M + cw * i + cw / 2
        r = 9
        cv.add(f'<path d="M{cx:.1f},{line_y - r} L{cx + r:.1f},{line_y} L{cx:.1f},{line_y + r} '
               f'L{cx - r:.1f},{line_y} Z" class="ms"/>')
        cv.glyph(cx - r, line_y - r, cx + r, line_y + r, "milestone")
        tx, maxw = M + cw * i + 6, cw - 14
        yy = cv.para(tx, line_y + 34, m["name"], 14.5, maxw, "t1", bold=True)
        yy = cv.para(tx, yy + 17, m["short"], 12.5, maxw, "t2")
        gis = sorted({owner[r_][0] for r_ in m["reached_by"]})
        label = ("work in groups " + ", ".join(str(g + 1) for g in gis) if len(gis) > 1
                 else f"work in group {gis[0] + 1}")
        yy = cv.para(tx, yy + 17, label, 12, maxw, "t3")
        bottom = max(bottom, yy)
    cv.h = bottom + 26
    return cv


def card_height(g, colw):
    maxw = colw - 34
    h = 30
    h += 24 + (len(wrap(g["description"], maxw, 13.5)) - 1) * 13.5 * 1.32 + 0.24 * 13.5 + 12
    subs = " · ".join(sg["name"] for sg in g["subgroups"])
    h += 13 + (len(wrap(subs, maxw, 13)) - 1) * 13 * 1.32 + 0.24 * 13 + 14
    h += 13 + 18
    return h


# ---------------------------------------------------------------- one group

def leaf_lines(lf, leaves, maxw):
    """The content of a leaf box, as (text, size, cls, bold, gap_before)."""
    out = [(ln, 13, "t1", True) for ln in wrap(lf["name"], maxw, 13, True)]
    meta = f"{lf['status']} · size {lf['size']}"
    out.append(("META", meta))
    if lf["hard_deps"]:
        s = "needs: " + ", ".join(leaves[x]["short"] for x in lf["hard_deps"])
    elif lf["status"] == "done":
        s = None
    else:
        s = "needs: nothing; can start now" if lf["status"] == "not started" else "needs: nothing"
    if s:
        out += [(ln, 12, "t2", False) for ln in wrap(s, maxw, 12)]
    if lf["order"] == "by choice":
        s = "later by choice: after " + ", ".join(leaves[x]["short"] for x in lf["placed_after"])
        out += [(ln, 12, "t2", False) for ln in wrap(s, maxw, 12)]
    return out


def lines_height(lines):
    h = 0
    for ln in lines:
        if ln[0] == "META":
            h += 21
        else:
            h += ln[1] * 1.36
    return h


def group_chart(d, leaves, gi, g, W=900):
    M, gap, ncol = 24, 12, 3
    cv = Canvas(f"group-{g['id']}.svg", W, f"Group {gi + 1}: {g['name']}",
                f"The subgroups and tasks of the group {g['name']}, with status, size, "
                "hard dependencies and placements by choice.")
    y = 30
    cv.text(M, y, f"Group {gi + 1} of {len(d['groups'])}", 12.5, "t3")
    cv.text(M + 16, y + 30, g["name"], 22, bold=True)
    cv.rect(M, y + 12, 6, 24, f"g{gi}", rx=2)
    y = cv.para(M, y + 56, g["description"], 13.5, W - 2 * M, "t2") + 22
    # legend
    x = M
    for st in ("done", "in progress", "not started"):
        cv.status_mark(x + 5, y - 4.5, st)
        x += 14
        x += cv.text(x, y, st, 12, "t2") + 18
    cv.text(x, y, "S, M, L: weeks, months, longer", 12, "t2")
    y = cv.para(M, y + 26, "needs: the tasks whose results this one requires (its gates). Later by choice: "
                "placed after other work by the maintainer's priorities, not because it must wait.",
                12, W - 2 * M, "t3") + 22
    bw = (W - 2 * M - 12 - (ncol - 1) * gap) / ncol
    pad = 12
    for sg in g["subgroups"]:
        top = y
        content = []
        yy = top + 40
        for i in range(0, len(sg["leaves"]), ncol):
            row = sg["leaves"][i:i + ncol]
            ls = [leaf_lines(lf, leaves, bw - 2 * pad) for lf in row]
            rh = max(lines_height(l) for l in ls) + 2 * pad + 2
            for k, (lf, l) in enumerate(zip(row, ls)):
                content.append((M + 6 + k * (bw + gap), yy, rh, lf, l))
            yy += rh + gap
        band_h = yy - top + 4
        cv.rect(M - 8, top, W - 2 * M + 16, band_h, "band", rx=8, back=True)
        cv.rect(M - 8, top, 5, band_h, f"g{gi}", rx=2, back=True)
        cv.text(M + 6, top + 23, sg["name"], 15, bold=True)
        for bx, by, rh, lf, l in content:
            draw_leaf(cv, bx, by, bw, rh, lf, l, pad)
        y = top + band_h + 16
    cv.h = y + 8
    return cv


def draw_leaf(cv, bx, by, bw, bh, lf, lines, pad):
    box = (bx, by, bx + bw, by + bh)
    cv.rect(bx, by, bw, bh, "card", back=True)
    yy = by + pad + 11
    for ln in lines:
        if ln[0] == "META":
            cv.status_mark(bx + pad + 5, yy - 1, lf["status"])
            cv.text(bx + pad + 16, yy + 3, ln[1], 12, "t2", inside=box)
            yy += 21
        else:
            text, size, cls, bold = ln
            cv.text(bx + pad, yy, text, size, cls, bold, inside=box)
            yy += size * 1.36
    if lines_height(lines) > bh - 2 * pad + 2:
        raise LayoutError(f"leaf box too small: {lf['id']}")


# ---------------------------------------------------------------- dependency view

def deps_chart(d, leaves, owner, colw=180):
    """The narrowest of the routings."""
    cands = [deps_routed(d, leaves, owner, colw, r, rl) for r in ("early", "late") for rl in (False, True)]
    return min(cands, key=lambda cv: cv.w)


def deps_routed(d, leaves, owner, colw, route, right_last):
    lv = levels(leaves)
    R = max(lv.values()) + 1
    G = len(d["groups"])
    M, labw, pad, fs, lane_sp = 20, 58, 8, 11.5, 4.5
    intro_w = 860
    col = {lid: owner[lid][0] for lid in leaves}
    cells = {}
    for gi, g in enumerate(d["groups"]):
        for lf in all_leaves(g):
            cells.setdefault((lv[lf["id"]], gi), []).append(lf)

    def box_lines(lf):
        return wrap(lf["name"], colw - 2 * pad - 14, fs, True)

    def box_h(lf):
        return len(box_lines(lf)) * fs * 1.3 + 2 * pad + 2

    # edges: (source, target, kind); an arrow points from a leaf to the leaf that waits for it
    edges = [(dep, lid, "hard") for lid, lf in leaves.items() for dep in lf["hard_deps"]]
    edges += [(p, lid, "choice") for lid, lf in leaves.items() for p in lf.get("placed_after", [])]

    def gutters(e):
        # right_last: edges into the last column from the left enter it from
        # its right side, which relieves the gutter in front of it.
        sc, tc = col[e[0]], col[e[1]]
        if right_last and tc == G - 1 and sc < tc:
            return sc + 1, G
        return (sc + 1 if tc >= sc else sc), (tc if tc >= sc else tc + 1)

    def gap_of(e):
        # Where an edge crosses between gutters: "early" in the gap above the
        # target's level, "late" in the gap below the source's level. Both are
        # drawn and the narrower picture is kept.
        a, r = lv[e[0]], lv[e[1]]
        return r if route == "early" or a + 1 >= R else a + 1

    # Edges run only in the vertical gutters between columns and in the
    # horizontal gaps above each level, never across a box. Lanes in a gap are
    # assigned first (by gutter numbers), which fixes every y; lanes in the
    # gutters are then assigned from exact y spans.
    rspans = {r: [] for r in range(R)}
    for e in edges:
        gs, gt = gutters(e)
        if gs != gt:
            rspans[gap_of(e)].append((e, min(gs, gt), max(gs, gt)))
    rlane, rcount = {}, {}
    for r, spans in rspans.items():
        lanes, rcount[r] = colour(spans)
        rlane.update(lanes)
    gap_h = {r: 16 + lane_sp * rcount[r] for r in range(R)}

    intro = ("Each task sits in its group's column, at the level of its longest chain of hard "
             "dependencies: level 0 needs nothing else. A solid arrow points from a task to one that "
             "needs it (a gate). A dashed arrow points from a task to one placed after it by choice.")
    y = 34 + 26 + (len(wrap(intro, intro_w, 13)) - 1) * 13 * 1.32 + 0.24 * 13 + 16
    legend_y = y
    head_y = y + 30
    y = head_y + 26
    rowy, ypos = {}, {}
    for r in range(R):
        y += gap_h[r]
        rowy[r] = y
        h = 0
        for gi in range(G):
            yy = y
            for lf in cells.get((r, gi), []):
                bh = box_h(lf)
                ypos[lf["id"]] = (yy, bh)
                yy += bh + 8
            h = max(h, yy - y - 8)
        y += h
    height = y + 24

    def ys(e):
        (sy, sh), (ty, th) = ypos[e[0]], ypos[e[1]]
        gs, gt = gutters(e)
        r = gap_of(e)
        yg = rowy[r] - gap_h[r] / 2 if gs == gt else rowy[r] - gap_h[r] + 8 + lane_sp * rlane[e]
        return sy + min(sh * 0.35, 14), yg, ty + max(th * 0.62, th - 14)

    gspans = {i: [] for i in range(G + 1)}
    m = 4  # vertical clearance between two edges sharing a lane
    for e in edges:
        gs, gt = gutters(e)
        y_out, yg, y_in = ys(e)
        if gs == gt:
            gspans[gs].append(((e, "v"), min(y_out, yg, y_in) - m, max(y_out, yg, y_in) + m))
        else:
            gspans[gs].append(((e, "s"), min(y_out, yg) - m, max(y_out, yg) + m))
            gspans[gt].append(((e, "t"), min(yg, y_in) - m, max(yg, y_in) + m))
    glane, gcount = {}, {}
    for i, spans in gspans.items():
        lanes, gcount[i] = colour(spans)
        glane.update(lanes)
    gx, colx = {}, {}
    x = M + labw
    for i in range(G + 1):
        gx[i] = x
        x += 14 + lane_sp * gcount[i]
        if i < G:
            colx[i] = x
            x += colw
    W = round(x + M)

    cv = Canvas("deps.svg", W, "Roadmap: dependency view",
                "Every task of the roadmap in its group's column, at the level of its longest chain of "
                "hard dependencies; solid arrows are hard dependencies (gates), dashed arrows are "
                "placements by choice.")
    cv.h = height
    cv.text(M, 34, "Dependency view", 22, bold=True)
    cv.para(M, 60, intro, 13, intro_w, "t2")
    y = legend_y
    lx = M
    cv.add(f'<line x1="{lx}" y1="{y - 4}" x2="{lx + 34}" y2="{y - 4}" class="edge" marker-end="url(#ah)"/>')
    cv.glyph(lx, y - 9, lx + 36, y + 1, "legend arrow")
    lx += 42
    lx += cv.text(lx, y, "hard dependency (gate)", 12, "t2") + 22
    cv.add(f'<line x1="{lx}" y1="{y - 4}" x2="{lx + 34}" y2="{y - 4}" class="choice" marker-end="url(#ahc)"/>')
    cv.glyph(lx, y - 9, lx + 36, y + 1, "legend arrow")
    lx += 42
    lx += cv.text(lx, y, "placed later by choice", 12, "t2") + 22
    for st in ("done", "in progress", "not started"):
        cv.status_mark(lx + 5, y - 4.5, st)
        lx += 14
        lx += cv.text(lx, y, st, 12, "t2") + 16
    for gi, g in enumerate(d["groups"]):
        cv.rect(colx[gi], head_y - 16, colw, 5, f"g{gi}", rx=2)
        cv.para(colx[gi], head_y + 6, f"{gi + 1}  {g['name']}", 14, colw, "t1", bold=True)
    for r in range(R):
        ry = rowy[r] - gap_h[r] / 2
        cv.add(f'<line x1="{M}" y1="{ry:.1f}" x2="{W - M}" y2="{ry:.1f}" class="rule" stroke-dasharray="2 4"/>',
               back=True)
        cv.text(M, rowy[r] + 13, f"level {r}", 11.5, "t3")

    for e in edges:
        s, t, kind = e
        gs, gt = gutters(e)
        y_out, yg, y_in = ys(e)
        if gs == gt:
            xs = xt = gx[gs] + 7 + lane_sp * glane[(e, "v")]
        else:
            xs = gx[gs] + 7 + lane_sp * glane[(e, "s")]
            xt = gx[gt] + 7 + lane_sp * glane[(e, "t")]
        x_out = colx[col[s]] + colw if gs == col[s] + 1 else colx[col[s]]
        x_in = colx[col[t]] if gt == col[t] else colx[col[t]] + colw
        pts = [(x_out, y_out), (xs, y_out), (xs, yg), (xt, yg), (xt, y_in), (x_in, y_in)]
        dpath = "M" + " L".join(f"{px:.1f},{py:.1f}" for px, py in dedupe(pts))
        cls, mk = ("edge", "ah") if kind == "hard" else ("choice", "ahc")
        cv.add(f'<path d="{dpath}" class="{cls}" marker-end="url(#{mk})"/>', back=True)

    for lid, (by, bh) in ypos.items():
        lf = leaves[lid]
        bx = colx[col[lid]]
        box = (bx, by, bx + colw, by + bh)
        cv.rect(bx, by, colw, bh, "card")
        cv.rect(bx, by, 4, bh, f"g{col[lid]}", rx=2)
        cv.status_mark(bx + pad + 6, by + pad + 7, lf["status"], r=4.5)
        yy = by + pad + fs
        for ln in box_lines(lf):
            cv.text(bx + pad + 15, yy, ln, fs, "t1", True, inside=box)
            yy += fs * 1.3
    return cv


def colour(spans):
    """Interval colouring: give each (key, lo, hi) the lowest lane free of touching spans."""
    ends, out = [], {}
    for key, lo, hi in sorted(spans, key=lambda s: (s[1], s[2])):
        for k, end in enumerate(ends):
            if end < lo:
                ends[k] = hi
                out[key] = k
                break
        else:
            ends.append(hi)
            out[key] = len(ends) - 1
    return out, len(ends)


def dedupe(pts):
    out = [pts[0]]
    for p in pts[1:]:
        if abs(p[0] - out[-1][0]) > 0.05 or abs(p[1] - out[-1][1]) > 0.05:
            out.append(p)
    return out


# ---------------------------------------------------------------- main

def svg_text(cv):
    cv.check()
    s = cv.svg()
    xml.dom.minidom.parseString(s.encode("utf-8"))
    return s


def names(leaves, ids):
    return ", ".join(leaves[x]["short"] for x in ids) or "nothing"


def status_counts(c):
    return ", ".join(f"{c[st]} {st}" for st in ("done", "in progress", "not started") if c[st])


def leaf_status(lf):
    extra = ", later by choice" if lf["order"] == "by choice" else ""
    return f"*{lf['status']}{extra}*"


def md_lists(d, leaves, owner):
    """The README's nested lists, one block per group."""
    out = []
    for gi, g in enumerate(d["groups"]):
        out.append(f"<!-- group {gi + 1}: {g['name']} -->")
        for sg in g["subgroups"]:
            out.append(f"- **{sg['name']}**")
            for lf in sg["leaves"]:
                out.append(f"  - {lf['name']}: {leaf_status(lf)}")
        out.append("")
    return "\n".join(out)


def source_link(ref, sources):
    """A Markdown link to a file at the pinned commit (or to an item at its version), with its lines."""
    r = sources[ref["in"]]
    where = ref["path"] + (f":{ref['lines']}" if ref.get("lines") else "") + (f", {ref['at']}" if ref.get("at") else "")
    if "commit" in r:
        lines = ref.get("lines", "")
        anchor = "#L" + "-L".join(lines.split("-")) if lines else ""
        return f"[{r['name'].split('/')[-1]}@{r['commit'][:7]} {where}]({r['url']}/blob/{r['commit']}/{ref['path']}{anchor})"
    return f"[{r['name']}, {where}]({r['url']})"


def evidence(k, sources):
    s = f"*{EVIDENCE[k['evidence']]}*"
    if k.get("source"):
        s += ": " + ", ".join(source_link(ref, sources) for ref in k["source"])
    if k.get("cite"):
        s += f": {k['cite']}"
    return s


def md_prior_work(sg, sources):
    out = []
    for lf in sg["leaves"]:
        pw = lf["prior_work"]
        s = f"- **{lf['short']}** ({', '.join(pw['effect'])})."
        if pw.get("note"):
            s += f" {pw['note']}"
        if pw.get("known"):
            works = [k["work"] for k in pw["known"]]
            # inside the sentence, an entry that opens with a common word starts in lower case
            works = [w if i == 0 or w.split(" ")[0] not in GENERIC else w[0].lower() + w[1:]
                     for i, w in enumerate(works)]
            s += " " + "; ".join(f"{w} ({evidence(k, sources)})" for w, k in zip(works, pw["known"])) + "."
        out.append(s)
    return out


def md_sources(d):
    """The repositories and other items whose source was inspected, at the commit or version read."""
    rows = ["| Source | Commit or version | Commit date |", "|---|---|---|"]
    for r in sorted(d["sources"].values(), key=lambda r: r["name"].lower()):
        if "commit" in r:
            rows.append(f"| [{r['name']}]({r['url']}) | [`{r['commit']}`]({r['url']}/tree/{r['commit']}) | {r['date']} |")
        else:
            rows.append(f"| [{r['name']}]({r['url']}) | {r['version']} | |")
    return "\n".join(rows)


def md_evidence(leaves):
    c = {e: 0 for e in EVIDENCE}
    for lf in leaves.values():
        for k in lf["prior_work"].get("known", []):
            c[k["evidence"]] += 1
    parts = ", ".join(f"{n} *{EVIDENCE[e]}*" for e, n in c.items())
    return f"Of the {sum(c.values())} prior-work entries above: {parts}."


def md_tables(d, leaves, owner):
    """Per group: description, chart, and per subgroup a table of tasks and the prior work found."""
    out = []
    for gi, g in enumerate(d["groups"]):
        out += [f"### {gi + 1}. {g['name']}", "", g["description"], "",
                f"![Group {gi + 1}, {g['name']}: its subgroups and tasks](roadmap/group-{g['id']}.svg)", ""]
        for sg in g["subgroups"]:
            out += [f"#### {sg['name']}", "",
                    "| Task | Status | Size | Needs | Helped by | Order |", "|---|---|---|---|---|---|"]
            for lf in sg["leaves"]:
                order = lf["order"]
                if order == "by choice":
                    order = f"by choice, after {names(leaves, lf['placed_after'])}. {lf['order_reason']}"
                status = lf["status"]
                if lf.get("status_note"):
                    status = f"{status}. {lf['status_note']}"
                out.append(f"| {lf['name']} | {status} | {lf['size']}: {lf['size_reason']} | "
                           f"{names(leaves, lf['hard_deps'])} | {names(leaves, lf['soft_deps'])} | {order} |")
            out += ["", "Prior work:", ""] + md_prior_work(sg, d.get("sources", {})) + [""]
    return "\n".join(out).rstrip("\n")


def md_choice(d, leaves):
    rows = ["| Task | Placed after | Why |", "|---|---|---|"]
    for lf in leaves.values():
        if lf["order"] == "by choice":
            rows.append(f"| {lf['name']} | {names(leaves, lf['placed_after'])} | {lf['order_reason']} |")
    return "\n".join(rows)


def md_moves(d, leaves):
    rows = ["| Task | Before | Why it moved |", "|---|---|---|"]
    for lf in leaves.values():
        if lf.get("moved"):
            rows.append(f"| {lf['name']} | {lf['moved']['from']} | {lf['moved']['why']} |")
    return "\n".join(rows)


def md_now(d, leaves):
    """Every task under way, and every task whose gates are all done and that is not held back by choice."""
    out = []
    for g in d["groups"]:
        going = [lf["short"] for lf in all_leaves(g) if lf["status"] == "in progress"]
        ready = [lf["short"] for lf in all_leaves(g)
                 if lf["status"] == "not started" and lf["order"] == "by dependency"
                 and all(leaves[x]["status"] == "done" for x in lf["hard_deps"])]
        parts = []
        if going:
            parts.append("Under way: " + "; ".join(going) + ".")
        if ready:
            parts.append("Can start: " + "; ".join(ready) + ".")
        out.append(f"- **{g['name']}.** " + (" ".join(parts) if parts else "Nothing yet."))
    return "\n".join(out)


def md_milestones(d):
    rows = ["| Milestone | True when |", "|---|---|"]
    rows += [f"| {m['name']} | {m['true_when']} |" for m in d["milestones"]]
    return "\n".join(rows)


def md_established(d):
    return "\n".join(f"- {s}" for s in d["established"])


def md_readme(d, leaves, owner):
    out = [f"![{d['meta']['overview_alt']}](docs/roadmap/overview.svg)", "", d["meta"]["readme_intro"], ""]
    lists = md_lists(d, leaves, owner).split("\n")
    for gi, g in enumerate(d["groups"]):
        start = lists.index(f"<!-- group {gi + 1}: {g['name']} -->") + 1
        end = lists.index("", start)
        out += ["<details>",
                f"<summary><b>{gi + 1}. {g['name']}</b>: {g['tagline']} "
                f"({status_counts(counts(all_leaves(g)))})</summary>", "",
                f"![Group {gi + 1}, {g['name']}: its subgroups and tasks](docs/roadmap/group-{g['id']}.svg)", ""]
        out += lists[start:end] + ["", "</details>", ""]
    return "\n".join(out).rstrip("\n")


def splice(text, name, body, path):
    pat = re.compile(r"(<!-- generated:%s:start -->\n).*?(<!-- generated:%s:end -->)" % (name, name), re.S)
    if len(pat.findall(text)) != 1:
        raise SystemExit(f"{path}: expected one pair of <!-- generated:{name}:start/end --> markers")
    return pat.sub(lambda m: m.group(1) + body + "\n" + m.group(2), text)


def outputs(d, leaves, owner):
    """Every generated file, as {path: content}."""
    try:
        charts = [overview(d, leaves, owner)]
        charts += [group_chart(d, leaves, gi, g) for gi, g in enumerate(d["groups"])]
        charts.append(deps_chart(d, leaves, owner))
        files = {os.path.join(OUTDIR, cv.name): svg_text(cv) for cv in charts}
    except LayoutError as e:
        raise SystemExit(f"layout check failed: {e}")
    files[README] = splice(read(README), "roadmap", md_readme(d, leaves, owner), README)
    s = read(ROADMAP)
    for name, body in (("milestones", md_milestones(d)),
                       ("plan", md_tables(d, leaves, owner)), ("now", md_now(d, leaves)),
                       ("choice", md_choice(d, leaves)), ("moves", md_moves(d, leaves)),
                       ("established", md_established(d)), ("sources", md_sources(d)),
                       ("evidence", md_evidence(leaves))):
        s = splice(s, name, body, ROADMAP)
    files[ROADMAP] = s
    return files


def main():
    args = sys.argv[1:]
    d, leaves, owner = load()
    if args in (["--lists"], ["--tables"]):
        print(md_lists(d, leaves, owner) if args[0] == "--lists" else md_tables(d, leaves, owner))
        return
    if args not in ([], ["--check"]):
        raise SystemExit(__doc__)
    files = outputs(d, leaves, owner)
    if args == ["--check"]:
        stale = [p for p, s in files.items() if not os.path.exists(p) or read(p) != s]
        extra = [os.path.join(OUTDIR, f) for f in sorted(os.listdir(OUTDIR))
                 if f.endswith(".svg") and os.path.join(OUTDIR, f) not in files]
        for p in stale:
            print(f"out of date: {os.path.relpath(p, ROOT)}")
        for p in extra:
            print(f"not generated from the data: {os.path.relpath(p, ROOT)}")
        if stale or extra:
            raise SystemExit("run python3 scripts/roadmap_chart.py to regenerate")
        print(f"up to date: {len(files)} files")
        return
    os.makedirs(OUTDIR, exist_ok=True)
    for p, s in files.items():
        with open(p, "w", encoding="utf-8") as f:
            f.write(s)
        print(f"wrote {os.path.relpath(p, ROOT)}")


if __name__ == "__main__":
    main()
