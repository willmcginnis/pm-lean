#!/usr/bin/env python3
"""Export names for PM's numbered propositions (docs/NAMING.md): writes data/export_names.json and
checks it.

An export name is `PM.star<N>_<M>_<descriptor>[_reading_<word>]`: PM's number; then PM's own name for
the proposition, lowercased, when PM gives one (data/naming/pm_names.json); then a descriptor of the
statement, generated from its shape in the style of Mathlib's naming conventions from the words of
data/naming/vocabulary.json; then, for a statement of ✱9 by its own method, the reading it is stated
under (data/naming/readings.json). Results about PM's system rather than in it are `PM.meta_<words>`,
named by hand.

The statements come from Checks/ExportStatements.lean (run with `lake env lean`), which prints each
elaborated statement as a tree. The descriptor is read from the tree:
  - each connective gives its word, read left to right (`p ∨ ∼p` is `or_not`); variables give none;
  - an asserted implication A ⊃ B is named conclusion first, `B_of_A`, and each hypothesis H of the
    Lean statement adds `_of_H`, as in Mathlib;
  - an asserted equivalence A ≡ B is `A_iff_B`;
  - X op X is `op_self`; A ⊃ B or A ≡ B with B the operands of A swapped is `op_comm`; a variable on one
    side that is the left or right operand of the other side is `left` or `right`.
  A descriptor of more than 6 words is replaced by its shape (the connectives of the top two levels
  only), and the entry is marked `needs_human`. Every descriptor is reviewed by people before release.

Usage (from the repository root, after `lake build`):
  python3 scripts/export_names.py                    write data/export_names.json
  python3 scripts/export_names.py --check            exit 1 if it is not up to date or breaks a rule
  python3 scripts/export_names.py --tsv PATH [--chapters 1-5]   also write a review table
  python3 scripts/export_names.py --pm-names HTML    first rewrite data/naming/pm_names.json from
                                                     Project Gutenberg eBook #78050 (pg78050-images.html)
"""
import html
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "data" / "export_names.json"
LOCK = ROOT / "data" / "export_names.lock"
VOCAB = ROOT / "data" / "naming" / "vocabulary.json"
READINGS = ROOT / "data" / "naming" / "readings.json"
PM_NAMES = ROOT / "data" / "naming" / "pm_names.json"
MAX_WORDS = 6
WORKING_READING = "C"   # a ✱9 statement for every reading is exported under the working reading

# which declarations state PM's propositions, by module: (module, regex on the last name component)
SOURCES = [
    ("PM.Replay", r"PM\.t(\d+)_(\d+)"), ("PM.Replay2", r"PM\.t(\d+)_(\d+)"),
    *[(f"PM.Star{c}", r"PM\.q(\d+)_(\d+)") for c in (10, 11, 12, 13, 14, 20, 21)],
    ("PM.Found9.Star9", r"PM\.F9\.f(\d+)_(\d+)(?:_(?:russell|switch|prenex))?"),
]
# ✱1's primitive propositions are the constructors of `PM.Thm`
PRIMITIVES = {"PM.Thm.taut": "*1.2", "PM.Thm.add": "*1.3", "PM.Thm.perm": "*1.4",
              "PM.Thm.assoc": "*1.5", "PM.Thm.sum": "*1.6"}
# results about PM's system, named by hand: lean name -> (export name, PM number it concerns or None)
META = {"PM.sound": ("PM.meta_sound", None), "PM.complete": ("PM.meta_complete", None),
        "PM.star1_4_variant_not_a_theorem": ("PM.meta_perm_variant_not_thm", "*1.4")}

NAME_RE = re.compile(r"PM\.star(\d+)_(\d+)_([a-z][a-z0-9]*(?:_[a-z][a-z0-9]*)*)")
META_RE = re.compile(r"PM\.meta_([a-z][a-z0-9]*(?:_[a-z][a-z0-9]*)*)")


def load(p):
    return json.loads(p.read_text(encoding="utf-8"))


# ---------------------------------------------------------------- PM's names (from the Gutenberg text)

def pm_names_from_html(path):
    """PM's "Alphabetical list of propositions referred to by names" (Vol I front matter): one row per
    number; a ditto mark repeats the name above."""
    t = pathlib.Path(path).read_text(encoding="utf-8")
    i = t.index("REFERRED TO BY NAMES")
    rows, name = [], None
    for r in re.findall(r"<tr>(.*?)</tr>", t[i:t.index("</table>", i)], re.S):
        tds = [re.sub(r"<[^>]+>", "", x).strip() for x in re.findall(r"<td[^>]*>(.*?)</td>", r, re.S)]
        m = re.fullmatch(r"\*(\d+)·(\d+)\.", tds[1]) if len(tds) > 1 else None
        if not m:
            continue
        name = name if tds[0] in ('"', "”") else tds[0]
        tex = re.findall(r'data-tex="([^"]*)"', r)
        rows.append({"name": name, "number": f"*{m[1]}.{m[2]}", "printed": html.unescape(tex[0]) if tex else None})
    return rows


def write_pm_names(rows):
    doc = {"source": "Project Gutenberg eBook #78050 (Principia Mathematica, Vol. I), \"Alphabetical list "
                     "of propositions referred to by names\"; the formula is the transcription's TeX",
           "note": "PM gives one name to several numbers (Syll, Transp, Simp), so a name is never a key "
                   "on its own: the key is the number.",
           "names": rows}
    PM_NAMES.write_text(json.dumps(doc, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")


# ---------------------------------------------------------------- statements

def lean_statements():
    p = subprocess.run(["lake", "env", "lean", "Checks/ExportStatements.lean"], cwd=ROOT,
                       capture_output=True, text=True, timeout=3600)
    if p.returncode != 0:
        raise SystemExit(f"Checks/ExportStatements.lean failed:\n{p.stdout}{p.stderr}")
    return [json.loads(l) for l in p.stdout.splitlines() if l.startswith("{")]


def module_file(m):
    return m.replace(".", "/") + ".lean"


def mentions_reading(t):
    s = json.dumps(t)
    return '"v": "R"' in s or "PM.F9.Reading" in s or "PM.F9.Defs" in s or "PM.F9.Rule" in s


def reading_of(row, readings):
    """The reading tag a ✱9 statement is stated under, and how it was read."""
    s = json.dumps(row)
    by_lean = {r["lean"]: tag for tag, r in readings.items()}
    named = sorted({by_lean[c] for c in re.findall(r'"(PM\.F9\.Reading\.\w+)"', s) if c in by_lean})
    if named:
        assert len(named) == 1, (row["name"], named)
        return named[0], "statement"
    return WORKING_READING, "every reading (exported under the working reading)"


# ---------------------------------------------------------------- descriptors

class Words:
    def __init__(self, vocab):
        self.heads = vocab["lean_heads"]
        self.unknown = set()

    def head(self, t):
        if "c" in t:
            h = self.heads.get(t["c"])
            if h is None:
                self.unknown.add(t["c"])
                return {"form": "prefix", "words": ["unknown"]}, t["a"]
            return h, t["a"][h.get("skip", 0):]
        return None, None

    def is_atom(self, t):
        h, args = self.head(t)
        if h is None:
            return "lam" not in t or self.is_atom(t["lam"])
        if h["form"] == "atom":
            return True
        if h["form"] == "transparent":
            return self.is_atom(args[-1])
        return False

    def strip(self, t):
        """Look through transparent heads and functions."""
        while True:
            if "lam" in t:
                t = t["lam"]; continue
            h, args = self.head(t)
            if h is not None and h["form"] == "transparent":
                t = args[-1]; continue
            return t

    def binary(self, t):
        """(op word, left, right) if t is an infix connective."""
        t = self.strip(t)
        h, args = self.head(t)
        if h is not None and h["form"] == "infix" and len(args) == 2:
            return h["words"], self.strip(args[0]), self.strip(args[1])
        return None

    def words(self, t, depth=None):
        if depth == 0:
            return []
        d = None if depth is None else depth - 1
        t = self.strip(t)
        if self.is_atom(t):
            return []
        h, args = self.head(t)
        if h is None:
            return []
        f = h["form"]
        if f == "infix":
            a, b = self.strip(args[0]), self.strip(args[1])
            if a == b:
                return self.words(a, d) + h["words"] + ["self"]
            return self.words(a, d) + h["words"] + self.words(b, d)
        if f == "quant_infix":          # (x) . φx ⊃ ψx and the like: `all_imp`
            a, b = self.strip(args[0]), self.strip(args[1])
            return h["words"] + self.words(a, d) + h["op"] + self.words(b, d)
        # prefix, binder, fixed: the words, then those of the arguments
        out = list(h["words"])
        for x in args:
            out += self.words(x, d)
        return out

    def side(self, x, other, depth):
        """Words for one side of an asserted ⊃ or ≡; a variable that is an operand of the other side is
        `left` or `right`."""
        x = self.strip(x)
        if self.is_atom(x):
            b = self.binary(other)
            if b:
                _, l, r = b
                if x == l and x == r:
                    return []
                if x == l:
                    return ["left"]
                if x == r:
                    return ["right"]
            return []
        return self.words(x, depth)

    def top(self, c, depth=None):
        c = self.strip(c)
        h, args = self.head(c)
        if h is not None and h["form"] == "infix" and h["words"] in (["imp"], ["iff"]) and len(args) == 2:
            a, b = self.strip(args[0]), self.strip(args[1])
            if a == b:
                return h["words"] + ["self"]
            ba, bb = self.binary(a), self.binary(b)
            if ba and bb and ba[0] == bb[0] and ba[1] == bb[2] and ba[2] == bb[1] and ba[1] != ba[2]:
                return ba[0] + ["comm"]
            wa, wb = self.side(a, b, depth), self.side(b, a, depth)
            if h["words"] == ["imp"]:
                return wb + (["of"] + wa if wa else [])
            return wa + ["iff"] + wb
        return self.words(c, depth)

    def descriptor(self, concl, hyps):
        """(words, needs_human)."""
        for depth in (None, 2, 1):
            w = self.top(concl, depth)
            for hy in hyps:
                hw = self.top(hy, depth)
                if hw:
                    w += ["of"] + hw
            if not w:
                w = ["prop"]
            if len(w) <= MAX_WORDS:
                return w, depth is not None or "unknown" in w or w == ["prop"]
        return w[:MAX_WORDS], True


# ---------------------------------------------------------------- entries

def build(rows, vocab, readings, pm_names):
    names_by_num = {}
    for r in pm_names["names"]:
        names_by_num.setdefault(r["number"], []).append(r["name"])
    W = Words(vocab)
    out = []

    def entry(row, pm, reading=None, how=None):
        hyps = [h for h in row["hyps"] if not mentions_reading(h)] if reading else row["hyps"]
        desc, human = W.descriptor(row["concl"], hyps)
        c, d = pm[1:].split(".")
        pmn = names_by_num.get(pm, [])
        assert len(pmn) <= 1, (pm, pmn)
        pmn = pmn[0] if pmn else None
        word = readings[reading]["word"] if reading else None
        name = f"PM.star{c}_{d}_" + "_".join(([pmn.lower()] if pmn else []) + desc) + \
               (f"_reading_{word}" if word else "")
        e = {"export": name, "slug": name.replace(".", "_"), "lean": row["name"], "pm": pm,
             "pm_name": pmn, "descriptor": "_".join(desc), "reading": word, "needs_human": human,
             "source": module_file(row["module"])}
        if reading:
            e["reading_from"] = how
        out.append(e)

    by_name = {r["name"]: r for r in rows}
    for lean, pm in PRIMITIVES.items():
        entry(by_name[lean], pm)
    for row in rows:
        for mod, rx in SOURCES:
            if row["module"] != mod:
                continue
            m = re.fullmatch(rx, row["name"])
            if not m:
                continue
            pm = f"*{m[1]}.{m[2]}"
            if mod == "PM.Found9.Star9":
                tag, how = reading_of(row, readings)
                entry(row, pm, tag, how)
            else:
                entry(row, pm)
    for lean, (name, pm) in META.items():
        row = by_name[lean]
        out.append({"export": name, "slug": name.replace(".", "_"), "lean": lean, "pm": pm,
                    "pm_name": None, "descriptor": name.split(".", 1)[1], "reading": None,
                    "needs_human": True, "source": module_file(row["module"]), "meta": True})
    out.sort(key=lambda e: (e.get("meta", False),
                            int(e["pm"][1:].split(".")[0]) if e["pm"] else 0,
                            [int(ch) for ch in e["pm"][1:].split(".")[1]] if e["pm"] else [], e["export"]))
    return out, sorted(W.unknown)


# ---------------------------------------------------------------- checks

def vocabulary_words(vocab):
    return set(vocab["words"])


def check_pattern(entries, ctx):
    bad = []
    for e in entries:
        n = e["export"]
        if not n.isascii():
            bad.append(f"{n}: not ASCII"); continue
        if e.get("meta"):
            if not META_RE.fullmatch(n):
                bad.append(f"{n}: not PM.meta_<words>")
            continue
        m = NAME_RE.fullmatch(n)
        if not m:
            bad.append(f"{n}: not PM.star<N>_<M>_<descriptor>"); continue
        if f"*{m[1]}.{m[2]}" != e["pm"]:
            bad.append(f"{n}: number does not match {e['pm']}")
    return bad


def check_unique_name(entries, ctx):
    seen, bad = set(), []
    for e in entries:
        if e["export"] in seen:
            bad.append(f"{e['export']}: used twice")
        seen.add(e["export"])
    return bad


def check_unique_slug(entries, ctx):
    seen, bad = {}, []
    for e in entries:
        s = e["export"].replace(".", "_")
        if e.get("slug") != s:
            bad.append(f"{e['export']}: slug {e.get('slug')} is not {s}")
        if s in seen:
            bad.append(f"{e['export']}: slug {s} also {seen[s]}")
        seen[s] = e["export"]
    return bad


VERSION_RE = re.compile(r"_v([2-9]|[1-9][0-9]+)$")   # a statement superseded: name_vN (docs/VERSIONING.md)


def descriptor_words(e):
    """The words of an export name after the number, without the reading and version suffixes."""
    n = VERSION_RE.sub("", e["export"])
    if e.get("meta"):
        return n.split(".", 1)[1].split("_")
    m = NAME_RE.fullmatch(n)
    if not m:
        return []
    rest = m[3]
    if "_reading_" in "_" + rest:
        rest = ("_" + rest).rsplit("_reading_", 1)[0][1:]
    return rest.split("_") if rest else []


def check_vocabulary(entries, ctx):
    words = vocabulary_words(ctx["vocab"])
    bad = []
    for e in entries:
        out = [w for w in descriptor_words(e) if w not in words]
        if out:
            bad.append(f"{e['export']}: not in the vocabulary: {', '.join(out)}")
    return bad


def check_pm_name_first(entries, ctx):
    names = {}
    for r in ctx["pm_names"]["names"]:
        names.setdefault(r["number"], set()).add(r["name"])
    bad = []
    for e in entries:
        if e.get("meta"):
            continue
        given = names.get(e["pm"], set())
        w = descriptor_words(e)
        if given:
            if e["pm_name"] not in given or not w or w[0] != e["pm_name"].lower():
                bad.append(f"{e['export']}: PM names {e['pm']} {'/'.join(sorted(given))}; the name must "
                           "come first")
        elif e["pm_name"] is not None:
            bad.append(f"{e['export']}: PM gives {e['pm']} no name, but pm_name is {e['pm_name']}")
    return bad


def check_readings(entries, ctx):
    words = {r["word"] for r in ctx["readings"].values()}
    bad = []
    for e in entries:
        n = VERSION_RE.sub("", e["export"])
        k = n.count("reading")
        suffix = re.search(r"_reading_([a-z0-9]+)$", n)
        if k > (1 if suffix else 0):
            bad.append(f"{n}: 'reading' only as the suffix _reading_<word>")
        if suffix and suffix[1] not in words:
            bad.append(f"{n}: reading {suffix[1]} is not in data/naming/readings.json")
        if (suffix[1] if suffix else None) != e["reading"]:
            bad.append(f"{n}: suffix does not match reading {e['reading']}")
    return bad


def check_no_top_level(entries, ctx):
    return [f"{e['export']}: a name must be under PM., never top-level PM_"
            for e in entries if not e["export"].startswith("PM.") or e["export"].startswith("PM_")]


def check_frozen(entries, ctx):
    have = {e["export"] for e in entries}
    return [f"{n}: in data/export_names.lock but missing (released names never change)"
            for n in ctx["lock"] if n not in have]


CHECKS = {"pattern": check_pattern, "unique_name": check_unique_name, "unique_slug": check_unique_slug,
          "vocabulary": check_vocabulary, "pm_name_first": check_pm_name_first,
          "readings": check_readings, "no_top_level": check_no_top_level, "frozen": check_frozen}


def read_lock(path=LOCK):
    if not path.exists():
        return []
    return [l.strip() for l in path.read_text(encoding="utf-8").splitlines()
            if l.strip() and not l.lstrip().startswith("#")]


def context():
    return {"vocab": load(VOCAB), "readings": load(READINGS), "pm_names": load(PM_NAMES), "lock": read_lock()}


def check(entries, ctx, skip=()):
    """{check name: [problems]} for the checks not skipped."""
    return {k: f(entries, ctx) for k, f in CHECKS.items() if k not in skip}


# ---------------------------------------------------------------- main

def chapter_counts(entries):
    out = {}
    for e in entries:
        c = "meta" if e.get("meta") else int(e["pm"][1:].split(".")[0])
        n = out.setdefault(c, [0, 0])
        n[0] += 1
        n[1] += e["needs_human"]
    return out


def write_tsv(entries, path, chapters=None):
    lo, hi = chapters or (0, 10 ** 6)
    sel = [e for e in entries
           if (e.get("meta") and lo <= 1 <= hi) or (e["pm"] and lo <= int(e["pm"][1:].split(".")[0]) <= hi
                                                    and not e.get("meta"))]
    cols = ["pm", "pm_name", "lean", "export", "descriptor", "reading", "needs_human", "source"]
    lines = ["\t".join(cols)] + ["\t".join("" if e.get(k) is None else str(e.get(k)) for k in cols) for e in sel]
    pathlib.Path(path).write_text("\n".join(lines) + "\n", encoding="utf-8")
    return len(sel)


def main(args):
    if "--pm-names" in args:
        write_pm_names(pm_names_from_html(args[args.index("--pm-names") + 1]))
    ctx = context()
    entries, unknown = build(lean_statements(), ctx["vocab"], ctx["readings"], ctx["pm_names"])
    text = json.dumps(entries, ensure_ascii=False, indent=1) + "\n"
    failed = False
    if "--check" in args:
        if not OUT.exists() or OUT.read_text(encoding="utf-8") != text:
            print("data/export_names.json is not up to date: run python3 scripts/export_names.py")
            failed = True
        checked = json.loads(OUT.read_text(encoding="utf-8")) if OUT.exists() else []
    else:
        OUT.write_text(text, encoding="utf-8")
        checked = entries
    problems = check(checked, ctx)
    problems["heads"] = [f"no word for {c} in data/naming/vocabulary.json" for c in unknown]
    for k, v in problems.items():
        for p in v:
            print(f"{k}: {p}")
        failed |= bool(v)
    if "--tsv" in args:
        ch = None
        if "--chapters" in args:
            a, b = args[args.index("--chapters") + 1].split("-")
            ch = (int(a), int(b))
        n = write_tsv(entries, args[args.index("--tsv") + 1], ch)
        print(f"wrote {n} rows")
    counts = chapter_counts(entries)
    print(f"export names: {len(entries)} entries, {sum(e['needs_human'] for e in entries)} need a person; "
          + "; ".join(f"{'✱' + str(c) if c != 'meta' else 'meta'} {n[1]}/{n[0]}" for c, n in counts.items()))
    print("checks: " + ", ".join(f"{k} {'ok' if not v else 'FAILED'}" for k, v in problems.items()))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
