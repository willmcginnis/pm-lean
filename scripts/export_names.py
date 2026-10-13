#!/usr/bin/env python3
"""Export names for PM's numbered propositions (docs/NAMING.md): writes data/export_names.json and
checks it.

An export name is `PM.star<N>_<M>[_<pmname>][_df|_rule][_reading_<word>][_v<N>]`: PM's number; PM's own
name for the item, lowercased, when PM gives one (data/naming/pm_names.json); `_df` for a definition and
`_rule` for an inference rule (data/naming/slots.json); for a statement of ✱9 by its own method, the
reading it is stated under (data/naming/readings.json); and, last, `_v<N>` for a superseded statement's
replacement (docs/VERSIONING.md). Nothing else: no descriptor of the statement and no Mathlib word.
Results about PM's system rather than in it are `PM.meta_<words>`, named by hand.

Each entry also has, outside the name:
  - a descriptor of the statement, generated from its shape in the style of Mathlib's naming conventions
    from the words of data/naming/vocabulary.json, for titles and search (docs/NAMING.md);
  - the digests that bind a released name to its meaning: `statement_digest`, of the elaborated
    statement, and `definitions_digest`, of the definitions under `PM` it uses (docs/VERSIONING.md).
Exact Lean and Mathlib counterparts of ✱1–✱5 are in data/naming/counterparts.json, also not in names.

The statements come from Checks/ExportStatements.lean (run with `lake env lean`), which prints each
elaborated statement as a tree and in a canonical text. The descriptor is read from the tree:
  - each connective gives its word, read left to right (`p ∨ ∼p` is `or_not`); variables give none;
  - an asserted implication A ⊃ B is named conclusion first, `B_of_A`, and each hypothesis H of the
    Lean statement adds `_of_H`, as in Mathlib;
  - an asserted equivalence A ≡ B is `A_iff_B`;
  - X op X is `op_self`; A ⊃ B or A ≡ B with B the operands of A swapped is `op_comm`; a variable on one
    side that is the left or right operand of the other side is `left` or `right`.
  A descriptor of more than 6 words is replaced by its shape (the connectives of the top two levels
  only), and the entry is marked `descriptor_needs_human`.

A released name keeps its spelling whatever the generator would now produce: an entry whose Lean
declaration is in data/export_names.lock takes the locked name and reading, and a row of data/changes.tsv
whose `old` is that name gives the name it is superseded by.

Usage (from the repository root, after `lake build`):
  python3 scripts/export_names.py                    write data/export_names.json
  python3 scripts/export_names.py --check            exit 1 if it is not up to date or breaks a rule
  python3 scripts/export_names.py --tsv PATH [--chapters 1-5]   also write a review table
  python3 scripts/export_names.py --write-lock       at a release: lock every name and reading meaning
  python3 scripts/export_names.py --verify-counterparts DIR    check each counterpart's file:line in
                                                     checkouts DIR/<repository>-<commit> (not run in CI)
  python3 scripts/export_names.py --pm-names HTML    first rewrite data/naming/pm_names.json from
                                                     Project Gutenberg eBook #78050 (pg78050-images.html)
"""
import functools
import hashlib
import html
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "data" / "export_names.json"
LOCK = ROOT / "data" / "export_names.lock"
CHANGES = ROOT / "data" / "changes.tsv"
ITEMS = ROOT / "data" / "vol1_items.json"
NAMING = ROOT / "data" / "naming"
VOCAB = NAMING / "vocabulary.json"
READINGS = NAMING / "readings.json"
READINGS_LOCK = NAMING / "readings.lock"
PM_NAMES = NAMING / "pm_names.json"
SLOTS = NAMING / "slots.json"
COUNTERPARTS = NAMING / "counterparts.json"
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

SLOT_WORDS = ("df", "rule")          # definitions and inference rules (data/naming/slots.json)
RESERVED = {*SLOT_WORDS, "reading", "meta", "star"}
WORD = r"[a-z][a-z0-9]*"
STAR_RE = re.compile(r"PM\.star([1-9][0-9]*)_([0-9]+)((?:_[a-z0-9]+)*)")
META_RE = re.compile(rf"PM\.meta_{WORD}(?:_{WORD})*")
VERSION_RE = re.compile(r"v([2-9]|[1-9][0-9]+)")   # a superseded statement's replacement: name_vN
DIGEST_RE = re.compile(r"sha256:[0-9a-f]{64}")
COMMIT_RE = re.compile(r"[0-9a-f]{40}")
SOURCE_RE = re.compile(r"[A-Za-z0-9_][A-Za-z0-9_./-]*\.lean:[1-9][0-9]*")
LOCK_COLUMNS = ["export", "lean", "reading", "statement_digest", "definitions_digest"]
CHANGES_COLUMNS = ["date", "old", "new", "reason", "statement_id"]


def load(p):
    return json.loads(p.read_text(encoding="utf-8"))


def sha256(s):
    return "sha256:" + hashlib.sha256(s.encode("utf-8")).hexdigest()


def pm_key(pm):
    """✱N·M as (N, M) strings: PM's numbers are strings, so ✱2·01 and ✱2·1 stay apart."""
    return tuple(pm[1:].split("."))


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

@functools.lru_cache(maxsize=None)
def lean_output():
    """(statement rows, {definition: canonical text}) from Checks/ExportStatements.lean."""
    p = subprocess.run(["lake", "env", "lean", "Checks/ExportStatements.lean"], cwd=ROOT,
                       capture_output=True, text=True, timeout=3600)
    if p.returncode != 0:
        raise SystemExit(f"Checks/ExportStatements.lean failed:\n{p.stdout}{p.stderr}")
    lines = [json.loads(l) for l in p.stdout.splitlines() if l.startswith("{")]
    return [l for l in lines if "name" in l], {l["def"]: l["canon"] for l in lines if "def" in l}


def digests(row, defs):
    """The statement's digest, and the digest of the definitions it uses (each by name and digest)."""
    d = "\n".join(f"{n} {sha256(defs[n])}" for n in sorted(row["deps"]))
    return sha256(row["canon"]), sha256(d)


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


# ---------------------------------------------------------------- descriptors (not part of names)

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


# ---------------------------------------------------------------- formulas (for review tables and counterparts)

SYMBOLS = {"imp": "→", "or": "∨", "and": "∧", "iff": "↔"}


def render(t, vocab):
    """A propositional formula, fully parenthesized as in counterparts.json: `((p ∨ q) → (q ∨ p))`.
    Other heads are written `name(arguments)`."""
    heads = vocab["lean_heads"]

    def go(t):
        if "v" in t:
            return t["v"]
        if "s" in t or "n" in t:          # a variable named by a literal, as in PM.F.var "p"
            return str(t.get("s", t.get("n")))
        if "lam" in t:
            return "λ. " + go(t["lam"])
        if "c" in t:
            h = heads.get(t["c"], {})
            args = t["a"][h.get("skip", 0):]
            w = h.get("words", [])
            if h.get("form") == "infix" and len(args) == 2 and len(w) == 1 and w[0] in SYMBOLS:
                return f"({go(args[0])} {SYMBOLS[w[0]]} {go(args[1])})"
            if h.get("form") == "prefix" and w == ["not"] and len(args) == 1:
                return "¬" + go(args[0])
            if h.get("form") == "atom" and len(args) == 1:
                return go(args[0])
            return f"{t['c'].removeprefix('PM.')}({', '.join(go(a) for a in args)})"
        if "app" in t:
            return f"{go(t['app'])}({', '.join(go(a) for a in t['a'])})"
        if "b" in t:
            return f"#{t['b']}"
        return "?"
    s = go(t["concl"])
    return ", ".join(go(h) for h in t["hyps"]) + " ⊢ " + s if t["hyps"] else s


def parse_formula(s):
    """A fully parenthesized propositional formula as a tree: a variable is a string, ¬A is ("¬", A),
    (A op B) is (op, A, B)."""
    toks = re.findall(r"[a-z]+|[()¬∧∨→↔]|\S", s.replace(" ", ""))
    pos = 0

    def f():
        nonlocal pos
        t = toks[pos]; pos += 1
        if t == "¬":
            return ("¬", f())
        if t == "(":
            a = f(); op = toks[pos]; pos += 1; b = f()
            if op not in "∧∨→↔" or toks[pos] != ")":
                raise ValueError(s)
            pos += 1
            return (op, a, b)
        if re.fullmatch(r"[a-z]+", t):
            return t
        raise ValueError(s)
    try:
        out = f()
    except IndexError:
        raise ValueError(s)
    if pos != len(toks):
        raise ValueError(s)
    return out


def reverse_iffs(t, paths):
    """t with the two sides of the ↔ at each path swapped; a path is `root` or operand positions
    `2`, `2.1`, … (1 the left operand, 2 the right). Raises ValueError if a path is not at a ↔."""
    def at(t, path):
        if not path:
            if not (isinstance(t, tuple) and t[0] == "↔"):
                raise ValueError("not a ↔")
            return ("↔", t[2], t[1])
        if not isinstance(t, tuple):
            raise ValueError("no such operand")
        i = path[0]
        if t[0] == "¬":
            if i != 1:
                raise ValueError("no such operand")
            return ("¬", at(t[1], path[1:]))
        if i not in (1, 2):
            raise ValueError("no such operand")
        return (t[0], at(t[1], path[1:]), t[2]) if i == 1 else (t[0], t[1], at(t[2], path[1:]))
    for p in paths:
        t = at(t, [] if p == "root" else [int(x) for x in p.split(".")])
    return t


# ---------------------------------------------------------------- entries

def slot_items(slots, items):
    """{PM number: "df" | "rule"} for the definitions and inference rules (data/naming/slots.json)."""
    out = {it["id"]: "df" for it in items if it["cat"] == "Df"}
    out.update({it["id"]: "rule" for it in items if it["cat"] == "rule/prose"})
    out.update({pm: "rule" for pm in slots["pp_rules"]})
    return out


def compose(pm, pm_name, slot, word):
    c, d = pm_key(pm)
    return (f"PM.star{c}_{d}" + (f"_{pm_name.lower()}" if pm_name else "") + (f"_{slot}" if slot else "")
            + (f"_reading_{word}" if word else ""))


def superseded(name, changes):
    """The name that replaces `name`, following data/changes.tsv; `name` itself if none."""
    nxt = {r["old"]: r["new"] for r in changes}
    seen = set()
    while name in nxt and name not in seen:
        seen.add(name)
        name = nxt[name]
    return name


def build(rows, defs, ctx):
    vocab, readings = ctx["vocab"], ctx["readings"]
    names_by_num = {}
    for r in ctx["pm_names"]["names"]:
        names_by_num.setdefault(r["number"], []).append(r["name"])
    slot_of = slot_items(ctx["slots"], ctx["items"])
    locked = {r["lean"]: r for r in ctx["lock"]}
    tag_of_word = {r["word"]: tag for tag, r in readings.items()}
    W = Words(vocab)
    out = []

    def entry(row, pm, reading=None, how=None):
        hyps = [h for h in row["hyps"] if not mentions_reading(h)] if reading else row["hyps"]
        desc, human = W.descriptor(row["concl"], hyps)
        pmn = names_by_num.get(pm, [])
        assert len(pmn) <= 1, (pm, pmn)
        pmn = pmn[0] if pmn else None
        name = compose(pm, pmn, slot_of.get(pm), readings[reading]["word"] if reading else None)
        if row["name"] in locked:          # released: the name and reading stay as locked
            lk = locked[row["name"]]
            name, reading = lk["export"], (tag_of_word.get(lk["reading"]) if lk["reading"] else None)
        name = superseded(name, ctx["changes"])
        sd, dd = digests(row, defs)
        e = {"export": name, "slug": name.replace(".", "_"), "lean": row["name"], "pm": pm,
             "pm_name": pmn, "slot": slot_of.get(pm), "reading": readings[reading]["word"] if reading else None,
             "descriptor": "_".join(desc), "descriptor_needs_human": human,
             "statement_digest": sd, "definitions_digest": dd, "source": module_file(row["module"])}
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
        sd, dd = digests(row, defs)
        out.append({"export": name, "slug": name.replace(".", "_"), "lean": lean, "pm": pm,
                    "pm_name": None, "slot": None, "reading": None, "descriptor": name.split(".", 1)[1],
                    "descriptor_needs_human": True, "statement_digest": sd, "definitions_digest": dd,
                    "source": module_file(row["module"]), "meta": True})
    out.sort(key=lambda e: (e.get("meta", False),
                            int(e["pm"][1:].split(".")[0]) if e["pm"] else 0,
                            [int(ch) for ch in e["pm"][1:].split(".")[1]] if e["pm"] else [], e["export"]))
    return out, sorted(W.unknown)


# ---------------------------------------------------------------- checks

def parts(name):
    """The parts of a `PM.star…` name after the number, in the order written: a list of (kind, value),
    kind one of pm_name, slot, reading, version, extra; None if the name is not `PM.star<N>_<M>…`."""
    m = STAR_RE.fullmatch(name)
    if not m:
        return None
    toks = m[3].split("_")[1:]
    out, i = [], 0
    while i < len(toks):
        t = toks[i]
        if t == "reading" and i + 1 < len(toks):
            out.append(("reading", toks[i + 1])); i += 2; continue
        if t in SLOT_WORDS:
            out.append(("slot", t))
        elif VERSION_RE.fullmatch(t):
            out.append(("version", t))
        elif not out and re.fullmatch(WORD, t) and t not in RESERVED:
            out.append(("pm_name", t))
        else:
            out.append(("extra", t))
        i += 1
    return out


ORDER = ["pm_name", "slot", "reading", "version"]


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
        m = STAR_RE.fullmatch(n)
        if not m:
            bad.append(f"{n}: not PM.star<N>_<M>[_<pmname>][_df|_rule][_reading_<word>][_v<N>] in lower case")
            continue
        if f"*{m[1]}.{m[2]}" != e["pm"]:
            bad.append(f"{n}: number does not match {e['pm']}")
    return bad


def check_suffix_order(entries, ctx):
    """Each optional part at most once and in the order of ORDER; so `_v<N>` is terminal."""
    bad = []
    for e in entries:
        ps = parts(e["export"]) if not e.get("meta") else None
        if not ps:
            continue
        kinds = [k for k, _ in ps if k != "extra"]
        if len(set(kinds)) != len(kinds) or kinds != sorted(kinds, key=ORDER.index):
            bad.append(f"{e['export']}: parts out of order; the order is [_<pmname>][_df|_rule]"
                       "[_reading_<word>][_v<N>], and _v<N> comes last")
    return bad


def check_pm_name_only(entries, ctx):
    """Option B: after the number, PM's own name when PM gives one, and no other word (no descriptor,
    no Mathlib word)."""
    names = {}
    for r in ctx["pm_names"]["names"]:
        names.setdefault(r["number"], set()).add(r["name"])
    bad = [f"PM's name {r['name']} ({r['number']}) is a reserved word of export names"
           for r in ctx["pm_names"]["names"] if r["name"].lower() in RESERVED or VERSION_RE.fullmatch(r["name"].lower())]
    for e in entries:
        if e.get("meta"):
            continue
        ps = parts(e["export"]) or []
        extra = [v for k, v in ps if k == "extra"]
        if extra:
            bad.append(f"{e['export']}: words other than PM's name and the suffixes: {', '.join(extra)} "
                       "(no descriptors or Mathlib words in names)")
        got = [v for k, v in ps if k == "pm_name"]
        given = names.get(e["pm"], set())
        want = sorted(n.lower() for n in given)
        if got != want[:1] or (given and e["pm_name"] not in given) or (not given and e["pm_name"] is not None):
            bad.append(f"{e['export']}: PM names {e['pm']} {'/'.join(sorted(given)) or 'nothing'}; the name "
                       f"has {'_'.join(got) or 'none'}")
    return bad


def check_slots(entries, ctx):
    """`_df` exactly for PM's definitions and `_rule` exactly for its inference rules."""
    cats = {it["id"]: it["cat"] for it in ctx["items"]}
    bad = [f"data/naming/slots.json: {pm} is not a Pp of data/vol1_items.json"
           for pm in ctx["slots"]["pp_rules"] if cats.get(pm) != "Pp"]
    slot_of = slot_items(ctx["slots"], ctx["items"])
    for e in entries:
        if e.get("meta"):
            continue
        got = [v for k, v in parts(e["export"]) or [] if k == "slot"]
        want = slot_of.get(e["pm"])
        if got != ([want] if want else []) or e.get("slot") != want:
            what = {"df": "a definition (Df)", "rule": "an inference rule"}.get(want, "an asserted proposition")
            bad.append(f"{e['export']}: {e['pm']} is {what}, so the name has "
                       f"{'_' + want if want else 'no _df or _rule'}")
    return bad


def check_readings(entries, ctx):
    words = [r["word"] for r in ctx["readings"].values()]
    bad = [f"data/naming/readings.json: word {w} used twice" for w in set(words) if words.count(w) > 1]
    for e in entries:
        n = e["export"]
        ps = parts(n) or []
        got = [v for k, v in ps if k == "reading"]
        if n.count("reading") > len(got):
            bad.append(f"{n}: 'reading' only as the suffix _reading_<word>")
        for w in got:
            if w not in words:
                bad.append(f"{n}: reading {w} is not in data/naming/readings.json")
        if (got[0] if got else None) != e["reading"]:
            bad.append(f"{n}: suffix does not match reading {e['reading']}")
    return bad


def check_readings_frozen(entries, ctx):
    """Reading meanings are append-only: a locked reading keeps its tag, word and meaning."""
    bad = []
    for tag, r in ctx["readings_lock"].items():
        now = ctx["readings"].get(tag)
        if now is None:
            bad.append(f"reading {tag} ({r['word']}) is locked in data/naming/readings.lock but was removed")
            continue
        for k in ("word", "meaning"):
            if now.get(k) != r[k]:
                bad.append(f"reading {tag}: {k} changed from {r[k]!r} to {now.get(k)!r}; a released reading "
                           "never changes meaning: add a new reading instead")
    return bad


def check_unique_name(entries, ctx):
    seen, bad = set(), []
    for e in entries:
        if e["export"] in seen:
            bad.append(f"{e['export']}: used twice")
        seen.add(e["export"])
    return bad


def check_unique_slug(entries, ctx):
    """The platform slug is the name with `.` → `_`: ASCII, and unique, also ignoring case."""
    seen, bad = {}, []
    for e in entries:
        s = e["export"].replace(".", "_")
        if e.get("slug") != s:
            bad.append(f"{e['export']}: slug {e.get('slug')} is not {s}")
        if not s.isascii() or not re.fullmatch(r"[A-Za-z0-9_]+", s):
            bad.append(f"{e['export']}: slug {s} is not ASCII letters, digits and _")
        if s.lower() in seen:
            bad.append(f"{e['export']}: slug {s} also {seen[s.lower()]}")
        seen[s.lower()] = e["export"]
    return bad


def check_no_top_level(entries, ctx):
    return [f"{e['export']}: a name is PM.<one component>, never top-level PM_ or nested"
            for e in entries if not e["export"].startswith("PM.") or e["export"].count(".") != 1]


def check_vocabulary(entries, ctx):
    """The descriptor (a field, not part of the name) uses only vocabulary words."""
    words = set(ctx["vocab"]["words"])
    bad = []
    for e in entries:
        out = [w for w in e["descriptor"].split("_") if w not in words]
        if out:
            bad.append(f"{e['export']}: descriptor {e['descriptor']}: not in the vocabulary: {', '.join(out)}")
    return bad


def check_lock(entries, ctx):
    """Every locked name is still exported, for the same statement, definitions and reading."""
    by = {e["export"]: e for e in entries}
    bad = []
    for r in ctx["lock"]:
        n, e = r["export"], by.get(r["export"])
        if e is None:
            bad.append(f"{n}: in data/export_names.lock but no longer exported; a released name stays, and a "
                       "superseded card stays importable (docs/VERSIONING.md)")
            continue
        for k, what in (("statement_digest", "statement"), ("definitions_digest", "definitions it uses")):
            if e[k] != r[k]:
                bad.append(f"{n}: its {what} changed since release ({r[k][:19]}… → {e[k][:19]}…); a released "
                           f"name always means the same statement: name the new statement {n}_v<N> and add "
                           "a row to data/changes.tsv (docs/VERSIONING.md)")
        if (e["reading"] or "") != r["reading"]:
            bad.append(f"{n}: locked under reading {r['reading'] or 'none'}, now {e['reading']}")
    return bad


def check_versions(entries, ctx):
    """A name ending `_v<N>` is the `new` of a row of data/changes.tsv, whose statement_id is its digest."""
    rows = {r["new"]: r for r in ctx["changes"]}
    bad = []
    for r in ctx["changes"]:
        if (not re.fullmatch(r"\d{4}-\d{2}-\d{2}", r["date"]) or not r["reason"].strip()
                or not DIGEST_RE.fullmatch(r["statement_id"])):
            bad.append(f"data/changes.tsv: malformed row {r}")
    for e in entries:
        ps = parts(e["export"]) or []
        if any(k == "version" for k, _ in ps):
            r = rows.get(e["export"])
            if r is None:
                bad.append(f"{e['export']}: no row of data/changes.tsv gives this name as new")
            elif r["statement_id"] != e["statement_digest"]:
                bad.append(f"{e['export']}: data/changes.tsv gives statement {r['statement_id']}, not its digest")
    return bad


def check_counterparts(entries, ctx):
    """data/naming/counterparts.json: pinned, well formed, and an exact match under the criterion of
    docs/NAMING.md for the statement exported now. No network: the files are not fetched."""
    cp = ctx["counterparts"]
    by = {e["pm"]: e for e in entries if not e.get("meta") and e["reading"] is None}
    rows_by = {r["name"]: r for r in ctx["rows"]}
    bad = []
    for k, repo in cp["repositories"].items():
        if not COMMIT_RE.fullmatch(repo.get("commit", "")) or not repo.get("url", "").startswith("https://"):
            bad.append(f"repository {k}: needs a url and a full 40-digit commit")
    seen = set()
    for r in cp["counterparts"]:
        pm, where = r.get("pm"), f"counterpart {r.get('pm')} {r.get('declaration')}"
        if pm in seen:
            bad.append(f"{where}: a second counterpart for {pm}")
        seen.add(pm)
        e = by.get(pm)
        if e is None:
            bad.append(f"{where}: {pm} is not exported"); continue
        if r.get("export") != e["export"]:
            bad.append(f"{where}: export {r.get('export')} is not {e['export']}")
        if not r.get("declaration") or not r.get("signature"):
            bad.append(f"{where}: needs the declaration and its signature")
        repo = cp["repositories"].get(r.get("repository"))
        if repo is None:
            bad.append(f"{where}: repository {r.get('repository')} is not listed")
        elif r.get("commit") != repo["commit"] or not COMMIT_RE.fullmatch(r.get("commit") or ""):
            bad.append(f"{where}: commit {r.get('commit')} is not the pinned commit of {r.get('repository')}")
        src = r.get("source") or ""
        if not SOURCE_RE.fullmatch(src) or ".." in src.split("/"):
            bad.append(f"{where}: source {src!r} is not <relative path>.lean:<line>")
        for b in ("classical", "iff_reversed"):
            if not isinstance(r.get(b), bool):
                bad.append(f"{where}: {b} must be true or false")
        if r.get("classical_from") not in ("axioms", "source"):
            bad.append(f"{where}: classical_from must be axioms or source")
        if r.get("checked") not in ("lean", "source"):
            bad.append(f"{where}: checked must be lean or source")
        paths = r.get("iff_reversed_at", [])
        if r.get("iff_reversed") is not bool(paths):
            bad.append(f"{where}: iff_reversed must say whether iff_reversed_at is empty")
        try:
            ours = parse_formula(render(rows_by[e["lean"]], ctx["vocab"]))
            if parse_formula(r.get("pm_formula", "")) != ours:
                bad.append(f"{where}: pm_formula {r.get('pm_formula')} is not the statement exported now")
            elif reverse_iffs(parse_formula(r.get("statement", "")), paths) != ours:
                bad.append(f"{where}: statement {r.get('statement')} is not the PM formula up to the recorded "
                           "iff reversals")
        except (ValueError, KeyError) as x:
            bad.append(f"{where}: cannot read a formula ({x})")
    return bad


CHECKS = {"pattern": check_pattern, "suffix_order": check_suffix_order, "pm_name_only": check_pm_name_only,
          "slots": check_slots, "readings": check_readings, "readings_frozen": check_readings_frozen,
          "unique_name": check_unique_name, "unique_slug": check_unique_slug, "no_top_level": check_no_top_level,
          "vocabulary": check_vocabulary, "lock": check_lock, "versions": check_versions,
          "counterparts": check_counterparts}


def read_tsv(path, columns):
    """Rows of a tab-separated file with a header line; lines starting with # are comments."""
    if not path.exists():
        return []
    lines = [l for l in path.read_text(encoding="utf-8").splitlines() if l.strip() and not l.startswith("#")]
    if not lines:
        return []
    if lines[0].split("\t") != columns:
        raise SystemExit(f"{path}: the header must be {' '.join(columns)}")
    return [dict(zip(columns, l.split("\t"))) for l in lines[1:]]


def context(lock=LOCK, readings_lock=READINGS_LOCK):
    rows, _ = lean_output()
    return {"vocab": load(VOCAB), "readings": load(READINGS), "pm_names": load(PM_NAMES), "slots": load(SLOTS),
            "items": load(ITEMS), "counterparts": load(COUNTERPARTS), "lock": read_tsv(lock, LOCK_COLUMNS),
            "readings_lock": load(readings_lock) if readings_lock.exists() else {},
            "changes": read_tsv(CHANGES, CHANGES_COLUMNS), "rows": rows}


def check(entries, ctx, skip=()):
    """{check name: [problems]} for the checks not skipped."""
    return {k: f(entries, ctx) for k, f in CHECKS.items() if k not in skip}


def lock_rows(entries, ctx):
    """The rows of the lock after a release of `entries`: the rows already locked, then each new name
    with its Lean declaration, reading and digests."""
    old = {r["export"]: r for r in ctx["lock"]}
    for e in entries:
        old.setdefault(e["export"], {"export": e["export"], "lean": e["lean"], "reading": e["reading"] or "",
                                     "statement_digest": e["statement_digest"],
                                     "definitions_digest": e["definitions_digest"]})
    return list(old.values())


def write_lock(entries, ctx, lock=LOCK, readings_lock=READINGS_LOCK):
    """At a release: every exported name with its Lean declaration, reading and digests, and every
    reading's word and meaning. Names already locked stay; new ones are added."""
    head =["# Released export names (docs/VERSIONING.md): each name with the Lean declaration it was",
            "# released from, its reading, and the digests of its statement and of the definitions it",
            "# uses. Rows are only ever added. Written by scripts/export_names.py --write-lock.",
            "\t".join(LOCK_COLUMNS)]
    lock.write_text("\n".join(head + ["\t".join(r[c] for c in LOCK_COLUMNS) for r in lock_rows(entries, ctx)])
                    + "\n",
                    encoding="utf-8")
    rl = dict(ctx["readings_lock"])
    for tag, r in ctx["readings"].items():
        rl.setdefault(tag, {"word": r["word"], "meaning": r["meaning"]})
    readings_lock.write_text(json.dumps(rl, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")


def verify_counterparts(ctx, base):
    """Each counterpart's file:line, in a checkout `base/<repository>-<commit>`, names the declaration (or,
    for a structure's constructor such as And.intro, declares the structure, as Lean's declaration
    ranges do)."""
    bad = []
    for r in ctx["counterparts"]["counterparts"]:
        path, line = r["source"].rsplit(":", 1)
        f = pathlib.Path(base) / f"{r['repository']}-{r['commit']}" / path
        if not f.exists():
            bad.append(f"{r['pm']} {r['declaration']}: no file {f}"); continue
        text = f.read_text(encoding="utf-8").splitlines()
        *ns, last = r["declaration"].split(".")
        pat = rf"(?<![\w']){re.escape(last)}(?![\w'₀-₉])"
        if ns:
            pat += rf"|\b(structure|inductive|class)\s+{re.escape(ns[-1])}\b"
        if int(line) > len(text) or not re.search(pat, text[int(line) - 1]):
            bad.append(f"{r['pm']} {r['declaration']}: {r['source']} does not name {last}")
    return bad


# ---------------------------------------------------------------- main

def chapter_counts(entries):
    out = {}
    for e in entries:
        c = "meta" if e.get("meta") else int(e["pm"][1:].split(".")[0])
        n = out.setdefault(c, [0, 0])
        n[0] += 1
        n[1] += bool(e.get("slot"))
    return out


def write_tsv(entries, ctx, path, chapters=None):
    lo, hi = chapters or (0, 10 ** 6)
    sel = [e for e in entries
           if (e.get("meta") and lo <= 1 <= hi) or (e["pm"] and lo <= int(e["pm"][1:].split(".")[0]) <= hi
                                                    and not e.get("meta"))]
    rows = {r["name"]: r for r in ctx["rows"]}
    cps = {r["export"]: r["declaration"] for r in ctx["counterparts"]["counterparts"]}
    cols = ["pm", "pm_name", "export", "formula", "counterpart"]
    lines = ["\t".join(cols)]
    for e in sel:
        v = {**e, "formula": render(rows[e["lean"]], ctx["vocab"]), "counterpart": cps.get(e["export"])}
        lines.append("\t".join("" if v.get(k) is None else str(v[k]) for k in cols))
    pathlib.Path(path).write_text("\n".join(lines) + "\n", encoding="utf-8")
    return len(sel)


def main(args):
    if "--pm-names" in args:
        write_pm_names(pm_names_from_html(args[args.index("--pm-names") + 1]))
    ctx = context()
    rows, defs = lean_output()
    entries, unknown = build(rows, defs, ctx)
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
    if "--verify-counterparts" in args:
        problems["counterpart_sources"] = verify_counterparts(ctx, args[args.index("--verify-counterparts") + 1])
    for k, v in problems.items():
        for p in v:
            print(f"{k}: {p}")
        failed |= bool(v)
    if "--write-lock" in args and not failed:
        write_lock(entries, ctx)
        print("wrote data/export_names.lock and data/naming/readings.lock")
    if "--tsv" in args:
        ch = None
        if "--chapters" in args:
            a, b = args[args.index("--chapters") + 1].split("-")
            ch = (int(a), int(b))
        n = write_tsv(entries, ctx, args[args.index("--tsv") + 1], ch)
        print(f"wrote {n} rows")
    counts = chapter_counts(entries)
    print(f"export names: {len(entries)} entries, longest {max(len(e['export']) for e in entries)} characters, "
          f"{len(ctx['lock'])} locked, {len(ctx['counterparts']['counterparts'])} with a counterpart; "
          "definitions and rules: "
          + "; ".join(f"{'✱' + str(c) if c != 'meta' else 'meta'} {n[1]}/{n[0]}" for c, n in counts.items()))
    print("checks: " + ", ".join(f"{k} {'ok' if not v else 'FAILED'}" for k, v in problems.items()))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
