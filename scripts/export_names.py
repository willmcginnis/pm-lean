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
declaration is in data/export_names.lock takes the locked name and reading, also once the declaration has
moved to PM/Deprecated/ because its statement was superseded. The replacement is the declaration of the
same Lean name with `_v<N>`, exported as the old one's name with `_v<N>`; data/changes.tsv records the
pair and renames nothing (docs/VERSIONING.md).

Checks/Counterparts.lean, which has Lean check the Lean core counterparts, is also written from
data/naming/counterparts.json and the statements; so is Checks/MathlibCounterparts/MathlibCounterparts.lean,
which does the same for the Mathlib ones against the pinned Mathlib, in a Lake project of its own.

Usage (from the repository root, after `lake build`):
  python3 scripts/export_names.py                    write data/export_names.json, Checks/Counterparts.lean,
                                                     Checks/MathlibCounterparts/MathlibCounterparts.lean
  python3 scripts/export_names.py --check            exit 1 if they are not up to date or break a rule
  python3 scripts/export_names.py --tsv PATH [--chapters 1-5]   also write a review table
  python3 scripts/export_names.py --write-lock       at a release: lock every name and reading meaning
  python3 scripts/export_names.py --write-lock --chapters 1-5   lock only the names of ✱1–✱5 and the results
                                                     about the system, and only the readings they use
  python3 scripts/export_names.py --root             print the Merkle root of the lock and the release's
                                                     build metadata `m.<first 12 digits>` (docs/VERSIONING.md)
  python3 scripts/export_names.py --verify-counterparts DIR    check each counterpart's file:line (and a
                                                     Mathlib one's header) in checkouts
                                                     DIR/<repository>-<commit> (not run in CI)
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
COUNTERPARTS_LEAN = ROOT / "Checks" / "Counterparts.lean"
MATHLIB_COUNTERPARTS_LEAN = ROOT / "Checks" / "MathlibCounterparts" / "MathlibCounterparts.lean"
BUNDLES = NAMING / "definition_bundles.json"
MAX_WORDS = 6
WORKING_READING = "C"   # a ✱9 statement for every reading is exported under the working reading

# which declarations state PM's propositions, by module: (module, regex on the full name). A Lean name
# ending `_v<N>` is the replacement of a superseded declaration (docs/VERSIONING.md); the superseded one
# keeps its Lean name in the same module under PM.Deprecated (PM/Deprecated/Star21.lean for PM/Star21.lean).
LEAN_VERSION = r"(?:_v(?P<v>[2-9]|[1-9][0-9]+))?"
SOURCES = [
    ("PM.Replay", r"PM\.t(\d+)_(\d+)"), ("PM.Replay2", r"PM\.t(\d+)_(\d+)"),
    *[(f"PM.Star{c}", r"PM\.q(\d+)_(\d+)") for c in (10, 11, 12, 13, 14, 20, 21, 22, 23, 24, 25)],
    ("PM.Found9.Star9", r"PM\.F9\.f(\d+)_(\d+)(?:_(?:russell|switch|prenex))?"),
]
DEPRECATED = "PM.Deprecated."
# a check theorem (docs/NAMING.md): a test of the repository's own definitions, never a proposition of PM
CHECK_RE = re.compile(r"(?:.*\.)?check_[^.]*")


def is_check(lean_name):
    """Is this Lean declaration a check theorem (its last component begins `check_`)?"""
    return CHECK_RE.fullmatch(lean_name) is not None
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
BUNDLE_RE = re.compile(r"PM_core_[a-z0-9]+(?:_[a-z0-9]+)*")   # a definition bundle (not a proposition of PM)
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


SIG_TOKEN = re.compile(r"\s*(@\[[^\]]*\]|[∀,:{}()→↔∧∨¬*]|[^\W\d][\w'.₀-₉]*)")


def parse_signature(sig, section_variables=""):
    """A declaration's type, read strictly as a schema of the propositional fragment: (binders, body).
    `binders` are its leading variables in order, each (name, "Prop" or "Sort"); `body` is a tree as
    parse_formula's over their names. Accepted: a type as Lean prints it (`∀ {a b : Prop}, b → a ∨ b`,
    `{α : Sort u} → α → α`) or a declaration header as written in the source (`theorem em' (p : Prop) :
    ¬p ∨ p`, with the section's `variable {a b : Prop}` for the variables it uses but does not bind).
    Lean's precedences: ¬ binds tightest, then ∧, ∨ (both to the right), → (to the right), ↔ (neither).
    A binder `(x : α)` with α a Sort variable and x unused is the implication α → …, as in Lean, and
    `A → False` is ¬A (docs/NAMING.md, the criterion). Anything else raises ValueError."""
    def tokens(s):
        out, pos, s = [], 0, s.strip()
        while pos < len(s):
            m = SIG_TOKEN.match(s, pos)
            if not m or not m[1]:
                raise ValueError(f"cannot read {s[pos:pos + 20]!r} in {sig!r}")
            out.append(m[1]); pos = m.end()
        return out

    toks, pos = tokens(sig), 0
    sorts = {}                                     # bound name -> "Prop" | "Sort" (a variable)
    leading = []

    def peek(k=0):
        return toks[pos + k] if pos + k < len(toks) else None

    def take(want=None):
        nonlocal pos
        t = peek()
        if t is None or (want is not None and t != want):
            raise ValueError(f"expected {want or 'more'} at {t!r} in {sig!r}")
        pos += 1
        return t

    def ident():
        t = take()
        if not re.fullmatch(r"[^\W\d][\w'₀-₉]*", t) or t in ("Prop", "Sort", "False", "Type"):
            raise ValueError(f"not a variable: {t!r} in {sig!r}")
        return t

    def sort_of():
        """The type in a binder: Prop, Sort u, Sort*, or a Sort variable (then a hypothesis)."""
        t = take()
        if t == "Prop":
            return "Prop"
        if t == "Sort":
            if peek() == "*":
                take()
            else:
                ident()
            return "Sort"
        if sorts.get(t) == "Sort":
            return ("var", t)
        raise ValueError(f"binder type {t!r} is not Prop, a Sort or a Sort variable in {sig!r}")

    def group(close):
        names = []
        while peek() != ":":
            names.append(ident())
        take(":")
        s = sort_of()
        take(close)
        if not names:
            raise ValueError(f"empty binder in {sig!r}")
        return names, s

    def bind(names, s, top):
        """Bind variables; a hypothesis binder over a Sort variable is returned for the caller."""
        if isinstance(s, tuple):
            return [s[1]] * len(names), names
        if not top:
            raise ValueError(f"a propositional variable bound inside the formula in {sig!r}")
        for n in names:
            if n in sorts:
                raise ValueError(f"{n} bound twice in {sig!r}")
            sorts[n] = s
            leading.append((n, s))
        return [], []

    def binders_then(top, sep):
        """`∀ groups, T` (sep ",") or `{x : S} → T` (sep "→")."""
        hyps, hnames = [], []
        while peek() in ("{", "("):
            close = "}" if take() == "{" else ")"
            h, hn = bind(*group(close), top)
            hyps += h; hnames += hn
            if sep == "→":
                break
        take(sep)
        body = typ(top)
        for n in hnames:
            if n in leaves(body):
                raise ValueError(f"{n} used as a term in {sig!r}")
        for h in reversed(hyps):
            body = ("→", h, body)
        return body

    def binder_ahead():
        """`{` always opens a binder; `(` does when names and then `:` follow."""
        if peek() == "{":
            return True
        k = pos + 1
        while k < len(toks) and re.fullmatch(r"[^\W\d][\w'₀-₉]*", toks[k]):
            k += 1
        return peek() == "(" and k > pos + 1 and k < len(toks) and toks[k] == ":"

    def typ(top=False):
        if peek() == "∀":
            take()
            return binders_then(top, ",")
        if peek() in ("{", "(") and binder_ahead():
            return binders_then(top, "→")
        return iff()

    def iff():
        a = imp()
        if peek() == "↔":
            take()
            b = imp()
            if peek() == "↔":
                raise ValueError(f"↔ does not associate, in {sig!r}")
            return ("↔", a, b)
        return a

    def imp():
        a = disj()
        if peek() == "→":
            take()
            return ("→", a, imp())
        return a

    def disj():
        a = conj()
        if peek() == "∨":
            take()
            return ("∨", a, disj())
        return a

    def conj():
        a = neg()
        if peek() == "∧":
            take()
            return ("∧", a, conj())
        return a

    def neg():
        if peek() == "¬":
            take()
            return ("¬", neg())
        if peek() == "∀":
            take()
            return binders_then(False, ",")
        return atom()

    def atom():
        t = take()
        if t == "(":
            a = typ()
            take(")")
            return a
        if t == "False":
            return "False"
        if sorts.get(t) is None:
            raise ValueError(f"{t!r} is not a bound variable in {sig!r}")
        return t

    if peek() and (peek().startswith("@[") or peek() in ("protected", "theorem", "lemma")):
        # a source header: [@[attrs]] [protected] theorem|lemma name binders : type
        while peek() and peek().startswith("@["):
            take()
        if peek() == "protected":
            take()
        if take() not in ("theorem", "lemma"):
            raise ValueError(f"not a theorem or lemma header: {sig!r}")
        take()                                     # the declaration's name
        header_binders = []
        while peek() in ("{", "("):
            close = "}" if take() == "{" else ")"
            header_binders.append(group(close))
        take(":")
        rest = toks[pos:]
        bound = {n for ns, _ in header_binders for n in ns}
        if section_variables:                      # `variable {a b : Prop}`: those the header uses
            vt = tokens(section_variables)
            if not vt or vt[0] != "variable":
                raise ValueError(f"not a variable command: {section_variables!r}")
            toks_save, pos_save = toks, pos
            toks, pos = vt, 1
            groups = []
            while peek() in ("{", "("):
                close = "}" if take() == "{" else ")"
                groups.append(group(close))
            if pos != len(toks):
                raise ValueError(f"cannot read {section_variables!r}")
            toks, pos = toks_save, pos_save
            for ns, s in groups:
                used = [n for n in ns if n in rest and n not in bound]
                if used:
                    bind(used, s, True)
        for ns, s in header_binders:
            bind(ns, s, True)
        body = typ(True)
    else:
        body = typ(True)
    if pos != len(toks):
        raise ValueError(f"unread {' '.join(toks[pos:])!r} in {sig!r}")

    def norm(t):
        if isinstance(t, tuple):
            if t[0] == "→" and t[2] == "False":
                return ("¬", norm(t[1]))
            return (t[0], *map(norm, t[1:]))
        if t == "False":
            raise ValueError(f"False outside A → False in {sig!r}")
        return t
    return leading, norm(body)


def leaves(t):
    """The variables (and False) of a tree."""
    return {t} if isinstance(t, str) else set().union(*(leaves(x) for x in t[1:]))


def substitute(t, sub):
    if isinstance(t, tuple):
        return (t[0], *(substitute(x, sub) for x in t[1:]))
    return sub[t]


def lean_formula(t):
    """A tree as Lean source over Prop variables, fully parenthesized."""
    if isinstance(t, str):
        return t
    if t[0] == "¬":
        return f"¬{lean_formula(t[1])}"
    return f"({lean_formula(t[1])} {t[0]} {lean_formula(t[2])})"


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


def without_version(name):
    """`name` without a final `_v<N>`, and N (1 if none)."""
    m = re.fullmatch(r"(.*)_(v([2-9]|[1-9][0-9]+))", name)
    return (m[1], int(m[3])) if m else (name, 1)


def build(rows, defs, ctx):
    """The entries for the statements of `rows`. A locked declaration keeps its locked name and reading,
    also when it has moved to PM.Deprecated (docs/VERSIONING.md); a declaration `<lean>_v<N>` is the
    replacement of `<lean>` (or `<lean>_v<N-1>`) and is exported as that one's name with `_v<N>`; it
    supersedes that one, locked or not, so that locking a replacement changes nothing (a fixed point)."""
    vocab, readings = ctx["vocab"], ctx["readings"]
    names_by_num = {}
    for r in ctx["pm_names"]["names"]:
        names_by_num.setdefault(r["number"], []).append(r["name"])
    slot_of = slot_items(ctx["slots"], ctx["items"])
    locked = {r["lean"]: r for r in ctx["lock"]}
    tag_of_word = {r["word"]: tag for tag, r in readings.items()}
    W = Words(vocab)
    out = []

    def named(lean, pm, pmn, reading):
        """(export name, reading tag) of the declaration `lean`, and the export name it supersedes."""
        base, n = without_version(lean)
        before = None if n == 1 else base if n == 2 else f"{base}_v{n - 1}"   # the declaration it replaces
        if lean in locked:             # released: the name and reading stay as locked
            lk = locked[lean]
            return (lk["export"], (tag_of_word.get(lk["reading"]) if lk["reading"] else None),
                    named(before, pm, pmn, reading)[0] if before else None)
        if before:                     # the replacement of the declaration before it
            old, reading, _ = named(before, pm, pmn, reading)
            return f"{without_version(old)[0]}_v{n}", reading, old
        return compose(pm, pmn, slot_of.get(pm), readings[reading]["word"] if reading else None), reading, None

    def entry(row, pm, reading=None, how=None):
        hyps = [h for h in row["hyps"] if not mentions_reading(h)] if reading else row["hyps"]
        desc, human = W.descriptor(row["concl"], hyps)
        pmn = names_by_num.get(pm, [])
        assert len(pmn) <= 1, (pm, pmn)
        pmn = pmn[0] if pmn else None
        name, reading, supersedes = named(row["name"], pm, pmn, reading)
        sd, dd = digests(row, defs)
        e = {"export": name, "slug": name.replace(".", "_"), "lean": row["name"], "pm": pm,
             "pm_name": pmn, "slot": slot_of.get(pm), "reading": readings[reading]["word"] if reading else None,
             "descriptor": "_".join(desc), "descriptor_needs_human": human,
             "statement_digest": sd, "definitions_digest": dd, "source": module_file(row["module"])}
        if reading:
            e["reading_from"] = how
        if supersedes:
            e["supersedes"] = supersedes
        if row["module"].startswith(DEPRECATED) or "deprecated" in row:
            e["deprecated"] = True
            e["deprecated_lean"] = row.get("deprecated", {})   # the Lean attribute; resolved below
        out.append(e)

    by_name = {r["name"]: r for r in rows}
    for lean, pm in PRIMITIVES.items():
        entry(by_name[lean], pm)
    for row in rows:
        if is_check(row["name"]):  # never exported, whatever it is named after
            continue
        module = row["module"]
        if module.startswith(DEPRECATED):  # a superseded declaration, kept with its Lean name
            module = "PM." + module[len(DEPRECATED):]
        for mod, rx in SOURCES:
            if module != mod:
                continue
            m = re.fullmatch(rx + LEAN_VERSION, row["name"])
            if not m:
                continue
            pm = f"*{m[1]}.{m[2]}"
            if mod == "PM.Found9.Star9":
                tag, how = reading_of(row, readings)
                entry(row, pm, tag, how)
            else:
                entry(row, pm)
    # a deprecated entry names its replacement: the export of the declaration its @[deprecated] names
    export_of = {e["lean"]: e["export"] for e in out}
    for e in out:
        if "deprecated_lean" in e:
            d = e.pop("deprecated_lean")
            e["superseded_by"] = export_of.get(d.get("new"))
            e["deprecated_since"] = d.get("since") or None
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


def check_no_checks(entries, ctx):
    """No check theorem (`check_…`) is exported: it is not a proposition of PM."""
    return [f"{e['export']}: its Lean declaration {e['lean']} is a check theorem, never exported"
            for e in entries if is_check(e["lean"])]


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
                           f"name always means the same statement: keep {r['lean']} as it was in "
                           f"PM/Deprecated/, @[deprecated {r['lean']}_v<N>], state the new statement as "
                           f"{r['lean']}_v<N> (exported as {n}_v<N>), and add a row to data/changes.tsv "
                           "(docs/VERSIONING.md)")
        if (e["reading"] or "") != r["reading"]:
            bad.append(f"{n}: locked under reading {r['reading'] or 'none'}, now {e['reading']}")
    return bad


def check_versions(entries, ctx):
    """Superseded statements (docs/VERSIONING.md): both generations exported, linked three ways.

    - a `_v<N>` name is the `new` of a row of data/changes.tsv whose statement_id is its digest and whose
      `old` is the name it supersedes (`_v<N-1>`, or no `_v` for N = 2);
    - a deprecated entry (a declaration of PM/Deprecated/, marked @[deprecated]) is a released (locked)
      name, its @[deprecated] names the replacement's declaration, and a row of data/changes.tsv gives
      that replacement as its `new`;
    - every row's `old` is exported and deprecated, and its `new` is exported."""
    by = {e["export"]: e for e in entries}
    locked = {r["export"] for r in ctx["lock"]}
    rows_new = {r["new"]: r for r in ctx["changes"]}
    rows_old = {r["old"]: r for r in ctx["changes"]}
    bad = []
    for r in ctx["changes"]:
        if (not re.fullmatch(r"\d{4}-\d{2}-\d{2}", r["date"]) or not r["reason"].strip()
                or not DIGEST_RE.fullmatch(r["statement_id"])):
            bad.append(f"data/changes.tsv: malformed row {r}")
        old, new = by.get(r["old"]), by.get(r["new"])
        if old is None:
            bad.append(f"data/changes.tsv: {r['old']} is not exported; a superseded card stays exported, "
                       "from its declaration in PM/Deprecated/")
        elif not old.get("deprecated"):
            bad.append(f"data/changes.tsv: {r['old']} is superseded but its declaration {old['lean']} is not "
                       "a @[deprecated] declaration of PM/Deprecated/")
        if new is None:
            bad.append(f"data/changes.tsv: {r['new']} is not exported")
        base, n = without_version(r["old"])
        if r["new"] != f"{base}_v{n + 1}":
            bad.append(f"data/changes.tsv: {r['old']} is superseded by {base}_v{n + 1}, not {r['new']}")
    for e in entries:
        n = e["export"]
        if any(k == "version" for k, _ in parts(n) or []):
            r = rows_new.get(n)
            if r is None:
                bad.append(f"{n}: no row of data/changes.tsv gives this name as new")
            else:
                if r["statement_id"] != e["statement_digest"]:
                    bad.append(f"{n}: data/changes.tsv gives statement {r['statement_id']}, not its digest")
                if r["old"] != e.get("supersedes"):
                    bad.append(f"{n}: data/changes.tsv gives old {r['old']}, but its declaration {e['lean']} "
                               f"replaces the one exported as {e.get('supersedes')}")
        if e.get("deprecated"):
            if n not in locked:
                bad.append(f"{n}: deprecated but never released (not in data/export_names.lock); an unreleased "
                           "statement is changed in place")
            if not e.get("superseded_by"):
                bad.append(f"{n}: its declaration {e['lean']} is not @[deprecated <the replacement>]")
            r = rows_old.get(n)
            if r is None:
                bad.append(f"{n}: deprecated with no row of data/changes.tsv giving it as old")
            elif e.get("superseded_by") and r["new"] != e["superseded_by"]:
                bad.append(f"{n}: @[deprecated] names {e['superseded_by']}, data/changes.tsv {r['new']}")
    return bad


def check_counterparts(entries, ctx):
    """data/naming/counterparts.json: pinned, well formed, and an exact match under the criterion of
    docs/NAMING.md for the statement exported now. No network: the files are not fetched."""
    cp = ctx["counterparts"]
    by = {e["pm"]: e for e in entries if not e.get("meta") and e["reading"] is None and not e.get("deprecated")}
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
        if r.get("checked") not in CHECKED.get(r.get("repository"), ()):
            bad.append(f"{where}: checked must be {' or '.join(CHECKED.get(r.get('repository'), ('?',)))} for "
                       f"{r.get('repository')}: a Lean core counterpart is checked by Lean "
                       "(Checks/Counterparts.lean), a Mathlib one from its source unless compiled "
                       "(Checks/MathlibCounterparts/)")
        sv, svs = r.get("section_variables"), r.get("section_variables_source")
        if bool(sv) != bool(svs) or (svs and (not SOURCE_RE.fullmatch(svs)
                                               or svs.rsplit(":", 1)[0] != src.rsplit(":", 1)[0])):
            bad.append(f"{where}: section_variables needs section_variables_source, a line of the same file")
        paths = r.get("iff_reversed_at", [])
        if r.get("iff_reversed") is not bool(paths):
            bad.append(f"{where}: iff_reversed must say whether iff_reversed_at is empty")
        try:
            ours = parse_formula(render(rows_by[e["lean"]], ctx["vocab"]))
            if parse_formula(r.get("pm_formula", "")) != ours:
                bad.append(f"{where}: pm_formula {r.get('pm_formula')} is not the statement exported now")
                continue
            schema = reverse_iffs(ours, paths)
            if parse_formula(r.get("statement", "")) != schema:
                bad.append(f"{where}: statement {r.get('statement')} is not the PM formula up to the recorded "
                           "iff reversals")
            bad += [f"{where}: {p}" for p in signature_problems(r, schema)]
        except (ValueError, KeyError) as x:
            bad.append(f"{where}: cannot read a formula ({x})")
    return bad


CHECKED = {"lean4": ("lean",), "mathlib4": ("source", "lean-mathlib")}


def check_bundle_names(entries, ctx):
    """Definition bundles (data/naming/definition_bundles.json): `PM_core_<words>`, lower-case ASCII with no
    dot, a valid platform definition name; one per source module, which exists; and unique, also ignoring
    case, among themselves and against every card's slug."""
    bad = []
    slugs = {e["slug"].lower(): e["export"] for e in entries}
    seen, mods = {}, set()
    for b in ctx["bundles"]["bundles"]:
        n, m = b.get("name", ""), b.get("module", "")
        if not BUNDLE_RE.fullmatch(n) or not re.fullmatch(r"[a-zA-Z_][a-zA-Z0-9_]*", n):
            bad.append(f"bundle {n!r}: not PM_core_<word>[_<word>]… in lower-case ASCII")
        if n.lower() in seen:
            bad.append(f"bundle {n}: also {seen[n.lower()]}")
        if n.lower() in slugs:
            bad.append(f"bundle {n}: the slug of {slugs[n.lower()]}")
        seen[n.lower()] = n
        if m in mods:
            bad.append(f"bundle {n}: a second bundle for {m}")
        mods.add(m)
        if not (ROOT / module_file(m)).exists():
            bad.append(f"bundle {n}: no module {m}")
        if not b.get("what"):
            bad.append(f"bundle {n}: says nothing about what it holds")
    return bad

LEAN_CHECK_HEAD = '''\
-- Lean decides whether each Lean core counterpart of data/naming/counterparts.json states PM's formula
-- (docs/NAMING.md, "Counterparts"). Written by scripts/export_names.py from that file and the statements
-- exported now; `python3 scripts/export_names.py --check` fails if it is out of date. Run from the
-- repository root with `lake env lean Checks/Counterparts.lean`; it needs Lean's core only.
--
-- For each record, PM's formula is a schema over propositional variables, translated connective for
-- connective (∼ `Not`, ∨ `Or`, ⊃ `→`, . `And`, ≡ `Iff`), with the sides of an equivalence swapped only
-- where the record says so. Then
--   `example : <schema> := @<declaration> <variables>`
-- is checked by the kernel, and
--   `#counterpart <declaration> [<variables>] "<signature>" : <schema>`
-- checks that the declaration's type prints as the recorded signature; that its first binders, one per
-- listed variable, are propositional variables (`Prop`, or `Sort u` only when marked `(specialized)`);
-- that the variables listed are distinct; and that its type so instantiated is the schema exactly, up to
-- the names of bound variables and `A → False` read as `¬A`: no unfolding, so a declaration that only
-- implies the schema, or states it up to definitional unfolding, fails.
import Lean

section
open Lean Elab Command Term Meta

/-- `e` with each `A → False` written `¬A`. -/
partial def Counterparts.normNot (e : Expr) : Expr :=
  e.replace fun
    | .forallE _ a (.const ``False []) _ => some (mkApp (.const ``Not []) (Counterparts.normNot a))
    | _ => none

/-- See the head of this file. -/
elab "#counterpart " spec:("(specialized) ")? d:ident " [" vs:ident,* "] " sig:str " : " s:term : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverload d
  let info ← getConstInfo c
  -- printed outside the section's variables, so that no bound name is renamed to avoid them
  let pp ← liftTermElabM do return toString (← ppExpr info.type)
  let ws (x : String) := " ".intercalate (x.splitOn " " |>.filter (· ≠ ""))
  unless ws pp == ws sig.getString do
    throwError "{c}: its type is{indentD pp}\\nnot the recorded signature{indentD sig.getString}"
  runTermElabM fun _ => do
    let vs := vs.getElems
    unless (vs.map (·.getId)).toList.eraseDups.length == vs.size do
      throwError "{c}: two of its variables are instantiated with the same variable"
    let general ← forallBoundedTelescope info.type vs.size fun xs _ => do
      unless xs.size == vs.size do throwError "{c}: fewer than {vs.size} binders"
      xs.mapM fun x => do
        match ← inferType x with
        | .sort .zero => pure false
        | .sort _ => pure true
        | t => throwError "{c}: its binder {x} : {t} is not a propositional variable"
    if general.any id != spec.isSome then
      throwError "{c}: {if spec.isSome then "marked (specialized) with no Sort parameter"
        else "a Sort parameter specialized to Prop, but the record does not say so"}"
    let schema ← elabType s
    let e ← elabTerm (← `(@$d $vs*)) none
    synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars (← inferType e)
    unless Counterparts.normNot ty == Counterparts.normNot schema do
      throwError "{c}: instantiated, it states{indentExpr ty}\\nnot PM's formula{indentExpr schema}"

end
'''


def counterpart_blocks(entries, ctx, checked):
    """For each counterpart checked `checked`: (record, PM's formula as a Lean schema with the recorded iff
    reversals, its variables)."""
    rows_by = {r["name"]: r for r in ctx["rows"]}
    by = {e["export"]: e for e in entries}
    out = []
    for r in ctx["counterparts"]["counterparts"]:
        e = by.get(r.get("export"))
        if r.get("checked") != checked or e is None:
            continue
        schema = reverse_iffs(parse_formula(render(rows_by[e["lean"]], ctx["vocab"])), r.get("iff_reversed_at", []))
        out.append((r, lean_formula(schema), leaves(schema)))
    return out


def counterparts_lean(entries, ctx):
    """The text of Checks/Counterparts.lean: every counterpart checked "lean" (docs/NAMING.md)."""
    blocks, names = [], set()
    for r, f, vs_used in counterpart_blocks(entries, ctx, "lean"):
        names |= vs_used
        vs = " ".join(r.get("instantiation") or [])
        sig = json.dumps(r.get("signature", ""), ensure_ascii=False)
        spec = "(specialized) " if r.get("specialized") else ""
        blocks.append(f"-- {r['pm'].replace('*', '✱').replace('.', '·')} {r['export']}: {r['declaration']}, "
                      f"{r['source']}\n"
                      f"example : {f} := @{r['declaration']} {vs}\n"
                      f"#counterpart {spec}{r['declaration']} [{', '.join(r.get('instantiation') or [])}] {sig} : {f}")
    return (LEAN_CHECK_HEAD + f"\nvariable ({' '.join(sorted(names))} : Prop)\n\n" + "\n\n".join(blocks)
            + f'\n\n#eval IO.println "counterparts: {len(blocks)} checked by Lean"\n')


# The Mathlib counterparts' check: the same `#counterpart` as Checks/Counterparts.lean but for the printed
# signature (a Mathlib record's signature is its header in the source, checked by --verify-counterparts),
# and `#classical`, which checks the record's `classical` against the axioms the proof uses.
MATHLIB_CHECK_HEAD = '''\
-- Lean decides whether each Mathlib counterpart of data/naming/counterparts.json checked "lean-mathlib"
-- states PM's formula (docs/NAMING.md, "Counterparts"), against Mathlib at the commit the records pin.
-- Written by scripts/export_names.py from that file and the statements exported now;
-- `python3 scripts/export_names.py --check` fails if it is out of date. A Lake project of its own, so the
-- repository's `lake build` needs no Mathlib: run by scripts/release_check.sh, or by hand from
-- Checks/MathlibCounterparts/ with `lake exe cache get` and then `lake env lean MathlibCounterparts.lean`.
--
-- As in Checks/Counterparts.lean, PM's formula is a schema over propositional variables, translated
-- connective for connective, with the sides of an equivalence swapped only where the record says so. Then
--   `example : <schema> := @<declaration> <variables>`
-- is checked by the kernel, and
--   `#counterpart <declaration> [<variables>] : <schema>`
-- checks that its first binders, one per listed variable, are propositional variables (`Prop`, or
-- `Sort u` only when marked `(specialized)`); that the variables listed are distinct; and that its type
-- so instantiated is the schema exactly, up to the names of bound variables and `A → False` read as `¬A`.
-- The recorded signature is the declaration's header in Mathlib's source, which
-- `scripts/export_names.py --verify-counterparts` compares with the pinned file. Last,
--   `#classical <declaration> <true|false>`
-- checks the record's `classical`: whether the axioms of the declaration's proof include
-- `Classical.choice`.
'''

ELAB_TAIL = LEAN_CHECK_HEAD[LEAN_CHECK_HEAD.index("  runTermElabM fun _ => do"):LEAN_CHECK_HEAD.index("\nend\n")]

MATHLIB_ELABS = '''
section
open Lean Elab Command Term Meta

/-- `e` with each `A → False` written `¬A`. -/
partial def Counterparts.normNot (e : Expr) : Expr :=
  e.replace fun
    | .forallE _ a (.const ``False []) _ => some (mkApp (.const ``Not []) (Counterparts.normNot a))
    | _ => none

/-- See the head of this file. -/
elab "#counterpart " spec:("(specialized) ")? d:ident " [" vs:ident,* "]" " : " s:term : command => do
  -- the record's name is the full name, so it is not resolved against open namespaces (`not_imp_self`,
  -- not `Decidable.not_imp_self`)
  let c := d.getId
  let info ← getConstInfo c
  let d := mkIdent (rootNamespace ++ c)
''' + ELAB_TAIL + '''
/-- See the head of this file. -/
elab "#classical " d:ident b:ident : command => do
  let c := d.getId
  discard <| getConstInfo c
  let axs ← liftCoreM <| collectAxioms c
  let uses := axs.contains ``Classical.choice
  unless b.getId == (if uses then `true else `false) do
    throwError "{c}: its proof uses the axioms {axs.toList}, so classical is {uses}, not {b.getId}"

end
'''


def mathlib_counterparts_lean(entries, ctx):
    """The text of Checks/MathlibCounterparts/MathlibCounterparts.lean: every counterpart checked
    "lean-mathlib" (docs/NAMING.md), with the Mathlib modules that declare them."""
    blocks, names, mods = [], set(), set()
    for r, f, vs_used in counterpart_blocks(entries, ctx, "lean-mathlib"):
        names |= vs_used
        mods.add(r["source"].rsplit(":", 1)[0].removesuffix(".lean").replace("/", "."))
        vs = " ".join(r.get("instantiation") or [])
        spec = "(specialized) " if r.get("specialized") else ""
        blocks.append(f"-- {r['pm'].replace('*', '✱').replace('.', '·')} {r['export']}: {r['declaration']}, "
                      f"{r['source']}\n"
                      f"example : {f} := @{r['declaration']} {vs}\n"
                      f"#counterpart {spec}{r['declaration']} [{', '.join(r.get('instantiation') or [])}] : {f}\n"
                      f"#classical {r['declaration']} {'true' if r['classical'] else 'false'}")
    commit = ctx["counterparts"]["repositories"]["mathlib4"]["commit"]
    return (MATHLIB_CHECK_HEAD + "".join(f"import {m}\n" for m in sorted(mods)) + MATHLIB_ELABS
            + f"\nvariable ({' '.join(sorted(names))} : Prop)\n\n" + "\n\n".join(blocks)
            + f'\n\n#eval IO.println "Mathlib counterparts: {len(blocks)} checked by Lean against Mathlib '
            f'{commit[:7]}"\n')


def signature_problems(r, schema):
    """The declaration's own type (its signature, read strictly), its variables instantiated as recorded,
    against PM's formula with the recorded iff reversals: the criterion of docs/NAMING.md."""
    try:
        binders, body = parse_signature(r.get("signature", ""), r.get("section_variables", ""))
    except ValueError as x:
        return [f"signature is not a type of the propositional fragment ({x})"]
    inst = r.get("instantiation")
    if (not isinstance(inst, list) or len(inst) != len(binders) or len(set(inst)) != len(inst)
            or not all(isinstance(v, str) and re.fullmatch(r"[a-z]", v) for v in inst)):
        return [f"instantiation {inst} must give a different PM variable to each of its "
                f"{len(binders)} variables {[n for n, _ in binders]}"]
    out = []
    general = [n for n, s in binders if s == "Sort"]
    if bool(general) != bool(r.get("specialized")):
        out.append(f"specialized is {r.get('specialized')}, but its Sort parameters are {general or 'none'}")
    stated = substitute(body, dict(zip([n for n, _ in binders], inst)))
    if stated != schema:
        out.append(f"{r.get('declaration')} instantiated as recorded states {lean_formula(stated)}, not PM's "
                   f"formula {lean_formula(schema)} (with the recorded iff reversals {r.get('iff_reversed_at')})")
    return out


CHECKS = {"pattern": check_pattern, "suffix_order": check_suffix_order, "pm_name_only": check_pm_name_only,
          "slots": check_slots, "readings": check_readings, "readings_frozen": check_readings_frozen,
          "unique_name": check_unique_name, "unique_slug": check_unique_slug, "no_top_level": check_no_top_level,
          "no_checks": check_no_checks, "vocabulary": check_vocabulary, "lock": check_lock, "versions": check_versions,
          "counterparts": check_counterparts, "bundle_names": check_bundle_names}


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
            "changes": read_tsv(CHANGES, CHANGES_COLUMNS), "rows": rows, "bundles": load(BUNDLES)}


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


def write_lock(entries, ctx, lock=LOCK, readings_lock=READINGS_LOCK, all_readings=True):
    """At a release: each name of `entries` with its Lean declaration, reading and digests, and each
    reading's word and meaning: every reading, or with all_readings=False only those the locked names use.
    Names and readings already locked stay; new ones are added."""
    head =["# Released export names (docs/VERSIONING.md): each name with the Lean declaration it was",
            "# released from, its reading, and the digests of its statement and of the definitions it",
            "# uses. Rows are only ever added. Written by scripts/export_names.py --write-lock.",
            "\t".join(LOCK_COLUMNS)]
    rows = lock_rows(entries, ctx)
    lock.write_text("\n".join(head + ["\t".join(r[c] for c in LOCK_COLUMNS) for r in rows]) + "\n",
                    encoding="utf-8")
    rl = dict(ctx["readings_lock"])
    used = {r["reading"] for r in rows}
    for tag, r in ctx["readings"].items():
        if all_readings or r["word"] in used:
            rl.setdefault(tag, {"word": r["word"], "meaning": r["meaning"]})
    readings_lock.write_text(json.dumps(rl, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")


def merkle_root(rows):
    """The Merkle root of released names (docs/VERSIONING.md): the Merkle Tree Hash of RFC 6962 (Certificate
    Transparency) over one leaf per name, `<export>\t<statement_digest>\t<definitions_digest>` in UTF-8,
    sorted by export name; a leaf is hashed as SHA-256(0x00 ‖ leaf), two subtrees as SHA-256(0x01 ‖ left ‖
    right), and a tree of n > 1 leaves splits after the largest power of two less than n."""
    leaves = sorted(f"{r['export']}\t{r['statement_digest']}\t{r['definitions_digest']}" for r in rows)
    return merkle_tree_hash([x.encode("utf-8") for x in leaves]).hex()


def merkle_tree_hash(leaves):
    """RFC 6962, section 2.1, for a list of byte strings (the hash of the empty list is SHA-256 of nothing)."""
    if not leaves:
        return hashlib.sha256(b"").digest()
    if len(leaves) == 1:
        return hashlib.sha256(b"\x00" + leaves[0]).digest()
    k = 1
    while k * 2 < len(leaves):
        k *= 2
    return hashlib.sha256(b"\x01" + merkle_tree_hash(leaves[:k]) + merkle_tree_hash(leaves[k:])).digest()


def verify_counterparts(ctx, base):
    """Each counterpart's file:line, in a checkout `base/<repository>-<commit>`, names the declaration (or,
    for a structure's constructor such as And.intro, declares the structure, as Lean's declaration
    ranges do). For a Mathlib counterpart (checked from its source, or compiled), the declaration's header
    there (from its line to `:=`) is the recorded signature, and its section's `variable` line the recorded
    one, up to whitespace."""
    def ws(s):
        return " ".join(s.split())

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
            continue
        if r["checked"] not in ("source", "lean-mathlib"):
            continue
        header = "\n".join(text[int(line) - 1:int(line) + 20]).split(":=", 1)[0]
        if ws(header) != ws(r["signature"]):
            bad.append(f"{r['pm']} {r['declaration']}: {r['source']} declares {ws(header)!r}, not the recorded "
                       f"signature {r['signature']!r}")
        if r.get("section_variables"):
            vline = int(r["section_variables_source"].rsplit(":", 1)[1])
            if vline > len(text) or ws(text[vline - 1]) != ws(r["section_variables"]):
                bad.append(f"{r['pm']} {r['declaration']}: {r['section_variables_source']} is not "
                           f"{r['section_variables']!r}")
            # the declaration is in that variable's section: no `end` closes it in between
            if vline >= int(line) or any(re.match(r"end\b", t) for t in text[vline:int(line) - 1]):
                bad.append(f"{r['pm']} {r['declaration']}: {r['section_variables_source']} is not in scope at "
                           f"{r['source']}")
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


def select_chapters(entries, chapters=None):
    """The entries of ✱a–✱b, and the results about the system when ✱1 is in the range."""
    lo, hi = chapters or (0, 10 ** 6)
    return [e for e in entries
            if (e.get("meta") and lo <= 1 <= hi) or (e["pm"] and lo <= int(e["pm"][1:].split(".")[0]) <= hi
                                                     and not e.get("meta"))]


def write_tsv(entries, ctx, path, chapters=None):
    sel = select_chapters(entries, chapters)
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
    generated = ((OUT, text), (COUNTERPARTS_LEAN, counterparts_lean(entries, ctx)),
                 (MATHLIB_COUNTERPARTS_LEAN, mathlib_counterparts_lean(entries, ctx)))
    failed = False
    if "--check" in args:
        for path, want in generated:
            if not path.exists() or path.read_text(encoding="utf-8") != want:
                print(f"{path.relative_to(ROOT)} is not up to date: run python3 scripts/export_names.py")
                failed = True
        checked = json.loads(OUT.read_text(encoding="utf-8")) if OUT.exists() else []
    else:
        for path, want in generated:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(want, encoding="utf-8")
        checked = entries
    problems = check(checked, ctx)
    problems["heads"] = [f"no word for {c} in data/naming/vocabulary.json" for c in unknown]
    if "--verify-counterparts" in args:
        problems["counterpart_sources"] = verify_counterparts(ctx, args[args.index("--verify-counterparts") + 1])
    for k, v in problems.items():
        for p in v:
            print(f"{k}: {p}")
        failed |= bool(v)
    ch = None
    if "--chapters" in args:
        a, b = args[args.index("--chapters") + 1].split("-")
        ch = (int(a), int(b))
    if "--write-lock" in args and not failed:
        write_lock(select_chapters(entries, ch), ctx, all_readings=ch is None)
        print("wrote data/export_names.lock and data/naming/readings.lock"
              + (f" for ✱{ch[0]}–✱{ch[1]} and the results about the system" if ch else ""))
    if "--root" in args:
        root = merkle_root(read_tsv(LOCK, LOCK_COLUMNS))
        print(f"Merkle root of data/export_names.lock: {root}; build metadata m.{root[:12]}")
    if "--tsv" in args:
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
