#!/usr/bin/env python3
"""Export PM's ✱1–✱5 to Prove2Me (https://prove2.me): the files of the platform, from a commit of this
repository. No credentials and no network: uploading is a separate step, not in this repository.

    Definitions/Def_<bundle>.lean   one bundle of definitions per source module (data/naming/definition_bundles.json)
    Theorems/Thm_<slug>.lean        one card per statement, `theorem <export name> … := by sorry`
    Solutions/Sol_<slug>.lean       the card's proof, as a top-level `theorem solution`
    manifest.json                   what an uploader needs: names, preambles, statements, dependency edges, links

Card names are the export names of data/export_names.json (docs/NAMING.md); the slug is the name with `.`
replaced by `_`, as the platform names a module.

Method: Prove2Me's references/upload_full_project.md ("skeleton subtraction"). Every fact about the Lean
code comes from Lean, not from searching the text:

    Stage 1   Prove2Me's scripts/extract_decl_graph.lean   declarations, kinds, typeDeps/valueDeps
    Stage 2   Prove2Me's scripts/extract_sketch_info.lean  declaration spans, proof start, docstring, every
                                                           reference to a constant of the project
    Stage 2b  scripts/prove2me/extract_commands.lean        every top-level command and its syntax kind; the
                                                           constructors of an inductive type

Prove2Me's two scripts are not copied here: pass a checkout of github.com/prove2me/prove2me_workspace at
the commit of config.json with --platform-scripts.

Each generated file is the source file with the unselected commands deleted; the commands kept are copied
byte for byte. The only edits, each at a range Lean reported:
  - import lines, rewritten to the platform's modules;
  - a statement is cut at its proof (Stage 2's `valStart`), and its docstring is cut (the platform drops a
    declaration with a leading docstring);
  - the declared name: the export name in a statement, `solution` in a solution;
  - a reference to another card's declaration, renamed to that card's export name (`t2_05` becomes
    `PM.star2_05_syll`), since the platform knows the card by its export name only;
  - with `expand_macros`, each use of one of the repository's tactic macros is replaced by the macro's own
    expansion in parentheses (the platform refuses `macro` in a submission; a macro naming theorems cannot go
    in a bundle, which comes before the theorems).

Classification (upload_full_project.md, Phase 2), with one project-level rule: every target is a card,
whatever its proof length (config.json `targets`: PM's numbering is the decomposition). Every other
reachable theorem is an inline helper, pasted into each solution that needs it; every reachable definition
goes into its module's bundle. ✱1·2–✱1·6 are the constructors of `PM.Thm`, not theorems: their cards state
each constructor's binders and type as declared in PM/Basic.lean, and are proved by the constructor.

Everything is read from the commit exported (`git archive`), built with the platform's toolchain in a copy:
the generated links name that commit, and the files are what that commit says.

Usage (from the repository root):
    python3 scripts/prove2me/export.py all --platform-scripts DIR [--commit REF] [--work DIR]
    (or one stage: extract | plan | generate)
The work directory defaults to .lake/prove2me (ignored by git); the tree is written to <work>/out.
Then scripts/prove2me/metadata.py writes titles and descriptions, and scripts/prove2me/verify.py checks the
tree with the platform's Lean.
"""
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import time
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
CONFIG = os.path.join(HERE, "config.json")


# ----------------------------------------------------------------------------- setup

def args_of(argv):
    a = {"stage": argv[0] if argv else None, "commit": "HEAD", "work": os.path.join(ROOT, ".lake", "prove2me"),
         "platform_scripts": None}
    i = 1
    while i < len(argv):
        k = argv[i].lstrip("-").replace("-", "_")
        if k not in a or i + 1 >= len(argv):
            raise SystemExit(__doc__)
        a[k] = argv[i + 1]
        i += 2
    if a["stage"] not in ("extract", "plan", "generate", "all"):
        raise SystemExit(__doc__)
    a["work"] = os.path.abspath(a["work"])
    return a


def load_config():
    return json.load(open(CONFIG, encoding="utf-8"))


def paths(work):
    return {"repo": os.path.join(work, "repo"), "facts": os.path.join(work, "facts"),
            "out": os.path.join(work, "out")}


def run(cmd, cwd, log=None, timeout=7200):
    t = time.time()
    r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    if log is not None:
        log.append({"cmd": " ".join(os.path.basename(c) if os.path.isabs(c) else c for c in cmd),
                    "rc": r.returncode, "seconds": round(time.time() - t, 2)})
    if r.returncode != 0:
        raise SystemExit(f"command failed ({r.returncode}): {' '.join(cmd)}\n{r.stdout[-3000:]}\n{r.stderr[-3000:]}")
    return r.stdout


def module_file(repo, mod):
    return os.path.join(repo, *mod.split(".")) + ".lean"


# ----------------------------------------------------------------------------- extract

def cmd_extract(cfg, a):
    P = paths(a["work"])
    if not a["platform_scripts"]:
        raise SystemExit("--platform-scripts DIR: a checkout of " + cfg["platform_scripts"]["repository"])
    ps = a["platform_scripts"]
    want = cfg["platform_scripts"]["commit"]
    got = subprocess.run(["git", "-C", ps, "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    if got != want:
        raise SystemExit(f"{ps} is at {got or 'no git commit'}, not {want} (config.json platform_scripts)")
    for f in cfg["platform_scripts"]["files"]:
        if subprocess.run(["git", "-C", ps, "diff", "--quiet", want, "--", f]).returncode != 0:
            raise SystemExit(f"{ps}/{f} differs from the pinned commit")
    commit = run(["git", "rev-parse", a["commit"] + "^{commit}"], ROOT).strip()
    log = []
    # the commit, as a copy built with the platform's toolchain
    shutil.rmtree(a["work"], ignore_errors=True)
    os.makedirs(P["facts"])
    tar = subprocess.run(["git", "archive", "--format=tar", commit], cwd=ROOT, capture_output=True, check=True).stdout
    with tarfile.open(fileobj=io.BytesIO(tar)) as t:
        t.extractall(P["repo"], filter="data")
    open(os.path.join(P["repo"], "lean-toolchain"), "w").write(cfg["environment"]["toolchain"] + "\n")
    run(["lake", "build"] + cfg["modules"], P["repo"], log)
    # Stage 1, with the playbook's two EDIT lines filled in (+ `import Lean`: a project without Mathlib does
    # not get the meta API transitively)
    src = open(os.path.join(ps, "scripts", "extract_decl_graph.lean"), encoding="utf-8").read()
    imports = "\n".join(f"import {m}" for m in cfg["modules"]) + "\nimport Lean"
    src2 = re.sub(r"^import SumSquares$", lambda _: imports, src, count=1, flags=re.M)
    src2 = src2.replace("let projPrefix := `SumSquares", f"let projPrefix := `{cfg['project_prefix']}")
    assert imports in src2 and f"`{cfg['project_prefix']}" in src2, "Stage 1 EDIT lines not found"
    open(os.path.join(P["repo"], "extract_decl_graph.lean"), "w", encoding="utf-8").write(src2)
    run(["lake", "env", "lean", "extract_decl_graph.lean"], P["repo"], log)
    shutil.move(os.path.join(P["repo"], "decl_graph.jsonl"), os.path.join(P["facts"], "decl_graph.jsonl"))
    os.remove(os.path.join(P["repo"], "extract_decl_graph.lean"))
    # Stage 2 and 2b on every module
    sk = os.path.join(ps, "scripts", "extract_sketch_info.lean")
    cm = os.path.join(P["repo"], "scripts", "prove2me", "extract_commands.lean")    # the commit's own tool
    for m in cfg["modules"]:
        f = module_file(P["repo"], m)
        out = run(["lake", "env", "lean", "--run", sk, f, cfg["project_prefix"]], P["repo"], log)
        open(os.path.join(P["facts"], f"sk_{m}.jsonl"), "w", encoding="utf-8").write(out)
        out = run(["lake", "env", "lean", "--run", cm, f, cfg["project_prefix"]], P["repo"], log)
        open(os.path.join(P["facts"], f"cmd_{m}.jsonl"), "w", encoding="utf-8").write(out)
    lean = run(["lake", "env", "lean", "--version"], P["repo"]).strip()
    json.dump({"commit": commit, "lean": lean, "platform_scripts": got, "log": log},
              open(os.path.join(P["facts"], "extract_meta.json"), "w"), indent=1)
    print(f"extract: commit {commit}, {lean}, {len(log)} runs")


# ----------------------------------------------------------------------------- facts

class Facts:
    """Everything Stages 1, 2 and 2b said, joined."""

    def __init__(self, cfg, work):
        P = paths(work)
        self.cfg, self.repo = cfg, P["repo"]
        fd = P["facts"]
        self.rows = [json.loads(l) for l in open(os.path.join(fd, "decl_graph.jsonl")) if l.strip()]
        self.by = {r["name"]: r for r in self.rows}
        self.meta = json.load(open(os.path.join(fd, "extract_meta.json")))
        self.mods = list(cfg["modules"])
        self.text, self.decls, self.refs, self.cmds = {}, {}, {}, {}
        for m in self.mods:
            self.text[m] = open(module_file(self.repo, m), "rb").read()
            sk = [json.loads(l) for l in open(os.path.join(fd, f"sk_{m}.jsonl")) if l.strip()]
            self.decls[m] = [x for x in sk if x["kind"] == "decl"]
            self.refs[m] = [x for x in sk if x["kind"] == "ref"]
            cm = sorted((json.loads(l) for l in open(os.path.join(fd, f"cmd_{m}.jsonl")) if l.strip()),
                        key=lambda c: c["start"]["offset"])
            n = len(self.text[m])
            for i, c in enumerate(cm):
                c["xstart"] = c["start"]["offset"] if i else 0          # a leading file comment rides with cmd 0
                c["xend"] = cm[i + 1]["start"]["offset"] if i + 1 < len(cm) else n
            self.cmds[m] = cm
        # join: graph row -> decl fact (containment of startLine), decl fact -> command (same start)
        self.decl_of = {}
        for r in self.rows:
            if r["startLine"] == 0 or r["module"] not in self.decls:
                continue
            hits = [d for d in self.decls[r["module"]] if d["declStart"]["line"] <= r["startLine"] <= d["declEnd"]["line"]]
            if len(hits) == 1:
                self.decl_of[r["name"]] = hits[0]
        for m in self.mods:
            starts = {c["start"]["offset"]: c for c in self.cmds[m]}
            for d in self.decls[m]:
                d["cmd"] = starts.get(d["declStart"]["offset"])
                assert d["cmd"] is not None, f"declaration without a command in {m}: {d}"
        self.imports = {}
        for m in self.mods:
            h = [c for c in self.cmds[m] if c["syntaxKind"] == "header"]
            toks = self.text[m][h[0]["start"]["offset"]:h[0]["end"]["offset"]].decode().split() if h else []
            self.imports[m] = [toks[i + 1] for i, t in enumerate(toks) if t == "import"]

    def proj_imports(self, m):
        return [i for i in self.imports[m] if i in self.mods]

    def closure(self, m):
        seen, todo = [], [m]
        while todo:
            for i in self.proj_imports(todo.pop()):
                if i not in seen:
                    seen.append(i)
                    todo.append(i)
        return seen

    def topo_modules(self):
        order, done = [], set()

        def visit(m):
            if m in done:
                return
            done.add(m)
            for i in self.proj_imports(m):
                visit(i)
            order.append(m)
        for m in self.mods:
            visit(m)
        return order

    def nonproject_imports(self, m):
        out = []
        for x in [m] + self.closure(m):
            out += [i for i in self.imports[x] if i not in self.mods and not i.startswith(self.cfg["project_prefix"] + ".")]
        return sorted(set(out))

    def line_count(self, name):
        d = self.decl_of[name]
        return d["declEnd"]["line"] - (d["valStart"] or d["declStart"])["line"]

    def ctor(self, name):
        """(module, inductive command, constructor fact) of a constructor `PM.Thm.taut`."""
        ind, short = name.rsplit(".", 1)
        m = self.by[ind]["module"]
        for c in self.cmds[m]:
            for k in c.get("ctors", []):
                if k["name"] == short and self.decl_of.get(ind, {}).get("cmd") is c:
                    return m, c, k
        raise SystemExit(f"constructor {name} not found")


def export_entries(repo, cfg):
    """The export names of the cards of this export (data/export_names.json of the commit exported): the
    statements of chapters ✱a–✱b and the results about the system."""
    lo, hi = cfg["chapters"]
    es = json.load(open(os.path.join(repo, "data", "export_names.json"), encoding="utf-8"))
    return [e for e in es if e.get("meta") or lo <= int(e["pm"][1:].split(".")[0]) <= hi]


def bundle_names(repo):
    doc = json.load(open(os.path.join(repo, "data", "naming", "definition_bundles.json"), encoding="utf-8"))
    return {b["module"]: b["name"] for b in doc["bundles"]}


# ----------------------------------------------------------------------------- plan

def cmd_plan(cfg, a):
    F = Facts(cfg, a["work"])
    by = F.by
    tg = cfg["targets"]
    targets = [r["name"] for r in F.rows if r["kind"] == "theorem" and r["startLine"] > 0
               and (r["module"] in tg["modules"] or r["name"] in tg["names"])]
    for n in tg["names"] + tg["constructors"]:
        assert n in by, f"target {n} is not in the graph"
    # every card of this export is a target, and every target has an export name
    entries = export_entries(F.repo, cfg)
    want = {e["lean"] for e in entries}
    have = set(targets) | set(tg["constructors"])
    assert want == have, f"targets without an export name: {sorted(have - want)}; names without a target: {sorted(want - have)}"
    # reachability (typeDeps ∪ valueDeps), inductives -> constructors, instances as roots
    ctors = defaultdict(list)
    for r in F.rows:
        if r["kind"] == "ctor":
            ctors[r["name"].rsplit(".", 1)[0]].append(r["name"])
    roots = list(targets) + list(tg["constructors"]) + [r["name"] for r in F.rows if r["isInstance"] and r["module"] in F.mods]
    reach, todo = set(), list(roots)
    while todo:
        n = todo.pop()
        if n in reach or n not in by:
            continue
        reach.add(n)
        r = by[n]
        todo += r["typeDeps"] + r["valueDeps"]
        if r["kind"] == "inductive":
            todo += ctors[n]
        if r["kind"] == "ctor":
            todo.append(n.rsplit(".", 1)[0])
    spanned = {n for n in reach if by[n]["startLine"] > 0}
    defmat = {n for n in spanned if by[n]["kind"] in ("def", "inductive", "opaque", "axiom")}
    thms = {n for n in spanned if by[n]["kind"] == "theorem"}
    decl_id = lambda n: id(F.decl_of.get(n))
    def_decl_ids = {decl_id(n) for n in defmat}
    thms = {n for n in thms if decl_id(n) not in def_decl_ids}
    embedded, todo = set(), [d for n in defmat for d in by[n]["valueDeps"] if d in thms]
    while todo:
        n = todo.pop()
        if n in embedded:
            continue
        embedded.add(n)
        todo += [d for d in by[n]["valueDeps"] if d in thms]
    thms -= embedded
    TH = cfg["thresholds"]
    reason = {t: "target" for t in targets}

    def signals(n, nodes):
        users = [u for u in nodes if n in by[u]["valueDeps"]]
        cross = any(by[u]["module"] != by[n]["module"] for u in thms if n in by[u]["valueDeps"])
        return len(users) >= 2 or cross or F.decl_of[n].get("docstring") is not None
    changed = True
    while changed:
        changed = False
        nodes = set(reason)
        for n in sorted(thms - nodes):
            if by[n]["isPrivate"]:
                continue
            lc = F.line_count(n)
            if lc > TH["node_lines"] or (lc > TH["inline_lines"] and signals(n, nodes)):
                reason[n] = f"line rule ({lc} lines)"
                changed = True
    nodes = set(reason)
    extra = sorted(nodes - want)
    assert not extra, f"theorems the line rule would make cards, with no export name: {extra}"
    helpers = thms - nodes
    for n in nodes:
        bad = [d for d in by[n]["typeDeps"] if d in helpers or (d in by and by[d]["isPrivate"] and d not in defmat)]
        assert not bad, f"the statement of {n} needs {bad}, which cannot be imported"
    plan_nodes = {}
    for n in sorted(nodes):
        hs, deps, todo = set(), set(), list(by[n]["valueDeps"])
        while todo:
            d = todo.pop()
            if d in nodes and d != n:
                deps.add(d)
            elif d in helpers and d not in hs:
                hs.add(d)
                todo += by[d]["valueDeps"] + by[d]["typeDeps"]
        plan_nodes[n] = {"module": by[n]["module"], "reason": reason[n], "helpers": sorted(hs),
                         "node_deps": sorted(deps), "proof_lines": F.line_count(n)}
    names = bundle_names(F.repo)
    bundles = {}
    for m in F.topo_modules():
        own = sorted(n for n in defmat | embedded if by[n]["module"] == m)
        if own:
            assert m in names, f"{m} has definitions but no bundle name in data/naming/definition_bundles.json"
            bundles[m] = {"name": names[m], "decls": own}
    unused = sorted(set(names) - set(bundles))
    assert not unused, f"bundle names for modules with no definitions to export: {unused}"
    for m, b in bundles.items():
        b["imports"] = [bundles[x]["name"] for x in F.topo_modules() if x in bundles and x in F.closure(m)]
    order, done = [], set()

    def visit(n):
        if n in done:
            return
        done.add(n)
        for d in plan_nodes[n]["node_deps"]:
            visit(d)
        order.append(n)
    for n in sorted(nodes, key=lambda n: (F.topo_modules().index(by[n]["module"]), by[n]["startLine"])):
        visit(n)
    plan = {
        "commit": F.meta["commit"],
        "counts": {"graph_rows": len(F.rows), "reachable_spanned": len(spanned), "definitions_decls": len(defmat),
                   "definition_bundles": len(bundles), "def_embedded_theorems": len(embedded),
                   "theorem_cards": len(nodes), "constructor_cards": len(tg["constructors"]),
                   "inline_helpers": len(helpers)},
        "dead_theorems": sorted(r["name"] for r in F.rows if r["kind"] == "theorem" and r["startLine"] > 0
                                and r["name"] not in spanned),
        "bundles": bundles, "embedded": sorted(embedded), "helpers": sorted(helpers),
        "constructors": list(tg["constructors"]), "nodes": plan_nodes, "order": order,
    }
    json.dump(plan, open(os.path.join(paths(a["work"])["facts"], "plan.json"), "w"), indent=1, ensure_ascii=False)
    print("plan: " + json.dumps(plan["counts"]))
    return plan


# ----------------------------------------------------------------------------- generate

SCOPE_KINDS = {"Lean.Parser.Command.namespace", "Lean.Parser.Command.end", "Lean.Parser.Command.section",
               "Lean.Parser.Command.open", "Lean.Parser.Command.variable", "Lean.Parser.Command.universe",
               "Lean.Parser.Command.set_option"}
NOTATION_KINDS = {"Lean.Parser.Command.notation", "Lean.Parser.Command.macro", "Lean.Parser.Command.syntax",
                  "Lean.Parser.Command.macro_rules", "Lean.Parser.Command.mixfix",
                  "Lean.Parser.Command.elab", "Lean.Parser.Command.elab_rules", "Lean.Parser.Command.notation3"}


def classify_cmd(c):
    """scope: kept in every skeleton; bundle: kept in the module's bundle only; decl: kept iff selected;
    drop: never."""
    k = c["syntaxKind"]
    if k == "header":
        return "drop"
    if k in SCOPE_KINDS:
        return "scope"
    if k in NOTATION_KINDS:
        return "scope" if c["isLocal"] else "bundle"
    if k == "Lean.Parser.Command.moduleDoc":
        return "bundle"
    if k == "Lean.Parser.Command.declaration":
        return "bundle" if c["innerKind"] == "Lean.Parser.Command.example" else "decl"
    if k == "Lean.Parser.Command.attribute":
        return "bundle"
    raise SystemExit(f"unclassified command kind {k}: add it to scripts/prove2me/export.py")


class Gen:
    def __init__(self, cfg, plan, work):
        self.cfg, self.plan = cfg, plan
        self.F = F = Facts(cfg, work)
        self.commit = plan["commit"]
        self.entries = {e["lean"]: e for e in export_entries(F.repo, cfg)}
        # the cards' declarations, renamed in solutions to their export names (constructors are not)
        self.rename = {n: self.entries[n]["export"] for n in plan["nodes"]}
        self.decl_by_start = {m: {d["declStart"]["offset"]: d for d in F.decls[m]} for m in F.mods}
        self.names_of = defaultdict(list)
        for n, d in F.decl_of.items():
            self.names_of[id(d)].append(n)
        self.in_bundle = {n for b in plan["bundles"].values() for n in b["decls"]}
        self.macro_body = {}
        for m in F.mods:
            for c in F.cmds[m]:
                if c["syntaxKind"] == "Lean.Parser.Command.macro" and c.get("quotBody"):
                    body = self.cut(m, c["quotBody"]["start"]["offset"], c["quotBody"]["end"]["offset"])
                    for r in F.rows:
                        if r["module"] == m and c["start"]["line"] <= r["startLine"] <= c["end"]["line"]:
                            self.macro_body[r["name"]] = body
        self.n_expanded = self.n_renamed = 0

    def export(self, n):
        return self.entries[n]["export"]

    def slug(self, n):
        return self.entries[n]["slug"]

    def cut(self, m, a, b):
        return self.F.text[m][a:b].decode()

    def expand_cuts(self, m, c, a, b):
        """Each use of a project macro inside [a, b) of command c, replaced by its expansion in parentheses."""
        if not self.cfg.get("expand_macros"):
            return []
        cuts = []
        for u in c.get("userSyntax", []):
            s, e = u["range"]["start"]["offset"], u["range"]["end"]["offset"]
            if a <= s and e <= b and u["kind"] in self.macro_body:
                cuts.append((s, e, "(" + self.macro_body[u["kind"]] + ")"))
        self.n_expanded += len(cuts)
        return cuts

    def rename_cuts(self, m, a, b, skip=None):
        """Each reference inside [a, b) to another card's declaration, renamed to its export name."""
        cuts = []
        for r in self.F.refs[m]:
            s, e = r["start"]["offset"], r["end"]["offset"]
            if a <= s and e <= b and r["const"] in self.rename and (s, e) != skip:
                cuts.append((s, e, self.rename[r["const"]]))
        self.n_renamed += len(cuts)
        return cuts

    def apply_cuts(self, m, a, b, cuts):
        cuts = sorted(set(cuts))
        for (s1, e1, _), (s2, e2, _) in zip(cuts, cuts[1:]):
            assert e1 <= s2, f"overlapping edits in {m} at {s1}-{e1} and {s2}-{e2}"
        txt = self.F.text[m][a:b]
        for s, e, rep in reversed(cuts):
            txt = txt[:s - a] + rep.encode() + txt[e - a:]
        return txt.decode()

    def binding_ref(self, m, name, d):
        a, b = d["declStart"]["offset"], (d["valStart"] or d["declEnd"])["offset"]
        hits = [r for r in self.F.refs[m] if r["const"] == name and a <= r["start"]["offset"] < b]
        assert hits, f"no binding occurrence of {name}"
        return min(hits, key=lambda r: r["start"]["offset"])

    def decl_selected(self, m, c, keep):
        d = self.decl_by_start[m].get(c["start"]["offset"])
        return d is not None and any(n in keep for n in self.names_of[id(d)])

    def example_ok(self, m, c, available):
        refs = [r["const"] for r in self.F.refs[m] if c["start"]["offset"] <= r["start"]["offset"] < c["end"]["offset"]]
        return all(r in available for r in refs)

    def theorem_refs(self, c, frames):
        prefixes = [""] + [f["full"] + "." for f in frames if f["kind"] == "namespace"]
        refs = set()
        for i in c.get("idents", []):
            for p in prefixes:
                r = self.F.by.get(p + i)
                if r is not None and r["kind"] == "theorem":
                    refs.add(p + i)
        return refs

    def skeleton(self, m, keep, mode, upto=None, available=None):
        """The module's commands minus the unselected ones (mode 'bundle' or 'proof'), stopping before byte
        offset `upto`. Returns (text, the scope frames still open at the end)."""
        out, frames = [], []
        for c in self.F.cmds[m]:
            if upto is not None and c["start"]["offset"] >= upto:
                break
            k = classify_cmd(c)
            if k == "bundle" and c["syntaxKind"] in NOTATION_KINDS and self.theorem_refs(c, frames):
                # a macro naming theorems is declared after them, never in a bundle; with expand_macros its
                # uses are expanded instead
                k = "proof" if self.theorem_refs(c, frames) <= set(keep) and not self.cfg.get("expand_macros") else "skip"
            take = (k == "scope" or (k == "decl" and self.decl_selected(m, c, keep)) or (k == "proof" and mode == "proof")
                    or (k == "bundle" and mode == "bundle"
                        and (c["innerKind"] != "Lean.Parser.Command.example" or self.example_ok(m, c, available))))
            if k == "scope":
                self.track(m, c, frames)
            if take:
                a = c["xstart"]
                if c is self.F.cmds[m][0] and c["syntaxKind"] != "header" and mode != "bundle":
                    a = c["start"]["offset"]
                if k == "decl" and mode == "proof":
                    out.append(self.apply_cuts(m, a, c["xend"], self.expand_cuts(m, c, a, c["xend"])
                                               + self.rename_cuts(m, a, c["xend"])))
                else:
                    out.append(self.cut(m, a, c["xend"]))
        return "".join(out).rstrip() + "\n", frames

    def track(self, m, c, frames):
        k = c["syntaxKind"]
        body = self.cut(m, c["start"]["offset"], c["end"]["offset"])
        if k == "Lean.Parser.Command.namespace":
            name = body.split(None, 1)[1].strip()
            full = ".".join([f["name"] for f in frames if f["kind"] == "namespace"] + [name])
            frames.append({"kind": "namespace", "name": name, "full": full, "lines": []})
        elif k == "Lean.Parser.Command.section":
            parts = body.split(None, 1)
            frames.append({"kind": "section", "name": parts[1].strip() if len(parts) > 1 else "", "lines": []})
        elif k == "Lean.Parser.Command.end":
            frames.pop()
        elif frames:
            frames[-1]["lines"].append(body)
        else:
            frames.append({"kind": "top", "name": "", "lines": [body]})

    @staticmethod
    def scope_lines(frames):
        """The scope at a declaration, flattened for a top-level declaration: each namespace becomes
        `open <full name>`, followed by the lines in force inside it."""
        out = []
        for f in frames:
            if f["kind"] == "namespace":
                out.append(f"open {f['full']}")
            out += f["lines"]
        return out

    @staticmethod
    def close_frames(frames):
        return [f"end {f['name']}".rstrip() for f in reversed(frames) if f["kind"] != "top"]

    def def_imports(self, mods):
        b = self.plan["bundles"]
        return [f"import Definitions.Def_{b[x]['name']}" for x in self.F.topo_modules()
                if x in b and any(x == m or x in self.F.closure(m) for m in mods)]

    def rel(self, m):
        return os.path.relpath(module_file(self.F.repo, m), self.F.repo)

    def header(self, lines):
        return "".join(f"-- {l}\n" for l in lines)

    def frames_at(self, m, offset):
        frames = []
        for c in self.F.cmds[m]:
            if c["start"]["offset"] >= offset:
                break
            if classify_cmd(c) == "scope":
                self.track(m, c, frames)
        return frames

    # -- the three kinds of file
    def bundle_file(self, m):
        b = self.plan["bundles"][m]
        available = set(self.in_bundle) & {n for x in [m] + self.F.closure(m) for n in self.plan["bundles"].get(x, {}).get("decls", [])}
        available |= {n for n in self.F.by if self.F.by[n]["kind"] in ("ctor", "rec") or self.F.by[n]["startLine"] == 0}
        body, _ = self.skeleton(m, set(b["decls"]), "bundle", available=available)
        imps = [f"import Definitions.Def_{n}" for n in b["imports"]] + [f"import {i}" for i in self.F.nonproject_imports(m)]
        head = self.header([f"{self.rel(m)} at {self.commit[:12]}, without its theorems (skeleton subtraction);",
                            "generated by scripts/prove2me/export.py; every command kept is copied verbatim."])
        return head + "\n".join(imps) + ("\n\n" if imps else "\n") + body

    def statement(self, n):
        m = self.F.by[n]["module"]
        d = self.F.decl_of[n]
        ref = self.binding_ref(m, n, d)
        a, v = d["declStart"]["offset"], d["valStart"]["offset"]
        cuts = [(ref["start"]["offset"], ref["end"]["offset"], self.export(n))]
        if d.get("docstring"):
            cuts.append((d["docstring"]["start"]["offset"], d["docstring"]["end"]["offset"], ""))
        if d.get("privateTok"):
            cuts.append((d["privateTok"]["start"]["offset"], d["privateTok"]["end"]["offset"], ""))
        stmt = self.apply_cuts(m, a, v, cuts).strip() + " := by sorry"
        imports = self.def_imports([m]) + [f"import {i}" for i in self.F.nonproject_imports(m)]
        preamble = "\n".join(imports) + "\n\n" + "\n".join(self.scope_lines(self.frames_at(m, a)))
        return preamble.strip(), stmt

    def ctor_statement(self, n):
        """A constructor's card: its binders and type as declared, under the export name."""
        m, c, k = self.F.ctor(n)
        sig = " ".join(self.cut(m, k["sig"]["start"]["offset"], k["sig"]["end"]["offset"]).split())
        imports = self.def_imports([m]) + [f"import {i}" for i in self.F.nonproject_imports(m)]
        preamble = "\n".join(imports) + "\n\n" + "\n".join(self.scope_lines(self.frames_at(m, c["start"]["offset"])))
        return preamble.strip(), f"theorem {self.export(n)} {sig} := by sorry", sig, m, k["sig"]["start"]["line"]

    def theorem_file(self, n, pre, stmt, what):
        head = self.header([f"{what} at {self.commit[:12]}; generated by scripts/prove2me/export.py:",
                            "the platform's imports, the scope in force at the declaration, and the statement under its",
                            "export name (data/export_names.json), cut at its proof."])
        return head + pre + "\n\n" + stmt + "\n"

    def solution_file(self, n):
        pn = self.plan["nodes"][n]
        m = pn["module"]
        d = self.F.decl_of[n]
        ref = self.binding_ref(m, n, d)
        hs = set(pn["helpers"])
        hmods = sorted({self.F.by[h]["module"] for h in hs}, key=self.F.topo_modules().index)
        imports = self.def_imports([m] + hmods)
        imports += [f"import Theorems.Thm_{self.slug(x)}" for x in pn["node_deps"]]
        imports += [f"import {i}" for i in sorted(set(i for x in [m] + hmods for i in self.F.nonproject_imports(x)))]
        parts = []
        self.n_expanded = self.n_renamed = 0
        for x in hmods:
            if x == m:
                continue
            body, fr = self.skeleton(x, hs, "proof")
            assert not [f for f in fr if f["kind"] != "top"], f"unbalanced skeleton of {x}"
            parts.append(f"-- inline helpers from {self.rel(x)}\n" + body)
        own, fr = self.skeleton(m, hs, "proof", upto=d["declStart"]["offset"])
        closing = self.close_frames(fr)
        parts.append(f"-- {'inline helpers and ' if m in hmods else ''}scope from {self.rel(m)}\n"
                     + own + ("\n".join(closing) + "\n" if closing else ""))
        a, e = d["declStart"]["offset"], d["declEnd"]["offset"]
        bind = (ref["start"]["offset"], ref["end"]["offset"])
        cuts = [(*bind, "solution")]
        if d.get("privateTok"):
            cuts.append((d["privateTok"]["start"]["offset"], d["privateTok"]["end"]["offset"], ""))
        cuts += self.expand_cuts(m, d["cmd"], a, e) + self.rename_cuts(m, a, e, skip=bind)
        txt = self.apply_cuts(m, a, e, cuts)
        scope = self.scope_lines(fr)
        counts = {"macro_uses_expanded": self.n_expanded, "references_renamed": self.n_renamed}
        head = self.header([f"{self.rel(m)} at {self.commit[:12]}; generated by scripts/prove2me/export.py:",
                            f"the proof of {self.export(n)} ({n} in the repository), as a top-level `theorem solution`;",
                            f"inline helpers: {len(hs)}; platform theorems imported: {len(pn['node_deps'])}; "
                            f"references renamed to export names: {self.n_renamed}"
                            + (f"; macro uses expanded: {self.n_expanded}." if self.n_expanded else ".")])
        return (head + "\n".join(imports) + "\n\n" + "\n".join(parts) + "\n"
                + ("\n".join(scope) + "\n\n" if scope else "") + txt + "\n"), counts

    def ctor_solution_file(self, n, pre, sig, m):
        head = self.header([f"{self.rel(m)} at {self.commit[:12]}; generated by scripts/prove2me/export.py:",
                            f"{n} is a constructor of the inductive type of theorems of ✱1: this card's proof is the",
                            "constructor itself."])
        return head + pre + "\n\n" + f"theorem solution {sig} :=\n  {n.removeprefix(self.cfg['project_prefix'] + '.')} ..\n"

    def source_link(self, m, start, end):
        return f'{self.cfg["repo_url"]}/blob/{self.commit}/{self.rel(m)}#L{start}-L{end}'


def cmd_generate(cfg, a):
    P = paths(a["work"])
    plan = json.load(open(os.path.join(P["facts"], "plan.json")))
    G = Gen(cfg, plan, a["work"])
    out = P["out"]
    shutil.rmtree(out, ignore_errors=True)
    for sub in ("Definitions", "Theorems", "Solutions"):
        os.makedirs(os.path.join(out, sub))
    man = {"release": cfg["release"], "commit": plan["commit"], "repo_url": cfg["repo_url"],
           "environment": cfg["environment"], "lean": G.F.meta["lean"], "counts": plan["counts"],
           "definitions": [], "nodes": []}
    for m, b in plan["bundles"].items():
        f = f'Definitions/Def_{b["name"]}.lean'
        open(os.path.join(out, f), "w", encoding="utf-8").write(G.bundle_file(m))
        man["definitions"].append({"definition_name": b["name"], "module": m, "file": f, "imports": b["imports"],
                                   "decls": b["decls"], "source": f'{cfg["repo_url"]}/blob/{plan["commit"]}/{G.rel(m)}'})
    for n in plan["constructors"]:
        pre, stmt, sig, m, line = G.ctor_statement(n)
        slug = G.slug(n)
        open(os.path.join(out, "Theorems", f"Thm_{slug}.lean"), "w", encoding="utf-8").write(
            G.theorem_file(n, pre, stmt, f"The constructor {n} of {G.rel(m)}"))
        open(os.path.join(out, "Solutions", f"Sol_{slug}.lean"), "w", encoding="utf-8").write(G.ctor_solution_file(n, pre, sig, m))
        man["nodes"].append({"theorem_name": G.export(n), "lean": n, "kind": "constructor", "slug": slug, "module": m,
                             "preamble": pre, "formal_statement": stmt, "node_deps": [], "helpers": [],
                             "macro_uses_expanded": 0, "references_renamed": 0, "docstring": None,
                             "theorem_file": f"Theorems/Thm_{slug}.lean", "solution_file": f"Solutions/Sol_{slug}.lean",
                             "source": G.source_link(m, line, line)})
    for n in plan["order"]:
        pn = plan["nodes"][n]
        slug = G.slug(n)
        pre, stmt = G.statement(n)
        open(os.path.join(out, "Theorems", f"Thm_{slug}.lean"), "w", encoding="utf-8").write(
            G.theorem_file(n, pre, stmt, f"{n} of {G.rel(pn['module'])}"))
        sol, counts = G.solution_file(n)
        open(os.path.join(out, "Solutions", f"Sol_{slug}.lean"), "w", encoding="utf-8").write(sol)
        d = G.F.decl_of[n]
        doc = G.cut(pn["module"], d["docstring"]["start"]["offset"], d["docstring"]["end"]["offset"]) if d.get("docstring") else None
        man["nodes"].append({"theorem_name": G.export(n), "lean": n, "kind": "theorem", "slug": slug, "module": pn["module"],
                             "reason": pn["reason"], "preamble": pre, "formal_statement": stmt,
                             "node_deps": [G.export(x) for x in pn["node_deps"]], "helpers": pn["helpers"],
                             **counts, "docstring": doc,
                             "theorem_file": f"Theorems/Thm_{slug}.lean", "solution_file": f"Solutions/Sol_{slug}.lean",
                             "source": G.source_link(pn["module"], d["declStart"]["line"], d["declEnd"]["line"])})
    # the cards no other card imports: making these public publishes the whole tree
    used = {x for nd in man["nodes"] for x in nd["node_deps"]}
    man["roots"] = [nd["theorem_name"] for nd in man["nodes"] if nd["theorem_name"] not in used]
    json.dump(man, open(os.path.join(out, "manifest.json"), "w", encoding="utf-8"), indent=1, ensure_ascii=False)
    print(f"generate: {len(man['definitions'])} definition bundles, {len(man['nodes'])} cards, "
          f"{sum(nd['macro_uses_expanded'] for nd in man['nodes'])} macro uses expanded, "
          f"{sum(nd['references_renamed'] for nd in man['nodes'])} references renamed, {len(man['roots'])} roots -> {out}")


if __name__ == "__main__":
    a = args_of(sys.argv[1:])
    cfg = load_config()
    if a["stage"] in ("extract", "all"):
        cmd_extract(cfg, a)
    if a["stage"] in ("plan", "all"):
        cmd_plan(cfg, a)
    if a["stage"] in ("generate", "all"):
        cmd_generate(cfg, a)
