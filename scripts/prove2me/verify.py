#!/usr/bin/env python3
"""Check an exported Prove2Me tree (scripts/prove2me/export.py) with the platform's Lean, before upload.

A scratch workspace (<work>/verify_ws) mirrors the platform's: its toolchain, `autoImplicit false`, and the
module layout Definitions/ Theorems/ Solutions/, plus Checks/Canon.lean of the commit exported (the
canonical text of statements, docs/VERSIONING.md). Then:

  0. mutation   the quick tier of the statement mutation (scripts/mutation/mutate.py --quick,
                docs/STATEMENT_MUTATION.md) passes on the copy of the commit exported, run with that
                commit's own tool; a commit without the tool fails
  1. build     every generated module compiles; no `sorry` outside Theorems/; no generated file sets
                `autoImplicit`
  2. gates      for every card: the statement is a `sorry` stub; `solution` has exactly its type (Expr
                equality, as the platform checks); the solution does not import its own card; the
                axioms of `solution`, not descending into imported cards, are within propext,
                Classical.choice and Quot.sound; and no generated file (definition, statement or
                solution) declares a global macro, syntax, notation or elaborator (the platform refuses
                `macro` in a submission; `local notation`, which ✱1·4's check uses, was accepted in the
                private pilot of 2026-10-12)
  3. typediff   the type of every card equals the type of its declaration in the repository built with
                the same Lean (pretty-printed with full names)
  4. digests    the statement digest and definitions digest of every card, computed from the platform files
                exactly as scripts/export_names.py computes them from the repository, equal those of
                data/export_names.json: the card states the statement its name is bound to by the lock

Usage (from the repository root): python3 scripts/prove2me/verify.py [--work DIR] [--tree DIR]
--tree checks another tree with a manifest (e.g. one pulled back from the platform) against the same
commit. Writes <work>/verify_report.json; exits 1 if anything fails, and an export goes to upload only
when this prints "all checks passed".
"""
import concurrent.futures as cf
import glob
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
from export import load_config, paths  # noqa: E402

AXIOMS_OK = {"propext", "Classical.choice", "Quot.sound"}
METAPROG = {"Lean.Parser.Command.macro", "Lean.Parser.Command.syntax", "Lean.Parser.Command.macro_rules",
            "Lean.Parser.Command.elab", "Lean.Parser.Command.elab_rules", "Lean.Parser.Command.notation",
            "Lean.Parser.Command.mixfix", "Lean.Parser.Command.initialize", "Lean.Parser.Command.syntaxAbbrev",
            "Lean.Parser.Command.syntaxCat", "Lean.Parser.Command.declare_syntax_cat",
            "Lean.Parser.Command.notation3"}
LAKEFILE = """import Lake
open Lake DSL

-- The platform's environment for files that import no Mathlib: its toolchain (lean-toolchain) and its
-- option autoImplicit false. Checks/Canon.lean is this repository's, for the digests.
package «verify» where
  leanOptions := #[⟨`autoImplicit, false⟩]

lean_lib «Definitions» where
  globs := #[.submodules `Definitions]
lean_lib «Theorems» where
  globs := #[.submodules `Theorems]
lean_lib «Solutions» where
  globs := #[.submodules `Solutions]
lean_lib «Checks» where
  roots := #[`Checks.Canon]
"""


def sh(cmd, cwd, timeout=7200):
    t = time.time()
    r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    return r, time.time() - t


def sha256(s):
    return "sha256:" + hashlib.sha256(s.encode("utf-8")).hexdigest()


def mutation_check(repo):
    """Check 0: `scripts/mutation/mutate.py --quick` of the copy `repo` of the commit exported, run with that
    commit's own tool (docs/STATEMENT_MUTATION.md). Returns (report, passed); a commit without the tool fails."""
    mut = os.path.join(repo, "scripts", "mutation", "mutate.py")
    if not os.path.exists(mut):
        print("mutation: FAILED, the commit exported has no scripts/mutation/mutate.py")
        return {"rc": None, "error": "the commit exported has no scripts/mutation/mutate.py"}, False
    r, dt = sh([sys.executable, mut, "--quick"], repo)
    lines = (r.stdout + r.stderr).strip().splitlines()
    print(f"mutation: --quick rc {r.returncode} in {dt:.0f}s: {lines[-1] if lines else 'no output'}")
    if r.returncode:
        print("\n".join(lines[-40:]))
    return {"rc": r.returncode, "seconds": round(dt, 1), "output": lines[-40:]}, r.returncode == 0


def main(argv):
    cfg = load_config()
    work = os.path.join(ROOT, ".lake", "prove2me")
    tree = None
    for i, a in enumerate(argv):
        if a == "--work":
            work = os.path.abspath(argv[i + 1])
        if a == "--tree":
            tree = os.path.abspath(argv[i + 1])
    P = paths(work)
    tree = tree or P["out"]
    man = json.load(open(os.path.join(tree, "manifest.json"), encoding="utf-8"))
    ws = os.path.join(work, "verify_ws")
    rep = {"tree": os.path.relpath(tree, work), "commit": man["commit"], "environment": cfg["environment"]}
    failed = []

    # 0. the quick tier of the statement mutation, on the commit exported
    rep["mutation"], ok = mutation_check(P["repo"])
    if not ok:
        failed.append("mutation")

    # 1. workspace and build
    shutil.rmtree(ws, ignore_errors=True)
    for sub in ("Definitions", "Theorems", "Solutions", "Checks", "checks"):
        os.makedirs(os.path.join(ws, sub))
    open(os.path.join(ws, "lakefile.lean"), "w").write(LAKEFILE)
    open(os.path.join(ws, "lean-toolchain"), "w").write(cfg["environment"]["toolchain"] + "\n")
    shutil.copy(os.path.join(P["repo"], "Checks", "Canon.lean"), os.path.join(ws, "Checks"))
    for sub in ("Definitions", "Theorems", "Solutions"):
        for f in glob.glob(os.path.join(tree, sub, "*.lean")):
            shutil.copy(f, os.path.join(ws, sub))
    files = sorted(glob.glob(os.path.join(ws, "*", "*.lean")))
    auto = [os.path.relpath(f, ws) for f in files if "autoImplicit" in open(f, encoding="utf-8").read()]
    rep["sets_autoImplicit"] = auto
    if auto:
        failed.append("autoImplicit")
    mods = ([f'Definitions.Def_{d["definition_name"]}' for d in man["definitions"]]
            + [f'Theorems.Thm_{n["slug"]}' for n in man["nodes"]] + [f'Solutions.Sol_{n["slug"]}' for n in man["nodes"]])
    r, dt = sh(["lake", "build", "Checks"] + mods, ws)
    out = r.stdout + r.stderr
    times = {}
    for m in re.finditer(r"Built (\S+)(?: \(([\d.]+)(ms|s)\))?", r.stdout):
        v = m.group(2)
        times[m.group(1)] = None if v is None else (float(v) / 1000 if m.group(3) == "ms" else float(v))
    sorry_mods = sorted(set(re.findall(r"((?:Solutions|Definitions)/\S+?\.lean):\d+:\d+: warning: declaration uses 'sorry'", out)))
    lean = sh(["lake", "env", "lean", "--version"], ws)[0].stdout.strip()
    rep["build"] = {"rc": r.returncode, "lean": lean, "wall_seconds": round(dt, 1), "modules": len(mods),
                    "max_seconds": max((v for v in times.values() if v is not None), default=None),
                    "sorry_outside_Theorems": sorry_mods,
                    "errors": [l for l in out.splitlines() if re.match(r"(?i)error: \S+\.lean:\d+", l) or ": error" in l][:40]}
    print(f"build: rc {r.returncode}, {len(mods)} modules in {dt:.0f}s with {lean}; sorry outside Theorems: "
          f"{len(sorry_mods)}; files setting autoImplicit: {len(auto)}")
    if r.returncode != 0:
        print("\n".join(rep["build"]["errors"]))
        json.dump(rep, open(os.path.join(work, "verify_report.json"), "w"), indent=1, ensure_ascii=False)
        return 1
    if sorry_mods:
        failed.append("sorry")

    # 2. gates, per card; the metaprogramming check, per file
    chk = os.path.join(ws, "checks")
    extract = os.path.join(P["repo"], "scripts", "prove2me", "extract_commands.lean")   # the commit's own tool

    def gate(n):
        name, slug = n["theorem_name"], n["slug"]
        sol = open(os.path.join(ws, "Solutions", f"Sol_{slug}.lean"), encoding="utf-8").read()
        own_import = re.search(rf"^import Theorems\.Thm_{re.escape(slug)}$", sol, re.M) is not None
        src = f"""import Theorems.Thm_{slug}
import Solutions.Sol_{slug}
import Lean
open Lean Meta
run_meta do
  let env ← getEnv
  let a ← getConstInfo `solution
  let b ← getConstInfo `{name}
  unless a.type == b.type do throwError "TYPE MISMATCH"
  let some bv := b.value? (allowOpaque := true) | throwError "the card has no value"
  unless bv.getUsedConstants.contains ``sorryAx do throwError "the card is not a sorry stub"
  let mut seen : Std.HashSet Name := {{}}
  let mut todo : Array Name := #[`solution]
  let mut axs : Array Name := #[]
  let mut stubs : Array Name := #[]
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if c != `solution then
      if let some idx := env.getModuleIdxFor? c then
        if (`Theorems).isPrefixOf env.header.moduleNames[idx.toNat]! then
          stubs := stubs.push c
          continue
    match env.find? c with
    | some (.axiomInfo _) => axs := axs.push c
    | some ci =>
      todo := todo ++ ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then todo := todo ++ v.getUsedConstants
    | none => pure ()
  logInfo m!"AXIOMS {{axs.toList}} STUBS {{stubs.size}}"
"""
        f = os.path.join(chk, f"gate_{slug}.lean")
        open(f, "w", encoding="utf-8").write(src)
        r, dt = sh(["lake", "env", "lean", f], ws)
        m = re.search(r"AXIOMS \[(.*?)\] STUBS (\d+)", r.stdout)
        axs = [x.strip() for x in m.group(1).split(",") if x.strip()] if m else None
        ok = r.returncode == 0 and m is not None and set(axs) <= AXIOMS_OK and not own_import
        return name, {"ok": ok, "axioms": axs, "cards_imported": int(m.group(2)) if m else None,
                      "own_import": own_import, "seconds": round(dt, 2),
                      "error": None if ok else (r.stdout + r.stderr)[-1500:]}

    def metaprog(f):
        r, _ = sh(["lake", "env", "lean", "--run", extract, f], ws)
        kinds = [json.loads(l) for l in r.stdout.splitlines() if l.strip()]
        bad = [k["syntaxKind"] for k in kinds if k["syntaxKind"] in METAPROG and not k["isLocal"]]
        return os.path.relpath(f, ws), (r.returncode == 0, bad)

    t = time.time()
    with cf.ThreadPoolExecutor(8) as ex:
        gates = dict(ex.map(gate, man["nodes"]))
        gen = [f for f in files if not f.startswith(os.path.join(ws, "Checks"))]
        meta = dict(ex.map(metaprog, gen))
    bad = {k: v for k, v in gates.items() if not v["ok"]}
    meta_bad = {k: v for k, v in meta.items() if not v[0] or v[1]}
    rep["gates"] = {"cards": len(gates), "failed": bad, "seconds": round(time.time() - t, 1),
                    "axioms_seen": sorted({a for v in gates.values() for a in (v["axioms"] or [])}),
                    "axioms_by_card": {k: v["axioms"] for k, v in gates.items() if v["axioms"]},
                    "cards_imported": {k: v["cards_imported"] for k, v in gates.items()},
                    "files_parsed_for_metaprogramming": len(meta), "metaprogramming": meta_bad}
    print(f"gates: {len(gates) - len(bad)}/{len(gates)} cards pass; axioms seen {rep['gates']['axioms_seen']}; "
          f"metaprogramming in {len(meta_bad)} of {len(meta)} files")
    if bad:
        failed.append("gates")
    if meta_bad:
        failed.append("metaprogramming")

    # 3. typediff: each card against its declaration in the repository built with the same Lean
    def pp_script(pairs, outpath):
        return ("import Lean\nopen Lean Meta\nset_option pp.fullNames true\nset_option pp.universes true\n"
                "run_meta do\n  let mut out : Array (String × Json) := #[]\n"
                f"  for n in [{', '.join('`' + x for x in pairs)}] do\n"
                "    let ci ← getConstInfo n\n"
                "    out := out.push (n.toString, Json.str (toString (← ppExpr ci.type)))\n"
                f"  IO.FS.writeFile \"{outpath}\" (Json.mkObj out.toList).compress\n")
    orig = [n["lean"] for n in man["nodes"]]
    cards = [n["theorem_name"] for n in man["nodes"]]
    oj, nj = os.path.join(chk, "types_repo.json"), os.path.join(chk, "types_cards.json")
    open(os.path.join(chk, "types_repo.lean"), "w").write(
        "".join(f"import {m}\n" for m in cfg["modules"]) + pp_script(orig, oj))
    open(os.path.join(chk, "types_cards.lean"), "w").write(
        "".join(f"import Theorems.Thm_{n['slug']}\n" for n in man["nodes"]) + pp_script(cards, nj))
    r1, _ = sh(["lake", "env", "lean", os.path.join(chk, "types_repo.lean")], P["repo"])
    r2, _ = sh(["lake", "env", "lean", os.path.join(chk, "types_cards.lean")], ws)
    if r1.returncode or r2.returncode:
        print(r1.stdout[-2000:], r1.stderr[-2000:], r2.stdout[-2000:], r2.stderr[-2000:])
        return 1
    a, b = json.load(open(oj)), json.load(open(nj))
    diff = {n["theorem_name"]: (a[n["lean"]], b[n["theorem_name"]]) for n in man["nodes"]
            if a[n["lean"]] != b[n["theorem_name"]]}
    rep["typediff"] = {"compared": len(man["nodes"]), "differ": diff}
    print(f"typediff: {len(man['nodes'])} cards against the repository's declarations, {len(diff)} differ")
    if diff:
        failed.append("typediff")

    # 4. digests: the cards' statements and definitions, hashed as scripts/export_names.py does
    dj = os.path.join(chk, "digests.jsonl")
    open(os.path.join(chk, "digests.lean"), "w").write(
        "".join(f"import Theorems.Thm_{n['slug']}\n" for n in man["nodes"]) + "import Checks.Canon\n"
        "open Lean Meta PMCanon\nrun_meta do\n  let mut out : Array String := #[]\n  let mut used : NameSet := {}\n"
        f"  for n in [{', '.join('`' + x for x in cards)}] do\n"
        "    let (c, ds) ← statementCanon n\n"
        "    used := ds.foldl (·.insert ·) used\n"
        "    out := out.push (Json.mkObj [(\"name\", Json.str n.toString), (\"canon\", Json.str c),\n"
        "      (\"deps\", toJson (ds.map (·.toString)))]).compress\n"
        "  for d in used.toList do\n"
        "    out := out.push (Json.mkObj [(\"def\", Json.str d.toString), (\"canon\", Json.str (← defCanon d).1)]).compress\n"
        f"  IO.FS.writeFile \"{dj}\" (\"\\n\".intercalate out.toList)\n")
    r, _ = sh(["lake", "env", "lean", os.path.join(chk, "digests.lean")], ws)
    if r.returncode:
        print(r.stdout[-2000:], r.stderr[-2000:])
        return 1
    lines = [json.loads(l) for l in open(dj) if l.strip()]
    defs = {l["def"]: l["canon"] for l in lines if "def" in l}
    names = {e["export"]: e for e in json.load(open(os.path.join(P["repo"], "data", "export_names.json"), encoding="utf-8"))}
    dd = {}
    for l in lines:
        if "name" not in l:
            continue
        e = names[l["name"]]
        sd = sha256(l["canon"])
        dg = sha256("\n".join(f"{n} {sha256(defs[n])}" for n in sorted(l["deps"])))
        if (sd, dg) != (e["statement_digest"], e["definitions_digest"]):
            dd[l["name"]] = {"statement": sd == e["statement_digest"], "definitions": dg == e["definitions_digest"]}
    rep["digests"] = {"compared": len(cards), "differ": dd}
    print(f"digests: {len(cards)} cards against data/export_names.json, {len(dd)} differ")
    if dd:
        failed.append("digests")

    rep["failed"] = failed
    json.dump(rep, open(os.path.join(work, "verify_report.json"), "w"), indent=1, ensure_ascii=False)
    print("all checks passed" if not failed else f"FAILED: {failed}")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
