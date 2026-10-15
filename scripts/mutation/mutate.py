#!/usr/bin/env python3
"""Statement mutation: is each statement tied to its proof? (docs/STATEMENT_MUTATION.md)

    python3 scripts/mutation/mutate.py --quick   the export-path tier, well under a minute
    python3 scripts/mutation/mutate.py --full    everything; with ✱25, 14 min 59 s with 8 jobs and
                                                 about 1.48 GiB of memory per process (measured
                                                 2026-10-14 on the code of 10fb7d0; docs/
                                                 STATEMENT_MUTATION.md, "Measured code")
    python3 scripts/mutation/mutate.py --compare-methods   Part 2 compared both ways (see below)

Both first run `lake build` on the modules the meta-program imports, so that what is analysed is the
proofs in the sources; then scripts/mutation/StatementMutation.lean (Part 1, unused hypotheses, on every
theorem written in the source; Part 2, statement mutants checked against the original proof term by
the kernel: in --quick on a fixed sample of ✱1–✱5, in --full on all of ✱1–✱5 and on every numbered
proposition from ✱9 on). --full adds two recompilations:

  re-elaboration   each mutant that is a tautology of a ✱1–✱5 statement proved in a replay file (and
                   every 10th of the others, and the unchanged statement as a control) is compiled with
                   the original proof SCRIPT, the statement's definition `s…` replaced by the mutant.
                   Only a tautology can have a proof at all (✱1–✱5 is sound, `PM.sound`), so these are
                   the mutants a proof by a decision procedure, rather than by PM's derivation, could
                   still prove. The primitive propositions ✱1·2–✱1·6 are `Thm`'s constructors and have
                   no script: their mutants are checked against the proof term only.
  hypotheses       each hypothesis of a theorem proved by tactics (and every 25th of the others) is
                   replaced by `True` (a class argument is removed) in a copy of its file cut after
                   the theorem, and the copy is compiled.

The kernel compares a proof's type with a mutant after bringing both to normal form by its own
reductions (--method normal, the default); --method direct compares the terms as they are, which gives
the same verdicts much more slowly on ✱22–✱25. --compare-methods runs Part 2 with both on every mutant
(or on --modules, --only, all but --skip) and fails if they differ anywhere (docs/STATEMENT_MUTATION.md,
"How a mutant is compared").

Findings already examined and accepted are listed, with their classification, in
scripts/mutation/expected.json; anything else makes the run fail. Working files go to .lake/mutation/.
"""
import argparse
import concurrent.futures as cf
import json
import os
import re
import subprocess
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN_FILE = "scripts/mutation/StatementMutation.lean"
EXPECTED = ROOT / "scripts" / "mutation" / "expected.json"
WORK = ROOT / ".lake" / "mutation"
ERROR = re.compile(r"^(?P<file>[^\n]*?):(?P<line>\d+):(?P<col>\d+): error")
REELAB_SAMPLE = 10   # every n-th non-tautological mutant is re-elaborated too
HYP_SAMPLE = 25      # every n-th hypothesis of a term-mode proof is recompiled too


def lean(path, env=None):
    """Compile one file; return (exit code, lines with an error, output)."""
    r = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT, env=env, capture_output=True,
                       text=True)
    out = r.stdout + r.stderr
    lines = {int(m.group("line")) for m in map(ERROR.match, out.splitlines()) if m}
    return r.returncode, lines, out


def module_lines(module, cache={}):
    if module not in cache:
        cache[module] = (ROOT / (module.replace(".", "/") + ".lean")).read_text().split("\n")
    return cache[module]


def build_targets(path=ROOT / LEAN_FILE):
    """The repository's modules the meta-program imports (`import Lean` is the toolchain's)."""
    mods = re.findall(r"^import\s+(\S+)", path.read_text(encoding="utf-8"), re.M)
    return [m for m in mods if m.split(".")[0] != "Lean"]


def build():
    """Bring the oleans of what the meta-program imports up to date, so that it reads the proofs in the
    sources and not those of an earlier build; on an up-to-date tree this takes about a second. The
    recompilations import only modules within the same closure."""
    r = subprocess.run(["lake", "build", *build_targets()], cwd=ROOT, capture_output=True, text=True)
    if r.returncode != 0:
        print(r.stdout + r.stderr)
        sys.exit("lake build failed: the proofs are not analysed")


def run_meta(mode, method="normal", modules="", only="", skip="", name=None):
    """Run the meta-program. `method` is how a proof's type is compared with a mutant: `normal` (the
    kernel's normal forms), `direct` (the terms as they are) or `both`; `modules`, `only` restrict
    Part 2 to some modules or declarations, `skip` leaves some declarations out (comma-separated
    names)."""
    WORK.mkdir(parents=True, exist_ok=True)
    out = WORK / f"{name or mode}.jsonl"
    env = dict(os.environ, PM_MUTATION_MODE=mode, PM_MUTATION_OUT=str(out), PM_MUTATION_METHOD=method,
               PM_MUTATION_MODULES=modules, PM_MUTATION_ONLY=only, PM_MUTATION_SKIP=skip)
    rc, _, text = lean(LEAN_FILE, env)
    if rc != 0:
        print(text)
        sys.exit(f"{LEAN_FILE} failed")
    return [json.loads(line) for line in out.read_text().splitlines()]


# ---------------------------------------------------------------- re-elaboration (✱1–✱5, --full)

def has_script(st):
    """A ✱1–✱5 statement proved in a replay file. The others, ✱1·2–✱1·6, are `Thm`'s constructors:
    no proof script, so only the check against the proof term applies to them."""
    return st["isF"] and st["module"] in ("PM.Replay", "PM.Replay2", "PM.Derived")


def reelab_files(stmts, muts):
    """One file per theorem: the control, then each selected mutant, each in its own namespace with
    the statement's definition replaced. Returns [(path, decl, [(key, first line, last line)])]."""
    by_decl = defaultdict(list)
    for m in muts:
        if m["src"]:
            by_decl[m["decl"]].append(m)
    d = WORK / "reelab"
    d.mkdir(parents=True, exist_ok=True)
    files = []
    for st in stmts:
        if not has_script(st):
            continue
        L = module_lines(st["module"])
        theorem = L[st["line"] - 1:st["endLine"]]
        opens = [x for x in L[:st["line"] - 1] if x.startswith("open ")]
        sdef = st["stmtDef"].split(".")[-1]
        binders = " ".join(f"({v} : F)" for v in st["vars"])
        nontaut = [m for m in by_decl[st["decl"]] if m["taut"] is not True]
        chosen = [("control", st["src"])]
        chosen += [(f"{m['op']}#{m['i']}", m["src"]) for m in by_decl[st["decl"]] if m["taut"] is True]
        chosen += [(f"{m['op']}#{m['i']}", m["src"]) for k, m in enumerate(nontaut) if k % REELAB_SAMPLE == 0]
        text = ["import PM"]
        blocks = []
        for k, (key, src) in enumerate(chosen):
            first = len(text) + 1
            text += [f"namespace PM.Mut{k}", *opens, f"def {sdef} {binders} : F := {src}", *theorem,
                     f"end PM.Mut{k}"]
            blocks.append((key, first, len(text)))
        path = d / (st["decl"].replace(".", "_") + ".lean")
        path.write_text("\n".join(text) + "\n")
        files.append((path, st["decl"], blocks))
    return files


def run_reelab(stmts, muts, jobs):
    files = reelab_files(stmts, muts)
    tautOf = {(m["decl"], f"{m['op']}#{m['i']}"): m["taut"] for m in muts}
    results = []
    with cf.ThreadPoolExecutor(jobs) as ex:
        for (path, decl, blocks), (rc, errs, out) in zip(files, ex.map(lambda f: lean(f[0]), files)):
            for key, a, b in blocks:
                ok = not any(a <= n <= b for n in errs)
                results.append({"decl": decl, "key": key, "compiles": ok,
                                "taut": True if key == "control" else tautOf[(decl, key)]})
    return results


# ---------------------------------------------------------------- hypotheses replaced by True (--full)

OPEN, CLOSE = "([{⦃", ")]}⦄"


def binder_groups(text, start):
    """Top-level binder groups of a signature from `start` up to the colon of its result type."""
    groups, depth, i, g0 = [], 0, start, None
    while i < len(text):
        c = text[i]
        if c in OPEN:
            if depth == 0:
                g0 = i
            depth += 1
        elif c in CLOSE:
            depth -= 1
            if depth == 0:
                groups.append((g0, i + 1))
        elif depth == 0 and c == ":":
            break
        i += 1
    return groups


def split_group(inner):
    depth = 0
    for i, c in enumerate(inner):
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif c == ":" and depth == 0 and inner[i + 1:i + 2] != "=":
            return inner[:i], inner[i + 1:]
    return None, inner


def norm(ty):
    return " ".join(ty.replace("PM.", "").split())


def drop_hypothesis(h, L=None):
    """The file (its lines `L`) cut after the theorem, with the hypothesis replaced by `True` (a class
    removed), or None with a reason."""
    L = L if L is not None else module_lines(h["module"])
    text = "\n".join(L[:h["endLine"]]) + "\n"
    name = h["decl"].split(".")[-1]
    line_start = sum(len(x) + 1 for x in L[:h["line"] - 1])
    m = re.compile(r"(?<![\w'])" + re.escape(name) + r"(?![\w'])").search(text, line_start)
    if not m:
        return None, "name not found"
    for a, b in binder_groups(text, m.end()):
        o, c = text[a], text[b - 1]
        names, ty = split_group(text[a + 1:b - 1])
        if h["kind"] == "class":
            if names is None and norm(ty) == norm(h["type"]):
                return text[:a] + text[b:], None
            continue
        if names is None or h["binder"] not in names.split():
            continue
        # split the group around the binder, keeping the order of the binders
        ns = names.split()
        k = ns.index(h["binder"])
        parts = [f"{o}{' '.join(ns[:k])} :{ty}{c}"] if k else []
        parts.append(f"{o}{h['binder']} : True{c}")
        if ns[k + 1:]:
            parts.append(f"{o}{' '.join(ns[k + 1:])} :{ty}{c}")
        return text[:a] + " ".join(parts) + text[b:], None
    return None, "binder not in the signature's text"


def tactic_proof(h):
    L = module_lines(h["module"])
    body = "\n".join(L[h["line"] - 1:h["endLine"]])
    return re.search(r"(:=|=>)\s*(by\b|.*<\|\s*by\b)", body) is not None or "\n  by" in body


def run_hyps(hyps, jobs):
    tactic = [h for h in hyps if tactic_proof(h)]
    term = [h for h in hyps if not tactic_proof(h)]
    chosen = [(h, "tactic") for h in tactic] + [(h, "term sample") for k, h in enumerate(term)
                                               if k % HYP_SAMPLE == 0]
    d = WORK / "hyp"
    d.mkdir(parents=True, exist_ok=True)
    work, results = [], []
    for k, (h, why) in enumerate(chosen):
        text, reason = drop_hypothesis(h)
        if text is None:
            results.append({**h, "why": why, "compiles": None, "skipped": reason})
            continue
        path = d / f"h{k:04d}.lean"
        path.write_text(text)
        work.append((h, why, path))
    with cf.ThreadPoolExecutor(jobs) as ex:
        for (h, why, path), (rc, errs, out) in zip(work, ex.map(lambda w: lean(w[2]), work)):
            before = any(n < h["line"] - 1 for n in errs)
            results.append({**h, "why": why, "compiles": rc == 0 and not errs,
                            "harness": before, "file": str(path.relative_to(ROOT))})
    return results


# ---------------------------------------------------------------- the two comparisons, side by side

def compare_report(recs):
    """The verdicts of the two comparisons on every mutant and control of a `both` run. Returns the
    problems: any mutant or control on which they differ."""
    stmts = [r for r in recs if r["part"] == "stmt"]
    muts = [r for r in recs if r["part"] == "mut"]
    rows = defaultdict(Counter)
    problems = []
    for s in stmts:
        c = rows[s["module"]]
        c["statements"] += 1
        c["directMs"] += s["defeqMs"]
        c["normalMs"] += s["normalMs"]
        if s["controlNormal"] is None:
            c["fallbacks"] += 1
        elif s["controlNormal"] != s["controlDirect"]:
            c["disagreements"] += 1
            problems.append(f"control of {s['decl']}: direct {s['controlDirect']}, normal forms {s['controlNormal']}")
    mod = {s["decl"]: s["module"] for s in stmts}
    for m in muts:
        c = rows[mod[m["decl"]]]
        c["mutants"] += 1
        if m["survivesNormal"] is None:
            c["fallbacks"] += 1
        elif m["survivesNormal"] != m["survivesDirect"]:
            c["disagreements"] += 1
            problems.append(f"{m['decl']}:{m['op']}#{m['i']}: direct {m['survivesDirect']}, "
                            f"normal forms {m['survivesNormal']}")
    total = sum(rows.values(), Counter())
    print(f"Both comparisons: {total['statements']} statements (and their controls), {total['mutants']} mutants; "
          f"{total['disagreements']} disagreements, {total['fallbacks']} fallbacks")
    print(f"  {'module':18} {'stmts':>5} {'mutants':>7} {'disagree':>8} {'fallback':>8} {'direct s':>9} {'normal s':>9}")
    for m, c in sorted(rows.items()) + [("total", total)]:
        print(f"  {m:18} {c['statements']:5} {c['mutants']:7} {c['disagreements']:8} {c['fallbacks']:8} "
              f"{c['directMs'] / 1000:9.1f} {c['normalMs'] / 1000:9.1f}")
    return problems


def audit_report(recs):
    """The audit of the normal forms (docs/STATEMENT_MUTATION.md): what could make the kernel's comparison
    of two normal forms more than a comparison of trees. Every comparison of a statement whose normal
    forms are flagged falls back to the direct one, so a finding here costs time, not correctness."""
    t = next(r for r in recs if r["part"] == "timing")
    w = next(r for r in recs if r["part"] == "selfTest")["witness"]
    print(f"Planted witness (a proof-valued projection): direct {w['direct']}, normal forms with the audit "
          f"bypassed {w['normalAuditBypassed']}; flagged {w['proofs']}, so decided by direct: {w['verdict']}")
    if t["method"] == "direct":
        print("Comparison by direct: the proof's type and each mutant as they are")
        return
    fb = sum(r.get("fallbacks", 0) for r in recs if r["part"] == "stmt")
    flags = t["auditProofs"] + t["auditStructCtors"] + t["auditUnitLike"]
    print(f"Comparison by {t['method']}: {fb} fallbacks to the direct comparison (bound "
          f"{t['nfBudget']} steps); audit of {t['auditNodes']} subterms of normal forms: "
          + ("nothing flagged" if not flags else
             f"proofs {t['auditProofs']}, structure constructors {t['auditStructCtors']}, "
             f"unit-like {t['auditUnitLike']}"))


# ---------------------------------------------------------------- report

def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--quick", action="store_true")
    g.add_argument("--full", action="store_true")
    g.add_argument("--compare-methods", action="store_true",
                   help="Part 2 with both comparisons on every mutant; fails if they differ anywhere")
    ap.add_argument("--method", choices=("normal", "direct"), default="normal",
                    help="how --quick and --full compare a proof's type with a mutant (default: normal)")
    ap.add_argument("--modules", default="", help="--compare-methods only: these modules (comma-separated)")
    ap.add_argument("--only", default="", help="--compare-methods only: these declarations (comma-separated)")
    ap.add_argument("--skip", default="", help="--compare-methods only: not these declarations (comma-separated)")
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    args = ap.parse_args()
    t0 = time.time()
    build()
    t_build = time.time() - t0
    if args.compare_methods:
        recs = run_meta("part2", "both", args.modules, args.only, args.skip, name="compare")
        problems = compare_report(recs)
        audit_report(recs)
        print(f"wall time: {time.time() - t0:.0f} s (lake build {t_build:.0f} s)")
        if problems:
            print("FAILED: the two comparisons differ:\n  " + "\n  ".join(problems))
            sys.exit(1)
        print("compare methods: identical verdicts")
        return
    mode = "full" if args.full else "quick"
    recs = run_meta(mode, args.method)
    t_meta = time.time() - t0 - t_build
    expected = json.loads(EXPECTED.read_text())
    problems = []
    for cat in ("unusedHypotheses", "termSurvivors", "scriptSurvivors", "droppableHypotheses"):
        for e in expected[cat]:
            if e.get("class") not in expected["classes"]:
                problems.append(f"expected.json: {e['id']} has no known class")
    found = defaultdict(set)   # category -> ids found in this run

    summ = next(r for r in recs if r["part"] == "hypSummary")
    unused = [r for r in recs if r["part"] == "hyp"]
    print(f"Part 1, unused hypotheses: {summ['theorems']} theorems, {summ['hypotheses']} hypotheses "
          f"({', '.join(f'{k} {v}' for d in summ['byKind'] for k, v in d.items())}); unused: {len(unused)}; "
          f"planted cases flagged: {len(summ['plantedFlagged'])} of {summ['plantedExpected']}")
    print(f"  left out as generated by Lean: "
          f"{', '.join(f'{n} {k}' for d in summ['generated'] for k, n in sorted(d.items()))}")
    known = {e["id"] for e in expected["unusedHypotheses"]}
    for r in unused:
        key = f"{r['decl']}:{r['binder']}"
        found["unusedHypotheses"].add(key)
        tag = "accepted" if key in known else "NEW"
        print(f"  {tag}: {r['module'].replace('.', '/')}.lean:{r['line']} {r['decl']} ({r['binder']} : {r['type']}), "
              f"{r['kind']}, {'shallow' if r['shallow'] else 'deep only'}")
        if key not in known:
            problems.append(f"unused hypothesis {key}")

    stmts = [r for r in recs if r["part"] == "stmt"]
    muts = [r for r in recs if r["part"] == "mut"]
    for r in stmts:
        if not r["control"]:
            problems.append(f"control: the proof of {r['decl']} does not check against its own statement")
    # seeded: the ebook's ✱1·4, p ∨ q . ⊃ . p ∨ p (docs/FIDELITY.md), is one of ✱1·4's mutants, not a
    # tautology, and rejected by the proof
    slip = [m for m in muts if m["decl"] == "PM.Thm.perm" and m["src"] == "(PM.F.imp (PM.F.or p q) (PM.F.or p p))"]
    if not slip or slip[0]["taut"] is not False or slip[0]["survives"]:
        problems.append("seeded: the ebook's reading of ✱1·4 is not a rejected, non-tautological mutant")
    else:
        print(f"Seeded: the ebook's ✱1·4 (p ∨ q . ⊃ . p ∨ p) is mutant {slip[0]['op']}#{slip[0]['i']} of ✱1·4: "
              "not a tautology, rejected")
    audit_report(recs)
    known = {e["id"] for e in expected["termSurvivors"]}
    for isF, label in ((True, "✱1–✱5"), (False, "from ✱9 on")):
        ss = [r for r in stmts if r["isF"] == isF]
        ms = [m for m in muts if (m["src"] != "") == isF]
        if not ss:
            continue
        surv = [m for m in ms if m["survives"]]
        c = Counter((m["op"].split()[0], m["taut"]) for m in ms)
        ops = ["orAnd", "dropAntecedent", "iffImp", "negate", "substOcc", "swap"]
        print(f"Part 2, {label}: {len(ss)} statements, {len(ms)} mutants, {len(surv)} accepted by the "
              f"original proof term")
        taut = "tautology" if isF else "skeleton a tautology"
        for op in ops:
            n = sum(v for (o, _), v in c.items() if o == op)
            print(f"  {op:15} {n:5} mutants, {c[(op, True)]:4} {taut}")
        for m in surv:
            key = f"{m['decl']}:{m['op']}#{m['i']}"
            found["termSurvivors"].add(key)
            print(f"  {'accepted' if key in known else 'NEW'} survivor: {key} {m['mutant']}")
            if key not in known:
                problems.append(f"term survivor {key}")

    if args.full:
        t1 = time.time()
        re_res = run_reelab(stmts, muts, args.jobs)
        t_re = time.time() - t1
        ctrl = [r for r in re_res if r["key"] == "control"]
        bad = [r["decl"] for r in ctrl if not r["compiles"]]
        mres = [r for r in re_res if r["key"] != "control"]
        surv = [r for r in mres if r["compiles"]]
        print(f"Re-elaboration of ✱1–✱5 proof scripts: {len(ctrl)} controls ({len(bad)} fail), "
              f"{sum(r['taut'] is True for r in mres)} tautological mutants and "
              f"{sum(r['taut'] is not True for r in mres)} others; {len(surv)} still compile ({t_re:.0f} s)")
        prim = {s["decl"] for s in stmts if s["isF"] and not has_script(s)}
        ptaut = [m for m in muts if m["decl"] in prim and m["taut"] is True]
        print(f"  not re-elaborated: {len(prim)} primitive propositions (Thm's constructors, no proof "
              f"script), {len(ptaut)} tautological mutants ({sum(m['op'].split()[0] != 'swap' for m in ptaut)} not "
              f"renamings); checked against the proof term only")
        problems += [f"re-elaboration control fails: {d}" for d in bad]
        known = {e["id"] for e in expected["scriptSurvivors"]}
        for r in surv:
            key = f"{r['decl']}:{r['key']}"
            found["scriptSurvivors"].add(key)
            print(f"  {'accepted' if key in known else 'NEW'} survivor: {key}")
            if key not in known:
                problems.append(f"script survivor {key}")
        t2 = time.time()
        hyps = [r for r in recs if r["part"] == "hypAll"]
        h_res = run_hyps(hyps, args.jobs)
        t_h = time.time() - t2
        ran = [r for r in h_res if r["compiles"] is not None]
        skipped = [r for r in h_res if r["compiles"] is None]
        comp = [r for r in ran if r["compiles"]]
        harness = [r for r in ran if r.get("harness")]
        print(f"Hypotheses replaced by True and recompiled: {len(ran)} "
              f"({sum(r['why'] == 'tactic' for r in ran)} in tactic proofs, "
              f"{sum(r['why'] != 'tactic' for r in ran)} sampled term proofs); {len(comp)} still compile; "
              f"{len(skipped)} not editable in the source ({t_h:.0f} s)")
        for why, n in Counter(r["skipped"] for r in skipped).items():
            print(f"  not editable: {n} ({why})")
        problems += [f"harness: error before {r['decl']} in {r['file']}" for r in harness]
        known = {e["id"] for e in expected["droppableHypotheses"]}
        for r in comp:
            key = f"{r['decl']}:{r['binder']}"
            found["droppableHypotheses"].add(key)
            print(f"  {'accepted' if key in known else 'NEW'}: {r['module'].replace('.', '/')}.lean:{r['line']} "
                  f"{key} ({r['kind']}) compiles without it")
            if key not in known:
                problems.append(f"droppable hypothesis {key}")
        (WORK / "summary-full.json").write_text(json.dumps(
            {"reelab": re_res, "hyps": h_res}, indent=1, ensure_ascii=False))
    # entries no longer found: in --full every category is measured in full
    for cat in ("unusedHypotheses", "termSurvivors", "scriptSurvivors", "droppableHypotheses") if args.full else ():
        for e in expected[cat]:
            if e["id"] not in found[cat]:
                problems.append(f"stale entry of expected.json ({cat}): {e['id']}")
    print(f"wall time: {time.time() - t0:.0f} s (lake build {t_build:.0f} s, Lean meta-program {t_meta:.0f} s)")
    if problems:
        print("FAILED:\n  " + "\n  ".join(problems))
        sys.exit(1)
    print("statement mutation: no unexpected finding")


if __name__ == "__main__":
    main()
