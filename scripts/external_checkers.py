#!/usr/bin/env python3
"""The proofs re-checked by two kernels independent of Lean's (docs/VERIFICATION.md, "External checkers").

    python3 scripts/external_checkers.py                        build what is missing, export, check
    python3 scripts/external_checkers.py --nanoda-upstream require
                                                                also fail if nanoda's pin is not the
                                                                upstream head (scripts/release_check.sh)

Steps, each of which must pass for exit 0:

  tools      lean4export, con-leche and nanoda_lib cloned at the pinned commits below and built (a step
             that is already built takes seconds); lean4export with this repository's toolchain, so that
             it reads the oleans this toolchain wrote; con-leche with its own toolchain; nanoda with cargo
  build      `lake build PM Checks.PinnedStatements`
  export     lean4export of the modules PM and Checks.PinnedStatements: every constant of their import
             closure, Lean's core library included; its size and sha256 are printed
  con-leche  `con-leche --verified`: must accept every declaration
  nanoda     the configuration of NANODA_CONFIG (below, with the reason for each setting): must report
             no typechecker error
  scan       of the export (scan_export): the only axioms declared are Lean core's seven; no declaration
             names sorryAx, Lean.ofReduceBool or Lean.ofReduceNat; only Lean.reduceBool and
             Lean.reduceNat name Lean.trustCompiler. Names are compared as the export structures them,
             component by component (N, read_names), never as printed
  counts     con-leche's count must be the export's declaration records; nanoda's, its constants with
             an inductive declaration's types, constructors and recursors counted separately, less the
             axioms nanoda skips (reconcile)
  attributes no declaration of a module under PM or Checks has an implementation attribute, which the
             export leaves out (scripts/implementation_attributes.lean, on the built environment)
  controls   seeded faults, one or more for each rule (CONTROLS): each small module is compiled, the
             closure of its one theorem exported, and each checker named for it must reject it, the
             scan for the reason it plants; and one module for each implementation attribute
             (ATTRIBUTE_CONTROLS), which the attribute check must find

Exit 0 if all pass, 1 if a check fails, 2 if a tool cannot be fetched or built. Working files (clones,
builds, logs, summary.json) go to .lake/external-checkers/ (--work); the export is deleted after a run
that passes, unless --keep-export. Each step prints its wall time, the peak resident memory of its
process tree and the load average at its start and end. A step of tests/run_all.sh (SKIP_EXTERNAL=1
leaves it out) and, with --nanoda-upstream require, of scripts/release_check.sh.
"""
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / ".lake" / "external-checkers"
TARGETS = ["PM", "Checks.PinnedStatements"]

# name: (repository, pinned commit, what is built)
TOOLS = {
    # tag v4.34.0; built with this repository's toolchain, written over its lean-toolchain
    "lean4export": ("https://github.com/leanprover/lean4export", "076e8e57707e813375e8f9da8bf989799ace9680",
                    ".lake/build/bin/lean4export"),
    # built with its own toolchain (leanprover/lean4:v4.35.0-rc3 at this commit)
    "con-leche": ("https://github.com/leanprover/con-leche", "c26f79316c01ae19ab0fbe85acab371d2d8d390a",
                  ".lake/build/bin/con-leche"),
    # kept at upstream's head (--nanoda-upstream checks it)
    "nanoda_lib": ("https://github.com/ammkrn/nanoda_lib", "e0d76f5ec30bba244023466875b4845a57fd3ea5",
                   "target/release/nanoda_bin"),
}


def N(*parts):
    """A Lean name as the scan compares names: the tuple of its components, each ("str", text) or
    ("num", n), never a dotted string. So «Lean.reduceBool», one component, is not Lean.reduceBool, two,
    and the string component "1" is not the numeric component 1."""
    return tuple(("num", p) if isinstance(p, int) else ("str", p) for p in parts)


IDENT_RE = re.compile(r"[^\W\d][\w'!?]*")


def show(name):
    """A name as Lean prints it, a string component that is not a plain identifier in «»: for messages
    only; no rule compares printed names."""
    return ".".join(str(v) if k == "num" else v if IDENT_RE.fullmatch(v) else f"«{v}»" for k, v in name)


# Lean core declares these seven axioms in every export, used or not.
STANDARD_AXIOMS = {N("propext"), N("Quot", "sound"), N("Classical", "choice")}
TRUST_COMPILER = N("Lean", "trustCompiler")
NEVER_NAMED = {N("sorryAx"), N("Lean", "ofReduceBool"), N("Lean", "ofReduceNat")}
CORE_AXIOMS = STANDARD_AXIOMS | NEVER_NAMED | {TRUST_COMPILER}
WATCHED = NEVER_NAMED | {TRUST_COMPILER}
# The bodies of these two core opaque constants name Lean.trustCompiler; an opaque body never unfolds.
TRUST_COMPILER_USERS = {N("Lean", "reduceBool"), N("Lean", "reduceNat")}

# nanoda: the three standard axioms and Lean.trustCompiler permitted, unpermitted axioms skipped rather
# than a hard error. With the hard error, nanoda stops on the presence of sorryAx, which Lean core
# declares in every export; without Lean.trustCompiler permitted, it panics on the bodies of
# Lean.reduceBool and Lean.reduceNat, which name it (upstream issue ammkrn/nanoda_lib#53). A skipped
# axiom is an error only where a declaration uses it; the scan checks that nothing but those two bodies
# names Lean.trustCompiler.
# nanoda takes the permitted axioms as printed names: it admitted an axiom «Classical.choice», one
# component (MEASURED); the scan, which compares structured names, rejects one.
NANODA_PERMITTED = STANDARD_AXIOMS | {TRUST_COMPILER}
NANODA_CONFIG = {
    "permitted_axioms": ["propext", "Classical.choice", "Quot.sound", "Lean.trustCompiler"],
    "unpermitted_axiom_hard_error": False,
    "nat_extension": True,
    "string_extension": True,
    "print_success_message": True,
}

# Seeded faults: (module, its source, the theorem exported with its closure, the checkers that must
# reject it, the rule of the scan it must fail). The first two are the faults both checkers must reject.
# `native_decide` declares an auxiliary axiom (in Lean 4.34; earlier versions used Lean.ofReduceBool),
# caught as a stray axiom. The last three name a non-standard core axiom directly; con-leche and nanoda
# are not required to reject them, since con-leche replaces those axioms by definitions of the same
# type and nanoda is configured to admit Lean.trustCompiler: there the scan is the check.
CONTROLS = [
    ("NegSorry", "theorem bad_sorry : False := sorry\n", "bad_sorry",
     {"con-leche", "nanoda", "scan"}, "sorryAx"),
    ("NegAxiom", "axiom stray_axiom : False\ntheorem bad_axiom : False := stray_axiom\n", "bad_axiom",
     {"con-leche", "nanoda", "scan"}, "axiom"),
    ("NegNativeDecide", "theorem bad_native_decide : 2 + 2 = 4 := by native_decide\n",
     "bad_native_decide", {"scan"}, "axiom"),
    ("NegReduceBool", "set_option linter.deprecated false\n"
     "theorem bad_reduce_bool (h : Lean.reduceBool true = false) : true = false :=\n"
     "  Lean.ofReduceBool true false h\n", "bad_reduce_bool", {"scan"}, "Lean.ofReduceBool"),
    ("NegReduceNat", "set_option linter.deprecated false\n"
     "theorem bad_reduce_nat (h : Lean.reduceNat 0 = 1) : 0 = 1 :=\n"
     "  Lean.ofReduceNat 0 1 h\n", "bad_reduce_nat", {"scan"}, "Lean.ofReduceNat"),
    ("NegTrustCompiler", "set_option linter.deprecated false\n"
     "theorem bad_trust_compiler : True := Lean.trustCompiler\n", "bad_trust_compiler",
     {"scan"}, "Lean.trustCompiler"),
    # Names quoted into one component that print like core's of two: a scan comparing printed names
    # passed both, and nanoda admits the first (it permits axioms by printed name).
    ("NegQuotedAxiom", "axiom «Classical.choice» : False\n"
     "theorem bad_quoted_axiom : False := «Classical.choice»\n", "bad_quoted_axiom",
     {"con-leche", "scan"}, "axiom"),
    ("NegQuotedCoreUser", "set_option linter.deprecated false\n"
     "opaque «Lean.reduceBool» : True := Lean.trustCompiler\n"
     "theorem bad_quoted_core_user : True := «Lean.reduceBool»\n", "bad_quoted_core_user",
     {"scan"}, "Lean.trustCompiler"),
]

# Implementation attributes, which a logical export leaves out: (module, its source, the declaration
# scripts/implementation_attributes.lean must find with one). Each is a valid logical definition; the
# check is that the repository's declarations carry no such attribute.
ATTRIBUTE_CONTROLS = [
    ("NegImplementedBy", "def runtime : Bool := false\n@[implemented_by runtime] def logical : Bool := true\n",
     "logical"),
    ("NegExtern", "@[extern \"pm_external\"] def external : Bool := true\n", "external"),
]
REPO_PREFIXES = ["PM", "Checks"]

NICE = 10
STEPS = []   # one record per step, written to summary.json


def log(msg):
    print(f"[{time.strftime('%H:%M:%S', time.gmtime())}Z] {msg}", flush=True)


def load():
    return round(os.getloadavg()[0], 2)


def run(label, cmd, cwd=ROOT, out=None, env=None, logs=None):
    """Run cmd niced, its output to files under logs (stdout to `out` if given); return (exit code,
    stdout text unless redirected, stderr text). Records wall time, peak RSS of the process tree (from
    wait4) and the load average before and after."""
    logs.mkdir(parents=True, exist_ok=True)
    out_path = out or logs / f"{label}.out"
    err_path = logs / f"{label}.err"
    l0, t0 = load(), time.monotonic()
    with open(out_path, "wb") as fo, open(err_path, "wb") as fe:
        p = subprocess.Popen(["nice", "-n", str(NICE)] + [str(c) for c in cmd], cwd=cwd, stdout=fo,
                             stderr=fe, env=env)
        _, status, ru = os.wait4(p.pid, 0)
    p.returncode = os.waitstatus_to_exitcode(status)
    rec = {"step": label, "rc": p.returncode, "wall_s": round(time.monotonic() - t0, 1),
           "peak_rss_mib": round(ru.ru_maxrss / 1024), "load_start": l0, "load_end": load()}
    STEPS.append(rec)
    log(f"  {label}: rc {rec['rc']}, {rec['wall_s']} s, peak {rec['peak_rss_mib']} MiB, "
        f"load {l0} -> {rec['load_end']}")
    text = "" if out else out_path.read_text(errors="replace")
    return p.returncode, text, err_path.read_text(errors="replace")


def setup_failure(msg):
    log(f"SETUP FAILED: {msg}")
    sys.exit(2)


def cargo():
    found = shutil.which("cargo") or str(Path.home() / ".cargo" / "bin" / "cargo")
    if not Path(found).exists():
        setup_failure("cargo not found (on PATH or in ~/.cargo/bin)")
    return found


def fetch(name, work, mirror):
    url, rev, _ = TOOLS[name]
    src = str(Path(mirror) / name) if mirror else url
    d = work / name
    git = ["git", "-C", str(d)]
    if not (d / ".git").exists():
        if subprocess.run(["git", "clone", "-q", src, str(d)]).returncode:
            setup_failure(f"clone of {src} failed")
    if subprocess.run(git + ["cat-file", "-e", rev + "^{commit}"], capture_output=True).returncode:
        if subprocess.run(git + ["fetch", "-q", src]).returncode:
            setup_failure(f"fetch of {src} failed")
    if subprocess.run(git + ["checkout", "-q", "-f", "--detach", rev]).returncode:
        setup_failure(f"checkout of {rev} in {name} failed")
    head = subprocess.run(git + ["rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    if head != rev:
        setup_failure(f"{name} is at {head}, not {rev}")
    log(f"{name} at {head}")
    return d


def upstream_head(name):
    url = TOOLS[name][0]
    try:
        r = subprocess.run(["git", "ls-remote", url, "HEAD"], capture_output=True, text=True, timeout=120)
    except subprocess.TimeoutExpired:
        return None
    return r.stdout.split()[0] if r.returncode == 0 and r.stdout.strip() else None


def build_tools(work, mirror, logs):
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    dirs = {name: fetch(name, work, mirror) for name in TOOLS}
    (dirs["lean4export"] / "lean-toolchain").write_text(toolchain + "\n")
    log(f"building lean4export on {toolchain}")
    if run("build-lean4export", ["lake", "build"], cwd=dirs["lean4export"], logs=logs)[0]:
        setup_failure("lean4export build failed")
    conleche_toolchain = (dirs["con-leche"] / "lean-toolchain").read_text().strip()
    log(f"building con-leche on {conleche_toolchain}")
    if run("build-con-leche", ["lake", "build", "con-leche"], cwd=dirs["con-leche"], logs=logs)[0]:
        setup_failure("con-leche build failed")
    log("building nanoda")
    if run("build-nanoda", [cargo(), "build", "--release", "--locked"], cwd=dirs["nanoda_lib"], logs=logs)[0]:
        setup_failure("nanoda build failed")
    return {name: dirs[name] / TOOLS[name][2] for name in TOOLS}


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 24), b""):
            h.update(chunk)
    return h.hexdigest()


def conleche(binary, export, jobs, label, logs):
    rc, out, err = run(label, [binary, "--verified", f"--jobs={jobs}", export], logs=logs)
    m = re.search(r"accepted (\d+) declarations \(--verified\)", out + err)
    msg = next((x for x in (out + err).splitlines() if "con-leche:" in x and "stats:" not in x
                and ("accepted" in x or "not implemented" in x or "error" in x.lower())), "")
    return {"accepted": rc == 0 and m is not None, "rc": rc,
            "declarations": int(m.group(1)) if m else None, "message": msg.strip()[:300]}


def nanoda(binary, export, jobs, label, logs):
    cfg = dict(NANODA_CONFIG, export_file_path=str(export), num_threads=jobs)
    cfg_path = logs / f"{label}.json"
    cfg_path.write_text(json.dumps(cfg, indent=1) + "\n")
    rc, out, err = run(label, [binary, cfg_path], logs=logs)
    m = re.search(r"Checked (\d+) declarations with no (?:typechecker )?errors", out)
    msg = (out.strip().splitlines() or [""])[0] if m else " ".join((err.strip() or out.strip()).split())
    return {"accepted": rc == 0 and m is not None, "rc": rc,
            "declarations": int(m.group(1)) if m else None, "message": msg[:300]}


CONST_RE = re.compile(r'"const":\{"name":(\d+)')
CHILD_RE = re.compile(r'"(?:body|type|fn|arg|value|struct|expr|rhs)":(\d+)')
EXPR_ID_RE = re.compile(r'"ie":(\d+)')
DECL_KINDS = ('{"axiom"', '{"def"', '{"thm"', '{"opaque"', '{"quot"', '{"inductive"')


def read_names(path):
    """The export's names, by index, each as the tuple of its components (N above). Each name record
    is parsed as JSON, so a string component is taken whole and unescaped, whatever it contains;
    lean4export writes a name's prefix before the name. Index 0 is the anonymous name."""
    names = {0: ()}
    with open(path) as f:
        for line in f:
            if line.startswith('{"in"'):
                d = json.loads(line)
                if "str" in d:
                    names[d["in"]] = names[d["str"]["pre"]] + (("str", d["str"]["str"]),)
                else:
                    names[d["in"]] = names[d["num"]["pre"]] + (("num", d["num"]["i"]),)
    return names


def scan_export(path):
    """One streaming pass over the export (lean4export writes every name and expression before its
    first use). Returns (passes, report): the axioms declared, and the declarations whose type, value
    or recursor rules name each of Lean core's four non-standard axioms, directly or through an
    expression. Because every declaration of the export is scanned, a declaration that reaches one of
    them through another constant is caught at that constant. Every rule compares structured names
    (read_names), never printed ones. The report also gives the counts the checkers' are reconciled
    with (reconcile): declaration records, and constants with an inductive declaration's types,
    constructors and recursors counted separately, both also by first name component."""
    names = read_names(path)
    watched = {i: n for i, n in names.items() if n in WATCHED}
    tainted, users, axioms, records, expanded = {}, {}, [], 0, 0
    by_namespace = {}
    with open(path) as f:
        for line in f:
            if line.startswith(('{"in"', '{"il"', '{"meta"')):
                continue
            is_decl = line.startswith(DECL_KINDS)
            if is_decl:
                records += 1
                d = json.loads(line)
                kind, body = next(iter(d.items()))
                if kind == "inductive":
                    decl_names = [names[t["name"]] for t in body["types"]]
                    constants = decl_names + [names[c["name"]] for c in body["ctors"] + body["recs"]]
                else:
                    decl_names = constants = [names[body["name"]]]
                expanded += len(constants)
                # a record under its (first) type's first component, a constant under its own: a
                # private constructor of a public structure is under _private
                by_namespace.setdefault(show(decl_names[0][:1]), [0, 0])[0] += 1
                for n in constants:
                    by_namespace.setdefault(show(n[:1]), [0, 0])[1] += 1
                if kind == "axiom":
                    axioms.append(decl_names[0])
            hit = {watched[int(c)] for c in CONST_RE.findall(line) if int(c) in watched}
            for k in CHILD_RE.findall(line):
                hit |= tainted.get(int(k), set())
            if not hit:
                continue
            if is_decl:
                for w in hit:
                    users.setdefault(w, set()).update(decl_names)
            else:
                m = EXPR_ID_RE.search(line)
                if m:
                    tainted[int(m.group(1))] = hit
    def listed(ns):
        return sorted(show(n) for n in ns)

    reasons = []
    stray = set(axioms) - CORE_AXIOMS
    if stray:
        reasons.append(f"axiom: declared, not one of Lean core's seven: {listed(stray)}")
    for w in sorted(NEVER_NAMED):
        if users.get(w):
            reasons.append(f"{show(w)}: named by {listed(users[w])[:10]}")
    extra = users.get(TRUST_COMPILER, set()) - TRUST_COMPILER_USERS
    if extra:
        reasons.append(f"{show(TRUST_COMPILER)}: named by {listed(extra)[:10]}, not only by "
                       f"{listed(TRUST_COMPILER_USERS)}")
    nanoda_skipped = [a for a in axioms if a not in NANODA_PERMITTED]
    report = {"passes": not reasons, "declarations": records, "expanded": expanded,
              "nanoda_skipped": listed(nanoda_skipped), "nanoda_expected": expanded - len(nanoda_skipped),
              "axioms": listed(axioms),
              "users": {show(w): listed(users.get(w, ())) for w in sorted(WATCHED)},
              "namespaces": {k: {"records": v[0], "constants": v[1]}
                             for k, v in sorted(by_namespace.items(), key=lambda kv: -kv[1][1])},
              "reasons": reasons}
    return not reasons, report


def reconcile(cl, nd, rep):
    """The checkers' counts against the export's: con-leche counts one per declaration record; nanoda
    counts an inductive declaration's types, constructors and recursors separately and leaves out the
    axioms it skips (those it does not permit). Returns the disagreements; a checker that gave no count
    disagrees."""
    out = []
    if cl["declarations"] != rep["declarations"]:
        out.append(f"con-leche count: {cl['declarations']} declarations accepted, the export has "
                   f"{rep['declarations']} declaration records")
    if nd["declarations"] != rep["nanoda_expected"]:
        out.append(f"nanoda count: {nd['declarations']} declarations checked, expected "
                   f"{rep['nanoda_expected']} (the export's {rep['expanded']} constants, an inductive "
                   f"declaration's types, constructors and recursors counted separately, less the "
                   f"{len(rep['nanoda_skipped'])} axioms it skips: {', '.join(rep['nanoda_skipped'])})")
    return out


def timed_scan(label, export, logs):
    """The scan in a process of its own, so that its time and memory are measured as the tools' are
    (and a forked tool does not start from the memory the scan held)."""
    report = logs / f"{label}.json"
    rc, _, err = run(label, [sys.executable, Path(__file__).resolve(), "--scan", export, report], logs=logs)
    if not report.exists():
        setup_failure(f"the scan did not finish: {err[-500:]}")
    rep = json.loads(report.read_text())
    return rc == 0 and rep["passes"], rep


def attribute_scan(label, prefixes, modules, env, logs):
    """scripts/implementation_attributes.lean on MODULES: passes if no declaration of a module under
    one of PREFIXES has an implementation attribute. Returns (passes, its report)."""
    cmd = ["lean", "--run", ROOT / "scripts" / "implementation_attributes.lean"] + prefixes + ["--"] + modules
    rc, out, err = run(label, (["lake", "env"] if env is None else []) + cmd, env=env, logs=logs)
    lines = [x for x in out.splitlines() if x.startswith("{")]
    if not lines:
        return False, {"rc": rc, "error": " ".join((err or out).split())[:500]}
    rep = json.loads(lines[-1])
    rep["rc"] = rc
    return rc == 0 and not rep["attributed"], rep


def run_attribute_controls(work, logs):
    """Each module of ATTRIBUTE_CONTROLS must be found to carry the attribute it plants."""
    cdir = work / "controls"
    cdir.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_PATH=str(cdir))
    results, ok = [], True
    for module, source, decl in ATTRIBUTE_CONTROLS:
        log(f"control {module}: {source.strip().splitlines()[-1]}")
        (cdir / f"{module}.lean").write_text(source)
        rc, _, err = run(f"{module}-compile", ["lean", "-o", cdir / f"{module}.olean", cdir / f"{module}.lean"],
                         logs=logs)
        if rc:
            setup_failure(f"control {module} does not compile: {err[:500]}")
        passes, rep = attribute_scan(f"{module}-attributes", [module], [module], env, logs)
        good = not passes and decl in rep.get("attributed", [])
        log(f"  found with an implementation attribute: {rep.get('attributed', rep.get('error'))}")
        log(f"  control {module}: {'rejected as required' if good else 'FAILED'}")
        ok = ok and good
        results.append({"module": module, "source": source, "declaration": decl, "report": rep,
                        "passes": good})
    return ok, results


def run_controls(bins, work, jobs, logs):
    """Each seeded fault must be rejected by the checkers named for it, and by the scan for its reason."""
    cdir = work / "controls"
    cdir.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_PATH=str(cdir))
    results, ok = [], True
    for module, source, theorem, rejectors, reason in CONTROLS:
        log(f"control {module}: {source.strip().splitlines()[-1]}")
        (cdir / f"{module}.lean").write_text(source)
        olean = cdir / f"{module}.olean"
        rc, _, err = run(f"{module}-compile", ["lean", "-o", olean, cdir / f"{module}.lean"], logs=logs)
        if rc:
            setup_failure(f"control {module} does not compile: {err[:500]}")
        export = cdir / f"{module}.ndjson"
        if run(f"{module}-export", [bins["lean4export"], module, "--", theorem], out=export, env=env,
               logs=logs)[0]:
            setup_failure(f"control {module}: export failed")
        verdicts = {"con-leche": conleche(bins["con-leche"], export, jobs, f"{module}-con-leche", logs),
                    "nanoda": nanoda(bins["nanoda_lib"], export, jobs, f"{module}-nanoda", logs)}
        scan_ok, rep = scan_export(export)
        verdicts["scan"] = {"accepted": scan_ok, "message": "; ".join(rep["reasons"])}
        good = True
        for checker, v in verdicts.items():
            must = checker in rejectors
            if must and v["accepted"]:
                good = False
            log(f"  {checker}: {'accepted' if v['accepted'] else 'rejected'}"
                f"{'' if must else ' (not required to reject)'}: {v['message'][:200]}")
        if not any(r.startswith(reason) for r in rep["reasons"]):
            good = False
            log(f"  the scan did not give the planted reason ({reason})")
        log(f"  control {module}: {'rejected as required' if good else 'FAILED'}")
        ok = ok and good
        results.append({"module": module, "source": source, "theorem": theorem,
                        "must_reject": sorted(rejectors), "reason": reason, "verdicts": verdicts,
                        "passes": good})
    return ok, results


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--work", default=str(WORK), help="working directory (default .lake/external-checkers)")
    ap.add_argument("--jobs", type=int, default=4, help="threads for con-leche and nanoda (default 4)")
    ap.add_argument("--mirror", help="clone the tools from DIR/<name> instead of their repositories")
    ap.add_argument("--nanoda-upstream", choices=["skip", "report", "require"], default="report",
                    help="compare nanoda's pin with upstream's head: report (default), require (fail "
                         "unless equal, or if upstream cannot be reached), skip")
    ap.add_argument("--keep-export", action="store_true",
                    help="keep the export (766 MB at 8dbf6e2) after a run that passes; it is always kept "
                         "after one that fails")
    ap.add_argument("--scan", nargs=2, metavar=("EXPORT", "REPORT"), help=argparse.SUPPRESS)
    args = ap.parse_args()
    if args.scan:
        ok, rep = scan_export(args.scan[0])
        Path(args.scan[1]).write_text(json.dumps(rep, indent=1) + "\n")
        sys.exit(0 if ok else 1)
    work = Path(args.work).resolve()
    logs = work / "logs"
    work.mkdir(parents=True, exist_ok=True)
    t_start, failed, summary = time.monotonic(), [], {}
    log(f"external checkers, load {load()}")

    if args.nanoda_upstream != "skip":
        head, pin = upstream_head("nanoda_lib"), TOOLS["nanoda_lib"][1]
        current = head == pin
        log(f"nanoda_lib: pin {pin[:7]}, upstream head {head[:7] if head else 'unreachable'}"
            f"{'' if current else ' -- the pin is not current'}")
        summary["nanoda_upstream"] = {"pin": pin, "head": head, "current": current}
        if args.nanoda_upstream == "require" and not current:
            failed.append("nanoda pin is not upstream's head")

    bins = build_tools(work, args.mirror, logs)

    log(f"lake build {' '.join(TARGETS)}")
    if run("build-pm", ["lake", "build"] + TARGETS, logs=logs)[0]:
        setup_failure("lake build failed")

    export = work / "pm.ndjson"
    log(f"export of {' + '.join(TARGETS)}")
    if run("export", ["lake", "env", bins["lean4export"]] + TARGETS, out=export, logs=logs)[0]:
        setup_failure("export failed")
    digest = sha256(export)
    summary["export"] = {"modules": TARGETS, "bytes": export.stat().st_size, "sha256": digest}
    log(f"export: {export.stat().st_size:,} bytes, sha256 {digest}")

    log(f"con-leche --verified --jobs={args.jobs}")
    cl = conleche(bins["con-leche"], export, args.jobs, "con-leche", logs)
    summary["con-leche"] = cl
    log(f"  {cl['message']}")
    if not cl["accepted"]:
        failed.append("con-leche")

    log("nanoda")
    nd = nanoda(bins["nanoda_lib"], export, args.jobs, "nanoda", logs)
    summary["nanoda"] = nd
    log(f"  {nd['message']}")
    if not nd["accepted"]:
        failed.append("nanoda")

    log("scan of the export")
    scan_ok, rep = timed_scan("scan", export, logs)
    summary["scan"] = rep
    log(f"  {rep['declarations']:,} declaration records ({rep['expanded']:,} constants with an inductive "
        f"declaration's types, constructors and recursors counted separately); axioms declared: "
        f"{', '.join(rep['axioms'])}")
    for w, us in rep["users"].items():
        log(f"  {w}: named by {us}")
    for r in rep["reasons"]:
        log(f"  FAILS: {r}")
    if not scan_ok:
        failed.append("scan")

    counts = reconcile(cl, nd, rep)
    summary["counts"] = {"con-leche": cl["declarations"], "records": rep["declarations"],
                         "nanoda": nd["declarations"], "nanoda_expected": rep["nanoda_expected"],
                         "disagreements": counts}
    log(f"counts: con-leche {cl['declarations']} = {rep['declarations']} records; nanoda "
        f"{nd['declarations']} = {rep['expanded']} constants - {len(rep['nanoda_skipped'])} skipped axioms "
        f"= {rep['nanoda_expected']}")
    for c in counts:
        log(f"  FAILS: {c}")
    if counts:
        failed.append("counts")

    log(f"implementation attributes of {', '.join(REPO_PREFIXES)} declarations")
    attr_ok, attrs = attribute_scan("attributes", REPO_PREFIXES, TARGETS, None, logs)
    summary["attributes"] = attrs
    log(f"  {attrs.get('declarations')} declarations; with an implementation attribute: "
        f"{attrs.get('attributed')}; unsafe or partial, so not exported: {attrs.get('excludedCount')}")
    if not attr_ok:
        failed.append("implementation attributes")

    log("negative controls")
    ctl_ok, ctl = run_controls(bins, work, args.jobs, logs)
    actl_ok, actl = run_attribute_controls(work, logs)
    ctl += actl
    summary["controls"] = ctl
    if not (ctl_ok and actl_ok):
        failed.append("negative controls")

    summary.update(steps=STEPS, failed=failed, wall_s=round(time.monotonic() - t_start, 1),
                   pins={n: t[1] for n, t in TOOLS.items()})
    (work / "summary.json").write_text(json.dumps(summary, indent=1) + "\n")
    log(f"total {summary['wall_s']} s, load {load()}")
    if failed:
        log(f"FAILED: {', '.join(failed)} (the export is kept: {export})")
        sys.exit(1)
    if not args.keep_export:
        export.unlink()
    log(f"external checkers: con-leche accepted {cl['declarations']} declarations, nanoda checked "
        f"{nd['declarations']}, both as the export's counts require, the scan passed, no implementation "
        f"attribute, {len(ctl)} negative controls rejected")


if __name__ == "__main__":
    main()
