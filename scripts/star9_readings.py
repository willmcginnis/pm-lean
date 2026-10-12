#!/usr/bin/env python3
"""Write docs/STAR9_READINGS.md: ✱9 under its four readings (docs/REPAIRS.md).

A, the definitions ✱9·01–✱9·08 as printed; C, the same definitions with Russell's ✱8·13 (second
edition, 1925) carried over to ✱9, the working reading and the default; L, Landini's ✱9+ (2000): the
definitions as printed with ✱9·yy, ✱9·zz and the rule Switch, a published variant kept as a
cross-check; B, an alternative convention of our own, kept as a cross-check. The results come from two
sources:

- Checks/Star9Readings.lean (run with `lake env lean`), which reads from the statements of the Lean
  theorems under which readings each ✱9 proposition is derived, prints the combinations of p. 142 that
  each reading leaves open (PM/Found9/Simul.lean), and measures where C's proofs use ✱8·13 and L's use
  Switch;
- PM/Found9/Star9.lean, whose lines PM justifies by definitions ("[(4).(✱9·06)]") are listed with how
  Lean checks them: `by_defs` in a proof for every reading checks the step under the definitions as
  printed (A and C), those of ✱9+ (L) and of B; a plain step in a proof stated for one reading is
  checked under that reading only.

Usage (from the repository root, after `lake build`):
  python3 scripts/star9_readings.py          write docs/STAR9_READINGS.md
  python3 scripts/star9_readings.py --check  exit 1 if the file is not up to date
"""
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "docs" / "STAR9_READINGS.md"
STAR9 = ROOT / "PM" / "Found9" / "Star9.lean"
READINGS = ["A", "C", "L", "B"]
NAMES = {"A": "A, as printed", "C": "C, as printed + ✱8·13 (working, default)",
         "L": "L, Landini's ✱9+ (published variant, cross-check)",
         "B": "B, alternative convention (cross-check)"}
STMT = {"A": "Reading.printed", "C": "Reading.russell", "L": "Reading.withSwitch",
        "B": "Reading.convention"}
RULE = {"C": "✱8·13", "L": "Switch"}
KINDS = {"AE": "(x)(∃y)", "EA": "(∃x)(y)", "AA": "(x)(y)", "EE": "(∃x)(∃y)"}
# combinations of p. 142 besides the all-elementary one, per ✱1 primitive (letters: 1, 2, 2, 3, 3)
COMBOS = {"*1.2": 2, "*1.3": 8, "*1.4": 8, "*1.5": 26, "*1.6": 26}
# a citation of a definition: ✱1·01 or one of ✱9·01–✱9·08, inside parentheses
DEF_CITE = re.compile(r"\((?:[^()]*?)(?:✱1·01|✱9·0[1-8])")


def star(i):
    return i.replace("*", "✱").replace(".", "·")


def lean_results():
    p = subprocess.run(["lake", "env", "lean", "Checks/Star9Readings.lean"], cwd=ROOT,
                       capture_output=True, text=True, timeout=3600)
    if p.returncode != 0:
        raise SystemExit(f"Checks/Star9Readings.lean failed:\n{p.stdout}{p.stderr}")
    rows = [json.loads(l) for l in p.stdout.splitlines() if l.startswith("{")]
    kind = lambda k: [r for r in rows if r["kind"] == k]
    uses = {r: [u for u in kind("use") if u["reading"] == r] for r in ("C", "L")}
    return (kind("prop"), {r["name"]: r for r in kind("decl")},
            {r["reading"]: r["open"] for r in kind("simul")}, uses, kind("combo"))


def definitional_steps():
    """[(theorem, line number, PM's citation, how Lean checks it)] for PM/Found9/Star9.lean.

    A step is a line whose trailing comment cites a definition. The code of the step runs back to the
    line that starts it (`have`, `:=`, or the first line of the proof term)."""
    lines = STAR9.read_text(encoding="utf-8").split("\n")
    steps, thm, stmt, start, in_doc = [], None, "", 0, False
    for i, line in enumerate(lines):
        # docstrings and block comments (`/-- … -/`, `/-! … -/`) are not proof lines
        if in_doc or line.lstrip().startswith("/-"):
            in_doc = "-/" not in line
            continue
        m = re.match(r"(?:theorem|def) (\S+)", line)
        if m:
            thm, stmt, start = m.group(1), line, i
            continue
        if thm and not stmt.rstrip().endswith(":=") and ":=" not in stmt.split("--")[0]:
            stmt += " " + line
        code, _, comment = line.partition("--")
        if re.match(r"\s*(have |by_defs|fun |Thm9|exI|emp|h\d)", code) or ":=" in code:
            start = i
        if thm is None or not DEF_CITE.search(comment):
            continue
        span = " ".join(l.partition("--")[0] for l in lines[start:i + 1])
        generic = "Reading." not in stmt.split(":=")[0]
        if "by_defs" in span:
            if not generic:
                raise SystemExit(f"Star9.lean:{i + 1}: by_defs in {thm}, which is not stated for every reading")
            how = "ACLB"
        elif generic:
            how = "plain"  # checked by Lean for every reading without splitting: ✱9·01·02 only
        else:
            how = "only:" + ",".join(r for r in READINGS if STMT[r] in stmt)
        steps.append((thm, i + 1, comment.strip(), how))
    return steps


def cells_of(f):
    return " | ".join(f(r) for r in READINGS)


def code(n):
    return f"`{n.removeprefix('PM.F9.')}`"


def kinds_str(ks):
    """Occurrences of ✱8·13 by the kinds of the quantifiers exchanged, e.g. "2 of (x)(∃y), 1 of (∃x)(∃y)"."""
    counts = {}
    for k in ks:
        counts[k] = counts.get(k, 0) + 1
    return ", ".join(f"{n} of {KINDS.get(k, k)}" for k, n in counts.items())


def render():
    props, decls, simul, uses, combos = lean_results()
    steps = definitional_steps()
    numbered = [p for p in props if p["id"].startswith("*9.")]
    tenth = [p for p in props if p["id"].startswith("*10.")]
    out = []
    w = out.append
    w("# ✱9 under four readings")
    w("")
    w("Generated by `scripts/star9_readings.py` from `Checks/Star9Readings.lean` (which reads the Lean")
    w("statements and measures where the proofs use the exchange rules) and from the proofs in")
    w("`PM/Found9/Star9.lean`; do not edit by hand. `tests/test_star9_readings.py` checks that this file is")
    w("up to date and pins its numbers. The readings and the repairs behind them:")
    w("[REPAIRS.md](REPAIRS.md); the foundation: [STAR9_FOUNDATION.md](STAR9_FOUNDATION.md). Every result")
    w("here is **[MEAS]**.")
    w("")
    w("- **A, as printed**: ✱9·01–✱9·08 as printed (`PF.orPrinted`, `Reading.printed`), kept so that what")
    w("  PM printed stays visible.")
    w("- **C, as printed + ✱8·13 (working, default)**: the same definitions, and Russell's rule ✱8·13 of")
    w("  the second edition (1925, Vol. I, Appendix A, p. 636) carried over to ✱9 (`Reading.russell`,")
    w("  `Thm9.exch`; R1, R2 in REPAIRS.md): the authors' own repair.")
    w("- **L, Landini's ✱9+ (published variant, cross-check)**: Landini's repair of ✱9 (2000, p. 64):")
    w("  ✱9·01–✱9·08 as printed, ✱9·yy and ✱9·zz for two quantifiers of the same kind (`PF.orPlus`), and")
    w("  the rule Switch (`Reading.withSwitch`; R3). Kept as a checked variant, credited; not the default.")
    w("- **B, alternative convention (cross-check)**: a precedence convention of our own read off PM's")
    w("  proofs (`PF.or`, `Reading.convention`; R4). It is not the default and not precedent. It is kept")
    w("  because a second, independent way of reading the text also makes PM's proof of ✱9·31 go through,")
    w("  which shows that the ambiguity there is real, and because where B and C agree, neither repair")
    w("  changes anything beyond ✱9·31.")
    w("")
    w("## Summary")
    w("")
    w("| | " + " | ".join(NAMES[r] for r in READINGS) + " |")
    w("|---|" + "---|" * len(READINGS))
    w("| numbered ✱9 propositions (✱9·2–✱9·521) derived along PM's Dem. lines | " + cells_of(
        lambda r: f"{sum(r in p['readings'] for p in numbered)} of {len(numbered)}") + " |")
    w("| not derived | " + cells_of(
        lambda r: ", ".join(star(p["id"]) for p in numbered if r not in p["readings"]) or "none") + " |")
    w("| ✱10·01, ✱10·1, ✱10·11, ✱10·12 (✱10·12 for an elementary p) | " + cells_of(
        lambda r: f"{sum(r in p['readings'] for p in tenth)} of {len(tenth)}") + " |")
    total = sum(COMBOS.values())
    w("| p. 142, one apparent variable per letter: combinations proved | " + cells_of(
        lambda r: f"{total - sum(len(v) for v in simul[r].values())} of {total}") + " |")

    def uncovered(r):
        parts = [f"{star(k)} {', '.join('`' + c + '`' for c in v)}" for k, v in simul[r].items() if v]
        return "; ".join(parts) if parts else "none"
    w("| not covered (forms of p, q, r) | " + cells_of(uncovered) + " |")
    every_p = {"A": "given `Rep` and a variable of every type (`Rep.distrib`)",
               "C": "given `Rep` and a variable of every type (`Rep.distrib`)",
               "L": "given `Rep` and a variable of every type (`Rep.distrib`)",
               "B": "yes, from the primitive propositions (`distrib_convention`)"}
    assert decls["PM.F9.distrib_convention"]["exists"] and decls["PM.F9.distrib_convention"]["readings"] == ["B"]
    assert decls["PM.F9.Rep.distrib"]["readings"] == READINGS
    w("| ✱10·12 (= ✱9·25) for every p | " + cells_of(lambda r: every_p[r]) + " |")
    assert decls["PM.F9.star9_iff_star10"]["readings"] == READINGS
    w("| `star9_iff_star10` (✱9's method agrees with ✱10's) | " + cells_of(
        lambda r: "given a variable of every type and `Rep` of the reading") + " |")
    disagree = [s for s in steps if s[3].startswith("only:")]
    w("| \"by definitions\" steps of the Dem. lines that are not definitional rewrites under the reading's definitions | " + cells_of(
        lambda r: str(sum(r not in s[3] for s in disagree))) + " |")

    def rule_cell(r):
        if r not in RULE:
            return "none (no rule)"
        n = sum(u["direct"] for u in uses[r] if u["id"].startswith("*9."))
        return f"{RULE[r]}: {n} (✱9·31, (3)–(4))"
    w("| exchange rule; steps of PM's own proofs it takes | " + cells_of(rule_cell) + " |")

    def needing(r):
        if r not in RULE:
            return "—"
        res = [star(u["id"]) for u in uses[r] if u["closure"] > 0]
        n = sum(1 for c in combos if c[f"proved{r}"] and (c[f"steps{r}"] or 0) > 0)
        return ", ".join(res) + f"; {n} combinations of p. 142"
    w("| results whose proofs use the rule | " + cells_of(needing) + " |")
    w("")
    w("Notes:")
    w("")
    w("- In C and in L, ✱9·31 is derived along PM's lines with the step (3)–(4) taken by the exchange rule")
    w("  instead of by definitions (`f9_31_russell`, `f9_31_switch`); that step is not a definitional")
    w("  rewrite under the definitions as printed, which A and C share (`f9_31_step`), nor in L")
    w("  (`f9_31_step_plus`). Landini found this flaw (2000, §4): \"Unique among all the demonstrations of")
    w("  ✱9, this one misapplies the definition ✱9.03.\" Under A ✱9·31 is not derived, and whether ✱9's")
    w("  primitive propositions derive it by another route under A is open.")
    w("- C has A's definitions, so every proposition of C is the proposition A makes of the same")
    w("  expression; it adds one rule. L's definitions differ from A's where two quantifiers of the same")
    w("  kind meet and the left side has a further quantifier (R2, R3).")
    for n in ("PM.F9.exchStep_q10", "PM.F9.switchStep_q10", "PM.F9.switch_wide_unsound",
              "PM.F9.switch_russell", "PM.F9.exch_plus", "PM.F9.Thm9.russell_toPrenex",
              "PM.F9.exch_not_general"):
        assert decls[n]["exists"], n
    assert decls["PM.F9.switch_russell"]["readings"] == ["C"] and decls["PM.F9.exch_plus"]["readings"] == ["L"]
    w("- Both rules are derivable by ✱10's method (`exchStep_q10`, `switchStep_q10`), so C and L are sound")
    w("  in every structure with an individual (`thm9_sound`); neither is a general exchange of")
    w("  quantifiers (`exch_not_general`, `switch_not_general`). Their side condition (`Sep`) is")
    w("  formalized with a restriction that neither Russell's wording nor Landini's states: without it the")
    w("  rule is unsound (`switch_wide_unsound`; REPAIRS.md, R1).")
    w("- C and L: Landini's Switch is the (x)(∃y) to (∃y)(x) direction of ✱8·13, so it is a derived rule")
    w("  of C (`switch_russell`); every step of ✱8·13 is derivable in L (`exch_plus`: the converse")
    w("  direction without Switch, the exchanges of two quantifiers of the same kind with one step of")
    w("  Switch each). Whether C and L prove the same expressions (each in its own order of quantifiers)")
    w("  is open.")
    p_total = total - sum(len(v) for v in simul["P"].values())
    w("- The prenex Switch (R5), our earlier repair, kept for comparison: every theorem of C is a theorem")
    w("  with it (`Thm9.russell_toPrenex`); with it every theorem of B is a theorem of the definitions as")
    w("  printed (`Thm9.convention_toSwitch`), `Rep` for B gives `Rep` there (`Rep.toSwitch`), ✱10·12")
    w(f"  holds for every p without `Rep` (`distrib_switch`), and p. 142 has {p_total} of {total} combinations")
    w("  (`PrenexSwitch.t1_2` …). Whether C or L derives it is open.")
    w("- Under B, the three combinations of ✱1·6 left open have no proof by ✱9·13, ✱9·1 and ✱9·11 alone")
    w("  (PM/Found9/Simul.lean); whether those left open under A, C and L have a longer proof is open.")
    w("")
    render_rules(w, uses, decls, combos)
    w("## Steps PM justifies by definitions")
    w("")
    by = {k: [s for s in steps if s[3] == k] for k in ("ACLB", "plain")}
    w(f"PM/Found9/Star9.lean has {len(steps)} lines whose justification cites a definition (✱1·01,")
    w("✱9·01–✱9·08). Lean checks each as \"the same proposition as the line before\":")
    w("")
    w(f"- {len(by['ACLB'])} with `by_defs`, in proofs stated for every reading: checked under the")
    w("  definitions as printed (A and C), those of L and those of B (the proof splits on the reading's")
    w("  definitions);")
    if by["plain"]:
        w(f"- {len(by['plain'])} without, in proofs for every reading (steps by ✱9·01, ✱9·02, which the")
        w("  readings share);")
    w(f"- {len(disagree)} in a proof stated for one reading only, because under the other definitions")
    w("  the two lines are different propositions:")
    w("")
    w("| Theorem | Line of Star9.lean | PM's justification | Checked under | Under the other definitions |")
    w("|---|---|---|---|---|")
    for thm, ln, cite, how in disagree:
        other = ("different propositions in A and C (`f9_31_step`) and in L (`f9_31_step_plus`); in C the "
                 "step is taken by ✱8·13 (`f9_31_russell`), in L by Switch (`f9_31_switch`)") \
            if thm == "f9_31" else "see the theorem"
        w(f"| `{thm}` | {ln} | `{cite}` | {how[5:]} | {other} |")
    w("")
    w("Every step checked under all three definitions, by theorem:")
    w("")
    w("| Theorem | PM's justifications |")
    w("|---|---|")
    seen = {}
    for thm, ln, cite, how in steps:
        if how in ("ACLB", "plain"):
            seen.setdefault(thm, []).append(cite)
    for thm, cites in seen.items():
        w(f"| `{thm}` | " + "; ".join(f"`{c}`" for c in cites) + " |")
    w("")
    return "\n".join(out)


def render_rules(w, uses, decls, combos):
    """The section "Where the exchange rule is used", for C (✱8·13) and L (Switch)."""
    w("## Where the exchange rule is used")
    w("")
    w("What is counted (Checks/Star9Readings.lean). The rule is ✱8·13 (`Thm9.exch`) in C and Switch")
    w("(`Thm9.switch`) in L. For a Lean declaration, *direct* is the number of occurrences of the rule in")
    w("its own proof term, and *through lemmas* the number of occurrences in the proof terms of the")
    w("declaration and of every declaration it uses, directly or through others, each counted once. A")
    w("lemma stated for other readings only is not followed (a lemma stated for every reading reaches it")
    w("only in another reading's branch), so *through lemmas* is an upper bound on what the reading's")
    w("proof uses. Each occurrence of ✱8·13 is also listed by the kinds of the two quantifiers it")
    w("exchanges, (x)(∃y) or (∃x)(∃y) (none of (∃x)(y) or (x)(y) occurs). For a combination of p. 142 the")
    w("search is run again on the reading's proposition, first without the rule, then with it; *steps*")
    w("is the number of steps of the rule in the proof found (each use of a lemma counts that lemma's")
    w("occurrences). \"Derived under A\" means derived by our proofs under A's definitions, without a")
    w("rule, as the same proposition; \"not derived\" means not derived by our proofs, and whether ✱9's")
    w("rules derive it by a longer route stays open.")
    w("")
    w("**(a) Steps of PM's own proofs taken by the rule.**")
    w("")
    for r in ("C", "L"):
        pm_steps = [(u["id"], u["decl"], u["direct"], u["kinds"]) for u in uses[r]
                    if u["id"].startswith("*9.") and u["direct"] > 0]
        n_pm = sum(d for _, _, d, _ in pm_steps)
        w(f"- {r}, {RULE[r]}: {n_pm}. " + "; ".join(
            f"{star(i)}, step (3)–(4), in {code(d)} ({k} occurrence{'s' if k != 1 else ''}, {kinds_str(ks)})"
            for i, d, k, ks in pm_steps) + ".")
    w("")
    w("Every other line of ✱9's proofs that PM justifies by definitions is a definitional rewrite under")
    w("each reading's definitions (section \"Steps PM justifies by definitions\").")
    w("")
    w("**(b) The numbered propositions and the ✱10 assertions.**")
    w("")
    w("| Result | Proof (C) | Derived under A, the same proposition as C's | ✱8·13 in C: direct | through lemmas | Proof (L) | L's proposition is A's | Switch in L: direct | through lemmas | L's lemmas that use it |")
    w("|---|---|---|---|---|---|---|---|---|---|")
    by_id = {}
    for r in ("C", "L"):
        for u in uses[r]:
            by_id.setdefault(u["id"], {})[r] = u
    groups = {}
    order = []
    for i, d in by_id.items():
        c, l = d["C"], d["L"]
        gen = lambda u: u["decl"] == "PM.F9.f" + u["id"][1:].replace(".", "_")
        key = (gen(c), c["underA"], c["direct"], c["closure"], gen(l), l["sameAsA"], l["direct"],
               l["closure"], tuple(l["via"]))
        if key not in groups:
            order.append(key)
        groups.setdefault(key, []).append((i, c, l))
    for key in order:
        rows = groups[key]
        ids = ", ".join(star(i) for i, _, _ in rows)
        c, l = rows[0][1], rows[0][2]
        cdecl = "for every reading" if key[0] else ", ".join(code(x[1]["decl"]) for x in rows)
        ldecl = "for every reading" if key[4] else ", ".join(code(x[2]["decl"]) for x in rows)
        a = "yes" if c["underA"] else "no"
        la = "yes" if l["sameAsA"] else ("no" if l["underA"] else "A does not derive it")
        vias = ", ".join(code(v) for v in l["via"]) or "none"
        w(f"| {ids} | {cdecl} | {a} | {c['direct']} | {c['closure']} | {ldecl} | {la} | {l['direct']} | {l['closure']} | {vias} |")
    w("")
    for n, what in (("PM.F9.Rep.distrib", "✱10·12 for every p, given `Rep` (`Rep.distrib`)"),
                    ("PM.F9.qthm_toF9", "every ✱10 theorem, given `Rep` (`qthm_toF9`, `star9_iff_star10`)")):
        d = decls[n]["uses"]
        cv = ", ".join(code(v) for v in d["C"]["via"]) or "none"
        lv = ", ".join(code(v) for v in d["L"]["via"]) or "none"
        w(f"- {what}: ✱8·13 in C through lemmas {d['C']['closure']} ({cv}); Switch in L through lemmas "
          f"{d['L']['closure']} ({lv}).")
    w("")
    w("**(c) The combinations of p. 142.**")
    w("")
    plain_c = [c for c in combos if c["provedC"] and c["stepsC"] == 0]
    with_c = [c for c in combos if c["provedC"] and c["stepsC"] > 0]
    open_c = [c for c in combos if not c["provedC"]]
    plain_l = [c for c in combos if c["plainL"]]
    plain_la = [c for c in plain_l if c["provedA"] and c["sameAsA"]]
    with_l = [c for c in combos if c["provedL"] and not c["plainL"]]
    open_l = [c for c in combos if not c["provedL"]]
    assert all(c["provedA"] for c in plain_c) and all(not c["provedA"] for c in with_c)
    w(f"Of {len(combos)} combinations, C proves {len(plain_c) + len(with_c)}: {len(plain_c)} without ✱8·13")
    w(f"(exactly those derived under A, the same propositions), and {len(with_c)} with it; {len(open_c)} are")
    w(f"not covered. L proves {len(plain_l) + len(with_l)}: {len(plain_l)} without Switch ({len(plain_la)} of them")
    w(f"also derived under A, the same proposition), and {len(with_l)} with it; {len(open_l)} are not covered.")
    w("")
    w("| Combination | Steps of ✱8·13 in C (kinds) | Steps of Switch in L | Derived under A | L's proposition is A's |")
    w("|---|---|---|---|---|")
    for c in combos:
        if not ((c["provedC"] and c["stepsC"] > 0) or (c["provedL"] and not c["plainL"])):
            continue
        sc = f"{c['stepsC']} ({kinds_str(c['kindsC'])})" if c["provedC"] else "not covered"
        sl = str(c["stepsL"]) if c["provedL"] and not c["plainL"] else ("0" if c["plainL"] else "not covered")
        w(f"| {star(c['id'])} | {sc} | {sl} | {'yes' if c['provedA'] else 'no'} | {'yes' if c['sameAsA'] else 'no'} |")
    w("")
    w("Not covered in C: " + ", ".join(star(c["id"]) for c in open_c) + ".")
    w("Not covered in L: " + ", ".join(star(c["id"]) for c in open_l) + ".")
    diff = [c for c in combos if not c["sameAsA"]]
    w("Where L's proposition is not A's and C's (✱9·yy and ✱9·zz take the sides' quantifiers out in pairs): " +
      ", ".join(star(c["id"]) for c in diff) + "; of these A derives " +
      (", ".join(star(c["id"]) for c in diff if c["provedA"]) or "none") + ", C " +
      (", ".join(star(c["id"]) for c in diff if c["provedC"]) or "none") + ".")
    w("")
    ks_c = [k for c in with_c for k in c["kindsC"]]
    n_c = sorted({c["stepsC"] for c in with_c})
    n_l = sorted({c["stepsL"] for c in with_l})
    res_c = [star(u["id"]) for u in uses["C"] if u["closure"] > 0]
    res_l = [star(u["id"]) for u in uses["L"] if u["closure"] > 0]
    others = sum(1 for u in uses["C"] if u["id"].startswith("*9.") and u["closure"] == 0)
    w("**(d) In short.** In C, ✱8·13 takes one step of PM's own proofs, the step (3)–(4) of ✱9·31 that")
    w(f"Landini found misapplies ✱9·03; the other {others} numbered propositions of ✱9 and the four ✱10")
    w("assertions are derived in C without it, each the same proposition as under A. So the results")
    w(f"that need ✱8·13 at all are {', '.join(res_c)}, and, of the {len(combos)} combinations of p. 142, {len(with_c)},")
    w(f"with {'–'.join(str(s) for s in (n_c[0], n_c[-1]))} steps each ({kinds_str(ks_c)}); {len(open_c)} combinations are not covered in C")
    assert res_l == ["✱9·31", "✱10·1"], res_l
    w("even with it, by our proofs. In L, Switch is needed for ✱9·31, for ✱10·1 for every function")
    w("(through `exDrinker_plus`, where ✱9·zz puts an existential quantifier of φy before the universal one")
    w(f"whose variable it needs), and for {len(with_l)} combinations, with {'–'.join(str(s) for s in (n_l[0], n_l[-1]))} steps each. \"Need\"")
    w("means: our proofs use it; whether ✱9's rules derive these results without it by a longer route is")
    w("open.")
    w("")


def main():
    text = render()
    if "--check" in sys.argv:
        if not OUT.exists() or OUT.read_text(encoding="utf-8") != text:
            print("docs/STAR9_READINGS.md is not up to date: run python3 scripts/star9_readings.py")
            sys.exit(1)
        print("docs/STAR9_READINGS.md is up to date")
        return
    OUT.write_text(text, encoding="utf-8")
    print(f"wrote {OUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
