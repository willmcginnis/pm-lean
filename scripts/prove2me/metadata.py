#!/usr/bin/env python3
"""Titles, descriptions and proof explanations for the cards and definition bundles of a Prove2Me export
(scripts/prove2me/export.py): writes <work>/out/metadata.json.

A card's title is `PM ✱N·M (Name): <formula>`, PM's own name when PM gives one. Its description (the
platform's natural_language_statement, Markdown with KaTeX) follows the platform's guidelines
(references/contribute.md of the Prove2Me skill): context for every symbol, the formula in a display
block, a paragraph on its role, and Lean-specific matters last, under **Formalization Note**. It begins
with a DRAFT line pointing to the dated change log (docs/EXPORT_LOG.md); then PM's statement as printed
and its page; then, under the note, the Lean or Mathlib counterpart when there is one, and a link to the
declaration at the commit exported; and, for a statement of ✱9 by its own method, the reading it is
stated under.

Sources, all read from the commit exported:
  formulas      scripts/prove2me/render_formulas.lean, from the elaborated statement definitions
  printed text  data/vol1.jsonl: PM's printed statement (Gutenberg #78050 transcription) and page
  PM's names    data/naming/pm_names.json; the three laws PM's Introduction gives with their numbers
  counterparts  data/naming/counterparts.json
  readings      data/naming/readings.json
  proofs        data/replay_ledger.json, data/replay2_ledger.json
  notes         docs/FIDELITY.md, "What the proofs found in the text"

Usage (from the repository root, after export.py): python3 scripts/prove2me/metadata.py [--work DIR]
"""
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
from export import load_config, paths  # noqa: E402

TITLE_MAX = 200
# the Introduction's laws given with their numbers (Vol. I, Introduction, ch. I, "Some simple propositions")
PM_INTRO = {"*2.11": "the law of excluded middle", "*3.24": "the law of contradiction",
            "*4.13": "the law of double negation"}
# what the proofs found in the text (docs/FIDELITY.md)
STATEMENT_NOTES = {
    "*1.4": "The Gutenberg transcription prints the consequent as $p \\lor p$; the 1910 print has "
            "$q \\lor p$, which is what is stated here. The transcribed variant is not a theorem "
            "(the card `PM.meta_perm_variant_not_thm`).",
}
PROOF_NOTES = {
    "*4.42": "On line (2) the 1910 print cites ✱3·26, which the Gutenberg transcription omits; "
             "✱3·26 is therefore counted as PM's own citation here.",
    "*4.32": "In line (1) the 1910 print cites ✱4·12 for a step that is ✱2·03 taken both ways "
             "(an apparent slip in the print, awaiting a human check).",
    "*4.43": "PM's ✱2·65 (∼p/p) yields ∼(∼p) where the line prints p; PM drops the double negation "
             "without citing ✱2·14 (an apparent slip in the print, awaiting a human check).",
}
CTOR = {"*1.2": "taut", "*1.3": "add", "*1.4": "perm", "*1.5": "assoc", "*1.6": "sum"}
REPO_NAMES = {"lean4": "Lean core", "mathlib4": "Mathlib"}

SETTING = ("Formulas of PM's propositional calculus are built from propositional variables by negation "
           "${\\sim}$ and disjunction $\\lor$, PM's two primitive ideas (✱1). Implication, conjunction and "
           "equivalence are PM's definitions: $p \\supset q$ is ${\\sim}p \\lor q$ (✱1·01), $p \\land q$ "
           "(PM writes $p\\,.\\,q$) is ${\\sim}({\\sim}p \\lor {\\sim}q)$ (✱3·01), and $p \\equiv q$ is "
           "$(p \\supset q) \\land (q \\supset p)$ (✱4·01). A *theorem of ✱1* is a formula derivable "
           "from the primitive propositions ✱1·2–✱1·6 by the rule of inference ✱1·1 (from $p$ and "
           "$p \\supset q$, infer $q$).")
LEAN_NOTE = ("**Formalization Note** Deep embedding of PM ✱1: formulas are the inductive type `PM.F` "
             "(variables named by strings), the theorems of ✱1 are the inductive predicate `PM.Thm`, "
             "whose constructors are ✱1·1–✱1·6, and ✱1·01, ✱3·01, ✱4·01 are reducible definitions "
             "(`F.imp`, `F.and`, `F.iff`), so PM's definitions hold by definition. {what} Brackets are "
             "written out in full here in place of PM's dots.")


def star(pm):
    """*2.01 -> ✱2·01"""
    return "✱" + pm[1:].replace(".", "·")


def draft(cfg):
    return (f"**DRAFT** — part of an in-progress public formalization of *Principia Mathematica*; it may "
            f"still change, and every change is dated in the project's [change log]({cfg['log_url']}).")


def counterpart_line(r, cps):
    repo = cps["repositories"][r["repository"]]
    path, line = r["source"].rsplit(":", 1)
    url = f"{repo['url']}/blob/{r['commit']}/{path}#L{line}"
    where = (f"Lean core {repo['version']}" if r["repository"] == "lean4"
             else f"Mathlib at {r['commit'][:7]}")
    notes = [where]
    if r["classical"]:
        notes.append("its proof is classical")
    if r["iff_reversed"]:
        notes.append("with the two sides of an equivalence the other way round")
    if r.get("specialized"):
        notes.append("specialized from `Sort` to `Prop`")
    return (f"Lean/Mathlib counterpart: [`{r['declaration']}`]({url}) ({'; '.join(notes)}). It states the same "
            "law for Lean's own propositions, connective for connective.")


def main(argv):
    cfg = load_config()
    work = os.path.abspath(argv[argv.index("--work") + 1]) if "--work" in argv else os.path.join(ROOT, ".lake", "prove2me")
    P = paths(work)
    repo, out = P["repo"], P["out"]
    man = json.load(open(os.path.join(out, "manifest.json"), encoding="utf-8"))
    r = subprocess.run(["lake", "env", "lean", os.path.join(repo, "scripts", "prove2me", "render_formulas.lean")], cwd=repo,
                       capture_output=True, text=True)
    assert r.returncode == 0, r.stdout + r.stderr
    forms = json.load(open(os.path.join(repo, "formulas.json"), encoding="utf-8"))
    load = lambda *p: json.load(open(os.path.join(repo, *p), encoding="utf-8"))
    vol1 = {}
    for l in open(os.path.join(repo, "data", "vol1.jsonl"), encoding="utf-8"):
        x = json.loads(l)
        vol1.setdefault(x["id"], x)
    led1 = {x["id"]: x for x in load("data", "replay_ledger.json")}
    led2 = {x["id"]: x for x in load("data", "replay2_ledger.json")}
    pm_names = {r["number"]: r["name"] for r in load("data", "naming", "pm_names.json")["names"]}
    cps = load("data", "naming", "counterparts.json")
    cp_by = {r["export"]: r for r in cps["counterparts"]}
    readings = {r["word"]: r for r in load("data", "naming", "readings.json").values()}
    entries = {e["export"]: e for e in load("data", "export_names.json")}
    bundles = {b["name"]: b for b in load("data", "naming", "definition_bundles.json")["bundles"]}
    commit = man["commit"]
    meta = {"definitions": {}, "nodes": {}}
    for nd in man["nodes"]:
        n = nd["theorem_name"]
        e = entries[n]
        if e.get("meta"):
            meta["nodes"][n] = special(n, nd, cfg)
            continue
        pm = e["pm"]
        f = forms[f"PM.s{pm[1:].replace('.', '_')}"]
        v = vol1.get(pm, {})
        page = v.get("page")
        pname = pm_names.get(pm)
        label = star(pm) + (f" ({pname})" if pname else "")
        title = f"PM {label}: ${f['latex']}$"
        if len(title) > TITLE_MAX:
            title = f"PM {label}: {f['text']}"
        assert len(title) <= TITLE_MAX, (n, len(title))
        binders = f["binders"]
        vars_ = ", ".join(f"${b}$" for b in binders)
        printed = (v.get("statement") or "").replace("\\begin{align}", "\\begin{aligned}").replace("\\end{align}", "\\end{aligned}")
        is_pp = nd["kind"] == "constructor"
        body = [draft(cfg),
                f"**Principia Mathematica {label}**: Whitehead and Russell, *Principia Mathematica*, Vol. I (1910), "
                f"Part I, Section A{', p. ' + str(page) if page else ''}."
                + (f" PM prints (Gutenberg #78050 transcription):\n\n$$\n{printed}\n$$" if printed else ""),
                SETTING,
                (f"For all formulas {vars_}, the formula" if len(binders) > 1 else f"For every formula {vars_}, the formula"),
                f"$$\n{f['latex']}\n$$",
                ("is a theorem of ✱1." if not is_pp else
                 "is a theorem of ✱1: it is one of PM's primitive propositions (Pp), so it is asserted outright.")]
        if pm in STATEMENT_NOTES:
            body.append(STATEMENT_NOTES[pm])
        role = []
        if pname:
            role.append(f"PM refers to this proposition by the name **{pname}** (Vol. I, *Alphabetical list of "
                        "propositions referred to by names*), and cites it by that name in later proofs.")
        if pm in PM_INTRO:
            role.append(f"PM's Introduction lists it as {PM_INTRO[pm]}, among \"the most important of the elementary "
                        "properties of propositions appearing among the deductions\".")
        if not role:
            role.append(f"It is one of the propositions of {star(pm.split('.')[0])} from which PM builds the "
                        "propositional calculus used throughout the work.")
        body.append(" ".join(role))
        what = ("The statement is the type of the constructor `PM.Thm." + CTOR[pm] + "`." if is_pp else
                f"The statement formula is the definition `PM.s{pm[1:].replace('.', '_')}` of the bundle "
                "`PM_core_statement_formulas`.")
        body.append(LEAN_NOTE.format(what=what))
        if e.get("reading"):
            rd = readings[e["reading"]]
            body.append(f"Stated under the reading **{e['reading']}** of ✱9's definitions: {rd['meaning']}.")
        if n in cp_by:
            body.append(counterpart_line(cp_by[n], cps))
        body.append(f"Source: [`{nd['lean']}` in {nd['source'].split('/blob/', 1)[1].split('/', 1)[1].split('#')[0]}]"
                    f"({nd['source']}) at commit {commit[:12]}.")
        nls = "\n\n".join(body)
        source = (f"Whitehead and Russell, Principia Mathematica, Vol. I (1910), {star(pm)}"
                  + (f", p. {page}" if page else "") + f"; formalization: {nd['source']}")
        meta["nodes"][n] = {"theorem_title": title, "natural_language_statement": nls, "source": source,
                            "tags": [], "explanation": explanation(pm, label, f, vars_, nd, led1, led2, is_pp),
                            "pm": pm, "pm_name": pname, "page": page, "formula_latex": f["latex"]}
    for d in man["definitions"]:
        meta["definitions"][d["definition_name"]] = definition_meta(d, cfg, bundles, repo, out)
    json.dump(meta, open(os.path.join(out, "metadata.json"), "w", encoding="utf-8"), indent=1, ensure_ascii=False)
    longest = max(len(m["theorem_title"]) for m in meta["nodes"].values())
    print(f"metadata: {len(meta['definitions'])} definitions, {len(meta['nodes'])} cards, longest title {longest} characters")


def explanation(pm, label, f, vars_, nd, led1, led2, is_pp):
    expl = [f"We prove PM {label}:", f"$$\n{f['latex']}\n$$", "for all formulas " + vars_ + ", as a theorem of PM's system ✱1."]
    if is_pp:
        expl.append(f"{star(pm)} is a primitive proposition of PM, so the derivation is one step: the constructor "
                    f"`PM.Thm.{CTOR[pm]}` of the theorems of ✱1, at the given formulas.")
    elif pm in led2:
        L = led2[pm]
        cited = ", ".join(star(c) for c in L["cited_used"]) or "nothing"
        expl.append(f"**Proof idea.** The derivation follows PM's own demonstration ({L['note']}). "
                    f"PM's citations used: {cited}.")
        if L["extra_used"]:
            expl.append("**Steps PM leaves tacit.** The derivation also uses "
                        + ", ".join(star(c) for c in L["extra_used"])
                        + (f", which PM does not cite: {L['reason']}" if L["reason"] else ", which PM does not cite."))
        if L.get("tacit"):
            expl.append("Tacit steps done by derived rules: "
                        + ", ".join(re.sub(r"\*(\d+)\.(\d+)", lambda m: star(f"*{m.group(1)}.{m.group(2)}"), t)
                                    for t in L["tacit"]) + ".")
    elif pm in led1:
        L = led1[pm]
        cited = ", ".join(star(c) for c in L["cited"]) or "nothing"
        expl.append(f"**Proof idea.** The derivation replays PM's demonstration, which cites {cited}"
                    + (". It is FAITHFUL: it uses exactly PM's citations." if L["tag"] == "FAITHFUL" else
                       f". It is REPAIRED: it also uses {', '.join(star(c) for c in L['extra'])}, which PM's text "
                       "does not cite (recorded in the source repository's ledger)."))
    if pm in PROOF_NOTES:
        expl.append(PROOF_NOTES[pm])
    if nd["node_deps"]:
        expl.append("**Structure.** The earlier propositions used are imported as their own cards: "
                    + ", ".join(f"`{d}`" for d in nd["node_deps"]) + ".")
    if nd["helpers"]:
        expl.append("The derived rules used (syllogism as a rule, and the natural-deduction layer of "
                    "`PM/Derived.lean`, where $\\Gamma \\vdash \\varphi$ is by definition the theorem "
                    "$h_1 \\supset (h_2 \\supset \\cdots \\supset \\varphi)$) are copied into the solution unchanged "
                    f"from the source repository ({len(nd['helpers'])} declarations); each is itself an explicit "
                    "derivation from the constructors of `PM.Thm` and earlier propositions.")
    if nd["macro_uses_expanded"]:
        expl.append("The source proof uses the tactic abbreviations `intro_` (the deduction theorem) and "
                    "`split_iff` of `PM/Derived.lean`; this platform does not accept macro declarations in a "
                    "submission, so each use is written out as its own one-line expansion.")
    if nd["references_renamed"]:
        expl.append("References to other cards use their names on this platform (in the source repository "
                    f"they have shorter Lean names, e.g. `{nd['lean']}` for this one).")
    expl.append(f"Source proof: {nd['source']}.")
    return "\n\n".join(expl)


def special(n, nd, cfg):
    src = nd["source"]
    link = f"Source: [`{nd['lean']}`]({src})."
    if n == "PM.meta_sound":
        return {"theorem_title": "PM ✱1 (about the system): soundness of ✱1 for two-valued truth tables",
                "natural_language_statement": "\n\n".join([
                    draft(cfg),
                    "**Soundness of the primitive system ✱1 of *Principia Mathematica*.**",
                    "Let $\\varphi$ be a formula of PM's propositional calculus (built from propositional variables "
                    "by ${\\sim}$ and $\\lor$; $\\supset$, $\\land$, $\\equiv$ are PM's definitions ✱1·01, ✱3·01, "
                    "✱4·01). A *valuation* $v$ assigns a truth value to every propositional variable; "
                    "$\\llbracket\\varphi\\rrbracket_v$ is the truth value of $\\varphi$ computed by the usual tables "
                    "(${\\sim}$ is negation, $\\lor$ is inclusive or). If $\\varphi$ is a theorem of ✱1 (derivable "
                    "from ✱1·2–✱1·6 by ✱1·1), then",
                    "$$\n\\llbracket\\varphi\\rrbracket_v = \\mathrm{true} \\quad\\text{for every valuation } v.\n$$",
                    "This is not a proposition of PM; it is a result about PM's system. It turns a falsifying "
                    "valuation into a proof that a formula is *not* a theorem, which is how transcription errors in "
                    "the source text are detected (the card `PM.meta_perm_variant_not_thm`).",
                    "**Formalization Note** `PM.F.eval v φ : Bool` is the truth-table value; valuations are "
                    "functions from variable names (strings) to `Bool`.", link]),
                "source": f"About Whitehead and Russell, Principia Mathematica, Vol. I (1910), ✱1; formalization: {src}",
                "tags": [], "pm": None,
                "explanation": ("We prove that every theorem of ✱1 is true under every valuation, by induction on the "
                                "derivation. **Base cases.** Each primitive proposition ✱1·2–✱1·6 is a tautology: a "
                                "case split on the truth values of its (at most three) formulas checks it. **Step.** "
                                "If $p$ and $p \\supset q$, i.e. ${\\sim}p \\lor q$, are true under $v$, then $q$ is "
                                f"true under $v$ (✱1·1 preserves truth).\n\nSource proof: {src}.")}
    if n == "PM.meta_complete":
        return {"theorem_title": "PM ✱1 (about the system): completeness of ✱1 for two-valued truth tables",
                "natural_language_statement": "\n\n".join([
                    draft(cfg),
                    "**Completeness of the primitive system ✱1 of *Principia Mathematica*.**",
                    "Let $\\varphi$ be a formula of PM's propositional calculus (built from propositional variables "
                    "by ${\\sim}$ and $\\lor$; $\\supset$, $\\land$, $\\equiv$ are PM's definitions ✱1·01, ✱3·01, "
                    "✱4·01). Call $\\varphi$ a *tautology* if it is true under every assignment of truth values to "
                    "the propositional variables occurring in it. Then",
                    "$$\n\\varphi \\text{ is a tautology} \\implies \\varphi \\text{ is a theorem of ✱1},\n$$",
                    "that is, $\\varphi$ is derivable from the primitive propositions ✱1·2–✱1·6 by the rule ✱1·1.",
                    "PM does not state or prove this; it is the completeness theorem for PM's propositional calculus "
                    "(Post, 1921). With the soundness card it shows that the theorems of ✱1 are exactly the "
                    "tautologies.",
                    "**Formalization Note** The hypothesis is the decidable check `PM.F.isTaut φ = true`, which "
                    "evaluates $\\varphi$ under every assignment to the list of its variables (`PM.F.vars`, "
                    "`PM.assignments`).", link]),
                "source": f"About Whitehead and Russell, Principia Mathematica, Vol. I (1910), ✱1; Post (1921); formalization: {src}",
                "tags": [], "pm": None,
                "explanation": ("We prove completeness by Kalmár's method. **Kalmár's lemma.** For a valuation $v$ "
                                "and a list of variables containing those of $\\varphi$, the literals $x^v$ ($x$ if "
                                "$v(x)$ is true, ${\\sim}x$ otherwise) prove $\\varphi^v$ ($\\varphi$ if true under "
                                "$v$, ${\\sim}\\varphi$ otherwise); this is an induction on $\\varphi$ using the derived "
                                "rules of PM's system (∨-introduction from ✱1·3 and ✱2·2, and ${\\sim}a \\supset "
                                "({\\sim}b \\supset {\\sim}(a \\lor b))$). **Discharging the hypotheses.** If "
                                "$\\varphi$ is a tautology, each assignment proves $\\varphi$ from its literals; the "
                                "hypotheses are discharged one variable at a time by the case split on the law of "
                                "excluded middle ✱2·11. Every step is an explicit derivation in ✱1, built from the "
                                "derived rules of `PM/Derived.lean`, which are copied into the solution unchanged, "
                                "except that the two uses of the tactic abbreviation `intro_` are written out as its "
                                "one-line expansion (this platform does not accept macro declarations in a "
                                "submission). References to other cards use their names on this platform."
                                f"\n\nSource proof: {src}.")}
    if n == "PM.meta_perm_variant_not_thm":
        return {"theorem_title": "PM ✱1·4 (about the text): the transcribed $p \\lor q \\supset p \\lor p$ is not a theorem of ✱1",
                "natural_language_statement": "\n\n".join([
                    draft(cfg),
                    "**A check on the text of ✱1·4 (Perm).** PM's primitive proposition ✱1·4 is, in the 1910 print "
                    "(Vol. I, p. 100),",
                    "$$\n(p \\lor q) \\supset (q \\lor p).\n$$",
                    "The Gutenberg #78050 transcription prints $p \\lor p$ in place of $q \\lor p$. Let $p$ and $q$ "
                    "be two distinct propositional variables. Then the transcribed formula",
                    "$$\n(p \\lor q) \\supset (p \\lor p)\n$$",
                    "is **not** a theorem of ✱1 (not derivable from ✱1·2–✱1·6 by ✱1·1, with the 1910 ✱1·4).",
                    "This records, as a checked fact, that the one-letter variant is a transcription slip and not a "
                    "reading of PM: the card for ✱1·4 follows the print.",
                    "**Formalization Note** $p$ and $q$ are the variables named \"p\" and \"q\" (`F.var \"p\"`, "
                    "`F.var \"q\"`), introduced by local notation.", link]),
                "source": f"Whitehead and Russell, Principia Mathematica, Vol. I (1910), ✱1·4, p. 100; Project Gutenberg eBook #78050; formalization: {src}",
                "tags": [], "pm": "*1.4",
                "explanation": ("**Counterexample.** Let $v$ make $p$ false and $q$ true. Then $p \\lor q$ is true and "
                                "$p \\lor p$ is false, so $(p \\lor q) \\supset (p \\lor p)$ is false under $v$. "
                                "**Argument.** By soundness (imported as its own card, `PM.meta_sound`), every theorem "
                                "of ✱1 is true under every valuation; this formula is false under $v$, so it is not a "
                                f"theorem. The truth value is computed by evaluation (`decide`).\n\nSource proof: {src}.")}
    raise SystemExit(f"no metadata for {n}")


DEFS = {
    "PM.Basic": ("PM ✱1: formulas, the theorems of ✱1, truth tables",
                 "The primitive apparatus of Whitehead and Russell's *Principia Mathematica*, ✱1 (Vol. I, 1910, "
                 "pp. 98–101), as a deep embedding.\n\n"
                 "1. **Formulas** $\\mathcal F$: propositional variables, negation ${\\sim}p$ and disjunction "
                 "$p \\lor q$, PM's two primitive ideas.\n"
                 "2. **Defined connectives**, as PM's definitions: $p \\supset q := {\\sim}p \\lor q$ (✱1·01), "
                 "$p \\land q := {\\sim}({\\sim}p \\lor {\\sim}q)$ (✱3·01; PM writes $p\\,.\\,q$), "
                 "$p \\equiv q := (p \\supset q) \\land (q \\supset p)$ (✱4·01).\n"
                 "3. **Theorems of ✱1**: the least set of formulas containing the primitive propositions\n\n"
                 "$$\n\\begin{aligned}&(p \\lor p) \\supset p &&(✱1·2,\\ \\text{Taut})\\\\ "
                 "&q \\supset (p \\lor q) &&(✱1·3,\\ \\text{Add})\\\\ "
                 "&(p \\lor q) \\supset (q \\lor p) &&(✱1·4,\\ \\text{Perm})\\\\ "
                 "&(p \\lor (q \\lor r)) \\supset (q \\lor (p \\lor r)) &&(✱1·5,\\ \\text{Assoc})\\\\ "
                 "&(q \\supset r) \\supset ((p \\lor q) \\supset (p \\lor r)) &&(✱1·6,\\ \\text{Sum})\\end{aligned}\n$$\n\n"
                 "for all formulas $p, q, r$, and closed under the rule ✱1·1: from $p$ and $p \\supset q$ infer $q$.\n"
                 "4. **Truth tables**: the two-valued value of a formula under a valuation, the variables of a formula, "
                 "and the decidable test that a formula is a tautology.\n\n"
                 "The card of each numbered proposition of ✱1–✱5 states that its formula is a theorem of ✱1 in "
                 "this sense.\n\n"
                 "**Formalization Note** PM states the primitive propositions with real variables and a rule of "
                 "substitution; here they are schemas over arbitrary formulas, which has the same effect (✱1·11)."),
    "PM.Statements": ("PM ✱2–✱5: the statement formulas",
                      "The asserted formulas of *Principia Mathematica* ✱2–✱5 (Vol. I, 1910, Part I, Section A), one "
                      "definition per numbered proposition: `s2_01 p` is the formula of ✱2·01, "
                      "$(p \\supset {\\sim}p) \\supset {\\sim}p$, as a function of its propositional variables. "
                      "The formulas use the connectives of the bundle `PM_core_star1_system` (✱1·01, ✱3·01, ✱4·01 as "
                      "definitions).\n\n"
                      "{checks}\n\n"
                      "These are the statements of the cards: the card for ✱x·y asserts that `sx_y` is a theorem of "
                      "✱1 for all formulas substituted for its variables.\n\n"
                      "**Formalization Note** Generated in the source repository (`scripts/gen_lean.py`) from the "
                      "Gutenberg #78050 transcription of Vol. I. The formulas of ✱1·2–✱1·6 are not here: their cards "
                      "state the constructors of the theorems of ✱1 directly."),
    "PM.Derived": ("PM ✱1: hypothetical derivations (contexts)",
                   "Contexts for derivations in PM's system ✱1. For a list of formulas $\\Gamma = [h_1,\\dots,h_n]$ "
                   "and a formula $\\varphi$,\n\n$$\n\\mathrm{ctx}(\\Gamma,\\varphi) = h_1 \\supset (h_2 \\supset "
                   "(\\cdots \\supset (h_n \\supset \\varphi)))\n$$\n\nand $\\Gamma \\vdash \\varphi$ (`Pf Γ φ`) is "
                   "*defined* as: $\\mathrm{ctx}(\\Gamma,\\varphi)$ is a theorem of ✱1. So a derivation under "
                   "hypotheses is an ordinary ✱1 theorem. Also: the $n$-th hypothesis of a context.\n\n"
                   "This is proof infrastructure, not a part of PM's text: PM argues from hypotheses informally; "
                   "these definitions let such arguments be written as explicit ✱1 derivations.\n\n"
                   "**Formalization Note** The rules over contexts (modus ponens under hypotheses, ∧/≡ introduction "
                   "and elimination, case split on ✱2·11, …) are theorems; they are copied into the solutions that "
                   "use them. The repository's two tactic abbreviations are not in this bundle: the platform does "
                   "not accept macros, so the solutions write out each use."),
    "PM.Complete": ("PM ✱1: literals of a valuation (for completeness)",
                    "For a truth value $b$ and a formula $\\varphi$, $\\varphi^b$ is $\\varphi$ if $b$ is true and "
                    "${\\sim}\\varphi$ otherwise. For a valuation $v$ and a variable $x$, the *literal* $x^v$ is "
                    "$x^{v(x)}$; for a list of variables $[x_1,\\dots,x_n]$ the literals are the list "
                    "$[x_n^v,\\dots,x_1^v]$.\n\n"
                    "These are the hypotheses of Kalmár's lemma in the completeness proof of PM's ✱1 for truth "
                    "tables (the card `PM.meta_complete`)."),
}


def statement_checks(d, repo, out):
    """Where the source checks that each formula of the bundle is a tautology: the `example … := by decide`
    after each `def` in PM/Statements.lean. The bundle keeps the definitions only, so the checks are not in it."""
    defs = re.findall(r"^def (s\w+) ", open(os.path.join(out, d["file"]), encoding="utf-8").read(), re.M)
    src = open(os.path.join(repo, "PM", "Statements.lean"), encoding="utf-8").read().splitlines()
    rows = [(i + 1, m.group(1)) for i, l in enumerate(src)
            if (m := re.fullmatch(r"example : \((s\w+)[ )].*\)\.isTaut = true := by decide", l)) and m.group(1) in defs]
    assert sorted(n for _, n in rows) == sorted(defs), "a definition of the bundle without its check in the source"
    first, last = rows[0][0], rows[-1][0]
    return (f"In the source repository each of these definitions is followed by a check, run by Lean's kernel when "
            f"the file is compiled, that the formula is a truth-table tautology (`{src[first - 1]}`): {len(rows)} "
            f"checks, in [PM/Statements.lean, lines {first}–{last}]({d['source']}#L{first}-L{last}). The checks are "
            "not part of this bundle, which keeps the definitions only.")


def definition_meta(d, cfg, bundles, repo, out):
    title, nls = DEFS[d["module"]]
    assert bundles[d["definition_name"]]["module"] == d["module"]
    if "{checks}" in nls:
        nls = nls.replace("{checks}", statement_checks(d, repo, out))
    return {"definition_title": title,
            "natural_language_statement": draft(cfg) + "\n\n" + nls + f"\n\nSource: [{d['module']}]({d['source']}).",
            "source": f"Whitehead and Russell, Principia Mathematica, Vol. I (1910), ✱1–✱5; formalization: {d['source']}",
            "tags": []}


if __name__ == "__main__":
    main(sys.argv[1:])
