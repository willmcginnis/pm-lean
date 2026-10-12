# How far each formalization of PM got

A dated survey of the formalizations of *Principia Mathematica*, this one included. It was measured on
2026-10-11 (this project's row on 2026-10-12, at commit `27b4f85`); the **Measured** column gives the date and,
where it was recorded, the commit of each row. It moved here on 2026-10-12 from the README of the companion
[text audit](https://github.com/willmcginnis/principia-mathematica-text-audit), with its definitions,
qualifications, dates and footnotes unchanged except for links. The claims about other projects have not been
re-measured since. If your project's row is wrong or out of date, please open an issue.

**License.** As in the text audit, where it first appeared, this document is dedicated to the public domain under
[CC0 1.0](https://creativecommons.org/publicdomain/zero/1.0/); the legal code is in
[LICENSE-CC0](../LICENSE-CC0). The rest of this repository is under the MIT License (see
[the README](../README.md#license)).

Measured by us on 2026-10-11 from each project's own files. Only facts and numbers are given here; no code or
text from the projects is included.

**How to read it.** The unit is one of PM's own numbered propositions (✱N·M). Only *assertions* count: numbered
items that PM prints with the assertion sign ⊢ and that are neither a definition (Df), a primitive proposition
(Pp), nor a rule stated in words. Each cell reads **S / P / F**:

- **S**: the number of PM assertions in that range for which the project states a formal statement labelled
  with that PM number. Several declarations for one number count once.
- **P**: of those, the number with a complete proof. That means no `sorry`, `Admitted`, `postulate` or `axiom`
  stands in for the proof, and the proof does not depend on another unproved PM item. An assertion that a
  project takes as an axiom is not counted in P.
- **F**: of those proved, the number where the project itself records, *for that proposition*, that the proof
  follows PM's own proof. The record can be a ledger entry or a per-declaration tag. It need not say whether the
  proof also uses propositions PM does not cite, so F means the same for every project, ours included. **ns**
  means "not stated" per proposition. Project-wide claims, and PM's Dem. quoted beside a proof, do not count.

The denominator row gives how many assertions PM prints in each range (counted from the Gutenberg text with a
few corrections, [`data/vol1_items.json`](../data/README.md); for ✱20–✱97 our counts agree with the PM-MATS citation graph's to within about 2%, which is
agreement between two counts, not a measured error bound). Read every cell against it, and against the
**Emb.** and **Check** columns. In a *deep* embedding, P means the statement was derived from the project's
primitive rules. In a *shallow* one, P means the statement holds in the host logic (for example classical Coq
or Lean), which says nothing about PM's deductive system. **Check** says how P was established: `build` means
we compiled the project; `static` means P comes from reading and searching the source, with nothing compiled;
`D-recheck` means we re-ran the condensed-detachment proofs with our own checker. **Fits within PM**:

- **yes**: the embedding is deep; its formulas are built from PM's own primitive ideas (∼ and ∨, and (x) from
  ✱9 on); every rule used by a proof counted in P is one of PM's own primitive propositions for the method it
  follows (✱1·1–✱1·6 with ✱1·11; for ✱9–✱10 those of ✱9 or those of ✱10's alternative method; from ✱12 on also
  ✱12·1 and ✱12·11), and we have checked this against the source (for ✱12·1/✱12·11, the transcription); and no proof counted in P takes an extra
  assumption. An extra rule that no proof counted in P uses is allowed, and is noted in a footnote.
- **partly**: deep, and the rules are PM's ✱1 primitive propositions, but the formulas are built from other
  primitive signs.
- **not verified**: deep, but we have not checked that the rules are exactly PM's primitive propositions.
- **no**: shallow, or the rules are another axiom system.

| Project | Measured | Prim. | Emb. | Check | Fits within PM | ✱2–✱5 | ✱9 | ✱10 | ✱11–✱14 | ✱20–✱56 | ✱60–✱97 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| **PM assertions (denominator)** | 2026-10-11 | | | | | **188** | **28** | **48** | **123** | **1366** | **1477** |
| [ours](../README.md) (Lean 4) | 2026-10-12, `27b4f85` | PM ✱1·1–✱1·6; ✱10 alt. method; ✱12·1/✱12·11 | deep | build | yes for its PM propositions (✱1–✱5, ✱9–✱21); has an extra comprehension rule that no numbered PM proposition uses⁶ | 188/188/177¹ | 6/4/ns | 48/46/ns | 123/123/123⁷ | 99/99/99⁷ | – |
| [l-pommeret](https://github.com/l-pommeret/Principia-Mathematica) (Lean 4) | 2026-10-11, `3fb187a` | PM ✱1·1–✱1·6, ✱1·11; ramified system | deep (shallow from ✱70) | build⁴ | yes for ✱1–✱5; not verified for its ramified ranges; no for its shallow ones⁵ | 188/188/171 | 28/26/21 | 35/34/34 | 71/68/66 | 183/128/88 | 160/151/98 (6 deep) |
| [Neo-Principia](https://github.com/MudroadWhite/Neo-Principia) (Rocq) | 2026-10-11, commit not recorded | host logic (classical Coq); ✱9+ Pps admitted | shallow | static | no | 186/186/ns² | 28/28‡/ns | 48/47‡/ns | 123/66‡/ns | 51/1‡/ns | – |
| [PrincipiaMathematica_Agda](https://github.com/yangg1g/PrincipiaMathematica_Agda) (Agda) | 2026-10-11, commit not recorded | Sheffer stroke; PM ✱1·1–✱1·6 | deep | static | partly (its primitive connective is the Sheffer stroke) | 188/188/ns | 28/0/ns | – | – | – | – |
| [principia-rewrite](https://github.com/LogicalAtomist/principia-rewrite) (Coq, PL.v) | 2026-10-11, commit not recorded | host logic (classical Coq) | shallow | static | no | 188/188/ns | – | – | – | – | – |
| [luk-pmproofs](https://github.com/xamidi/luk-pmproofs) | 2026-10-11, commit not recorded | Łukasiewicz's 3 axioms + condensed detachment | CD text | D-recheck | no | 188/188/ns | – | – | – | – | – |
| [Metamath pmproofs.txt](https://us.metamath.org/mmsolitaire/pmproofs.txt) | 2026-10-11, version not recorded | ax-1–ax-3 + condensed detachment | CD text | D-recheck | no | 188/188/ns | – | – | – | – | – |
| [Metamath set.mm](https://github.com/metamath/set.mm) (pm\* theorems) | not measured | ax-1–ax-3 + ax-mp | – | – | no | not measured³ | | | | | |
| [ndrwnaguib/principia](https://github.com/ndrwnaguib/principia) (Lean 4) | 2026-10-11, commit not recorded | host logic (Lean + Mathlib) | shallow | static | no | 47/47/ns | – | – | – | – | – |
| [Lacrimae-Angeli](https://github.com/MudroadWhite/Lacrimae-Angeli) (Rocq) | 2026-10-11, commit not recorded | none yet | sketch | static | – | – | – | – | – | – | – |
| [PM-MATS](https://github.com/LogicalAtomist/PM-MATS) | 2026-10-11 | not a formalization (a citation graph) | – | – | – | – | – | – | – | – | – |

"–" means nothing in that range. CD text: a text file of condensed-detachment proofs.

‡ The proof is complete relative to the project's admitted primitive propositions, but by our reading of the
source (not compiled) those admitted primitives are jointly inconsistent: its admitted stand-in for ✱9·13 yields
`∀ x : Prop, x`, so that stand-in alone is inconsistent. Treat these as unproved.

¹ ✱2–✱5 F = 177 proofs that our ledgers record as following PM's proof: 112 use only the propositions PM cites,
and 65 also need at least one proposition PM does not cite (listed per proof in our ledgers). The other 11 have no
PM proof to follow (the transcription has no Dem. or hint for them). 112 + 65 + 11 = 188.

² The two missing assertions, ✱4·8 and ✱4·81, are probably present under names that lack the chapter number;
they are not counted.

³ set.mm was not measured.

⁴ Built by us on 2026-10-11 (Lean v4.30.0, upstream commit `3fb187a`, 319 jobs, no errors). P was mapped
statically from names and proof status; the build confirms they compile. F comes from the project's own
per-declaration tags, which we did not verify. The project also states 404 assertions from Vols II–III, 375
of them with proofs, all in its shallow part (no denominator here).

⁵ For ✱1–✱5 its rules are ✱1·1, ✱1·11 and ✱1·2–✱1·6. Its ramified system has 20 rules, each labelled with a PM
number, among them ✱12·1 and ✱12·11 (the axiom of reducibility); we have not checked them against PM's own list
of primitive propositions. 59 PM numbers have deep proofs that take an extra hypothesis that is never discharged,
such as an assumption about carrying reducibility across scopes; those are counted as not proved, unless the
same number has another, unconditional proof.

⁶ Our row was measured at commit `27b4f85` of this repository (2026-10-12), which we built. Every
PM proposition counted in P is derived from PM's primitive propositions: ✱1·1–✱1·6, those of ✱10's alternative
method, and ✱12·1 and ✱12·11. The system also has an opt-in comprehension rule (our reading of ✱9·15/✱10·122); no
PM proposition counted in P uses it. `RedCheck.lean`, which follows each proof down to the rules, finds 1 of
the 485 declarations it treats as PM propositions using it, the helper `q12_1_of_var` (not a numbered PM
proposition). Besides the rule's own statements, 9 other declarations that are not PM propositions
(metatheorems about the system, the trap and the styles of predicativity) also use it. Consistency is proved in a
finite model with no Lean axioms, stated at the model's variables (see [SEMANTICS.md](SEMANTICS.md)). The formula type
also contains terms that correspond to no finite PM formula; there is no adequacy theorem yet (see
[SEMANTICS.md](SEMANTICS.md)).

⁷ ✱11–✱14: all 51 ✱11 assertions, all 25 of ✱13 and all 47 of ✱14, ✱14·3 as a schema, not as printed. As printed
it takes propositions as apparent variables, and the formalization's types, following p. 172, have none. So the
Lean statement is one theorem per instance, with PM's antecedent (p, q real) as a premise to be proved, not assumed;
this repository proves it for every truth-function built by ✱1–✱11's processes (p. 193). Whether to add a type
of propositions is an open design question ([TYPES_DESIGN.md](TYPES_DESIGN.md) §5, Q8). ✱12 has no assertions: ✱12·1 and ✱12·11 are primitive propositions,
here primitive rules. F comes from the per-proposition ledgers, counted as for ✱11 before: every ledgered proof
follows PM's Dem. lines or hint. As in [FIDELITY.md](FIDELITY.md), `pm-lines` means it uses only the propositions PM cites (with
the steps PM leaves tacit), `pm-lines+extra` that it also needs at least one PM does not cite: ✱11 34/17, ✱13 12/13,
✱14 9/38⁸ (123 in all). ✱20–✱56: 53 of ✱20's 55 assertions and 46 of ✱21's 48, F = 99⁸: ✱20 18/33 and ✱21 12/32,
plus two numbered propositions in each that are proved as rules (✱20·62, ✱20·633, ✱21·62, ✱21·633, all `pm-lines`).
✱20·631, ✱20·632, ✱21·631 and ✱21·632 concern significance and are built into the syntax, so they are not counted.
✱20·4, ✱20·41, ✱21·4 and ✱21·41 use classes of classes (✱20·03, ✱20·08, ✱20·081, ✱21·03, ✱21·08–✱21·083), built
as printed. Not done: ✱14·3 as printed; ✱22 onward; a proof that comprehension
without ✱12·1 is weaker (so that the styles of predicativity differ without reducibility; its test F4); an adequacy
theorem; and functions of three or more arguments.

⁸ [FIDELITY.md](FIDELITY.md) gives three readings of the ✱11, ✱13, ✱14, ✱20 and ✱21 counts, which differ in whether the
structural steps PM leaves unstated (what FIDELITY.md calls "glue": joining the lines of a displayed chain, putting factors in order,
carrying a step under (∃x)) count as tacit or as extra: strict (all glue extra), as recorded (the ledgers'
`fidelity` field) and all glue tacit. The counts shown here are the ones as recorded, in which joining chain
lines is tacit (PM p. 123: "The use of ✱4·22 will often be tacit") and the other glue is extra. We do not choose
among the readings; all three are in the fidelity table of
[FIDELITY.md](FIDELITY.md) (section "The three counts").

**l-pommeret is the furthest deep formalization in the table:** a deep ramified system whose rules include
✱12·1 and ✱12·11, with deep proofs into ✱11–✱56. We built it ourselves. Like ours, it records per proposition
whether a proof follows PM's. What our ledgers add, and what we have not found in the other projects' files, is
a list, for each of the 188 ✱2–✱5 proofs and the 51 ✱11 proofs, of the propositions it needs that PM does not
cite (l-pommeret's status document reports how many of its proofs reach a proposition by a route PM does not
print). This repository's proofs can be checked by building it ([build steps](../README.md#build-and-check)). The row's fidelity counts come
from its ledgers (`data/*_ledger.json`), not from the build; which rules each theorem uses comes from the
rule table in [VERIFICATION.md](VERIFICATION.md), which `RedCheck.lean` cross-checks against the proofs.
