# Classes of classes and classes of relations

Decision (maintainer, 2026-10-12, [TYPES_DESIGN.md](TYPES_DESIGN.md) §5, Q6): option (A), the literal reading,
"explicit is better than implicit". ✱20·08 is built as printed, with no use of typical ambiguity in
place of the definition, no new axiom and no new rule. The same holds for relations (✱21·03,
✱21·08–✱21·083). Page numbers are those of the 1910 print, read from the Gutenberg #78050
transcription (its LaTeX source).

Code: `PM/Star20.lean` (definitions in `namespace QF`; lemmas and ✱20·4, ✱20·41 in the section
"Classes of classes"), `PM/Star21.lean` (the same for relations, ✱21·4, ✱21·41).

## What PM prints

- ✱20·03 `Cls = α̂{(∃φ) . α = ẑ(φ!z)}` Df (p. 199; the summary on p. 198 prints ẑ!(φ!z)).
- ✱20·08 `f{α̂(ψα)} . = : (∃φ) : ψα . ≡_α . φ!α : f(φ!α̂)` Df (p. 200).
- ✱20·081 `α ∈ ψ!α̂ . = . ψ!α` Df (p. 200).
- ✱20·4 `⊢ : α ∈ Cls . ≡ . (∃φ) . α = ẑ(φ!z)` [✱20·3 . (✱20·03)] and ✱20·41 `⊢ . ẑ(ψz) ∈ Cls`
  [✱20·4·151] (p. 204).
- ✱21·03 (Rel), ✱21·08 and ✱21·081 (relations of relations), ✱21·082 and ✱21·083 (classes of
  relations) (p. 213); ✱21·4 and ✱21·41 (p. 215).

The ✱20·3 of ✱20·4's hint is not ✱20·3 itself: Cls is a class of classes, so it is ✱20·3 for classes
of classes. PM proves "the analogues of our primitive propositions" for classes (✱20·6–✱20·71), after
which "the analogues of other propositions follow by merely repeating previous proofs. These analogues
will, therefore, be quoted by the numbers of the original propositions" (p. 206). The same holds for
✱21·4, whose ✱20·3 is the analogue for classes of relations.

## The two layers

A class of classes is two steps away from the individuals:

```
α ∈ κ                        κ = α̂(Ψα), a class of classes
  │  ✱20·08, ✱20·081
  ▼
φ!α                          φ a predicative function of classes: type pred1 (pred1 a)
  │  ✱20·01, with context φ!χ!ẑ
  ▼
φ!(χ!ẑ)                      χ a predicative function of individuals: type pred1 a
```

- **Class of classes → predicative function of classes.** ✱20·08 eliminates α̂(Ψα): there is a
  predicative φ with Ψα ≡_α φ!α, and the context is applied to φ!α̂. ≡_α ranges over classes: it is
  (α) . Ψα ≡ φ!α with α apparent, i.e. ✱20·07, `clsAll`, which binds a predicative function θ of
  individuals and puts ẑ(θ!z) for α.
- **Predicative function of classes → function of functions of individuals.** φ!α has a class as
  argument, and a class is an incomplete symbol, so φ!α is eliminated by ✱20·01 with context φ!χ!ẑ:
  (∃χ) : χ!x ≡ₓ ψx : φ!(χ!ẑ). In Lean, φ has type `Ty.pred1 (Ty.pred1 a)`, a predicative function of
  predicative functions of the type of z.

Relations follow the same pattern with ✱21·01 and `Ty.pred2 a b`: a class of relations binds φ of type
`pred1 (pred2 a b)`; a relation of relations φ of type `pred2 (pred2 a b) (pred2 c d)`, and φ!(R, S)
is eliminated by ✱21·01 twice, R (written first) with the larger scope, as in identity (p. 201).

## The definitions

All are `@[reducible]` macros, like ✱20·01 (docs/TYPES_DESIGN.md decision 9). A class of classes is
written by its defining expression `Ψ : (V a → QF V) → QF V`, as a class is written by its defining
function `ψ : V a → QF V`. α̂(Ψα) has no term of its own, so it stays an incomplete symbol.

| PM | Lean | Unfolds to |
|---|---|---|
| ✱20·03 Cls | `QF.Cls` | `fun α => ex φ, clsEq α (pf φ)` |
| φ!α | `QF.clsApp φ α` | `cls α fun χ => φ!χ` (✱20·01) |
| ✱20·08 f{α̂(Ψα)} | `QF.clsCls Ψ f` | `ex φ, (clsAll fun α => Ψα ≡ clsApp φ α) . f φ` |
| ✱20·081 α ∈ φ!α̂ | `QF.memCls α φ` | `clsApp φ α` |
| α ∈ α̂(Ψα) | `QF.clsClsMem α Ψ`, notation `α ∈ Ψ` | `clsCls Ψ fun φ => memCls α φ` |
| ✱21·03 Rel | `QF.Rel` | `fun R => ex φ, relEq R (pf2 φ)` |
| φ!R | `QF.relClsApp φ R` | `rel R fun χ => φ!χ` (✱21·01) |
| ✱21·082 f{R̂(ΨR)} | `QF.relCls Ψ f` | as `clsCls`, over relations |
| ✱21·083 R ∈ φ!R̂ | `QF.memRelCls R φ` | `relClsApp φ R` |
| R ∈ R̂(ΨR) | `QF.relClsMem R Ψ`, notation `R ∈ Ψ` | `relCls Ψ fun φ => memRelCls R φ` |
| φ!(R, S) | `QF.relRelApp φ R S` | `rel R fun χ => rel S fun θ => φ!(χ, θ)` |
| ✱21·08 f{R̂Ŝψ(R, S)} | `QF.relRel Ψ f` | `ex φ, (R, S) : Ψ(R, S) ≡ φ!(R, S) . f φ` |
| ✱21·081 P{φ!(R̂, Ŝ)}Q | `QF.relAppRel P φ Q` | `relRelApp φ P Q` |
| P{R̂Ŝψ(R, S)}Q | `QF.relRelHolds P Ψ Q` | `relRel Ψ fun φ => relAppRel P φ Q` |

The class or relation in φ!α, φ!R and φ!(R, S) has the smallest scope (p. 197), and in α ∈ κ the class
of classes is eliminated first, as in PM's ✱20·3.

## The folding

The aim is that a reader sees PM's formulas and PM's lines, and that each definition is unfolded once,
in one named place.

1. **Notation** (scoped to `PM`, like the chain notation of PM/Chain.lean): `x ∈ α` (`clsMem`), `α ∈ κ`
   (`clsClsMem`) and `R ∈ κ` (`relClsMem`). The three share the symbol and are told apart by the
   types of their arguments. Each unfolds to the formula it names, so a statement written with them is
   the same Lean statement. ✱20·4 reads

   ```lean
   theorem q20_4 [Reducibility S] (ψ : V a → QF V) :
       QThm S (iff (ψ ∈ Cls) (ex (τ := Ty.pred1 a) fun φ => clsEq ψ (pf φ)))
   ```

2. **One named step per layer**, each proved once by ✱4·2 and the definition, like ✱20·1:
   - `qclsCls1`: ✱20·08 for any context f (the analogue of ✱20·1), [✱4·2 . (✱20·08)];
   - `qmemCls`: ✱20·081, [✱4·2 . (✱20·081)];
   - `qclsClsMem`: α ∈ α̂(Ψα) ≡ (∃φ) : Ψβ ≡_β φ!β : φ!α, the two together, [✱4·2 . (✱20·08) . (✱20·081)];
   - `qclsApp`: ✱20·01 for φ!α, [✱20·1].

   For relations: `qrelCls1`, `qmemRelCls`, `qrelClsMem`, `qrelClsApp` (✱21·082, ✱21·083, ✱21·01) and
   `qrelRel1`, `qrelAppRel`, `qrelRelApp` (✱21·08, ✱21·081, ✱21·01 twice).

3. **Chains as `calc` blocks**, one line per PM line, with PM/Chain.lean's `Trans` instances. ✱20·3 for
   classes of classes (`qcls20_3`) is ✱20·3's Dem.:

   ```lean
   calc (ψ ∈ Ψ)
       ≡ ex (fun φ => QF.and (P φ) (clsApp φ ψ)) := qclsClsMem Ψ ψ            -- (✱20·08) . (✱20·081)
     _ ≡ ex (fun φ => QF.and (P φ) (Ψ ψ)) := …                                 -- [✱10·43]
     _ ≡ QF.and (ex P) (Ψ ψ) := qex_and_perm P (Ψ ψ)                           -- [✱10·35]
     _ ≡ Ψ ψ := qand_true_left (qclsRed Ψ hΨ)                                 -- [✱12·1]
   ```

   where `P φ` is Ψβ ≡_β φ!β. ✱20·4 is then one line: `qcls20_3 Cls clsExt_Cls ψ`.

## What a reader sees, and what Lean unfolds

A reader sees `ψ ∈ Cls`. Lean sees, after unfolding the reducible macros (a check in PM/Star20.lean
unfolds α ∈ α̂(Ψα) one layer per line, for any Ψ; PM/Star21.lean has the same for P{R̂Ŝψ(R, S)}Q):

```
(∃φ : pred1 (pred1 a)) :
    (θ : pred1 a) : [(∃ρ : pred1 a) . ẑ(θ!z) = ẑ(ρ!z)] ≡ φ!ẑ(θ!z)      -- Ψβ ≡_β φ!β, β = ẑ(θ!z)
  : (∃χ : pred1 a) : χ!x ≡ₓ ψx : φ!(χ!ẑ)                                -- φ!α, by ✱20·01
```

where each ẑ(…) and φ!ẑ(θ!z) is in turn ✱20·01 with its context, and the identity of classes is
✱13·01 at type `pred1 a` (`clsEq`, p. 201). Nothing in the proofs unfolds this by hand: the lemmas above
do it once, and the proofs of ✱20·4 and ✱21·4 cite them.

## Extensionality of the defining expression

✱20·4's α is real, "some expression of the form ẑ(ψz)" (p. 203), whose defining function need not be
predicative. ✱20·3's Dem. uses ✱10·43 at that α, and the class analogue of ✱10·1 at a non-predicative
class is ✱20·17's argument (p. 206, `qclsAllAt`). That argument needs the expression to be
extensional: ψ ≡ₓ χ . ⊃ . Ψ{ẑ(ψz)} ≡ Ψ{ẑ(χz)}. In PM this always holds: "every proposition about a
class expresses an extensional property of the determining function of the class" (p. 200), because
every occurrence of a class is eliminated by ✱20·01, and ✱20·11 proves it for each context. In Lean a
defining expression `Ψ` is any Lean function, which need not be built that way, so the property is a
premise, `ClsExt S Ψ` (✱20·11 for Ψ), proved for each expression used:

- `clsExt_cls f`: a generic f{α} (`cls α f`, p. 199), by ✱20·11;
- `clsExt_ex`: (∃v) . Ψ(v, α), from each Ψ(v, α), by ✱10·11·21 and ✱10·281;
- `clsExt_Cls`: Cls's (∃φ) . α = ẑ(φ!z), from the two above.

For relations: `RelExt`, `relExt_rel` (✱21·11), `relExt_ex`, `relExt_Rel`.

**PM's claim, checked for the expressions PM forms.** Beside the premise, `ClsExpr Ψ` (PM/Star20.lean) says
that Ψα is built the way PM's notation builds a proposition about a class: from formulas not containing α
by ∼, ∨ and (x) (x of any type, so apparent classes and relations too), and by ✱20·01 at α itself, f{α},
whose context f may contain α again. `clsExpr_ext` proves `ClsExt S Ψ` for every `ClsExpr Ψ`, by
induction, with ✱20·11 at each elimination of α (as `qtfnCongr` does for the truth-functions of ✱14·3).
So the premise of `qcls20_3` is discharged once for all such Ψ: `qclsExpr20_3` is ✱20·3 for classes of
classes and `qclsExprRed` ✱20·7, both with no premise, and ✱20·4 follows from `ClsExpr.Cls` alone.
`q20_4` and `q21_4` themselves stay on the premise version (`qcls20_3` with `clsExt_Cls`, `qrelCls20_3`
with `relExt_Rel`), which is the shorter dependency; the premise-free route proves the same statements,
as two checks in PM/Star20.lean and PM/Star21.lean show (`qclsExpr20_3 ClsExpr.Cls ψ` and
`qrelExpr20_3 RelExpr.Rel ψ`, each with ✱20·4's or ✱21·4's statement).

- *Included.* Every defined notation of ✱10–✱21 is a reducible definition that unfolds into ∼, ∨, (x) and
  ✱20·01, so an expression written with them is a `ClsExpr` when α occurs only as a class. Lemmas in
  `ClsExpr` give the cases by name: ⊃, ., ≡, (∃x), ≡ₓ; x ∈ α, φ!α, α ∈ κ and Cls's (∃φ) . α = ẑ(φ!z);
  a class ẑ(ψz) (`clsOf`), a description (ιx)(φx) (`desc`) or a class of classes (`clsCls`) whose
  defining function contains α; (β) . fβ and (∃β) . fβ. Identities α = β, β = α and α = α are ✱20·01 at
  each class (the constructor `cls` at α, `clsOf` at β). A check states an expression with α in several places
  (under an apparent class, inside another class's defining function, in α ∈ κ) and gets its ✱20·3.
- *Not included.* A Lean function that uses the defining function otherwise: one that inspects the formula
  ψx (`match`), compares ψ with a given function, or uses ψx outside an elimination by ✱20·01. PM's
  notation cannot form these (a class "has no meaning in isolation", and ψx is a proposition about ψ,
  not about the class). For an arbitrary Lean function `qcls20_3` keeps its premise.
- *The bare ψx.* `fun α => α x`, the defining function applied directly, is not a constructor of
  `ClsExpr`, because PM's notation cannot form it as a proposition about the class. A class enters a
  proposition either as a variable α, which ✱20·07 and ✱20·071 make range over classes, and which PM
  writes only in x ∈ α, α = β, φ!α and the like, all eliminated by ✱20·01 (there is no notation "αx");
  or as a class ẑ(ψz), an incomplete symbol whose only meaning is the one ✱20·01 gives it in a context
  f{ẑ(ψz)}. In the second case ψx can be written beside it, but it is then an occurrence of ψ, not of
  ẑ(ψz): replacing the class by a coextensive one does not touch it. Leaving it out hides no
  counterexample: `clsExt_app` proves it extensional anyway, by ✱10·1 (`relExt_app`, by ✱11·1, for
  ψ(x, y) and relations).
- *No counterexample.* The induction goes through for every constructor, so no expression PM forms fails
  the claim.

For relations: `RelExpr`, `relExpr_ext` (✱21·11), `qrelExpr20_3`, `qrelExprRed`, `RelExpr.Rel`
(PM/Star21.lean; p. 213, after ✱21·11: "every proposition about a relation expresses an extensional
property of the determining function").

The analogue of ✱12·1 is ✱20·7, (∃g) : fα ≡_α g!α, stated for a generic fα. For an extensional Ψ,
`qclsGen` writes Ψ{ẑ(θ!z)} as f{ẑ(θ!z)} for the context f(χ!ẑ) = Ψ{ẑ(χ!z)} (p. 199: fα "is, in
reality, a function of φẑ, namely the extensional function associated with f(ψ!ẑ) by means of
✱20·01"), and `qclsRed` is ✱20·7 for Ψ. The ledgers list these steps as `extra_used` of ✱20·4 and
✱21·4. They also list the steps of ✱20·3's Dem. as the analogue repeats them: ✱10·35 and ✱20·7 (✱21·7)
as extra, the chain under Hp (✱2·02, ✱3·43) as chain glue, and ✱10·27, ✱10·28 (and ✱10·271 for
relations), which the analogue takes inside `qcls20_3`, as under-exists glue
([FIDELITY.md](FIDELITY.md)).

## Reuse

Later numbers write their classes of classes as defining expressions and use `α ∈ κ`, `qcls20_3`
(their "✱20·3") and an extensionality proof from `clsExt_cls` and `clsExt_ex`, or `qclsExpr20_3` with a
`ClsExpr` proof:

- ✱40·01, ✱40·02: p'κ = x̂(α ∈ κ . ⊃_α . x ∈ α) and s'κ = x̂{(∃α) . α ∈ κ . x ∈ α} are classes of
  individuals whose defining functions contain `α ∈ κ`, κ real; ✱40·1 and ✱40·11 are ✱20·3 itself.
- ✱52·01: 1 = α̂{(∃x) . α = ι'x}. PM/Star20.lean has a check that states it, with ι'x written ŷ(y = x)
  (✱51·11; ✱30's descriptive functions are not built), and gets ✱52·1 `α ∈ 1 . ≡ . (∃x) . α = ι'x`
  [✱20·3 . (✱52·01)] from `qcls20_3`.
- ✱54·02: 2 = α̂{(∃x, y) . x ≠ y . α = ι'x ∪ ι'y}, the same way once ✱22's ∪ is built.
- ✱60·01: Cl = κ̂α̂{κ = β̂(β ⊂ α)}, a relation of a class of classes to a class. β̂(β ⊂ α) is a defining
  expression as above; κ = β̂(β ⊂ α) needs identity of classes of classes (below), and κ̂ a relation
  whose referent is a class of classes.

Not built yet, and needed by those numbers:

- **Apparent classes of classes**, (κ) . fκ and (∃κ) . fκ: ✱20·07, ✱20·071 read one type up,
  (κ) . fκ . = . (φ) . f{α̂(φ!α)}, with `fun α => clsApp φ α` as the defining expression of α̂(φ!α).
- **Identity of classes of classes**, ✱13·01 at type `pred1 (pred1 a)` with ✱20·08 twice, and the
  analogues of ✱20·1–✱20·43 for classes of classes (✱20·15, ✱20·31, …), each by repeating the proof
  as p. 206 says.
- Classes of classes of classes would need ✱20·08 one type further up.

## Size

- PM/Star20.lean: 5 macros; `ClsExt` and 11 lemmas (its three instances, the four elimination steps,
  `qclsGen`, `qclsRed`, `qcls10_43`, `qcls20_3`); ✱20·4, ✱20·41; two checks. For PM's claim of p. 200: `ClsExpr` (5
  constructors), `clsExpr_ext`, 14 lemmas in `ClsExpr`, `qclsExprRed`, `qclsExpr20_3`, `clsExt_app`; two
  checks.
- PM/Star21.lean: 9 macros; `RelExt` and 14 lemmas (the same, and the three steps of ✱21·08, ✱21·081);
  ✱21·4, ✱21·41; one check. For p. 213: `RelExpr` (5 constructors), `relExpr_ext`, 7 lemmas in
  `RelExpr`, `qrelExprRed`, `qrelExpr20_3`, `relExt_app`; one check.
- ✱20·4 and ✱21·4 are one line each; ✱20·41 and ✱21·41 one line each. `qcls20_3` is a four-line `calc`.
