import PM.Star20
/-!
  ✱21: general theory of relations (1910 print, pp. 211–216; summary pp. 211–213, definitions p. 213,
  numbered propositions pp. 213–216). The print has 48 numbered propositions, ✱21·1 to ✱21·71. 46 are
  proved here. ✱21·631 and ✱21·632 concern significance and are built into the syntax, as ✱20·631,
  ✱20·632 (and ✱10·121, ✱10·122) are.

  "The proofs of the propositions of this number are usually omitted, since they are exactly analogous
  to those of ✱20, merely substituting ✱12·11 for ✱12·1, and propositions in ✱11 for propositions in
  ✱10" (p. 212). So the proofs here are those of PM/Star20.lean with that substitution, and use the
  propositions of PM's bracketed hint where it prints one; the comment on each Lean line gives the hint.
  `data/star21_ledger.json` records, per proposition, which cited propositions are used and which
  further ones were needed. Statements are read from the Gutenberg #78050 transcription of the 1910
  print (its formula source), not from the scan images.

  Relations are incomplete symbols, like classes (✱20): x̂ŷψ(x, y) has meaning only in a context, and
  the context is an explicit argument of the macro:
    ✱21·01  f{x̂ŷψ(x, y)} . = : (∃φ) : φ!(x, y) . ≡_{x,y} . ψ(x, y) : f{φ!(û, v̂)}   Df   (`QF.rel ψ f`)
    ✱21·02  a{φ!(x̂, ŷ)}b . = . φ!(a, b)                                       Df   (`QF.relApp a φ b`)
    ✱21·07  (R) . fR . = . (φ) . f{x̂ŷφ!(x, y)}                               Df   (`QF.relAll`)
    ✱21·071 (∃R) . fR . = . (∃φ) . f{x̂ŷφ!(x, y)}                             Df   (`QF.relEx`)
    ✱21·072 [(ιR)(φR)] . f(ιR)(φR) . = : (∃S) : φR . ≡_R . R = S : fS        Df   (`QF.descRel`)
    ✱21·03  Rel = R̂{(∃φ) . R = x̂ŷφ!(x, y)}                                   Df   (`QF.Rel`)
    ✱21·08  f{R̂Ŝψ(R, S)} . = : (∃φ) : ψ(R, S) . ≡_{R,S} . φ!(R, S) : f{φ!(R̂, Ŝ)}   Df   (`QF.relRel Ψ f`)
    ✱21·081 P{φ!(R̂, Ŝ)}Q . = . φ!(P, Q)                                      Df   (`QF.relAppRel P φ Q`)
    ✱21·082 f{R̂(ψR)} . = : (∃φ) : ψR . ≡_R . φ!R : f(φ!R̂)                   Df   (`QF.relCls Ψ f`)
    ✱21·083 R ∈ φ!R̂ . = . φ!R                                                Df   (`QF.memRelCls R φ`)
  The order convention of pp. 211–212 (the argument mentioned first goes to the letter first in the
  alphabet) is the order of the Lean arguments: `ψ x y`, `φ!(x, y)` is `.app2 φ x y`. Identity of
  relations is ✱13·01 at the type of predicative functions of two arguments, the relation written first
  having the larger scope (`QF.relEq`). Capital letters follow the conventions for Greek letters in ✱20
  (p. 212): a real R is any formula with two holes, an apparent one is φ!(x̂, ŷ) with φ bound; an
  expression fR is a Lean function `F` of the defining function, each occurrence eliminated where it
  stands, and a generic f{x̂ŷψ(x, y)} is `rel ψ f`.

  As in ✱20, where a proof instantiates an apparent relation at a relation x̂ŷφ(x, y) whose defining
  function need not be predicative (✱21·53, ✱21·54 and the steps of ✱21·55–✱21·58), the step is the
  analogue for relations of ✱20·17's argument: ✱12·11 and ✱21·11 (`qrelAllAt`, `qrelExAt`).

  Relations of relations (✱21·08, ✱21·081) and classes of relations (✱21·082, ✱21·083) are built as
  printed, as classes of classes are in ✱20 (docs/CLASSES_OF_CLASSES.md): φ is a predicative function
  whose arguments are relations, ≡_R ranges over relations (✱21·07), and φ!R, φ!(R, S) are eliminated
  by ✱21·01 with context φ!χ!(x̂, ŷ) (`QF.relClsApp`, `QF.relRelApp`; of two relations the one written
  first has the larger scope). `R ∈ κ` (scoped to `PM`) is `relClsMem R κ`. ✱21·4 and ✱21·41 are proved
  after ✱21·7, whose analogue of ✱12·1 their ✱20·3 (the analogue for classes of relations) needs.

  Not formalized:
  - ✱21·631, ✱21·632 (significance, built into the syntax). ✱21·62 and ✱21·633 are proved as rules.
  - The converse-order form f{ŷx̂ψ(x, y)} of ✱21·01 (p. 213), which is not numbered and not used.
  - E!(ιR)(φR), which ✱21·56 uses, is the analogue of ✱14·02 (`QF.exists1Rel`), not printed in ✱21.

  Steps done silently are those of PM/Star11.lean's header and of PM/Star14.lean's (chaining ⊃ and ≡
  lines under a hypothesis; the ledger lists the propositions that join them as `glue`). PM prints no
  Dem. in ✱21, only bracketed hints, so there is no displayed chain to write as a `calc` block. A ✱10 proposition carried under (x) and (y) by its ✱10·11·27·271 pattern
  (PM pp. 161–162: "the analogous proposition in ✱10 is used twice") is counted as that proposition.

  Names: `q21_1` is ✱21·1, and so on. ψ, χ, φ are formulas with two holes (defining functions of
  relations); f, g are contexts of a predicative function of two arguments; F, G, Φ are expressions
  containing a relation; Ψ is the defining expression of a class of relations or a relation of relations.
-/
namespace PM
open QF

namespace QF
variable {V : Ty → Type} {S : Sys V}
/-- ✱21·01 `f{x̂ŷψ(x, y)} . = : (∃φ) : φ!(x, y) . ≡_{x,y} . ψ(x, y) : f{φ!(û, v̂)}` Df. `f` is the context. -/
@[reducible] def rel {a b : Ty} (ψ : V a → V b → QF V) (f : V (Ty.pred2 a b) → QF V) : QF V :=
  ex (τ := Ty.pred2 a b) fun φ => QF.and (fiff2 (fun x y => .app2 φ x y) ψ) (f φ)
/-- ✱21·02 `a{φ!(x̂, ŷ)}b . = . φ!(a, b)` Df -/
@[reducible] def relApp {a b : Ty} (x : V a) (φ : V (Ty.pred2 a b)) (y : V b) : QF V := .app2 φ x y
/-- φ!(x̂, ŷ) as a formula with two holes: the defining function of the relation x̂ŷφ!(x, y). -/
@[reducible] def pf2 {a b : Ty} (φ : V (Ty.pred2 a b)) : V a → V b → QF V := fun x y => .app2 φ x y
/-- `x̂ŷψ(x, y) = x̂ŷχ(x, y)`: ✱13·01 between predicative functions of two arguments, with ✱21·01 applied
    to the first relation first. -/
@[reducible] def relEq {a b : Ty} (ψ χ : V a → V b → QF V) : QF V :=
  rel ψ fun φ => rel χ fun θ => ident φ θ
/-- `x{x̂ŷψ(x, y)}y`, i.e. xRy: ✱21·02 with ✱21·01 applied to the relation, with the smallest scope. -/
@[reducible] def relHolds {a b : Ty} (x : V a) (ψ : V a → V b → QF V) (y : V b) : QF V :=
  rel ψ fun φ => relApp x φ y
/-- ✱21·07 `(R) . fR . = . (φ) . f{x̂ŷφ!(x, y)}` Df -/
@[reducible] def relAll {a b : Ty} (F : (V a → V b → QF V) → QF V) : QF V :=
  .all (τ := Ty.pred2 a b) fun φ => F (pf2 φ)
/-- ✱21·071 `(∃R) . fR . = . (∃φ) . f{x̂ŷφ!(x, y)}` Df -/
@[reducible] def relEx {a b : Ty} (F : (V a → V b → QF V) → QF V) : QF V :=
  ex (τ := Ty.pred2 a b) fun φ => F (pf2 φ)
/-- ✱21·072 `[(ιR)(φR)] . f(ιR)(φR) . = : (∃S) : φR . ≡_R . R = S : fS` Df -/
@[reducible] def descRel {a b : Ty} (Φ G : (V a → V b → QF V) → QF V) : QF V :=
  relEx fun T => QF.and (relAll fun R => iff (Φ R) (relEq R T)) (G T)
/-- `E!(ιR)(φR) . = : (∃S) : φR . ≡_R . R = S`, the analogue of ✱14·02 that ✱21·56 uses. -/
@[reducible] def exists1Rel {a b : Ty} (Φ : (V a → V b → QF V) → QF V) : QF V :=
  relEx fun T => relAll fun R => iff (Φ R) (relEq R T)
/-- ✱21·03 `Rel = R̂{(∃φ) . R = x̂ŷφ!(x, y)}` Df: the defining expression of the class of relations, with R the
    smallest scope ("similar remarks apply to it as to the definition of 'Cls'", p. 212). -/
@[reducible] def Rel {a b : Ty} : (V a → V b → QF V) → QF V :=
  fun R => ex (τ := Ty.pred2 a b) fun φ => relEq R (pf2 φ)
/-- φ!R, a predicative function φ of relations applied to the relation R = x̂ŷψ(x, y): ✱21·01 with context
    φ!χ!(x̂, ŷ), the relation having the smallest scope. -/
@[reducible] def relClsApp {a b : Ty} (φ : V (Ty.pred1 (Ty.pred2 a b))) (R : V a → V b → QF V) : QF V :=
  rel R fun χ => .app1 φ χ
/-- ✱21·082 `f{R̂(ψR)} . = : (∃φ) : ψR . ≡_R . φ!R : f(φ!R̂)` Df: classes of relations. -/
@[reducible] def relCls {a b : Ty} (Ψ : (V a → V b → QF V) → QF V) (f : V (Ty.pred1 (Ty.pred2 a b)) → QF V) :
    QF V :=
  ex (τ := Ty.pred1 (Ty.pred2 a b)) fun φ => QF.and (relAll fun R => iff (Ψ R) (relClsApp φ R)) (f φ)
/-- ✱21·083 `R ∈ φ!R̂ . = . φ!R` Df -/
@[reducible] def memRelCls {a b : Ty} (R : V a → V b → QF V) (φ : V (Ty.pred1 (Ty.pred2 a b))) : QF V :=
  relClsApp φ R
/-- `R ∈ R̂(ΨR)`: ✱21·083 with ✱21·082 applied to the class of relations, with the smallest scope. -/
@[reducible] def relClsMem {a b : Ty} (R : V a → V b → QF V) (Ψ : (V a → V b → QF V) → QF V) : QF V :=
  relCls Ψ fun φ => memRelCls R φ
/-- φ!(R, S), a predicative function φ of two relations applied to R = x̂ŷψ(x, y) and S = x̂ŷχ(x, y): ✱21·01
    for R and then for S (R, written first, has the larger scope), with context φ!(χ!(x̂, ŷ), θ!(x̂, ŷ)). -/
@[reducible] def relRelApp {a b c d : Ty} (φ : V (Ty.pred2 (Ty.pred2 a b) (Ty.pred2 c d)))
    (R : V a → V b → QF V) (T : V c → V d → QF V) : QF V :=
  rel R fun χ => rel T fun θ => .app2 φ χ θ
/-- ✱21·08 `f{R̂Ŝψ(R, S)} . = : (∃φ) : ψ(R, S) . ≡_{R,S} . φ!(R, S) : f{φ!(R̂, Ŝ)}` Df: relations of relations.
    ≡_{R,S} is (R, S) : ψ(R, S) . ≡ . φ!(R, S), the relations apparent (✱21·07). -/
@[reducible] def relRel {a b c d : Ty} (Ψ : (V a → V b → QF V) → (V c → V d → QF V) → QF V)
    (f : V (Ty.pred2 (Ty.pred2 a b) (Ty.pred2 c d)) → QF V) : QF V :=
  ex (τ := Ty.pred2 (Ty.pred2 a b) (Ty.pred2 c d)) fun φ =>
    QF.and (relAll fun R => relAll fun T => iff (Ψ R T) (relRelApp φ R T)) (f φ)
/-- ✱21·081 `P{φ!(R̂, Ŝ)}Q . = . φ!(P, Q)` Df -/
@[reducible] def relAppRel {a b c d : Ty} (P : V a → V b → QF V) (φ : V (Ty.pred2 (Ty.pred2 a b) (Ty.pred2 c d)))
    (Q : V c → V d → QF V) : QF V :=
  relRelApp φ P Q
/-- `P{R̂Ŝψ(R, S)}Q`: ✱21·081 with ✱21·08 applied to the relation of relations, with the smallest scope. -/
@[reducible] def relRelHolds {a b c d : Ty} (P : V a → V b → QF V) (Ψ : (V a → V b → QF V) → (V c → V d → QF V) → QF V)
    (Q : V c → V d → QF V) : QF V :=
  relRel Ψ fun φ => relAppRel P φ Q
end QF

/-- `R ∈ κ`, κ a class of relations: `relClsMem R κ` (scoped to `PM`, like `x ∈ α` and `α ∈ κ` of ✱20). -/
scoped infix:50 " ∈ " => QF.relClsMem

variable {V : Ty → Type} {S : Sys V} {a b : Ty}

/-! ## ✱10 propositions for two variables, each listed in the ledger where used -/

/-- ✱10·32 for two variables: `φ(x, y) . ≡_{x,y} . ψ(x, y) : ≡ : ψ(x, y) . ≡_{x,y} . φ(x, y)` (✱10·32 under
    (x), ✱10·11·271). -/
theorem qfiff2Symm {σ τ : Ty} (φ ψ : V σ → V τ → QF V) : QThm S (iff (fiff2 φ ψ) (fiff2 ψ φ)) :=
  q10_11_271 fun x => q10_32 (φ x) (ψ x)
/-- ✱10·321 for two variables, by ✱10·321's proof with ✱11·371 for ✱10·301 (Fact, ✱3·45). -/
theorem qfiff2_321 {σ τ : Ty} (φ ψ χ : V σ → V τ → QF V) :
    QThm S (imp (QF.and (fiff2 φ ψ) (fiff2 φ χ)) (fiff2 ψ χ)) :=
  qsyl (QThm.mp (qiffMp (qfiff2Symm φ ψ)) (QL.t3_45 _ _ _)) (q11_371 ψ φ χ)
/-- ✱4·86 for the second member under (x, y): `ψ ≡_{x,y} χ . ⊃ : ω ≡_{x,y} ψ . ≡ . ω ≡_{x,y} χ`
    (`qiffCongrRImp` under (y) and (x) by ✱10·11·27, ✱10·271). -/
theorem qfiff2CongrR {σ τ : Ty} (ω ψ χ : V σ → V τ → QF V) :
    QThm S (imp (fiff2 ψ χ) (iff (fiff2 ω ψ) (fiff2 ω χ))) :=
  qsyl (q10_11_27 fun x => qsyl (q10_11_27 fun y => qiffCongrRImp (ω x y) (ψ x y) (χ x y))
      (q10_271 (fun y => iff (ω x y) (ψ x y)) fun y => iff (ω x y) (χ x y)))
    (q10_271 _ _)
/-- ✱10·43 for two variables: its proof with ✱11·1 for ✱10·1, and ✱5·32. -/
theorem qfiff2_43 {σ τ : Ty} (φ ψ : V σ → V τ → QF V) (x : V σ) (y : V τ) :
    QThm S (iff (QF.and (fiff2 φ ψ) (φ x y)) (QF.and (fiff2 φ ψ) (ψ x y))) :=
  QThm.mp (q11_1 (fun z w => iff (φ z w) (ψ z w)) x y) (qiffMp (QL.t5_32 (fiff2 φ ψ) (φ x y) (ψ x y)))

/-! ## ✱21·1–✱21·112 -/

/-- ✱21·1 `⊢ :. f{x̂ŷψ(x, y)} . ≡ : (∃φ) : φ!(x, y) . ≡_{x,y} . ψ(x, y) : f{φ!(û, v̂)}` [✱4·2 . (✱21·01)] -/
theorem q21_1 (ψ : V a → V b → QF V) (f : V (Ty.pred2 a b) → QF V) :
    QThm S (iff (rel ψ f) (ex (τ := Ty.pred2 a b) fun φ => QF.and (fiff2 (pf2 φ) ψ) (f φ))) :=
  QL.t4_2 _

/-- ✱21·11 `⊢ :. ψ(x, y) . ≡_{x,y} . χ(x, y) : ⊃ : f{x̂ŷψ(x, y)} . ≡ . f{x̂ŷχ(x, y)}`
    [✱4·86·36 . ✱10·281 . ✱21·1]. ✱4·86 (for the second member) is carried under (x, y) (`qfiff2CongrR`). -/
theorem q21_11 (ψ χ : V a → V b → QF V) (f : V (Ty.pred2 a b) → QF V) :
    QThm S (imp (fiff2 ψ χ) (iff (rel ψ f) (rel χ f))) :=
  have h : ∀ φ : V (Ty.pred2 a b), QThm S (imp (fiff2 ψ χ)
      (iff (QF.and (fiff2 (pf2 φ) ψ) (f φ)) (QF.and (fiff2 (pf2 φ) χ) (f φ)))) := fun φ =>
    qsyl (qfiff2CongrR (pf2 φ) ψ χ) (QL.t4_36 _ _ (f φ))                          -- ✱4·86·36
  qsyl (q10_11_21 h) (q10_281 _ _)                                                -- ✱10·281 . ✱21·1

/-- ✱21·111 `⊢ :. f{φ!(x̂, ŷ)} . ≡_φ . g{φ!(x̂, ŷ)} : ⊃ : f{x̂ŷφ!(x, y)} . ≡_φ . g{x̂ŷφ!(x, y)}`
    [Fact . ✱11·11·3 . ✱10·281 . ✱21·1]. As in ✱20·111, f(ψ!(x̂, ŷ)) ≡ g(ψ!(x̂, ŷ)) is ✱10·1 at ψ, and
    "Fact" for the ≡ of products is ✱4·36 on the second factor (with ✱4·3). ✱11·11·3 generalizes over
    (φ, ψ), and ✱10·281 is carried under (φ). -/
theorem q21_111 (f g : V (Ty.pred2 a b) → QF V) :
    QThm S (imp (fiff f g) (fiff (fun φ => rel (pf2 φ) f) (fun φ => rel (pf2 φ) g))) :=
  let A : V (Ty.pred2 a b) → V (Ty.pred2 a b) → QF V := fun φ ψ => QF.and (fiff2 (pf2 ψ) (pf2 φ)) (f ψ)
  let B : V (Ty.pred2 a b) → V (Ty.pred2 a b) → QF V := fun φ ψ => QF.and (fiff2 (pf2 ψ) (pf2 φ)) (g ψ)
  have h : ∀ φ ψ, QThm S (imp (fiff f g) (iff (A φ ψ) (B φ ψ))) := fun φ ψ =>
    qsyl (q10_1 (fun ψ => iff (f ψ) (g ψ)) ψ) (qandCongrRImp (f ψ) (g ψ) (fiff2 (pf2 ψ) (pf2 φ)))  -- Fact
  qsyl (qiffMpr (q11_3 _ _) |> QThm.mp (q11_11 h))                                -- ✱11·11·3
    (q10_11_27 fun φ => q10_281 (A φ) (B φ))                                      -- ✱10·281 . ✱21·1

/-- ✱21·112 `⊢ :. (∃g) :. f{x̂ŷφ!(x, y)} . ≡_φ . g!{x̂ŷφ!(x, y)}` [✱12·1 . ✱21·111]: "It is ✱12·1, not ✱12·11,
    which is required in this proposition, because we are concerned with a function (f) of one variable,
    namely φ". -/
theorem q21_112 [Reducibility S] (f : V (Ty.pred2 a b) → QF V) :
    QThm S (ex (τ := Ty.pred1 (Ty.pred2 a b)) fun g =>
      fiff (fun φ => rel (pf2 φ) f) (fun φ => rel (pf2 φ) fun χ => .app1 g χ)) :=
  QThm.mp (q12_1 f) (q10_11_28 fun g => q21_111 f fun χ => .app1 g χ)            -- ✱12·1 . ✱21·111

/-! ## ✱21·12–✱21·191 -/

/-- ✱12·11 with the orientation of ✱21·01: `(∃φ) : φ!(x, y) . ≡_{x,y} . ψ(x, y)` (✱10·32 under (x),
    `qfiff2Symm`, under (∃φ)). -/
theorem qred2rel [Reducibility S] (ψ : V a → V b → QF V) :
    QThm S (ex (τ := Ty.pred2 a b) fun φ => fiff2 (pf2 φ) ψ) :=
  QThm.mp (q12_11 ψ) (q10_11_28 fun φ => qiffMp (qfiff2Symm ψ (pf2 φ)))

/-- ✱21·12 `⊢ :. (∃φ) :. φ!(x, y) . ≡_{x,y} . ψ(x, y) : f{x̂ŷψ(x, y)} . ≡ . f{x̂ŷφ!(x, y)}` [✱21·11 . ✱12·11]:
    "the first use of the primitive proposition ✱12·11, except in ✱20·701·702·703". As in ✱20·12, the
    first factor is ✱12·11 turned (✱10·32 under (x)), joined with ✱21·11 by Comp (✱3·43). -/
theorem q21_12 [Reducibility S] (ψ : V a → V b → QF V) (f : V (Ty.pred2 a b) → QF V) :
    QThm S (ex (τ := Ty.pred2 a b) fun φ => QF.and (fiff2 (pf2 φ) ψ) (iff (rel ψ f) (rel (pf2 φ) f))) :=
  QThm.mp (q12_11 ψ) (q10_11_28 fun φ =>
    qcomp (qiffMp (qfiff2Symm ψ (pf2 φ))) (q21_11 ψ (pf2 φ) f))                   -- ✱21·11 . ✱12·11

/-- ✱21·13 `⊢ :. ψ(x, y) . ≡_{x,y} . χ(x, y) : ⊃ . x̂ŷψ(x, y) = x̂ŷχ(x, y)` [✱21·1 . ✱12·11 . ✱13·195]. The
    proof of ✱20·13 with ✱12·11: ψ ≡ φ! is turned (✱10·32 under (x)); with Hp, ✱10·321 for two
    variables (`qfiff2_321`, ✱11·371) gives φ! ≡ χ; the ✱13·195 step is its proof's first line, ✱3·2 .
    ✱13·15 . ✱10·24, with θ = φ written φ = θ (Comm); Comp and Exp (✱3·43, ✱3·3); ✱10·11·21·28. -/
theorem q21_13 [Reducibility S] (ψ χ : V a → V b → QF V) : QThm S (imp (fiff2 ψ χ) (relEq ψ χ)) :=
  let R : V (Ty.pred2 a b) → QF V := fun φ => QF.and (fiff2 (pf2 φ) ψ) (rel χ fun θ => ident φ θ)
  have step : ∀ φ : V (Ty.pred2 a b), QThm S (imp (fiff2 ψ χ) (imp (fiff2 ψ (pf2 φ)) (R φ))) := fun φ =>
    have k1 : QThm S (imp (QF.and (fiff2 ψ χ) (fiff2 ψ (pf2 φ))) (fiff2 (pf2 φ) ψ)) :=
      qsyl (QL.t3_27 _ _) (qiffMp (qfiff2Symm _ _))
    have k2 : QThm S (imp (QF.and (fiff2 ψ χ) (fiff2 ψ (pf2 φ))) (fiff2 (pf2 φ) χ)) :=
      qsyl (qfiff2_321 ψ χ (pf2 φ)) (qiffMp (qfiff2Symm _ _))
    have k3 : QThm S (imp (fiff2 (pf2 φ) χ) (rel χ fun θ => ident φ θ)) :=
      qsyl (QThm.mp (q13_15 φ) (QThm.mp (QL.t3_2 _ _) (QL.t2_04 _ _ _)))         -- ✱3·2 . ✱13·15
        (q10_24 (fun θ => QF.and (fiff2 (pf2 θ) χ) (ident φ θ)) φ)               -- ✱10·24 [✱13·195]
    QThm.mp (qcomp k1 (qsyl k2 k3)) (QL.t3_3 _ _ _)
  QThm.mp (q12_11 ψ) (QThm.mp (qsyl (q10_11_21 step) (q10_28 _ R)) (QL.t2_04 _ _ _))  -- ✱21·1 . ✱12·11

/-- ✱21·14 `⊢ :. x̂ŷψ(x, y) = x̂ŷχ(x, y) . ⊃ : ψ(x, y) . ≡_{x,y} . χ(x, y)` [Proof as in ✱20·14]: ✱13·195 with
    the factors commuted (✱4·3) and φ = θ turned by ✱13·16 (✱4·36), under (∃θ) by ✱10·11·281; then
    ✱10·322 for two variables, which with ✱21·01's orientation is ✱10·321's (`qfiff2_321`, ✱11·371), and
    ✱10·11·23. -/
theorem q21_14 [Reducibility S] (ψ χ : V a → V b → QF V) : QThm S (imp (relEq ψ χ) (fiff2 ψ χ)) :=
  let Q : V (Ty.pred2 a b) → QF V := fun θ => fiff2 (pf2 θ) χ
  have j : ∀ φ : V (Ty.pred2 a b), QThm S (iff (rel χ fun θ => ident φ θ) (Q φ)) := fun φ =>
    qiffTrans (q10_11_281 fun θ =>
        qiffTrans (QL.t4_3 (Q θ) (ident φ θ)) (QThm.mp (q13_16 φ θ) (QL.t4_36 _ _ _)))
      (q13_195 Q φ)                                                               -- [✱13·195]
  have k : ∀ φ : V (Ty.pred2 a b),
      QThm S (imp (QF.and (fiff2 (pf2 φ) ψ) (rel χ fun θ => ident φ θ)) (fiff2 ψ χ)) :=
    fun φ => qsyl (qandR (qiffMp (j φ))) (qfiff2_321 (pf2 φ) ψ χ)                 -- [✱10·322]
  QThm.mp (q10_11 k) (qiffMp (q10_23 _ _))                                        -- ✱10·11·23

/-- ✱21·15 `⊢ :. ψ(x, y) . ≡_{x,y} . χ(x, y) : ≡ . x̂ŷψ(x, y) = x̂ŷχ(x, y)` [✱21·13·14] -/
theorem q21_15 [Reducibility S] (ψ χ : V a → V b → QF V) : QThm S (iff (fiff2 ψ χ) (relEq ψ χ)) :=
  qiffI (q21_13 ψ χ) (q21_14 ψ χ)

/-- ✱21·151 `⊢ . (∃φ) . x̂ŷψ(x, y) = x̂ŷφ!(x, y)` [✱21·15 . ✱12·11]: "every relation can be defined by a
    predicative function". -/
theorem q21_151 [Reducibility S] (ψ : V a → V b → QF V) :
    QThm S (ex (τ := Ty.pred2 a b) fun φ => relEq ψ (pf2 φ)) :=
  QThm.mp (q12_11 ψ) (q10_11_28 fun φ => qiffMp (q21_15 ψ (pf2 φ)))             -- ✱21·15 . ✱12·11

/-- ✱21·16 `⊢ : (∃φ) : f{x̂ŷψ(x, y)} . ≡ . f{x̂ŷφ!(x, y)}` [✱21·12]. The second factor by ✱3·27 under (∃φ). -/
theorem q21_16 [Reducibility S] (ψ : V a → V b → QF V) (f : V (Ty.pred2 a b) → QF V) :
    QThm S (ex (τ := Ty.pred2 a b) fun φ => iff (rel ψ f) (rel (pf2 φ) f)) :=
  QThm.mp (q21_12 ψ f) (q10_11_28 fun _ => QL.t3_27 _ _)                          -- [✱21·12]

/-- ✱21·17 `⊢ : (φ) . f{x̂ŷφ!(x, y)} . ⊃ . f{x̂ŷψ(x, y)}` [✱21·16 . ✱10·1], as ✱20·17 (✱3·27, ✱2·06, ✱10·11,
    ✱10·23). -/
theorem q21_17 [Reducibility S] (ψ : V a → V b → QF V) (f : V (Ty.pred2 a b) → QF V) :
    QThm S (imp (.all (τ := Ty.pred2 a b) fun φ => rel (pf2 φ) f) (rel ψ f)) :=
  QThm.mp (q21_16 ψ f) (QThm.mp (q10_11 fun φ =>
      qsyl (QL.t3_27 _ _) (QThm.mp (q10_1 (fun φ => rel (pf2 φ) f) φ) (QL.t2_06 _ _ _)))  -- ✱10·1
    (qiffMp (q10_23 _ _)))                                                        -- [✱21·16]

/-- ✱21·18 `⊢ :. x̂ŷφ(x, y) = x̂ŷψ(x, y) . ⊃ : f{x̂ŷφ(x, y)} . ≡ . f{x̂ŷψ(x, y)}` [✱21·11·15] -/
theorem q21_18 [Reducibility S] (ψ χ : V a → V b → QF V) (f : V (Ty.pred2 a b) → QF V) :
    QThm S (imp (relEq ψ χ) (iff (rel ψ f) (rel χ f))) :=
  qsyl (qiffMpr (q21_15 ψ χ)) (q21_11 ψ χ f)                                      -- ✱21·11·15

/-- The step of ✱21·19 that is `[✱20·112 . ✱10·1] [✱4·2]` in ✱20·19 (`qclsIndisc`), with ✱21·112 and, for
    ✱10·301, ✱11·371: `(f) : f!x̂ŷφ!(x, y) . ⊃ . f!x̂ŷθ!(x, y) : ⊃ . φ!(x, y) ≡_{x,y} θ!(x, y)`. -/
theorem qrelIndisc [Reducibility S] (φ θ : V (Ty.pred2 a b)) :
    QThm S (imp (.all (τ := Ty.pred1 (Ty.pred2 a b)) fun f =>
        imp (rel (pf2 φ) fun φ' => .app1 f φ') (rel (pf2 θ) fun φ' => .app1 f φ'))
      (fiff2 (pf2 φ) (pf2 θ))) :=
  let F : V (Ty.pred2 a b) → QF V := fun χ => fiff2 (pf2 φ) (pf2 χ)
  let P : QF V := .all (τ := Ty.pred1 (Ty.pred2 a b)) fun f =>
    imp (rel (pf2 φ) fun φ' => .app1 f φ') (rel (pf2 θ) fun φ' => .app1 f φ')
  have h1 : ∀ g : V (Ty.pred1 (Ty.pred2 a b)),
      QThm S (imp (fiff (fun φ' => rel (pf2 φ') F) (fun φ' => rel (pf2 φ') fun χ => .app1 g χ))
        (imp P (imp (rel (pf2 φ) F) (rel (pf2 θ) F)))) := fun g =>
    have e1 := q10_1 (fun φ' => iff (rel (pf2 φ') F) (rel (pf2 φ') fun χ => .app1 g χ)) φ
    have e2 := q10_1 (fun φ' => iff (rel (pf2 φ') F) (rel (pf2 φ') fun χ => .app1 g χ)) θ
    have e3 := qsyl (qimpImpIffCongr e1 e2) (QL.t3_27 _ _)
    have e4 := q10_1 (fun f : V (Ty.pred1 (Ty.pred2 a b)) =>
      imp (rel (pf2 φ) fun φ' => .app1 f φ') (rel (pf2 θ) fun φ' => .app1 f φ')) g
    qsyl e3 (QThm.mp e4 (QL.t2_06 _ _ _))
  have h2 : QThm S (imp P (imp (rel (pf2 φ) F) (rel (pf2 θ) F))) :=
    QThm.mp (q21_112 F) (QThm.mp (q10_11 h1) (qiffMp (q10_23 _ _)))
  have h3 : QThm S (rel (pf2 φ) F) :=
    QThm.mp (q10_13 (q11_11 fun x y => QL.t4_2 (.app2 φ x y)) (q11_11 fun x y => QL.t4_2 (.app2 φ x y)))
      (q10_24 (fun χ => QF.and (fiff2 (pf2 χ) (pf2 φ)) (F χ)) φ)
  have h4 : QThm S (imp (rel (pf2 θ) F) (fiff2 (pf2 φ) (pf2 θ))) :=
    QThm.mp (q10_11 fun χ => qsyl (QL.t3_22 _ _) (q11_371 (pf2 φ) (pf2 χ) (pf2 θ))) (qiffMp (q10_23 _ _))
  qsyl h2 (qsyl (QThm.mp h3 (QL.t2_27 _ _)) h4)

/-- ✱21·19 `⊢ :. x̂ŷψ(x, y) = x̂ŷχ(x, y) . ≡ : (f) : f!x̂ŷψ(x, y) . ⊃ . f!x̂ŷχ(x, y)`
    [✱21·18 . ✱10·11·21 . ✱21·1 . ✱10·35 . (✱13·01) . ✱21·112 . ✱10·301]. The proof of ✱20·19 with ✱21 for ✱20,
    ✱12·11 for ✱12·1 and, for ✱10·301 and ✱10·32 of two variables, ✱11·371 and ✱10·32 under (x)
    (`qrelIndisc`, `qred2rel`). -/
theorem q21_19 [Reducibility S] (ψ χ : V a → V b → QF V) :
    QThm S (iff (relEq ψ χ) (.all (τ := Ty.pred1 (Ty.pred2 a b)) fun f =>
      imp (rel ψ fun φ => .app1 f φ) (rel χ fun φ => .app1 f φ))) :=
  let P : QF V := .all (τ := Ty.pred1 (Ty.pred2 a b)) fun f =>
    imp (rel ψ fun φ => .app1 f φ) (rel χ fun φ => .app1 f φ)
  have h1 : QThm S (imp (relEq ψ χ) P) :=
    q10_11_21 fun f => qsyl (q21_18 ψ χ fun φ => .app1 f φ) (QL.t3_26 _ _)       -- ✱21·18 . ✱10·11·21
  have h2 : ∀ (φ θ : V (Ty.pred2 a b)) (f : V (Ty.pred1 (Ty.pred2 a b))),
      QThm S (imp (QF.and (fiff2 (pf2 φ) ψ) (fiff2 (pf2 θ) χ))
        (imp (imp (rel ψ fun φ' => .app1 f φ') (rel χ fun φ' => .app1 f φ'))
          (imp (rel (pf2 φ) fun φ' => .app1 f φ') (rel (pf2 θ) fun φ' => .app1 f φ')))) := fun φ θ f =>
    have e1 := qsyl (QL.t3_26 _ _) (qsyl (qiffMp (q21_15 (pf2 φ) ψ)) (q21_18 (pf2 φ) ψ fun φ' => .app1 f φ'))
    have e2 := qsyl (QL.t3_27 _ _) (qsyl (qiffMp (q21_15 (pf2 θ) χ)) (q21_18 (pf2 θ) χ fun φ' => .app1 f φ'))
    qsyl (qimpImpIffCongr e1 e2) (QL.t3_27 _ _)
  have h3 : ∀ φ θ : V (Ty.pred2 a b),
      QThm S (imp (QF.and (fiff2 (pf2 φ) ψ) (fiff2 (pf2 θ) χ)) (imp P (relEq ψ χ))) := fun φ θ =>
    have k1 := qsyl (q10_11_21 (h2 φ θ)) (q10_27 _ _)
    have k2 := qimpImpTransR k1 (qrelIndisc φ θ)                                  -- ✱21·112
    have c := qsyl (qsyl (QL.t3_26 _ _) (qiffMp (qfiff2Symm (pf2 φ) ψ)))
      (QThm.mp (q11_371 ψ (pf2 φ) (pf2 θ)) (QL.t3_3 _ _ _))
    have d := qsyl (QL.t3_27 _ _)
      (QThm.mp (QThm.mp (q11_371 ψ (pf2 θ) χ) (QL.t3_3 _ _ _)) (QL.t2_04 _ _ _))  -- ✱10·301
    qimpImpTransR (qimpImpTrans k2 (qimpImpTrans c d)) (qiffMp (q21_15 ψ χ))
  have h4 : ∀ φ : V (Ty.pred2 a b), QThm S (imp (fiff2 (pf2 φ) ψ) (imp P (relEq ψ χ))) := fun φ =>
    have k := q10_11 fun θ => QThm.mp (QThm.mp (h3 φ θ) (QL.t3_3 _ _ _)) (QL.t2_04 _ _ _)
    QThm.mp (qred2rel χ) (QThm.mp k (qiffMp (q10_23 _ _)))
  have h5 : QThm S (imp P (relEq ψ χ)) :=
    QThm.mp (qred2rel ψ) (QThm.mp (q10_11 h4) (qiffMp (q10_23 _ _)))
  qiffI h1 h5

/-- ✱21·191 `⊢ :. x̂ŷψ(x, y) = x̂ŷχ(x, y) . ≡ : (f) : f!x̂ŷψ(x, y) . ≡ . f!x̂ŷχ(x, y)` [✱21·18·19]. As ✱20·191:
    ✱21·18 under (f) by ✱10·11·21, and ✱10·22 with Simp (✱3·26, `qfiffMp`) before ✱21·19. -/
theorem q21_191 [Reducibility S] (ψ χ : V a → V b → QF V) :
    QThm S (iff (relEq ψ χ) (.all (τ := Ty.pred1 (Ty.pred2 a b)) fun f =>
      iff (rel ψ fun φ => .app1 f φ) (rel χ fun φ => .app1 f φ))) :=
  qiffI (q10_11_21 fun f => q21_18 ψ χ fun φ => .app1 f φ)                       -- ✱21·18
    (qsyl (qfiffMp (τ := Ty.pred1 (Ty.pred2 a b)) (fun f => rel ψ fun φ => .app1 f φ)
      (fun f => rel χ fun φ => .app1 f φ)) (qiffMpr (q21_19 ψ χ)))                -- ✱21·19

/-! ## ✱21·2–✱21·24 -/

/-- ✱21·2 `⊢ . x̂ŷφ(x, y) = x̂ŷφ(x, y)` [✱21·15 . ✱4·2]. ✱4·2 is generalized over (x, y) by ✱11·11. -/
theorem q21_2 [Reducibility S] (φ : V a → V b → QF V) : QThm S (relEq φ φ) :=
  QThm.mp (q11_11 fun x y => QL.t4_2 (φ x y)) (qiffMp (q21_15 φ φ))               -- ✱21·15 . ✱4·2

/-- ✱21·21 `⊢ : x̂ŷφ(x, y) = x̂ŷψ(x, y) . ≡ . x̂ŷψ(x, y) = x̂ŷφ(x, y)` [✱21·15 . ✱10·32] (✱10·32 under (x)). -/
theorem q21_21 [Reducibility S] (φ ψ : V a → V b → QF V) : QThm S (iff (relEq φ ψ) (relEq ψ φ)) :=
  qiffTrans (qiffSymm (q21_15 φ ψ)) (qiffTrans (qfiff2Symm φ ψ) (q21_15 ψ φ))

/-- ✱21·22 `⊢ : x̂ŷφ(x, y) = x̂ŷψ(x, y) . x̂ŷψ(x, y) = x̂ŷχ(x, y) . ⊃ . x̂ŷφ(x, y) = x̂ŷχ(x, y)`
    [✱21·15 . ✱10·301]. ✱10·301 for two variables is ✱11·371; ✱21·15 is used on both factors (✱3·47). -/
theorem q21_22 [Reducibility S] (φ ψ χ : V a → V b → QF V) :
    QThm S (imp (QF.and (relEq φ ψ) (relEq ψ χ)) (relEq φ χ)) :=
  qsyl (QThm.mp (qandI (qiffMpr (q21_15 φ ψ)) (qiffMpr (q21_15 ψ χ))) (QL.t3_47 _ _ _ _))  -- ✱21·15
    (qsyl (q11_371 φ ψ χ) (qiffMp (q21_15 φ χ)))                                  -- ✱10·301

/-- ✱21·23 `⊢ : x̂ŷφ(x, y) = x̂ŷψ(x, y) . x̂ŷφ(x, y) = x̂ŷχ(x, y) . ⊃ . x̂ŷψ(x, y) = x̂ŷχ(x, y)` [✱21·21·22]
    (Fact, ✱3·45). -/
theorem q21_23 [Reducibility S] (φ ψ χ : V a → V b → QF V) :
    QThm S (imp (QF.and (relEq φ ψ) (relEq φ χ)) (relEq ψ χ)) :=
  qsyl (QThm.mp (qiffMp (q21_21 φ ψ)) (QL.t3_45 _ _ _)) (q21_22 ψ φ χ)          -- ✱21·21·22

/-- ✱21·24 `⊢ : x̂ŷψ(x, y) = x̂ŷφ(x, y) . x̂ŷχ(x, y) = x̂ŷφ(x, y) . ⊃ . x̂ŷψ(x, y) = x̂ŷχ(x, y)` [✱21·21·22]
    (✱3·47 with Id, `qandR`). -/
theorem q21_24 [Reducibility S] (φ ψ χ : V a → V b → QF V) :
    QThm S (imp (QF.and (relEq ψ φ) (relEq χ φ)) (relEq ψ χ)) :=
  qsyl (qandR (qiffMp (q21_21 χ φ))) (q21_22 ψ φ χ)                              -- ✱21·21·22

/-! ## ✱21·3–✱21·43 -/

/-- ✱21·3 `⊢ : x{x̂ŷψ(x, y)}y . ≡ . ψ(x, y)` [✱21·1·02 . ✱10·43·35 . ✱12·11]: "the primitive proposition ✱12·11
    is again required here". As ✱20·3: ✱10·43 for two variables (`qfiff2_43`: ✱11·1, ✱5·32) under (∃φ),
    ✱10·35 with p second (✱4·3, `qex_and_perm`), and ✱12·11 turned (✱10·32 under (x)) drops the asserted
    factor (✱3·27, ✱3·2). -/
theorem q21_3 [Reducibility S] (ψ : V a → V b → QF V) (x : V a) (y : V b) :
    QThm S (iff (relHolds x ψ y) (ψ x y)) :=
  let P : V (Ty.pred2 a b) → QF V := fun φ => fiff2 (pf2 φ) ψ
  have h1 := q10_11_281 fun φ => qfiff2_43 (pf2 φ) ψ x y                           -- ✱21·1·02 . ✱10·43
  have h2 := qex_and_perm P (ψ x y)                                               -- ✱10·35
  qiffTrans h1 (qiffTrans h2 (qand_true_left (qred2rel ψ)))                       -- ✱12·11

/-- ✱21·31 `⊢ :. x̂ŷψ(x, y) = x̂ŷχ(x, y) . ≡ : x{x̂ŷψ(x, y)}y . ≡_{x,y} . x{x̂ŷχ(x, y)}y` [✱21·15·3]. ✱21·3
    replaces both members under (x, y) (✱4·86, with ✱4·21 for the second member). -/
theorem q21_31 [Reducibility S] (ψ χ : V a → V b → QF V) :
    QThm S (iff (relEq ψ χ) (fiff2 (fun x y => relHolds x ψ y) (fun x y => relHolds x χ y))) :=
  qiffTrans (qiffSymm (q21_15 ψ χ))                                               -- ✱21·15
    (q10_11_271 fun x => q10_11_271 fun y =>
      qiffIffCongr (qiffSymm (q21_3 ψ x y)) (qiffSymm (q21_3 χ x y)))             -- ✱21·3

/-- ✱21·32 `⊢ . x̂ŷ[x{x̂ŷφ(x, y)}y] = x̂ŷφ(x, y)` [✱21·3·15]. ✱21·3 is generalized over (x, y) by ✱11·11. -/
theorem q21_32 [Reducibility S] (φ : V a → V b → QF V) :
    QThm S (relEq (fun x y => relHolds x φ y) φ) :=
  QThm.mp (q11_11 fun x y => q21_3 φ x y) (qiffMp (q21_15 (fun x y => relHolds x φ y) φ))  -- ✱21·3·15

/-- ✱21·33 `⊢ :. R = x̂ŷφ(x, y) . ≡ : xRy . ≡_{x,y} . φ(x, y)` [✱21·31·3], R real (an expression x̂ŷψ(x, y)).
    ✱21·3 replaces the second member under (x, y) (✱4·86 with ✱4·21). -/
theorem q21_33 [Reducibility S] (ψ φ : V a → V b → QF V) :
    QThm S (iff (relEq ψ φ) (fiff2 (fun x y => relHolds x ψ y) φ)) :=
  qiffTrans (q21_31 ψ φ)                                                          -- ✱21·31
    (q10_11_271 fun x => q10_11_271 fun y =>
      QThm.mp (q21_3 φ x y) (qiffCongrRImp (relHolds x ψ y) _ _))                 -- ✱21·3

/-- ✱21·42 `⊢ . x̂ŷ(xRy) = R` [✱21·3·15], R real (an expression x̂ŷψ(x, y)). -/
theorem q21_42 [Reducibility S] (ψ : V a → V b → QF V) : QThm S (relEq (fun x y => relHolds x ψ y) ψ) :=
  QThm.mp (q11_11 fun x y => q21_3 ψ x y) (qiffMp (q21_15 (fun x y => relHolds x ψ y) ψ))  -- ✱21·3·15

/-- ✱21·43 `⊢ :. R = S . ≡ : xRy . ≡_{x,y} . xSy` [✱21·15·3], R and S real (expressions x̂ŷψ(x, y),
    x̂ŷχ(x, y)): the statement and proof of ✱21·31. -/
theorem q21_43 [Reducibility S] (ψ χ : V a → V b → QF V) :
    QThm S (iff (relEq ψ χ) (fiff2 (fun x y => relHolds x ψ y) (fun x y => relHolds x χ y))) :=
  qiffTrans (qiffSymm (q21_15 ψ χ))                                               -- ✱21·15
    (q10_11_271 fun x => q10_11_271 fun y =>
      qiffIffCongr (qiffSymm (q21_3 ψ x y)) (qiffSymm (q21_3 χ x y)))             -- ✱21·3

/-! ## ✱21·53–✱21·58: relations and descriptions

  "✱20·5·51·52 have no analogues in the theory of relations" (p. 215). -/

/-- The analogue for relations of `qclsAllAt` (✱10·1 at a relation x̂ŷψ(x, y) whose defining function need
    not be predicative): ✱12·11 (turned, `qred2rel`), ✱10·1 at φ, `h` (each occurrence carried by ✱21·11),
    ✱2·06, ✱10·11, ✱10·23. -/
theorem qrelAllAt [Reducibility S] (G : (V a → V b → QF V) → QF V) (ψ : V a → V b → QF V)
    (h : ∀ φ : V (Ty.pred2 a b), QThm S (imp (fiff2 (pf2 φ) ψ) (imp (G (pf2 φ)) (G ψ)))) :
    QThm S (imp (relAll G) (G ψ)) :=
  have h2 : ∀ φ : V (Ty.pred2 a b), QThm S (imp (fiff2 (pf2 φ) ψ) (imp (relAll G) (G ψ))) := fun φ =>
    qsyl (h φ) (QThm.mp (q10_1 (fun φ => G (pf2 φ)) φ) (QL.t2_06 _ _ _))
  QThm.mp (qred2rel ψ) (QThm.mp (q10_11 h2) (qiffMp (q10_23 _ _)))

/-- The analogue for relations of `qclsExAt` (✱10·24): ✱12·11, ✱10·24 with ✱2·05, ✱10·11, ✱10·23. -/
theorem qrelExAt [Reducibility S] (G : (V a → V b → QF V) → QF V) (ψ : V a → V b → QF V)
    (h : ∀ φ : V (Ty.pred2 a b), QThm S (imp (fiff2 (pf2 φ) ψ) (imp (G ψ) (G (pf2 φ))))) :
    QThm S (imp (G ψ) (relEx G)) :=
  have h2 : ∀ φ : V (Ty.pred2 a b), QThm S (imp (fiff2 (pf2 φ) ψ) (imp (G ψ) (relEx G))) := fun φ =>
    qsyl (h φ) (QThm.mp (q10_24 (fun φ => G (pf2 φ)) φ) (QL.t2_05 _ _ _))
  QThm.mp (qred2rel ψ) (QThm.mp (q10_11 h2) (qiffMp (q10_23 _ _)))

/-- `x̂ŷψ(x, y) = x̂ŷχ(x, y) . ⊃ : W = x̂ŷψ(x, y) . ≡ . W = x̂ŷχ(x, y)` (✱21·22, Exp, Comm; ✱21·24 with the
    factors commuted, ✱3·22, Exp; Comp, ✱3·43), as `qclsEqR`. -/
theorem qrelEqR [Reducibility S] (ψ χ ω : V a → V b → QF V) :
    QThm S (imp (relEq ψ χ) (iff (relEq ω ψ) (relEq ω χ))) :=
  have h2 := QThm.mp (QThm.mp (q21_22 ω ψ χ) (QL.t3_3 _ _ _)) (QL.t2_04 _ _ _)
  have h3 := QThm.mp (qsyl (QL.t3_22 _ _) (q21_24 χ ω ψ)) (QL.t3_3 _ _ _)
  qcomp h2 h3

/-- ✱21·53 `⊢ :. S = R . ⊃_S . φS : ≡ . φR` [✱10·1 . ✱21·2·18·21 . Comm . ✱10·11·21], S apparent, R real (an
    expression x̂ŷψ(x, y)), φS a generic expression (`rel S f`). As ✱20·53: ✱10·1 at R is `qrelAllAt`
    (✱12·11, ✱10·32 under (x), ✱21·11 for both occurrences, joined by ✱4·84, ✱4·85, the ⊃ half by ✱3·26,
    ✱2·06, ✱10·23), ✱21·2 detached by ✱2·27, and ✱21·18's "≡" used left to right (✱3·26). -/
theorem q21_53 [Reducibility S] (ψ : V a → V b → QF V) (f : V (Ty.pred2 a b) → QF V) :
    QThm S (iff (relAll fun T => imp (relEq T ψ) (rel T f)) (rel ψ f)) :=
  let G : (V a → V b → QF V) → QF V := fun T => imp (relEq T ψ) (rel T f)
  have h1 : QThm S (imp (relAll G) (G ψ)) :=
    qrelAllAt G ψ fun θ =>
      qsyl (qimpImpIffCongr (q21_11 (pf2 θ) ψ fun θ' => rel ψ fun θ'' => ident θ' θ'')
        (q21_11 (pf2 θ) ψ f)) (QL.t3_26 _ _)                                      -- ✱10·1
  have h1' := qsyl h1 (QThm.mp (q21_2 ψ) (QL.t2_27 _ _))                          -- ✱21·2
  have h2 : ∀ θ : V (Ty.pred2 a b), QThm S (imp (relEq (pf2 θ) ψ) (imp (rel ψ f) (rel (pf2 θ) f))) := fun θ =>
    qsyl (qiffMp (q21_21 (pf2 θ) ψ)) (qsyl (q21_18 ψ (pf2 θ) f) (QL.t3_26 _ _))    -- ✱21·18·21
  qiffI h1' (q10_11_21 fun θ => QThm.mp (h2 θ) (QL.t2_04 _ _ _))                  -- Comm . ✱10·11·21

/-- ✱21·54's argument for an expression G in which the relation may occur several times, given the analogue
    of ✱21·18 for G (`hG`), as `qcls54`: (1) `hG`, ✱3·26, Imp (✱3·31), ✱10·11, ✱10·23; (2) ✱21·2, ✱3·2 and
    the analogue of ✱10·24 (`qrelExAt`), the identity got by ✱21·13 and G carried by `hG` (✱3·27), with
    ✱2·02, ✱2·06 and Comp (✱3·43). -/
theorem qrel54 [Reducibility S] (G : (V a → V b → QF V) → QF V) (ψ : V a → V b → QF V)
    (hG : ∀ φ : V (Ty.pred2 a b), QThm S (imp (relEq (pf2 φ) ψ) (iff (G (pf2 φ)) (G ψ)))) :
    QThm S (iff (relEx fun T => QF.and (relEq T ψ) (G T)) (G ψ)) :=
  have h1 : QThm S (imp (relEx fun T => QF.and (relEq T ψ) (G T)) (G ψ)) :=
    QThm.mp (q10_11 fun φ => QThm.mp (qsyl (hG φ) (QL.t3_26 _ _)) (QL.t3_31 _ _ _))
      (qiffMp (q10_23 _ _))
  have h2 : QThm S (imp (G ψ) (QF.and (relEq ψ ψ) (G ψ))) := QThm.mp (q21_2 ψ) (QL.t3_2 _ _)
  have h3 : QThm S (imp (QF.and (relEq ψ ψ) (G ψ)) (relEx fun T => QF.and (relEq T ψ) (G T))) :=
    qrelExAt (fun T => QF.and (relEq T ψ) (G T)) ψ fun φ =>
      have e := q21_13 (pf2 φ) ψ
      have k1 : QThm S (imp (fiff2 (pf2 φ) ψ) (imp (QF.and (relEq ψ ψ) (G ψ)) (relEq (pf2 φ) ψ))) :=
        qsyl e (QL.t2_02 _ _)
      have k2 : QThm S (imp (fiff2 (pf2 φ) ψ) (imp (QF.and (relEq ψ ψ) (G ψ)) (G (pf2 φ)))) :=
        qsyl (qsyl e (qsyl (hG φ) (QL.t3_27 _ _))) (QThm.mp (QL.t3_27 _ _) (QL.t2_06 _ _ _))
      qsyl (qcomp k1 k2) (QL.t3_43 _ _ _)
  qiffI h1 (qsyl h2 h3)

/-- ✱21·54 `⊢ :. (∃S) . S = R . φS . ≡ . φR` [✱21·18 . ✱10·11·23 . ✱21·2 . ✱10·24], R real (an expression
    x̂ŷψ(x, y)), φS generic (`rel S f`): `qrel54` with ✱21·18; ✱10·24 at R is the analogue `qrelExAt`. -/
theorem q21_54 [Reducibility S] (ψ : V a → V b → QF V) (f : V (Ty.pred2 a b) → QF V) :
    QThm S (iff (relEx fun T => QF.and (relEq T ψ) (rel T f)) (rel ψ f)) :=
  qrel54 (fun T => rel T f) ψ fun θ => q21_18 (pf2 θ) ψ f                         -- ✱21·18

/-- `[(ιR)(ΦR)] . x̂ŷφ(x, y) = (ιR)(ΦR) . ≡ : ΦR . ≡_R . R = x̂ŷφ(x, y)`, the description with the larger
    scope: ✱21·072 and `qrel54` for ΦR ≡_R R = S (with `qrelEqR` under (R): ✱4·86, ✱10·11·21, ✱10·271);
    the factors commuted (✱4·3) and x̂ŷφ(x, y) = S turned by ✱21·21 (✱4·36), under (∃S) by ✱10·11·281. -/
theorem qdescRelEq [Reducibility S] (Φ : (V a → V b → QF V) → QF V) (φ : V a → V b → QF V) :
    QThm S (iff (descRel Φ fun T => relEq φ T) (relAll fun R => iff (Φ R) (relEq R φ))) :=
  let G : (V a → V b → QF V) → QF V := fun T => relAll fun R => iff (Φ R) (relEq R T)
  have hG : ∀ θ : V (Ty.pred2 a b), QThm S (imp (relEq (pf2 θ) φ) (iff (G (pf2 θ)) (G φ))) := fun θ =>
    qsyl (q10_11_21 fun θ' => qsyl (qrelEqR (pf2 θ) φ (pf2 θ')) (qiffCongrRImp (Φ (pf2 θ')) _ _))
      (q10_271 _ _)
  qiffTrans (q10_11_281 fun θ => qiffTrans (QL.t4_3 (G (pf2 θ)) (relEq φ (pf2 θ)))
      (qandCongrL (G (pf2 θ)) (q21_21 φ (pf2 θ))))
    (qrel54 G φ hG)

/-- ✱21·55 `⊢ . x̂ŷφ(x, y) = (ιR){xRy . ≡_{x,y} . φ(x, y)}` [✱21·33·54 . ✱14·1], the description with the larger
    scope: ✱21·33 generalized over R (✱10·11) and read from right to left; "✱21·54 . ✱14·1" is
    `qdescRelEq`. -/
theorem q21_55 [Reducibility S] (φ : V a → V b → QF V) :
    QThm S (descRel (fun R => fiff2 (fun x y => relHolds x R y) φ) fun T => relEq φ T) :=
  QThm.mp (q10_11 fun θ => qiffSymm (q21_33 (pf2 θ) φ))                          -- ✱21·33
    (qiffMpr (qdescRelEq _ φ))                                                    -- ✱21·54 . ✱14·1

/-- ✱14·21 for descriptions of relations (✱10·5, ✱3·26), as `qdescClsE`. -/
theorem qdescRelE (Φ G : (V a → V b → QF V) → QF V) : QThm S (imp (descRel Φ G) (exists1Rel Φ)) :=
  qsyl (q10_5 (fun θ => relAll fun R => iff (Φ R) (relEq R (pf2 θ))) fun θ => G (pf2 θ)) (QL.t3_26 _ _)

/-- ✱21·56 `⊢ . E!(ιR){xRy . ≡_{x,y} . φ(x, y)}` [✱21·55 . ✱14·21] -/
theorem q21_56 [Reducibility S] (φ : V a → V b → QF V) :
    QThm S (exists1Rel fun R => fiff2 (fun x y => relHolds x R y) φ) :=
  QThm.mp (q21_55 φ) (qdescRelE _ _)                                              -- ✱21·55 . ✱14·21

/-- The analogue for relations of ✱13·183 and ✱20·25 (not numbered in ✱21): `R = x̂ŷφ(x, y) . ≡_R . R =
    x̂ŷψ(x, y) : ≡ . x̂ŷφ(x, y) = x̂ŷψ(x, y)`, by ✱20·25's proof with ✱21 for ✱20 (`qrelAllAt`, ✱21·11,
    ✱4·86, ✱3·26, ✱21·2, ✱2·27, `qrelEqR`). -/
theorem qrel183 [Reducibility S] (φ ψ : V a → V b → QF V) :
    QThm S (iff (relAll fun R => iff (relEq R φ) (relEq R ψ)) (relEq φ ψ)) :=
  let G : (V a → V b → QF V) → QF V := fun R => iff (relEq R φ) (relEq R ψ)
  have h1 : QThm S (imp (relAll G) (G φ)) :=
    qrelAllAt G φ fun θ =>
      qsyl (qimpIffIffCongr (q21_11 (pf2 θ) φ fun θ' => rel φ fun θ'' => ident θ' θ'')
        (q21_11 (pf2 θ) φ fun θ' => rel ψ fun θ'' => ident θ' θ'')) (QL.t3_26 _ _)
  have h1' := qsyl h1 (qsyl (QL.t3_26 _ _) (QThm.mp (q21_2 φ) (QL.t2_27 _ _)))
  qiffI h1' (q10_11_21 fun θ => qrelEqR φ ψ (pf2 θ))

/-- ✱21·57 `⊢ :. x̂ŷφ(x, y) = (ιR)(fR) . ⊃ : g{x̂ŷφ(x, y)} . ≡ . g{(ιR)(fR)}` [✱14·1 . ✱21·54 . ✱13·183], as
    ✱20·57: (1) is `qdescRelEq`; fR is replaced by R = x̂ŷφ(x, y) under (R) (✱4·86, ✱10·11·27, ✱10·271,
    Fact as ✱4·36, ✱10·11·21, ✱10·281); "✱13·183" is its analogue for relations (`qrel183`), with ✱21·21
    for ✱21·54 (✱4·36). -/
theorem q21_57 [Reducibility S] (φ : V a → V b → QF V) (F : (V a → V b → QF V) → QF V)
    (g : V (Ty.pred2 a b) → QF V) :
    QThm S (imp (descRel F fun T => relEq φ T) (iff (rel φ g) (descRel F fun T => rel T g))) :=
  let A : QF V := relAll fun R => iff (F R) (relEq R φ)
  have h1 : QThm S (imp (descRel F fun T => relEq φ T) A) := qiffMp (qdescRelEq F φ)  -- ✱14·1 . ✱21·54
  have h3 : QThm S (imp A (iff (descRel F fun T => rel T g)
      (relEx fun T => QF.and (relAll fun R => iff (relEq R φ) (relEq R T)) (rel T g)))) :=
    qsyl (q10_11_21 fun θ =>
        qsyl (q10_11_27 fun θ' => QL.t4_86 (F (pf2 θ')) (relEq (pf2 θ') φ) (relEq (pf2 θ') (pf2 θ)))
          (qsyl (q10_271 _ _) (QL.t4_36 _ _ (rel (pf2 θ) g))))
      (q10_281 _ _)                                                               -- ✱14·1
  have e4 : QThm S (iff (relEx fun T => QF.and (relAll fun R => iff (relEq R φ) (relEq R T)) (rel T g))
      (rel φ g)) :=
    qiffTrans (q10_11_281 fun θ => qandCongrL (rel (pf2 θ) g)
        (qiffTrans (qrel183 φ (pf2 θ)) (q21_21 φ (pf2 θ))))                       -- ✱13·183
      (q21_54 φ g)                                                                -- ✱21·54
  qsyl h1 (qimpIffSymm (qimpIffTransR h3 e4))

/-- ✱21·58 `⊢ . x̂ŷφ(x, y) = (ιR){R = x̂ŷφ(x, y)}` [✱4·2 . ✱10·11 . ✱21·54 . ✱14·1] -/
theorem q21_58 [Reducibility S] (φ : V a → V b → QF V) :
    QThm S (descRel (fun R => relEq R φ) fun T => relEq φ T) :=
  QThm.mp (q10_11 fun θ => QL.t4_2 (relEq (pf2 θ) φ)) (qiffMpr (qdescRelEq _ φ))  -- ✱4·2 . ✱10·11 . ✱21·54 . ✱14·1

/-! ## ✱21·6–✱21·71: relations have the formal properties of individuals

  ✱21·631 and ✱21·632 (significance) are built into the syntax. -/

/-- ✱21·6 `⊢ : (∃R) . fR . ≡ . ∼{(R) . ∼fR}` [Proof as in ✱20·6: ✱4·2 . (✱21·071) . (✱10·01) . (✱21·07)] -/
theorem q21_6 (F : (V a → V b → QF V) → QF V) : QThm S (iff (relEx F) (.neg (relAll fun R => .neg (F R)))) :=
  QL.t4_2 _

/-- ✱21·61 `⊢ : (R) . fR . ⊃ . fS` [Proof as in ✱20·61: ✱10·1 . (✱21·07)], S of the form x̂ŷψ!(x, y). -/
theorem q21_61 (F : (V a → V b → QF V) → QF V) (ψ : V (Ty.pred2 a b)) : QThm S (imp (relAll F) (F (pf2 ψ))) :=
  q10_1 (fun φ => F (pf2 φ)) ψ

/-- ✱21·62 "When fR is true, whatever possible argument of the form x̂ŷφ!(x, y) R may be, (R) . fR is true"
    [Proof as in ✱20·62: ✱10·11] -/
theorem q21_62 {F : (V a → V b → QF V) → QF V} (h : ∀ ψ : V (Ty.pred2 a b), QThm S (F (pf2 ψ))) :
    QThm S (relAll F) :=
  q10_11 h

/-- ✱21·63 `⊢ :. (R) . p ∨ fR . ⊃ : p . ∨ . (R) . fR` [Proof as in ✱20·63: ✱4·2 . (✱21·07) . ✱10·12] -/
theorem q21_63 (p : QF V) (F : (V a → V b → QF V) → QF V) :
    QThm S (imp (relAll fun R => .or p (F R)) (.or p (relAll F))) :=
  q10_12 p fun φ => F (pf2 φ)

/-- ✱21·633 "'Whatever possible relation R may be, f(R, S) is true whatever possible relation S may be'
    implies 'whatever possible relation S may be, f(R, S) is true whatever possible relation R may be'"
    [Proof as in ✱20·633: ✱11·07] -/
theorem q21_633 {c d : Ty} {F : (V a → V b → QF V) → (V c → V d → QF V) → QF V}
    (h : QThm S (relAll fun R => relAll fun T => F R T)) : QThm S (relAll fun T => relAll fun R => F R T) :=
  q11_07 (φ := fun φ ψ => F (pf2 φ) (pf2 ψ)) h

/-- ✱21·64 `⊢ :. (R) . fR : (R) . gR : ⊃ . fS . gS` [Proof as in ✱20·64: ✱4·2 . (✱21·07) . ✱10·14] -/
theorem q21_64 (F G : (V a → V b → QF V) → QF V) (ψ : V (Ty.pred2 a b)) :
    QThm S (imp (QF.and (relAll F) (relAll G)) (QF.and (F (pf2 ψ)) (G (pf2 ψ)))) :=
  q10_14 (fun φ => F (pf2 φ)) (fun φ => G (pf2 φ)) ψ

/-- ✱21·7 `⊢ : (∃g) : fR . ≡_R . g!R` [Proof as in ✱20·7]: by ✱21·07 the statement is ✱21·112. -/
theorem q21_7 [Reducibility S] (f : V (Ty.pred2 a b) → QF V) :
    QThm S (ex (τ := Ty.pred1 (Ty.pred2 a b)) fun g =>
      relAll fun R => iff (rel R f) (rel R fun χ => .app1 g χ)) :=
  q21_112 f                                                                       -- ✱21·112

/-- ✱20·111 for a context of two arguments, eliminated at the first by a condition E (✱20·01 or ✱21·01):
    `f(φ, x) . ≡_{φ,x} . g(φ, x) : ⊃ : f{φ, x} . ≡_{φ,x} . g{φ, x}` (`qcls111_2`'s lines: ✱11·1, ✱4·36 with
    ✱4·3, ✱10·11·21, ✱10·281, ✱11·11·3). -/
theorem qelim1_2 {τ₁ τ₂ : Ty} (E : V τ₁ → V τ₁ → QF V) (f g : V τ₁ → V τ₂ → QF V) :
    QThm S (imp (fiff2 f g)
      (fiff2 (fun φ x => ex fun χ => QF.and (E χ φ) (f χ x)) (fun φ x => ex fun χ => QF.and (E χ φ) (g χ x)))) :=
  have h : ∀ (φ : V τ₁) (x : V τ₂), QThm S (imp (fiff2 f g)
      (iff (ex fun χ => QF.and (E χ φ) (f χ x)) (ex fun χ => QF.and (E χ φ) (g χ x)))) := fun φ x =>
    qsyl (q10_11_21 fun ψ => qsyl (q11_1 (fun ψ x => iff (f ψ x) (g ψ x)) ψ x)
        (qandCongrRImp (f ψ x) (g ψ x) (E ψ φ)))
      (q10_281 _ _)
  qiffMpr (q11_3 _ _) |> QThm.mp (q11_11 h)

/-- ✱20·703's lines for a context of two arguments, each eliminated by its condition (✱20·01 or ✱21·01), the
    first with the larger scope: ✱11·1 at (χ, θ) and ✱4·36 with ✱4·3 twice for PM's ✱10·311, ✱11·11·3·341,
    and ✱10·35 under (∃χ) (✱10·11·281). -/
theorem qelim2 {τ₁ τ₂ : Ty} (E₁ : V τ₁ → V τ₁ → QF V) (E₂ : V τ₂ → V τ₂ → QF V) (f g : V τ₁ → V τ₂ → QF V) :
    QThm S (imp (fiff2 f g)
      (fiff2 (fun φ ψ => ex fun χ => QF.and (E₁ χ φ) (ex fun θ => QF.and (E₂ θ ψ) (f χ θ)))
        (fun φ ψ => ex fun χ => QF.and (E₁ χ φ) (ex fun θ => QF.and (E₂ θ ψ) (g χ θ))))) :=
  let K (h : V τ₁ → V τ₂ → QF V) (φ : V τ₁) (ψ : V τ₂) (χ : V τ₁) (θ : V τ₂) : QF V :=
    QF.and (E₁ χ φ) (QF.and (E₂ θ ψ) (h χ θ))
  have r : ∀ (h : V τ₁ → V τ₂ → QF V) φ ψ, QThm S (iff (ex2 (K h φ ψ))
      (ex fun χ => QF.and (E₁ χ φ) (ex fun θ => QF.and (E₂ θ ψ) (h χ θ)))) := fun h φ ψ =>
    q10_11_281 fun χ => q10_35 (fun θ => QF.and (E₂ θ ψ) (h χ θ)) (E₁ χ φ)
  have l : ∀ φ ψ, QThm S (imp (fiff2 f g)
      (iff (ex fun χ => QF.and (E₁ χ φ) (ex fun θ => QF.and (E₂ θ ψ) (f χ θ)))
        (ex fun χ => QF.and (E₁ χ φ) (ex fun θ => QF.and (E₂ θ ψ) (g χ θ))))) := fun φ ψ =>
    have l1 : ∀ χ θ, QThm S (imp (fiff2 f g) (iff (K f φ ψ χ θ) (K g φ ψ χ θ))) := fun χ θ =>
      qsyl (q11_1 (fun χ θ => iff (f χ θ) (g χ θ)) χ θ)
        (qsyl (qandCongrRImp _ _ (E₂ θ ψ)) (qandCongrRImp _ _ (E₁ χ φ)))
    have l2 := qsyl (qiffMpr (q11_3 _ _) |> QThm.mp (q11_11 l1)) (q11_341 (K f φ ψ) (K g φ ψ))
    qimpIffTransL (qiffSymm (r f φ ψ)) (qimpIffTransR l2 (r g φ ψ))
  qiffMpr (q11_3 _ _) |> QThm.mp (q11_11 l)

/-- ✱21·701 `⊢ : (∃g) : f(R, x) . ≡_{R,x} . g!(R, x)` [Proof as in ✱20·701]: ✱12·11 and ✱21·111 for two
    arguments (`qelim1_2`). fR, x is generic (`rel R (f · x)`), g!(R, x) is `rel R (g!(·, x))`. -/
theorem q21_701 [Reducibility S] {c : Ty} (f : V (Ty.pred2 a b) → V c → QF V) :
    QThm S (ex (τ := Ty.pred2 (Ty.pred2 a b) c) fun g =>
      fiff2 (fun φ x => rel (pf2 φ) fun χ => f χ x) (fun φ x => rel (pf2 φ) fun χ => .app2 g χ x)) :=
  QThm.mp (q12_11 f) (q10_11_28 fun g =>
    qelim1_2 (fun χ φ => fiff2 (pf2 χ) (pf2 φ)) f fun χ x => .app2 g χ x)          -- ✱12·11 . ✱21·111

/-- ✱21·702 `⊢ : (∃g) : f(x, R) . ≡_{R,x} . g!(R, x)` [Proof as in ✱20·702], as printed: g!(R, x), with R
    first (✱20·702 has g!{x, ẑ(φ!z)}). ✱12·11 is applied to f(x, R) as a function of (R, x). -/
theorem q21_702 [Reducibility S] {c : Ty} (f : V c → V (Ty.pred2 a b) → QF V) :
    QThm S (ex (τ := Ty.pred2 (Ty.pred2 a b) c) fun g =>
      fiff2 (fun φ x => rel (pf2 φ) fun χ => f x χ) (fun φ x => rel (pf2 φ) fun χ => .app2 g χ x)) :=
  QThm.mp (q12_11 fun χ x => f x χ) (q10_11_28 fun g =>
    qelim1_2 (fun χ φ => fiff2 (pf2 χ) (pf2 φ)) (fun χ x => f x χ) fun χ x => .app2 g χ x)  -- ✱12·11 . ✱21·111

/-- ✱21·703 `⊢ : (∃g) : f(R, S) . ≡_{R,S} . g!(R, S)` [Proof as in ✱20·703]: ✱20·703's lines (`qelim2`) and
    ✱12·11; R has the larger scope. -/
theorem q21_703 [Reducibility S] {c d : Ty} (f : V (Ty.pred2 a b) → V (Ty.pred2 c d) → QF V) :
    QThm S (ex (τ := Ty.pred2 (Ty.pred2 a b) (Ty.pred2 c d)) fun g =>
      fiff2 (fun φ ψ => rel (pf2 φ) fun χ => rel (pf2 ψ) fun θ => f χ θ)
        (fun φ ψ => rel (pf2 φ) fun χ => rel (pf2 ψ) fun θ => .app2 g χ θ)) :=
  QThm.mp (q12_11 f) (q10_11_28 fun g =>
    qelim2 (fun χ φ => fiff2 (pf2 χ) (pf2 φ)) (fun θ ψ => fiff2 (pf2 θ) (pf2 ψ)) f
      fun χ θ => .app2 g χ θ)                                                     -- ✱20·703 . ✱12·11

/-- ✱21·704 `⊢ : (∃g) : f(R, α) . ≡_{R,α} . g!(R, α)` [Proof as in ✱20·703]: a relation and a class, R with
    the larger scope (`qelim2` with ✱21·01 and ✱20·01). -/
theorem q21_704 [Reducibility S] {c : Ty} (f : V (Ty.pred2 a b) → V (Ty.pred1 c) → QF V) :
    QThm S (ex (τ := Ty.pred2 (Ty.pred2 a b) (Ty.pred1 c)) fun g =>
      fiff2 (fun φ ψ => rel (pf2 φ) fun χ => cls (pf ψ) fun θ => f χ θ)
        (fun φ ψ => rel (pf2 φ) fun χ => cls (pf ψ) fun θ => .app2 g χ θ)) :=
  QThm.mp (q12_11 f) (q10_11_28 fun g =>
    qelim2 (fun χ φ => fiff2 (pf2 χ) (pf2 φ)) (fun θ ψ => fiff (pf θ) (pf ψ)) f
      fun χ θ => .app2 g χ θ)                                                     -- ✱20·703 . ✱12·11

/-- ✱21·705 `⊢ : (∃g) : f(α, R) . ≡_{α,R} . g!(α, R)` [Proof as in ✱20·703]: α with the larger scope. -/
theorem q21_705 [Reducibility S] {c : Ty} (f : V (Ty.pred1 c) → V (Ty.pred2 a b) → QF V) :
    QThm S (ex (τ := Ty.pred2 (Ty.pred1 c) (Ty.pred2 a b)) fun g =>
      fiff2 (fun φ ψ => cls (pf φ) fun χ => rel (pf2 ψ) fun θ => f χ θ)
        (fun φ ψ => cls (pf φ) fun χ => rel (pf2 ψ) fun θ => .app2 g χ θ)) :=
  QThm.mp (q12_11 f) (q10_11_28 fun g =>
    qelim2 (fun χ φ => fiff (pf χ) (pf φ)) (fun θ ψ => fiff2 (pf2 θ) (pf2 ψ)) f
      fun χ θ => .app2 g χ θ)                                                     -- ✱20·703 . ✱12·11

/-- ✱21·71 `⊢ :. R = S . ≡ : g!R . ⊃_g . g!S` [Proof as in ✱20·71]: R, S real, so the statement is ✱21·19. -/
theorem q21_71 [Reducibility S] (ψ χ : V a → V b → QF V) :
    QThm S (iff (relEq ψ χ) (.all (τ := Ty.pred1 (Ty.pred2 a b)) fun g =>
      imp (rel ψ fun φ => .app1 g φ) (rel χ fun φ => .app1 g φ))) :=
  q21_19 ψ χ                                                                      -- ✱21·19

/-! ## Classes of relations and relations of relations: ✱21·03, ✱21·08–✱21·083; ✱21·4, ✱21·41

  As for classes of classes (PM/Star20.lean, `qcls20_3`), with ✱21·01, ✱21·11, ✱21·7, ✱12·11 and
  `qrelAllAt` for ✱20·01, ✱20·11, ✱20·7, ✱12·1 and `qclsAllAt`. ✱21·4's hint "✱20·3 . (✱21·03)" cites
  ✱20·3 for the class of relations Rel: `qrelCls20_3`. -/

/-- `Ψ` is extensional: `⊢ :. ψ(x, y) . ≡_{x,y} . χ(x, y) : ⊃ : Ψ{x̂ŷψ(x, y)} . ≡ . Ψ{x̂ŷχ(x, y)}` for all ψ, χ,
    i.e. ✱21·11 for the expression ΨR. -/
def RelExt (S : Sys V) (Ψ : (V a → V b → QF V) → QF V) : Prop :=
  ∀ ψ χ : V a → V b → QF V, QThm S (imp (fiff2 ψ χ) (iff (Ψ ψ) (Ψ χ)))

/-- A generic expression f{R} (`rel R f`) is extensional: ✱21·11. -/
theorem relExt_rel (f : V (Ty.pred2 a b) → QF V) : RelExt S fun R => rel R f :=
  fun ψ χ => q21_11 ψ χ f

/-- (∃v) . Ψ(v, R) is extensional when each Ψ(v, R) is: ✱10·11·21 and ✱10·281. -/
theorem relExt_ex {τ : Ty} (Ψ : V τ → (V a → V b → QF V) → QF V) (h : ∀ v, RelExt S (Ψ v)) :
    RelExt S fun R => ex fun v => Ψ v R :=
  fun ψ χ => qsyl (q10_11_21 fun v => h v ψ χ) (q10_281 _ _)

/-- The defining expression of Rel, (∃φ) . R = x̂ŷφ!(x, y), is extensional (`relExt_ex`, `relExt_rel`). -/
theorem relExt_Rel : RelExt S (Rel (V := V) (a := a) (b := b)) :=
  relExt_ex (fun φ R => relEq R (pf2 φ)) fun _ => relExt_rel _

/-- The bare application ψ(x, y), a function of ψ rather than of the relation x̂ŷψ(x, y), is
    extensional too: ✱11·1. `RelExpr` leaves it out, as `ClsExpr` leaves out ψx (`clsExt_app`). -/
theorem relExt_app (x : V a) (y : V b) : RelExt S fun R => R x y :=
  fun ψ χ => q11_1 (fun u v => iff (ψ u v) (χ u v)) x y

/-- ✱21·1 for classes of relations: `⊢ :. f{R̂(ψR)} . ≡ : (∃φ) : ψR . ≡_R . φ!R : f(φ!R̂)` [✱4·2 . (✱21·082)]. -/
theorem qrelCls1 (Ψ : (V a → V b → QF V) → QF V) (f : V (Ty.pred1 (Ty.pred2 a b)) → QF V) :
    QThm S (iff (relCls Ψ f) (ex (τ := Ty.pred1 (Ty.pred2 a b)) fun φ =>
      QF.and (relAll fun R => iff (Ψ R) (relClsApp φ R)) (f φ))) :=
  QL.t4_2 _

/-- `⊢ : R ∈ φ!R̂ . ≡ . φ!R` [✱4·2 . (✱21·083)] -/
theorem qmemRelCls (R : V a → V b → QF V) (φ : V (Ty.pred1 (Ty.pred2 a b))) :
    QThm S (iff (memRelCls R φ) (relClsApp φ R)) :=
  QL.t4_2 _

/-- `⊢ :. R ∈ R̂(ψR) . ≡ : (∃φ) : ψT . ≡_T . φ!T : φ!R` [✱4·2 . (✱21·082) . (✱21·083)]. -/
theorem qrelClsMem (Ψ : (V a → V b → QF V) → QF V) (R : V a → V b → QF V) :
    QThm S (iff (R ∈ Ψ) (ex (τ := Ty.pred1 (Ty.pred2 a b)) fun φ =>
      QF.and (relAll fun T => iff (Ψ T) (relClsApp φ T)) (relClsApp φ R))) :=
  QL.t4_2 _

/-- `⊢ :. φ!{x̂ŷψ(x, y)} . ≡ : (∃χ) : χ!(x, y) . ≡_{x,y} . ψ(x, y) : φ!χ!(x̂, ŷ)` [✱21·1]: ✱21·01 with context
    φ!χ!(x̂, ŷ). -/
theorem qrelClsApp (φ : V (Ty.pred1 (Ty.pred2 a b))) (ψ : V a → V b → QF V) :
    QThm S (iff (relClsApp φ ψ) (ex (τ := Ty.pred2 a b) fun χ => QF.and (fiff2 (pf2 χ) ψ) (.app1 φ χ))) :=
  q21_1 ψ _

/-- ✱21·1 for relations of relations: `⊢ :. f{R̂Ŝψ(R, S)} . ≡ : (∃φ) : ψ(R, S) . ≡_{R,S} . φ!(R, S) :
    f{φ!(R̂, Ŝ)}` [✱4·2 . (✱21·08)]. -/
theorem qrelRel1 {c d : Ty} (Ψ : (V a → V b → QF V) → (V c → V d → QF V) → QF V)
    (f : V (Ty.pred2 (Ty.pred2 a b) (Ty.pred2 c d)) → QF V) :
    QThm S (iff (relRel Ψ f) (ex (τ := Ty.pred2 (Ty.pred2 a b) (Ty.pred2 c d)) fun φ =>
      QF.and (relAll fun R => relAll fun T => iff (Ψ R T) (relRelApp φ R T)) (f φ))) :=
  QL.t4_2 _

/-- `⊢ : P{φ!(R̂, Ŝ)}Q . ≡ . φ!(P, Q)` [✱4·2 . (✱21·081)] -/
theorem qrelAppRel {c d : Ty} (P : V a → V b → QF V) (φ : V (Ty.pred2 (Ty.pred2 a b) (Ty.pred2 c d)))
    (Q : V c → V d → QF V) : QThm S (iff (relAppRel P φ Q) (relRelApp φ P Q)) :=
  QL.t4_2 _

/-- `⊢ :. φ!(x̂ŷψ(x, y), x̂ŷω(x, y)) . ≡ : (∃χ) : χ!(x, y) . ≡_{x,y} . ψ(x, y) : (∃θ) : θ!(x, y) . ≡_{x,y} .
    ω(x, y) : φ!(χ!(x̂, ŷ), θ!(x̂, ŷ))` [✱21·1]: ✱21·01 for each relation, the first with the larger scope. -/
theorem qrelRelApp {c d : Ty} (φ : V (Ty.pred2 (Ty.pred2 a b) (Ty.pred2 c d))) (ψ : V a → V b → QF V)
    (ω : V c → V d → QF V) :
    QThm S (iff (relRelApp φ ψ ω) (ex (τ := Ty.pred2 a b) fun χ => QF.and (fiff2 (pf2 χ) ψ)
      (ex (τ := Ty.pred2 c d) fun θ => QF.and (fiff2 (pf2 θ) ω) (.app2 φ χ θ)))) :=
  q21_1 ψ _

/-- `qclsGen` for relations: an extensional expression of a predicative relation x̂ŷθ!(x, y) is
    f{x̂ŷθ!(x, y)} for the context f(χ!(x̂, ŷ)) that is the expression of x̂ŷχ!(x, y). ⊃: θ!(x, y) ≡_{x,y}
    θ!(x, y) (✱4·2, ✱11·11), joined (✱3·2), and ✱10·24 at θ. ⊂: `hΨ` (✱3·26) with Imp (✱3·31), under (∃χ)
    by ✱10·11, ✱10·23. -/
theorem qrelGen (Ψ : (V a → V b → QF V) → QF V) (hΨ : RelExt S Ψ) (θ : V (Ty.pred2 a b)) :
    QThm S (iff (Ψ (pf2 θ)) (rel (pf2 θ) fun χ => Ψ (pf2 χ))) :=
  have h1 : QThm S (imp (Ψ (pf2 θ)) (rel (pf2 θ) fun χ => Ψ (pf2 χ))) :=
    qsyl (QThm.mp (q11_11 fun x y => QL.t4_2 (.app2 θ x y)) (QL.t3_2 _ _))
      (q10_24 (fun χ => QF.and (fiff2 (pf2 χ) (pf2 θ)) (Ψ (pf2 χ))) θ)
  have h2 : QThm S (imp (rel (pf2 θ) fun χ => Ψ (pf2 χ)) (Ψ (pf2 θ))) :=
    QThm.mp (q10_11 fun χ => QThm.mp (qsyl (hΨ (pf2 χ) (pf2 θ)) (QL.t3_26 _ _)) (QL.t3_31 _ _ _))
      (qiffMp (q10_23 _ _))
  qiffI h1 h2

/-- ✱21·7, the analogue of ✱12·1 for relations, for an extensional expression ΨR: `⊢ : (∃g) : ΨR . ≡_R . g!R`.
    ✱21·7 for the context f(χ!(x̂, ŷ)) = Ψ{x̂ŷχ!(x, y)}, and `qrelGen` for the first member, under (R) and
    (∃g) (✱10·11·27·28). -/
theorem qrelRed [Reducibility S] (Ψ : (V a → V b → QF V) → QF V) (hΨ : RelExt S Ψ) :
    QThm S (ex (τ := Ty.pred1 (Ty.pred2 a b)) fun g => relAll fun R => iff (Ψ R) (relClsApp g R)) :=
  QThm.mp (q21_7 fun χ => Ψ (pf2 χ)) (q10_11_28 fun _ => q10_11_27 fun θ =>
    qsyl (QThm.mp (qrelGen Ψ hΨ θ) (QL.t3_2 _ _)) (QL.t4_22 _ _ _))                -- ✱21·7

/-- ✱10·43 for relations, at a relation x̂ŷψ(x, y) whose defining function need not be predicative, as
    `qcls10_43`: `qrelAllAt` for ✱10·1, the members carried by `hΨ`, `hΦ`, joined by ✱4·86 (✱3·26); ✱5·32. -/
theorem qrel10_43 [Reducibility S] (Ψ Φ : (V a → V b → QF V) → QF V) (hΨ : RelExt S Ψ) (hΦ : RelExt S Φ)
    (ψ : V a → V b → QF V) :
    QThm S (iff (QF.and (relAll fun T => iff (Ψ T) (Φ T)) (Ψ ψ))
      (QF.and (relAll fun T => iff (Ψ T) (Φ T)) (Φ ψ))) :=
  QThm.mp (qrelAllAt (fun T => iff (Ψ T) (Φ T)) ψ fun θ =>
      qsyl (qimpIffIffCongr (hΨ (pf2 θ) ψ) (hΦ (pf2 θ) ψ)) (QL.t3_26 _ _))         -- ✱10·1
    (qiffMp (QL.t5_32 _ (Ψ ψ) (Φ ψ)))                                             -- ✱5·32

/-- ✱20·3 for classes of relations: `⊢ : R ∈ R̂(ΨR) . ≡ . ΨR`, R real (an expression x̂ŷψ(x, y)) and ΨR
    extensional. `qcls20_3`'s lines: ✱21·082, ✱21·083 (`qrelClsMem`); ✱10·43 at R (`qrel10_43`) under (∃φ);
    ✱10·35 with p second (✱4·3); ✱21·7 (`qrelRed`) for ✱12·1 (✱3·27, ✱3·2). -/
theorem qrelCls20_3 [Reducibility S] (Ψ : (V a → V b → QF V) → QF V) (hΨ : RelExt S Ψ)
    (ψ : V a → V b → QF V) : QThm S (iff (ψ ∈ Ψ) (Ψ ψ)) :=
  let P : V (Ty.pred1 (Ty.pred2 a b)) → QF V := fun φ => relAll fun T => iff (Ψ T) (relClsApp φ T)
  calc (ψ ∈ Ψ)
      ≡ ex (fun φ => QF.and (P φ) (relClsApp φ ψ)) := qrelClsMem Ψ ψ               -- (✱21·082) . (✱21·083)
    _ ≡ ex (fun φ => QF.and (P φ) (Ψ ψ)) :=
        q10_11_281 fun φ => qiffSymm (qrel10_43 Ψ (relClsApp φ) hΨ (relExt_rel _) ψ)  -- [✱10·43]
    _ ≡ QF.and (ex P) (Ψ ψ) := qex_and_perm P (Ψ ψ)                                -- [✱10·35]
    _ ≡ Ψ ψ := qand_true_left (qrelRed Ψ hΨ)                                      -- [✱12·1]

/-- ✱21·4 `⊢ : R ∈ Rel . ≡ . (∃φ) . R = x̂ŷφ!(x, y)` [✱20·3 . (✱21·03)], R real (an expression x̂ŷψ(x, y)).
    ✱20·3 is its analogue for classes of relations (`qrelCls20_3`), at the defining expression of Rel,
    extensional by ✱21·11 under (∃φ) (`relExt_Rel`). -/
theorem q21_4 [Reducibility S] (ψ : V a → V b → QF V) :
    QThm S (iff (ψ ∈ Rel) (ex (τ := Ty.pred2 a b) fun φ => relEq ψ (pf2 φ))) :=
  qrelCls20_3 Rel relExt_Rel ψ                                                    -- ✱20·3 . (✱21·03)

/-- ✱21·41 `⊢ . x̂ŷφ(x, y) ∈ Rel` [✱21·4·151] -/
theorem q21_41 [Reducibility S] (φ : V a → V b → QF V) : QThm S (φ ∈ Rel) :=
  QThm.mp (q21_151 φ) (qiffMpr (q21_4 φ))                                         -- ✱21·4·151

/-! ## Every expression of a relation that PM's notation forms is extensional (p. 213)

  After ✱21·11: "This proposition proves that every proposition about a relation expresses an extensional
  property of the determining function" (p. 213). As `ClsExpr` and `clsExpr_ext` (PM/Star20.lean), with
  ✱21·01 and ✱21·11 for ✱20·01 and ✱20·11. -/

/-- The expressions ΨR of a relation R that PM's notation forms: from formulas not containing R by ∼, ∨, (x),
    and by ✱21·01 at R (f{R}, the context f possibly containing R again). As for `ClsExpr`, each of PM's
    notations (R = S, xRy, φ!R, R ∈ κ, a class, relation or description whose defining function contains
    R, apparent classes and relations) unfolds into these. -/
inductive RelExpr {V : Ty → Type} {a b : Ty} : ((V a → V b → QF V) → QF V) → Prop
  | const (r : QF V) : RelExpr fun _ => r
  | neg {F : (V a → V b → QF V) → QF V} : RelExpr F → RelExpr fun R => .neg (F R)
  | or {F G : (V a → V b → QF V) → QF V} : RelExpr F → RelExpr G → RelExpr fun R => .or (F R) (G R)
  | all {τ : Ty} {F : V τ → (V a → V b → QF V) → QF V} : (∀ x, RelExpr (F x)) →
      RelExpr fun R => .all fun x => F x R
  | rel {F : V (Ty.pred2 a b) → (V a → V b → QF V) → QF V} : (∀ φ, RelExpr (F φ)) →
      RelExpr fun R => rel R fun φ => F φ R

/-- Every `RelExpr` is extensional: `⊢ :. ψ(x, y) . ≡_{x,y} . χ(x, y) : ⊃ : Ψ{x̂ŷψ(x, y)} . ≡ . Ψ{x̂ŷχ(x, y)}`,
    the claim of p. 213 for the expressions PM forms. As `clsExpr_ext`, with ✱21·11 for ✱20·11. -/
theorem relExpr_ext {Ψ : (V a → V b → QF V) → QF V} (hΨ : RelExpr Ψ) : RelExt S Ψ := by
  intro ψ χ
  induction hΨ with
  | const r => exact QThm.mp (QL.t4_2 r) (QL.t2_02 _ _)                          -- ✱4·2 . Simp
  | neg _ ih => exact qsyl ih (qiffMp (QL.t4_11 _ _))                            -- ✱4·11
  | or _ _ ih1 ih2 => exact qsyl (qcomp ih1 ih2) (QL.t4_39 _ _ _ _)              -- Comp . ✱4·39
  | all _ ih => exact qsyl (q10_11_21 ih) (q10_271 _ _)                          -- ✱10·11·21 . ✱10·271
  | @rel F _ ih =>
    exact qimpIffTrans (q21_11 ψ χ fun φ => F φ ψ)                               -- ✱21·11
      (qsyl (q10_11_21 fun φ => qsyl (ih φ) (qandCongrRImp _ _ _)) (q10_281 _ _))  -- ✱4·36 . ✱10·11·21·281

namespace RelExpr
/-- p . q (✱3·01). -/
theorem and {F G : (V a → V b → QF V) → QF V} (hF : RelExpr F) (hG : RelExpr G) :
    RelExpr fun R => QF.and (F R) (G R) := .neg (.or (.neg hF) (.neg hG))
/-- p ≡ q (✱4·01). -/
theorem iff {F G : (V a → V b → QF V) → QF V} (hF : RelExpr F) (hG : RelExpr G) :
    RelExpr fun R => QF.iff (F R) (G R) := and (.or (.neg hF) hG) (.or (.neg hG) hF)
/-- (∃x) . F(x, R) (✱10·01). -/
theorem ex {τ : Ty} {F : V τ → (V a → V b → QF V) → QF V} (h : ∀ x, RelExpr (F x)) :
    RelExpr fun R => QF.ex fun x => F x R := .neg (.all fun x => .neg (h x))
/-- xRy (✱21·02 with ✱21·01). -/
theorem relHolds (x : V a) (y : V b) : RelExpr fun R => QF.relHolds x R y := .rel fun _ => .const _
/-- φ!R (✱21·01 with context φ!χ!(x̂, ŷ)). -/
theorem relClsApp (φ : V (Ty.pred1 (Ty.pred2 a b))) : RelExpr fun R => QF.relClsApp φ R := .rel fun _ => .const _
/-- R ∈ κ, κ a class of relations (✱21·083 with ✱21·082). -/
theorem relClsMem (κ : (V a → V b → QF V) → QF V) : RelExpr fun R => R ∈ κ :=
  ex fun φ => and (.const _) (relClsApp φ)
/-- The defining expression of Rel, (∃φ) . R = x̂ŷφ!(x, y) (✱21·03). -/
theorem Rel : RelExpr (QF.Rel (V := V) (a := a) (b := b)) := ex fun _ => .rel fun _ => .const _
end RelExpr

/-- ✱21·7 for every relation expression ΨR that PM forms, without the premise: `⊢ : (∃g) : ΨR . ≡_R . g!R`
    (`qrelRed`, `relExpr_ext`). -/
theorem qrelExprRed [Reducibility S] {Ψ : (V a → V b → QF V) → QF V} (hΨ : RelExpr Ψ) :
    QThm S (ex (τ := Ty.pred1 (Ty.pred2 a b)) fun g => relAll fun R => iff (Ψ R) (relClsApp g R)) :=
  qrelRed Ψ (relExpr_ext hΨ)

/-- ✱20·3 for classes of relations, for every relation expression ΨR that PM forms, without the premise:
    `⊢ : R ∈ R̂(ΨR) . ≡ . ΨR`, R real (`qrelCls20_3`, `relExpr_ext`). -/
theorem qrelExpr20_3 [Reducibility S] {Ψ : (V a → V b → QF V) → QF V} (hΨ : RelExpr Ψ)
    (ψ : V a → V b → QF V) : QThm S (iff (ψ ∈ Ψ) (Ψ ψ)) :=
  qrelCls20_3 Ψ (relExpr_ext hΨ) ψ

/-! ✱21·4 again, from `qrelExpr20_3` and `RelExpr.Rel`, with no premise about Rel; not a PM proposition. -/
theorem check_star21_4_again [Reducibility S] (ψ : V a → V b → QF V) :
    QThm S (iff (ψ ∈ Rel) (ex (τ := Ty.pred2 a b) fun φ => relEq ψ (pf2 φ))) :=
  qrelExpr20_3 RelExpr.Rel ψ

/-! A check of the layers for relations of relations (docs/CLASSES_OF_CLASSES.md); not a PM proposition.
  P{R̂Ŝψ(R, S)}Q, unfolded one layer per line: ✱21·08, ✱21·081, ✱21·01 (twice, P first). -/
theorem check_relation_layers_unfolded {c d : Ty} (Ψ : (V a → V b → QF V) → (V c → V d → QF V) → QF V) (P : V a → V b → QF V)
    (Q : V c → V d → QF V) :
    QThm S (iff (relRelHolds P Ψ Q) (ex (τ := Ty.pred2 (Ty.pred2 a b) (Ty.pred2 c d)) fun φ =>
      QF.and (relAll fun R => relAll fun T => iff (Ψ R T) (relRelApp φ R T))
        (ex (τ := Ty.pred2 a b) fun χ => QF.and (fiff2 (pf2 χ) P)
          (ex (τ := Ty.pred2 c d) fun θ => QF.and (fiff2 (pf2 θ) Q) (.app2 φ χ θ))))) :=
  let H : V (Ty.pred2 (Ty.pred2 a b) (Ty.pred2 c d)) → QF V := fun φ =>
    relAll fun R => relAll fun T => iff (Ψ R T) (relRelApp φ R T)
  calc relRelHolds P Ψ Q
      ≡ ex (fun φ => QF.and (H φ) (relAppRel P φ Q)) := qrelRel1 Ψ _                -- (✱21·08)
    _ ≡ ex (fun φ => QF.and (H φ) (relRelApp φ P Q)) :=
        q10_11_281 fun φ => qandCongrR _ (qrelAppRel P φ Q)                      -- (✱21·081)
    _ ≡ ex (fun φ => QF.and (H φ) (ex fun χ => QF.and (fiff2 (pf2 χ) P)
          (ex fun θ => QF.and (fiff2 (pf2 θ) Q) (.app2 φ χ θ)))) :=
        q10_11_281 fun φ => qandCongrR _ (qrelRelApp φ P Q)                      -- (✱21·01)

end PM
