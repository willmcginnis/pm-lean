import PM.Star21
/-!
  ✱23: calculus of relations (1910 print, pp. 226–228; summary p. 226, definitions p. 226, numbered
  propositions pp. 226–228). The print has 79 numbered items, ✱23·01 to ✱23·95: seven definitions
  (✱23·01–✱23·05, ✱23·53, ✱23·71) and 72 propositions. All 72 are proved here.

  "The definitions and propositions of this number are to be exact analogues of those of ✱22. […] Proofs
  will be omitted in the present number, as they are precisely analogous to those of analogous
  propositions in ✱22" (p. 226). PM prints no proof, no Dem. and no hint in ✱23. So each proof here is
  the printed proof of the analogous proposition of ✱22 (pp. 220–225: its Dem. lines or its bracketed
  hint), with ✱21 for ✱20, propositions of ✱11 for those of ✱10 ("merely substituting […] propositions
  in ✱11 for propositions in ✱10", p. 212, where ✱21 says the same of ✱20), and ✱23 for ✱22. The
  comment on each Lean line gives ✱22's line or hint so translated. `data/star23_ledger.json` records,
  per proposition, ✱22's citations so translated (`cited_used`, `cited_unused`) and every further
  proposition the proof needs. Where ✱10 has no counterpart in ✱11 (✱10·251, ✱10·411, ✱10·413), the
  ✱10 proposition is used for two variables by its own proof, and the row says so. Statements are read
  from the Gutenberg #78050 transcription of the 1910 print (its formula source), not from the scan
  images, except at ✱23·02 (below).

  "In this number, as always in future, capital Latin letters stand for expressions of the form
  x̂ŷφ!(x, y), or, where they are not being used as apparent variables, for x̂ŷφ(x, y)" (p. 226). As in
  PM/Star21.lean, a real relation R is a formula with two holes `R : V a → V b → QF V` (of any order),
  xRy is `relHolds x R y` (✱21·02 with ✱21·01, the relation having the smallest scope), R = S is
  `relEq R S` (✱13·01 with ✱21·01, R the larger scope) and R ≠ S is ∼(R = S) (✱13·02); an apparent
  relation is `pf2 φ`, bound by ✱21·07 (`relAll`) or ✱21·071 (`relEx`). The system of rules is `S`, as in
  every PM theorem here (the `calc` notations of PM/Chain.lean name it), so PM's relation S is written
  `S'` in Lean statements; the docstrings keep PM's letters.

  The definitions are macros, each a relation (a formula with two holes) or a formula:
    ✱23·01  R ⪽ S . = : xRy . ⊃_{x,y} . xSy                Df   (`QF.relSubset`, `R ⪽ S`)
    ✱23·02  R ∩̇ S = x̂ŷ(xRy . xSy)                          Df   (`QF.relInter`, `R ∩̇ S`)
    ✱23·03  R ⊍ S = x̂ŷ(xRy . ∨ . xSy)                      Df   (`QF.relUnion`, `R ⊍ S`)
    ✱23·04  ∸R = x̂ŷ{∼(xRy)}                                Df   (`QF.relCompl`, `∸R`)
    ✱23·05  R ∸ S = R ∩̇ ∸S                                 Df   (`QF.relDiff`, `R ∸ S`)
    ✱23·53  R ∩̇ S ∩̇ T = (R ∩̇ S) ∩̇ T                         Df   (`QF.relInter3`)
    ✱23·71  R ⊍ S ⊍ T = (R ⊍ S) ⊍ T                         Df   (`QF.relUnion3`)
  ✱23·02 is read from the 1910 print: the Gutenberg transcription drops the R of "R ∩̇ S" (the text
  audit's Vol I list, entry 9, checked against the scan). The transcription writes the sign of ✱23·04
  as ∸ there and as a dotted minus from ✱23·392 on; they are one sign, read as ∸ throughout. At ✱23·81
  the transcription applies the published Errata (the audit says so and leaves it out of its list);
  the statement is the corrected one, which is the analogue of ✱22·81.

  An expression fR of a relation, in ✱23·94 and ✱23·95, is an extensional one (`RelExt`, PM/Star21.lean:
  "every proposition about a relation expresses an extensional property of the determining function",
  p. 213), so that ✱21·18, which the proofs use for it, holds for it: `qrel21_18` is ✱21·18 for such an
  expression, by ✱21·18's proof (✱21·11·15) with the premise for ✱21·11. A generic f{R} (`rel R f`) is
  extensional by ✱21·11 (`relExt_rel`), and every expression PM's notation forms by `relExpr_ext`; so the
  same step replaces R by S in R ⪽ T and T ⪽ R (✱23·54, ✱23·55). Where ✱22's proof uses ✱10·1 at a class
  such as −α, whose defining function need not be predicative, the step is the analogue for relations
  (`qrelAllAt`: ✱12·11 and ✱21·11), as in PM/Star21.lean. These are the choices of PM/Star22.lean for
  classes (`ClsExt`, `qcls20_18`, `clsExt_neg`, `clsExt_compl`), made for relations.

  ✱23·351 (∸R ≠ R) takes real variables x, y, as ✱10·25 does: ✱22·351's proof uses ✱10·251, which
  instantiates at a real variable, and in an empty domain ∸R and R would both be empty and equal.

  Steps done silently are those of PM/Star11.lean's header and of PM/Star14.lean's (chaining ⊃ and ≡
  lines under a hypothesis; the ledger lists the propositions that join them as `glue`). Where ✱22's
  proof leaves a step tacit that is not among these (reading x ∈ α ∩ β as x ∈ α . x ∈ β, which is
  ✱22·33, or α = β as x ∈ α ≡ₓ x ∈ β, which is ✱20·43), the ✱23 proposition that does it is used and
  listed as extra.

  Names: `q23_1` is ✱23·1, and so on. P, Q, R, S, T are relations (formulas with two holes), as in
  PM; f, F are expressions containing a relation.
-/
namespace PM
open QF

namespace QF
variable {V : Ty → Type}
/-- ✱23·01 `R ⪽ S . = : xRy . ⊃_{x,y} . xSy` Df -/
@[reducible] def relSubset {a b : Ty} (R S' : V a → V b → QF V) : QF V :=
  fimp2 (fun x y => relHolds x R y) (fun x y => relHolds x S' y)
/-- ✱23·02 `R ∩̇ S = x̂ŷ(xRy . xSy)` Df, as printed in 1910 (p. 226; the Gutenberg transcription drops
    the R of R ∩̇ S). -/
@[reducible] def relInter {a b : Ty} (R S' : V a → V b → QF V) : V a → V b → QF V :=
  fun x y => QF.and (relHolds x R y) (relHolds x S' y)
/-- ✱23·03 `R ⊍ S = x̂ŷ(xRy . ∨ . xSy)` Df -/
@[reducible] def relUnion {a b : Ty} (R S' : V a → V b → QF V) : V a → V b → QF V :=
  fun x y => .or (relHolds x R y) (relHolds x S' y)
/-- ✱23·04 `∸R = x̂ŷ{∼(xRy)}` Df -/
@[reducible] def relCompl {a b : Ty} (R : V a → V b → QF V) : V a → V b → QF V :=
  fun x y => .neg (relHolds x R y)
/-- ✱23·05 `R ∸ S = R ∩̇ ∸S` Df -/
@[reducible] def relDiff {a b : Ty} (R S' : V a → V b → QF V) : V a → V b → QF V :=
  relInter R (relCompl S')
/-- ✱23·53 `R ∩̇ S ∩̇ T = (R ∩̇ S) ∩̇ T` Df -/
@[reducible] def relInter3 {a b : Ty} (R S' T : V a → V b → QF V) : V a → V b → QF V :=
  relInter (relInter R S') T
/-- ✱23·71 `R ⊍ S ⊍ T = (R ⊍ S) ⊍ T` Df -/
@[reducible] def relUnion3 {a b : Ty} (R S' T : V a → V b → QF V) : V a → V b → QF V :=
  relUnion (relUnion R S') T
end QF

/-! PM's signs for the definitions (scoped to `PM`). Each unfolds to the macro it names, so a statement
    written with them is the same Lean statement. -/
/-- `R ⪽ S`: `relSubset R S` (✱23·01). -/
scoped infix:50 " ⪽ " => QF.relSubset
/-- `R ∩̇ S`: `relInter R S` (✱23·02). -/
scoped infixl:70 " ∩̇ " => QF.relInter
/-- `R ⊍ S`: `relUnion R S` (✱23·03). -/
scoped infixl:65 " ⊍ " => QF.relUnion
/-- `∸R`: `relCompl R` (✱23·04). -/
scoped prefix:max "∸" => QF.relCompl
/-- `R ∸ S`: `relDiff R S` (✱23·05). -/
scoped infixl:65 " ∸ " => QF.relDiff

variable {V : Ty → Type} {S : Sys} {a b : Ty}

/-! ## Steps used by several proofs, each listed in the ledger where used -/

/-- PM's "(1) . ✱10·11 . ✱20·43" for relations: from `⊢ : xRy . ≡ . xTy` for all x, y, `⊢ . R = T`
    (✱11·11, ✱21·43). -/
theorem qrelEqI [Reducibility S] {R T : V a → V b → QF V}
    (h : ∀ x y, QThm S (iff (relHolds x R y) (relHolds x T y))) : QThm S (relEq R T) :=
  QThm.mp (q11_11 h) (qiffMpr (q21_43 R T))

/-- Members of a product replaced by equivalents: from `⊢ . A ≡ A'` and `⊢ . B ≡ B'`, `⊢ : A . B . ≡ .
    A' . B'` (✱4·38, the hypotheses joined by ✱3·2). -/
theorem qandIffCongr {A A' B B' : QF V} (h1 : QThm S (iff A A')) (h2 : QThm S (iff B B')) :
    QThm S (iff (QF.and A B) (QF.and A' B')) :=
  QThm.mp (qandI h1 h2) (QL.t4_38 _ _ _ _)

/-- Members of a sum replaced by equivalents: `⊢ : A ∨ B . ≡ . A' ∨ B'` (✱4·39, ✱3·2). -/
theorem qorIffCongr {A A' B B' : QF V} (h1 : QThm S (iff A A')) (h2 : QThm S (iff B B')) :
    QThm S (iff (.or A B) (.or A' B')) :=
  QThm.mp (qandI h1 h2) (QL.t4_39 _ _ _ _)

/-- Both members of `⊃_{x,y}` replaced by equivalents under (x, y): `A ⊃_{x,y} B . ≡ . A' ⊃_{x,y} B'`
    (✱4·84, ✱4·85, ✱11·11·33): ✱10·413 for two variables. -/
theorem qfimp2Congr {A A' B B' : V a → V b → QF V} (h1 : ∀ x y, QThm S (iff (A x y) (A' x y)))
    (h2 : ∀ x y, QThm S (iff (B x y) (B' x y))) : QThm S (iff (fimp2 A B) (fimp2 A' B')) :=
  QThm.mp (q11_11 fun x y => qimpIffCongr (h1 x y) (h2 x y)) (q11_33 _ _)

/-- Both members of `≡_{x,y}` replaced by equivalents under (x, y): `A ≡_{x,y} B . ≡ . A' ≡_{x,y} B'`
    (✱4·86 for each member, ✱11·11·33): ✱10·414 for two variables. -/
theorem qfiff2Congr {A A' B B' : V a → V b → QF V} (h1 : ∀ x y, QThm S (iff (A x y) (A' x y)))
    (h2 : ∀ x y, QThm S (iff (B x y) (B' x y))) : QThm S (iff (fiff2 A B) (fiff2 A' B')) :=
  QThm.mp (q11_11 fun x y => qiffIffCongr (h1 x y) (h2 x y)) (q11_33 _ _)

/-- ✱21·18 for an extensional expression ΨR (`RelExt`, p. 213): `⊢ :. R = S . ⊃ : ΨR . ≡ . ΨS`, by ✱21·18's
    proof (✱21·11·15), with Ψ's extensionality (✱21·11 for Ψ) for ✱21·11. As `qcls20_18` (PM/Star22.lean). -/
theorem qrel21_18 [Reducibility S] (Ψ : (V a → V b → QF V) → QF V) (hΨ : RelExt S Ψ) (R T : V a → V b → QF V) :
    QThm S (imp (relEq R T) (iff (Ψ R) (Ψ T))) :=
  qsyl (qiffMpr (q21_15 R T)) (hΨ R T)

/-- ∼ΨR is extensional when ΨR is (✱4·11). -/
theorem relExt_neg {Ψ : (V a → V b → QF V) → QF V} (hΨ : RelExt S Ψ) : RelExt S fun R => .neg (Ψ R) :=
  fun ψ χ => qsyl (hΨ ψ χ) (qiffMp (QL.t4_11 _ _))

/-- Ψ(∸R) is extensional when ΨR is: from ψ(x, y) ≡_{x,y} χ(x, y), x ∸x̂ŷψ(x, y) y . ≡_{x,y} . x ∸x̂ŷχ(x, y) y
    as defining functions, i.e. ∼{x(x̂ŷψ(x, y))y} ≡_{x,y} ∼{x(x̂ŷχ(x, y))y}, by ✱21·11 (context of xRy) and ✱4·11,
    under (x, y) by ✱10·11·21. -/
theorem relExt_compl {Ψ : (V a → V b → QF V) → QF V} (hΨ : RelExt S Ψ) : RelExt S fun R => Ψ (∸R) :=
  fun ψ χ => qsyl (q10_11_21 fun x => q10_11_21 fun y =>
      qsyl (q21_11 ψ χ fun φ => .app2 φ x y) (qiffMp (QL.t4_11 _ _)))
    (hΨ (∸ψ) (∸χ))

namespace RelExpr
/-- R ⪽ T as an expression of R (✱23·01). -/
theorem relSubset_left (T : V a → V b → QF V) : RelExpr fun R => R ⪽ T :=
  .all fun x => .all fun y => .or (.neg (relHolds x y)) (.const _)
/-- T ⪽ R as an expression of R (✱23·01). -/
theorem relSubset_right (T : V a → V b → QF V) : RelExpr fun R => T ⪽ R :=
  .all fun x => .all fun y => .or (.neg (.const _)) (relHolds x y)
end RelExpr

/-! ## ✱23·1–✱23·39 -/

/-- ✱23·1 `⊢ :. R ⪽ S . ≡ : xRy . ⊃_{x,y} . xSy` [as ✱22·1: ✱4·2 . (✱23·01)] -/
theorem q23_1 (R S' : V a → V b → QF V) :
    QThm S (iff (R ⪽ S') (fimp2 (fun x y => relHolds x R y) (fun x y => relHolds x S' y))) :=
  QL.t4_2 _                                                                       -- ✱4·2 . (✱23·01)

/-- ✱23·2 `⊢ . R ∩̇ S = x̂ŷ(xRy . xSy)` [as ✱22·2: ✱21·2 . (✱23·02)] -/
theorem q23_2 [Reducibility S] (R S' : V a → V b → QF V) :
    QThm S (relEq (R ∩̇ S') fun x y => QF.and (relHolds x R y) (relHolds x S' y)) :=
  q21_2 _                                                                         -- ✱21·2 . (✱23·02)

/-- ✱23·3 `⊢ . R ⊍ S = x̂ŷ(xRy . ∨ . xSy)` [as ✱22·3: ✱21·2 . (✱23·03)] -/
theorem q23_3 [Reducibility S] (R S' : V a → V b → QF V) :
    QThm S (relEq (R ⊍ S') fun x y => .or (relHolds x R y) (relHolds x S' y)) :=
  q21_2 _                                                                         -- ✱21·2 . (✱23·03)

/-- ✱23·31 `⊢ . ∸R = x̂ŷ{∼(xRy)}` [as ✱22·31: ✱21·2 . (✱23·04)] -/
theorem q23_31 [Reducibility S] (R : V a → V b → QF V) :
    QThm S (relEq (∸R) fun x y => .neg (relHolds x R y)) :=
  q21_2 _                                                                         -- ✱21·2 . (✱23·04)

/-- ✱23·32 `⊢ . R ∸ S = x̂ŷ{xRy . ∼(xSy)}` [as ✱22·32: ✱21·2 . (✱23·05) . ✱23·2 . ✱21·32]. By (✱23·05),
    R ∸ S is R ∩̇ ∸S (a macro: the same relation), and ✱23·2 gives R ∩̇ ∸S = x̂ŷ{xRy . x(∸S)y}. The step from
    x(∸S)y to ∼(xSy) inside the product, which PM takes by ✱21·32 (✱20·32), is taken by ✱21·32's proof:
    ✱21·3 (with ✱4·36's form for the second factor, `qandCongrR`) under (x, y) by ✱11·11, and ✱21·15. The
    two identities are joined by ✱21·22. -/
theorem q23_32 [Reducibility S] (R S' : V a → V b → QF V) :
    QThm S (relEq (R ∸ S') fun x y => QF.and (relHolds x R y) (.neg (relHolds x S' y))) :=
  have h1 := q23_2 R (∸S')                                                         -- (✱23·05) . ✱23·2
  have h2 := QThm.mp (q11_11 fun x y => qandCongrR (relHolds x R y) (q21_3 (∸S') x y))  -- ✱21·32
    (qiffMp (q21_15 _ (fun x y => QF.and (relHolds x R y) (.neg (relHolds x S' y)))))
  QThm.mp (qandI h1 h2) (q21_22 _ _ _)

/-- ✱23·33 `⊢ : x(R ∩̇ S)y . ≡ . xRy . xSy` [as ✱22·33: ✱21·3 . ✱23·2]. By (✱23·02), ✱23·2 is ✱21·2, and
    ✱21·3 is used at the relation x̂ŷ(xRy . xSy) itself. -/
theorem q23_33 [Reducibility S] (R S' : V a → V b → QF V) (x : V a) (y : V b) :
    QThm S (iff (relHolds x (R ∩̇ S') y) (QF.and (relHolds x R y) (relHolds x S' y))) :=
  q21_3 (R ∩̇ S') x y                                                               -- ✱21·3 . ✱23·2

/-- ✱23·34 `⊢ :. x(R ⊍ S)y . ≡ : xRy . ∨ . xSy` [as ✱22·34: ✱21·3 . ✱23·3] -/
theorem q23_34 [Reducibility S] (R S' : V a → V b → QF V) (x : V a) (y : V b) :
    QThm S (iff (relHolds x (R ⊍ S') y) (.or (relHolds x R y) (relHolds x S' y))) :=
  q21_3 (R ⊍ S') x y                                                               -- ✱21·3 . ✱23·3

/-- ✱23·35 `⊢ : x ∸R y . ≡ . ∼(xRy)` [as ✱22·35: ✱21·3 . ✱23·31] -/
theorem q23_35 [Reducibility S] (R : V a → V b → QF V) (x : V a) (y : V b) :
    QThm S (iff (relHolds x (∸R) y) (.neg (relHolds x R y))) :=
  q21_3 (∸R) x y                                                                  -- ✱21·3 . ✱23·31

/-- ✱10·251 for two variables, by its proof (✱10·25 . Transp) with ✱11·1 for ✱10·1:
    `⊢ : (x, y) . ∼φ(x, y) . ⊃ . ∼{(x, y) . φ(x, y)}`, at real variables x, y. ✱11·1 at (x, y) for both,
    and Transp (✱2·16). -/
theorem qall2_251 {σ τ : Ty} (φ : V σ → V τ → QF V) (x : V σ) (y : V τ) :
    QThm S (imp (all2 fun x y => .neg (φ x y)) (.neg (all2 φ))) :=
  qsyl (q11_1 (fun x y => .neg (φ x y)) x y) (QThm.mp (q11_1 φ x y) (QL.t2_16 _ _))

/-- ✱23·351 `⊢ . ∸R ≠ R`, at real variables x, y (✱10·25). As ✱22·351:
    `✱23·35 . ✱5·19 . ⊃ ⊢ : ∼{x ∸R y . ≡ . xRy}`: ✱5·19 is ∼{xRy . ≡ . ∼(xRy)}, and by ✱23·35 the first
    member is replaced (✱4·86, as `qiffLeft`) and the members commuted (✱4·21), then Transp (✱2·16);
    `[✱10·11]` (for two variables ✱11·11); `[✱10·251]` (for two variables, `qall2_251`);
    `[✱20·43 . Transp]` is ✱21·43 with Transp (✱2·16). -/
theorem q23_351 [Reducibility S] (R : V a → V b → QF V) (x : V a) (y : V b) :
    QThm S (.neg (relEq (∸R) R)) :=
  have h1 : ∀ x y, QThm S (.neg (iff (relHolds x (∸R) y) (relHolds x R y))) := fun x y =>
    QThm.mp (QL.t5_19 (relHolds x R y))
      (QThm.mp (qsyl (qiffLeft (qiffSymm (q23_35 R x y))) (qiffMp (QL.t4_21 _ _)))
        (QL.t2_16 _ _))                                                           -- ✱23·35 . ✱5·19
  have h2 := QThm.mp (q11_11 h1) (qall2_251 _ x y)                                -- [✱10·11] [✱10·251]
  QThm.mp h2 (QThm.mp (qiffMp (q21_43 (∸R) R)) (QL.t2_16 _ _))                    -- [✱20·43 . Transp]

/-- ✱23·36 `⊢ . R ∩̇ S ∈ Rel` [as ✱22·36: ✱21·41] -/
theorem q23_36 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (R ∩̇ S' ∈ Rel) :=
  q21_41 _                                                                        -- ✱21·41

/-- ✱23·37 `⊢ . R ⊍ S ∈ Rel` [as ✱22·37: ✱21·41] -/
theorem q23_37 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (R ⊍ S' ∈ Rel) :=
  q21_41 _                                                                        -- ✱21·41

/-- ✱23·38 `⊢ . ∸R ∈ Rel` [as ✱22·38: ✱21·41] -/
theorem q23_38 [Reducibility S] (R : V a → V b → QF V) : QThm S (∸R ∈ Rel) :=
  q21_41 _                                                                        -- ✱21·41

/-- ✱23·39 `⊢ . x̂ŷφ(x, y) ∩̇ x̂ŷψ(x, y) = x̂ŷ{φ(x, y) . ψ(x, y)}`. As ✱22·39:
    `✱23·33 . ⊃ ⊢ : x{x̂ŷφ(x, y) ∩̇ x̂ŷψ(x, y)}y . ≡ . x{x̂ŷφ(x, y)}y . x{x̂ŷψ(x, y)}y .`
    `[✱21·3] ≡ . φ(x, y) . ψ(x, y)` (1), both factors at once (✱4·38); `(1) . ✱21·33 . ⊃ ⊢ . Prop`, with (1)
    generalized over (x, y) by ✱11·11. -/
theorem q23_39 [Reducibility S] (φ ψ : V a → V b → QF V) :
    QThm S (relEq (φ ∩̇ ψ) fun x y => QF.and (φ x y) (ψ x y)) :=
  have h1 : ∀ x y, QThm S (iff (relHolds x (φ ∩̇ ψ) y) (QF.and (φ x y) (ψ x y))) := fun x y =>
    calc relHolds x (φ ∩̇ ψ) y
        ≡ QF.and (relHolds x φ y) (relHolds x ψ y) := q23_33 φ ψ x y              -- ✱23·33
      _ ≡ QF.and (φ x y) (ψ x y) := qandIffCongr (q21_3 φ x y) (q21_3 ψ x y)       -- [✱21·3] (1)
  QThm.mp (q11_11 h1) (qiffMpr (q21_33 _ _))                                      -- (1) . ✱21·33

/-- ✱23·391 `⊢ . x̂ŷφ(x, y) ⊍ x̂ŷψ(x, y) = x̂ŷ{φ(x, y) . ∨ . ψ(x, y)}` [as ✱22·391: Similar proof]: ✱23·34,
    ✱21·3 for both disjuncts (✱4·39), ✱11·11, ✱21·33. -/
theorem q23_391 [Reducibility S] (φ ψ : V a → V b → QF V) :
    QThm S (relEq (φ ⊍ ψ) fun x y => .or (φ x y) (ψ x y)) :=
  have h1 : ∀ x y, QThm S (iff (relHolds x (φ ⊍ ψ) y) (.or (φ x y) (ψ x y))) := fun x y =>
    calc relHolds x (φ ⊍ ψ) y
        ≡ .or (relHolds x φ y) (relHolds x ψ y) := q23_34 φ ψ x y                  -- ✱23·34
      _ ≡ .or (φ x y) (ψ x y) := qorIffCongr (q21_3 φ x y) (q21_3 ψ x y)           -- [✱21·3] (1)
  QThm.mp (q11_11 h1) (qiffMpr (q21_33 _ _))                                      -- (1) . ✱21·33

/-- ✱23·392 `⊢ . ∸x̂ŷφ(x, y) = x̂ŷ{∼φ(x, y)}` [as ✱22·392: Similar proof]: ✱23·35, ✱21·3 under ∼ (✱4·11),
    ✱11·11, ✱21·33. -/
theorem q23_392 [Reducibility S] (φ : V a → V b → QF V) :
    QThm S (relEq (∸φ) fun x y => .neg (φ x y)) :=
  have h1 : ∀ x y, QThm S (iff (relHolds x (∸φ) y) (.neg (φ x y))) := fun x y =>
    calc relHolds x (∸φ) y
        ≡ .neg (relHolds x φ y) := q23_35 φ x y                                     -- ✱23·35
      _ ≡ .neg (φ x y) := qiffNeg (q21_3 φ x y)                                    -- [✱21·3] (1)
  QThm.mp (q11_11 h1) (qiffMpr (q21_33 _ _))                                      -- (1) . ✱21·33

/-! ## ✱23·4–✱23·52 -/

/-- ✱23·4 `⊢ :. R ⪽ S . S ⪽ R . ≡ : xRy . ≡_{x,y} . xSy`. As ✱22·4: `✱23·1 . ⊃ ⊢ :: R ⪽ S . ≡ : xRy .
    ⊃_{x,y} . xSy :. S ⪽ R . ≡ : xSy . ⊃_{x,y} . xRy :.`; `[✱4·38]` joins them; `[✱10·22]` is ✱11·31. R ⪽ S is
    its definiens (✱23·01, a macro), so the ✱23·1 and ✱4·38 lines are the definition. -/
theorem q23_4 (R S' : V a → V b → QF V) :
    QThm S (iff (QF.and (R ⪽ S') (S' ⪽ R)) (fiff2 (fun x y => relHolds x R y) (fun x y => relHolds x S' y))) :=
  q11_31 _ _                                                                      -- [✱10·22]

/-- ✱23·41 `⊢ : R ⪽ S . S ⪽ R . ≡ . R = S` [as ✱22·41: ✱23·4 . ✱21·43] -/
theorem q23_41 [Reducibility S] (R S' : V a → V b → QF V) :
    QThm S (iff (QF.and (R ⪽ S') (S' ⪽ R)) (relEq R S')) :=
  qiffTrans (q23_4 R S') (qiffSymm (q21_43 R S'))                                   -- ✱23·4 . ✱21·43

/-- ✱23·42 `⊢ . R ⪽ R` [as ✱22·42: Id . ✱11·11] -/
theorem q23_42 (R : V a → V b → QF V) : QThm S (R ⪽ R) :=
  q11_11 fun _ _ => QL.t2_08 _                                                    -- Id . ✱11·11

/-- ✱23·43 `⊢ . R ∩̇ S ⪽ R` [as ✱22·43: ✱3·26 . ✱11·11]. x(R ∩̇ S)y is read as xRy . xSy by ✱23·33. -/
theorem q23_43 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (R ∩̇ S' ⪽ R) :=
  q11_11 fun x y => qsyl (qiffMp (q23_33 R S' x y)) (QL.t3_26 _ _)                  -- ✱3·26 . ✱11·11

/-- ✱23·44 `⊢ : R ⪽ S . S ⪽ T . ⊃ . R ⪽ T` [as ✱22·44: ✱10·3, which is ✱11·37 for two variables] -/
theorem q23_44 (R S' T : V a → V b → QF V) : QThm S (imp (QF.and (R ⪽ S') (S' ⪽ T)) (R ⪽ T)) :=
  q11_37 _ _ _                                                                    -- ✱10·3

/-- ✱23·441 `⊢ : R ⪽ S . xRy . ⊃ . xSy` [as ✱22·441: ✱10·1 . Imp]; ✱10·1 is ✱11·1 for two variables, Imp
    is ✱3·31. -/
theorem q23_441 (R S' : V a → V b → QF V) (x : V a) (y : V b) :
    QThm S (imp (QF.and (R ⪽ S') (relHolds x R y)) (relHolds x S' y)) :=
  QThm.mp (q11_1 (fun x y => imp (relHolds x R y) (relHolds x S' y)) x y)
    (QL.t3_31 _ _ _)                                                              -- ✱10·1 . Imp

/-- ✱23·45 `⊢ : R ⪽ S . R ⪽ T . ≡ . R ⪽ S ∩̇ T`. As ✱22·45: `✱23·1` (the definition); `[✱10·29]` is
    ✱11·391; `[✱22·33 . ✱10·413]`: ✱23·33 replaces the consequent under (x, y), which is ✱10·413 for two
    variables with the antecedent unchanged: ✱4·85 under (x, y) (✱11·11·33). -/
theorem q23_45 [Reducibility S] (R S' T : V a → V b → QF V) :
    QThm S (iff (QF.and (R ⪽ S') (R ⪽ T)) (R ⪽ S' ∩̇ T)) :=
  calc QF.and (R ⪽ S') (R ⪽ T)
      ≡ fimp2 (fun x y => relHolds x R y) (fun x y => QF.and (relHolds x S' y) (relHolds x T y)) :=
        q11_391 _ _ _                                                             -- [✱10·29]
    _ ≡ (R ⪽ S' ∩̇ T) :=
        QThm.mp (q11_11 fun x y => QThm.mp (qiffSymm (q23_33 S' T x y)) (QL.t4_85 _ _ _))
          (q11_33 _ _)                                                            -- [✱23·33 . ✱10·413]

/-- ✱23·46 `⊢ : xRy . R ⪽ S . ⊃ . xSy` [as ✱22·46: ✱23·441 . Perm]; Perm, for the factors of a product, is
    ✱3·22. -/
theorem q23_46 (R S' : V a → V b → QF V) (x : V a) (y : V b) :
    QThm S (imp (QF.and (relHolds x R y) (R ⪽ S')) (relHolds x S' y)) :=
  qsyl (QL.t3_22 _ _) (q23_441 R S' x y)                                           -- ✱23·441 . Perm

/-- ✱23·47 `⊢ : R ⪽ T . ⊃ . R ∩̇ S ⪽ T` [as ✱22·47: ✱23·43·44]: ✱23·43 is the first factor of ✱23·44's
    hypothesis (✱3·2). -/
theorem q23_47 [Reducibility S] (R S' T : V a → V b → QF V) : QThm S (imp (R ⪽ T) (R ∩̇ S' ⪽ T)) :=
  qsyl (QThm.mp (q23_43 R S') (QL.t3_2 _ _)) (q23_44 (R ∩̇ S') R T)                   -- ✱23·43·44

/-- ✱23·48 `⊢ : R ⪽ S . ⊃ . R ∩̇ T ⪽ S ∩̇ T` [as ✱22·48: ✱10·31, which is ✱11·38 for two variables]. x(R ∩̇ T)y
    and x(S ∩̇ T)y are read as products by ✱23·33, under (x, y) (✱10·413 for two variables). -/
theorem q23_48 [Reducibility S] (R S' T : V a → V b → QF V) :
    QThm S (imp (R ⪽ S') (R ∩̇ T ⪽ S' ∩̇ T)) :=
  qsyl (q11_38 _ _ _)                                                             -- ✱10·31
    (qiffMp (qfimp2Congr (fun x y => qiffSymm (q23_33 R T x y)) fun x y => qiffSymm (q23_33 S' T x y)))

/-- ✱23·481 `⊢ : R = S . ⊃ . R ∩̇ T = S ∩̇ T`. As ✱22·481: `✱23·41 . ⊃ :. Hp . ⊃ : R ⪽ S . S ⪽ R :`
    `[✱23·48] ⊃ : R ∩̇ T ⪽ S ∩̇ T . S ∩̇ T ⪽ R ∩̇ T :` (✱23·48 for each factor, ✱3·47) `[✱23·41] ⊃ : R ∩̇ T = S ∩̇ T`. -/
theorem q23_481 [Reducibility S] (R S' T : V a → V b → QF V) :
    QThm S (imp (relEq R S') (relEq (R ∩̇ T) (S' ∩̇ T))) :=
  calc relEq R S'
      ⊃ QF.and (R ⪽ S') (S' ⪽ R) := qiffMpr (q23_41 R S')                             -- ✱23·41
    _ ⊃ QF.and (R ∩̇ T ⪽ S' ∩̇ T) (S' ∩̇ T ⪽ R ∩̇ T) :=
        QThm.mp (qandI (q23_48 R S' T) (q23_48 S' R T)) (QL.t3_47 _ _ _ _)           -- [✱23·48]
    _ ⊃ relEq (R ∩̇ T) (S' ∩̇ T) := qiffMp (q23_41 _ _)                              -- [✱23·41]

/-- ✱23·49 `⊢ : P ⪽ Q . R ⪽ S . ⊃ . P ∩̇ R ⪽ Q ∩̇ S` [as ✱22·49: ✱10·39, which is ✱11·39 for two variables].
    The products are read by ✱23·33 under (x, y), as in ✱23·48. -/
theorem q23_49 [Reducibility S] (P Q R S' : V a → V b → QF V) :
    QThm S (imp (QF.and (P ⪽ Q) (R ⪽ S')) (P ∩̇ R ⪽ Q ∩̇ S')) :=
  qsyl (q11_39 _ _ _ _)                                                           -- ✱10·39
    (qiffMp (qfimp2Congr (fun x y => qiffSymm (q23_33 P R x y)) fun x y => qiffSymm (q23_33 Q S' x y)))

/-- ✱23·5 `⊢ . R ∩̇ R = R`. As ✱22·5: `✱23·33 . ⊃ ⊢ :. x(R ∩̇ R)y . ≡ : xRy . xRy :` `[✱4·24] ≡ : xRy` (1);
    `(1) . ✱11·11 . ✱21·43 . ⊃ ⊢ . Prop` (`qrelEqI`). -/
theorem q23_5 [Reducibility S] (R : V a → V b → QF V) : QThm S (relEq (R ∩̇ R) R) :=
  qrelEqI fun x y =>                                                              -- (1) . ✱11·11 . ✱21·43
    calc relHolds x (R ∩̇ R) y
        ≡ QF.and (relHolds x R y) (relHolds x R y) := q23_33 R R x y               -- ✱23·33
      _ ≡ relHolds x R y := qiffSymm (QL.t4_24 _)                                  -- [✱4·24] (1)

/-- ✱23·51 `⊢ . R ∩̇ S = S ∩̇ R` [as ✱22·51: ✱23·33 . ✱4·3 . ✱11·11 . ✱21·43] -/
theorem q23_51 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (relEq (R ∩̇ S') (S' ∩̇ R)) :=
  qrelEqI fun x y =>                                                              -- ✱11·11 . ✱21·43
    calc relHolds x (R ∩̇ S') y
        ≡ QF.and (relHolds x R y) (relHolds x S' y) := q23_33 R S' x y               -- ✱23·33
      _ ≡ QF.and (relHolds x S' y) (relHolds x R y) := QL.t4_3 _ _                  -- ✱4·3
      _ ≡ relHolds x (S' ∩̇ R) y := qiffSymm (q23_33 S' R x y)                         -- ✱23·33

/-- ✱23·52 `⊢ . (R ∩̇ S) ∩̇ T = R ∩̇ (S ∩̇ T)` [as ✱22·52: ✱23·33 . ✱4·32 . ✱11·11 . ✱21·43]. ✱23·33 is used for
    the inner product inside the outer one (✱4·36 and its form for the second factor, `qandCongrL`,
    `qandCongrR`). -/
theorem q23_52 [Reducibility S] (R S' T : V a → V b → QF V) :
    QThm S (relEq ((R ∩̇ S') ∩̇ T) (R ∩̇ (S' ∩̇ T))) :=
  qrelEqI fun x y =>                                                              -- ✱11·11 . ✱21·43
    calc relHolds x ((R ∩̇ S') ∩̇ T) y
        ≡ QF.and (relHolds x (R ∩̇ S') y) (relHolds x T y) := q23_33 _ T x y           -- ✱23·33
      _ ≡ QF.and (QF.and (relHolds x R y) (relHolds x S' y)) (relHolds x T y) :=
          qandCongrL _ (q23_33 R S' x y)                                           -- ✱23·33
      _ ≡ QF.and (relHolds x R y) (QF.and (relHolds x S' y) (relHolds x T y)) := QL.t4_32 _ _ _  -- ✱4·32
      _ ≡ QF.and (relHolds x R y) (relHolds x (S' ∩̇ T) y) :=
          qandCongrR _ (qiffSymm (q23_33 S' T x y))                                -- ✱23·33
      _ ≡ relHolds x (R ∩̇ (S' ∩̇ T)) y := qiffSymm (q23_33 R _ x y)                   -- ✱23·33

/-! ## ✱23·54–✱23·74 -/

/-- ✱23·54 `⊢ :. R = S . ⊃ : R ⪽ T . ≡ . S ⪽ T` [as ✱22·54: ✱21·18], ✱21·18 for the expression R ⪽ T
    (`qrel21_18`, `relExpr_ext`). -/
theorem q23_54 [Reducibility S] (R S' T : V a → V b → QF V) :
    QThm S (imp (relEq R S') (iff (R ⪽ T) (S' ⪽ T))) :=
  qrel21_18 _ (relExpr_ext (RelExpr.relSubset_left T)) R S'                       -- ✱21·18

/-- ✱23·55 `⊢ :. R = S . ⊃ : T ⪽ R . ≡ . T ⪽ S` [as ✱22·55: ✱21·18], for the expression T ⪽ R. -/
theorem q23_55 [Reducibility S] (R S' T : V a → V b → QF V) :
    QThm S (imp (relEq R S') (iff (T ⪽ R) (T ⪽ S'))) :=
  qrel21_18 _ (relExpr_ext (RelExpr.relSubset_right T)) R S'                      -- ✱21·18

/-- ✱23·551 `⊢ : R = S . ⊃ . R ⊍ T = S ⊍ T` [as ✱22·551: ✱10·411]. R = S is read by ✱21·43 (both ways),
    and x(R ⊍ T)y, x(S ⊍ T)y by ✱23·34. ✱10·411 for two variables with the second disjunct unchanged is
    ✱4·37 under (x, y): ✱11·11 and ✱11·32. -/
theorem q23_551 [Reducibility S] (R S' T : V a → V b → QF V) :
    QThm S (imp (relEq R S') (relEq (R ⊍ T) (S' ⊍ T))) :=
  calc relEq R S'
      ⊃ fiff2 (fun x y => relHolds x R y) (fun x y => relHolds x S' y) := qiffMp (q21_43 R S')  -- ✱21·43
    _ ⊃ fiff2 (fun x y => .or (relHolds x R y) (relHolds x T y))
          (fun x y => .or (relHolds x S' y) (relHolds x T y)) :=
        QThm.mp (q11_11 fun _ _ => QL.t4_37 _ _ _) (q11_32 _ _)                   -- ✱10·411
    _ ⊃ fiff2 (fun x y => relHolds x (R ⊍ T) y) (fun x y => relHolds x (S' ⊍ T) y) :=
        qiffMp (qfiff2Congr (fun x y => qiffSymm (q23_34 R T x y)) fun x y => qiffSymm (q23_34 S' T x y))
    _ ⊃ relEq (R ⊍ T) (S' ⊍ T) := qiffMpr (q21_43 _ _)                              -- ✱21·43

/-- ✱23·56 `⊢ . R ⊍ R = R` [as ✱22·56: ✱4·25 . ✱11·11], with ✱23·34 and ✱21·43 as in ✱23·5. -/
theorem q23_56 [Reducibility S] (R : V a → V b → QF V) : QThm S (relEq (R ⊍ R) R) :=
  qrelEqI fun x y =>                                                              -- ✱11·11
    qiffTrans (q23_34 R R x y) (qiffSymm (QL.t4_25 _))                            -- ✱4·25

/-- ✱23·57 `⊢ . R ⊍ S = S ⊍ R` [as ✱22·57: ✱4·31 . ✱11·11], with ✱23·34 and ✱21·43. -/
theorem q23_57 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (relEq (R ⊍ S') (S' ⊍ R)) :=
  qrelEqI fun x y =>                                                              -- ✱11·11
    qiffTrans (q23_34 R S' x y) (qiffTrans (QL.t4_31 _ _) (qiffSymm (q23_34 S' R x y)))  -- ✱4·31

/-- ✱23·58 `⊢ . R ⪽ R ⊍ S . S ⪽ R ⊍ S` [as ✱22·58: ✱1·3 . ✱2·2], each under (x, y) by ✱11·11, with ✱23·34. -/
theorem q23_58 [Reducibility S] (R S' : V a → V b → QF V) :
    QThm S (QF.and (R ⪽ R ⊍ S') (S' ⪽ R ⊍ S')) :=
  qandI (q11_11 fun x y => qsyl (QL.t2_2 _ _) (qiffMpr (q23_34 R S' x y)))          -- ✱2·2
    (q11_11 fun x y => qsyl (QThm.add _ _) (qiffMpr (q23_34 R S' x y)))             -- ✱1·3

/-- ✱23·59 `⊢ : R ⪽ T . S ⪽ T . ≡ . R ⊍ S ⪽ T`. As ✱22·59: `✱23·1` (the definition); `[✱10·22]` is ✱11·31;
    `[✱4·77 . ✱10·271]`, ✱10·271 for two variables being ✱11·33 (with ✱11·11); `[✱23·34 . ✱10·413]`:
    ✱10·413 for two variables with the consequent unchanged is ✱4·84 under (x, y) (✱11·11·33). -/
theorem q23_59 [Reducibility S] (R S' T : V a → V b → QF V) :
    QThm S (iff (QF.and (R ⪽ T) (S' ⪽ T)) (R ⊍ S' ⪽ T)) :=
  calc QF.and (R ⪽ T) (S' ⪽ T)
      ≡ all2 (fun x y => QF.and (imp (relHolds x R y) (relHolds x T y))
          (imp (relHolds x S' y) (relHolds x T y))) := q11_31 _ _                  -- [✱10·22]
    _ ≡ fimp2 (fun x y => .or (relHolds x R y) (relHolds x S' y)) (fun x y => relHolds x T y) :=
        QThm.mp (q11_11 fun _ _ => QL.t4_77 _ _ _) (q11_33 _ _)                   -- [✱4·77 . ✱10·271]
    _ ≡ (R ⊍ S' ⪽ T) :=
        QThm.mp (q11_11 fun x y => QThm.mp (qiffSymm (q23_34 R S' x y)) (QL.t4_84 _ _ _))
          (q11_33 _ _)                                                            -- [✱23·34 . ✱10·413]

/-- ✱23·6 `⊢ :. x(R ⊍ S)y . ≡ : R ⪽ T . S ⪽ T . ⊃_T . xTy`, T apparent. As ✱22·6:
    `✱23·59 . ⊃ ⊢ :. R ⪽ T . S ⪽ T . ⊃ : x(R ⊍ S)y . ⊃ . xTy` (✱23·59 read as ⊃, then ✱11·1 at (x, y));
    `[Comm]` (✱2·04); `[✱10·11·21]` (1); `✱10·1 . ⊃ ⊢ :. R ⪽ T . S ⪽ T . ⊃_T . xTy : ⊃ : R ⪽ R ⊍ S .
    S ⪽ R ⊍ S . ⊃ . x(R ⊍ S)y :` — ✱10·1 at R ⊍ S, whose defining function need not be predicative, is
    the analogue for relations (`qrelAllAt`: ✱12·11, ✱21·11 by `relExpr_ext`); `[✱23·58] ⊃ : x(R ⊍ S)y`
    (2), ✱23·58 detached by ✱2·27; `(1) . (2) . ⊃ ⊢ . Prop`. -/
theorem q23_6 [Reducibility S] (R S' : V a → V b → QF V) (x : V a) (y : V b) :
    QThm S (iff (relHolds x (R ⊍ S') y)
      (relAll fun T => imp (QF.and (R ⪽ T) (S' ⪽ T)) (relHolds x T y))) :=
  let G : (V a → V b → QF V) → QF V := fun T => imp (QF.and (R ⪽ T) (S' ⪽ T)) (relHolds x T y)
  have hG : RelExpr G :=
    .or (.neg (.and (RelExpr.relSubset_right R) (RelExpr.relSubset_right S'))) (RelExpr.relHolds x y)
  have h1 : QThm S (imp (relHolds x (R ⊍ S') y) (relAll G)) :=
    q10_11_21 fun θ =>                                                            -- [✱10·11·21]
      QThm.mp (qsyl (qiffMp (q23_59 R S' (pf2 θ))) (q11_1 _ x y)) (QL.t2_04 _ _ _)  -- ✱23·59 [Comm] (1)
  have h2 : QThm S (imp (relAll G) (relHolds x (R ⊍ S') y)) :=
    qsyl (qrelAllAt G (R ⊍ S') fun θ => qsyl (relExpr_ext hG (pf2 θ) _) (QL.t3_26 _ _))  -- ✱10·1
      (QThm.mp (q23_58 R S') (QL.t2_27 _ _))                                       -- [✱23·58] (2)
  qiffI h1 h2                                                                     -- (1) . (2)

/-- ✱23·61 `⊢ : R ⪽ S . ⊃ . R ⪽ S ⊍ T` [as ✱22·61: ✱23·44·58]: the first factor of ✱23·58 (S, T for R, S;
    ✱3·26) is the second factor of ✱23·44's hypothesis (✱3·21). -/
theorem q23_61 [Reducibility S] (R S' T : V a → V b → QF V) : QThm S (imp (R ⪽ S') (R ⪽ S' ⊍ T)) :=
  qsyl (QThm.mp (QThm.mp (q23_58 S' T) (QL.t3_26 _ _)) (QL.t3_21 _ _))              -- ✱23·58
    (q23_44 R S' (S' ⊍ T))                                                          -- ✱23·44

/-- ✱23·62 `⊢ : R ⪽ S . ≡ . R ⊍ S = S`. As ✱22·62: `✱4·72 . ⊃ ⊢ :: xRy . ⊃ . xSy :≡:. xRy . ∨ . xSy : ≡ .
    xSy :.` (✱4·72 with the members of the second ≡ commuted, ✱4·21) `[✱23·34] ≡ :. x(R ⊍ S)y . ≡ . xSy` (1)
    (✱4·86); `(1) . ✱10·271` (for two variables ✱11·33, with ✱11·11) `⊃ ⊢ :: R ⪽ S . ≡ :. x(R ⊍ S)y .
    ≡_{x,y} . xSy :.`; `[✱21·43] ≡ :. R ⊍ S = S`. -/
theorem q23_62 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (iff (R ⪽ S') (relEq (R ⊍ S') S')) :=
  have h1 : ∀ x y, QThm S (iff (imp (relHolds x R y) (relHolds x S' y))
      (iff (relHolds x (R ⊍ S') y) (relHolds x S' y))) := fun x y =>
    calc imp (relHolds x R y) (relHolds x S' y)
        ≡ iff (.or (relHolds x R y) (relHolds x S' y)) (relHolds x S' y) :=
          qiffTrans (QL.t4_72 _ _) (QL.t4_21 _ _)                                  -- ✱4·72
      _ ≡ iff (relHolds x (R ⊍ S') y) (relHolds x S' y) :=
          QThm.mp (qiffSymm (q23_34 R S' x y)) (QL.t4_86 _ _ _)                     -- [✱23·34] (1)
  calc (R ⪽ S')
      ≡ fiff2 (fun x y => relHolds x (R ⊍ S') y) (fun x y => relHolds x S' y) :=
        QThm.mp (q11_11 h1) (q11_33 _ _)                                          -- (1) . ✱10·271
    _ ≡ relEq (R ⊍ S') S' := qiffSymm (q21_43 _ _)                                  -- [✱21·43]

/-- ✱23·621 `⊢ : R ⪽ S . ≡ . R ∩̇ S = R` [as ✱22·621: ✱4·71], as ✱23·62: ✱4·71 with the members of the
    second ≡ commuted (✱4·21), ✱23·33 (✱4·86 for the second member), ✱11·11·33, ✱21·43. -/
theorem q23_621 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (iff (R ⪽ S') (relEq (R ∩̇ S') R)) :=
  have h1 : ∀ x y, QThm S (iff (imp (relHolds x R y) (relHolds x S' y))
      (iff (relHolds x (R ∩̇ S') y) (relHolds x R y))) := fun x y =>
    calc imp (relHolds x R y) (relHolds x S' y)
        ≡ iff (relHolds x R y) (QF.and (relHolds x R y) (relHolds x S' y)) := QL.t4_71 _ _  -- ✱4·71
      _ ≡ iff (relHolds x R y) (relHolds x (R ∩̇ S') y) :=
          QThm.mp (qiffSymm (q23_33 R S' x y)) (qiffCongrRImp _ _ _)                -- ✱23·33
      _ ≡ iff (relHolds x (R ∩̇ S') y) (relHolds x R y) := QL.t4_21 _ _
  QThm.mp (q11_11 h1) (q11_33 _ _) |> fun h => qiffTrans h (qiffSymm (q21_43 _ _))  -- ✱11·33 . ✱21·43

/-- ✱23·63 `⊢ . R ⊍ (R ∩̇ S) = R` [as ✱22·63: ✱4·44], with ✱23·34, ✱23·33 (inside the sum, ✱4·37's form
    for the second disjunct, `qorCongrRImp`), ✱11·11 and ✱21·43. -/
theorem q23_63 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (relEq (R ⊍ (R ∩̇ S')) R) :=
  qrelEqI fun x y =>
    calc relHolds x (R ⊍ (R ∩̇ S')) y
        ≡ .or (relHolds x R y) (relHolds x (R ∩̇ S') y) := q23_34 R _ x y              -- ✱23·34
      _ ≡ .or (relHolds x R y) (QF.and (relHolds x R y) (relHolds x S' y)) :=
          QThm.mp (q23_33 R S' x y) (qorCongrRImp _ _ _)                            -- ✱23·33
      _ ≡ relHolds x R y := qiffSymm (QL.t4_44 _ _)                                -- ✱4·44

/-- ✱23·631 `⊢ . R ∩̇ (R ⊍ S) = R` [as ✱22·631: ✱23·58·621]: the first factor of ✱23·58 (✱3·26) and ✱23·621
    with R ⊍ S for S. -/
theorem q23_631 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (relEq (R ∩̇ (R ⊍ S')) R) :=
  QThm.mp (QThm.mp (q23_58 R S') (QL.t3_26 _ _)) (qiffMp (q23_621 R (R ⊍ S')))       -- ✱23·58·621

/-- ✱23·632 `⊢ : R = S . ⊃ . R = R ∩̇ S` [as ✱22·632: ✱23·42·621]. From R = S, R ⪽ S: ✱23·55 with T = R
    (✱21·18 for T ⪽ R), its ≡ read as ⊃, and ✱23·42 detached (✱2·27); then ✱23·621, and R ∩̇ S = R turned
    by ✱21·21. -/
theorem q23_632 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (imp (relEq R S') (relEq R (R ∩̇ S'))) :=
  calc relEq R S'
      ⊃ iff (R ⪽ R) (R ⪽ S') := q23_55 R S' R
    _ ⊃ (R ⪽ S') := qsyl (QL.t3_26 _ _) (QThm.mp (q23_42 R) (QL.t2_27 _ _))           -- ✱23·42
    _ ⊃ relEq (R ∩̇ S') R := qiffMp (q23_621 R S')                                     -- ✱23·621
    _ ⊃ relEq R (R ∩̇ S') := qiffMp (q21_21 _ _)

/-- ✱23·633 `⊢ : R ⪽ S . ⊃ . R ⊍ T = (R ∩̇ S) ⊍ T` [as ✱22·633: ✱23·551·621]; R ∩̇ S = R is turned by ✱21·21. -/
theorem q23_633 [Reducibility S] (R S' T : V a → V b → QF V) :
    QThm S (imp (R ⪽ S') (relEq (R ⊍ T) ((R ∩̇ S') ⊍ T))) :=
  calc (R ⪽ S')
      ⊃ relEq (R ∩̇ S') R := qiffMp (q23_621 R S')                                     -- ✱23·621
    _ ⊃ relEq R (R ∩̇ S') := qiffMp (q21_21 _ _)
    _ ⊃ relEq (R ⊍ T) ((R ∩̇ S') ⊍ T) := q23_551 R (R ∩̇ S') T                          -- ✱23·551

/-- ✱23·64 `⊢ :. R ⪽ T . ∨ . S ⪽ T : ⊃ . R ∩̇ S ⪽ T`. As ✱22·64: `✱23·47·51 . ⊃ ⊢ : R ⪽ T . ⊃ . R ∩̇ S ⪽ T :
    S ⪽ T . ⊃ . R ∩̇ S ⪽ T` (1): the second is ✱23·47 for S, R, with S ∩̇ R replaced by R ∩̇ S by ✱23·51 and
    ✱23·54 (✱21·18), its ≡ read as ⊃; `(1) . ✱4·77 . ⊃ ⊢ . Prop`. -/
theorem q23_64 [Reducibility S] (R S' T : V a → V b → QF V) :
    QThm S (imp (.or (R ⪽ T) (S' ⪽ T)) (R ∩̇ S' ⪽ T)) :=
  have h1 := q23_47 R S' T                                                         -- ✱23·47
  have h2 := qsyl (q23_47 S' R T) (qiffMp (QThm.mp (q23_51 S' R) (q23_54 _ _ T)))     -- ✱23·47·51 (1)
  QThm.mp (qandI h1 h2) (qiffMp (QL.t4_77 _ _ _))                                  -- (1) . ✱4·77

/-- ✱23·65 `⊢ :. R ⪽ S . ∨ . R ⪽ T : ⊃ . R ⪽ S ⊍ T` [as ✱22·65: ✱23·61·57 . ✱4·77]: ✱23·61, and ✱23·61 for
    T, S with T ⊍ S replaced by S ⊍ T by ✱23·57 and ✱23·55 (✱21·18), its ≡ read as ⊃. -/
theorem q23_65 [Reducibility S] (R S' T : V a → V b → QF V) :
    QThm S (imp (.or (R ⪽ S') (R ⪽ T)) (R ⪽ S' ⊍ T)) :=
  have h1 := q23_61 R S' T                                                         -- ✱23·61
  have h2 := qsyl (q23_61 R T S') (qiffMp (QThm.mp (q23_57 T S') (q23_55 _ _ R)))     -- ✱23·61·57
  QThm.mp (qandI h1 h2) (qiffMp (QL.t4_77 _ _ _))                                  -- ✱4·77

/-- ✱23·66 `⊢ : R ⪽ S . ⊃ . R ⊍ T ⪽ S ⊍ T` [as ✱22·66: ✱2·38], under (x, y) by ✱11·11 and ✱11·32 (✱10·27
    for two variables), the sums read by ✱23·34 (✱10·413 for two variables). -/
theorem q23_66 [Reducibility S] (R S' T : V a → V b → QF V) :
    QThm S (imp (R ⪽ S') (R ⊍ T ⪽ S' ⊍ T)) :=
  qsyl (QThm.mp (q11_11 fun x y => QL.t2_38 (relHolds x T y) _ _) (q11_32 _ _))     -- ✱2·38
    (qiffMp (qfimp2Congr (fun x y => qiffSymm (q23_34 R T x y)) fun x y => qiffSymm (q23_34 S' T x y)))

/-- ✱23·68 `⊢ . (R ∩̇ S) ⊍ (R ∩̇ T) = R ∩̇ (S ⊍ T)`. As ✱22·68: `✱23·34 . ⊃ ⊢ :: x{(R ∩̇ S) ⊍ (R ∩̇ T)}y . ≡ :.
    x(R ∩̇ S)y . ∨ . x(R ∩̇ T)y :.` `[✱23·33] ≡ :. xRy . xSy . ∨ . xRy . xTy :.` (✱4·39) `[✱4·4] ≡ :. xRy :
    xSy . ∨ . xTy :.` `[✱23·34] ≡ :. xRy . x(S ⊍ T)y :.` (✱4·36's form for the second factor)
    `[✱23·33] ≡ :. x{R ∩̇ (S ⊍ T)}y` (1); `(1) . ✱11·11 . ✱21·43 . ⊃ ⊢ . Prop`. -/
theorem q23_68 [Reducibility S] (R S' T : V a → V b → QF V) :
    QThm S (relEq ((R ∩̇ S') ⊍ (R ∩̇ T)) (R ∩̇ (S' ⊍ T))) :=
  qrelEqI fun x y =>                                                              -- (1) . ✱11·11 . ✱21·43
    calc relHolds x ((R ∩̇ S') ⊍ (R ∩̇ T)) y
        ≡ .or (relHolds x (R ∩̇ S') y) (relHolds x (R ∩̇ T) y) := q23_34 _ _ x y         -- ✱23·34
      _ ≡ .or (QF.and (relHolds x R y) (relHolds x S' y)) (QF.and (relHolds x R y) (relHolds x T y)) :=
          qorIffCongr (q23_33 R S' x y) (q23_33 R T x y)                            -- [✱23·33]
      _ ≡ QF.and (relHolds x R y) (.or (relHolds x S' y) (relHolds x T y)) := qiffSymm (QL.t4_4 _ _ _)  -- [✱4·4]
      _ ≡ QF.and (relHolds x R y) (relHolds x (S' ⊍ T) y) :=
          qandCongrR _ (qiffSymm (q23_34 S' T x y))                                -- [✱23·34]
      _ ≡ relHolds x (R ∩̇ (S' ⊍ T)) y := qiffSymm (q23_33 R _ x y)                   -- [✱23·33] (1)

/-- ✱23·69 `⊢ . (R ⊍ S) ∩̇ (R ⊍ T) = R ⊍ (S ∩̇ T)` [as ✱22·69: Similar proof, by ✱4·41]: ✱23·33, ✱23·34 (✱4·38),
    ✱4·41, ✱23·33 inside the sum (`qorCongrRImp`), ✱23·34, ✱11·11, ✱21·43. -/
theorem q23_69 [Reducibility S] (R S' T : V a → V b → QF V) :
    QThm S (relEq ((R ⊍ S') ∩̇ (R ⊍ T)) (R ⊍ (S' ∩̇ T))) :=
  qrelEqI fun x y =>
    calc relHolds x ((R ⊍ S') ∩̇ (R ⊍ T)) y
        ≡ QF.and (relHolds x (R ⊍ S') y) (relHolds x (R ⊍ T) y) := q23_33 _ _ x y       -- ✱23·33
      _ ≡ QF.and (.or (relHolds x R y) (relHolds x S' y)) (.or (relHolds x R y) (relHolds x T y)) :=
          qandIffCongr (q23_34 R S' x y) (q23_34 R T x y)                           -- ✱23·34
      _ ≡ .or (relHolds x R y) (QF.and (relHolds x S' y) (relHolds x T y)) := qiffSymm (QL.t4_41 _ _ _)  -- ✱4·41
      _ ≡ .or (relHolds x R y) (relHolds x (S' ∩̇ T) y) :=
          QThm.mp (qiffSymm (q23_33 S' T x y)) (qorCongrRImp _ _ _)                 -- ✱23·33
      _ ≡ relHolds x (R ⊍ (S' ∩̇ T)) y := qiffSymm (q23_34 R _ x y)                   -- ✱23·34

/-- ✱23·7 `⊢ . (R ⊍ S) ⊍ T = R ⊍ (S ⊍ T)` [as ✱22·7: ✱4·33], with ✱23·34 (inside the outer sum: ✱4·37 and
    its form for the second disjunct), ✱11·11 and ✱21·43. -/
theorem q23_7 [Reducibility S] (R S' T : V a → V b → QF V) :
    QThm S (relEq ((R ⊍ S') ⊍ T) (R ⊍ (S' ⊍ T))) :=
  qrelEqI fun x y =>
    calc relHolds x ((R ⊍ S') ⊍ T) y
        ≡ .or (relHolds x (R ⊍ S') y) (relHolds x T y) := q23_34 _ T x y               -- ✱23·34
      _ ≡ .or (.or (relHolds x R y) (relHolds x S' y)) (relHolds x T y) :=
          QThm.mp (q23_34 R S' x y) (QL.t4_37 _ _ _)                                -- ✱23·34
      _ ≡ .or (relHolds x R y) (.or (relHolds x S' y) (relHolds x T y)) := QL.t4_33 _ _ _  -- ✱4·33
      _ ≡ .or (relHolds x R y) (relHolds x (S' ⊍ T) y) :=
          QThm.mp (qiffSymm (q23_34 S' T x y)) (qorCongrRImp _ _ _)                 -- ✱23·34
      _ ≡ relHolds x (R ⊍ (S' ⊍ T)) y := qiffSymm (q23_34 R _ x y)                   -- ✱23·34

/-- ✱23·72 `⊢ : P ⪽ R . Q ⪽ S . ⊃ . P ⊍ Q ⪽ R ⊍ S` [as ✱22·72: ✱3·48], under (x, y) as ✱11·39 is (✱11·31,
    ✱11·11, ✱11·32), the sums read by ✱23·34 (✱10·413 for two variables). -/
theorem q23_72 [Reducibility S] (P Q R S' : V a → V b → QF V) :
    QThm S (imp (QF.and (P ⪽ R) (Q ⪽ S')) (P ⊍ Q ⪽ R ⊍ S')) :=
  qsyl (qiffMp (q11_31 _ _))
    (qsyl (QThm.mp (q11_11 fun _ _ => QL.t3_48 _ _ _ _) (q11_32 _ _))               -- ✱3·48
      (qiffMp (qfimp2Congr (fun x y => qiffSymm (q23_34 P Q x y)) fun x y => qiffSymm (q23_34 R S' x y))))

/-- ✱23·73 `⊢ : P = R . Q = S . ⊃ . P ⊍ Q = R ⊍ S` [as ✱22·73: ✱10·411]. P = R and Q = S are read by ✱21·43
    (each factor, ✱3·47); ✱10·411 for two variables is ✱4·39 under (x, y) as in ✱11·39's proof (✱11·31,
    ✱11·11, ✱11·32); the sums are read by ✱23·34 (✱10·414 for two variables) and R ⊍ S = … by ✱21·43. -/
theorem q23_73 [Reducibility S] (P Q R S' : V a → V b → QF V) :
    QThm S (imp (QF.and (relEq P R) (relEq Q S')) (relEq (P ⊍ Q) (R ⊍ S'))) :=
  calc QF.and (relEq P R) (relEq Q S')
      ⊃ QF.and (fiff2 (fun x y => relHolds x P y) (fun x y => relHolds x R y))
          (fiff2 (fun x y => relHolds x Q y) (fun x y => relHolds x S' y)) :=
        QThm.mp (qandI (qiffMp (q21_43 P R)) (qiffMp (q21_43 Q S'))) (QL.t3_47 _ _ _ _)  -- ✱21·43
    _ ⊃ fiff2 (fun x y => .or (relHolds x P y) (relHolds x Q y))
          (fun x y => .or (relHolds x R y) (relHolds x S' y)) :=
        qsyl (qiffMp (q11_31 _ _)) (QThm.mp (q11_11 fun _ _ => QL.t4_39 _ _ _ _) (q11_32 _ _))  -- ✱10·411
    _ ⊃ fiff2 (fun x y => relHolds x (P ⊍ Q) y) (fun x y => relHolds x (R ⊍ S') y) :=
        qiffMp (qfiff2Congr (fun x y => qiffSymm (q23_34 P Q x y)) fun x y => qiffSymm (q23_34 R S' x y))
    _ ⊃ relEq (P ⊍ Q) (R ⊍ S') := qiffMpr (q21_43 _ _)                              -- ✱21·43

/-- ✱23·74 `⊢ : P ∩̇ Q ⪽ R . P ∩̇ R ⪽ Q . ≡ . P ∩̇ Q = P ∩̇ R`. As ✱22·74: `✱23·43 . ✱4·73 . ⊃ ⊢ : P ∩̇ Q ⪽ R .
    ≡ . P ∩̇ Q ⪽ P . P ∩̇ Q ⪽ R .` (✱4·73's product commuted, ✱4·3) `[✱23·45] ≡ . P ∩̇ Q ⪽ P ∩̇ R` (1);
    `(1) R, Q/Q, R` (2); `(1) . (2) . ✱4·38 . ⊃ ⊢ : P ∩̇ Q ⪽ R . P ∩̇ R ⪽ Q . ≡ . P ∩̇ Q ⪽ P ∩̇ R . P ∩̇ R ⪽ P ∩̇ Q .`
    `[✱23·41] ≡ . P ∩̇ Q = P ∩̇ R`. -/
theorem q23_74 [Reducibility S] (P Q R : V a → V b → QF V) :
    QThm S (iff (QF.and (P ∩̇ Q ⪽ R) (P ∩̇ R ⪽ Q)) (relEq (P ∩̇ Q) (P ∩̇ R))) :=
  have h1 : ∀ Q R : V a → V b → QF V, QThm S (iff (P ∩̇ Q ⪽ R) (P ∩̇ Q ⪽ P ∩̇ R)) := fun Q R =>
    calc (P ∩̇ Q ⪽ R)
        ≡ QF.and (P ∩̇ Q ⪽ R) (P ∩̇ Q ⪽ P) := QThm.mp (q23_43 P Q) (QL.t4_73 _ _)    -- ✱23·43 . ✱4·73
      _ ≡ QF.and (P ∩̇ Q ⪽ P) (P ∩̇ Q ⪽ R) := QL.t4_3 _ _
      _ ≡ (P ∩̇ Q ⪽ P ∩̇ R) := q23_45 _ _ _                                            -- [✱23·45] (1)
  calc QF.and (P ∩̇ Q ⪽ R) (P ∩̇ R ⪽ Q)
      ≡ QF.and (P ∩̇ Q ⪽ P ∩̇ R) (P ∩̇ R ⪽ P ∩̇ Q) := qandIffCongr (h1 Q R) (h1 R Q)     -- (1) . (2) . ✱4·38
    _ ≡ relEq (P ∩̇ Q) (P ∩̇ R) := q23_41 _ _                                         -- [✱23·41]

/-! ## ✱23·8–✱23·95 -/

/-- ✱23·8 `⊢ . ∸(∸R) = R` [as ✱22·8: ✱4·13], with ✱23·35 (twice, the second under ∼ by ✱4·11), ✱11·11 and
    ✱21·43. -/
theorem q23_8 [Reducibility S] (R : V a → V b → QF V) : QThm S (relEq (∸(∸R)) R) :=
  qrelEqI fun x y =>
    calc relHolds x (∸(∸R)) y
        ≡ .neg (relHolds x (∸R) y) := q23_35 _ x y                                  -- ✱23·35
      _ ≡ .neg (.neg (relHolds x R y)) := qiffNeg (q23_35 R x y)                    -- ✱23·35
      _ ≡ relHolds x R y := qiffSymm (QL.t4_13 _)                                  -- ✱4·13

/-- ✱23·81 `⊢ : R ⪽ S . ≡ . ∸S ⪽ ∸R` [as ✱22·81: ✱4·1], under (x, y) by ✱11·11·33, with ✱23·35 for both
    members (✱4·84, ✱4·85). The statement is the Gutenberg transcription's, which applies the published
    Errata here. -/
theorem q23_81 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (iff (R ⪽ S') (∸S' ⪽ ∸R)) :=
  QThm.mp (q11_11 fun x y => qiffTrans (QL.t4_1 _ _)
      (qimpIffCongr (qiffSymm (q23_35 S' x y)) (qiffSymm (q23_35 R x y))))          -- ✱4·1
    (q11_33 _ _)

/-- ✱23·811 `⊢ : R ⪽ ∸S . ≡ . S ⪽ ∸R` [as ✱22·811: ✱4·1 . ✱23·8]: ✱23·81 (whose proof is ✱4·1) with ∸S for
    S, and ∸(∸S) replaced by S by ✱23·8 and ✱23·54 (✱21·18). -/
theorem q23_811 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (iff (R ⪽ ∸S') (S' ⪽ ∸R)) :=
  qiffTrans (q23_81 R (∸S')) (QThm.mp (q23_8 S') (q23_54 _ _ _))                     -- ✱4·1 . ✱23·8

/-- ✱23·82 `⊢ : R ∩̇ S ⪽ T . ≡ . R ∸ T ⪽ ∸S` [as ✱22·82: ✱4·14], under (x, y) by ✱11·11·33; x(R ∩̇ S)y,
    x(R ∸ T)y = x(R ∩̇ ∸T)y and x ∸T y, x ∸S y are read by ✱23·33 and ✱23·35 (✱4·84, ✱4·85, ✱4·36's form
    for the second factor). -/
theorem q23_82 [Reducibility S] (R S' T : V a → V b → QF V) : QThm S (iff (R ∩̇ S' ⪽ T) (R ∸ T ⪽ ∸S')) :=
  QThm.mp (q11_11 fun x y =>
      calc imp (relHolds x (R ∩̇ S') y) (relHolds x T y)
          ≡ imp (QF.and (relHolds x R y) (relHolds x S' y)) (relHolds x T y) :=
            QThm.mp (q23_33 R S' x y) (QL.t4_84 _ _ _)                              -- ✱23·33
        _ ≡ imp (QF.and (relHolds x R y) (.neg (relHolds x T y))) (.neg (relHolds x S' y)) :=
            QL.t4_14 _ _ _                                                        -- ✱4·14
        _ ≡ imp (relHolds x (R ∸ T) y) (relHolds x (∸S') y) :=
            qimpIffCongr (qiffTrans (qandCongrR _ (qiffSymm (q23_35 T x y))) (qiffSymm (q23_33 R (∸T) x y)))
              (qiffSymm (q23_35 S' x y)))                                          -- ✱23·33·35
    (q11_33 _ _)

/-- ✱23·83 `⊢ : R = S . ≡ . ∸R = ∸S` [as ✱22·83: ✱4·11]: ✱21·43, ✱4·11 under (x, y) (✱11·11·33), ✱23·35 for
    both members (✱10·414 for two variables), ✱21·43. -/
theorem q23_83 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (iff (relEq R S') (relEq (∸R) (∸S'))) :=
  calc relEq R S'
      ≡ fiff2 (fun x y => relHolds x R y) (fun x y => relHolds x S' y) := q21_43 R S'  -- ✱21·43
    _ ≡ fiff2 (fun x y => .neg (relHolds x R y)) (fun x y => .neg (relHolds x S' y)) :=
        QThm.mp (q11_11 fun _ _ => QL.t4_11 _ _) (q11_33 _ _)                     -- ✱4·11
    _ ≡ fiff2 (fun x y => relHolds x (∸R) y) (fun x y => relHolds x (∸S') y) :=
        qfiff2Congr (fun x y => qiffSymm (q23_35 R x y)) fun x y => qiffSymm (q23_35 S' x y)  -- ✱23·35
    _ ≡ relEq (∸R) (∸S') := qiffSymm (q21_43 _ _)                                  -- ✱21·43

/-- ✱23·831 `⊢ : R = ∸S . ≡ . S = ∸R` [as ✱22·831: ✱4·12], as ✱23·83. -/
theorem q23_831 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (iff (relEq R (∸S')) (relEq S' (∸R))) :=
  calc relEq R (∸S')
      ≡ fiff2 (fun x y => relHolds x R y) (fun x y => relHolds x (∸S') y) := q21_43 _ _  -- ✱21·43
    _ ≡ fiff2 (fun x y => relHolds x R y) (fun x y => .neg (relHolds x S' y)) :=
        qfiff2Congr (fun _ _ => QL.t4_2 _) fun x y => q23_35 S' x y                  -- ✱23·35
    _ ≡ fiff2 (fun x y => relHolds x S' y) (fun x y => .neg (relHolds x R y)) :=
        QThm.mp (q11_11 fun _ _ => QL.t4_12 _ _) (q11_33 _ _)                     -- ✱4·12
    _ ≡ fiff2 (fun x y => relHolds x S' y) (fun x y => relHolds x (∸R) y) :=
        qfiff2Congr (fun _ _ => QL.t4_2 _) fun x y => qiffSymm (q23_35 R x y)       -- ✱23·35
    _ ≡ relEq S' (∸R) := qiffSymm (q21_43 _ _)                                     -- ✱21·43

/-- ✱23·84 `⊢ . ∸(R ∩̇ S) = ∸R ⊍ ∸S` [as ✱22·84: ✱4·51], with ✱23·35, ✱23·33 (under ∼, ✱4·11), ✱23·35 for each
    disjunct (✱4·39), ✱23·34, ✱11·11, ✱21·43. -/
theorem q23_84 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (relEq (∸(R ∩̇ S')) (∸R ⊍ ∸S')) :=
  qrelEqI fun x y =>
    calc relHolds x (∸(R ∩̇ S')) y
        ≡ .neg (relHolds x (R ∩̇ S') y) := q23_35 _ x y                               -- ✱23·35
      _ ≡ .neg (QF.and (relHolds x R y) (relHolds x S' y)) := qiffNeg (q23_33 R S' x y)  -- ✱23·33
      _ ≡ .or (.neg (relHolds x R y)) (.neg (relHolds x S' y)) := QL.t4_51 _ _         -- ✱4·51
      _ ≡ .or (relHolds x (∸R) y) (relHolds x (∸S') y) :=
          qorIffCongr (qiffSymm (q23_35 R x y)) (qiffSymm (q23_35 S' x y))          -- ✱23·35
      _ ≡ relHolds x (∸R ⊍ ∸S') y := qiffSymm (q23_34 _ _ x y)                        -- ✱23·34

/-- ✱23·85 `⊢ . R ∩̇ S = ∸(∸R ⊍ ∸S)` [as ✱22·85: ✱23·84·831]: ✱23·831 for R ∩̇ S, ∸R ⊍ ∸S, and ✱23·84 turned by
    ✱21·21. -/
theorem q23_85 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (relEq (R ∩̇ S') (∸(∸R ⊍ ∸S'))) :=
  QThm.mp (QThm.mp (q23_84 R S') (qiffMp (q21_21 _ _))) (qiffMpr (q23_831 _ _))      -- ✱23·84·831

/-- ✱23·86 `⊢ . ∸(∸R ∩̇ ∸S) = R ⊍ S` [as ✱22·86: ✱4·57], as ✱23·84. -/
theorem q23_86 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (relEq (∸(∸R ∩̇ ∸S')) (R ⊍ S')) :=
  qrelEqI fun x y =>
    calc relHolds x (∸(∸R ∩̇ ∸S')) y
        ≡ .neg (relHolds x (∸R ∩̇ ∸S') y) := q23_35 _ x y                             -- ✱23·35
      _ ≡ .neg (QF.and (relHolds x (∸R) y) (relHolds x (∸S') y)) := qiffNeg (q23_33 _ _ x y)  -- ✱23·33
      _ ≡ .neg (QF.and (.neg (relHolds x R y)) (.neg (relHolds x S' y))) :=
          qiffNeg (qandIffCongr (q23_35 R x y) (q23_35 S' x y))                     -- ✱23·35
      _ ≡ .or (relHolds x R y) (relHolds x S' y) := QL.t4_57 _ _                      -- ✱4·57
      _ ≡ relHolds x (R ⊍ S') y := qiffSymm (q23_34 R S' x y)                          -- ✱23·34

/-- ✱23·87 `⊢ . ∸R ∩̇ ∸S = ∸(R ⊍ S)` [as ✱22·87: ✱23·86·831]: ✱23·831 for ∸R ∩̇ ∸S, R ⊍ S, and ✱23·86 turned by
    ✱21·21. -/
theorem q23_87 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (relEq (∸R ∩̇ ∸S') (∸(R ⊍ S'))) :=
  QThm.mp (QThm.mp (q23_86 R S') (qiffMp (q21_21 _ _))) (qiffMpr (q23_831 _ _))      -- ✱23·86·831

/-- ✱23·88 `⊢ . (x, y) . x(R ⊍ ∸R)y` [as ✱22·88: ✱2·11], with ✱23·34 and ✱23·35 (✱4·37's form for the second
    disjunct), under (x, y) by ✱11·11. -/
theorem q23_88 [Reducibility S] (R : V a → V b → QF V) : QThm S (all2 fun x y => relHolds x (R ⊍ ∸R) y) :=
  q11_11 fun x y => QThm.mp (QL.t2_11 _)                                          -- ✱2·11
    (qiffMpr (qiffTrans (q23_34 R (∸R) x y) (QThm.mp (q23_35 R x y) (qorCongrRImp _ _ _))))

/-- ✱23·89 `⊢ . (x, y) . ∼{x(R ∸ R)y}` [as ✱22·89: ✱3·24], with ✱23·33 and ✱23·35 (✱4·36's form for the
    second factor) under ∼ (✱4·11), under (x, y) by ✱11·11. -/
theorem q23_89 [Reducibility S] (R : V a → V b → QF V) :
    QThm S (all2 fun x y => .neg (relHolds x (R ∸ R) y)) :=
  q11_11 fun x y => QThm.mp (QL.t3_24 _)                                          -- ✱3·24
    (qiffMpr (qiffNeg (qiffTrans (q23_33 R (∸R) x y) (qandCongrR _ (q23_35 R x y)))))

/-- ✱23·9 `⊢ . (R ⊍ S) ∸ S = R ∸ S` [as ✱22·9: ✱5·61], with ✱23·33, ✱23·34, ✱23·35 (✱4·38), ✱11·11, ✱21·43. -/
theorem q23_9 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (relEq ((R ⊍ S') ∸ S') (R ∸ S')) :=
  qrelEqI fun x y =>
    calc relHolds x ((R ⊍ S') ∸ S') y
        ≡ QF.and (.or (relHolds x R y) (relHolds x S' y)) (.neg (relHolds x S' y)) :=
          qiffTrans (q23_33 _ _ x y) (qandIffCongr (q23_34 R S' x y) (q23_35 S' x y)) -- ✱23·33·34·35
      _ ≡ QF.and (relHolds x R y) (.neg (relHolds x S' y)) := QL.t5_61 _ _           -- ✱5·61
      _ ≡ relHolds x (R ∸ S') y :=
          qiffTrans (qandCongrR _ (qiffSymm (q23_35 S' x y))) (qiffSymm (q23_33 R _ x y))  -- ✱23·33·35

/-- ✱23·91 `⊢ . R ⊍ S = R ⊍ (S ∸ R)`. As ✱22·91: `✱5·63 . ⊃ ⊢ :. xRy . ∨ . xSy : ≡ : xRy . ∨ . xSy . ∼(xRy) :.`
    (✱5·63's product commuted, ✱4·3, inside the sum, `qorCongrRImp`) `[✱23·33·34·35] ⊃ ⊢ :. x(R ⊍ S)y . ≡ : xRy .
    ∨ . x(S ∸ R)y :` `[✱23·34] ≡ : x{R ⊍ (S ∸ R)}y` (1); `(1) . ✱11·11 . ✱21·43 . ⊃ ⊢ . Prop`. -/
theorem q23_91 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (relEq (R ⊍ S') (R ⊍ (S' ∸ R))) :=
  qrelEqI fun x y =>                                                              -- (1) . ✱11·11 . ✱21·43
    calc relHolds x (R ⊍ S') y
        ≡ .or (relHolds x R y) (relHolds x S' y) := q23_34 R S' x y                    -- [✱23·34]
      _ ≡ .or (relHolds x R y) (QF.and (relHolds x S' y) (.neg (relHolds x R y))) :=
          qiffTrans (QL.t5_63 _ _) (QThm.mp (QL.t4_3 _ _) (qorCongrRImp _ _ _))     -- ✱5·63
      _ ≡ .or (relHolds x R y) (relHolds x (S' ∸ R) y) :=
          QThm.mp (qiffTrans (qandCongrR _ (qiffSymm (q23_35 R x y))) (qiffSymm (q23_33 S' (∸R) x y)))
            (qorCongrRImp _ _ _)                                                  -- [✱23·33·35]
      _ ≡ relHolds x (R ⊍ (S' ∸ R)) y := qiffSymm (q23_34 R _ x y)                    -- [✱23·34] (1)

/-- ✱23·92 `⊢ : R ⪽ S . ⊃ . S = R ⊍ (S ∸ R)` [as ✱22·92: ✱23·91·62]: by ✱23·62, R ⊍ S = S; with ✱23·91,
    R ⊍ S = R ⊍ (S ∸ R), ✱21·23 gives S = R ⊍ (S ∸ R) (the factors joined by ✱3·2). -/
theorem q23_92 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (imp (R ⪽ S') (relEq S' (R ⊍ (S' ∸ R)))) :=
  calc (R ⪽ S')
      ⊃ relEq (R ⊍ S') S' := qiffMp (q23_62 R S')                                     -- ✱23·62
    _ ⊃ QF.and (relEq (R ⊍ S') S') (relEq (R ⊍ S') (R ⊍ (S' ∸ R))) :=
        QThm.mp (q23_91 R S') (QL.t3_21 _ _)                                       -- ✱23·91
    _ ⊃ relEq S' (R ⊍ (S' ∸ R)) := q21_23 _ _ _

/-- ✱23·93 `⊢ . R ∸ S = R ∸ (R ∩̇ S)`. As ✱22·93: `✱4·73 . Transp . ⊃ ⊢ :. xRy . ⊃ : ∼(xSy) . ≡ . ∼(xRy .
    xSy) .` (✱4·73's product commuted, ✱4·3 under ✱4·86's form for the second member; Transp is ✱4·11)
    `[✱23·33] ≡ . ∼{x(R ∩̇ S)y} :.` (and by ✱23·35 both members are x ∸S y, x ∸(R ∩̇ S) y)
    `[✱5·32] ⊃ ⊢ :. xRy . x ∸S y . ≡ . xRy . x ∸(R ∩̇ S) y :.` `[✱23·35·33] ⊃ ⊢ : x(R ∸ S)y . ≡ . x{R ∸ (R ∩̇ S)}y :`
    `[✱11·11 . ✱21·43] ⊃ ⊢ . R ∸ S = R ∸ (R ∩̇ S)`. -/
theorem q23_93 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (relEq (R ∸ S') (R ∸ (R ∩̇ S'))) :=
  qrelEqI fun x y =>                                                              -- [✱11·11 . ✱21·43]
    have h1 : QThm S (imp (relHolds x R y)
        (iff (relHolds x (∸S') y) (relHolds x (∸(R ∩̇ S')) y))) :=
      calc relHolds x R y
          ⊃ iff (relHolds x S' y) (QF.and (relHolds x S' y) (relHolds x R y)) := QL.t4_73 _ _
        _ ⊃ iff (relHolds x S' y) (QF.and (relHolds x R y) (relHolds x S' y)) :=
            qiffMp (QThm.mp (QL.t4_3 _ _) (qiffCongrRImp _ _ _))
        _ ⊃ iff (.neg (relHolds x S' y)) (.neg (QF.and (relHolds x R y) (relHolds x S' y))) :=
            qiffMp (QL.t4_11 _ _)                                                 -- ✱4·73 . Transp
        _ ⊃ iff (relHolds x (∸S') y) (relHolds x (∸(R ∩̇ S')) y) :=
            qiffMp (qiffIffCongr (qiffSymm (q23_35 S' x y))
              (qiffTrans (qiffNeg (qiffSymm (q23_33 R S' x y))) (qiffSymm (q23_35 _ x y))))  -- [✱23·33]
    calc relHolds x (R ∸ S') y
        ≡ QF.and (relHolds x R y) (relHolds x (∸S') y) := q23_33 R (∸S') x y            -- [✱23·35·33]
      _ ≡ QF.and (relHolds x R y) (relHolds x (∸(R ∩̇ S')) y) :=
          QThm.mp h1 (qiffMp (QL.t5_32 _ _ _))                                     -- [✱5·32]
      _ ≡ relHolds x (R ∸ (R ∩̇ S')) y := qiffSymm (q23_33 R _ x y)                    -- [✱23·35·33]

/-- ✱23·94 `⊢ : (R) . fR . ≡ . (R) . f(∸R)`, R apparent (✱21·07), fR an extensional expression of R (`RelExt`;
    p. 213). As ✱22·94: `✱10·1 . ⊃ ⊢ : (R) . fR . ⊃ . f(∸R)`, ✱10·1 at ∸R, whose defining function is not
    predicative, being its analogue for relations (`qrelAllAt`: ✱12·11, and the premise for ✱21·11);
    `[✱10·11·21]` (1); `✱10·1 . ⊃ ⊢ : (R) . f(∸R) . ⊃ . f{∸(∸R)} .`, again at ∸R (`qrelAllAt`, f(∸R) being
    extensional by `relExt_compl`); `[✱23·8 . ✱21·18] ⊃ . fR` (✱21·18 for fR, `qrel21_18`, its ≡ read as ⊃);
    `[✱10·11·21]` (2); `(1) . (2) . ⊃ ⊢ . Prop`. For a generic f{R} (`rel R f`) the premise is ✱21·11
    (`relExt_rel`), and for an expression PM's notation forms it is `relExpr_ext`. -/
theorem q23_94 [Reducibility S] (F : (V a → V b → QF V) → QF V) (hF : RelExt S F) :
    QThm S (iff (relAll F) (relAll fun R => F (∸R))) :=
  have h1 : QThm S (imp (relAll F) (relAll fun R => F (∸R))) :=
    q10_11_21 fun φ =>                                                            -- [✱10·11·21] (1)
      qrelAllAt F (∸(pf2 φ)) fun θ => qsyl (hF (pf2 θ) _) (QL.t3_26 _ _)          -- ✱10·1
  have h2 : QThm S (imp (relAll fun R => F (∸R)) (relAll F)) :=
    q10_11_21 fun φ =>                                                            -- [✱10·11·21] (2)
      qsyl (qrelAllAt (fun R => F (∸R)) (∸(pf2 φ)) fun θ =>
          qsyl (relExt_compl hF (pf2 θ) _) (QL.t3_26 _ _))                        -- ✱10·1
        (qiffMp (QThm.mp (q23_8 (pf2 φ)) (qrel21_18 F hF _ _)))                    -- [✱23·8 . ✱21·18]
  qiffI h1 h2                                                                     -- (1) . (2)

/-- ✱23·95 `⊢ : (∃R) . fR . ≡ . (∃R) . f(∸R)`, fR as in ✱23·94. As ✱22·95: `✱23·94 . ⊃ ⊢ : (R) . ∼fR . ≡ .
    (R) . ∼f(∸R)` (1), ∼fR being extensional too (✱4·11, `relExt_neg`); `(1) . Transp . ✱21·6 . ⊃ ⊢ . Prop`,
    Transp being ✱4·11. -/
theorem q23_95 [Reducibility S] (F : (V a → V b → QF V) → QF V) (hF : RelExt S F) :
    QThm S (iff (relEx F) (relEx fun R => F (∸R))) :=
  qiffTrans (q21_6 F)
    (qiffTrans (qiffNeg (q23_94 (fun R => .neg (F R)) (relExt_neg hF)))           -- ✱23·94 (1) . Transp
      (qiffSymm (q21_6 _)))                                                       -- ✱21·6

end PM
