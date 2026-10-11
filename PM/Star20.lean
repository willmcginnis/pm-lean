import PM.Star14
/-!
  ✱20: general theory of classes (1910 print, pp. 196–212). **Partial**: the definitions ✱20·01 and
  ✱20·02 and the propositions ✱20·1, ✱20·13, ✱20·14, ✱20·15 and ✱20·3, as a usability test of the
  ramified base (docs/TYPES_DESIGN.md, test U5). The rest of ✱20 is not formalized.

  Classes are incomplete symbols: ẑ(ψz) has meaning only in a context f{ẑ(ψz)}, defined by ✱20·01 in
  terms of a predicative function φ!ẑ formally equivalent to ψẑ. As for descriptions (PM/Star14.lean),
  the context is an explicit argument of the macro:
    ✱20·01  f{ẑ(ψz)} . = : (∃φ) : φ!x . ≡ₓ . ψx : f{φ!ẑ}   Df   (`QF.cls ψ f`)
    ✱20·02  x ∈ (φ!ẑ) . = . φ!x                            Df   (`QF.mem x φ`)
  Identity of classes is ✱13·01 at the type of predicative functions, eliminated by ✱20·01 twice, the
  first class having the larger scope "because it occurs first" (p. 201): `QF.clsEq ψ χ`.
  So ✱13·01 is used at the type `Ty.pred1 a`, and ✱12·1 at the type of its argument, through
  ✱13·195 (typical ambiguity: the same Lean definitions and theorems at a higher type).
-/
namespace PM
open QF

namespace QF
variable {V : Ty → Type}
/-- ✱20·01 `f{ẑ(ψz)} . = : (∃φ) : φ!x . ≡ₓ . ψx : f{φ!ẑ}` Df. `f` is the context of the class. -/
@[reducible] def cls {a : Ty} (ψ : V a → QF V) (f : V (Ty.pred1 a) → QF V) : QF V :=
  ex (τ := Ty.pred1 a) fun φ => QF.and (fiff (fun x => .app1 φ x) ψ) (f φ)
/-- ✱20·02 `x ∈ (φ!ẑ) . = . φ!x` Df -/
@[reducible] def mem {a : Ty} (x : V a) (φ : V (Ty.pred1 a)) : QF V := .app1 φ x
/-- `ẑ(ψz) = ẑ(χz)`: ✱13·01 between predicative functions, with ✱20·01 applied to ẑ(ψz) first and
    then to ẑ(χz) (p. 201). -/
@[reducible] def clsEq {a : Ty} (ψ χ : V a → QF V) : QF V :=
  cls ψ fun φ => cls χ fun θ => ident φ θ
end QF

variable {V : Ty → Type} {a : Ty}

/-- From `⊢ . p`, `⊢ : p . q . ≡ . q` (✱3·27, ✱3·2). -/
theorem qand_true_left {p q : QF V} (hp : QThm p) : QThm (iff (QF.and p q) q) :=
  qiffI (QL.t3_27 p q) (QThm.mp hp (QL.t3_2 p q))

/-- ✱20·1 `⊢ :. f{ẑ(ψz)} . ≡ : (∃φ) : φ!x . ≡ₓ . ψx : f{φ!ẑ}` [✱4·2 . (✱20·01)] -/
theorem q20_1 (ψ : V a → QF V) (f : V (Ty.pred1 a) → QF V) :
    QThm (iff (cls ψ f) (ex (τ := Ty.pred1 a) fun φ => QF.and (fiff (fun x => .app1 φ x) ψ) (f φ))) :=
  QL.t4_2 _

/-- ✱20·13 `⊢ :. ψx . ≡ₓ . χx : ⊃ . ẑ(ψz) = ẑ(χz)`. PM's (1) is the definitional unfolding (✱20·1
    twice). In (2), ✱12·1 gives (∃φ) : ψx ≡ₓ φ!x, read as φ!x ≡ₓ ψx by ✱10·32; with Hp, ✱10·321 gives
    φ!x ≡ₓ χx; and the step PM takes by ✱13·195 (from F φ to (∃θ) : θ = φ . F θ) is taken by its
    proof's first line, ✱3·2 . ✱13·15 . ✱10·24, with θ = φ written φ = θ as ✱13·01 needs. The two
    hypotheses are joined by Comp and Exp (✱3·43, ✱3·3) and carried under (∃φ) by ✱10·11·21·28. -/
theorem q20_13 (ψ χ : V a → QF V) : QThm (imp (fiff ψ χ) (clsEq ψ χ)) :=
  let P : V (Ty.pred1 a) → QF V := fun φ => fiff (fun x => .app1 φ x) ψ
  let R : V (Ty.pred1 a) → QF V := fun φ => QF.and (P φ) (cls χ fun θ => ident φ θ)
  have h1 : QThm (ex fun φ => fiff ψ fun x => .app1 φ x) := q12_1 ψ                -- ✱12·1
  have step : ∀ φ : V (Ty.pred1 a), QThm (imp (fiff ψ χ) (imp (fiff ψ fun x => .app1 φ x) (R φ))) :=
    fun φ =>
      let K := QF.and (fiff ψ χ) (fiff ψ fun x => .app1 φ x)
      have k1 : QThm (imp K (P φ)) := qsyl (QL.t3_27 _ _) (qiffMp (q10_32 _ _))  -- ✱10·32
      have k2 : QThm (imp K (fiff (fun x => .app1 φ x) χ)) :=
        qsyl (q10_321 ψ χ fun x => .app1 φ x) (qiffMp (q10_32 _ _))              -- ✱10·321
      have k3 : QThm (imp (fiff (fun x => .app1 φ x) χ) (cls χ fun θ => ident φ θ)) :=
        qsyl (QThm.mp (q13_15 φ) (QThm.mp (QL.t3_2 _ _) (QL.t2_04 _ _ _)))       -- ✱3·2 . ✱13·15
          (q10_24 (fun θ => QF.and (fiff (fun x => .app1 θ x) χ) (ident φ θ)) φ) -- ✱10·24 [✱13·195]
      QThm.mp (qcomp k1 (qsyl k2 k3)) (QL.t3_3 _ _ _)                            -- Comp . Exp
  have h2 := qsyl (q10_11_21 step) (q10_28 _ R)                                  -- ✱10·11·21·28
  QThm.mp h1 (QThm.mp h2 (QL.t2_04 _ _ _))                                       -- (1).(2)

/-- ✱20·14 `⊢ :. ẑ(ψz) = ẑ(χz) . ⊃ : ψx . ≡ₓ . χx`. ✱13·195 needs `θ = φ . F θ` where ✱20·01 gives
    `F θ : φ = θ`; the factors are commuted (✱4·3) and φ = θ turned by ✱13·16 (with ✱4·36), under (∃θ)
    by ✱10·11·281. Then ✱10·321 (PM: ✱10·322, for PM's orientation ψx ≡ₓ φ!x) inside (∃φ) and ✱10·23. -/
theorem q20_14 (ψ χ : V a → QF V) : QThm (imp (clsEq ψ χ) (fiff ψ χ)) :=
  let P : V (Ty.pred1 a) → QF V := fun φ => fiff (fun x => .app1 φ x) ψ
  let Q : V (Ty.pred1 a) → QF V := fun θ => fiff (fun x => .app1 θ x) χ
  have j : ∀ φ : V (Ty.pred1 a), QThm (iff (cls χ fun θ => ident φ θ) (Q φ)) := fun φ =>
    qiffTrans (q10_11_281 fun θ =>
        qiffTrans (QL.t4_3 (Q θ) (ident φ θ)) (QThm.mp (q13_16 φ θ) (QL.t4_36 _ _ _)))  -- ✱20·1 . ✱13·16
      (q13_195 Q φ)                                                              -- [✱13·195]
  have k : ∀ φ : V (Ty.pred1 a), QThm (imp (QF.and (P φ) (cls χ fun θ => ident φ θ)) (fiff ψ χ)) :=
    fun φ => qsyl (qandR (qiffMp (j φ))) (q10_321 (fun x => .app1 φ x) ψ χ)    -- [✱10·322]
  QThm.mp (q10_11 k) (qiffMp (q10_23 _ _))                                       -- ✱10·11·23

/-- ✱20·15 `⊢ :. ψx . ≡ₓ . χx : ≡ . ẑ(ψz) = ẑ(χz)` [✱20·13·14]. "Two functions determine the same class
    when, and only when, they are formally equivalent" (p. 201). -/
theorem q20_15 (ψ χ : V a → QF V) : QThm (iff (fiff ψ χ) (clsEq ψ χ)) :=
  qiffI (q20_13 ψ χ) (q20_14 ψ χ)

/-- ✱20·3 `⊢ : x ∈ ẑ(ψz) . ≡ . ψx`. PM's lines have ψy ≡_y φ!y; ✱20·01 gives φ!y ≡_y ψy, so ✱12·1 is
    turned by ✱10·32 (under (∃φ), ✱10·11·281). ✱10·35 is used with p as the second factor
    (`qex_and_perm`, ✱4·3), and "[✱12·1]" drops the asserted factor by ✱3·27 and ✱3·2. -/
theorem q20_3 (ψ : V a → QF V) (x : V a) : QThm (iff (cls ψ fun φ => mem x φ) (ψ x)) :=
  let P : V (Ty.pred1 a) → QF V := fun φ => fiff (fun y => .app1 φ y) ψ
  have h1 := q10_11_281 fun φ => q10_43 (fun y => .app1 φ y) ψ x                 -- ✱20·1 . (✱20·02) . [✱10·43]
  have h2 := qex_and_perm P (ψ x)                                                -- [✱10·35]
  have h3 : QThm (ex P) := QThm.mp (q12_1 ψ) (qiffMp (q10_11_281 fun φ => q10_32 ψ fun y => .app1 φ y))
  qiffTrans h1 (qiffTrans h2 (qand_true_left h3))                                -- [✱12·1]

/-! ## Typical ambiguity (docs/TYPES_DESIGN.md, test F5)

  One Lean theorem is used at several types: ✱13·15 and ✱13·101 at individuals, at predicative
  functions of individuals, and at predicative functions of those. -/

example {V : Ty → Type} (x : V .ind) (φ : V (Ty.pred1 .ind)) (f : V (Ty.pred1 (Ty.pred1 .ind))) :
    QThm (ident x x) ∧ QThm (ident φ φ) ∧ QThm (ident f f) :=
  ⟨q13_15 x, q13_15 φ, q13_15 f⟩

example {V : Ty → Type} (x y : V .ind) (φ θ : V (Ty.pred1 .ind)) (ψ : V .ind → QF V)
    (χ : V (Ty.pred1 .ind) → QF V) :
    QThm (imp (ident x y) (imp (ψ x) (ψ y))) ∧ QThm (imp (ident φ θ) (imp (χ φ) (χ θ))) :=
  ⟨q13_101 ψ x y, q13_101 χ φ θ⟩

end PM
