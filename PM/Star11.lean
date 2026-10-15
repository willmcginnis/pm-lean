import PM.Star10
import PM.Chain
import PM.Models.Finite
/-!
  ✱11: theory of two apparent variables (1910 print, pp. 157–167; summary pp. 157–158, numbered
  propositions pp. 159–167), in ✱10's alternative method (PM/Quant.lean).

  Statements are read from the scans. Each proof follows PM's Dem. line by line where PM prints one,
  or, where PM prints only a bracketed hint, uses the hinted propositions in PM's order; the comment
  on each Lean line gives PM's line or hint. `data/star11_ledger.json` records, per proposition,
  which cited propositions are used and which further ones were needed.

  Definitions. ✱11·01–✱11·06 are macros (`QF.all2`, `QF.all3`, `QF.ex2`, `QF.ex3`, `QF.fimp2`,
  `QF.fiff2`), so "(x, y) . φ(x, y)" is literally "(x) : (y) . φ(x, y)", as ✱11·01 says. The two
  variables may have different types (`x : V σ`, `y : V τ`), which ✱12 onward uses for function types.

  Steps done silently, as in PM/Star10.lean and PM/Replay2.lean (the ones PM leaves tacit everywhere):
  - joining two lines by ✱3·2 (or ✱4·01 for "≡"), and chaining "⊃" or "≡" lines (Syll, ✱4·22; a
    displayed chain is a `calc` block, PM/Chain.lean);
  - reading an equivalence from right to left (✱4·21);
  - reading a definition (✱1·01, ✱3·01, ✱4·01, ✱10·01–✱10·03, ✱11·01–✱11·06), which is definitional;
  - ✱10·11 before ✱10·27, ✱10·271, ✱10·28, ✱10·281, and the use of one of these to carry a ✱10
    proposition under the outer variable: PM states this pattern on pp. 161–162 ("the analogous
    proposition in ✱10 is used twice, together with ✱10·27 or ✱10·271 or ✱10·28 or ✱10·281 as the case
    may be") and then gives only the references.
  Any other proposition a proof needs is named in its docstring and listed as `extra_used` in the ledger.

  Real variables. As in ✱10, propositions whose proofs pass through ✱10·33, ✱10·34 or ✱10·37 take real
  variables z, w for the variables PM's proof uses (in an empty type they can fail).

  Names: `q11_1` is ✱11·1, and so on. φ, ψ, χ, θ are functions of one or two variables; p is a formula.
-/
namespace PM
open QF

namespace QF
variable {V : Ty → Type} {S : Sys V}
/-- ✱11·01 `(x, y) . φ(x, y) . = : (x) : (y) . φ(x, y)` Df -/
@[reducible] def all2 {σ τ : Ty} (φ : V σ → V τ → QF V) : QF V := .all fun x => .all fun y => φ x y
/-- ✱11·02 `(x, y, z) . φ(x, y, z) . = : (x) : (y, z) . φ(x, y, z)` Df -/
@[reducible] def all3 {ρ σ τ : Ty} (φ : V ρ → V σ → V τ → QF V) : QF V :=
  .all fun x => all2 fun y z => φ x y z
/-- ✱11·03 `(∃x, y) . φ(x, y) . = : (∃x) : (∃y) . φ(x, y)` Df -/
@[reducible] def ex2 {σ τ : Ty} (φ : V σ → V τ → QF V) : QF V := ex fun x => ex fun y => φ x y
/-- ✱11·04 `(∃x, y, z) . φ(x, y, z) . = : (∃x) : (∃y, z) . φ(x, y, z)` Df -/
@[reducible] def ex3 {ρ σ τ : Ty} (φ : V ρ → V σ → V τ → QF V) : QF V :=
  ex fun x => ex2 fun y z => φ x y z
/-- ✱11·05 `φ(x, y) . ⊃_{x,y} . ψ(x, y) : = : (x, y) : φ(x, y) . ⊃ . ψ(x, y)` Df -/
@[reducible] def fimp2 {σ τ : Ty} (φ ψ : V σ → V τ → QF V) : QF V := all2 fun x y => imp (φ x y) (ψ x y)
/-- ✱11·06 `φ(x, y) . ≡_{x,y} . ψ(x, y) : = : (x, y) : φ(x, y) . ≡ . ψ(x, y)` Df -/
@[reducible] def fiff2 {σ τ : Ty} (φ ψ : V σ → V τ → QF V) : QF V := all2 fun x y => iff (φ x y) (ψ x y)
end QF

variable {V : Ty → Type} {S : Sys V} {ρ σ τ : Ty}

/-! ## Compound citations and transformed forms of ✱10 propositions -/

/-- "✱10·11·28": from `⊢ . φx ⊃ ψx` for every x, infer `⊢ : (∃x) . φx . ⊃ . (∃x) . ψx`. -/
theorem q10_11_28 {φ ψ : V τ → QF V} (h : ∀ x, QThm S (imp (φ x) (ψ x))) : QThm S (imp (ex φ) (ex ψ)) :=
  QThm.mp (q10_11 h) (q10_28 φ ψ)
/-- "✱10·11·281": from `⊢ . φx ≡ ψx` for every x, infer `⊢ : (∃x) . φx . ≡ . (∃x) . ψx`. -/
theorem q10_11_281 {φ ψ : V τ → QF V} (h : ∀ x, QThm S (iff (φ x) (ψ x))) : QThm S (iff (ex φ) (ex ψ)) :=
  QThm.mp (q10_11 h) (q10_281 φ ψ)

/-- ✱10·252 . Transp: `(∃x) . φx . ≡ . ∼{(x) . ∼φx}`. ✱10·252 (`∼(∃x) . φx . ≡ . (x) . ∼φx`) is
    transposed by ✱4·12. (By ✱10·01 the two sides are the same formula in Lean; this follows PM's
    citation instead of reading the definition.) -/
theorem qex_transp (φ : V τ → QF V) : QThm S (iff (ex φ) (.neg (.all fun x => .neg (φ x)))) :=
  QThm.mp (qiffSymm (q10_252 φ)) (qiffMp (QL.t4_12 (.all fun x => .neg (φ x)) (ex φ)))

/-- ✱10·2 with the disjuncts permuted by ✱4·31: `(x) . φx ∨ p . ≡ : (x) . φx . ∨ . p`. -/
theorem qall_or_perm (φ : V τ → QF V) (p : QF V) :
    QThm S (iff (.all fun x => .or (φ x) p) (.or (.all φ) p)) :=
  qiffTrans (q10_11_271 fun x => QL.t4_31 (φ x) p) (qiffTrans (q10_2 p φ) (QL.t4_31 p (.all φ)))

/-- ✱10·33 with the factors commuted by ✱4·3: `(x) : p . φx : ≡ : p : (x) . φx` (real variable y, as
    in ✱10·33). -/
theorem qall_and_perm (φ : V τ → QF V) (p : QF V) (y : V τ) :
    QThm S (iff (.all fun x => QF.and p (φ x)) (QF.and p (.all φ))) :=
  qiffTrans (q10_11_271 fun x => QL.t4_3 p (φ x)) (qiffTrans (q10_33 φ p y) (QL.t4_3 (.all φ) p))

/-- ✱10·35 with the factors commuted by ✱4·3: `(∃x) . φx . p . ≡ : (∃x) . φx : p`. -/
theorem qex_and_perm (φ : V τ → QF V) (p : QF V) :
    QThm S (iff (ex fun x => QF.and (φ x) p) (QF.and (ex φ) p)) :=
  qiffTrans (q10_11_281 fun x => QL.t4_3 (φ x) p) (qiffTrans (q10_35 φ p) (QL.t4_3 p (ex φ)))

/-- From `⊢ . f ⊃ e` and `⊢ . e' ⊃ f'`, `⊢ : e ⊃ e' . ⊃ . f ⊃ f'` (Syll, ✱2·05 and ✱2·06): replacing
    the antecedent and consequent of an implication. -/
theorem qimpCongr {e e' f f' : QF V} (h1 : QThm S (imp f e)) (h2 : QThm S (imp e' f')) :
    QThm S (imp (imp e e') (imp f f')) :=
  qsyl (QThm.mp h2 (QL.t2_05 e e' f')) (QThm.mp h1 (QL.t2_06 f e f'))

/-! ## ✱11·07–✱11·14 -/

/-- ✱11·1 `⊢ : (x, y) . φ(x, y) . ⊃ . φ(z, w)` -/
theorem q11_1 (φ : V σ → V τ → QF V) (z : V σ) (w : V τ) : QThm S (imp (all2 φ) (φ z w)) :=
  qsyl (q10_1 (fun x => .all (φ x)) z)                                         -- ✱10·1: Hp ⊃ (y) . φ(z, y)
    (q10_1 (φ z) w)                                                             -- [✱10·1] ⊃ φ(z, w)

/-- ✱11·07 "'Whatever possible argument x may be, φ(x, y) is true whatever possible argument y may
    be' implies the corresponding statement with x and y interchanged." PM takes it as a primitive
    proposition (p. 159; p. 158 says it is needed "in addition to the definition ✱11·01"). In the
    alternative method as formalized here it is derivable, so it is proved, not assumed: ✱11·1 gives
    φ(x, y) for real x, y, and ✱10·11 (a rule about real variables) may turn them into apparent
    variables in either order. -/
theorem q11_07 {φ : V σ → V τ → QF V} (h : QThm S (all2 φ)) : QThm S (all2 fun y x => φ x y) :=
  q10_11 fun y => q10_11 fun x => QThm.mp h (q11_1 φ x y)

/-- ✱11·11 "If φ(z, w) is true whatever possible arguments z and w may be, then (x, y) . φ(x, y) is
    true." PM's Dem.: ✱10·11 twice. -/
theorem q11_11 {φ : V σ → V τ → QF V} (h : ∀ z w, QThm S (φ z w)) : QThm S (all2 φ) :=
  q10_11 fun z => q10_11 fun w => h z w

/-- ✱11·12 `⊢ :. (x, y) . p ∨ φ(x, y) . ⊃ : p . ∨ . (x, y) . φ(x, y)` -/
theorem q11_12 (p : QF V) (φ : V σ → V τ → QF V) :
    QThm S (imp (all2 fun x y => .or p (φ x y)) (.or p (all2 φ))) :=
  qsyl (q10_11_27 fun x => q10_12 p (φ x))                                     -- ✱10·12 [✱10·11·27]
    (q10_12 p fun x => .all (φ x))                                              -- [✱10·12]

/-- ✱11·13 "If φ(x̂, ŷ), ψ(x̂, ŷ) take their first and second arguments respectively of the same type,
    and we have ⊢ . φ(x, y) and ⊢ . ψ(x, y), we shall have ⊢ . φ(x, y) . ψ(x, y)." [Proof as in ✱10·13] -/
theorem q11_13 {φ ψ : V σ → V τ → QF V} (hφ : ∀ x y, QThm S (φ x y)) (hψ : ∀ x y, QThm S (ψ x y))
    (x : V σ) (y : V τ) : QThm S (QF.and (φ x y) (ψ x y)) :=
  q10_13 (hφ x y) (hψ x y)

/-- ✱11·14 `⊢ :. (x, y) . φ(x, y) : (x, y) . ψ(x, y) : ⊃ : φ(z, w) . ψ(z, w)` -/
theorem q11_14 (φ ψ : V σ → V τ → QF V) (z : V σ) (w : V τ) :
    QThm S (imp (QF.and (all2 φ) (all2 ψ)) (QF.and (φ z w) (ψ z w))) :=
  qsyl (q10_14 (fun x => .all (φ x)) (fun x => .all (ψ x)) z)                 -- ✱10·14: Hp ⊃ (y).φ(z,y) : (y).ψ(z,y)
    (q10_14 (φ z) (ψ z) w)                                                      -- [✱10·14]

/-! ## ✱11·2–✱11·27 -/

/-- ✱11·2 `⊢ : (x, y) . φ(x, y) . ≡ . (y, x) . φ(x, y)`. Line (3) is ✱11·12 with ∼{(x, y) . φ(x, y)}
    for p; "Similarly" (4) repeats (1)–(3) with the variables interchanged. -/
theorem q11_2 (φ : V σ → V τ → QF V) : QThm S (iff (all2 φ) (all2 fun y x => φ x y)) :=
  have h1 := q11_1 φ                                                            -- ✱11·1 (1)
  have h2 : QThm S (all2 fun w z => imp (all2 φ) (φ z w)) := q11_07 (q11_11 h1)   -- (1).✱11·07·11 (2)
  have h3 : QThm S (imp (all2 φ) (all2 fun w z => φ z w)) :=
    QThm.mp h2 (q11_12 (.neg (all2 φ)) fun w z => φ z w)                        -- (2).✱11·12 (3)
  have h4 : QThm S (imp (all2 fun w z => φ z w) (all2 φ)) :=
    QThm.mp (q11_07 (q11_11 (q11_1 fun w z => φ z w)))
      (q11_12 (.neg (all2 fun w z => φ z w)) φ)                                 -- Similarly (4)
  qiffI h3 h4                                                                   -- (3).(4)

/-- ✱11·21 `⊢ : (x, y, z) . φ(x, y, z) . ≡ . (y, z, x) . φ(x, y, z)` -/
theorem q11_21 (φ : V ρ → V σ → V τ → QF V) :
    QThm S (iff (all3 φ) (all3 fun y z x => φ x y z)) :=
  qiffTrans (q11_2 fun x y => .all (φ x y))                                     -- (✱11·01·02) [✱11·2]
    (q10_11_271 fun y => q11_2 fun x z => φ x y z)                              -- [✱11·2 . ✱10·271] (✱11·01·02)

/-- ✱11·22 `⊢ : (∃x, y) . φ(x, y) . ≡ . ∼{(x, y) . ∼φ(x, y)}`. The negation of the ✱10·271 equivalence
    is taken by ✱4·11, which PM leaves tacit (as in ✱10·34). -/
theorem q11_22 (φ : V σ → V τ → QF V) :
    QThm S (iff (ex2 φ) (.neg (all2 fun x y => .neg (φ x y)))) :=
  qiffTrans (qex_transp fun x => ex (φ x))                                      -- ✱10·252 . Transp . (✱11·03)
    (qiffNeg (q10_11_271 fun x => q10_252 (φ x)))                              -- [✱10·252·271] [(✱11·01)]

/-- ✱11·23 `⊢ : (∃x, y) . φ(x, y) . ≡ . (∃y, x) . φ(x, y)`. "Transp" is ✱4·11. -/
theorem q11_23 (φ : V σ → V τ → QF V) : QThm S (iff (ex2 φ) (ex2 fun y x => φ x y)) :=
  qiffTrans (q11_22 φ)                                                          -- ✱11·22
    (qiffTrans (qiffNeg (q11_2 fun x y => .neg (φ x y)))                       -- [✱11·2 . Transp]
      (qiffSymm (q11_22 fun y x => φ x y)))                                     -- [✱11·22]

/-- ✱11·24 `⊢ : (∃x, y, z) . φ(x, y, z) . ≡ . (∃y, z, x) . φ(x, y, z)` -/
theorem q11_24 (φ : V ρ → V σ → V τ → QF V) :
    QThm S (iff (ex3 φ) (ex3 fun y z x => φ x y z)) :=
  qiffTrans (q11_23 fun x y => ex (φ x y))                                      -- (✱11·03·04) [✱11·23]
    (q10_11_281 fun y => q11_23 fun x z => φ x y z)                             -- [✱11·23 . ✱10·281] (✱11·03·04)

/-- ✱11·25 `⊢ : ∼{(∃x, y) . φ(x, y)} . ≡ . (x, y) . ∼φ(x, y)` [✱11·22 . Transp]. "Transp" is ✱4·12. -/
theorem q11_25 (φ : V σ → V τ → QF V) :
    QThm S (iff (.neg (ex2 φ)) (all2 fun x y => .neg (φ x y))) :=
  qiffSymm (QThm.mp (q11_22 φ) (qiffMp (QL.t4_12 (ex2 φ) (all2 fun x y => .neg (φ x y)))))

/-- ✱11·26 `⊢ :. (∃x) : (y) . φ(x, y) : ⊃ : (y) : (∃x) . φ(x, y)`. Line (1), "✱10·1·28", applies ✱10·28
    to ✱10·1 turned into an apparent variable by ✱10·11 (tacit). PM notes (p. 161) that the converse
    is false; see `not_qthm_converse_11_26`. -/
theorem q11_26 (φ : V σ → V τ → QF V) :
    QThm S (imp (ex fun x => .all (φ x)) (.all fun y => ex fun x => φ x y)) :=
  have h1 : ∀ y, QThm S (imp (ex fun x => .all (φ x)) (ex fun x => φ x y)) := fun y =>
    QThm.mp (q10_11 fun x => q10_1 (φ x) y) (q10_28 (fun x => .all (φ x)) (fun x => φ x y))  -- ✱10·1·28 (1)
  q10_11_21 h1                                                                  -- (1).✱10·11·21

/-- ✱11·27 `⊢ :. (∃x, y) : (∃z) . φ(x, y, z) : ≡ : (∃x) : (∃y, z) . φ(x, y, z) : ≡ : (∃x, y, z) . φ(x, y, z)`.
    The chain "A ≡ B ≡ C" is stated as `A ≡ B . B ≡ C`. -/
theorem q11_27 (φ : V ρ → V σ → V τ → QF V) :
    QThm S (QF.and (iff (ex2 fun x y => ex (φ x y)) (ex fun x => ex2 (φ x)))
                 (iff (ex fun x => ex2 (φ x)) (ex3 φ))) :=
  have h1 : QThm S (iff (ex2 fun x y => ex (φ x y)) (ex fun x => ex fun y => ex (φ x y))) :=
    QL.t4_2 _                                                                   -- ✱4·2 . (✱11·03) (1)
  have h2 : ∀ x, QThm S (iff (ex fun y => ex (φ x y)) (ex2 (φ x))) :=
    fun x => QL.t4_2 (ex fun y => ex (φ x y))                                   -- ✱4·2 . (✱11·03) (2)
  have h3 := q10_11_281 h2                                                      -- (2).✱10·11·281 (3)
  qandI (qiffTrans h1 h3) (QL.t4_2 _)                                           -- (1).(3).(✱11·04)

/-! ## ✱11·3–✱11·401 -/

/-- ✱11·3 `⊢ :. p . ⊃ . (x, y) . φ(x, y) : ≡ : (x, y) : p . ⊃ . φ(x, y)` -/
theorem q11_3 (p : QF V) (φ : V σ → V τ → QF V) :
    QThm S (iff (imp p (all2 φ)) (all2 fun x y => imp p (φ x y))) :=
  qiffTrans (qiffSymm (q10_21 p fun x => .all (φ x)))                           -- ✱10·21
    (q10_11_271 fun x => qiffSymm (q10_21 p (φ x)))                            -- [✱10·21·271]

/-- ✱11·31 `⊢ :: (x, y) . φ(x, y) : (x, y) . ψ(x, y) : ≡ :. (x, y) : φ(x, y) . ψ(x, y)` -/
theorem q11_31 (φ ψ : V σ → V τ → QF V) :
    QThm S (iff (QF.and (all2 φ) (all2 ψ)) (all2 fun x y => QF.and (φ x y) (ψ x y))) :=
  qiffTrans (qiffSymm (q10_22 (fun x => .all (φ x)) (fun x => .all (ψ x))))    -- ✱10·22
    (q10_11_271 fun x => qiffSymm (q10_22 (φ x) (ψ x)))                        -- [✱10·22·271]

/-- ✱11·311 "If φ(x̂, ŷ), ψ(x̂, ŷ) take arguments of the same type, and we have ⊢ . φ(x, y) and
    ⊢ . ψ(x, y), we shall have ⊢ . φ(x, y) . ψ(x, y)." [Proof as in ✱10·13] (It repeats ✱11·13.) -/
theorem q11_311 {φ ψ : V σ → V τ → QF V} (hφ : ∀ x y, QThm S (φ x y)) (hψ : ∀ x y, QThm S (ψ x y))
    (x : V σ) (y : V τ) : QThm S (QF.and (φ x y) (ψ x y)) :=
  q10_13 (hφ x y) (hψ x y)

/-- ✱11·32 `⊢ :. (x, y) : φ(x, y) . ⊃ . ψ(x, y) : ⊃ : (x, y) . φ(x, y) . ⊃ . (x, y) . ψ(x, y)` [✱10·27] -/
theorem q11_32 (φ ψ : V σ → V τ → QF V) :
    QThm S (imp (fimp2 φ ψ) (imp (all2 φ) (all2 ψ))) :=
  qsyl (q10_11_27 fun x => q10_27 (φ x) (ψ x))                                 -- ✱10·27 (inner)
    (q10_27 (fun x => .all (φ x)) (fun x => .all (ψ x)))                       -- ✱10·27 (outer)

/-- ✱11·33 `⊢ :. (x, y) : φ(x, y) . ≡ . ψ(x, y) : ⊃ : (x, y) . φ(x, y) . ≡ . (x, y) . ψ(x, y)` [✱10·271].
    ✱10·271 is used twice; the inner use is carried under (x) by ✱10·11·27 (the pattern of p. 162). -/
theorem q11_33 (φ ψ : V σ → V τ → QF V) :
    QThm S (imp (fiff2 φ ψ) (iff (all2 φ) (all2 ψ))) :=
  qsyl (q10_11_27 fun x => q10_271 (φ x) (ψ x))                                -- ✱10·271 (inner)
    (q10_271 (fun x => .all (φ x)) (fun x => .all (ψ x)))                      -- ✱10·271 (outer)

/-- ✱11·34 `⊢ :. (x, y) : φ(x, y) . ⊃ . ψ(x, y) : ⊃ : (∃x, y) . φ(x, y) . ⊃ . (∃x, y) . ψ(x, y)` [✱10·27·28] -/
theorem q11_34 (φ ψ : V σ → V τ → QF V) :
    QThm S (imp (fimp2 φ ψ) (imp (ex2 φ) (ex2 ψ))) :=
  qsyl (q10_11_27 fun x => q10_28 (φ x) (ψ x))                                 -- ✱10·28 (inner), ✱10·27
    (q10_28 (fun x => ex (φ x)) (fun x => ex (ψ x)))                           -- ✱10·28 (outer)

/-- ✱11·341 `⊢ :. (x, y) : φ(x, y) . ≡ . ψ(x, y) : ⊃ : (∃x, y) . φ(x, y) . ≡ . (∃x, y) . ψ(x, y)`
    [✱10·271·281]. ✱10·281 is used twice. Carrying the inner use under (x) needs ✱10·27 (an implication
    under (x)), not the cited ✱10·271; compare ✱11·34's hint [✱10·27·28]. -/
theorem q11_341 (φ ψ : V σ → V τ → QF V) :
    QThm S (imp (fiff2 φ ψ) (iff (ex2 φ) (ex2 ψ))) :=
  qsyl (q10_11_27 fun x => q10_281 (φ x) (ψ x))                                -- ✱10·281 (inner), ✱10·27
    (q10_281 (fun x => ex (φ x)) (fun x => ex (ψ x)))                          -- ✱10·281 (outer)

/-- ✱11·35 `⊢ :. (x, y) : φ(x, y) . ⊃ . p : ≡ : (∃x, y) . φ(x, y) . ⊃ . p` [✱10·23·271] -/
theorem q11_35 (φ : V σ → V τ → QF V) (p : QF V) :
    QThm S (iff (all2 fun x y => imp (φ x y) p) (imp (ex2 φ) p)) :=
  qiffTrans (q10_11_271 fun x => q10_23 (φ x) p)                               -- ✱10·23 . ✱10·271
    (q10_23 (fun x => ex (φ x)) p)                                              -- ✱10·23

/-- ✱11·36 `⊢ : φ(z, w) . ⊃ . (∃x, y) . φ(x, y)`. (1).Transp (✱2·03) gives `φ(z, w) . ⊃ . ∼(x, y) . ∼φ(x, y)`;
    reading that as `(∃x, y) . φ(x, y)` needs ✱11·22, which PM leaves tacit (in Lean, ✱11·03 makes
    (∃x, y) . φ(x, y) the formula ∼(x) . ∼∼(y) . ∼φ(x, y), not ∼(x, y) . ∼φ(x, y)). -/
theorem q11_36 (φ : V σ → V τ → QF V) (z : V σ) (w : V τ) : QThm S (imp (φ z w) (ex2 φ)) :=
  have h1 := q11_1 (fun x y => .neg (φ x y)) z w                                -- ✱11·1 (1)
  qsyl (QThm.mp h1 (QL.t2_03 (all2 fun x y => .neg (φ x y)) (φ z w)))          -- (1).Transp
    (qiffMpr (q11_22 φ))                                                        -- ✱11·22

/-- ✱11·37 `⊢ :: (x, y) : φ(x, y) . ⊃ . ψ(x, y) :. (x, y) : ψ(x, y) . ⊃ . χ(x, y) :. ⊃ : (x, y) : φ(x, y) . ⊃ . χ(x, y)`.
    "Syll" in line (2) is ✱3·33. -/
theorem q11_37 (φ ψ χ : V σ → V τ → QF V) :
    QThm S (imp (QF.and (fimp2 φ ψ) (fimp2 ψ χ)) (fimp2 φ χ)) :=
  have h1 := qiffMp (q11_31 (fun x y => imp (φ x y) (ψ x y)) (fun x y => imp (ψ x y) (χ x y)))  -- ✱11·31 (1)
  have h2 := QThm.mp (q11_11 fun x y => QL.t3_33 (φ x y) (ψ x y) (χ x y))      -- Syll . ✱11·11
    (q11_32 (fun x y => QF.and (imp (φ x y) (ψ x y)) (imp (ψ x y) (χ x y)))
      (fun x y => imp (φ x y) (χ x y)))                                         -- [✱11·32] (2)
  qsyl h1 h2                                                                    -- (1).(2).Syll

/-- ✱11·371 `⊢ :: (x, y) : φ(x, y) . ≡ . ψ(x, y) :. (x, y) : ψ(x, y) . ≡ . χ(x, y) :. ⊃ :. (x, y) : φ(x, y) . ≡ . χ(x, y)`
    [✱11·31·11·33]. Done as ✱11·37, with ✱4·22 for Syll. The step from `(x, y) : A . ⊃ . B` to
    `(x, y) . A . ⊃ . (x, y) . B` is ✱11·32; the cited ✱11·33 (for "≡") does not give it. -/
theorem q11_371 (φ ψ χ : V σ → V τ → QF V) :
    QThm S (imp (QF.and (fiff2 φ ψ) (fiff2 ψ χ)) (fiff2 φ χ)) :=
  have h1 := qiffMp (q11_31 (fun x y => iff (φ x y) (ψ x y)) (fun x y => iff (ψ x y) (χ x y)))  -- ✱11·31
  have h2 := QThm.mp (q11_11 fun x y => QL.t4_22 (φ x y) (ψ x y) (χ x y))      -- ✱4·22 . ✱11·11
    (q11_32 (fun x y => QF.and (iff (φ x y) (ψ x y)) (iff (ψ x y) (χ x y)))
      (fun x y => iff (φ x y) (χ x y)))                                         -- ✱11·32
  qsyl h1 h2

/-- ✱11·38 `⊢ :: (x, y) : φ(x, y) . ⊃ . ψ(x, y) :. ⊃ :. (x, y) : φ(x, y) . χ(x, y) . ⊃ . ψ(x, y) . χ(x, y)`
    [Fact . ✱11·11·32] -/
theorem q11_38 (φ ψ χ : V σ → V τ → QF V) :
    QThm S (imp (fimp2 φ ψ)
      (fimp2 (fun x y => QF.and (φ x y) (χ x y)) (fun x y => QF.and (ψ x y) (χ x y)))) :=
  QThm.mp (q11_11 fun x y => QL.t3_45 (φ x y) (ψ x y) (χ x y))                 -- Fact . ✱11·11
    (q11_32 (fun x y => imp (φ x y) (ψ x y))
      (fun x y => imp (QF.and (φ x y) (χ x y)) (QF.and (ψ x y) (χ x y))))     -- ✱11·32

/-- ✱11·39 `⊢ :: (x, y) : φ(x, y) . ⊃ . ψ(x, y) :. (x, y) : χ(x, y) . ⊃ . θ(x, y) :. ⊃ :.
    (x, y) : φ(x, y) . χ(x, y) . ⊃ . ψ(x, y) . θ(x, y)` [✱3·47 . ✱11·11·32]. The two factors of the
    hypothesis are first combined by ✱11·31, which the hint omits (compare line (1) of ✱11·37). -/
theorem q11_39 (φ ψ χ θ : V σ → V τ → QF V) :
    QThm S (imp (QF.and (fimp2 φ ψ) (fimp2 χ θ))
      (fimp2 (fun x y => QF.and (φ x y) (χ x y)) (fun x y => QF.and (ψ x y) (θ x y)))) :=
  qsyl (qiffMp (q11_31 (fun x y => imp (φ x y) (ψ x y)) (fun x y => imp (χ x y) (θ x y))))  -- ✱11·31
    (QThm.mp (q11_11 fun x y => QL.t3_47 (φ x y) (χ x y) (ψ x y) (θ x y))     -- ✱3·47 . ✱11·11
      (q11_32 (fun x y => QF.and (imp (φ x y) (ψ x y)) (imp (χ x y) (θ x y)))
        (fun x y => imp (QF.and (φ x y) (χ x y)) (QF.and (ψ x y) (θ x y)))))  -- ✱11·32

/-- ✱11·391 `⊢ :: (x, y) : φ(x, y) . ⊃ . ψ(x, y) :. (x, y) : φ(x, y) . ⊃ . χ(x, y) :. ≡ :
    (x, y) : φ(x, y) . ⊃ . ψ(x, y) . χ(x, y)` -/
theorem q11_391 (φ ψ χ : V σ → V τ → QF V) :
    QThm S (iff (QF.and (fimp2 φ ψ) (fimp2 φ χ)) (fimp2 φ fun x y => QF.and (ψ x y) (χ x y))) :=
  have h2 := QThm.mp (q11_11 fun x y => QL.t4_76 (φ x y) (ψ x y) (χ x y))      -- ✱4·76 [✱11·11·33]
    (q11_33 (fun x y => QF.and (imp (φ x y) (ψ x y)) (imp (φ x y) (χ x y)))
      (fun x y => imp (φ x y) (QF.and (ψ x y) (χ x y))))
  qiffTrans (q11_31 (fun x y => imp (φ x y) (ψ x y)) (fun x y => imp (φ x y) (χ x y))) h2  -- [✱11·31]

/-- ✱11·4 `⊢ :: (x, y) : φ(x, y) . ≡ . ψ(x, y) :. (x, y) : χ(x, y) . ≡ . θ(x, y) :. ⊃ :.
    (x, y) : φ(x, y) . χ(x, y) . ≡ . ψ(x, y) . θ(x, y)` -/
theorem q11_4 (φ ψ χ θ : V σ → V τ → QF V) :
    QThm S (imp (QF.and (fiff2 φ ψ) (fiff2 χ θ))
      (fiff2 (fun x y => QF.and (φ x y) (χ x y)) (fun x y => QF.and (ψ x y) (θ x y)))) :=
  qsyl (qiffMp (q11_31 (fun x y => iff (φ x y) (ψ x y)) (fun x y => iff (χ x y) (θ x y))))  -- ✱11·31
    (QThm.mp (q11_11 fun x y => QL.t4_38 (φ x y) (χ x y) (ψ x y) (θ x y))     -- [✱4·38 . ✱11·11·32]
      (q11_32 (fun x y => QF.and (iff (φ x y) (ψ x y)) (iff (χ x y) (θ x y)))
        (fun x y => iff (QF.and (φ x y) (χ x y)) (QF.and (ψ x y) (θ x y)))))

/-- ✱11·401 `⊢ :: (x, y) : φ(x, y) . ≡ . ψ(x, y) : ⊃ :. (x, y) : φ(x, y) . χ(x, y) . ≡ . ψ(x, y) . χ(x, y)`
    [✱11·4 χ/θ . Id]. "Id" for `(x, y) : χ(x, y) . ≡ . χ(x, y)` is ✱4·2 generalized by ✱11·11. Dropping
    that asserted factor from the hypothesis uses Exp (✱3·3) and Comm (✱2·04), which PM leaves tacit. -/
theorem q11_401 (φ ψ χ : V σ → V τ → QF V) :
    QThm S (imp (fiff2 φ ψ)
      (fiff2 (fun x y => QF.and (φ x y) (χ x y)) (fun x y => QF.and (ψ x y) (χ x y)))) :=
  have h := q11_4 φ ψ χ χ                                                       -- ✱11·4 χ/θ
  have hid : QThm S (fiff2 χ χ) := q11_11 fun x y => QL.t4_2 (χ x y)              -- Id
  QThm.mp hid (QThm.mp (QThm.mp h (QL.t3_3 _ _ _)) (QL.t2_04 _ _ _))

/-! ## ✱11·41–✱11·47 -/

/-- ✱11·41 `⊢ :. (∃x, y) . φ(x, y) : ∨ : (∃x, y) . ψ(x, y) : ≡ : (∃x, y) : φ(x, y) . ∨ . ψ(x, y)` [✱10·42·281] -/
theorem q11_41 (φ ψ : V σ → V τ → QF V) :
    QThm S (iff (.or (ex2 φ) (ex2 ψ)) (ex2 fun x y => .or (φ x y) (ψ x y))) :=
  qiffTrans (q10_42 (fun x => ex (φ x)) (fun x => ex (ψ x)))                   -- ✱10·42 (outer)
    (q10_11_281 fun x => q10_42 (φ x) (ψ x))                                    -- ✱10·42 (inner) . ✱10·281

/-- ✱11·42 `⊢ :. (∃x, y) . φ(x, y) . ψ(x, y) . ⊃ : (∃x, y) . φ(x, y) : (∃x, y) . ψ(x, y)` [✱10·5] -/
theorem q11_42 (φ ψ : V σ → V τ → QF V) :
    QThm S (imp (ex2 fun x y => QF.and (φ x y) (ψ x y)) (QF.and (ex2 φ) (ex2 ψ))) :=
  qsyl (q10_11_28 fun x => q10_5 (φ x) (ψ x))                                   -- ✱10·5 (inner) . ✱10·28
    (q10_5 (fun x => ex (φ x)) (fun x => ex (ψ x)))                             -- ✱10·5 (outer)

/-- ✱11·421 `⊢ :. (x, y) . φ(x, y) . ∨ . (x, y) . ψ(x, y) : ⊃ : (x, y) : φ(x, y) . ∨ . ψ(x, y)`
    [✱11·42 ∼φ, ∼ψ/φ, ψ . Transp . ✱4·56]. Transp is ✱2·16. PM reads `∼(∃x, y) . ∼φ(x, y)` as
    `(x, y) . φ(x, y)` tacitly; in Lean that takes ✱11·25 and ✱4·13 (under ✱11·11·33), and on the left
    ✱4·51 and ✱4·39 to pass through the negated product. ✱4·56 is negated by ✱4·11. -/
theorem q11_421 (φ ψ : V σ → V τ → QF V) :
    QThm S (imp (.or (all2 φ) (all2 ψ)) (all2 fun x y => .or (φ x y) (ψ x y))) :=
  let nφ : V σ → V τ → QF V := fun x y => .neg (φ x y)
  let nψ : V σ → V τ → QF V := fun x y => .neg (ψ x y)
  have h1 := q11_42 nφ nψ                                                       -- ✱11·42 ∼φ, ∼ψ/φ, ψ
  have h2 := QThm.mp h1 (QL.t2_16 _ _)                                          -- Transp
  have dn : ∀ (χ : V σ → V τ → QF V), QThm S (iff (.neg (ex2 fun x y => .neg (χ x y))) (all2 χ)) :=
    fun χ => qiffTrans (q11_25 fun x y => .neg (χ x y))
      (QThm.mp (q11_11 fun x y => qiffSymm (QL.t4_13 (χ x y)))
        (q11_33 (fun x y => .neg (.neg (χ x y))) χ))
  have l : QThm S (imp (.or (all2 φ) (all2 ψ)) (.neg (QF.and (ex2 nφ) (ex2 nψ)))) :=
    qiffMpr (qiffTrans (QL.t4_51 (ex2 nφ) (ex2 nψ))
      (QThm.mp (qandI (dn φ) (dn ψ)) (QL.t4_39 _ _ _ _)))
  have r : QThm S (imp (.neg (ex2 fun x y => QF.and (nφ x y) (nψ x y)))
      (all2 fun x y => .or (φ x y) (ψ x y))) :=
    qiffMp (qiffTrans (q11_25 fun x y => QF.and (nφ x y) (nψ x y))
      (QThm.mp (q11_11 fun x y => qiffTrans (qiffNeg (QL.t4_56 (φ x y) (ψ x y)))  -- ✱4·56
          (qiffSymm (QL.t4_13 (.or (φ x y) (ψ x y)))))
        (q11_33 (fun x y => .neg (QF.and (nφ x y) (nψ x y))) (fun x y => .or (φ x y) (ψ x y)))))
  qsyl l (qsyl h2 r)

/-- ✱11·43 `⊢ :. (∃x, y) : φ(x, y) . ⊃ . p : ≡ : (x, y) . φ(x, y) . ⊃ . p` [✱10·34·281]. ✱10·34 takes a
    real variable, so this takes one of each type. -/
theorem q11_43 (φ : V σ → V τ → QF V) (p : QF V) (z : V σ) (w : V τ) :
    QThm S (iff (ex2 fun x y => imp (φ x y) p) (imp (all2 φ) p)) :=
  qiffTrans (q10_11_281 fun x => q10_34 (φ x) p w)                              -- ✱10·34 (inner) . ✱10·281
    (q10_34 (fun x => .all (φ x)) p z)                                          -- ✱10·34 (outer)

/-- ✱11·44 `⊢ :. (x, y) : φ(x, y) . ∨ . p : ≡ : (x, y) . φ(x, y) . ∨ . p` [✱10·2·271]. ✱10·2 has p as the
    first disjunct; both uses are permuted by ✱4·31 (`qall_or_perm`). -/
theorem q11_44 (φ : V σ → V τ → QF V) (p : QF V) :
    QThm S (iff (all2 fun x y => .or (φ x y) p) (.or (all2 φ) p)) :=
  qiffTrans (q10_11_271 fun x => qall_or_perm (φ x) p)                          -- ✱10·2 (inner) . ✱10·271
    (qall_or_perm (fun x => .all (φ x)) p)                                      -- ✱10·2 (outer)

/-- ✱11·45 `⊢ :. (∃x, y) : p . φ(x, y) : ≡ : p : (∃x, y) . φ(x, y)` [✱10·35·281] -/
theorem q11_45 (φ : V σ → V τ → QF V) (p : QF V) :
    QThm S (iff (ex2 fun x y => QF.and p (φ x y)) (QF.and p (ex2 φ))) :=
  qiffTrans (q10_11_281 fun x => q10_35 (φ x) p)                                -- ✱10·35 (inner) . ✱10·281
    (q10_35 (fun x => ex (φ x)) p)                                              -- ✱10·35 (outer)

/-- ✱11·46 `⊢ :. (∃x, y) : p . ⊃ . φ(x, y) : ≡ : p . ⊃ . (∃x, y) . φ(x, y)` [✱10·37·281]. ✱10·37 takes a
    real variable, so this takes one of each type. -/
theorem q11_46 (φ : V σ → V τ → QF V) (p : QF V) (z : V σ) (w : V τ) :
    QThm S (iff (ex2 fun x y => imp p (φ x y)) (imp p (ex2 φ))) :=
  qiffTrans (q10_11_281 fun x => q10_37 (φ x) p w)                              -- ✱10·37 (inner) . ✱10·281
    (q10_37 (fun x => ex (φ x)) p z)                                            -- ✱10·37 (outer)

/-- ✱11·47 `⊢ :. (x, y) : p . φ(x, y) : ≡ : p : (x, y) . φ(x, y)` [✱10·33·271]. ✱10·33 has p as the second
    factor; both uses are commuted by ✱4·3 (`qall_and_perm`). ✱10·33 takes a real variable. -/
theorem q11_47 (φ : V σ → V τ → QF V) (p : QF V) (z : V σ) (w : V τ) :
    QThm S (iff (all2 fun x y => QF.and p (φ x y)) (QF.and p (all2 φ))) :=
  qiffTrans (q10_11_271 fun x => qall_and_perm (φ x) p w)                       -- ✱10·33 (inner) . ✱10·271
    (qall_and_perm (fun x => .all (φ x)) p z)                                   -- ✱10·33 (outer)

/-! ## ✱11·5–✱11·59 -/

/-- ✱11·5 `⊢ :. (∃x) : ∼{(y) . φ(x, y)} : ≡ : ∼{(x, y) . φ(x, y)} : ≡ : (∃x, y) . ∼φ(x, y)`. The chain is
    stated as `A ≡ B . B ≡ C`; B ≡ C comes from (1) and (2) by ✱4·21 and ✱4·22 (tacit). -/
theorem q11_5 (φ : V σ → V τ → QF V) :
    QThm S (QF.and (iff (ex fun x => .neg (.all (φ x))) (.neg (all2 φ)))
                 (iff (.neg (all2 φ)) (ex2 fun x y => .neg (φ x y)))) :=
  have h1 : QThm S (iff (ex fun x => .neg (.all (φ x))) (.neg (all2 φ))) :=
    qiffSymm (q10_253 fun x => .all (φ x))                                      -- ✱10·253 [(✱11·01)] (1)
  have h2 : QThm S (iff (ex fun x => .neg (.all (φ x))) (ex2 fun x y => .neg (φ x y))) :=
    q10_11_281 fun x => q10_253 (φ x)                                           -- ✱10·253 [✱10·11·281] [(✱11·03)] (2)
  qandI h1 (qiffTrans (qiffSymm h1) h2)                                         -- (1).(2)

/-- ✱11·51 `⊢ :. (∃x) : (y) . φ(x, y) : ≡ : ∼{(x) : (∃y) . ∼φ(x, y)}`. The second "Transp" is ✱4·11. -/
theorem q11_51 (φ : V σ → V τ → QF V) :
    QThm S (iff (ex fun x => .all (φ x)) (.neg (.all fun x => ex fun y => .neg (φ x y)))) :=
  have h1 := qex_transp fun x => .all (φ x)                                     -- ✱10·252 . Transp (1)
  have h2 := qiffNeg (q10_11_271 fun x => q10_253 (φ x))                       -- ✱10·253 [✱10·11·271] [Transp] (2)
  qiffTrans h1 h2                                                               -- (1).(2)

/-- ✱11·52 `⊢ :. (∃x, y) . φ(x, y) . ψ(x, y) . ≡ . ∼{(x, y) : φ(x, y) . ⊃ . ∼ψ(x, y)}`. "Transp" is ✱4·11. -/
theorem q11_52 (φ ψ : V σ → V τ → QF V) :
    QThm S (iff (ex2 fun x y => QF.and (φ x y) (ψ x y)) (.neg (fimp2 φ fun x y => .neg (ψ x y)))) :=
  have h1 : ∀ x y, QThm S (iff (.neg (QF.and (φ x y) (ψ x y))) (imp (φ x y) (.neg (ψ x y)))) :=
    fun x y => qiffTrans (QL.t4_51 (φ x y) (ψ x y))
      (qiffSymm (QL.t4_62 (φ x y) (ψ x y)))                                     -- ✱4·51·62 (1)
  have h2 := QThm.mp (q11_11 h1)
    (q11_33 (fun x y => .neg (QF.and (φ x y) (ψ x y))) (fun x y => imp (φ x y) (.neg (ψ x y))))  -- (1).✱11·11·33 (2)
  qiffTrans (q11_22 fun x y => QF.and (φ x y) (ψ x y)) (qiffNeg h2)            -- (2).Transp.✱11·22

/-- ✱11·521 `⊢ :. ∼(∃x, y) . φ(x, y) . ∼ψ(x, y) . ≡ : (x, y) : φ(x, y) . ⊃ . ψ(x, y)`
    [✱11·52 . Transp . ∼ψ(x, y)/ψ(x, y)]. Transp is ✱4·12. The substitution gives `φ(x, y) . ⊃ . ∼∼ψ(x, y)`;
    PM drops the double negation tacitly. Here it is removed by ✱2·14, ✱2·12 and ✱2·05 under ✱11·11·33. -/
theorem q11_521 (φ ψ : V σ → V τ → QF V) :
    QThm S (iff (.neg (ex2 fun x y => QF.and (φ x y) (.neg (ψ x y)))) (fimp2 φ ψ)) :=
  let E : QF V := ex2 fun x y => QF.and (φ x y) (.neg (ψ x y))
  let F : QF V := fimp2 φ fun x y => .neg (.neg (ψ x y))
  have h1 : QThm S (iff E (.neg F)) := q11_52 φ fun x y => .neg (ψ x y)          -- ✱11·52 ∼ψ/ψ
  have h2 : QThm S (iff (.neg E) F) := qiffSymm (QThm.mp h1 (qiffMp (QL.t4_12 E F)))  -- Transp
  have h3 : ∀ x y, QThm S (iff (imp (φ x y) (.neg (.neg (ψ x y)))) (imp (φ x y) (ψ x y))) := fun x y =>
    qiffI (QThm.mp (QL.t2_14 (ψ x y)) (QL.t2_05 (φ x y) _ _))
      (QThm.mp (QL.t2_12 (ψ x y)) (QL.t2_05 (φ x y) _ _))
  qiffTrans h2 (QThm.mp (q11_11 h3)
    (q11_33 (fun x y => imp (φ x y) (.neg (.neg (ψ x y)))) (fun x y => imp (φ x y) (ψ x y))))

/-- ✱11·53 `⊢ :. (x, y) . φx ⊃ ψy . ≡ : (∃x) . φx . ⊃ . (y) . ψy` -/
theorem q11_53 (φ : V σ → QF V) (ψ : V τ → QF V) :
    QThm S (iff (all2 fun x y => imp (φ x) (ψ y)) (imp (ex φ) (.all ψ))) :=
  qiffTrans (q10_11_271 fun x => q10_21 (φ x) ψ)                                -- ✱10·21·271
    (q10_23 φ (.all ψ))                                                         -- [✱10·23]

/-- ✱11·54 `⊢ :. (∃x, y) . φx . ψy . ≡ : (∃x) . φx : (∃y) . ψy`. In the last line ✱10·35 is needed with p
    as the second factor; it is commuted by ✱4·3 (`qex_and_perm`). -/
theorem q11_54 (φ : V σ → QF V) (ψ : V τ → QF V) :
    QThm S (iff (ex2 fun x y => QF.and (φ x) (ψ y)) (QF.and (ex φ) (ex ψ))) :=
  qiffTrans (q10_11_281 fun x => q10_35 ψ (φ x))                                -- ✱10·35 [✱10·11·281]
    (qex_and_perm φ (ex ψ))                                                     -- [✱10·35]

/-- ✱11·55 `⊢ :. (∃x, y) . φx . ψ(x, y) . ≡ : (∃x) : φx : (∃y) . ψ(x, y)` -/
theorem q11_55 (φ : V σ → QF V) (ψ : V σ → V τ → QF V) :
    QThm S (iff (ex2 fun x y => QF.and (φ x) (ψ x y)) (ex fun x => QF.and (φ x) (ex (ψ x)))) :=
  have h1 := fun x => q10_35 (ψ x) (φ x)                                        -- ✱10·35
  have h2 := q10_11 h1                                                          -- [✱10·11]
  QThm.mp h2 (q10_281 (fun x => ex fun y => QF.and (φ x) (ψ x y))
    (fun x => QF.and (φ x) (ex (ψ x))))                                         -- [✱10·281]

/-- ✱11·56 `⊢ :. (x) . φx : (y) . ψy : ≡ : (x, y) . φx . ψy`. In the second ✱10·33 line p is the first
    factor; it is commuted by ✱4·3 (`qall_and_perm`). ✱10·33 takes a real variable, so this takes one
    of each type. -/
theorem q11_56 (φ : V σ → QF V) (ψ : V τ → QF V) (z : V σ) (w : V τ) :
    QThm S (iff (QF.and (.all φ) (.all ψ)) (all2 fun x y => QF.and (φ x) (ψ y))) :=
  have h1 := qiffSymm (q10_33 φ (.all ψ) z)                                     -- ✱10·33 (1)
  have l := fun x => qiffSymm (qall_and_perm ψ (φ x) w)                         -- ✱10·33
  have h2 := QThm.mp (q10_11 l)                                                 -- [✱10·11]
    (q10_271 (fun x => QF.and (φ x) (.all ψ)) (fun x => .all fun y => QF.and (φ x) (ψ y)))  -- [✱10·271] (2)
  qiffTrans h1 h2                                                               -- (1).(2)

/-- ✱11·57 `⊢ : (x) . φx . ≡ . (x, y) . φx . φy` [✱11·56 . ✱4·24]. PM: "The use of ✱4·24 here depends upon
    the fact that (x) . φx and (y) . φy are the same proposition"; in Lean they are the same term.
    Real variable z as in ✱11·56. -/
theorem q11_57 (φ : V τ → QF V) (z : V τ) :
    QThm S (iff (.all φ) (all2 fun x y => QF.and (φ x) (φ y))) :=
  qiffTrans (QL.t4_24 (.all φ)) (q11_56 φ φ z z)

/-- ✱11·58 `⊢ : (∃x) . φx . ≡ . (∃x, y) . φx . φy` [✱11·54 . ✱4·24] -/
theorem q11_58 (φ : V τ → QF V) : QThm S (iff (ex φ) (ex2 fun x y => QF.and (φ x) (φ y))) :=
  qiffTrans (QL.t4_24 (ex φ)) (qiffSymm (q11_54 φ φ))

/-- ✱11·59 `⊢ :. φx . ⊃ₓ . ψx : ≡ : φx . φy . ⊃_{x,y} . ψx . ψy`. Line (3) replaces φx . φx and ψx . ψx
    by φx and ψx using the two halves of ✱4·24 and Syll (`qimpCongr`). Real variable z as in ✱11·57. -/
theorem q11_59 (φ ψ : V τ → QF V) (z : V τ) :
    QThm S (iff (fimp φ ψ) (fimp2 (fun x y => QF.and (φ x) (φ y)) (fun x y => QF.and (ψ x) (ψ y)))) :=
  let H : QF V := fimp2 (fun x y => QF.and (φ x) (φ y)) (fun x y => QF.and (ψ x) (ψ y))
  have h1 : QThm S (imp (fimp φ ψ) H) :=
    qsyl (qiffMp (q11_57 (fun x => imp (φ x) (ψ x)) z))                         -- ✱11·57
      (QThm.mp (q11_11 fun x y => QL.t3_47 (φ x) (φ y) (ψ x) (ψ y))             -- [✱3·47 . ✱11·32] (1)
        (q11_32 (fun x y => QF.and (imp (φ x) (ψ x)) (imp (φ y) (ψ y)))
          (fun x y => imp (QF.and (φ x) (φ y)) (QF.and (ψ x) (ψ y)))))
  have h2 := q11_1 (fun x y => imp (QF.and (φ x) (φ y)) (QF.and (ψ x) (ψ y)))  -- ✱11·1 (2)
  have h3 : ∀ x, QThm S (imp H (imp (φ x) (ψ x))) := fun x =>
    qsyl (h2 x x) (qimpCongr (qiffMp (QL.t4_24 (φ x))) (qiffMpr (QL.t4_24 (ψ x))))  -- (2) x/y . ✱4·24 (3)
  have h4 : QThm S (imp H (fimp φ ψ)) := q10_11_21 h3                             -- (3).✱10·11·21 (4)
  qiffI h1 h4                                                                   -- (1).(4)

/-! ## ✱11·6–✱11·71 -/

/-- ✱11·6 `⊢ :: (∃x) :. (∃y) . φ(x, y) . ψy : χx :. ≡ :. (∃y) :. (∃x) . φ(x, y) . χx : ψy`. ✱10·35 is
    needed with p (χx, ψy) as the second factor: commuted by ✱4·3 (`qex_and_perm`). "Perm" in line 4
    is the rearrangement `φ . ψ . χ ≡ φ . χ . ψ` of a product, done by ✱4·32, ✱4·38 (with ✱4·2, ✱4·3)
    and ✱4·32 again. -/
theorem q11_6 (φ : V σ → V τ → QF V) (ψ : V τ → QF V) (χ : V σ → QF V) :
    QThm S (iff (ex fun x => QF.and (ex fun y => QF.and (φ x y) (ψ y)) (χ x))
              (ex fun y => QF.and (ex fun x => QF.and (φ x y) (χ x)) (ψ y))) :=
  have h1 := fun x => qiffSymm (qex_and_perm (fun y => QF.and (φ x y) (ψ y)) (χ x))  -- ✱10·35
  have h2 := q10_11_281 h1                                                      -- [✱10·11·281]
  have h3 := q11_23 fun x y => QF.and (QF.and (φ x y) (ψ y)) (χ x)              -- [✱11·23]
  have hp : ∀ y x, QThm S (iff (QF.and (QF.and (φ x y) (ψ y)) (χ x)) (QF.and (QF.and (φ x y) (χ x)) (ψ y))) :=
    fun y x => qiffTrans (QL.t4_32 _ _ _)
      (qiffTrans (QThm.mp (qandI (QL.t4_2 (φ x y)) (QL.t4_3 (ψ y) (χ x))) (QL.t4_38 _ _ _ _))
        (qiffSymm (QL.t4_32 _ _ _)))
  have h4 := QThm.mp (q11_11 hp)
    (q11_341 (fun y x => QF.and (QF.and (φ x y) (ψ y)) (χ x))
      (fun y x => QF.and (QF.and (φ x y) (χ x)) (ψ y)))                         -- [✱11·341 . Perm]
  have h5 := q10_11_281 fun y => qex_and_perm (fun x => QF.and (φ x y) (χ x)) (ψ y)  -- [✱10·35·281]
  qiffTrans h2 (qiffTrans h3 (qiffTrans h4 h5))

/-- ✱11·61 `⊢ :. (∃y) : φx . ⊃ₓ . ψ(x, y) : ⊃ : φx . ⊃ₓ . (∃y) . ψ(x, y)`. ✱10·37 takes a real variable,
    so this takes one (w). -/
theorem q11_61 (φ : V σ → QF V) (ψ : V σ → V τ → QF V) (w : V τ) :
    QThm S (imp (ex fun y => fimp φ fun x => ψ x y) (fimp φ fun x => ex (ψ x))) :=
  have h1 := q11_26 fun y x => imp (φ x) (ψ x y)                                -- ✱11·26 (1)
  have h2 := q10_11_27 fun x => qiffMp (q10_37 (ψ x) (φ x) w)                   -- ✱10·37 [✱10·11·27] (2)
  qsyl h1 h2                                                                    -- (1).(2)

/-- ✱11·62 `⊢ :: φx . ψ(x, y) . ⊃_{x,y} . χ(x, y) : ≡ :. φx . ⊃ₓ : ψ(x, y) . ⊃_y . χ(x, y)`. The first of the
    three equivalences that make up ✱4·87 is taken by ✱3·26 (twice). -/
theorem q11_62 (φ : V σ → QF V) (ψ χ : V σ → V τ → QF V) :
    QThm S (iff (fimp2 (fun x y => QF.and (φ x) (ψ x y)) χ) (fimp φ fun x => fimp (ψ x) (χ x))) :=
  have h1 := QThm.mp (q11_11 fun x y =>
      QThm.mp (QThm.mp (QL.t4_87 (φ x) (ψ x y) (χ x y)) (QL.t3_26 _ _)) (QL.t3_26 _ _))  -- ✱4·87 . ✱11·11
    (q11_33 (fun x y => imp (QF.and (φ x) (ψ x y)) (χ x y))
      (fun x y => imp (φ x) (imp (ψ x y) (χ x y))))                             -- ✱11·33
  qiffTrans h1 (q10_11_271 fun x => q10_21 (φ x) fun y => imp (ψ x y) (χ x y))  -- [✱10·21·11·271]

/-- ✱11·63 `⊢ :. ∼(∃x, y) . φ(x, y) . ⊃ : φ(x, y) . ⊃_{x,y} . ψ(x, y)` -/
theorem q11_63 (φ ψ : V σ → V τ → QF V) : QThm S (imp (.neg (ex2 φ)) (fimp2 φ ψ)) :=
  have h := QThm.mp (q11_11 fun x y => QL.t2_21 (φ x y) (ψ x y))               -- ✱2·21 . ✱11·11
    (q11_32 (fun x y => .neg (φ x y)) (fun x y => imp (φ x y) (ψ x y)))        -- [✱11·32]
  qsyl (qiffMp (q11_25 φ)) h                                                    -- [✱11·25]

/-- ✱11·7 `⊢ :. (∃x, y) : φ(x, y) . ∨ . φ(y, x) : ≡ . (∃x, y) . φ(x, y)`. PM: "(∃x, y) . φ(x, y) and
    (∃y, x) . φ(y, x) are the same proposition"; in Lean they are the same term. Replacing the second
    disjunct by ✱11·23 uses ✱4·39 (with ✱4·2), which PM leaves tacit. -/
theorem q11_7 (φ : V τ → V τ → QF V) :
    QThm S (iff (ex2 fun x y => .or (φ x y) (φ y x)) (ex2 φ)) :=
  have h1 := qiffSymm (q11_41 φ fun x y => φ y x)                               -- ✱11·41
  have h2 := QThm.mp (qandI (QL.t4_2 (ex2 φ)) (q11_23 fun x y => φ y x)) (QL.t4_39 _ _ _ _)  -- [✱11·23]
  qiffTrans h1 (qiffTrans h2 (qiffSymm (QL.t4_25 (ex2 φ))))                    -- [✱4·25]

/-- ✱11·71 `⊢ :: (∃z) . φz : (∃w) . χw : ⊃ :. φz . ⊃_z . ψz : χw . ⊃_w . θw : ≡ : φz . χw . ⊃_{z,w} . ψz . θw`.
    Tacit steps: in (4), Exp (✱3·3) before Comm; "Similarly" (6) takes `(w) : (z)` from Hp by ✱11·2,
    uses ✱10·35 with p second (✱4·3, `qex_and_perm`) and ✱3·27 for ✱3·26; in (7), the factors from
    ✱3·47 are commuted by ✱3·22 before Comp; the final (2).(7) adds Hp to (2) by ✱2·02 and joins by Comp. -/
theorem q11_71 (φ ψ : V σ → QF V) (χ θ : V τ → QF V) :
    QThm S (imp (QF.and (ex φ) (ex χ))
      (iff (QF.and (fimp φ ψ) (fimp χ θ))
           (fimp2 (fun z w => QF.and (φ z) (χ w)) (fun z w => QF.and (ψ z) (θ w))))) :=
  let A : QF V := fimp φ ψ
  let B : QF V := fimp χ θ
  let K : QF V := fimp2 (fun z w => QF.and (φ z) (χ w)) (fun z w => QF.and (ψ z) (θ w))
  have h1 : ∀ z w, QThm S (imp (QF.and A B) (imp (QF.and (φ z) (χ w)) (QF.and (ψ z) (θ w)))) :=
    fun z w => qsyl (QThm.mp (qandI (q10_1 (fun z => imp (φ z) (ψ z)) z) (q10_1 (fun w => imp (χ w) (θ w)) w))
        (QL.t3_47 A B _ _))
      (QL.t3_47 (φ z) (χ w) (ψ z) (θ w))                                        -- ✱10·1 . ✱3·47 (1)
  have h2 : QThm S (imp (QF.and A B) K) :=
    QThm.mp (q11_11 h1) (qiffMpr (q11_3 (QF.and A B)
      (fun z w => imp (QF.and (φ z) (χ w)) (QF.and (ψ z) (θ w)))))             -- (1).✱11·11·3 (2)
  have h3 : ∀ z, QThm S (imp K (imp (QF.and (φ z) (ex χ)) (QF.and (ψ z) (ex θ)))) := fun z =>
    calc K
        ⊃ .all (fun w => imp (QF.and (φ z) (χ w)) (QF.and (ψ z) (θ w))) :=
          q10_1 (fun z => .all fun w => imp (QF.and (φ z) (χ w)) (QF.and (ψ z) (θ w))) z  -- ✱10·1
      _ ⊃ imp (ex fun w => QF.and (φ z) (χ w)) (ex fun w => QF.and (ψ z) (θ w)) :=
          q10_28 (fun w => QF.and (φ z) (χ w)) (fun w => QF.and (ψ z) (θ w))    -- [✱10·28]
      _ ⊃ imp (QF.and (φ z) (ex χ)) (QF.and (ψ z) (ex θ)) :=
          qimpCongr (qiffMpr (q10_35 χ (φ z))) (qiffMp (q10_35 θ (ψ z)))        -- [✱10·35] (3)
  have h4 : ∀ z, QThm S (imp (ex χ) (imp K (imp (φ z) (ψ z)))) := fun z =>
    QThm.mp (qsyl (qsyl (qsyl (h3 z) (QThm.mp (QL.t3_26 (ψ z) (ex θ)) (QL.t2_05 _ _ _)))
        (QL.t3_3 (φ z) (ex χ) (ψ z))) (QL.t2_04 (φ z) (ex χ) (ψ z)))
      (QL.t2_04 K (ex χ) _)                                                     -- (3).Comm.✱3·26 (4)
  have h5 : QThm S (imp (ex χ) (imp K A)) :=
    qsyl (q10_11_21 h4) (qiffMp (q10_21 K fun z => imp (φ z) (ψ z)))            -- (4).✱10·11·21 (5)
  have h3' : ∀ w, QThm S (imp K (imp (QF.and (ex φ) (χ w)) (QF.and (ex ψ) (θ w)))) := fun w =>
    calc K
        ⊃ all2 (fun w z => imp (QF.and (φ z) (χ w)) (QF.and (ψ z) (θ w))) :=
          qiffMp (q11_2 fun z w => imp (QF.and (φ z) (χ w)) (QF.and (ψ z) (θ w)))  -- Similarly: (✱11·2)
      _ ⊃ .all (fun z => imp (QF.and (φ z) (χ w)) (QF.and (ψ z) (θ w))) :=
          q10_1 (fun w => .all fun z => imp (QF.and (φ z) (χ w)) (QF.and (ψ z) (θ w))) w  -- ✱10·1
      _ ⊃ imp (ex fun z => QF.and (φ z) (χ w)) (ex fun z => QF.and (ψ z) (θ w)) :=
          q10_28 (fun z => QF.and (φ z) (χ w)) (fun z => QF.and (ψ z) (θ w))    -- [✱10·28]
      _ ⊃ imp (QF.and (ex φ) (χ w)) (QF.and (ex ψ) (θ w)) :=
          qimpCongr (qiffMpr (qex_and_perm φ (χ w))) (qiffMp (qex_and_perm ψ (θ w)))  -- [✱10·35]
  have h6' : ∀ w, QThm S (imp (ex φ) (imp K (imp (χ w) (θ w)))) := fun w =>
    QThm.mp (qsyl (qsyl (h3' w) (QThm.mp (QL.t3_27 (ex ψ) (θ w)) (QL.t2_05 _ _ _)))
        (QL.t3_3 (ex φ) (χ w) (θ w)))
      (QL.t2_04 K (ex φ) _)
  have h6 : QThm S (imp (ex φ) (imp K B)) :=
    qsyl (q10_11_21 h6') (qiffMp (q10_21 K fun w => imp (χ w) (θ w)))           -- Similarly (6)
  have h7 : QThm S (imp (QF.and (ex φ) (ex χ)) (imp K (QF.and A B))) :=
    qsyl (qsyl (QThm.mp (qandI h6 h5) (QL.t3_47 _ _ _ _)) (QL.t3_22 _ _))
      (QL.t3_43 K A B)                                                          -- (5).(6).✱3·47.Comp (7)
  qcomp (QThm.mp h2 (QL.t2_02 (QF.and (ex φ) (ex χ)) (imp (QF.and A B) K))) h7  -- (2).(7)

/-! ## A counter-model PM gives in words -/

/-- PM p. 161, after ✱11·26: "Note that the converse of this proposition is false." It is not a theorem:
    in `twoModel`, with φ(x, y) the formula "φx ≡ φy" (true iff x and y are the same individual),
    `(y) : (∃x) . φ(x, y)` is true and `(∃x) : (y) . φ(x, y)` is false. -/
theorem not_qthm_converse_11_26 {S : (V : Ty → Type) → Sys V} :
    ¬ ∀ (V : Ty → Type) (φ : V .ind → V .ind → QF V),
      QThm (S V) (imp (.all fun y => ex fun x => φ x y) (ex fun x => .all (φ x))) :=
  fun h => not_qthm_of_countermodel twoModel
    (p := imp (.all fun y => ex fun x => iff (.atom "φ" [x]) (.atom "φ" [y]))
      (ex fun x => .all fun y => iff (.atom "φ" [x]) (.atom "φ" [y]))) rfl
    (h twoModel.den fun x y => iff (.atom "φ" [x]) (.atom "φ" [y]))

end PM
