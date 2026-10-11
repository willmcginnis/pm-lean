import PM.Star13
/-!
  ✱14: descriptions (1910 print, pp. 181–190). **Partial**: the definitions ✱14·01 and ✱14·02 and the
  propositions ✱14·1, ✱14·101, ✱14·11, ✱14·12, ✱14·121, ✱14·2, ✱14·201 and ✱14·21, as a usability test
  of the ramified base (docs/TYPES_DESIGN.md, test U4). The rest of ✱14 is not formalized.

  Descriptions are incomplete symbols (PM p. 66 and ✱14 summary): `(ιx)(φx)` has no meaning by itself,
  only in a context. So there is no term for it. ✱14·01 is a macro that takes the description's
  condition φ and its *scope* ψ (a formula with a hole where the description stands):
    ✱14·01  [(ιx)(φx)] . ψ(ιx)(φx) . = : (∃b) : φx . ≡ₓ . x = b : ψb   Df   (`QF.desc φ ψ`)
    ✱14·02  E!(ιx)(φx) . = : (∃b) : φx . ≡ₓ . x = b                   Df   (`QF.exists1 φ`)
  The scope is therefore always explicit: `desc φ (fun z => .neg (χ z))` is [(ιx)(φx)] . ∼χ(ιx)(φx),
  and `.neg (desc φ χ)` is ∼{[(ιx)(φx)] . χ(ιx)(φx)}. PM's convention that an unmarked description
  has the smallest scope (p. 182) becomes a choice the Lean author makes when writing the term.
-/
namespace PM
open QF

namespace QF
variable {V : Ty → Type} {S : Sys}
/-- ✱14·01 `[(ιx)(φx)] . ψ(ιx)(φx) . = : (∃b) : φx . ≡ₓ . x = b : ψb` Df. ψ is the scope. -/
@[reducible] def desc {a : Ty} (φ ψ : V a → QF V) : QF V :=
  ex fun b => QF.and (fiff φ fun x => ident x b) (ψ b)
/-- ✱14·02 `E!(ιx)(φx) . = : (∃b) : φx . ≡ₓ . x = b` Df -/
@[reducible] def exists1 {a : Ty} (φ : V a → QF V) : QF V :=
  ex fun b => fiff φ fun x => ident x b
end QF

variable {V : Ty → Type} {S : Sys} {a : Ty}

/-- ✱14·1 `⊢ :. [(ιx)(φx)] . ψ(ιx)(φx) . ≡ : (∃b) : φx . ≡ₓ . x = b : ψb` [✱4·2 . (✱14·01)] -/
theorem q14_1 (φ ψ : V a → QF V) :
    QThm S (iff (desc φ ψ) (ex fun b => QF.and (fiff φ fun x => ident x b) (ψ b))) :=
  QL.t4_2 _

/-- ✱14·101 `⊢ :. ψ(ιx)(φx) . ≡ : (∃b) : φx . ≡ₓ . x = b : ψb` [✱14·1]. With the scope explicit in the
    Lean term, this is ✱14·1 again: PM's convention reads the unmarked ψ(ιx)(φx) as having scope ψ. -/
theorem q14_101 (φ ψ : V a → QF V) :
    QThm S (iff (desc φ ψ) (ex fun b => QF.and (fiff φ fun x => ident x b) (ψ b))) :=
  q14_1 φ ψ

/-- ✱14·11 `⊢ :. E!(ιx)(φx) . ≡ : (∃b) : φx . ≡ₓ . x = b` [✱4·2 . (✱14·02)] -/
theorem q14_11 (φ : V a → QF V) : QThm S (iff (exists1 φ) (ex fun b => fiff φ fun x => ident x b)) :=
  QL.t4_2 _

/-- ✱14·12 `⊢ :. E!(ιx)(φx) . ⊃ : φx . φy . ⊃_{x,y} . x = y`. In (2), ✱10·1 is used at x and at y and
    the two joined by Comp (✱3·43); the "≡" of ✱4·38 is used left to right (✱3·26) and chained with
    ✱13·172 by Syll (✱2·05). -/
theorem q14_12 [Reducibility S] (φ : V a → QF V) :
    QThm S (imp (exists1 φ) (fimp2 (fun x y => QF.and (φ x) (φ y)) fun x y => ident x y)) :=
  have h1 := qiffMp (q14_11 φ)                                                   -- ✱14·11 (1)
  have h2 : ∀ b x y, QThm S (imp (fiff φ fun x => ident x b)
      (imp (QF.and (φ x) (φ y)) (ident x y))) := fun b x y =>
    have e := qsyl (qcomp (q10_1 (fun x => iff (φ x) (ident x b)) x)
      (q10_1 (fun x => iff (φ x) (ident x b)) y)) (QL.t4_38 _ _ _ _)           -- ✱4·38 . ✱10·1
    qsyl (qsyl e (QL.t3_26 _ _)) (QThm.mp (q13_172 b x y) (QL.t2_05 _ _ _))    -- [✱13·172] (2)
  have h2' : ∀ b, QThm S (imp (fiff φ fun x => ident x b)
      (fimp2 (fun x y => QF.and (φ x) (φ y)) fun x y => ident x y)) := fun b =>
    qiffMpr (q11_3 _ _) |> QThm.mp (q11_11 (h2 b))                              -- ✱11·11·3
  qsyl h1 (QThm.mp (q10_11 h2') (qiffMp (q10_23 _ _)))                          -- (2).✱10·11·23 (3) . (1).(3)

/-- From ⊢ x = x, `φx . ≡ . x = x : ⊃ . φx` (used in ✱14·121 and ✱14·201 for "[✱13·15]"):
    ✱3·27, Comm (✱2·04) and ✱13·15. -/
theorem qiff_refl_elim (φ : V a → QF V) (x : V a) : QThm S (imp (iff (φ x) (ident x x)) (φ x)) :=
  QThm.mp (q13_15 x) (QThm.mp (QL.t3_27 _ _) (QL.t2_04 _ _ _))

/-- ✱14·121 `⊢ :. φx . ≡ₓ . x = b : φx . ≡ₓ . x = c : ⊃ . b = c`. ✱10·1 at b for both factors is ✱10·14;
    "[Ass]" is ✱3·35, after ✱3·26 turns φb ≡ b = c into φb ⊃ b = c. -/
theorem q14_121 (φ : V a → QF V) (b c : V a) :
    QThm S (imp (QF.and (fiff φ fun x => ident x b) (fiff φ fun x => ident x c)) (ident b c)) :=
  have h1 := q10_14 (fun x => iff (φ x) (ident x b)) (fun x => iff (φ x) (ident x c)) b  -- ✱10·1
  have h2 := QThm.mp (qiff_refl_elim φ b) (QL.t3_45 _ _ _)                       -- [✱13·15]
  qsyl h1 (qsyl h2 (qsyl (qandR (QL.t3_26 _ _)) (QL.t3_35 _ _)))                 -- [Ass]

/-- ✱14·2 `⊢ . (ιx)(x = a) = a`, i.e. `[(ιx)(x = a)] . (ιx)(x = a) = a`. ✱13·195 needs the factors
    `b = a . F b`; they are commuted under (∃b) by ✱4·3 and ✱10·11·281. "Id" is ✱4·2 under ✱10·11. -/
theorem q14_2 [Reducibility S] (c : V a) : QThm S (desc (fun x => ident x c) fun z => ident z c) :=
  let F : V a → QF V := fun b => fiff (fun x => ident x c) fun x => ident x b
  have h1 : QThm S (iff (desc (fun x => ident x c) fun z => ident z c) (F c)) :=
    qiffTrans (q14_101 _ _)                                                      -- ✱14·101
      (qiffTrans (q10_11_281 fun b => QL.t4_3 (F b) (ident b c)) (q13_195 F c))  -- [✱13·195] (1)
  QThm.mp (q10_11 fun x => QL.t4_2 (ident x c)) (qiffMpr h1)                    -- (1).Id

/-- ✱14·201 `⊢ : E!(ιx)(φx) . ⊃ . (∃x) . φx`. ✱10·1 and "[✱13·15]" act under (∃b) (✱10·11·28). -/
theorem q14_201 (φ : V a → QF V) : QThm S (imp (exists1 φ) (ex φ)) :=
  qsyl (qiffMp (q14_11 φ))                                                       -- ✱14·11
    (q10_11_28 fun b => qsyl (q10_1 (fun x => iff (φ x) (ident x b)) b)          -- [✱10·1]
      (qiff_refl_elim φ b))                                                      -- [✱13·15]

/-- ✱14·21 `⊢ : ψ(ιx)(φx) . ⊃ . E!(ιx)(φx)`, the description in ψ having the scope ψ. ✱10·5 gives the
    product of the two existentials; its first factor is taken by ✱3·26 (tacit). -/
theorem q14_21 (φ ψ : V a → QF V) : QThm S (imp (desc φ ψ) (exists1 φ)) :=
  qsyl (qiffMp (q14_1 φ ψ))                                                      -- ✱14·1
    (qsyl (q10_5 _ ψ) (QL.t3_26 _ _))                                            -- [✱10·5] [✱14·11]

/-- ✱14·21 with the smallest scope inside a negation: `∼χ(ιx)(φx)`, i.e. [(ιx)(φx)] . ∼χ(ιx)(φx),
    also implies E!(ιx)(φx). With the larger scope, ∼{[(ιx)(φx)] . χ(ιx)(φx)} does not (PM p. 190:
    when the description does not exist there are true propositions in which it has a secondary
    occurrence); see `not_qthm_neg_desc_imp_exists1`. -/
theorem q14_21_neg (φ χ : V a → QF V) : QThm S (imp (desc φ fun z => .neg (χ z)) (exists1 φ)) :=
  q14_21 φ fun z => .neg (χ z)

/-! ## A counter-model for the larger scope -/

/-- In every structure, x = x is true (✱13·01 evaluated). -/
theorem eval_ident_refl (M : QModel) {a : Ty} (x : M.den a) : (ident x x).eval M = true :=
  (M.hA _ _).mpr fun f => by
    show (!(M.ap1 f x) || M.ap1 f x) = true
    cases M.ap1 f x <;> rfl

/-- `φ0 x` is `qx . ∼qx`, false of every individual. -/
def φ0 {V : Ty → Type} (x : V .ind) : QF V := QF.and (.atom "q" [x]) (.neg (.atom "q" [x]))

/-- Scope matters (PM pp. 181–182, 190): with the larger scope, ∼{[(ιx)(φx)] . χ(ιx)(φx)} does not imply
    E!(ιx)(φx), whereas [(ιx)(φx)] . ∼χ(ιx)(φx) does (`q14_21_neg`). In `twoModel` nothing satisfies
    φ0, so (ιx)(φ0 x) does not exist, the description with the larger scope is false and its negation true.
    `twoModel` is the finite coded model (PM/Models/Finite.lean), so the formula is evaluated by
    computation, including the quantifier over the four predicative functions in ✱13·01. -/
theorem not_qthm_neg_desc_imp_exists1 :
    ¬ ∀ (V : Ty → Type) (φ χ : V .ind → QF V), QThm S (imp (.neg (desc φ χ)) (exists1 φ)) :=
  fun h => not_qthm_of_countermodel twoModel (p := imp (.neg (desc φ0 φ0)) (exists1 φ0)) rfl (h _ φ0 φ0)

end PM
