import PM.Found9.Star9
import PM.Star10
/-!
  From ✱9's method to ✱10's: every proposition asserted by ✱9's method, written with ✱10's primitive
  ideas (`PF.toQ`), is asserted by ✱10's method, in the same system `S`.

  ✱9's definitions ✱9·01–✱9·08 move every quantifier to the front. In ✱10's method the moves are
  substantial propositions: ✱10·2, ✱10·252, ✱10·253 and ✱10·36. The last needs a real variable y (PM's
  proof uses one; without it the proposition fails in an empty structure, PM/Star10.lean). So the
  results here assume that every type has a variable (`hV : ∀ τ, Nonempty (V τ)`), as PM's proofs
  assume an individual. PM/Found9/Empty.lean shows that the assumption cannot be dropped.

  - `toQ_neg`, `toQ_or`: ✱10 proves the ✱9 negation and disjunction equivalent to ✱10's own;
  - `toQ_toF9`: a ✱10 formula is equivalent to the ✱9 proposition for which it stands;
  - `thm9_toQ`: every ✱9 theorem is a ✱10 theorem.
-/
namespace PM.F9
open QF

variable {V : Ty → Type} {S : Sys}

/-! ## Equivalences in ✱10 used as replacement rules (✱4·11, ✱4·39 and their consequences) -/

/-- ✱4·39 as a rule: equivalents may replace each other in a disjunction. -/
theorem qorCong {a a' b b' : QF V} (h1 : QThm S (iff a a')) (h2 : QThm S (iff b b')) :
    QThm S (iff (.or a b) (.or a' b')) := QThm.mp (qandI h1 h2) (QL.t4_39 a b a' b')
/-- An equivalence between implications, by ✱4·11 and ✱4·39 (✱1·01). -/
theorem qimpCong {a a' b b' : QF V} (h1 : QThm S (iff a a')) (h2 : QThm S (iff b b')) :
    QThm S (iff (imp a b) (imp a' b')) := qorCong (qiffNeg h1) h2
/-- An equivalence between logical products, by ✱4·11 and ✱4·39 (✱3·01). -/
theorem qandCong {a a' b b' : QF V} (h1 : QThm S (iff a a')) (h2 : QThm S (iff b b')) :
    QThm S (iff (QF.and a b) (QF.and a' b')) := qiffNeg (qorCong (qiffNeg h1) (qiffNeg h2))
/-- An equivalence between equivalences (✱4·01). -/
theorem qiffCong {a a' b b' : QF V} (h1 : QThm S (iff a a')) (h2 : QThm S (iff b b')) :
    QThm S (iff (iff a b) (iff a' b')) := qandCong (qimpCong h1 h2) (qimpCong h2 h1)
/-- ✱10·11·281: from `⊢ . φx ≡ ψx` for every x, infer `⊢ : (∃x) . φx . ≡ . (∃x) . ψx`. -/
theorem qexCong {τ : Ty} {φ ψ : V τ → QF V} (h : ∀ x, QThm S (iff (φ x) (ψ x))) :
    QThm S (iff (ex φ) (ex ψ)) := QThm.mp (QThm.gen h) (q10_281 φ ψ)
/-- Modus ponens through an equivalence. -/
theorem qiffMpRule {a b : QF V} (h : QThm S (iff a b)) (ha : QThm S a) : QThm S b :=
  QThm.mp ha (qiffMp h)

/-! ## Moving a quantifier to the front, in ✱10 -/

/-- ✱10·2 with the disjunction the other way round: `(x) . φx ∨ p . ≡ : (x) . φx . ∨ . p`. -/
theorem q_all_or {τ : Ty} (φ : V τ → QF V) (p : QF V) :
    QThm S (iff (.all fun x => .or (φ x) p) (.or (.all φ) p)) :=
  qiffTrans (q10_11_271 fun x => QL.t4_31 (φ x) p) (qiffTrans (q10_2 p φ) (QL.t4_31 p (.all φ)))

/-- ✱10·36 with the disjunction the other way round: `(∃x) . p ∨ φx . ≡ : p . ∨ . (∃x) . φx`. -/
theorem q_ex_or' {τ : Ty} (φ : V τ → QF V) (p : QF V) (y : V τ) :
    QThm S (iff (ex fun x => .or p (φ x)) (.or p (ex φ))) :=
  qiffTrans (qexCong fun x => QL.t4_31 p (φ x)) (qiffTrans (q10_36 φ p y) (QL.t4_31 (ex φ) p))

/-! ## ✱9's negation and disjunction in ✱10 -/

/-- The ✱9 negation of a proposition is equivalent, in ✱10, to its ✱10 negation (✱10·252, ✱10·253). -/
theorem toQ_neg : ∀ A : PF V, QThm S (iff (PF.neg A).toQ (.neg A.toQ))
  | .el _ => QL.t4_2 _
  | .all φ =>
    have h : ∀ x, QThm S (iff (.neg (PF.neg (φ x)).toQ) (φ x).toQ) := fun x =>
      qiffTrans (qiffNeg (toQ_neg (φ x))) (qiffSymm (QL.t4_13 _))
    qiffNeg (q10_11_271 h)
  | .ex φ =>
    qiffTrans (q10_11_271 fun x => toQ_neg (φ x)) (QL.t4_13 _)

/-- p ∨ q for an elementary p (✱9·04, ✱9·06) is equivalent, in ✱10, to ✱10's disjunction. -/
theorem toQ_orEl (hV : ∀ τ, Nonempty (V τ)) (a : EF V) :
    ∀ B : PF V, QThm S (iff (PF.orEl a B).toQ (.or a.toQ B.toQ))
  | .el _ => QL.t4_2 _
  | .all ψ => qiffTrans (q10_11_271 fun y => toQ_orEl hV a (ψ y)) (q10_2 _ _)
  | @PF.ex _ τ ψ =>
    (hV τ).elim fun y => qiffTrans (qexCong fun y => toQ_orEl hV a (ψ y)) (q_ex_or' _ _ y)

/-- (∃x) . φx . ∨ . q (✱9·05, ✱9·08) is equivalent, in ✱10, to ✱10's disjunction, given the same
    for each φx ∨ q. -/
theorem toQ_orEx (hV : ∀ τ, Nonempty (V τ)) {τ : Ty} (φ : V τ → PF V)
    (ih : ∀ x B, QThm S (iff (PF.or (φ x) B).toQ (.or (φ x).toQ B.toQ))) :
    ∀ B : PF V, QThm S (iff (PF.orEx (fun x q => PF.or (φ x) q) B).toQ (.or (PF.ex φ).toQ B.toQ))
  | .all ψ => qiffTrans (q10_11_271 fun y => toQ_orEx hV φ ih (ψ y)) (q10_2 _ _)
  | .el b => (hV τ).elim fun y => qiffTrans (qexCong fun x => ih x (.el b)) (q10_36 _ _ y)
  | .ex ψ => (hV τ).elim fun y => qiffTrans (qexCong fun x => ih x (.ex ψ)) (q10_36 _ _ y)

/-- The ✱9 disjunction of two propositions is equivalent, in ✱10, to their ✱10 disjunction. -/
theorem toQ_or (hV : ∀ τ, Nonempty (V τ)) :
    ∀ A B : PF V, QThm S (iff (PF.or A B).toQ (.or A.toQ B.toQ))
  | .el a, B => toQ_orEl hV a B
  | .all φ, B => qiffTrans (q10_11_271 fun x => toQ_or hV (φ x) B) (q_all_or _ _)
  | .ex φ, B => toQ_orEx hV φ (fun x B => toQ_or hV (φ x) B) B

/-- ✱9's implication (✱1·01 over ✱9·01–✱9·08) and ✱10's. -/
theorem toQ_imp (hV : ∀ τ, Nonempty (V τ)) (A B : PF V) :
    QThm S (iff (PF.imp A B).toQ (imp A.toQ B.toQ)) :=
  qiffTrans (toQ_or hV _ _) (qorCong (toQ_neg A) (QL.t4_2 _))

/-- ✱9's equivalence (✱4·01) and ✱10's. -/
theorem toQ_iff (hV : ∀ τ, Nonempty (V τ)) (A B : PF V) :
    QThm S (iff (PF.iff A B).toQ (iff A.toQ B.toQ)) :=
  qiffTrans (toQ_neg _) (qiffNeg (qiffTrans (toQ_or hV _ _)
    (qorCong (qiffTrans (toQ_neg _) (qiffNeg (toQ_imp hV A B)))
      (qiffTrans (toQ_neg _) (qiffNeg (toQ_imp hV B A))))))

/-- A ✱10 formula is equivalent, in ✱10, to the ✱9 proposition for which it stands. -/
theorem toQ_toF9 (hV : ∀ τ, Nonempty (V τ)) : ∀ q : QF V, QThm S (iff q.toF9.toQ q)
  | .atom _ _ => QL.t4_2 _
  | .app1 _ _ => QL.t4_2 _
  | .app2 _ _ _ => QL.t4_2 _
  | .neg p => qiffTrans (toQ_neg _) (qiffNeg (toQ_toF9 hV p))
  | .or p q => qiffTrans (toQ_or hV _ _) (qorCong (toQ_toF9 hV p) (toQ_toF9 hV q))
  | .all φ => q10_11_271 fun x => toQ_toF9 hV (φ x)

/-! ## Every ✱9 theorem is a ✱10 theorem -/

/-- Every proposition asserted by ✱9's method is asserted by ✱10's, in the same system: ✱1·2–✱1·6 for
    elementary propositions are instances of ✱10's; ✱9·1 and ✱9·11 are ✱10·24 and its consequence
    (PM/Star10.lean); ✱9·12 is ✱1·1; ✱9·13 is ✱10·11; comprehension and ✱12·1, ✱12·11 are the same
    rules. -/
theorem thm9_toQ (hV : ∀ τ, Nonempty (V τ)) {p : PF V} (h : Thm9 S p) : QThm S p.toQ := by
  induction h with
  | mp _ _ ih1 ih2 => exact QThm.mp ih1 (qiffMpRule (toQ_imp hV _ _) ih2)
  | taut p => exact QThm.taut _
  | add p q => exact QThm.add _ _
  | perm p q => exact QThm.perm _ _
  | assoc p q r => exact QThm.assoc _ _ _
  | sum p q r => exact QThm.sum _ _ _
  | ex1 φ x => exact qiffMpRule (qiffSymm (toQ_imp hV _ _)) (q9_1 (fun x => (φ x).toQ) x)
  | ex2 φ x y =>
    exact qiffMpRule (qiffSymm (qiffTrans (toQ_imp hV _ _) (qimpCong (toQ_or hV _ _) (QL.t4_2 _))))
      (q9_11 (fun x => (φ x).toQ) x y)
  | gen _ ih => exact QThm.gen ih
  | compr1 hS ψ hψ =>
    exact qiffMpRule (qexCong fun f => q10_11_271 fun x =>
        qiffSymm (qiffTrans (toQ_iff hV _ _) (qiffCong (toQ_toF9 hV (ψ x)) (QL.t4_2 _))))
      (QThm.compr1 hS ψ hψ)
  | compr2 hS ψ hψ =>
    exact qiffMpRule (qexCong fun f => q10_11_271 fun x => q10_11_271 fun y =>
        qiffSymm (qiffTrans (toQ_iff hV _ _) (qiffCong (toQ_toF9 hV (ψ x y)) (QL.t4_2 _))))
      (QThm.compr2 hS ψ hψ)
  | red1 hS φ =>
    exact qiffMpRule (qexCong fun f => q10_11_271 fun x => qiffSymm (toQ_iff hV _ _))
      (QThm.red1 hS fun x => (φ x).toQ)
  | red2 hS φ =>
    exact qiffMpRule (qexCong fun f => q10_11_271 fun x => q10_11_271 fun y =>
        qiffSymm (toQ_iff hV _ _))
      (QThm.red2 hS fun x y => (φ x y).toQ)

end PM.F9
