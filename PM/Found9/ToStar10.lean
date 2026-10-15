import PM.Found9.Exch
import PM.Star10
/-!
  From ✱9's method to ✱10's: every proposition asserted by ✱9's method, written with ✱10's primitive
  ideas (`PF.toQ`), is asserted by ✱10's method, in the same system `S`, under every reading of ✱9
  (as printed, with ✱8·13, ✱9+ with Switch, the alternative convention, with or without the prenex
  Switch).

  ✱9's definitions ✱9·01–✱9·08 move every quantifier to the front. In ✱10's method the moves are
  substantial propositions: ✱10·2, ✱10·252, ✱10·253 and ✱10·36. The last needs a real variable y (PM's
  proof uses one; without it the proposition fails in an empty structure, PM/Star10.lean). So the
  results here assume that every type has a variable (`hV : ∀ τ, Nonempty (V τ)`), as PM's proofs
  assume an individual. `thm9_unsound_empty` (PM/Found9/Equiv.lean) shows that the assumption cannot be
  dropped.

  - `toQ_neg`, `toQ_merge`, `toQ_or`: ✱10 proves the ✱9 negation equivalent to ✱10's, and every way of
    taking the quantifiers of a disjunction to the front (`Merge`), so either definitions of ∨, equivalent
    to ✱10's disjunction;
  - `exchStep_q10`: a step of Russell's ✱8·13 carried over to ✱9 is an equivalence in ✱10: before and
    after it the proposition is a merge of the same two parts (`Sep.merges`), so ✱8·13 is derivable by
    ✱10's method;
  - `switchStep_q10`: a step of Landini's Switch, (x) : (∃y) . A to (∃y) : (x) . A with A a merge of a
    part with x and a part with y, is an equivalence in ✱10 (by ✱10·2 and ✱10·36), so Switch is
    derivable by ✱10's method;
  - `toQ_prenex`, `switch_q10`: every prenex form of an expression is equivalent to it in ✱10, so the
    prenex Switch is derivable by ✱10's method;
  - `toQ_toF9`: a ✱10 formula is equivalent to the ✱9 proposition for which it stands;
  - `thm9_toQ`: every ✱9 theorem is a ✱10 theorem.
-/
namespace PM.F9
open QF

variable {V : Ty → Type} {S : Sys V}

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

/-- A merge of X and Y (any order of taking their quantifiers out, `Merge`) is equivalent, in ✱10, to
    the ✱10 disjunction of X and Y: a universal quantifier by ✱10·2, an existential one by ✱10·36
    (which takes a value of its variable, `hV`). -/
theorem toQ_merge (hV : ∀ τ, Nonempty (V τ)) {X Y Z : PF V} (h : Merge X Y Z) :
    QThm S (iff Z.toQ (.or X.toQ Y.toQ)) := by
  induction h with
  | el a b => exact QL.t4_2 _
  | allL _ ih => exact qiffTrans (q10_11_271 ih) (q_all_or _ _)
  | @exL τ _ _ _ _ ih => exact (hV τ).elim fun y₀ => qiffTrans (qexCong ih) (q10_36 _ _ y₀)
  | allR _ ih => exact qiffTrans (q10_11_271 ih) (q10_2 _ _)
  | @exR τ _ _ _ _ ih => exact (hV τ).elim fun y₀ => qiffTrans (qexCong ih) (q_ex_or' _ _ y₀)

/-- The ✱9 disjunction of two propositions, under either definitions, is equivalent, in ✱10, to their
    ✱10 disjunction. -/
theorem toQ_or (hV : ∀ τ, Nonempty (V τ)) (d : Defs) (A B : PF V) :
    QThm S (iff (PF.disj d A B).toQ (.or A.toQ B.toQ)) :=
  toQ_merge hV (merge_disj d A B)

/-- ✱9's implication (✱1·01 over ✱9·01–✱9·08) and ✱10's. -/
theorem toQ_imp (hV : ∀ τ, Nonempty (V τ)) (R : Reading) (A B : PF V) :
    QThm S (iff (R.imp A B).toQ (imp A.toQ B.toQ)) :=
  qiffTrans (toQ_or hV _ _ _) (qorCong (toQ_neg A) (QL.t4_2 _))

/-- ✱9's equivalence (✱4·01) and ✱10's. -/
theorem toQ_iff (hV : ∀ τ, Nonempty (V τ)) (R : Reading) (A B : PF V) :
    QThm S (iff (R.iff A B).toQ (iff A.toQ B.toQ)) :=
  qiffTrans (toQ_neg _) (qiffNeg (qiffTrans (toQ_or hV _ _ _)
    (qorCong (qiffTrans (toQ_neg _) (qiffNeg (toQ_imp hV R A B)))
      (qiffTrans (toQ_neg _) (qiffNeg (toQ_imp hV R B A))))))

/-- A prenex form of an expression is equivalent, in ✱10, to the expression. -/
theorem toQ_prenex (hV : ∀ τ, Nonempty (V τ)) {t : PE V} {X : PF V} (h : Prenex t X) :
    QThm S (iff X.toQ t.toQ) := by
  induction h with
  | pf X => exact QL.t4_2 _
  | all _ ih => exact q10_11_271 ih
  | ex _ ih => exact qexCong ih
  | neg _ ih => exact qiffTrans (toQ_neg _) (qiffNeg ih)
  | or _ _ m ih1 ih2 => exact qiffTrans (toQ_merge hV m) (qorCong ih1 ih2)

/-- **The prenex Switch is derivable by ✱10's method**: any two prenex forms of one expression are
    equivalent in ✱10, given a variable of every type. -/
theorem switch_q10 (hV : ∀ τ, Nonempty (V τ)) {t : PE V} {X Y : PF V} (hX : Prenex t X)
    (hY : Prenex t Y) : QThm S (iff X.toQ Y.toQ) :=
  qiffTrans (toQ_prenex hV hX) (qiffSymm (toQ_prenex hV hY))

/-- In ✱10, (x) : (∃y) . Px ∨ Qy and (∃y) : (x) . Px ∨ Qy are both (x) . Px . ∨ . (∃y) . Qy (✱10·2,
    ✱10·36, which takes a value of y). -/
theorem q_switch_or {τ σ : Ty} (P : V τ → QF V) (Q : V σ → QF V) (y₀ : V σ) :
    QThm S (iff (.all fun x => ex fun y => .or (P x) (Q y)) (ex fun y => .all fun x => .or (P x) (Q y))) :=
  qiffTrans (qiffTrans (q10_11_271 fun x => q_ex_or' Q (P x) y₀) (q_all_or P (ex Q)))
    (qiffSymm (qiffTrans (qexCong fun y => q_all_or P (Q y)) (q_ex_or' Q (.all P) y₀)))

/-- `q_switch_or` with the part with y on the left: (x) : (∃y) . Qy ∨ Px and (∃y) : (x) . Qy ∨ Px
    are both (∃y) . Qy . ∨ . (x) . Px. -/
theorem q_switch_ro {τ σ : Ty} (P : V τ → QF V) (Q : V σ → QF V) (y₀ : V σ) :
    QThm S (iff (.all fun x => ex fun y => .or (Q y) (P x)) (ex fun y => .all fun x => .or (Q y) (P x))) :=
  qiffTrans (qiffTrans (q10_11_271 fun x => q10_36 Q (P x) y₀) (q10_2 (ex Q) P))
    (qiffSymm (qiffTrans (qexCong fun y => q10_2 (Q y) P) (q10_36 Q (.all P) y₀)))

/-- **Landini's Switch is derivable by ✱10's method**: a step of Switch is an equivalence in ✱10, given
    a variable of every type. -/
theorem switchStep_q10 (hV : ∀ τ, Nonempty (V τ)) {X Y : PF V} (h : SwitchStep X Y) :
    QThm S (iff X.toQ Y.toQ) := by
  induction h with
  | @here τ σ Z hZ =>
    refine (hV σ).elim fun y₀ => ?_
    cases hZ with
    | left L R hm =>
      exact qiffTrans (q10_11_271 fun x => qexCong fun y => toQ_merge hV (hm x y))
        (qiffTrans (q_switch_or (fun x => (L x).toQ) (fun y => (R y).toQ) y₀)
          (qiffSymm (qexCong fun y => q10_11_271 fun x => toQ_merge hV (hm x y))))
    | right L R hm =>
      exact qiffTrans (q10_11_271 fun x => qexCong fun y => toQ_merge hV (hm x y))
        (qiffTrans (q_switch_ro (fun x => (L x).toQ) (fun y => (R y).toQ) y₀)
          (qiffSymm (qexCong fun y => q10_11_271 fun x => toQ_merge hV (hm x y))))
  | all _ ih => exact q10_11_271 ih
  | ex _ ih => exact qexCong ih

/-- **✱8·13 carried over to ✱9 is derivable by ✱10's method**: a step of it is an equivalence in ✱10,
    given a variable of every type. -/
theorem exchStep_q10 (hV : ∀ τ, Nonempty (V τ)) {k₁ k₂ : Bool} {X Y : PF V} (h : ExchStep k₁ k₂ X Y) :
    QThm S (iff X.toQ Y.toQ) := by
  induction h with
  | here hZ =>
    obtain ⟨A, B, h1, h2⟩ := Sep.merges k₁ k₂ hZ
    exact qiffTrans (toQ_merge hV h1) (qiffSymm (toQ_merge hV h2))
  | all _ ih => exact q10_11_271 ih
  | ex _ ih => exact qexCong ih

/-- A ✱10 formula is equivalent, in ✱10, to the ✱9 proposition for which it stands, under either
    definitions. -/
theorem toQ_toF9 (hV : ∀ τ, Nonempty (V τ)) (d : Defs) : ∀ q : QF V, QThm S (iff (q.toF9 d).toQ q)
  | .atom _ _ => QL.t4_2 _
  | .app1 _ _ => QL.t4_2 _
  | .app2 _ _ _ => QL.t4_2 _
  | .neg p => qiffTrans (toQ_neg _) (qiffNeg (toQ_toF9 hV d p))
  | .or p q => qiffTrans (toQ_or hV d _ _) (qorCong (toQ_toF9 hV d p) (toQ_toF9 hV d q))
  | .all φ => q10_11_271 fun x => toQ_toF9 hV d (φ x)

/-! ## Every ✱9 theorem is a ✱10 theorem -/

/-- Every proposition asserted by ✱9's method, under any reading, is asserted by ✱10's, in the same
    system: ✱1·2–✱1·6 for elementary propositions are instances of ✱10's; ✱9·1 and ✱9·11 are ✱10·24
    and its consequence (PM/Star10.lean); ✱9·12 is ✱1·1; ✱9·13 is ✱10·11; comprehension and ✱12·1,
    ✱12·11 are the same rules; ✱8·13 is `exchStep_q10`, Switch `switchStep_q10`, the prenex Switch
    `switch_q10`. -/
theorem thm9_toQ (hV : ∀ τ, Nonempty (V τ)) {R : Reading} {p : PF V} (h : Thm9 S R p) :
    QThm S p.toQ := by
  induction h with
  | mp _ _ ih1 ih2 => exact QThm.mp ih1 (qiffMpRule (toQ_imp hV _ _ _) ih2)
  | taut p => exact QThm.taut _
  | add p q => exact QThm.add _ _
  | perm p q => exact QThm.perm _ _
  | assoc p q r => exact QThm.assoc _ _ _
  | sum p q r => exact QThm.sum _ _ _
  | ex1 φ x => exact qiffMpRule (qiffSymm (toQ_imp hV _ _ _)) (q9_1 (fun x => (φ x).toQ) x)
  | ex2 φ x y =>
    exact qiffMpRule (qiffSymm (qiffTrans (toQ_imp hV _ _ _) (qimpCong (toQ_or hV _ _ _) (QL.t4_2 _))))
      (q9_11 (fun x => (φ x).toQ) x y)
  | gen _ ih => exact QThm.gen ih
  | compr1 hS ψ hψ =>
    exact qiffMpRule (qexCong fun f => q10_11_271 fun x =>
        qiffSymm (qiffTrans (toQ_iff hV _ _ _) (qiffCong (toQ_toF9 hV _ (ψ x)) (QL.t4_2 _))))
      (QThm.compr1 hS ψ hψ)
  | compr2 hS ψ hψ =>
    exact qiffMpRule (qexCong fun f => q10_11_271 fun x => q10_11_271 fun y =>
        qiffSymm (qiffTrans (toQ_iff hV _ _ _) (qiffCong (toQ_toF9 hV _ (ψ x y)) (QL.t4_2 _))))
      (QThm.compr2 hS ψ hψ)
  | red1 hS φ =>
    exact qiffMpRule (qexCong fun f => q10_11_271 fun x => qiffSymm (toQ_iff hV _ _ _))
      (QThm.red1 hS fun x => (φ x).toQ)
  | red2 hS φ =>
    exact qiffMpRule (qexCong fun f => q10_11_271 fun x => q10_11_271 fun y =>
        qiffSymm (toQ_iff hV _ _ _))
      (QThm.red2 hS fun x y => (φ x y).toQ)
  | exch _ h _ ih => exact qiffMpRule (exchStep_q10 hV h) ih
  | switch _ h _ ih => exact qiffMpRule (switchStep_q10 hV h) ih
  | prenexSwitch _ hX hY _ ih => exact qiffMpRule (switch_q10 hV hX hY) ih

end PM.F9
