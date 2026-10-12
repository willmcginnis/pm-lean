import PM.Found9.Star9
/-!
  From ✱10's method to ✱9's: every ✱10 theorem stands for a ✱9 theorem, given that ✱1·2–✱1·6 hold in
  ✱9 for every proposition.

  PM's claim (p. 142): "We have now completed the proof that, in the primitive propositions of ✱1, any
  *one* of the propositions that occur may be replaced by (x) . φx or (∃x) . φx. It follows that, by
  merely repeating the proofs, we can show that any other of the propositions that occur in these
  propositions can be simultaneously replaced by (x) . ψx or (∃x) . ψx. ... It follows, by mere
  repetition of the proofs, that the propositions of ✱1—✱5 hold when p, q, r are replaced by
  propositions containing any number of apparent variables." `Rep S V` states the conclusion of this
  claim: ✱1·2–✱1·6 for every ✱9 proposition. It is not proved here (see docs/STAR9_FOUNDATION.md for
  what the proofs of ✱9·3–✱9·52 do and do not give).

  Given `Rep` and a variable of every type, every primitive of ✱10's method holds in ✱9's, and so every
  ✱10 theorem does (`qthm_toF9`), by induction on the ✱10 derivation:
  - ✱1·1 is ✱9·12; ✱1·2–✱1·6 are `Rep`;
  - ✱10·1 is ✱9·2, proved for every function without `Rep` (PM/Found9/Base.lean); ✱10·11 is ✱9·13;
  - ✱10·12 is ✱9·25. For an elementary p its two sides are the same proposition (✱9·04); for a p with
    apparent variables they can be (p = (∃u) . χu, φ elementary) or not (`distrib_sides_ne`), and the
    order that ✱9·03–✱9·08 give the quantifiers does not always let ✱9·1 and ✱9·13 prove it
    directly: with p = (u) . χu and φ elementary it is
    (x) : (u) . χu ∨ φx . ⊃ : (u) : (x) . χu ∨ φx, in which ✱9·08 asks for the x of the antecedent
    before the x of the consequent has been introduced. `Rep.distrib` proves it from `Rep`, by
    ✱2·31, ✱2·32, ✱1·4 and ✱9·07; the step that ✱9·07 makes from p ∨ (∃w) . ρw to (∃w) . p ∨ ρw
    needs a value of w (`hV`). `Rep` and `hV` are assumptions of this proof for every p, not of each
    instance: one whose two sides are the same proposition is Id (`idt`). Whether ✱9's primitive
    propositions prove ✱9·25 for every p without `Rep` is not settled here.
  - comprehension and ✱12·1, ✱12·11 are the same rules: ✱10's (∃f) is ∼(f) . ∼, which ✱9·01 turns into
    (∃f) . ∼∼, and `Rep` gives ✱2·12 under (∃f) (by ✱9·22 as a rule, `exImp`).
-/
namespace PM.F9
open PF

variable {V : Ty → Type} {S : Sys}

/-- ✱1·2–✱1·6 for every proposition of ✱9 (the conclusion of PM's claim on p. 142). -/
structure Rep (S : Sys) (V : Ty → Type) : Prop where
  taut  : ∀ p : PF V, Thm9 S (imp (PF.or p p) p)                                   -- ✱1·2
  add   : ∀ p q : PF V, Thm9 S (imp q (PF.or p q))                                 -- ✱1·3
  perm  : ∀ p q : PF V, Thm9 S (imp (PF.or p q) (PF.or q p))                       -- ✱1·4
  assoc : ∀ p q r : PF V, Thm9 S (imp (PF.or p (PF.or q r)) (PF.or q (PF.or p r))) -- ✱1·5
  sum   : ∀ p q r : PF V, Thm9 S (imp (imp q r) (imp (PF.or p q) (PF.or p r)))      -- ✱1·6

/-- Replace the propositional variables of a ✱1–✱5 formula by ✱9 propositions. -/
def _root_.PM.F.toF9 (σ : String → PF V) : F → PF V
  | .var s  => σ s
  | .neg p  => PF.neg (F.toF9 σ p)
  | .or p q => PF.or (F.toF9 σ p) (F.toF9 σ q)

/-- Given `Rep`, every ✱1–✱5 theorem holds in ✱9 for any propositions: "the previous proofs of
    subsequent propositions in ✱2—✱5 become applicable" (p. 138). -/
theorem Rep.lift (hR : Rep S V) {t : F} (h : Thm t) (σ : String → PF V) : Thm9 S (t.toF9 σ) := by
  induction h with
  | mp _ _ ih1 ih2 => exact Thm9.mp ih1 ih2
  | taut p => exact hR.taut _
  | add p q => exact hR.add _ _
  | perm p q => exact hR.perm _ _
  | assoc p q r => exact hR.assoc _ _ _
  | sum p q r => exact hR.sum _ _ _

/-- The substitution p, q, r ↦ the given propositions (other letters ↦ p). -/
def psub (p q r : PF V) : String → PF V :=
  fun x => if x = "q" then q else if x = "r" then r else p

/-- Given `Rep`: from ⊢ (∃x) . φx infer ⊢ (∃x) . ∼∼φx (✱2·12 and ✱9·22 as a rule). -/
theorem Rep.exNegNeg (hR : Rep S V) {τ : Ty} {φ : V τ → PF V} (h : Thm9 S (.ex φ)) :
    Thm9 S (.ex fun x => neg (neg (φ x))) :=
  Thm9.mp h (exImp fun x => hR.lift (t2_12 (.var "p")) (psub (φ x) (φ x) (φ x)))

/-! ## ✱9·25 for every p, given `Rep` -/

/-- Given `Rep`, the syllogism (✱2·05). -/
theorem Rep.syl (hR : Rep S V) {a b c : PF V} (h1 : Thm9 S (imp a b)) (h2 : Thm9 S (imp b c)) :
    Thm9 S (imp a c) :=
  Thm9.mp h1 (Thm9.mp h2 (hR.lift (t2_05 (.var "p") (.var "q") (.var "r")) (psub a b c)))

/-- Given `Rep`: from ⊢ a ⊃ c and ⊢ b ⊃ c infer ⊢ a ∨ b . ⊃ . c (✱3·2, ✱3·44). -/
theorem Rep.orElim (hR : Rep S V) {a b c : PF V} (h1 : Thm9 S (imp a c)) (h2 : Thm9 S (imp b c)) :
    Thm9 S (imp (PF.or a b) c) :=
  Thm9.mp (Thm9.mp h2 (Thm9.mp h1 (hR.lift (t3_2 (.var "p") (.var "q")) (psub (imp a c) (imp b c) c))))
    (hR.lift (t3_44 (.var "p") (.var "q") (.var "r")) (psub c a b))

/-- Given `Rep` and a value of w: from ⊢ b . ∨ . (∃w) . ρw infer ⊢ (∃w) . b ∨ ρw. By ✱2·2 and ✱9·1,
    b implies it; by ✱1·3 and ✱9·22 as a rule, (∃w) . ρw does. -/
theorem Rep.exIn (hR : Rep S V) (hV : ∀ τ, Nonempty (V τ)) {b : PF V} {τ : Ty} {ρ : V τ → PF V}
    (h : Thm9 S (PF.or b (.ex ρ))) : Thm9 S (.ex fun w => PF.or b (ρ w)) :=
  (hV τ).elim fun w₀ =>
    Thm9.mp h (hR.orElim
      (hR.syl (hR.lift (t2_2 (.var "p") (.var "q")) (psub b (ρ w₀) b))
        (Thm9.ex1 (fun w => PF.or b (ρ w)) w₀))
      (exImp fun w => hR.add b (ρ w)))

/-- Given `Rep` and a variable of every type: from ⊢ φx ∨ d for every x infer
    ⊢ (x) . φx . ∨ . d. By ✱9·03 (repeated if d begins with (y)) the conclusion is (x) . φx ∨ d; by
    ✱9·07, if d is (∃w) . ρw, it is (x) : (∃w) . φx ∨ ρw (`Rep.exIn`). -/
theorem Rep.allOrL (hR : Rep S V) (hV : ∀ τ, Nonempty (V τ)) {τ : Ty} {φ : V τ → PF V} :
    ∀ {d : PF V}, (∀ x, Thm9 S (PF.or (φ x) d)) → Thm9 S (PF.or (.all φ) d)
  | .el _, h => Thm9.gen h
  | .all _, h => Thm9.gen h
  | .ex _, h => Thm9.gen fun x => hR.exIn hV (h x)

/-- `Rep.allOrL` on the right of the disjunction (✱1·4). -/
theorem Rep.allOr (hR : Rep S V) (hV : ∀ τ, Nonempty (V τ)) {τ : Ty} {φ : V τ → PF V} {d : PF V}
    (h : ∀ x, Thm9 S (PF.or d (φ x))) : Thm9 S (PF.or d (.all φ)) :=
  Thm9.mp (hR.allOrL hV fun x => Thm9.mp (h x) (hR.perm d (φ x))) (hR.perm (.all φ) d)

/-- Given `Rep` and a variable of every type, ✱9·25 `⊢ :. (x) . p ∨ φx . ⊃ : p . ∨ . (x) . φx` (it is
    ✱10·12) for every p and every function φ: ✱9·2 gives ∼A ∨ (p ∨ φx) for A the antecedent, ✱2·31
    regroups it as (∼A ∨ p) ∨ φx, `Rep.allOr` gives (∼A ∨ p) ∨ (x) . φx, and ✱2·32 regroups again. -/
theorem Rep.distrib (hR : Rep S V) (hV : ∀ τ, Nonempty (V τ)) (p : PF V) {τ : Ty}
    (φ : V τ → PF V) : Thm9 S (imp (.all fun x => PF.or p (φ x)) (PF.or p (.all φ))) :=
  let nA := neg (.all fun x => PF.or p (φ x))
  have h1 : ∀ x, Thm9 S (PF.or nA (PF.or p (φ x))) := fun x => inst (fun x => PF.or p (φ x)) x
  have h2 : ∀ x, Thm9 S (PF.or (PF.or nA p) (φ x)) := fun x =>
    Thm9.mp (h1 x) (show Thm9 S (imp (PF.or nA (PF.or p (φ x))) (PF.or (PF.or nA p) (φ x))) from
      hR.lift (t2_31 (.var "p") (.var "q") (.var "r")) (psub nA p (φ x)))         -- ✱2·31
  Thm9.mp (hR.allOr hV h2)
    (show Thm9 S (imp (PF.or (PF.or nA p) (.all φ)) (PF.or nA (PF.or p (.all φ)))) from
      hR.lift (t2_32 (.var "p") (.var "q") (.var "r")) (psub nA p (.all φ)))      -- ✱2·32

/-! ## Every ✱10 theorem stands for a ✱9 theorem -/

/-- Given `Rep` and a variable of every type, every ✱10 theorem stands for a ✱9 theorem, in the same
    system. -/
theorem qthm_toF9 (hV : ∀ τ, Nonempty (V τ)) (hR : Rep S V) {q : QF V} (h : QThm S q) :
    Thm9 S q.toF9 := by
  induction h with
  | mp _ _ ih1 ih2 => exact Thm9.mp ih1 ih2
  | taut p => exact hR.taut _
  | add p q => exact hR.add _ _
  | perm p q => exact hR.perm _ _
  | assoc p q r => exact hR.assoc _ _ _
  | sum p q r => exact hR.sum _ _ _
  | inst φ y => exact inst (fun x => (φ x).toF9) y
  | gen _ ih => exact Thm9.gen ih
  | distrib p φ => exact hR.distrib hV p.toF9 fun x => (φ x).toF9
  | compr1 hS ψ hψ => exact hR.exNegNeg (Thm9.compr1 hS ψ hψ)
  | compr2 hS ψ hψ => exact hR.exNegNeg (Thm9.compr2 hS ψ hψ)
  | red1 hS φ => exact hR.exNegNeg (Thm9.red1 hS fun x => (φ x).toF9)
  | red2 hS φ => exact hR.exNegNeg (Thm9.red2 hS fun x y => (φ x y).toF9)

end PM.F9
