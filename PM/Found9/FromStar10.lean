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

  Given `Rep`, every primitive of ✱10's method holds in ✱9's, and so every ✱10 theorem does
  (`qthm_toF9`), by induction on the ✱10 derivation:
  - ✱1·1 is ✱9·12; ✱1·2–✱1·6 are `Rep`;
  - ✱10·1 is ✱9·2 and ✱10·12 is ✱9·25, both proved for every function without `Rep`
    (PM/Found9/Base.lean); ✱10·11 is ✱9·13;
  - comprehension and ✱12·1, ✱12·11 are the same rules: ✱10's (∃f) is ∼(f) . ∼, which ✱9·01 turns into
    (∃f) . ∼∼, and `Rep` gives ✱2·12 under (∃f).
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

/-- Given `Rep`: from ⊢ (∃x) . φx infer ⊢ (∃x) . ∼∼φx (✱2·12, ✱2·05 and ✱9·1, under ∃-elimination). -/
theorem Rep.exNegNeg (hR : Rep S V) {τ : Ty} {φ : V τ → PF V} (h : Thm9 S (.ex φ)) :
    Thm9 S (.ex fun x => neg (neg (φ x))) :=
  exE (fun z => Thm9.mp (Thm9.ex1 (fun x => neg (neg (φ x))) z)
      (Thm9.mp (hR.lift (t2_12 (.var "p")) (psub (φ z) (φ z) (φ z)))
        (hR.lift (t2_06 (.var "p") (.var "q") (.var "r"))
          (psub (φ z) (neg (neg (φ z))) (.ex fun x => neg (neg (φ x)))))))
    h

/-- Given `Rep`, every ✱10 theorem stands for a ✱9 theorem, in the same system. -/
theorem qthm_toF9 (hR : Rep S V) {q : QF V} (h : QThm S q) : Thm9 S q.toF9 := by
  induction h with
  | mp _ _ ih1 ih2 => exact Thm9.mp ih1 ih2
  | taut p => exact hR.taut _
  | add p q => exact hR.add _ _
  | perm p q => exact hR.perm _ _
  | assoc p q r => exact hR.assoc _ _ _
  | sum p q r => exact hR.sum _ _ _
  | inst φ y => exact inst (fun x => (φ x).toF9) y
  | gen _ ih => exact Thm9.gen ih
  | distrib p φ => exact distrib p.toF9 fun x => (φ x).toF9
  | compr1 hS ψ hψ => exact hR.exNegNeg (Thm9.compr1 hS ψ hψ)
  | compr2 hS ψ hψ => exact hR.exNegNeg (Thm9.compr2 hS ψ hψ)
  | red1 hS φ => exact hR.exNegNeg (Thm9.red1 hS fun x => (φ x).toF9)
  | red2 hS φ => exact hR.exNegNeg (Thm9.red2 hS fun x y => (φ x y).toF9)

end PM.F9
