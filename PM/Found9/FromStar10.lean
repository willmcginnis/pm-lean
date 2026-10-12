import PM.Found9.Switch
/-!
  From ✱10's method to ✱9's: every ✱10 theorem stands for a ✱9 theorem, given that ✱1·2–✱1·6 hold in
  ✱9 for every proposition.

  PM's claim (p. 142): "We have now completed the proof that, in the primitive propositions of ✱1, any
  *one* of the propositions that occur may be replaced by (x) . φx or (∃x) . φx. It follows that, by
  merely repeating the proofs, we can show that any other of the propositions that occur in these
  propositions can be simultaneously replaced by (x) . ψx or (∃x) . ψx. ... It follows, by mere
  repetition of the proofs, that the propositions of ✱1—✱5 hold when p, q, r are replaced by
  propositions containing any number of apparent variables." `Rep S R V` states the conclusion of this
  claim under the reading R: ✱1·2–✱1·6 for every ✱9 proposition. It is not proved here, under any
  reading (see docs/STAR9_FOUNDATION.md for what the proofs of ✱9·3–✱9·52 do and do not give); `Rep`
  for the alternative convention gives `Rep` for the definitions as printed with the prenex Switch
  (`Rep.toSwitch`).

  Given `Rep` and a variable of every type, every primitive of ✱10's method holds in ✱9's, and so every
  ✱10 theorem does (`qthm_toF9`), under every reading, by induction on the ✱10 derivation:
  - ✱1·1 is ✱9·12; ✱1·2–✱1·6 are `Rep`;
  - ✱10·1 is ✱9·2, proved for every function without `Rep` (PM/Found9/Base.lean; in ✱9+ with
    Switch); ✱10·11 is ✱9·13;
  - ✱10·12 is ✱9·25. For an elementary p its two sides are the same proposition (✱9·04). For every p,
    under the alternative convention it is proved from the primitive propositions
    (`distrib_convention`), and with the prenex Switch (`distrib_switch`). As printed and in ✱9+, for
    a p with apparent variables the two sides can be the same proposition (p = (∃u) . χu, φ elementary)
    or not (`distrib_sides_ne`), and the order that the definitions give the quantifiers does not
    always let ✱9·1 and ✱9·13 prove it directly: with p = (u) . χu and φ elementary it is
    (x) : (u) . χu ∨ φx . ⊃ : (u) : (x) . χu ∨ φx, in which ✱9·08 asks for the x of the antecedent
    before the x of the consequent has been introduced. `Rep.distrib` proves it from `Rep`, by
    ✱2·31, ✱2·32, ✱1·4 and ✱9·07; the step that ✱9·07 makes from p ∨ (∃w) . ρw to (∃w) . p ∨ ρw
    needs a value of w (`hV`). `Rep` and `hV` are assumptions of this proof for every p, not of each
    instance: one whose two sides are the same proposition is Id (`idt`). Whether ✱9's primitive
    propositions prove ✱9·25 for every p without `Rep` as printed or in ✱9+ (with Switch) is not
    settled here.
  - comprehension and ✱12·1, ✱12·11 are the same rules: ✱10's (∃f) is ∼(f) . ∼, which ✱9·01 turns into
    (∃f) . ∼∼, and `Rep` gives ✱2·12 under (∃f) (by ✱9·22 as a rule, `Rep.exImp`).
-/
namespace PM.F9
open PF

variable {V : Ty → Type} {S : Sys} {R : Reading}

/-- ✱1·2–✱1·6 for every proposition of ✱9 under the reading `R` (the conclusion of PM's claim on
    p. 142). -/
structure Rep (S : Sys) (R : Reading) (V : Ty → Type) : Prop where
  taut  : ∀ p : PF V, Thm9 S R (R.imp (R.or p p) p)                                -- ✱1·2
  add   : ∀ p q : PF V, Thm9 S R (R.imp q (R.or p q))                              -- ✱1·3
  perm  : ∀ p q : PF V, Thm9 S R (R.imp (R.or p q) (R.or q p))                     -- ✱1·4
  assoc : ∀ p q r : PF V, Thm9 S R (R.imp (R.or p (R.or q r)) (R.or q (R.or p r))) -- ✱1·5
  sum   : ∀ p q r : PF V, Thm9 S R (R.imp (R.imp q r) (R.imp (R.or p q) (R.or p r)))  -- ✱1·6

/-- Replace the propositional variables of a ✱1–✱5 formula by ✱9 propositions, reading ∨ by the
    definitions `d`. -/
def _root_.PM.F.toF9 (d : Defs) (σ : String → PF V) : F → PF V
  | .var s  => σ s
  | .neg p  => PF.neg (F.toF9 d σ p)
  | .or p q => PF.disj d (F.toF9 d σ p) (F.toF9 d σ q)

/-- Given `Rep`, every ✱1–✱5 theorem holds in ✱9 for any propositions: "the previous proofs of
    subsequent propositions in ✱2—✱5 become applicable" (p. 138). -/
theorem Rep.lift (hR : Rep S R V) {t : F} (h : Thm t) (σ : String → PF V) :
    Thm9 S R (t.toF9 R.defs σ) := by
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

/-- Adding the prenex Switch to a reading without ✱8·13 keeps its theorems (with ✱8·13 and the
    definitions as printed, `Thm9.russell_toPrenex`, PM/Found9/Exch.lean). -/
theorem Thm9.addSwitch {d : Defs} {sw : Rule} (hE : sw ≠ .exch) {p : PF V} (h : Thm9 S ⟨d, sw⟩ p) :
    Thm9 S ⟨d, .prenex⟩ p := by
  induction h with
  | mp _ _ ih1 ih2 => exact Thm9.mp ih1 ih2
  | taut p => exact Thm9.taut p
  | add p q => exact Thm9.add p q
  | perm p q => exact Thm9.perm p q
  | assoc p q r => exact Thm9.assoc p q r
  | sum p q r => exact Thm9.sum p q r
  | ex1 φ x => exact Thm9.ex1 φ x
  | ex2 φ x y => exact Thm9.ex2 φ x y
  | gen _ ih => exact Thm9.gen ih
  | compr1 hS ψ hψ => exact Thm9.compr1 hS ψ hψ
  | compr2 hS ψ hψ => exact Thm9.compr2 hS ψ hψ
  | red1 hS φ => exact Thm9.red1 hS φ
  | red2 hS φ => exact Thm9.red2 hS φ
  | exch h => exact absurd h hE
  | switch h hs _ ih => exact Thm9.switch (R := ⟨d, .prenex⟩) h hs ih
  | prenexSwitch _ hX hY _ ih => exact Thm9.prenexSwitch rfl hX hY ih

/-- `Rep` for the alternative convention gives `Rep` for the definitions as printed with the prenex
    Switch (which carries each instance to the proposition the definitions as printed make of its
    expression). -/
theorem Rep.toSwitch (hR : Rep S Reading.convention V) : Rep S Reading.prenexSwitch V where
  taut p := Thm9.reread (R := Reading.convention) nofun nofun (PE.imp (.or (.pf p) (.pf p)) (.pf p))
    (hR.taut p) .printed
  add p q := Thm9.reread (R := Reading.convention) nofun nofun (PE.imp (.pf q) (.or (.pf p) (.pf q)))
    (hR.add p q) .printed
  perm p q := Thm9.reread (R := Reading.convention) nofun nofun
    (PE.imp (.or (.pf p) (.pf q)) (.or (.pf q) (.pf p))) (hR.perm p q) .printed
  assoc p q r := Thm9.reread (R := Reading.convention) nofun nofun (PE.imp (.or (.pf p) (.or (.pf q) (.pf r)))
    (.or (.pf q) (.or (.pf p) (.pf r)))) (hR.assoc p q r) .printed
  sum p q r := Thm9.reread (R := Reading.convention) nofun nofun (PE.imp (PE.imp (.pf q) (.pf r))
    (PE.imp (.or (.pf p) (.pf q)) (.or (.pf p) (.pf r)))) (hR.sum p q r) .printed

/-! ## Tools given `Rep` -/

/-- Given `Rep`, the syllogism (✱2·05). -/
theorem Rep.syl (hR : Rep S R V) {a b c : PF V} (h1 : Thm9 S R (R.imp a b))
    (h2 : Thm9 S R (R.imp b c)) : Thm9 S R (R.imp a c) :=
  Thm9.mp h1 (Thm9.mp h2 (hR.lift (t2_05 (.var "p") (.var "q") (.var "r")) (psub a b c)))

/-- Given `Rep`, ✱9·22 as a rule for every pair of functions: from ⊢ φx ⊃ ψx for every x infer
    ⊢ (∃x) . φx . ⊃ . (∃x) . ψx. As printed and in ✱9+ it is direct (`exImp_printed`, `exImp_plus`);
    under the alternative convention the conclusion is (z) . φz ⊃ (∃x) . ψx, given by the syllogism
    with ✱9·1. -/
theorem Rep.exImp (hR : Rep S R V) {τ : Ty} {φ ψ : V τ → PF V}
    (h : ∀ x, Thm9 S R (R.imp (φ x) (ψ x))) : Thm9 S R (R.imp (.ex φ) (.ex ψ)) := by
  rcases R with ⟨_ | _ | _, sw⟩
  · exact exImp_printed h
  · exact Thm9.gen fun z => hR.syl (h z) (Thm9.ex1 ψ z)
  · exact exImp_plus h

/-- Given `Rep`: from ⊢ (∃x) . φx infer ⊢ (∃x) . ∼∼φx (✱2·12 and ✱9·22 as a rule). -/
theorem Rep.exNegNeg (hR : Rep S R V) {τ : Ty} {φ : V τ → PF V} (h : Thm9 S R (.ex φ)) :
    Thm9 S R (.ex fun x => neg (neg (φ x))) :=
  Thm9.mp h (hR.exImp fun x => hR.lift (t2_12 (.var "p")) (psub (φ x) (φ x) (φ x)))

/-! ## ✱9·25 for every p, given `Rep` -/

/-- Given `Rep`: from ⊢ a ⊃ c and ⊢ b ⊃ c infer ⊢ a ∨ b . ⊃ . c (✱3·2, ✱3·44). -/
theorem Rep.orElim (hR : Rep S R V) {a b c : PF V} (h1 : Thm9 S R (R.imp a c))
    (h2 : Thm9 S R (R.imp b c)) : Thm9 S R (R.imp (R.or a b) c) :=
  Thm9.mp (Thm9.mp h2 (Thm9.mp h1
      (hR.lift (t3_2 (.var "p") (.var "q")) (psub (R.imp a c) (R.imp b c) c))))
    (hR.lift (t3_44 (.var "p") (.var "q") (.var "r")) (psub c a b))

/-- Given `Rep` and a value of w: from ⊢ b . ∨ . (∃w) . ρw infer ⊢ (∃w) . b ∨ ρw. By ✱2·2 and ✱9·1,
    b implies it; by ✱1·3 and ✱9·22 as a rule, (∃w) . ρw does. -/
theorem Rep.exIn (hR : Rep S R V) (hV : ∀ τ, Nonempty (V τ)) {b : PF V} {τ : Ty} {ρ : V τ → PF V}
    (h : Thm9 S R (R.or b (.ex ρ))) : Thm9 S R (.ex fun w => R.or b (ρ w)) :=
  (hV τ).elim fun w₀ =>
    Thm9.mp h (hR.orElim
      (hR.syl (hR.lift (t2_2 (.var "p") (.var "q")) (psub b (ρ w₀) b))
        (Thm9.ex1 (fun w => R.or b (ρ w)) w₀))
      (hR.exImp fun w => hR.add b (ρ w)))

/-- Given `Rep` and a variable of every type: from ⊢ φx ∨ d for every x infer ⊢ (x) . φx . ∨ . d.
    Under the alternative convention the conclusion is (x) . φx ∨ d (✱9·03 for every d). As printed it
    is that by ✱9·03 if d is elementary or begins with (y), and (x) : (∃w) . φx ∨ ρw by ✱9·07 if d is
    (∃w) . ρw (`Rep.exIn`). In ✱9+ it is the same, except that for d = (y) . ψy ✱9·yy makes it
    (x) : (y) . φx ∨ ψy, given by ✱9·2 and ✱1·6. -/
theorem Rep.allOrL (hR : Rep S R V) (hV : ∀ τ, Nonempty (V τ)) {τ : Ty} {φ : V τ → PF V}
    {d : PF V} (h : ∀ x, Thm9 S R (R.or (φ x) d)) : Thm9 S R (R.or (.all φ) d) := by
  rcases R with ⟨_ | _ | _, sw⟩
  · cases d with
    | el _ => exact Thm9.gen h
    | all _ => exact Thm9.gen h
    | ex _ => exact Thm9.gen fun x => hR.exIn hV (h x)
  · exact Thm9.gen h
  · cases d with
    | el _ => exact Thm9.gen h
    | all ψ => exact Thm9.gen fun x => Thm9.gen fun y =>
        Thm9.mp (h x) (Thm9.mp (inst ψ y) (hR.sum (φ x) (.all ψ) (ψ y)))
    | ex _ => exact Thm9.gen fun x => hR.exIn hV (h x)

/-- `Rep.allOrL` on the right of the disjunction (✱1·4). -/
theorem Rep.allOr (hR : Rep S R V) (hV : ∀ τ, Nonempty (V τ)) {τ : Ty} {φ : V τ → PF V} {d : PF V}
    (h : ∀ x, Thm9 S R (R.or d (φ x))) : Thm9 S R (R.or d (.all φ)) :=
  Thm9.mp (hR.allOrL hV fun x => Thm9.mp (h x) (hR.perm d (φ x))) (hR.perm (.all φ) d)

/-- Given `Rep` and a variable of every type, ✱9·25 `⊢ :. (x) . p ∨ φx . ⊃ : p . ∨ . (x) . φx` (it is
    ✱10·12) for every p and every function φ, under every reading: ✱9·2 gives ∼A ∨ (p ∨ φx) for A the
    antecedent, ✱2·31 regroups it as (∼A ∨ p) ∨ φx, `Rep.allOr` gives (∼A ∨ p) ∨ (x) . φx, and ✱2·32
    regroups again. Under the alternative convention and with the prenex Switch it needs neither
    assumption (`distrib_convention`, `distrib_switch`). -/
theorem Rep.distrib (hR : Rep S R V) (hV : ∀ τ, Nonempty (V τ)) (p : PF V) {τ : Ty}
    (φ : V τ → PF V) : Thm9 S R (R.imp (.all fun x => R.or p (φ x)) (R.or p (.all φ))) :=
  let nA := neg (.all fun x => R.or p (φ x))
  have h1 : ∀ x, Thm9 S R (R.or nA (R.or p (φ x))) := fun x => inst (fun x => R.or p (φ x)) x
  have h2 : ∀ x, Thm9 S R (R.or (R.or nA p) (φ x)) := fun x =>
    Thm9.mp (h1 x) (show Thm9 S R (R.imp (R.or nA (R.or p (φ x))) (R.or (R.or nA p) (φ x))) from
      hR.lift (t2_31 (.var "p") (.var "q") (.var "r")) (psub nA p (φ x)))         -- ✱2·31
  Thm9.mp (hR.allOr hV h2)
    (show Thm9 S R (R.imp (R.or (R.or nA p) (.all φ)) (R.or nA (R.or p (.all φ)))) from
      hR.lift (t2_32 (.var "p") (.var "q") (.var "r")) (psub nA p (.all φ)))      -- ✱2·32

/-! ## Every ✱10 theorem stands for a ✱9 theorem -/

/-- Given `Rep` and a variable of every type, every ✱10 theorem stands for a ✱9 theorem, in the same
    system, under every reading. -/
theorem qthm_toF9 (hV : ∀ τ, Nonempty (V τ)) (hR : Rep S R V) {q : QF V} (h : QThm S q) :
    Thm9 S R (q.toF9 R.defs) := by
  induction h with
  | mp _ _ ih1 ih2 => exact Thm9.mp ih1 ih2
  | taut p => exact hR.taut _
  | add p q => exact hR.add _ _
  | perm p q => exact hR.perm _ _
  | assoc p q r => exact hR.assoc _ _ _
  | sum p q r => exact hR.sum _ _ _
  | inst φ y => exact inst (fun x => (φ x).toF9 R.defs) y
  | gen _ ih => exact Thm9.gen ih
  | distrib p φ => exact hR.distrib hV (p.toF9 R.defs) fun x => (φ x).toF9 R.defs
  | compr1 hS ψ hψ => exact hR.exNegNeg (Thm9.compr1 hS ψ hψ)
  | compr2 hS ψ hψ => exact hR.exNegNeg (Thm9.compr2 hS ψ hψ)
  | red1 hS φ => exact hR.exNegNeg (Thm9.red1 hS fun x => (φ x).toF9 R.defs)
  | red2 hS φ => exact hR.exNegNeg (Thm9.red2 hS fun x y => (φ x y).toF9 R.defs)

end PM.F9
