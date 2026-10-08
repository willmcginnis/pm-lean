import PM.Replay
/-!
  Derived rules for the ✱1 Hilbert system. Every rule here is a meta-level Lean lemma of the shape
  `Thm a → … → Thm c` (or a theorem schema), built only from `Thm`'s constructors and the
  already-replayed `t…` theorems of PM.Replay. Nothing is assumed: `#print axioms` is empty.

  Part 1: Hilbert-level rules (syllogism, ∧/≡ introduction and elimination).
  Part 2: PM's chain ✱2·73 → ✱2·77 (Frege's "S" axiom), proved following PM's citations. The
          `t2_73 … t2_77` theorems of PM.Replay2 are these lemmas.
  Part 3: a natural-deduction layer. `Pf Γ φ` is *defined* as the theorem `Thm (h₁ ⊃ (h₂ ⊃ … ⊃ φ))`,
          so the deduction theorem is definitional (`Pf (Γ ++ [h]) φ` is `Pf Γ (h ⊃ φ)`), and
          `Pf [] φ` is `Thm φ`. The rules lift PM's propositions into a context.
-/
namespace PM
open F

/-! ## Part 1: Hilbert-level rules -/

/-- Syllogism as a rule (✱2·05). -/
theorem syl {a b c : F} (h1 : Thm (imp a b)) (h2 : Thm (imp b c)) : Thm (imp a c) :=
  Thm.mp h1 (Thm.mp h2 (t2_05 a b c))

/-- ✱2·02 as a rule. -/
theorem kI {a b : F} (h : Thm b) : Thm (imp a b) := Thm.mp h (t2_02 a b)

/-- ✱2·04 (commutation) as a rule. -/
theorem comm {a b c : F} (h : Thm (imp a (imp b c))) : Thm (imp b (imp a c)) :=
  Thm.mp h (t2_04 a b c)

/-- Replace the antecedent of a consequent: from `a ⊃ (x ⊃ y)` and `z ⊃ x` infer `a ⊃ (z ⊃ y)` (✱2·06). -/
theorem sylMid {a x y z : F} (h : Thm (imp a (imp x y))) (hz : Thm (imp z x)) :
    Thm (imp a (imp z y)) :=
  syl h (Thm.mp hz (t2_06 z x y))

/-- Strengthen the consequent of a consequent: from `a ⊃ (x ⊃ y)` and `y ⊃ z` infer `a ⊃ (x ⊃ z)` (✱2·05). -/
theorem sylEnd {a x y z : F} (h : Thm (imp a (imp x y))) (hz : Thm (imp y z)) :
    Thm (imp a (imp x z)) :=
  syl h (Thm.mp hz (t2_05 x y z))

/-- Syll (✱2·06) applied to an antecedent: from `a ⊃ b` infer `(b ⊃ c) ⊃ (a ⊃ c)`. -/
theorem sylAnt {a b c : F} (h : Thm (imp a b)) : Thm (imp (imp b c) (imp a c)) :=
  Thm.mp h (t2_06 a b c)

/-- Syll (✱2·05) applied to a consequent: from `b ⊃ c` infer `(a ⊃ b) ⊃ (a ⊃ c)`. -/
theorem sylCons {a b c : F} (h : Thm (imp b c)) : Thm (imp (imp a b) (imp a c)) :=
  Thm.mp h (t2_05 a b c)

/-- ✱3·2 as a rule. -/
theorem andIh {a b : F} (ha : Thm a) (hb : Thm b) : Thm (and a b) := Thm.mp hb (Thm.mp ha (t3_2 a b))
/-- ✱3·26 as a rule. -/
theorem andE1h {a b : F} (h : Thm (and a b)) : Thm a := Thm.mp h (t3_26 a b)
/-- ✱3·27 as a rule. -/
theorem andE2h {a b : F} (h : Thm (and a b)) : Thm b := Thm.mp h (t3_27 a b)

/-- ✱4·01 + ✱3·2 as a rule. -/
theorem iffIh {a b : F} (h1 : Thm (imp a b)) (h2 : Thm (imp b a)) : Thm (iff a b) := andIh h1 h2
/-- ✱4·01 + ✱3·26 as a rule. -/
theorem iffMph {a b : F} (h : Thm (iff a b)) : Thm (imp a b) := andE1h h
/-- ✱4·01 + ✱3·27 as a rule. -/
theorem iffMprh {a b : F} (h : Thm (iff a b)) : Thm (imp b a) := andE2h h

/-- An asserted equivalence read right to left (✱4·01; its halves recombined by ✱3·03). -/
theorem iffSymmh {a b : F} (h : Thm (iff a b)) : Thm (iff b a) := iffIh (iffMprh h) (iffMph h)
/-- PM's chain `⊢ : a . ≡ . b : ≡ . c`: the two halves joined by Syll, as for a `⊃`-chain. -/
theorem iffTransh {a b c : F} (h1 : Thm (iff a b)) (h2 : Thm (iff b c)) : Thm (iff a c) :=
  iffIh (syl (iffMph h1) (iffMph h2)) (syl (iffMprh h2) (iffMprh h1))
/-- Syll (✱2·05) applied to the consequent of a consequent, in a `⊃`-chain under a hypothesis `h`. -/
theorem sylUnder {h y z : F} (x : F) (d : Thm (imp h (imp y z))) :
    Thm (imp h (imp (imp x y) (imp x z))) :=
  syl d (t2_05 x y z)
/-- The links of a printed chain `⊢ : a . ≡ . b : ≡ . c : ≡ . d` (✱4·87), which Lean states as the
    conjunction `(a ≡ b . b ≡ c) . c ≡ d`. -/
theorem link1 {a b c : F} (h : Thm (and (and a b) c)) : Thm a := andE1h (andE1h h)
theorem link2 {a b c : F} (h : Thm (and (and a b) c)) : Thm b := andE2h (andE1h h)
theorem link3 {a b c : F} (h : Thm (and (and a b) c)) : Thm c := andE2h h
/-- An asserted equivalence applied, by Syll both ways, to an antecedent. -/
theorem iffSylAnt {a b : F} (c : F) (h : Thm (iff a b)) : Thm (iff (imp a c) (imp b c)) :=
  iffIh (sylAnt (iffMprh h)) (sylAnt (iffMph h))
/-- An asserted equivalence applied, by Syll both ways, to a consequent. -/
theorem iffSylCons {a b : F} (c : F) (h : Thm (iff a b)) : Thm (iff (imp c a) (imp c b)) :=
  iffIh (sylCons (iffMph h)) (sylCons (iffMprh h))

/-! ## Part 2: PM ✱2·73 – ✱2·77 -/

/-- ✱2·73 [✱2·621, ✱2·38]. -/
theorem pm2_73 (p q r : F) : Thm (s2_73 p q r) := syl (t2_621 p q) (t2_38 r (.or p q) q)

/-- ✱2·74 [✱2·73 (q,p/p,q), ✱1·4 under ✱2·38, ✱2·06]. -/
theorem pm2_74 (p q r : F) : Thm (s2_74 p q r) :=
  sylMid (pm2_73 q p r) (Thm.mp (Thm.perm p q) (t2_38 r (.or p q) (.or q p)))

/-- ✱2·75 [✱2·74 (∼q/q), ✱2·53, ✱2·31]. -/
theorem pm2_75 (p q r : F) : Thm (s2_75 p q r) :=
  sylMid (syl (syl (Thm.perm p q) (t2_53 q p)) (pm2_74 p (.neg q) r)) (t2_31 p (.neg q) r)

/-- ✱2·76 [✱2·75, ✱2·04]. -/
theorem pm2_76 (p q r : F) : Thm (s2_76 p q r) := comm (pm2_75 p q r)

/-- ✱2·77 [✱2·76 (∼p/p)] — Frege's S. -/
theorem pm2_77 (p q r : F) : Thm (s2_77 p q r) := pm2_76 (.neg p) q r

/-! ## Part 3: natural deduction in a context -/

/-- `ctx [h₁,…,hₙ] φ = h₁ ⊃ (… ⊃ (hₙ ⊃ φ))`. -/
@[reducible] def ctx : List F → F → F
  | [], φ => φ
  | h :: Γ, φ => imp h (ctx Γ φ)

/-- `Pf Γ φ`: φ is a theorem under the hypotheses Γ, i.e. `Thm (ctx Γ φ)`. -/
def Pf (Γ : List F) (φ : F) : Prop := Thm (ctx Γ φ)

namespace Pf

theorem ctx_append : ∀ (Γ : List F) (h φ : F), ctx (Γ ++ [h]) φ = ctx Γ (imp h φ)
  | [], _, _ => rfl
  | g :: Γ, h, φ => congrArg (imp g) (ctx_append Γ h φ)

/-- Deduction theorem (definitional for concrete Γ). -/
theorem intro {Γ : List F} {h φ : F} (d : Pf (Γ ++ [h]) φ) : Pf Γ (imp h φ) :=
  Eq.mp (congrArg Thm (ctx_append Γ h φ)) d

theorem unintro {Γ : List F} {h φ : F} (d : Pf Γ (imp h φ)) : Pf (Γ ++ [h]) φ :=
  Eq.mpr (congrArg Thm (ctx_append Γ h φ)) d

/-- A theorem holds in any context (✱2·02). -/
theorem ofThm {Γ : List F} {φ : F} (h : Thm φ) : Pf Γ φ := by
  induction Γ with
  | nil => exact h
  | cons g Γ ih => exact kI ih

theorem dist (Γ : List F) (a b : F) : Thm (imp (ctx Γ (imp a b)) (imp (ctx Γ a) (ctx Γ b))) := by
  induction Γ with
  | nil => exact t2_08 _
  | cons g Γ ih => exact syl (Thm.mp ih (t2_05 g _ _)) (pm2_77 g _ _)

/-- Modus ponens (✱1·1) under hypotheses, via ✱2·77. -/
theorem mp {Γ : List F} {a b : F} (ha : Pf Γ a) (hab : Pf Γ (imp a b)) : Pf Γ b :=
  Thm.mp ha (Thm.mp hab (dist Γ a b))

/-- Apply a theorem `a ⊃ b` under hypotheses. -/
theorem app {Γ : List F} {a b : F} (h : Thm (imp a b)) (ha : Pf Γ a) : Pf Γ b := mp ha (ofThm h)
/-- Apply a theorem `a ⊃ (b ⊃ c)` under hypotheses. -/
theorem app2 {Γ : List F} {a b c : F} (h : Thm (imp a (imp b c))) (ha : Pf Γ a) (hb : Pf Γ b) :
    Pf Γ c := mp hb (app h ha)
/-- Apply a theorem `a ⊃ (b ⊃ (c ⊃ d))` under hypotheses. -/
theorem app3 {Γ : List F} {a b c d : F} (h : Thm (imp a (imp b (imp c d)))) (ha : Pf Γ a)
    (hb : Pf Γ b) (hc : Pf Γ c) : Pf Γ d := mp hc (app2 h ha hb)

theorem self_ctx (Γ : List F) (φ : F) : Thm (imp φ (ctx Γ φ)) := by
  induction Γ with
  | nil => exact t2_08 φ
  | cons g Γ ih => exact syl ih (t2_02 g _)

/-- Use a hypothesis. -/
theorem hyp {Γ : List F} {φ : F} : φ ∈ Γ → Pf Γ φ
  | .head Γ => self_ctx Γ φ
  | .tail _ h => kI (hyp h)

/-- The `n`-th hypothesis of a context (0-based, oldest first). -/
def nth : List F → Nat → F
  | [], _ => .var ""
  | a :: _, 0 => a
  | _ :: l, n + 1 => nth l n

theorem hyN : ∀ (Γ : List F) (n : Nat), n < Γ.length → Pf Γ (nth Γ n)
  | [], n, h => absurd h (Nat.not_lt_zero n)
  | g :: Γ, 0, _ => self_ctx Γ g
  | _ :: Γ, n + 1, h => kI (hyN Γ n (Nat.lt_of_succ_lt_succ h))

/-- Use the `n`-th hypothesis (0-based, oldest first). The bound is checked by evaluation. -/
theorem hy {Γ : List F} (n : Nat) (h : n < Γ.length := by exact Nat.le_of_ble_eq_true rfl) :
    Pf Γ (nth Γ n) :=
  hyN Γ n h

/-- Weaken by an extra (last) hypothesis. -/
theorem weaken {Γ : List F} {h φ : F} (d : Pf Γ φ) : Pf (Γ ++ [h]) φ :=
  unintro (app (t2_02 h φ) d)

/-- ✱3·2 under hypotheses. -/
theorem andI {Γ : List F} {a b : F} (ha : Pf Γ a) (hb : Pf Γ b) : Pf Γ (and a b) :=
  app2 (t3_2 a b) ha hb
/-- ✱3·26 under hypotheses. -/
theorem andE1 {Γ : List F} {a b : F} (h : Pf Γ (and a b)) : Pf Γ a := app (t3_26 a b) h
/-- ✱3·27 under hypotheses. -/
theorem andE2 {Γ : List F} {a b : F} (h : Pf Γ (and a b)) : Pf Γ b := app (t3_27 a b) h

/-- ✱4·01 + ✱3·2 under hypotheses. -/
theorem iffI {Γ : List F} {a b : F} (h1 : Pf Γ (imp a b)) (h2 : Pf Γ (imp b a)) : Pf Γ (iff a b) :=
  andI h1 h2
theorem iffMp {Γ : List F} {a b : F} (h : Pf Γ (iff a b)) : Pf Γ (imp a b) := andE1 h
theorem iffMpr {Γ : List F} {a b : F} (h : Pf Γ (iff a b)) : Pf Γ (imp b a) := andE2 h
/-- Equivalence-substitution of a whole formula: from `a ≡ b` and `a`, infer `b`. -/
theorem iffE {Γ : List F} {a b : F} (h : Pf Γ (iff a b)) (ha : Pf Γ a) : Pf Γ b := mp ha (iffMp h)
theorem iffE' {Γ : List F} {a b : F} (h : Pf Γ (iff a b)) (hb : Pf Γ b) : Pf Γ a := mp hb (iffMpr h)

/-- ✱1·3 under hypotheses. -/
theorem orIR {Γ : List F} {a b : F} (h : Pf Γ b) : Pf Γ (.or a b) := app (Thm.add a b) h
/-- ✱2·2 under hypotheses. -/
theorem orIL {Γ : List F} {a b : F} (h : Pf Γ a) : Pf Γ (.or a b) := app (t2_2 a b) h

/-- Proof by cases, as a schema: `(a ⊃ c) ⊃ ((b ⊃ c) ⊃ (a ∨ b ⊃ c))` [✱1·6, ✱1·4, ✱1·2]. -/
theorem orE_schema (a b c : F) : Thm (imp (imp a c) (imp (imp b c) (imp (.or a b) c))) :=
  -- under [a ⊃ c, b ⊃ c, a ∨ b]
  have hac : Pf [imp a c, imp b c, .or a b] (imp a c) := hy 0
  have hbc : Pf [imp a c, imp b c, .or a b] (imp b c) := hy 1
  have hab : Pf [imp a c, imp b c, .or a b] (.or a b) := hy 2
  have h1 : Pf [imp a c, imp b c, .or a b] (.or a c) := app2 (Thm.sum a b c) hbc hab
  have h2 : Pf [imp a c, imp b c, .or a b] (.or c a) := app (Thm.perm a c) h1
  have h3 : Pf [imp a c, imp b c, .or a b] (.or c c) := app2 (Thm.sum c a c) hac h2
  app (Thm.taut c) h3

/-- ∨-elimination under hypotheses. -/
theorem orE {Γ : List F} {a b c : F} (h : Pf Γ (.or a b)) (ha : Pf (Γ ++ [a]) c)
    (hb : Pf (Γ ++ [b]) c) : Pf Γ c :=
  app3 (orE_schema a b c) (intro ha) (intro hb) h

/-- ✱2·11: excluded middle, used as a case split. -/
theorem cases {Γ : List F} (a : F) {c : F} (ha : Pf (Γ ++ [a]) c) (hna : Pf (Γ ++ [.neg a]) c) :
    Pf Γ c :=
  orE (ofThm (t2_11 a)) ha hna

/-- ✱2·24: from `a` and `∼a`, anything. -/
theorem absurd {Γ : List F} {a : F} (c : F) (ha : Pf Γ a) (hna : Pf Γ (.neg a)) : Pf Γ c :=
  app2 (t2_24 a c) ha hna

/-- ✱2·01: reductio, `∼`-introduction. -/
theorem negI {Γ : List F} {a : F} (h : Pf (Γ ++ [a]) (.neg a)) : Pf Γ (.neg a) :=
  app (t2_01 a) (intro h)

/-- ✱2·18: classical reductio. -/
theorem byContra {Γ : List F} {a : F} (h : Pf (Γ ++ [.neg a]) a) : Pf Γ a :=
  app (t2_18 a) (intro h)

/-- ∼-introduction from a contradiction. -/
theorem negI' {Γ : List F} {a : F} (b : F) (hb : Pf (Γ ++ [a]) b) (hnb : Pf (Γ ++ [a]) (.neg b)) :
    Pf Γ (.neg a) :=
  negI (absurd _ hb hnb)

/-- Classical reductio from a contradiction. -/
theorem byContra' {Γ : List F} {a : F} (b : F) (hb : Pf (Γ ++ [.neg a]) b)
    (hnb : Pf (Γ ++ [.neg a]) (.neg b)) : Pf Γ a :=
  byContra (absurd _ hb hnb)

/-- ✱2·14 / ✱2·12 under hypotheses. -/
theorem dne {Γ : List F} {a : F} (h : Pf Γ (.neg (.neg a))) : Pf Γ a := app (t2_14 a) h
theorem dni {Γ : List F} {a : F} (h : Pf Γ a) : Pf Γ (.neg (.neg a)) := app (t2_12 a) h

end Pf

/-- `intro_`: deduction theorem, `⊢ Γ ⊃ (h ⊃ φ)` from `Γ, h ⊢ φ`. -/
macro "intro_" : tactic => `(tactic| apply PM.Pf.intro)
/-- `split_iff`: prove `a ≡ b` as `a ⊢ b` and `b ⊢ a`. -/
macro "split_iff" : tactic => `(tactic| (apply PM.Pf.iffI <;> apply PM.Pf.intro))

/-- Run a natural-deduction proof with no hypotheses. -/
theorem ofPf {φ : F} (h : Pf [] φ) : Thm φ := h

end PM
