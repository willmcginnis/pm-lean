import PM.Found9.Switch
/-!
  Russell's ✱8·13 carried over to ✱9 (reading C, `Thm9.exch`; docs/REPAIRS.md, R1), and how it relates
  to Landini's Switch (reading L, R3) and to our prenex Switch (R5).

  ✱8·13, as printed in the second edition (1925; Vol. I, Appendix A, p. 636, page image): "If all
  occurrences of x are separated from all occurrences of y by a certain stroke, we can change the order
  of x and y in the prefix, i.e. we can replace "(y) : (∃x) . φx | ψy" by "(∃x) : (y) . φx | ψy" and
  vice versa. Pp" A step of it in ✱9 (`ExchStep k₁ k₂`) exchanges two adjacent quantifiers of the
  prefix, of kinds k₁ and k₂, over an A that `Sep` separates.

  - `Sep.merges`, `exch_here_prenex`: before and after a step at the front, the proposition is a merge
    of the same two parts, so a step of ✱8·13 is a step of the prenex Switch; with the definitions as
    printed and the prenex Switch, ⊢ X ⊃ Y for every step (`exch_imp_prenex`), and every theorem of C is
    a theorem there (`Thm9.russell_toPrenex`).
  - `ExchStep.symm`: "and vice versa": the converse of a step is a step.
  - Landini's Switch is the direction (x)(∃y) to (∃y)(x) of ✱8·13 (`SwitchStep.toExch`,
    `ExchStep.toSwitch`), so it is a derived rule of C (`switch_russell`): a step of ✱8·13.
  - ✱8·13 in ✱9+: every step is derivable in L (`exch_plus`). The direction (x)(∃y) to (∃y)(x) is
    Switch; the converse is dr(S*), without Switch (`exch_imp_plus_ea`, as `switch_converse`); the
    exchanges of two quantifiers of the same kind take one step of Switch each (`exch_imp_plus_aa`,
    `exch_imp_plus_ee`). None of the three needs the side condition.

  What is not shown: whether C and L have the same theorems up to the order of quantifiers that their
  definitions give (their definitions make different propositions of the same expression where two
  quantifiers of the same kind meet, docs/REPAIRS.md, R2, R3); whether either derives the prenex
  Switch.
-/
namespace PM.F9
open PF

variable {V : Ty → Type} {S : Sys}

/-! ## A step at the front: two merges of the same parts -/

theorem Merge.quL (k : Bool) {τ : Ty} {φ : V τ → PF V} {Y : PF V} {Z : V τ → PF V}
    (h : ∀ x, Merge (φ x) Y (Z x)) : Merge (PF.qu k φ) Y (PF.qu k Z) := by
  cases k
  · exact .exL h
  · exact .allL h

theorem Merge.quR (k : Bool) {τ : Ty} {X : PF V} {ψ : V τ → PF V} {Z : V τ → PF V}
    (h : ∀ y, Merge X (ψ y) (Z y)) : Merge X (PF.qu k ψ) (PF.qu k Z) := by
  cases k
  · exact .exR h
  · exact .allR h

/-- Under `Sep`, both orders of two quantifiers over A are merges of the same two parts: the part with
    x under its quantifier and the part with y under its own. -/
theorem Sep.merges (k₁ k₂ : Bool) {τ σ : Ty} {Z : V τ → V σ → PF V} (h : Sep Z) :
    ∃ A B : PF V, Merge A B (PF.qu k₁ fun x => PF.qu k₂ fun y => Z x y) ∧
      Merge A B (PF.qu k₂ fun y => PF.qu k₁ fun x => Z x y) := by
  cases h with
  | left L R hm =>
    exact ⟨PF.qu k₁ L, PF.qu k₂ R, .quL k₁ fun x => .quR k₂ fun y => hm x y,
      .quR k₂ fun y => .quL k₁ fun x => hm x y⟩
  | right L R hm =>
    exact ⟨PF.qu k₂ R, PF.qu k₁ L, .quR k₁ fun x => .quL k₂ fun y => hm x y,
      .quL k₂ fun y => .quR k₁ fun x => hm x y⟩

/-- A step of ✱8·13 at the front of a proposition is a step of the prenex Switch. -/
theorem exch_here_prenex (k₁ k₂ : Bool) {τ σ : Ty} {Z : V τ → V σ → PF V} (h : Sep Z) :
    ∃ t : PE V, Prenex t (PF.qu k₁ fun x => PF.qu k₂ fun y => Z x y) ∧
      Prenex t (PF.qu k₂ fun y => PF.qu k₁ fun x => Z x y) := by
  obtain ⟨A, B, h1, h2⟩ := Sep.merges k₁ k₂ h
  exact ⟨.or (.pf A) (.pf B), .or (.pf A) (.pf B) h1, .or (.pf A) (.pf B) h2⟩

/-! ## "And vice versa" -/

/-- `Sep` for the two variables taken in the other order. -/
theorem Sep.swap {τ σ : Ty} {Z : V τ → V σ → PF V} (h : Sep Z) : Sep fun y x => Z x y := by
  cases h with
  | left L R hm => exact .right R L fun y x => hm x y
  | right L R hm => exact .left R L fun y x => hm x y

/-- The converse of a step of ✱8·13 is a step of it: Russell's "and vice versa". -/
theorem ExchStep.symm {k₁ k₂ : Bool} {X Y : PF V} (h : ExchStep k₁ k₂ X Y) : ExchStep k₂ k₁ Y X := by
  induction h with
  | here hZ => exact .here (Z := fun y x => _) hZ.swap
  | all _ ih => exact .all ih
  | ex _ ih => exact .ex ih

/-! ## Landini's Switch and ✱8·13 -/

/-- A step of Landini's Switch is a step of ✱8·13: the direction (x)(∃y) to (∃y)(x). -/
theorem SwitchStep.toExch {X Y : PF V} (h : SwitchStep X Y) : ExchStep true false X Y := by
  induction h with
  | here hZ => exact .here hZ
  | all _ ih => exact .all ih
  | ex _ ih => exact .ex ih

/-- A step of ✱8·13 from (x)(∃y) to (∃y)(x) is a step of Landini's Switch. -/
theorem ExchStep.toSwitch {X Y : PF V} (h : ExchStep true false X Y) : SwitchStep X Y := by
  induction h with
  | here hZ => exact .here hZ
  | all _ ih => exact .all ih
  | ex _ ih => exact .ex ih

/-- **Landini's Switch is a derived rule of C** (and of every reading with ✱8·13): each of its steps is
    one of ✱8·13. -/
theorem switch_russell {d : Defs} {X Y : PF V} (h : SwitchStep X Y) (hX : Thm9 S ⟨d, .exch⟩ X) :
    Thm9 S ⟨d, .exch⟩ Y :=
  Thm9.exch rfl h.toExch hX

/-! ## ✱8·13 in ✱9+ -/

/-- In ✱9+, ⊢ (∃x) : (y) . A . ⊃ . (y) : (∃x) . A, without Switch: by ✱9·yy and ✱9·zz it is
    (x) : (y′) : (∃y) : (∃x′) . ∼A(x, y) ∨ A(x′, y′), which ✱9·13 and ✱9·1 prove (dr(S*), Landini 2000,
    §5). -/
theorem exch_imp_plus_ea (pr : Rule) {τ σ : Ty} (Z : V τ → V σ → PF V) :
    Thm9 S ⟨.plus, pr⟩ (Reading.imp ⟨.plus, pr⟩ (PF.qu false fun x => PF.qu true fun y => Z x y)
      (PF.qu true fun y => PF.qu false fun x => Z x y)) :=
  Thm9.gen fun x => Thm9.gen fun y' => exI y' (exI x (idt_plus pr (Z x y')))

/-- In ✱9+, ⊢ (x) : (y) . A . ⊃ . (y) : (x) . A, with one step of Switch: by ✱9·08 it is
    (y′) : (∃x) : (x′) : (∃y) . ∼A(x, y) ∨ A(x′, y′); ✱9·13 and ✱9·1 prove (y′) : (x′) : (∃x) : (∃y),
    and Switch takes (x′) : (∃x) to (∃x) : (x′), the ∨ having x on one side and x′ on the other. -/
theorem exch_imp_plus_aa (pr : Rule) {τ σ : Ty} (Z : V τ → V σ → PF V) :
    Thm9 S ⟨.plus, pr⟩ (Reading.imp ⟨.plus, pr⟩ (PF.qu true fun x => PF.qu true fun y => Z x y)
      (PF.qu true fun y => PF.qu true fun x => Z x y)) :=
  Thm9.gen fun y' => Thm9.switch rfl
    (.here (.right (fun x' => Z x' y') (fun x => .ex fun y => PF.neg (Z x y))
      fun _ _ => .exL fun _ => merge_orPlus _ _))
    (Thm9.gen fun x' => exI x' (exI y' (idt_plus pr (Z x' y'))))

/-- In ✱9+, ⊢ (∃x) : (∃y) . A . ⊃ . (∃y) : (∃x) . A, with one step of Switch: by ✱9·07 it is
    (x) : (∃y′) : (y) : (∃x′) . ∼A(x, y) ∨ A(x′, y′); ✱9·13 and ✱9·1 prove (x) : (y) : (∃y′) : (∃x′), and
    Switch takes (y) : (∃y′) to (∃y′) : (y). -/
theorem exch_imp_plus_ee (pr : Rule) {τ σ : Ty} (Z : V τ → V σ → PF V) :
    Thm9 S ⟨.plus, pr⟩ (Reading.imp ⟨.plus, pr⟩ (PF.qu false fun x => PF.qu false fun y => Z x y)
      (PF.qu false fun y => PF.qu false fun x => Z x y)) :=
  Thm9.gen fun x => Thm9.switch rfl
    (.here (.left (fun y => PF.neg (Z x y)) (fun y' => .ex fun x' => Z x' y')
      fun _ _ => .exR fun _ => merge_orPlus _ _))
    (Thm9.gen fun y => exI y (exI x (idt_plus pr (Z x y))))

/-- In ✱9+, a step of ✱8·13 other than (x)(∃y) to (∃y)(x) as an implication, inside the quantifiers in
    front (✱9·21 and ✱9·22 as rules). -/
theorem exch_imp_plus (pr : Rule) {k₁ k₂ : Bool} (hk : (k₁, k₂) ≠ (true, false)) {X Y : PF V}
    (h : ExchStep k₁ k₂ X Y) : Thm9 S ⟨.plus, pr⟩ (Reading.imp ⟨.plus, pr⟩ X Y) := by
  induction h with
  | @here τ σ Z _ =>
    cases k₁ <;> cases k₂
    · exact exch_imp_plus_ee pr Z
    · exact exch_imp_plus_ea pr Z
    · exact absurd rfl hk
    · exact exch_imp_plus_aa pr Z
  | all _ ih => exact allImp ih
  | ex _ ih => exact exImp_plus ih

/-- **✱8·13 is derivable in ✱9+** (reading L): from ⊢ X and a step of ✱8·13 from X to Y infer ⊢ Y. -/
theorem exch_plus (pr : Rule) {k₁ k₂ : Bool} {X Y : PF V} (h : ExchStep k₁ k₂ X Y)
    (hX : Thm9 S ⟨.plus, pr⟩ X) : Thm9 S ⟨.plus, pr⟩ Y := by
  by_cases hk : (k₁, k₂) = (true, false)
  · cases hk
    exact Thm9.switch rfl h.toSwitch hX
  · exact Thm9.mp hX (exch_imp_plus pr hk h)

/-! ## ✱8·13 and the prenex Switch -/

/-- With the definitions as printed and the prenex Switch, ⊢ X ⊃ Y for every step of ✱8·13 from X to
    Y: Id, then the prenex Switch on the consequent at the front, then ✱9·21 and ✱9·22 as rules. -/
theorem exch_imp_prenex {k₁ k₂ : Bool} {X Y : PF V} (h : ExchStep k₁ k₂ X Y) :
    Thm9 S Reading.prenexSwitch (Reading.prenexSwitch.imp X Y) := by
  induction h with
  | @here τ σ Z hZ =>
    obtain ⟨A, B, h1, h2⟩ := Sep.merges k₁ k₂ hZ
    exact Thm9.prenexSwitch rfl
      (.or (.pf _) (.or (.pf A) (.pf B) h1) (merge_orPrinted _ _))
      (.or (.pf _) (.or (.pf A) (.pf B) h2) (merge_orPrinted _ _)) (idt _)
  | all _ ih => exact allImp ih
  | ex _ ih => exact exImp_printed ih

/-- Every theorem of C (the definitions as printed with ✱8·13) is a theorem of the definitions as
    printed with the prenex Switch, the same proposition. -/
theorem Thm9.russell_toPrenex {p : PF V} (h : Thm9 S Reading.russell p) :
    Thm9 S Reading.prenexSwitch p := by
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
  | exch _ hs _ ih => exact Thm9.mp ih (exch_imp_prenex hs)
  | switch h => cases h
  | prenexSwitch h => cases h

end PM.F9
