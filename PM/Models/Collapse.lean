import PM.Quant
/-!
  The collapse model (docs/TYPES_DESIGN.md, decision 11): a function of any order denotes a Boolean
  function of its arguments, so all the orders of a type denote the same function space. With the
  axiom of reducibility this is a model of PM 1910: PM 1910 with reducibility is no stronger than the
  simple theory of types (Holmes 2023), so forgetting orders gives a model.

  This is the general model: any domain of individuals, any interpretation of the letters. Its
  quantifiers over function spaces are classical (`classicalAll`, from `Classical.propDecidable`), so the
  structures built from it use `propext`, `Classical.choice` and `Quot.sound`. Consistency and the
  counter-models are proved instead in the finite coded model (PM/Models/Finite.lean), with no axioms.
-/
namespace PM

/-- What a variable of each type ranges over, given a domain `D` of individuals. The order is ignored. -/
def Ty.den (D : Type) : Ty → Type
  | .ind => D
  | .fn1 a _ => Ty.den D a → Bool
  | .fn2 a b _ => Ty.den D a → Ty.den D b → Bool

/-- A collapse structure from a domain, the letters, and quantifier oracles for every type. -/
def QModel.collapse (D : Type) (R : String → List D → Bool) (A : (τ : Ty) → (τ.den D → Bool) → Bool)
    (hA : ∀ τ f, A τ f = true ↔ ∀ d, f d = true) : QModel where
  den := Ty.den D
  R := R
  ap1 := fun f x => f x
  ap2 := fun f x y => f x y
  lam1 := fun g => g
  lam2 := fun g => g
  ap_lam1 := fun _ _ => rfl
  ap_lam2 := fun _ _ _ => rfl
  A := A
  hA := hA

/-- The classical universal quantifier over any type, as a Boolean (uses `Classical.propDecidable`). -/
noncomputable def classicalAll {T : Type} (f : T → Bool) : Bool :=
  @decide (∀ d, f d = true) (Classical.propDecidable _)

theorem classicalAll_spec {T : Type} (f : T → Bool) : classicalAll f = true ↔ ∀ d, f d = true :=
  ⟨fun h => @of_decide_eq_true _ (Classical.propDecidable _) h,
   fun h => @decide_eq_true _ (Classical.propDecidable _) h⟩

/-- The collapse model over any domain, with classical quantifiers at every type. -/
noncomputable def QModel.classical (D : Type) (R : String → List D → Bool) : QModel :=
  QModel.collapse D R (fun _ => classicalAll) (fun _ => classicalAll_spec)

/-- Consistency in the collapse model (two individuals, classical quantifiers): the letter `p` is not a
    theorem, in any system `S`. Uses the classical axioms of `QModel.classical`; the axiom-free proof is
    `consistent` (PM/Models/Finite.lean). -/
theorem consistent_collapse (S : Sys) :
    ¬ QThm (V := (QModel.classical Bool fun _ xs => xs.headD false).den) S (.atom "p" []) :=
  not_qthm_of_countermodel _ rfl

end PM
