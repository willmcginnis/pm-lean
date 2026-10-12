import PM.Quant
/-!
  The finite coded model (docs/TYPES_DESIGN.md, decision 11; the maintainer's decision on Q5, 2026-10-11): a
  structure in which every type has finitely many values, function values are truth tables, and every
  quantifier is computed by enumeration. So `consistent` and the counter-models use no axioms, for
  every system `S` (every combination of rules and every style), since `qsound` holds for all of them.

  Values are coded by shapes `Sh`: the empty type, the unit type, the Booleans, and pairs. A truth
  table of a function from a shape `A` to a shape `R` is again a shape, `A.pow R` (a pair for a
  Boolean argument, nested tables for a pair of arguments), with `ap` (look up) and `lam` (tabulate)
  and `ap (lam g) x = g x`. The values of `fn1 a k` are the tables of functions from the values of `a`
  to the Booleans, for every k: like the collapse model, this model forgets orders.

  The general model, for any domain, is the classical collapse model (PM/Models/Collapse.lean).
-/
namespace PM

/-- Shapes of finite sets of values. -/
inductive Sh where
  | empty | unit | bool
  | prod : Sh → Sh → Sh

/-- The values of a shape. -/
def Sh.T : Sh → Type
  | .empty => Empty
  | .unit => Unit
  | .bool => Bool
  | .prod A B => A.T × B.T

/-- `A.pow R`: the shape of the truth tables of functions from `A` to `R`. -/
def Sh.pow : Sh → Sh → Sh
  | .empty, _ => .unit
  | .unit, R => R
  | .bool, R => .prod R R
  | .prod A B, R => Sh.pow A (Sh.pow B R)

/-- Look up the value of a table at an argument. -/
def Sh.ap : (A R : Sh) → (A.pow R).T → A.T → R.T
  | .empty, _, _, x => nomatch x
  | .unit, _, f, _ => f
  | .bool, _, f, b => Bool.casesOn (motive := fun _ => _) b f.1 f.2
  | .prod A B, R, f, x => Sh.ap B R (Sh.ap A (B.pow R) f x.1) x.2

/-- Tabulate a function. -/
def Sh.lam : (A R : Sh) → (A.T → R.T) → (A.pow R).T
  | .empty, _, _ => ()
  | .unit, _, g => g ()
  | .bool, _, g => (g false, g true)
  | .prod A B, R, g => Sh.lam A (B.pow R) fun a => Sh.lam B R fun b => g (a, b)

theorem Sh.ap_lam : (A R : Sh) → (g : A.T → R.T) → (x : A.T) → Sh.ap A R (Sh.lam A R g) x = g x
  | .empty, _, _, x => nomatch x
  | .unit, _, _, () => rfl
  | .bool, _, _, false => rfl
  | .bool, _, _, true => rfl
  | .prod A B, R, g, (a, b) => by
    show Sh.ap B R (Sh.ap A (B.pow R) (Sh.lam A (B.pow R) fun a => Sh.lam B R fun b => g (a, b)) a) b = g (a, b)
    rw [Sh.ap_lam A (B.pow R)]
    exact Sh.ap_lam B R _ b

/-- The universal quantifier over a shape, by enumeration. -/
def Sh.all : (A : Sh) → (A.T → Bool) → Bool
  | .empty, _ => true
  | .unit, g => g ()
  | .bool, g => g false && g true
  | .prod A B, g => Sh.all A fun a => Sh.all B fun b => g (a, b)

private theorem and_true_iff' : {a b : Bool} → ((a && b) = true ↔ a = true ∧ b = true)
  | true, true => ⟨fun _ => ⟨rfl, rfl⟩, fun _ => rfl⟩
  | true, false => ⟨fun h => (nomatch h), fun h => (nomatch h.2)⟩
  | false, _ => ⟨fun h => (nomatch h), fun h => (nomatch h.1)⟩

theorem Sh.all_spec : (A : Sh) → (g : A.T → Bool) → (Sh.all A g = true ↔ ∀ x, g x = true)
  | .empty, _ => ⟨fun _ x => (nomatch x), fun _ => rfl⟩
  | .unit, _ => ⟨fun h x => (match x with | () => h), fun h => h ()⟩
  | .bool, _ => ⟨fun h x => match x, and_true_iff'.mp h with
                  | false, ⟨h0, _⟩ => h0
                  | true, ⟨_, h1⟩ => h1,
                 fun h => and_true_iff'.mpr ⟨h false, h true⟩⟩
  | .prod A B, _ =>
    ⟨fun h x => match x with
      | (a, b) => (Sh.all_spec B _).mp ((Sh.all_spec A _).mp h a) b,
     fun h => (Sh.all_spec A _).mpr fun a => (Sh.all_spec B _).mpr fun b => h (a, b)⟩

/-- The shape of the values of a type, given the shape `D` of the individuals. -/
def Ty.sh (D : Sh) : Ty → Sh
  | .ind => D
  | .fn1 a _ => (a.sh D).pow .bool
  | .fn2 a b _ => (a.sh D).pow ((b.sh D).pow .bool)

/-- The finite coded structure with individuals of shape `D`. -/
def finModel (D : Sh) (R : String → List D.T → Bool) : QModel where
  den τ := (τ.sh D).T
  R := R
  ap1 := fun {a _} f x => Sh.ap (a.sh D) .bool f x
  ap2 := fun {a b _} f x y => Sh.ap (b.sh D) .bool (Sh.ap (a.sh D) ((b.sh D).pow .bool) f x) y
  lam1 := fun {a _} g => Sh.lam (a.sh D) .bool g
  lam2 := fun {a b _} g => Sh.lam (a.sh D) ((b.sh D).pow .bool) fun x => Sh.lam (b.sh D) .bool (g x)
  ap_lam1 := fun {a _} g x => Sh.ap_lam (a.sh D) .bool g x
  ap_lam2 := fun {a b _} g x y => by
    show Sh.ap (b.sh D) .bool (Sh.ap (a.sh D) ((b.sh D).pow .bool)
      (Sh.lam (a.sh D) ((b.sh D).pow .bool) fun x => Sh.lam (b.sh D) .bool (g x)) x) y = g x y
    rw [Sh.ap_lam (a.sh D)]
    exact Sh.ap_lam (b.sh D) .bool (g x) y
  A τ := Sh.all (τ.sh D)
  hA τ := Sh.all_spec (τ.sh D)

/-- Two individuals, `false` and `true`; every letter is true of its first argument, so "φ" holds of
    `true` only. -/
def twoModel : QModel := finModel .bool fun _ xs => xs.headD false

/-- The structure with no individuals (functions of individuals still exist: the empty table). -/
def emptyModel : QModel := finModel .empty fun _ _ => false

/-- Consistency: the letter `p` is not a theorem, in any system `S` (every combination of the rules
    and every style). It is stated at the variables of a structure (`twoModel.den`), not at an arbitrary
    family `V`: `QThm` at an arbitrary `V` can be degenerate (an empty or one-element type of functions
    makes ✱10·11 too strong, and ✱12·1 or comprehension then contradicts it; PM/Trap.lean), so a
    consistency claim must name a structure's own variables. Uses no axioms. -/
theorem consistent (S : Sys) : ¬ QThm (V := twoModel.den) S (.atom "p" []) :=
  not_qthm_of_countermodel twoModel rfl

/-- Consistency of the theorems that hold for every family of variables (which is how every PM
    theorem in this project is stated): `p` is not one of them. -/
theorem consistent_all (S : Sys) : ¬ ∀ V : Ty → Type, QThm (V := V) S (.atom "p" []) :=
  fun h => consistent S (h _)

/-- PM p. 137: "⊢ : φy . ⊃ . (x) . φx … means 'However y may be chosen, φy implies (x).φx,' which is in
    general false." It is not a theorem: `twoModel` falsifies it. This is why ✱9·13 / ✱10·11 is a rule
    of inference and not an implication. -/
theorem not_qthm_phiy_imp_all {S : Sys} :
    ¬ ∀ (V : Ty → Type) (φ : V .ind → QF V) (y : V .ind), QThm S (QF.imp (φ y) (.all φ)) :=
  fun h => not_qthm_of_countermodel twoModel
    (p := QF.imp (.atom "φ" [true]) (.all fun x => .atom "φ" [x])) rfl
    (h twoModel.den (fun x => .atom "φ" [x]) true)

/-- ✱10·25 cannot be reversed: `(∃x).φx ⊃ (x).φx` is not a theorem. -/
theorem not_qthm_ex_imp_all {S : Sys} :
    ¬ ∀ (V : Ty → Type) (φ : V .ind → QF V), QThm S (QF.imp (QF.ex φ) (.all φ)) :=
  fun h => not_qthm_of_countermodel twoModel
    (p := QF.imp (QF.ex fun x => .atom "φ" [x]) (.all fun x => .atom "φ" [x])) rfl
    (h twoModel.den (fun x => .atom "φ" [x]))

/-- ✱10·25 `(x) . φx . ⊃ . (∃x) . φx` needs an individual: it is false in `emptyModel`. So the Lean
    statement of ✱10·25 (PM/Star10.lean) takes the real variable y that PM's proof uses. -/
theorem not_qthm_all_imp_ex_empty {S : Sys} :
    ¬ ∀ (V : Ty → Type) (φ : V .ind → QF V), QThm S (QF.imp (.all φ) (QF.ex φ)) :=
  fun h => not_qthm_of_countermodel emptyModel
    (p := QF.imp (.all fun x => .atom "φ" [x]) (QF.ex fun x => .atom "φ" [x])) rfl
    (h emptyModel.den (fun x => .atom "φ" [x]))

end PM
