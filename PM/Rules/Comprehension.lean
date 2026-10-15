import PM.Quant
/-!
  Comprehension at function types, as an opt-in rule. It is OUR reading; PM never states it as a
  proposition, and PM's own proofs get every function they need from ✱12·1 instead (e.g. ✱14·17,
  p. 188). It is kept, marked for what it is for (maintainer, 2026-10-11, open question Q2):
  - it is the rule that forms functions in the predicative fragment (no ✱12·1), which the 1925 second
    edition needs;
  - it gives the check `q12_1_of_var` (PM/Star12.lean);
  - the styles of predicativity (PM/Pred/) differ only in what it accepts.

  Warrant. ✱9·15 (p. 138) and ✱10·122 (p. 146): "If, for some a, there is a proposition φa, then there
  is a function φx̂". Applied to an apparent variable over functions of a given order, with ✱10·24 (or
  ✱10·1), this gives an existential whose witness is that function. PM licenses functions of a given
  order to be formed from formulas whose variables are of lower order: pp. 54–56, 169–171, and p. 172,
  "non-predicative functions always result from such as are predicative by means of generalization".

  The rules are the constructors `QThm.compr1` and `QThm.compr2`, usable only in a system with
  `compr`, and only at formulas the system's style admits (`Style.adm1`, `Style.adm2`).
-/
namespace PM
open QF

/-- The system `S` has comprehension at function types. -/
class Comprehension {V : Ty → Type} (S : Sys V) : Prop where
  compr : S.compr = true

variable {V : Ty → Type} {S : Sys V}

/-- Comprehension: `⊢ (∃f : fn1 a k) : ψx . ≡ₓ . f x` for ψ that the style admits at `fn1 a k`. -/
theorem comprehension1 [Comprehension S] {a : Ty} {k : Nat} (ψ : V a → QF V)
    (h : S.style.adm1 k ψ) :
    QThm S (ex (τ := .fn1 a k) fun f => fiff ψ fun x => .app1 f x) :=
  QThm.compr1 Comprehension.compr ψ h

/-- Comprehension for two arguments. -/
theorem comprehension2 [Comprehension S] {a b : Ty} {k : Nat} (ψ : V a → V b → QF V)
    (h : S.style.adm2 k ψ) :
    QThm S (ex (τ := .fn2 a b k) fun f => .all fun x => .all fun y => iff (ψ x y) (.app2 f x y)) :=
  QThm.compr2 Comprehension.compr ψ h

end PM
