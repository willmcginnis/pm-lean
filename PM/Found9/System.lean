import PM.Found9.Syntax
/-!
  ✱9's primitive propositions (pp. 136–138), as the inductive predicate `Thm9 S`.

  "The primitive propositions required are six in number, and may be divided into three sets of two"
  (p. 136):
    ✱9·1   ⊢ : φx . ⊃ . (∃z) . φz                               Pp   (`Thm9.ex1`)
    ✱9·11  ⊢ : φx ∨ φy . ⊃ . (∃z) . φz                          Pp   (`Thm9.ex2`)
    ✱9·12  What is implied by a true premiss is true.            Pp   (`Thm9.mp`)
    ✱9·13  In any assertion containing a real variable, this real variable may be turned into an
           apparent variable of which all possible values are asserted to satisfy the function in
           question.                                             Pp   (`Thm9.gen`)
    ✱9·14, ✱9·15 (types and significance): built into the syntax (PM/Found9/Syntax.lean).
  Before these, ✱9 assumes "the primitive ideas and propositions of ✱1 as applied to elementary
  propositions" (p. 134): ✱1·2–✱1·6 for elementary p, q, r (`Thm9.taut` … `Thm9.sum`); ✱1·1 is ✱9·12.

  Which φ. ✱9·1 and ✱9·11 are the two propositions "which effect the passage from elementary to
  first-order propositions" (p. 136), and "the above definitions can be repeated for successive types"
  (p. 136). PM uses ✱9·1 with a φ that already contains apparent variables: in the proof of ✱9·21
  (p. 139), line (3) applies ✱9·1 to line (2), which contains (∃y). So `ex1` and `ex2` are stated for
  every function φ, with or without apparent variables. ✱1·2–✱1·6 are stated for elementary
  propositions only: that they hold for the others is what ✱9·3–✱9·52 set out to prove (p. 138).

  Real variables. "From the purely technical point of view" ✱9·12 is also used "as in ✱1·11" (p. 137),
  from ⊢ . φx and ⊢ . φx ⊃ ψx to ⊢ . ψx with x real: in Lean that is `mp` under a binder of the real
  variable, so it needs no separate rule.

  Opt-in rules (PM/Rules/, PM/Systems.lean), carried over so that each `Sys` has its ✱9 counterpart:
  - comprehension (`compr1`, `compr2`), when `S.compr`, for a formula ψ that the style of `S` admits.
    The styles (PM/Pred/) are written for the formulas `QF V` of ✱10's method, so the rule takes ψ as
    such a formula and asserts the ✱9 proposition for which the ✱10 instance stands (`QF.toF9`);
  - the axiom of reducibility ✱12·1, ✱12·11 (`red1`, `red2`), when `S.red`, for any function φ of ✱9,
    in the form printed on p. 174: `⊢ : (∃f) : φx . ≡ₓ . f!x`, with (∃f) primitive as in ✱9.
-/
namespace PM.F9
open PF

/-- Asserted propositions of ✱9's method in the system `S`. -/
inductive Thm9 {V : Ty → Type} (S : Sys) : PF V → Prop where
  | mp      {p q : PF V} : Thm9 S p → Thm9 S (imp p q) → Thm9 S q                       -- ✱9·12, ✱1·1
  | taut    (p : EF V)     : Thm9 S (.el (EF.imp (.or p p) p))                           -- ✱1·2
  | add     (p q : EF V)   : Thm9 S (.el (EF.imp q (.or p q)))                           -- ✱1·3
  | perm    (p q : EF V)   : Thm9 S (.el (EF.imp (.or p q) (.or q p)))                   -- ✱1·4
  | assoc   (p q r : EF V) : Thm9 S (.el (EF.imp (.or p (.or q r)) (.or q (.or p r))))   -- ✱1·5
  | sum     (p q r : EF V) : Thm9 S (.el (EF.imp (EF.imp q r) (EF.imp (.or p q) (.or p r))))  -- ✱1·6
  | ex1     {τ : Ty} (φ : V τ → PF V) (x : V τ) : Thm9 S (imp (φ x) (.ex φ))              -- ✱9·1
  | ex2     {τ : Ty} (φ : V τ → PF V) (x y : V τ) :
      Thm9 S (imp (PF.or (φ x) (φ y)) (.ex φ))                                          -- ✱9·11
  | gen     {τ : Ty} {φ : V τ → PF V} : (∀ y, Thm9 S (φ y)) → Thm9 S (.all φ)          -- ✱9·13
  /-- Comprehension at `fn1 a k`, for a ✱10 formula ψx that the style admits. -/
  | compr1  {a : Ty} {k : Nat} (_ : S.compr = true) (ψ : V a → QF V) (_ : S.style.adm1 k ψ) :
      Thm9 S (.ex (τ := .fn1 a k) fun f => .all fun x => iff (ψ x).toF9 (.el (.app1 f x)))
  /-- Comprehension at `fn2 a b k`. -/
  | compr2  {a b : Ty} {k : Nat} (_ : S.compr = true) (ψ : V a → V b → QF V) (_ : S.style.adm2 k ψ) :
      Thm9 S (.ex (τ := .fn2 a b k) fun f => .all fun x => .all fun y =>
        iff (ψ x y).toF9 (.el (.app2 f x y)))
  /-- ✱12·1 `⊢ : (∃f) : φx . ≡ₓ . f!x` Pp (p. 174). -/
  | red1    {a : Ty} (_ : S.red = true) (φ : V a → PF V) :
      Thm9 S (.ex (τ := Ty.pred1 a) fun f => .all fun x => iff (φ x) (.el (.app1 f x)))
  /-- ✱12·11 `⊢ : (∃f) : φ(x, y) . ≡ₓ,ᵧ . f!(x, y)` Pp (p. 174). -/
  | red2    {a b : Ty} (_ : S.red = true) (φ : V a → V b → PF V) :
      Thm9 S (.ex (τ := Ty.pred2 a b) fun f => .all fun x => .all fun y =>
        iff (φ x y) (.el (.app2 f x y)))

end PM.F9
