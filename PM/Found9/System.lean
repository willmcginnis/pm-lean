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

  Readings. `Thm9 S R` is ✱9's method under the reading `R` (PM/Found9/Syntax.lean): `R.imp`, `R.or`,
  `R.iff` are ✱1·01, ∨ and ✱4·01 under its definitions: as printed (A, and C, the default), ✱9+ (L) or
  the alternative convention (B). A proof stated for every `R` holds under each; where PM justifies a
  line by definitions alone, such a proof takes the step by `by_defs`, which checks it under the
  definitions as printed (A and C), of ✱9+ (L) and of B.

  The rule of reading C, admitted when `R.rule = .exch`:
  - ✱8·13 carried over (`exch`; docs/REPAIRS.md, R1): Russell's rule of the second edition (1925,
    Vol. I, Appendix A, p. 636, page image), "If all occurrences of x are separated from all
    occurrences of y by a certain stroke, we can change the order of x and y in the prefix ... and vice
    versa. Pp", with the stroke read as the ∨ of ✱9's matrix and the prefix as the quantifiers that
    ✱9's definitions put in front (`ExchStep`, A as `Sep` asks). It is the authors' own repair, for ✱8,
    which replaces ✱9; we carry it over to ✱9. It takes the step of ✱9·31 that PM cites as
    definitional.
  The rule of ✱9+ (reading L), admitted exactly when the definitions are ✱9+'s (`R.defs = .plus`):
  - Switch (`switch`; Landini 2000, p. 64; docs/REPAIRS.md, R3): "From B[(x)(∃y)Axy] infer
    B[(∃y)(x)Axy]", A as `Sep` asks (`SwitchStep`). It is Landini's repair of ✱9, and takes the same
    step of ✱9·31. Each of the two rules is derivable in the other's system (PM/Found9/Exch.lean).
  Opt-in rules (PM/Rules/, PM/Systems.lean), carried over so that each `Sys` has its ✱9 counterpart:
  - comprehension (`compr1`, `compr2`), when `S.compr`, for a formula ψ that the style of `S` admits.
    The styles (PM/Pred/) are written for the formulas `QF V` of ✱10's method, so the rule takes ψ as
    such a formula and asserts the ✱9 proposition for which the ✱10 instance stands (`QF.toF9`);
  - the axiom of reducibility ✱12·1, ✱12·11 (`red1`, `red2`), when `S.red`, for any function φ of ✱9,
    in the form printed on p. 174: `⊢ : (∃f) : φx . ≡ₓ . f!x`, with (∃f) primitive as in ✱9.
  And one opt-in rule of the reading, off by default and gated as those are (`R.rule = .prenex`):
  - the prenex Switch (`prenexSwitch`; docs/REPAIRS.md, R5): if X and Y are two prenex forms of the
    same expression t (`Prenex`), from ⊢ X infer ⊢ Y. Our own earlier repair of the same step, kept for
    comparison; whether C or ✱9+ derives it is open (docs/STAR9_FOUNDATION.md). The gates are in the
    reading, not in `Sys`, because `Sys` is shared with ✱10's method, which proves all three rules
    (`exchStep_q10`, `switchStep_q10`, `switch_q10`).
-/
namespace PM.F9
open PF

/-- Asserted propositions of ✱9's method in the system `S`, under the reading `R` (its definitions of
    ∨, with which ✱9+ brings Switch, and the rule it adds: ✱8·13 carried over, or the prenex Switch). -/
inductive Thm9 {V : Ty → Type} (S : Sys) (R : Reading) : PF V → Prop where
  | mp      {p q : PF V} : Thm9 S R p → Thm9 S R (R.imp p q) → Thm9 S R q                 -- ✱9·12, ✱1·1
  | taut    (p : EF V)     : Thm9 S R (.el (EF.imp (.or p p) p))                         -- ✱1·2
  | add     (p q : EF V)   : Thm9 S R (.el (EF.imp q (.or p q)))                         -- ✱1·3
  | perm    (p q : EF V)   : Thm9 S R (.el (EF.imp (.or p q) (.or q p)))                 -- ✱1·4
  | assoc   (p q r : EF V) : Thm9 S R (.el (EF.imp (.or p (.or q r)) (.or q (.or p r)))) -- ✱1·5
  | sum     (p q r : EF V) : Thm9 S R (.el (EF.imp (EF.imp q r) (EF.imp (.or p q) (.or p r))))  -- ✱1·6
  | ex1     {τ : Ty} (φ : V τ → PF V) (x : V τ) : Thm9 S R (R.imp (φ x) (.ex φ))          -- ✱9·1
  | ex2     {τ : Ty} (φ : V τ → PF V) (x y : V τ) :
      Thm9 S R (R.imp (R.or (φ x) (φ y)) (.ex φ))                                      -- ✱9·11
  | gen     {τ : Ty} {φ : V τ → PF V} : (∀ y, Thm9 S R (φ y)) → Thm9 S R (.all φ)      -- ✱9·13
  /-- Comprehension at `fn1 a k`, for a ✱10 formula ψx that the style admits. -/
  | compr1  {a : Ty} {k : Nat} (_ : S.compr = true) (ψ : V a → QF V) (_ : S.style.adm1 k ψ) :
      Thm9 S R (.ex (τ := .fn1 a k) fun f => .all fun x =>
        R.iff ((ψ x).toF9 R.defs) (.el (.app1 f x)))
  /-- Comprehension at `fn2 a b k`. -/
  | compr2  {a b : Ty} {k : Nat} (_ : S.compr = true) (ψ : V a → V b → QF V) (_ : S.style.adm2 k ψ) :
      Thm9 S R (.ex (τ := .fn2 a b k) fun f => .all fun x => .all fun y =>
        R.iff ((ψ x y).toF9 R.defs) (.el (.app2 f x y)))
  /-- ✱12·1 `⊢ : (∃f) : φx . ≡ₓ . f!x` Pp (p. 174). -/
  | red1    {a : Ty} (_ : S.red = true) (φ : V a → PF V) :
      Thm9 S R (.ex (τ := Ty.pred1 a) fun f => .all fun x => R.iff (φ x) (.el (.app1 f x)))
  /-- ✱12·11 `⊢ : (∃f) : φ(x, y) . ≡ₓ,ᵧ . f!(x, y)` Pp (p. 174). -/
  | red2    {a b : Ty} (_ : S.red = true) (φ : V a → V b → PF V) :
      Thm9 S R (.ex (τ := Ty.pred2 a b) fun f => .all fun x => .all fun y =>
        R.iff (φ x y) (.el (.app2 f x y)))
  /-- ✱8·13 carried over to ✱9 (reading C; docs/REPAIRS.md, R1), when `R.rule = .exch`: two adjacent
      quantifiers of the prefix, of any kinds, separated by the ∨ of the matrix (`Sep`), may change
      their order (`ExchStep`), either way. Russell's rule, ✱8·13 of the second edition (p. 636). It
      gives no (x) : (∃y) . R(x, y) : ⊃ : (∃y) : (x) . R(x, y) (`exch_not_general`,
      PM/Found9/Equiv.lean). -/
  | exch    (_ : R.rule = .exch) {k₁ k₂ : Bool} {X Y : PF V} :
      ExchStep k₁ k₂ X Y → Thm9 S R X → Thm9 S R Y
  /-- Switch, the rule of ✱9+ (reading L; Landini 2000, p. 64; docs/REPAIRS.md, R3), when
      `R.defs = .plus`: "From B[(x)(∃y)Axy] infer B[(∃y)(x)Axy]", where A has a connective with every
      free x on one side and every free y on the other (`Sep`, `SwitchStep`). It goes one way only; it
      gives no (x) : (∃y) . R(x, y) : ⊃ : (∃y) : (x) . R(x, y) (`switch_not_general`,
      PM/Found9/Equiv.lean). -/
  | switch  (_ : R.defs = .plus) {X Y : PF V} : SwitchStep X Y → Thm9 S R X → Thm9 S R Y
  /-- The prenex Switch (docs/REPAIRS.md, R5), when `R.rule = .prenex`: if X and Y are two prenex forms
      of the same expression t, from ⊢ X infer ⊢ Y. That is, quantifiers that come from different
      disjuncts may be taken out in another order, each disjunct's own quantifiers keeping theirs. -/
  | prenexSwitch (_ : R.rule = .prenex) {t : PE V} {X Y : PF V} :
      Prenex t X → Prenex t Y → Thm9 S R X → Thm9 S R Y

/-- A step that PM justifies by definitions alone ("[(4).(✱9·06)]"): the proposition is the same as
    the line before. In a proof stated for every reading `R`, this term checks the step under each
    of the three definitions of ∨ (the proof splits on `R.defs` and accepts the line before, unchanged,
    in each case; A and C share theirs); nothing else lets a generic proof use ✱9·03–✱9·08, since
    `R.or` does not compute until the reading is known. -/
macro "by_defs " h:term : term =>
  `(by rcases $(Lean.mkIdent `R):ident with ⟨_ | _ | _, _⟩ <;> exact $h)

end PM.F9
