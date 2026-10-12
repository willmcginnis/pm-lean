import PM.Star14
/-!
  ✱20: general theory of classes (1910 print, pp. 196–210; summary pp. 196–199, definitions
  pp. 197–200, numbered propositions pp. 200–210). The print has 55 numbered propositions, ✱20·1 to
  ✱20·81. 51 are proved here. ✱20·631 and ✱20·632 concern significance and are built into the syntax,
  as ✱10·121 and ✱10·122 are (PM/Star10.lean). ✱20·4 and ✱20·41 are not formalized; they are about
  "Cls" (see "Not formalized" below).

  Statements are read from the Gutenberg #78050 transcription of the 1910 print (its formula source),
  not from the scan images. Each proof follows PM's Dem. line by line, or uses the propositions of PM's
  bracketed hint in PM's order; the comment on each Lean line gives PM's line or hint.
  `data/star20_ledger.json` records, per proposition, which cited propositions are used and which
  further ones were needed.

  Classes are incomplete symbols: ẑ(ψz) has meaning only in a context f{ẑ(ψz)}, defined by ✱20·01 in
  terms of a predicative function φ!ẑ formally equivalent to ψẑ. As for descriptions (PM/Star14.lean),
  the context is an explicit argument of the macro:
    ✱20·01  f{ẑ(ψz)} . = : (∃φ) : φ!x . ≡ₓ . ψx : f{φ!ẑ}   Df   (`QF.cls ψ f`)
    ✱20·02  x ∈ (φ!ẑ) . = . φ!x                            Df   (`QF.mem x φ`)
    ✱20·04–✱20·06  x, y ∈ α;  x, y, z ∈ α;  x ∼∈ α        Df   (`QF.mem2`, `QF.mem3`, `QF.nmem`)
    ✱20·07  (α) . fα . = . (φ) . f{ẑ(φ!z)}                 Df   (`QF.clsAll`)
    ✱20·071 (∃α) . fα . = . (∃φ) . f{ẑ(φ!z)}               Df   (`QF.clsEx`)
    ✱20·072 [(ια)(φα)] . f(ια)(φα) . = : (∃γ) : φα . ≡_α . α = γ : fγ   Df   (`QF.descCls`)
  Identity of classes is ✱13·01 at the type of predicative functions, eliminated by ✱20·01 twice, the
  first class having the larger scope "because it occurs first" (p. 201): `QF.clsEq ψ χ`. So ✱13·01 is
  used at the type `Ty.pred1 a`, and ✱12·1 at the type of its argument, through ✱13·195 (typical
  ambiguity: the same Lean definitions and theorems at a higher type).

  Greek letters (pp. 197–199, 203, 208). A class is written by its defining function: a real Greek
  letter α stands for "some expression of the form ẑ(ψz)" (p. 203), so it is a formula with a hole
  `ψ : V a → QF V`, of any order; an apparent one "stand[s] for a symbol of the form ẑ(φ!z), where φ
  is properly the apparent variable concerned" (p. 198), so `clsAll` and `clsEx` bind φ and put
  `pf φ` (φ!ẑ as a formula with a hole) for α. An expression fα containing α is a Lean function
  `F : (V a → QF V) → QF V`, in which each occurrence of the class is eliminated where it stands.
  The scope conventions are those of ✱14 (p. 197): an unmarked class has the smallest scope, so
  `x ∈ α` is `clsMem x α`, i.e. ✱20·01 with context x ∈ φ!ẑ; in an identity the class written first
  has the larger scope; and where classes and descriptions both occur, "the descriptions are to have
  a larger scope than the classes" (p. 204). A generic expression "f{ẑ(ψz)}" or "fα" of PM's general
  propositions is `cls ψ f`, for an arbitrary context f of a predicative function: "'fα' therefore
  stands for 'f{ẑ(φz)}.' This is, in reality, a function of φẑ, namely the extensional function
  associated with f(ψ!ẑ) by means of ✱20·01" (p. 199).

  Where PM's proofs instantiate an apparent class at a class ẑ(φz) whose defining function need not
  be predicative, citing ✱10·1 or ✱10·24 (✱20·25, ✱20·53, ✱20·54), the step is the class analogue,
  as p. 206 says ("In practice we also need ⊢ : (α) . fα . ⊃ . f{ẑ(ψz)}. This is ✱20·17"): ✱12·1
  gives a predicative φ formally equivalent to the defining function, ✱10·1 (or ✱10·24) is used at
  φ, and each occurrence of the class is carried from φ!ẑ to ẑ(φz) by ✱20·11 (`qclsAllAt`,
  `qclsExAt`).

  Not formalized:
  - ✱20·03 (Cls), ✱20·08 and ✱20·081 (classes of classes, f{α̂(ψα)} and α ∈ ψ!α̂), and so ✱20·4
    and ✱20·41, which state α ∈ Cls. ✱20·08 binds a predicative function of classes and ranges
    ≡_α over classes; how to encode that is a design decision that has not been made.
  - ✱20·631, ✱20·632 (significance, built into the syntax as ✱10·121, ✱10·122 are). ✱20·62 and
    ✱20·633, the analogues of the rules ✱10·11 and ✱11·07, are proved as rules (`q20_62`, `q20_633`).
  - E!(ια)(φα), which ✱20·56 uses, is not among PM's definitions; p. 206 keeps "the analogues of
    ✱20·01·02 and of ✱14·01" as definitions. `QF.exists1Cls` is the analogue of ✱14·02.

  Steps done silently are those of PM/Star11.lean's header and of PM/Star14.lean's (chaining ⊃ and ≡
  lines under a hypothesis). Any other proposition a proof needs is named in its docstring and listed as
  `extra_used` in the ledger.

  Names: `q20_1` is ✱20·1, and so on. ψ, χ, φ are formulas with a hole (defining functions of classes,
  PM's real function variables of any order); f, g are contexts of a predicative function; F, G, Φ are
  expressions containing a class.
-/
namespace PM
open QF

namespace QF
variable {V : Ty → Type} {S : Sys}
/-- ✱20·01 `f{ẑ(ψz)} . = : (∃φ) : φ!x . ≡ₓ . ψx : f{φ!ẑ}` Df. `f` is the context of the class. -/
@[reducible] def cls {a : Ty} (ψ : V a → QF V) (f : V (Ty.pred1 a) → QF V) : QF V :=
  ex (τ := Ty.pred1 a) fun φ => QF.and (fiff (fun x => .app1 φ x) ψ) (f φ)
/-- ✱20·02 `x ∈ (φ!ẑ) . = . φ!x` Df -/
@[reducible] def mem {a : Ty} (x : V a) (φ : V (Ty.pred1 a)) : QF V := .app1 φ x
/-- φ!ẑ as a formula with a hole: the defining function of the class ẑ(φ!z). -/
@[reducible] def pf {a : Ty} (φ : V (Ty.pred1 a)) : V a → QF V := fun z => .app1 φ z
/-- `ẑ(ψz) = ẑ(χz)`: ✱13·01 between predicative functions, with ✱20·01 applied to ẑ(ψz) first and
    then to ẑ(χz) (p. 201). -/
@[reducible] def clsEq {a : Ty} (ψ χ : V a → QF V) : QF V :=
  cls ψ fun φ => cls χ fun θ => ident φ θ
/-- `x ∈ ẑ(ψz)`: ✱20·02 with ✱20·01 applied to the class, whose scope is x ∈ ẑ(ψz) (the smallest). -/
@[reducible] def clsMem {a : Ty} (x : V a) (ψ : V a → QF V) : QF V := cls ψ fun φ => mem x φ
/-- ✱20·04 `x, y ∈ α . = . x ∈ α . y ∈ α` Df -/
@[reducible] def mem2 {a : Ty} (x y : V a) (α : V a → QF V) : QF V := QF.and (clsMem x α) (clsMem y α)
/-- ✱20·05 `x, y, z ∈ α . = . x, y ∈ α . z ∈ α` Df -/
@[reducible] def mem3 {a : Ty} (x y z : V a) (α : V a → QF V) : QF V := QF.and (mem2 x y α) (clsMem z α)
/-- ✱20·06 `x ∼∈ α . = . ∼(x ∈ α)` Df -/
@[reducible] def nmem {a : Ty} (x : V a) (α : V a → QF V) : QF V := .neg (clsMem x α)
/-- ✱20·07 `(α) . fα . = . (φ) . f{ẑ(φ!z)}` Df. `F` is the expression fα as a function of the class. -/
@[reducible] def clsAll {a : Ty} (F : (V a → QF V) → QF V) : QF V := .all (τ := Ty.pred1 a) fun φ => F (pf φ)
/-- ✱20·071 `(∃α) . fα . = . (∃φ) . f{ẑ(φ!z)}` Df -/
@[reducible] def clsEx {a : Ty} (F : (V a → QF V) → QF V) : QF V := ex (τ := Ty.pred1 a) fun φ => F (pf φ)
/-- ✱20·072 `[(ια)(φα)] . f(ια)(φα) . = : (∃γ) : φα . ≡_α . α = γ : fγ` Df. `Φ` is the condition, `G` the
    scope. -/
@[reducible] def descCls {a : Ty} (Φ G : (V a → QF V) → QF V) : QF V :=
  clsEx fun γ => QF.and (clsAll fun α => iff (Φ α) (clsEq α γ)) (G γ)
/-- `E!(ια)(φα) . = : (∃γ) : φα . ≡_α . α = γ`, the analogue of ✱14·02 that ✱20·56 uses (not printed as a
    definition in ✱20). -/
@[reducible] def exists1Cls {a : Ty} (Φ : (V a → QF V) → QF V) : QF V :=
  clsEx fun γ => clsAll fun α => iff (Φ α) (clsEq α γ)
end QF

variable {V : Ty → Type} {S : Sys} {a : Ty}

/-- From `⊢ . p`, `⊢ : p . q . ≡ . q` (✱3·27, ✱3·2). -/
theorem qand_true_left {p q : QF V} (hp : QThm S p) : QThm S (iff (QF.and p q) q) :=
  qiffI (QL.t3_27 p q) (QThm.mp hp (QL.t3_2 p q))

/-! ## Further steps, each listed in the ledger where used -/

/-- From `⊢ . A ≡ A'` and `⊢ . B ≡ B'`, `⊢ : A ≡ B . ≡ . A' ≡ B'` (✱4·86, and ✱4·86 for the second member). -/
theorem qiffIffCongr {A A' B B' : QF V} (h1 : QThm S (iff A A')) (h2 : QThm S (iff B B')) :
    QThm S (iff (iff A B) (iff A' B')) :=
  qiffTrans (QThm.mp h1 (QL.t4_86 A A' B)) (QThm.mp h2 (qiffCongrRImp A' B B'))
/-- From `⊢ . A ≡ A'` and `⊢ . B ≡ B'`, `⊢ : A ⊃ B . ≡ . A' ⊃ B'` (✱4·84, ✱4·85). -/
theorem qimpIffCongr {A A' B B' : QF V} (h1 : QThm S (iff A A')) (h2 : QThm S (iff B B')) :
    QThm S (iff (imp A B) (imp A' B')) :=
  qiffTrans (QThm.mp h1 (QL.t4_84 A A' B)) (QThm.mp h2 (QL.t4_85 B B' A'))
/-- Under a hypothesis: `H ⊃ . A ≡ A'` and `H ⊃ . B ≡ B'` give `H ⊃ : A ≡ B . ≡ . A' ≡ B'` (✱4·86). -/
theorem qimpIffIffCongr {H A A' B B' : QF V} (h1 : QThm S (imp H (iff A A'))) (h2 : QThm S (imp H (iff B B'))) :
    QThm S (imp H (iff (iff A B) (iff A' B'))) :=
  qimpIffTrans (qsyl h1 (QL.t4_86 A A' B)) (qsyl h2 (qiffCongrRImp A' B B'))
/-- Under a hypothesis: `H ⊃ . A ≡ A'` and `H ⊃ . B ≡ B'` give `H ⊃ : A ⊃ B . ≡ . A' ⊃ B'` (✱4·84, ✱4·85). -/
theorem qimpImpIffCongr {H A A' B B' : QF V} (h1 : QThm S (imp H (iff A A'))) (h2 : QThm S (imp H (iff B B'))) :
    QThm S (imp H (iff (imp A B) (imp A' B'))) :=
  qimpIffTrans (qsyl h1 (QL.t4_84 A A' B)) (qsyl h2 (QL.t4_85 B B' A'))

/-! ## ✱20·1–✱20·112 -/

/-- ✱20·1 `⊢ :. f{ẑ(ψz)} . ≡ : (∃φ) : φ!x . ≡ₓ . ψx : f{φ!ẑ}` [✱4·2 . (✱20·01)] -/
theorem q20_1 (ψ : V a → QF V) (f : V (Ty.pred1 a) → QF V) :
    QThm S (iff (cls ψ f) (ex (τ := Ty.pred1 a) fun φ => QF.and (fiff (fun x => .app1 φ x) ψ) (f φ))) :=
  QL.t4_2 _

/-- ✱20·11 `⊢ :. ψx . ≡ₓ . χx : ⊃ : f{ẑ(ψz)} . ≡ . f{ẑ(χz)}`. ✱4·86 for the second member (with ✱4·21) is
    carried under (x) and then (φ) by the ✱10·11·27·271·21 pattern. -/
theorem q20_11 (ψ χ : V a → QF V) (f : V (Ty.pred1 a) → QF V) :
    QThm S (imp (fiff ψ χ) (iff (cls ψ f) (cls χ f))) :=
  have h : ∀ φ : V (Ty.pred1 a), QThm S (imp (fiff ψ χ)
      (iff (QF.and (fiff (pf φ) ψ) (f φ)) (QF.and (fiff (pf φ) χ) (f φ)))) := fun φ =>
    qsyl (qsyl (q10_11_27 fun x => qiffCongrRImp (.app1 φ x) (ψ x) (χ x))
        (q10_271 (fun x => iff (.app1 φ x) (ψ x)) fun x => iff (.app1 φ x) (χ x)))  -- ✱4·86
      (QL.t4_36 _ _ (f φ))                                                        -- [✱4·36]
  qsyl (q10_11_21 h) (q10_281 _ _)                                                -- [✱10·281] [✱20·1]

/-- ✱20·111 `⊢ :. f(φ!ẑ) . ≡_φ . g(φ!ẑ) : ⊃ : f{ẑ(φ!z)} . ≡_φ . g{ẑ(φ!z)}`. PM's first line reads
    f(ψ!ẑ) ≡ g(ψ!ẑ) from Hp, which is ✱10·1 at ψ; "Fact" for the ≡ of products is ✱4·36, here on the
    second factor (with ✱4·3, `qandCongrRImp`). -/
theorem q20_111 (f g : V (Ty.pred1 a) → QF V) :
    QThm S (imp (fiff f g) (fiff (fun φ => cls (pf φ) f) (fun φ => cls (pf φ) g))) :=
  have h1 : ∀ φ : V (Ty.pred1 a), QThm S (imp (fiff f g) (iff (cls (pf φ) f) (cls (pf φ) g))) := fun φ =>
    qsyl (q10_11_21 fun ψ => qsyl (q10_1 (fun ψ => iff (f ψ) (g ψ)) ψ)
        (qandCongrRImp (f ψ) (g ψ) (fiff (pf ψ) (pf φ))))                          -- Fact [✱10·11·21]
      (q10_281 _ _)                                                               -- [✱10·281] [✱20·1] (1)
  q10_11_21 h1                                                                    -- (1).✱10·11·21

/-- ✱20·112 `⊢ :. (∃g) :. f{ẑ(φ!z)} . ≡_φ . g!{ẑ(φ!z)}`: "the axiom of reducibility still holds for
    classes as arguments". ✱12·1 is used at the type of predicative functions, and (1).✱20·111 is
    carried under (∃g). -/
theorem q20_112 [Reducibility S] (f : V (Ty.pred1 a) → QF V) :
    QThm S (ex (τ := Ty.pred1 (Ty.pred1 a)) fun g =>
      fiff (fun φ => cls (pf φ) f) (fun φ => cls (pf φ) fun χ => .app1 g χ)) :=
  QThm.mp (q12_1 f) (q10_11_28 fun g => q20_111 f fun χ => .app1 g χ)            -- ✱12·1 (1) . (1).✱20·111

/-! ## ✱20·12–✱20·19 -/

/-- ✱12·1 with the orientation of ✱20·01: `(∃φ) : φ!x . ≡ₓ . ψx` (✱10·32 under (∃φ)). -/
theorem qred1cls [Reducibility S] (ψ : V a → QF V) : QThm S (ex (τ := Ty.pred1 a) fun φ => fiff (pf φ) ψ) :=
  QThm.mp (q12_1 ψ) (q10_11_28 fun φ => qiffMp (q10_32 ψ (pf φ)))

/-- ✱20·12 `⊢ : (∃φ) : φ!x . ≡ₓ . ψx : f{ẑ(ψz)} . ≡ . f{ẑ(φ!z)}` [✱20·11 . ✱12·1]. ✱12·1 gives ψx ≡ₓ φ!x,
    turned by ✱10·32 for the first factor and joined with ✱20·11 by Comp (✱3·43), under (∃φ). -/
theorem q20_12 [Reducibility S] (ψ : V a → QF V) (f : V (Ty.pred1 a) → QF V) :
    QThm S (ex (τ := Ty.pred1 a) fun φ => QF.and (fiff (pf φ) ψ) (iff (cls ψ f) (cls (pf φ) f))) :=
  QThm.mp (q12_1 ψ) (q10_11_28 fun φ =>
    qcomp (qiffMp (q10_32 ψ (pf φ))) (q20_11 ψ (pf φ) f))                          -- ✱20·11 . ✱12·1

/-- ✱20·13 `⊢ :. ψx . ≡ₓ . χx : ⊃ . ẑ(ψz) = ẑ(χz)`. PM's (1) is the definitional unfolding (✱20·1
    twice). In (2), ✱12·1 gives (∃φ) : ψx ≡ₓ φ!x, read as φ!x ≡ₓ ψx by ✱10·32; with Hp, ✱10·321 gives
    φ!x ≡ₓ χx; and the step PM takes by ✱13·195 (from F φ to (∃θ) : θ = φ . F θ) is taken by its
    proof's first line, ✱3·2 . ✱13·15 . ✱10·24, with θ = φ written φ = θ as ✱13·01 needs. The two
    hypotheses are joined by Comp and Exp (✱3·43, ✱3·3) and carried under (∃φ) by ✱10·11·21·28. -/
theorem q20_13 [Reducibility S] (ψ χ : V a → QF V) : QThm S (imp (fiff ψ χ) (clsEq ψ χ)) :=
  let P : V (Ty.pred1 a) → QF V := fun φ => fiff (fun x => .app1 φ x) ψ
  let R : V (Ty.pred1 a) → QF V := fun φ => QF.and (P φ) (cls χ fun θ => ident φ θ)
  have h1 : QThm S (ex fun φ => fiff ψ fun x => .app1 φ x) := q12_1 ψ                -- ✱12·1
  have step : ∀ φ : V (Ty.pred1 a), QThm S (imp (fiff ψ χ) (imp (fiff ψ fun x => .app1 φ x) (R φ))) :=
    fun φ =>
      let K := QF.and (fiff ψ χ) (fiff ψ fun x => .app1 φ x)
      have k1 : QThm S (imp K (P φ)) := qsyl (QL.t3_27 _ _) (qiffMp (q10_32 _ _))  -- ✱10·32
      have k2 : QThm S (imp K (fiff (fun x => .app1 φ x) χ)) :=
        qsyl (q10_321 ψ χ fun x => .app1 φ x) (qiffMp (q10_32 _ _))              -- ✱10·321
      have k3 : QThm S (imp (fiff (fun x => .app1 φ x) χ) (cls χ fun θ => ident φ θ)) :=
        qsyl (QThm.mp (q13_15 φ) (QThm.mp (QL.t3_2 _ _) (QL.t2_04 _ _ _)))       -- ✱3·2 . ✱13·15
          (q10_24 (fun θ => QF.and (fiff (fun x => .app1 θ x) χ) (ident φ θ)) φ) -- ✱10·24 [✱13·195]
      QThm.mp (qcomp k1 (qsyl k2 k3)) (QL.t3_3 _ _ _)                            -- Comp . Exp
  have h2 := qsyl (q10_11_21 step) (q10_28 _ R)                                  -- ✱10·11·21·28
  QThm.mp h1 (QThm.mp h2 (QL.t2_04 _ _ _))                                       -- (1).(2)

/-- ✱20·14 `⊢ :. ẑ(ψz) = ẑ(χz) . ⊃ : ψx . ≡ₓ . χx`. ✱13·195 needs `θ = φ . F θ` where ✱20·01 gives
    `F θ : φ = θ`; the factors are commuted (✱4·3) and φ = θ turned by ✱13·16 (with ✱4·36), under (∃θ)
    by ✱10·11·281. Then ✱10·321 (PM: ✱10·322, for PM's orientation ψx ≡ₓ φ!x) inside (∃φ) and ✱10·23. -/
theorem q20_14 [Reducibility S] (ψ χ : V a → QF V) : QThm S (imp (clsEq ψ χ) (fiff ψ χ)) :=
  let P : V (Ty.pred1 a) → QF V := fun φ => fiff (fun x => .app1 φ x) ψ
  let Q : V (Ty.pred1 a) → QF V := fun θ => fiff (fun x => .app1 θ x) χ
  have j : ∀ φ : V (Ty.pred1 a), QThm S (iff (cls χ fun θ => ident φ θ) (Q φ)) := fun φ =>
    qiffTrans (q10_11_281 fun θ =>
        qiffTrans (QL.t4_3 (Q θ) (ident φ θ)) (QThm.mp (q13_16 φ θ) (QL.t4_36 _ _ _)))  -- ✱20·1 . ✱13·16
      (q13_195 Q φ)                                                              -- [✱13·195]
  have k : ∀ φ : V (Ty.pred1 a), QThm S (imp (QF.and (P φ) (cls χ fun θ => ident φ θ)) (fiff ψ χ)) :=
    fun φ => qsyl (qandR (qiffMp (j φ))) (q10_321 (fun x => .app1 φ x) ψ χ)    -- [✱10·322]
  QThm.mp (q10_11 k) (qiffMp (q10_23 _ _))                                       -- ✱10·11·23

/-- ✱20·15 `⊢ :. ψx . ≡ₓ . χx : ≡ . ẑ(ψz) = ẑ(χz)` [✱20·13·14]. "Two functions determine the same class
    when, and only when, they are formally equivalent" (p. 201). -/
theorem q20_15 [Reducibility S] (ψ χ : V a → QF V) : QThm S (iff (fiff ψ χ) (clsEq ψ χ)) :=
  qiffI (q20_13 ψ χ) (q20_14 ψ χ)

/-- ✱20·151 `⊢ . (∃φ) . ẑ(ψz) = ẑ(φ!z)`: "all classes can be obtained from predicative functions". -/
theorem q20_151 [Reducibility S] (ψ : V a → QF V) : QThm S (ex (τ := Ty.pred1 a) fun φ => clsEq ψ (pf φ)) :=
  QThm.mp (q12_1 ψ) (q10_11_28 fun φ => qiffMp (q20_15 ψ (pf φ)))              -- ✱20·15 . ✱10·11·28 (1) . (1).✱12·1

/-- ✱20·16 `⊢ : (∃φ) : f{ẑ(ψz)} . ≡ . f{ẑ(φ!z)}` [✱20·12]. The second factor is taken by ✱3·27 under (∃φ). -/
theorem q20_16 [Reducibility S] (ψ : V a → QF V) (f : V (Ty.pred1 a) → QF V) :
    QThm S (ex (τ := Ty.pred1 a) fun φ => iff (cls ψ f) (cls (pf φ) f)) :=
  QThm.mp (q20_12 ψ f) (q10_11_28 fun _ => QL.t3_27 _ _)                         -- [✱20·12]

/-- ✱20·17 `⊢ : (φ) . f{ẑ(φ!z)} . ⊃ . f{ẑ(ψz)}` [✱20·16 . ✱10·1]. For each φ, ✱10·1 and the converse half
    of ✱20·16's equivalence (✱3·27) are chained by ✱2·06; (∃φ) is removed by ✱10·11, ✱10·23. -/
theorem q20_17 [Reducibility S] (ψ : V a → QF V) (f : V (Ty.pred1 a) → QF V) :
    QThm S (imp (.all (τ := Ty.pred1 a) fun φ => cls (pf φ) f) (cls ψ f)) :=
  QThm.mp (q20_16 ψ f) (QThm.mp (q10_11 fun φ =>
      qsyl (QL.t3_27 _ _) (QThm.mp (q10_1 (fun φ => cls (pf φ) f) φ) (QL.t2_06 _ _ _)))  -- ✱10·1
    (qiffMp (q10_23 _ _)))                                                        -- [✱20·16]

/-- ✱20·18 `⊢ :. ẑ(ψz) = ẑ(χz) . ⊃ : f{ẑ(ψz)} . ≡ . f{ẑ(χz)}` [✱20·11·15]: "the analogue of ✱13·12". -/
theorem q20_18 [Reducibility S] (ψ χ : V a → QF V) (f : V (Ty.pred1 a) → QF V) :
    QThm S (imp (clsEq ψ χ) (iff (cls ψ f) (cls χ f))) :=
  qsyl (qiffMpr (q20_15 ψ χ)) (q20_11 ψ χ f)                                      -- ✱20·11·15

/-- The step `[✱20·112 . ✱10·1] [✱4·2]` of ✱20·19: `(f) : f!ẑ(φ!z) . ⊃ . f!ẑ(θ!z) : ⊃ . φ!x ≡ₓ θ!x`.
    ✱20·112 for the context φ!x ≡ₓ χ!x gives g with g!ẑ(χ!z) ≡_χ (φ!x ≡ₓ χ!x) in the form of ✱20·01;
    ✱10·1 at g, and at φ and θ (joined by ✱4·84, ✱4·85, the converse half by ✱3·27, and ✱2·06), gives
    the implication for the context, and (∃g) is removed by ✱10·11, ✱10·23. PM reads the context of
    ẑ(θ!z) as φ!x ≡ₓ θ!x; from its ✱20·01 form (∃χ) : χ!x ≡ₓ θ!x : φ!x ≡ₓ χ!x it follows by ✱10·301
    (factors commuted, ✱3·22) under (∃χ) (✱10·11, ✱10·23), and the form at φ holds by ✱4·2 (under
    ✱10·11), ✱10·13 and ✱10·24; it is detached by ✱2·27. -/
theorem qclsIndisc [Reducibility S] (φ θ : V (Ty.pred1 a)) :
    QThm S (imp (.all (τ := Ty.pred1 (Ty.pred1 a)) fun f =>
        imp (cls (pf φ) fun φ' => .app1 f φ') (cls (pf θ) fun φ' => .app1 f φ'))
      (fiff (pf φ) (pf θ))) :=
  let F : V (Ty.pred1 a) → QF V := fun χ => fiff (pf φ) (pf χ)
  let P : QF V := .all (τ := Ty.pred1 (Ty.pred1 a)) fun f =>
    imp (cls (pf φ) fun φ' => .app1 f φ') (cls (pf θ) fun φ' => .app1 f φ')
  have h1 : ∀ g : V (Ty.pred1 (Ty.pred1 a)),
      QThm S (imp (fiff (fun φ' => cls (pf φ') F) (fun φ' => cls (pf φ') fun χ => .app1 g χ))
        (imp P (imp (cls (pf φ) F) (cls (pf θ) F)))) := fun g =>
    have e1 := q10_1 (fun φ' => iff (cls (pf φ') F) (cls (pf φ') fun χ => .app1 g χ)) φ
    have e2 := q10_1 (fun φ' => iff (cls (pf φ') F) (cls (pf φ') fun χ => .app1 g χ)) θ
    have e3 := qsyl (qimpImpIffCongr e1 e2) (QL.t3_27 _ _)
    have e4 := q10_1 (fun f : V (Ty.pred1 (Ty.pred1 a)) =>
      imp (cls (pf φ) fun φ' => .app1 f φ') (cls (pf θ) fun φ' => .app1 f φ')) g     -- ✱10·1
    qsyl e3 (QThm.mp e4 (QL.t2_06 _ _ _))
  have h2 : QThm S (imp P (imp (cls (pf φ) F) (cls (pf θ) F))) :=
    QThm.mp (q20_112 F) (QThm.mp (q10_11 h1) (qiffMp (q10_23 _ _)))              -- [✱20·112]
  have h3 : QThm S (cls (pf φ) F) :=
    QThm.mp (q10_13 (q10_11 fun x => QL.t4_2 (.app1 φ x)) (q10_11 fun x => QL.t4_2 (.app1 φ x)))
      (q10_24 (fun χ => QF.and (fiff (pf χ) (pf φ)) (F χ)) φ)
  have h4 : QThm S (imp (cls (pf θ) F) (fiff (pf φ) (pf θ))) :=
    QThm.mp (q10_11 fun χ => qsyl (QL.t3_22 _ _) (q10_301 (pf φ) (pf χ) (pf θ))) (qiffMp (q10_23 _ _))
  qsyl h2 (qsyl (QThm.mp h3 (QL.t2_27 _ _)) h4)                                  -- [✱4·2]

/-- ✱20·19 `⊢ :. ẑ(ψz) = ẑ(χz) . ≡ : (f) : f!ẑ(ψz) . ⊃ . f!ẑ(χz)`. f ranges over the predicative functions
    of predicative functions, and f!ẑ(ψz) is ✱20·01 with context f!φ!ẑ. In (1), ✱20·18's "≡" is used
    left to right (✱3·26). In (2), ✱20·15 (left to right) and ✱20·18 are used for each factor of Hp,
    picked by ✱3·26 and ✱3·27, joined by ✱4·84, ✱4·85, and the converse half taken (✱3·27). (2) is
    kept in the exported form `Hp ⊃ : f!ẑ(ψz) ⊃ f!ẑ(χz) . ⊃ . f!ẑ(φ!z) ⊃ f!ẑ(θ!z)`, so in (3) PM's
    ✱10·33 (which needs a real variable) is not used: ✱10·11·21 and ✱10·27 carry it under (f).
    "[✱20·112 . ✱10·1] [✱4·2]" is `qclsIndisc`; "[✱10·301·32 . Hp]" turns the first factor by ✱10·32
    and uses ✱10·301 twice, with Exp (✱3·3) and Comm (✱2·04). (4) and (5): the two existentials of
    ✱12·1 (turned by ✱10·32, `qred1cls`) are used one after the other, with Exp and Comm, ✱10·11 and
    ✱10·23, not combined by ✱10·35. -/
theorem q20_19 [Reducibility S] (ψ χ : V a → QF V) :
    QThm S (iff (clsEq ψ χ) (.all (τ := Ty.pred1 (Ty.pred1 a)) fun f =>
      imp (cls ψ fun φ => .app1 f φ) (cls χ fun φ => .app1 f φ))) :=
  let P : QF V := .all (τ := Ty.pred1 (Ty.pred1 a)) fun f =>
    imp (cls ψ fun φ => .app1 f φ) (cls χ fun φ => .app1 f φ)
  have h1 : QThm S (imp (clsEq ψ χ) P) :=
    q10_11_21 fun f => qsyl (q20_18 ψ χ fun φ => .app1 f φ) (QL.t3_26 _ _)       -- ✱20·18 . ✱10·11·21 (1)
  have h2 : ∀ (φ θ : V (Ty.pred1 a)) (f : V (Ty.pred1 (Ty.pred1 a))),
      QThm S (imp (QF.and (fiff (pf φ) ψ) (fiff (pf θ) χ))
        (imp (imp (cls ψ fun φ' => .app1 f φ') (cls χ fun φ' => .app1 f φ'))
          (imp (cls (pf φ) fun φ' => .app1 f φ') (cls (pf θ) fun φ' => .app1 f φ')))) := fun φ θ f =>
    have e1 := qsyl (QL.t3_26 _ _) (qsyl (qiffMp (q20_15 (pf φ) ψ)) (q20_18 (pf φ) ψ fun φ' => .app1 f φ'))
    have e2 := qsyl (QL.t3_27 _ _) (qsyl (qiffMp (q20_15 (pf θ) χ)) (q20_18 (pf θ) χ fun φ' => .app1 f φ'))
    qsyl (qimpImpIffCongr e1 e2) (QL.t3_27 _ _)                                   -- ✱20·18·15 (2)
  have h3 : ∀ φ θ : V (Ty.pred1 a),
      QThm S (imp (QF.and (fiff (pf φ) ψ) (fiff (pf θ) χ)) (imp P (clsEq ψ χ))) := fun φ θ =>
    have k1 := qsyl (q10_11_21 (h2 φ θ)) (q10_27 _ _)                             -- (2).✱10·11·27
    have k2 := qimpImpTransR k1 (qclsIndisc φ θ)                                  -- [✱20·112 . ✱10·1] [✱4·2]
    have c := qsyl (qsyl (QL.t3_26 _ _) (qiffMp (q10_32 (pf φ) ψ)))
      (QThm.mp (q10_301 ψ (pf φ) (pf θ)) (QL.t3_3 _ _ _))
    have d := qsyl (QL.t3_27 _ _)
      (QThm.mp (QThm.mp (q10_301 ψ (pf θ) χ) (QL.t3_3 _ _ _)) (QL.t2_04 _ _ _))
    qimpImpTransR (qimpImpTrans k2 (qimpImpTrans c d)) (qiffMp (q20_15 ψ χ))      -- [✱10·301·32 . Hp] [✱20·15] (3)
  have h4 : ∀ φ : V (Ty.pred1 a), QThm S (imp (fiff (pf φ) ψ) (imp P (clsEq ψ χ))) := fun φ =>
    have k := q10_11 fun θ => QThm.mp (QThm.mp (h3 φ θ) (QL.t3_3 _ _ _)) (QL.t2_04 _ _ _)
    QThm.mp (qred1cls χ) (QThm.mp k (qiffMp (q10_23 _ _)))                        -- (3).✱10·11·23 . ✱12·1
  have h5 : QThm S (imp P (clsEq ψ χ)) :=
    QThm.mp (qred1cls ψ) (QThm.mp (q10_11 h4) (qiffMp (q10_23 _ _)))              -- (4).✱12·1 (5)
  qiffI h1 h5                                                                     -- (1).(5)

/-- ✱20·191 `⊢ :. ẑ(ψz) = ẑ(χz) . ≡ : (f) : f!ẑ(ψz) . ≡ . f!ẑ(χz)` [✱20·18·19 . ✱10·22]. ✱10·22 is used with
    Simp (✱3·26, `qfiffMp`). -/
theorem q20_191 [Reducibility S] (ψ χ : V a → QF V) :
    QThm S (iff (clsEq ψ χ) (.all (τ := Ty.pred1 (Ty.pred1 a)) fun f =>
      iff (cls ψ fun φ => .app1 f φ) (cls χ fun φ => .app1 f φ))) :=
  qiffI (q10_11_21 fun f => q20_18 ψ χ fun φ => .app1 f φ)                       -- ✱20·18
    (qsyl (qfiffMp (τ := Ty.pred1 (Ty.pred1 a)) (fun f => cls ψ fun φ => .app1 f φ)
      (fun f => cls χ fun φ => .app1 f φ)) (qiffMpr (q20_19 ψ χ)))                -- ✱10·22 . ✱20·19

/-! ## ✱20·2–✱20·25: identity of classes is reflexive, symmetrical and transitive -/

/-- ✱20·2 `⊢ . ẑ(φz) = ẑ(φz)` -/
theorem q20_2 [Reducibility S] (φ : V a → QF V) : QThm S (clsEq φ φ) :=
  QThm.mp (q10_11 fun x => QL.t4_2 (φ x)) (qiffMp (q20_15 φ φ))                   -- ✱20·15 (1) . (1).✱4·2.✱10·11

/-- ✱20·21 `⊢ : ẑ(φz) = ẑ(ψz) . ≡ . ẑ(ψz) = ẑ(φz)` [✱20·15 . ✱10·32] -/
theorem q20_21 [Reducibility S] (φ ψ : V a → QF V) : QThm S (iff (clsEq φ ψ) (clsEq ψ φ)) :=
  qiffTrans (qiffSymm (q20_15 φ ψ)) (qiffTrans (q10_32 φ ψ) (q20_15 ψ φ))

/-- ✱20·22 `⊢ : ẑ(φz) = ẑ(ψz) . ẑ(ψz) = ẑ(χz) . ⊃ . ẑ(φz) = ẑ(χz)` [✱20·15 . ✱10·301]. ✱20·15 is used on
    both factors, joined by ✱3·47. -/
theorem q20_22 [Reducibility S] (φ ψ χ : V a → QF V) :
    QThm S (imp (QF.and (clsEq φ ψ) (clsEq ψ χ)) (clsEq φ χ)) :=
  qsyl (QThm.mp (qandI (qiffMpr (q20_15 φ ψ)) (qiffMpr (q20_15 ψ χ))) (QL.t3_47 _ _ _ _))  -- ✱20·15
    (qsyl (q10_301 φ ψ χ) (qiffMp (q20_15 φ χ)))                                  -- ✱10·301 . ✱20·15

/-- ✱20·23 `⊢ : ẑ(φz) = ẑ(ψz) . ẑ(φz) = ẑ(χz) . ⊃ . ẑ(ψz) = ẑ(χz)` [✱20·21·22]. ✱20·21 acts on the first
    factor (Fact, ✱3·45). -/
theorem q20_23 [Reducibility S] (φ ψ χ : V a → QF V) :
    QThm S (imp (QF.and (clsEq φ ψ) (clsEq φ χ)) (clsEq ψ χ)) :=
  qsyl (QThm.mp (qiffMp (q20_21 φ ψ)) (QL.t3_45 _ _ _)) (q20_22 ψ φ χ)          -- ✱20·21·22

/-- ✱20·24 `⊢ : ẑ(ψz) = ẑ(φz) . ẑ(χz) = ẑ(φz) . ⊃ . ẑ(ψz) = ẑ(χz)` [✱20·21·22]. ✱20·21 acts on the second
    factor (✱3·47 with Id, `qandR`). -/
theorem q20_24 [Reducibility S] (φ ψ χ : V a → QF V) :
    QThm S (imp (QF.and (clsEq ψ φ) (clsEq χ φ)) (clsEq ψ χ)) :=
  qsyl (qandR (qiffMp (q20_21 χ φ))) (q20_22 ψ φ χ)                              -- ✱20·21·22

/-- The class analogue of ✱10·1 at a class ẑ(ψz) whose defining function need not be predicative (p. 206,
    ✱20·17's argument), for an expression G in which the class may occur several times: ✱12·1 gives φ
    with ψx ≡ₓ φ!x (turned by ✱10·32, `qred1cls`); ✱10·1 gives G(φ!ẑ), and `h` (each occurrence carried
    by ✱20·11) gives G(ψ), chained by ✱2·06; (∃φ) is removed by ✱10·11, ✱10·23. -/
theorem qclsAllAt [Reducibility S] (G : (V a → QF V) → QF V) (ψ : V a → QF V)
    (h : ∀ φ : V (Ty.pred1 a), QThm S (imp (fiff (pf φ) ψ) (imp (G (pf φ)) (G ψ)))) :
    QThm S (imp (clsAll G) (G ψ)) :=
  have h2 : ∀ φ : V (Ty.pred1 a), QThm S (imp (fiff (pf φ) ψ) (imp (clsAll G) (G ψ))) := fun φ =>
    qsyl (h φ) (QThm.mp (q10_1 (fun φ => G (pf φ)) φ) (QL.t2_06 _ _ _))
  QThm.mp (qred1cls ψ) (QThm.mp (q10_11 h2) (qiffMp (q10_23 _ _)))

/-- The class analogue of ✱10·24 at a class ẑ(ψz) whose defining function need not be predicative, as
    `qclsAllAt` (✱12·1, ✱10·32, ✱10·24 with ✱2·05, ✱10·11, ✱10·23). -/
theorem qclsExAt [Reducibility S] (G : (V a → QF V) → QF V) (ψ : V a → QF V)
    (h : ∀ φ : V (Ty.pred1 a), QThm S (imp (fiff (pf φ) ψ) (imp (G ψ) (G (pf φ))))) :
    QThm S (imp (G ψ) (clsEx G)) :=
  have h2 : ∀ φ : V (Ty.pred1 a), QThm S (imp (fiff (pf φ) ψ) (imp (G ψ) (clsEx G))) := fun φ =>
    qsyl (h φ) (QThm.mp (q10_24 (fun φ => G (pf φ)) φ) (QL.t2_05 _ _ _))
  QThm.mp (qred1cls ψ) (QThm.mp (q10_11 h2) (qiffMp (q10_23 _ _)))

/-- `ẑ(ψz) = ẑ(χz) . ⊃ : ω = ẑ(ψz) . ≡ . ω = ẑ(χz)`: lines (2)–(4) of ✱20·25 for one class ω (✱20·22, Exp,
    Comm; ✱20·24 with the factors commuted (✱3·22), Exp; joined by Comp, ✱3·43). -/
theorem qclsEqR [Reducibility S] (ψ χ ω : V a → QF V) :
    QThm S (imp (clsEq ψ χ) (iff (clsEq ω ψ) (clsEq ω χ))) :=
  have h2 := QThm.mp (QThm.mp (q20_22 ω ψ χ) (QL.t3_3 _ _ _)) (QL.t2_04 _ _ _)   -- ✱20·22 . Exp . Comm (2)
  have h3 := QThm.mp (qsyl (QL.t3_22 _ _) (q20_24 χ ω ψ)) (QL.t3_3 _ _ _)       -- ✱20·24 . Exp (3)
  qcomp h2 h3                                                                     -- (2).(3)

/-- ✱20·25 `⊢ :. α = ẑ(φz) . ≡_α . α = ẑ(ψz) : ≡ . ẑ(φz) = ẑ(ψz)`. α is apparent (✱20·07). In (1), PM's
    ✱10·1 instantiates α at ẑ(φz): the class analogue `qclsAllAt`, each occurrence carried by ✱20·11
    and the two joined by ✱4·86 (the ⊃ half by ✱3·26); "[✱20·2]" detaches ẑ(φz) = ẑ(φz) by ✱3·26 and
    ✱2·27. (2)–(4) are `qclsEqR` (✱20·24 with its factors commuted, ✱3·22; Comp, ✱3·43). -/
theorem q20_25 [Reducibility S] (φ ψ : V a → QF V) :
    QThm S (iff (clsAll fun α => iff (clsEq α φ) (clsEq α ψ)) (clsEq φ ψ)) :=
  let G : (V a → QF V) → QF V := fun α => iff (clsEq α φ) (clsEq α ψ)
  have h1 : QThm S (imp (clsAll G) (G φ)) :=
    qclsAllAt G φ fun θ =>
      qsyl (qimpIffIffCongr (q20_11 (pf θ) φ fun θ' => cls φ fun θ'' => ident θ' θ'')
        (q20_11 (pf θ) φ fun θ' => cls ψ fun θ'' => ident θ' θ'')) (QL.t3_26 _ _)  -- ✱10·1
  have h1' := qsyl h1 (qsyl (QL.t3_26 _ _) (QThm.mp (q20_2 φ) (QL.t2_27 _ _)))     -- [✱20·2] (1)
  have h4 := q10_11_21 fun θ => qclsEqR φ ψ (pf θ)                               -- (2).(3) [✱10·11·21] (4)
  qiffI h1' h4                                                                    -- (1).(4)

/-! ## ✱20·3–✱20·43 -/

/-- ✱20·3 `⊢ : x ∈ ẑ(ψz) . ≡ . ψx`. PM's lines have ψy ≡_y φ!y; ✱20·01 gives φ!y ≡_y ψy, so ✱12·1 is
    turned by ✱10·32 (under (∃φ), ✱10·11·281). ✱10·35 is used with p as the second factor
    (`qex_and_perm`, ✱4·3), and "[✱12·1]" drops the asserted factor by ✱3·27 and ✱3·2. -/
theorem q20_3 [Reducibility S] (ψ : V a → QF V) (x : V a) : QThm S (iff (cls ψ fun φ => mem x φ) (ψ x)) :=
  let P : V (Ty.pred1 a) → QF V := fun φ => fiff (fun y => .app1 φ y) ψ
  have h1 := q10_11_281 fun φ => q10_43 (fun y => .app1 φ y) ψ x                 -- ✱20·1 . (✱20·02) . [✱10·43]
  have h2 := qex_and_perm P (ψ x)                                                -- [✱10·35]
  have h3 : QThm S (ex P) := QThm.mp (q12_1 ψ) (qiffMp (q10_11_281 fun φ => q10_32 ψ fun y => .app1 φ y))
  qiffTrans h1 (qiffTrans h2 (qand_true_left h3))                                -- [✱12·1]

/-- ✱20·31 `⊢ :. ẑ(ψz) = ẑ(χz) . ≡ : x ∈ ẑ(ψz) . ≡ₓ . x ∈ ẑ(χz)` [✱20·15·3]. ✱20·3 replaces both members
    under (x) (✱4·86, and for the second member with ✱4·21). -/
theorem q20_31 [Reducibility S] (ψ χ : V a → QF V) :
    QThm S (iff (clsEq ψ χ) (fiff (fun x => clsMem x ψ) (fun x => clsMem x χ))) :=
  qiffTrans (qiffSymm (q20_15 ψ χ))                                               -- ✱20·15
    (q10_11_271 fun x => qiffIffCongr (qiffSymm (q20_3 ψ x)) (qiffSymm (q20_3 χ x)))  -- ✱20·3

/-- ✱20·32 `⊢ . x̂{x ∈ ẑ(φz)} = ẑ(φz)` [✱20·3·15] -/
theorem q20_32 [Reducibility S] (φ : V a → QF V) : QThm S (clsEq (fun x => clsMem x φ) φ) :=
  QThm.mp (q10_11 fun x => q20_3 φ x) (qiffMp (q20_15 (fun x => clsMem x φ) φ))  -- ✱20·3 . ✱20·15

/-- ✱20·33 `⊢ :. α = ẑ(φz) . ≡ : x ∈ α . ≡ₓ . φx`, α real (an expression ẑ(ψz)). In (1).✱20·3, the second
    member is replaced under (x) by ✱4·86 (with ✱4·21, `qiffCongrRImp`). -/
theorem q20_33 [Reducibility S] (ψ φ : V a → QF V) :
    QThm S (iff (clsEq ψ φ) (fiff (fun x => clsMem x ψ) φ)) :=
  qiffTrans (q20_31 ψ φ)                                                          -- ✱20·31 (1)
    (q10_11_271 fun x => QThm.mp (q20_3 φ x) (qiffCongrRImp (clsMem x ψ) _ _))   -- (1).✱20·3

/-- ✱20·34 `⊢ :. x = y . ≡ : x ∈ α . ⊃_α . y ∈ α`, α apparent (✱20·07) and each x ∈ α with the smallest
    scope. ✱20·3 replaces both sides of the implication under (φ) (✱4·84, ✱4·85). -/
theorem q20_34 [Reducibility S] (x y : V a) :
    QThm S (iff (ident x y) (clsAll fun α => imp (clsMem x α) (clsMem y α))) :=
  qiffTrans (q13_1 x y)                                                           -- [✱13·1]
    (qiffSymm (q10_11_271 fun φ => qimpIffCongr (q20_3 (pf φ) x) (q20_3 (pf φ) y)))  -- ✱4·2 . (✱20·07) [✱20·3]

/-- ✱20·35 `⊢ :. x = y . ≡ : x ∈ α . ≡_α . y ∈ α` [✱20·3 . ✱13·11]. ✱20·3 replaces both members under (φ)
    (✱4·86, and for the second member with ✱4·21). -/
theorem q20_35 [Reducibility S] (x y : V a) :
    QThm S (iff (ident x y) (clsAll fun α => iff (clsMem x α) (clsMem y α))) :=
  qiffTrans (q13_11 x y)                                                          -- ✱13·11
    (qiffSymm (q10_11_271 fun φ => qiffIffCongr (q20_3 (pf φ) x) (q20_3 (pf φ) y)))  -- ✱20·3

/-- ✱20·42 `⊢ . ẑ(z ∈ α) = α`, α real (an expression ẑ(ψz)): "this proposition is ✱20·32 repeated". -/
theorem q20_42 [Reducibility S] (ψ : V a → QF V) : QThm S (clsEq (fun z => clsMem z ψ) ψ) :=
  QThm.mp (q10_11 fun x => q20_3 ψ x) (qiffMp (q20_15 (fun z => clsMem z ψ) ψ))  -- ✱20·3 . ✱10·11 [✱20·15]

/-- ✱20·43 `⊢ :. α = β . ≡ : x ∈ α . ≡ₓ . x ∈ β` [✱20·31], α and β real (expressions ẑ(ψz), ẑ(χz)):
    "the same proposition as ✱20·31, merely employing Greek letters". -/
theorem q20_43 [Reducibility S] (ψ χ : V a → QF V) :
    QThm S (iff (clsEq ψ χ) (fiff (fun x => clsMem x ψ) (fun x => clsMem x χ))) :=
  q20_31 ψ χ                                                                      -- [✱20·31]

/-! ## ✱20·5–✱20·59: classes and descriptions

  "The descriptions are to have a larger scope than the classes" (p. 204). -/

/-- ✱20·5 `⊢ : (ιx)(φx) ∈ ẑ(ψz) . ≡ . ψ{(ιx)(φx)}`. ✱20·3 acts on the second factor (✱4·36 with ✱4·3,
    `qandCongrR`), under (∃c). -/
theorem q20_5 [Reducibility S] (φ ψ : V a → QF V) :
    QThm S (iff (desc φ fun c => clsMem c ψ) (desc φ ψ)) :=
  q10_11_281 fun c => qandCongrR _ (q20_3 ψ c)                                    -- ✱14·1 . [✱20·3] [✱14·1]

/-- ✱20·51 `⊢ :. (ιx)(φx) = b . ≡ : (ιx)(φx) ∈ α . ≡_α . b ∈ α`. ✱20·5 and ✱20·3 at α = ẑ(ψ!z) are joined by
    ✱4·86 (and for the second member with ✱4·21) under (ψ). -/
theorem q20_51 [Reducibility S] (φ : V a → QF V) (b : V a) :
    QThm S (iff (desc φ fun z => ident z b)
      (clsAll fun α => iff (desc φ fun c => clsMem c α) (clsMem b α))) :=
  qiffTrans (q14_17 φ b)                                                          -- [✱14·17]
    (qiffSymm (q10_11_271 fun ψ => qiffIffCongr (q20_5 φ (pf ψ)) (q20_3 (pf ψ) b)))  -- ✱20·5·3 [✱10·11]

/-- ✱20·52 `⊢ :. E!(ιx)(φx) . ≡ : (∃b) : (ιx)(φx) ∈ α . ≡_α . b ∈ α` -/
theorem q20_52 [Reducibility S] (φ : V a → QF V) :
    QThm S (iff (exists1 φ)
      (ex fun b => clsAll fun α => iff (desc φ fun c => clsMem c α) (clsMem b α))) :=
  qiffTrans (q14_204 φ) (q10_11_281 fun b => q20_51 φ b)                          -- ✱20·51 . ✱10·11·281 (1) . (1).✱14·204

/-- ✱20·53 `⊢ :. β = α . ⊃_β . φβ : ≡ . φα`, β apparent, α real (an expression ẑ(ψz)), and φβ a generic
    expression (`cls β f`, p. 199): "the analogue of ✱13·191". In (1), PM's ✱10·1 instantiates β at α:
    the class analogue `qclsAllAt`, both occurrences carried by ✱20·11 and joined by ✱4·84, ✱4·85 (the
    ⊃ half by ✱3·26); "[✱20·2]" detaches α = α by ✱2·27. In (2), ✱20·18's "≡" is used from left to
    right (✱3·26). -/
theorem q20_53 [Reducibility S] (ψ : V a → QF V) (f : V (Ty.pred1 a) → QF V) :
    QThm S (iff (clsAll fun β => imp (clsEq β ψ) (cls β f)) (cls ψ f)) :=
  let G : (V a → QF V) → QF V := fun β => imp (clsEq β ψ) (cls β f)
  have h1 : QThm S (imp (clsAll G) (G ψ)) :=
    qclsAllAt G ψ fun θ =>
      qsyl (qimpImpIffCongr (q20_11 (pf θ) ψ fun θ' => cls ψ fun θ'' => ident θ' θ'')
        (q20_11 (pf θ) ψ f)) (QL.t3_26 _ _)                                       -- ✱10·1
  have h1' := qsyl h1 (QThm.mp (q20_2 ψ) (QL.t2_27 _ _))                          -- [✱20·2] (1)
  have h2 : ∀ θ : V (Ty.pred1 a), QThm S (imp (clsEq (pf θ) ψ) (imp (cls ψ f) (cls (pf θ) f))) := fun θ =>
    qsyl (qiffMp (q20_21 (pf θ) ψ)) (qsyl (q20_18 ψ (pf θ) f) (QL.t3_26 _ _))      -- ✱20·18·21
  qiffI h1' (q10_11_21 fun θ => QThm.mp (h2 θ) (QL.t2_04 _ _ _))                  -- [Comm] [✱10·11·21] (2) . (1).(2)

/-- ✱20·54's argument for an expression G in which the class may occur several times, given the analogue
    of ✱20·18 for G (`hG`): `(∃β) . β = ẑ(ψz) . Gβ . ≡ . G{ẑ(ψz)}`. (1): `hG` with ✱3·26 and Imp (✱3·31),
    ✱10·11, ✱10·23. (2): ✱20·2, ✱3·2 and the class analogue of ✱10·24 (`qclsExAt`), the identity got
    from ψ's formal equivalence by ✱20·13 and G carried by `hG` (✱3·27), with ✱2·02, ✱2·06 and Comp
    (✱3·43). -/
theorem qcls54 [Reducibility S] (G : (V a → QF V) → QF V) (ψ : V a → QF V)
    (hG : ∀ φ : V (Ty.pred1 a), QThm S (imp (clsEq (pf φ) ψ) (iff (G (pf φ)) (G ψ)))) :
    QThm S (iff (clsEx fun β => QF.and (clsEq β ψ) (G β)) (G ψ)) :=
  have h1 : QThm S (imp (clsEx fun β => QF.and (clsEq β ψ) (G β)) (G ψ)) :=
    QThm.mp (q10_11 fun φ => QThm.mp (qsyl (hG φ) (QL.t3_26 _ _)) (QL.t3_31 _ _ _))
      (qiffMp (q10_23 _ _))                                                       -- ✱20·18 . ✱10·11 [✱10·23] (1)
  have h2 : QThm S (imp (G ψ) (QF.and (clsEq ψ ψ) (G ψ))) := QThm.mp (q20_2 ψ) (QL.t3_2 _ _)  -- ✱20·2 . ✱3·2
  have h3 : QThm S (imp (QF.and (clsEq ψ ψ) (G ψ)) (clsEx fun β => QF.and (clsEq β ψ) (G β))) :=
    qclsExAt (fun β => QF.and (clsEq β ψ) (G β)) ψ fun φ =>
      have e := q20_13 (pf φ) ψ
      have k1 : QThm S (imp (fiff (pf φ) ψ) (imp (QF.and (clsEq ψ ψ) (G ψ)) (clsEq (pf φ) ψ))) :=
        qsyl e (QL.t2_02 _ _)
      have k2 : QThm S (imp (fiff (pf φ) ψ) (imp (QF.and (clsEq ψ ψ) (G ψ)) (G (pf φ)))) :=
        qsyl (qsyl e (qsyl (hG φ) (QL.t3_27 _ _))) (QThm.mp (QL.t3_27 _ _) (QL.t2_06 _ _ _))
      qsyl (qcomp k1 k2) (QL.t3_43 _ _ _)                                         -- [✱10·24]
  qiffI h1 (qsyl h2 h3)                                                           -- (2) . (1).(2)

/-- ✱20·54 `⊢ : (∃β) . β = α . φβ . ≡ . φα`, α real (an expression ẑ(ψz)), φβ a generic expression
    (`cls β f`): "the analogue of ✱13·195". The lines are `qcls54`'s with ✱20·18 for `hG`; in (2), PM's
    ✱10·24 is used at α, whose defining function need not be predicative (the class analogue
    `qclsExAt`). -/
theorem q20_54 [Reducibility S] (ψ : V a → QF V) (f : V (Ty.pred1 a) → QF V) :
    QThm S (iff (clsEx fun β => QF.and (clsEq β ψ) (cls β f)) (cls ψ f)) :=
  qcls54 (fun β => cls β f) ψ fun θ => q20_18 (pf θ) ψ f                           -- ✱20·18

/-- `[(ια)(Φα)] . ẑ(φz) = (ια)(Φα) . ≡ : Φα . ≡_α . α = ẑ(φz)`, the description having the larger scope
    (p. 204): ✱20·072 and ✱20·54's argument (`qcls54`) for Φα ≡_α α = β, whose analogue of ✱20·18 is
    `qclsEqR` under (α) (✱4·86 with ✱4·21, ✱10·11·21, ✱10·271); the factors are commuted (✱4·3) and
    ẑ(φz) = β turned by ✱20·21 (with ✱4·36) under (∃β) by ✱10·11·281. The analogue of `qidentDesc`. -/
theorem qdescClsEq [Reducibility S] (Φ : (V a → QF V) → QF V) (φ : V a → QF V) :
    QThm S (iff (descCls Φ fun γ => clsEq φ γ) (clsAll fun α => iff (Φ α) (clsEq α φ))) :=
  let G : (V a → QF V) → QF V := fun β => clsAll fun α => iff (Φ α) (clsEq α β)
  have hG : ∀ θ : V (Ty.pred1 a), QThm S (imp (clsEq (pf θ) φ) (iff (G (pf θ)) (G φ))) := fun θ =>
    qsyl (q10_11_21 fun θ' => qsyl (qclsEqR (pf θ) φ (pf θ')) (qiffCongrRImp (Φ (pf θ')) _ _))
      (q10_271 _ _)
  qiffTrans (q10_11_281 fun θ => qiffTrans (QL.t4_3 (G (pf θ)) (clsEq φ (pf θ)))
      (qandCongrL (G (pf θ)) (q20_21 φ (pf θ))))
    (qcls54 G φ hG)

/-- ✱20·55 `⊢ . ẑ(φz) = (ια)(x ∈ α . ≡ₓ . φx)`, the description having the larger scope (p. 204). ✱20·33
    is generalized over α by ✱10·11 (✱20·62) and read from right to left; "[✱20·54] [✱14·1]" is
    `qdescClsEq`, where PM's line `(∃β) : … : ẑ(φz) = β` comes from ✱20·54's `β = ẑ(φz) . …` by ✱20·21
    and ✱4·3. -/
theorem q20_55 [Reducibility S] (φ : V a → QF V) :
    QThm S (descCls (fun α => fiff (fun x => clsMem x α) φ) fun γ => clsEq φ γ) :=
  QThm.mp (q10_11 fun θ => qiffSymm (q20_33 (pf θ) φ))                            -- ✱20·33
    (qiffMpr (qdescClsEq _ φ))                                                    -- [✱20·54] [✱14·1]

/-- ✱14·21 for descriptions of classes, `[(ια)(Φα)] . G(ια)(Φα) . ⊃ . E!(ια)(Φα)`, proved as ✱14·21 is
    (✱10·5, ✱3·26). -/
theorem qdescClsE (Φ G : (V a → QF V) → QF V) : QThm S (imp (descCls Φ G) (exists1Cls Φ)) :=
  qsyl (q10_5 (fun θ => clsAll fun α => iff (Φ α) (clsEq α (pf θ))) fun θ => G (pf θ)) (QL.t3_26 _ _)

/-- ✱20·56 `⊢ . E!(ια)(x ∈ α . ≡ₓ . φx)` [✱20·55 . ✱14·21]. ✱14·21 for classes is `qdescClsE`. -/
theorem q20_56 [Reducibility S] (φ : V a → QF V) :
    QThm S (exists1Cls fun α => fiff (fun x => clsMem x α) φ) :=
  QThm.mp (q20_55 φ) (qdescClsE _ _)                                              -- ✱20·55 . ✱14·21

/-- ✱20·57 `⊢ :. ẑ(φz) = (ια)(fα) . ⊃ : g{ẑ(φz)} . ≡ . g{(ια)(fα)}`, fα any expression containing α (`F`),
    g a generic context (p. 199), the descriptions with the larger scope (p. 204). (1) is `qdescClsEq`
    (✱14·1, ✱20·54, with ✱20·21, ✱4·3). (1).(2): fα is replaced by α = ẑ(φz) under (α) by ✱4·86
    (✱10·11·27, ✱10·271), Fact as ✱4·36, under (∃β) by ✱10·11·21 and ✱10·281. "[✱13·183]" is its class
    analogue ✱20·25, with β = ẑ(φz) turned by ✱20·21 for ✱20·54 (with ✱4·36). The chain is read from
    right to left at the end (`qimpIffSymm`). -/
theorem q20_57 [Reducibility S] (φ : V a → QF V) (F : (V a → QF V) → QF V) (g : V (Ty.pred1 a) → QF V) :
    QThm S (imp (descCls F fun γ => clsEq φ γ) (iff (cls φ g) (descCls F fun γ => cls γ g))) :=
  let A : QF V := clsAll fun α => iff (F α) (clsEq α φ)
  have h1 : QThm S (imp (descCls F fun γ => clsEq φ γ) A) := qiffMp (qdescClsEq F φ)  -- ✱14·1 [✱20·54] (1)
  have h3 : QThm S (imp A (iff (descCls F fun γ => cls γ g)
      (clsEx fun β => QF.and (clsAll fun α => iff (clsEq α φ) (clsEq α β)) (cls β g)))) :=
    qsyl (q10_11_21 fun θ =>
        qsyl (q10_11_27 fun θ' => QL.t4_86 (F (pf θ')) (clsEq (pf θ') φ) (clsEq (pf θ') (pf θ)))
          (qsyl (q10_271 _ _) (QL.t4_36 _ _ (cls (pf θ) g))))
      (q10_281 _ _)                                                               -- ✱14·1 (2) . (1).(2)
  have e4 : QThm S (iff (clsEx fun β => QF.and (clsAll fun α => iff (clsEq α φ) (clsEq α β)) (cls β g))
      (cls φ g)) :=
    qiffTrans (q10_11_281 fun θ => qandCongrL (cls (pf θ) g)
        (qiffTrans (q20_25 φ (pf θ)) (q20_21 φ (pf θ))))                          -- [✱13·183]
      (q20_54 φ g)                                                                -- [✱20·54]
  qsyl h1 (qimpIffSymm (qimpIffTransR h3 e4))

/-- ✱20·58 `⊢ . ẑ(φz) = (ια){α = ẑ(φz)}`, the description having the larger scope. "✱4·2 . ✱10·11" gives
    the condition; "[✱20·54] [✱14·1]" is `qdescClsEq` (as in ✱20·55). -/
theorem q20_58 [Reducibility S] (φ : V a → QF V) :
    QThm S (descCls (fun α => clsEq α φ) fun γ => clsEq φ γ) :=
  QThm.mp (q10_11 fun θ => QL.t4_2 (clsEq (pf θ) φ)) (qiffMpr (qdescClsEq _ φ))   -- ✱4·2 . ✱10·11 [✱20·54] [✱14·1]

/-- ✱20·59 `⊢ : ẑ(φz) = (ια)(fα) . ≡ . (ια)(fα) = ẑ(φz)`. On both sides the description has the larger
    scope (p. 204). PM's Dem. eliminates ẑ(φz) first (✱20·1) and then cites ✱14·13 for the description
    and the predicative function ψ!ẑ put for the class; with the description eliminated first, the step
    is ✱14·13's own argument: ✱20·21 (for ✱13·16) on the second factor (✱4·36 with ✱4·3) under (∃β)
    by ✱10·11·281. -/
theorem q20_59 [Reducibility S] (φ : V a → QF V) (F : (V a → QF V) → QF V) :
    QThm S (iff (descCls F fun γ => clsEq φ γ) (descCls F fun γ => clsEq γ φ)) :=
  q10_11_281 fun θ => qandCongrR _ (q20_21 φ (pf θ))                              -- [✱14·13]

/-! ## ✱20·6–✱20·71: classes have the formal properties of individuals

  ✱20·631 and ✱20·632 (significance) are built into the syntax, as ✱10·121 and ✱10·122 are. -/

/-- ✱20·6 `⊢ : (∃α) . fα . ≡ . ∼{(α) . ∼fα}` [✱4·2 . (✱20·071) . (✱10·01) . (✱20·07)]: the analogue of ✱10·01. -/
theorem q20_6 (F : (V a → QF V) → QF V) : QThm S (iff (clsEx F) (.neg (clsAll fun α => .neg (F α)))) :=
  QL.t4_2 _

/-- ✱20·61 `⊢ : (α) . fα . ⊃ . fβ` [✱10·1 . (✱20·07)], β "merely an abbreviation for any symbol of the form
    ẑ(ψ!z)" (p. 208): the analogue of ✱10·1. -/
theorem q20_61 (F : (V a → QF V) → QF V) (ψ : V (Ty.pred1 a)) : QThm S (imp (clsAll F) (F (pf ψ))) :=
  q10_1 (fun φ => F (pf φ)) ψ

/-- ✱20·62 "When fβ is true, whatever possible argument of the form ẑ(φ!z) β may be, then (α) . fα is true"
    [✱10·11]: the analogue of ✱10·11. -/
theorem q20_62 {F : (V a → QF V) → QF V} (h : ∀ ψ : V (Ty.pred1 a), QThm S (F (pf ψ))) : QThm S (clsAll F) :=
  q10_11 h

/-- ✱20·63 `⊢ :. (α) . p ∨ fα . ⊃ : p . ∨ . (α) . fα` [✱4·2 . (✱20·07) . ✱10·12]: the analogue of ✱10·12. -/
theorem q20_63 (p : QF V) (F : (V a → QF V) → QF V) :
    QThm S (imp (clsAll fun α => .or p (F α)) (.or p (clsAll F))) :=
  q10_12 p fun φ => F (pf φ)

/-- ✱20·633 "'Whatever possible class α may be, f(α, β) is true whatever possible class β may be' implies the
    corresponding statement with α and β interchanged": the analogue of ✱11·07, which "follows at once
    from ✱11·07". -/
theorem q20_633 {b : Ty} {F : (V a → QF V) → (V b → QF V) → QF V}
    (h : QThm S (clsAll fun α => clsAll fun β => F α β)) : QThm S (clsAll fun β => clsAll fun α => F α β) :=
  q11_07 (φ := fun φ ψ => F (pf φ) (pf ψ)) h

/-- ✱20·64 `⊢ :. (α) . fα : (α) . gα : ⊃ . fβ . gβ` [✱4·2 . (✱20·07) . ✱10·14]: the analogue of ✱10·14. -/
theorem q20_64 (F G : (V a → QF V) → QF V) (ψ : V (Ty.pred1 a)) :
    QThm S (imp (QF.and (clsAll F) (clsAll G)) (QF.and (F (pf ψ)) (G (pf ψ)))) :=
  q10_14 (fun φ => F (pf φ)) (fun φ => G (pf φ)) ψ

/-- ✱20·7 `⊢ : (∃g) : fα . ≡_α . g!α` [✱20·112]: the analogue of ✱12·1. fα is the generic `cls α f` and g!α
    is `cls α (g!·)` (✱20·01); by ✱20·07 the statement is ✱20·112. -/
theorem q20_7 [Reducibility S] (f : V (Ty.pred1 a) → QF V) :
    QThm S (ex (τ := Ty.pred1 (Ty.pred1 a)) fun g =>
      clsAll fun α => iff (cls α f) (cls α fun χ => .app1 g χ)) :=
  q20_112 f                                                                       -- [✱20·112]

/-- ✱20·111 for two arguments, the class first: `f(φ!ẑ, x) . ≡_{φ,x} . g(φ!ẑ, x) : ⊃ : f{ẑ(φ!z), x} . ≡_{φ,x} .
    g{ẑ(φ!z), x}` (✱20·111's lines with ✱11·1 for ✱10·1 and ✱11·11·3 for ✱10·11·21). -/
theorem qcls111_2 {b : Ty} (f g : V (Ty.pred1 a) → V b → QF V) :
    QThm S (imp (fiff2 f g)
      (fiff2 (fun φ x => cls (pf φ) fun χ => f χ x) (fun φ x => cls (pf φ) fun χ => g χ x))) :=
  have h : ∀ (φ : V (Ty.pred1 a)) (x : V b), QThm S (imp (fiff2 f g)
      (iff (cls (pf φ) fun χ => f χ x) (cls (pf φ) fun χ => g χ x))) := fun φ x =>
    qsyl (q10_11_21 fun ψ => qsyl (q11_1 (fun ψ x => iff (f ψ x) (g ψ x)) ψ x)
        (qandCongrRImp (f ψ x) (g ψ x) (fiff (pf ψ) (pf φ))))
      (q10_281 _ _)
  qiffMpr (q11_3 _ _) |> QThm.mp (q11_11 h)

/-- ✱20·111 for two arguments, the class second: as `qcls111_2`, with the hypothesis over (x, φ). -/
theorem qcls111_2r {b : Ty} (f g : V b → V (Ty.pred1 a) → QF V) :
    QThm S (imp (fiff2 f g)
      (fiff2 (fun φ x => cls (pf φ) fun χ => f x χ) (fun φ x => cls (pf φ) fun χ => g x χ))) :=
  have h : ∀ (φ : V (Ty.pred1 a)) (x : V b), QThm S (imp (fiff2 f g)
      (iff (cls (pf φ) fun χ => f x χ) (cls (pf φ) fun χ => g x χ))) := fun φ x =>
    qsyl (q10_11_21 fun ψ => qsyl (q11_1 (fun x ψ => iff (f x ψ) (g x ψ)) x ψ)
        (qandCongrRImp (f x ψ) (g x ψ) (fiff (pf ψ) (pf φ))))
      (q10_281 _ _)
  qiffMpr (q11_3 _ _) |> QThm.mp (q11_11 h)

/-- ✱20·701 `⊢ : (∃g) : f{ẑ(φ!z), x} . ≡_{φ,x} . g!{ẑ(φ!z), x}` ["The proof proceeds as in ✱20·112, using
    ✱12·11 instead of ✱12·1"]: ✱12·11 at the types of φ and x, and ✱20·111 for two arguments
    (`qcls111_2`: ✱11·1, ✱4·36 with ✱4·3, ✱10·11·21, ✱10·281, ✱11·11·3) under (∃g). -/
theorem q20_701 [Reducibility S] {b : Ty} (f : V (Ty.pred1 a) → V b → QF V) :
    QThm S (ex (τ := Ty.pred2 (Ty.pred1 a) b) fun g =>
      fiff2 (fun φ x => cls (pf φ) fun χ => f χ x) (fun φ x => cls (pf φ) fun χ => .app2 g χ x)) :=
  QThm.mp (q12_11 f) (q10_11_28 fun g => qcls111_2 f fun χ x => .app2 g χ x)      -- ✱12·11 . ✱20·111

/-- ✱20·702 `⊢ : (∃g) : f{x, ẑ(φ!z)} . ≡_{φ,x} . g!{x, ẑ(φ!z)}` [Proof as in ✱20·701] (`qcls111_2r`). -/
theorem q20_702 [Reducibility S] {b : Ty} (f : V b → V (Ty.pred1 a) → QF V) :
    QThm S (ex (τ := Ty.pred2 b (Ty.pred1 a)) fun g =>
      fiff2 (fun φ x => cls (pf φ) fun χ => f x χ) (fun φ x => cls (pf φ) fun χ => .app2 g x χ)) :=
  QThm.mp (q12_11 f) (q10_11_28 fun g => qcls111_2r f fun x χ => .app2 g x χ)    -- ✱12·11 . ✱20·111

/-- ✱20·703 `⊢ : (∃g) : f{ẑ(φ!z), ẑ(ψ!z)} . ≡_{φ,ψ} . g!{ẑ(φ!z), ẑ(ψ!z)}`, the first class with the larger
    scope. (1): PM's ✱10·311 is used for both added factors at once: ✱11·1 at (χ, θ), and ✱4·36 with ✱4·3
    twice (`qandCongrRImp`). "[✱20·1 . ✱10·35]" brings (∃χ, θ) to ✱20·01's form by ✱10·35 under (∃χ)
    (✱10·11·281). In (3), (2) is an implication, carried under (∃g) by ✱10·11·28 (PM prints
    "✱10·11·281"). -/
theorem q20_703 [Reducibility S] {a' : Ty} (f : V (Ty.pred1 a) → V (Ty.pred1 a') → QF V) :
    QThm S (ex (τ := Ty.pred2 (Ty.pred1 a) (Ty.pred1 a')) fun g =>
      fiff2 (fun φ ψ => cls (pf φ) fun χ => cls (pf ψ) fun θ => f χ θ)
        (fun φ ψ => cls (pf φ) fun χ => cls (pf ψ) fun θ => .app2 g χ θ)) :=
  let E (h : V (Ty.pred1 a) → V (Ty.pred1 a') → QF V) (φ : V (Ty.pred1 a)) (ψ : V (Ty.pred1 a'))
      (χ : V (Ty.pred1 a)) (θ : V (Ty.pred1 a')) : QF V :=
    QF.and (fiff (pf χ) (pf φ)) (QF.and (fiff (pf θ) (pf ψ)) (h χ θ))
  have r : ∀ (h : V (Ty.pred1 a) → V (Ty.pred1 a') → QF V) φ ψ,
      QThm S (iff (ex2 (E h φ ψ)) (cls (pf φ) fun χ => cls (pf ψ) fun θ => h χ θ)) := fun h φ ψ =>
    q10_11_281 fun χ => q10_35 (fun θ => QF.and (fiff (pf θ) (pf ψ)) (h χ θ)) (fiff (pf χ) (pf φ))
  have k : ∀ g : V (Ty.pred2 (Ty.pred1 a) (Ty.pred1 a')),
      QThm S (imp (fiff2 f fun χ θ => .app2 g χ θ)
        (fiff2 (fun φ ψ => cls (pf φ) fun χ => cls (pf ψ) fun θ => f χ θ)
          (fun φ ψ => cls (pf φ) fun χ => cls (pf ψ) fun θ => .app2 g χ θ))) := fun g =>
    let g' : V (Ty.pred1 a) → V (Ty.pred1 a') → QF V := fun χ θ => .app2 g χ θ
    have l : ∀ φ ψ, QThm S (imp (fiff2 f g')
        (iff (cls (pf φ) fun χ => cls (pf ψ) fun θ => f χ θ) (cls (pf φ) fun χ => cls (pf ψ) fun θ => g' χ θ))) :=
      fun φ ψ =>
        have l1 : ∀ χ θ, QThm S (imp (fiff2 f g') (iff (E f φ ψ χ θ) (E g' φ ψ χ θ))) := fun χ θ =>
          qsyl (q11_1 (fun χ θ => iff (f χ θ) (g' χ θ)) χ θ)
            (qsyl (qandCongrRImp _ _ (fiff (pf θ) (pf ψ))) (qandCongrRImp _ _ (fiff (pf χ) (pf φ))))  -- ✱10·311 (1)
        have l2 := qsyl (qiffMpr (q11_3 _ _) |> QThm.mp (q11_11 l1)) (q11_341 (E f φ ψ) (E g' φ ψ))  -- (1).✱11·11·3·341
        qimpIffTransL (qiffSymm (r f φ ψ)) (qimpIffTransR l2 (r g' φ ψ))           -- [✱20·1 . ✱10·35] (2)
    qiffMpr (q11_3 _ _) |> QThm.mp (q11_11 l)
  QThm.mp (q12_11 f) (q10_11_28 k)                                                -- (2).✱10·11·28 (3) . (3).✱12·11

/-- ✱20·71 `⊢ :. α = β . ≡ : g!α . ⊃_g . g!β` [✱20·19]: the analogue of ✱13·01. α and β are real
    (expressions ẑ(ψz), ẑ(χz)) and g!α is ✱20·01 with context g!φ!ẑ, so the statement is ✱20·19. -/
theorem q20_71 [Reducibility S] (ψ χ : V a → QF V) :
    QThm S (iff (clsEq ψ χ) (.all (τ := Ty.pred1 (Ty.pred1 a)) fun g =>
      imp (cls ψ fun φ => .app1 g φ) (cls χ fun φ => .app1 g φ))) :=
  q20_19 ψ χ                                                                      -- [✱20·19]

/-! ## ✱20·8–✱20·81: consequences of ✱13·3 -/

/-- ✱20·8 `⊢ : φa ∨ ∼φa . ⊃ . x̂(φx ∨ ∼φx) = x̂(x = a . ∨ . x ≠ a)` -/
theorem q20_8 [Reducibility S] {τ : Ty} (φ : V τ → QF V) (a : V τ) :
    QThm S (imp (.or (φ a) (.neg (φ a)))
      (clsEq (fun x => .or (φ x) (.neg (φ x))) (fun x => .or (ident x a) (nident x a)))) :=
  qsyl (q10_11_21 fun x => q13_3 φ a x)                                           -- ✱13·3 . ✱10·11·21
    (qiffMp (q20_15 _ _))                                                         -- [✱20·15]

/-- ✱20·81 `⊢ : φa ∨ ∼φa . ψa ∨ ∼ψa . ⊃ . x̂(φx ∨ ∼φx) = x̂(ψx ∨ ∼ψx)`. Hp's factors are picked by ✱3·26, ✱3·27
    for the two uses of ✱20·8. PM's ✱10·121 and ✱10·13 identify the a's of (1) and (2): here they are one
    variable of one Lean type, and the lines are joined by Comp (✱3·43). -/
theorem q20_81 [Reducibility S] {τ : Ty} (φ ψ : V τ → QF V) (a : V τ) :
    QThm S (imp (QF.and (.or (φ a) (.neg (φ a))) (.or (ψ a) (.neg (ψ a))))
      (clsEq (fun x => .or (φ x) (.neg (φ x))) (fun x => .or (ψ x) (.neg (ψ x))))) :=
  qsyl (qcomp (qsyl (QL.t3_26 _ _) (q20_8 φ a)) (qsyl (QL.t3_27 _ _) (q20_8 ψ a)))  -- ✱20·8 (1), (2) . Comp
    (q20_24 (fun x => .or (ident x a) (nident x a)) (fun x => .or (φ x) (.neg (φ x)))
      (fun x => .or (ψ x) (.neg (ψ x))))                                          -- [✱20·24]

/-! ## Typical ambiguity (docs/TYPES_DESIGN.md, test F5)

  One Lean theorem is used at several types: ✱13·15 and ✱13·101 at individuals, at predicative
  functions of individuals, and at predicative functions of those. -/

example {V : Ty → Type} (x : V .ind) (φ : V (Ty.pred1 .ind)) (f : V (Ty.pred1 (Ty.pred1 .ind))) :
    QThm S (ident x x) ∧ QThm S (ident φ φ) ∧ QThm S (ident f f) :=
  ⟨q13_15 x, q13_15 φ, q13_15 f⟩

example [Reducibility S] {V : Ty → Type} (x y : V .ind) (φ θ : V (Ty.pred1 .ind)) (ψ : V .ind → QF V)
    (χ : V (Ty.pred1 .ind) → QF V) :
    QThm S (imp (ident x y) (imp (ψ x) (ψ y))) ∧ QThm S (imp (ident φ θ) (imp (χ φ) (χ θ))) :=
  ⟨q13_101 ψ x y, q13_101 χ φ θ⟩

end PM
