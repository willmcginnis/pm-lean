import PM.Star13
/-!
  ✱14: descriptions (1910 print, pp. 181–196; summary pp. 181–183, numbered propositions pp. 184–195).
  The definitions ✱14·01–✱14·04 and 46 of the 47 numbered propositions ✱14·1–✱14·34; ✱14·3 is not
  formalized (below). ✱14·21 was the usability test of the ramified base (docs/TYPES_DESIGN.md, test U4).

  Statements are read from the Gutenberg #78050 transcription of the 1910 print (its formula source), not
  from the scan images. Each proof follows PM's Dem. line by line, or uses the propositions of PM's
  bracketed hint in PM's order; the comment on each Lean line gives PM's line or hint.
  `data/star14_ledger.json` records, per proposition, which cited propositions are used and which further
  ones were needed.

  Descriptions are incomplete symbols (PM p. 66 and ✱14 summary): `(ιx)(φx)` has no meaning by itself,
  only in a context. So there is no term for it. ✱14·01 is a macro that takes the description's
  condition φ and its *scope* ψ (a formula with a hole where the description stands):
    ✱14·01  [(ιx)(φx)] . ψ(ιx)(φx) . = : (∃b) : φx . ≡ₓ . x = b : ψb   Df   (`QF.desc φ ψ`)
    ✱14·02  E!(ιx)(φx) . = : (∃b) : φx . ≡ₓ . x = b                   Df   (`QF.exists1 φ`)
    ✱14·03  [(ιx)(φx), (ιx)(ψx)] . f{…} . = : [(ιx)(φx)] : [(ιx)(ψx)] . f{…}   Df   (`QF.desc2 φ ψ f`)
    ✱14·04  [(ιx)(ψx)] . f{(ιx)(φx), (ιx)(ψx)} . = . [(ιx)(ψx), (ιx)(φx)] . f{…}   Df   (`QF.desc2r φ ψ f`)
  The scope is therefore always explicit: `desc φ (fun z => .neg (χ z))` is [(ιx)(φx)] . ∼χ(ιx)(φx),
  and `.neg (desc φ χ)` is ∼{[(ιx)(φx)] . χ(ιx)(φx)}. PM's conventions become choices the Lean author
  makes when writing the term, and the statements here make them as PM does:
  - an unmarked description has the smallest scope (p. 182): `a = (ιx)(φx)` is
    `desc φ fun z => ident a z`, and in `φy . ≡_y . y = (ιx)(φx)` (✱14·241) the scope is `y = (ιx)(φx)`;
  - of two descriptions, the one written first has the larger scope (p. 182): `(ιx)(φx) = (ιx)(ψx)` is
    `desc2 φ ψ fun b c => ident b c`;
  - ✱14·28's Dem. eliminates "(ιx)(φx)" in `(ιx)(φx) = (ιx)(φx)` once, with scope ẑ = ẑ, so its
    statement is `desc φ fun b => ident b b`.

  Not formalized: ✱14·3 (p. 194). It takes propositions p, q as apparent variables
  (`p ≡ q . ⊃_{p,q} . f(p) ≡ f(q)`), and the types here have no type of propositions (p. 172:
  propositions "will no longer" occur as variables; docs/TYPES_DESIGN.md decision 1). PM itself does not
  use it later and proves ✱14·31–✱14·34 independently "because ✱14·3 introduces propositions … as
  apparent variables, which we have not done elsewhere" (p. 194).

  Steps done silently are those of PM/Star11.lean's header, and also chaining ⊃ and ≡ lines under a
  hypothesis, as PM writes "Hp . ⊃ : A . ≡ . B . [✱x] ≡ . C" (`qimpIffTrans`, `qimpIffTransR`,
  `qimpIffTransL`, `qimpImpTrans`, `qimpImpTransR`, `qimpIffSymm` below; in Lean they need Comp, ✱3·33, ✱2·02 or ✱4·21
  besides Syll and ✱4·22, the way PM/Star11.lean's `qimpCongr` does in ✱11·71). Any other proposition a
  proof needs is named in its docstring and listed as `extra_used` in the ledger.

  Names: `q14_1` is ✱14·1, and so on. φ, ψ, χ are formulas with a hole (PM's real function variables of
  any order); a, b, c are real variables of the description's type `α`.
-/
namespace PM
open QF

namespace QF
variable {V : Ty → Type} {S : Sys}
/-- ✱14·01 `[(ιx)(φx)] . ψ(ιx)(φx) . = : (∃b) : φx . ≡ₓ . x = b : ψb` Df. ψ is the scope. -/
@[reducible] def desc {a : Ty} (φ ψ : V a → QF V) : QF V :=
  ex fun b => QF.and (fiff φ fun x => ident x b) (ψ b)
/-- ✱14·02 `E!(ιx)(φx) . = : (∃b) : φx . ≡ₓ . x = b` Df -/
@[reducible] def exists1 {a : Ty} (φ : V a → QF V) : QF V :=
  ex fun b => fiff φ fun x => ident x b
/-- ✱14·03 `[(ιx)(φx), (ιx)(ψx)] . f{(ιx)(φx), (ιx)(ψx)} . = : [(ιx)(φx)] : [(ιx)(ψx)] . f{(ιx)(φx), (ιx)(ψx)}`
    Df. `f` is the context of both descriptions. -/
@[reducible] def desc2 {a a' : Ty} (φ : V a → QF V) (ψ : V a' → QF V) (f : V a → V a' → QF V) : QF V :=
  desc φ fun y => desc ψ fun z => f y z
/-- ✱14·04 `[(ιx)(ψx)] . f{(ιx)(φx), (ιx)(ψx)} . = . [(ιx)(ψx), (ιx)(φx)] . f{(ιx)(φx), (ιx)(ψx)}` Df: the
    description written second has the larger scope. The right side is ✱14·03 with ψ first. -/
@[reducible] def desc2r {a a' : Ty} (φ : V a → QF V) (ψ : V a' → QF V) (f : V a → V a' → QF V) : QF V :=
  desc2 ψ φ fun z y => f y z
end QF

variable {V : Ty → Type} {S : Sys} {α β : Ty}

/-! ## Steps PM leaves tacit: chaining lines under a hypothesis -/

/-- Chaining two ≡ lines under one hypothesis (Comp ✱3·43, ✱4·22). -/
theorem qimpIffTrans {H A B C : QF V} (h1 : QThm S (imp H (iff A B))) (h2 : QThm S (imp H (iff B C))) :
    QThm S (imp H (iff A C)) :=
  qsyl (qcomp h1 h2) (QL.t4_22 A B C)
/-- Chaining a ≡ line under a hypothesis with an asserted ≡ (✱2·02, ✱3·43, ✱4·22). -/
theorem qimpIffTransR {H A B C : QF V} (h1 : QThm S (imp H (iff A B))) (h2 : QThm S (iff B C)) :
    QThm S (imp H (iff A C)) :=
  qimpIffTrans h1 (QThm.mp h2 (QL.t2_02 H _))
/-- An asserted ≡ followed by a ≡ line under a hypothesis (✱2·02, ✱3·43, ✱4·22). -/
theorem qimpIffTransL {H A B C : QF V} (h1 : QThm S (iff A B)) (h2 : QThm S (imp H (iff B C))) :
    QThm S (imp H (iff A C)) :=
  qimpIffTrans (QThm.mp h1 (QL.t2_02 H _)) h2
/-- Chaining two ⊃ lines under one hypothesis (Comp ✱3·43, Syll ✱3·33). -/
theorem qimpImpTrans {H A B C : QF V} (h1 : QThm S (imp H (imp A B))) (h2 : QThm S (imp H (imp B C))) :
    QThm S (imp H (imp A C)) :=
  qsyl (qcomp h1 h2) (QL.t3_33 A B C)
/-- Chaining a ⊃ line under a hypothesis with an asserted ⊃ (Syll ✱2·05). -/
theorem qimpImpTransR {H A B C : QF V} (h1 : QThm S (imp H (imp A B))) (h2 : QThm S (imp B C)) :
    QThm S (imp H (imp A C)) :=
  qsyl h1 (QThm.mp h2 (QL.t2_05 A B C))
/-- Reading the ≡ of a line under a hypothesis from right to left (✱4·21). -/
theorem qimpIffSymm {H A B : QF V} (h : QThm S (imp H (iff A B))) : QThm S (imp H (iff B A)) :=
  qsyl h (qiffMp (QL.t4_21 A B))

/-! ## Further steps, each listed in the ledger where used -/

/-- ✱4·36 for the second factor: `p ≡ q . ⊃ : r . p . ≡ . r . q` (✱4·36 with ✱4·3). -/
theorem qandCongrRImp (p q r : QF V) : QThm S (imp (iff p q) (iff (QF.and r p) (QF.and r q))) :=
  qimpIffTransL (QL.t4_3 r p) (qimpIffTransR (QL.t4_36 p q r) (QL.t4_3 q r))
/-- From `⊢ . p ≡ q`, `⊢ : r . p . ≡ . r . q` (✱4·36 with ✱4·3). -/
theorem qandCongrR {p q : QF V} (r : QF V) (h : QThm S (iff p q)) : QThm S (iff (QF.and r p) (QF.and r q)) :=
  QThm.mp h (qandCongrRImp p q r)
/-- From `⊢ . p ≡ q`, `⊢ : p . r . ≡ . q . r` (✱4·36). -/
theorem qandCongrL {p q : QF V} (r : QF V) (h : QThm S (iff p q)) : QThm S (iff (QF.and p r) (QF.and q r)) :=
  QThm.mp h (QL.t4_36 p q r)
/-- `p . q . r ≡ q . p . r` for the right-nested product (✱4·32, ✱4·3 with ✱4·36). -/
theorem qandPerm (p q r : QF V) : QThm S (iff (QF.and p (QF.and q r)) (QF.and q (QF.and p r))) :=
  qiffTrans (qiffSymm (QL.t4_32 p q r)) (qiffTrans (qandCongrL r (QL.t4_3 p q)) (QL.t4_32 q p r))
/-- ✱4·86 for the second member: `q ≡ r . ⊃ : p ≡ q . ≡ . p ≡ r` (✱4·86 with ✱4·21). -/
theorem qiffCongrRImp (p q r : QF V) : QThm S (imp (iff q r) (iff (iff p q) (iff p r))) :=
  qimpIffTransL (QL.t4_21 p q) (qimpIffTransR (QL.t4_86 q r p) (QL.t4_21 r p))
/-- ✱4·37 for the second disjunct: `q ≡ r . ⊃ : p ∨ q . ≡ . p ∨ r` (✱4·37 with ✱4·31). -/
theorem qorCongrRImp (p q r : QF V) : QThm S (imp (iff q r) (iff (.or p q) (.or p r))) :=
  qimpIffTransL (QL.t4_31 p q) (qimpIffTransR (QL.t4_37 q r p) (QL.t4_31 r p))
/-- From `⊢ . q`, `p ≡ q . ⊃ . p` (✱3·27, Comm ✱2·04): an equivalence with an asserted side. -/
theorem qiffElimOf {p q : QF V} (hq : QThm S q) : QThm S (imp (iff p q) p) :=
  QThm.mp hq (QThm.mp (QL.t3_27 _ _) (QL.t2_04 _ _ _))

/-! ## Descriptions with formally equivalent conditions or scopes -/

/-- The lines of ✱14·272's Dem.: `φx ≡ₓ ψx . ⊃ : [(ιx)(φx)] . χ(ιx)(φx) . ≡ . [(ιx)(ψx)] . χ(ιx)(ψx)`.
    ✱4·86 under (x) (✱10·11·27, ✱10·271), Fact as ✱4·36, then ✱10·11·21 and ✱10·281. -/
theorem qdescCongr (φ ψ χ : V α → QF V) : QThm S (imp (fiff φ ψ) (iff (desc φ χ) (desc ψ χ))) :=
  have h1 : ∀ b : V α, QThm S (imp (fiff φ ψ)
      (iff (fiff φ fun x => ident x b) (fiff ψ fun x => ident x b))) := fun b =>
    qsyl (q10_11_27 fun x => QL.t4_86 (φ x) (ψ x) (ident x b))                 -- ✱4·86 [✱10·11·27]
      (q10_271 (fun x => iff (φ x) (ident x b)) (fun x => iff (ψ x) (ident x b)))  -- [✱10·271]
  have h2 : ∀ b : V α, QThm S (imp (fiff φ ψ) (iff (QF.and (fiff φ fun x => ident x b) (χ b))
      (QF.and (fiff ψ fun x => ident x b) (χ b)))) := fun b =>
    qsyl (h1 b) (QL.t4_36 _ _ (χ b))                                           -- [Fact]
  qsyl (q10_11_21 h2) (q10_281 _ _)                                            -- [✱10·11·21] [✱10·281]

/-- A scope replaced by a formally equivalent one: `χx ≡ₓ θx . ⊃ : [(ιx)(φx)] . χ(ιx)(φx) . ≡ .
    [(ιx)(φx)] . θ(ιx)(φx)` (✱10·1, ✱4·36 on the second factor (with ✱4·3), ✱10·11·21, ✱10·281). -/
theorem qdescScope (φ χ θ : V α → QF V) : QThm S (imp (fiff χ θ) (iff (desc φ χ) (desc φ θ))) :=
  have h : ∀ b : V α, QThm S (imp (fiff χ θ) (iff (QF.and (fiff φ fun x => ident x b) (χ b))
      (QF.and (fiff φ fun x => ident x b) (θ b)))) := fun b =>
    qsyl (q10_1 (fun x => iff (χ x) (θ x)) b) (qandCongrRImp _ _ _)
  qsyl (q10_11_21 h) (q10_281 _ _)

/-- Line (2) of ✱14·15 and of ✱14·16: `φx ≡ₓ x = b . ⊃ : ψ(ιx)(φx) . ≡ . ψb`. ✱14·1, then the step
    from φx ≡ₓ x = b to (∃c) : x = b . ≡ₓ . x = c : ψc, which PM leaves tacit and is ✱14·272's
    argument (`qdescCongr`), then ✱13·192. -/
theorem qdescAt [Reducibility S] (φ ψ : V α → QF V) (b : V α) :
    QThm S (imp (fiff φ fun x => ident x b) (iff (desc φ ψ) (ψ b))) :=
  qimpIffTransR (qdescCongr φ (fun x => ident x b) ψ) (q13_192 ψ b)

/-- `a = (ιx)(φx) . ≡ : φx . ≡ₓ . x = a`: line (1) of ✱14·145 (✱14·1 [✱13·195]). ✱13·195 needs
    `b = a . F b`; ✱14·1 gives `F b : a = b`, so the factors are commuted (✱4·3) and a = b turned by
    ✱13·16 (with ✱4·36), under (∃b) by ✱10·11·281. -/
theorem qidentDesc [Reducibility S] (φ : V α → QF V) (a : V α) :
    QThm S (iff (desc φ fun z => ident a z) (fiff φ fun x => ident x a)) :=
  let F : V α → QF V := fun b => fiff φ fun x => ident x b
  qiffTrans (q10_11_281 fun b => qiffTrans (QL.t4_3 (F b) (ident a b)) (qandCongrL (F b) (q13_16 a b)))
    (q13_195 F a)                                                               -- ✱14·1 [✱13·195]

/-! ## ✱14·1–✱14·124 -/

/-- ✱14·1 `⊢ :. [(ιx)(φx)] . ψ(ιx)(φx) . ≡ : (∃b) : φx . ≡ₓ . x = b : ψb` [✱4·2 . (✱14·01)] -/
theorem q14_1 (φ ψ : V α → QF V) :
    QThm S (iff (desc φ ψ) (ex fun b => QF.and (fiff φ fun x => ident x b) (ψ b))) :=
  QL.t4_2 _

/-- ✱14·101 `⊢ :. ψ(ιx)(φx) . ≡ : (∃b) : φx . ≡ₓ . x = b : ψb` [✱14·1]. With the scope explicit in the
    Lean term, this is ✱14·1 again: PM's convention reads the unmarked ψ(ιx)(φx) as having scope ψ. -/
theorem q14_101 (φ ψ : V α → QF V) :
    QThm S (iff (desc φ ψ) (ex fun b => QF.and (fiff φ fun x => ident x b) (ψ b))) :=
  q14_1 φ ψ

/-- ✱14·11 `⊢ :. E!(ιx)(φx) . ≡ : (∃b) : φx . ≡ₓ . x = b` [✱4·2 . (✱14·02)] -/
theorem q14_11 (φ : V α → QF V) : QThm S (iff (exists1 φ) (ex fun b => fiff φ fun x => ident x b)) :=
  QL.t4_2 _

/-- ✱14·111 `⊢ :. [(ιx)(ψx)] . f{(ιx)(φx), (ιx)(ψx)} . ≡ : (∃b, c) : φx . ≡ₓ . x = b : ψx . ≡ₓ . x = c :
    f(b, c)`. The first three lines are definitional (✱4·2, ✱14·04·03, ✱14·1 twice). ✱11·55 gives
    `(∃c, b) . ψx ≡ₓ x = c . φx ≡ₓ x = b . f(b, c)`; PM's last line (whose transcription has "x = c" twice)
    has (∃b, c) and the factors in the order of the statement: the variables are interchanged by ✱11·23
    and the factors permuted by ✱4·32, ✱4·3 (with ✱4·36), under (b, c) by ✱11·11·341. -/
theorem q14_111 (φ : V α → QF V) (ψ : V β → QF V) (f : V α → V β → QF V) :
    QThm S (iff (desc2r φ ψ f) (ex2 fun b c => QF.and (fiff φ fun x => ident x b)
      (QF.and (fiff ψ fun x => ident x c) (f b c)))) :=
  let Fφ : V α → QF V := fun b => fiff φ fun x => ident x b
  let Fψ : V β → QF V := fun c => fiff ψ fun x => ident x c
  have h1 := qiffSymm (q11_55 Fψ fun c b => QF.and (Fφ b) (f b c))              -- [✱11·55]
  have h2 := q11_23 fun c b => QF.and (Fψ c) (QF.and (Fφ b) (f b c))           -- ✱11·23
  have h3 := QThm.mp (q11_11 fun b c => qandPerm (Fψ c) (Fφ b) (f b c))
    (q11_341 (fun b c => QF.and (Fψ c) (QF.and (Fφ b) (f b c)))
      (fun b c => QF.and (Fφ b) (QF.and (Fψ c) (f b c))))                       -- ✱4·32·3 . ✱11·11·341
  qiffTrans h1 (qiffTrans h2 h3)

/-- ✱14·112 `⊢ :. f{(ιx)(φx), (ιx)(ψx)} . ≡ : (∃b, c) : φx . ≡ₓ . x = b : ψx . ≡ₓ . x = c : f(b, c)`
    [Proof as in ✱14·111]. The unmarked f{(ιx)(φx), (ιx)(ψx)} gives the first description the larger
    scope (p. 182), i.e. ✱14·03; ✱4·2, ✱14·03 and ✱14·1 twice are definitional, and ✱11·55 is the
    last line. -/
theorem q14_112 (φ : V α → QF V) (ψ : V β → QF V) (f : V α → V β → QF V) :
    QThm S (iff (desc2 φ ψ f) (ex2 fun b c => QF.and (fiff φ fun x => ident x b)
      (QF.and (fiff ψ fun x => ident x c) (f b c)))) :=
  qiffSymm (q11_55 (fun b => fiff φ fun x => ident x b)
    fun b c => QF.and (fiff ψ fun x => ident x c) (f b c))                      -- [✱11·55]

/-- ✱14·113 `⊢ : [(ιx)(ψx)] . f{(ιx)(φx), (ιx)(ψx)} . ≡ . f{(ιx)(φx), (ιx)(ψx)}` [✱14·111·112]: "the
    truth-value of the proposition is unaffected by the question which has the larger scope". -/
theorem q14_113 (φ : V α → QF V) (ψ : V β → QF V) (f : V α → V β → QF V) :
    QThm S (iff (desc2r φ ψ f) (desc2 φ ψ f)) :=
  qiffTrans (q14_111 φ ψ f) (qiffSymm (q14_112 φ ψ f))

/-- ✱14·12 `⊢ :. E!(ιx)(φx) . ⊃ : φx . φy . ⊃_{x,y} . x = y`. In (2), ✱10·1 is used at x and at y and
    the two joined by Comp (✱3·43); the "≡" of ✱4·38 is used left to right (✱3·26) and chained with
    ✱13·172 by Syll (✱2·05). -/
theorem q14_12 [Reducibility S] (φ : V α → QF V) :
    QThm S (imp (exists1 φ) (fimp2 (fun x y => QF.and (φ x) (φ y)) fun x y => ident x y)) :=
  have h1 := qiffMp (q14_11 φ)                                                   -- ✱14·11 (1)
  have h2 : ∀ b x y, QThm S (imp (fiff φ fun x => ident x b)
      (imp (QF.and (φ x) (φ y)) (ident x y))) := fun b x y =>
    have e := qsyl (qcomp (q10_1 (fun x => iff (φ x) (ident x b)) x)
      (q10_1 (fun x => iff (φ x) (ident x b)) y)) (QL.t4_38 _ _ _ _)           -- ✱4·38 . ✱10·1
    qsyl (qsyl e (QL.t3_26 _ _)) (QThm.mp (q13_172 b x y) (QL.t2_05 _ _ _))    -- [✱13·172] (2)
  have h2' : ∀ b, QThm S (imp (fiff φ fun x => ident x b)
      (fimp2 (fun x y => QF.and (φ x) (φ y)) fun x y => ident x y)) := fun b =>
    qiffMpr (q11_3 _ _) |> QThm.mp (q11_11 (h2 b))                              -- ✱11·11·3
  qsyl h1 (QThm.mp (q10_11 h2') (qiffMp (q10_23 _ _)))                          -- (2).✱10·11·23 (3) . (1).(3)

/-- From ⊢ x = x, `φx . ≡ . x = x : ⊃ . φx` (used in ✱14·121 and ✱14·201 for "[✱13·15]"):
    ✱3·27, Comm (✱2·04) and ✱13·15. -/
theorem qiff_refl_elim (φ : V α → QF V) (x : V α) : QThm S (imp (iff (φ x) (ident x x)) (φ x)) :=
  qiffElimOf (q13_15 x)

/-- ✱14·121 `⊢ :. φx . ≡ₓ . x = b : φx . ≡ₓ . x = c : ⊃ . b = c`. ✱10·1 at b for both factors is ✱10·14;
    "[Ass]" is ✱3·35, after ✱3·26 turns φb ≡ b = c into φb ⊃ b = c. -/
theorem q14_121 (φ : V α → QF V) (b c : V α) :
    QThm S (imp (QF.and (fiff φ fun x => ident x b) (fiff φ fun x => ident x c)) (ident b c)) :=
  have h1 := q10_14 (fun x => iff (φ x) (ident x b)) (fun x => iff (φ x) (ident x c)) b  -- ✱10·1
  have h2 := QThm.mp (qiff_refl_elim φ b) (QL.t3_45 _ _ _)                       -- [✱13·15]
  qsyl h1 (qsyl h2 (qsyl (qandR (QL.t3_26 _ _)) (QL.t3_35 _ _)))                 -- [Ass]

/-- ✱14·122 `⊢ :. φx . ≡ₓ . x = b : ≡ : φx . ⊃ₓ . x = b : φb : ≡ : φx . ⊃ₓ . x = b : (∃x) . φx`. The chain
    is stated as `A ≡ B . B ≡ C`. In (1), ✱13·191 replaces the second factor (✱4·36 with ✱4·3); in (2),
    ✱13·195 needs `x = b . φx`, so the factors are commuted (✱4·3) under (∃x) by ✱10·11·281. -/
theorem q14_122 [Reducibility S] (φ : V α → QF V) (b : V α) :
    QThm S (QF.and
      (iff (fiff φ fun x => ident x b) (QF.and (fimp φ fun x => ident x b) (φ b)))
      (iff (QF.and (fimp φ fun x => ident x b) (φ b)) (QF.and (fimp φ fun x => ident x b) (ex φ)))) :=
  let H : QF V := fimp φ fun x => ident x b
  have h1 := qiffTrans (q10_22 (fun x => imp (φ x) (ident x b)) (fun x => imp (ident x b) (φ x)))  -- ✱10·22
    (qandCongrR H (q13_191 φ b))                                                -- [✱13·191] (1)
  have h2 : QThm S (imp H (iff (ex φ) (φ b))) :=
    qimpIffTransR
      (qsyl (q10_11_27 fun x => qiffMp (QL.t4_71 (φ x) (ident x b)))            -- ✱4·71 [✱10·11·27]
        (q10_281 φ fun x => QF.and (φ x) (ident x b)))                          -- [✱10·281]
      (qiffTrans (q10_11_281 fun x => QL.t4_3 (φ x) (ident x b)) (q13_195 φ b)) -- [✱13·195] (2)
  have h3 := QThm.mp h2 (qiffMp (QL.t5_32 H (ex φ) (φ b)))                      -- (2).✱5·32 (3)
  qandI h1 (qiffSymm h3)                                                        -- (1).(3)

/-- ✱14·123 `⊢ :. φ(z, w) . ≡_{z,w} . z = x . w = y : ≡ : φ(z, w) . ⊃_{z,w} . z = x . w = y : φ(x, y) : ≡ :
    φ(z, w) . ⊃_{z,w} . z = x . w = y : (∃z, w) . φ(z, w)`. The chain is stated as `A ≡ B . B ≡ C`. In (1),
    ✱13·21 replaces the second factor (✱4·36 with ✱4·3); in (2), ✱13·22 needs `z = x . w = y . φ(z, w)`,
    so the factors are rearranged (✱4·3, ✱4·32) under (z, w) by ✱11·11·341. -/
theorem q14_123 [Reducibility S] (φ : V α → V β → QF V) (x : V α) (y : V β) :
    QThm S (QF.and
      (iff (fiff2 φ fun z w => QF.and (ident z x) (ident w y))
        (QF.and (fimp2 φ fun z w => QF.and (ident z x) (ident w y)) (φ x y)))
      (iff (QF.and (fimp2 φ fun z w => QF.and (ident z x) (ident w y)) (φ x y))
        (QF.and (fimp2 φ fun z w => QF.and (ident z x) (ident w y)) (ex2 φ)))) :=
  let E : V α → V β → QF V := fun z w => QF.and (ident z x) (ident w y)
  let H : QF V := fimp2 φ E
  have h1 := qiffTrans (qiffSymm (q11_31 (fun z w => imp (φ z w) (E z w)) (fun z w => imp (E z w) (φ z w))))  -- ✱11·31
    (qandCongrR H (q13_21 φ x y))                                               -- [✱13·21] (1)
  have r : ∀ z w, QThm S (iff (QF.and (φ z w) (E z w))
      (QF.and (ident z x) (QF.and (ident w y) (φ z w)))) := fun z w =>
    qiffTrans (QL.t4_3 (φ z w) (E z w)) (QL.t4_32 (ident z x) (ident w y) (φ z w))
  have h2 : QThm S (imp H (iff (ex2 φ) (φ x y))) :=
    qimpIffTransR
      (qsyl (QThm.mp (q11_11 fun z w => qiffMp (QL.t4_71 (φ z w) (E z w)))
          (q11_32 (fun z w => imp (φ z w) (E z w)) (fun z w => iff (φ z w) (QF.and (φ z w) (E z w)))))  -- ✱4·71 [✱11·11·32]
        (q11_341 φ fun z w => QF.and (φ z w) (E z w)))                          -- [✱11·341]
      (qiffTrans (QThm.mp (q11_11 r) (q11_341 _ _)) (q13_22 φ x y))             -- [✱13·22] (2)
  have h3 := QThm.mp h2 (qiffMp (QL.t5_32 H (ex2 φ) (φ x y)))                   -- (2).✱5·32 (3)
  qandI h1 (qiffSymm h3)                                                        -- (1).(3)

/-- ✱14·124 `⊢ :. (∃x, y) : φ(z, w) . ≡_{z,w} . z = x . w = y : ≡ : (∃x, y) . φ(x, y) : φ(z, w) . φ(u, v) .
    ⊃_{z,w,u,v} . z = u . w = v`. "⊃_{z,w,u,v}" is `(z, w) : (u, v)`, ✱11·01 twice. Steps PM leaves
    tacit: (1) takes ✱14·123's chain end to end (✱3·26, ✱3·27) and removes (∃x, y) by ✱11·11·35, cited
    in (3); in (2), ✱11·1 is used at (z, w) and at (u, v), its ⊃ halves taken by ✱3·26 and joined by
    Comp before ✱3·47, and z = x, u = x and w = y, v = y are picked out (✱3·26, ✱3·27) and joined by Comp
    for the two uses of ✱13·172; (4) uses ✱11·11·3 twice; in (5), ✱11·1 is carried under (z, w) by
    ✱11·11·3 and applied to the second factor (✱3·47 with Id, ✱2·08), ✱5·33 needs φ(x, y) . φ(z, w) where
    Hp has φ(z, w) . φ(x, y) (✱3·22, ✱2·06), is exported by ✱3·27 and Exp (✱3·3), carried under (z, w) by
    ✱11·11·3 and ✱11·32 and imported by ✱3·31, φ(x, y) being kept by ✱3·26 and Comp; (∃z, w) . φ(z, w) is
    got from φ(x, y) by ✱11·36; (6) needs `U . φ(x, y)` for ✱11·45, so the factors are commuted (✱4·3,
    ✱3·22); the last line joins (1) and (4) by Comp. -/
theorem q14_124 [Reducibility S] (φ : V α → V β → QF V) :
    QThm S (iff
      (ex2 fun x y => fiff2 φ fun z w => QF.and (ident z x) (ident w y))
      (QF.and (ex2 φ) (all2 fun z w => all2 fun u v =>
        imp (QF.and (φ z w) (φ u v)) (QF.and (ident z u) (ident w v))))) :=
  let E : V α → V β → V α → V β → QF V := fun x y z w => QF.and (ident z x) (ident w y)
  let F : V α → V β → QF V := fun x y => fiff2 φ (E x y)
  let G : V α → V β → QF V := fun x y => fimp2 φ (E x y)
  let K : V α → V β → V α → V β → QF V := fun z w u v =>
    imp (QF.and (φ z w) (φ u v)) (QF.and (ident z u) (ident w v))
  let U : QF V := all2 fun z w => all2 (K z w)
  have c1 : ∀ x y, QThm S (iff (F x y) (QF.and (G x y) (ex2 φ))) := fun x y =>
    have c := q14_123 φ x y
    qiffTrans (QThm.mp c (QL.t3_26 _ _)) (QThm.mp c (QL.t3_27 _ _))
  have h1 : QThm S (imp (ex2 F) (ex2 φ)) :=
    qiffMp (q11_35 F (ex2 φ)) |> QThm.mp (q11_11 fun x y =>
      qsyl (qiffMp (c1 x y)) (QL.t3_27 _ _))                                    -- ✱14·123 . ✱3·27 (1)
  have h2 : ∀ x y z w u v, QThm S (imp (F x y) (K z w u v)) := fun x y z w u v =>
    let P : V α → V β → QF V := fun z w => iff (φ z w) (E x y z w)
    have a3 : QThm S (imp (F x y)
        (imp (QF.and (φ z w) (φ u v)) (QF.and (E x y z w) (E x y u v)))) :=
      qsyl (qcomp (qsyl (q11_1 P z w) (QL.t3_26 _ _)) (qsyl (q11_1 P u v) (QL.t3_26 _ _)))
        (QL.t3_47 (φ z w) (φ u v) (E x y z w) (E x y u v))                     -- ✱11·1 . ✱3·47
    have m1 : QThm S (imp (QF.and (E x y z w) (E x y u v)) (ident z u)) :=
      qsyl (qcomp (qsyl (QL.t3_26 _ _) (QL.t3_26 _ _)) (qsyl (QL.t3_27 _ _) (QL.t3_26 _ _)))
        (q13_172 x z u)
    have m2 : QThm S (imp (QF.and (E x y z w) (E x y u v)) (ident w v)) :=
      qsyl (qcomp (qsyl (QL.t3_26 _ _) (QL.t3_27 _ _)) (qsyl (QL.t3_27 _ _) (QL.t3_27 _ _)))
        (q13_172 y w v)
    qimpImpTransR a3 (qcomp m1 m2)                                              -- [✱13·172] (2)
  have h4 : QThm S (imp (ex2 F) U) :=
    qiffMpr (q11_3 (ex2 F) fun z w => all2 (K z w)) |> QThm.mp (q11_11 fun z w =>
      qiffMpr (q11_3 (ex2 F) (K z w)) |> QThm.mp (q11_11 fun u v =>
        qiffMp (q11_35 F (K z w u v)) |> QThm.mp (q11_11 fun x y => h2 x y z w u v)))  -- (2).✱11·11·35 (3), (3).✱11·11·3 (4)
  have h5 : ∀ x y, QThm S (imp (QF.and (φ x y) U) (F x y)) := fun x y =>
    let A : V α → V β → QF V := fun z w => K z w x y
    have u1 : QThm S (imp U (all2 A)) :=
      qiffMpr (q11_3 U A) |> QThm.mp (q11_11 fun z w =>
        qsyl (q11_1 (fun z w => all2 (K z w)) z w) (q11_1 (K z w) x y))         -- ✱11·1
    have e : ∀ z w, QThm S (imp (φ x y) (imp (A z w) (imp (φ z w) (E x y z w)))) := fun z w =>
      have s1 := QThm.mp (QL.t3_22 (φ x y) (φ z w)) (QL.t2_06 _ _ (E x y z w))
      QThm.mp (qsyl (qsyl (qandR s1) (qiffMpr (QL.t5_33 (φ x y) (φ z w) (E x y z w)))) (QL.t3_27 _ _))
        (QL.t3_3 _ _ _)                                                         -- [✱5·33]
    have e2 : QThm S (imp (φ x y) (imp (all2 A) (G x y))) :=
      qsyl (qiffMpr (q11_3 (φ x y) fun z w => imp (A z w) (imp (φ z w) (E x y z w))) |>
          QThm.mp (q11_11 e))
        (q11_32 A fun z w => imp (φ z w) (E x y z w))
    have e3 : QThm S (imp (QF.and (φ x y) (all2 A)) (QF.and (G x y) (ex2 φ))) :=
      qcomp (QThm.mp e2 (QL.t3_31 _ _ _)) (qsyl (QL.t3_26 _ _) (q11_36 φ x y))
    qsyl (qandR u1) (qsyl e3 (qiffMpr (c1 x y)))                               -- [✱14·123] (5)
  have h6 : QThm S (imp (QF.and (ex2 φ) U) (ex2 F)) :=
    qsyl (qiffMp (qiffTrans (QL.t4_3 (ex2 φ) U) (qiffSymm (q11_45 φ U))))       -- [✱11·45]
      (QThm.mp (q11_11 fun x y => qsyl (QL.t3_22 U (φ x y)) (h5 x y))
        (q11_34 (fun x y => QF.and U (φ x y)) F))                               -- (5).✱11·11·34 (6)
  qiffI (qcomp h1 h4) h6                                                        -- (1).(4).(6)

/-! ## ✱14·13–✱14·18 -/

/-- ✱14·13 `⊢ : a = (ιx)(φx) . ≡ . (ιx)(φx) = a`. In (2), ✱4·36 is used on the second factor (with
    ✱4·3). PM (p. 186): "This proposition is not an immediate consequence of ✱13·16, because
    'a = (ιx)(φx)' is not a value of the function 'x = y'." -/
theorem q14_13 [Reducibility S] (φ : V α → QF V) (a : V α) :
    QThm S (iff (desc φ fun z => ident a z) (desc φ fun z => ident z a)) :=
  q10_11_281 fun b => qandCongrR _ (q13_16 a b)                                 -- ✱14·1 . ✱13·16 . ✱4·36 [✱10·11·281] [✱14·1]

/-- ✱14·131 `⊢ : (ιx)(φx) = (ιx)(ψx) . ≡ . (ιx)(ψx) = (ιx)(φx)`, each description written first having the
    larger scope (p. 187). ✱11·6 needs the factors `(∃c) . b = c . ψx ≡ₓ x = c : φx ≡ₓ x = b`, so those
    of the ✱14·1 lines are commuted (✱4·3, with ✱4·36) under (∃b), (∃c) by ✱10·11·281, before ✱11·6 and
    back after it. -/
theorem q14_131 [Reducibility S] (φ ψ : V α → QF V) :
    QThm S (iff (desc2 φ ψ fun b c => ident b c) (desc2 ψ φ fun c b => ident c b)) :=
  let Fφ : V α → QF V := fun b => fiff φ fun x => ident x b
  let Fψ : V α → QF V := fun c => fiff ψ fun x => ident x c
  have h1 : QThm S (iff (desc2 φ ψ fun b c => ident b c)
      (ex fun b => QF.and (ex fun c => QF.and (ident b c) (Fψ c)) (Fφ b))) :=
    q10_11_281 fun b => qiffTrans (QL.t4_3 (Fφ b) _)
      (qandCongrL (Fφ b) (q10_11_281 fun c => QL.t4_3 (Fψ c) (ident b c)))     -- ✱14·1 . ✱14·1
  have h2 := q11_6 (fun b c => ident b c) Fψ Fφ                                 -- [✱11·6]
  have h3 : QThm S (iff (ex fun c => QF.and (ex fun b => QF.and (ident b c) (Fφ b)) (Fψ c))
      (ex fun c => QF.and (Fψ c) (desc φ fun b => ident c b))) :=
    q10_11_281 fun c => qiffTrans (QL.t4_3 _ (Fψ c))
      (qandCongrR (Fψ c) (qiffTrans (q10_11_281 fun b => QL.t4_3 (ident b c) (Fφ b))  -- [✱14·1]
        (qiffSymm (q14_13 φ c))))                                               -- [✱14·13]
  qiffTrans h1 (qiffTrans h2 h3)                                                -- [✱14·1]

/-- ✱14·14 `⊢ : a = b . b = (ιx)(φx) . ⊃ . a = (ιx)(φx)` [✱13·13]. ✱13·13 with ψẑ the formula
    ẑ = (ιx)(φx), b for x and a for y needs `b = (ιx)(φx) . b = a`: a = b is turned by ✱13·16 (on the
    second factor, ✱3·47 with Id) and the factors commuted by ✱3·22. -/
theorem q14_14 [Reducibility S] (φ : V α → QF V) (a b : V α) :
    QThm S (imp (QF.and (ident a b) (desc φ fun z => ident b z)) (desc φ fun z => ident a z)) :=
  qsyl (qsyl (QL.t3_22 _ _) (qandR (qiffMp (q13_16 a b))))
    (q13_13 (fun z => desc φ fun c => ident z c) b a)                           -- [✱13·13]

/-- ✱14·142 `⊢ : a = (ιx)(φx) . (ιx)(φx) = (ιx)(ψx) . ⊃ . a = (ιx)(ψx)`. "[✱13·195]" in the second line is
    `qidentDesc` (✱13·195 with ✱13·16 and ✱4·3), applied to the first factor by ✱4·36; "[✱14·121]"
    picks out φx ≡ₓ x = a and φx ≡ₓ x = c by ✱3·26, ✱3·27 and joins them by Comp; in the last line
    ✱13·195 needs c = a, got from a = c by ✱13·16 with Fact (✱3·45). -/
theorem q14_142 [Reducibility S] (φ ψ : V α → QF V) (a : V α) :
    QThm S (imp (QF.and (desc φ fun z => ident a z) (desc2 φ ψ fun b c => ident b c))
      (desc ψ fun z => ident a z)) :=
  let Fφ : V α → QF V := fun b => fiff φ fun x => ident x b
  let R : V α → QF V := fun c => desc ψ fun z => ident c z
  have h1 := qandCongrL (desc2 φ ψ fun b c => ident b c) (qidentDesc φ a)       -- ✱14·1 [✱13·195]
  have h2 := qiffSymm (q10_35 (fun c => QF.and (Fφ c) (R c)) (Fφ a))           -- [✱10·35]
  have h3 : ∀ c, QThm S (imp (QF.and (Fφ a) (QF.and (Fφ c) (R c)))
      (QF.and (Fφ a) (QF.and (ident a c) (R c)))) := fun c =>
    qcomp (QL.t3_26 _ _)
      (qcomp (qsyl (qcomp (QL.t3_26 _ _) (qsyl (QL.t3_27 _ _) (QL.t3_26 _ _))) (q14_121 φ a c))
        (qsyl (QL.t3_27 _ _) (QL.t3_27 _ _)))                                   -- [✱14·121]
  have h4 : ∀ c, QThm S (imp (QF.and (Fφ a) (QF.and (ident a c) (R c))) (QF.and (ident c a) (R c))) :=
    fun c => qsyl (QL.t3_27 _ _) (QThm.mp (qiffMp (q13_16 a c)) (QL.t3_45 _ _ _))  -- [✱3·27]
  qsyl (qiffMp (qiffTrans h1 h2))
    (qsyl (q10_11_28 h3) (qsyl (q10_11_28 h4) (qiffMp (q13_195 R a))))          -- [✱13·195]

/-- `(ιx)(θx) = (ιx)(θ'x) . ⊃ : (∃a) : θx . ≡ₓ . x = a : θ'x . ≡ₓ . x = a`: the first two lines of
    ✱14·144's Dem. (✱14·111, read as ✱14·112, then ✱13·195, which here is ✱10·35 and `qidentDesc`). -/
theorem qdescEqCommon [Reducibility S] (θ θ' : V α → QF V) :
    QThm S (imp (desc2 θ θ' fun b c => ident b c)
      (ex fun a => QF.and (fiff θ fun x => ident x a) (fiff θ' fun x => ident x a))) :=
  qiffMp (qiffTrans (q14_112 θ θ' fun b c => ident b c)
    (q10_11_281 fun a => qiffTrans (q10_35 _ _) (qandCongrR _ (qidentDesc θ' a))))

/-- ✱14·144 `⊢ : (ιx)(φx) = (ιx)(ψx) . (ιx)(ψx) = (ιx)(χx) . ⊃ . (ιx)(φx) = (ιx)(χx)`. PM cites ✱14·111
    for the form `(∃a, b) : φx . ≡ₓ . x = a : ψx . ≡ₓ . x = b : a = b`; with PM's convention (p. 182) that is
    the unmarked description's ✱14·112 (equivalent by ✱14·113). The two factors of Hp are treated by
    ✱3·47; "[✱13·195]" is ✱10·35 with `qidentDesc` (✱13·195, ✱13·16, ✱4·3, ✱4·36); "[✱14·121 . ✱11·42]"
    picks out the factors (✱3·26, ✱3·27, Comp) and is carried under (∃a, c) by ✱11·11·34 (✱11·42
    distributes (∃a, c) over a product, which this step does not need). -/
theorem q14_144 [Reducibility S] (φ ψ χ : V α → QF V) :
    QThm S (imp (QF.and (desc2 φ ψ fun b c => ident b c) (desc2 ψ χ fun b c => ident b c))
      (desc2 φ χ fun b c => ident b c)) :=
  let Fφ : V α → QF V := fun b => fiff φ fun x => ident x b
  let Fψ : V α → QF V := fun b => fiff ψ fun x => ident x b
  let Fχ : V α → QF V := fun b => fiff χ fun x => ident x b
  have h1 := QThm.mp (qandI (qdescEqCommon φ ψ) (qdescEqCommon ψ χ)) (QL.t3_47 _ _ _ _)  -- ✱14·111 [✱13·195]
  have h2 := qiffMpr (q11_54 (fun a => QF.and (Fφ a) (Fψ a)) fun c => QF.and (Fψ c) (Fχ c))  -- [✱11·54]
  have h3 : ∀ a c, QThm S (imp (QF.and (QF.and (Fφ a) (Fψ a)) (QF.and (Fψ c) (Fχ c)))
      (QF.and (Fφ a) (QF.and (Fχ c) (ident a c)))) := fun a c =>
    qcomp (qsyl (QL.t3_26 _ _) (QL.t3_26 _ _))
      (qcomp (qsyl (QL.t3_27 _ _) (QL.t3_27 _ _))
        (qsyl (qcomp (qsyl (QL.t3_26 _ _) (QL.t3_27 _ _)) (qsyl (QL.t3_27 _ _) (QL.t3_26 _ _)))
          (q14_121 ψ a c)))                                                     -- [✱14·121]
  have h4 := QThm.mp (q11_11 h3) (q11_34 _ _)                                   -- [✱11·11·34]
  qsyl h1 (qsyl h2 (qsyl h4 (qiffMpr (q14_112 φ χ fun b c => ident b c))))      -- [✱14·111]

/-- ✱14·145 `⊢ : a = (ιx)(φx) . a = (ιx)(ψx) . ⊃ . (ιx)(φx) = (ιx)(ψx)`. Line (1) is `qidentDesc`
    (✱14·1, ✱13·195, with ✱13·16 and ✱4·3), used on the first factor of Hp by ✱4·36. The last line
    takes (∃b) : φx ≡ₓ x = a : ψx ≡ₓ x = b : a = b to (∃a, b) . … by ✱10·24 and then, as in ✱14·144, PM's
    ✱14·111 is ✱14·112 for the unmarked descriptions. -/
theorem q14_145 [Reducibility S] (φ ψ : V α → QF V) (a : V α) :
    QThm S (imp (QF.and (desc φ fun z => ident a z) (desc ψ fun z => ident a z))
      (desc2 φ ψ fun b c => ident b c)) :=
  let Fφ : V α → QF V := fun b => fiff φ fun x => ident x b
  let Fψ : V α → QF V := fun b => fiff ψ fun x => ident x b
  have h1 := qandCongrL (desc ψ fun z => ident a z) (qidentDesc φ a)           -- (1) . ✱14·1
  have h2 := qiffSymm (q10_35 (fun b => QF.and (Fψ b) (ident a b)) (Fφ a))     -- [✱10·35]
  have h3 := q10_24 (fun a' => ex fun b => QF.and (Fφ a') (QF.and (Fψ b) (ident a' b))) a  -- ✱10·24
  qsyl (qiffMp (qiffTrans h1 h2)) (qsyl h3 (qiffMpr (q14_112 φ ψ fun b c => ident b c)))  -- [✱14·111]

/-- ✱14·15 `⊢ :. (ιx)(φx) = b . ⊃ : ψ{(ιx)(φx)} . ≡ . ψb`. In (1), ✱13·195 needs `c = b . F c`, so the
    factors are commuted (✱4·3) under (∃c) by ✱10·11·281. (2) is `qdescAt`: ✱14·1, ✱13·192, and the
    step PM leaves tacit between them (✱14·272's argument). -/
theorem q14_15 [Reducibility S] (φ ψ : V α → QF V) (b : V α) :
    QThm S (imp (desc φ fun z => ident z b) (iff (desc φ ψ) (ψ b))) :=
  let F : V α → QF V := fun c => fiff φ fun x => ident x c
  have h1 := qiffMp (qiffTrans (q10_11_281 fun c => QL.t4_3 (F c) (ident c b)) (q13_195 F b))  -- ✱14·1 [✱13·195] (1)
  qsyl h1 (qdescAt φ ψ b)                                                       -- (1).✱14·1 [✱13·192]

/-- ✱14·16 `⊢ :. (ιx)(φx) = (ιx)(ψx) . ⊃ : χ{(ιx)(φx)} . ≡ . χ{(ιx)(ψx)}`. (2) is `qdescAt` as in ✱14·15;
    in (4), (2) and (3) are joined on the product by ✱3·47; the last line's "✱10·1·23" is done by
    ✱10·11 and ✱10·23 (✱10·1 is not needed). -/
theorem q14_16 [Reducibility S] (φ ψ χ : V α → QF V) :
    QThm S (imp (desc2 φ ψ fun b c => ident b c) (iff (desc φ χ) (desc ψ χ))) :=
  let F : V α → QF V := fun b => fiff φ fun x => ident x b
  let R : V α → QF V := fun b => desc ψ fun c => ident b c
  have h3 : ∀ b, QThm S (imp (R b) (iff (χ b) (desc ψ χ))) := fun b =>
    qsyl (qiffMp (q14_13 ψ b)) (qimpIffSymm (q14_15 ψ χ b))                     -- ✱14·13·15 (3)
  have h4 : ∀ b, QThm S (imp (QF.and (F b) (R b)) (iff (desc φ χ) (desc ψ χ))) := fun b =>
    qsyl (QThm.mp (qandI (qdescAt φ χ b) (h3 b)) (QL.t3_47 _ _ _ _)) (QL.t4_22 _ _ _)  -- (2).(3) (4)
  QThm.mp (q10_11 h4) (qiffMp (q10_23 _ _))                                     -- (1).(4).✱10·1·23

/-- ✱14·17 `⊢ :. (ιx)(φx) = b . ≡ : ψ!(ιx)(φx) . ≡_ψ . ψ!b`; ψ ranges over the predicative functions,
    and ψ!(ιx)(φx) has the smallest scope. Line (4) is ✱12·1, which gives `x = b . ≡ₓ . χ!x`; (2) and (3)
    are written with that orientation (PM writes χ!x ≡ₓ x = b), so ✱10·1 at b gives b = b ≡ χ!b, read
    from right to left by ✱4·21. (2) picks the factors of its hypothesis by ✱3·26, ✱3·27; the step
    from χ!(ιx)(φx) to (ιx)(φx) = b, which PM leaves tacit, is `qdescScope` (✱10·1, ✱4·36, ✱4·3,
    ✱10·21, ✱10·281); "[✱13·15]" is ✱3·27 with Comm (✱2·04). -/
theorem q14_17 [Reducibility S] (φ : V α → QF V) (b : V α) :
    QThm S (iff (desc φ fun z => ident z b)
      (.all (τ := Ty.pred1 α) fun ψ => iff (desc φ fun z => .app1 ψ z) (.app1 ψ b))) :=
  let A : QF V := desc φ fun z => ident z b
  let P : QF V := .all (τ := Ty.pred1 α) fun ψ => iff (desc φ fun z => .app1 ψ z) (.app1 ψ b)
  have h1 : QThm S (imp A P) := q10_11_21 fun ψ => q14_15 φ (fun z => .app1 ψ z) b  -- ✱14·15 . ✱10·11·21 (1)
  have h2 : ∀ χ : V (Ty.pred1 α),
      QThm S (imp (QF.and (fiff (fun x => ident x b) fun x => .app1 χ x) P) A) := fun χ =>
    have k1 : QThm S (imp (QF.and (fiff (fun x => ident x b) fun x => .app1 χ x) P)
        (iff A (desc φ fun z => .app1 χ z))) :=
      qsyl (QL.t3_26 _ _) (qdescScope φ (fun z => ident z b) fun z => .app1 χ z)
    have k2 : QThm S (imp (QF.and (fiff (fun x => ident x b) fun x => .app1 χ x) P)
        (iff (desc φ fun z => .app1 χ z) (.app1 χ b))) :=
      qsyl (QL.t3_27 _ _) (q10_1 (fun ψ => iff (desc φ fun z => .app1 ψ z) (.app1 ψ b)) χ)  -- ✱10·1
    have k3 : QThm S (imp (QF.and (fiff (fun x => ident x b) fun x => .app1 χ x) P)
        (iff (.app1 χ b) (ident b b))) :=
      qimpIffSymm (qsyl (QL.t3_26 _ _) (q10_1 (fun x => iff (ident x b) (.app1 χ x)) b))  -- ✱10·1
    qsyl (qimpIffTrans (qimpIffTrans k1 k2) k3) (qiffElimOf (q13_15 b))         -- ✱4·22 [✱13·15] (2)
  have h3 : QThm S (imp (ex (τ := Ty.pred1 α) fun χ => fiff (fun x => ident x b) fun x => .app1 χ x)
      (imp P A)) :=
    QThm.mp (q10_11 fun χ => QThm.mp (h2 χ) (QL.t3_3 _ _ _)) (qiffMp (q10_23 _ _))  -- (2).Exp.✱10·11·23 (3)
  qiffI h1 (QThm.mp (q12_1 fun x => ident x b) h3)                              -- ✱12·1 (4) . (3).(4) (5) . (1).(5)

/-- ✱14·171 `⊢ :. (ιx)(φx) = b . ≡ : ψ!b . ⊃_ψ . ψ!(ιx)(φx)`. In (1), the converse halves of ✱14·17's
    ≡_ψ are taken by ✱10·22 and ✱3·27 (`qfiffMpr`). In (2), ✱12·1 gives χ with `x = b . ≡ₓ . χ!x` (the
    orientation of ✱12·1); its hypothesis is picked apart by ✱3·26, ✱3·27; χ!(ιx)(φx) is turned into
    (ιx)(φx) = b by `qdescScope` (✱10·1, ✱4·36, ✱4·3, ✱10·21, ✱10·281); "[✱13·15]" detaches b = b by
    ✱2·27; χ is removed by Exp, ✱10·11 and ✱10·23. -/
theorem q14_171 [Reducibility S] (φ : V α → QF V) (b : V α) :
    QThm S (iff (desc φ fun z => ident z b)
      (.all (τ := Ty.pred1 α) fun ψ => imp (.app1 ψ b) (desc φ fun z => .app1 ψ z))) :=
  let A : QF V := desc φ fun z => ident z b
  let Q : QF V := .all (τ := Ty.pred1 α) fun ψ => imp (.app1 ψ b) (desc φ fun z => .app1 ψ z)
  have h1 : QThm S (imp A Q) :=
    qsyl (qiffMp (q14_17 φ b))
      (qfiffMpr (τ := Ty.pred1 α) (fun ψ => desc φ fun z => .app1 ψ z) fun ψ => .app1 ψ b)  -- ✱14·17 (1)
  have h2 : ∀ χ : V (Ty.pred1 α),
      QThm S (imp (QF.and (fiff (fun x => ident x b) fun x => .app1 χ x) Q) A) := fun χ =>
    have k1 : QThm S (imp (QF.and (fiff (fun x => ident x b) fun x => .app1 χ x) Q)
        (imp (.app1 χ b) (desc φ fun z => .app1 χ z))) :=
      qsyl (QL.t3_27 _ _) (q10_1 (fun ψ => imp (.app1 ψ b) (desc φ fun z => .app1 ψ z)) χ)  -- ✱10·1
    have k2 : QThm S (imp (QF.and (fiff (fun x => ident x b) fun x => .app1 χ x) Q)
        (imp (ident b b) (.app1 χ b))) :=
      qsyl (QL.t3_26 _ _) (qsyl (q10_1 (fun x => iff (ident x b) (.app1 χ x)) b) (QL.t3_26 _ _))
    have k3 : QThm S (imp (QF.and (fiff (fun x => ident x b) fun x => .app1 χ x) Q)
        (imp (desc φ fun z => .app1 χ z) A)) :=
      qsyl (QL.t3_26 _ _) (qsyl (qdescScope φ (fun z => ident z b) fun z => .app1 χ z) (QL.t3_27 _ _))
    qsyl (qimpImpTrans (qimpImpTrans k2 k1) k3) (QThm.mp (q13_15 b) (QL.t2_27 _ _))  -- ✱12·1 [✱13·15] (2)
  have h3 : QThm S (imp (ex (τ := Ty.pred1 α) fun χ => fiff (fun x => ident x b) fun x => .app1 χ x)
      (imp Q A)) :=
    QThm.mp (q10_11 fun χ => QThm.mp (h2 χ) (QL.t3_3 _ _ _)) (qiffMp (q10_23 _ _))
  qiffI h1 (QThm.mp (q12_1 fun x => ident x b) h3)                              -- (1).(2)

/-- ✱14·18 `⊢ :. E!(ιx)(φx) . ⊃ : (x) . ψx . ⊃ . ψ(ιx)(φx)`. "Fact" acts on the second factor ((x) . ψx);
    ✱3·45 acts on the first, so it is ✱3·47 with Id (✱2·08) (`qandR`); ✱10·35 is used with p as the
    second factor (✱4·3 under (∃x) by ✱10·11·281, `qex_and_perm`); the last line's E! : (x) . ψx : ⊃ is
    exported by Exp (✱3·3). -/
theorem q14_18 (φ ψ : V α → QF V) : QThm S (imp (exists1 φ) (imp (.all ψ) (desc φ ψ))) :=
  let F : V α → QF V := fun b => fiff φ fun x => ident x b
  have h1 : ∀ b, QThm S (imp (QF.and (F b) (.all ψ)) (QF.and (F b) (ψ b))) := fun b =>
    qandR (q10_1 ψ b)                                                           -- ✱10·1 [Fact]
  have h2 := qsyl (qiffMpr (qex_and_perm F (.all ψ))) (q10_11_28 h1)            -- [✱10·11·28] [✱10·35]
  QThm.mp h2 (QL.t3_3 _ _ _)                                                    -- [✱14·1·11]

/-! ## ✱14·2–✱14·205 -/

/-- ✱14·2 `⊢ . (ιx)(x = a) = a`, i.e. `[(ιx)(x = a)] . (ιx)(x = a) = a`. ✱13·195 needs the factors
    `b = a . F b`; they are commuted under (∃b) by ✱4·3 and ✱10·11·281. "Id" is ✱4·2 under ✱10·11. -/
theorem q14_2 [Reducibility S] (c : V α) : QThm S (desc (fun x => ident x c) fun z => ident z c) :=
  let F : V α → QF V := fun b => fiff (fun x => ident x c) fun x => ident x b
  have h1 : QThm S (iff (desc (fun x => ident x c) fun z => ident z c) (F c)) :=
    qiffTrans (q14_101 _ _)                                                      -- ✱14·101
      (qiffTrans (q10_11_281 fun b => QL.t4_3 (F b) (ident b c)) (q13_195 F c))  -- [✱13·195] (1)
  QThm.mp (q10_11 fun x => QL.t4_2 (ident x c)) (qiffMpr h1)                    -- (1).Id

/-- ✱14·201 `⊢ : E!(ιx)(φx) . ⊃ . (∃x) . φx`. ✱10·1 and "[✱13·15]" act under (∃b) (✱10·11·28). -/
theorem q14_201 (φ : V α → QF V) : QThm S (imp (exists1 φ) (ex φ)) :=
  qsyl (qiffMp (q14_11 φ))                                                       -- ✱14·11
    (q10_11_28 fun b => qsyl (q10_1 (fun x => iff (φ x) (ident x b)) b)          -- [✱10·1]
      (qiff_refl_elim φ b))                                                      -- [✱13·15]

/-- ✱14·202 `⊢ :. φx . ≡ₓ . x = b : ≡ : (ιx)(φx) = b : ≡ : φx . ≡ₓ . b = x : ≡ : b = (ιx)(φx)`. The chain
    A ≡ B ≡ C ≡ D is stated as `A ≡ B . B ≡ C . C ≡ D`. First half (A ≡ B): ✱14·1 [✱13·195], with the
    factors commuted (✱4·3) under (∃c). "The second half is proved in the same way": D ≡ A is
    `qidentDesc` (✱13·195 with ✱13·16 and ✱4·3, ✱4·36). The links through C need A ≡ C, which PM does not
    print: ✱13·16 under (x) (✱4·86 with ✱4·21, ✱10·11·271). -/
theorem q14_202 [Reducibility S] (φ : V α → QF V) (b : V α) :
    QThm S (QF.and (iff (fiff φ fun x => ident x b) (desc φ fun z => ident z b))
      (QF.and (iff (desc φ fun z => ident z b) (fiff φ fun x => ident b x))
        (iff (fiff φ fun x => ident b x) (desc φ fun z => ident b z)))) :=
  let F : V α → QF V := fun c => fiff φ fun x => ident x c
  have h1 : QThm S (iff (desc φ fun z => ident z b) (F b)) :=
    qiffTrans (q10_11_281 fun c => QL.t4_3 (F c) (ident c b)) (q13_195 F b)     -- ✱14·1 [✱13·195]
  have h2 : QThm S (iff (desc φ fun z => ident b z) (F b)) := qidentDesc φ b
  have h3 : QThm S (iff (F b) (fiff φ fun x => ident b x)) :=
    q10_11_271 fun x => QThm.mp (q13_16 x b) (qiffCongrRImp (φ x) _ _)          -- ✱13·16
  qandI (qiffSymm h1) (qandI (qiffTrans h1 h3) (qiffTrans (qiffSymm h3) (qiffSymm h2)))

/-- The ends of ✱14·202's chain, `φx . ≡ₓ . x = b : ≡ : b = (ιx)(φx)`, its links taken by ✱3·26 and
    ✱3·27 and chained by ✱4·22. -/
theorem qfiffDescEq [Reducibility S] (φ : V α → QF V) (b : V α) :
    QThm S (iff (fiff φ fun x => ident x b) (desc φ fun z => ident b z)) :=
  have c := q14_202 φ b
  qiffTrans (QThm.mp c (QL.t3_26 _ _))
    (qiffTrans (QThm.mp (QThm.mp c (QL.t3_27 _ _)) (QL.t3_26 _ _))
      (QThm.mp (QThm.mp c (QL.t3_27 _ _)) (QL.t3_27 _ _)))

/-- ✱14·203 `⊢ :. E!(ιx)(φx) . ≡ : (∃x) . φx : φx . φy . ⊃_{x,y} . x = y`. Tacit steps: (1) joins ✱14·12
    and ✱14·201 by Comp; in (2), ✱10·1 (at x and at b) is generalized over x by ✱10·11·21 and applied
    to the second factor by ✱3·47 with Id; "[✱5·33]" is ✱5·33 with the factors φx . φb commuted (✱3·22,
    ✱2·06), Exp (✱3·3) and ✱3·27, carried under (x) by ✱10·11·21·27 and joined back by ✱3·31, ✱3·26
    and Comp; "[✱13·191]" acts on the first factor (Fact, ✱3·45); "[✱10·22]" needs the factors in the
    other order (✱3·22). In (3), PM's "✱10·1·28" is ✱10·11·28, and ✱10·35 is used with p second
    (✱4·3 under (∃x) by ✱10·11·281, `qex_and_perm`). -/
theorem q14_203 [Reducibility S] (φ : V α → QF V) :
    QThm S (iff (exists1 φ)
      (QF.and (ex φ) (fimp2 (fun x y => QF.and (φ x) (φ y)) fun x y => ident x y))) :=
  let U : QF V := fimp2 (fun x y => QF.and (φ x) (φ y)) fun x y => ident x y
  let F : V α → QF V := fun b => fiff φ fun x => ident x b
  have h1 := qcomp (q14_201 φ) (q14_12 φ)                                        -- ✱14·12·201 (1)
  have h2 : ∀ b, QThm S (imp (QF.and (φ b) U) (F b)) := fun b =>
    have u : QThm S (imp U (.all fun x => imp (QF.and (φ x) (φ b)) (ident x b))) :=
      q10_11_21 fun x => qsyl (q10_1 _ x) (q10_1 _ b)                            -- ✱10·1
    have e : ∀ x, QThm S (imp (φ b) (imp (imp (QF.and (φ x) (φ b)) (ident x b))
        (imp (φ x) (ident x b)))) := fun x =>
      have s1 := QThm.mp (QL.t3_22 (φ b) (φ x)) (QL.t2_06 _ _ (ident x b))
      QThm.mp (qsyl (qsyl (qandR s1) (qiffMpr (QL.t5_33 (φ b) (φ x) (ident x b)))) (QL.t3_27 _ _))
        (QL.t3_3 _ _ _)                                                         -- [✱5·33]
    have e2 : QThm S (imp (φ b) (imp (.all fun x => imp (QF.and (φ x) (φ b)) (ident x b))
        (fimp φ fun x => ident x b))) :=
      qsyl (q10_11_21 e) (q10_27 _ _)
    have m1 : QThm S (imp (QF.and (φ b) (.all fun x => imp (QF.and (φ x) (φ b)) (ident x b)))
        (QF.and (fimp (fun x => ident x b) φ) (fimp φ fun x => ident x b))) :=
      qsyl (qcomp (QL.t3_26 _ _) (QThm.mp e2 (QL.t3_31 _ _ _)))
        (QThm.mp (qiffMpr (q13_191 φ b)) (QL.t3_45 _ _ _))                      -- [✱13·191]
    qsyl (qandR u) (qsyl m1 (qsyl (QL.t3_22 _ _)
      (qiffMpr (q10_22 (fun x => imp (φ x) (ident x b)) fun x => imp (ident x b) (φ x)))))  -- [✱10·22] (2)
  have h3 := qsyl (qiffMpr (qex_and_perm φ U)) (q10_11_28 h2)                   -- (2).✱10·1·28 [✱10·35] [✱14·11] (3)
  qiffI h1 h3                                                                    -- (1).(3)

/-- ✱14·204 `⊢ :. E!(ιx)(φx) . ≡ : (∃b) . (ιx)(φx) = b`. The first link of ✱14·202 is taken by ✱3·26. -/
theorem q14_204 [Reducibility S] (φ : V α → QF V) :
    QThm S (iff (exists1 φ) (ex fun b => desc φ fun z => ident z b)) :=
  q10_11_281 fun b => QThm.mp (q14_202 φ b) (QL.t3_26 _ _)                      -- ✱14·202 . ✱10·11 [✱10·281] (1) . ✱14·11

/-- ✱14·205 `⊢ : ψ(ιx)(φx) . ≡ . (∃b) . b = (ιx)(φx) . ψb` [✱14·202·1]. ✱14·202 is used end to end
    (`qfiffDescEq`) on the first factor (✱4·36), under (∃b) by ✱10·11·281. -/
theorem q14_205 [Reducibility S] (φ ψ : V α → QF V) :
    QThm S (iff (desc φ ψ) (ex fun b => QF.and (desc φ fun z => ident b z) (ψ b))) :=
  q10_11_281 fun b => qandCongrL (ψ b) (qfiffDescEq φ b)                        -- ✱14·1 [✱14·202]

/-! ## ✱14·21–✱14·28 -/

/-- ✱14·21 `⊢ : ψ(ιx)(φx) . ⊃ . E!(ιx)(φx)`, the description in ψ having the scope ψ. ✱10·5 gives the
    product of the two existentials; its first factor is taken by ✱3·26 (tacit). -/
theorem q14_21 (φ ψ : V α → QF V) : QThm S (imp (desc φ ψ) (exists1 φ)) :=
  qsyl (qiffMp (q14_1 φ ψ))                                                      -- ✱14·1
    (qsyl (q10_5 _ ψ) (QL.t3_26 _ _))                                            -- [✱10·5] [✱14·11]

/-- ✱14·21 for `∼χ(ιx)(φx)` with the description's scope wider than the negation (a primary
    occurrence), i.e. [(ιx)(φx)] . ∼χ(ιx)(φx): it also implies E!(ιx)(φx). When the negation has the wider
    scope (the description the narrower, a secondary occurrence), ∼{[(ιx)(φx)] . χ(ιx)(φx)} does not (PM p. 190:
    when the description does not exist there are true propositions in which it has a secondary
    occurrence); see `not_qthm_neg_desc_imp_exists1`. -/
theorem q14_21_neg (φ χ : V α → QF V) : QThm S (imp (desc φ fun z => .neg (χ z)) (exists1 φ)) :=
  q14_21 φ fun z => .neg (χ z)

/-- ✱14·22 `⊢ : E!(ιx)(φx) . ≡ . φ(ιx)(φx)`. In (1), the first link of ✱14·122 is taken by ✱3·26 and its
    second factor φb by ✱3·27. -/
theorem q14_22 [Reducibility S] (φ : V α → QF V) : QThm S (iff (exists1 φ) (desc φ φ)) :=
  q10_11_281 fun b =>
    have h1 := qsyl (qiffMp (QThm.mp (q14_122 φ b) (QL.t3_26 _ _))) (QL.t3_27 _ _)  -- ✱14·122 (1)
    QThm.mp h1 (qiffMp (QL.t4_71 _ _))                                           -- (1).✱4·71 [✱10·11·281] [✱14·11·101]

/-- ✱14·23 `⊢ : E!(ιx)(φx . ψx) . ≡ . φ{(ιx)(φx . ψx)}`. PM notes (p. 191) that "✱10·5, not only ✱3·26, is
    required", since the scope is the whole product φ{…} . ψ{…}. The step from
    `(∃b) : φx . ψx . ≡ₓ . x = b : φb . ψb` to `(∃b) : … : φb` is ✱3·26 on the second factor (✱3·47 with Id)
    carried under (∃b) by ✱10·11·28; ✱10·5 (distributing (∃b) over a product) does not give it. -/
theorem q14_23 [Reducibility S] (φ ψ : V α → QF V) :
    QThm S (iff (exists1 fun x => QF.and (φ x) (ψ x)) (desc (fun x => QF.and (φ x) (ψ x)) φ)) :=
  have h1 := qsyl (qiffMp (q14_22 fun x => QF.and (φ x) (ψ x)))
    (q10_11_28 fun b => qandR (QL.t3_26 (φ b) (ψ b)))                            -- ✱14·22 [✱10·5 . ✱3·26] (1)
  qiffI h1 (q14_21 _ φ)                                                          -- ✱14·21 (2) . (1).(2)

/-- ✱14·24 `⊢ :. E!(ιx)(φx) . ≡ : [(ιx)(φx)] : φy . ≡_y . y = (ιx)(φx)`: the description's scope is the
    whole formal equivalence. -/
theorem q14_24 (φ : V α → QF V) :
    QThm S (iff (exists1 φ) (desc φ fun b => fiff φ fun y => ident y b)) :=
  q10_11_281 fun _ => QL.t4_24 _                                                 -- ✱14·1 [✱4·24 . ✱10·281] [✱14·11]

/-- ✱14·241 `⊢ :. E!(ιx)(φx) . ⊃ : φy . ≡_y . y = (ιx)(φx)`, the description having the smallest scope
    y = (ιx)(φx). Tacit steps: ✱14·203's second factor is taken by ✱3·27 and instantiated at y and x by
    ✱10·1 (twice); "[✱13·191]" needs `y = x . ⊃ₓ . φx` where ✱13·191 gives `x = y . ⊃ₓ . φx`, turned by
    ✱13·16 (with ✱4·84, ✱10·11·271), and acts on the first factor (✱4·36); "[✱10·22]" needs the factors
    in the other order (✱4·3); "[✱14·202]" is its third link (✱3·27 twice); PM's last line is under
    Hp for one y, generalized by ✱10·11·21. -/
theorem q14_241 [Reducibility S] (φ : V α → QF V) :
    QThm S (imp (exists1 φ) (fiff φ fun y => desc φ fun z => ident y z)) :=
  let U : QF V := fimp2 (fun x y => QF.and (φ x) (φ y)) fun x y => ident x y
  have hU : QThm S (imp (exists1 φ) U) := qsyl (qiffMp (q14_203 φ)) (QL.t3_27 _ _)  -- ✱14·203
  q10_11_21 fun y =>
    have a1 : QThm S (imp (exists1 φ) (imp (φ y) (fimp φ fun x => ident y x))) :=
      qsyl hU (qsyl (q10_11_21 fun x => qsyl (qsyl (q10_1 _ y) (q10_1 _ x)) (QL.t3_3 _ _ _))  -- [Exp] [✱10·11·21]
        (qiffMp (q10_21 (φ y) fun x => imp (φ x) (ident y x))))
    have a2 := qsyl a1 (qiffMp (QL.t4_71 _ _))                                   -- [✱4·71]
    have r : QThm S (iff (fimp (fun x => ident y x) φ) (φ y)) :=
      qiffTrans (q10_11_271 fun x => QThm.mp (q13_16 y x) (QL.t4_84 _ _ (φ x))) (q13_191 φ y)
    have a3 := qimpIffTransR a2 (qandCongrL _ (qiffSymm r))                      -- [✱13·191]
    have a4 := qimpIffTransR a3 (qiffTrans (QL.t4_3 _ _)
      (qiffSymm (q10_22 (fun x => imp (φ x) (ident y x)) fun x => imp (ident y x) (φ x))))  -- [✱10·22]
    qimpIffTransR a4 (QThm.mp (QThm.mp (q14_202 φ y) (QL.t3_27 _ _)) (QL.t3_27 _ _))  -- [✱14·202]

/-- ✱14·242 `⊢ :. φx . ≡ₓ . x = b : ⊃ : ψb . ≡ . ψ(ιx)(φx)` [✱14·202·15]. The first link of ✱14·202 is
    taken by ✱3·26. -/
theorem q14_242 [Reducibility S] (φ ψ : V α → QF V) (b : V α) :
    QThm S (imp (fiff φ fun x => ident x b) (iff (ψ b) (desc φ ψ))) :=
  qsyl (qiffMp (QThm.mp (q14_202 φ b) (QL.t3_26 _ _))) (qimpIffSymm (q14_15 φ ψ b))  -- [✱14·202·15]

/-- ✱14·25 `⊢ :. E!(ιx)(φx) . ⊃ : φx ⊃ₓ ψx . ≡ . ψ(ιx)(φx)` -/
theorem q14_25 [Reducibility S] (φ ψ : V α → QF V) :
    QThm S (imp (exists1 φ) (iff (fimp φ ψ) (desc φ ψ))) :=
  have h1 : ∀ b, QThm S (imp (fiff φ fun x => ident x b) (iff (fimp φ ψ) (desc φ ψ))) := fun b =>
    qimpIffTrans
      (qimpIffTransR (qsyl (q10_11_27 fun x => QL.t4_84 (φ x) (ident x b) (ψ x))
          (q10_271 _ _)) (q13_191 ψ b))                                         -- ✱4·84 . ✱10·27·271 [✱13·191]
      (q14_242 φ ψ b)                                                           -- [✱14·242] (1)
  QThm.mp (q10_11 h1) (qiffMp (q10_23 _ _))                                     -- (1).✱10·11·23 (2) . (2).✱14·11

/-- ✱14·26 `⊢ :. E!(ιx)(φx) . ⊃ : (∃x) . φx . ψx . ≡ . ψ{(ιx)(φx)} . ≡ . φx ⊃ₓ ψx`. The chain is stated as
    `A ≡ B . B ≡ C`; the last line joins (3) with ✱14·25 (read from right to left) by Comp. -/
theorem q14_26 [Reducibility S] (φ ψ : V α → QF V) :
    QThm S (imp (exists1 φ) (QF.and (iff (ex fun x => QF.and (φ x) (ψ x)) (desc φ ψ))
      (iff (desc φ ψ) (fimp φ ψ)))) :=
  have h2 : ∀ b, QThm S (imp (fiff φ fun x => ident x b)
      (iff (ex fun x => QF.and (φ x) (ψ x)) (desc φ ψ))) := fun b =>
    qimpIffTrans
      (qimpIffTransR (qsyl (q10_311 φ (fun x => ident x b) ψ) (q10_281 _ _)) (q13_195 ψ b))  -- ✱10·311 [✱10·281] [✱13·195]
      (q14_242 φ ψ b)                                                           -- [✱14·242] (2)
  have h3 := QThm.mp (q10_11 h2) (qiffMp (q10_23 _ _))                          -- (2).✱10·11·23 (3)
  qcomp h3 (qimpIffSymm (q14_25 φ ψ))                                           -- (1).(3).✱14·25

/-- ✱14·27 `⊢ :. E!(ιx)(φx) . ⊃ : φx ≡ₓ ψx . ≡ . (ιx)(φx) = (ιx)(ψx)`. "[✱14·202]" is used end to end
    (`qfiffDescEq`: its links taken by ✱3·26, ✱3·27). -/
theorem q14_27 [Reducibility S] (φ ψ : V α → QF V) :
    QThm S (imp (exists1 φ) (iff (fiff φ ψ) (desc2 φ ψ fun b c => ident b c))) :=
  have h2 : ∀ b, QThm S (imp (fiff φ fun x => ident x b)
      (iff (fiff φ ψ) (desc2 φ ψ fun b c => ident b c))) := fun b =>
    have l1 : ∀ x, QThm S (imp (iff (φ x) (ident x b))
        (iff (iff (φ x) (ψ x)) (iff (ψ x) (ident x b)))) := fun x =>
      qimpIffTransR (QL.t4_86 (φ x) (ident x b) (ψ x)) (QL.t4_21 _ _)           -- ✱4·86·21 (1)
    qimpIffTrans
      (qimpIffTransR (qsyl (q10_11_27 l1) (q10_271 _ _)) (qfiffDescEq ψ b))     -- (1).✱10·11·27 [✱10·271] [✱14·202]
      (q14_242 φ (fun c => desc ψ fun d => ident c d) b)                        -- [✱14·242] (2)
  QThm.mp (q10_11 h2) (qiffMp (q10_23 _ _))                                     -- (2).✱10·11·23.✱14·11

/-- ✱14·271 `⊢ :. φx ≡ₓ ψx . ⊃ : E!(ιx)(φx) . ≡ . E!(ιx)(ψx)` -/
theorem q14_271 (φ ψ : V α → QF V) : QThm S (imp (fiff φ ψ) (iff (exists1 φ) (exists1 ψ))) :=
  qsyl (q10_11_21 fun b => qsyl (q10_11_27 fun x => QL.t4_86 (φ x) (ψ x) (ident x b))  -- ✱4·86 [✱10·11·27]
      (q10_271 (fun x => iff (φ x) (ident x b)) fun x => iff (ψ x) (ident x b)))  -- [✱10·271] [✱10·11·21]
    (q10_281 _ _)                                                               -- [✱10·281]

/-- ✱14·272 `⊢ :. φx ≡ₓ ψx . ⊃ : χ(ιx)(φx) . ≡ . χ(ιx)(ψx)`: `qdescCongr`. PM's second line cites
    "✱10·11·414"; the step it takes, from (x) : φx ≡ x = b . ≡ . ψx ≡ x = b to φx ≡ₓ x = b . ≡ . ψx ≡ₓ x = b,
    is ✱10·271 (as in ✱14·271's Dem.), not ✱10·414 (which gives a formal equivalence ≡ₓ, not an
    equivalence of the two (x)'s). "Fact" for the ≡ of products is ✱4·36. -/
theorem q14_272 (φ ψ χ : V α → QF V) : QThm S (imp (fiff φ ψ) (iff (desc φ χ) (desc ψ χ))) :=
  qdescCongr φ ψ χ

/-- ✱14·28 `⊢ : E!(ιx)(φx) . ≡ . (ιx)(φx) = (ιx)(φx)`. PM's Dem. eliminates the description once, with
    scope ẑ = ẑ (`(∃b) : φx . ≡ₓ . x = b : b = b`), and so does the statement here; reading the two
    occurrences as two descriptions by ✱14·03 would give a different formula, not proved here. -/
theorem q14_28 (φ : V α → QF V) : QThm S (iff (exists1 φ) (desc φ fun b => ident b b)) :=
  q10_11_281 fun b => QThm.mp (q13_15 b) (QL.t4_73 _ _)                          -- ✱13·15 . ✱4·73 (1) . ✱10·11·281 (2) . ✱14·1·11

/-! ## ✱14·31–✱14·34 (✱14·3 is not formalized; see the header) -/

/-- ✱14·31 `⊢ :: E!(ιx)(φx) . ⊃ :. [(ιx)(φx)] . p ∨ χ(ιx)(φx) . ≡ : p . ∨ . [(ιx)(φx)] . χ(ιx)(φx)`. ✱4·37 has
    the varied disjunct first; here it is second (✱4·31). ✱10·23 needs (b) first (✱10·11). -/
theorem q14_31 [Reducibility S] (φ χ : V α → QF V) (p : QF V) :
    QThm S (imp (exists1 φ) (iff (desc φ fun z => .or p (χ z)) (.or p (desc φ χ)))) :=
  have h3 : ∀ b, QThm S (imp (fiff φ fun x => ident x b)
      (iff (desc φ fun z => .or p (χ z)) (.or p (desc φ χ)))) := fun b =>
    qimpIffTrans (qimpIffSymm (q14_242 φ (fun z => .or p (χ z)) b))             -- ✱14·242 (1)
      (qsyl (q14_242 φ χ b) (qorCongrRImp p _ _))                               -- ✱14·242 [✱4·37] (2) . (1).(2) (3)
  QThm.mp (q10_11 h3) (qiffMp (q10_23 _ _))                                     -- (3).✱10·23.✱14·11

/-- ✱14·32 `⊢ :. E!(ιx)(φx) . ≡ : [(ιx)(φx)] . ∼χ(ιx)(φx) . ≡ . ∼{[(ιx)(φx)] . χ(ιx)(φx)}`
    [✱14·242 . ✱4·11 . ✱10·23 . ✱14·11]. The hint proves the implication from E!(ιx)(φx) (✱10·23 needs
    (b) first, ✱10·11). The converse is not in the hint; as pp. 194–195 explain, when (ιx)(φx) does not
    exist both [(ιx)(φx)] . ∼χ(ιx)(φx) and [(ιx)(φx)] . χ(ιx)(φx) are false (✱14·21), so they are not
    each other's negation: from the right-hand side, ∼{…} ⊃ [(ιx)(φx)] . ∼χ(ιx)(φx) (✱3·27) gives the
    disjunction of the two (✱2·54), and either implies E!(ιx)(φx) by ✱14·21 (joined by ✱3·44). -/
theorem q14_32 [Reducibility S] (φ χ : V α → QF V) :
    QThm S (iff (exists1 φ) (iff (desc φ fun z => .neg (χ z)) (.neg (desc φ χ)))) :=
  have h : ∀ b, QThm S (imp (fiff φ fun x => ident x b)
      (iff (desc φ fun z => .neg (χ z)) (.neg (desc φ χ)))) := fun b =>
    qimpIffTrans (qimpIffSymm (q14_242 φ (fun z => .neg (χ z)) b))              -- ✱14·242
      (qsyl (q14_242 φ χ b) (qiffMp (QL.t4_11 _ _)))                             -- ✱14·242 . ✱4·11
  have h1 := QThm.mp (q10_11 h) (qiffMp (q10_23 _ _))                            -- ✱10·23 . ✱14·11 (1)
  have h2 := QThm.mp (qandI (q14_21 φ χ) (q14_21_neg φ χ)) (QL.t3_44 _ _ _)     -- ✱14·21 . ✱3·44 (2)
  qiffI h1 (qsyl (QL.t3_27 _ _) (qsyl (QL.t2_54 _ _) h2))                        -- ✱3·27 . ✱2·54 . (2) . (1)

/-- ✱14·33 `⊢ :: E!(ιx)(φx) . ⊃ :. [(ιx)(φx)] . p ⊃ χ(ιx)(φx) . ≡ : p . ⊃ . [(ιx)(φx)] . χ(ιx)(φx)`
    [✱14·242 . ✱4·85 . ✱10·23 . ✱14·11]. ✱10·23 needs (b) first (✱10·11). -/
theorem q14_33 [Reducibility S] (φ χ : V α → QF V) (p : QF V) :
    QThm S (imp (exists1 φ) (iff (desc φ fun z => imp p (χ z)) (imp p (desc φ χ)))) :=
  have h : ∀ b, QThm S (imp (fiff φ fun x => ident x b)
      (iff (desc φ fun z => imp p (χ z)) (imp p (desc φ χ)))) := fun b =>
    qimpIffTrans (qimpIffSymm (q14_242 φ (fun z => imp p (χ z)) b))             -- ✱14·242
      (qsyl (q14_242 φ χ b) (QL.t4_85 _ _ p))                                    -- ✱14·242 . ✱4·85
  QThm.mp (q10_11 h) (qiffMp (q10_23 _ _))                                       -- ✱10·23 . ✱14·11

/-- ✱14·331 `⊢ :: E!(ιx)(φx) . ⊃ :. [(ιx)(φx)] . χ(ιx)(φx) ⊃ p . ≡ : [(ιx)(φx)] . χ(ιx)(φx) . ⊃ . p`
    [✱4·84 . ✱14·242 . ✱10·23 . ✱14·11]. ✱10·23 needs (b) first (✱10·11). -/
theorem q14_331 [Reducibility S] (φ χ : V α → QF V) (p : QF V) :
    QThm S (imp (exists1 φ) (iff (desc φ fun z => imp (χ z) p) (imp (desc φ χ) p))) :=
  have h : ∀ b, QThm S (imp (fiff φ fun x => ident x b)
      (iff (desc φ fun z => imp (χ z) p) (imp (desc φ χ) p))) := fun b =>
    qimpIffTrans (qimpIffSymm (q14_242 φ (fun z => imp (χ z) p) b))             -- ✱14·242
      (qsyl (q14_242 φ χ b) (QL.t4_84 _ _ p))                                    -- ✱4·84
  QThm.mp (q10_11 h) (qiffMp (q10_23 _ _))                                       -- ✱10·23 . ✱14·11

/-- ✱14·332 `⊢ :: E!(ιx)(φx) . ⊃ :. [(ιx)(φx)] . p ≡ χ(ιx)(φx) . ≡ : p . ≡ . [(ιx)(φx)] . χ(ιx)(φx)`
    [✱4·86 . ✱14·242 . ✱10·23 . ✱14·11]. ✱4·86 has the varied member first; here it is second (✱4·21,
    `qiffCongrRImp`). ✱10·23 needs (b) first (✱10·11). -/
theorem q14_332 [Reducibility S] (φ χ : V α → QF V) (p : QF V) :
    QThm S (imp (exists1 φ) (iff (desc φ fun z => iff p (χ z)) (iff p (desc φ χ)))) :=
  have h : ∀ b, QThm S (imp (fiff φ fun x => ident x b)
      (iff (desc φ fun z => iff p (χ z)) (iff p (desc φ χ)))) := fun b =>
    qimpIffTrans (qimpIffSymm (q14_242 φ (fun z => iff p (χ z)) b))             -- ✱14·242
      (qsyl (q14_242 φ χ b) (qiffCongrRImp p _ _))                               -- ✱4·86
  QThm.mp (q10_11 h) (qiffMp (q10_23 _ _))                                       -- ✱10·23 . ✱14·11

/-- ✱14·34 `⊢ :. p : [(ιx)(φx)] . χ(ιx)(φx) : ≡ : [(ιx)(φx)] : p . χ(ιx)(φx)`, without E!(ιx)(φx). PM's
    middle line `(∃b) : p : φx ≡ₓ x = b : χb` is rearranged to the scope p . χb of the last line by
    ✱4·32, ✱4·3 (with ✱4·36), under (∃b) by ✱10·11·281. -/
theorem q14_34 (φ χ : V α → QF V) (p : QF V) :
    QThm S (iff (QF.and p (desc φ χ)) (desc φ fun z => QF.and p (χ z))) :=
  qiffTrans (qiffSymm (q10_35 (fun b => QF.and (fiff φ fun x => ident x b) (χ b)) p))  -- ✱14·1 [✱10·35]
    (q10_11_281 fun _ => qandPerm p _ _)                                         -- [✱14·1]

/-! ## A counter-model for the negation with the wider scope -/

/-- In every structure, x = x is true (✱13·01 evaluated). -/
theorem eval_ident_refl (M : QModel) {a : Ty} (x : M.den a) : (ident x x).eval M = true :=
  (M.hA _ _).mpr fun f => by
    show (!(M.ap1 f x) || M.ap1 f x) = true
    cases M.ap1 f x <;> rfl

/-- `φ0 x` is `qx . ∼qx`, false of every individual. -/
def φ0 {V : Ty → Type} (x : V .ind) : QF V := QF.and (.atom "q" [x]) (.neg (.atom "q" [x]))

/-- Scope matters (PM pp. 181–182, 190): when the negation has the wider scope (the description the
    narrower), ∼{[(ιx)(φx)] . χ(ιx)(φx)} does not imply E!(ιx)(φx), whereas [(ιx)(φx)] . ∼χ(ιx)(φx), with
    the description's scope wider than the negation, does (`q14_21_neg`). In `twoModel` nothing
    satisfies φ0, so (ιx)(φ0 x) does not exist: [(ιx)(φ0 x)] . φ0(ιx)(φ0 x) is false and its negation true.
    `twoModel` is the finite coded model (PM/Models/Finite.lean), so the formula is evaluated by
    computation, including the quantifier over the four predicative functions in ✱13·01. -/
theorem not_qthm_neg_desc_imp_exists1 :
    ¬ ∀ (V : Ty → Type) (φ χ : V .ind → QF V), QThm S (imp (.neg (desc φ χ)) (exists1 φ)) :=
  fun h => not_qthm_of_countermodel twoModel (p := imp (.neg (desc φ0 φ0)) (exists1 φ0)) rfl (h _ φ0 φ0)

end PM
