import PM.QuantLift
/-!
  ✱9's primitive propositions and ✱10's propositions, proved in ✱10's alternative method (PM/Quant.lean).

  Statements are read from the 1910 print (pp. 136–156). Each proof follows PM's alternative-method
  proof line by line where PM gives one; `PM.QL.tX` is ✱X lifted to formulas with apparent variables
  (PM/QuantLift.lean). As in PM/Replay2.lean, the only silent steps are the ones PM leaves tacit:
  joining two lines by ✱3·2 (or ✱4·01 for "≡"), and reading a definition (✱1·01, ✱3·01, ✱4·01,
  ✱10·01–✱10·03), which in Lean is definitional.

  Names: `q10_1` is ✱10·1, `q9_1` is ✱9·1, and so on. φ, ψ, χ are functions `V τ → QF V`; p, q are formulas;
  x, y are real variables (elements of `V τ`). Every theorem holds at every type τ.
-/
namespace PM
open QF

variable {V : Ty → Type} {S : Sys V} {τ : Ty}

/-! ## Rules used tacitly by PM (as in PM/Derived.lean, now for ✱10 formulas) -/

/-- Syll (✱2·05) as a rule. -/
theorem qsyl {a b c : QF V} (h1 : QThm S (imp a b)) (h2 : QThm S (imp b c)) : QThm S (imp a c) :=
  QThm.mp h1 (QThm.mp h2 (QL.t2_05 a b c))
/-- ✱3·2 as a rule. -/
theorem qandI {a b : QF V} (ha : QThm S a) (hb : QThm S b) : QThm S (QF.and a b) :=
  QThm.mp hb (QThm.mp ha (QL.t3_2 a b))
/-- ✱4·01 + ✱3·2 as a rule. -/
theorem qiffI {a b : QF V} (h1 : QThm S (imp a b)) (h2 : QThm S (imp b a)) : QThm S (iff a b) := qandI h1 h2
/-- ✱4·01 + ✱3·26 as a rule. -/
theorem qiffMp {a b : QF V} (h : QThm S (iff a b)) : QThm S (imp a b) := QThm.mp h (QL.t3_26 _ _)
/-- ✱4·01 + ✱3·27 as a rule. -/
theorem qiffMpr {a b : QF V} (h : QThm S (iff a b)) : QThm S (imp b a) := QThm.mp h (QL.t3_27 _ _)
/-- An equivalence read right to left. -/
theorem qiffSymm {a b : QF V} (h : QThm S (iff a b)) : QThm S (iff b a) := qiffI (qiffMpr h) (qiffMp h)
/-- A chain `a ≡ b ≡ c`, its halves joined by Syll. -/
theorem qiffTrans {a b c : QF V} (h1 : QThm S (iff a b)) (h2 : QThm S (iff b c)) : QThm S (iff a c) :=
  qiffI (qsyl (qiffMp h1) (qiffMp h2)) (qsyl (qiffMpr h2) (qiffMpr h1))

/-! ## The primitive propositions of the alternative method -/

/-- ✱10·1 `⊢ : (x) . φx . ⊃ . φy` (Pp in the alternative method; ✱9·2). -/
theorem q10_1 (φ : V τ → QF V) (y : V τ) : QThm S (imp (.all φ) (φ y)) := QThm.inst φ y
/-- ✱10·11 "If φy is true whatever possible argument y may be, then (x) . φx is true." (Pp; ✱9·13) -/
theorem q10_11 {φ : V τ → QF V} (h : ∀ y, QThm S (φ y)) : QThm S (.all φ) := QThm.gen h
/-- ✱10·12 `⊢ :. (x) . p ∨ φx . ⊃ : p . ∨ . (x) . φx` (Pp in the alternative method; ✱9·25). -/
theorem q10_12 (p : QF V) (φ : V τ → QF V) :
    QThm S (imp (.all fun x => .or p (φ x)) (.or p (.all φ))) := QThm.distrib p φ

/-- ✱10·13 "If φx̂ and ψx̂ take arguments of the same type, and we have `⊢ . φx` and `⊢ . ψx`, we shall
    have `⊢ . φx . ψx`." PM proves it from ✱2·11, ✱2·32 and ✱9·12. -/
theorem q10_13 {a b : QF V} (ha : QThm S a) (hb : QThm S b) : QThm S (QF.and a b) :=
  have h1 : QThm S (.or (.or (.neg a) (.neg b)) (QF.and a b)) := QL.t2_11 (.or (.neg a) (.neg b))   -- (1)
  have h2 : QThm S (imp a (imp b (QF.and a b))) :=
    QThm.mp h1 (QL.t2_32 (.neg a) (.neg b) (QF.and a b))                                          -- (2)
  QThm.mp hb (QThm.mp ha h2)                                                                       -- ✱9·12

/-- ✱10·14 `⊢ :. (x) . φx : (x) . ψx : ⊃ . φy . ψy` -/
theorem q10_14 (φ ψ : V τ → QF V) (y : V τ) :
    QThm S (imp (QF.and (.all φ) (.all ψ)) (QF.and (φ y) (ψ y))) :=
  have h1 := q10_1 φ y                                                         -- (1)
  have h2 := q10_1 ψ y                                                         -- (2)
  QThm.mp (q10_13 h1 h2) (QL.t3_47 (.all φ) (.all ψ) (φ y) (ψ y))              -- (1).(2).✱10·13, [✱3·47]

/-- ✱10·2 `⊢ :. (x) . p ∨ φx . ≡ : p . ∨ . (x) . φx` -/
theorem q10_2 (p : QF V) (φ : V τ → QF V) :
    QThm S (iff (.all fun x => .or p (φ x)) (.or p (.all φ))) :=
  have l1 : ∀ y, QThm S (imp (.or p (.all φ)) (.or p (φ y))) :=
    fun y => QThm.mp (q10_1 φ y) (QThm.sum p (.all φ) (φ y))                   -- ✱10·1.✱1·6
  have l2 := q10_11 l1                                                          -- [✱10·11]
  have h1 : QThm S (imp (.or p (.all φ)) (.all fun y => .or p (φ y))) :=
    QThm.mp l2 (q10_12 (.neg (.or p (.all φ))) (fun y => .or p (φ y)))         -- [✱10·12] (1)
  have h2 := q10_12 p φ                                                         -- (2)
  qiffI h2 h1

/-- ✱10·21 `⊢ :. (x) . p ⊃ φx . ≡ : p . ⊃ . (x) . φx` [✱10·2 ∼p/p] -/
theorem q10_21 (p : QF V) (φ : V τ → QF V) :
    QThm S (iff (.all fun x => imp p (φ x)) (imp p (.all φ))) := q10_2 (.neg p) φ

/-- "✱10·11·21": from `⊢ . p ⊃ φy` for every y, infer `⊢ : p . ⊃ . (x) . φx` (PM p. 148: "the two
    steps which it requires will not be separately put down"). -/
theorem q10_11_21 {p : QF V} {φ : V τ → QF V} (h : ∀ y, QThm S (imp p (φ y))) : QThm S (imp p (.all φ)) :=
  QThm.mp (q10_11 h) (qiffMp (q10_21 p φ))

/-- ✱10·22 `⊢ :. (x) . φx . ψx . ≡ : (x) . φx : (x) . ψx` -/
theorem q10_22 (φ ψ : V τ → QF V) :
    QThm S (iff (.all fun x => QF.and (φ x) (ψ x)) (QF.and (.all φ) (.all ψ))) :=
  let A : QF V := .all fun x => QF.and (φ x) (ψ x)
  have l1 : ∀ y, QThm S (imp A (QF.and (φ y) (ψ y))) := fun y => q10_1 _ y      -- ✱10·1 (1)
  have h2 : QThm S (imp A (.all φ)) :=
    q10_11_21 fun y => qsyl (l1 y) (QL.t3_26 (φ y) (ψ y))                       -- [✱3·26] [✱10·11] [✱10·21] (2)
  have h3 : QThm S (imp A (.all ψ)) :=
    q10_11_21 fun z => qsyl (l1 z) (QL.t3_27 (φ z) (ψ z))                       -- (1).✱3·27 [✱10·11] [✱10·21] (3)
  have h4 : QThm S (imp A (QF.and (.all φ) (.all ψ))) :=
    QThm.mp (qandI h2 h3) (QL.t3_43 A (.all φ) (.all ψ))                         -- (2).(3).Comp (4)
  have h5 : QThm S (imp (QF.and (.all φ) (.all ψ)) A) :=
    q10_11_21 fun y => q10_14 φ ψ y                                              -- ✱10·14·11 [✱10·21] (5)
  qiffI h4 h5

/-- ✱10·23 `⊢ :. (x) . φx ⊃ p . ≡ : (∃x) . φx . ⊃ . p` (PM's second proof, for the alternative method) -/
theorem q10_23 (φ : V τ → QF V) (p : QF V) :
    QThm S (iff (.all fun x => imp (φ x) p) (imp (ex φ) p)) :=
  have e0 : QThm S (iff (imp (ex φ) p) (imp (.neg p) (.all fun x => .neg (φ x)))) :=
    qiffI (QL.t2_15 (.all fun x => .neg (φ x)) p) (QL.t2_15 p (.all fun x => .neg (φ x)))  -- Transp.(✱10·01)
  have h1 : QThm S (iff (imp (ex φ) p) (.all fun x => imp (.neg p) (.neg (φ x)))) :=
    qiffTrans e0 (qiffSymm (q10_21 (.neg p) fun x => .neg (φ x)))              -- [✱10·21] (1)
  have h2 : QThm S (imp (imp (ex φ) p) (.all fun x => imp (φ x) p)) :=
    q10_11_21 fun x =>
      qsyl (qsyl (qiffMp h1) (q10_1 (fun x => imp (.neg p) (.neg (φ x))) x))  -- [✱10·1]
        (QL.t2_17 (φ x) p)                                                      -- [Transp] [✱10·11] [✱10·21] (2)
  have h3 : QThm S (imp (.all fun x => imp (φ x) p) (imp (ex φ) p)) :=
    qsyl (q10_11_21 fun x =>
        qsyl (q10_1 (fun x => imp (φ x) p) x) (QL.t2_16 (φ x) p))              -- ✱10·1 [Transp] [✱10·11·21]
      (qiffMpr h1)                                                              -- [(1)] (3)
  qiffI h3 h2

/-- ✱10·24 `⊢ : φy . ⊃ . (∃x) . φx` (this is ✱9·1; PM's proof in the alternative method) -/
theorem q10_24 (φ : V τ → QF V) (y : V τ) : QThm S (imp (φ y) (ex φ)) :=
  QThm.mp (q10_1 (fun x => .neg (φ x)) y)                                       -- ✱10·1
    (QL.t2_03 (.all fun x => .neg (φ x)) (φ y))                                 -- [Transp] [(✱10·01)]

/-- ✱10·25 `⊢ : (x) . φx . ⊃ . (∃x) . φx` [✱10·1·24]. PM's proof uses a real variable `y`, so the
    Lean statement takes one: in an empty domain the proposition is false. -/
theorem q10_25 (φ : V τ → QF V) (y : V τ) : QThm S (imp (.all φ) (ex φ)) :=
  qsyl (q10_1 φ y) (q10_24 φ y)

/-- ✱10·251 `⊢ : (x) . ∼φx . ⊃ . ∼{(x) . φx}` [✱10·25 . Transp] -/
theorem q10_251 (φ : V τ → QF V) (y : V τ) :
    QThm S (imp (.all fun x => .neg (φ x)) (.neg (.all φ))) :=
  QThm.mp (q10_25 φ y) (QL.t2_03 (.all φ) (.all fun x => .neg (φ x)))

/-- ✱10·252 `⊢ : ∼{(∃x) . φx} . ≡ . (x) . ∼φx` [✱4·13 . (✱10·01)] -/
theorem q10_252 (φ : V τ → QF V) : QThm S (iff (.neg (ex φ)) (.all fun x => .neg (φ x))) :=
  qiffSymm (QL.t4_13 (.all fun x => .neg (φ x)))

/-- ✱10·253 `⊢ : ∼{(x) . φx} . ≡ . (∃x) . ∼φx` -/
theorem q10_253 (φ : V τ → QF V) : QThm S (iff (.neg (.all φ)) (ex fun x => .neg (φ x))) :=
  have h1 : QThm S (imp (ex fun x => .neg (φ x)) (.neg (.all φ))) :=
    QThm.mp (q10_11_21 fun y =>                                                 -- [✱10·11·21]
        qsyl (q10_1 φ y) (QL.t2_12 (φ y)))                                      -- ✱10·1 [✱2·12]
      (QL.t2_16 (.all φ) (.all fun y => .neg (.neg (φ y))))                     -- [Transp] [(✱10·01)] (1)
  have h2 : QThm S (imp (.neg (.all φ)) (ex fun x => .neg (φ x))) :=
    QThm.mp (q10_11_21 fun x =>                                                 -- [✱10·11·21]
        qsyl (q10_1 (fun y => .neg (.neg (φ y))) x) (QL.t2_14 (φ x)))           -- ✱10·1 [✱2·14]
      (QL.t2_16 (.all fun y => .neg (.neg (φ y))) (.all φ))                     -- [Transp] [(✱10·01)] (2)
  qiffI h2 h1

/-- ✱10·26 `⊢ :. (z) . φz ⊃ ψz : φx : ⊃ . ψx` [✱10·1 . Imp] -/
theorem q10_26 (φ ψ : V τ → QF V) (x : V τ) :
    QThm S (imp (QF.and (fimp φ ψ) (φ x)) (ψ x)) :=
  QThm.mp (q10_1 (fun z => imp (φ z) (ψ z)) x) (QL.t3_31 (fimp φ ψ) (φ x) (ψ x))

/-- ✱10·27 `⊢ :. (z) . φz ⊃ ψz . ⊃ : (z) . φz . ⊃ . (z) . ψz` (✱9·21; PM's alternative-method proof).
    The print cites "[✱10·1]" for the step that turns y into an apparent variable; that step is
    ✱10·11, which is what the Lean line uses. "Ass" (✱3·35) is stated for `p . p ⊃ q`; PM applies it to
    `p ⊃ q . p`, so the factors are first commuted by ✱3·22. -/
theorem q10_27 (φ ψ : V τ → QF V) :
    QThm S (imp (fimp φ ψ) (imp (.all φ) (.all ψ))) :=
  have h1 : QThm S (imp (QF.and (fimp φ ψ) (.all φ)) (.all ψ)) :=
    q10_11_21 fun y =>                                                          -- [✱10·11] [✱10·21] (1)
      qsyl (qsyl (q10_14 (fun z => imp (φ z) (ψ z)) φ y)                        -- ✱10·14
        (QL.t3_22 (imp (φ y) (ψ y)) (φ y))) (QL.t3_35 (φ y) (ψ y))               -- [Ass]
  QThm.mp h1 (QL.t3_3 (fimp φ ψ) (.all φ) (.all ψ))                              -- (1).Exp

/-- ✱10·271 `⊢ :. (z) . φz ≡ ψz . ⊃ : (z) . φz . ≡ . (z) . ψz` -/
theorem q10_271 (φ ψ : V τ → QF V) :
    QThm S (imp (fiff φ ψ) (iff (.all φ) (.all ψ))) :=
  have e := qiffMp (q10_22 (fun z => imp (φ z) (ψ z)) (fun z => imp (ψ z) (φ z)))  -- ✱10·22
  have h1 : QThm S (imp (fiff φ ψ) (imp (.all φ) (.all ψ))) :=
    qsyl (qsyl e (QL.t3_26 _ _)) (q10_27 φ ψ)                                   -- Hp ⊃ (z).φz ⊃ ψz [✱10·27] (1)
  have h2 : QThm S (imp (fiff φ ψ) (imp (.all ψ) (.all φ))) :=
    qsyl (qsyl e (QL.t3_27 _ _)) (q10_27 ψ φ)                                   -- (2)
  QThm.mp (qandI h1 h2) (QL.t3_43 _ _ _)                                         -- (1).(2).Comp

/-- ✱10·28 `⊢ :. (x) . φx ⊃ ψx . ⊃ : (∃x) . φx . ⊃ . (∃x) . ψx` (✱9·22; PM's alternative-method proof) -/
theorem q10_28 (φ ψ : V τ → QF V) :
    QThm S (imp (fimp φ ψ) (imp (ex φ) (ex ψ))) :=
  have h : QThm S (imp (fimp φ ψ) (.all fun y => imp (.neg (ψ y)) (.neg (φ y)))) :=
    q10_11_21 fun y =>                                                          -- [✱10·11·21]
      qsyl (q10_1 (fun x => imp (φ x) (ψ x)) y) (QL.t2_16 (φ y) (ψ y))          -- ✱10·1 [Transp]
  qsyl (qsyl h (q10_27 (fun y => .neg (ψ y)) (fun y => .neg (φ y))))            -- [✱10·27]
    (QL.t2_16 (.all fun y => .neg (ψ y)) (.all fun y => .neg (φ y)))            -- [Transp]

/-- ✱10·281 `⊢ :. (x) . φx ≡ ψx . ⊃ : (∃x) . φx . ≡ . (∃x) . ψx` [✱10·22·28 . Comp] -/
theorem q10_281 (φ ψ : V τ → QF V) :
    QThm S (imp (fiff φ ψ) (iff (ex φ) (ex ψ))) :=
  have e := qiffMp (q10_22 (fun z => imp (φ z) (ψ z)) (fun z => imp (ψ z) (φ z)))
  QThm.mp (qandI (qsyl (qsyl e (QL.t3_26 _ _)) (q10_28 φ ψ))
    (qsyl (qsyl e (QL.t3_27 _ _)) (q10_28 ψ φ))) (QL.t3_43 _ _ _)

/-! ## ✱9's primitive propositions, in the alternative method

  ✱9·12 is `QThm.mp`, ✱9·13 is `QThm.gen` (= ✱10·11). ✱9·14 and ✱9·15 are built into the syntax (see
  PM/Quant.lean). ✱9·1 and ✱9·11 "are not required as primitive propositions in the alternative method"
  (p. 144): they are proved here. -/

/-- ✱9·1 `⊢ : φx . ⊃ . (∃z) . φz` (= ✱10·24) -/
theorem q9_1 (φ : V τ → QF V) (x : V τ) : QThm S (imp (φ x) (ex φ)) := q10_24 φ x

/-- ✱9·11 `⊢ : φx ∨ φy . ⊃ . (∃z) . φz`. Not in PM's alternative method; proved from ✱9·1 by ✱3·44,
    the use of ✱1·2 that ✱9 (p. 137) cannot make for (∃z) . φz under ✱9's own method. -/
theorem q9_11 (φ : V τ → QF V) (x y : V τ) : QThm S (imp (.or (φ x) (φ y)) (ex φ)) :=
  QThm.mp (qandI (q9_1 φ x) (q9_1 φ y)) (QL.t3_44 (ex φ) (φ x) (φ y))

/-- ✱9·12 "What is implied by a true premiss is true." -/
theorem q9_12 {p q : QF V} (hp : QThm S p) (h : QThm S (imp p q)) : QThm S q := QThm.mp hp h

/-- ✱9·13 "In any assertion containing a real variable, this real variable may be turned into an
    apparent variable of which all possible values are asserted to satisfy the function in question." -/
theorem q9_13 {φ : V τ → QF V} (h : ∀ y, QThm S (φ y)) : QThm S (.all φ) := QThm.gen h

/-- ✱9·2 `⊢ : (x) . φx . ⊃ . φy` (= ✱10·1) -/
theorem q9_2 (φ : V τ → QF V) (y : V τ) : QThm S (imp (.all φ) (φ y)) := q10_1 φ y
/-- ✱9·21 `⊢ :. (x) . φx ⊃ ψx . ⊃ : (x) . φx . ⊃ . (x) . ψx` (= ✱10·27) -/
theorem q9_21 (φ ψ : V τ → QF V) : QThm S (imp (fimp φ ψ) (imp (.all φ) (.all ψ))) := q10_27 φ ψ
/-- ✱9·22 `⊢ :. (x) . φx ⊃ ψx . ⊃ : (∃x) . φx . ⊃ . (∃x) . ψx` (= ✱10·28) -/
theorem q9_22 (φ ψ : V τ → QF V) : QThm S (imp (fimp φ ψ) (imp (ex φ) (ex ψ))) := q10_28 φ ψ
/-- ✱9·23 `⊢ : (x) . φx . ⊃ . (x) . φx`. PM's ✱9 proof is "Id . ✱9·13·21"; here it is Id (✱2·08). -/
theorem q9_23 (φ : V τ → QF V) : QThm S (imp (.all φ) (.all φ)) := QL.t2_08 _
/-- ✱9·24 `⊢ : (∃x) . φx . ⊃ . (∃x) . φx` (Id) -/
theorem q9_24 (φ : V τ → QF V) : QThm S (imp (ex φ) (ex φ)) := QL.t2_08 _
/-- ✱9·25 `⊢ :. (x) . p ∨ φx . ⊃ : p . ∨ . (x) . φx` (= ✱10·12) -/
theorem q9_25 (p : QF V) (φ : V τ → QF V) :
    QThm S (imp (.all fun x => .or p (φ x)) (.or p (.all φ))) := q10_12 p φ

/-! ## ✱10·29–✱10·57 -/

/-- Comp (✱3·43) as a rule. -/
theorem qcomp {a b c : QF V} (h1 : QThm S (imp a b)) (h2 : QThm S (imp a c)) : QThm S (imp a (QF.and b c)) :=
  QThm.mp (qandI h1 h2) (QL.t3_43 a b c)
/-- ✱4·11 as a rule: an equivalence holds between the negations. -/
theorem qiffNeg {a b : QF V} (h : QThm S (iff a b)) : QThm S (iff (.neg a) (.neg b)) :=
  QThm.mp h (qiffMp (QL.t4_11 a b))
/-- "✱10·11·27": from `⊢ . φx ⊃ ψx` for every x, infer `⊢ : (x) . φx . ⊃ . (x) . ψx`. -/
theorem q10_11_27 {φ ψ : V τ → QF V} (h : ∀ x, QThm S (imp (φ x) (ψ x))) :
    QThm S (imp (.all φ) (.all ψ)) :=
  QThm.mp (q10_11 h) (q10_27 φ ψ)
/-- "✱10·11·271": from `⊢ . φx ≡ ψx` for every x, infer `⊢ : (x) . φx . ≡ . (x) . ψx`. -/
theorem q10_11_271 {φ ψ : V τ → QF V} (h : ∀ x, QThm S (iff (φ x) (ψ x))) :
    QThm S (iff (.all φ) (.all ψ)) :=
  QThm.mp (q10_11 h) (q10_271 φ ψ)

/-- ✱10·29 `⊢ :. (x) . φx ⊃ ψx : (x) . φx ⊃ χx : ≡ : (x) : φx . ⊃ . ψx . χx` -/
theorem q10_29 (φ ψ χ : V τ → QF V) :
    QThm S (iff (QF.and (fimp φ ψ) (fimp φ χ)) (.all fun x => imp (φ x) (QF.and (ψ x) (χ x)))) :=
  have h1 := q10_22 (fun x => imp (φ x) (ψ x)) (fun x => imp (φ x) (χ x))     -- ✱10·22 (1)
  have h2 := q10_11_271 fun x => QL.t4_76 (φ x) (ψ x) (χ x)                    -- ✱4·76 [✱10·11] [✱10·271] (2)
  qiffTrans (qiffSymm h1) h2

/-- ✱10·3 `⊢ :. (x) . φx ⊃ ψx : (x) . ψx ⊃ χx : ⊃ . (x) . φx ⊃ χx` -/
theorem q10_3 (φ ψ χ : V τ → QF V) :
    QThm S (imp (QF.and (fimp φ ψ) (fimp ψ χ)) (fimp φ χ)) :=
  qsyl (qiffMpr (q10_22 (fun x => imp (φ x) (ψ x)) (fun x => imp (ψ x) (χ x))))  -- ✱10·22·221
    (q10_11_27 fun x => QL.t3_33 (φ x) (ψ x) (χ x))                              -- [Syll . ✱10·27]

/-- ✱10·301 `⊢ :. (x) . φx ≡ ψx : (x) . ψx ≡ χx : ⊃ . (x) . φx ≡ χx` -/
theorem q10_301 (φ ψ χ : V τ → QF V) :
    QThm S (imp (QF.and (fiff φ ψ) (fiff ψ χ)) (fiff φ χ)) :=
  qsyl (qiffMpr (q10_22 (fun x => iff (φ x) (ψ x)) (fun x => iff (ψ x) (χ x))))  -- ✱10·22·221
    (q10_11_27 fun x => QL.t4_22 (φ x) (ψ x) (χ x))                              -- [✱4·22 . ✱10·27]

/-- ✱10·31 `⊢ :. (x) . φx ⊃ ψx . ⊃ : (x) : φx . χx . ⊃ . ψx . χx` -/
theorem q10_31 (φ ψ χ : V τ → QF V) :
    QThm S (imp (fimp φ ψ) (.all fun x => imp (QF.and (φ x) (χ x)) (QF.and (ψ x) (χ x)))) :=
  q10_11_27 fun x => QL.t3_45 (φ x) (ψ x) (χ x)                                  -- Fact . ✱10·11 (1), ✱10·27

/-- ✱10·311 `⊢ :. (x) . φx ≡ ψx . ⊃ : (x) : φx . χx . ≡ . ψx . χx` -/
theorem q10_311 (φ ψ χ : V τ → QF V) :
    QThm S (imp (fiff φ ψ) (.all fun x => iff (QF.and (φ x) (χ x)) (QF.and (ψ x) (χ x)))) :=
  q10_11_27 fun x => QL.t4_36 (φ x) (ψ x) (χ x)                                  -- ✱4·36 . ✱10·11 (1), ✱10·27

/-- ✱10·32 `⊢ : φx ≡ₓ ψx . ≡ . ψx ≡ₓ φx` -/
theorem q10_32 (φ ψ : V τ → QF V) : QThm S (iff (fiff φ ψ) (fiff ψ φ)) :=
  qiffTrans (q10_22 (fun x => imp (φ x) (ψ x)) (fun x => imp (ψ x) (φ x)))      -- ✱10·22
    (qiffTrans (QL.t4_3 (fimp φ ψ) (fimp ψ φ))                                   -- [✱4·3]
      (qiffSymm (q10_22 (fun x => imp (ψ x) (φ x)) (fun x => imp (φ x) (ψ x)))))  -- [✱10·22]

/-- ✱10·321 `⊢ : φx ≡ₓ ψx . φx ≡ₓ χx . ⊃ . ψx ≡ₓ χx` -/
theorem q10_321 (φ ψ χ : V τ → QF V) :
    QThm S (imp (QF.and (fiff φ ψ) (fiff φ χ)) (fiff ψ χ)) :=
  qsyl (QThm.mp (qiffMp (q10_32 φ ψ)) (QL.t3_45 (fiff φ ψ) (fiff ψ φ) (fiff φ χ))) -- ✱10·32 . Fact
    (q10_301 ψ φ χ)                                                               -- [✱10·301]

/-- ✱10·322 `⊢ : ψx ≡ₓ φx . χx ≡ₓ φx . ⊃ . ψx ≡ₓ χx`. PM cites ✱10·32 for turning the second factor
    round; the two factors are joined by ✱3·47 (with Id for the first), which PM leaves tacit. -/
theorem q10_322 (φ ψ χ : V τ → QF V) :
    QThm S (imp (QF.and (fiff ψ φ) (fiff χ φ)) (fiff ψ χ)) :=
  qsyl (QThm.mp (qandI (QL.t2_08 (fiff ψ φ)) (qiffMp (q10_32 χ φ)))              -- ✱10·32
      (QL.t3_47 (fiff ψ φ) (fiff χ φ) (fiff ψ φ) (fiff φ χ)))
    (q10_301 ψ φ χ)                                                               -- [✱10·301]

/-- ✱10·33 `⊢ :. (x) : φx . p : ≡ : (x) . φx : p`. Line (2) gets `p` from `φy . p` for one real
    variable y, so the Lean statement takes one. -/
theorem q10_33 (φ : V τ → QF V) (p : QF V) (y : V τ) :
    QThm S (iff (.all fun x => QF.and (φ x) p) (QF.and (.all φ) p)) :=
  let A : QF V := .all fun x => QF.and (φ x) p
  have l1 : ∀ y, QThm S (imp A (QF.and (φ y) p)) := fun y => q10_1 _ y           -- ✱10·1 (1)
  have h2 : QThm S (imp A p) := qsyl (l1 y) (QL.t3_27 (φ y) p)                     -- [✱3·27] (2)
  have h3 : QThm S (imp A (.all φ)) :=
    q10_11_21 fun y => qsyl (l1 y) (QL.t3_26 (φ y) p)                             -- (1).✱3·26 [✱10·11·21] (3)
  have h4 := qcomp h3 h2                                                          -- (2).(3) (4)
  have h5 : QThm S (imp (QF.and (.all φ) p) A) :=
    q10_11_21 fun x => QThm.mp (q10_1 φ x) (QL.t3_45 (.all φ) (φ x) p)           -- ✱10·1 [Fact] [✱10·11·21] (5)
  qiffI h4 h5

/-- ✱10·34 `⊢ :. (∃x) . φx ⊃ p . ≡ : (x) . φx . ⊃ . p` (PM's alternative-method proof). It cites
    ✱10·33, so it takes a real variable y too. The negations of the ✱10·271 and ✱10·33 equivalences
    are taken by ✱4·11, which PM leaves tacit. -/
theorem q10_34 (φ : V τ → QF V) (p : QF V) (y : V τ) :
    QThm S (iff (ex fun x => imp (φ x) p) (imp (.all φ) p)) :=
  have e1 : QThm S (iff (ex fun x => imp (φ x) p) (.neg (.all fun x => QF.and (φ x) (.neg p)))) :=
    qiffNeg (q10_11_271 fun x => QL.t4_61 (φ x) p)                                -- ✱4·2.(✱10·01) [✱4·61 . ✱10·271]
  have e2 := qiffNeg (q10_33 φ (.neg p) y)                                        -- [✱10·33]
  have e3 := QL.t4_53 (.all φ) p                                                  -- [✱4·53]
  have e4 := qiffSymm (QL.t4_6 (.all φ) p)                                        -- [✱4·6]
  qiffTrans e1 (qiffTrans e2 (qiffTrans e3 e4))

/-- ✱10·35 `⊢ :. (∃x) . p . φx . ≡ : p : (∃x) . φx` -/
theorem q10_35 (φ : V τ → QF V) (p : QF V) :
    QThm S (iff (ex fun x => QF.and p (φ x)) (QF.and p (ex φ))) :=
  have h1 : QThm S (imp (ex fun x => QF.and p (φ x)) p) :=
    QThm.mp (q10_11 fun x => QL.t3_26 p (φ x))                                    -- ✱3·26 [✱10·11]
      (qiffMp (q10_23 (fun x => QF.and p (φ x)) p))                               -- [✱10·23] (1)
  have h2 : QThm S (imp (ex fun x => QF.and p (φ x)) (ex φ)) :=
    QThm.mp (q10_11 fun x => QL.t3_27 p (φ x)) (q10_28 _ φ)                       -- ✱3·27 [✱10·11] [✱10·28] (2)
  have h3 : QThm S (imp p (imp (ex φ) (ex fun x => QF.and p (φ x)))) :=
    qsyl (q10_11_21 fun x => QL.t3_2 p (φ x)) (q10_28 φ _)                        -- ✱3·2 [✱10·11·21] [✱10·28] (3)
  qiffI (qcomp h1 h2) (QThm.mp h3 (QL.t3_31 p (ex φ) _))                          -- (1).(2).(3).Imp

/-- ✱10·36 `⊢ :. (∃x) . φx ∨ p . ≡ : (∃x) . φx . ∨ . p` (PM's alternative-method proof; it cites
    ✱10·34, so it takes a real variable y). -/
theorem q10_36 (φ : V τ → QF V) (p : QF V) (y : V τ) :
    QThm S (iff (ex fun x => .or (φ x) p) (.or (ex φ) p)) :=
  have e1 : QThm S (iff (ex fun x => .or (φ x) p) (ex fun x => imp (.neg (φ x)) p)) :=
    QThm.mp (q10_11 fun x => qiffSymm (QL.t4_64 (φ x) p)) (q10_281 _ _)           -- ✱4·64 [✱10·11] [✱10·281]
  have e2 := q10_34 (fun x => .neg (φ x)) p y                                     -- [✱10·34]
  have e3 := QL.t4_6 (.all fun x => .neg (φ x)) p                                 -- [✱4·6 . (✱10·01)]
  qiffTrans e1 (qiffTrans e2 e3)

/-- ✱10·37 `⊢ :. (∃x) . p ⊃ φx . ≡ : p . ⊃ . (∃x) . φx` [✱10·36 ∼p/p]. The substitution gives
    `φx ∨ ∼p` where the statement has `∼p ∨ φx`; the disjuncts are permuted by ✱4·31. -/
theorem q10_37 (φ : V τ → QF V) (p : QF V) (y : V τ) :
    QThm S (iff (ex fun x => imp p (φ x)) (imp p (ex φ))) :=
  qiffTrans (QThm.mp (q10_11 fun x => QL.t4_31 (.neg p) (φ x)) (q10_281 _ _))    -- ✱4·31
    (qiffTrans (q10_36 φ (.neg p) y) (QL.t4_31 (ex φ) (.neg p)))                   -- ✱10·36 ∼p/p, ✱4·31

/-- ✱10·39 `⊢ :. φx ⊃ₓ χx : ψx ⊃ₓ θx : ⊃ : φx . ψx . ⊃ₓ . χx . θx` -/
theorem q10_39 (φ ψ χ θ : V τ → QF V) :
    QThm S (imp (QF.and (fimp φ χ) (fimp ψ θ))
      (fimp (fun x => QF.and (φ x) (ψ x)) (fun x => QF.and (χ x) (θ x)))) :=
  qsyl (qiffMpr (q10_22 (fun x => imp (φ x) (χ x)) (fun x => imp (ψ x) (θ x))))   -- ✱10·22
    (q10_11_27 fun x => QL.t3_47 (φ x) (ψ x) (χ x) (θ x))                          -- [✱3·47 . ✱10·27]

/-- `φx ≡ₓ ψx . ⊃ . φx ⊃ₓ ψx` and `φx ≡ₓ ψx . ⊃ . ψx ⊃ₓ φx` (✱10·22, ✱3·26, ✱3·27). -/
theorem qfiffMp (φ ψ : V τ → QF V) : QThm S (imp (fiff φ ψ) (fimp φ ψ)) :=
  qsyl (qiffMp (q10_22 (fun x => imp (φ x) (ψ x)) (fun x => imp (ψ x) (φ x)))) (QL.t3_26 _ _)
theorem qfiffMpr (φ ψ : V τ → QF V) : QThm S (imp (fiff φ ψ) (fimp ψ φ)) :=
  qsyl (qiffMp (q10_22 (fun x => imp (φ x) (ψ x)) (fun x => imp (ψ x) (φ x)))) (QL.t3_27 _ _)

/-- ✱10·4 `⊢ :. φx ≡ₓ χx . ψx ≡ₓ θx . ⊃ : φx . ψx . ≡ₓ . χx . θx`. The two uses of ✱10·22 on the
    factors of Hp are joined by ✱3·47, which PM leaves tacit. -/
theorem q10_4 (φ ψ χ θ : V τ → QF V) :
    QThm S (imp (QF.and (fiff φ χ) (fiff ψ θ))
      (fiff (fun x => QF.and (φ x) (ψ x)) (fun x => QF.and (χ x) (θ x)))) :=
  have h1 := qsyl (QThm.mp (qandI (qfiffMp φ χ) (qfiffMp ψ θ)) (QL.t3_47 _ _ _ _))  -- ✱10·22
    (q10_39 φ ψ χ θ)                                                                -- [✱10·39] (1)
  have h2 := qsyl (QThm.mp (qandI (qfiffMpr φ χ) (qfiffMpr ψ θ)) (QL.t3_47 _ _ _ _))
    (q10_39 χ θ φ ψ)                                                                -- Similarly (2)
  qsyl (qcomp h1 h2)                                                                -- (1).(2).Comp
    (qiffMpr (q10_22 (fun x => imp (QF.and (φ x) (ψ x)) (QF.and (χ x) (θ x)))
      (fun x => imp (QF.and (χ x) (θ x)) (QF.and (φ x) (ψ x)))))                    -- [✱10·22]

/-- ✱10·41 `⊢ :. (x) . φx . ∨ . (x) . ψx : ⊃ . (x) . φx ∨ ψx` -/
theorem q10_41 (φ ψ : V τ → QF V) :
    QThm S (imp (.or (.all φ) (.all ψ)) (.all fun x => .or (φ x) (ψ x))) :=
  q10_11_21 fun y =>                                                               -- [✱10·11·21]
    have h1 := qsyl (q10_1 φ y) (QL.t2_2 (φ y) (ψ y))                              -- ✱10·1 [✱2·2] (1)
    have h2 := qsyl (q10_1 ψ y) (QThm.add (φ y) (ψ y))                             -- ✱10·1 [✱1·3] (2)
    QThm.mp (q10_13 h1 h2) (QL.t3_44 _ (.all φ) (.all ψ))                          -- (1).(2).✱10·13 [✱3·44]

/-- ✱10·411 `⊢ :. φx ≡ₓ χx . ψx ≡ₓ θx . ⊃ : φx ∨ ψx . ≡ₓ . χx ∨ θx` -/
theorem q10_411 (φ ψ χ θ : V τ → QF V) :
    QThm S (imp (QF.and (fiff φ χ) (fiff ψ θ))
      (fiff (fun x => .or (φ x) (ψ x)) (fun x => .or (χ x) (θ x)))) :=
  q10_11_21 fun x =>                                                               -- (1).✱10·11·21
    qsyl (q10_14 (fun x => iff (φ x) (χ x)) (fun x => iff (ψ x) (θ x)) x)          -- ✱10·14
      (QL.t4_39 (φ x) (ψ x) (χ x) (θ x))                                           -- [✱4·39] (1)

/-- ✱10·412 `⊢ : φx ≡ₓ ψx . ≡ . ∼φx ≡ₓ ∼ψx` [✱4·11 . ✱10·11·271] -/
theorem q10_412 (φ ψ : V τ → QF V) :
    QThm S (iff (fiff φ ψ) (fiff (fun x => .neg (φ x)) (fun x => .neg (ψ x)))) :=
  q10_11_271 fun x => QL.t4_11 (φ x) (ψ x)

/-- ✱10·413 `⊢ :. φx ≡ₓ χx . ψx ≡ₓ θx . ⊃ : φx ⊃ ψx . ≡ₓ . χx ⊃ θx`. ✱10·412 is applied to the first
    factor of Hp by Fact (✱3·45), which PM leaves tacit. -/
theorem q10_413 (φ ψ χ θ : V τ → QF V) :
    QThm S (imp (QF.and (fiff φ χ) (fiff ψ θ))
      (fiff (fun x => imp (φ x) (ψ x)) (fun x => imp (χ x) (θ x)))) :=
  qsyl (QThm.mp (qiffMp (q10_412 φ χ)) (QL.t3_45 _ _ (fiff ψ θ)))                -- ✱10·412
    (q10_411 (fun x => .neg (φ x)) ψ (fun x => .neg (χ x)) θ)                       -- ✱10·411 [(✱1·01)]

/-- ✱10·414 `⊢ :. φx ≡ₓ χx . ψx ≡ₓ θx . ⊃ : φx ≡ ψx . ≡ₓ . χx ≡ θx`. Line (1) is ✱10·413 with
    ψ, φ, θ, χ for φ, ψ, χ, θ; its hypothesis is Hp with the factors commuted (✱3·22, tacit in PM). -/
theorem q10_414 (φ ψ χ θ : V τ → QF V) :
    QThm S (imp (QF.and (fiff φ χ) (fiff ψ θ))
      (fiff (fun x => iff (φ x) (ψ x)) (fun x => iff (χ x) (θ x)))) :=
  have h1 := qsyl (QL.t3_22 (fiff φ χ) (fiff ψ θ)) (q10_413 ψ φ θ χ)              -- ✱10·413 ψ,φ,θ,χ/φ,ψ,χ,θ (1)
  qsyl (qcomp (q10_413 φ ψ χ θ) h1)                                                -- ✱10·413 . (1)
    (q10_4 (fun x => imp (φ x) (ψ x)) (fun x => imp (ψ x) (φ x))
      (fun x => imp (χ x) (θ x)) (fun x => imp (θ x) (χ x)))                       -- ✱10·4

/-- ✱10·42 `⊢ :. (∃x) . φx . ∨ . (∃x) . ψx : ≡ . (∃x) . φx ∨ ψx`. The negation of the ✱10·271
    equivalence is taken by ✱4·11, which PM leaves tacit; ✱10·253 is the reading of ∼(x).∼ as ∃
    (✱10·01), which is definitional here. -/
theorem q10_42 (φ ψ : V τ → QF V) :
    QThm S (iff (.or (ex φ) (ex ψ)) (ex fun x => .or (φ x) (ψ x))) :=
  have e1 := qiffNeg (qiffSymm (q10_22 (fun x => .neg (φ x)) (fun x => .neg (ψ x))))  -- ✱10·22 [✱4·11]
  have e2 := QL.t4_51 (.all fun x => .neg (φ x)) (.all fun x => .neg (ψ x))          -- [✱4·51]
  have e3 := qiffNeg (q10_11_271 fun x => QL.t4_56 (φ x) (ψ x))                      -- [✱4·56 . ✱10·271]
  qiffTrans (qiffSymm e2) (qiffTrans e1 e3)                                           -- [✱10·253]

/-- ✱10·43 `⊢ : φz ≡_z ψz . φx . ≡ . φz ≡_z ψz . ψx` -/
theorem q10_43 (φ ψ : V τ → QF V) (x : V τ) :
    QThm S (iff (QF.and (fiff φ ψ) (φ x)) (QF.and (fiff φ ψ) (ψ x))) :=
  QThm.mp (q10_1 (fun z => iff (φ z) (ψ z)) x)                                     -- ✱10·1 (1)
    (qiffMp (QL.t5_32 (fiff φ ψ) (φ x) (ψ x)))                                     -- (1).✱5·32

/-- ✱10·5 `⊢ :. (∃x) . φx . ψx . ⊃ : (∃x) . φx : (∃x) . ψx` -/
theorem q10_5 (φ ψ : V τ → QF V) :
    QThm S (imp (ex fun x => QF.and (φ x) (ψ x)) (QF.and (ex φ) (ex ψ))) :=
  qcomp (QThm.mp (q10_11 fun x => QL.t3_26 (φ x) (ψ x)) (q10_28 _ φ))              -- ✱3·26 . ✱10·11 [✱10·28] (1)
    (QThm.mp (q10_11 fun x => QL.t3_27 (φ x) (ψ x)) (q10_28 _ ψ))                  -- ✱3·27 . ✱10·11 [✱10·28] (2)

/-- ✱10·51 `⊢ :. ∼{(∃x) . φx . ψx} . ≡ : φx . ⊃ₓ . ∼ψx` -/
theorem q10_51 (φ ψ : V τ → QF V) :
    QThm S (iff (.neg (ex fun x => QF.and (φ x) (ψ x))) (fimp φ fun x => .neg (ψ x))) :=
  qiffTrans (q10_252 fun x => QF.and (φ x) (ψ x))                                  -- ✱10·252
    (q10_11_271 fun x => qiffTrans (QL.t4_51 (φ x) (ψ x))
      (qiffSymm (QL.t4_62 (φ x) (ψ x))))                                           -- [✱4·51·62 . ✱10·271]

/-- `(p ≡ q) ⊃ (r ≡ q)` from `r ≡ p` (✱4·22 exported by ✱3·3): replacing an equivalent on the left. -/
theorem qiffLeft {p q r : QF V} (h : QThm S (iff r p)) : QThm S (imp (iff p q) (iff r q)) :=
  QThm.mp h (QThm.mp (QL.t4_22 r p q) (QL.t3_3 _ _ _))

/-- ✱10·52 `⊢ :. (∃x) . φx . ⊃ : (x) . φx ⊃ p . ≡ . p`. ✱5·5 gives `(∃x).φx ⊃ p . ≡ . p`; ✱10·23
    replaces its left side, by ✱4·22 (tacit in PM). -/
theorem q10_52 (φ : V τ → QF V) (p : QF V) :
    QThm S (imp (ex φ) (iff (.all fun x => imp (φ x) p) p)) :=
  qsyl (QL.t5_5 (ex φ) p)                                                          -- ✱5·5
    (qiffLeft (q10_23 φ p))                                                        -- [✱10·23]

/-- ✱10·53 `⊢ :. ∼(∃x) . φx . ⊃ : φx . ⊃ₓ . ψx` -/
theorem q10_53 (φ ψ : V τ → QF V) : QThm S (imp (.neg (ex φ)) (fimp φ ψ)) :=
  qsyl (qiffMp (q10_252 φ))                                                        -- [✱10·252]
    (q10_11_27 fun x => QL.t2_21 (φ x) (ψ x))                                       -- ✱2·21 . ✱10·11 [✱10·27]

/-- ✱10·541 `⊢ :: φy . ⊃_y . p ∨ ψy : ≡ : p . ∨ . φy ⊃_y ψy`. Lean reads `∼φy ∨ p ∨ ψy` as
    `∼φy ∨ (p ∨ ψy)`, which is the definition of `φy ⊃ p ∨ ψy` (✱1·01); Assoc is ✱1·5 both ways. -/
theorem q10_541 (φ ψ : V τ → QF V) (p : QF V) :
    QThm S (iff (fimp φ fun y => .or p (ψ y)) (.or p (fimp φ ψ))) :=
  qiffTrans (q10_11_271 fun y => qiffI (QThm.assoc (.neg (φ y)) p (ψ y))
      (QThm.assoc p (.neg (φ y)) (ψ y)))                                           -- ✱4·2.(✱1·01) [Assoc . ✱10·271]
    (q10_2 p fun y => imp (φ y) (ψ y))                                             -- [✱10·2] [(✱1·01)]

/-- ✱10·542 `⊢ :. φy . ⊃_y . p ⊃ ψy : ≡ : p . ⊃ . φy ⊃_y ψy` [✱10·541 ∼p/p] -/
theorem q10_542 (φ ψ : V τ → QF V) (p : QF V) :
    QThm S (iff (fimp φ fun y => imp p (ψ y)) (imp p (fimp φ ψ))) := q10_541 φ ψ (.neg p)

/-- ✱10·55 `⊢ :. (∃x) . φx . ψx : φx ⊃ₓ ψx : ≡ : (∃x) . φx : φx ⊃ₓ ψx`. ✱4·71 gives `φx ≡ φx . ψx`;
    it is turned round by ✱4·21, and the factors of ✱5·32 are commuted by ✱4·3 (both tacit in PM). -/
theorem q10_55 (φ ψ : V τ → QF V) :
    QThm S (iff (QF.and (ex fun x => QF.and (φ x) (ψ x)) (fimp φ ψ)) (QF.and (ex φ) (fimp φ ψ))) :=
  have h2 : QThm S (imp (fimp φ ψ) (iff (ex fun x => QF.and (φ x) (ψ x)) (ex φ))) :=
    qsyl (q10_11_27 fun x =>
        qsyl (qiffMp (QL.t4_71 (φ x) (ψ x)))                                       -- ✱4·71 (1)
          (qiffMp (QL.t4_21 (φ x) (QF.and (φ x) (ψ x)))))                           -- (1).✱10·11·27
      (q10_281 (fun x => QF.and (φ x) (ψ x)) φ)                                    -- [✱10·281] (2)
  qiffTrans (QL.t4_3 _ _) (qiffTrans (QThm.mp h2 (qiffMp (QL.t5_32 _ _ _)))        -- (2).✱5·32
    (QL.t4_3 _ _))

/-- ✱10·56 `⊢ :. φx ⊃ₓ . ψx : (∃x) . φx . χx : ⊃ . (∃x) . ψx . χx` -/
theorem q10_56 (φ ψ χ : V τ → QF V) :
    QThm S (imp (QF.and (fimp φ ψ) (ex fun x => QF.and (φ x) (χ x))) (ex fun x => QF.and (ψ x) (χ x))) :=
  QThm.mp (qsyl (q10_31 φ ψ χ) (q10_28 _ _))                                       -- ✱10·31 [✱10·28] (1)
    (QL.t3_31 _ _ _)                                                               -- (1).Imp

/-- ✱10·57 `⊢ :. φx . ⊃ₓ . ψx ∨ χx : ⊃ : φx ⊃ₓ ψx . ∨ . (∃x) . φx . χx`. Fact is applied to the
    second factor (✱3·47 with Id); ✱5·61 is followed by ✱3·26 to drop `∼χx`; ✱5·6 gives the disjuncts
    in the other order, permuted by ✱1·4. These steps are tacit in PM. -/
theorem q10_57 (φ ψ χ : V τ → QF V) :
    QThm S (imp (fimp φ fun x => .or (ψ x) (χ x))
      (.or (fimp φ ψ) (ex fun x => QF.and (φ x) (χ x)))) :=
  let F : QF V := fimp φ fun x => .or (ψ x) (χ x)
  let E : QF V := ex fun x => QF.and (φ x) (χ x)
  have h1 : QThm S (imp (QF.and F (.neg E)) (fimp φ ψ)) :=
    qsyl (QThm.mp (qandI (QL.t2_08 F) (qiffMp (q10_51 φ χ))) (QL.t3_47 _ _ _ _))   -- ✱10·51 . Fact
      (qsyl (qiffMp (q10_29 φ (fun x => .or (ψ x) (χ x)) fun x => .neg (χ x)))     -- [✱10·29]
        (q10_11_27 fun x => QThm.mp (qsyl (qiffMp (QL.t5_61 (ψ x) (χ x)))
          (QL.t3_26 (ψ x) (.neg (χ x)))) (QL.t2_05 (φ x) _ _)))                     -- [✱5·61] (1)
  qsyl (QThm.mp h1 (qiffMp (QL.t5_6 F E (fimp φ ψ)))) (QThm.perm E (fimp φ ψ))      -- (1).✱5·6

end PM
