import PM.Star12
/-!
  ✱13: identity (1910 print, pp. 176–180).

  Statements are read from the Gutenberg #78050 transcription of the 1910 print (its formula source), not
  from the scan images. As in PM/Star11.lean, each proof follows PM's Dem. line by line,
  or uses the propositions of PM's bracketed hint in PM's order; the comment on each Lean line gives
  PM's line or hint, and any step PM leaves tacit beyond those listed in PM/Star11.lean's header is
  named in the docstring.

  Definitions (macros, like ✱1·01 and ✱10·01):
    ✱13·01  x = y . = : (φ) : φ!x . ⊃ . φ!y   Df    (`QF.ident`; φ ranges over `Ty.pred1 a`)
    ✱13·02  x ≠ y . = . ∼(x = y)              Df    (`QF.nident`)
    ✱13·03  x = y = z . = . x = y . y = z     Df    (`QF.ident3`)
  x and y have any type `a` (typical ambiguity): identity of individuals and identity of functions
  (used in ✱20) are the same Lean definition at different types.

  Reducibility. ✱13·101 cites ✱12·1 (PM p. 177: "It will be observed that the proof uses the axiom of
  reducibility"); everything that rests on ✱13·101 (✱13·11, ✱13·12, ✱13·13, …) uses it through it.
  RedCheck.lean lists them. ✱13·15 and ✱13·17 do not use it.

  ✱13·3 (p. 180) is about significance, and its proof turns on ✱10·221 (identifying the types of two
  real variables). Like ✱10·221 itself, that identification is built into the Lean typing: x and a are
  variables of one type, so the joins by ✱10·13 typecheck. The proof otherwise follows PM's lines.

  Names: `q13_101` is ✱13·101. ψ, φ are formulas with a hole (`V a → QF V`), i.e. PM's real function
  variables of any order.
-/
namespace PM
open QF

namespace QF
variable {V : Ty → Type} {S : Sys}
/-- ✱13·01 `x = y . = : (φ) : φ!x . ⊃ . φ!y` Df -/
@[reducible] def ident {a : Ty} (x y : V a) : QF V :=
  .all (τ := Ty.pred1 a) fun φ => imp (.app1 φ x) (.app1 φ y)
/-- ✱13·02 `x ≠ y . = . ∼(x = y)` Df -/
@[reducible] def nident {a : Ty} (x y : V a) : QF V := .neg (ident x y)
/-- ✱13·03 `x = y = z . = . x = y . y = z` Df -/
@[reducible] def ident3 {a : Ty} (x y z : V a) : QF V := QF.and (ident x y) (ident y z)
end QF

variable {V : Ty → Type} {S : Sys} {a b : Ty}

/-- "Fact" with the factor on the left: from `⊢ . q ⊃ r`, `⊢ : p . q . ⊃ . p . r` (✱3·47 with Id). -/
theorem qandR {p q r : QF V} (h : QThm S (imp q r)) : QThm S (imp (QF.and p q) (QF.and p r)) :=
  QThm.mp (qandI (QL.t2_08 p) h) (QL.t3_47 p q p r)

/-- ✱13·1 `⊢ :. x = y . ≡ : φ!x . ⊃_φ . φ!y` [✱4·2 . (✱13·01) . (✱10·02)] -/
theorem q13_1 (x y : V a) :
    QThm S (iff (ident x y) (fimp (τ := Ty.pred1 a) (fun φ => .app1 φ x) (fun φ => .app1 φ y))) :=
  QL.t4_2 _

/-- ✱13·101 `⊢ : x = y . ⊃ . ψx ⊃ ψy`, ψ any function, "predicative or non-predicative" (p. 177).
    Line (1) gets `(∃φ) : ψx . ≡ . φ!x : ψy . ≡ . φ!y` from ✱12·1 by ✱10·1 at x and at y, joined by Comp
    (✱3·43) and carried under (∃φ) by ✱10·11·28 (tacit in PM). In (2), ✱4·84 and ✱4·85 are joined by
    ✱3·47 and ✱4·22, and the converse half taken by ✱3·27; Comm (✱2·04) puts φ!x ⊃ φ!y first. -/
theorem q13_101 [Reducibility S] (ψ : V a → QF V) (x y : V a) : QThm S (imp (ident x y) (imp (ψ x) (ψ y))) :=
  let C : V (Ty.pred1 a) → QF V := fun φ => QF.and (iff (ψ x) (.app1 φ x)) (iff (ψ y) (.app1 φ y))
  let A : QF V := imp (ψ x) (ψ y)
  have h1 : QThm S (ex C) :=
    QThm.mp (q12_1 ψ) (q10_11_28 fun φ =>
      qcomp (q10_1 (fun z => iff (ψ z) (.app1 φ z)) x) (q10_1 (fun z => iff (ψ z) (.app1 φ z)) y))  -- ✱12·1 (1)
  have e : ∀ φ, QThm S (imp (C φ) (imp (imp (.app1 φ x) (.app1 φ y)) A)) := fun φ =>
    have h := QThm.mp (qandI (QL.t4_84 (ψ x) (.app1 φ x) (ψ y)) (QL.t4_85 (ψ y) (.app1 φ y) (.app1 φ x)))
      (QL.t3_47 _ _ _ _)                                                        -- ✱4·84·85
    qsyl (qsyl h (QL.t4_22 _ _ _)) (QL.t3_27 _ _)
  have h2 : QThm S (imp (ident x y) (.all fun φ => imp (C φ) A)) :=
    QThm.mp (q10_11 fun φ => QThm.mp (e φ) (QL.t2_04 _ _ _)) (q10_27 _ _)    -- ✱13·1 . [✱4·84·85 . ✱10·27]
  have h3 : QThm S (imp (ident x y) (imp (ex C) A)) := qsyl h2 (qiffMp (q10_23 C A))  -- [✱10·23] (2)
  QThm.mp h1 (QThm.mp h3 (QL.t2_04 _ _ _))                                      -- (1).(2)

/-- ✱13·11 `⊢ :. x = y . ≡ : φ!x . ≡_φ . φ!y`. "✱10·22" in (1) is ✱10·22 with Simp (`qfiffMp`). -/
theorem q13_11 [Reducibility S] (x y : V a) :
    QThm S (iff (ident x y) (fiff (τ := Ty.pred1 a) (fun φ => .app1 φ x) (fun φ => .app1 φ y))) :=
  have h1 := qfiffMp (τ := Ty.pred1 a) (fun φ => .app1 φ x) (fun φ => .app1 φ y)  -- ✱10·22 [✱13·1] (1)
  have h2 := fun φ : V (Ty.pred1 a) => q13_101 (fun z => .app1 φ z) x y          -- ✱13·101 (2)
  have h3 := fun φ : V (Ty.pred1 a) =>
    qsyl (q13_101 (fun z => .neg (.app1 φ z)) x y) (QL.t2_17 (.app1 φ y) (.app1 φ x))  -- ✱13·101 . ✱1·7 [Transp] (3)
  have h4 := q10_11_21 fun φ => qcomp (h2 φ) (h3 φ)                              -- (2).(3).Comp [✱10·11·21] (4)
  qiffI h4 h1                                                                    -- (1).(4)

/-- ✱13·12 `⊢ : x = y . ⊃ . ψx ≡ ψy`. PM: ✱13·101 . Comp, then Transp; here Transp (✱2·17) is applied
    to the second ✱13·101 before Comp. -/
theorem q13_12 [Reducibility S] (ψ : V a → QF V) (x y : V a) : QThm S (imp (ident x y) (iff (ψ x) (ψ y))) :=
  qcomp (q13_101 ψ x y)                                                          -- ✱13·101
    (qsyl (q13_101 (fun z => .neg (ψ z)) x y) (QL.t2_17 (ψ y) (ψ x)))            -- ✱13·101 . Transp . Comp

/-- ✱13·13 `⊢ : ψx . x = y . ⊃ . ψy` [✱13·101 . Comm . Imp] -/
theorem q13_13 [Reducibility S] (ψ : V a → QF V) (x y : V a) : QThm S (imp (QF.and (ψ x) (ident x y)) (ψ y)) :=
  QThm.mp (QThm.mp (q13_101 ψ x y) (QL.t2_04 _ _ _)) (QL.t3_31 _ _ _)

/-- ✱13·14 `⊢ : ψx . ∼ψy . ⊃ . x ≠ y` [✱13·13 . ✱4·14] -/
theorem q13_14 [Reducibility S] (ψ : V a → QF V) (x y : V a) : QThm S (imp (QF.and (ψ x) (.neg (ψ y))) (nident x y)) :=
  QThm.mp (q13_13 ψ x y) (qiffMp (QL.t4_14 (ψ x) (ident x y) (ψ y)))

/-- ✱13·15 `⊢ . x = x` [Id . ✱10·11 . ✱13·1] -/
theorem q13_15 (x : V a) : QThm S (ident x x) :=
  q10_11 fun φ => QL.t2_08 (.app1 φ x)

/-- ✱13·16 `⊢ : x = y . ≡ . y = x` [✱13·11 . ✱10·32] -/
theorem q13_16 [Reducibility S] (x y : V a) : QThm S (iff (ident x y) (ident y x)) :=
  qiffTrans (q13_11 x y) (qiffTrans (q10_32 _ _) (qiffSymm (q13_11 y x)))

/-- ✱13·17 `⊢ : x = y . y = z . ⊃ . x = z`. ✱13·1 reads Hp as `φ!x . ⊃_φ . φ!y : φ!y . ⊃_φ . φ!z`
    (definitional); then ✱10·3 with φ for its x (p. 178). -/
theorem q13_17 (x y z : V a) : QThm S (imp (QF.and (ident x y) (ident y z)) (ident x z)) :=
  q10_3 (τ := Ty.pred1 a) (fun φ => .app1 φ x) (fun φ => .app1 φ y) (fun φ => .app1 φ z)  -- ✱13·1 [✱10·3]

/-- ✱13·171 `⊢ : x = y . x = z . ⊃ . y = z` [✱13·16·17]. ✱13·16 is applied to the first factor by Fact (✱3·45). -/
theorem q13_171 [Reducibility S] (x y z : V a) : QThm S (imp (QF.and (ident x y) (ident x z)) (ident y z)) :=
  qsyl (QThm.mp (qiffMp (q13_16 x y)) (QL.t3_45 _ _ _)) (q13_17 y x z)

/-- ✱13·172 `⊢ : y = x . z = x . ⊃ . y = z` [✱13·16·17]. ✱13·16 is applied to the second factor (`qandR`). -/
theorem q13_172 [Reducibility S] (x y z : V a) : QThm S (imp (QF.and (ident y x) (ident z x)) (ident y z)) :=
  qsyl (qandR (qiffMp (q13_16 z x))) (q13_17 y x z)

/-- ✱13·18 `⊢ : x = y . x ≠ z . ⊃ . y ≠ z` [✱13·17 . ✱4·14] -/
theorem q13_18 (x y z : V a) : QThm S (imp (QF.and (ident x y) (nident x z)) (nident y z)) :=
  QThm.mp (q13_17 x y z) (qiffMp (QL.t4_14 (ident x y) (ident y z) (ident x z)))

/-- ✱13·181 `⊢ : x = y . y ≠ z . ⊃ . x ≠ z` [✱13·171 . ✱4·14] -/
theorem q13_181 [Reducibility S] (x y z : V a) : QThm S (imp (QF.and (ident x y) (nident y z)) (nident x z)) :=
  QThm.mp (q13_171 x y z) (qiffMp (QL.t4_14 (ident x y) (ident x z) (ident y z)))

/-- ✱13·182 `⊢ :. x = y . ⊃ : z = x . ≡ . z = y` [✱13·17·172 . Exp . Comp]. Comm (✱2·04) after Exp. -/
theorem q13_182 [Reducibility S] (x y z : V a) : QThm S (imp (ident x y) (iff (ident z x) (ident z y))) :=
  qcomp (QThm.mp (QThm.mp (q13_17 z x y) (QL.t3_3 _ _ _)) (QL.t2_04 _ _ _))      -- ✱13·17 . Exp
    (QThm.mp (QThm.mp (q13_172 y z x) (QL.t3_3 _ _ _)) (QL.t2_04 _ _ _))         -- ✱13·172 . Exp . Comp

/-- ✱13·183 `⊢ :. x = y . ≡ : z = x . ≡_z . z = y`. In (2), "[✱13·15]" detaches x = x by ✱3·26 and
    ✱2·27. -/
theorem q13_183 [Reducibility S] (x y : V a) :
    QThm S (iff (ident x y) (fiff (fun z => ident z x) (fun z => ident z y))) :=
  have h1 := q10_11_21 fun z => q13_182 x y z                                    -- ✱13·182 . ✱10·11·21 (1)
  have h2 := qsyl (q10_1 (fun z => iff (ident z x) (ident z y)) x)               -- ✱10·1
    (qsyl (QL.t3_26 _ _) (QThm.mp (q13_15 x) (QL.t2_27 _ _)))                   -- [✱13·15] (2)
  qiffI h1 h2                                                                    -- (1).(2)

/-- ✱13·19 `⊢ . (∃y) . y = x` [✱13·15 . ✱10·24] -/
theorem q13_19 (x : V a) : QThm S (ex fun y => ident y x) :=
  QThm.mp (q13_15 x) (q10_24 (fun y => ident y x) x)

/-- ✱13·191 `⊢ :. y = x . ⊃_y . φy : ≡ . φx`. In (1), "[✱13·15]" detaches x = x by ✱2·27; in (2),
    the half φx ⊃ φy of ✱13·12 is taken by ✱3·27. -/
theorem q13_191 [Reducibility S] (φ : V a → QF V) (x : V a) :
    QThm S (iff (fimp (fun y => ident y x) φ) (φ x)) :=
  have h1 := qsyl (q10_1 (fun y => imp (ident y x) (φ y)) x)                    -- ✱10·1
    (QThm.mp (q13_15 x) (QL.t2_27 _ _))                                         -- [✱13·15] (1)
  have h2 := q10_11_21 fun y =>
    QThm.mp (qsyl (q13_12 φ y x) (QL.t3_27 _ _)) (QL.t2_04 _ _ _)                -- ✱13·12 [Comm] [✱10·11·21] (2)
  qiffI h1 h2                                                                    -- (1).(2)

/-- ✱13·192 `⊢ :. (∃c) : x = b . ≡ₓ . x = c : ψc : ≡ . ψb`. In (2), ✱5·501 with ✱13·15 gives
    `b = b . ≡ . b = c : ⊃ . b = c`; ✱13·13 needs `c = b`, got by ✱13·16, and the factors commuted by ✱3·22. -/
theorem q13_192 [Reducibility S] (ψ : V a → QF V) (b : V a) :
    QThm S (iff (ex fun c => QF.and (fiff (fun x => ident x b) (fun x => ident x c)) (ψ c)) (ψ b)) :=
  let E : V a → QF V := fun c => QF.and (fiff (fun x => ident x b) (fun x => ident x c)) (ψ c)
  have h1 : QThm S (imp (ψ b) (ex E)) :=
    qsyl (QThm.mp (q10_11 fun x => QL.t4_2 (ident x b)) (QL.t3_2 _ _))          -- ✱4·2 . ✱3·2
      (q10_24 E b)                                                              -- [✱10·24] (1)
  have h2 : ∀ c, QThm S (imp (E c) (ψ b)) := fun c =>
    have e1 := QThm.mp (q10_1 (fun x => iff (ident x b) (ident x c)) b) (QL.t3_45 _ _ (ψ c))  -- ✱10·1
    have e2 : QThm S (imp (iff (ident b b) (ident b c)) (ident b c)) :=
      qiffMpr (QThm.mp (q13_15 b) (QL.t5_501 (ident b b) (ident b c)))         -- [✱5·501 . ✱13·15]
    have e4 := qsyl (QThm.mp (qsyl e2 (qiffMp (q13_16 b c))) (QL.t3_45 _ _ (ψ c))) (QL.t3_22 _ _)
    qsyl e1 (qsyl e4 (q13_13 ψ c b))                                           -- [✱13·13] (2)
  have h3 : QThm S (imp (ex E) (ψ b)) := QThm.mp (q10_11 h2) (qiffMp (q10_23 E (ψ b)))  -- (2).✱10·11·23 (3)
  qiffI h3 h1                                                                    -- (1).(3)

/-- ✱13·193 `⊢ : φx . x = y . ≡ . φy . x = y`. "Fact" in (4) acts on the second factor (`qandR`). -/
theorem q13_193 [Reducibility S] (φ : V a → QF V) (x y : V a) :
    QThm S (iff (QF.and (φ x) (ident x y)) (QF.and (φ y) (ident x y))) :=
  have h3 : ∀ x y : V a, QThm S (imp (QF.and (φ x) (ident x y)) (QF.and (φ y) (ident x y))) :=
    fun x y => qcomp (q13_13 φ x y) (QL.t3_27 _ _)                               -- Simp (1) . ✱13·13 (2) . Comp (3)
  have h4 := qsyl (qandR (qiffMp (q13_16 x y)))                                  -- ✱13·16 . Fact
    (qsyl (h3 y x) (qandR (qiffMp (q13_16 y x))))                                -- [(3) y,x/x,y] [✱13·16 . Fact] (4)
  qiffI (h3 x y) h4                                                              -- (3).(4)

/-- ✱13·194 `⊢ : φx . x = y . ≡ . φx . φy . x = y` [✱13·13 . ✱4·71]. ✱4·71 gives
    `φx . x = y : φy`; it is rearranged to `φx . φy : x = y` by ✱4·32 and ✱4·3 (with ✱4·38, ✱4·2). -/
theorem q13_194 [Reducibility S] (φ : V a → QF V) (x y : V a) :
    QThm S (iff (QF.and (φ x) (ident x y)) (QF.and (QF.and (φ x) (φ y)) (ident x y))) :=
  have h1 := QThm.mp (q13_13 φ x y) (qiffMp (QL.t4_71 _ _))                     -- ✱13·13 . ✱4·71
  have h2 : QThm S (iff (QF.and (QF.and (φ x) (ident x y)) (φ y)) (QF.and (QF.and (φ x) (φ y)) (ident x y))) :=
    qiffTrans (QL.t4_32 _ _ _)
      (qiffTrans (QThm.mp (qandI (QL.t4_2 (φ x)) (QL.t4_3 (ident x y) (φ y))) (QL.t4_38 _ _ _ _))
        (qiffSymm (QL.t4_32 _ _ _)))
  qiffTrans h1 h2

/-- ✱13·195 `⊢ : (∃y) . y = x . φy . ≡ . φx`. In (2), ✱13·13 has the factors in the other order
    (commuted by ✱3·22). -/
theorem q13_195 [Reducibility S] (φ : V a → QF V) (x : V a) :
    QThm S (iff (ex fun y => QF.and (ident y x) (φ y)) (φ x)) :=
  have h1 := qsyl (QThm.mp (q13_15 x) (QL.t3_2 _ (φ x)))                        -- ✱3·2 . ✱13·15
    (q10_24 (fun y => QF.and (ident y x) (φ y)) x)                              -- [✱10·24] (1)
  have h2 := QThm.mp (q10_11 fun y => qsyl (QL.t3_22 _ _) (q13_13 φ y x))       -- ✱13·13 . ✱10·11
    (qiffMp (q10_23 (fun y => QF.and (ident y x) (φ y)) (φ x)))                 -- [✱10·23] (2)
  qiffI h2 h1                                                                    -- (1).(2)

/-- ✱13·196 `⊢ :. ∼φx . ≡ : φy . ⊃_y . y ≠ x` [✱13·195 . Transp . ✱10·51]. ✱10·51 has the factors
    `φy . y = x`; they are commuted under (∃y) by ✱4·3 and ✱10·11·281. "Transp" is ✱4·11. -/
theorem q13_196 [Reducibility S] (φ : V a → QF V) (x : V a) :
    QThm S (iff (.neg (φ x)) (fimp φ fun y => nident y x)) :=
  have h1 := qiffNeg (q13_195 φ x)                                               -- ✱13·195 . Transp
  have h2 := qiffNeg (q10_11_281 fun y => QL.t4_3 (φ y) (ident y x))
  qiffTrans (qiffSymm h1) (qiffTrans (qiffSymm h2) (q10_51 φ fun y => ident y x))  -- ✱10·51

/-- ✱13·21 `⊢ :. z = x . w = y . ⊃_{z,w} . φ(z, w) : ≡ . φ(x, y)` -/
theorem q13_21 [Reducibility S] (φ : V a → V b → QF V) (x : V a) (y : V b) :
    QThm S (iff (fimp2 (fun z w => QF.and (ident z x) (ident w y)) φ) (φ x y)) :=
  qiffTrans (q11_62 (fun z => ident z x) (fun _ w => ident w y) φ)              -- ✱11·62
    (qiffTrans (q13_191 (fun z => fimp (fun w => ident w y) (φ z)) x)          -- [✱13·191]
      (q13_191 (φ x) y))                                                        -- [✱13·191]

/-- ✱13·22 `⊢ : (∃z, w) . z = x . w = y . φ(z, w) . ≡ . φ(x, y)` -/
theorem q13_22 [Reducibility S] (φ : V a → V b → QF V) (x : V a) (y : V b) :
    QThm S (iff (ex2 fun z w => QF.and (ident z x) (QF.and (ident w y) (φ z w))) (φ x y)) :=
  qiffTrans (q11_55 (fun z => ident z x) fun z w => QF.and (ident w y) (φ z w))  -- ✱11·55
    (qiffTrans (q13_195 (fun z => ex fun w => QF.and (ident w y) (φ z w)) x)   -- [✱13·195]
      (q13_195 (φ x) y))                                                        -- [✱13·195]

/-- ✱13·3 `⊢ :: φa ∨ ∼φa . ⊃ :. φx ∨ ∼φx . ≡ : x = a . ∨ . x ≠ a` (p. 180): if φa is significant, φx is
    significant when, and only when, x is identical with a or not. PM's two uses of ✱10·221 (in (6) and
    (7)) identify the a's and x's of the lines joined; here x and a have one type `τ`, so ✱10·13
    (`q10_13`) joins them directly. Simp is ✱2·02 in (2) and (4), and ✱3·26, ✱3·27 in (8), which drops
    (5) from the product (7). Line (5) needs ✱13·101 in the form `a = x . ⊃ . ψa ⊃ ψx`; PM writes x = a,
    which is turned by ✱13·16. Through ✱13·101 the proof uses ✱12·1; the statement itself is a
    propositional consequence of ✱2·11, but that is not PM's route and is not taken. -/
theorem q13_3 [Reducibility S] {τ : Ty} (φ : V τ → QF V) (a x : V τ) :
    QThm S (imp (.or (φ a) (.neg (φ a)))
      (iff (.or (φ x) (.neg (φ x))) (.or (ident x a) (nident x a)))) :=
  let P : QF V := .or (φ a) (.neg (φ a))
  let Q : QF V := .or (φ x) (.neg (φ x))
  let R : QF V := .or (ident x a) (nident x a)
  have h1 : QThm S Q := QL.t2_11 (φ x)                                          -- ✱2·11 (1)
  have h2 : QThm S (imp P Q) := QThm.mp h1 (QL.t2_02 P Q)                       -- (1).Simp (2)
  have h3 : QThm S R := QL.t2_11 (ident x a)                                    -- ✱2·11 (3)
  have h4 : QThm S (imp P R) := QThm.mp h3 (QL.t2_02 P R)                       -- (3).Simp (4)
  have h5 : QThm S (imp P (imp (ident x a) Q)) :=
    QThm.mp (qsyl (qiffMp (q13_16 x a)) (q13_101 (fun z => .or (φ z) (.neg (φ z))) a x))
      (QL.t2_04 _ _ _)                                                          -- ✱13·101 . Comm (5)
  have h6 := q10_13 h4 h5                                                       -- (4).(5).✱10·13·221 (6)
  have h7 := q10_13 h2 h6                                                       -- (2).(6).✱10·13·221 (7)
  have h8 : QThm S (QF.and (imp P Q) (imp P R)) :=
    qandI (QThm.mp h7 (QL.t3_26 _ _)) (QThm.mp (QThm.mp h7 (QL.t3_27 _ _)) (QL.t3_26 _ _))  -- (7).Simp (8)
  QThm.mp h8 (QL.t5_35 P Q R)                                                   -- (8).✱5·35

end PM
