import PM.Star22
/-!
  ✱24: the universal class, the null-class, and the existence of classes (1910 print; numbered items
  pp. 231–240, after the number's summary, pp. 229–230). The print has 73 numbered items: the
  definitions ✱24·01–✱24·03 (p. 231) and 70 propositions, ✱24·1 to ✱24·63.

  The definitions are macros (`@[reducible]`), like ✱20·01 and ✱22·01–✱22·05 (docs/TYPES_DESIGN.md
  decision 9). A class is written by its defining function (PM/Star20.lean), so V, which PM defines as the
  class x̂(x = x), is the function x ↦ x = x, and Λ = −V is ✱22·04's x ↦ x ∼∈ V. ∃!α is a proposition about
  the class α, its definiens with x ∈ α eliminated where it stands (`clsMem x α`, ✱20·01 with the smallest
  scope):
    ✱24·01  V = x̂(x = x)                   Df   (`QF.clsUniv`, `𝐕`)
    ✱24·02  Λ = −V                          Df   (`QF.clsEmpty`, `Λ`)
    ✱24·03  ∃!α . = . (∃x) . x ∈ α          Df   (`QF.clsNonempty α`)
  V and Λ are "ambiguous as to type" (p. 229), like Cls (✱20·03): the type `a` of their members is
  implicit, fixed by the context. ∃!α, "α exists", is not E! of ✱14·02 (p. 229: "This sense of 'existence'
  must not be confused with that defined in ✱14·02").

  Notation (scoped to `PM`): `Λ` is PM's sign. V cannot be a token, since `V` names the variable family of
  every file (`V : Ty → Type`), so it is the bold `𝐕`; and PM's ∃! is not used as a token, since `∃!` is
  Lean's unique existence, so ∃!α is written `clsNonempty α`.

  Statements are read from the Gutenberg #78050 transcription of the 1910 print (its formula source),
  checked against the scan of the print for every item of this number. Where they differ, the print is
  followed, and the docstring says so: ✱24·21 and ✱24·311 (`= Λ`, not `= V`), ✱24·41 and ✱24·411 (a closing
  bracket), ✱24·45 (`β ⊂ γ . γ ⊂ −α`), ✱24·55, ✱24·58 and ✱24·6 (`α ⊂ β`, not `α ⊃ β`), all on the text
  audit's list of errors for Vol I (entries 11–18); ✱24·431 ((α ∩ β), not (α ∩ γ); read here from the scan,
  p. 235); and ✱24·51, which the transcription omits (its Dem. stands under ✱24·5).

  Each proof follows PM's Dem. line by line, or uses the propositions of PM's bracketed hint in PM's order;
  the comment on each Lean line gives PM's line or hint. `data/star24_ledger.json` records, per proposition,
  which cited propositions are used and which further ones were needed. Steps done silently are those of
  PM/Star11.lean's header and PM/Star14.lean's. A displayed chain is a `calc` block (PM/Chain.lean); so is a
  chain of identities of classes, "α = β [✱x] = γ", joined by ✱20·22 (`≐`, below). Two steps recur that PM
  does not cite, each named in the docstrings and listed in the ledger:
  - putting a class for an identical one inside an expression ("equals for equals"): ✱20·18 for the
    expression, with ✱20·2 (`qclsEqCongr`), or ✱22·481, ✱22·551 where PM's lines use them;
  - using a proposition about an apparent class (✱24·11, ✱24·12) at a real one: the class analogue of ✱10·1
    (`qclsAllAt`, p. 206, ✱20·17), the expression being extensional (`clsExpr_ext`, p. 200).

  Grouping: an unbracketed product of three or more factors is grouped from the left, as PM's own
  definitions group x, y, z ∈ α (✱20·05), α ∩ β ∩ γ (✱22·53) and α ∪ β ∪ γ (✱22·71); a chain of
  equivalences "A ≡ B ≡ C" (✱24·4) is A ≡ B . B ≡ C, as in ✱14·26.

  ✱24·1 and ✱24·52 take a real variable `y`, as ✱22·351 does: they are false for an empty type, and PM says
  so (p. 239: "The assumption that there is something ... is involved in the use of the real variable").

  Names: `q24_1` is ✱24·1, and so on. α, β, γ, ξ, η, ξ', η' are classes, written by their defining
  functions; κ is a class of classes, written by its defining expression (✱24·63).
-/
namespace PM
open QF

namespace QF
variable {V : Ty → Type}
/-- ✱24·01 `V = x̂(x = x)` Df: the class whose defining function is x = x (✱13·01). -/
@[reducible] def clsUniv {a : Ty} : V a → QF V := fun x => ident x x
/-- ✱24·02 `Λ = −V` Df -/
@[reducible] def clsEmpty {a : Ty} : V a → QF V := clsCompl clsUniv
/-- ✱24·03 `∃!α . = . (∃x) . x ∈ α` Df -/
@[reducible] def clsNonempty {a : Ty} (α : V a → QF V) : QF V := ex fun x => clsMem x α
end QF

/-! The notations of ✱24 (scoped to `PM`, like those of ✱22): `𝐕` for V (✱24·01) and `Λ` for Λ (✱24·02).
    Each unfolds to the definition it names. -/
/-- `𝐕`: `clsUniv` (✱24·01), PM's V. -/
scoped notation "𝐕" => QF.clsUniv
/-- `Λ`: `clsEmpty` (✱24·02). -/
scoped notation "Λ" => QF.clsEmpty

variable {V : Ty → Type} {S : Sys V} {a : Ty}

/-! Checks of the notation: each statement is the definition it names. -/
theorem check_notation_cls_univ : (𝐕 : V a → QF V) = fun x => ident x x := rfl
theorem check_notation_cls_empty : (Λ : V a → QF V) = −𝐕 := rfl
theorem check_notation_cls_empty_unfolded : (Λ : V a → QF V) = fun x => QF.neg (x ∈ 𝐕) := rfl
theorem check_notation_cls_nonempty (α : V a → QF V) : clsNonempty α = ex fun x => x ∈ α := rfl

/-! ## Chains of identities of classes

  PM displays a chain of identities of classes as it does a chain of equivalences: "⊢ . α = β [✱x] = γ
  [✱y] = δ", or under a hypothesis "⊢ : Hp . ⊃ . α = β [✱x] = γ" (✱24·401, ✱24·412, ✱24·432). It is a
  `calc` block here, one line per PM line, as for ≡ and ⊃ (PM/Chain.lean), with the relations below. Two
  lines are joined by ✱20·22, the transitivity of identity of classes, as two ≡ lines are by ✱4·22; under a
  hypothesis, by Comp (✱3·43) and ✱20·22, and an asserted line is put under it by ✱2·02. PM leaves the
  joining step unstated, as it does ✱4·22 ("The principle is the same as that explained in respect of
  implication in ✱2·31", p. 123); the ledger lists ✱20·22 as `glue` of kind `chain` (docs/FIDELITY.md). -/

/-- `⊢ . α = β` between classes (`clsEq`), as a relation between α and β. -/
def QClsEq (S : Sys V) (ψ χ : V a → QF V) : Prop := QThm S (clsEq ψ χ)
/-- `⊢ : H . ⊃ . α = β` between classes, as a relation between α and β. -/
def QClsEqH (S : Sys V) (H : QF V) (ψ χ : V a → QF V) : Prop := QThm S (imp H (clsEq ψ χ))

/-! The notations name the system `S` of the theorem they are used in, as those of PM/Chain.lean do. -/
set_option hygiene false in
/-- `α ≐ β`: `⊢ . α = β`, identity of classes (`QClsEq`), in a chain. -/
scoped infix:50 " ≐ " => QClsEq S
set_option hygiene false in
/-- `α ≐[H] β`: `⊢ : H . ⊃ . α = β` (`QClsEqH`), in a chain. -/
scoped notation:50 A:51 " ≐[" H "] " B:51 => QClsEqH S H A B

/-- `α = β`, `β = γ` give `α = γ` (✱20·22). -/
instance transClsEq [Reducibility S] :
    @Trans (V a → QF V) (V a → QF V) (V a → QF V) (QClsEq S) (QClsEq S) (QClsEq S) :=
  ⟨fun h1 h2 => QThm.mp (qandI h1 h2) (q20_22 _ _ _)⟩
/-- Under H, `α = β` and `β = γ` give `α = γ` (Comp ✱3·43, ✱20·22). -/
instance transHClsEq [Reducibility S] {H : QF V} :
    @Trans (V a → QF V) (V a → QF V) (V a → QF V) (QClsEqH S H) (QClsEqH S H) (QClsEqH S H) :=
  ⟨fun h1 h2 => qsyl (qcomp h1 h2) (q20_22 _ _ _)⟩
/-- Under H, `α = β`, and the asserted `β = γ`, give `α = γ` (✱2·02, Comp ✱3·43, ✱20·22). -/
instance transHClsEqClsEq [Reducibility S] {H : QF V} :
    @Trans (V a → QF V) (V a → QF V) (V a → QF V) (QClsEqH S H) (QClsEq S) (QClsEqH S H) :=
  ⟨fun h1 h2 => qsyl (qcomp h1 (QThm.mp h2 (QL.t2_02 H _))) (q20_22 _ _ _)⟩
/-- The asserted `α = β`, and under H `β = γ`, give `α = γ` under H (✱2·02, Comp ✱3·43, ✱20·22). -/
instance transClsEqHClsEq [Reducibility S] {H : QF V} :
    @Trans (V a → QF V) (V a → QF V) (V a → QF V) (QClsEq S) (QClsEqH S H) (QClsEqH S H) :=
  ⟨fun h1 h2 => qsyl (qcomp (QThm.mp h1 (QL.t2_02 H _)) h2) (q20_22 _ _ _)⟩

/-! ## Further steps, each listed in the ledger where used -/

/-- `ClsExpr` for the expressions of ✱22 and ✱24 written out in a statement: the expression is unfolded
    into ∼, ∨, (x) and ✱20·01 at the class (PM/Star20.lean, `ClsExpr`), which this tactic follows
    constructor by constructor. It proves only that an expression is one PM's notation forms. -/
macro "cls_expr" : tactic => `(tactic| repeat (first
  | exact ClsExpr.const _
  | exact ClsExpr.clsMem _
  | apply ClsExpr.or
  | apply ClsExpr.neg
  | apply ClsExpr.cls
  | apply ClsExpr.all
  | intro))

/-- ✱20·18 for an expression F of a class whose value is a class (the analogue of ✱13·12 for identities,
    "equals put for equals"): `⊢ :. α = β . ⊃ . F(α) = F(β)`. ✱20·18 for the expression F(α) = F(β)
    (`qcls20_18`; extensional, `ClsExpr`) gives F(α) = F(β) . ≡ . F(β) = F(β), whose second member is ✱20·2
    (detached by ✱3·27 and Comm, `qiffElimOf`). That F is such an expression is an explicit argument,
    given at each use by `by cls_expr`. -/
theorem qclsEqCongr [Reducibility S] {b : Ty} (F : (V a → QF V) → V b → QF V) (ψ χ : V a → QF V)
    (hF : ∀ z, ClsExpr fun α => F α z) :
    QThm S (imp (clsEq ψ χ) (clsEq (F ψ) (F χ))) :=
  qsyl (qcls20_18 (fun α => clsEq (F α) (F χ))
      (clsExpr_ext (ClsExpr.clsOf (fun z => hF z) fun _ => .const _)) ψ χ)
    (qiffElimOf (q20_2 _))

/-- ✱20·21 as a rule: from `⊢ . α = β`, `⊢ . β = α`. -/
theorem qclsEqSymm [Reducibility S] {ψ χ : V a → QF V} (h : QThm S (clsEq ψ χ)) : QThm S (clsEq χ ψ) :=
  QThm.mp h (qiffMp (q20_21 ψ χ))

/-- `ẑ(ψz) = ẑ(χz) . ⊃ : ẑ(ψz) = ω . ≡ . ẑ(χz) = ω`: ✱20·23 and ✱20·22, each with Exp (✱3·3), joined by
    Comp (✱3·43); the analogue of `qclsEqR` (PM/Star20.lean) for the first member. -/
theorem qclsEqL [Reducibility S] (ψ χ ω : V a → QF V) :
    QThm S (imp (clsEq ψ χ) (iff (clsEq ψ ω) (clsEq χ ω))) :=
  qcomp (QThm.mp (q20_23 ψ χ ω) (QL.t3_3 _ _ _)) (QThm.mp (q20_22 ψ χ ω) (QL.t3_3 _ _ _))

/-- The class analogue of ✱10·1 for an extensional expression G (`qclsAllAt`, p. 206, ✱20·17): from (α) . Gα,
    G at a real class ẑ(ψz), whose defining function need not be predicative. -/
theorem qclsAllAtExt [Reducibility S] (G : (V a → QF V) → QF V) (hG : ClsExt S G) (ψ : V a → QF V) :
    QThm S (imp (clsAll G) (G ψ)) :=
  qclsAllAt G ψ fun θ => qsyl (hG (pf θ) ψ) (QL.t3_26 _ _)

/-- ✱20·53 for an extensional expression G (as `qcls20_18` is ✱20·18 for one), the class analogue of
    ✱13·191: `⊢ :. β = α . ⊃_β . Gβ : ≡ . Gα`, β apparent, α real. ✱20·53's lines with G for f{β}: the
    class analogue of ✱10·1 (`qclsAllAt`), the occurrences carried by ✱20·11 and G's extensionality and
    joined by ✱4·84, ✱4·85 (the ⊃ half by ✱3·26), "[✱20·2]" by ✱2·27; and ✱20·18 for G (`qcls20_18`) with
    ✱20·21, its "≡" used from left to right (✱3·26), Comm and ✱10·11·21. -/
theorem qcls20_53 [Reducibility S] (G : (V a → QF V) → QF V) (hG : ClsExt S G) (ψ : V a → QF V) :
    QThm S (iff (clsAll fun β => imp (clsEq β ψ) (G β)) (G ψ)) :=
  let F : (V a → QF V) → QF V := fun β => imp (clsEq β ψ) (G β)
  have h1 : QThm S (imp (clsAll F) (G ψ)) :=
    calc clsAll F
        ⊃ F ψ :=
          qclsAllAt F ψ fun θ =>
            qsyl (qimpImpIffCongr (q20_11 (pf θ) ψ fun θ' => cls ψ fun θ'' => ident θ' θ'') (hG (pf θ) ψ))
              (QL.t3_26 _ _)                                                      -- ✱10·1
      _ ⊃ G ψ := QThm.mp (q20_2 ψ) (QL.t2_27 _ _)                                  -- [✱20·2]
  have h2 : ∀ θ : V (Ty.pred1 a), QThm S (imp (clsEq (pf θ) ψ) (imp (G ψ) (G (pf θ)))) := fun θ =>
    qsyl (qiffMp (q20_21 (pf θ) ψ)) (qsyl (qcls20_18 G hG ψ (pf θ)) (QL.t3_26 _ _))  -- ✱20·18·21
  qiffI h1 (q10_11_21 fun θ => QThm.mp (h2 θ) (QL.t2_04 _ _ _))

/-- Hp ⊃ A and Hp ⊃ (A ⊃ B) give Hp ⊃ B (Comp ✱3·43, Ass ✱3·35): a line of a chain under Hp whose step uses
    Hp again. -/
theorem qimpMpH {H A B : QF V} (h1 : QThm S (imp H A)) (h2 : QThm S (imp H (imp A B))) : QThm S (imp H B) :=
  qsyl (qcomp h1 h2) (QL.t3_35 _ _)

/-- ✱22·68 with the common factor second: `⊢ . (β ∪ γ) ∩ δ = (β ∩ δ) ∪ (γ ∩ δ)`. ✱22·68 at δ, β, γ (read from
    right to left, ✱20·21), each product commuted by ✱22·51 (inside a class: `qclsEqCongr`). -/
theorem qclsDistribRight [Reducibility S] (β γ δ : V a → QF V) :
    QThm S (clsEq ((β ∪ γ) ∩ δ) ((β ∩ δ) ∪ (γ ∩ δ))) :=
  show (β ∪ γ) ∩ δ ≐ (β ∩ δ) ∪ (γ ∩ δ) from
  calc (β ∪ γ) ∩ δ
      ≐ δ ∩ (β ∪ γ) := q22_51 _ _                                                 -- ✱22·51
    _ ≐ (δ ∩ β) ∪ (δ ∩ γ) := qclsEqSymm (q22_68 δ β γ)                              -- ✱22·68
    _ ≐ (β ∩ δ) ∪ (δ ∩ γ) := QThm.mp (q22_51 δ β) (qclsEqCongr (fun X => X ∪ (δ ∩ γ)) _ _ (by cls_expr))  -- ✱22·51
    _ ≐ (β ∩ δ) ∪ (γ ∩ δ) := QThm.mp (q22_51 δ γ) (qclsEqCongr (fun X => (β ∩ δ) ∪ X) _ _ (by cls_expr))  -- ✱22·51

/-! ## ✱24·1–✱24·17: V and Λ -/

/-- ✱24·1 `⊢ . Λ ≠ V` [✱22·351 . (✱24·02)]: ✱22·351 at V. y is the real variable of ✱22·351 (✱10·251): the
    statement needs a non-empty type, as ✱10·1 does; PM says so after ✱24·52 (p. 239). -/
theorem q24_1 [Reducibility S] (y : V a) : QThm S (.neg (clsEq (Λ : V a → QF V) 𝐕)) :=
  q22_351 𝐕 y                                                                     -- ✱22·351 . (✱24·02)

/-- ✱24·101 `⊢ . V = −Λ` [✱22·831 . (✱24·02)]: Λ = −V is ✱20·2 by ✱24·02, and ✱22·831 turns it. -/
theorem q24_101 [Reducibility S] : QThm S (clsEq (𝐕 : V a → QF V) (−Λ)) :=
  QThm.mp (q20_2 Λ) (qiffMp (q22_831 Λ 𝐕))                                        -- ✱22·831 . (✱24·02)

/-- ✱24·102 `⊢ : (x) . φx . ≡ . ẑ(φz) = V`. In the first line, ✱5·501 with x = x (✱13·15) gives
    φx ≡ (x = x ≡ φx), whose second member PM writes φx ≡ x = x (✱4·21). -/
theorem q24_102 [Reducibility S] (φ : V a → QF V) : QThm S (iff (.all φ) (clsEq φ 𝐕)) :=
  have h1 : ∀ x, QThm S (iff (φ x) (iff (φ x) (ident x x))) := fun x =>
    calc φ x
        ≡ iff (ident x x) (φ x) := QThm.mp (q13_15 x) (QL.t5_501 _ _)             -- ✱13·15 . ✱5·501
      _ ≡ iff (φ x) (ident x x) := QL.t4_21 _ _
  calc QF.all φ
      ≡ fiff φ 𝐕 := q10_11_271 h1                                                 -- [✱10·11·271]
    _ ≡ clsEq φ 𝐕 := q20_15 φ 𝐕                                                   -- [✱20·15] [(✱24·01)]

/-- ✱24·103 `⊢ : (x) . ∼φx . ≡ . ẑ(φz) = Λ`. Each identity is replaced in its first member by ✱20·22·23
    (`qclsEqL`, [✱22·392]) or turned by ✱20·21 ([✱22·831], which has −V second). -/
theorem q24_103 [Reducibility S] (φ : V a → QF V) : QThm S (iff (.all fun x => .neg (φ x)) (clsEq φ Λ)) :=
  calc QF.all (fun x => .neg (φ x))
      ≡ clsEq (fun z => .neg (φ z)) 𝐕 := q24_102 _                                -- ✱24·102
    _ ≡ clsEq (−φ) 𝐕 := qiffSymm (QThm.mp (q22_392 φ) (qclsEqL _ _ 𝐕))             -- [✱22·392]
    _ ≡ clsEq 𝐕 (−φ) := q20_21 _ _
    _ ≡ clsEq φ (−𝐕) := qiffSymm (q22_831 φ 𝐕)                                    -- [✱22·831]
    _ ≡ clsEq φ Λ := QL.t4_2 _                                                    -- [(✱24·02)]

/-- ✱24·104 `⊢ . (x) . x ∈ V` -/
theorem q24_104 [Reducibility S] : QThm S (.all fun x : V a => x ∈ 𝐕) :=
  have h1 : ∀ x : V a, QThm S (iff (x ∈ 𝐕) (ident x x)) := fun x => q20_3 𝐕 x    -- ✱20·3 (1)
  QThm.mp (q10_11 fun x => q13_15 x) (qiffMpr (q10_11_271 h1))                   -- (1).✱13·15.✱10·11·271

/-- ✱24·105 `⊢ . (x) . x ∼∈ Λ`. ✱4·12 gives x ∈ V ≡ x ∼∈ Λ, which PM writes x ∼∈ Λ ≡ x ∈ V (✱4·21). -/
theorem q24_105 [Reducibility S] : QThm S (.all fun x : V a => nmem x Λ) :=
  have h1 : ∀ x : V a, QThm S (iff (nmem x Λ) (x ∈ 𝐕)) := fun x =>
    qiffSymm (QThm.mp (q22_35 𝐕 x) (qiffMp (QL.t4_12 _ _)))                       -- ✱22·35 [✱4·12] (1)
  QThm.mp q24_104 (qiffMpr (q10_11_271 h1))                                        -- (1).✱10·11·271.✱24·104

/-- ✱24·11 `⊢ . (α) . α ⊂ V`, α apparent (✱20·07). -/
theorem q24_11 [Reducibility S] : QThm S (clsAll fun α : V a → QF V => α ⊂ 𝐕) :=
  q10_11 fun _ => q10_11 fun x =>                                                 -- [✱10·11] [✱10·11 . ✱22·1]
    QThm.mp (QThm.mp q24_104 (q10_1 _ x)) (QL.t2_02 _ _)                           -- ✱24·104.✱10·1 [Simp]

/-- ✱24·12 `⊢ . (α) . Λ ⊂ α`, α apparent (✱20·07). -/
theorem q24_12 [Reducibility S] : QThm S (clsAll fun α : V a → QF V => Λ ⊂ α) :=
  q10_11 fun _ => q10_11 fun x =>                                                 -- (1).✱10·11.✱22·1
    QThm.mp (QThm.mp q24_105 (q10_1 _ x)) (QL.t2_21 _ _)                           -- ✱24·105.✱10·1 [✱2·21] (1)

/-- ✱24·12 at a real class α, by the class analogue of ✱10·1 (`qclsAllAtExt`; the expression Λ ⊂ α is
    extensional, `clsExpr_ext`). -/
theorem qnullSubset [Reducibility S] (α : V a → QF V) : QThm S (Λ ⊂ α) :=
  QThm.mp q24_12 (qclsAllAtExt _ (clsExpr_ext (ClsExpr.clsSubset_right Λ)) α)

/-- ✱24·11 at a real class α, by the class analogue of ✱10·1 (`qclsAllAtExt`). -/
theorem qsubsetUniv [Reducibility S] (α : V a → QF V) : QThm S (α ⊂ 𝐕) :=
  QThm.mp q24_11 (qclsAllAtExt _ (clsExpr_ext (ClsExpr.clsSubset_left 𝐕)) α)

/-- ✱24·13 `⊢ : α = Λ . ≡ . α ⊂ Λ`. PM's lines prove α ⊂ Λ . ≡ . α = Λ, read from right to left (✱4·21);
    ✱24·12 is used at α by the class analogue of ✱10·1 (`qnullSubset`). -/
theorem q24_13 [Reducibility S] (α : V a → QF V) : QThm S (iff (clsEq α Λ) (α ⊂ Λ)) :=
  qiffSymm <|
    calc (α ⊂ Λ)
        ≡ QF.and (α ⊂ Λ) (Λ ⊂ α) := QThm.mp (qnullSubset α) (QL.t4_73 _ _)           -- ✱24·12 . ✱4·73
      _ ≡ clsEq α Λ := q22_41 α Λ                                                   -- [✱22·41]

/-- ✱24·14 `⊢ : (x) . x ∈ α . ≡ . α = V`. "[✱20·32]" replaces x̂(x ∈ α) by α in the first member of the
    identity (✱20·22·23, `qclsEqL`). -/
theorem q24_14 [Reducibility S] (α : V a → QF V) : QThm S (iff (.all fun x => x ∈ α) (clsEq α 𝐕)) :=
  calc QF.all (fun x => x ∈ α)
      ≡ clsEq (fun x => x ∈ α) 𝐕 := q24_102 _                                     -- ✱24·102
    _ ≡ clsEq α 𝐕 := QThm.mp (q20_32 α) (qclsEqL _ _ 𝐕)                            -- [✱20·32]

/-- ✱24·141 `⊢ : V ⊂ α . ≡ . V = α`. ✱4·73 gives V ⊂ α . α ⊂ V, whose factors PM writes in the other order
    (✱4·3); ✱24·11 is used at α (`qsubsetUniv`). PM's last line is α = V; the statement's V = α is its turn
    by ✱20·21. -/
theorem q24_141 [Reducibility S] (α : V a → QF V) : QThm S (iff (𝐕 ⊂ α) (clsEq 𝐕 α)) :=
  calc (𝐕 ⊂ α)
      ≡ QF.and (𝐕 ⊂ α) (α ⊂ 𝐕) := QThm.mp (qsubsetUniv α) (QL.t4_73 _ _)
    _ ≡ QF.and (α ⊂ 𝐕) (𝐕 ⊂ α) := QL.t4_3 _ _                                      -- ✱24·11 . ✱4·73
    _ ≡ clsEq α 𝐕 := q22_41 α 𝐕                                                   -- [✱22·41]
    _ ≡ clsEq 𝐕 α := q20_21 _ _

/-- ✱24·15 `⊢ : (x) . x ∼∈ α . ≡ . α = Λ`, as ✱24·14. -/
theorem q24_15 [Reducibility S] (α : V a → QF V) : QThm S (iff (.all fun x => nmem x α) (clsEq α Λ)) :=
  calc QF.all (fun x => nmem x α)
      ≡ clsEq (fun x => x ∈ α) Λ := q24_103 _                                     -- ✱24·103
    _ ≡ clsEq α Λ := QThm.mp (q20_32 α) (qclsEqL _ _ Λ)                            -- [✱20·32]

/-- ✱24·17 `⊢ : α = V . ≡ . −α = Λ` [✱22·83 . (✱24·02)] -/
theorem q24_17 [Reducibility S] (α : V a → QF V) : QThm S (iff (clsEq α 𝐕) (clsEq (−α) Λ)) :=
  q22_83 α 𝐕                                                                      -- ✱22·83 . (✱24·02)

/-! ## ✱24·21–✱24·27: Λ and V with the operations of ✱22 -/

/-- ✱24·21 `⊢ . α ∩ −α = Λ` [✱24·103 . ✱22·89], as printed in 1910 (p. 232; the Gutenberg transcription has
    `= V`, the text audit's Vol I list, entry 11). ✱24·103 is used at the defining function of α ∩ −α, and
    ✱22·89's x ∼∈ α − α is written ∼(x ∈ α . x ∈ −α) by ✱22·33 (✱4·11, under (x)). -/
theorem q24_21 [Reducibility S] (α : V a → QF V) : QThm S (clsEq (α ∩ −α) Λ) :=
  have h : QThm S (.all fun x => .neg (QF.and (x ∈ α) (x ∈ −α))) :=
    QThm.mp (q22_89 α) (qiffMp (q10_11_271 fun x => qiffNeg (q22_33 α (−α) x)))   -- ✱22·89
  QThm.mp h (qiffMp (q24_103 (α ∩ −α)))                                            -- ✱24·103

/-- ✱24·22 `⊢ . α ∪ −α = V` [✱22·88 . ✱24·102]: ✱24·102 at the defining function of α ∪ −α, with ✱22·34 for
    ✱22·88's x ∈ α ∪ −α (under (x)). -/
theorem q24_22 [Reducibility S] (α : V a → QF V) : QThm S (clsEq (α ∪ −α) 𝐕) :=
  have h : QThm S (.all fun x => .or (x ∈ α) (x ∈ −α)) :=
    QThm.mp (q22_88 α) (qiffMp (q10_11_271 fun x => q22_34 α (−α) x))              -- ✱22·88
  QThm.mp h (qiffMp (q24_102 (α ∪ −α)))                                            -- ✱24·102

/-- ✱24·23 `⊢ . α ∩ Λ = Λ` [✱24·12 . ✱22·621]: ✱22·621 gives Λ ∩ α = Λ, commuted by ✱22·51. -/
theorem q24_23 [Reducibility S] (α : V a → QF V) : QThm S (clsEq (α ∩ Λ) Λ) :=
  show α ∩ Λ ≐ Λ from
  calc α ∩ Λ
      ≐ Λ ∩ α := q22_51 _ _
    _ ≐ Λ := QThm.mp (qnullSubset α) (qiffMp (q22_621 Λ α))                        -- ✱24·12 . ✱22·621

/-- ✱24·24 `⊢ . α ∪ Λ = α` [✱24·12 . ✱22·62]: ✱22·62 gives Λ ∪ α = α, commuted by ✱22·57. -/
theorem q24_24 [Reducibility S] (α : V a → QF V) : QThm S (clsEq (α ∪ Λ) α) :=
  show α ∪ Λ ≐ α from
  calc α ∪ Λ
      ≐ Λ ∪ α := q22_57 _ _
    _ ≐ α := QThm.mp (qnullSubset α) (qiffMp (q22_62 Λ α))                         -- ✱24·12 . ✱22·62

/-- ✱24·26 `⊢ . α ∩ V = α` [✱22·621 . ✱24·11] -/
theorem q24_26 [Reducibility S] (α : V a → QF V) : QThm S (clsEq (α ∩ 𝐕) α) :=
  QThm.mp (qsubsetUniv α) (qiffMp (q22_621 α 𝐕))                                   -- ✱22·621 . ✱24·11

/-- ✱24·27 `⊢ . α ∪ V = V` [✱22·62 . ✱24·11] -/
theorem q24_27 [Reducibility S] (α : V a → QF V) : QThm S (clsEq (α ∪ 𝐕) 𝐕) :=
  QThm.mp (qsubsetUniv α) (qiffMp (q22_62 α 𝐕))                                    -- ✱22·62 . ✱24·11

/-! ## ✱24·3–✱24·39: inclusion and the null-class -/

/-- ✱24·3 `⊢ : α ⊂ β . ≡ . α − β = Λ`. In the first line, ✱4·6 and ✱4·53 (from right to left) give
    ∼(x ∈ α . x ∼∈ β); ✱22·35 acts on the second factor (✱4·36 with ✱4·3) and ✱22·33 on the product, each
    inside the negation (✱4·11). -/
theorem q24_3 [Reducibility S] (α β : V a → QF V) : QThm S (iff (α ⊂ β) (clsEq (α − β) Λ)) :=
  have h1 : ∀ x, QThm S (iff (imp (x ∈ α) (x ∈ β)) (nmem x (α − β))) := fun x =>
    calc imp (x ∈ α) (x ∈ β)
        ≡ .neg (QF.and (x ∈ α) (nmem x β)) :=
          qiffTrans (QL.t4_6 _ _) (qiffSymm (QL.t4_53 _ _))                         -- ✱4·53·6
      _ ≡ .neg (QF.and (x ∈ α) (x ∈ −β)) := qiffNeg (qandCongrR _ (qiffSymm (q22_35 β x)))  -- [✱22·35]
      _ ≡ nmem x (α − β) := qiffNeg (qiffSymm (q22_33 α (−β) x))                    -- [✱22·33] (1)
  calc (α ⊂ β)
      ≡ .all (fun x => nmem x (α − β)) := q10_11_271 h1                           -- (1).✱10·11·271
    _ ≡ clsEq (α − β) Λ := q24_15 _                                               -- [✱24·15]

/-- ✱24·31 `⊢ : α ⊂ β . ≡ . −α ∪ β = V`. ✱22·35 acts on the first disjunct (✱4·37), under (x). -/
theorem q24_31 [Reducibility S] (α β : V a → QF V) : QThm S (iff (α ⊂ β) (clsEq (−α ∪ β) 𝐕)) :=
  calc (α ⊂ β)
      ≡ .all (fun x => .or (nmem x α) (x ∈ β)) := q10_11_271 fun _ => QL.t4_6 _ _   -- ✱4·6 [✱10·11·271]
    _ ≡ .all (fun x => .or (x ∈ −α) (x ∈ β)) :=
        q10_11_271 fun x => QThm.mp (qiffSymm (q22_35 α x)) (QL.t4_37 _ _ _)       -- [✱22·35]
    _ ≡ .all (fun x => x ∈ (−α ∪ β)) := q10_11_271 fun x => qiffSymm (q22_34 _ _ x)  -- [✱22·34]
    _ ≡ clsEq (−α ∪ β) 𝐕 := q24_14 _                                              -- [✱24·14]

/-- ✱24·311 `⊢ : α ⊂ −β . ≡ . α ∩ β = Λ`, as printed in 1910 (p. 233; the Gutenberg transcription has `= V`,
    the text audit's Vol I list, entry 12). In the first line ✱22·35 acts on the consequent (✱4·85);
    "[✱4·51·62]" is ✱4·62 and ✱4·51 from right to left; ✱22·33 acts inside the negation (✱4·11). -/
theorem q24_311 [Reducibility S] (α β : V a → QF V) : QThm S (iff (α ⊂ −β) (clsEq (α ∩ β) Λ)) :=
  have h1 : ∀ x, QThm S (iff (imp (x ∈ α) (x ∈ −β)) (nmem x (α ∩ β))) := fun x =>
    calc imp (x ∈ α) (x ∈ −β)
        ≡ imp (x ∈ α) (nmem x β) := QThm.mp (q22_35 β x) (QL.t4_85 _ _ _)           -- ✱22·35
      _ ≡ .neg (QF.and (x ∈ α) (x ∈ β)) := qiffTrans (QL.t4_62 _ _) (qiffSymm (QL.t4_51 _ _))  -- [✱4·51·62]
      _ ≡ nmem x (α ∩ β) := qiffNeg (qiffSymm (q22_33 α β x))                      -- [✱22·33] (1)
  calc (α ⊂ −β)
      ≡ .all (fun x => nmem x (α ∩ β)) := q10_11_271 h1                           -- (1).✱10·11·271
    _ ≡ clsEq (α ∩ β) Λ := q24_15 _                                               -- [✱24·15]

/-- ✱24·312 `⊢ : −α ⊂ β . ≡ . α ∪ β = V`. ✱22·35 acts on the antecedent (✱4·84), under (x). -/
theorem q24_312 [Reducibility S] (α β : V a → QF V) : QThm S (iff (−α ⊂ β) (clsEq (α ∪ β) 𝐕)) :=
  calc (−α ⊂ β)
      ≡ fimp (fun x => nmem x α) (fun x => x ∈ β) :=
        q10_11_271 fun x => QThm.mp (q22_35 α x) (QL.t4_84 _ _ _)                  -- ✱22·35
    _ ≡ .all (fun x => .or (x ∈ α) (x ∈ β)) := q10_11_271 fun _ => QL.t4_64 _ _     -- [✱4·64]
    _ ≡ .all (fun x => x ∈ α ∪ β) := q10_11_271 fun x => qiffSymm (q22_34 _ _ x)   -- [✱22·34]
    _ ≡ clsEq (α ∪ β) 𝐕 := q24_14 _                                               -- [✱24·14]

/-- ✱24·313 `⊢ : α ∩ β = Λ . ≡ . α = α − β` [✱24·311 . ✱22·621]. ✱22·621's α ∩ −β = α is turned by ✱20·21. -/
theorem q24_313 [Reducibility S] (α β : V a → QF V) : QThm S (iff (clsEq (α ∩ β) Λ) (clsEq α (α − β))) :=
  calc clsEq (α ∩ β) Λ
      ≡ (α ⊂ −β) := qiffSymm (q24_311 α β)                                        -- ✱24·311
    _ ≡ clsEq (α ∩ −β) α := q22_621 α (−β)                                        -- ✱22·621
    _ ≡ clsEq α (α − β) := q20_21 _ _

/-- ✱24·32 `⊢ :. α ∪ β = Λ . ≡ . α = Λ . β = Λ`. ✱24·13 is used for both factors, joined by ✱4·38. -/
theorem q24_32 [Reducibility S] (α β : V a → QF V) :
    QThm S (iff (clsEq (α ∪ β) Λ) (QF.and (clsEq α Λ) (clsEq β Λ))) :=
  calc clsEq (α ∪ β) Λ
      ≡ (α ∪ β ⊂ Λ) := q24_13 _                                                   -- ✱24·13
    _ ≡ QF.and (α ⊂ Λ) (β ⊂ Λ) := qiffSymm (q22_59 α β Λ)                          -- [✱22·59]
    _ ≡ QF.and (clsEq α Λ) (clsEq β Λ) :=
        QThm.mp (qandI (qiffSymm (q24_13 α)) (qiffSymm (q24_13 β))) (QL.t4_38 _ _ _ _)  -- [✱24·13]

/-- ✱24·33 `⊢ : α = V . ⊃ . α ∪ β = V`. "[✱24·27 . ✱22·57]" is two lines here. -/
theorem q24_33 [Reducibility S] (α β : V a → QF V) : QThm S (imp (clsEq α 𝐕) (clsEq (α ∪ β) 𝐕)) :=
  show α ∪ β ≐[clsEq α 𝐕] 𝐕 from
  calc α ∪ β
      ≐[clsEq α 𝐕] 𝐕 ∪ β := q22_551 α 𝐕 β                                         -- ✱22·551
    _ ≐ β ∪ 𝐕 := q22_57 _ _                                                       -- [✱22·57]
    _ ≐ 𝐕 := q24_27 β                                                             -- [✱24·27]

/-- ✱24·34 `⊢ : α = Λ . ⊃ . α ∩ β = Λ` [✱22·481 . ✱24·23], with ✱22·51 for ✱24·23's β ∩ Λ. -/
theorem q24_34 [Reducibility S] (α β : V a → QF V) : QThm S (imp (clsEq α Λ) (clsEq (α ∩ β) Λ)) :=
  show α ∩ β ≐[clsEq α Λ] Λ from
  calc α ∩ β
      ≐[clsEq α Λ] Λ ∩ β := q22_481 α Λ β                                         -- ✱22·481
    _ ≐ β ∩ Λ := q22_51 _ _
    _ ≐ Λ := q24_23 β                                                             -- ✱24·23

/-- ✱24·35 `⊢ : α = V . ⊃ . α ∩ β = β` [✱22·481 . ✱24·26], with ✱22·51 for ✱24·26's β ∩ V. -/
theorem q24_35 [Reducibility S] (α β : V a → QF V) : QThm S (imp (clsEq α 𝐕) (clsEq (α ∩ β) β)) :=
  show α ∩ β ≐[clsEq α 𝐕] β from
  calc α ∩ β
      ≐[clsEq α 𝐕] 𝐕 ∩ β := q22_481 α 𝐕 β                                         -- ✱22·481
    _ ≐ β ∩ 𝐕 := q22_51 _ _
    _ ≐ β := q24_26 β                                                             -- ✱24·26

/-- ✱24·36 `⊢ : α = Λ . ⊃ . α ∪ β = β` [✱22·551 . ✱24·24], with ✱22·57 for ✱24·24's β ∪ Λ. -/
theorem q24_36 [Reducibility S] (α β : V a → QF V) : QThm S (imp (clsEq α Λ) (clsEq (α ∪ β) β)) :=
  show α ∪ β ≐[clsEq α Λ] β from
  calc α ∪ β
      ≐[clsEq α Λ] Λ ∪ β := q22_551 α Λ β                                         -- ✱22·551
    _ ≐ β ∪ Λ := q22_57 _ _
    _ ≐ β := q24_24 β                                                             -- ✱24·24

/-- ✱24·37 `⊢ :. α ∩ β = Λ . ≡ : x ∈ α . y ∈ β . ⊃_{x,y} . x ≠ y`. "[✱13·191]": for each x, ✱13·191 at
    y ↦ ∼(x ∈ α . y ∈ β), whose y = x PM writes x = y (✱13·16, with ✱4·84, under (y)). "[Transp]" is ✱2·03
    both ways. -/
theorem q24_37 [Reducibility S] (α β : V a → QF V) :
    QThm S (iff (clsEq (α ∩ β) Λ) (fimp2 (fun x y => QF.and (x ∈ α) (y ∈ β)) fun x y => nident x y)) :=
  have h13 : ∀ x, QThm S (iff (.neg (QF.and (x ∈ α) (x ∈ β)))
      (.all fun y => imp (ident x y) (.neg (QF.and (x ∈ α) (y ∈ β))))) := fun x =>
    qiffSymm <|
      calc QF.all (fun y => imp (ident x y) (.neg (QF.and (x ∈ α) (y ∈ β))))
          ≡ fimp (fun y => ident y x) (fun y => .neg (QF.and (x ∈ α) (y ∈ β))) :=
            q10_11_271 fun y => QThm.mp (q13_16 x y) (QL.t4_84 _ _ _)
        _ ≡ .neg (QF.and (x ∈ α) (x ∈ β)) := q13_191 (fun y => .neg (QF.and (x ∈ α) (y ∈ β))) x
  calc clsEq (α ∩ β) Λ
      ≡ .all (fun x => nmem x (α ∩ β)) := qiffSymm (q24_15 _)                     -- ✱24·15
    _ ≡ .all (fun x => .neg (QF.and (x ∈ α) (x ∈ β))) :=
        q10_11_271 fun x => qiffNeg (q22_33 α β x)                                -- [✱22·33]
    _ ≡ all2 (fun x y => imp (ident x y) (.neg (QF.and (x ∈ α) (y ∈ β)))) :=
        q10_11_271 h13                                                            -- [✱13·191]
    _ ≡ fimp2 (fun x y => QF.and (x ∈ α) (y ∈ β)) (fun x y => nident x y) :=
        q10_11_271 fun _ => q10_11_271 fun _ => qiffI (QL.t2_03 _ _) (QL.t2_03 _ _)  -- [Transp]

/-- α ∩ β = Λ . α = β . ⊃ . α ∩ α = Λ, the first line of ✱24·38 and of ✱24·57 [✱22·481]: ✱22·481 gives
    α ∩ α = β ∩ α, and β ∩ α = α ∩ β (✱22·51) = Λ, joined by ✱20·22. -/
theorem qinterSelfNull [Reducibility S] (α β : V a → QF V) :
    QThm S (imp (QF.and (clsEq (α ∩ β) Λ) (clsEq α β)) (clsEq (α ∩ α) Λ)) :=
  show α ∩ α ≐[QF.and (clsEq (α ∩ β) Λ) (clsEq α β)] Λ from
  calc α ∩ α
      ≐[QF.and (clsEq (α ∩ β) Λ) (clsEq α β)] β ∩ α := qsyl (QL.t3_27 _ _) (q22_481 α β α)  -- ✱22·481
    _ ≐ α ∩ β := q22_51 _ _
    _ ≐[QF.and (clsEq (α ∩ β) Λ) (clsEq α β)] Λ := QL.t3_26 _ _

/-- ✱24·38 `⊢ :. α ∩ β = Λ . ⊃ : α ≠ β . ∨ . α = Λ . β = Λ`. "[✱22·5]": α = α ∩ α (✱22·5, turned by ✱20·21)
    replaces α ∩ α in α ∩ α = Λ (✱20·22·23, `qclsEqL`); "[✱20·23]" takes α = β from Hp (✱3·27), joined by
    Comp (✱3·43). -/
theorem q24_38 [Reducibility S] (α β : V a → QF V) :
    QThm S (imp (clsEq (α ∩ β) Λ) (.or (.neg (clsEq α β)) (QF.and (clsEq α Λ) (clsEq β Λ)))) :=
  let H := QF.and (clsEq (α ∩ β) Λ) (clsEq α β)
  have l1 : QThm S (imp H (clsEq (α ∩ α) Λ)) := qinterSelfNull α β                 -- ✱22·481
  have l2 : QThm S (imp H (clsEq α Λ)) :=
    qsyl l1 (qiffMp (QThm.mp (q22_5 α) (qclsEqL _ _ Λ)))                           -- [✱22·5]
  have h1 : QThm S (imp H (QF.and (clsEq α Λ) (clsEq β Λ))) :=
    qcomp l2 (qsyl (qcomp (QL.t3_27 _ _) l2) (q20_23 α β Λ))                       -- [✱20·23] (1)
  calc clsEq (α ∩ β) Λ
      ⊃ imp (clsEq α β) (QF.and (clsEq α Λ) (clsEq β Λ)) := QThm.mp h1 (QL.t3_3 _ _ _)  -- (1).Exp
    _ ⊃ .or (.neg (clsEq α β)) (QF.and (clsEq α Λ) (clsEq β Λ)) := qiffMp (QL.t4_6 _ _)  -- [✱4·6]

/-- ✱24·39 `⊢ :. α ∩ β = Λ . ≡ : x ∈ α . ⊃ₓ . x ∼∈ β` [✱24·311 . ✱22·35], ✱22·35 on the consequent (✱4·85,
    under (x)). -/
theorem q24_39 [Reducibility S] (α β : V a → QF V) :
    QThm S (iff (clsEq (α ∩ β) Λ) (fimp (fun x => x ∈ α) fun x => nmem x β)) :=
  calc clsEq (α ∩ β) Λ
      ≡ (α ⊂ −β) := qiffSymm (q24_311 α β)                                        -- ✱24·311
    _ ≡ fimp (fun x => x ∈ α) (fun x => nmem x β) :=
        q10_11_271 fun x => QThm.mp (q22_35 β x) (QL.t4_85 _ _ _)                  -- ✱22·35

/-! ## ✱24·4–✱24·495: lemmas "for use in much later propositions" (p. 236) -/

/-- ✱24·4 `⊢ : α ∩ β = Λ . ≡ . (α ∪ β) − α = β . ≡ . (α ∪ β) − β = α`, the chain stated as A ≡ B . B ≡ C (as
    ✱14·26 is); PM's (1) and (2) are A ≡ B and A ≡ C, joined by ✱4·21 and ✱4·22. In (1), ✱24·311 at β, α has
    β ∩ α, written α ∩ β by ✱22·51 (with ✱20·22·23, `qclsEqL`), and ✱22·9 at β, α has (β ∪ α) − α, written
    (α ∪ β) − α by ✱22·57 (inside a class, `qclsEqCongr`). In (2), "[✱22·51·57]" rewrites (1) at β, α the
    same way. -/
theorem q24_4 [Reducibility S] (α β : V a → QF V) :
    QThm S (QF.and (iff (clsEq (α ∩ β) Λ) (clsEq ((α ∪ β) − α) β))
      (iff (clsEq ((α ∪ β) − α) β) (clsEq ((α ∪ β) − β) α))) :=
  have h1 : ∀ α β : V a → QF V, QThm S (iff (clsEq (α ∩ β) Λ) (clsEq ((α ∪ β) − α) β)) := fun α β =>
    have e : QThm S (clsEq ((α ∪ β) − α) (β − α)) :=
      show (α ∪ β) − α ≐ β − α from
      calc (α ∪ β) − α
          ≐ (β ∪ α) − α := QThm.mp (q22_57 α β) (qclsEqCongr (fun X => X − α) _ _ (by cls_expr))
        _ ≐ β − α := q22_9 β α
    calc clsEq (α ∩ β) Λ
        ≡ clsEq (β ∩ α) Λ := QThm.mp (q22_51 α β) (qclsEqL _ _ Λ)
      _ ≡ (β ⊂ −α) := qiffSymm (q24_311 β α)                                      -- ✱24·311
      _ ≡ clsEq (β − α) β := q22_621 β (−α)                                       -- [✱22·621]
      _ ≡ clsEq ((α ∪ β) − α) β := qiffSymm (QThm.mp e (qclsEqL _ _ β))            -- [✱22·9] (1)
  have h2 : QThm S (iff (clsEq (α ∩ β) Λ) (clsEq ((α ∪ β) − β) α)) :=
    calc clsEq (α ∩ β) Λ
        ≡ clsEq (β ∩ α) Λ := QThm.mp (q22_51 α β) (qclsEqL _ _ Λ)
      _ ≡ clsEq ((β ∪ α) − β) α := h1 β α                                         -- (1) β, α / α, β
      _ ≡ clsEq ((α ∪ β) − β) α :=
          QThm.mp (QThm.mp (q22_57 β α) (qclsEqCongr (fun X => X − β) _ _ (by cls_expr))) (qclsEqL _ _ α)  -- [✱22·51·57] (2)
  qandI (h1 α β) (qiffTrans (qiffSymm (h1 α β)) h2)                                 -- (1).(2)

/-- ✱24·401 `⊢ : β ⊂ α . ⊃ . (β ∪ γ) − α = γ − α`. (1) is ✱22·68 with the common factor second
    (`qclsDistribRight`); in (1).(2), β − α = Λ is put for β − α in the sum (✱22·551), and "[✱24·24]" has
    the sum in the other order (✱22·57). -/
theorem q24_401 [Reducibility S] (α β γ : V a → QF V) :
    QThm S (imp (β ⊂ α) (clsEq ((β ∪ γ) − α) (γ − α))) :=
  show (β ∪ γ) − α ≐[β ⊂ α] γ − α from
  calc (β ∪ γ) − α
      ≐ (β − α) ∪ (γ − α) := qclsDistribRight β γ (−α)                            -- ✱22·68 (1)
    _ ≐[β ⊂ α] Λ ∪ (γ − α) := qsyl (qiffMp (q24_3 β α)) (q22_551 _ _ _)             -- ✱24·3 (2) . (1).(2)
    _ ≐ (γ − α) ∪ Λ := q22_57 _ _
    _ ≐ γ − α := q24_24 _                                                         -- [✱24·24]

/-- ✱24·402 `⊢ : α ∩ β = Λ . ξ ⊂ α . η ⊂ β . ⊃ . ξ ∩ η = Λ`. The factors of Hp are taken by Simp (✱3·26,
    ✱3·27, Comp ✱3·43); "[✱22·55]" uses Hp's α ∩ β = Λ (✱3·35, `qimpMpH`). -/
theorem q24_402 [Reducibility S] (α β ξ η : V a → QF V) :
    QThm S (imp (QF.and (QF.and (clsEq (α ∩ β) Λ) (ξ ⊂ α)) (η ⊂ β)) (clsEq (ξ ∩ η) Λ)) :=
  let H := QF.and (QF.and (clsEq (α ∩ β) Λ) (ξ ⊂ α)) (η ⊂ β)
  have hA : QThm S (imp H (clsEq (α ∩ β) Λ)) := qsyl (QL.t3_26 _ _) (QL.t3_26 _ _)
  have hB : QThm S (imp H (QF.and (ξ ⊂ α) (η ⊂ β))) :=
    qcomp (qsyl (QL.t3_26 _ _) (QL.t3_27 _ _)) (QL.t3_27 _ _)
  have l1 : QThm S (imp H (ξ ∩ η ⊂ α ∩ β)) := qsyl hB (q22_49 ξ α η β)            -- ✱22·49
  have l2 : QThm S (imp H (ξ ∩ η ⊂ Λ)) :=
    qimpMpH l1 (qsyl hA (qsyl (q22_55 _ _ _) (QL.t3_26 _ _)))                       -- [✱22·55]
  qsyl l2 (qiffMpr (q24_13 _))                                                    -- [✱24·13]

/-- ✱24·41 `⊢ . α = (α ∩ β) ∪ (α − β)`, as printed (p. 235; the transcription drops the last bracket, the text
    audit's Vol I list, entry 13). PM's lines prove (α ∩ β) ∪ (α − β) = α, turned by ✱20·21; "[✱24·22]" puts V
    for β ∪ −β inside α ∩ (β ∪ −β) (`qclsEqCongr`). -/
theorem q24_41 [Reducibility S] (α β : V a → QF V) : QThm S (clsEq α ((α ∩ β) ∪ (α − β))) :=
  qclsEqSymm <|
    show (α ∩ β) ∪ (α − β) ≐ α from
    calc (α ∩ β) ∪ (α − β)
        ≐ α ∩ (β ∪ −β) := q22_68 α β (−β)                                         -- ✱22·68
      _ ≐ α ∩ 𝐕 := QThm.mp (q24_22 β) (qclsEqCongr (fun X => α ∩ X) _ _ (by cls_expr))           -- [✱24·22]
      _ ≐ α := q24_26 α                                                           -- [✱24·26]

/-- ✱24·411 `⊢ : β ⊂ α . ⊃ . α = β ∪ (α − β)`, as printed (p. 235; the transcription drops the last bracket, the
    text audit's Vol I list, entry 14). ✱22·633 at β, α, α − β gives (β ∩ α) ∪ (α − β), which PM writes
    (α ∩ β) ∪ (α − β) (✱22·51, inside the sum); ✱24·41 is turned by ✱20·21, and so is the result. -/
theorem q24_411 [Reducibility S] (α β : V a → QF V) : QThm S (imp (β ⊂ α) (clsEq α (β ∪ (α − β)))) :=
  have h : QThm S (imp (β ⊂ α) (clsEq (β ∪ (α − β)) α)) :=
    show β ∪ (α − β) ≐[β ⊂ α] α from
    calc β ∪ (α − β)
        ≐[β ⊂ α] (β ∩ α) ∪ (α − β) := q22_633 β α (α − β)                         -- ✱22·633
      _ ≐ (α ∩ β) ∪ (α − β) := QThm.mp (q22_51 β α) (q22_551 _ _ _)
      _ ≐ α := qclsEqSymm (q24_41 α β)                                            -- [✱24·41]
  qsyl h (qiffMp (q20_21 _ _))

/-- ✱24·412 `⊢ : β ⊂ α . γ ⊂ β . ⊃ . (α − β) ∪ (β − γ) = α − γ`. The first line is ✱24·41 at α − β, γ inside
    the sum (✱22·551). "[✱24·3·23]": (α − β) ∩ γ is α ∩ (γ − β) (✱22·52, ✱22·51), which is α ∩ Λ by ✱24·3 and
    Hp, and Λ by ✱24·23; the term Λ is dropped by ✱22·57 and ✱24·24. "[✱22·68]" is ✱22·68 with the common
    factor second (`qclsDistribRight`), from right to left. "[✱24·411]" has (α − β) ∪ β in the other order
    (✱22·57). Each line acts inside a class by `qclsEqCongr`. -/
theorem q24_412 [Reducibility S] (α β γ : V a → QF V) :
    QThm S (imp (QF.and (β ⊂ α) (γ ⊂ β)) (clsEq ((α − β) ∪ (β − γ)) (α − γ))) :=
  let H := QF.and (β ⊂ α) (γ ⊂ β)
  have hz : QThm S (imp H (clsEq ((α − β) ∩ γ) Λ)) :=
    show (α − β) ∩ γ ≐[H] Λ from
    calc (α − β) ∩ γ
        ≐ α ∩ (−β ∩ γ) := q22_52 α (−β) γ
      _ ≐ α ∩ (γ − β) := QThm.mp (q22_51 (−β) γ) (qclsEqCongr (fun X => α ∩ X) _ _ (by cls_expr))
      _ ≐[H] α ∩ Λ := qsyl (QL.t3_27 _ _) (qsyl (qiffMp (q24_3 γ β)) (qclsEqCongr (fun X => α ∩ X) _ _ (by cls_expr)))  -- ✱24·3
      _ ≐ Λ := q24_23 α                                                           -- ✱24·23
  have hβ : QThm S (imp H (clsEq ((α − β) ∪ β) α)) :=
    show (α − β) ∪ β ≐[H] α from
    calc (α − β) ∪ β
        ≐ β ∪ (α − β) := q22_57 _ _
      _ ≐[H] α := qsyl (QL.t3_26 _ _) (qsyl (q24_411 α β) (qiffMp (q20_21 _ _)))      -- ✱24·411
  show (α − β) ∪ (β − γ) ≐[H] α − γ from
  calc (α − β) ∪ (β − γ)
      ≐ ((α − β) ∩ γ ∪ ((α − β) − γ)) ∪ (β − γ) := QThm.mp (q24_41 (α − β) γ) (q22_551 _ _ _)  -- ✱24·41
    _ ≐[H] (Λ ∪ ((α − β) − γ)) ∪ (β − γ) :=
        qsyl hz (qclsEqCongr (fun X => (X ∪ ((α − β) − γ)) ∪ (β − γ)) _ _ (by cls_expr))          -- [✱24·3·23]
    _ ≐ (((α − β) − γ) ∪ Λ) ∪ (β − γ) := QThm.mp (q22_57 _ _) (q22_551 _ _ _)
    _ ≐ ((α − β) − γ) ∪ (β − γ) := QThm.mp (q24_24 _) (q22_551 _ _ _)
    _ ≐ ((α − β) ∪ β) − γ := qclsEqSymm (qclsDistribRight (α − β) β (−γ))          -- [✱22·68]
    _ ≐[H] α − γ := qsyl hβ (q22_481 _ _ _)                                        -- [✱24·411]

/-- ✱24·42 `⊢ : α ∩ β ⊂ γ . α − β ⊂ γ . ≡ . α ⊂ γ`. "[✱24·41]" puts α for (α ∩ β) ∪ (α − β) by ✱22·54 (with
    ✱24·41 turned by ✱20·21). -/
theorem q24_42 [Reducibility S] (α β γ : V a → QF V) :
    QThm S (iff (QF.and (α ∩ β ⊂ γ) (α − β ⊂ γ)) (α ⊂ γ)) :=
  calc QF.and (α ∩ β ⊂ γ) (α − β ⊂ γ)
      ≡ ((α ∩ β) ∪ (α − β) ⊂ γ) := q22_59 _ _ _                                  -- ✱22·59
    _ ≡ (α ⊂ γ) := QThm.mp (qclsEqSymm (q24_41 α β)) (q22_54 _ _ γ)               -- [✱24·41]

/-- ✱24·43 `⊢ : α − β ⊂ γ . ≡ . α ⊂ β ∪ γ`. The line of ✱5·6 is written from its first member: ✱22·33 and
    ✱22·35 (on the second factor, ✱4·36 with ✱4·3) act on the antecedent (✱4·84), ✱22·34 on the consequent
    (✱4·85). -/
theorem q24_43 [Reducibility S] (α β γ : V a → QF V) : QThm S (iff (α − β ⊂ γ) (α ⊂ β ∪ γ)) :=
  q10_11_271 fun x =>                                                             -- (1).✱10·11·271
    calc imp (x ∈ α − β) (x ∈ γ)
        ≡ imp (QF.and (x ∈ α) (nmem x β)) (x ∈ γ) :=
          QThm.mp (qiffTrans (q22_33 α (−β) x) (qandCongrR _ (q22_35 β x))) (QL.t4_84 _ _ _)  -- [✱22·35·33]
      _ ≡ imp (x ∈ α) (.or (x ∈ β) (x ∈ γ)) := QL.t5_6 _ _ _                       -- ✱5·6
      _ ≡ imp (x ∈ α) (x ∈ β ∪ γ) := QThm.mp (qiffSymm (q22_34 β γ x)) (QL.t4_85 _ _ _)  -- [✱22·34] (1)

/-- ✱24·431 `⊢ . (α ∪ γ) ∩ (β ∪ −γ) = (α ∩ β) ∪ (α − γ) ∪ (β ∩ γ)`, as printed (p. 235). The Gutenberg
    transcription has (α ∩ γ) for the first term, here and in the last line of the Dem., and (α ∩ γ) for
    (α ∩ β) in the second line; with (α ∩ γ) the statement is false (α = γ = {a}, β = Λ). The scan, p. 235,
    reads (α ∩ β). PM's first line is ✱22·68 from right to
    left; its second is ✱22·68 with the common factor second (`qclsDistribRight`) on both terms, the four
    terms regrouped by ✱22·7 (PM writes them without brackets, ✱22·71); "[✱22·51·57]" also needs ✱22·7. -/
theorem q24_431 [Reducibility S] (α β γ : V a → QF V) :
    QThm S (clsEq ((α ∪ γ) ∩ (β ∪ −γ)) ((α ∩ β) ∪ (α − γ) ∪ (β ∩ γ))) :=
  show (α ∪ γ) ∩ (β ∪ −γ) ≐ (α ∩ β) ∪ (α − γ) ∪ (β ∩ γ) from
  calc (α ∪ γ) ∩ (β ∪ −γ)
      ≐ ((α ∪ γ) ∩ β) ∪ ((α ∪ γ) ∩ −γ) := qclsEqSymm (q22_68 _ _ _)                 -- ✱22·68
    _ ≐ ((α ∩ β) ∪ (γ ∩ β)) ∪ ((α ∪ γ) ∩ −γ) := QThm.mp (qclsDistribRight α γ β) (q22_551 _ _ _)
    _ ≐ ((α ∩ β) ∪ (γ ∩ β)) ∪ ((α − γ) ∪ (γ − γ)) :=
        QThm.mp (qclsDistribRight α γ (−γ)) (qclsEqCongr (fun X => ((α ∩ β) ∪ (γ ∩ β)) ∪ X) _ _ (by cls_expr))
    _ ≐ (α ∩ β) ∪ (γ ∩ β) ∪ (α − γ) ∪ (γ − γ) := qclsEqSymm (q22_7 _ _ _)           -- [✱22·68]
    _ ≐ (α ∩ β) ∪ (γ ∩ β) ∪ (α − γ) ∪ Λ :=
        QThm.mp (q24_21 γ) (qclsEqCongr (fun X => (α ∩ β) ∪ (γ ∩ β) ∪ (α − γ) ∪ X) _ _ (by cls_expr))  -- [✱24·21]
    _ ≐ (α ∩ β) ∪ (γ ∩ β) ∪ (α − γ) := q24_24 _                                    -- [✱24·24]
    _ ≐ (α ∩ β) ∪ ((γ ∩ β) ∪ (α − γ)) := q22_7 _ _ _
    _ ≐ (α ∩ β) ∪ ((α − γ) ∪ (γ ∩ β)) := QThm.mp (q22_57 _ _) (qclsEqCongr (fun X => (α ∩ β) ∪ X) _ _ (by cls_expr))
    _ ≐ (α ∩ β) ∪ (α − γ) ∪ (γ ∩ β) := qclsEqSymm (q22_7 _ _ _)
    _ ≐ (α ∩ β) ∪ (α − γ) ∪ (β ∩ γ) :=
        QThm.mp (q22_51 γ β) (qclsEqCongr (fun X => (α ∩ β) ∪ (α − γ) ∪ X) _ _ (by cls_expr))      -- [✱22·51·57]

/-- ✱24·432 `⊢ . (α − γ) ∪ (β ∩ γ) = (α ∩ β) ∪ (α − γ) ∪ (β ∩ γ)`. PM's lines prove the identity from right to
    left (turned by ✱20·21). "✱24·22·35" is ✱24·35 with γ ∪ −γ = V (its product commuted, ✱22·51);
    "[✱22·51]" also needs ✱22·52 (α ∩ β − γ is α ∩ −γ ∩ β); each "[✱22·63]" is ✱22·63 for a term absorbed by
    the term beside it, after ✱22·7, ✱22·57 (and ✱22·51, ✱22·52 for α ∩ β ∩ γ). -/
theorem q24_432 [Reducibility S] (α β γ : V a → QF V) :
    QThm S (clsEq ((α − γ) ∪ (β ∩ γ)) ((α ∩ β) ∪ (α − γ) ∪ (β ∩ γ))) :=
  have l1 : QThm S (clsEq (α ∩ β) (((α ∩ β) ∩ γ) ∪ ((α − γ) ∩ β))) :=
    show α ∩ β ≐ ((α ∩ β) ∩ γ) ∪ ((α − γ) ∩ β) from
    calc α ∩ β
        ≐ (γ ∪ −γ) ∩ (α ∩ β) := qclsEqSymm (QThm.mp (q24_22 γ) (q24_35 _ _))       -- ✱24·22·35
      _ ≐ (α ∩ β) ∩ (γ ∪ −γ) := q22_51 _ _
      _ ≐ ((α ∩ β) ∩ γ) ∪ ((α ∩ β) − γ) := qclsEqSymm (q22_68 _ _ _)               -- [✱22·68]
      _ ≐ ((α ∩ β) ∩ γ) ∪ (α ∩ (β − γ)) :=
          QThm.mp (q22_52 α β (−γ)) (qclsEqCongr (fun X => ((α ∩ β) ∩ γ) ∪ X) _ _ (by cls_expr))
      _ ≐ ((α ∩ β) ∩ γ) ∪ (α ∩ (−γ ∩ β)) :=
          QThm.mp (q22_51 β (−γ)) (qclsEqCongr (fun X => ((α ∩ β) ∩ γ) ∪ (α ∩ X)) _ _ (by cls_expr))
      _ ≐ ((α ∩ β) ∩ γ) ∪ ((α − γ) ∩ β) :=
          QThm.mp (qclsEqSymm (q22_52 α (−γ) β)) (qclsEqCongr (fun X => ((α ∩ β) ∩ γ) ∪ X) _ _ (by cls_expr))  -- [✱22·51]
  have l2 : QThm S (clsEq ((α ∩ β) ∪ (α − γ)) ((α − γ) ∪ ((α ∩ β) ∩ γ))) :=
    show (α ∩ β) ∪ (α − γ) ≐ (α − γ) ∪ ((α ∩ β) ∩ γ) from
    calc (α ∩ β) ∪ (α − γ)
        ≐ ((α ∩ β) ∩ γ) ∪ ((α − γ) ∩ β) ∪ (α − γ) := QThm.mp l1 (q22_551 _ _ _)      -- [✱22·551]
      _ ≐ ((α ∩ β) ∩ γ) ∪ (((α − γ) ∩ β) ∪ (α − γ)) := q22_7 _ _ _
      _ ≐ ((α ∩ β) ∩ γ) ∪ ((α − γ) ∪ ((α − γ) ∩ β)) :=
          QThm.mp (q22_57 _ _) (qclsEqCongr (fun X => ((α ∩ β) ∩ γ) ∪ X) _ _ (by cls_expr))
      _ ≐ ((α ∩ β) ∩ γ) ∪ (α − γ) :=
          QThm.mp (q22_63 (α − γ) β) (qclsEqCongr (fun X => ((α ∩ β) ∩ γ) ∪ X) _ _ (by cls_expr))  -- [✱22·63]
      _ ≐ (α − γ) ∪ ((α ∩ β) ∩ γ) := q22_57 _ _                                  -- [✱22·57]
  qclsEqSymm <|
    show (α ∩ β) ∪ (α − γ) ∪ (β ∩ γ) ≐ (α − γ) ∪ (β ∩ γ) from
    calc (α ∩ β) ∪ (α − γ) ∪ (β ∩ γ)
        ≐ (α − γ) ∪ ((α ∩ β) ∩ γ) ∪ (β ∩ γ) := QThm.mp l2 (q22_551 _ _ _)           -- [✱22·551]
      _ ≐ (α − γ) ∪ (((α ∩ β) ∩ γ) ∪ (β ∩ γ)) := q22_7 _ _ _
      _ ≐ (α − γ) ∪ ((α ∩ (β ∩ γ)) ∪ (β ∩ γ)) :=
          QThm.mp (q22_52 α β γ) (qclsEqCongr (fun X => (α − γ) ∪ (X ∪ (β ∩ γ))) _ _ (by cls_expr))
      _ ≐ (α − γ) ∪ (((β ∩ γ) ∩ α) ∪ (β ∩ γ)) :=
          QThm.mp (q22_51 α (β ∩ γ)) (qclsEqCongr (fun X => (α − γ) ∪ (X ∪ (β ∩ γ))) _ _ (by cls_expr))
      _ ≐ (α − γ) ∪ ((β ∩ γ) ∪ ((β ∩ γ) ∩ α)) :=
          QThm.mp (q22_57 _ _) (qclsEqCongr (fun X => (α − γ) ∪ X) _ _ (by cls_expr))
      _ ≐ (α − γ) ∪ (β ∩ γ) :=
          QThm.mp (q22_63 (β ∩ γ) α) (qclsEqCongr (fun X => (α − γ) ∪ X) _ _ (by cls_expr))       -- [✱22·63]

/-- ✱24·44 `⊢ . (α ∪ γ) ∩ (β ∪ −γ) = (α ∩ −γ) ∪ (β ∩ γ)` [✱24·431·432], joined by ✱20·24. -/
theorem q24_44 [Reducibility S] (α β γ : V a → QF V) :
    QThm S (clsEq ((α ∪ γ) ∩ (β ∪ −γ)) ((α ∩ −γ) ∪ (β ∩ γ))) :=
  QThm.mp (qandI (q24_431 α β γ) (q24_432 α β γ)) (q20_24 _ _ _)                   -- ✱24·431·432

/-- ✱24·45 `⊢ : (α ∩ γ) ∪ (β − γ) = Λ . ≡ . β ⊂ γ . γ ⊂ −α`, as printed (p. 236; the transcription has
    `β ⊂ γ ⊂ . γ ⊂ −α`, the text audit's Vol I list, entry 15). "[✱24·3·311]": ✱24·311 at γ, α has γ ∩ α
    (✱22·51), and the two are joined by ✱4·38; PM's last line has the factors in the other order (✱4·3). -/
theorem q24_45 [Reducibility S] (α β γ : V a → QF V) :
    QThm S (iff (clsEq ((α ∩ γ) ∪ (β − γ)) Λ) (QF.and (β ⊂ γ) (γ ⊂ −α))) :=
  have h311 : QThm S (iff (clsEq (α ∩ γ) Λ) (γ ⊂ −α)) :=
    qiffTrans (QThm.mp (q22_51 α γ) (qclsEqL _ _ Λ)) (qiffSymm (q24_311 γ α))
  calc clsEq ((α ∩ γ) ∪ (β − γ)) Λ
      ≡ QF.and (clsEq (α ∩ γ) Λ) (clsEq (β − γ) Λ) := q24_32 _ _                    -- ✱24·32
    _ ≡ QF.and (γ ⊂ −α) (β ⊂ γ) := QThm.mp (qandI h311 (qiffSymm (q24_3 β γ))) (QL.t4_38 _ _ _ _)  -- [✱24·3·311]
    _ ≡ QF.and (β ⊂ γ) (γ ⊂ −α) := QL.t4_3 _ _

/-- ✱24·46 `⊢ : (α ∩ γ) ∪ (β − γ) = Λ . ⊃ . α ∩ β = Λ` -/
theorem q24_46 [Reducibility S] (α β γ : V a → QF V) :
    QThm S (imp (clsEq ((α ∩ γ) ∪ (β − γ)) Λ) (clsEq (α ∩ β) Λ)) :=
  calc clsEq ((α ∩ γ) ∪ (β − γ)) Λ
      ⊃ (β ⊂ −α) := qsyl (qiffMp (q24_45 α β γ)) (q22_44 β γ (−α))                  -- ✱24·45.✱22·44
    _ ⊃ (α ⊂ −β) := qiffMpr (q22_811 α β)                                         -- [✱22·811]
    _ ⊃ clsEq (α ∩ β) Λ := qiffMp (q24_311 α β)                                   -- [✱24·311]

/-- ✱24·47 `⊢ : α ∩ β = Λ . α ∪ β = γ . ≡ . α ⊂ γ . β = γ − α`. In (1), ✱24·311 at β, α has β ∩ α (✱22·51);
    ✱22·59 and ✱24·43 (at γ, α, β) are joined by ✱4·38, and (1).(2) by ✱4·38. "[✱4·3]" is ✱4·3 with ✱4·32
    (and ✱4·36). -/
theorem q24_47 [Reducibility S] (α β γ : V a → QF V) :
    QThm S (iff (QF.and (clsEq (α ∩ β) Λ) (clsEq (α ∪ β) γ)) (QF.and (α ⊂ γ) (clsEq β (γ − α)))) :=
  have h1 : QThm S (iff (clsEq (α ∩ β) Λ) (β ⊂ −α)) :=
    qiffTrans (QThm.mp (q22_51 α β) (qclsEqL _ _ Λ)) (qiffSymm (q24_311 β α))      -- ✱24·311 (1)
  have h2 : QThm S (iff (clsEq (α ∪ β) γ) (QF.and (QF.and (α ⊂ γ) (β ⊂ γ)) (γ − α ⊂ β))) :=
    calc clsEq (α ∪ β) γ
        ≡ QF.and (α ∪ β ⊂ γ) (γ ⊂ α ∪ β) := qiffSymm (q22_41 _ _)                  -- ✱22·41
      _ ≡ QF.and (QF.and (α ⊂ γ) (β ⊂ γ)) (γ − α ⊂ β) :=
          QThm.mp (qandI (qiffSymm (q22_59 α β γ)) (qiffSymm (q24_43 γ α β))) (QL.t4_38 _ _ _ _)  -- [✱22·59.✱24·43] (2)
  calc QF.and (clsEq (α ∩ β) Λ) (clsEq (α ∪ β) γ)
      ≡ QF.and (β ⊂ −α) (QF.and (QF.and (α ⊂ γ) (β ⊂ γ)) (γ − α ⊂ β)) :=
        QThm.mp (qandI h1 h2) (QL.t4_38 _ _ _ _)                                   -- (1).(2)
    _ ≡ QF.and (β ⊂ −α) (QF.and (α ⊂ γ) (QF.and (β ⊂ γ) (γ − α ⊂ β))) := qandCongrR _ (QL.t4_32 _ _ _)
    _ ≡ QF.and (α ⊂ γ) (QF.and (β ⊂ −α) (QF.and (β ⊂ γ) (γ − α ⊂ β))) := qandPerm _ _ _
    _ ≡ QF.and (α ⊂ γ) (QF.and (QF.and (β ⊂ −α) (β ⊂ γ)) (γ − α ⊂ β)) :=
        qandCongrR _ (qiffSymm (QL.t4_32 _ _ _))
    _ ≡ QF.and (α ⊂ γ) (QF.and (QF.and (β ⊂ γ) (β ⊂ −α)) (γ − α ⊂ β)) :=
        qandCongrR _ (qandCongrL _ (QL.t4_3 _ _))                                  -- [✱4·3]
    _ ≡ QF.and (α ⊂ γ) (QF.and (β ⊂ γ − α) (γ − α ⊂ β)) :=
        qandCongrR _ (qandCongrL _ (q22_45 β γ (−α)))                              -- [✱22·45]
    _ ≡ QF.and (α ⊂ γ) (clsEq β (γ − α)) := qandCongrR _ (q22_41 β (γ − α))         -- [✱22·41]

/-- The hypothesis of ✱24·48: ξ ⊂ α . ξ' ⊂ α . η ⊂ β . η' ⊂ β . α ∩ β = Λ, a product grouped from the left. -/
@[reducible] def hyp24_48 (α β ξ ξ' η η' : V a → QF V) : QF V :=
  QF.and (QF.and (QF.and (QF.and (ξ ⊂ α) (ξ' ⊂ α)) (η ⊂ β)) (η' ⊂ β)) (clsEq (α ∩ β) Λ)

/-- Line (8) of ✱24·48, for any classes: `Hp . ⊃ : ξ ∪ η = ξ' ∪ η' . ⊃ . ξ = ξ'`. (2): ✱22·481, and "[✱22·68]"
    with the common factor second (`qclsDistribRight`) in both members (✱20·22·23, `qclsEqL`, `qclsEqR`).
    (3): ✱22·621 twice, joined by ✱3·47. (4): ✱22·48 gives η ∩ α ⊂ β ∩ α, written α ∩ β by ✱22·51 and ✱22·55;
    "[✱22·55]" uses α ∩ β = Λ (✱3·35, `qimpMpH`). (6), (7): the two identities joined by ✱22·73, then ✱24·24.
    (8): ✱20·22 under Hp, with ✱20·21, and Exp (✱3·3). The factors of Hp are taken by Simp (✱3·26, ✱3·27,
    Comp ✱3·43). -/
theorem qline24_48 [Reducibility S] (α β ξ ξ' η η' : V a → QF V) :
    QThm S (imp (hyp24_48 α β ξ ξ' η η') (imp (clsEq (ξ ∪ η) (ξ' ∪ η')) (clsEq ξ ξ'))) :=
  let H := hyp24_48 α β ξ ξ' η η'
  have p12 : QThm S (imp H (QF.and (ξ ⊂ α) (ξ' ⊂ α))) :=
    qsyl (QL.t3_26 _ _) (qsyl (QL.t3_26 _ _) (QL.t3_26 _ _))
  have pη : QThm S (imp H (η ⊂ β)) := qsyl (QL.t3_26 _ _) (qsyl (QL.t3_26 _ _) (QL.t3_27 _ _))
  have pη' : QThm S (imp H (η' ⊂ β)) := qsyl (QL.t3_26 _ _) (QL.t3_27 _ _)
  have pΛ : QThm S (imp H (clsEq (α ∩ β) Λ)) := QL.t3_27 _ _
  have h2 : QThm S (imp (clsEq (ξ ∪ η) (ξ' ∪ η')) (clsEq ((ξ ∩ α) ∪ (η ∩ α)) ((ξ' ∩ α) ∪ (η' ∩ α)))) :=
    calc clsEq (ξ ∪ η) (ξ' ∪ η')
        ⊃ clsEq ((ξ ∪ η) ∩ α) ((ξ' ∪ η') ∩ α) := q22_481 _ _ α                      -- ✱22·481
      _ ≡ clsEq ((ξ ∩ α) ∪ (η ∩ α)) ((ξ' ∪ η') ∩ α) := QThm.mp (qclsDistribRight ξ η α) (qclsEqL _ _ _)
      _ ≡ clsEq ((ξ ∩ α) ∪ (η ∩ α)) ((ξ' ∩ α) ∪ (η' ∩ α)) :=
          QThm.mp (qclsDistribRight ξ' η' α) (qclsEqR _ _ _)                       -- [✱22·68] (2)
  have h3 : QThm S (imp (QF.and (ξ ⊂ α) (ξ' ⊂ α)) (QF.and (clsEq (ξ ∩ α) ξ) (clsEq (ξ' ∩ α) ξ'))) :=
    QThm.mp (qandI (qiffMp (q22_621 ξ α)) (qiffMp (q22_621 ξ' α))) (QL.t3_47 _ _ _ _)  -- ✱22·621 [✱3·47] (3)
  have h4 : ∀ η : V a → QF V, QThm S (imp (QF.and (η ⊂ β) (clsEq (α ∩ β) Λ)) (clsEq (η ∩ α) Λ)) := fun η =>
    have k : QThm S (imp (η ⊂ β) (η ∩ α ⊂ α ∩ β)) :=
      qsyl (q22_48 η β α) (qiffMp (QThm.mp (q22_51 β α) (q22_55 _ _ (η ∩ α))))     -- ✱22·48
    have k2 : QThm S (imp (QF.and (η ⊂ β) (clsEq (α ∩ β) Λ)) (η ∩ α ⊂ Λ)) :=
      qimpMpH (qsyl (QL.t3_26 _ _) k) (qsyl (QL.t3_27 _ _) (qsyl (q22_55 _ _ _) (QL.t3_26 _ _)))  -- [✱22·55]
    qsyl k2 (qiffMpr (q24_13 _))                                                  -- [✱24·13] (4), (5)
  have h6 : QThm S (imp H (clsEq ((ξ ∩ α) ∪ (η ∩ α)) ξ)) :=
    show (ξ ∩ α) ∪ (η ∩ α) ≐[H] ξ from
    calc (ξ ∩ α) ∪ (η ∩ α)
        ≐[H] ξ ∪ Λ :=
          qsyl (qcomp (qsyl p12 (qsyl h3 (QL.t3_26 _ _))) (qsyl (qcomp pη pΛ) (h4 η))) (q22_73 _ _ _ _)  -- (3).(4)
      _ ≐ ξ := q24_24 ξ                                                           -- [✱24·24] (6)
  have h7 : QThm S (imp H (clsEq ((ξ' ∩ α) ∪ (η' ∩ α)) ξ')) :=
    show (ξ' ∩ α) ∪ (η' ∩ α) ≐[H] ξ' from
    calc (ξ' ∩ α) ∪ (η' ∩ α)
        ≐[H] ξ' ∪ Λ :=
          qsyl (qcomp (qsyl p12 (qsyl h3 (QL.t3_27 _ _))) (qsyl (qcomp pη' pΛ) (h4 η'))) (q22_73 _ _ _ _)  -- (3).(5)
      _ ≐ ξ' := q24_24 ξ'                                                         -- [✱24·24] (7)
  let H2 := QF.and H (clsEq (ξ ∪ η) (ξ' ∪ η'))
  have h8 : QThm S (imp H2 (clsEq ξ ξ')) :=
    show ξ ≐[H2] ξ' from
    calc ξ
        ≐[H2] (ξ ∩ α) ∪ (η ∩ α) := qsyl (QL.t3_26 _ _) (qsyl h6 (qiffMp (q20_21 _ _)))  -- (6)
      _ ≐[H2] (ξ' ∩ α) ∪ (η' ∩ α) := qsyl (QL.t3_27 _ _) h2                        -- (2)
      _ ≐[H2] ξ' := qsyl (QL.t3_26 _ _) h7                                         -- (7)
  QThm.mp h8 (QL.t3_3 _ _ _)                                                       -- (2).(6).(7) (8)

/-- ✱24·48 `⊢ :. ξ ⊂ α . ξ' ⊂ α . η ⊂ β . η' ⊂ β . α ∩ β = Λ . ⊃ : ξ ∪ η = ξ' ∪ η' . ≡ . ξ = ξ' . η = η'`, Hp
    grouped from the left. (8) is `qline24_48`; "Similarly" (9) is (8) for η, η', ξ, ξ', β, α, its Hp got from
    this one by Simp and Comp (with ✱22·51 for β ∩ α) and its ξ ∪ η, ξ' ∪ η' commuted by ✱22·57 (✱20·22·23,
    Syll ✱2·06). (1).(8).(9): the halves joined by ✱3·43, (1) put under Hp by ✱2·02. -/
theorem q24_48 [Reducibility S] (α β ξ ξ' η η' : V a → QF V) :
    QThm S (imp (QF.and (QF.and (QF.and (QF.and (ξ ⊂ α) (ξ' ⊂ α)) (η ⊂ β)) (η' ⊂ β)) (clsEq (α ∩ β) Λ))
      (iff (clsEq (ξ ∪ η) (ξ' ∪ η')) (QF.and (clsEq ξ ξ') (clsEq η η')))) :=
  let H := hyp24_48 α β ξ ξ' η η'
  let E := clsEq (ξ ∪ η) (ξ' ∪ η')
  have h1 : QThm S (imp (QF.and (clsEq ξ ξ') (clsEq η η')) E) := q22_73 ξ η ξ' η'    -- ✱22·73 (1)
  have h8 : QThm S (imp H (imp E (clsEq ξ ξ'))) := qline24_48 α β ξ ξ' η η'          -- (8)
  have hH' : QThm S (imp H (hyp24_48 β α η η' ξ ξ')) :=
    qcomp (qcomp (qcomp (qcomp (qsyl (QL.t3_26 _ _) (qsyl (QL.t3_26 _ _) (QL.t3_27 _ _)))
      (qsyl (QL.t3_26 _ _) (QL.t3_27 _ _)))
      (qsyl (QL.t3_26 _ _) (qsyl (QL.t3_26 _ _) (qsyl (QL.t3_26 _ _) (QL.t3_26 _ _)))))
      (qsyl (QL.t3_26 _ _) (qsyl (QL.t3_26 _ _) (qsyl (QL.t3_26 _ _) (QL.t3_27 _ _)))))
      (qsyl (QL.t3_27 _ _) (qiffMp (QThm.mp (q22_51 α β) (qclsEqL _ _ Λ))))
  have hsw : QThm S (imp E (clsEq (η ∪ ξ) (η' ∪ ξ'))) :=
    qsyl (qiffMp (QThm.mp (q22_57 ξ η) (qclsEqL _ _ _))) (qiffMp (QThm.mp (q22_57 ξ' η') (qclsEqR _ _ _)))
  have h9 : QThm S (imp H (imp E (clsEq η η'))) :=
    qsyl hH' (qsyl (qline24_48 β α η η' ξ ξ') (QThm.mp hsw (QL.t2_06 _ _ _)))       -- Similarly (9)
  qcomp (qsyl (qcomp h8 h9) (QL.t3_43 _ _ _)) (QThm.mp h1 (QL.t2_02 H _))          -- (1).(8).(9)

/-- ✱24·481 `⊢ :. α ∩ β = Λ . α ∩ γ = Λ . ⊃ : α ∪ β = α ∪ γ . ≡ . β = γ`. (1) is ✱24·48 at α, −α, α, α, β, γ.
    In (2), the asserted factors α ⊂ α (✱22·42) and α − α = Λ (✱24·21) are dropped (✱4·73, ✱4·32, and ✱3·2,
    ✱3·27, `qand_true_left`), and ✱24·311 at β, α and γ, α has β ∩ α, γ ∩ α (✱22·51), joined by ✱4·38. (3):
    ✱4·73 has α = α second (✱4·3). (1).(2).(3): Hp gives (1)'s Hp by (2), and (3) replaces the second member
    (✱4·22, `qimpIffTransR`). -/
theorem q24_481 [Reducibility S] (α β γ : V a → QF V) :
    QThm S (imp (QF.and (clsEq (α ∩ β) Λ) (clsEq (α ∩ γ) Λ))
      (iff (clsEq (α ∪ β) (α ∪ γ)) (clsEq β γ))) :=
  have h1 := q24_48 α (−α) α α β γ                                               -- ✱24·48 (1)
  have e : ∀ δ : V a → QF V, QThm S (iff (δ ⊂ −α) (clsEq (α ∩ δ) Λ)) := fun δ =>
    qiffTrans (q24_311 δ α) (QThm.mp (q22_51 δ α) (qclsEqL _ _ Λ))
  have h2 : QThm S (iff (hyp24_48 α (−α) α α β γ) (QF.and (clsEq (α ∩ β) Λ) (clsEq (α ∩ γ) Λ))) :=
    calc hyp24_48 α (−α) α α β γ
        ≡ QF.and (QF.and (QF.and (α ⊂ α) (α ⊂ α)) (β ⊂ −α)) (γ ⊂ −α) :=
          qiffSymm (QThm.mp (q24_21 α) (QL.t4_73 _ _))
      _ ≡ QF.and (QF.and (α ⊂ α) (α ⊂ α)) (QF.and (β ⊂ −α) (γ ⊂ −α)) := QL.t4_32 _ _ _
      _ ≡ QF.and (β ⊂ −α) (γ ⊂ −α) := qand_true_left (qandI (q22_42 α) (q22_42 α))  -- ✱22·42.✱24·21
      _ ≡ QF.and (clsEq (α ∩ β) Λ) (clsEq (α ∩ γ) Λ) :=
          QThm.mp (qandI (e β) (e γ)) (QL.t4_38 _ _ _ _)                           -- [✱24·311] (2)
  have h3 : QThm S (iff (QF.and (clsEq α α) (clsEq β γ)) (clsEq β γ)) :=
    qiffSymm (qiffTrans (QThm.mp (q20_2 α) (QL.t4_73 _ _)) (QL.t4_3 _ _))           -- ✱20·2.✱4·73 (3)
  qsyl (qiffMpr h2) (qimpIffTransR h1 h3)                                          -- (1).(2).(3)

/-- ✱24·482 `⊢ :. ξ ⊂ α . η ⊂ β . α ∩ β = Λ . ⊃ : ξ ∪ η = α ∪ β . ≡ . ξ = α . η = β` [✱24·48 (α, β / ξ', η') .
    ✱22·42]: ✱24·48's Hp from this one by Simp and Comp, with α ⊂ α, β ⊂ β (✱22·42) put under it by ✱2·02. -/
theorem q24_482 [Reducibility S] (α β ξ η : V a → QF V) :
    QThm S (imp (QF.and (QF.and (ξ ⊂ α) (η ⊂ β)) (clsEq (α ∩ β) Λ))
      (iff (clsEq (ξ ∪ η) (α ∪ β)) (QF.and (clsEq ξ α) (clsEq η β)))) :=
  let H := QF.and (QF.and (ξ ⊂ α) (η ⊂ β)) (clsEq (α ∩ β) Λ)
  have hH : QThm S (imp H (hyp24_48 α β ξ α η β)) :=
    qcomp (qcomp (qcomp (qcomp (qsyl (QL.t3_26 _ _) (QL.t3_26 _ _)) (QThm.mp (q22_42 α) (QL.t2_02 H _)))
      (qsyl (QL.t3_26 _ _) (QL.t3_27 _ _))) (QThm.mp (q22_42 β) (QL.t2_02 H _))) (QL.t3_27 _ _)  -- ✱22·42
  qsyl hH (q24_48 α β ξ α η β)                                                     -- ✱24·48 (α, β / ξ', η')

/-- ✱24·49 `⊢ :. α ∩ β = Λ . ⊃ : α ⊂ β ∪ γ . ≡ . α ⊂ γ`. ✱22·621's α ∩ (β ∪ γ) = α and α ∩ γ = α are turned by
    ✱20·21; (1) puts (α ∩ β) ∪ (α ∩ γ) for α ∩ (β ∪ γ) by ✱22·68 (with ✱20·22, `qclsEqR`); in (2), Hp is put for
    α ∩ β (✱22·551) and "✱24·24" has the sum in the other order (✱22·57). -/
theorem q24_49 [Reducibility S] (α β γ : V a → QF V) :
    QThm S (imp (clsEq (α ∩ β) Λ) (iff (α ⊂ β ∪ γ) (α ⊂ γ))) :=
  have h2 : QThm S (imp (clsEq (α ∩ β) Λ) (clsEq ((α ∩ β) ∪ (α ∩ γ)) (α ∩ γ))) :=
    show (α ∩ β) ∪ (α ∩ γ) ≐[clsEq (α ∩ β) Λ] α ∩ γ from
    calc (α ∩ β) ∪ (α ∩ γ)
        ≐[clsEq (α ∩ β) Λ] Λ ∪ (α ∩ γ) := q22_551 _ _ _
      _ ≐ (α ∩ γ) ∪ Λ := q22_57 _ _
      _ ≐ α ∩ γ := q24_24 _                                                       -- ✱24·24 (2)
  calc (α ⊂ β ∪ γ)
      ≡ clsEq (α ∩ (β ∪ γ)) α := q22_621 _ _                                      -- ✱22·621
    _ ≡ clsEq α (α ∩ (β ∪ γ)) := q20_21 _ _
    _ ≡ clsEq α ((α ∩ β) ∪ (α ∩ γ)) := QThm.mp (qclsEqSymm (q22_68 α β γ)) (qclsEqR _ _ α)  -- [✱22·68] (1)
    _ ≡[clsEq (α ∩ β) Λ] clsEq α (α ∩ γ) := qsyl h2 (qclsEqR _ _ α)                -- (1).(2)
    _ ≡ clsEq (α ∩ γ) α := q20_21 _ _
    _ ≡ (α ⊂ γ) := qiffSymm (q22_621 α γ)                                         -- [✱22·621]

/-- ✱24·491 `⊢ : β ∩ γ = Λ . α ⊂ β ∪ γ . ⊃ . α − β = α ∩ γ . α − γ = α ∩ β . α = (α − β) ∪ (α − γ)`, the
    conclusion grouped from the left. "[✱24·4]": α ∩ (β ∪ γ) − γ is α ∩ {(β ∪ γ) − γ} (✱22·52), and ✱24·4 at β, γ
    gives (β ∪ γ) − γ = β from Hp (its two halves by ✱3·26, ✱3·27); "Similarly" (2) uses its first half. In (3),
    (1).(2) are joined by ✱22·73, and ✱22·621 needs γ ∪ β written β ∪ γ (✱22·57). Each replacement inside a class
    is `qclsEqCongr`; Hp's factors are taken by ✱3·26, ✱3·27. -/
theorem q24_491 [Reducibility S] (α β γ : V a → QF V) :
    QThm S (imp (QF.and (clsEq (β ∩ γ) Λ) (α ⊂ β ∪ γ))
      (QF.and (QF.and (clsEq (α − β) (α ∩ γ)) (clsEq (α − γ) (α ∩ β))) (clsEq α ((α − β) ∪ (α − γ))))) :=
  let H := QF.and (clsEq (β ∩ γ) Λ) (α ⊂ β ∪ γ)
  have hα : QThm S (imp H (clsEq α (α ∩ (β ∪ γ)))) :=
    qsyl (QL.t3_27 _ _) (qsyl (qiffMp (q22_621 α (β ∪ γ))) (qiffMp (q20_21 _ _)))   -- ✱22·621
  have h4 := q24_4 β γ
  have hB : QThm S (imp H (clsEq ((β ∪ γ) − β) γ)) :=
    qsyl (QL.t3_26 _ _) (qiffMp (QThm.mp h4 (QL.t3_26 _ _)))
  have hC : QThm S (imp H (clsEq ((β ∪ γ) − γ) β)) := qsyl hB (qiffMp (QThm.mp h4 (QL.t3_27 _ _)))
  have h1 : QThm S (imp H (clsEq (α − γ) (α ∩ β))) :=
    show α − γ ≐[H] α ∩ β from
    calc α − γ
        ≐[H] (α ∩ (β ∪ γ)) − γ := qsyl hα (q22_481 _ _ (−γ))                       -- [✱22·481]
      _ ≐ α ∩ ((β ∪ γ) − γ) := q22_52 _ _ _
      _ ≐[H] α ∩ β := qsyl hC (qclsEqCongr (fun X => α ∩ X) _ _ (by cls_expr))                     -- [✱24·4] (1)
  have h2 : QThm S (imp H (clsEq (α − β) (α ∩ γ))) :=
    show α − β ≐[H] α ∩ γ from
    calc α − β
        ≐[H] (α ∩ (β ∪ γ)) − β := qsyl hα (q22_481 _ _ (−β))
      _ ≐ α ∩ ((β ∪ γ) − β) := q22_52 _ _ _
      _ ≐[H] α ∩ γ := qsyl hB (qclsEqCongr (fun X => α ∩ X) _ _ (by cls_expr))                     -- Similarly (2)
  have h3 : QThm S (imp H (clsEq ((α − β) ∪ (α − γ)) α)) :=
    show (α − β) ∪ (α − γ) ≐[H] α from
    calc (α − β) ∪ (α − γ)
        ≐[H] (α ∩ γ) ∪ (α ∩ β) := qsyl (qcomp h2 h1) (q22_73 _ _ _ _)               -- (1).(2)
      _ ≐ α ∩ (γ ∪ β) := q22_68 _ _ _                                             -- [✱22·68]
      _ ≐ α ∩ (β ∪ γ) := QThm.mp (q22_57 γ β) (qclsEqCongr (fun X => α ∩ X) _ _ (by cls_expr))
      _ ≐[H] α := qsyl (QL.t3_27 _ _) (qiffMp (q22_621 α (β ∪ γ)))                  -- [✱22·621] (3)
  qcomp (qcomp h2 h1) (qsyl h3 (qiffMp (q20_21 _ _)))                              -- (1).(2).(3)

/-- ✱24·492 `⊢ : β ⊂ α . α − β = γ . ⊃ . α − γ = β`. "[✱22·481]" puts α − β for γ in α − γ (Hp turned by
    ✱20·21; `qclsEqCongr`). "[✱22·8·86]": −(α − β) is −(−(−α) ∩ −β) (✱22·8), which is −α ∪ β by ✱22·86.
    "[✱22·8·9]": α ∩ (−α ∪ β) is (β ∪ −α) − (−α) by ✱22·51, ✱22·8, ✱22·57, which is β − (−α) by ✱22·9, and
    β ∩ α by ✱22·8 (and ✱22·51). "[✱22·621]" gives β ∩ α = β (✱22·51). -/
theorem q24_492 [Reducibility S] (α β γ : V a → QF V) :
    QThm S (imp (QF.and (β ⊂ α) (clsEq (α − β) γ)) (clsEq (α − γ) β)) :=
  let H := QF.and (β ⊂ α) (clsEq (α − β) γ)
  have hN : QThm S (clsEq (−(α − β)) (−α ∪ β)) :=
    show −(α − β) ≐ −α ∪ β from
    calc −(α − β)
        ≐ −(−(−α) ∩ −β) := QThm.mp (qclsEqSymm (q22_8 α)) (qclsEqCongr (fun X => −(X ∩ −β)) _ _ (by cls_expr))
      _ ≐ −α ∪ β := q22_86 (−α) β                                                 -- ✱22·86
  show α − γ ≐[H] β from
  calc α − γ
      ≐[H] α − (α − β) :=
        qsyl (QL.t3_27 _ _) (qsyl (qiffMp (q20_21 _ _)) (qclsEqCongr (fun X => α − X) _ _ (by cls_expr)))  -- ✱22·481
    _ ≐ α ∩ (−α ∪ β) := QThm.mp hN (qclsEqCongr (fun X => α ∩ X) _ _ (by cls_expr))               -- [✱22·8·86]
    _ ≐ (−α ∪ β) ∩ α := q22_51 _ _
    _ ≐ (−α ∪ β) ∩ −(−α) := QThm.mp (qclsEqSymm (q22_8 α)) (qclsEqCongr (fun X => (−α ∪ β) ∩ X) _ _ (by cls_expr))
    _ ≐ (β ∪ −α) − (−α) := QThm.mp (q22_57 (−α) β) (qclsEqCongr (fun X => X − (−α)) _ _ (by cls_expr))
    _ ≐ β − (−α) := q22_9 β (−α)
    _ ≐ β ∩ α := QThm.mp (q22_8 α) (qclsEqCongr (fun X => β ∩ X) _ _ (by cls_expr))
    _ ≐ α ∩ β := q22_51 _ _                                                       -- [✱22·8·9]
    _ ≐ β ∩ α := q22_51 _ _
    _ ≐[H] β := qsyl (QL.t3_26 _ _) (qiffMp (q22_621 β α))                          -- [✱22·621]

/-- ✱24·493 `⊢ : β ∩ γ = Λ . ⊃ . α = (α − β) ∪ (α − γ)`. "✱22·84 . ✱24·17": ✱24·17 at −(β ∩ γ), whose −(−(β ∩ γ))
    is β ∩ γ by ✱22·8, and ✱22·84 (each identity replaced in its first member, ✱20·22·23, `qclsEqL`).
    "[✱24·26]": α = α ∩ V (✱20·21), V replaced inside the class (`qclsEqCongr`). -/
theorem q24_493 [Reducibility S] (α β γ : V a → QF V) :
    QThm S (imp (clsEq (β ∩ γ) Λ) (clsEq α ((α − β) ∪ (α − γ)))) :=
  have hV : QThm S (imp (clsEq (β ∩ γ) Λ) (clsEq (−β ∪ −γ) 𝐕)) :=
    calc clsEq (β ∩ γ) Λ
        ⊃ clsEq (−(−(β ∩ γ))) Λ := qiffMpr (QThm.mp (q22_8 _) (qclsEqL _ _ Λ))
      _ ⊃ clsEq (−(β ∩ γ)) 𝐕 := qiffMpr (q24_17 _)                                  -- ✱24·17
      _ ⊃ clsEq (−β ∪ −γ) 𝐕 := qiffMp (QThm.mp (q22_84 β γ) (qclsEqL _ _ 𝐕))         -- ✱22·84
  show α ≐[clsEq (β ∩ γ) Λ] (α − β) ∪ (α − γ) from
  calc α
      ≐ α ∩ 𝐕 := qclsEqSymm (q24_26 α)
    _ ≐[clsEq (β ∩ γ) Λ] α ∩ (−β ∪ −γ) :=
        qsyl hV (qsyl (qiffMp (q20_21 _ _)) (qclsEqCongr (fun X => α ∩ X) _ _ (by cls_expr)))     -- [✱24·26]
    _ ≐ (α − β) ∪ (α − γ) := qclsEqSymm (q22_68 α (−β) (−γ))                        -- [✱22·68]

/-- ✱24·494 `⊢ : ξ ⊂ α . η ⊂ β . α ∩ β = Λ . ⊃ . (ξ ∪ η) − α = η . (ξ ∪ η) − β = ξ`. ✱24·311 at β, α has β ∩ α
    (✱22·51); (3) is ✱22·68 with the common factor second (`qclsDistribRight`); in (4), (1) and (2) are put in
    the sum by ✱22·73, and ✱24·24 has it in the other order (✱22·57). "Similarly" (5) is written out, with
    ✱24·3, ✱24·311, ✱22·44 and ✱22·621 at η, ξ, β. Hp's factors are taken by ✱3·26, ✱3·27. -/
theorem q24_494 [Reducibility S] (α β ξ η : V a → QF V) :
    QThm S (imp (QF.and (QF.and (ξ ⊂ α) (η ⊂ β)) (clsEq (α ∩ β) Λ))
      (QF.and (clsEq ((ξ ∪ η) − α) η) (clsEq ((ξ ∪ η) − β) ξ))) :=
  let H := QF.and (QF.and (ξ ⊂ α) (η ⊂ β)) (clsEq (α ∩ β) Λ)
  have pξ : QThm S (imp H (ξ ⊂ α)) := qsyl (QL.t3_26 _ _) (QL.t3_26 _ _)
  have pη : QThm S (imp H (η ⊂ β)) := qsyl (QL.t3_26 _ _) (QL.t3_27 _ _)
  have pΛ : QThm S (imp H (clsEq (α ∩ β) Λ)) := QL.t3_27 _ _
  have h1 : QThm S (imp H (clsEq (ξ − α) Λ)) := qsyl pξ (qiffMp (q24_3 ξ α))       -- ✱24·3 (1)
  have hβ : QThm S (imp H (β ⊂ −α)) :=
    qsyl pΛ (qiffMpr (qiffTrans (q24_311 β α) (QThm.mp (q22_51 β α) (qclsEqL _ _ Λ))))  -- ✱24·311
  have hη : QThm S (imp H (η ⊂ −α)) := qsyl (qcomp pη hβ) (q22_44 η β (−α))       -- [✱22·44]
  have h2 : QThm S (imp H (clsEq (η − α) η)) := qsyl hη (qiffMp (q22_621 η (−α)))  -- [✱22·621] (2)
  have h4 : QThm S (imp H (clsEq ((ξ ∪ η) − α) η)) :=
    show (ξ ∪ η) − α ≐[H] η from
    calc (ξ ∪ η) − α
        ≐ (ξ − α) ∪ (η − α) := qclsDistribRight ξ η (−α)                          -- ✱22·68 (3)
      _ ≐[H] Λ ∪ η := qsyl (qcomp h1 h2) (q22_73 _ _ _ _)                          -- (1).(2)
      _ ≐ η ∪ Λ := q22_57 _ _
      _ ≐ η := q24_24 η                                                           -- ✱24·24 (4)
  have g1 : QThm S (imp H (clsEq (η − β) Λ)) := qsyl pη (qiffMp (q24_3 η β))
  have gα : QThm S (imp H (α ⊂ −β)) := qsyl pΛ (qiffMpr (q24_311 α β))
  have gξ : QThm S (imp H (ξ ⊂ −β)) := qsyl (qcomp pξ gα) (q22_44 ξ α (−β))
  have g2 : QThm S (imp H (clsEq (ξ − β) ξ)) := qsyl gξ (qiffMp (q22_621 ξ (−β)))
  have h5 : QThm S (imp H (clsEq ((ξ ∪ η) − β) ξ)) :=
    show (ξ ∪ η) − β ≐[H] ξ from
    calc (ξ ∪ η) − β
        ≐ (ξ − β) ∪ (η − β) := qclsDistribRight ξ η (−β)
      _ ≐[H] ξ ∪ Λ := qsyl (qcomp g2 g1) (q22_73 _ _ _ _)
      _ ≐ ξ := q24_24 ξ                                                           -- Similarly (5)
  qcomp h4 h5                                                                     -- (4).(5)

/-- ✱24·495 `⊢ : α ∩ γ = Λ . ⊃ . (α ∪ γ) − (β ∪ γ) = α − β`. "✱22·87·68": −(β ∪ γ) is −β ∩ −γ (✱22·87 turned by
    ✱20·21), and ✱22·68 with the common factor second (`qclsDistribRight`), each product regrouped by ✱22·52
    (both at once by ✱22·73). "[✱24·21]": (γ − β) − γ is −β ∩ (γ ∩ −γ) (✱22·51, ✱22·52), so −β ∩ Λ, which is Λ by
    ✱24·23, dropped by ✱24·24. (1).(2): (α − β) − γ is (α − γ) − β (✱22·52, ✱22·51), and (2) is put for α − γ
    (✱22·481). Each replacement inside a class is `qclsEqCongr`. -/
theorem q24_495 [Reducibility S] (α β γ : V a → QF V) :
    QThm S (imp (clsEq (α ∩ γ) Λ) (clsEq ((α ∪ γ) − (β ∪ γ)) (α − β))) :=
  have hz : QThm S (clsEq ((γ − β) − γ) Λ) :=
    show (γ − β) − γ ≐ Λ from
    calc (γ − β) − γ
        ≐ (−β ∩ γ) ∩ −γ := QThm.mp (q22_51 γ (−β)) (q22_481 _ _ _)
      _ ≐ −β ∩ (γ ∩ −γ) := q22_52 _ _ _
      _ ≐ −β ∩ Λ := QThm.mp (q24_21 γ) (qclsEqCongr (fun X => −β ∩ X) _ _ (by cls_expr))          -- ✱24·21
      _ ≐ Λ := q24_23 _
  have h1 : QThm S (clsEq ((α ∪ γ) − (β ∪ γ)) ((α − β) − γ)) :=
    show (α ∪ γ) − (β ∪ γ) ≐ (α − β) − γ from
    calc (α ∪ γ) − (β ∪ γ)
        ≐ (α ∪ γ) ∩ (−β ∩ −γ) :=
          QThm.mp (qclsEqSymm (q22_87 β γ)) (qclsEqCongr (fun X => (α ∪ γ) ∩ X) _ _ (by cls_expr))  -- ✱22·87
      _ ≐ (α ∩ (−β ∩ −γ)) ∪ (γ ∩ (−β ∩ −γ)) := qclsDistribRight α γ _               -- ✱22·68
      _ ≐ ((α − β) − γ) ∪ ((γ − β) − γ) :=
          QThm.mp (qandI (qclsEqSymm (q22_52 α (−β) (−γ))) (qclsEqSymm (q22_52 γ (−β) (−γ))))
            (q22_73 _ _ _ _)
      _ ≐ ((α − β) − γ) ∪ Λ := QThm.mp hz (qclsEqCongr (fun X => ((α − β) − γ) ∪ X) _ _ (by cls_expr))  -- [✱24·21]
      _ ≐ (α − β) − γ := q24_24 _                                                 -- (1)
  have h2 : QThm S (imp (clsEq (α ∩ γ) Λ) (clsEq (α − γ) α)) :=
    qsyl (qiffMpr (q24_311 α γ)) (qiffMp (q22_621 α (−γ)))                         -- ✱24·311.✱22·621 (2)
  show (α ∪ γ) − (β ∪ γ) ≐[clsEq (α ∩ γ) Λ] α − β from
  calc (α ∪ γ) − (β ∪ γ)
      ≐ (α − β) − γ := h1                                                         -- (1)
    _ ≐ α ∩ (−β ∩ −γ) := q22_52 _ _ _
    _ ≐ α ∩ (−γ ∩ −β) := QThm.mp (q22_51 _ _) (qclsEqCongr (fun X => α ∩ X) _ _ (by cls_expr))
    _ ≐ (α − γ) − β := qclsEqSymm (q22_52 _ _ _)
    _ ≐[clsEq (α ∩ γ) Λ] α − β := qsyl h2 (q22_481 _ _ _)                           -- (1).(2)

/-! ## ✱24·5–✱24·63: the existence of classes -/

/-- ✱24·5 `⊢ : ∃!α . ≡ . (∃x) . x ∈ α` [✱4·2 . (✱24·03)] -/
theorem q24_5 (α : V a → QF V) : QThm S (iff (clsNonempty α) (ex fun x => x ∈ α)) :=
  QL.t4_2 _                                                                       -- ✱4·2 . (✱24·03)

/-- ✱24·51 `⊢ : ∼∃!α . ≡ . α = Λ`, as printed (p. 239). The Gutenberg transcription omits this proposition:
    its Dem. is printed under ✱24·5, and data/vol1.jsonl has no entry for it. ✱24·5 is used inside the
    negation (✱4·11). -/
theorem q24_51 [Reducibility S] (α : V a → QF V) : QThm S (iff (.neg (clsNonempty α)) (clsEq α Λ)) :=
  calc QF.neg (clsNonempty α)
      ≡ .neg (ex fun x => x ∈ α) := qiffNeg (q24_5 α)                              -- ✱24·5
    _ ≡ .all (fun x => nmem x α) := q10_252 _                                     -- [✱10·252]
    _ ≡ clsEq α Λ := q24_15 α                                                     -- [✱24·15]

/-- ✱24·52 `⊢ . ∃!V` [✱24·51·1 . Transp]: ✱24·1's Λ ≠ V is written V ≠ Λ (✱20·21, inside the negation, ✱4·11),
    and Transp is ✱2·15. y is ✱24·1's real variable: "The assumption that there is something ... is involved in
    the use of the real variable" (p. 239). -/
theorem q24_52 [Reducibility S] (y : V a) : QThm S (clsNonempty (𝐕 : V a → QF V)) :=
  have h1 : QThm S (.neg (clsEq (𝐕 : V a → QF V) Λ)) := QThm.mp (q24_1 y) (qiffMp (qiffNeg (q20_21 Λ 𝐕)))
  QThm.mp h1 (QThm.mp (qiffMp (q24_51 𝐕)) (QL.t2_15 _ _))                           -- ✱24·51·1 . Transp

/-- ✱24·53 `⊢ . ∼∃!Λ` [✱24·51 . ✱20·2] -/
theorem q24_53 [Reducibility S] : QThm S (.neg (clsNonempty (Λ : V a → QF V))) :=
  QThm.mp (q20_2 Λ) (qiffMpr (q24_51 Λ))                                          -- ✱24·51 . ✱20·2

/-- ✱24·54 `⊢ : ∃!α . ≡ . α ≠ Λ` [✱24·51 . Transp]: Transp is ✱4·11, with ✱4·13 for ∃!α . ≡ . ∼∼∃!α. -/
theorem q24_54 [Reducibility S] (α : V a → QF V) : QThm S (iff (clsNonempty α) (.neg (clsEq α Λ))) :=
  qiffTrans (QL.t4_13 _) (qiffNeg (q24_51 α))                                      -- ✱24·51 . Transp

/-- ✱24·55 `⊢ : ∼(α ⊂ β) . ≡ . ∃!α − β` [✱24·3 . Transp . ✱24·54], as printed (p. 240; the transcription has
    `α ⊃ β`, the text audit's Vol I list, entry 16). `∃!α − β` is read as ∃!(α − β): ∃! applies to the class
    α − β, as in ✱24·54's ∃!α. Transp is ✱4·11. -/
theorem q24_55 [Reducibility S] (α β : V a → QF V) : QThm S (iff (.neg (α ⊂ β)) (clsNonempty (α − β))) :=
  qiffTrans (qiffNeg (q24_3 α β)) (qiffSymm (q24_54 _))                            -- ✱24·3 . Transp . ✱24·54

/-- ✱24·56 `⊢ :. ∃!(α ∪ β) . ≡ : ∃!α . ∨ . ∃!β` [✱10·42 . ✱22·34], ✱22·34 under (∃x). -/
theorem q24_56 [Reducibility S] (α β : V a → QF V) :
    QThm S (iff (clsNonempty (α ∪ β)) (.or (clsNonempty α) (clsNonempty β))) :=
  calc clsNonempty (α ∪ β)
      ≡ ex (fun x => .or (x ∈ α) (x ∈ β)) := q10_11_281 fun x => q22_34 α β x        -- ✱22·34
    _ ≡ .or (clsNonempty α) (clsNonempty β) := qiffSymm (q10_42 _ _)                -- ✱10·42

/-- ✱24·561 `⊢ : ∃!(α ∩ β) . ⊃ . ∃!α . ∃!β` [✱10·5 . ✱22·33], ✱22·33 under (∃x). -/
theorem q24_561 [Reducibility S] (α β : V a → QF V) :
    QThm S (imp (clsNonempty (α ∩ β)) (QF.and (clsNonempty α) (clsNonempty β))) :=
  calc clsNonempty (α ∩ β)
      ≡ ex (fun x => QF.and (x ∈ α) (x ∈ β)) := q10_11_281 fun x => q22_33 α β x     -- ✱22·33
    _ ⊃ QF.and (clsNonempty α) (clsNonempty β) := q10_5 _ _                         -- ✱10·5

/-- ✱24·57 `⊢ :. α ∩ β = Λ . ⊃ : ∃!α . ⊃ . α ≠ β`. The first two lines are those of ✱24·38 (`qinterSelfNull`,
    ✱20·22·23 with ✱22·5); Transp is ✱2·03. -/
theorem q24_57 [Reducibility S] (α β : V a → QF V) :
    QThm S (imp (clsEq (α ∩ β) Λ) (imp (clsNonempty α) (.neg (clsEq α β)))) :=
  have h1 : QThm S (imp (QF.and (clsEq (α ∩ β) Λ) (clsEq α β)) (.neg (clsNonempty α))) :=
    calc QF.and (clsEq (α ∩ β) Λ) (clsEq α β)
        ⊃ clsEq (α ∩ α) Λ := qinterSelfNull α β                                     -- ✱22·481
      _ ⊃ clsEq α Λ := qiffMp (QThm.mp (q22_5 α) (qclsEqL _ _ Λ))                    -- [✱22·5]
      _ ⊃ .neg (clsNonempty α) := qiffMpr (q24_51 α)                               -- [✱24·51] (1)
  qsyl (QThm.mp h1 (QL.t3_3 _ _ _)) (QL.t2_03 _ _)                                 -- (1).Exp.Transp

/-- ✱24·571 `⊢ : ∃!α . α = β . ⊃ . ∃!(α ∩ β)`. Comm is ✱2·04, Transp ✱2·03, Imp ✱3·31. -/
theorem q24_571 [Reducibility S] (α β : V a → QF V) :
    QThm S (imp (QF.and (clsNonempty α) (clsEq α β)) (clsNonempty (α ∩ β))) :=
  have h1 : QThm S (imp (clsNonempty α) (imp (clsEq α β) (clsNonempty (α ∩ β)))) :=
    calc clsNonempty α
        ⊃ imp (clsEq (α ∩ β) Λ) (.neg (clsEq α β)) := QThm.mp (q24_57 α β) (QL.t2_04 _ _ _)  -- ✱24·57 . Comm
      _ ⊃ imp (clsEq α β) (.neg (clsEq (α ∩ β) Λ)) := QL.t2_03 _ _                   -- [Transp]
      _ ⊃ imp (clsEq α β) (clsNonempty (α ∩ β)) :=
          QThm.mp (qiffMpr (q24_54 _)) (QL.t2_05 _ _ _)                             -- [✱24·54] (1)
  QThm.mp h1 (QL.t3_31 _ _ _)                                                      -- (1).Imp

/-- ✱24·58 `⊢ :. α ⊂ β . ⊃ : ∃!α . ⊃ . ∃!β` [✱10·28], as printed (p. 240; the transcription has `α ⊃ β`, the
    text audit's Vol I list, entry 17). -/
theorem q24_58 (α β : V a → QF V) : QThm S (imp (α ⊂ β) (imp (clsNonempty α) (clsNonempty β))) :=
  q10_28 _ _                                                                      -- [✱10·28]

/-- ✱24·6 `⊢ :. α ⊂ β . ⊃ : α ≠ β . ≡ . ∃!β − α`, as printed (p. 240; the transcription has `α ⊃ β`, the text
    audit's Vol I list, entry 18); `∃!β − α` is read as ∃!(β − α), as in ✱24·55. "✱22·41 . Transp": ✱22·41 with Exp (✱3·3), and Transp (✱2·16); the Dem.'s
    ∼(β ⊂ α) is printed so (the transcription has ∼(β ⊃ α)). (2): α = β puts β − β for β − α (`qclsEqCongr`),
    which is Λ by ✱24·21. (1).(3): (3) put under Hp by ✱2·02, joined by Comp (✱3·43). -/
theorem q24_6 [Reducibility S] (α β : V a → QF V) :
    QThm S (imp (α ⊂ β) (iff (.neg (clsEq α β)) (clsNonempty (β − α)))) :=
  have h1 : QThm S (imp (α ⊂ β) (imp (.neg (clsEq α β)) (clsNonempty (β − α)))) :=
    calc (α ⊂ β)
        ⊃ imp (β ⊂ α) (clsEq α β) := QThm.mp (qiffMp (q22_41 α β)) (QL.t3_3 _ _ _)
      _ ⊃ imp (.neg (clsEq α β)) (.neg (β ⊂ α)) := QL.t2_16 _ _                      -- ✱22·41 . Transp
      _ ⊃ imp (.neg (clsEq α β)) (clsNonempty (β − α)) :=
          QThm.mp (qiffMp (q24_55 β α)) (QL.t2_05 _ _ _)                             -- [✱24·55] (1)
  have h2 : QThm S (imp (clsEq α β) (clsEq (β − α) Λ)) :=
    show β − α ≐[clsEq α β] Λ from
    calc β − α
        ≐[clsEq α β] β − β := qclsEqCongr (fun X => β − X) α β (by cls_expr)
      _ ≐ Λ := q24_21 β                                                           -- ✱24·21 (2)
  have h3 : QThm S (imp (clsNonempty (β − α)) (.neg (clsEq α β))) :=
    qsyl (qiffMp (q24_54 _)) (QThm.mp h2 (QL.t2_16 _ _))                            -- (2).Transp.✱24·54 (3)
  qcomp h1 (QThm.mp h3 (QL.t2_02 _ _))                                             -- (1).(3)

/-- ✱24·61 `⊢ : ∼∃!β . ⊃ . α ∪ β = α` [✱24·51·24], ✱24·51's β = Λ put for β in α ∪ β (`qclsEqCongr`). -/
theorem q24_61 [Reducibility S] (α β : V a → QF V) : QThm S (imp (.neg (clsNonempty β)) (clsEq (α ∪ β) α)) :=
  show α ∪ β ≐[.neg (clsNonempty β)] α from
  calc α ∪ β
      ≐[.neg (clsNonempty β)] α ∪ Λ := qsyl (qiffMp (q24_51 β)) (qclsEqCongr (fun X => α ∪ X) _ _ (by cls_expr))  -- ✱24·51
    _ ≐ α := q24_24 α                                                             -- ✱24·24

/-- ✱24·62 `⊢ : ∼∃!β . ⊃ . α ∩ β = Λ` [✱24·51·23], ✱24·51's β = Λ put for β in α ∩ β (`qclsEqCongr`). -/
theorem q24_62 [Reducibility S] (α β : V a → QF V) : QThm S (imp (.neg (clsNonempty β)) (clsEq (α ∩ β) Λ)) :=
  show α ∩ β ≐[.neg (clsNonempty β)] Λ from
  calc α ∩ β
      ≐[.neg (clsNonempty β)] α ∩ Λ := qsyl (qiffMp (q24_51 β)) (qclsEqCongr (fun X => α ∩ X) _ _ (by cls_expr))  -- ✱24·51
    _ ≐ Λ := q24_23 α                                                             -- ✱24·23

/-- ✱24·63 `⊢ :. Λ ∼∈ κ . ≡ : α ∈ κ . ⊃_α . ∃!α`, κ a class of classes ("the conditions of significance require
    that κ should be a class of classes", p. 240), α apparent (✱20·07). "[✱13·191]" is its class analogue ✱20·53
    for the extensional expression α ∼∈ κ (`qcls20_53`; p. 206); "[Transp]" is ✱2·03 both ways, and ✱24·54 acts on
    the consequent (✱4·85), under (α). -/
theorem q24_63 [Reducibility S] (κ : (V a → QF V) → QF V) :
    QThm S (iff (.neg ((Λ : V a → QF V) ∈ κ)) (clsAll fun α => imp (α ∈ κ) (clsNonempty α))) :=
  calc QF.neg ((Λ : V a → QF V) ∈ κ)
      ≡ clsAll (fun α => imp (clsEq α Λ) (.neg (α ∈ κ))) :=
        qiffSymm (qcls20_53 (fun α => .neg (α ∈ κ)) (clsExpr_ext (.neg (ClsExpr.clsClsMem κ))) Λ)  -- ✱13·191
    _ ≡ clsAll (fun α => imp (α ∈ κ) (.neg (clsEq α Λ))) :=
        q10_11_271 fun _ => qiffI (QL.t2_03 _ _) (QL.t2_03 _ _)                     -- [Transp]
    _ ≡ clsAll (fun α => imp (α ∈ κ) (clsNonempty α)) :=
        q10_11_271 fun φ => QThm.mp (qiffSymm (q24_54 (pf φ))) (QL.t4_85 _ _ _)      -- [✱24·54]

end PM
