import PM.Star23
import PM.Star24
/-!
  ✱25: the universal relation, the null relation, and the existence of relations (1910 print, pp. 241–243;
  summary p. 241, numbered items pp. 241–243). The print has 73 numbered items: the definitions
  ✱25·01–✱25·03 (p. 241) and 70 propositions, ✱25·1 to ✱25·63, numbered as ✱24's.

  "This number contains the analogues, for relations, of the definitions and propositions of ✱24. Proofs
  will not be given, as they proceed precisely as in ✱24. […] The propositions of this number are much
  less often referred to than those of ✱24, but for the sake of uniformity we have given the analogues
  of all propositions in ✱24, with the same numeration (except for the integral part). All the remarks
  made in ✱24 apply, mutatis mutandis, in the present number" (p. 241).

  The definitions are macros (`@[reducible]`), like ✱23·01–✱23·05 and ✱24·01–✱24·03 (docs/TYPES_DESIGN.md
  decision 9). A relation is written by its defining function, a formula with two holes (PM/Star21.lean),
  so V̇, which PM defines as the relation x̂ŷ(x = x . y = y), is the function (x, y) ↦ x = x . y = y, and
  Λ̇ = ∸V̇ is ✱23·04's (x, y) ↦ ∼{x V̇ y}. ∃̇!R is a proposition about the relation R, its definiens with xRy
  eliminated where it stands (`relHolds x R y`, ✱21·02 with ✱21·01, the smallest scope), and (∃x, y) the
  two-variable quantifier of ✱11·03:
    ✱25·01  V̇ = x̂ŷ(x = x . y = y)            Df   (`QF.relUniv`, `𝐕̇`)
    ✱25·02  Λ̇ = ∸V̇                           Df   (`QF.relEmpty`, `Λ̇`)
    ✱25·03  ∃̇!R . = . (∃x, y) . xRy          Df   (`QF.relNonempty R`)
  V̇ and Λ̇ are ambiguous as to type, like V and Λ: "the relation which holds between any two terms
  whatever of the appropriate types, whatever these may be in the given context" (p. 241). The types `a`,
  `b` of their domain and converse domain are implicit, fixed by the context.

  Notation (scoped to `PM`): `Λ̇` is PM's sign. V̇ is the bold `𝐕̇`, as ✱24's V is `𝐕` (`V` names the variable
  family of every file); PM's ∃̇! is not used as a token, as ∃! is not in ✱24, so ∃̇!R is `relNonempty R`.

  PM prints no proof, no Dem. and no hint in ✱25. Each proof here is the printed proof of the analogous
  proposition of ✱24 (its Dem. lines or its bracketed hint, PM/Star24.lean), with ✱25 for ✱24, ✱23 for ✱22,
  ✱21 for ✱20, and for a proposition of ✱10 its form for two variables in ✱11 (✱10·11·271 is ✱11·11·33,
  ✱10·252 is ✱11·25, ✱10·42 is ✱11·41, ✱10·5 is ✱11·42, ✱10·28 is ✱11·34), as ✱23 does for ✱22; ✱13·191 for
  two variables is ✱13·21, and ✱20·53 for relations ✱21·53. The comment on each Lean line gives ✱24's line or
  hint so translated. `data/star25_ledger.json` records, per proposition, ✱24's citations so translated
  (`cited_used`, `cited_unused`) and every further proposition the proof needs. The steps that ✱24's proofs
  take without citing them are taken here for relations, each named in the docstrings and listed in the
  ledger: a chain of identities of relations, "R = S [✱x] = T", is a `calc` block joined by ✱21·22 (`≑`,
  below); a relation is put for an identical one inside an expression by ✱21·18 for the expression, with
  ✱21·2 (`qrelEqCongr`), or ✱23·481, ✱23·551 where ✱24's lines use ✱22·481, ✱22·551; and a proposition about
  an apparent relation (✱25·11, ✱25·12) is used at a real one by the analogue for relations of ✱10·1
  (`qrelAllAt`, ✱21·11), the expression being extensional (`relExpr_ext`, p. 213).

  Statements are read from the Gutenberg #78050 transcription of the 1910 print (its formula source), and
  each was compared with its ✱24 analogue and checked against the scan of the print (pp. 241–243). The
  transcription leaves out none of the 70 propositions. Where it differs from the print, the print is
  followed, and the docstring says so: ✱25·47 (brackets the print does not have, no change to the
  statement) and ✱25·56 (∃̇!(R ⊍ S), with brackets), both on the text audit's list of errors for Vol I
  (entries 19, 20). At ✱25·37 and ✱25·412 the print has zRw for zSw and R ⪽ Q for S ⪽ Q, neither a theorem;
  the transcription has the corrected statements, the analogues of ✱24·37 and ✱24·412, and they are the ones
  proved, as at ✱23·81. The source of these corrections is not yet identified: the Errata page bound into the
  1910 print has no entry for p. 242, and the ebook's Transcriber's Note says only "All items in the Errata,
  from all three volumes, have been added and corrected accordingly." One statement is printed otherwise than its
  analogue, and is stated as printed: ✱25·313 has R ∸ S = R where ✱24·313 has α = α − β.

  Grouping, as in ✱24: an unbracketed product of three or more factors is grouped from the left, as PM's own
  definitions group R ∩̇ S ∩̇ T (✱23·53) and R ⊍ S ⊍ T (✱23·71); a chain of equivalences "A ≡ B ≡ C" (✱25·4) is
  A ≡ B . B ≡ C; and (x, y, z, w) is (x, y) : (z, w) (✱25·37), as ✱11·02 has (x, y, z) = (x) : (y, z).

  ✱25·1 and ✱25·52 take real variables x, y, as ✱23·351 does: they are false for empty types, as ✱24·1 and
  ✱24·52 are, and "all the remarks made in ✱24 apply" (p. 241), among them p. 239's on the real variable.

  Names: `q25_1` is ✱25·1, and so on. P, Q, R, S, R', S' are relations, as in PM; as in PM/Star23.lean,
  the system of rules is `S`, so PM's relation S is written `S'` in Lean statements, and PM's S' is `S''`;
  the docstrings keep PM's letters. κ is a class of relations (✱25·63).
-/
namespace PM
open QF

namespace QF
variable {V : Ty → Type}
/-- ✱25·01 `V̇ = x̂ŷ(x = x . y = y)` Df: the relation whose defining function is x = x . y = y (✱13·01,
    ✱3·01). -/
@[reducible] def relUniv {a b : Ty} : V a → V b → QF V := fun x y => QF.and (ident x x) (ident y y)
/-- ✱25·02 `Λ̇ = ∸V̇` Df -/
@[reducible] def relEmpty {a b : Ty} : V a → V b → QF V := relCompl relUniv
/-- ✱25·03 `∃̇!R . = . (∃x, y) . xRy` Df -/
@[reducible] def relNonempty {a b : Ty} (R : V a → V b → QF V) : QF V := ex2 fun x y => relHolds x R y
end QF

/-! The notations of ✱25 (scoped to `PM`, like those of ✱23 and ✱24): `𝐕̇` for V̇ (✱25·01) and `Λ̇` for Λ̇
    (✱25·02). Each unfolds to the definition it names. -/
/-- `𝐕̇`: `relUniv` (✱25·01), PM's V̇. -/
scoped notation "𝐕̇" => QF.relUniv
/-- `Λ̇`: `relEmpty` (✱25·02). -/
scoped notation "Λ̇" => QF.relEmpty

variable {V : Ty → Type} {S : Sys} {a b : Ty}

/-! Checks of the notation: each statement is the definition it names. -/
theorem check_notation_rel_univ : (𝐕̇ : V a → V b → QF V) = fun x y => QF.and (ident x x) (ident y y) := rfl
theorem check_notation_rel_empty : (Λ̇ : V a → V b → QF V) = ∸𝐕̇ := rfl
theorem check_notation_rel_empty_unfolded : (Λ̇ : V a → V b → QF V) = fun x y => QF.neg (relHolds x 𝐕̇ y) := rfl
theorem check_notation_rel_nonempty (R : V a → V b → QF V) : relNonempty R = ex2 fun x y => relHolds x R y := rfl
/-! ✱24's signs and ✱25's are read apart: Λ and 𝐕 are classes, Λ̇ and 𝐕̇ relations. -/
theorem check_notation_empty_cls_and_rel : (Λ : V a → QF V) = clsEmpty ∧ (Λ̇ : V a → V b → QF V) = relEmpty := ⟨rfl, rfl⟩
theorem check_notation_univ_cls_and_rel : (𝐕 : V a → QF V) = clsUniv ∧ (𝐕̇ : V a → V b → QF V) = relUniv := ⟨rfl, rfl⟩

/-! ## Chains of identities of relations

  As in ✱24 for classes (PM/Star24.lean): a displayed chain "⊢ . R = S [✱x] = T" is a `calc` block, one line
  per PM line, with the relations below; two lines are joined by ✱21·22, the transitivity of identity of
  relations (✱20·22's analogue), and under a hypothesis by Comp (✱3·43) and ✱21·22, an asserted line being
  put under it by ✱2·02. The ledger lists ✱21·22 as `glue` of kind `chain`, as ✱24's lists ✱20·22. The sign
  is `≑` (a dotted =, as PM dots the signs of ✱23 and ✱25), so that a chain of relations is not read as one
  of classes (`≐`). -/

/-- `⊢ . R = S` between relations (`relEq`), as a relation between R and S. -/
def QRelEq (S : Sys) (ψ χ : V a → V b → QF V) : Prop := QThm S (relEq ψ χ)
/-- `⊢ : H . ⊃ . R = S` between relations, as a relation between R and S. -/
def QRelEqH (S : Sys) (H : QF V) (ψ χ : V a → V b → QF V) : Prop := QThm S (imp H (relEq ψ χ))

/-! The notations name the system `S` of the theorem they are used in, as those of PM/Chain.lean do. -/
set_option hygiene false in
/-- `R ≑ S`: `⊢ . R = S`, identity of relations (`QRelEq`), in a chain. -/
scoped infix:50 " ≑ " => QRelEq S
set_option hygiene false in
/-- `R ≑[H] S`: `⊢ : H . ⊃ . R = S` (`QRelEqH`), in a chain. -/
scoped notation:50 A:51 " ≑[" H "] " B:51 => QRelEqH S H A B

/-- `R = S`, `S = T` give `R = T` (✱21·22). -/
instance transRelEq [Reducibility S] :
    @Trans (V a → V b → QF V) (V a → V b → QF V) (V a → V b → QF V) (QRelEq S) (QRelEq S) (QRelEq S) :=
  ⟨fun h1 h2 => QThm.mp (qandI h1 h2) (q21_22 _ _ _)⟩
/-- Under H, `R = S` and `S = T` give `R = T` (Comp ✱3·43, ✱21·22). -/
instance transHRelEq [Reducibility S] {H : QF V} :
    @Trans (V a → V b → QF V) (V a → V b → QF V) (V a → V b → QF V) (QRelEqH S H) (QRelEqH S H)
      (QRelEqH S H) :=
  ⟨fun h1 h2 => qsyl (qcomp h1 h2) (q21_22 _ _ _)⟩
/-- Under H, `R = S`, and the asserted `S = T`, give `R = T` (✱2·02, Comp ✱3·43, ✱21·22). -/
instance transHRelEqRelEq [Reducibility S] {H : QF V} :
    @Trans (V a → V b → QF V) (V a → V b → QF V) (V a → V b → QF V) (QRelEqH S H) (QRelEq S) (QRelEqH S H) :=
  ⟨fun h1 h2 => qsyl (qcomp h1 (QThm.mp h2 (QL.t2_02 H _))) (q21_22 _ _ _)⟩
/-- The asserted `R = S`, and under H `S = T`, give `R = T` under H (✱2·02, Comp ✱3·43, ✱21·22). -/
instance transRelEqHRelEq [Reducibility S] {H : QF V} :
    @Trans (V a → V b → QF V) (V a → V b → QF V) (V a → V b → QF V) (QRelEq S) (QRelEqH S H) (QRelEqH S H) :=
  ⟨fun h1 h2 => qsyl (qcomp (QThm.mp h1 (QL.t2_02 H _)) h2) (q21_22 _ _ _)⟩

/-! ## Further steps, each listed in the ledger where used -/

namespace RelExpr
/-- p ⊃ q (✱1·01). -/
theorem imp {F G : (V a → V b → QF V) → QF V} (hF : RelExpr F) (hG : RelExpr G) :
    RelExpr fun R => QF.imp (F R) (G R) := .or (.neg hF) hG
/-- A relation x̂ŷG(x, y, R) whose defining function contains R, in a context that may contain R (✱21·01),
    as `ClsExpr.clsOf` for a class. -/
theorem relOf {c d : Ty} {G : V c → V d → (V a → V b → QF V) → QF V}
    {F : V (Ty.pred2 c d) → (V a → V b → QF V) → QF V} (hG : ∀ z w, RelExpr (G z w))
    (hF : ∀ φ, RelExpr (F φ)) : RelExpr fun R => QF.rel (fun z w => G z w R) fun φ => F φ R :=
  ex fun _ => and (.all fun _ => .all fun _ => iff (.const _) (hG _ _)) (hF _)
end RelExpr

/-- `RelExpr` for the expressions of ✱23 and ✱25 written out in a statement: the expression is unfolded
    into ∼, ∨, (x) and ✱21·01 at the relation (PM/Star21.lean, `RelExpr`), which this tactic follows
    constructor by constructor, as `cls_expr` (PM/Star24.lean) follows `ClsExpr`. It proves only that an
    expression is one PM's notation forms. -/
macro "rel_expr" : tactic => `(tactic| repeat (first
  | exact RelExpr.const _
  | exact RelExpr.relHolds _ _
  | apply RelExpr.or
  | apply RelExpr.neg
  | apply RelExpr.rel
  | apply RelExpr.relOf
  | apply RelExpr.all
  | intro))

/-- ✱21·18 for an expression F of a relation whose value is a relation ("equals put for equals", as
    `qclsEqCongr` for classes): `⊢ :. R = S . ⊃ . F(R) = F(S)`. ✱21·18 for the expression F(R) = F(S)
    (`qrel21_18`; extensional, `RelExpr`) gives F(R) = F(S) . ≡ . F(S) = F(S), whose second member is ✱21·2
    (detached by ✱3·27 and Comm, `qiffElimOf`). That F is such an expression is an explicit argument,
    given at each use by `by rel_expr`. -/
theorem qrelEqCongr [Reducibility S] {c d : Ty} (F : (V a → V b → QF V) → V c → V d → QF V)
    (ψ χ : V a → V b → QF V) (hF : ∀ z w, RelExpr fun R => F R z w) :
    QThm S (imp (relEq ψ χ) (relEq (F ψ) (F χ))) :=
  qsyl (qrel21_18 (fun R => relEq (F R) (F χ))
      (relExpr_ext (RelExpr.relOf (fun z w => hF z w) fun _ => .const _)) ψ χ)
    (qiffElimOf (q21_2 _))

/-- ✱21·21 as a rule: from `⊢ . R = S`, `⊢ . S = R`. -/
theorem qrelEqSymm [Reducibility S] {ψ χ : V a → V b → QF V} (h : QThm S (relEq ψ χ)) :
    QThm S (relEq χ ψ) :=
  QThm.mp h (qiffMp (q21_21 ψ χ))

/-- `R = S . ⊃ : R = T . ≡ . S = T`: ✱21·23 and ✱21·22, each with Exp (✱3·3), joined by Comp (✱3·43); the
    analogue of `qrelEqR` (PM/Star21.lean) for the first member, as `qclsEqL` is of `qclsEqR`. -/
theorem qrelEqL [Reducibility S] (ψ χ ω : V a → V b → QF V) :
    QThm S (imp (relEq ψ χ) (iff (relEq ψ ω) (relEq χ ω))) :=
  qcomp (QThm.mp (q21_23 ψ χ ω) (QL.t3_3 _ _ _)) (QThm.mp (q21_22 ψ χ ω) (QL.t3_3 _ _ _))

/-- The analogue for relations of ✱10·1 for an extensional expression G (`qrelAllAt`, PM/Star21.lean): from
    (R) . GR, G at a real relation x̂ŷψ(x, y), whose defining function need not be predicative. -/
theorem qrelAllAtExt [Reducibility S] (G : (V a → V b → QF V) → QF V) (hG : RelExt S G)
    (ψ : V a → V b → QF V) : QThm S (imp (relAll G) (G ψ)) :=
  qrelAllAt G ψ fun θ => qsyl (hG (pf2 θ) ψ) (QL.t3_26 _ _)

/-! ## ✱25·1–✱25·17: V̇ and Λ̇ -/

/-- ✱25·1 `⊢ . Λ̇ ≠ V̇`, as ✱24·1 [✱22·351 . (✱24·02)]: ✱23·351 at V̇. x, y are the real variables of ✱23·351
    (✱10·25 for two variables): the statement needs non-empty types, as ✱24·1 does (p. 239). -/
theorem q25_1 [Reducibility S] (x : V a) (y : V b) : QThm S (.neg (relEq (Λ̇ : V a → V b → QF V) 𝐕̇)) :=
  q23_351 𝐕̇ x y                                                                   -- ✱23·351 . (✱25·02)

/-- ✱25·101 `⊢ . V̇ = ∸Λ̇`, as ✱24·101 [✱22·831 . (✱24·02)]: Λ̇ = ∸V̇ is ✱21·2 by ✱25·02, and ✱23·831 turns
    it. -/
theorem q25_101 [Reducibility S] : QThm S (relEq (𝐕̇ : V a → V b → QF V) (∸Λ̇)) :=
  QThm.mp (q21_2 Λ̇) (qiffMp (q23_831 Λ̇ 𝐕̇))                                        -- ✱23·831 . (✱25·02)

/-- ✱25·102 `⊢ : (x, y) . φ(x, y) . ≡ . x̂ŷφ(x, y) = V̇`, as ✱24·102. In the first line, ✱5·501 with
    x = x . y = y (✱13·15 for each factor) gives φ(x, y) ≡ (x = x . y = y ≡ φ(x, y)), whose second member is
    written φ(x, y) ≡ x = x . y = y (✱4·21); ✱10·11·271 for two variables is ✱11·11·33; ✱20·15 is ✱21·15. -/
theorem q25_102 [Reducibility S] (φ : V a → V b → QF V) : QThm S (iff (all2 φ) (relEq φ 𝐕̇)) :=
  have h1 : ∀ x y, QThm S (iff (φ x y) (iff (φ x y) (QF.and (ident x x) (ident y y)))) := fun x y =>
    calc φ x y
        ≡ iff (QF.and (ident x x) (ident y y)) (φ x y) :=
          QThm.mp (qandI (q13_15 x) (q13_15 y)) (QL.t5_501 _ _)                    -- ✱13·15 . ✱5·501
      _ ≡ iff (φ x y) (QF.and (ident x x) (ident y y)) := QL.t4_21 _ _
  calc all2 φ
      ≡ fiff2 φ 𝐕̇ := QThm.mp (q11_11 h1) (q11_33 _ _)                              -- [✱11·11·33]
    _ ≡ relEq φ 𝐕̇ := q21_15 φ 𝐕̇                                                    -- [✱21·15] [(✱25·01)]

/-- ✱25·103 `⊢ : (x, y) . ∼φ(x, y) . ≡ . x̂ŷφ(x, y) = Λ̇`, as ✱24·103. Each identity is replaced in its first
    member by ✱21·22·23 (`qrelEqL`, [✱23·392]) or turned by ✱21·21 ([✱23·831], which has ∸V̇ second). -/
theorem q25_103 [Reducibility S] (φ : V a → V b → QF V) :
    QThm S (iff (all2 fun x y => .neg (φ x y)) (relEq φ Λ̇)) :=
  calc all2 (fun x y => .neg (φ x y))
      ≡ relEq (fun x y => .neg (φ x y)) 𝐕̇ := q25_102 _                              -- ✱25·102
    _ ≡ relEq (∸φ) 𝐕̇ := qiffSymm (QThm.mp (q23_392 φ) (qrelEqL _ _ 𝐕̇))               -- [✱23·392]
    _ ≡ relEq 𝐕̇ (∸φ) := q21_21 _ _
    _ ≡ relEq φ (∸𝐕̇) := qiffSymm (q23_831 φ 𝐕̇)                                     -- [✱23·831]
    _ ≡ relEq φ Λ̇ := QL.t4_2 _                                                     -- [(✱25·02)]

/-- ✱25·104 `⊢ . (x, y) . xV̇y`, as ✱24·104: ✱21·3 (1), ✱13·15 for each factor, ✱11·11·33. -/
theorem q25_104 [Reducibility S] : QThm S (all2 fun (x : V a) (y : V b) => relHolds x 𝐕̇ y) :=
  have h1 : ∀ (x : V a) (y : V b), QThm S (iff (relHolds x 𝐕̇ y) (QF.and (ident x x) (ident y y))) :=
    fun x y => q21_3 𝐕̇ x y                                                         -- ✱21·3 (1)
  QThm.mp (q11_11 fun x y => qandI (q13_15 x) (q13_15 y))
    (qiffMpr (QThm.mp (q11_11 h1) (q11_33 _ _)))                                  -- (1).✱13·15.✱11·11·33

/-- ✱25·105 `⊢ . (x, y) . ∼(xΛ̇y)`, as ✱24·105. ✱4·12 gives xV̇y ≡ ∼(xΛ̇y), written ∼(xΛ̇y) ≡ xV̇y (✱4·21). -/
theorem q25_105 [Reducibility S] : QThm S (all2 fun (x : V a) (y : V b) => .neg (relHolds x Λ̇ y)) :=
  have h1 : ∀ (x : V a) (y : V b), QThm S (iff (.neg (relHolds x Λ̇ y)) (relHolds x 𝐕̇ y)) := fun x y =>
    qiffSymm (QThm.mp (q23_35 𝐕̇ x y) (qiffMp (QL.t4_12 _ _)))                      -- ✱23·35 [✱4·12] (1)
  QThm.mp q25_104 (qiffMpr (QThm.mp (q11_11 h1) (q11_33 _ _)))                     -- (1).✱11·11·33.✱25·104

/-- ✱25·11 `⊢ . (R) . R ⪽ V̇`, R apparent (✱21·07), as ✱24·11: ✱10·11 for R, ✱11·11 for x, y. -/
theorem q25_11 [Reducibility S] : QThm S (relAll fun R : V a → V b → QF V => R ⪽ 𝐕̇) :=
  q10_11 fun _ => q11_11 fun x y =>                                               -- [✱10·11] [✱11·11]
    QThm.mp (QThm.mp q25_104 (q11_1 _ x y)) (QL.t2_02 _ _)                         -- ✱25·104.✱11·1 [Simp]

/-- ✱25·12 `⊢ . (R) . Λ̇ ⪽ R`, R apparent (✱21·07), as ✱24·12. -/
theorem q25_12 [Reducibility S] : QThm S (relAll fun R : V a → V b → QF V => Λ̇ ⪽ R) :=
  q10_11 fun _ => q11_11 fun x y =>                                               -- (1).✱10·11.✱11·11
    QThm.mp (QThm.mp q25_105 (q11_1 _ x y)) (QL.t2_21 _ _)                         -- ✱25·105.✱11·1 [✱2·21] (1)

/-- ✱25·12 at a real relation R, by the analogue for relations of ✱10·1 (`qrelAllAtExt`; the expression
    Λ̇ ⪽ R is extensional, `relExpr_ext`). -/
theorem qnullRelSubset [Reducibility S] (R : V a → V b → QF V) : QThm S (Λ̇ ⪽ R) :=
  QThm.mp q25_12 (qrelAllAtExt _ (relExpr_ext (RelExpr.relSubset_right Λ̇)) R)

/-- ✱25·11 at a real relation R, by the analogue for relations of ✱10·1 (`qrelAllAtExt`). -/
theorem qrelSubsetUniv [Reducibility S] (R : V a → V b → QF V) : QThm S (R ⪽ 𝐕̇) :=
  QThm.mp q25_11 (qrelAllAtExt _ (relExpr_ext (RelExpr.relSubset_left 𝐕̇)) R)

/-- ✱25·13 `⊢ : R = Λ̇ . ≡ . R ⪽ Λ̇`, as ✱24·13: the lines prove R ⪽ Λ̇ . ≡ . R = Λ̇, read from right to left
    (✱4·21); ✱25·12 is used at R (`qnullRelSubset`). -/
theorem q25_13 [Reducibility S] (R : V a → V b → QF V) : QThm S (iff (relEq R Λ̇) (R ⪽ Λ̇)) :=
  qiffSymm <|
    calc (R ⪽ Λ̇)
        ≡ QF.and (R ⪽ Λ̇) (Λ̇ ⪽ R) := QThm.mp (qnullRelSubset R) (QL.t4_73 _ _)        -- ✱25·12 . ✱4·73
      _ ≡ relEq R Λ̇ := q23_41 R Λ̇                                                  -- [✱23·41]

/-- ✱25·14 `⊢ : (x, y) . xRy . ≡ . R = V̇`, as ✱24·14: "[✱20·32]" is ✱21·32, which replaces x̂ŷ(xRy) by R in
    the first member of the identity (✱21·22·23, `qrelEqL`). -/
theorem q25_14 [Reducibility S] (R : V a → V b → QF V) :
    QThm S (iff (all2 fun x y => relHolds x R y) (relEq R 𝐕̇)) :=
  calc all2 (fun x y => relHolds x R y)
      ≡ relEq (fun x y => relHolds x R y) 𝐕̇ := q25_102 _                            -- ✱25·102
    _ ≡ relEq R 𝐕̇ := QThm.mp (q21_32 R) (qrelEqL _ _ 𝐕̇)                             -- [✱21·32]

/-- ✱25·141 `⊢ : V̇ ⪽ R . ≡ . V̇ = R`, as ✱24·141. ✱4·73 gives V̇ ⪽ R . R ⪽ V̇, whose factors are written in the
    other order (✱4·3); ✱25·11 is used at R (`qrelSubsetUniv`). The last line of ✱24·141 is α = V; the
    statement's V̇ = R is its turn by ✱21·21. -/
theorem q25_141 [Reducibility S] (R : V a → V b → QF V) : QThm S (iff (𝐕̇ ⪽ R) (relEq 𝐕̇ R)) :=
  calc (𝐕̇ ⪽ R)
      ≡ QF.and (𝐕̇ ⪽ R) (R ⪽ 𝐕̇) := QThm.mp (qrelSubsetUniv R) (QL.t4_73 _ _)
    _ ≡ QF.and (R ⪽ 𝐕̇) (𝐕̇ ⪽ R) := QL.t4_3 _ _                                       -- ✱25·11 . ✱4·73
    _ ≡ relEq R 𝐕̇ := q23_41 R 𝐕̇                                                    -- [✱23·41]
    _ ≡ relEq 𝐕̇ R := q21_21 _ _

/-- ✱25·15 `⊢ : (x, y) . ∼(xRy) . ≡ . R = Λ̇`, as ✱24·15. -/
theorem q25_15 [Reducibility S] (R : V a → V b → QF V) :
    QThm S (iff (all2 fun x y => .neg (relHolds x R y)) (relEq R Λ̇)) :=
  calc all2 (fun x y => .neg (relHolds x R y))
      ≡ relEq (fun x y => relHolds x R y) Λ̇ := q25_103 _                            -- ✱25·103
    _ ≡ relEq R Λ̇ := QThm.mp (q21_32 R) (qrelEqL _ _ Λ̇)                             -- [✱21·32]

/-- ✱25·17 `⊢ : R = V̇ . ≡ . ∸R = Λ̇`, as ✱24·17 [✱22·83 . (✱24·02)]. -/
theorem q25_17 [Reducibility S] (R : V a → V b → QF V) : QThm S (iff (relEq R 𝐕̇) (relEq (∸R) Λ̇)) :=
  q23_83 R 𝐕̇                                                                      -- ✱23·83 . (✱25·02)

/-! ## ✱25·21–✱25·27: Λ̇ and V̇ with the operations of ✱23 -/

/-- ✱25·21 `⊢ . R ∩̇ ∸R = Λ̇`, as ✱24·21 [✱24·103 . ✱22·89]: ✱25·103 at the defining function of R ∩̇ ∸R, and
    ✱23·89's ∼{x(R ∸ R)y} written ∼(xRy . x ∸R y) by ✱23·33 (✱4·11, under (x, y), ✱11·11·33). -/
theorem q25_21 [Reducibility S] (R : V a → V b → QF V) : QThm S (relEq (R ∩̇ ∸R) Λ̇) :=
  have h : QThm S (all2 fun x y => .neg (QF.and (relHolds x R y) (relHolds x (∸R) y))) :=
    QThm.mp (q23_89 R)
      (qiffMp (QThm.mp (q11_11 fun x y => qiffNeg (q23_33 R (∸R) x y)) (q11_33 _ _)))  -- ✱23·89
  QThm.mp h (qiffMp (q25_103 (R ∩̇ ∸R)))                                            -- ✱25·103

/-- ✱25·22 `⊢ . R ⊍ ∸R = V̇`, as ✱24·22 [✱22·88 . ✱24·102]: ✱25·102 at the defining function of R ⊍ ∸R, with
    ✱23·34 for ✱23·88's x(R ⊍ ∸R)y (under (x, y), ✱11·11·33). -/
theorem q25_22 [Reducibility S] (R : V a → V b → QF V) : QThm S (relEq (R ⊍ ∸R) 𝐕̇) :=
  have h : QThm S (all2 fun x y => .or (relHolds x R y) (relHolds x (∸R) y)) :=
    QThm.mp (q23_88 R) (qiffMp (QThm.mp (q11_11 fun x y => q23_34 R (∸R) x y) (q11_33 _ _)))  -- ✱23·88
  QThm.mp h (qiffMp (q25_102 (R ⊍ ∸R)))                                            -- ✱25·102

/-- ✱25·23 `⊢ . R ∩̇ Λ̇ = Λ̇`, as ✱24·23 [✱24·12 . ✱22·621]: ✱23·621 gives Λ̇ ∩̇ R = Λ̇, commuted by ✱23·51. -/
theorem q25_23 [Reducibility S] (R : V a → V b → QF V) : QThm S (relEq (R ∩̇ Λ̇) Λ̇) :=
  show R ∩̇ Λ̇ ≑ Λ̇ from
  calc R ∩̇ Λ̇
      ≑ Λ̇ ∩̇ R := q23_51 _ _
    _ ≑ Λ̇ := QThm.mp (qnullRelSubset R) (qiffMp (q23_621 Λ̇ R))                       -- ✱25·12 . ✱23·621

/-- ✱25·24 `⊢ . R ⊍ Λ̇ = R`, as ✱24·24 [✱24·12 . ✱22·62]: ✱23·62 gives Λ̇ ⊍ R = R, commuted by ✱23·57. -/
theorem q25_24 [Reducibility S] (R : V a → V b → QF V) : QThm S (relEq (R ⊍ Λ̇) R) :=
  show R ⊍ Λ̇ ≑ R from
  calc R ⊍ Λ̇
      ≑ Λ̇ ⊍ R := q23_57 _ _
    _ ≑ R := QThm.mp (qnullRelSubset R) (qiffMp (q23_62 Λ̇ R))                        -- ✱25·12 . ✱23·62

/-- ✱25·26 `⊢ . R ∩̇ V̇ = R`, as ✱24·26 [✱22·621 . ✱24·11] -/
theorem q25_26 [Reducibility S] (R : V a → V b → QF V) : QThm S (relEq (R ∩̇ 𝐕̇) R) :=
  QThm.mp (qrelSubsetUniv R) (qiffMp (q23_621 R 𝐕̇))                                -- ✱23·621 . ✱25·11

/-- ✱25·27 `⊢ . R ⊍ V̇ = V̇`, as ✱24·27 [✱22·62 . ✱24·11] -/
theorem q25_27 [Reducibility S] (R : V a → V b → QF V) : QThm S (relEq (R ⊍ 𝐕̇) 𝐕̇) :=
  QThm.mp (qrelSubsetUniv R) (qiffMp (q23_62 R 𝐕̇))                                 -- ✱23·62 . ✱25·11

/-! ## ✱25·3–✱25·39: inclusion and the null relation -/

/-- ✱25·3 `⊢ : R ⪽ S . ≡ . R ∸ S = Λ̇`, as ✱24·3. In the first line, ✱4·6 and ✱4·53 (from right to left)
    give ∼{xRy . ∼(xSy)}; ✱23·35 acts on the second factor (✱4·36 with ✱4·3) and ✱23·33 on the product,
    each inside the negation (✱4·11); ✱10·11·271 for two variables is ✱11·11·33. -/
theorem q25_3 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (iff (R ⪽ S') (relEq (R ∸ S') Λ̇)) :=
  have h1 : ∀ x y, QThm S (iff (imp (relHolds x R y) (relHolds x S' y)) (.neg (relHolds x (R ∸ S') y))) :=
    fun x y =>
    calc imp (relHolds x R y) (relHolds x S' y)
        ≡ .neg (QF.and (relHolds x R y) (.neg (relHolds x S' y))) :=
          qiffTrans (QL.t4_6 _ _) (qiffSymm (QL.t4_53 _ _))                         -- ✱4·53·6
      _ ≡ .neg (QF.and (relHolds x R y) (relHolds x (∸S') y)) :=
          qiffNeg (qandCongrR _ (qiffSymm (q23_35 S' x y)))                         -- [✱23·35]
      _ ≡ .neg (relHolds x (R ∸ S') y) := qiffNeg (qiffSymm (q23_33 R (∸S') x y))     -- [✱23·33] (1)
  calc (R ⪽ S')
      ≡ all2 (fun x y => .neg (relHolds x (R ∸ S') y)) := QThm.mp (q11_11 h1) (q11_33 _ _)  -- (1).✱11·11·33
    _ ≡ relEq (R ∸ S') Λ̇ := q25_15 _                                               -- [✱25·15]

/-- ✱25·31 `⊢ : R ⪽ S . ≡ . ∸R ⊍ S = V̇`, as ✱24·31. ✱23·35 acts on the first disjunct (✱4·37), under (x, y). -/
theorem q25_31 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (iff (R ⪽ S') (relEq (∸R ⊍ S') 𝐕̇)) :=
  calc (R ⪽ S')
      ≡ all2 (fun x y => .or (.neg (relHolds x R y)) (relHolds x S' y)) :=
        QThm.mp (q11_11 fun _ _ => QL.t4_6 _ _) (q11_33 _ _)                       -- ✱4·6 [✱11·11·33]
    _ ≡ all2 (fun x y => .or (relHolds x (∸R) y) (relHolds x S' y)) :=
        QThm.mp (q11_11 fun x y => QThm.mp (qiffSymm (q23_35 R x y)) (QL.t4_37 _ _ _))
          (q11_33 _ _)                                                            -- [✱23·35]
    _ ≡ all2 (fun x y => relHolds x (∸R ⊍ S') y) :=
        QThm.mp (q11_11 fun x y => qiffSymm (q23_34 _ _ x y)) (q11_33 _ _)        -- [✱23·34]
    _ ≡ relEq (∸R ⊍ S') 𝐕̇ := q25_14 _                                              -- [✱25·14]

/-- ✱25·311 `⊢ : R ⪽ ∸S . ≡ . R ∩̇ S = Λ̇`, as ✱24·311. In the first line ✱23·35 acts on the consequent
    (✱4·85); "[✱4·51·62]" is ✱4·62 and ✱4·51 from right to left; ✱23·33 acts inside the negation (✱4·11). -/
theorem q25_311 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (iff (R ⪽ ∸S') (relEq (R ∩̇ S') Λ̇)) :=
  have h1 : ∀ x y, QThm S (iff (imp (relHolds x R y) (relHolds x (∸S') y)) (.neg (relHolds x (R ∩̇ S') y))) :=
    fun x y =>
    calc imp (relHolds x R y) (relHolds x (∸S') y)
        ≡ imp (relHolds x R y) (.neg (relHolds x S' y)) := QThm.mp (q23_35 S' x y) (QL.t4_85 _ _ _)  -- ✱23·35
      _ ≡ .neg (QF.and (relHolds x R y) (relHolds x S' y)) :=
          qiffTrans (QL.t4_62 _ _) (qiffSymm (QL.t4_51 _ _))                        -- [✱4·51·62]
      _ ≡ .neg (relHolds x (R ∩̇ S') y) := qiffNeg (qiffSymm (q23_33 R S' x y))        -- [✱23·33] (1)
  calc (R ⪽ ∸S')
      ≡ all2 (fun x y => .neg (relHolds x (R ∩̇ S') y)) := QThm.mp (q11_11 h1) (q11_33 _ _)  -- (1).✱11·11·33
    _ ≡ relEq (R ∩̇ S') Λ̇ := q25_15 _                                               -- [✱25·15]

/-- ✱25·312 `⊢ : ∸R ⪽ S . ≡ . R ⊍ S = V̇`, as ✱24·312. ✱23·35 acts on the antecedent (✱4·84), under (x, y). -/
theorem q25_312 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (iff (∸R ⪽ S') (relEq (R ⊍ S') 𝐕̇)) :=
  calc (∸R ⪽ S')
      ≡ fimp2 (fun x y => .neg (relHolds x R y)) (fun x y => relHolds x S' y) :=
        QThm.mp (q11_11 fun x y => QThm.mp (q23_35 R x y) (QL.t4_84 _ _ _)) (q11_33 _ _)  -- ✱23·35
    _ ≡ all2 (fun x y => .or (relHolds x R y) (relHolds x S' y)) :=
        QThm.mp (q11_11 fun _ _ => QL.t4_64 _ _) (q11_33 _ _)                     -- [✱4·64]
    _ ≡ all2 (fun x y => relHolds x (R ⊍ S') y) :=
        QThm.mp (q11_11 fun x y => qiffSymm (q23_34 _ _ x y)) (q11_33 _ _)        -- [✱23·34]
    _ ≡ relEq (R ⊍ S') 𝐕̇ := q25_14 _                                               -- [✱25·14]

/-- ✱25·313 `⊢ : R ∩̇ S = Λ̇ . ≡ . R ∸ S = R`, as ✱24·313 [✱24·311 . ✱22·621], read from the 1910 print
    (p. 242), which here differs from its analogue: ✱24·313's second member is α = α − β, ✱25·313's is
    R ∸ S = R, the identity the other way round. ✱23·621 gives R ∩̇ ∸S = R, which is R ∸ S = R (✱23·05), so
    the turn by ✱20·21 that ✱24·313 needs is not needed here. -/
theorem q25_313 [Reducibility S] (R S' : V a → V b → QF V) :
    QThm S (iff (relEq (R ∩̇ S') Λ̇) (relEq (R ∸ S') R)) :=
  calc relEq (R ∩̇ S') Λ̇
      ≡ (R ⪽ ∸S') := qiffSymm (q25_311 R S')                                       -- ✱25·311
    _ ≡ relEq (R ∸ S') R := q23_621 R (∸S')                                        -- ✱23·621

/-- ✱25·32 `⊢ : R ⊍ S = Λ̇ . ≡ . R = Λ̇ . S = Λ̇`, as ✱24·32. ✱25·13 is used for both factors, joined by ✱4·38.
    As in ✱24·32's statement, the dots beside ≡ are single, like the dot of logical product; a dot of logical
    product has less force than a dot of the same number beside ≡ (p. 10), so ≡ is the main connective. -/
theorem q25_32 [Reducibility S] (R S' : V a → V b → QF V) :
    QThm S (iff (relEq (R ⊍ S') Λ̇) (QF.and (relEq R Λ̇) (relEq S' Λ̇))) :=
  calc relEq (R ⊍ S') Λ̇
      ≡ (R ⊍ S' ⪽ Λ̇) := q25_13 _                                                   -- ✱25·13
    _ ≡ QF.and (R ⪽ Λ̇) (S' ⪽ Λ̇) := qiffSymm (q23_59 R S' Λ̇)                         -- [✱23·59]
    _ ≡ QF.and (relEq R Λ̇) (relEq S' Λ̇) :=
        QThm.mp (qandI (qiffSymm (q25_13 R)) (qiffSymm (q25_13 S'))) (QL.t4_38 _ _ _ _)  -- [✱25·13]

/-- ✱25·33 `⊢ : R = V̇ . ⊃ . R ⊍ S = V̇`, as ✱24·33: "[✱24·27 . ✱22·57]" is two lines. -/
theorem q25_33 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (imp (relEq R 𝐕̇) (relEq (R ⊍ S') 𝐕̇)) :=
  show R ⊍ S' ≑[relEq R 𝐕̇] 𝐕̇ from
  calc R ⊍ S'
      ≑[relEq R 𝐕̇] 𝐕̇ ⊍ S' := q23_551 R 𝐕̇ S'                                        -- ✱23·551
    _ ≑ S' ⊍ 𝐕̇ := q23_57 _ _                                                      -- [✱23·57]
    _ ≑ 𝐕̇ := q25_27 S'                                                            -- [✱25·27]

/-- ✱25·34 `⊢ : R = Λ̇ . ⊃ . R ∩̇ S = Λ̇`, as ✱24·34 [✱22·481 . ✱24·23], with ✱23·51 for ✱25·23's S ∩̇ Λ̇. -/
theorem q25_34 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (imp (relEq R Λ̇) (relEq (R ∩̇ S') Λ̇)) :=
  show R ∩̇ S' ≑[relEq R Λ̇] Λ̇ from
  calc R ∩̇ S'
      ≑[relEq R Λ̇] Λ̇ ∩̇ S' := q23_481 R Λ̇ S'                                        -- ✱23·481
    _ ≑ S' ∩̇ Λ̇ := q23_51 _ _
    _ ≑ Λ̇ := q25_23 S'                                                            -- ✱25·23

/-- ✱25·35 `⊢ : R = V̇ . ⊃ . R ∩̇ S = S`, as ✱24·35 [✱22·481 . ✱24·26], with ✱23·51 for ✱25·26's S ∩̇ V̇. -/
theorem q25_35 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (imp (relEq R 𝐕̇) (relEq (R ∩̇ S') S')) :=
  show R ∩̇ S' ≑[relEq R 𝐕̇] S' from
  calc R ∩̇ S'
      ≑[relEq R 𝐕̇] 𝐕̇ ∩̇ S' := q23_481 R 𝐕̇ S'                                        -- ✱23·481
    _ ≑ S' ∩̇ 𝐕̇ := q23_51 _ _
    _ ≑ S' := q25_26 S'                                                           -- ✱25·26

/-- ✱25·36 `⊢ : R = Λ̇ . ⊃ . R ⊍ S = S`, as ✱24·36 [✱22·551 . ✱24·24], with ✱23·57 for ✱25·24's S ⊍ Λ̇. -/
theorem q25_36 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (imp (relEq R Λ̇) (relEq (R ⊍ S') S')) :=
  show R ⊍ S' ≑[relEq R Λ̇] S' from
  calc R ⊍ S'
      ≑[relEq R Λ̇] Λ̇ ⊍ S' := q23_551 R Λ̇ S'                                        -- ✱23·551
    _ ≑ S' ⊍ Λ̇ := q23_57 _ _
    _ ≑ S' := q25_24 S'                                                           -- ✱25·24

/-- ✱25·37 `⊢ :: R ∩̇ S = Λ̇ . ≡ :. xRy . zSw . ⊃_{x,y,z,w} : x ≠ z . ∨ . y ≠ w`, the statement as corrected
    in the Gutenberg transcription. The 1910 print has zRw for zSw (scan, p. 242), which is not a theorem:
    with S = Λ̇ and R holding between some x and y, the left side holds and the right fails at z = x, w = y.
    The corrected statement is the analogue of ✱24·37, and is the one proved. The source of the correction
    is not yet identified: the Errata page bound into the 1910 print has no entry for p. 242, and the
    ebook's Transcriber's Note says only that all items in the Errata, from all three volumes, were applied.

    (x, y, z, w) is (x, y) : (z, w), as ✱11·02 has (x, y, z) = (x) : (y, z), and ⊃_{x,y,z,w} is ✱11·05's
    pattern. As ✱24·37: ✱25·15 and ✱23·33 (under (x, y), ✱11·11·33); "[✱13·191]" is its two-variable form
    ✱13·21, at (z, w) ↦ ∼(xRy . zSw) for each x, y, whose z = x . w = y is written x = z . y = w (✱13·16 for
    each factor, ✱4·38, with ✱4·84, under (z, w)); "[Transp]" is ✱2·03 both ways; and ∼(x = z . y = w) is
    x ≠ z . ∨ . y ≠ w by ✱4·51 (✱4·85, under (x, y, z, w)). -/
theorem q25_37 [Reducibility S] (R S' : V a → V b → QF V) :
    QThm S (iff (relEq (R ∩̇ S') Λ̇) (all2 fun x y =>
      fimp2 (fun z w => QF.and (relHolds x R y) (relHolds z S' w)) fun z w => .or (nident x z) (nident y w))) :=
  have h13 : ∀ x y, QThm S (iff (.neg (QF.and (relHolds x R y) (relHolds x S' y)))
      (all2 fun z w => imp (QF.and (ident x z) (ident y w)) (.neg (QF.and (relHolds x R y) (relHolds z S' w))))) :=
    fun x y =>
    qiffSymm <|
      calc all2 (fun z w => imp (QF.and (ident x z) (ident y w)) (.neg (QF.and (relHolds x R y) (relHolds z S' w))))
          ≡ fimp2 (fun z w => QF.and (ident z x) (ident w y))
              (fun z w => .neg (QF.and (relHolds x R y) (relHolds z S' w))) :=
            QThm.mp (q11_11 fun z w => QThm.mp (qandIffCongr (q13_16 x z) (q13_16 y w)) (QL.t4_84 _ _ _))
              (q11_33 _ _)
        _ ≡ .neg (QF.and (relHolds x R y) (relHolds x S' y)) :=
            q13_21 (fun z w => .neg (QF.and (relHolds x R y) (relHolds z S' w))) x y
  calc relEq (R ∩̇ S') Λ̇
      ≡ all2 (fun x y => .neg (relHolds x (R ∩̇ S') y)) := qiffSymm (q25_15 _)        -- ✱25·15
    _ ≡ all2 (fun x y => .neg (QF.and (relHolds x R y) (relHolds x S' y))) :=
        QThm.mp (q11_11 fun x y => qiffNeg (q23_33 R S' x y)) (q11_33 _ _)        -- [✱23·33]
    _ ≡ all2 (fun x y => all2 fun z w =>
          imp (QF.and (ident x z) (ident y w)) (.neg (QF.and (relHolds x R y) (relHolds z S' w)))) :=
        QThm.mp (q11_11 h13) (q11_33 _ _)                                         -- [✱13·191]
    _ ≡ all2 (fun x y => fimp2 (fun z w => QF.and (relHolds x R y) (relHolds z S' w))
          fun z w => .neg (QF.and (ident x z) (ident y w))) :=
        QThm.mp (q11_11 fun _ _ =>
          QThm.mp (q11_11 fun _ _ => qiffI (QL.t2_03 _ _) (QL.t2_03 _ _)) (q11_33 _ _)) (q11_33 _ _)  -- [Transp]
    _ ≡ all2 (fun x y => fimp2 (fun z w => QF.and (relHolds x R y) (relHolds z S' w))
          fun z w => .or (nident x z) (nident y w)) :=
        QThm.mp (q11_11 fun _ _ =>
          QThm.mp (q11_11 fun _ _ => QThm.mp (QL.t4_51 _ _) (QL.t4_85 _ _ _)) (q11_33 _ _)) (q11_33 _ _)  -- ✱4·51

/-- R ∩̇ S = Λ̇ . R = S . ⊃ . R ∩̇ R = Λ̇, the first line of ✱25·38 and of ✱25·57, as `qinterSelfNull` is of
    ✱24·38 and ✱24·57 [✱22·481]: ✱23·481 gives R ∩̇ R = S ∩̇ R, and S ∩̇ R = R ∩̇ S (✱23·51) = Λ̇, joined by
    ✱21·22. -/
theorem qrelInterSelfNull [Reducibility S] (R S' : V a → V b → QF V) :
    QThm S (imp (QF.and (relEq (R ∩̇ S') Λ̇) (relEq R S')) (relEq (R ∩̇ R) Λ̇)) :=
  show R ∩̇ R ≑[QF.and (relEq (R ∩̇ S') Λ̇) (relEq R S')] Λ̇ from
  calc R ∩̇ R
      ≑[QF.and (relEq (R ∩̇ S') Λ̇) (relEq R S')] S' ∩̇ R := qsyl (QL.t3_27 _ _) (q23_481 R S' R)  -- ✱23·481
    _ ≑ R ∩̇ S' := q23_51 _ _
    _ ≑[QF.and (relEq (R ∩̇ S') Λ̇) (relEq R S')] Λ̇ := QL.t3_26 _ _

/-- ✱25·38 `⊢ :. R ∩̇ S = Λ̇ . ⊃ : R ≠ S . ∨ . R = Λ̇ . S = Λ̇`, as ✱24·38. "[✱22·5]": R = R ∩̇ R (✱23·5, turned
    by ✱21·21) replaces R ∩̇ R in R ∩̇ R = Λ̇ (✱21·22·23, `qrelEqL`); "[✱20·23]" is ✱21·23, which takes R = S
    from Hp (✱3·27), joined by Comp (✱3·43). -/
theorem q25_38 [Reducibility S] (R S' : V a → V b → QF V) :
    QThm S (imp (relEq (R ∩̇ S') Λ̇) (.or (.neg (relEq R S')) (QF.and (relEq R Λ̇) (relEq S' Λ̇)))) :=
  let H := QF.and (relEq (R ∩̇ S') Λ̇) (relEq R S')
  have l1 : QThm S (imp H (relEq (R ∩̇ R) Λ̇)) := qrelInterSelfNull R S'           -- ✱23·481
  have l2 : QThm S (imp H (relEq R Λ̇)) :=
    qsyl l1 (qiffMp (QThm.mp (q23_5 R) (qrelEqL _ _ Λ̇)))                           -- [✱23·5]
  have h1 : QThm S (imp H (QF.and (relEq R Λ̇) (relEq S' Λ̇))) :=
    qcomp l2 (qsyl (qcomp (QL.t3_27 _ _) l2) (q21_23 R S' Λ̇))                       -- [✱21·23] (1)
  calc relEq (R ∩̇ S') Λ̇
      ⊃ imp (relEq R S') (QF.and (relEq R Λ̇) (relEq S' Λ̇)) := QThm.mp h1 (QL.t3_3 _ _ _)  -- (1).Exp
    _ ⊃ .or (.neg (relEq R S')) (QF.and (relEq R Λ̇) (relEq S' Λ̇)) := qiffMp (QL.t4_6 _ _)  -- [✱4·6]

/-- ✱25·39 `⊢ :. R ∩̇ S = Λ̇ . ≡ : xRy . ⊃_{x,y} . ∼(xSy)`, as ✱24·39 [✱24·311 . ✱22·35], ✱23·35 on the
    consequent (✱4·85, under (x, y), ✱11·11·33). -/
theorem q25_39 [Reducibility S] (R S' : V a → V b → QF V) :
    QThm S (iff (relEq (R ∩̇ S') Λ̇) (fimp2 (fun x y => relHolds x R y) fun x y => .neg (relHolds x S' y))) :=
  calc relEq (R ∩̇ S') Λ̇
      ≡ (R ⪽ ∸S') := qiffSymm (q25_311 R S')                                       -- ✱25·311
    _ ≡ fimp2 (fun x y => relHolds x R y) (fun x y => .neg (relHolds x S' y)) :=
        QThm.mp (q11_11 fun x y => QThm.mp (q23_35 S' x y) (QL.t4_85 _ _ _)) (q11_33 _ _)  -- ✱23·35

/-! ## ✱25·4–✱25·495: the analogues of ✱24's lemmas "for use in much later propositions" -/

/-- ✱23·68 with the common factor second: `⊢ . (Q ⊍ R) ∩̇ T = (Q ∩̇ T) ⊍ (R ∩̇ T)`, as `qclsDistribRight`.
    ✱23·68 at T, Q, R (read from right to left, ✱21·21), each product commuted by ✱23·51 (inside a relation:
    `qrelEqCongr`). -/
theorem qrelDistribRight [Reducibility S] (Q R T : V a → V b → QF V) :
    QThm S (relEq ((Q ⊍ R) ∩̇ T) ((Q ∩̇ T) ⊍ (R ∩̇ T))) :=
  show (Q ⊍ R) ∩̇ T ≑ (Q ∩̇ T) ⊍ (R ∩̇ T) from
  calc (Q ⊍ R) ∩̇ T
      ≑ T ∩̇ (Q ⊍ R) := q23_51 _ _                                                 -- ✱23·51
    _ ≑ (T ∩̇ Q) ⊍ (T ∩̇ R) := qrelEqSymm (q23_68 T Q R)                              -- ✱23·68
    _ ≑ (Q ∩̇ T) ⊍ (T ∩̇ R) := QThm.mp (q23_51 T Q) (qrelEqCongr (fun X => X ⊍ (T ∩̇ R)) _ _ (by rel_expr))  -- ✱23·51
    _ ≑ (Q ∩̇ T) ⊍ (R ∩̇ T) := QThm.mp (q23_51 T R) (qrelEqCongr (fun X => (Q ∩̇ T) ⊍ X) _ _ (by rel_expr))  -- ✱23·51

/-- ✱25·4 `⊢ : P ∩̇ Q = Λ̇ . ≡ . (P ⊍ Q) ∸ P = Q . ≡ . (P ⊍ Q) ∸ Q = P`, the chain stated as A ≡ B . B ≡ C, as
    ✱24·4 is; ✱24·4's (1) and (2) are A ≡ B and A ≡ C, joined by ✱4·21 and ✱4·22. In (1), ✱25·311 at Q, P has
    Q ∩̇ P, written P ∩̇ Q by ✱23·51 (with ✱21·22·23, `qrelEqL`), and ✱23·9 at Q, P has (Q ⊍ P) ∸ P, written
    (P ⊍ Q) ∸ P by ✱23·57 (inside a relation, `qrelEqCongr`). In (2), "[✱22·51·57]" (✱23·51·57) rewrites (1)
    at Q, P the same way. -/
theorem q25_4 [Reducibility S] (P Q : V a → V b → QF V) :
    QThm S (QF.and (iff (relEq (P ∩̇ Q) Λ̇) (relEq ((P ⊍ Q) ∸ P) Q))
      (iff (relEq ((P ⊍ Q) ∸ P) Q) (relEq ((P ⊍ Q) ∸ Q) P))) :=
  have h1 : ∀ P Q : V a → V b → QF V, QThm S (iff (relEq (P ∩̇ Q) Λ̇) (relEq ((P ⊍ Q) ∸ P) Q)) := fun P Q =>
    have e : QThm S (relEq ((P ⊍ Q) ∸ P) (Q ∸ P)) :=
      show (P ⊍ Q) ∸ P ≑ Q ∸ P from
      calc (P ⊍ Q) ∸ P
          ≑ (Q ⊍ P) ∸ P := QThm.mp (q23_57 P Q) (qrelEqCongr (fun X => X ∸ P) _ _ (by rel_expr))
        _ ≑ Q ∸ P := q23_9 Q P
    calc relEq (P ∩̇ Q) Λ̇
        ≡ relEq (Q ∩̇ P) Λ̇ := QThm.mp (q23_51 P Q) (qrelEqL _ _ Λ̇)
      _ ≡ (Q ⪽ ∸P) := qiffSymm (q25_311 Q P)                                       -- ✱25·311
      _ ≡ relEq (Q ∸ P) Q := q23_621 Q (∸P)                                        -- [✱23·621]
      _ ≡ relEq ((P ⊍ Q) ∸ P) Q := qiffSymm (QThm.mp e (qrelEqL _ _ Q))            -- [✱23·9] (1)
  have h2 : QThm S (iff (relEq (P ∩̇ Q) Λ̇) (relEq ((P ⊍ Q) ∸ Q) P)) :=
    calc relEq (P ∩̇ Q) Λ̇
        ≡ relEq (Q ∩̇ P) Λ̇ := QThm.mp (q23_51 P Q) (qrelEqL _ _ Λ̇)
      _ ≡ relEq ((Q ⊍ P) ∸ Q) P := h1 Q P                                         -- (1) Q, P / P, Q
      _ ≡ relEq ((P ⊍ Q) ∸ Q) P :=
          QThm.mp (QThm.mp (q23_57 Q P) (qrelEqCongr (fun X => X ∸ Q) _ _ (by rel_expr))) (qrelEqL _ _ P)  -- [✱23·51·57] (2)
  qandI (h1 P Q) (qiffTrans (qiffSymm (h1 P Q)) h2)                                 -- (1).(2)

/-- ✱25·401 `⊢ : Q ⪽ P . ⊃ . (Q ⊍ R) ∸ P = R ∸ P`, as ✱24·401. (1) is ✱23·68 with the common factor second
    (`qrelDistribRight`); in (1).(2), Q ∸ P = Λ̇ is put for Q ∸ P in the sum (✱23·551), and "[✱24·24]" (✱25·24)
    has the sum in the other order (✱23·57). -/
theorem q25_401 [Reducibility S] (P Q R : V a → V b → QF V) :
    QThm S (imp (Q ⪽ P) (relEq ((Q ⊍ R) ∸ P) (R ∸ P))) :=
  show (Q ⊍ R) ∸ P ≑[Q ⪽ P] R ∸ P from
  calc (Q ⊍ R) ∸ P
      ≑ (Q ∸ P) ⊍ (R ∸ P) := qrelDistribRight Q R (∸P)                             -- ✱23·68 (1)
    _ ≑[Q ⪽ P] Λ̇ ⊍ (R ∸ P) := qsyl (qiffMp (q25_3 Q P)) (q23_551 _ _ _)              -- ✱25·3 (2) . (1).(2)
    _ ≑ (R ∸ P) ⊍ Λ̇ := q23_57 _ _
    _ ≑ R ∸ P := q25_24 _                                                         -- [✱25·24]

/-- ✱25·402 `⊢ : P ∩̇ Q = Λ̇ . R ⪽ P . S ⪽ Q . ⊃ . R ∩̇ S = Λ̇`, as ✱24·402. The factors of Hp are taken by Simp
    (✱3·26, ✱3·27, Comp ✱3·43); "[✱22·55]" (✱23·55) uses Hp's P ∩̇ Q = Λ̇ (✱3·35, `qimpMpH`). -/
theorem q25_402 [Reducibility S] (P Q R S' : V a → V b → QF V) :
    QThm S (imp (QF.and (QF.and (relEq (P ∩̇ Q) Λ̇) (R ⪽ P)) (S' ⪽ Q)) (relEq (R ∩̇ S') Λ̇)) :=
  let H := QF.and (QF.and (relEq (P ∩̇ Q) Λ̇) (R ⪽ P)) (S' ⪽ Q)
  have hA : QThm S (imp H (relEq (P ∩̇ Q) Λ̇)) := qsyl (QL.t3_26 _ _) (QL.t3_26 _ _)
  have hB : QThm S (imp H (QF.and (R ⪽ P) (S' ⪽ Q))) :=
    qcomp (qsyl (QL.t3_26 _ _) (QL.t3_27 _ _)) (QL.t3_27 _ _)
  have l1 : QThm S (imp H (R ∩̇ S' ⪽ P ∩̇ Q)) := qsyl hB (q23_49 R P S' Q)           -- ✱23·49
  have l2 : QThm S (imp H (R ∩̇ S' ⪽ Λ̇)) :=
    qimpMpH l1 (qsyl hA (qsyl (q23_55 _ _ _) (QL.t3_26 _ _)))                       -- [✱23·55]
  qsyl l2 (qiffMpr (q25_13 _))                                                    -- [✱25·13]

/-- ✱25·41 `⊢ . R = (R ∩̇ S) ⊍ (R ∸ S)`, as ✱24·41. ✱24·41's lines prove (α ∩ β) ∪ (α − β) = α, turned by
    ✱21·21; "[✱24·22]" (✱25·22) puts V̇ for S ⊍ ∸S inside R ∩̇ (S ⊍ ∸S) (`qrelEqCongr`). -/
theorem q25_41 [Reducibility S] (R S' : V a → V b → QF V) : QThm S (relEq R ((R ∩̇ S') ⊍ (R ∸ S'))) :=
  qrelEqSymm <|
    show (R ∩̇ S') ⊍ (R ∸ S') ≑ R from
    calc (R ∩̇ S') ⊍ (R ∸ S')
        ≑ R ∩̇ (S' ⊍ ∸S') := q23_68 R S' (∸S')                                       -- ✱23·68
      _ ≑ R ∩̇ 𝐕̇ := QThm.mp (q25_22 S') (qrelEqCongr (fun X => R ∩̇ X) _ _ (by rel_expr))            -- [✱25·22]
      _ ≑ R := q25_26 R                                                           -- [✱25·26]

/-- ✱25·411 `⊢ : S ⪽ R . ⊃ . R = S ⊍ (R ∸ S)`, as ✱24·411. ✱23·633 at S, R, R ∸ S gives (S ∩̇ R) ⊍ (R ∸ S),
    written (R ∩̇ S) ⊍ (R ∸ S) (✱23·51, inside the sum); ✱25·41 is turned by ✱21·21, and so is the result. -/
theorem q25_411 [Reducibility S] (R S' : V a → V b → QF V) :
    QThm S (imp (S' ⪽ R) (relEq R (S' ⊍ (R ∸ S')))) :=
  have h : QThm S (imp (S' ⪽ R) (relEq (S' ⊍ (R ∸ S')) R)) :=
    show S' ⊍ (R ∸ S') ≑[S' ⪽ R] R from
    calc S' ⊍ (R ∸ S')
        ≑[S' ⪽ R] (S' ∩̇ R) ⊍ (R ∸ S') := q23_633 S' R (R ∸ S')                       -- ✱23·633
      _ ≑ (R ∩̇ S') ⊍ (R ∸ S') := QThm.mp (q23_51 S' R) (q23_551 _ _ _)
      _ ≑ R := qrelEqSymm (q25_41 R S')                                           -- [✱25·41]
  qsyl h (qiffMp (q21_21 _ _))

/-- ✱25·412 `⊢ : Q ⪽ P . S ⪽ Q . ⊃ . (P ∸ Q) ⊍ (Q ∸ S) = P ∸ S`, the statement as corrected in the Gutenberg
    transcription. The 1910 print has R ⪽ Q for S ⪽ Q (scan, p. 242), a hypothesis about a relation the conclusion does not
    mention, which is not a theorem: with Q = Λ̇, R = Λ̇ and P = S = V̇ the hypothesis holds, the left side is
    V̇ and the right Λ̇ (in non-empty types). The corrected statement is the analogue of ✱24·412, and is the
    one proved. The source of the correction is not yet identified: the Errata page bound into the 1910
    print has no entry for p. 242, and the ebook's Transcriber's Note says only that all items in the
    Errata, from all three volumes, were applied.

    As ✱24·412: the first line is ✱25·41 at P ∸ Q, S inside the sum (✱23·551). "[✱24·3·23]": (P ∸ Q) ∩̇ S is
    P ∩̇ (S ∸ Q) (✱23·52, ✱23·51), which is P ∩̇ Λ̇ by ✱25·3 and Hp, and Λ̇ by ✱25·23; the term Λ̇ is dropped
    by ✱23·57 and ✱25·24. "[✱22·68]" is ✱23·68 with the common factor second (`qrelDistribRight`), from right
    to left. "[✱24·411]" has (P ∸ Q) ⊍ Q in the other order (✱23·57). Each line acts inside a relation by
    `qrelEqCongr`. -/
theorem q25_412 [Reducibility S] (P Q S' : V a → V b → QF V) :
    QThm S (imp (QF.and (Q ⪽ P) (S' ⪽ Q)) (relEq ((P ∸ Q) ⊍ (Q ∸ S')) (P ∸ S'))) :=
  let H := QF.and (Q ⪽ P) (S' ⪽ Q)
  have hz : QThm S (imp H (relEq ((P ∸ Q) ∩̇ S') Λ̇)) :=
    show (P ∸ Q) ∩̇ S' ≑[H] Λ̇ from
    calc (P ∸ Q) ∩̇ S'
        ≑ P ∩̇ (∸Q ∩̇ S') := q23_52 P (∸Q) S'
      _ ≑ P ∩̇ (S' ∸ Q) := QThm.mp (q23_51 (∸Q) S') (qrelEqCongr (fun X => P ∩̇ X) _ _ (by rel_expr))
      _ ≑[H] P ∩̇ Λ̇ :=
          qsyl (QL.t3_27 _ _) (qsyl (qiffMp (q25_3 S' Q)) (qrelEqCongr (fun X => P ∩̇ X) _ _ (by rel_expr)))  -- ✱25·3
      _ ≑ Λ̇ := q25_23 P                                                           -- ✱25·23
  have hQ : QThm S (imp H (relEq ((P ∸ Q) ⊍ Q) P)) :=
    show (P ∸ Q) ⊍ Q ≑[H] P from
    calc (P ∸ Q) ⊍ Q
        ≑ Q ⊍ (P ∸ Q) := q23_57 _ _
      _ ≑[H] P := qsyl (QL.t3_26 _ _) (qsyl (q25_411 P Q) (qiffMp (q21_21 _ _)))      -- ✱25·411
  show (P ∸ Q) ⊍ (Q ∸ S') ≑[H] P ∸ S' from
  calc (P ∸ Q) ⊍ (Q ∸ S')
      ≑ ((P ∸ Q) ∩̇ S' ⊍ ((P ∸ Q) ∸ S')) ⊍ (Q ∸ S') :=
        QThm.mp (q25_41 (P ∸ Q) S') (q23_551 _ _ _)                                 -- ✱25·41
    _ ≑[H] (Λ̇ ⊍ ((P ∸ Q) ∸ S')) ⊍ (Q ∸ S') :=
        qsyl hz (qrelEqCongr (fun X => (X ⊍ ((P ∸ Q) ∸ S')) ⊍ (Q ∸ S')) _ _ (by rel_expr))          -- [✱25·3·23]
    _ ≑ (((P ∸ Q) ∸ S') ⊍ Λ̇) ⊍ (Q ∸ S') := QThm.mp (q23_57 _ _) (q23_551 _ _ _)
    _ ≑ ((P ∸ Q) ∸ S') ⊍ (Q ∸ S') := QThm.mp (q25_24 _) (q23_551 _ _ _)
    _ ≑ ((P ∸ Q) ⊍ Q) ∸ S' := qrelEqSymm (qrelDistribRight (P ∸ Q) Q (∸S'))          -- [✱23·68]
    _ ≑[H] P ∸ S' := qsyl hQ (q23_481 _ _ _)                                        -- [✱25·411]

/-- ✱25·42 `⊢ : P ∩̇ Q ⪽ R . P ∸ Q ⪽ R . ≡ . P ⪽ R`, as ✱24·42. "[✱24·41]" (✱25·41) puts P for
    (P ∩̇ Q) ⊍ (P ∸ Q) by ✱23·54 (with ✱25·41 turned by ✱21·21). -/
theorem q25_42 [Reducibility S] (P Q R : V a → V b → QF V) :
    QThm S (iff (QF.and (P ∩̇ Q ⪽ R) (P ∸ Q ⪽ R)) (P ⪽ R)) :=
  calc QF.and (P ∩̇ Q ⪽ R) (P ∸ Q ⪽ R)
      ≡ ((P ∩̇ Q) ⊍ (P ∸ Q) ⪽ R) := q23_59 _ _ _                                     -- ✱23·59
    _ ≡ (P ⪽ R) := QThm.mp (qrelEqSymm (q25_41 P Q)) (q23_54 _ _ R)                 -- [✱25·41]

/-- ✱25·43 `⊢ : P ∸ Q ⪽ R . ≡ . P ⪽ Q ⊍ R`, as ✱24·43. The line of ✱5·6 is written from its first member:
    ✱23·33 and ✱23·35 (on the second factor, ✱4·36 with ✱4·3) act on the antecedent (✱4·84), ✱23·34 on the
    consequent (✱4·85); ✱10·11·271 for two variables is ✱11·11·33. -/
theorem q25_43 [Reducibility S] (P Q R : V a → V b → QF V) : QThm S (iff (P ∸ Q ⪽ R) (P ⪽ Q ⊍ R)) :=
  QThm.mp (q11_11 fun x y =>
    calc imp (relHolds x (P ∸ Q) y) (relHolds x R y)
        ≡ imp (QF.and (relHolds x P y) (.neg (relHolds x Q y))) (relHolds x R y) :=
          QThm.mp (qiffTrans (q23_33 P (∸Q) x y) (qandCongrR _ (q23_35 Q x y))) (QL.t4_84 _ _ _)  -- [✱23·35·33]
      _ ≡ imp (relHolds x P y) (.or (relHolds x Q y) (relHolds x R y)) := QL.t5_6 _ _ _  -- ✱5·6
      _ ≡ imp (relHolds x P y) (relHolds x (Q ⊍ R) y) :=
          QThm.mp (qiffSymm (q23_34 Q R x y)) (QL.t4_85 _ _ _))                     -- [✱23·34] (1)
    (q11_33 _ _)                                                                  -- (1).✱11·11·33

/-- ✱25·431 `⊢ . (P ⊍ R) ∩̇ (Q ⊍ ∸R) = (P ∩̇ Q) ⊍ (P ∸ R) ⊍ (Q ∩̇ R)`, as ✱24·431 (whose first term is (α ∩ β) in
    the print, p. 235; ✱25·431 is so printed too, p. 242). ✱24·431's first line is ✱23·68 from right to left;
    its second is ✱23·68 with the common factor second (`qrelDistribRight`) on both terms, the four terms
    regrouped by ✱23·7 (written without brackets, ✱23·71); "[✱22·51·57]" also needs ✱23·7. -/
theorem q25_431 [Reducibility S] (P Q R : V a → V b → QF V) :
    QThm S (relEq ((P ⊍ R) ∩̇ (Q ⊍ ∸R)) ((P ∩̇ Q) ⊍ (P ∸ R) ⊍ (Q ∩̇ R))) :=
  show (P ⊍ R) ∩̇ (Q ⊍ ∸R) ≑ (P ∩̇ Q) ⊍ (P ∸ R) ⊍ (Q ∩̇ R) from
  calc (P ⊍ R) ∩̇ (Q ⊍ ∸R)
      ≑ ((P ⊍ R) ∩̇ Q) ⊍ ((P ⊍ R) ∩̇ ∸R) := qrelEqSymm (q23_68 _ _ _)                  -- ✱23·68
    _ ≑ ((P ∩̇ Q) ⊍ (R ∩̇ Q)) ⊍ ((P ⊍ R) ∩̇ ∸R) := QThm.mp (qrelDistribRight P R Q) (q23_551 _ _ _)
    _ ≑ ((P ∩̇ Q) ⊍ (R ∩̇ Q)) ⊍ ((P ∸ R) ⊍ (R ∸ R)) :=
        QThm.mp (qrelDistribRight P R (∸R)) (qrelEqCongr (fun X => ((P ∩̇ Q) ⊍ (R ∩̇ Q)) ⊍ X) _ _ (by rel_expr))
    _ ≑ (P ∩̇ Q) ⊍ (R ∩̇ Q) ⊍ (P ∸ R) ⊍ (R ∸ R) := qrelEqSymm (q23_7 _ _ _)          -- [✱23·68]
    _ ≑ (P ∩̇ Q) ⊍ (R ∩̇ Q) ⊍ (P ∸ R) ⊍ Λ̇ :=
        QThm.mp (q25_21 R) (qrelEqCongr (fun X => (P ∩̇ Q) ⊍ (R ∩̇ Q) ⊍ (P ∸ R) ⊍ X) _ _ (by rel_expr))  -- [✱25·21]
    _ ≑ (P ∩̇ Q) ⊍ (R ∩̇ Q) ⊍ (P ∸ R) := q25_24 _                                     -- [✱25·24]
    _ ≑ (P ∩̇ Q) ⊍ ((R ∩̇ Q) ⊍ (P ∸ R)) := q23_7 _ _ _
    _ ≑ (P ∩̇ Q) ⊍ ((P ∸ R) ⊍ (R ∩̇ Q)) := QThm.mp (q23_57 _ _) (qrelEqCongr (fun X => (P ∩̇ Q) ⊍ X) _ _ (by rel_expr))
    _ ≑ (P ∩̇ Q) ⊍ (P ∸ R) ⊍ (R ∩̇ Q) := qrelEqSymm (q23_7 _ _ _)
    _ ≑ (P ∩̇ Q) ⊍ (P ∸ R) ⊍ (Q ∩̇ R) :=
        QThm.mp (q23_51 R Q) (qrelEqCongr (fun X => (P ∩̇ Q) ⊍ (P ∸ R) ⊍ X) _ _ (by rel_expr))       -- [✱23·51·57]

/-- ✱25·432 `⊢ . (P ∸ R) ⊍ (Q ∩̇ R) = (P ∩̇ Q) ⊍ (P ∸ R) ⊍ (Q ∩̇ R)`, as ✱24·432: its lines prove the identity
    from right to left (turned by ✱21·21). "✱24·22·35" is ✱25·35 with R ⊍ ∸R = V̇ (✱25·22; its product
    commuted, ✱23·51); "[✱22·51]" also needs ✱23·52 (P ∩̇ Q ∸ R is P ∩̇ ∸R ∩̇ Q); each "[✱22·63]" is ✱23·63 for a
    term absorbed by the term beside it, after ✱23·7, ✱23·57 (and ✱23·51, ✱23·52 for P ∩̇ Q ∩̇ R). -/
theorem q25_432 [Reducibility S] (P Q R : V a → V b → QF V) :
    QThm S (relEq ((P ∸ R) ⊍ (Q ∩̇ R)) ((P ∩̇ Q) ⊍ (P ∸ R) ⊍ (Q ∩̇ R))) :=
  have l1 : QThm S (relEq (P ∩̇ Q) (((P ∩̇ Q) ∩̇ R) ⊍ ((P ∸ R) ∩̇ Q))) :=
    show P ∩̇ Q ≑ ((P ∩̇ Q) ∩̇ R) ⊍ ((P ∸ R) ∩̇ Q) from
    calc P ∩̇ Q
        ≑ (R ⊍ ∸R) ∩̇ (P ∩̇ Q) := qrelEqSymm (QThm.mp (q25_22 R) (q25_35 _ _))          -- ✱25·22·35
      _ ≑ (P ∩̇ Q) ∩̇ (R ⊍ ∸R) := q23_51 _ _
      _ ≑ ((P ∩̇ Q) ∩̇ R) ⊍ ((P ∩̇ Q) ∸ R) := qrelEqSymm (q23_68 _ _ _)                  -- [✱23·68]
      _ ≑ ((P ∩̇ Q) ∩̇ R) ⊍ (P ∩̇ (Q ∸ R)) :=
          QThm.mp (q23_52 P Q (∸R)) (qrelEqCongr (fun X => ((P ∩̇ Q) ∩̇ R) ⊍ X) _ _ (by rel_expr))
      _ ≑ ((P ∩̇ Q) ∩̇ R) ⊍ (P ∩̇ (∸R ∩̇ Q)) :=
          QThm.mp (q23_51 Q (∸R)) (qrelEqCongr (fun X => ((P ∩̇ Q) ∩̇ R) ⊍ (P ∩̇ X)) _ _ (by rel_expr))
      _ ≑ ((P ∩̇ Q) ∩̇ R) ⊍ ((P ∸ R) ∩̇ Q) :=
          QThm.mp (qrelEqSymm (q23_52 P (∸R) Q)) (qrelEqCongr (fun X => ((P ∩̇ Q) ∩̇ R) ⊍ X) _ _ (by rel_expr))  -- [✱23·51]
  have l2 : QThm S (relEq ((P ∩̇ Q) ⊍ (P ∸ R)) ((P ∸ R) ⊍ ((P ∩̇ Q) ∩̇ R))) :=
    show (P ∩̇ Q) ⊍ (P ∸ R) ≑ (P ∸ R) ⊍ ((P ∩̇ Q) ∩̇ R) from
    calc (P ∩̇ Q) ⊍ (P ∸ R)
        ≑ ((P ∩̇ Q) ∩̇ R) ⊍ ((P ∸ R) ∩̇ Q) ⊍ (P ∸ R) := QThm.mp l1 (q23_551 _ _ _)        -- [✱23·551]
      _ ≑ ((P ∩̇ Q) ∩̇ R) ⊍ (((P ∸ R) ∩̇ Q) ⊍ (P ∸ R)) := q23_7 _ _ _
      _ ≑ ((P ∩̇ Q) ∩̇ R) ⊍ ((P ∸ R) ⊍ ((P ∸ R) ∩̇ Q)) :=
          QThm.mp (q23_57 _ _) (qrelEqCongr (fun X => ((P ∩̇ Q) ∩̇ R) ⊍ X) _ _ (by rel_expr))
      _ ≑ ((P ∩̇ Q) ∩̇ R) ⊍ (P ∸ R) :=
          QThm.mp (q23_63 (P ∸ R) Q) (qrelEqCongr (fun X => ((P ∩̇ Q) ∩̇ R) ⊍ X) _ _ (by rel_expr))    -- [✱23·63]
      _ ≑ (P ∸ R) ⊍ ((P ∩̇ Q) ∩̇ R) := q23_57 _ _                                     -- [✱23·57]
  qrelEqSymm <|
    show (P ∩̇ Q) ⊍ (P ∸ R) ⊍ (Q ∩̇ R) ≑ (P ∸ R) ⊍ (Q ∩̇ R) from
    calc (P ∩̇ Q) ⊍ (P ∸ R) ⊍ (Q ∩̇ R)
        ≑ (P ∸ R) ⊍ ((P ∩̇ Q) ∩̇ R) ⊍ (Q ∩̇ R) := QThm.mp l2 (q23_551 _ _ _)             -- [✱23·551]
      _ ≑ (P ∸ R) ⊍ (((P ∩̇ Q) ∩̇ R) ⊍ (Q ∩̇ R)) := q23_7 _ _ _
      _ ≑ (P ∸ R) ⊍ ((P ∩̇ (Q ∩̇ R)) ⊍ (Q ∩̇ R)) :=
          QThm.mp (q23_52 P Q R) (qrelEqCongr (fun X => (P ∸ R) ⊍ (X ⊍ (Q ∩̇ R))) _ _ (by rel_expr))
      _ ≑ (P ∸ R) ⊍ (((Q ∩̇ R) ∩̇ P) ⊍ (Q ∩̇ R)) :=
          QThm.mp (q23_51 P (Q ∩̇ R)) (qrelEqCongr (fun X => (P ∸ R) ⊍ (X ⊍ (Q ∩̇ R))) _ _ (by rel_expr))
      _ ≑ (P ∸ R) ⊍ ((Q ∩̇ R) ⊍ ((Q ∩̇ R) ∩̇ P)) :=
          QThm.mp (q23_57 _ _) (qrelEqCongr (fun X => (P ∸ R) ⊍ X) _ _ (by rel_expr))
      _ ≑ (P ∸ R) ⊍ (Q ∩̇ R) :=
          QThm.mp (q23_63 (Q ∩̇ R) P) (qrelEqCongr (fun X => (P ∸ R) ⊍ X) _ _ (by rel_expr))         -- [✱23·63]

/-- ✱25·44 `⊢ . (P ⊍ R) ∩̇ (Q ⊍ ∸R) = (P ∩̇ ∸R) ⊍ (Q ∩̇ R)`, as ✱24·44 [✱24·431·432], joined by ✱21·24. -/
theorem q25_44 [Reducibility S] (P Q R : V a → V b → QF V) :
    QThm S (relEq ((P ⊍ R) ∩̇ (Q ⊍ ∸R)) ((P ∩̇ ∸R) ⊍ (Q ∩̇ R))) :=
  QThm.mp (qandI (q25_431 P Q R) (q25_432 P Q R)) (q21_24 _ _ _)                    -- ✱25·431·432

/-- ✱25·45 `⊢ : (P ∩̇ R) ⊍ (Q ∸ R) = Λ̇ . ≡ . Q ⪽ R . R ⪽ ∸P`, as ✱24·45. "[✱24·3·311]": ✱25·311 at R, P has
    R ∩̇ P (✱23·51), and the two are joined by ✱4·38; the last line has the factors in the other order (✱4·3). -/
theorem q25_45 [Reducibility S] (P Q R : V a → V b → QF V) :
    QThm S (iff (relEq ((P ∩̇ R) ⊍ (Q ∸ R)) Λ̇) (QF.and (Q ⪽ R) (R ⪽ ∸P))) :=
  have h311 : QThm S (iff (relEq (P ∩̇ R) Λ̇) (R ⪽ ∸P)) :=
    qiffTrans (QThm.mp (q23_51 P R) (qrelEqL _ _ Λ̇)) (qiffSymm (q25_311 R P))
  calc relEq ((P ∩̇ R) ⊍ (Q ∸ R)) Λ̇
      ≡ QF.and (relEq (P ∩̇ R) Λ̇) (relEq (Q ∸ R) Λ̇) := q25_32 _ _                    -- ✱25·32
    _ ≡ QF.and (R ⪽ ∸P) (Q ⪽ R) :=
        QThm.mp (qandI h311 (qiffSymm (q25_3 Q R))) (QL.t4_38 _ _ _ _)              -- [✱25·3·311]
    _ ≡ QF.and (Q ⪽ R) (R ⪽ ∸P) := QL.t4_3 _ _

/-- ✱25·46 `⊢ : (P ∩̇ R) ⊍ (Q ∸ R) = Λ̇ . ⊃ . P ∩̇ Q = Λ̇`, as ✱24·46 (✱24·45 . ✱22·44, [✱22·811], [✱24·311]). -/
theorem q25_46 [Reducibility S] (P Q R : V a → V b → QF V) :
    QThm S (imp (relEq ((P ∩̇ R) ⊍ (Q ∸ R)) Λ̇) (relEq (P ∩̇ Q) Λ̇)) :=
  calc relEq ((P ∩̇ R) ⊍ (Q ∸ R)) Λ̇
      ⊃ (Q ⪽ ∸P) := qsyl (qiffMp (q25_45 P Q R)) (q23_44 Q R (∸P))                   -- ✱25·45.✱23·44
    _ ⊃ (P ⪽ ∸Q) := qiffMpr (q23_811 P Q)                                         -- [✱23·811]
    _ ⊃ relEq (P ∩̇ Q) Λ̇ := qiffMp (q25_311 P Q)                                   -- [✱25·311]

/-- ✱25·47 `⊢ : P ∩̇ Q = Λ̇ . P ⊍ Q = R . ≡ . P ⪽ R . Q = R ∸ P`, as printed (p. 243; the transcription has
    `(P ∩̇ Q) = Λ̇`, brackets the print does not have, the text audit's Vol I list, entry 19; they do not change
    the statement). As ✱24·47: in (1), ✱25·311 at Q, P has Q ∩̇ P (✱23·51); ✱23·59 and ✱25·43 (at R, P, Q) are
    joined by ✱4·38, and (1).(2) by ✱4·38. "[✱4·3]" is ✱4·3 with ✱4·32 (and ✱4·36). The step "[✱23·45]"
    needs ✱23·45 as an equivalence, as ✱24·47's "[✱22·45]" uses ✱22·45; the print states ✱23·45 with ⊃,
    so the step uses its variant `q23_45_iff`, as ✱23·74 does. -/
theorem q25_47 [Reducibility S] (P Q R : V a → V b → QF V) :
    QThm S (iff (QF.and (relEq (P ∩̇ Q) Λ̇) (relEq (P ⊍ Q) R)) (QF.and (P ⪽ R) (relEq Q (R ∸ P)))) :=
  have h1 : QThm S (iff (relEq (P ∩̇ Q) Λ̇) (Q ⪽ ∸P)) :=
    qiffTrans (QThm.mp (q23_51 P Q) (qrelEqL _ _ Λ̇)) (qiffSymm (q25_311 Q P))        -- ✱25·311 (1)
  have h2 : QThm S (iff (relEq (P ⊍ Q) R) (QF.and (QF.and (P ⪽ R) (Q ⪽ R)) (R ∸ P ⪽ Q))) :=
    calc relEq (P ⊍ Q) R
        ≡ QF.and (P ⊍ Q ⪽ R) (R ⪽ P ⊍ Q) := qiffSymm (q23_41 _ _)                    -- ✱23·41
      _ ≡ QF.and (QF.and (P ⪽ R) (Q ⪽ R)) (R ∸ P ⪽ Q) :=
          QThm.mp (qandI (qiffSymm (q23_59 P Q R)) (qiffSymm (q25_43 R P Q))) (QL.t4_38 _ _ _ _)  -- [✱23·59.✱25·43] (2)
  calc QF.and (relEq (P ∩̇ Q) Λ̇) (relEq (P ⊍ Q) R)
      ≡ QF.and (Q ⪽ ∸P) (QF.and (QF.and (P ⪽ R) (Q ⪽ R)) (R ∸ P ⪽ Q)) :=
        QThm.mp (qandI h1 h2) (QL.t4_38 _ _ _ _)                                   -- (1).(2)
    _ ≡ QF.and (Q ⪽ ∸P) (QF.and (P ⪽ R) (QF.and (Q ⪽ R) (R ∸ P ⪽ Q))) := qandCongrR _ (QL.t4_32 _ _ _)
    _ ≡ QF.and (P ⪽ R) (QF.and (Q ⪽ ∸P) (QF.and (Q ⪽ R) (R ∸ P ⪽ Q))) := qandPerm _ _ _
    _ ≡ QF.and (P ⪽ R) (QF.and (QF.and (Q ⪽ ∸P) (Q ⪽ R)) (R ∸ P ⪽ Q)) :=
        qandCongrR _ (qiffSymm (QL.t4_32 _ _ _))
    _ ≡ QF.and (P ⪽ R) (QF.and (QF.and (Q ⪽ R) (Q ⪽ ∸P)) (R ∸ P ⪽ Q)) :=
        qandCongrR _ (qandCongrL _ (QL.t4_3 _ _))                                  -- [✱4·3]
    _ ≡ QF.and (P ⪽ R) (QF.and (Q ⪽ R ∸ P) (R ∸ P ⪽ Q)) :=
        qandCongrR _ (qandCongrL _ (q23_45_iff Q R (∸P)))                          -- [✱23·45]
    _ ≡ QF.and (P ⪽ R) (relEq Q (R ∸ P)) := qandCongrR _ (q23_41 Q (R ∸ P))         -- [✱23·41]

/-- The hypothesis of ✱25·48: R ⪽ P . R' ⪽ P . S ⪽ Q . S' ⪽ Q . P ∩̇ Q = Λ̇, a product grouped from the left. -/
@[reducible] def hyp25_48 (P Q R R' S' S'' : V a → V b → QF V) : QF V :=
  QF.and (QF.and (QF.and (QF.and (R ⪽ P) (R' ⪽ P)) (S' ⪽ Q)) (S'' ⪽ Q)) (relEq (P ∩̇ Q) Λ̇)

/-- Line (8) of ✱24·48 for relations, for any relations: `Hp . ⊃ : R ⊍ S = R' ⊍ S' . ⊃ . R = R'`, as
    `qline24_48`. (2): ✱23·481, and "[✱22·68]" with the common factor second (`qrelDistribRight`) in both
    members (✱21·22·23, `qrelEqL`, `qrelEqR`). (3): ✱23·621 twice, joined by ✱3·47. (4): ✱23·48 gives
    S ∩̇ P ⪽ Q ∩̇ P, written P ∩̇ Q by ✱23·51 and ✱23·55; "[✱22·55]" uses P ∩̇ Q = Λ̇ (✱3·35, `qimpMpH`). (6),
    (7): the two identities joined by ✱23·73, then ✱25·24. (8): ✱21·22 under Hp, with ✱21·21, and Exp
    (✱3·3). The factors of Hp are taken by Simp (✱3·26, ✱3·27, Comp ✱3·43). -/
theorem qline25_48 [Reducibility S] (P Q R R' S' S'' : V a → V b → QF V) :
    QThm S (imp (hyp25_48 P Q R R' S' S'') (imp (relEq (R ⊍ S') (R' ⊍ S'')) (relEq R R'))) :=
  let H := hyp25_48 P Q R R' S' S''
  have p12 : QThm S (imp H (QF.and (R ⪽ P) (R' ⪽ P))) :=
    qsyl (QL.t3_26 _ _) (qsyl (QL.t3_26 _ _) (QL.t3_26 _ _))
  have pS : QThm S (imp H (S' ⪽ Q)) := qsyl (QL.t3_26 _ _) (qsyl (QL.t3_26 _ _) (QL.t3_27 _ _))
  have pS' : QThm S (imp H (S'' ⪽ Q)) := qsyl (QL.t3_26 _ _) (QL.t3_27 _ _)
  have pΛ : QThm S (imp H (relEq (P ∩̇ Q) Λ̇)) := QL.t3_27 _ _
  have h2 : QThm S (imp (relEq (R ⊍ S') (R' ⊍ S'')) (relEq ((R ∩̇ P) ⊍ (S' ∩̇ P)) ((R' ∩̇ P) ⊍ (S'' ∩̇ P)))) :=
    calc relEq (R ⊍ S') (R' ⊍ S'')
        ⊃ relEq ((R ⊍ S') ∩̇ P) ((R' ⊍ S'') ∩̇ P) := q23_481 _ _ P                      -- ✱23·481
      _ ≡ relEq ((R ∩̇ P) ⊍ (S' ∩̇ P)) ((R' ⊍ S'') ∩̇ P) := QThm.mp (qrelDistribRight R S' P) (qrelEqL _ _ _)
      _ ≡ relEq ((R ∩̇ P) ⊍ (S' ∩̇ P)) ((R' ∩̇ P) ⊍ (S'' ∩̇ P)) :=
          QThm.mp (qrelDistribRight R' S'' P) (qrelEqR _ _ _)                       -- [✱23·68] (2)
  have h3 : QThm S (imp (QF.and (R ⪽ P) (R' ⪽ P)) (QF.and (relEq (R ∩̇ P) R) (relEq (R' ∩̇ P) R'))) :=
    QThm.mp (qandI (qiffMp (q23_621 R P)) (qiffMp (q23_621 R' P))) (QL.t3_47 _ _ _ _)  -- ✱23·621 [✱3·47] (3)
  have h4 : ∀ T : V a → V b → QF V, QThm S (imp (QF.and (T ⪽ Q) (relEq (P ∩̇ Q) Λ̇)) (relEq (T ∩̇ P) Λ̇)) :=
    fun T =>
    have k : QThm S (imp (T ⪽ Q) (T ∩̇ P ⪽ P ∩̇ Q)) :=
      qsyl (q23_48 T Q P) (qiffMp (QThm.mp (q23_51 Q P) (q23_55 _ _ (T ∩̇ P))))       -- ✱23·48
    have k2 : QThm S (imp (QF.and (T ⪽ Q) (relEq (P ∩̇ Q) Λ̇)) (T ∩̇ P ⪽ Λ̇)) :=
      qimpMpH (qsyl (QL.t3_26 _ _) k) (qsyl (QL.t3_27 _ _) (qsyl (q23_55 _ _ _) (QL.t3_26 _ _)))  -- [✱23·55]
    qsyl k2 (qiffMpr (q25_13 _))                                                  -- [✱25·13] (4), (5)
  have h6 : QThm S (imp H (relEq ((R ∩̇ P) ⊍ (S' ∩̇ P)) R)) :=
    show (R ∩̇ P) ⊍ (S' ∩̇ P) ≑[H] R from
    calc (R ∩̇ P) ⊍ (S' ∩̇ P)
        ≑[H] R ⊍ Λ̇ :=
          qsyl (qcomp (qsyl p12 (qsyl h3 (QL.t3_26 _ _))) (qsyl (qcomp pS pΛ) (h4 S'))) (q23_73 _ _ _ _)  -- (3).(4)
      _ ≑ R := q25_24 R                                                           -- [✱25·24] (6)
  have h7 : QThm S (imp H (relEq ((R' ∩̇ P) ⊍ (S'' ∩̇ P)) R')) :=
    show (R' ∩̇ P) ⊍ (S'' ∩̇ P) ≑[H] R' from
    calc (R' ∩̇ P) ⊍ (S'' ∩̇ P)
        ≑[H] R' ⊍ Λ̇ :=
          qsyl (qcomp (qsyl p12 (qsyl h3 (QL.t3_27 _ _))) (qsyl (qcomp pS' pΛ) (h4 S''))) (q23_73 _ _ _ _)  -- (3).(5)
      _ ≑ R' := q25_24 R'                                                         -- [✱25·24] (7)
  let H2 := QF.and H (relEq (R ⊍ S') (R' ⊍ S''))
  have h8 : QThm S (imp H2 (relEq R R')) :=
    show R ≑[H2] R' from
    calc R
        ≑[H2] (R ∩̇ P) ⊍ (S' ∩̇ P) := qsyl (QL.t3_26 _ _) (qsyl h6 (qiffMp (q21_21 _ _)))  -- (6)
      _ ≑[H2] (R' ∩̇ P) ⊍ (S'' ∩̇ P) := qsyl (QL.t3_27 _ _) h2                        -- (2)
      _ ≑[H2] R' := qsyl (QL.t3_26 _ _) h7                                         -- (7)
  QThm.mp h8 (QL.t3_3 _ _ _)                                                       -- (2).(6).(7) (8)

/-- ✱25·48 `⊢ :. R ⪽ P . R' ⪽ P . S ⪽ Q . S' ⪽ Q . P ∩̇ Q = Λ̇ . ⊃ : R ⊍ S = R' ⊍ S' . ≡ . R = R' . S = S'`, Hp
    grouped from the left, as ✱24·48. (8) is `qline25_48`; "Similarly" (9) is (8) for S, S', R, R', Q, P, its
    Hp got from this one by Simp and Comp (with ✱23·51 for Q ∩̇ P) and its R ⊍ S, R' ⊍ S' commuted by ✱23·57
    (✱21·22·23, Syll ✱2·06). (1).(8).(9): the halves joined by ✱3·43, (1) put under Hp by ✱2·02. -/
theorem q25_48 [Reducibility S] (P Q R R' S' S'' : V a → V b → QF V) :
    QThm S (imp (QF.and (QF.and (QF.and (QF.and (R ⪽ P) (R' ⪽ P)) (S' ⪽ Q)) (S'' ⪽ Q)) (relEq (P ∩̇ Q) Λ̇))
      (iff (relEq (R ⊍ S') (R' ⊍ S'')) (QF.and (relEq R R') (relEq S' S'')))) :=
  let H := hyp25_48 P Q R R' S' S''
  let E := relEq (R ⊍ S') (R' ⊍ S'')
  have h1 : QThm S (imp (QF.and (relEq R R') (relEq S' S'')) E) := q23_73 R S' R' S''  -- ✱23·73 (1)
  have h8 : QThm S (imp H (imp E (relEq R R'))) := qline25_48 P Q R R' S' S''      -- (8)
  have hH' : QThm S (imp H (hyp25_48 Q P S' S'' R R')) :=
    qcomp (qcomp (qcomp (qcomp (qsyl (QL.t3_26 _ _) (qsyl (QL.t3_26 _ _) (QL.t3_27 _ _)))
      (qsyl (QL.t3_26 _ _) (QL.t3_27 _ _)))
      (qsyl (QL.t3_26 _ _) (qsyl (QL.t3_26 _ _) (qsyl (QL.t3_26 _ _) (QL.t3_26 _ _)))))
      (qsyl (QL.t3_26 _ _) (qsyl (QL.t3_26 _ _) (qsyl (QL.t3_26 _ _) (QL.t3_27 _ _)))))
      (qsyl (QL.t3_27 _ _) (qiffMp (QThm.mp (q23_51 P Q) (qrelEqL _ _ Λ̇))))
  have hsw : QThm S (imp E (relEq (S' ⊍ R) (S'' ⊍ R'))) :=
    qsyl (qiffMp (QThm.mp (q23_57 R S') (qrelEqL _ _ _))) (qiffMp (QThm.mp (q23_57 R' S'') (qrelEqR _ _ _)))
  have h9 : QThm S (imp H (imp E (relEq S' S''))) :=
    qsyl hH' (qsyl (qline25_48 Q P S' S'' R R') (QThm.mp hsw (QL.t2_06 _ _ _)))     -- Similarly (9)
  qcomp (qsyl (qcomp h8 h9) (QL.t3_43 _ _ _)) (QThm.mp h1 (QL.t2_02 H _))          -- (1).(8).(9)

/-- ✱25·481 `⊢ :. P ∩̇ Q = Λ̇ . P ∩̇ R = Λ̇ . ⊃ : P ⊍ Q = P ⊍ R . ≡ . Q = R`, as ✱24·481. (1) is ✱25·48 at
    P, ∸P, P, P, Q, R. In (2), the asserted factors P ⪽ P (✱23·42) and P ∸ P = Λ̇ (✱25·21) are dropped (✱4·73,
    ✱4·32, and ✱3·2, ✱3·27, `qand_true_left`), and ✱25·311 at Q, P and R, P has Q ∩̇ P, R ∩̇ P (✱23·51), joined
    by ✱4·38. (3): ✱4·73 has P = P second (✱4·3). (1).(2).(3): Hp gives (1)'s Hp by (2), and (3) replaces the
    second member (✱4·22, `qimpIffTransR`). -/
theorem q25_481 [Reducibility S] (P Q R : V a → V b → QF V) :
    QThm S (imp (QF.and (relEq (P ∩̇ Q) Λ̇) (relEq (P ∩̇ R) Λ̇))
      (iff (relEq (P ⊍ Q) (P ⊍ R)) (relEq Q R))) :=
  have h1 := q25_48 P (∸P) P P Q R                                                -- ✱25·48 (1)
  have e : ∀ T : V a → V b → QF V, QThm S (iff (T ⪽ ∸P) (relEq (P ∩̇ T) Λ̇)) := fun T =>
    qiffTrans (q25_311 T P) (QThm.mp (q23_51 T P) (qrelEqL _ _ Λ̇))
  have h2 : QThm S (iff (hyp25_48 P (∸P) P P Q R) (QF.and (relEq (P ∩̇ Q) Λ̇) (relEq (P ∩̇ R) Λ̇))) :=
    calc hyp25_48 P (∸P) P P Q R
        ≡ QF.and (QF.and (QF.and (P ⪽ P) (P ⪽ P)) (Q ⪽ ∸P)) (R ⪽ ∸P) :=
          qiffSymm (QThm.mp (q25_21 P) (QL.t4_73 _ _))
      _ ≡ QF.and (QF.and (P ⪽ P) (P ⪽ P)) (QF.and (Q ⪽ ∸P) (R ⪽ ∸P)) := QL.t4_32 _ _ _
      _ ≡ QF.and (Q ⪽ ∸P) (R ⪽ ∸P) := qand_true_left (qandI (q23_42 P) (q23_42 P))  -- ✱23·42.✱25·21
      _ ≡ QF.and (relEq (P ∩̇ Q) Λ̇) (relEq (P ∩̇ R) Λ̇) :=
          QThm.mp (qandI (e Q) (e R)) (QL.t4_38 _ _ _ _)                           -- [✱25·311] (2)
  have h3 : QThm S (iff (QF.and (relEq P P) (relEq Q R)) (relEq Q R)) :=
    qiffSymm (qiffTrans (QThm.mp (q21_2 P) (QL.t4_73 _ _)) (QL.t4_3 _ _))           -- ✱21·2.✱4·73 (3)
  qsyl (qiffMpr h2) (qimpIffTransR h1 h3)                                          -- (1).(2).(3)

/-- ✱25·482 `⊢ :. R ⪽ P . S ⪽ Q . P ∩̇ Q = Λ̇ . ⊃ : R ⊍ S = P ⊍ Q . ≡ . R = P . S = Q`, as ✱24·482 [✱24·48 (α, β /
    ξ', η') . ✱22·42]: ✱25·48's Hp from this one by Simp and Comp, with P ⪽ P, Q ⪽ Q (✱23·42) put under it by
    ✱2·02. -/
theorem q25_482 [Reducibility S] (P Q R S' : V a → V b → QF V) :
    QThm S (imp (QF.and (QF.and (R ⪽ P) (S' ⪽ Q)) (relEq (P ∩̇ Q) Λ̇))
      (iff (relEq (R ⊍ S') (P ⊍ Q)) (QF.and (relEq R P) (relEq S' Q)))) :=
  let H := QF.and (QF.and (R ⪽ P) (S' ⪽ Q)) (relEq (P ∩̇ Q) Λ̇)
  have hH : QThm S (imp H (hyp25_48 P Q R P S' Q)) :=
    qcomp (qcomp (qcomp (qcomp (qsyl (QL.t3_26 _ _) (QL.t3_26 _ _)) (QThm.mp (q23_42 P) (QL.t2_02 H _)))
      (qsyl (QL.t3_26 _ _) (QL.t3_27 _ _))) (QThm.mp (q23_42 Q) (QL.t2_02 H _))) (QL.t3_27 _ _)  -- ✱23·42
  qsyl hH (q25_48 P Q R P S' Q)                                                    -- ✱25·48 (P, Q / R', S')

/-- ✱25·49 `⊢ :. P ∩̇ Q = Λ̇ . ⊃ : P ⪽ Q ⊍ R . ≡ . P ⪽ R`, as ✱24·49. ✱23·621's P ∩̇ (Q ⊍ R) = P and P ∩̇ R = P are
    turned by ✱21·21; (1) puts (P ∩̇ Q) ⊍ (P ∩̇ R) for P ∩̇ (Q ⊍ R) by ✱23·68 (with ✱21·22, `qrelEqR`); in (2), Hp
    is put for P ∩̇ Q (✱23·551) and "✱24·24" (✱25·24) has the sum in the other order (✱23·57). -/
theorem q25_49 [Reducibility S] (P Q R : V a → V b → QF V) :
    QThm S (imp (relEq (P ∩̇ Q) Λ̇) (iff (P ⪽ Q ⊍ R) (P ⪽ R))) :=
  have h2 : QThm S (imp (relEq (P ∩̇ Q) Λ̇) (relEq ((P ∩̇ Q) ⊍ (P ∩̇ R)) (P ∩̇ R))) :=
    show (P ∩̇ Q) ⊍ (P ∩̇ R) ≑[relEq (P ∩̇ Q) Λ̇] P ∩̇ R from
    calc (P ∩̇ Q) ⊍ (P ∩̇ R)
        ≑[relEq (P ∩̇ Q) Λ̇] Λ̇ ⊍ (P ∩̇ R) := q23_551 _ _ _
      _ ≑ (P ∩̇ R) ⊍ Λ̇ := q23_57 _ _
      _ ≑ P ∩̇ R := q25_24 _                                                       -- ✱25·24 (2)
  calc (P ⪽ Q ⊍ R)
      ≡ relEq (P ∩̇ (Q ⊍ R)) P := q23_621 _ _                                      -- ✱23·621
    _ ≡ relEq P (P ∩̇ (Q ⊍ R)) := q21_21 _ _
    _ ≡ relEq P ((P ∩̇ Q) ⊍ (P ∩̇ R)) := QThm.mp (qrelEqSymm (q23_68 P Q R)) (qrelEqR _ _ P)  -- [✱23·68] (1)
    _ ≡[relEq (P ∩̇ Q) Λ̇] relEq P (P ∩̇ R) := qsyl h2 (qrelEqR _ _ P)                -- (1).(2)
    _ ≡ relEq (P ∩̇ R) P := q21_21 _ _
    _ ≡ (P ⪽ R) := qiffSymm (q23_621 P R)                                         -- [✱23·621]

/-- ✱25·491 `⊢ : Q ∩̇ R = Λ̇ . P ⪽ Q ⊍ R . ⊃ . P ∸ Q = P ∩̇ R . P ∸ R = P ∩̇ Q . P = (P ∸ Q) ⊍ (P ∸ R)`, the
    conclusion grouped from the left, as ✱24·491. "[✱24·4]": P ∩̇ (Q ⊍ R) ∸ R is P ∩̇ {(Q ⊍ R) ∸ R} (✱23·52), and
    ✱25·4 at Q, R gives (Q ⊍ R) ∸ R = Q from Hp (its two halves by ✱3·26, ✱3·27); "Similarly" (2) uses its
    first half. In (3), (1).(2) are joined by ✱23·73, and ✱23·621 needs R ⊍ Q written Q ⊍ R (✱23·57). Each
    replacement inside a relation is `qrelEqCongr`; Hp's factors are taken by ✱3·26, ✱3·27. -/
theorem q25_491 [Reducibility S] (P Q R : V a → V b → QF V) :
    QThm S (imp (QF.and (relEq (Q ∩̇ R) Λ̇) (P ⪽ Q ⊍ R))
      (QF.and (QF.and (relEq (P ∸ Q) (P ∩̇ R)) (relEq (P ∸ R) (P ∩̇ Q))) (relEq P ((P ∸ Q) ⊍ (P ∸ R))))) :=
  let H := QF.and (relEq (Q ∩̇ R) Λ̇) (P ⪽ Q ⊍ R)
  have hP : QThm S (imp H (relEq P (P ∩̇ (Q ⊍ R)))) :=
    qsyl (QL.t3_27 _ _) (qsyl (qiffMp (q23_621 P (Q ⊍ R))) (qiffMp (q21_21 _ _)))     -- ✱23·621
  have h4 := q25_4 Q R
  have hB : QThm S (imp H (relEq ((Q ⊍ R) ∸ Q) R)) :=
    qsyl (QL.t3_26 _ _) (qiffMp (QThm.mp h4 (QL.t3_26 _ _)))
  have hC : QThm S (imp H (relEq ((Q ⊍ R) ∸ R) Q)) := qsyl hB (qiffMp (QThm.mp h4 (QL.t3_27 _ _)))
  have h1 : QThm S (imp H (relEq (P ∸ R) (P ∩̇ Q))) :=
    show P ∸ R ≑[H] P ∩̇ Q from
    calc P ∸ R
        ≑[H] (P ∩̇ (Q ⊍ R)) ∸ R := qsyl hP (q23_481 _ _ (∸R))                         -- [✱23·481]
      _ ≑ P ∩̇ ((Q ⊍ R) ∸ R) := q23_52 _ _ _
      _ ≑[H] P ∩̇ Q := qsyl hC (qrelEqCongr (fun X => P ∩̇ X) _ _ (by rel_expr))                      -- [✱25·4] (1)
  have h2 : QThm S (imp H (relEq (P ∸ Q) (P ∩̇ R))) :=
    show P ∸ Q ≑[H] P ∩̇ R from
    calc P ∸ Q
        ≑[H] (P ∩̇ (Q ⊍ R)) ∸ Q := qsyl hP (q23_481 _ _ (∸Q))
      _ ≑ P ∩̇ ((Q ⊍ R) ∸ Q) := q23_52 _ _ _
      _ ≑[H] P ∩̇ R := qsyl hB (qrelEqCongr (fun X => P ∩̇ X) _ _ (by rel_expr))                      -- Similarly (2)
  have h3 : QThm S (imp H (relEq ((P ∸ Q) ⊍ (P ∸ R)) P)) :=
    show (P ∸ Q) ⊍ (P ∸ R) ≑[H] P from
    calc (P ∸ Q) ⊍ (P ∸ R)
        ≑[H] (P ∩̇ R) ⊍ (P ∩̇ Q) := qsyl (qcomp h2 h1) (q23_73 _ _ _ _)                 -- (1).(2)
      _ ≑ P ∩̇ (R ⊍ Q) := q23_68 _ _ _                                              -- [✱23·68]
      _ ≑ P ∩̇ (Q ⊍ R) := QThm.mp (q23_57 R Q) (qrelEqCongr (fun X => P ∩̇ X) _ _ (by rel_expr))
      _ ≑[H] P := qsyl (QL.t3_27 _ _) (qiffMp (q23_621 P (Q ⊍ R)))                   -- [✱23·621] (3)
  qcomp (qcomp h2 h1) (qsyl h3 (qiffMp (q21_21 _ _)))                              -- (1).(2).(3)

/-- ✱25·492 `⊢ : Q ⪽ P . P ∸ Q = R . ⊃ . P ∸ R = Q`, as ✱24·492. "[✱22·481]" puts P ∸ Q for R in P ∸ R (Hp
    turned by ✱21·21; `qrelEqCongr`). "[✱22·8·86]": ∸(P ∸ Q) is ∸(∸(∸P) ∩̇ ∸Q) (✱23·8), which is ∸P ⊍ Q by ✱23·86.
    "[✱22·8·9]": P ∩̇ (∸P ⊍ Q) is (Q ⊍ ∸P) ∸ (∸P) by ✱23·51, ✱23·8, ✱23·57, which is Q ∸ (∸P) by ✱23·9, and Q ∩̇ P
    by ✱23·8 (and ✱23·51). "[✱22·621]" gives Q ∩̇ P = Q (✱23·51). -/
theorem q25_492 [Reducibility S] (P Q R : V a → V b → QF V) :
    QThm S (imp (QF.and (Q ⪽ P) (relEq (P ∸ Q) R)) (relEq (P ∸ R) Q)) :=
  let H := QF.and (Q ⪽ P) (relEq (P ∸ Q) R)
  have hN : QThm S (relEq (∸(P ∸ Q)) (∸P ⊍ Q)) :=
    show ∸(P ∸ Q) ≑ ∸P ⊍ Q from
    calc ∸(P ∸ Q)
        ≑ ∸(∸(∸P) ∩̇ ∸Q) := QThm.mp (qrelEqSymm (q23_8 P)) (qrelEqCongr (fun X => ∸(X ∩̇ ∸Q)) _ _ (by rel_expr))
      _ ≑ ∸P ⊍ Q := q23_86 (∸P) Q                                                   -- ✱23·86
  show P ∸ R ≑[H] Q from
  calc P ∸ R
      ≑[H] P ∸ (P ∸ Q) :=
        qsyl (QL.t3_27 _ _) (qsyl (qiffMp (q21_21 _ _)) (qrelEqCongr (fun X => P ∸ X) _ _ (by rel_expr)))  -- ✱23·481
    _ ≑ P ∩̇ (∸P ⊍ Q) := QThm.mp hN (qrelEqCongr (fun X => P ∩̇ X) _ _ (by rel_expr))                 -- [✱23·8·86]
    _ ≑ (∸P ⊍ Q) ∩̇ P := q23_51 _ _
    _ ≑ (∸P ⊍ Q) ∩̇ ∸(∸P) := QThm.mp (qrelEqSymm (q23_8 P)) (qrelEqCongr (fun X => (∸P ⊍ Q) ∩̇ X) _ _ (by rel_expr))
    _ ≑ (Q ⊍ ∸P) ∸ (∸P) := QThm.mp (q23_57 (∸P) Q) (qrelEqCongr (fun X => X ∸ (∸P)) _ _ (by rel_expr))
    _ ≑ Q ∸ (∸P) := q23_9 Q (∸P)
    _ ≑ Q ∩̇ P := QThm.mp (q23_8 P) (qrelEqCongr (fun X => Q ∩̇ X) _ _ (by rel_expr))
    _ ≑ P ∩̇ Q := q23_51 _ _                                                       -- [✱23·8·9]
    _ ≑ Q ∩̇ P := q23_51 _ _
    _ ≑[H] Q := qsyl (QL.t3_26 _ _) (qiffMp (q23_621 Q P))                           -- [✱23·621]

/-- ✱25·493 `⊢ : Q ∩̇ R = Λ̇ . ⊃ . P = (P ∸ Q) ⊍ (P ∸ R)`, as ✱24·493. "✱22·84 . ✱24·17": ✱25·17 at ∸(Q ∩̇ R),
    whose ∸(∸(Q ∩̇ R)) is Q ∩̇ R by ✱23·8, and ✱23·84 (each identity replaced in its first member, ✱21·22·23,
    `qrelEqL`). "[✱24·26]": P = P ∩̇ V̇ (✱21·21), V̇ replaced inside the relation (`qrelEqCongr`). -/
theorem q25_493 [Reducibility S] (P Q R : V a → V b → QF V) :
    QThm S (imp (relEq (Q ∩̇ R) Λ̇) (relEq P ((P ∸ Q) ⊍ (P ∸ R)))) :=
  have hV : QThm S (imp (relEq (Q ∩̇ R) Λ̇) (relEq (∸Q ⊍ ∸R) 𝐕̇)) :=
    calc relEq (Q ∩̇ R) Λ̇
        ⊃ relEq (∸(∸(Q ∩̇ R))) Λ̇ := qiffMpr (QThm.mp (q23_8 _) (qrelEqL _ _ Λ̇))
      _ ⊃ relEq (∸(Q ∩̇ R)) 𝐕̇ := qiffMpr (q25_17 _)                                  -- ✱25·17
      _ ⊃ relEq (∸Q ⊍ ∸R) 𝐕̇ := qiffMp (QThm.mp (q23_84 Q R) (qrelEqL _ _ 𝐕̇))         -- ✱23·84
  show P ≑[relEq (Q ∩̇ R) Λ̇] (P ∸ Q) ⊍ (P ∸ R) from
  calc P
      ≑ P ∩̇ 𝐕̇ := qrelEqSymm (q25_26 P)
    _ ≑[relEq (Q ∩̇ R) Λ̇] P ∩̇ (∸Q ⊍ ∸R) :=
        qsyl hV (qsyl (qiffMp (q21_21 _ _)) (qrelEqCongr (fun X => P ∩̇ X) _ _ (by rel_expr)))     -- [✱25·26]
    _ ≑ (P ∸ Q) ⊍ (P ∸ R) := qrelEqSymm (q23_68 P (∸Q) (∸R))                        -- [✱23·68]

/-- ✱25·494 `⊢ : R ⪽ P . S ⪽ Q . P ∩̇ Q = Λ̇ . ⊃ . (R ⊍ S) ∸ P = S . (R ⊍ S) ∸ Q = R`, as ✱24·494. ✱25·311 at Q, P
    has Q ∩̇ P (✱23·51); (3) is ✱23·68 with the common factor second (`qrelDistribRight`); in (4), (1) and (2) are
    put in the sum by ✱23·73, and ✱25·24 has it in the other order (✱23·57). "Similarly" (5) is written out,
    with ✱25·3, ✱25·311, ✱23·44 and ✱23·621 at S, R, Q. Hp's factors are taken by ✱3·26, ✱3·27. -/
theorem q25_494 [Reducibility S] (P Q R S' : V a → V b → QF V) :
    QThm S (imp (QF.and (QF.and (R ⪽ P) (S' ⪽ Q)) (relEq (P ∩̇ Q) Λ̇))
      (QF.and (relEq ((R ⊍ S') ∸ P) S') (relEq ((R ⊍ S') ∸ Q) R))) :=
  let H := QF.and (QF.and (R ⪽ P) (S' ⪽ Q)) (relEq (P ∩̇ Q) Λ̇)
  have pR : QThm S (imp H (R ⪽ P)) := qsyl (QL.t3_26 _ _) (QL.t3_26 _ _)
  have pS : QThm S (imp H (S' ⪽ Q)) := qsyl (QL.t3_26 _ _) (QL.t3_27 _ _)
  have pΛ : QThm S (imp H (relEq (P ∩̇ Q) Λ̇)) := QL.t3_27 _ _
  have h1 : QThm S (imp H (relEq (R ∸ P) Λ̇)) := qsyl pR (qiffMp (q25_3 R P))        -- ✱25·3 (1)
  have hQ : QThm S (imp H (Q ⪽ ∸P)) :=
    qsyl pΛ (qiffMpr (qiffTrans (q25_311 Q P) (QThm.mp (q23_51 Q P) (qrelEqL _ _ Λ̇))))  -- ✱25·311
  have hS : QThm S (imp H (S' ⪽ ∸P)) := qsyl (qcomp pS hQ) (q23_44 S' Q (∸P))       -- [✱23·44]
  have h2 : QThm S (imp H (relEq (S' ∸ P) S')) := qsyl hS (qiffMp (q23_621 S' (∸P)))  -- [✱23·621] (2)
  have h4 : QThm S (imp H (relEq ((R ⊍ S') ∸ P) S')) :=
    show (R ⊍ S') ∸ P ≑[H] S' from
    calc (R ⊍ S') ∸ P
        ≑ (R ∸ P) ⊍ (S' ∸ P) := qrelDistribRight R S' (∸P)                          -- ✱23·68 (3)
      _ ≑[H] Λ̇ ⊍ S' := qsyl (qcomp h1 h2) (q23_73 _ _ _ _)                           -- (1).(2)
      _ ≑ S' ⊍ Λ̇ := q23_57 _ _
      _ ≑ S' := q25_24 S'                                                         -- ✱25·24 (4)
  have g1 : QThm S (imp H (relEq (S' ∸ Q) Λ̇)) := qsyl pS (qiffMp (q25_3 S' Q))
  have gP : QThm S (imp H (P ⪽ ∸Q)) := qsyl pΛ (qiffMpr (q25_311 P Q))
  have gR : QThm S (imp H (R ⪽ ∸Q)) := qsyl (qcomp pR gP) (q23_44 R P (∸Q))
  have g2 : QThm S (imp H (relEq (R ∸ Q) R)) := qsyl gR (qiffMp (q23_621 R (∸Q)))
  have h5 : QThm S (imp H (relEq ((R ⊍ S') ∸ Q) R)) :=
    show (R ⊍ S') ∸ Q ≑[H] R from
    calc (R ⊍ S') ∸ Q
        ≑ (R ∸ Q) ⊍ (S' ∸ Q) := qrelDistribRight R S' (∸Q)
      _ ≑[H] R ⊍ Λ̇ := qsyl (qcomp g2 g1) (q23_73 _ _ _ _)
      _ ≑ R := q25_24 R                                                           -- Similarly (5)
  qcomp h4 h5                                                                     -- (4).(5)

/-- ✱25·495 `⊢ : P ∩̇ R = Λ̇ . ⊃ . (P ⊍ R) ∸ (Q ⊍ R) = P ∸ Q`, as ✱24·495. "✱22·87·68": ∸(Q ⊍ R) is ∸Q ∩̇ ∸R
    (✱23·87 turned by ✱21·21), and ✱23·68 with the common factor second (`qrelDistribRight`), each product
    regrouped by ✱23·52 (both at once by ✱23·73). "[✱24·21]": (R ∸ Q) ∸ R is ∸Q ∩̇ (R ∩̇ ∸R) (✱23·51, ✱23·52), so
    ∸Q ∩̇ Λ̇, which is Λ̇ by ✱25·23, dropped by ✱25·24. (1).(2): (P ∸ Q) ∸ R is (P ∸ R) ∸ Q (✱23·52, ✱23·51), and
    (2) is put for P ∸ R (✱23·481). Each replacement inside a relation is `qrelEqCongr`. -/
theorem q25_495 [Reducibility S] (P Q R : V a → V b → QF V) :
    QThm S (imp (relEq (P ∩̇ R) Λ̇) (relEq ((P ⊍ R) ∸ (Q ⊍ R)) (P ∸ Q))) :=
  have hz : QThm S (relEq ((R ∸ Q) ∸ R) Λ̇) :=
    show (R ∸ Q) ∸ R ≑ Λ̇ from
    calc (R ∸ Q) ∸ R
        ≑ (∸Q ∩̇ R) ∩̇ ∸R := QThm.mp (q23_51 R (∸Q)) (q23_481 _ _ _)
      _ ≑ ∸Q ∩̇ (R ∩̇ ∸R) := q23_52 _ _ _
      _ ≑ ∸Q ∩̇ Λ̇ := QThm.mp (q25_21 R) (qrelEqCongr (fun X => ∸Q ∩̇ X) _ _ (by rel_expr))           -- ✱25·21
      _ ≑ Λ̇ := q25_23 _
  have h1 : QThm S (relEq ((P ⊍ R) ∸ (Q ⊍ R)) ((P ∸ Q) ∸ R)) :=
    show (P ⊍ R) ∸ (Q ⊍ R) ≑ (P ∸ Q) ∸ R from
    calc (P ⊍ R) ∸ (Q ⊍ R)
        ≑ (P ⊍ R) ∩̇ (∸Q ∩̇ ∸R) :=
          QThm.mp (qrelEqSymm (q23_87 Q R)) (qrelEqCongr (fun X => (P ⊍ R) ∩̇ X) _ _ (by rel_expr))  -- ✱23·87
      _ ≑ (P ∩̇ (∸Q ∩̇ ∸R)) ⊍ (R ∩̇ (∸Q ∩̇ ∸R)) := qrelDistribRight P R _                -- ✱23·68
      _ ≑ ((P ∸ Q) ∸ R) ⊍ ((R ∸ Q) ∸ R) :=
          QThm.mp (qandI (qrelEqSymm (q23_52 P (∸Q) (∸R))) (qrelEqSymm (q23_52 R (∸Q) (∸R))))
            (q23_73 _ _ _ _)
      _ ≑ ((P ∸ Q) ∸ R) ⊍ Λ̇ := QThm.mp hz (qrelEqCongr (fun X => ((P ∸ Q) ∸ R) ⊍ X) _ _ (by rel_expr))  -- [✱25·21]
      _ ≑ (P ∸ Q) ∸ R := q25_24 _                                                 -- (1)
  have h2 : QThm S (imp (relEq (P ∩̇ R) Λ̇) (relEq (P ∸ R) P)) :=
    qsyl (qiffMpr (q25_311 P R)) (qiffMp (q23_621 P (∸R)))                          -- ✱25·311.✱23·621 (2)
  show (P ⊍ R) ∸ (Q ⊍ R) ≑[relEq (P ∩̇ R) Λ̇] P ∸ Q from
  calc (P ⊍ R) ∸ (Q ⊍ R)
      ≑ (P ∸ Q) ∸ R := h1                                                         -- (1)
    _ ≑ P ∩̇ (∸Q ∩̇ ∸R) := q23_52 _ _ _
    _ ≑ P ∩̇ (∸R ∩̇ ∸Q) := QThm.mp (q23_51 _ _) (qrelEqCongr (fun X => P ∩̇ X) _ _ (by rel_expr))
    _ ≑ (P ∸ R) ∸ Q := qrelEqSymm (q23_52 _ _ _)
    _ ≑[relEq (P ∩̇ R) Λ̇] P ∸ Q := qsyl h2 (q23_481 _ _ _)                           -- (1).(2)

/-! ## ✱25·5–✱25·63: the existence of relations -/

/-- ✱25·5 `⊢ : ∃̇!R . ≡ . (∃x, y) . xRy`, as ✱24·5 [✱4·2 . (✱24·03)] -/
theorem q25_5 (R : V a → V b → QF V) : QThm S (iff (relNonempty R) (ex2 fun x y => relHolds x R y)) :=
  QL.t4_2 _                                                                       -- ✱4·2 . (✱25·03)

/-- ✱25·51 `⊢ : ∼∃̇!R . ≡ . R = Λ̇`, as ✱24·51 (✱24·5, [✱10·252], [✱24·15]): ✱25·5 is used inside the negation
    (✱4·11), and ✱10·252 for two variables is ✱11·25. -/
theorem q25_51 [Reducibility S] (R : V a → V b → QF V) : QThm S (iff (.neg (relNonempty R)) (relEq R Λ̇)) :=
  calc QF.neg (relNonempty R)
      ≡ .neg (ex2 fun x y => relHolds x R y) := qiffNeg (q25_5 R)                  -- ✱25·5
    _ ≡ all2 (fun x y => .neg (relHolds x R y)) := q11_25 _                       -- [✱11·25]
    _ ≡ relEq R Λ̇ := q25_15 R                                                     -- [✱25·15]

/-- ✱25·52 `⊢ . ∃̇!V̇`, as ✱24·52 [✱24·51·1 . Transp]: ✱25·1's Λ̇ ≠ V̇ is written V̇ ≠ Λ̇ (✱21·21, inside the
    negation, ✱4·11), and Transp is ✱2·15. x, y are ✱25·1's real variables: "The assumption that there is
    something ... is involved in the use of the real variable" (p. 239, which applies here, p. 241). -/
theorem q25_52 [Reducibility S] (x : V a) (y : V b) : QThm S (relNonempty (𝐕̇ : V a → V b → QF V)) :=
  have h1 : QThm S (.neg (relEq (𝐕̇ : V a → V b → QF V) Λ̇)) :=
    QThm.mp (q25_1 x y) (qiffMp (qiffNeg (q21_21 Λ̇ 𝐕̇)))
  QThm.mp h1 (QThm.mp (qiffMp (q25_51 𝐕̇)) (QL.t2_15 _ _))                           -- ✱25·51·1 . Transp

/-- ✱25·53 `⊢ . ∼∃̇!Λ̇`, as ✱24·53 [✱24·51 . ✱20·2] -/
theorem q25_53 [Reducibility S] : QThm S (.neg (relNonempty (Λ̇ : V a → V b → QF V))) :=
  QThm.mp (q21_2 Λ̇) (qiffMpr (q25_51 Λ̇))                                           -- ✱25·51 . ✱21·2

/-- ✱25·54 `⊢ : ∃̇!R . ≡ . R ≠ Λ̇`, as ✱24·54 [✱24·51 . Transp]: Transp is ✱4·11, with ✱4·13 for
    ∃̇!R . ≡ . ∼∼∃̇!R. -/
theorem q25_54 [Reducibility S] (R : V a → V b → QF V) : QThm S (iff (relNonempty R) (.neg (relEq R Λ̇))) :=
  qiffTrans (QL.t4_13 _) (qiffNeg (q25_51 R))                                       -- ✱25·51 . Transp

/-- ✱25·55 `⊢ : ∼(R ⪽ S) . ≡ . ∃̇!R ∸ S`, as ✱24·55 [✱24·3 . Transp . ✱24·54]; Transp is ✱4·11. -/
theorem q25_55 [Reducibility S] (R S' : V a → V b → QF V) :
    QThm S (iff (.neg (R ⪽ S')) (relNonempty (R ∸ S'))) :=
  qiffTrans (qiffNeg (q25_3 R S')) (qiffSymm (q25_54 _))                            -- ✱25·3 . Transp . ✱25·54

/-- ✱25·56 `⊢ :. ∃̇!(R ⊍ S) . ≡ : ∃̇!R . ∨ . ∃̇!S`, as printed (p. 243; the transcription has `∃̇!R ⊍ S`
    without the brackets, the text audit's Vol I list, entry 20). As ✱24·56 [✱10·42 . ✱22·34]: ✱10·42 for two
    variables is ✱11·41, and ✱23·34 acts under (∃x, y) (✱11·11·341). -/
theorem q25_56 [Reducibility S] (R S' : V a → V b → QF V) :
    QThm S (iff (relNonempty (R ⊍ S')) (.or (relNonempty R) (relNonempty S'))) :=
  calc relNonempty (R ⊍ S')
      ≡ ex2 (fun x y => .or (relHolds x R y) (relHolds x S' y)) :=
        QThm.mp (q11_11 fun x y => q23_34 R S' x y) (q11_341 _ _)                 -- ✱23·34
    _ ≡ .or (relNonempty R) (relNonempty S') := qiffSymm (q11_41 _ _)              -- ✱11·41

/-- ✱25·561 `⊢ : ∃̇!(R ∩̇ S) . ⊃ . ∃̇!R . ∃̇!S`, as ✱24·561 [✱10·5 . ✱22·33]: ✱10·5 for two variables is ✱11·42,
    and ✱23·33 acts under (∃x, y) (✱11·11·341). -/
theorem q25_561 [Reducibility S] (R S' : V a → V b → QF V) :
    QThm S (imp (relNonempty (R ∩̇ S')) (QF.and (relNonempty R) (relNonempty S'))) :=
  calc relNonempty (R ∩̇ S')
      ≡ ex2 (fun x y => QF.and (relHolds x R y) (relHolds x S' y)) :=
        QThm.mp (q11_11 fun x y => q23_33 R S' x y) (q11_341 _ _)                 -- ✱23·33
    _ ⊃ QF.and (relNonempty R) (relNonempty S') := q11_42 _ _                      -- ✱11·42

/-- ✱25·57 `⊢ :. R ∩̇ S = Λ̇ . ⊃ : ∃̇!R . ⊃ . R ≠ S`, as ✱24·57. The first two lines are those of ✱25·38
    (`qrelInterSelfNull`, ✱21·22·23 with ✱23·5); Transp is ✱2·03. -/
theorem q25_57 [Reducibility S] (R S' : V a → V b → QF V) :
    QThm S (imp (relEq (R ∩̇ S') Λ̇) (imp (relNonempty R) (.neg (relEq R S')))) :=
  have h1 : QThm S (imp (QF.and (relEq (R ∩̇ S') Λ̇) (relEq R S')) (.neg (relNonempty R))) :=
    calc QF.and (relEq (R ∩̇ S') Λ̇) (relEq R S')
        ⊃ relEq (R ∩̇ R) Λ̇ := qrelInterSelfNull R S'                                 -- ✱23·481
      _ ⊃ relEq R Λ̇ := qiffMp (QThm.mp (q23_5 R) (qrelEqL _ _ Λ̇))                    -- [✱23·5]
      _ ⊃ .neg (relNonempty R) := qiffMpr (q25_51 R)                               -- [✱25·51] (1)
  qsyl (QThm.mp h1 (QL.t3_3 _ _ _)) (QL.t2_03 _ _)                                 -- (1).Exp.Transp

/-- ✱25·571 `⊢ : ∃̇!R . R = S . ⊃ . ∃̇!(R ∩̇ S)`, as ✱24·571. Comm is ✱2·04, Transp ✱2·03, Imp ✱3·31. -/
theorem q25_571 [Reducibility S] (R S' : V a → V b → QF V) :
    QThm S (imp (QF.and (relNonempty R) (relEq R S')) (relNonempty (R ∩̇ S'))) :=
  have h1 : QThm S (imp (relNonempty R) (imp (relEq R S') (relNonempty (R ∩̇ S')))) :=
    calc relNonempty R
        ⊃ imp (relEq (R ∩̇ S') Λ̇) (.neg (relEq R S')) := QThm.mp (q25_57 R S') (QL.t2_04 _ _ _)  -- ✱25·57 . Comm
      _ ⊃ imp (relEq R S') (.neg (relEq (R ∩̇ S') Λ̇)) := QL.t2_03 _ _                   -- [Transp]
      _ ⊃ imp (relEq R S') (relNonempty (R ∩̇ S')) :=
          QThm.mp (qiffMpr (q25_54 _)) (QL.t2_05 _ _ _)                             -- [✱25·54] (1)
  QThm.mp h1 (QL.t3_31 _ _ _)                                                      -- (1).Imp

/-- ✱25·58 `⊢ :. R ⪽ S . ⊃ : ∃̇!R . ⊃ . ∃̇!S`, as ✱24·58 [✱10·28]: ✱10·28 for two variables is ✱11·34. -/
theorem q25_58 (R S' : V a → V b → QF V) : QThm S (imp (R ⪽ S') (imp (relNonempty R) (relNonempty S'))) :=
  q11_34 _ _                                                                      -- [✱11·34]

/-- ✱25·6 `⊢ :. R ⪽ S . ⊃ : R ≠ S . ≡ . ∃̇!S ∸ R`, as ✱24·6. "✱22·41 . Transp": ✱23·41 with Exp (✱3·3), and
    Transp (✱2·16). (2): R = S puts S ∸ S for S ∸ R (`qrelEqCongr`), which is Λ̇ by ✱25·21. (1).(3): (3) put
    under Hp by ✱2·02, joined by Comp (✱3·43). -/
theorem q25_6 [Reducibility S] (R S' : V a → V b → QF V) :
    QThm S (imp (R ⪽ S') (iff (.neg (relEq R S')) (relNonempty (S' ∸ R)))) :=
  have h1 : QThm S (imp (R ⪽ S') (imp (.neg (relEq R S')) (relNonempty (S' ∸ R)))) :=
    calc (R ⪽ S')
        ⊃ imp (S' ⪽ R) (relEq R S') := QThm.mp (qiffMp (q23_41 R S')) (QL.t3_3 _ _ _)
      _ ⊃ imp (.neg (relEq R S')) (.neg (S' ⪽ R)) := QL.t2_16 _ _                     -- ✱23·41 . Transp
      _ ⊃ imp (.neg (relEq R S')) (relNonempty (S' ∸ R)) :=
          QThm.mp (qiffMp (q25_55 S' R)) (QL.t2_05 _ _ _)                           -- [✱25·55] (1)
  have h2 : QThm S (imp (relEq R S') (relEq (S' ∸ R) Λ̇)) :=
    show S' ∸ R ≑[relEq R S'] Λ̇ from
    calc S' ∸ R
        ≑[relEq R S'] S' ∸ S' := qrelEqCongr (fun X => S' ∸ X) R S' (by rel_expr)
      _ ≑ Λ̇ := q25_21 S'                                                          -- ✱25·21 (2)
  have h3 : QThm S (imp (relNonempty (S' ∸ R)) (.neg (relEq R S'))) :=
    qsyl (qiffMp (q25_54 _)) (QThm.mp h2 (QL.t2_16 _ _))                            -- (2).Transp.✱25·54 (3)
  qcomp h1 (QThm.mp h3 (QL.t2_02 _ _))                                             -- (1).(3)

/-- ✱25·61 `⊢ : ∼∃̇!S . ⊃ . R ⊍ S = R`, as ✱24·61 [✱24·51·24], ✱25·51's S = Λ̇ put for S in R ⊍ S
    (`qrelEqCongr`). -/
theorem q25_61 [Reducibility S] (R S' : V a → V b → QF V) :
    QThm S (imp (.neg (relNonempty S')) (relEq (R ⊍ S') R)) :=
  show R ⊍ S' ≑[.neg (relNonempty S')] R from
  calc R ⊍ S'
      ≑[.neg (relNonempty S')] R ⊍ Λ̇ := qsyl (qiffMp (q25_51 S')) (qrelEqCongr (fun X => R ⊍ X) _ _ (by rel_expr))  -- ✱25·51
    _ ≑ R := q25_24 R                                                             -- ✱25·24

/-- ✱25·62 `⊢ : ∼∃̇!S . ⊃ . R ∩̇ S = Λ̇`, as ✱24·62 [✱24·51·23], ✱25·51's S = Λ̇ put for S in R ∩̇ S
    (`qrelEqCongr`). -/
theorem q25_62 [Reducibility S] (R S' : V a → V b → QF V) :
    QThm S (imp (.neg (relNonempty S')) (relEq (R ∩̇ S') Λ̇)) :=
  show R ∩̇ S' ≑[.neg (relNonempty S')] Λ̇ from
  calc R ∩̇ S'
      ≑[.neg (relNonempty S')] R ∩̇ Λ̇ := qsyl (qiffMp (q25_51 S')) (qrelEqCongr (fun X => R ∩̇ X) _ _ (by rel_expr))  -- ✱25·51
    _ ≑ Λ̇ := q25_23 R                                                             -- ✱25·23

/-- ✱21·53 for an extensional expression G (as `qrel21_18` is ✱21·18 for one, and `qcls20_53` ✱20·53), the
    analogue for relations of ✱13·191: `⊢ :. S = R . ⊃_S . GS : ≡ . GR`, S apparent, R real. ✱21·53's lines
    with G for φS: the analogue for relations of ✱10·1 (`qrelAllAt`), the occurrences carried by ✱21·11 and
    G's extensionality and joined by ✱4·84, ✱4·85 (the ⊃ half by ✱3·26), "[✱21·2]" by ✱2·27; and ✱21·18 for
    G (`qrel21_18`) with ✱21·21, its "≡" used from left to right (✱3·26), Comm and ✱10·11·21. -/
theorem qrel21_53 [Reducibility S] (G : (V a → V b → QF V) → QF V) (hG : RelExt S G) (ψ : V a → V b → QF V) :
    QThm S (iff (relAll fun T => imp (relEq T ψ) (G T)) (G ψ)) :=
  let F : (V a → V b → QF V) → QF V := fun T => imp (relEq T ψ) (G T)
  have h1 : QThm S (imp (relAll F) (G ψ)) :=
    calc relAll F
        ⊃ F ψ :=
          qrelAllAt F ψ fun θ =>
            qsyl (qimpImpIffCongr (q21_11 (pf2 θ) ψ fun θ' => rel ψ fun θ'' => ident θ' θ'') (hG (pf2 θ) ψ))
              (QL.t3_26 _ _)                                                      -- ✱10·1
      _ ⊃ G ψ := QThm.mp (q21_2 ψ) (QL.t2_27 _ _)                                  -- [✱21·2]
  have h2 : ∀ θ : V (Ty.pred2 a b), QThm S (imp (relEq (pf2 θ) ψ) (imp (G ψ) (G (pf2 θ)))) := fun θ =>
    qsyl (qiffMp (q21_21 (pf2 θ) ψ)) (qsyl (qrel21_18 G hG ψ (pf2 θ)) (QL.t3_26 _ _))  -- ✱21·18·21
  qiffI h1 (q10_11_21 fun θ => QThm.mp (h2 θ) (QL.t2_04 _ _ _))

/-- ✱25·63 `⊢ :. Λ̇ ∼∈ κ . ≡ : R ∈ κ . ⊃_R . ∃̇!R`, κ a class of relations, R apparent (✱21·07), as ✱24·63.
    "[✱13·191]" is its analogue for relations ✱21·53, for the extensional expression R ∼∈ κ (`qrel21_53`;
    p. 213); "[Transp]" is ✱2·03 both ways, and ✱25·54 acts on the consequent (✱4·85), under (R). -/
theorem q25_63 [Reducibility S] (κ : (V a → V b → QF V) → QF V) :
    QThm S (iff (.neg ((Λ̇ : V a → V b → QF V) ∈ κ)) (relAll fun R => imp (R ∈ κ) (relNonempty R))) :=
  calc QF.neg ((Λ̇ : V a → V b → QF V) ∈ κ)
      ≡ relAll (fun R => imp (relEq R Λ̇) (.neg (R ∈ κ))) :=
        qiffSymm (qrel21_53 (fun R => .neg (R ∈ κ)) (relExpr_ext (.neg (RelExpr.relClsMem κ))) Λ̇)  -- ✱21·53
    _ ≡ relAll (fun R => imp (R ∈ κ) (.neg (relEq R Λ̇))) :=
        q10_11_271 fun _ => qiffI (QL.t2_03 _ _) (QL.t2_03 _ _)                     -- [Transp]
    _ ≡ relAll (fun R => imp (R ∈ κ) (relNonempty R)) :=
        q10_11_271 fun φ => QThm.mp (qiffSymm (q25_54 (pf2 φ))) (QL.t4_85 _ _ _)     -- [✱25·54]

end PM
