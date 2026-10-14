import PM.Star21
/-!
  ✱22: calculus of classes (1910 print; numbered items pp. 219–225, after the number's summary). The
  print has 79 numbered items: the definitions ✱22·01–✱22·05 (pp. 219–220), ✱22·53 (p. 221) and ✱22·71
  (p. 223), and 72 propositions, ✱22·1 to ✱22·95 (there is no ✱22·67).

  Statements are read from the Gutenberg #78050 transcription of the 1910 print (its formula source),
  not from the scan images; no entry of the text audit's list of errors falls on pp. 219–225. Each
  proof follows PM's Dem. line by line, or uses the propositions of PM's bracketed hint in PM's order;
  the comment on each Lean line gives PM's line or hint. `data/star22_ledger.json` records, per
  proposition, which cited propositions are used and which further ones were needed.

  The definitions are macros (`@[reducible]`), like ✱20·01 (docs/TYPES_DESIGN.md decision 9). A class
  is written by its defining function (PM/Star20.lean), so each operation that PM defines as a class
  x̂(…) is the function x ↦ …, in which every occurrence of α and β is eliminated where it stands
  (x ∈ α is `clsMem x α`, ✱20·01 with the smallest scope):
    ✱22·01  α ⊂ β . = : x ∈ α . ⊃ₓ . x ∈ β               Df   (`QF.clsSubset α β`, `α ⊂ β`)
    ✱22·02  α ∩ β = x̂(x ∈ α . x ∈ β)                     Df   (`QF.clsInter α β`, `α ∩ β`)
    ✱22·03  α ∪ β = x̂(x ∈ α . ∨ . x ∈ β)                 Df   (`QF.clsUnion α β`, `α ∪ β`)
    ✱22·04  −α = x̂(x ∼∈ α)                                Df   (`QF.clsCompl α`, `−α`)
    ✱22·05  α − β = α ∩ −β                                Df   (`QF.clsDiff α β`, `α − β`)
    ✱22·53  α ∩ β ∩ γ = (α ∩ β) ∩ γ                       Df   (`QF.clsInter3`)
    ✱22·71  α ∪ β ∪ γ = (α ∪ β) ∪ γ                       Df   (`QF.clsUnion3`)
  So ✱22·2 `⊢ . α ∩ β = x̂(x ∈ α . x ∈ β)` [✱20·2 . (✱22·02)] is literally ✱20·2. ✱22·01 is a
  definition of a proposition, not of a class; its definiens is the formal implication ✱10·02.

  Most of PM's hints cite one proposition of ✱3–✱5 (✱22·5–✱22·93): the proof carries it under (x) by
  ✱10·11 (with ✱10·271), rewrites each membership by ✱22·33, ✱22·34 or ✱22·35, and gets the identity of
  classes by ✱20·43, as the printed Dem. of ✱22·5, ✱22·68 and ✱22·91 do.

  Steps done silently are those of PM/Star11.lean's header and of PM/Star14.lean's (chaining ⊃ and ≡
  lines under a hypothesis). A displayed chain is a `calc` block, one line per PM line with PM's
  citation (PM/Chain.lean); the propositions that join its lines under a hypothesis are listed per
  proposition as `glue` in the ledger, apart from the fidelity. Any other proposition a proof needs is
  named in its docstring and listed as `extra_used` in the ledger.

  Names: `q22_1` is ✱22·1, and so on. α, β, γ, δ are classes, written by their defining functions
  (formulas with a hole, of any order); `F` is an expression containing a class (✱22·94, ✱22·95).
-/
namespace PM
open QF

namespace QF
variable {V : Ty → Type}
/-- ✱22·01 `α ⊂ β . = : x ∈ α . ⊃ₓ . x ∈ β` Df -/
@[reducible] def clsSubset {a : Ty} (α β : V a → QF V) : QF V := fimp (fun x => clsMem x α) fun x => clsMem x β
/-- ✱22·02 `α ∩ β = x̂(x ∈ α . x ∈ β)` Df: the class whose defining function is x ∈ α . x ∈ β. -/
@[reducible] def clsInter {a : Ty} (α β : V a → QF V) : V a → QF V := fun x => QF.and (clsMem x α) (clsMem x β)
/-- ✱22·03 `α ∪ β = x̂(x ∈ α . ∨ . x ∈ β)` Df -/
@[reducible] def clsUnion {a : Ty} (α β : V a → QF V) : V a → QF V := fun x => .or (clsMem x α) (clsMem x β)
/-- ✱22·04 `−α = x̂(x ∼∈ α)` Df (x ∼∈ α is ✱20·06, `nmem`) -/
@[reducible] def clsCompl {a : Ty} (α : V a → QF V) : V a → QF V := fun x => nmem x α
/-- ✱22·05 `α − β = α ∩ −β` Df -/
@[reducible] def clsDiff {a : Ty} (α β : V a → QF V) : V a → QF V := clsInter α (clsCompl β)
/-- ✱22·53 `α ∩ β ∩ γ = (α ∩ β) ∩ γ` Df -/
@[reducible] def clsInter3 {a : Ty} (α β γ : V a → QF V) : V a → QF V := clsInter (clsInter α β) γ
/-- ✱22·71 `α ∪ β ∪ γ = (α ∪ β) ∪ γ` Df -/
@[reducible] def clsUnion3 {a : Ty} (α β γ : V a → QF V) : V a → QF V := clsUnion (clsUnion α β) γ
end QF

/-! The notations of ✱22 (scoped to `PM`, like `x ∈ α`): `α ⊂ β`, `α ∩ β`, `α ∪ β`, `−α` and `α − β`, with
    PM's minus sign (U+2212), not `-`. Each unfolds to the definition it names. ∩ binds more tightly than
    ∪ and −, and −α most tightly, so `α ∪ β ∩ γ` is α ∪ (β ∩ γ) and `−α ∩ β` is (−α) ∩ β; PM writes the
    brackets, and so do the statements here. -/
/-- `α ⊂ β`: `clsSubset α β` (✱22·01). -/
scoped infix:50 " ⊂ " => QF.clsSubset
/-- `α ∩ β`: `clsInter α β` (✱22·02). -/
scoped infixl:70 " ∩ " => QF.clsInter
/-- `α ∪ β`: `clsUnion α β` (✱22·03). -/
scoped infixl:65 " ∪ " => QF.clsUnion
/-- `−α`: `clsCompl α` (✱22·04). -/
scoped prefix:max "−" => QF.clsCompl
/-- `α − β`: `clsDiff α β` (✱22·05). -/
scoped infixl:65 " − " => QF.clsDiff

variable {V : Ty → Type} {S : Sys} {a : Ty}

/-! Checks of the notation: each statement is the definition it names. -/
example (α β : V a → QF V) : (α ⊂ β) = fimp (fun x => x ∈ α) (fun x => x ∈ β) := rfl
example (α β : V a → QF V) : (α ∩ β) = (fun x => QF.and (x ∈ α) (x ∈ β)) := rfl
example (α β : V a → QF V) : (α ∪ β) = (fun x => QF.or (x ∈ α) (x ∈ β)) := rfl
example (α : V a → QF V) : (−α) = (fun x => QF.neg (x ∈ α)) := rfl
example (α β : V a → QF V) : (α − β) = α ∩ −β := rfl
example (α β γ : V a → QF V) : clsInter3 α β γ = (α ∩ β) ∩ γ := rfl
example (α β γ : V a → QF V) : clsUnion3 α β γ = (α ∪ β) ∪ γ := rfl

/-! ## Further steps, each listed in the ledger where used -/

/-- ✱20·18 for an extensional expression G (the analogue of `qcls20_3` for ✱20·3): `⊢ :. α = β . ⊃ : Gα . ≡ . Gβ`,
    by ✱20·18's proof [✱20·11·15], with G's extensionality (`ClsExt`, ✱20·11 for G) for ✱20·11. PM's
    ✱20·18 is stated for a generic f{ẑ(ψz)}; a proposition about a class "expresses an extensional
    property of the determining function of the class" (p. 200). -/
theorem qcls20_18 [Reducibility S] (G : (V a → QF V) → QF V) (hG : ClsExt S G) (ψ χ : V a → QF V) :
    QThm S (imp (clsEq ψ χ) (iff (G ψ) (G χ))) :=
  qsyl (qiffMpr (q20_15 ψ χ)) (hG ψ χ)                                            -- ✱20·11·15

/-- ∼Gα is extensional when Gα is (✱4·11). -/
theorem clsExt_neg {G : (V a → QF V) → QF V} (hG : ClsExt S G) : ClsExt S fun α => .neg (G α) :=
  fun ψ χ => qsyl (hG ψ χ) (qiffMp (QL.t4_11 _ _))

/-- G(−α) is extensional when Gα is: from ψx ≡ₓ χx, x ∼∈ ẑ(ψz) . ≡ₓ . x ∼∈ ẑ(χz) by ✱20·11 (context x ∈ φ!ẑ) and
    ✱4·11, under (x) by ✱10·11·21. -/
theorem clsExt_compl {G : (V a → QF V) → QF V} (hG : ClsExt S G) : ClsExt S fun α => G (−α) :=
  fun ψ χ => qsyl (q10_11_21 fun x => qsyl (q20_11 ψ χ fun φ => mem x φ) (qiffMp (QL.t4_11 _ _)))
    (hG (−ψ) (−χ))

/-! ## ✱22·1–✱22·392 -/

/-- ✱22·1 `⊢ :. α ⊂ β . ≡ : x ∈ α . ⊃ₓ . x ∈ β` [✱4·2 . (✱22·01)] -/
theorem q22_1 (α β : V a → QF V) : QThm S (iff (α ⊂ β) (fimp (fun x => x ∈ α) fun x => x ∈ β)) :=
  QL.t4_2 _

/-- ✱22·2 `⊢ . α ∩ β = x̂(x ∈ α . x ∈ β)` [✱20·2 . (✱22·02)] -/
theorem q22_2 [Reducibility S] (α β : V a → QF V) : QThm S (clsEq (α ∩ β) fun x => QF.and (x ∈ α) (x ∈ β)) :=
  q20_2 _                                                                         -- ✱20·2 . (✱22·02)

/-- ✱22·3 `⊢ . α ∪ β = x̂(x ∈ α . ∨ . x ∈ β)` [✱20·2 . (✱22·03)] -/
theorem q22_3 [Reducibility S] (α β : V a → QF V) : QThm S (clsEq (α ∪ β) fun x => .or (x ∈ α) (x ∈ β)) :=
  q20_2 _                                                                         -- ✱20·2 . (✱22·03)

/-- ✱22·31 `⊢ . −α = x̂(x ∼∈ α)` [✱20·2 . (✱22·04)] -/
theorem q22_31 [Reducibility S] (α : V a → QF V) : QThm S (clsEq (−α) fun x => nmem x α) :=
  q20_2 _                                                                         -- ✱20·2 . (✱22·04)

/-- ✱22·32 `⊢ . α − β = x̂(x ∈ α . x ∼∈ β)` [✱20·2 . (✱22·05) . ✱22·2 . ✱20·32]. By ✱22·05 and ✱22·02, α − β is
    the class x̂(x ∈ α . x ∈ −β), so ✱22·2 (✱20·2) is the definitions' own step. ✱20·32 at −β = ẑ(z ∼∈ β) gives
    x̂(x ∈ −β) = −β, read as x ∈ −β . ≡ₓ . x ∼∈ β by ✱20·15; this replaces the second factor under (x) (✱4·36 with
    ✱4·3, ✱10·11·27), and ✱20·15 gives the identity. -/
theorem q22_32 [Reducibility S] (α β : V a → QF V) : QThm S (clsEq (α − β) fun x => QF.and (x ∈ α) (nmem x β)) :=
  have h1 : QThm S (fiff (fun x => x ∈ −β) fun x => nmem x β) :=
    QThm.mp (q20_32 (−β)) (qiffMpr (q20_15 _ _))                                  -- ✱20·32
  have h2 : QThm S (fiff (α − β) fun x => QF.and (x ∈ α) (nmem x β)) :=
    QThm.mp h1 (q10_11_27 fun x => qandCongrRImp (x ∈ −β) (nmem x β) (x ∈ α))
  QThm.mp h2 (qiffMp (q20_15 _ _))

/-- ✱22·33 `⊢ : x ∈ α ∩ β . ≡ . x ∈ α . x ∈ β` [✱20·3 . ✱22·2]. α ∩ β is the class x̂(x ∈ α . x ∈ β) by ✱22·02,
    so ✱20·3 applies to it directly. -/
theorem q22_33 [Reducibility S] (α β : V a → QF V) (x : V a) : QThm S (iff (x ∈ α ∩ β) (QF.and (x ∈ α) (x ∈ β))) :=
  q20_3 (α ∩ β) x                                                                 -- ✱20·3 . ✱22·2

/-- ✱22·34 `⊢ :. x ∈ α ∪ β . ≡ : x ∈ α . ∨ . x ∈ β` [✱20·3 . ✱22·3] -/
theorem q22_34 [Reducibility S] (α β : V a → QF V) (x : V a) : QThm S (iff (x ∈ α ∪ β) (.or (x ∈ α) (x ∈ β))) :=
  q20_3 (α ∪ β) x                                                                 -- ✱20·3 . ✱22·3

/-- ✱22·35 `⊢ : x ∈ −α . ≡ . x ∼∈ α` [✱20·3 . ✱22·31] -/
theorem q22_35 [Reducibility S] (α : V a → QF V) (x : V a) : QThm S (iff (x ∈ −α) (nmem x α)) :=
  q20_3 (−α) x                                                                    -- ✱20·3 . ✱22·31

/-- ✱22·351 `⊢ . −α ≠ α`. In the first line, ✱22·35 replaces x ∈ −α (✱4·86) and the members are commuted
    (✱4·21) to meet ✱5·19, which is transposed (✱2·16). y is the real variable at which ✱10·251 is used, as in
    `q10_251`: the statement needs a non-empty type, as ✱10·1 does. -/
theorem q22_351 [Reducibility S] (α : V a → QF V) (y : V a) : QThm S (.neg (clsEq (−α) α)) :=
  have h1 : ∀ x, QThm S (.neg (iff (x ∈ −α) (x ∈ α))) := fun x =>
    have e : QThm S (iff (iff (x ∈ −α) (x ∈ α)) (iff (x ∈ α) (nmem x α))) :=
      calc iff (x ∈ −α) (x ∈ α)
          ≡ iff (nmem x α) (x ∈ α) := QThm.mp (q22_35 α x) (QL.t4_86 _ _ _)
        _ ≡ iff (x ∈ α) (nmem x α) := QL.t4_21 _ _
    QThm.mp (QL.t5_19 (x ∈ α)) (QThm.mp (qiffMp e) (QL.t2_16 _ _))                -- ✱22·35 . ✱5·19
  have h2 : QThm S (.all fun x => .neg (iff (x ∈ −α) (x ∈ α))) := q10_11 h1      -- [✱10·11]
  have h3 : QThm S (.neg (fiff (fun x => x ∈ −α) fun x => x ∈ α)) := QThm.mp h2 (q10_251 _ y)  -- [✱10·251]
  QThm.mp h3 (QThm.mp (qiffMp (q20_43 (−α) α)) (QL.t2_16 _ _))                   -- [✱20·43 . Transp]

/-- ✱22·36 `⊢ . α ∩ β ∈ Cls` [✱20·41] -/
theorem q22_36 [Reducibility S] (α β : V a → QF V) : QThm S ((α ∩ β) ∈ Cls) :=
  q20_41 _                                                                        -- [✱20·41]

/-- ✱22·37 `⊢ . α ∪ β ∈ Cls` [✱20·41] -/
theorem q22_37 [Reducibility S] (α β : V a → QF V) : QThm S ((α ∪ β) ∈ Cls) :=
  q20_41 _                                                                        -- [✱20·41]

/-- ✱22·38 `⊢ . −α ∈ Cls` [✱20·41] -/
theorem q22_38 [Reducibility S] (α : V a → QF V) : QThm S ((−α) ∈ Cls) :=
  q20_41 _                                                                        -- [✱20·41]

/-- ✱22·39 `⊢ . ẑ(φz) ∩ ẑ(ψz) = ẑ(φz . ψz)`. In (1), ✱20·3 is used for each factor, joined by ✱4·38. -/
theorem q22_39 [Reducibility S] (φ ψ : V a → QF V) : QThm S (clsEq (φ ∩ ψ) fun z => QF.and (φ z) (ψ z)) :=
  have h1 : ∀ x, QThm S (iff (x ∈ φ ∩ ψ) (QF.and (φ x) (ψ x))) := fun x =>
    calc (x ∈ φ ∩ ψ)
        ≡ QF.and (x ∈ φ) (x ∈ ψ) := q22_33 φ ψ x                                  -- ✱22·33
      _ ≡ QF.and (φ x) (ψ x) := QThm.mp (qandI (q20_3 φ x) (q20_3 ψ x)) (QL.t4_38 _ _ _ _)  -- [✱20·3] (1)
  QThm.mp (q10_11 h1) (qiffMpr (q20_33 (φ ∩ ψ) _))                                -- (1).✱20·33

/-- ✱22·391 `⊢ . ẑ(φz) ∪ ẑ(ψz) = ẑ(φz ∨ ψz)` [Similar proof]: ✱22·34, ✱20·3 for each disjunct (joined by
    ✱4·39), ✱20·33. -/
theorem q22_391 [Reducibility S] (φ ψ : V a → QF V) : QThm S (clsEq (φ ∪ ψ) fun z => .or (φ z) (ψ z)) :=
  have h1 : ∀ x, QThm S (iff (x ∈ φ ∪ ψ) (.or (φ x) (ψ x))) := fun x =>
    calc (x ∈ φ ∪ ψ)
        ≡ QF.or (x ∈ φ) (x ∈ ψ) := q22_34 φ ψ x                                   -- ✱22·34
      _ ≡ QF.or (φ x) (ψ x) := QThm.mp (qandI (q20_3 φ x) (q20_3 ψ x)) (QL.t4_39 _ _ _ _)  -- [✱20·3]
  QThm.mp (q10_11 h1) (qiffMpr (q20_33 (φ ∪ ψ) _))                                -- ✱20·33

/-- ✱22·392 `⊢ . −ẑ(φz) = ẑ(∼φz)` [Similar proof]: ✱22·35, ✱20·3 under ∼ (✱4·11), ✱20·33. -/
theorem q22_392 [Reducibility S] (φ : V a → QF V) : QThm S (clsEq (−φ) fun z => .neg (φ z)) :=
  have h1 : ∀ x, QThm S (iff (x ∈ −φ) (.neg (φ x))) := fun x =>
    calc (x ∈ −φ)
        ≡ nmem x φ := q22_35 φ x                                                  -- ✱22·35
      _ ≡ .neg (φ x) := qiffNeg (q20_3 φ x)                                        -- [✱20·3]
  QThm.mp (q10_11 h1) (qiffMpr (q20_33 (−φ) _))                                   -- ✱20·33

/-! ## ✱22·4–✱22·49: inclusion -/

/-- ✱22·4 `⊢ :. α ⊂ β . β ⊂ α . ≡ : x ∈ α . ≡ₓ . x ∈ β` -/
theorem q22_4 (α β : V a → QF V) :
    QThm S (iff (QF.and (α ⊂ β) (β ⊂ α)) (fiff (fun x => x ∈ α) fun x => x ∈ β)) :=
  calc QF.and (α ⊂ β) (β ⊂ α)
      ≡ QF.and (fimp (fun x => x ∈ α) fun x => x ∈ β) (fimp (fun x => x ∈ β) fun x => x ∈ α) :=
        QThm.mp (qandI (q22_1 α β) (q22_1 β α)) (QL.t4_38 _ _ _ _)                 -- ✱22·1 [✱4·38]
    _ ≡ fiff (fun x => x ∈ α) fun x => x ∈ β :=
        qiffSymm (q10_22 (fun x => imp (x ∈ α) (x ∈ β)) fun x => imp (x ∈ β) (x ∈ α))  -- [✱10·22]

/-- ✱22·41 `⊢ : α ⊂ β . β ⊂ α . ≡ . α = β` [✱22·4 . ✱20·43] -/
theorem q22_41 [Reducibility S] (α β : V a → QF V) : QThm S (iff (QF.and (α ⊂ β) (β ⊂ α)) (clsEq α β)) :=
  qiffTrans (q22_4 α β) (qiffSymm (q20_43 α β))                                   -- ✱22·4 . ✱20·43

/-- ✱22·42 `⊢ . α ⊂ α` [Id . ✱10·11] -/
theorem q22_42 (α : V a → QF V) : QThm S (α ⊂ α) :=
  q10_11 fun x => QL.t2_08 (x ∈ α)                                               -- Id . ✱10·11

/-- ✱22·43 `⊢ : α ∩ β ⊂ α` [✱3·26 . ✱10·11]. x ∈ α ∩ β is first written x ∈ α . x ∈ β by ✱22·33. -/
theorem q22_43 [Reducibility S] (α β : V a → QF V) : QThm S (α ∩ β ⊂ α) :=
  q10_11 fun x => qsyl (qiffMp (q22_33 α β x)) (QL.t3_26 _ _)                     -- ✱3·26 . ✱10·11

/-- ✱22·44 `⊢ : α ⊂ β . β ⊂ γ . ⊃ . α ⊂ γ` [✱10·3] -/
theorem q22_44 (α β γ : V a → QF V) : QThm S (imp (QF.and (α ⊂ β) (β ⊂ γ)) (α ⊂ γ)) :=
  q10_3 _ _ _                                                                     -- [✱10·3]

/-- ✱22·441 `⊢ : α ⊂ β . x ∈ α . ⊃ . x ∈ β` [✱10·1 . Imp] -/
theorem q22_441 (α β : V a → QF V) (x : V a) : QThm S (imp (QF.and (α ⊂ β) (x ∈ α)) (x ∈ β)) :=
  QThm.mp (q10_1 (fun y => imp (y ∈ α) (y ∈ β)) x) (QL.t3_31 _ _ _)              -- ✱10·1 . Imp

/-- ✱22·45 `⊢ : α ⊂ β . α ⊂ γ . ≡ . α ⊂ β ∩ γ`. ✱22·1 is used for both factors (joined by ✱4·38, as in
    ✱22·4); for ✱10·413, x ∈ α . ≡ₓ . x ∈ α is ✱4·2 under (x). -/
theorem q22_45 [Reducibility S] (α β γ : V a → QF V) : QThm S (iff (QF.and (α ⊂ β) (α ⊂ γ)) (α ⊂ β ∩ γ)) :=
  calc QF.and (α ⊂ β) (α ⊂ γ)
      ≡ QF.and (fimp (fun x => x ∈ α) fun x => x ∈ β) (fimp (fun x => x ∈ α) fun x => x ∈ γ) :=
        QThm.mp (qandI (q22_1 α β) (q22_1 α γ)) (QL.t4_38 _ _ _ _)                 -- ✱22·1
    _ ≡ .all (fun x => imp (x ∈ α) (QF.and (x ∈ β) (x ∈ γ))) := q10_29 _ _ _      -- [✱10·29]
    _ ≡ (α ⊂ β ∩ γ) :=
        QThm.mp (QThm.mp (qandI (q10_11 fun x => QL.t4_2 (x ∈ α))
            (q10_11 fun x => qiffSymm (q22_33 β γ x))) (q10_413 _ _ _ _))
          (q10_271 _ _)                                                           -- [✱22·33 . ✱10·413]

/-- ✱22·46 `⊢ : x ∈ α . α ⊂ β . ⊃ . x ∈ β` [✱22·441 . Perm]. PM's "Perm" commutes the factors, which is
    ✱3·22. -/
theorem q22_46 (α β : V a → QF V) (x : V a) : QThm S (imp (QF.and (x ∈ α) (α ⊂ β)) (x ∈ β)) :=
  qsyl (QL.t3_22 _ _) (q22_441 α β x)                                            -- ✱22·441 . Perm

/-- ✱22·47 `⊢ : α ⊂ γ . ⊃ . α ∩ β ⊂ γ` [✱22·43·44] -/
theorem q22_47 [Reducibility S] (α β γ : V a → QF V) : QThm S (imp (α ⊂ γ) (α ∩ β ⊂ γ)) :=
  qsyl (QThm.mp (q22_43 α β) (QL.t3_2 _ _)) (q22_44 (α ∩ β) α γ)                  -- ✱22·43·44

/-- ✱22·48 `⊢ : α ⊂ β . ⊃ . α ∩ γ ⊂ β ∩ γ` [✱10·31]. ✱22·33 writes each membership in a product as the product
    of memberships, under (x) (✱4·84, ✱4·85, ✱10·11·271). -/
theorem q22_48 [Reducibility S] (α β γ : V a → QF V) : QThm S (imp (α ⊂ β) (α ∩ γ ⊂ β ∩ γ)) :=
  qsyl (q10_31 (fun x => x ∈ α) (fun x => x ∈ β) fun x => x ∈ γ)                 -- [✱10·31]
    (qiffMpr (q10_11_271 fun x => qimpIffCongr (q22_33 α γ x) (q22_33 β γ x)))

/-- ✱22·481 `⊢ : α = β . ⊃ . α ∩ γ = β ∩ γ`. ✱22·48 is used for both factors, joined by ✱3·47. -/
theorem q22_481 [Reducibility S] (α β γ : V a → QF V) : QThm S (imp (clsEq α β) (clsEq (α ∩ γ) (β ∩ γ))) :=
  calc clsEq α β
      ⊃ QF.and (α ⊂ β) (β ⊂ α) := qiffMpr (q22_41 α β)                           -- ✱22·41
    _ ⊃ QF.and (α ∩ γ ⊂ β ∩ γ) (β ∩ γ ⊂ α ∩ γ) :=
        QThm.mp (qandI (q22_48 α β γ) (q22_48 β α γ)) (QL.t3_47 _ _ _ _)          -- [✱22·48]
    _ ⊃ clsEq (α ∩ γ) (β ∩ γ) := qiffMp (q22_41 _ _)                              -- [✱22·41]

/-- ✱22·49 `⊢ : α ⊂ β . γ ⊂ δ . ⊃ . α ∩ γ ⊂ β ∩ δ` [✱10·39], with ✱22·33 as in ✱22·48. -/
theorem q22_49 [Reducibility S] (α β γ δ : V a → QF V) :
    QThm S (imp (QF.and (α ⊂ β) (γ ⊂ δ)) (α ∩ γ ⊂ β ∩ δ)) :=
  qsyl (q10_39 (fun x => x ∈ α) (fun x => x ∈ γ) (fun x => x ∈ β) fun x => x ∈ δ)  -- [✱10·39]
    (qiffMpr (q10_11_271 fun x => qimpIffCongr (q22_33 α γ x) (q22_33 β δ x)))

/-! ## ✱22·5–✱22·74: product and sum -/

/-- ✱22·5 `⊢ . α ∩ α = α` -/
theorem q22_5 [Reducibility S] (α : V a → QF V) : QThm S (clsEq (α ∩ α) α) :=
  have h1 : ∀ x, QThm S (iff (x ∈ α ∩ α) (x ∈ α)) := fun x =>
    calc (x ∈ α ∩ α)
        ≡ QF.and (x ∈ α) (x ∈ α) := q22_33 α α x                                  -- ✱22·33
      _ ≡ (x ∈ α) := qiffSymm (QL.t4_24 _)                                         -- [✱4·24] (1)
  QThm.mp (q10_11 h1) (qiffMpr (q20_43 _ _))                                      -- (1).✱10·11.✱20·43

/-- ✱22·51 `⊢ . α ∩ β = β ∩ α` [✱22·33 . ✱4·3 . ✱10·11 . ✱20·43] -/
theorem q22_51 [Reducibility S] (α β : V a → QF V) : QThm S (clsEq (α ∩ β) (β ∩ α)) :=
  have h1 : ∀ x, QThm S (iff (x ∈ α ∩ β) (x ∈ β ∩ α)) := fun x =>
    calc (x ∈ α ∩ β)
        ≡ QF.and (x ∈ α) (x ∈ β) := q22_33 α β x                                  -- ✱22·33
      _ ≡ QF.and (x ∈ β) (x ∈ α) := QL.t4_3 _ _                                    -- ✱4·3
      _ ≡ (x ∈ β ∩ α) := qiffSymm (q22_33 β α x)                                   -- ✱22·33
  QThm.mp (q10_11 h1) (qiffMpr (q20_43 _ _))                                      -- ✱10·11 . ✱20·43

/-- ✱22·52 `⊢ . (α ∩ β) ∩ γ = α ∩ (β ∩ γ)` [✱22·33 . ✱4·32 . ✱10·11 . ✱20·43]. ✱22·33 acts inside a factor
    (✱4·36, with ✱4·3 for the second factor). -/
theorem q22_52 [Reducibility S] (α β γ : V a → QF V) : QThm S (clsEq ((α ∩ β) ∩ γ) (α ∩ (β ∩ γ))) :=
  have h1 : ∀ x, QThm S (iff (x ∈ (α ∩ β) ∩ γ) (x ∈ α ∩ (β ∩ γ))) := fun x =>
    calc (x ∈ (α ∩ β) ∩ γ)
        ≡ QF.and (x ∈ α ∩ β) (x ∈ γ) := q22_33 _ _ x                               -- ✱22·33
      _ ≡ QF.and (QF.and (x ∈ α) (x ∈ β)) (x ∈ γ) := qandCongrL _ (q22_33 α β x)   -- ✱22·33
      _ ≡ QF.and (x ∈ α) (QF.and (x ∈ β) (x ∈ γ)) := QL.t4_32 _ _ _                -- ✱4·32
      _ ≡ QF.and (x ∈ α) (x ∈ β ∩ γ) := qandCongrR _ (qiffSymm (q22_33 β γ x))    -- ✱22·33
      _ ≡ (x ∈ α ∩ (β ∩ γ)) := qiffSymm (q22_33 _ _ x)                             -- ✱22·33
  QThm.mp (q10_11 h1) (qiffMpr (q20_43 _ _))                                      -- ✱10·11 . ✱20·43

/-- ✱22·54 `⊢ :. α = β . ⊃ : α ⊂ γ . ≡ . β ⊂ γ` [✱20·18]: ✱20·18 for the expression α ⊂ γ (`qcls20_18`), which is
    extensional as every expression of a class that PM forms is (`clsExpr_ext`, p. 200). -/
theorem q22_54 [Reducibility S] (α β γ : V a → QF V) : QThm S (imp (clsEq α β) (iff (α ⊂ γ) (β ⊂ γ))) :=
  qcls20_18 (fun α => α ⊂ γ) (clsExpr_ext (.all fun x => .imp (ClsExpr.clsMem x) (.const _))) α β  -- [✱20·18]

/-- ✱22·55 `⊢ :. α = β . ⊃ : γ ⊂ α . ≡ . γ ⊂ β` [✱20·18], as ✱22·54. -/
theorem q22_55 [Reducibility S] (α β γ : V a → QF V) : QThm S (imp (clsEq α β) (iff (γ ⊂ α) (γ ⊂ β))) :=
  qcls20_18 (fun α => γ ⊂ α) (clsExpr_ext (.all fun x => .imp (.const _) (ClsExpr.clsMem x))) α β  -- [✱20·18]

/-- ✱22·551 `⊢ : α = β . ⊃ . α ∪ γ = β ∪ γ` [✱10·11]: α = β is x ∈ α . ≡ₓ . x ∈ β by ✱20·43; with x ∈ γ . ≡ₓ .
    x ∈ γ (✱4·2 under (x), joined by ✱3·2 and Comm), ✱10·411 gives the formal equivalence of the sums, which
    ✱22·34 (✱4·86 under (x)) and ✱20·43 turn into the identity. -/
theorem q22_551 [Reducibility S] (α β γ : V a → QF V) : QThm S (imp (clsEq α β) (clsEq (α ∪ γ) (β ∪ γ))) :=
  have e : QThm S (fiff (fun x => x ∈ γ) fun x => x ∈ γ) := q10_11 fun _ => QL.t4_2 _
  calc clsEq α β
      ⊃ fiff (fun x => x ∈ α) (fun x => x ∈ β) := qiffMp (q20_43 α β)
    _ ⊃ QF.and (fiff (fun x => x ∈ α) (fun x => x ∈ β)) (fiff (fun x => x ∈ γ) fun x => x ∈ γ) :=
        QThm.mp e (QThm.mp (QL.t3_2 _ _) (QL.t2_04 _ _ _))
    _ ⊃ fiff (fun x => .or (x ∈ α) (x ∈ γ)) (fun x => .or (x ∈ β) (x ∈ γ)) := q10_411 _ _ _ _  -- [✱10·411]
    _ ⊃ fiff (fun x => x ∈ α ∪ γ) (fun x => x ∈ β ∪ γ) :=
        qiffMpr (q10_11_271 fun x => qiffIffCongr (q22_34 α γ x) (q22_34 β γ x))
    _ ⊃ clsEq (α ∪ γ) (β ∪ γ) := qiffMpr (q20_43 _ _)

/-- ✱22·56 `⊢ . α ∪ α = α` [✱4·25 . ✱10·11], with ✱22·34 and ✱20·43 as in ✱22·5. -/
theorem q22_56 [Reducibility S] (α : V a → QF V) : QThm S (clsEq (α ∪ α) α) :=
  have h1 : ∀ x, QThm S (iff (x ∈ α ∪ α) (x ∈ α)) := fun x =>
    calc (x ∈ α ∪ α)
        ≡ QF.or (x ∈ α) (x ∈ α) := q22_34 α α x
      _ ≡ (x ∈ α) := qiffSymm (QL.t4_25 _)                                         -- ✱4·25
  QThm.mp (q10_11 h1) (qiffMpr (q20_43 _ _))                                      -- ✱10·11

/-- ✱22·57 `⊢ . α ∪ β = β ∪ α` [✱4·31 . ✱10·11], with ✱22·34 and ✱20·43. -/
theorem q22_57 [Reducibility S] (α β : V a → QF V) : QThm S (clsEq (α ∪ β) (β ∪ α)) :=
  have h1 : ∀ x, QThm S (iff (x ∈ α ∪ β) (x ∈ β ∪ α)) := fun x =>
    calc (x ∈ α ∪ β)
        ≡ QF.or (x ∈ α) (x ∈ β) := q22_34 α β x
      _ ≡ QF.or (x ∈ β) (x ∈ α) := QL.t4_31 _ _                                    -- ✱4·31
      _ ≡ (x ∈ β ∪ α) := qiffSymm (q22_34 β α x)
  QThm.mp (q10_11 h1) (qiffMpr (q20_43 _ _))                                      -- ✱10·11

/-- ✱22·58 `⊢ . α ⊂ α ∪ β . β ⊂ α ∪ β` [✱1·3 . ✱2·2], with ✱22·34 (and ✱10·11). -/
theorem q22_58 [Reducibility S] (α β : V a → QF V) : QThm S (QF.and (α ⊂ α ∪ β) (β ⊂ α ∪ β)) :=
  qandI (q10_11 fun x => qsyl (QL.t2_2 (x ∈ α) (x ∈ β)) (qiffMpr (q22_34 α β x)))  -- ✱2·2
    (q10_11 fun x => qsyl (QThm.add (x ∈ α) (x ∈ β)) (qiffMpr (q22_34 α β x)))     -- ✱1·3

/-- ✱22·59 `⊢ : α ⊂ γ . β ⊂ γ . ≡ . α ∪ β ⊂ γ`. ✱22·1 is used for both factors (✱4·38); PM's "[✱10*22]" is
    ✱10·22; for ✱10·413, x ∈ γ . ≡ₓ . x ∈ γ is ✱4·2 under (x). -/
theorem q22_59 [Reducibility S] (α β γ : V a → QF V) : QThm S (iff (QF.and (α ⊂ γ) (β ⊂ γ)) (α ∪ β ⊂ γ)) :=
  calc QF.and (α ⊂ γ) (β ⊂ γ)
      ≡ QF.and (fimp (fun x => x ∈ α) fun x => x ∈ γ) (fimp (fun x => x ∈ β) fun x => x ∈ γ) :=
        QThm.mp (qandI (q22_1 α γ) (q22_1 β γ)) (QL.t4_38 _ _ _ _)                 -- ✱22·1
    _ ≡ .all (fun x => QF.and (imp (x ∈ α) (x ∈ γ)) (imp (x ∈ β) (x ∈ γ))) :=
        qiffSymm (q10_22 _ _)                                                     -- [✱10·22]
    _ ≡ .all (fun x => imp (.or (x ∈ α) (x ∈ β)) (x ∈ γ)) :=
        q10_11_271 fun _ => QL.t4_77 _ _ _                                         -- [✱4·77 . ✱10·271]
    _ ≡ (α ∪ β ⊂ γ) :=
        QThm.mp (QThm.mp (qandI (q10_11 fun x => qiffSymm (q22_34 α β x))
            (q10_11 fun x => QL.t4_2 (x ∈ γ))) (q10_413 _ _ _ _))
          (q10_271 _ _)                                                           -- [✱22·34 . ✱10·413]

/-- ✱22·6 `⊢ :. x ∈ α ∪ β . ≡ : α ⊂ γ . β ⊂ γ . ⊃_γ . x ∈ γ`, γ apparent (✱20·07). In (1), ✱22·59 gives
    α ∪ β ⊂ γ, used at x by ✱10·1. In (2), PM's ✱10·1 instantiates γ at α ∪ β, whose defining function is
    not predicative: the class analogue (`qclsAllAt`; p. 206, ✱20·17), the expression being extensional
    (`clsExpr_ext`); "[✱22·58]" detaches its antecedent by ✱2·27. -/
theorem q22_6 [Reducibility S] (α β : V a → QF V) (x : V a) :
    QThm S (iff (x ∈ α ∪ β) (clsAll fun γ => imp (QF.and (α ⊂ γ) (β ⊂ γ)) (x ∈ γ))) :=
  let G : (V a → QF V) → QF V := fun γ => imp (QF.and (α ⊂ γ) (β ⊂ γ)) (x ∈ γ)
  have hG : ClsExpr G :=
    .imp (.and (.all fun y => .imp (.const _) (ClsExpr.clsMem y)) (.all fun y => .imp (.const _) (ClsExpr.clsMem y)))
      (ClsExpr.clsMem x)
  have h1 : QThm S (imp (x ∈ α ∪ β) (clsAll G)) :=
    q10_11_21 fun θ =>
      have k := qsyl (qiffMp (q22_59 α β (pf θ))) (q10_1 (fun y => imp (y ∈ α ∪ β) (y ∈ pf θ)) x)  -- ✱22·59
      QThm.mp k (QL.t2_04 _ _ _)                                                  -- [Comm] [✱10·11·21] (1)
  have h2 : QThm S (imp (clsAll G) (x ∈ α ∪ β)) :=
    qsyl (qclsAllAt G (α ∪ β) fun θ => qsyl (clsExpr_ext hG (pf θ) (α ∪ β)) (QL.t3_26 _ _))  -- ✱10·1
      (QThm.mp (q22_58 α β) (QL.t2_27 _ _))                                       -- [✱22·58] (2)
  qiffI h1 h2                                                                     -- (1).(2)

/-- ✱22·61 `⊢ : α ⊂ β . ⊃ . α ⊂ β ∪ γ` [✱22·44·58] (PM's "✱22*44·58"): β ⊂ β ∪ γ is the first factor of ✱22·58
    (✱3·26), put beside α ⊂ β by ✱3·2 and Comm. -/
theorem q22_61 [Reducibility S] (α β γ : V a → QF V) : QThm S (imp (α ⊂ β) (α ⊂ β ∪ γ)) :=
  have h : QThm S (β ⊂ β ∪ γ) := QThm.mp (q22_58 β γ) (QL.t3_26 _ _)              -- ✱22·58
  qsyl (QThm.mp h (QThm.mp (QL.t3_2 _ _) (QL.t2_04 _ _ _))) (q22_44 α β (β ∪ γ))   -- ✱22·44

/-- ✱22·62 `⊢ : α ⊂ β . ≡ . α ∪ β = β`. ✱4·72's second member is commuted (✱4·21), and ✱22·34 replaces its
    first member (✱4·86). -/
theorem q22_62 [Reducibility S] (α β : V a → QF V) : QThm S (iff (α ⊂ β) (clsEq (α ∪ β) β)) :=
  have h1 : ∀ x, QThm S (iff (imp (x ∈ α) (x ∈ β)) (iff (x ∈ α ∪ β) (x ∈ β))) := fun x =>
    calc imp (x ∈ α) (x ∈ β)
        ≡ iff (x ∈ β) (.or (x ∈ α) (x ∈ β)) := QL.t4_72 _ _                        -- ✱4·72
      _ ≡ iff (.or (x ∈ α) (x ∈ β)) (x ∈ β) := QL.t4_21 _ _
      _ ≡ iff (x ∈ α ∪ β) (x ∈ β) := QThm.mp (qiffSymm (q22_34 α β x)) (QL.t4_86 _ _ _)  -- [✱22·34] (1)
  calc (α ⊂ β)
      ≡ fiff (fun x => x ∈ α ∪ β) (fun x => x ∈ β) := q10_11_271 h1                -- (1).✱10·271
    _ ≡ clsEq (α ∪ β) β := qiffSymm (q20_43 _ _)                                   -- [✱20·43]

/-- ✱22·621 `⊢ : α ⊂ β . ≡ . α ∩ β = α` [✱4·71], under (x) (✱10·11·271), with ✱22·33 (✱4·86), the members
    commuted (✱4·21), and ✱20·43, as in ✱22·62. -/
theorem q22_621 [Reducibility S] (α β : V a → QF V) : QThm S (iff (α ⊂ β) (clsEq (α ∩ β) α)) :=
  have h1 : ∀ x, QThm S (iff (imp (x ∈ α) (x ∈ β)) (iff (x ∈ α ∩ β) (x ∈ α))) := fun x =>
    calc imp (x ∈ α) (x ∈ β)
        ≡ iff (x ∈ α) (QF.and (x ∈ α) (x ∈ β)) := QL.t4_71 _ _                     -- ✱4·71
      _ ≡ iff (QF.and (x ∈ α) (x ∈ β)) (x ∈ α) := QL.t4_21 _ _
      _ ≡ iff (x ∈ α ∩ β) (x ∈ α) := QThm.mp (qiffSymm (q22_33 α β x)) (QL.t4_86 _ _ _)
  qiffTrans (q10_11_271 h1) (qiffSymm (q20_43 _ _))

/-- ✱22·63 `⊢ : α ∪ (α ∩ β) = α` [✱4·44], with ✱22·34, ✱22·33 (inside the second disjunct: ✱4·37 with ✱4·31),
    ✱10·11 and ✱20·43. -/
theorem q22_63 [Reducibility S] (α β : V a → QF V) : QThm S (clsEq (α ∪ (α ∩ β)) α) :=
  have h1 : ∀ x, QThm S (iff (x ∈ α ∪ (α ∩ β)) (x ∈ α)) := fun x =>
    calc (x ∈ α ∪ (α ∩ β))
        ≡ QF.or (x ∈ α) (x ∈ α ∩ β) := q22_34 _ _ x
      _ ≡ QF.or (x ∈ α) (QF.and (x ∈ α) (x ∈ β)) := QThm.mp (q22_33 α β x) (qorCongrRImp _ _ _)
      _ ≡ (x ∈ α) := qiffSymm (QL.t4_44 _ _)                                       -- ✱4·44
  QThm.mp (q10_11 h1) (qiffMpr (q20_43 _ _))

/-- ✱22·631 `⊢ . α ∩ (α ∪ β) = α` [✱22·58·621]. The first factor of ✱22·58 is taken by ✱3·26. -/
theorem q22_631 [Reducibility S] (α β : V a → QF V) : QThm S (clsEq (α ∩ (α ∪ β)) α) :=
  QThm.mp (QThm.mp (q22_58 α β) (QL.t3_26 _ _)) (qiffMp (q22_621 α (α ∪ β)))       -- ✱22·58·621

/-- ✱22·632 `⊢ : α = β . ⊃ . α = α ∩ β` [✱22·42·621]. From α = β, α ⊂ α (✱22·42) gives α ⊂ β by ✱22·55 (with
    ✱2·27); ✱22·621 gives α ∩ β = α, turned by ✱20·21. -/
theorem q22_632 [Reducibility S] (α β : V a → QF V) : QThm S (imp (clsEq α β) (clsEq α (α ∩ β))) :=
  calc clsEq α β
      ⊃ (α ⊂ β) := qsyl (q22_55 α β α) (qsyl (QL.t3_26 _ _) (QThm.mp (q22_42 α) (QL.t2_27 _ _)))  -- ✱22·42
    _ ⊃ clsEq (α ∩ β) α := qiffMp (q22_621 α β)                                    -- ✱22·621
    _ ⊃ clsEq α (α ∩ β) := qiffMp (q20_21 _ _)

/-- ✱22·633 `⊢ : α ⊂ β . ⊃ . α ∪ γ = (α ∩ β) ∪ γ` [✱22·551·621]. ✱22·621's α ∩ β = α is turned by ✱20·21. -/
theorem q22_633 [Reducibility S] (α β γ : V a → QF V) : QThm S (imp (α ⊂ β) (clsEq (α ∪ γ) ((α ∩ β) ∪ γ))) :=
  calc (α ⊂ β)
      ⊃ clsEq (α ∩ β) α := qiffMp (q22_621 α β)                                    -- ✱22·621
    _ ⊃ clsEq α (α ∩ β) := qiffMp (q20_21 _ _)
    _ ⊃ clsEq (α ∪ γ) ((α ∩ β) ∪ γ) := q22_551 _ _ γ                               -- ✱22·551

/-- ✱22·64 `⊢ :. α ⊂ γ . ∨ . β ⊂ γ : ⊃ . α ∩ β ⊂ γ`. In (1), ✱22·47 at β, α gives β ∩ α ⊂ γ, carried to α ∩ β ⊂ γ
    by ✱22·51 and ✱22·54; the two implications are joined by ✱3·2. -/
theorem q22_64 [Reducibility S] (α β γ : V a → QF V) :
    QThm S (imp (.or (α ⊂ γ) (β ⊂ γ)) (α ∩ β ⊂ γ)) :=
  have h1 : QThm S (QF.and (imp (α ⊂ γ) (α ∩ β ⊂ γ)) (imp (β ⊂ γ) (α ∩ β ⊂ γ))) :=
    qandI (q22_47 α β γ)
      (qsyl (q22_47 β α γ) (qiffMp (QThm.mp (q22_51 β α) (q22_54 _ _ γ))))        -- ✱22·47·51 (1)
  QThm.mp h1 (qiffMp (QL.t4_77 _ _ _))                                            -- (1).✱4·77

/-- ✱22·65 `⊢ :. α ⊂ β . ∨ . α ⊂ γ : ⊃ . α ⊂ β ∪ γ` [✱22·61·57 . ✱4·77]. ✱22·61 at γ, β gives α ⊂ γ ∪ β, carried to
    α ⊂ β ∪ γ by ✱22·57 and ✱22·55; joined by ✱3·2. -/
theorem q22_65 [Reducibility S] (α β γ : V a → QF V) :
    QThm S (imp (.or (α ⊂ β) (α ⊂ γ)) (α ⊂ β ∪ γ)) :=
  QThm.mp (qandI (q22_61 α β γ) (qsyl (q22_61 α γ β) (qiffMp (QThm.mp (q22_57 γ β) (q22_55 _ _ α)))))
    (qiffMp (QL.t4_77 _ _ _))                                                     -- ✱22·61·57 . ✱4·77

/-- ✱22·66 `⊢ : α ⊂ β . ⊃ . α ∪ γ ⊂ β ∪ γ` [✱2·38], under (x) (✱10·11·27), with ✱22·34 (✱4·84, ✱4·85, ✱10·11·271). -/
theorem q22_66 [Reducibility S] (α β γ : V a → QF V) : QThm S (imp (α ⊂ β) (α ∪ γ ⊂ β ∪ γ)) :=
  qsyl (q10_11_27 fun x => QL.t2_38 (x ∈ γ) (x ∈ α) (x ∈ β))                      -- ✱2·38
    (qiffMpr (q10_11_271 fun x => qimpIffCongr (q22_34 α γ x) (q22_34 β γ x)))

/-- ✱22·68 `⊢ . (α ∩ β) ∪ (α ∩ γ) = α ∩ (β ∪ γ)`. ✱22·33 acts on both disjuncts (✱4·39) and ✱22·34 on the second
    factor (✱4·36 with ✱4·3); ✱4·4 is read from right to left. -/
theorem q22_68 [Reducibility S] (α β γ : V a → QF V) : QThm S (clsEq ((α ∩ β) ∪ (α ∩ γ)) (α ∩ (β ∪ γ))) :=
  have h1 : ∀ x, QThm S (iff (x ∈ (α ∩ β) ∪ (α ∩ γ)) (x ∈ α ∩ (β ∪ γ))) := fun x =>
    calc (x ∈ (α ∩ β) ∪ (α ∩ γ))
        ≡ QF.or (x ∈ α ∩ β) (x ∈ α ∩ γ) := q22_34 _ _ x                            -- ✱22·34
      _ ≡ QF.or (QF.and (x ∈ α) (x ∈ β)) (QF.and (x ∈ α) (x ∈ γ)) :=
          QThm.mp (qandI (q22_33 α β x) (q22_33 α γ x)) (QL.t4_39 _ _ _ _)         -- [✱22·33]
      _ ≡ QF.and (x ∈ α) (.or (x ∈ β) (x ∈ γ)) := qiffSymm (QL.t4_4 _ _ _)          -- [✱4·4]
      _ ≡ QF.and (x ∈ α) (x ∈ β ∪ γ) := qandCongrR _ (qiffSymm (q22_34 β γ x))     -- [✱22·34]
      _ ≡ (x ∈ α ∩ (β ∪ γ)) := qiffSymm (q22_33 _ _ x)                             -- [✱22·33] (1)
  QThm.mp (q10_11 h1) (qiffMpr (q20_43 _ _))                                      -- (1).✱10·11.✱20·43

/-- ✱22·69 `⊢ . (α ∪ β) ∩ (α ∪ γ) = α ∪ (β ∩ γ)` [Similar proof, by ✱4·41]: ✱22·33, ✱22·34 on both factors
    (✱4·38), ✱4·41 from right to left, ✱22·33 in the second disjunct (✱4·37 with ✱4·31), ✱22·34. -/
theorem q22_69 [Reducibility S] (α β γ : V a → QF V) : QThm S (clsEq ((α ∪ β) ∩ (α ∪ γ)) (α ∪ (β ∩ γ))) :=
  have h1 : ∀ x, QThm S (iff (x ∈ (α ∪ β) ∩ (α ∪ γ)) (x ∈ α ∪ (β ∩ γ))) := fun x =>
    calc (x ∈ (α ∪ β) ∩ (α ∪ γ))
        ≡ QF.and (x ∈ α ∪ β) (x ∈ α ∪ γ) := q22_33 _ _ x                           -- ✱22·33
      _ ≡ QF.and (.or (x ∈ α) (x ∈ β)) (.or (x ∈ α) (x ∈ γ)) :=
          QThm.mp (qandI (q22_34 α β x) (q22_34 α γ x)) (QL.t4_38 _ _ _ _)         -- ✱22·34
      _ ≡ QF.or (x ∈ α) (QF.and (x ∈ β) (x ∈ γ)) := qiffSymm (QL.t4_41 _ _ _)      -- ✱4·41
      _ ≡ QF.or (x ∈ α) (x ∈ β ∩ γ) := QThm.mp (qiffSymm (q22_33 β γ x)) (qorCongrRImp _ _ _)  -- ✱22·33
      _ ≡ (x ∈ α ∪ (β ∩ γ)) := qiffSymm (q22_34 _ _ x)                             -- ✱22·34
  QThm.mp (q10_11 h1) (qiffMpr (q20_43 _ _))                                      -- ✱10·11 . ✱20·43

/-- ✱22·7 `⊢ . (α ∪ β) ∪ γ = α ∪ (β ∪ γ)` [✱4·33], with ✱22·34 (inside a disjunct: ✱4·37, with ✱4·31 for the
    second), ✱10·11 and ✱20·43, as ✱22·52. -/
theorem q22_7 [Reducibility S] (α β γ : V a → QF V) : QThm S (clsEq ((α ∪ β) ∪ γ) (α ∪ (β ∪ γ))) :=
  have h1 : ∀ x, QThm S (iff (x ∈ (α ∪ β) ∪ γ) (x ∈ α ∪ (β ∪ γ))) := fun x =>
    calc (x ∈ (α ∪ β) ∪ γ)
        ≡ QF.or (x ∈ α ∪ β) (x ∈ γ) := q22_34 _ _ x
      _ ≡ QF.or (.or (x ∈ α) (x ∈ β)) (x ∈ γ) := QThm.mp (q22_34 α β x) (QL.t4_37 _ _ _)
      _ ≡ QF.or (x ∈ α) (.or (x ∈ β) (x ∈ γ)) := QL.t4_33 _ _ _                    -- ✱4·33
      _ ≡ QF.or (x ∈ α) (x ∈ β ∪ γ) := QThm.mp (qiffSymm (q22_34 β γ x)) (qorCongrRImp _ _ _)
      _ ≡ (x ∈ α ∪ (β ∪ γ)) := qiffSymm (q22_34 _ _ x)
  QThm.mp (q10_11 h1) (qiffMpr (q20_43 _ _))

/-- ✱22·72 `⊢ : α ⊂ γ . β ⊂ δ . ⊃ . α ∪ β ⊂ γ ∪ δ` [✱3·48]. The two formal implications are joined under (x) by
    ✱10·22, ✱3·48 is carried under (x) (✱10·11·27), and ✱22·34 writes the sums as in ✱22·66. -/
theorem q22_72 [Reducibility S] (α β γ δ : V a → QF V) :
    QThm S (imp (QF.and (α ⊂ γ) (β ⊂ δ)) (α ∪ β ⊂ γ ∪ δ)) :=
  calc QF.and (α ⊂ γ) (β ⊂ δ)
      ⊃ .all (fun x => QF.and (imp (x ∈ α) (x ∈ γ)) (imp (x ∈ β) (x ∈ δ))) := qiffMpr (q10_22 _ _)
    _ ⊃ .all (fun x => imp (.or (x ∈ α) (x ∈ β)) (.or (x ∈ γ) (x ∈ δ))) :=
        q10_11_27 fun _ => QL.t3_48 _ _ _ _                                        -- [✱3·48]
    _ ⊃ (α ∪ β ⊂ γ ∪ δ) := qiffMpr (q10_11_271 fun x => qimpIffCongr (q22_34 α β x) (q22_34 γ δ x))

/-- ✱22·73 `⊢ : α = γ . β = δ . ⊃ . α ∪ β = γ ∪ δ` [✱10·411], with ✱20·43 for each factor (✱3·47) and ✱22·34
    (✱4·86 under (x)) as in ✱22·551. -/
theorem q22_73 [Reducibility S] (α β γ δ : V a → QF V) :
    QThm S (imp (QF.and (clsEq α γ) (clsEq β δ)) (clsEq (α ∪ β) (γ ∪ δ))) :=
  calc QF.and (clsEq α γ) (clsEq β δ)
      ⊃ QF.and (fiff (fun x => x ∈ α) fun x => x ∈ γ) (fiff (fun x => x ∈ β) fun x => x ∈ δ) :=
        QThm.mp (qandI (qiffMp (q20_43 α γ)) (qiffMp (q20_43 β δ))) (QL.t3_47 _ _ _ _)
    _ ⊃ fiff (fun x => .or (x ∈ α) (x ∈ β)) (fun x => .or (x ∈ γ) (x ∈ δ)) := q10_411 _ _ _ _  -- [✱10·411]
    _ ⊃ fiff (fun x => x ∈ α ∪ β) (fun x => x ∈ γ ∪ δ) :=
        qiffMpr (q10_11_271 fun x => qiffIffCongr (q22_34 α β x) (q22_34 γ δ x))
    _ ⊃ clsEq (α ∪ β) (γ ∪ δ) := qiffMpr (q20_43 _ _)

/-- ✱22·74 `⊢ : α ∩ β ⊂ γ . α ∩ γ ⊂ β . ≡ . α ∩ β = α ∩ γ`. In the first line, ✱22·43 gives the antecedent of
    ✱4·73, whose product has its factors in the other order (✱4·3). -/
theorem q22_74 [Reducibility S] (α β γ : V a → QF V) :
    QThm S (iff (QF.and (α ∩ β ⊂ γ) (α ∩ γ ⊂ β)) (clsEq (α ∩ β) (α ∩ γ))) :=
  have h1 : ∀ β γ : V a → QF V, QThm S (iff (α ∩ β ⊂ γ) (α ∩ β ⊂ α ∩ γ)) := fun β γ =>
    calc (α ∩ β ⊂ γ)
        ≡ QF.and (α ∩ β ⊂ γ) (α ∩ β ⊂ α) := QThm.mp (q22_43 α β) (QL.t4_73 _ _)
      _ ≡ QF.and (α ∩ β ⊂ α) (α ∩ β ⊂ γ) := QL.t4_3 _ _                            -- ✱22·43 . ✱4·73
      _ ≡ (α ∩ β ⊂ α ∩ γ) := q22_45 _ _ _                                          -- [✱22·45] (1)
  calc QF.and (α ∩ β ⊂ γ) (α ∩ γ ⊂ β)
      ≡ QF.and (α ∩ β ⊂ α ∩ γ) (α ∩ γ ⊂ α ∩ β) :=
        QThm.mp (qandI (h1 β γ) (h1 γ β)) (QL.t4_38 _ _ _ _)                       -- (1).(2).✱4·38
    _ ≡ clsEq (α ∩ β) (α ∩ γ) := q22_41 _ _                                        -- [✱22·41]

/-! ## ✱22·8–✱22·95: negation -/

/-- ✱22·8 `⊢ . −(−α) = α` [✱4·13], with ✱22·35 (inside the negation: ✱4·11), ✱10·11 and ✱20·43. -/
theorem q22_8 [Reducibility S] (α : V a → QF V) : QThm S (clsEq (−(−α)) α) :=
  have h1 : ∀ x, QThm S (iff (x ∈ −(−α)) (x ∈ α)) := fun x =>
    calc (x ∈ −(−α))
        ≡ nmem x (−α) := q22_35 _ x
      _ ≡ .neg (nmem x α) := qiffNeg (q22_35 α x)
      _ ≡ (x ∈ α) := qiffSymm (QL.t4_13 _)                                         -- ✱4·13
  QThm.mp (q10_11 h1) (qiffMpr (q20_43 _ _))

/-- ✱22·81 `⊢ : α ⊂ β . ≡ . −β ⊂ −α` [✱4·1], under (x) (✱10·11·271), with ✱22·35 (✱4·84, ✱4·85). -/
theorem q22_81 [Reducibility S] (α β : V a → QF V) : QThm S (iff (α ⊂ β) (−β ⊂ −α)) :=
  q10_11_271 fun x =>
    qiffTrans (QL.t4_1 (x ∈ α) (x ∈ β))                                            -- ✱4·1
      (qimpIffCongr (qiffSymm (q22_35 β x)) (qiffSymm (q22_35 α x)))

/-- ✱22·811 `⊢ : α ⊂ −β . ≡ . β ⊂ −α` [✱4·1 . ✱22·8]. ✱4·1 under (x) is ✱22·81 (at α, −β), and ✱22·8 replaces
    −(−β) by β, by ✱22·54. -/
theorem q22_811 [Reducibility S] (α β : V a → QF V) : QThm S (iff (α ⊂ −β) (β ⊂ −α)) :=
  qiffTrans (q22_81 α (−β)) (QThm.mp (q22_8 β) (q22_54 _ _ (−α)))                -- ✱4·1 . ✱22·8

/-- ✱22·82 `⊢ : α ∩ β ⊂ γ . ≡ . α − γ ⊂ −β` [✱4·14], under (x) (✱10·11·271), with ✱22·33 and ✱22·35 (✱4·84,
    ✱4·85, and ✱4·36 with ✱4·3 for the second factor). -/
theorem q22_82 [Reducibility S] (α β γ : V a → QF V) : QThm S (iff (α ∩ β ⊂ γ) (α − γ ⊂ −β)) :=
  q10_11_271 fun x =>
    calc imp (x ∈ α ∩ β) (x ∈ γ)
        ≡ imp (QF.and (x ∈ α) (x ∈ β)) (x ∈ γ) := qimpIffCongr (q22_33 α β x) (QL.t4_2 _)
      _ ≡ imp (QF.and (x ∈ α) (nmem x γ)) (nmem x β) := QL.t4_14 _ _ _             -- ✱4·14
      _ ≡ imp (x ∈ α − γ) (x ∈ −β) :=
          qimpIffCongr (qiffTrans (qandCongrR _ (qiffSymm (q22_35 γ x))) (qiffSymm (q22_33 α (−γ) x)))
            (qiffSymm (q22_35 β x))

/-- ✱22·83 `⊢ : α = β . ≡ . −α = −β` [✱4·11], under (x) (✱10·11·271), with ✱20·43 and ✱22·35 (✱4·86). -/
theorem q22_83 [Reducibility S] (α β : V a → QF V) : QThm S (iff (clsEq α β) (clsEq (−α) (−β))) :=
  calc clsEq α β
      ≡ fiff (fun x => x ∈ α) (fun x => x ∈ β) := q20_43 α β
    _ ≡ fiff (fun x => nmem x α) (fun x => nmem x β) := q10_11_271 fun _ => QL.t4_11 _ _  -- ✱4·11
    _ ≡ fiff (fun x => x ∈ −α) (fun x => x ∈ −β) :=
        q10_11_271 fun x => qiffIffCongr (qiffSymm (q22_35 α x)) (qiffSymm (q22_35 β x))
    _ ≡ clsEq (−α) (−β) := qiffSymm (q20_43 _ _)

/-- ✱22·831 `⊢ : α = −β . ≡ . β = −α` [✱4·12], under (x) (✱10·11·271), with ✱20·43 and ✱22·35 (✱4·86). -/
theorem q22_831 [Reducibility S] (α β : V a → QF V) : QThm S (iff (clsEq α (−β)) (clsEq β (−α))) :=
  calc clsEq α (−β)
      ≡ fiff (fun x => x ∈ α) (fun x => x ∈ −β) := q20_43 _ _
    _ ≡ fiff (fun x => x ∈ α) (fun x => nmem x β) :=
        q10_11_271 fun x => QThm.mp (q22_35 β x) (qiffCongrRImp _ _ _)
    _ ≡ fiff (fun x => x ∈ β) (fun x => nmem x α) := q10_11_271 fun _ => QL.t4_12 _ _  -- ✱4·12
    _ ≡ fiff (fun x => x ∈ β) (fun x => x ∈ −α) :=
        q10_11_271 fun x => QThm.mp (qiffSymm (q22_35 α x)) (qiffCongrRImp _ _ _)
    _ ≡ clsEq β (−α) := qiffSymm (q20_43 _ _)

/-- ✱22·84 `⊢ . −(α ∩ β) = −α ∪ −β` [✱4·51], with ✱22·35, ✱22·33 (inside the negation: ✱4·11), ✱22·35 on each
    disjunct (✱4·39), ✱22·34, ✱10·11 and ✱20·43. The transcription prints `−α ∨ −β`; a sum of classes is ∪
    (✱22·03), as in ✱22·86. -/
theorem q22_84 [Reducibility S] (α β : V a → QF V) : QThm S (clsEq (−(α ∩ β)) (−α ∪ −β)) :=
  have h1 : ∀ x, QThm S (iff (x ∈ −(α ∩ β)) (x ∈ −α ∪ −β)) := fun x =>
    calc (x ∈ −(α ∩ β))
        ≡ nmem x (α ∩ β) := q22_35 _ x
      _ ≡ .neg (QF.and (x ∈ α) (x ∈ β)) := qiffNeg (q22_33 α β x)
      _ ≡ QF.or (nmem x α) (nmem x β) := QL.t4_51 _ _                               -- ✱4·51
      _ ≡ QF.or (x ∈ −α) (x ∈ −β) :=
          QThm.mp (qandI (qiffSymm (q22_35 α x)) (qiffSymm (q22_35 β x))) (QL.t4_39 _ _ _ _)
      _ ≡ (x ∈ −α ∪ −β) := qiffSymm (q22_34 _ _ x)
  QThm.mp (q10_11 h1) (qiffMpr (q20_43 _ _))

/-- ✱22·85 `⊢ . α ∩ β = −(−α ∪ −β)` [✱22·84·831]. ✱22·84 is turned by ✱20·21 for ✱22·831. The transcription
    prints `−α ∨ −β`, as in ✱22·84. -/
theorem q22_85 [Reducibility S] (α β : V a → QF V) : QThm S (clsEq (α ∩ β) (−(−α ∪ −β))) :=
  QThm.mp (QThm.mp (q22_84 α β) (qiffMp (q20_21 _ _))) (qiffMp (q22_831 _ _))      -- ✱22·84·831

/-- ✱22·86 `⊢ . −(−α ∩ −β) = α ∪ β` [✱4·57], with ✱22·35, ✱22·33 and ✱22·35 inside the negation (✱4·38, ✱4·11),
    ✱22·34, ✱10·11 and ✱20·43. -/
theorem q22_86 [Reducibility S] (α β : V a → QF V) : QThm S (clsEq (−(−α ∩ −β)) (α ∪ β)) :=
  have h1 : ∀ x, QThm S (iff (x ∈ −(−α ∩ −β)) (x ∈ α ∪ β)) := fun x =>
    calc (x ∈ −(−α ∩ −β))
        ≡ nmem x (−α ∩ −β) := q22_35 _ x
      _ ≡ .neg (QF.and (x ∈ −α) (x ∈ −β)) := qiffNeg (q22_33 _ _ x)
      _ ≡ .neg (QF.and (nmem x α) (nmem x β)) :=
          qiffNeg (QThm.mp (qandI (q22_35 α x) (q22_35 β x)) (QL.t4_38 _ _ _ _))
      _ ≡ QF.or (x ∈ α) (x ∈ β) := QL.t4_57 _ _                                    -- ✱4·57
      _ ≡ (x ∈ α ∪ β) := qiffSymm (q22_34 _ _ x)
  QThm.mp (q10_11 h1) (qiffMpr (q20_43 _ _))

/-- ✱22·87 `⊢ . −α ∩ −β = −(α ∪ β)` [✱22·86·831]. ✱22·86 is turned by ✱20·21 for ✱22·831. -/
theorem q22_87 [Reducibility S] (α β : V a → QF V) : QThm S (clsEq (−α ∩ −β) (−(α ∪ β))) :=
  QThm.mp (QThm.mp (q22_86 α β) (qiffMp (q20_21 _ _))) (qiffMp (q22_831 _ _))      -- ✱22·86·831

/-- ✱22·88 `⊢ . (x) . x ∈ (α ∪ −α)` [✱2·11], with ✱22·35 in the second disjunct (✱4·37 with ✱4·31) and ✱22·34,
    under (x) (✱10·11). -/
theorem q22_88 [Reducibility S] (α : V a → QF V) : QThm S (.all fun x => x ∈ (α ∪ −α)) :=
  q10_11 fun x =>
    QThm.mp (QL.t2_11 (x ∈ α))                                                    -- ✱2·11
      (qsyl (qiffMp (QThm.mp (qiffSymm (q22_35 α x)) (qorCongrRImp _ _ _))) (qiffMpr (q22_34 α (−α) x)))

/-- ✱22·89 `⊢ . (x) . x ∼∈ (α − α)` [✱3·24], with ✱22·33 and ✱22·35 in the second factor (✱4·36 with ✱4·3), the
    negation carried by ✱4·11, under (x) (✱10·11). -/
theorem q22_89 [Reducibility S] (α : V a → QF V) : QThm S (.all fun x => nmem x (α − α)) :=
  q10_11 fun x =>
    QThm.mp (QL.t3_24 (x ∈ α))                                                    -- ✱3·24
      (qiffMpr (qiffNeg (qiffTrans (q22_33 α (−α) x) (qandCongrR _ (q22_35 α x)))))

/-- ✱22·9 `⊢ . (α ∪ β) − β = α − β` [✱5·61], with ✱22·33, ✱22·34 and ✱22·35 (✱4·38 for the two factors), ✱10·11
    and ✱20·43. -/
theorem q22_9 [Reducibility S] (α β : V a → QF V) : QThm S (clsEq ((α ∪ β) − β) (α − β)) :=
  have h1 : ∀ x, QThm S (iff (x ∈ (α ∪ β) − β) (x ∈ α − β)) := fun x =>
    calc (x ∈ (α ∪ β) − β)
        ≡ QF.and (x ∈ α ∪ β) (x ∈ −β) := q22_33 _ _ x
      _ ≡ QF.and (.or (x ∈ α) (x ∈ β)) (nmem x β) :=
          QThm.mp (qandI (q22_34 α β x) (q22_35 β x)) (QL.t4_38 _ _ _ _)
      _ ≡ QF.and (x ∈ α) (nmem x β) := QL.t5_61 _ _                                -- ✱5·61
      _ ≡ QF.and (x ∈ α) (x ∈ −β) := qandCongrR _ (qiffSymm (q22_35 β x))
      _ ≡ (x ∈ α − β) := qiffSymm (q22_33 _ _ x)
  QThm.mp (q10_11 h1) (qiffMpr (q20_43 _ _))

/-- ✱22·91 `⊢ . α ∪ β = α ∪ (β − α)`. ✱5·63's second disjunct ∼p . q has its factors in the other order in PM's
    line (✱4·3 under ∨, ✱4·37 with ✱4·31); "[✱22·33·34·35]" rewrites the memberships (✱4·39, and ✱4·36 with ✱4·3
    for a second factor). -/
theorem q22_91 [Reducibility S] (α β : V a → QF V) : QThm S (clsEq (α ∪ β) (α ∪ (β − α))) :=
  have h1 : ∀ x, QThm S (iff (x ∈ α ∪ β) (x ∈ α ∪ (β − α))) := fun x =>
    calc (x ∈ α ∪ β)
        ≡ QF.or (x ∈ α) (x ∈ β) := q22_34 α β x
      _ ≡ QF.or (x ∈ α) (QF.and (nmem x α) (x ∈ β)) := QL.t5_63 _ _                 -- ✱5·63
      _ ≡ QF.or (x ∈ α) (QF.and (x ∈ β) (nmem x α)) := QThm.mp (QL.t4_3 _ _) (qorCongrRImp _ _ _)
      _ ≡ QF.or (x ∈ α) (x ∈ β − α) :=
          QThm.mp (qiffSymm (qiffTrans (q22_33 β (−α) x) (qandCongrR _ (q22_35 α x))))
            (qorCongrRImp _ _ _)                                                  -- [✱22·33·34·35]
      _ ≡ (x ∈ α ∪ (β − α)) := qiffSymm (q22_34 _ _ x)                             -- [✱22·34] (1)
  QThm.mp (q10_11 h1) (qiffMpr (q20_43 _ _))                                      -- (1).✱10·11.✱20·43

/-- ✱22·92 `⊢ : α ⊂ β . ⊃ . β = α ∪ (β − α)` [✱22·91·62]. ✱22·62's α ∪ β = β and ✱22·91 are joined by ✱20·23. -/
theorem q22_92 [Reducibility S] (α β : V a → QF V) : QThm S (imp (α ⊂ β) (clsEq β (α ∪ (β − α)))) :=
  qsyl (qiffMp (q22_62 α β))                                                      -- ✱22·62
    (qsyl (QThm.mp (q22_91 α β) (QThm.mp (QL.t3_2 _ _) (QL.t2_04 _ _ _)))          -- ✱22·91
      (q20_23 (α ∪ β) β (α ∪ (β − α))))

/-- ✱22·93 `⊢ . α − β = α − (α ∩ β)`. In the first line, ✱4·73 at x ∈ α has its product in the other order
    (✱4·3), and its two members are negated by ✱4·11 (PM's "Transp"). -/
theorem q22_93 [Reducibility S] (α β : V a → QF V) : QThm S (clsEq (α − β) (α − (α ∩ β))) :=
  have h1 : ∀ x, QThm S (iff (x ∈ α − β) (x ∈ α − (α ∩ β))) := fun x =>
    have l1 : QThm S (imp (x ∈ α) (iff (nmem x β) (nmem x (α ∩ β)))) :=
      calc (x ∈ α)
          ⊃ iff (x ∈ β) (QF.and (x ∈ β) (x ∈ α)) := QL.t4_73 _ _
        _ ⊃ iff (x ∈ β) (QF.and (x ∈ α) (x ∈ β)) := qiffMp (QThm.mp (QL.t4_3 _ _) (qiffCongrRImp _ _ _))
        _ ⊃ iff (nmem x β) (.neg (QF.and (x ∈ α) (x ∈ β))) := qiffMp (QL.t4_11 _ _)  -- ✱4·73 . Transp
        _ ⊃ iff (nmem x β) (nmem x (α ∩ β)) :=
            qiffMp (QThm.mp (qiffNeg (qiffSymm (q22_33 α β x))) (qiffCongrRImp _ _ _))  -- [✱22·33]
    calc (x ∈ α − β)
        ≡ QF.and (x ∈ α) (nmem x β) := qiffTrans (q22_33 α (−β) x) (qandCongrR _ (q22_35 β x))
      _ ≡ QF.and (x ∈ α) (nmem x (α ∩ β)) := QThm.mp l1 (qiffMp (QL.t5_32 _ _ _))  -- [✱5·32]
      _ ≡ (x ∈ α − (α ∩ β)) :=
          qiffSymm (qiffTrans (q22_33 α (−(α ∩ β)) x) (qandCongrR _ (q22_35 _ x)))  -- [✱22·35·33]
  QThm.mp (q10_11 h1) (qiffMpr (q20_43 _ _))                                      -- [✱10·11 . ✱20·43]

/-- ✱22·94 `⊢ : (α) . fα . ≡ . (α) . f(−α)`, α apparent (✱20·07), fα an extensional expression of α (`ClsExt`;
    p. 200). PM's ✱10·1 instantiates α at −α, whose defining function is not predicative: the class analogue
    (`qclsAllAt`; p. 206, ✱20·17), f(−α) being extensional when fα is (`clsExt_compl`). "[✱22·8 . ✱20·18]" is
    ✱20·18 for the expression (`qcls20_18`). For a generic f{α} (`cls α f`, p. 199) the premise is ✱20·11
    (`clsExt_cls`). -/
theorem q22_94 [Reducibility S] (F : (V a → QF V) → QF V) (hF : ClsExt S F) :
    QThm S (iff (clsAll F) (clsAll fun α => F (−α))) :=
  have h1 : QThm S (imp (clsAll F) (clsAll fun α => F (−α))) :=
    q10_11_21 fun φ =>
      qclsAllAt F (−(pf φ)) fun θ => qsyl (hF (pf θ) (−(pf φ))) (QL.t3_26 _ _)    -- ✱10·1 [✱10·11·21] (1)
  have h2 : QThm S (imp (clsAll fun α => F (−α)) (clsAll F)) :=
    q10_11_21 fun φ =>
      calc clsAll (fun α => F (−α))
          ⊃ F (−(−(pf φ))) :=
            qclsAllAt (fun α => F (−α)) (−(pf φ)) fun θ =>
              qsyl (clsExt_compl hF (pf θ) (−(pf φ))) (QL.t3_26 _ _)              -- ✱10·1
        _ ⊃ F (pf φ) := qiffMp (QThm.mp (q22_8 (pf φ)) (qcls20_18 F hF _ _))       -- [✱22·8 . ✱20·18] [✱10·11·21] (2)
  qiffI h1 h2                                                                     -- (1).(2)

/-- ✱22·95 `⊢ : (∃α) . fα . ≡ . (∃α) . f(−α)`: (1) is ✱22·94 for ∼fα (extensional by ✱4·11, `clsExt_neg`);
    "Transp" is ✱4·11, and ✱20·6 writes each (∃α) as ∼(α) . ∼. -/
theorem q22_95 [Reducibility S] (F : (V a → QF V) → QF V) (hF : ClsExt S F) :
    QThm S (iff (clsEx F) (clsEx fun α => F (−α))) :=
  have h1 := q22_94 (fun α => .neg (F α)) (clsExt_neg hF)                         -- ✱22·94 (1)
  calc clsEx F
      ≡ .neg (clsAll fun α => .neg (F α)) := q20_6 F                               -- ✱20·6
    _ ≡ .neg (clsAll fun α => .neg (F (−α))) := qiffNeg h1                         -- (1).Transp
    _ ≡ clsEx (fun α => F (−α)) := qiffSymm (q20_6 _)                              -- ✱20·6

/-! ✱22·94 for a generic f{α} (`cls α f`, p. 199), whose extensionality is ✱20·11. Not a PM proposition. -/
example [Reducibility S] (f : V (Ty.pred1 a) → QF V) :
    QThm S (iff (clsAll fun α => cls α f) (clsAll fun α => cls (−α) f)) :=
  q22_94 (fun α => cls α f) (clsExt_cls f)

end PM
