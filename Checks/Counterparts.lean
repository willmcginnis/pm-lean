-- Lean decides whether each Lean core counterpart of data/naming/counterparts.json states PM's formula
-- (docs/NAMING.md, "Counterparts"). Written by scripts/export_names.py from that file and the statements
-- exported now; `python3 scripts/export_names.py --check` fails if it is out of date. Run from the
-- repository root with `lake env lean Checks/Counterparts.lean`; it needs Lean's core only.
--
-- For each record, PM's formula is a schema over propositional variables, translated connective for
-- connective (∼ `Not`, ∨ `Or`, ⊃ `→`, . `And`, ≡ `Iff`), with the sides of an equivalence swapped only
-- where the record says so. Then
--   `example : <schema> := @<declaration> <variables>`
-- is checked by the kernel, and
--   `#counterpart <declaration> [<variables>] "<signature>" : <schema>`
-- checks that the declaration's type prints as the recorded signature; that its first binders, one per
-- listed variable, are propositional variables (`Prop`, or `Sort u` only when marked `(specialized)`);
-- that the variables listed are distinct; and that its type so instantiated is the schema exactly, up to
-- the names of bound variables and `A → False` read as `¬A`: no unfolding, so a declaration that only
-- implies the schema, or states it up to definitional unfolding, fails.
import Lean

section
open Lean Elab Command Term Meta

/-- `e` with each `A → False` written `¬A`. -/
partial def Counterparts.normNot (e : Expr) : Expr :=
  e.replace fun
    | .forallE _ a (.const ``False []) _ => some (mkApp (.const ``Not []) (Counterparts.normNot a))
    | _ => none

/-- See the head of this file. -/
elab "#counterpart " spec:("(specialized) ")? d:ident " [" vs:ident,* "] " sig:str " : " s:term : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverload d
  let info ← getConstInfo c
  -- printed outside the section's variables, so that no bound name is renamed to avoid them
  let pp ← liftTermElabM do return toString (← ppExpr info.type)
  let ws (x : String) := " ".intercalate (x.splitOn " " |>.filter (· ≠ ""))
  unless ws pp == ws sig.getString do
    throwError "{c}: its type is{indentD pp}\nnot the recorded signature{indentD sig.getString}"
  runTermElabM fun _ => do
    let vs := vs.getElems
    unless (vs.map (·.getId)).toList.eraseDups.length == vs.size do
      throwError "{c}: two of its variables are instantiated with the same variable"
    let general ← forallBoundedTelescope info.type vs.size fun xs _ => do
      unless xs.size == vs.size do throwError "{c}: fewer than {vs.size} binders"
      xs.mapM fun x => do
        match ← inferType x with
        | .sort .zero => pure false
        | .sort _ => pure true
        | t => throwError "{c}: its binder {x} : {t} is not a propositional variable"
    if general.any id != spec.isSome then
      throwError "{c}: {if spec.isSome then "marked (specialized) with no Sort parameter"
        else "a Sort parameter specialized to Prop, but the record does not say so"}"
    let schema ← elabType s
    let e ← elabTerm (← `(@$d $vs*)) none
    synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars (← inferType e)
    unless Counterparts.normNot ty == Counterparts.normNot schema do
      throwError "{c}: instantiated, it states{indentExpr ty}\nnot PM's formula{indentExpr schema}"

end

variable (p q r : Prop)

-- ✱1·3 PM.star1_3_add: Or.inr, src/Init/Prelude.lean:624
example : (q → (p ∨ q)) := @Or.inr p q
#counterpart Or.inr [p, q] "∀ {a b : Prop}, b → a ∨ b" : (q → (p ∨ q))

-- ✱1·4 PM.star1_4_perm: Or.symm, src/Init/Core.lean:1065
example : ((p ∨ q) → (q ∨ p)) := @Or.symm p q
#counterpart Or.symm [p, q] "∀ {a b : Prop}, a ∨ b → b ∨ a" : ((p ∨ q) → (q ∨ p))

-- ✱1·6 PM.star1_6_sum: Or.imp_right, src/Init/SimpLemmas.lean:322
example : ((q → r) → ((p ∨ q) → (p ∨ r))) := @Or.imp_right q r p
#counterpart Or.imp_right [q, r, p] "∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c" : ((q → r) → ((p ∨ q) → (p ∨ r)))

-- ✱2·02 PM.star2_02_simp: imp_intro, src/Init/Core.lean:1734
example : (q → (p → q)) := @imp_intro q p
#counterpart imp_intro [q, p] "∀ {α β : Prop}, α → β → α" : (q → (p → q))

-- ✱2·04 PM.star2_04_comm: flip, src/Init/Core.lean:65
example : ((p → (q → r)) → (q → (p → r))) := @flip p q r
#counterpart (specialized) flip [p, q, r] "{α : Sort u} → {β : Sort v} → {φ : Sort w} → (α → β → φ) → β → α → φ" : ((p → (q → r)) → (q → (p → r)))

-- ✱2·05 PM.star2_05_syll: Function.comp, src/Init/Prelude.lean:141
example : ((q → r) → ((p → q) → (p → r))) := @Function.comp p q r
#counterpart (specialized) Function.comp [p, q, r] "{α : Sort u} → {β : Sort v} → {δ : Sort w} → (β → δ) → (α → β) → α → δ" : ((q → r) → ((p → q) → (p → r)))

-- ✱2·08 PM.star2_08_id: id, src/Init/Prelude.lean:131
example : (p → p) := @id p
#counterpart (specialized) id [p] "{α : Sort u} → α → α" : (p → p)

-- ✱2·11 PM.star2_11: Classical.em, src/Init/Classical.lean:36
example : (p ∨ ¬p) := @Classical.em p
#counterpart Classical.em [p] "∀ (p : Prop), p ∨ ¬p" : (p ∨ ¬p)

-- ✱2·12 PM.star2_12: not_not_intro, src/Init/Core.lean:838
example : (p → ¬¬p) := @not_not_intro p
#counterpart not_not_intro [p] "∀ {p : Prop}, p → ¬¬p" : (p → ¬¬p)

-- ✱2·16 PM.star2_16_transp: mt, src/Init/Core.lean:833
example : ((p → q) → (¬q → ¬p)) := @mt p q
#counterpart mt [p, q] "∀ {a b : Prop}, (a → b) → ¬b → ¬a" : ((p → q) → (¬q → ¬p))

-- ✱2·2 PM.star2_2: Or.inl, src/Init/Prelude.lean:622
example : (p → (p ∨ q)) := @Or.inl p q
#counterpart Or.inl [p, q] "∀ {a b : Prop}, a → a ∨ b" : (p → (p ∨ q))

-- ✱2·21 PM.star2_21: Not.elim, src/Init/Core.lean:1659
example : (¬p → (p → q)) := @Not.elim p q
#counterpart (specialized) Not.elim [p, q] "{a : Prop} → {α : Sort u_1} → ¬a → a → α" : (¬p → (p → q))

-- ✱2·24 PM.star2_24: absurd, src/Init/Prelude.lean:339
example : (p → (¬p → q)) := @absurd p q
#counterpart (specialized) absurd [p, q] "{a : Prop} → {b : Sort v} → a → ¬a → b" : (p → (¬p → q))

-- ✱2·38 PM.star2_38: Or.imp_left, src/Init/SimpLemmas.lean:321
example : ((q → r) → ((q ∨ p) → (r ∨ p))) := @Or.imp_left q r p
#counterpart Or.imp_left [q, r, p] "∀ {a b c : Prop}, (a → b) → a ∨ c → b ∨ c" : ((q → r) → ((q ∨ p) → (r ∨ p)))

-- ✱2·53 PM.star2_53: Or.resolve_left, src/Init/Prelude.lean:643
example : ((p ∨ q) → (¬p → q)) := @Or.resolve_left p q
#counterpart Or.resolve_left [p, q] "∀ {a b : Prop}, a ∨ b → ¬a → b" : ((p ∨ q) → (¬p → q))

-- ✱2·61 PM.star2_61: Classical.byCases, src/Init/Classical.lean:134
example : ((p → q) → ((¬p → q) → q)) := @Classical.byCases p q
#counterpart Classical.byCases [p, q] "∀ {p q : Prop}, (p → q) → (¬p → q) → q" : ((p → q) → ((¬p → q) → q))

-- ✱3·14 PM.star3_14: not_and_of_not_or_not, src/Init/PropLemmas.lean:151
example : ((¬p ∨ ¬q) → ¬(p ∧ q)) := @not_and_of_not_or_not p q
#counterpart not_and_of_not_or_not [p, q] "∀ {a b : Prop}, ¬a ∨ ¬b → ¬(a ∧ b)" : ((¬p ∨ ¬q) → ¬(p ∧ q))

-- ✱3·2 PM.star3_2: And.intro, src/Init/Prelude.lean:604
example : (p → (q → (p ∧ q))) := @And.intro p q
#counterpart And.intro [p, q] "∀ {a b : Prop}, a → b → a ∧ b" : (p → (q → (p ∧ q)))

-- ✱3·22 PM.star3_22: And.symm, src/Init/Core.lean:1061
example : ((p ∧ q) → (q ∧ p)) := @And.symm p q
#counterpart And.symm [p, q] "∀ {a b : Prop}, a ∧ b → b ∧ a" : ((p ∧ q) → (q ∧ p))

-- ✱3·24 PM.star3_24: and_not_self, src/Init/SimpLemmas.lean:259
example : ¬(p ∧ ¬p) := @and_not_self p
#counterpart and_not_self [p] "∀ {a : Prop}, ¬(a ∧ ¬a)" : ¬(p ∧ ¬p)

-- ✱3·26 PM.star3_26_simp: And.left, src/Init/Prelude.lean:609
example : ((p ∧ q) → p) := @And.left p q
#counterpart And.left [p, q] "∀ {a b : Prop}, a ∧ b → a" : ((p ∧ q) → p)

-- ✱3·27 PM.star3_27_simp: And.right, src/Init/Prelude.lean:612
example : ((p ∧ q) → q) := @And.right p q
#counterpart And.right [p, q] "∀ {a b : Prop}, a ∧ b → b" : ((p ∧ q) → q)

-- ✱3·31 PM.star3_31_imp: And.elim, src/Init/Core.lean:1662
example : ((p → (q → r)) → ((p ∧ q) → r)) := @And.elim p q r
#counterpart (specialized) And.elim [p, q, r] "{a b : Prop} → {α : Sort u_1} → (a → b → α) → a ∧ b → α" : ((p → (q → r)) → ((p ∧ q) → r))

-- ✱3·45 PM.star3_45_fact: And.imp_left, src/Init/PropLemmas.lean:43
example : ((p → q) → ((p ∧ r) → (q ∧ r))) := @And.imp_left p q r
#counterpart And.imp_left [p, q, r] "∀ {a b c : Prop}, (a → b) → a ∧ c → b ∧ c" : ((p → q) → ((p ∧ r) → (q ∧ r)))

-- ✱4·13 PM.star4_13: Classical.not_not, src/Init/Classical.lean:144
example : (¬¬p ↔ p) := @Classical.not_not p
#counterpart Classical.not_not [p] "∀ {a : Prop}, ¬¬a ↔ a" : (¬¬p ↔ p)

-- ✱4·2 PM.star4_2: Iff.rfl, src/Init/Core.lean:1036
example : (p ↔ p) := @Iff.rfl p
#counterpart Iff.rfl [p] "∀ {a : Prop}, a ↔ a" : (p ↔ p)

-- ✱4·21 PM.star4_21: iff_comm, src/Init/Core.lean:1059
example : ((p ↔ q) ↔ (q ↔ p)) := @iff_comm p q
#counterpart iff_comm [p, q] "∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)" : ((p ↔ q) ↔ (q ↔ p))

-- ✱4·24 PM.star4_24: and_self_iff, src/Init/PropLemmas.lean:38
example : ((p ∧ p) ↔ p) := @and_self_iff p
#counterpart and_self_iff [p] "∀ {a : Prop}, a ∧ a ↔ a" : ((p ∧ p) ↔ p)

-- ✱4·25 PM.star4_25: or_self_iff, src/Init/PropLemmas.lean:83
example : ((p ∨ p) ↔ p) := @or_self_iff p
#counterpart or_self_iff [p] "∀ {a : Prop}, a ∨ a ↔ a" : ((p ∨ p) ↔ p)

-- ✱4·3 PM.star4_3: and_comm, src/Init/Core.lean:1063
example : ((p ∧ q) ↔ (q ∧ p)) := @and_comm p q
#counterpart and_comm [p, q] "∀ {a b : Prop}, a ∧ b ↔ b ∧ a" : ((p ∧ q) ↔ (q ∧ p))

-- ✱4·31 PM.star4_31: or_comm, src/Init/Core.lean:1067
example : ((p ∨ q) ↔ (q ∨ p)) := @or_comm p q
#counterpart or_comm [p, q] "∀ {a b : Prop}, a ∨ b ↔ b ∨ a" : ((p ∨ q) ↔ (q ∨ p))

-- ✱4·32 PM.star4_32: and_assoc, src/Init/SimpLemmas.lean:296
example : (((p ∧ q) ∧ r) ↔ (p ∧ (q ∧ r))) := @and_assoc p q r
#counterpart and_assoc [p, q, r] "∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c" : (((p ∧ q) ∧ r) ↔ (p ∧ (q ∧ r)))

-- ✱4·33 PM.star4_33: or_assoc, src/Init/SimpLemmas.lean:324
example : (((p ∨ q) ∨ r) ↔ (p ∨ (q ∨ r))) := @or_assoc p q r
#counterpart or_assoc [p, q, r] "∀ {a b c : Prop}, (a ∨ b) ∨ c ↔ a ∨ b ∨ c" : (((p ∨ q) ∨ r) ↔ (p ∨ (q ∨ r)))

-- ✱4·36 PM.star4_36: and_congr_left', src/Init/PropLemmas.lean:48
example : ((p ↔ q) → ((p ∧ r) ↔ (q ∧ r))) := @and_congr_left' p q r
#counterpart and_congr_left' [p, q, r] "∀ {a b c : Prop}, (a ↔ b) → (a ∧ c ↔ b ∧ c)" : ((p ↔ q) → ((p ∧ r) ↔ (q ∧ r)))

-- ✱4·37 PM.star4_37: or_congr_left, src/Init/PropLemmas.lean:87
example : ((p ↔ q) → ((p ∨ r) ↔ (q ∨ r))) := @or_congr_left p q r
#counterpart or_congr_left [p, q, r] "∀ {a b c : Prop}, (a ↔ b) → (a ∨ c ↔ b ∨ c)" : ((p ↔ q) → ((p ∨ r) ↔ (q ∨ r)))

-- ✱4·4 PM.star4_4: and_or_left, src/Init/PropLemmas.lean:120
example : ((p ∧ (q ∨ r)) ↔ ((p ∧ q) ∨ (p ∧ r))) := @and_or_left p q r
#counterpart and_or_left [p, q, r] "∀ {a b c : Prop}, a ∧ (b ∨ c) ↔ a ∧ b ∨ a ∧ c" : ((p ∧ (q ∨ r)) ↔ ((p ∧ q) ∨ (p ∧ r)))

-- ✱4·41 PM.star4_41: or_and_left, src/Init/PropLemmas.lean:128
example : ((p ∨ (q ∧ r)) ↔ ((p ∨ q) ∧ (p ∨ r))) := @or_and_left p q r
#counterpart or_and_left [p, q, r] "∀ {a b c : Prop}, a ∨ b ∧ c ↔ (a ∨ b) ∧ (a ∨ c)" : ((p ∨ (q ∧ r)) ↔ ((p ∨ q) ∧ (p ∨ r)))

-- ✱4·51 PM.star4_51: Classical.not_and_iff_not_or_not, src/Init/Classical.lean:186
example : (¬(p ∧ q) ↔ (¬p ∨ ¬q)) := @Classical.not_and_iff_not_or_not p q
#counterpart Classical.not_and_iff_not_or_not [p, q] "∀ {a b : Prop}, ¬(a ∧ b) ↔ ¬a ∨ ¬b" : (¬(p ∧ q) ↔ (¬p ∨ ¬q))

-- ✱4·56 PM.star4_56: not_or, src/Init/PropLemmas.lean:149
example : (¬(p ∨ q) ↔ (¬p ∧ ¬q)) := @not_or p q
#counterpart not_or [p, q] "∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q" : (¬(p ∨ q) ↔ (¬p ∧ ¬q))

-- ✱4·61 PM.star4_61: Classical.not_imp_iff_and_not, src/Init/Classical.lean:184
example : (¬(p → q) ↔ (p ∧ ¬q)) := @Classical.not_imp_iff_and_not p q
#counterpart Classical.not_imp_iff_and_not [p, q] "∀ {a b : Prop}, ¬(a → b) ↔ a ∧ ¬b" : (¬(p → q) ↔ (p ∧ ¬q))

-- ✱4·64 PM.star4_64: Classical.or_iff_not_imp_left, src/Init/Classical.lean:181
example : ((p ∨ q) ↔ (¬p → q)) := @Classical.or_iff_not_imp_left p q
#counterpart Classical.or_iff_not_imp_left [p, q] "∀ {a b : Prop}, a ∨ b ↔ ¬a → b" : ((p ∨ q) ↔ (¬p → q))

-- ✱4·71 PM.star4_71: iff_self_and, src/Init/SimpLemmas.lean:315
example : ((p ↔ (p ∧ q)) ↔ (p → q)) := @iff_self_and p q
#counterpart iff_self_and [p, q] "∀ {p q : Prop}, (p ↔ p ∧ q) ↔ p → q" : ((p ↔ (p ∧ q)) ↔ (p → q))

-- ✱4·72 PM.star4_72: iff_or_self, src/Init/SimpLemmas.lean:340
example : ((q ↔ (p ∨ q)) ↔ (p → q)) := @iff_or_self p q
#counterpart iff_or_self [p, q] "∀ {a b : Prop}, (b ↔ a ∨ b) ↔ a → b" : ((q ↔ (p ∨ q)) ↔ (p → q))

-- ✱4·73 PM.star4_73: and_iff_left, src/Init/PropLemmas.lean:72
example : (q → ((p ∧ q) ↔ p)) := @and_iff_left q p
#counterpart and_iff_left [q, p] "∀ {b a : Prop}, b → (a ∧ b ↔ a)" : (q → ((p ∧ q) ↔ p))

-- ✱4·74 PM.star4_74: or_iff_right, src/Init/PropLemmas.lean:101
example : (¬p → ((p ∨ q) ↔ q)) := @or_iff_right p q
#counterpart or_iff_right [p, q] "∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)" : (¬p → ((p ∨ q) ↔ q))

-- ✱4·76 PM.star4_76: imp_and, src/Init/PropLemmas.lean:114
example : ((p → (q ∧ r)) ↔ ((p → q) ∧ (p → r))) := @imp_and q r p
#counterpart (specialized) imp_and [q, r, p] "∀ {b c : Prop} {α : Sort u_1}, (∀ (a : α), b ∧ c) ↔ (∀ (a : α), b) ∧ ∀ (a : α), c" : ((p → (q ∧ r)) ↔ ((p → q) ∧ (p → r)))

-- ✱4·77 PM.star4_77: or_imp, src/Init/PropLemmas.lean:135
example : (((q ∨ r) → p) ↔ ((q → p) ∧ (r → p))) := @or_imp q r p
#counterpart or_imp [q, r, p] "∀ {a b c : Prop}, a ∨ b → c ↔ (a → c) ∧ (b → c)" : (((q ∨ r) → p) ↔ ((q → p) ∧ (r → p)))

-- ✱4·8 PM.star4_8: imp_not_self, src/Init/Core.lean:1732
example : ((p → ¬p) ↔ ¬p) := @imp_not_self p
#counterpart imp_not_self [p] "∀ {a : Prop}, a → ¬a ↔ ¬a" : ((p → ¬p) ↔ ¬p)

-- ✱4·83 PM.star4_83: Classical.imp_and_neg_imp_iff, src/Init/Classical.lean:197
example : (((p → q) ∧ (¬p → q)) ↔ q) := @Classical.imp_and_neg_imp_iff p q
#counterpart Classical.imp_and_neg_imp_iff [p, q] "∀ (p : Prop) {q : Prop}, (p → q) ∧ (¬p → q) ↔ q" : (((p → q) ∧ (¬p → q)) ↔ q)

-- ✱4·84 PM.star4_84: imp_congr_left, src/Init/Core.lean:1755
example : ((p ↔ q) → ((p → r) ↔ (q → r))) := @imp_congr_left p q r
#counterpart imp_congr_left [p, q, r] "∀ {a b c : Prop}, (a ↔ b) → (a → c ↔ b → c)" : ((p ↔ q) → ((p → r) ↔ (q → r)))

-- ✱5·19 PM.star5_19: iff_not_self, src/Init/Core.lean:1723
example : ¬(p ↔ ¬p) := @iff_not_self p
#counterpart iff_not_self [p] "∀ {a : Prop}, ¬(a ↔ ¬a)" : ¬(p ↔ ¬p)

-- ✱5·32 PM.star5_32: and_congr_right_iff, src/Init/SimpLemmas.lean:304
example : (((p ∧ q) ↔ (p ∧ r)) ↔ (p → (q ↔ r))) := @and_congr_right_iff p q r
#counterpart and_congr_right_iff [p, q, r] "∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)" : (((p ∧ q) ↔ (p ∧ r)) ↔ (p → (q ↔ r)))

-- ✱5·5 PM.star5_5: imp_iff_right, src/Init/Core.lean:1738
example : (p → ((p → q) ↔ q)) := @imp_iff_right q p
#counterpart imp_iff_right [q, p] "∀ {b a : Prop}, a → (a → b ↔ b)" : (p → ((p → q) ↔ q))

-- ✱5·501 PM.star5_501: iff_true_left, src/Init/Core.lean:1682
example : (p → ((p ↔ q) ↔ q)) := @iff_true_left p q
#counterpart iff_true_left [p, q] "∀ {a b : Prop}, a → ((a ↔ b) ↔ b)" : (p → ((p ↔ q) ↔ q))

#eval IO.println "counterparts: 54 checked by Lean"
