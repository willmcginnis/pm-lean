-- Lean decides whether each Mathlib counterpart of data/naming/counterparts.json checked "lean-mathlib"
-- states PM's formula (docs/NAMING.md, "Counterparts"), against Mathlib at the commit the records pin.
-- Written by scripts/export_names.py from that file and the statements exported now;
-- `python3 scripts/export_names.py --check` fails if it is out of date. A Lake project of its own, so the
-- repository's `lake build` needs no Mathlib: run by scripts/release_check.sh, or by hand from
-- Checks/MathlibCounterparts/ with `lake exe cache get` and then `lake env lean MathlibCounterparts.lean`.
--
-- As in Checks/Counterparts.lean, PM's formula is a schema over propositional variables, translated
-- connective for connective, with the sides of an equivalence swapped only where the record says so. Then
--   `example : <schema> := @<declaration> <variables>`
-- is checked by the kernel, and
--   `#counterpart <declaration> [<variables>] : <schema>`
-- checks that its first binders, one per listed variable, are propositional variables (`Prop`, or
-- `Sort u` only when marked `(specialized)`); that the variables listed are distinct; and that its type
-- so instantiated is the schema exactly, up to the names of bound variables and `A → False` read as `¬A`.
-- The recorded signature is the declaration's header in Mathlib's source, which
-- `scripts/export_names.py --verify-counterparts` compares with the pinned file. Last,
--   `#classical <declaration> <true|false>`
-- checks the record's `classical`: whether the axioms of the declaration's proof include
-- `Classical.choice`.
import Mathlib.Logic.Basic
import Mathlib.Tactic.Contrapose

section
open Lean Elab Command Term Meta

/-- `e` with each `A → False` written `¬A`. -/
partial def Counterparts.normNot (e : Expr) : Expr :=
  e.replace fun
    | .forallE _ a (.const ``False []) _ => some (mkApp (.const ``Not []) (Counterparts.normNot a))
    | _ => none

/-- See the head of this file. -/
elab "#counterpart " spec:("(specialized) ")? d:ident " [" vs:ident,* "]" " : " s:term : command => do
  -- the record's name is the full name, so it is not resolved against open namespaces (`not_imp_self`,
  -- not `Decidable.not_imp_self`)
  let c := d.getId
  let info ← getConstInfo c
  let d := mkIdent (rootNamespace ++ c)
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

/-- See the head of this file. -/
elab "#classical " d:ident b:ident : command => do
  let c := d.getId
  discard <| getConstInfo c
  let axs ← liftCoreM <| collectAxioms c
  let uses := axs.contains ``Classical.choice
  unless b.getId == (if uses then `true else `false) do
    throwError "{c}: its proof uses the axioms {axs.toList}, so classical is {uses}, not {b.getId}"

end

variable (p q r : Prop)

-- ✱2·03 PM.star2_03_transp: Mathlib.Tactic.Contrapose.contrapose₃, Mathlib/Tactic/Contrapose.lean:38
example : ((p → ¬q) → (q → ¬p)) := @Mathlib.Tactic.Contrapose.contrapose₃ q p
#counterpart Mathlib.Tactic.Contrapose.contrapose₃ [q, p] : ((p → ¬q) → (q → ¬p))
#classical Mathlib.Tactic.Contrapose.contrapose₃ false

-- ✱2·1 PM.star2_1: em', Mathlib/Logic/Basic.lean:211
example : (¬p ∨ p) := @em' p
#counterpart em' [p] : (¬p ∨ p)
#classical em' true

-- ✱2·14 PM.star2_14: of_not_not, Mathlib/Logic/Basic.lean:260
example : (¬¬p → p) := @of_not_not p
#counterpart of_not_not [p] : (¬¬p → p)
#classical of_not_not true

-- ✱2·15 PM.star2_15_transp: Not.imp_symm, Mathlib/Logic/Basic.lean:268
example : ((¬p → q) → (¬q → p)) := @Not.imp_symm p q
#counterpart Not.imp_symm [p, q] : ((¬p → q) → (¬q → p))
#classical Not.imp_symm true

-- ✱2·17 PM.star2_17_transp: Function.mtr, Mathlib/Logic/Basic.lean:366
example : ((¬q → ¬p) → (p → q)) := @Function.mtr q p
#counterpart Function.mtr [q, p] : ((¬q → ¬p) → (p → q))
#classical Function.mtr true

-- ✱4·1 PM.star4_1_transp: not_imp_not, Mathlib/Logic/Basic.lean:359
example : ((¬q → ¬p) ↔ (p → q)) := @not_imp_not q p
#counterpart not_imp_not [q, p] : ((¬q → ¬p) ↔ (p → q))
#classical not_imp_not true

-- ✱4·11 PM.star4_11_transp: not_iff_not, Mathlib/Logic/Basic.lean:393
example : ((¬p ↔ ¬q) ↔ (p ↔ q)) := @not_iff_not p q
#counterpart not_iff_not [p, q] : ((¬p ↔ ¬q) ↔ (p ↔ q))
#classical not_iff_not true

-- ✱4·12 PM.star4_12: iff_not_comm, Mathlib/Logic/Basic.lean:399
example : ((p ↔ ¬q) ↔ (q ↔ ¬p)) := @iff_not_comm p q
#counterpart iff_not_comm [p, q] : ((p ↔ ¬q) ↔ (q ↔ ¬p))
#classical iff_not_comm true

-- ✱4·5 PM.star4_5: and_iff_not_or_not, Mathlib/Logic/Basic.lean:419
example : ((p ∧ q) ↔ ¬(¬p ∨ ¬q)) := @and_iff_not_or_not p q
#counterpart and_iff_not_or_not [p, q] : ((p ∧ q) ↔ ¬(¬p ∨ ¬q))
#classical and_iff_not_or_not true

-- ✱4·57 PM.star4_57: or_iff_not_and_not, Mathlib/Logic/Basic.lean:416
example : ((p ∨ q) ↔ ¬(¬p ∧ ¬q)) := @or_iff_not_and_not p q
#counterpart or_iff_not_and_not [p, q] : ((p ∨ q) ↔ ¬(¬p ∧ ¬q))
#classical or_iff_not_and_not true

-- ✱4·6 PM.star4_6: imp_iff_not_or, Mathlib/Logic/Basic.lean:354
example : ((p → q) ↔ (¬p ∨ q)) := @imp_iff_not_or p q
#counterpart imp_iff_not_or [p, q] : ((p → q) ↔ (¬p ∨ q))
#classical imp_iff_not_or true

-- ✱4·78 PM.star4_78: imp_or, Mathlib/Logic/Basic.lean:383
example : ((p → (q ∨ r)) ↔ ((p → q) ∨ (p → r))) := @imp_or p q r
#counterpart imp_or [p, q, r] : ((p → (q ∨ r)) ↔ ((p → q) ∨ (p → r)))
#classical imp_or true

-- ✱4·81 PM.star4_81: not_imp_self, Mathlib/Logic/Basic.lean:272
example : ((¬p → p) ↔ p) := @not_imp_self p
#counterpart not_imp_self [p] : ((¬p → p) ↔ p)
#classical not_imp_self true

-- ✱5·23 PM.star5_23: iff_iff_and_or_not_and_not, Mathlib/Logic/Basic.lean:401
example : ((p ↔ q) ↔ ((p ∧ q) ∨ (¬p ∧ ¬q))) := @iff_iff_and_or_not_and_not p q
#counterpart iff_iff_and_or_not_and_not [p, q] : ((p ↔ q) ↔ ((p ∧ q) ∨ (¬p ∧ ¬q)))
#classical iff_iff_and_or_not_and_not true

#eval IO.println "Mathlib counterparts: 14 checked by Lean against Mathlib 0df444a"
