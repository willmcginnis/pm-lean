# Scope of the ✱9–✱21 semantics

What the soundness and consistency theorems show, and what they do not. These limits bound what
"formalizing PM" means here; the README keeps a summary of them. The design behind them is in
[TYPES_DESIGN.md](TYPES_DESIGN.md) and [STAR9_DESIGN.md](STAR9_DESIGN.md).

## What the models show, and what they do not

- `qsound` holds in every structure (`QModel`), for every system.
- Two kinds of structure forget orders: the collapse model (`PM/Models/Collapse.lean`, every type of functions
  a full function space, classical quantifiers) and the finite coded model (`PM/Models/Finite.lean`, truth
  tables, quantifiers by enumeration). With reducibility the collapse model is a model of the 1910 system.
- `consistent` is proved in the finite model. So it shows that `QThm`, with ✱12·1, ✱12·11 and comprehension,
  does not prove everything, relative to Lean's type theory with no axioms.
- Neither model can see orders: a wrong order condition would still be "sound". So the order discipline is
  checked only syntactically (`PM/Orders.lean`), and nothing here proves that comprehension without ✱12·1 is
  weaker (test F4 in [TYPES_DESIGN.md](TYPES_DESIGN.md)).
- The model is extensional, so it validates sentences that are true only extensionally. This does not affect
  soundness, but a counter-model can never refute a sentence that is false only intensionally.

## Consistency is stated at a model's variables

- `QThm` is defined for every family `V`. At a family whose types are not full ranges, ✱10·11 says too much,
  and ✱12·1 then proves everything.
- This happens when a function type is empty, and also when every type has exactly one variable
  (`PM/Trap.lean`), so requiring non-empty types would not help.
- At the one-element family comprehension alone does the same as ✱12·1 (`trap_unit_compr`), so the limitation
  also affects the predicative fragment.
- Every PM theorem here is a Lean theorem for every `V`, so it holds at every model's variables. `consistent`
  names the variables of a model (`twoModel.den`), and `consistent_all` says that the theorems holding at
  every `V` do not include `p`.
- `QThm` at an arbitrary `V` is not PM's system.

## Exotic terms; no adequacy theorem

- `QF V` uses functions `V τ → QF V` for φx̂ (higher-order abstract syntax). Lean allows such functions to
  inspect their argument, so `QF V` also contains "exotic" terms that correspond to no finite formula of PM.
- `qsound` holds for all of them in every model, so nothing false becomes provable.
- But there is no adequacy theorem: no translation shows that `QF`/`QThm` correspond exactly to PM's finite
  formulas and derivations. The theorems are stated for arbitrary φ, so they also hold for these terms.

## The order checker and p. 56

- `PM/Orders.lean` decides the order condition for formulas over the one-element variable family `U` only.
  There is no theorem transferring the result to an arbitrary `V`.
- p. 56's second clause agrees with the lowest-order rule within this encoding (`second_clause_iff_lowestOrder`;
  `ClauseSearch.lean` finds no disagreement on 2,784,780 cases). This does not independently show that the
  encoding captures PM's "assignment of values", nor extend to arbitrary variable families.
- `p171_lowestOrder_predicative` derives p. 171 (1)'s existential in the lowest-order predicative system.
  Whether it is derivable in the matrix-style predicative fragment is not proved either way (test F4).

## Not formalized

- *Not as printed:* ✱14·3, proved as a schema: its propositions as apparent variables need a type of
  propositions ([TYPES_DESIGN.md](TYPES_DESIGN.md) §5, Q8; open: maintainer decision).
- Apparent classes of classes ((κ) . fκ) and identity of classes of classes, which later chapters need
  ([CLASSES_OF_CLASSES.md](CLASSES_OF_CLASSES.md)). Classes of classes themselves are built (✱20·03–✱20·081,
  ✱21·03–✱21·083), with the extensionality of a class's defining expression as an explicit premise of the
  analogue of ✱20·3, where PM asserts it in general (p. 200). The premise is proved for every expression
  PM's notation forms (`clsExpr_ext`; [PM_CLAIMS.md](PM_CLAIMS.md), D1).
- ✱22 onward; functions of three or more arguments; the 1925 second edition's system.
