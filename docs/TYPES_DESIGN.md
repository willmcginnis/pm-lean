# PM 1910 ramified types with the axiom of reducibility: design and acceptance tests

Will's decision (2026-10-11): the main road is the
1910 ramified theory of types with the axiom of reducibility (✱12·1, ✱12·11), "if it actually is
consistent and usable". The 1925 second edition is a later, separate pass.

Page numbers are those of the **1910 print** (Vol. I). They were read from the Distributed Proofreaders
transcription (Gutenberg #78050, `pg78050-images.html`), whose page markers follow the scan images, with
the formulas taken from its LaTeX source. The scan images themselves were not consulted (see test F3).

Code: `PM/Quant.lean` (types, syntax, rules, model, soundness), `PM/Star12.lean`, `PM/Star13.lean`,
`PM/Star14.lean` (partial), `PM/Star20.lean` (partial), `PM/Orders.lean` (order checker and golden
tests), `PM/Trap.lean` (degenerate variable families), `RedCheck.lean` (which theorems use
reducibility).

## 1. Decisions

Each decision is final for this pass. Each gives the page it rests on and the alternative rejected.
Where PM's text allows two readings, the decision also appears as an open question in §5.

### 1. Syntax: one many-sorted formula type

`QF (V : Ty → Type)`, with function variables bound in the PHOAS style already used for ✱9–✱11.

```
Ty  := ind | fn1 (a : Ty) (k : Nat) | fn2 (a b : Ty) (k : Nat)
QF  := atom P xs | app1 f x | app2 f x y | neg p | or p q | all {τ} (φ : V τ → QF V)
```

- **Unary and binary function types only.** PM states reducibility for one and two variables and says
  of more: "these assumptions are not indispensable for our purpose, and are therefore not made in this
  work" (p. 174). PM's later parts work with classes (one argument) and relations (two).
- **No type of propositions.** From ✱12 on, propositions "will no longer" occur as variables "except in
  a few isolated cases of which no subsequent use is made" (p. 172).
- **Rejected:** n-ary `fn (args : List Ty) (m : Nat)`. It needs a nested inductive with nested recursion
  in the model and gains nothing up to ✱12·11. It can be added later without restating anything, as
  `fn1`/`fn2` were added now.

### 2. Orders, and how types carry them

- `Ty.ord`: individuals 0; a function one above the highest order of its arguments, plus its excess `k`.
  Intro p. 56: "If the highest order of variable occurring in a function, whether as argument or as
  apparent variable, is a function of the nth order, then the function in which it occurs is of the
  n + 1th order". ✱12's summary says the same (p. 175, (2)).
- **The excess encoding.** `fn1 a k` has order `a.ord + 1 + k`. A type whose order is not above its
  arguments' orders cannot be written. (The idea of storing an excess is also in Pommeret's
  formalization. We took the idea only, no code.)
- **Orders are disjoint, not cumulative.** `fn1 a 0` and `fn1 a 1` are different types. This follows
  p. 168: "two different types are mutually exclusive".
- **Rejected:**
  - an explicit order `m` with a well-formedness side condition, which would admit junk types such as
    a first-order function of a second-order function;
  - Church's cumulative r-types.

### 3. (a) "Predicative": two styles (revised 2026-10-11, Will's decision on Q1)

PM's text has two definitions.

- **Lowest order.** Intro p. 56: "We will define a function of one variable as *predicative* when it
  is of the next order above that of its argument, i.e. of the lowest order compatible with its having
  that argument". p. 174 agrees in substance: "for higher types of arguments, predicative functions take
  the place that first-order functions take in respect of individuals".
- **Matrix.** ✱12 p. 172: "A function is said to be *predicative* when it is a matrix", and "'Matrix'
  or 'predicative function' is a primitive idea". A matrix is "any function, of however many
  variables, which does not involve any apparent variables" (p. 169). p. 171: "A second-order matrix of
  one variable will be called a predicative second-order function of one variable".

**They come apart.** Take (x) . φ!x as a function of φ!ẑ (p. 171, (1)). It is of order 2, the lowest
order possible for an argument of order 1, so it is predicative by p. 56. It is not a matrix, so it is
not predicative by p. 172. Likewise (y) . ψ(x, y), a first-order function of x (p. 54): predicative by
p. 56, not by p. 172. Holmes calls the matrix definition "completely destructive" (Notes p. 4).

**Decision (Will, 2026-10-11): both, as a deliberate, documented style choice.** Each reading is its own
module, and the proof system takes the style as a parameter (`Sys.style`, the same mechanism as the
rule capabilities of decision 13):
- `PM/Pred/Matrix.lean`, `Style.matrix`: comprehension at a predicative type (`fn1 a 0`, `fn2 a b 0`)
  accepts a formula only if it is a matrix (`IsMatrix`) AND passes the order check. The matrix test is
  conjoined with the order check, not put in its place (after an external review): φ!x with φ of order 2 is a
  matrix but not of order 1.
- `PM/Pred/LowestOrder.lean`, `Style.lowestOrder`: comprehension at `fn1 a k` accepts every formula
  that passes the order check at the order of `fn1 a k`.
- At non-predicative types (k > 0) the two styles accept the same formulas.
- `PM/Pred/Styles.lean` puts them side by side (`PredReading`, `Style.of`).

**The matrix style is primary** (Will: "the more elegant one"), in the docs and the entry files
(`Style.primary`); the lowest-order style is the alternative (`Style.alternative`). Reasons:
- it is ✱12's own definition, where the formal system starts, and it is "a primitive idea" there
  (p. 172), so the formal reading should use it; p. 56 is in the informal Introduction;
- it is a syntactic test on the formula, with no arithmetic of orders beyond the order check that both
  styles share;
- PM's proofs never need comprehension, so the stricter style loses nothing that PM uses: every
  function PM forms comes from ✱12·1.

**What is the same in both.** The types: `Ty.pred1 a := fn1 a 0` and `Ty.pred2 a b := fn2 a b 0` are the
predicative functions of either reading, the lowest order compatible with the arguments, and PM's
φ!x̂ is a variable of type `pred1 a` in both. A matrix condition restricts which formulas
comprehension turns into such a value; it is not a range of values itself. (As an external review noted, this is not
to say that values of matrices cannot form a quantified range; the types `pred1 a` are such a range.)
✱12·1 and ✱12·11 (decision 7) have no side condition, so they are the same in both.

**What the choice changes.**
- `matrix_adm1_le`, `QThm.matrix_to_lowestOrder`: the matrix style admits no more than the
  lowest-order style, so every theorem of a system in the matrix style is a theorem of the same system
  in the lowest-order style.
- Golden tests (PM/Pred/Styles.lean): p. 171 (1) and p. 54 are admitted by the lowest-order style and
  refused by the matrix style at a predicative type; p. 171 (1) at a non-predicative type, and the
  matrix φ!x ⊃ ψ!x, are admitted by both; (φ) . φ!x as a predicative function of x is refused by both.
  `p171_lowestOrder_predicative` (lowest-order style only, comprehension without ✱12·1) and
  `p171_reducibility` (every style, by ✱12·1) are the same statement in the two styles.
- Without reducibility, whether the matrix style is strictly weaker (`p171` not derivable at all in
  the matrix-style predicative fragment) is not proved: it needs a model that sees orders (test F4).
- "Both must pass": every PM theorem (✱1–✱20 so far) is stated for an arbitrary system, so for both
  styles; `StyleCheck.lean` instantiates each of the 351 PM propositions under each style and named
  system and reports the result (§3, test S1). Consistency is proved for both styles in both models
  (`consistent_of_style`, `consistent_collapse_of_style`).

**Arguments of a predicative function need not be predicative.** p. 174: "Let φx̂ be a function, of
any order, of an argument x, which may itself be either an individual or a function of any order". So
in `pred1 a`, `a` is any type, including a non-predicative `fn1 b (k+1)`. p. 172 says that in practice
all *variables* will be individuals or matrices. Our types allow that practice without forcing it.

**Rejected:** KLN's restriction of contexts to predicative types. In that system reducibility "cannot
even" be stated (KLN 2002, Rem. 42).

**Several arguments.** p. 56 states the lowest-order rule for several arguments explicitly, right
before the disputed clause: "If a function has several arguments, and the highest order of function
occurring among the arguments is the nth, we call the function predicative if it is of the n + 1th
order, i.e. again, if it is of the lowest order compatible with its having the arguments it has." So
`pred2 a b` (the maximum argument order plus one) is directly supported by p. 56 (after an external review;
the sentence this note quoted before, "If the highest order of variable occurring in a function …", is
a paragraph earlier on the same page and says the same for orders in general). ✱12·11's "a predicative
function of those variables, i.e. to a matrix" (p. 174) agrees. The clause that follows, "A function of
several arguments is predicative if there is one of its arguments such that, when the other arguments
have values assigned to them, we obtain a predicative function of the one undetermined argument", is
discussed under Q4 (§5).

### 4. Real and apparent function variables

**Real function variables are Lean functions.** PM writes "φx" for "a function (φ or f) whose order,
relatively to its argument, is not given", and "such a function will not be used as an apparent variable"
(p. 173). In
Lean it is a formula with a hole, `φ : V a → QF V`, exactly as for every real function variable of
✱9–✱11. Substituting a formula for it is Lean instantiation, which is how PM uses real variables
(✱9·15 p. 138, ✱10·122 p. 146: if there is a proposition φa, "there is a function φx̂").

**Apparent function variables are object variables.** They have a type `fn1 a k` or `fn2 a b k` and
are applied by `app1` or `app2` (f!x, f!(x, y)). PM uses only predicative ones ("this restriction
involves no loss of generality", p. 173). Non-predicative types exist and can be quantified over,
since p. 173 allows it once "we suppose its order previously fixed", and our types fix the order.

**Rejected:** real function variables as object variables of a function type with a stated order (the
prototype's `red1 (φ : V (fn1 a m))`). Every use of ✱13·101 at a formula (✱13·16 at ẑ = x, ✱14 at
x = b, …) would then need three extra steps:
- comprehension to get a variable;
- an order proof;
- an elimination.

PM does none of this; it substitutes. `q12_1_var` keeps that shape as a corollary, and `q12_1_of_var`
shows the two shapes agree (decision 7).

### 5. The order check `Lvl`

`Lvl p n` holds when p may be a value of a function of order n:
- every apparent variable in p has order below n;
- every function variable applied in p has order at most n;
- n ≥ 1, since individuals have order 0.

A *real* function variable counts with its own order m, not m + 1. This follows p. 55: "if
f!(φ!ẑ, x) is φ!x, the assignment of a value to φ gives us a predicative function of x". So
(∃g) : g!x ≡ₓ φ!x, with φ real and of order 1, is ordinary predicative comprehension.

The order of the *function* x̂ ↦ ψx is `fnOrder a ψ = max (a.ord + 1) (order of ψx)` (PM/Orders.lean).
It is decided at the one-element variable family `U` (`lvl_iff_order`, with a `Decidable` instance).

**Rejected:** counting a real variable φ as an argument that raises the order of φ!x to 2. That is the
order of φ!x as a function of φ *and* x (pp. 54, 170). It would forbid g := φ above.

### 6. (b) Comprehension

The decision is to **keep** comprehension, as the constructors `compr1` and `compr2`:

```
compr1 (ψ : V a → QF V) (h : ∀ x, Lvl (ψ x) (fn1 a k).ord) :
  ⊢ (∃f : fn1 a k) : ψx . ≡ₓ . f x
```

**Warrant.** ✱9·15 (p. 138) and ✱10·122 (p. 146): "If, for some a, there is a proposition φa, then
there is a function φx̂". Applied to an apparent variable over functions of order m, with ✱10·24 (or
✱10·1), this gives an existential whose witness is that function. PM licenses functions of a given
order to be formed from formulas whose variables are of lower order: pp. 54–56, 169–171, and p. 172,
"non-predicative functions always result from such as are predicative by means of generalization".

**The side condition** is exactly `Lvl ψ m` with m the order of the type of f (Intro p. 56, read as in
decision 5).

**Honest limits.**
- PM never states comprehension as a proposition, and its proofs never need it, because ✱12·1 gives
  a predicative equivalent of *every* formula. For example, ✱14·17 gets (∃χ) : χ!x ≡ₓ x = b from
  ✱12·1 (p. 188).
- So comprehension is our reading. It is used by exactly one theorem, `q12_1_of_var` (RedCheck.lean).

**If it were dropped:** every ✱13–✱20 theorem here would still be provable, since all go through
✱12·1, as PM's do. Two things would be lost:
1. the check `q12_1_of_var`: "✱12·1 for a function variable of order m" plus comprehension at order
   m gives ✱12·1 for every formula of that order, without `red1`. This shows that, assuming
   comprehension, taking φ as a formula (decision 4) adds nothing beyond "✱12·1 at every order", for
   formulas that are uniformly order-bounded (one order m bounds ψx for every x). Exotic HOAS bodies
   whose order is not uniformly bounded are not covered (after an external review);
2. a predicative fragment (the rules without `red1`/`red2`) that can say anything about function
   variables. That fragment matters for the 1925 pass.

### 7. ✱12·1 and ✱12·11

Primitive constructors `red1` and `red2`, with PM's shape (p. 174):

```
✱12·1   ⊢ : (∃f) : φx . ≡ₓ . f!x            red1 (φ : V a → QF V)       : (∃f : pred1 a)   : φx ≡ₓ f!x
✱12·11  ⊢ : (∃f) : φ(x, y) . ≡ₓ,ᵧ . f!(x, y)  red2 (φ : V a → V b → QF V) : (∃f : pred2 a b) : φ(x, y) ≡ₓ,ᵧ f!(x, y)
```

- φ is a real variable of any order (decision 4). The order is that of whatever formula is put for
  it, and there is no side condition.
- f is apparent and of the predicative type. "Every propositional function is equivalent, for all its
  values, to some predicative function of the same argument or arguments" (p. 174).
- "This assumption … is to be made whatever may be the type of their arguments" (p. 174): `a` and `b`
  are Lean parameters (decision 8).
- PM/Star12.lean restates both with PM's macros ≡ₓ (✱10·03) and ≡ₓ,ᵧ (✱11·06), as `q12_1` and
  `q12_11`.
- **✱12 has no other numbered propositions and no definitions.** Its primitive idea "matrix or
  predicative function" (p. 172) is the type `pred1 a` (decision 3). The rest of ✱12 is prose about
  types and orders, covered by decisions 2, 3 and 5 and by PM/Orders.lean.
- **Rejected:**
  - f of the *same* order as φ (Pommeret's constructor). That does not reduce the order, which is the
    point of the axiom (pp. 173–174).
  - ✱12·1 as an informal meta-axiom (KLN).
  - Landini's reading, in which all bindable variables are predicative and ✱12·1 is impredicative
    comprehension (IEP). Our predicative types with `red1` contain that system. Our non-predicative
    types are an addition that PM's p. 173 allows.

### 8. (c) Typical ambiguity

A Lean theorem is a schema: its types are implicit parameters (`{a b : Ty}`, `{τ : Ty}`), and each use
is elaborated at specific types.
- p. 172: "if we prove any proposition on the assumption that one of our variables is an individual,
  and another is a function of order n, the proof will still hold if, in place of an individual, we
  take a function of order m, and in place of our function of order n we take a function of order
  n + m, with corresponding changes for any other variables that may be involved".
- p. 169: "only the relative types of variables are relevant".
- ✱20 (p. 198): the definition of "Cls", "like many future definitions, is ambiguous as to type".

Lean's parameters are more general than PM's uniform shift: any assignment of types that makes the
formula well-typed. Every instance is still a statement at fixed types, which is what PM asserts.

A mismatch of types inside one proof is a Lean type error. That is the role of ✱10·221's identification
of variables (✱13·3's note, p. 180).

**Rejected:**
- object-level type variables with order inequalities (Holmes 2003's ML-style polymorphism);
- Lean universe polymorphism, which applies only to a shallow embedding.

### 9. Definitions and incomplete symbols

✱13·01–✱13·03, ✱14·01–✱14·02 and ✱20·01–✱20·02 are `@[reducible]` macros, like ✱1·01 and ✱10·01. So
"⊢ ✱13·1 [✱4·2 . (✱13·01)]" is literally ✱4·2.

**Descriptions and classes are incomplete symbols** (pp. 66–67, 181, 196–197), so they have no term
constructor. Their macros take the condition and the context:
- `desc φ ψ` is [(ιx)(φx)] . ψ(ιx)(φx) (✱14·01, p. 184);
- `cls ψ f` is f{ẑ(ψz)} (✱20·01, pp. 197, 199).

**The scope is the placement of the context, so it is always explicit.**
- `desc φ (fun z => ∼χ z)` and `∼(desc φ χ)` are the two scopes of ∼χ(ιx)(φx).
- PM's convention that an unmarked description has the smallest scope (p. 182) is not mechanized:
  the author picks the scope when writing the term.
- Identity of classes eliminates the first class first: "ẑ(ψz) is to have a larger scope than ẑ(χz)
  because it occurs first" (p. 201, `clsEq`).

**Rejected:** ι and ẑ as term constructors. That would make them complete symbols, contrary to PM.

### 10. Quantifier base

✱10's alternative method, unchanged (pp. 143–144; docs/STAR9_DESIGN.md).

### 11. Soundness and consistency

**Structures.** A `QModel` (PM/Quant.lean) gives each type a set of values, application `ap1`/`ap2`
of function values, abstraction `lam1`/`lam2` with `ap (lam g) x = g x`, the letters, and a Boolean
quantifier for each type with its specification. Orders are not seen.
- `qsound` covers every constructor, including `compr1`, `compr2`, `red1` and `red2`, for every system
  `S` (every combination of rules and every style). The witness is the value `lam (x ↦ ⟦φx⟧)`. The
  proof uses no axioms.

**The collapse model** (PM/Models/Collapse.lean), the general one: `Ty.den D`, a function of any order
denotes a Boolean function of its arguments. `QModel.collapse` builds a structure from any domain,
letters and quantifier oracles; `QModel.classical` supplies classical oracles (`classicalAll`) at every
type, for any domain. With reducibility, PM 1910 is no stronger than the simple theory of types
(Holmes 2023), so forgetting orders gives a model. `classicalAll`, its specification and
`QModel.classical` use `propext`, `Classical.choice` and `Quot.sound`, necessarily.

**The finite coded model** (PM/Models/Finite.lean; Will's decision on Q5, 2026-10-11). Values are
coded by shapes (empty, unit, Booleans, pairs); the values of a function type are the truth tables of
the Boolean functions of its argument values (`Sh.pow`, with `Sh.ap`, `Sh.lam`, `Sh.ap_lam`), and every
quantifier is computed by enumeration (`Sh.all`, `Sh.all_spec`). `finModel D R` is the structure with
individuals of shape D; `twoModel` has two individuals and `emptyModel` none. About 150 lines, as
estimated. Everything in it uses no axioms.

**Consistency** is stated at a structure's own variables (`consistent S`, at `twoModel.den`), and for
the theorems that hold at every V (`consistent_all S`), which is how every PM theorem here is stated.
Both are proved for every system `S`, so for every combination of rules and styles, and both use no
axioms. So do the five counter-model theorems, which evaluate in `twoModel` or `emptyModel` by
computation (the ✱14 one includes a quantifier over the four predicative functions of individuals).

The model is a consistency proof relative to Lean's type theory with no axioms. It forgets orders like
the collapse model, so it cannot show that comprehension without ✱12·1 is weaker (F4).

### 12. Degenerate variable families (Trap 1)

`QThm` is defined for every V. At a family whose function types are not full ranges, ✱10·11 says too
much, and ✱12·1 then proves everything (PM/Trap.lean):
- `trap_empty`: (ι)/1 is empty;
- `trap_unit`: every type has exactly one variable.

`trap_unit` shows that requiring non-empty function types (a natural repair) would
not help. `trap_unit_compr` (from an external review) does the same at `U` with comprehension in place of
✱12·1, so the limitation also affects the comprehension-only fragment, not only reducibility.

**Decision.** The rule is not repaired.
- Every PM theorem is a Lean theorem *for every* V, so it holds at every structure's variables.
- Consistency is stated at a structure's variables, or for ∀-V theorems.
- `QThm` at an arbitrary V is never presented as PM's system.

**Rejected:** an eigenvariable form of ✱10·11 over explicit contexts. It would change the statement or
proof of every ✱10–✱11 theorem.

### 13. Rules as opt-in capabilities (revised 2026-10-11, Will's decision on Q2)

The proof system is `QThm S` for a system `S : Sys` (PM/Quant.lean): two flags, `compr` and `red`, and a
style of predicativity (decision 3). The constructors `compr1`/`compr2` need a proof of `S.compr = true`,
and `red1`/`red2` a proof of `S.red = true`. Each rule is its own module with its PM warrant in the
header, and a class that supplies the proof:
- `PM/Rules/Reducibility.lean`: `class Reducibility S` (✱12·1, ✱12·11, p. 174);
- `PM/Rules/Comprehension.lean`: `class Comprehension S` (✱9·15, ✱10·122; our reading, decision 6).

A theorem that uses a rule takes the class in its signature (`theorem q13_101 [Reducibility S] …`). For
an arbitrary `S` there is no other way to get `S.red = true`, so Lean enforces the dependency, and the
signature shows it. Reaching a rule shows that a proof uses it, not that the rule is logically necessary for the theorem
(after an external review); the absence of a cycle in the constant graph only makes the reachability exact. A
theorem without a class holds in every system, including later ones (the 1925
pass will add an `Extensionality` capability). `QThm.mono` lifts a derivation to any system with more
rules and a more permissive style. `PM/Systems.lean` names four systems: `Sys.full` (both rules),
`Sys.reducibility` (PM's own route), `Sys.predicative` (comprehension only) and `Sys.base` (neither).

Every ✱1–✱11 proof is unchanged; their statements gained the parameter `S`. The ✱12–✱20 theorems that
use ✱12·1 gained `[Reducibility S]`, found by compiling (Lean refuses the proof without it); the list
is the same 29 that the old after-the-fact scan found.

`RedCheck.lean` is kept as an independent cross-check. It follows the constants used by each
declaration, transitively, as `#print axioms` does, and reports which reach the class field
`Reducibility.red` or `Comprehension.compr`, then compares that with whether the class occurs in the
declaration's type. Result: 29 PM propositions use reducibility, 1 uses comprehension, and 0 disagree
with their signatures. (The constructors themselves are not the test, because every proof by induction
on `QThm`, such as `qsound`, reaches all constructors through the recursor's type.)

**Rejected:**
- the earlier after-the-fact scan alone, with `QThm`'s type unchanged: the dependency was invisible in
  the statements;
- a second inductive per system: it would duplicate every rule-lemma of ✱10–✱11 (`qsyl`, `q10_11_27`, …).
  With one parameterised inductive, those lemmas are stated once for every `S`.

## 2. What was built

| File | Lines | Contents |
|---|---|---|
| `PM/Quant.lean` | 341 | `Ty` with `fn1`/`fn2` and `Ty.ord`, `pred1`/`pred2`; `QF.app1`/`app2`; `Lvl`; `QThm` with `compr1`, `compr2`, `red1`, `red2`; collapse model, `qsound`, `classicalAll`, `twoModel`, `emptyModel`, `consistent`, `consistent_all`, the old counter-models |
| `PM/Star12.lean` | 74 | ✱12·1, ✱12·11 with PM's macros; variable-shape corollaries; `q12_1_of_var` |
| `PM/Star13.lean` | 221 | ✱13·01–✱13·03 (macros); all 24 numbered propositions ✱13·1–✱13·22 except ✱13·3 |
| `PM/Star14.lean` | 140 | ✱14·01, ✱14·02 (macros); ✱14·1, ✱14·101, ✱14·11, ✱14·12, ✱14·121, ✱14·2, ✱14·201, ✱14·21; a scope counter-model |
| `PM/Star20.lean` | 109 | ✱20·01, ✱20·02 (macros), class identity; ✱20·1, ✱20·13, ✱20·14, ✱20·15, ✱20·3; typical-ambiguity checks |
| `PM/Orders.lean` | 171 | decidable order checker; 32 order tests |
| `PM/Trap.lean` | 61 | `trap_empty`, `trap_unit` |
| `RedCheck.lean` | 55 | reducibility and comprehension dependencies |

✱13·3 (p. 180) is not formalized. It concerns significance, and its proof turns on ✱10·221
(identifying the types of two variables), which, like ✱10·221, is built into the Lean typing.

Proofs follow PM's Dem. lines or bracketed hints, as in ✱11. Steps PM leaves tacit beyond those listed
in PM/Star11.lean's header are named in each docstring. The commonest are:
- ✱10·1 used at two arguments and joined by Comp;
- factors commuted by ✱3·22 or ✱4·3 where PM's ✱13·13 or ✱10·35 has them in the other order;
- ✱13·16 to turn y = x into x = y;
- orientation of ≡ₓ: PM writes ψx ≡ₓ φ!x in ✱20·13 and ✱20·3, but φ!x ≡ₓ ψx in ✱20·01, so ✱10·32 is
  used between them.

✱20·13's line (2) uses the first line of ✱13·195's proof (✱3·2, ✱13·15, ✱10·24) instead of ✱13·195
itself. There is no per-proposition ledger for ✱12–✱20 yet.

## 3. Acceptance tests

| Test | Result | Lean names / evidence |
|---|---|---|
| **C1** soundness covers every constructor, axiom-free | **pass** | `qsound`: "does not depend on any axioms" |
| **C2** consistency at a model's own V | **pass** | `consistent S` (at `twoModel.den`, the finite coded model), `consistent_all S` (∀ V), for every system `S`. No axioms (decision 11) |
| **C3** degenerate V documented or removed | **pass (documented, not removed)** | `trap_empty`, `trap_unit` in PM/Trap.lean; header of `consistent` and README |
| **C4** old counter-models still refute | **pass** | `not_qthm_phiy_imp_all` (φy ⊃ (x).φx), `not_qthm_ex_imp_all` ((∃x).φx ⊃ (x).φx), `not_qthm_all_imp_ex_empty` ((x).φx ⊃ (∃x).φx, empty D); also `not_qthm_converse_11_26` and the new `not_qthm_neg_desc_imp_exists1` |
| **U1** ✱2–✱5, ✱9–✱11 unchanged | **pass** | PM/QuantLift.lean, PM/Star10.lean, PM/Star11.lean: no line changed; all compile against the new `QF`/`QThm` |
| **U2** ✱10 used at a function sort | **pass** | `q13_101` uses ✱10·1, ✱10·27, ✱10·23 at `pred1 a`; `q20_14` uses ✱10·23 at `pred1 a`; `q12_1_of_var` at `fn1 a k` and `pred1 a` |
| **U3** ✱13·101, ✱13·12 along PM's lines, citing ✱12·1 | **pass** | `q13_101` (lines (1), (2) of p. 177; (1) is `q12_1`), `q13_12`; also ✱13·1–✱13·22 except ✱13·3 |
| **U4** ✱14·21 with explicit scope | **pass** | `q14_21`, `q14_21_neg` ([(ιx)(φx)] . ∼χ(ιx)(φx) ⊃ E!), `not_qthm_neg_desc_imp_exists1` (∼{[(ιx)(φx)] . χ(ιx)(φx)} ⊃ E! is not a theorem) |
| **U5** one ✱20 class theorem | **pass** | `q20_15` (ψx ≡ₓ χx . ≡ . ẑ(ψz) = ẑ(χz), p. 201), via `q20_13` (cites ✱12·1), `q20_14`; also `q20_3` (x ∈ ẑ(ψz) . ≡ . ψx, cites ✱12·1) |
| **U6** cost | **reported** | see below |
| **F1** decidable order checker | **pass** | `QF.order`, `lvl_iff_order`, `instance : Decidable (Lvl p n)` at `U`; `fnOrder` |
| **F2** golden order tests | **pass** | PM/Orders.lean: 6 type orders; 12 tests from Intro pp. 54–56; 12 from ✱12 pp. 170–171 (incl. the p. 56 / p. 172 divergence); 2 on comprehension (accepts (x) . φ!x as a function of φ; refuses (φ) . φ!x as a predicative function of x) |
| **F3** ✱12·1 shape vs the print; choices listed | **pass, against the transcription** | `red1`/`red2` and `q12_1`/`q12_11` match p. 174 term for term ((∃f) first, φx before f!x, ≡ₓ = ✱10·03, ≡ₓ,ᵧ = ✱11·06). Checked against the DP transcription's LaTeX, not against the scan image. Choices: §1 above |
| **F4** impredicative comprehension not derivable without ✱12·1 | **skipped** | Needs a non-collapsed model (Holmes's ι⁴ or "simple recursion" model). Only the syntactic half is done: `compr1` cannot be applied to (φ) . φ!x at a predicative type (PM/Orders.lean, last example). Non-derivability is **not** proved |
| **F5** one theorem at two sorts | **pass** | PM/Star20.lean examples: `q13_15` at ι, (ι)/1, ((ι)/1)/2; `q13_101` at ι and (ι)/1. In use: `q20_13` and `q20_14` use `q13_15`, `q13_16`, `q13_195` at `pred1 a`, hence ✱12·1 at `pred1 (pred1 a)` |
| **S1** every PM theorem under both styles of "predicative" (Will, Q1) | **pass** | `StyleCheck.lean`: each of the 351 PM propositions instantiates in `Sys.full` of the matrix style and of the lowest-order style (351/351 each); 0 without a parameter `S`; per system: reducibility 350, predicative 322, base 321 in both styles (the 29 that take `Reducibility` and the 1 that takes `Comprehension` drop out as expected). Consistency: `consistent_of_style`, `consistent_collapse_of_style` |

### U6: cost numbers

- **Lines per proposition** (Lean lines after the `theorem` line, comments excluded; a measure, not
  PM's line count):

  | File | Lines per proposition |
  |---|---|
  | ✱10 | 3.7 |
  | ✱11 | 4.9 |
  | ✱13 | 3.8 (24 propositions) |
  | ✱14 | 3.4 (9) |
  | ✱20 | 6.4 (5) |

  ✱13·101 is 13 lines, against PM's 5 Dem. lines. ✱20·13 is 15.
- **Direct citations of ✱12·1 / ✱12·11 in PM's ✱13–✱20** (1910 text; citations inside formulas and
  proofs, not prose): 10 of 145 numbered items (propositions and definitions).
  - ✱13: 1 of 28 (✱13·101);
  - ✱14: 2 of 51 (✱14·17, ✱14·171);
  - ✱20: 7 of 66 (✱20·112, ·12, ·13, ·151, ·19, ·3, ·703).
- **Here:**
  - **Direct citations:** 3 propositions cite ✱12·1 directly (`q13_101`, `q20_13`, `q20_3`).
  - **Transitive dependence (RedCheck):** 25 of the 38 formalized ✱13/✱14/✱20 propositions (counting the
    variant `q14_21_neg`) depend on ✱12·1:
    - ✱13: 19 of 24;
    - ✱14: `q14_12`, `q14_2`;
    - ✱20: `q20_13`, `q20_14`, `q20_15`, `q20_3`.
  - **Not dependent:**
    - ✱13·1, ✱13·15, ✱13·17, ✱13·18, ✱13·19;
    - ✱14·1, ✱14·101, ✱14·11, ✱14·121, ✱14·201, ✱14·21 (and `q14_21_neg`);
    - ✱20·1.
  - **Comprehension** is used only by `q12_1_of_var`.
- **What reducibility costs in practice.**
  - In ✱13 it is paid once, inside ✱13·101: line (1) is 3 Lean lines (✱12·1, then ✱10·1 at x and y
    joined by Comp under ✱10·11·28). The elimination at the end is ✱10·23 plus Comm, 2 lines.
  - Everything later reaches ✱12·1 only through ✱13·101, at no further cost.
  - Each direct use in ✱20 costs 1–2 lines, mostly turning ψ ≡ₓ φ! into φ! ≡ₓ ψ (✱10·32 under ∃).
- **Build:** clean `lake build`, 20 jobs, 16.6 s.

## 4. Axioms

`AxiomCheck.lean`: 587 names; 585 report no axioms. The other 2 are `classicalAll_spec` and
`QModel.classical` (below). Every PM theorem (✱2–✱5 and the ✱9–✱20 `q…` theorems), `complete`,
`qsound`, `consistent`, `consistent_all`, the five counter-models, the finite model, `lvl_iff_order`,
`trap_empty` and `trap_unit` are axiom-free.

`AllAxioms.lean`: all 1273 declarations under `PM` and all 30 private declarations of the PM modules
(`_private.PM.…`, skipped before an external review; none uses an axiom). Exactly 23 use an axiom:

| Declarations | Axioms | Why |
|---|---|---|
| `classicalAll`, `classicalAll_spec`, `QModel.classical` | propext, Classical.choice, Quot.sound | the general collapse model, kept: classical quantifiers over arbitrary function spaces (`Classical.propDecidable`) |
| `PM.sound`, `PM.not_thm_of_countermodel`, `PM.gutenberg_1_4_refuted` | propext, Quot.sound | propositional metatheorems (unchanged from before) |
| `injEq` lemmas of `F`, `QF`, `Ty`, `Sh`, `Style`, `Sys`, `QModel` (15), `instReprF`, `instReprF.repr` | propext | compiler-generated |

No `sorry`, `native_decide`, `axiom`, `unsafe`, `implemented_by` or `extern` anywhere (checked by
search).

## 5. Open questions for Will

1. **"Predicative": p. 56 or p. 172?** DECIDED by Will (2026-10-11): both, as a deliberate,
   documented style choice, the matrix reading (p. 172) primary as the more elegant one. Done: decision
   3; `PM/Pred/Matrix.lean` (matrix test conjoined with the order check, after an external review),
   `PM/Pred/LowestOrder.lean`, `PM/Pred/Styles.lean`; every PM theorem checked under both
   (`StyleCheck.lean`); consistency for both.
2. **Keep comprehension?** DECIDED by Will (2026-10-11): keep it, "mark it for what it's for", as its
   own module imported where needed. Done: `PM/Rules/Comprehension.lean`, class `Comprehension S`
   (decisions 6 and 13).
3. **Real variables count with their own order** (decision 5, p. 55). The alternative reading of p. 54
   counts them as arguments, giving φ!x order 2. That would make even (∃g) : g!x ≡ₓ φ!x need ✱12·1.
4. **Several-argument predicativity.** p. 56's second clause ("if there is one of its arguments such
   that …") is weaker than the lowest-order reading used for `pred2`. Is it worth a separate type?
5. **Axiom-free consistency.** DECIDED by Will (2026-10-11): yes, "its own little module". Done:
   PM/Models/Finite.lean; `consistent`, `consistent_all` and the counter-models use no axioms; the
   classical collapse model is kept as the general one (decision 11).

## 6. Not done

- ✱13·3; ✱14 beyond the eight propositions listed; ✱20 beyond the five listed.
- F4 (non-derivability of impredicative comprehension without ✱12·1): skipped. It needs a non-collapsed
  model.
- No per-proposition ledger (`data/…_ledger.json`) for ✱12–✱20.
- The scan images were not viewed (F3).
- The n-ary function types and the 1925 route.
