# PM 1910 ramified types with the axiom of reducibility: design and acceptance tests

Will's decision (2026-10-11): the main road is the 1910 ramified theory of types with the axiom of
reducibility (✱12·1, ✱12·11), "if it actually is consistent and usable". The 1925 second edition is
a later, separate pass.

Page numbers are those of the **1910 print** (Vol. I). They were read from the Distributed Proofreaders
transcription (Gutenberg #78050, `pg78050-images.html`), whose page markers follow the scan images, with
the formulas taken from its LaTeX source. The scan images themselves were not consulted (see test F3).

Code: `PM/Quant.lean` (types, syntax, styles and systems, rules, structures, soundness), `PM/Rules/`
(the opt-in rules), `PM/Pred/` (the styles of predicativity, currying and p. 56's second clause),
`PM/Systems.lean`, `PM/StylesEquiv.lean`, `PM/Models/` (the collapse model and the finite coded model),
`PM/Star12.lean`, `PM/Star13.lean`, `PM/Star14.lean` (partial), `PM/Star20.lean` (partial),
`PM/Orders.lean` (order checker and golden tests), `PM/Trap.lean` (degenerate variable families),
`PM/Vol1.lean` (entry file); checks `RedCheck.lean`, `StyleCheck.lean`, `ClauseSearch.lean`,
`AxiomCheck.lean`, `AllAxioms.lean`.

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
  These test the side condition of comprehension, a syntactic fact (`p171_compr_lowestOrder`,
  `p171_compr_matrix`), not derivability. `p171_lowestOrder_predicative` derives p. 171 (1)'s
  existential by the direct comprehension application, which only the lowest-order styles accept;
  `p171_reducibility` derives it in every style by ✱12·1. Whether it is derivable at all in the
  matrix-style predicative fragment, by another route, is not proved either way (test F4).
- **With reducibility the styles derive exactly the same theorems: `styles_equiv`** (PM/StylesEquiv.lean;
  Will's item (i)). For either setting of comprehension `c` and any two styles,
  `QThm ⟨c, true, Style.of P R⟩ p ↔ QThm ⟨c, true, Style.of P' R'⟩ p`. The proof is an induction over
  derivations (`restyle`): at a predicative type the conclusion of comprehension is literally ✱12·1
  (✱12·11); at `fn1 a (k+1)`, ✱12·1 gives a predicative g with ψx ≡ₓ g!x, every style admits g!x there
  (`admitsPredApp_of`), comprehension in the target style gives f with g!x ≡ₓ f x, and ✱10·301
  (✱11·371) joins them. It uses no axioms, and it USES ✱12·1 / ✱12·11: it takes `[Reducibility S']`,
  and RedCheck.lean reports that `restyle`, `styles_equiv` and `styles_equiv_full` reach
  `Reducibility.red` (and `restyle` cites `QThm.red1` directly). This replaces the earlier unproved
  remark "same theorems either way" (after an external review) with a proof, for the system as built.
- Without reducibility, whether the matrix style is strictly weaker (`p171` not derivable at all in
  the matrix-style predicative fragment) is not proved: it needs a model that sees orders (test F4).
  Skipped: neither the collapse model nor the finite model sees orders, and an order-aware model of the
  whole hierarchy (restricted ranges at every type, closed under comprehension) is not cheap. Only the
  syntactic half is proved: the matrix style admits less (`QThm.matrix_to_lowestOrder`, golden tests).
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
have values assigned to them, we obtain a predicative function of the one undetermined argument",
agrees with that rule within this encoding (both partial applications evaluated at `()` in `U`, with
the same body order; Will's item (iii), searched): see Q4 (§5) and PM/Pred/Curry.lean.

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

### 5. The order check: two readings of a real function variable (revised 2026-10-11, Will's decision on Q3)

**Decision (Will, 2026-10-11 ~19:00): both readings, as styles; both must pass.** Each is its own
module, and it combines with either reading of "predicative" (decision 3), giving four styles
`Style.of P R` (PM/Pred/Styles.lean):
- `PM/Pred/RealOwnOrder.lean`, `Lvl`: a real function variable counts with its own order (p. 55). The
  default.
- `PM/Pred/RealAsArgument.lean`, `LvlArg`: it counts as an argument and raises the order (p. 54, p. 170:
  "φ!x" is "a function of two variables, namely φ!ẑ and x"). The only difference from `Lvl` is a strict
  inequality for applied function variables, which matters only for the free ones (parameters): an
  apparent variable's quantifier already requires its order to be below n, and the function's own
  argument is always of lower order than the function.
- Golden tests (PM/Pred/Styles.lean): φ!x with φ real of order 1 is admitted at `pred1 ind` in the
  p. 55 styles and refused in the p. 54 styles; at `fn1 ind 1` both admit it; (x) . φ!x as a function
  of φ passes both order checks. These test the side condition of comprehension
  (`realPhi_compr_ownOrder`, `realPhi_compr_asArgument`), a syntactic fact. They say nothing about the
  derivability of (∃g) : φ!x ≡ₓ g!x: that is a theorem of every system, in every style, without
  comprehension or ✱12·1, since φ itself is a witness (`realPhi_every_system`). What differs between
  the styles is whether the direct comprehension application is accepted.
- `styles_equiv` covers all four styles: with reducibility they derive the same theorems;
  `styles_equiv_real` states the p. 55 / p. 54 case for `Sys.full`. `StyleCheck.lean`: all 351 PM
  propositions pass in `Sys.full` of each of the four styles.

The p. 55 reading is the default because it is what p. 55 says outright about the case at issue, and
because it is partial application (below): the p. 54 order is that of the same body as a function of φ
and x together.

`Lvl p n` (p. 55 reading) holds when p may be a value of a function of order n:
- every apparent variable in p has order below n;
- every function variable applied in p has order at most n;
- n ≥ 1, since individuals have order 0.

A *real* function variable counts with its own order m, not m + 1. This follows p. 55: "if
f!(φ!ẑ, x) is φ!x, the assignment of a value to φ gives us a predicative function of x". So
comprehension at `pred1 ind` accepts φ!x, with φ real and of order 1. (The existential
(∃g) : g!x ≡ₓ φ!x does not depend on that: φ itself is a witness, `realPhi_every_system`.)

The order of the *function* x̂ ↦ ψx is `fnOrder a ψ = max (a.ord + 1) (order of ψx)` (PM/Orders.lean).
It is decided at the one-element variable family `U` (`lvl_iff_order`, with a `Decidable` instance).

The p. 54 reading (`LvlArg`) counts a real variable φ as an argument that raises the order of φ!x to 2.
That is the order of φ!x as a function of φ *and* x (pp. 54, 170), and it refuses φ!x to
comprehension at `pred1 ind` (the existential itself still holds, with φ as witness). Before Will's
decision it was rejected for that reason; it is now the alternative style.

**The p. 55 reading is partial application** (Will's item (ii): "syntactic sugar"?). φ!x seen as a
function of (φ, x) and φ!x with φ fixed, seen as a function of x, are the same body as a
two-parameter function and as a one-parameter closure. `curry_order` (PM/Pred/Curry.lean) makes this a
checked fact: `fnOrder2 a b ψ = max (a.ord + 1) (fnOrder b (ψ φ))`, the order of the two-argument
function is the larger of the first argument's lowest compatible order and the order of the partial
application. `phi_x_two_views`: φ!x has order 2 as a function of (φ!ẑ, x) (pp. 54, 170) and is
predicative as a function of x with φ fixed (p. 55). Golden tests add p. 55's other case: with a
first-order function as apparent variable the partial application is of order 2. Partial application
is also how this encoding reads p. 56's second clause ("when the other arguments have values assigned
to them"), which links this to Q4.

### 6. (b) Comprehension

The decision is to **keep** comprehension (Will, 2026-10-11, Q2: as its own module, marked for what it
is for), as the constructors `compr1` and `compr2`, available in a system with `compr` (class
`Comprehension S`, PM/Rules/Comprehension.lean, decision 13):

```
compr1 (_ : S.compr = true) (ψ : V a → QF V) (h : S.style.adm1 k ψ) :
  ⊢ (∃f : fn1 a k) : ψx . ≡ₓ . f x
```

**Warrant.** ✱9·15 (p. 138) and ✱10·122 (p. 146): "If, for some a, there is a proposition φa, then
there is a function φx̂". Applied to an apparent variable over functions of order m, with ✱10·24 (or
✱10·1), this gives an existential whose witness is that function. PM licenses functions of a given
order to be formed from formulas whose variables are of lower order: pp. 54–56, 169–171, and p. 172,
"non-predicative functions always result from such as are predicative by means of generalization".

**The side condition** is the style's (decisions 3 and 5): the order check (`Lvl`, p. 55, or `LvlArg`,
p. 54) at the order of the type of f, and, in the matrix style at a predicative type, the matrix test.

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

**What Lean enforces, and what is convention.** Lean enforces that a rule is enabled in the system: a
proof that uses `red1` must supply a proof of `S.red = true`, and for an arbitrary `S` it has to get one
from a hypothesis. It does not enforce the form of that hypothesis: a theorem taking
`(h : S.red = true)` can call `QThm.red1 h φ` without `[Reducibility S]` (as an external review pointed out). That is
not a way around the rule (the evidence is equivalent to the capability), but the dependency is then
not shown by the class. That a theorem using a rule takes the class in its signature
(`theorem q13_101 [Reducibility S] …`) is the repository's convention, and `RedCheck.lean` checks it
(below), including that route. Reaching a rule shows that a proof uses it, not that the rule is
logically necessary for the theorem (after an external review); the absence of a cycle in the constant
graph only makes the reachability exact. A theorem that uses no rule holds in every system, including
later ones (the 1925 pass will add an `Extensionality` capability). `QThm.mono` lifts a derivation to
any system with more rules and a more permissive style. `PM/Systems.lean` names four systems: `Sys.full` (both rules),
`Sys.reducibility` (PM's own route), `Sys.predicative` (comprehension only) and `Sys.base` (neither).

Every ✱1–✱11 proof is unchanged; their statements gained the parameter `S`. The ✱12–✱20 theorems that
use ✱12·1 gained `[Reducibility S]`, found by compiling (Lean refuses the proof without some evidence
of `S.red = true`, and the class was the evidence given); the list
is the same 29 that the old after-the-fact scan found.

`RedCheck.lean` checks the convention from the proof terms, in two ways. (1) It follows the constants
used by each declaration, transitively, as `#print axioms` does, and reports which reach the class
field `Reducibility.red` or `Comprehension.compr`. (2) It follows only proof terms (the values of
constants) and reports which reach the constructors `QThm.red1`/`red2` or `QThm.compr1`/`compr2`; this
catches evidence supplied other than by the class, directly or through any helper lemma. It does not
look inside recursors, `casesOn`, `below`/`brecOn`, `noConfusion` or matchers, whose types name every
constructor, so that a proof by induction on `QThm`, such as `qsound`, does not count as using every
rule. A declaration uses a rule if either analysis finds it; that is compared with whether the class
occurs in the declaration's type. Result: 29 PM propositions use reducibility, 1 uses comprehension
(the two analyses agree on all 351), and 0 disagree with their signatures. The test
`RedCheckTest.red_with_explicit_evidence` (in RedCheck.lean; from an external review) calls
`QThm.red1` with explicit evidence and no class: RedCheck flags it, and fails if it does not.

**Rejected:**
- the earlier after-the-fact scan alone, with `QThm`'s type unchanged: the dependency was invisible in
  the statements;
- a second inductive per system: it would duplicate every rule-lemma of ✱10–✱11 (`qsyl`, `q10_11_27`, …).
  With one parameterised inductive, those lemmas are stated once for every `S`.

## 2. What was built

| File | Lines | Contents |
|---|---|---|
| `PM/Quant.lean` | 315 | `Ty` with `fn1`/`fn2` and `Ty.ord`, `pred1`/`pred2`; `QF.app1`/`app2`; `Style`, `OrderCheck`, `Sys`; `QThm S` with gated `compr1`, `compr2`, `red1`, `red2`; `QThm.mono`; `QModel` (values, application, abstraction), `qsound` |
| `PM/Rules/Reducibility.lean`, `PM/Rules/Comprehension.lean` | 25, 41 | the classes `Reducibility S`, `Comprehension S` with their PM warrants; `comprehension1`, `comprehension2` |
| `PM/Systems.lean` | 33 | `Sys.full`, `Sys.reducibility`, `Sys.predicative`, `Sys.base` and their instances |
| `PM/Pred/RealOwnOrder.lean`, `PM/Pred/RealAsArgument.lean` | 29, 72 | `Lvl` (p. 55), `LvlArg` (p. 54) with its decision procedure at `U` |
| `PM/Pred/Matrix.lean`, `PM/Pred/LowestOrder.lean` | 40, 26 | `IsMatrix`, `Style.matrix` (p. 172, primary); `Style.lowestOrder` (p. 56) |
| `PM/Pred/Styles.lean` | 211 | `PredReading`, `RealReading`, `Style.of` (four styles); `QThm.matrix_to_lowestOrder`; golden tests where the styles differ; `p171_…`, `realPhi_…`; `consistent_of_style`, `consistent_collapse_of_style` |
| `PM/StylesEquiv.lean` | 116 | `qex_chain`, `restyle`, `admitsPredApp_of`, `styles_equiv`, `styles_equiv_full`, `styles_equiv_real` |
| `PM/Pred/Curry.lean` | 163 | `fnOrder2`, `curry_order`, `phi_x_two_views`; `second_clause_iff_lowestOrder`, `second_clause_matrix_iff`, `anyLe_iff_le_maxL` |
| `PM/Models/Collapse.lean`, `PM/Models/Finite.lean` | 54, 152 | `Ty.den`, `QModel.collapse`, `classicalAll`, `QModel.classical`, `consistent_collapse`; shapes `Sh`, `finModel`, `twoModel`, `emptyModel`, `consistent`, `consistent_all`, three counter-models |
| `PM/Star12.lean` | 80 | ✱12·1, ✱12·11 with PM's macros; variable-shape corollaries; `q12_1_of_var` |
| `PM/Star13.lean` | 221 | ✱13·01–✱13·03 (macros); all 24 numbered propositions ✱13·1–✱13·22 except ✱13·3 |
| `PM/Star14.lean` | 125 | ✱14·01, ✱14·02 (macros); ✱14·1, ✱14·101, ✱14·11, ✱14·12, ✱14·121, ✱14·2, ✱14·201, ✱14·21; a scope counter-model |
| `PM/Star20.lean` | 109 | ✱20·01, ✱20·02 (macros), class identity; ✱20·1, ✱20·13, ✱20·14, ✱20·15, ✱20·3; typical-ambiguity checks |
| `PM/Orders.lean` | 166 | decidable order checker; order tests |
| `PM/Trap.lean` | 96 | `trap_empty`, `trap_unit`, `trap_unit_compr`, `trap_unit_compr_of` |
| `RedCheck.lean`, `StyleCheck.lean`, `ClauseSearch.lean` | 122, 73, 47 | rule use vs signatures; every PM proposition under every style and system; the p. 56 search |

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
itself. The per-proposition ledgers are `data/star12_ledger.json`, `star13_ledger.json`,
`star14_ledger.json` and `star20_ledger.json` (the format of `data/star11_ledger.json`).

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
| **S1** every PM theorem under every style (Will, Q1 and Q3) | **pass** | `StyleCheck.lean`: each of the 351 PM propositions instantiates in `Sys.full` of each of the four styles (matrix / lowest order × p. 55 / p. 54): 351/351 each; 0 without a parameter `S`; per system, in every style: reducibility 350, predicative 322, base 321 (the 29 that take `Reducibility` and the 1 that takes `Comprehension` drop out as expected). Consistency in every style: `consistent_of_style` (finite model, no axioms), `consistent_collapse_of_style` (collapse model, classical axioms) |
| **S2** `styles_equiv` (Will, item (i)) | **pass** | PM/StylesEquiv.lean: with reducibility, any two styles derive the same `QThm` theorems, for either setting of comprehension. Kernel-checked induction (`restyle`), no axioms; uses ✱12·1/✱12·11 (RedCheck). Without reducibility, strict weakness of the matrix style: **skipped** (needs an order-aware model, F4) |
| **S3** currying (Will, item (ii)) | **pass** | `curry_order`, `phi_x_two_views`, golden tests (PM/Pred/Curry.lean) |
| **S4** p. 56 second clause vs lowest order (Will, item (iii)) | **no case exists within this encoding** | `second_clause_iff_lowestOrder`, `second_clause_matrix_iff`, `anyLe_iff_le_maxL` (proofs, no axioms); `ClauseSearch.lean`: 2,784,780 cases, 0 disagreements, comparing the same definitions. Both partial applications are evaluated at `()` in `U` with the same body order, so the result is the arithmetic O ≤ a + 1 ∨ O ≤ b + 1 ↔ O ≤ max a b + 1; it does not show that the encoding captures PM's "assignment of values", nor extend to arbitrary variable families. Not added as a style (none needed within this encoding) |

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
- **Build:** clean `lake build`, 33 jobs, 12.5 s (wall clock, after `lake clean`).

## 4. Axioms

`AxiomCheck.lean`: 617 names; 613 report no axioms. The other 4 belong to the classical collapse model
(below). Every PM theorem (✱2–✱5 and the ✱9–✱20 `q…` theorems), `complete`, `qsound`, `QThm.mono`,
`consistent`, `consistent_all`, `consistent_of_style`, the five counter-models, the finite model,
`restyle`, `styles_equiv` (and `styles_equiv_full`, `styles_equiv_real`), `curry_order`,
`second_clause_iff_lowestOrder`, `anyLe_iff_le_maxL`, `lvl_iff_order`, `lvlArg_iff_orderArg`, the trap
theorems and the golden theorems are axiom-free.

`AllAxioms.lean`: all 1411 declarations under `PM` and all 31 private declarations of the PM modules
(`_private.PM.…`, skipped before an external review; none uses an axiom). Exactly 25 use an axiom:

| Declarations | Axioms | Why |
|---|---|---|
| `classicalAll`, `classicalAll_spec`, `QModel.classical` | propext, Classical.choice, Quot.sound | the general collapse model, kept: classical quantifiers over arbitrary function spaces (`Classical.propDecidable`) |
| `consistent_collapse`, `consistent_collapse_of_style` | propext, Classical.choice, Quot.sound | consistency evaluated in the classical collapse model (the axiom-free consistency proofs are `consistent`, `consistent_of_style`) |
| `PM.sound`, `PM.not_thm_of_countermodel`, `PM.star1_4_variant_not_a_theorem` | propext, Quot.sound | propositional metatheorems (unchanged from before) |
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
3. **Real variables count with their own order (p. 55) or as arguments (p. 54)?** DECIDED by Will
   (2026-10-11 ~19:00): both, as styles, both must pass. Done: decision 5;
   `PM/Pred/RealOwnOrder.lean` (default) and `PM/Pred/RealAsArgument.lean`, each combined with both
   readings of "predicative" (four styles); every PM theorem checked under every combination
   (`StyleCheck.lean`); consistency for each; golden tests where they differ; `styles_equiv` (and
   `styles_equiv_real`) shows that with reducibility they derive the same theorems. Will's framing
   ("syntactic sugar"?) is made precise by `curry_order` (decision 5): the two readings are the same
   body seen as a closure and as a two-argument function.
4. **Several-argument predicativity.** Proceeding on the recommended default (no separate type; Will has
   not objected, 2026-10-11), and SEARCHED as Will asked (item (iii), 2026-10-11 evening): is there a
   function of our types on which p. 56's second clause ("if there is one of its arguments such that,
   when the other arguments have values assigned to them, we obtain a predicative function of the one
   undetermined argument") and the lowest-order rule stated just before it disagree? **None exists
   within this encoding.** The encoding reads "the other arguments have values assigned to them" as
   evaluating both partial applications at `()` in the one-element family `U`, so both have the same
   body order O, and the order of the function of argument i, the others fixed, is max (oᵢ + 1) O
   (`fnOrder`). Under that reading, `second_clause_iff_lowestOrder` proves agreement for every
   two-argument body (fixed arguments counted at their own order, p. 55), `second_clause_matrix_iff`
   for the matrix reading, and `anyLe_iff_le_maxL` for any number of arguments; all three reduce to
   the arithmetic O ≤ a + 1 ∨ O ≤ b + 1 ↔ O ≤ max a b + 1. The concrete search (`ClauseSearch.lean`:
   34,380 bodies of depth ≤ 2 over 9 types × 81 pairs of argument types, 2,784,780 cases) compares the
   same definitions and found 0 disagreements. This is a theorem about this encoding; it does
   not independently show that the encoding captures PM's "assignment of values", nor extend to
   arbitrary variable families. **No separate style is needed within this encoding**, so the clause is
   not added as one. The earlier note that the clause is "weaker" does not hold in this encoding. A
   different reading of "assignment of values" (one in which assigning a value can change the order
   of the remaining function other than through max (oᵢ + 1) O) could make the clause differ; that
   question stays open.
5. **Axiom-free consistency.** DECIDED by Will (2026-10-11): yes, "its own little module". Done:
   PM/Models/Finite.lean; `consistent`, `consistent_all` and the counter-models use no axioms; the
   classical collapse model is kept as the general one (decision 11).

## 6. Not done

- ✱13·3; ✱14 beyond the eight propositions listed; ✱20 beyond the five listed.
- F4 (non-derivability of impredicative comprehension without ✱12·1), and so the strict weakness of the
  matrix style and of the p. 54 reading without reducibility: skipped. It needs a model that sees orders;
  both models here forget them.
- The scan images were not viewed (F3).
- The n-ary function types and the 1925 route.
