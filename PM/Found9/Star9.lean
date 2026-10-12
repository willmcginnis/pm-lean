import PM.Found9.Base
/-!
  ✱9's numbered propositions (pp. 136–142), proved by ✱9's own method (PM/Found9/System.lean).

  As in ✱9, p, q, r are elementary propositions and φ, ψ elementary functions (p. 134: "the single
  letters p and q will represent elementary propositions, and so will "φx," "ψx," etc."): in Lean
  `p q r : EF V` and `φ ψ : V τ → EF V`; `Al φ` is (x) . φx and `Ex φ` is (∃x) . φx. Each proof follows
  PM's Dem. line by line. A line that PM justifies by definitions alone ("[(4).(✱9·06)]") is stated in
  its printed form and checked by Lean as the same proposition, since ✱9·01–✱9·08 are computed by
  `PF.neg` and `PF.or`. "✱1·11 is used ... in almost all steps except such as are mere applications of
  definitions. Hence it will not be further referred to" (p. 139): it is `Thm9.mp`. Where PM writes
  "✱9·13" before a ✱9·21 or ✱9·22 that needs "(x) : φx ⊃ ψx", the step is `Thm9.gen`.

  Names: `f9_21` is ✱9·21 by ✱9's method (`q9_21` in PM/Star10.lean is the same proposition by ✱10's).
-/
namespace PM.F9
open PF

variable {V : Ty → Type} {S : Sys} {τ : Ty}

/-- (x) . φx, for an elementary function φ. -/
abbrev Al (φ : V τ → EF V) : PF V := .all fun x => .el (φ x)
/-- (∃x) . φx, for an elementary function φ. -/
abbrev Ex (φ : V τ → EF V) : PF V := .ex fun x => .el (φ x)

/-! ## The primitive propositions -/

/-- ✱9·1 `⊢ : φx . ⊃ . (∃z) . φz` Pp (stated for every function φ; see PM/Found9/System.lean). -/
theorem f9_1 (φ : V τ → PF V) (x : V τ) : Thm9 S (imp (φ x) (.ex φ)) := Thm9.ex1 φ x
/-- ✱9·11 `⊢ : φx ∨ φy . ⊃ . (∃z) . φz` Pp -/
theorem f9_11 (φ : V τ → PF V) (x y : V τ) : Thm9 S (imp (PF.or (φ x) (φ y)) (.ex φ)) :=
  Thm9.ex2 φ x y
/-- ✱9·12 "What is implied by a true premiss is true." Pp -/
theorem f9_12 {p q : PF V} (hp : Thm9 S p) (h : Thm9 S (imp p q)) : Thm9 S q := Thm9.mp hp h
/-- ✱9·13 "In any assertion containing a real variable, this real variable may be turned into an
    apparent variable of which all possible values are asserted to satisfy the function in question."
    Pp -/
theorem f9_13 {φ : V τ → PF V} (h : ∀ y, Thm9 S (φ y)) : Thm9 S (.all φ) := Thm9.gen h

/-! ## ✱9·2–✱9·25 -/

/-- ✱9·2 `⊢ : (x) . φx . ⊃ . φy` (p. 138). For every function φ it is `inst` (PM/Found9/Base.lean). -/
theorem f9_2 (φ : V τ → EF V) (y : V τ) : Thm9 S (imp (Al φ) (.el (φ y))) :=
  have h1 : Thm9 S (.el (.or (.neg (φ y)) (φ y))) :=
    elift (t2_1 (.var "p")) (esub (φ y) (φ y) (φ y))                            -- ✱2·1 (1)
  have h2 : Thm9 S (imp (.el (.or (.neg (φ y)) (φ y)))
      (.ex fun x => .el (.or (.neg (φ x)) (φ y)))) :=
    Thm9.ex1 (fun x => .el (.or (.neg (φ x)) (φ y))) y                           -- ✱9·1 (2)
  have h3 := Thm9.mp h1 h2                                                       -- (1).(2).✱1·11 (3)
  have h4 : Thm9 S (PF.or (.ex fun x => .el (.neg (φ x))) (.el (φ y))) := h3      -- [(3).(✱9·05)] (4)
  h4                                                                             -- [(4).(✱9·01.✱1·01)]

/-- ✱9·21 `⊢ :. (x) . φx ⊃ ψx . ⊃ : (x) . φx . ⊃ . (x) . ψx` (p. 139). "This is the proposition to be
    proved, since "(y) . φy" is the same proposition as "(x) . φx," and "(z) . ψz" is the same
    proposition as "(x) . ψx."" -/
theorem f9_21 (φ ψ : V τ → EF V) :
    Thm9 S (imp (.all fun x => .el (EF.imp (φ x) (ψ x))) (imp (Al φ) (Al ψ))) :=
  have h1 : ∀ z, Thm9 S (.el (EF.imp (EF.imp (φ z) (ψ z)) (EF.imp (φ z) (ψ z)))) :=
    fun z => eId (EF.imp (φ z) (ψ z))                                                               -- ✱2·08 (1)
  have h2 : ∀ z, Thm9 S (.ex fun y => .el (EF.imp (EF.imp (φ z) (ψ z)) (EF.imp (φ y) (ψ z)))) :=
    fun z => exI z (h1 z)                                                        -- (1).✱9·1 (2)
  have h3 : ∀ z, Thm9 S (.ex fun x => .ex fun y =>
      .el (EF.imp (EF.imp (φ x) (ψ x)) (EF.imp (φ y) (ψ z)))) :=
    fun z => exI z (h2 z)                                                        -- (2).✱9·1 (3)
  have h4 : Thm9 S (.all fun z => .ex fun x => .ex fun y =>
      .el (EF.imp (EF.imp (φ x) (ψ x)) (EF.imp (φ y) (ψ z)))) := Thm9.gen h3     -- (3).✱9·13 (4)
  have h5 : Thm9 S (.all fun z => .ex fun x =>
      imp (.el (EF.imp (φ x) (ψ x))) (.ex fun y => .el (EF.imp (φ y) (ψ z))))
    := h4                                                                        -- [(4).(✱9·06)] (5)
  have h6 : Thm9 S (PF.or (.ex fun x => .el (.neg (EF.imp (φ x) (ψ x))))
      (.all fun z => .ex fun y => .el (.or (.neg (φ y)) (ψ z)))) := h5            -- [(5).(✱1·01.✱9·08)] (6)
  have h7 : Thm9 S (PF.or (.ex fun x => .el (.neg (EF.imp (φ x) (ψ x))))
      (PF.or (.ex fun y => .el (.neg (φ y))) (Al ψ))) := h6                        -- [(6).(✱9·08)] (7)
  h7                                                                             -- [(7).(✱1·01)]

/-- ✱9·22 `⊢ :. (x) . φx ⊃ ψx . ⊃ : (∃x) . φx . ⊃ . (∃x) . ψx` (p. 139) -/
theorem f9_22 (φ ψ : V τ → EF V) :
    Thm9 S (imp (.all fun x => .el (EF.imp (φ x) (ψ x))) (imp (Ex φ) (Ex ψ))) :=
  have h1 : ∀ y, Thm9 S (.el (EF.imp (EF.imp (φ y) (ψ y)) (EF.imp (φ y) (ψ y)))) :=
    fun y => eId (EF.imp (φ y) (ψ y))                                                               -- ✱2·08 (1)
  have h2 : ∀ y, Thm9 S (.ex fun z => .el (EF.imp (EF.imp (φ y) (ψ y)) (EF.imp (φ y) (ψ z)))) :=
    fun y => exI y (h1 y)                                                        -- (1).✱9·1 (2)
  have h3 : ∀ y, Thm9 S (.ex fun x => .ex fun z =>
      .el (EF.imp (EF.imp (φ x) (ψ x)) (EF.imp (φ y) (ψ z)))) :=
    fun y => exI y (h2 y)                                                        -- (2).✱9·1 (3)
  have h4 : Thm9 S (.all fun y => .ex fun x => .ex fun z =>
      .el (EF.imp (EF.imp (φ x) (ψ x)) (EF.imp (φ y) (ψ z)))) := Thm9.gen h3     -- (3).✱9·13 (4)
  have h5 : Thm9 S (.all fun y => .ex fun x =>
      imp (.el (EF.imp (φ x) (ψ x))) (.ex fun z => .el (EF.imp (φ y) (ψ z))))
    := h4                                                                        -- [(4).(✱9·06)] (5)
  have h6 : Thm9 S (PF.or (.ex fun x => .el (.neg (EF.imp (φ x) (ψ x))))
      (.all fun y => .ex fun z => .el (.or (.neg (φ y)) (ψ z)))) := h5            -- [(5).(✱1·01.✱9·08)] (6)
  have h7 : Thm9 S (PF.or (.ex fun x => .el (.neg (EF.imp (φ x) (ψ x))))
      (PF.or (.all fun y => .el (.neg (φ y))) (Ex ψ))) := h6                       -- [(6).(✱1·01.✱9·07)] (7)
  h7                                                                             -- [(7).(✱1·01.✱9·01·02)]

/-- ✱9·23 `⊢ : (x) . φx . ⊃ . (x) . φx` [Id . ✱9·13·21] -/
theorem f9_23 (φ : V τ → EF V) : Thm9 S (imp (Al φ) (Al φ)) :=
  Thm9.mp (Thm9.gen fun x => eId (φ x)) (f9_21 φ φ)

/-- ✱9·24 `⊢ : (∃x) . φx . ⊃ . (∃x) . φx` [Id . ✱9·13·22] -/
theorem f9_24 (φ : V τ → EF V) : Thm9 S (imp (Ex φ) (Ex φ)) :=
  Thm9.mp (Thm9.gen fun x => eId (φ x)) (f9_22 φ φ)

/-- ✱9·25 `⊢ :. (x) . p ∨ φx . ⊃ : p . ∨ . (x) . φx` [✱9·23 . (✱9·04)]. By ✱9·04 the two sides are
    the same proposition: ✱10·12 "is a mere example of "q ⊃ q"" (p. 146). For an elementary p and every
    function φ it is `distribEl` (PM/Found9/Base.lean). For a p with apparent variables the two sides
    can be the same proposition or differ (`distrib_sides_ne`); for every p it is `Rep.distrib`, given
    `Rep` and a variable of every type (PM/Found9/FromStar10.lean). -/
theorem f9_25 (p : EF V) (φ : V τ → EF V) :
    Thm9 S (imp (.all fun x => .el (.or p (φ x))) (PF.or (.el p) (Al φ))) :=
  f9_23 fun x => .or p (φ x)

/-! ## ✱9·3–✱9·52: ✱1·2–✱1·6 with one letter replaced by (x) . φx or (∃x) . φx -/

/-- ✱9·3 `⊢ :. (x) . φx . ∨ . (x) . φx : ⊃ . (x) . φx` (p. 140). Line (5) applies ✱9·21 to the function
    "φx . ∨ . (y) . φy", which contains an apparent variable; ✱9·21 is proved above for elementary
    functions, so the Lean line uses its rule form for every function (`allImp`), after `allE`. -/
theorem f9_3 (φ : V τ → EF V) : Thm9 S (imp (PF.or (Al φ) (Al φ)) (Al φ)) :=
  have h1 : ∀ x, Thm9 S (.el (EF.imp (.or (φ x) (φ x)) (φ x))) :=
    fun x => Thm9.taut (φ x)                                                     -- ✱1·2 (1)
  have h2 : ∀ x, Thm9 S (.ex fun y => .el (EF.imp (.or (φ x) (φ y)) (φ x))) :=
    fun x => exI x (h1 x)                                                        -- (1).✱9·1 (2)
  have h3 : Thm9 S (.all fun x => .ex fun y => .el (EF.imp (.or (φ x) (φ y)) (φ x))) :=
    Thm9.gen h2                                                                  -- (2).✱9·13 (3)
  have h4 : Thm9 S (.all fun x => imp (PF.or (.el (φ x)) (Al φ)) (.el (φ x))) :=
    h3                                                                           -- [(3).(✱9·05·01·04)] (4)
  have h5 : Thm9 S (imp (.all fun x => PF.or (.el (φ x)) (Al φ)) (Al φ)) :=
    allImp fun x => allE h4 x                                                    -- (4).✱9·21 (5)
  h5                                                                             -- [(5).(✱9·03)]

/-- ✱9·31 `⊢ :. (∃x) . φx . ∨ . (∃x) . φx : ⊃ . (∃x) . φx` (p. 140), PM's Dem. lines (1)–(3). "This is
    the only proposition which employs ✱9·11." Line (3) is `⊢ : (x) : (∃y) . φx ∨ φy . ⊃ . (∃z) . φz`.
    PM passes to line (4), `(∃x) : (∃y) . φx ∨ φy : ⊃ . (∃z) . φz`, by "[(3).(✱9·03·02)]": it reads
    `(x) : (y) . ∼(φx ∨ φy) . ∨ . (∃z) . φz` by ✱9·03, with p = (∃z) . φz, as
    (x) : (y) : (∃z) . ∼(φx ∨ φy) ∨ φz, which is line (3). The definitions as printed do not give
    that: the left side begins with (x) and the right with (∃z), so ✱9·07 applies, "also when φ and ψ
    are not both elementary", and line (4) is (x) : (∃z) : (y) . ∼(φx ∨ φy) ∨ φz (`f9_31_step`). So the
    step, cited as definitions alone, is not a definitional rewrite, and PM cites no step that
    exchanges quantifiers. That does not show ✱9·31 false or underivable: whether ✱9's method derives
    it is open, and it is not proved here (docs/STAR9_FOUNDATION.md). With ✱1·2 for every proposition
    (`Rep`) it is an instance of ✱1·2. -/
theorem f9_31_3 (φ : V τ → EF V) :
    Thm9 S (.all fun x => imp (.ex fun y => .el (.or (φ x) (φ y))) (Ex φ)) :=
  have h1 : ∀ x, Thm9 S (.all fun y => imp (.el (.or (φ x) (φ y))) (Ex φ)) :=
    fun x => Thm9.gen fun y => Thm9.ex2 (fun z => .el (φ z)) x y                 -- ✱9·11·13 (1)
  have h2 : ∀ x, Thm9 S (imp (.ex fun y => .el (.or (φ x) (φ y))) (Ex φ)) :=
    h1                                                                           -- [(1).(✱9·03·02)] (2)
  Thm9.gen h2                                                                    -- (2).✱9·13 (3)

/-- PM's step from line (3) to line (4) of ✱9·31 is not an application of the definitions as
    printed: given a variable of every type, the two propositions differ in the order of their
    quantifiers, (x) : (y) : (∃z) and (x) : (∃z) : (y). In the earlier reading `PF.orL`, which applies
    ✱9·03 for every p, they are the same proposition (`f9_31_step_orL`). This is about the cited step
    only, not about whether ✱9·31 can be derived. -/
theorem f9_31_step (d : ∀ τ, V τ) (φ : V τ → EF V) :
    (PF.all fun x => imp (.ex fun y => .el (.or (φ x) (φ y))) (Ex φ)) ≠
      imp (PF.or (Ex φ) (Ex φ)) (Ex φ) := by
  intro h
  have h' : [true, true, false] = [true, false, true] := congrArg (PF.kinds d) h
  exact absurd h' (by decide)

/-- In the earlier reading `PF.orL`, PM's line (4) of ✱9·31 is line (3). -/
theorem f9_31_step_orL (φ : V τ → EF V) :
    (PF.all fun x => PF.orL (PF.neg (.ex fun y => .el (.or (φ x) (φ y)))) (Ex φ)) =
      PF.orL (PF.neg (PF.orL (Ex φ) (Ex φ))) (Ex φ) := rfl

/-- ✱9·32 `⊢ :. q . ⊃ : (x) . φx . ∨ . q` (p. 140). Line (2) cites ✱9·25, which is Id here. -/
theorem f9_32 (φ : V τ → EF V) (q : EF V) : Thm9 S (imp (.el q) (PF.or (Al φ) (.el q))) :=
  have h1 : ∀ x, Thm9 S (.el (EF.imp q (.or (φ x) q))) := fun x => Thm9.add (φ x) q  -- ✱1·3 (1)
  have h1' : Thm9 S (.all fun x => .el (.or (.neg q) (.or (φ x) q))) := Thm9.gen h1  -- (1).✱9·13
  have h2 : Thm9 S (imp (.el q) (.all fun x => .el (.or (φ x) q))) :=
    Thm9.mp h1' (f9_25 (.neg q) fun x => .or (φ x) q)                             -- [✱9·25] (2)
  h2                                                                             -- [(2).(✱9·03)]

/-- ✱9·33 `⊢ :. q . ⊃ : (∃x) . φx . ∨ . q` [Proof as above]. Reconstructed with ✱9·1 in place of
    ✱9·13 and ✱9·25, so it needs a real variable x: in Lean the statement takes one. -/
theorem f9_33 (φ : V τ → EF V) (q : EF V) (x : V τ) : Thm9 S (imp (.el q) (PF.or (Ex φ) (.el q))) :=
  have h1 : Thm9 S (.el (EF.imp q (.or (φ x) q))) := Thm9.add (φ x) q            -- ✱1·3 (1)
  have h2 : Thm9 S (.ex fun x => .el (EF.imp q (.or (φ x) q))) := exI x h1       -- (1).✱9·1
  have h3 : Thm9 S (imp (.el q) (.ex fun x => .el (.or (φ x) q))) := h2          -- [(✱9·06)] (2)
  h3                                                                             -- [(2).(✱9·05)]

/-- ✱9·34 `⊢ :. (x) . φx . ⊃ : p . ∨ . (x) . φx` (p. 141) -/
theorem f9_34 (φ : V τ → EF V) (p : EF V) : Thm9 S (imp (Al φ) (PF.or (.el p) (Al φ))) :=
  have h1 : ∀ x, Thm9 S (.el (EF.imp (φ x) (.or p (φ x)))) := fun x => Thm9.add p (φ x)  -- ✱1·3 (1)
  have h2 : Thm9 S (.all fun x => .el (EF.imp (φ x) (.or p (φ x)))) := Thm9.gen h1        -- (1).✱9·13 (2)
  have h3 : Thm9 S (imp (Al φ) (.all fun x => .el (.or p (φ x)))) :=
    Thm9.mp h2 (f9_21 φ fun x => .or p (φ x))                                    -- (2).✱9·21 (3)
  h3                                                                             -- (3).(✱9·04)

/-- ✱9·35 `⊢ :. (∃x) . φx . ⊃ : p . ∨ . (∃x) . φx` [Proof as above: ✱9·22 for ✱9·21, ✱9·06 for ✱9·04] -/
theorem f9_35 (φ : V τ → EF V) (p : EF V) : Thm9 S (imp (Ex φ) (PF.or (.el p) (Ex φ))) :=
  have h1 : ∀ x, Thm9 S (.el (EF.imp (φ x) (.or p (φ x)))) := fun x => Thm9.add p (φ x)  -- ✱1·3 (1)
  have h2 : Thm9 S (.all fun x => .el (EF.imp (φ x) (.or p (φ x)))) := Thm9.gen h1        -- (1).✱9·13 (2)
  have h3 : Thm9 S (imp (Ex φ) (.ex fun x => .el (.or p (φ x)))) :=
    Thm9.mp h2 (f9_22 φ fun x => .or p (φ x))                                    -- (2).✱9·22 (3)
  h3                                                                             -- (3).(✱9·06)

/-- ✱9·36 `⊢ :. p . ∨ . (x) . φx : ⊃ : (x) . φx . ∨ . p` (p. 141) -/
theorem f9_36 (φ : V τ → EF V) (p : EF V) :
    Thm9 S (imp (PF.or (.el p) (Al φ)) (PF.or (Al φ) (.el p))) :=
  have h1 : ∀ x, Thm9 S (.el (EF.imp (.or p (φ x)) (.or (φ x) p))) := fun x => Thm9.perm p (φ x)  -- ✱1·4 (1)
  have h2 : Thm9 S (imp (.all fun x => .el (.or p (φ x))) (.all fun x => .el (.or (φ x) p))) :=
    Thm9.mp (Thm9.gen h1) (f9_21 (fun x => .or p (φ x)) fun x => .or (φ x) p)    -- (1).✱9·13·21 (2)
  h2                                                                             -- (2).(✱9·03·04)

/-- ✱9·361 `⊢ :. (x) . φx . ∨ . p : ⊃ : p . ∨ . (x) . φx` [Similar proof] -/
theorem f9_361 (φ : V τ → EF V) (p : EF V) :
    Thm9 S (imp (PF.or (Al φ) (.el p)) (PF.or (.el p) (Al φ))) :=
  have h1 : ∀ x, Thm9 S (.el (EF.imp (.or (φ x) p) (.or p (φ x)))) := fun x => Thm9.perm (φ x) p  -- ✱1·4
  have h2 : Thm9 S (imp (.all fun x => .el (.or (φ x) p)) (.all fun x => .el (.or p (φ x)))) :=
    Thm9.mp (Thm9.gen h1) (f9_21 (fun x => .or (φ x) p) fun x => .or p (φ x))    -- ✱9·13·21
  h2                                                                             -- (✱9·03·04)

/-- ✱9·37 `⊢ :. p . ∨ . (∃x) . φx : ⊃ : (∃x) . φx . ∨ . p` [Similar proof] -/
theorem f9_37 (φ : V τ → EF V) (p : EF V) :
    Thm9 S (imp (PF.or (.el p) (Ex φ)) (PF.or (Ex φ) (.el p))) :=
  have h1 : ∀ x, Thm9 S (.el (EF.imp (.or p (φ x)) (.or (φ x) p))) := fun x => Thm9.perm p (φ x)  -- ✱1·4
  have h2 : Thm9 S (imp (.ex fun x => .el (.or p (φ x))) (.ex fun x => .el (.or (φ x) p))) :=
    Thm9.mp (Thm9.gen h1) (f9_22 (fun x => .or p (φ x)) fun x => .or (φ x) p)    -- ✱9·13·22
  h2                                                                             -- (✱9·05·06)

/-- ✱9·371 `⊢ :. (∃x) . φx . ∨ . p : ⊃ : p . ∨ . (∃x) . φx` [Similar proof] -/
theorem f9_371 (φ : V τ → EF V) (p : EF V) :
    Thm9 S (imp (PF.or (Ex φ) (.el p)) (PF.or (.el p) (Ex φ))) :=
  have h1 : ∀ x, Thm9 S (.el (EF.imp (.or (φ x) p) (.or p (φ x)))) := fun x => Thm9.perm (φ x) p  -- ✱1·4
  have h2 : Thm9 S (imp (.ex fun x => .el (.or (φ x) p)) (.ex fun x => .el (.or p (φ x)))) :=
    Thm9.mp (Thm9.gen h1) (f9_22 (fun x => .or (φ x) p) fun x => .or p (φ x))    -- ✱9·13·22
  h2                                                                             -- (✱9·05·06)

/-- ✱9·4 `⊢ :: p : ∨ : q . ∨ . (x) . φx :. ⊃ :. q : ∨ : p . ∨ . (x) . φx` (p. 141) -/
theorem f9_4 (φ : V τ → EF V) (p q : EF V) :
    Thm9 S (imp (PF.or (.el p) (PF.or (.el q) (Al φ))) (PF.or (.el q) (PF.or (.el p) (Al φ)))) :=
  have h1 : Thm9 S (imp (.all fun x => .el (.or p (.or q (φ x))))
      (.all fun x => .el (.or q (.or p (φ x))))) :=
    Thm9.mp (Thm9.gen fun x => Thm9.assoc p q (φ x))
      (f9_21 (fun x => .or p (.or q (φ x))) fun x => .or q (.or p (φ x)))         -- ✱1·5.✱9·21 (1)
  h1                                                                             -- (1).(✱9·04)

/-- ✱9·401 `⊢ :: p : ∨ : q . ∨ . (∃x) . φx :. ⊃ :. q : ∨ : p . ∨ . (∃x) . φx` [As above] -/
theorem f9_401 (φ : V τ → EF V) (p q : EF V) :
    Thm9 S (imp (PF.or (.el p) (PF.or (.el q) (Ex φ))) (PF.or (.el q) (PF.or (.el p) (Ex φ)))) :=
  have h1 : Thm9 S (imp (.ex fun x => .el (.or p (.or q (φ x))))
      (.ex fun x => .el (.or q (.or p (φ x))))) :=
    Thm9.mp (Thm9.gen fun x => Thm9.assoc p q (φ x))
      (f9_22 (fun x => .or p (.or q (φ x))) fun x => .or q (.or p (φ x)))         -- ✱1·5.✱9·22
  h1                                                                             -- (✱9·06)

/-- ✱9·41 `⊢ :: p : ∨ : (x) . φx . ∨ . r :. ⊃ :. (x) . φx : ∨ : p ∨ r` [As above] -/
theorem f9_41 (φ : V τ → EF V) (p r : EF V) :
    Thm9 S (imp (PF.or (.el p) (PF.or (Al φ) (.el r))) (PF.or (Al φ) (.el (.or p r)))) :=
  have h1 : Thm9 S (imp (.all fun x => .el (.or p (.or (φ x) r)))
      (.all fun x => .el (.or (φ x) (.or p r)))) :=
    Thm9.mp (Thm9.gen fun x => Thm9.assoc p (φ x) r)
      (f9_21 (fun x => .or p (.or (φ x) r)) fun x => .or (φ x) (.or p r))         -- ✱1·5.✱9·21
  h1                                                                             -- (✱9·03·04)

/-- ✱9·411 `⊢ :: p : ∨ : (∃x) . φx . ∨ . r :. ⊃ :. (∃x) . φx : ∨ : p ∨ r` [As above] -/
theorem f9_411 (φ : V τ → EF V) (p r : EF V) :
    Thm9 S (imp (PF.or (.el p) (PF.or (Ex φ) (.el r))) (PF.or (Ex φ) (.el (.or p r)))) :=
  have h1 : Thm9 S (imp (.ex fun x => .el (.or p (.or (φ x) r)))
      (.ex fun x => .el (.or (φ x) (.or p r)))) :=
    Thm9.mp (Thm9.gen fun x => Thm9.assoc p (φ x) r)
      (f9_22 (fun x => .or p (.or (φ x) r)) fun x => .or (φ x) (.or p r))         -- ✱1·5.✱9·22
  h1                                                                             -- (✱9·05·06)

/-- ✱9·42 `⊢ :: (x) . φx : ∨ : q ∨ r :. ⊃ :. q : ∨ : (x) . φx . ∨ . r` [As above] -/
theorem f9_42 (φ : V τ → EF V) (q r : EF V) :
    Thm9 S (imp (PF.or (Al φ) (.el (.or q r))) (PF.or (.el q) (PF.or (Al φ) (.el r)))) :=
  have h1 : Thm9 S (imp (.all fun x => .el (.or (φ x) (.or q r)))
      (.all fun x => .el (.or q (.or (φ x) r)))) :=
    Thm9.mp (Thm9.gen fun x => Thm9.assoc (φ x) q r)
      (f9_21 (fun x => .or (φ x) (.or q r)) fun x => .or q (.or (φ x) r))         -- ✱1·5.✱9·21
  h1                                                                             -- (✱9·03·04)

/-- ✱9·421 `⊢ :: (∃x) . φx : ∨ : q ∨ r :. ⊃ :. q : ∨ : (∃x) . φx . ∨ . r` [As above] -/
theorem f9_421 (φ : V τ → EF V) (q r : EF V) :
    Thm9 S (imp (PF.or (Ex φ) (.el (.or q r))) (PF.or (.el q) (PF.or (Ex φ) (.el r)))) :=
  have h1 : Thm9 S (imp (.ex fun x => .el (.or (φ x) (.or q r)))
      (.ex fun x => .el (.or q (.or (φ x) r)))) :=
    Thm9.mp (Thm9.gen fun x => Thm9.assoc (φ x) q r)
      (f9_22 (fun x => .or (φ x) (.or q r)) fun x => .or q (.or (φ x) r))         -- ✱1·5.✱9·22
  h1                                                                             -- (✱9·05·06)

/-- The line PM labels "✱1·6" in ✱9·5, ✱9·51 and ✱9·52 has the disjunctions in the other order:
    `q ⊃ r . ⊃ : q ∨ p . ⊃ . r ∨ p` is ✱2·38, proved from ✱1·6 by ✱1·4 (p. 107). -/
theorem e2_38 (p q r : EF V) : Thm9 S (.el (EF.imp (EF.imp q r) (EF.imp (.or q p) (.or r p)))) :=
  elift (t2_38 (.var "p") (.var "q") (.var "r")) (esub p q r)

/-- ✱9·5 `⊢ :: p ⊃ q . ⊃ :. p . ∨ . (x) . φx : ⊃ : q . ∨ . (x) . φx` (p. 141). Line (1) is cited as
    ✱1·6; it is ✱2·38 (`e2_38`). -/
theorem f9_5 (φ : V τ → EF V) (p q : EF V) :
    Thm9 S (imp (.el (EF.imp p q)) (imp (PF.or (.el p) (Al φ)) (PF.or (.el q) (Al φ)))) :=
  have h1 : ∀ y, Thm9 S (.el (EF.imp (EF.imp p q) (EF.imp (.or p (φ y)) (.or q (φ y))))) :=
    fun y => e2_38 (φ y) p q                                                     -- ✱1·6 (1)
  have h2 : ∀ y, Thm9 S (imp (.el (EF.imp p q))
      (.ex fun x => .el (EF.imp (.or p (φ x)) (.or q (φ y))))) :=
    fun y => exI (φ := fun x => .el (EF.imp (EF.imp p q) (EF.imp (.or p (φ x)) (.or q (φ y))))) y
      (h1 y)                                                                     -- (1).✱9·1.(✱9·06) (2)
  have h3 : Thm9 S (imp (.el (EF.imp p q)) (.all fun y => .ex fun x =>
      .el (EF.imp (.or p (φ x)) (.or q (φ y))))) := Thm9.gen h2                  -- (2).✱9·13.(✱9·04) (3)
  have h4 : Thm9 S (imp (.el (EF.imp p q)) (PF.or (.ex fun x => .el (.neg (.or p (φ x))))
      (.all fun y => .el (.or q (φ y))))) := h3                                   -- [(3).(✱9·08)] (4)
  have h5 : Thm9 S (imp (.el (EF.imp p q)) (imp (.all fun x => .el (.or p (φ x)))
      (.all fun y => .el (.or q (φ y))))) := h4                                   -- [(4).(✱9·01)] (5)
  h5                                                                             -- [(5).(✱9·04)]

/-- ✱9·501 `⊢ :: p ⊃ q . ⊃ :. p . ∨ . (∃x) . φx : ⊃ : q . ∨ . (∃x) . φx` [As above]: the roles of the
    two quantifiers exchanged, (x) for the antecedent's x and ✱9·1 for the consequent's. -/
theorem f9_501 (φ : V τ → EF V) (p q : EF V) :
    Thm9 S (imp (.el (EF.imp p q)) (imp (PF.or (.el p) (Ex φ)) (PF.or (.el q) (Ex φ)))) :=
  have h1 : ∀ x, Thm9 S (.el (EF.imp (EF.imp p q) (EF.imp (.or p (φ x)) (.or q (φ x))))) :=
    fun x => e2_38 (φ x) p q                                                     -- ✱1·6 (1)
  have h2 : ∀ x, Thm9 S (imp (.el (EF.imp p q))
      (.ex fun y => .el (EF.imp (.or p (φ x)) (.or q (φ y))))) :=
    fun x => exI (φ := fun y => .el (EF.imp (EF.imp p q) (EF.imp (.or p (φ x)) (.or q (φ y))))) x
      (h1 x)                                                                     -- (1).✱9·1.(✱9·06) (2)
  have h3 : Thm9 S (imp (.el (EF.imp p q)) (.all fun x => .ex fun y =>
      .el (EF.imp (.or p (φ x)) (.or q (φ y))))) := Thm9.gen h2                  -- (2).✱9·13.(✱9·04) (3)
  have h4 : Thm9 S (imp (.el (EF.imp p q)) (PF.or (.all fun x => .el (.neg (.or p (φ x))))
      (.ex fun y => .el (.or q (φ y))))) := h3                                    -- [(3).(✱9·03·06)] (4)
  have h5 : Thm9 S (imp (.el (EF.imp p q)) (imp (.ex fun x => .el (.or p (φ x)))
      (.ex fun y => .el (.or q (φ y))))) := h4                                    -- [(4).(✱9·02)] (5)
  h5                                                                             -- [(5).(✱9·06)]

/-- ✱9·51 `⊢ :: p . ⊃ . (x) . φx : ⊃ :. p ∨ r . ⊃ : (x) . φx . ∨ . r` (p. 141). Line (1) is cited as
    ✱1·6; it is ✱2·38. -/
theorem f9_51 (φ : V τ → EF V) (p r : EF V) :
    Thm9 S (imp (imp (.el p) (Al φ)) (imp (.el (.or p r)) (PF.or (Al φ) (.el r)))) :=
  have h1 : ∀ x, Thm9 S (.el (EF.imp (EF.imp p (φ x)) (EF.imp (.or p r) (.or (φ x) r)))) :=
    fun x => e2_38 r p (φ x)                                                     -- ✱1·6 (1)
  have h2 : Thm9 S (imp (.all fun x => .el (EF.imp p (φ x)))
      (.all fun x => .el (EF.imp (.or p r) (.or (φ x) r)))) :=
    Thm9.mp (Thm9.gen h1)
      (f9_21 (fun x => EF.imp p (φ x)) fun x => EF.imp (.or p r) (.or (φ x) r))   -- (1).✱9·13·21 (2)
  h2                                                                             -- (2).(✱9·03·04)

/-- ✱9·511 `⊢ :: p . ⊃ . (∃x) . φx : ⊃ :. p ∨ r . ⊃ : (∃x) . φx . ∨ . r` [As above] -/
theorem f9_511 (φ : V τ → EF V) (p r : EF V) :
    Thm9 S (imp (imp (.el p) (Ex φ)) (imp (.el (.or p r)) (PF.or (Ex φ) (.el r)))) :=
  have h1 : ∀ x, Thm9 S (.el (EF.imp (EF.imp p (φ x)) (EF.imp (.or p r) (.or (φ x) r)))) :=
    fun x => e2_38 r p (φ x)                                                     -- ✱1·6 (1)
  have h2 : Thm9 S (imp (.ex fun x => .el (EF.imp p (φ x)))
      (.ex fun x => .el (EF.imp (.or p r) (.or (φ x) r)))) :=
    Thm9.mp (Thm9.gen h1)
      (f9_22 (fun x => EF.imp p (φ x)) fun x => EF.imp (.or p r) (.or (φ x) r))   -- (1).✱9·13·22 (2)
  h2                                                                             -- (2).(✱9·05·06)

/-- ✱9·52 `⊢ :: (x) . φx . ⊃ . q : ⊃ :. (x) . φx . ∨ . r : ⊃ . q ∨ r` (p. 142). Line (1) is cited as
    ✱1·6; it is ✱2·38. -/
theorem f9_52 (φ : V τ → EF V) (q r : EF V) :
    Thm9 S (imp (imp (Al φ) (.el q)) (imp (PF.or (Al φ) (.el r)) (.el (.or q r)))) :=
  have h1 : ∀ x, Thm9 S (.el (EF.imp (EF.imp (φ x) q) (EF.imp (.or (φ x) r) (.or q r)))) :=
    fun x => e2_38 r (φ x) q                                                     -- ✱1·6 (1)
  have h2 : Thm9 S (imp (.ex fun x => .el (EF.imp (φ x) q))
      (.ex fun x => .el (EF.imp (.or (φ x) r) (.or q r)))) :=
    Thm9.mp (Thm9.gen h1)
      (f9_22 (fun x => EF.imp (φ x) q) fun x => EF.imp (.or (φ x) r) (.or q r))   -- (1).✱9·13·22 (2)
  have h3 : Thm9 S (imp (imp (Al φ) (.el q))
      (imp (.all fun x => .el (.or (φ x) r)) (.el (.or q r)))) := h2              -- (2).(✱9·05·01) (3)
  h3                                                                             -- (3).(✱9·03)

/-- ✱9·521 `⊢ :: (∃x) . φx . ⊃ . q : ⊃ :. (∃x) . φx . ∨ . r : ⊃ . q ∨ r` [As above] -/
theorem f9_521 (φ : V τ → EF V) (q r : EF V) :
    Thm9 S (imp (imp (Ex φ) (.el q)) (imp (PF.or (Ex φ) (.el r)) (.el (.or q r)))) :=
  have h1 : ∀ x, Thm9 S (.el (EF.imp (EF.imp (φ x) q) (EF.imp (.or (φ x) r) (.or q r)))) :=
    fun x => e2_38 r (φ x) q                                                     -- ✱1·6 (1)
  have h2 : Thm9 S (imp (.all fun x => .el (EF.imp (φ x) q))
      (.all fun x => .el (EF.imp (.or (φ x) r) (.or q r)))) :=
    Thm9.mp (Thm9.gen h1)
      (f9_21 (fun x => EF.imp (φ x) q) fun x => EF.imp (.or (φ x) r) (.or q r))   -- (1).✱9·13·21 (2)
  have h3 : Thm9 S (imp (imp (Ex φ) (.el q))
      (imp (.ex fun x => .el (.or (φ x) r)) (.el (.or q r)))) := h2               -- (2).(✱9·06·02) (3)
  h3                                                                             -- (3).(✱9·05)

/-! ## ✱10's primitive propositions, proved by ✱9's method

  "✱10·1 is ✱9·2, ✱10·11 is ✱9·13, ✱10·12 is ✱9·25" (p. 144). Here they are stated for every function
  φ, with or without apparent variables, as the alternative method takes them; ✱10·12 for an
  elementary p (for every p it is proved given ✱1·2–✱1·6 for every proposition and a variable of every
  type: `Rep.distrib`, PM/Found9/FromStar10.lean). ✱10·121 and ✱10·122 are ✱9·14 and ✱9·15, built
  into the syntax. -/

/-- ✱10·1 `⊢ : (x) . φx . ⊃ . φy` [✱9·2], for every function φ. -/
theorem f10_1 (φ : V τ → PF V) (y : V τ) : Thm9 S (imp (.all φ) (φ y)) := inst φ y

/-- ✱10·11 "If φy is true whatever possible argument y may be, then (x) . φx is true." [✱9·13] -/
theorem f10_11 {φ : V τ → PF V} (h : ∀ y, Thm9 S (φ y)) : Thm9 S (.all φ) := Thm9.gen h

/-- ✱10·12 `⊢ :. (x) . p ∨ φx . ⊃ : p . ∨ . (x) . φx` [✱9·25], for an elementary p and every
    function φ. -/
theorem f10_12 (p : EF V) (φ : V τ → PF V) :
    Thm9 S (imp (.all fun x => PF.or (.el p) (φ x)) (PF.or (.el p) (.all φ))) := distribEl p φ

/-- ✱10·01, read as a theorem: "This definition is only to be used when we discard the method of ✱9
    in favour of the alternative method already explained. In either case we have
    `⊢ : (∃x) . φx . ≡ . ∼(x) . ∼φx`." (p. 145). For elementary φ, as in ✱9. By ✱9·01,
    ∼(x) . ∼φx is (∃x) . ∼∼φx; PM gives no proof. Lean's: ✱2·12 and ✱2·14 joined by ✱3·2, then ✱9·1
    and ✱9·13 for each of the four apparent variables of the definitions' prenex form. -/
theorem f10_01 (φ : V τ → EF V) :
    Thm9 S (iff (Ex φ) (neg (.all fun x => .el (.neg (φ x))))) :=
  have h1 : ∀ x x' : V τ, Thm9 S (.el (EF.and (EF.imp (φ x) (.neg (.neg (φ x))))
      (EF.imp (.neg (.neg (φ x'))) (φ x')))) := fun x x' =>
    Thm9.mp (elift (t2_14 (.var "p")) (esub (φ x') (φ x') (φ x')))
      (Thm9.mp (elift (t2_12 (.var "p")) (esub (φ x) (φ x) (φ x)))
        (elift (t3_2 (.var "p") (.var "q"))
          (esub (EF.imp (φ x) (.neg (.neg (φ x)))) (EF.imp (.neg (.neg (φ x'))) (φ x'))
            (φ x))))                                                             -- ✱2·12.✱2·14.✱3·2
  have h2 : Thm9 S (.all fun x => .ex fun y => .all fun x' => .ex fun y' =>
      .el (EF.and (EF.imp (φ x) (.neg (.neg (φ y)))) (EF.imp (.neg (.neg (φ x'))) (φ y')))) :=
    Thm9.gen fun x => exI x (Thm9.gen fun x' => exI x' (h1 x x'))                -- ✱9·1·13
  h2                                                                             -- (✱9·01·02·05·06)

end PM.F9
