import PM.Found9.Star9
/-!
  Switch: Landini's rule of ✱9+ (reading L) and our earlier prenex Switch (docs/REPAIRS.md, R3, R5).
  Russell's ✱8·13 carried over (reading C), and how it relates to both: PM/Found9/Exch.lean.

  Landini's Switch (`Thm9.switch`, PM/Found9/System.lean): from ⊢ B[(x)(∃y)A] infer ⊢ B[(∃y)(x)A],
  where A joins a part with x and a part with y by a connective (`Sep`, `SwitchStep`).
  - `switch_converse`: the converse, from B[(∃y)(x)A] to B[(x)(∃y)A], in ✱9+ without Switch: ✱9·yy and
    ✱9·zz make (∃y) : (x) . A . ⊃ . (x) : (∃y) . A a proposition that ✱9·13 and ✱9·1 prove, and ✱9·21,
    ✱9·22 as rules carry it inside B. Landini derives this rule, dr(S*), from Switch, his T1 and MP2
    (2000, §5); here Switch is not needed for it, because B is the quantifiers in front.
  - `switch_here_prenex`: a step of Switch at the front of a proposition is a step of the prenex
    Switch (both (x)(∃y)A and (∃y)(x)A are prenex forms of (x) . A₁x . ∨ . (∃y) . A₂y).

  The prenex Switch (`Thm9.prenexSwitch`, opt-in by `R.prenex`): if X and Y are two prenex forms of the
  same expression t, from ⊢ X infer ⊢ Y. The quantifiers of different disjuncts may be taken out in
  another order; each disjunct's quantifiers keep their own order, and no quantifier passes one in whose
  scope it stands. It differs from Landini's Switch in four ways (docs/REPAIRS.md, R5): it goes both
  ways; it also exchanges two quantifiers of the same kind; it moves a quantifier past several at once;
  and it reorders the quantifiers of the disjuncts of a nested expression, which Landini's moves only
  where the parts are joined at the matrix. Whether ✱9+ derives it is open.
  - `Thm9.toSwitch`: with the prenex Switch, every theorem of the definitions as printed (without
    ✱8·13; with it, `Thm9.russell_toPrenex`, PM/Found9/Exch.lean) or of the alternative convention is
    a theorem, the same proposition. `Thm9.reread` carries a theorem about an
    expression from the proposition one reading's definitions make of it to the proposition another's
    make.
  - `distrib_switch`: ✱10·12 (= ✱9·25) for every p and every function, with the prenex Switch, without
    `Rep`.
  - `PE.readU`: the prenex form of an expression that takes the universal quantifiers out as early as
    possible (`prenex_readU`); PM/Found9/Simul.lean uses it for the prenex Switch.

  Soundness of both rules, and their derivation by ✱10's method: PM/Found9/ToStar10.lean
  (`switchStep_q10`, `switch_q10`) and PM/Found9/Equiv.lean.
-/
namespace PM.F9
open PF

variable {V : Ty → Type} {S : Sys}

/-! ## Landini's Switch: its converse, and its relation to the prenex Switch -/

/-- The converse of a step of Switch, as a proposition of ✱9+: ⊢ (∃y) : (x) . A . ⊃ . (x) : (∃y) . A
    inside the same quantifiers, without Switch. -/
theorem switch_converse_imp (pr : Rule) {X Y : PF V} (h : SwitchStep X Y) :
    Thm9 S ⟨.plus, pr⟩ (Reading.imp ⟨.plus, pr⟩ Y X) := by
  induction h with
  | here _ => exact Thm9.gen fun y => Thm9.gen fun x' => exI x' (exI y (idt_plus pr _))
  | all _ ih => exact allImp ih
  | ex _ ih => exact exImp_plus ih

/-- dr(S*): from ⊢ B[(∃y)(x)A] infer ⊢ B[(x)(∃y)A], in ✱9+ without Switch. With Switch, ✱9+ has both
    directions of the exchange of (x) and (∃y), which Russell's rule ✱8·13 gives in ✱8 of the second
    edition; the exchanges of two quantifiers of the same kind are in PM/Found9/Exch.lean
    (`exch_plus`). -/
theorem switch_converse (pr : Rule) {X Y : PF V} (h : SwitchStep X Y)
    (hY : Thm9 S ⟨.plus, pr⟩ Y) : Thm9 S ⟨.plus, pr⟩ X :=
  Thm9.mp hY (switch_converse_imp pr h)

/-- A step of Switch at the front of a proposition is a step of the prenex Switch: (x) : (∃y) . A and
    (∃y) : (x) . A are prenex forms of the same expression. -/
theorem switch_here_prenex {τ σ : Ty} {Z : V τ → V σ → PF V} (h : Sep Z) :
    ∃ t : PE V, Prenex t (.all fun x => .ex fun y => Z x y) ∧
      Prenex t (.ex fun y => .all fun x => Z x y) := by
  cases h with
  | left L R hm =>
    exact ⟨.or (.all fun x => .pf (L x)) (.ex fun y => .pf (R y)),
      .or (.all fun x => .pf _) (.ex fun y => .pf _) (.allL fun x => .exR fun y => hm x y),
      .or (.all fun x => .pf _) (.ex fun y => .pf _) (.exR fun y => .allL fun x => hm x y)⟩
  | right L R hm =>
    exact ⟨.or (.ex fun y => .pf (R y)) (.all fun x => .pf (L x)),
      .or (.ex fun y => .pf _) (.all fun x => .pf _) (.allR fun x => .exL fun y => hm x y),
      .or (.ex fun y => .pf _) (.all fun x => .pf _) (.exL fun y => .allR fun x => hm x y)⟩

/-! ## Prenex forms of compound expressions -/

theorem Prenex.disj (d : Defs) {s t : PE V} {X Y : PF V} (hs : Prenex s X) (ht : Prenex t Y) :
    Prenex (.or s t) (PF.disj d X Y) :=
  .or hs ht (merge_disj d X Y)

theorem Prenex.imp (R : Reading) {s t : PE V} {X Y : PF V} (hs : Prenex s X) (ht : Prenex t Y) :
    Prenex (PE.imp s t) (R.imp X Y) :=
  Prenex.disj R.defs (.neg hs) ht

theorem Prenex.iff (R : Reading) {s t : PE V} {X Y : PF V} (hs : Prenex s X) (ht : Prenex t Y) :
    Prenex (PE.iff s t) (R.iff X Y) :=
  .neg (Prenex.disj R.defs (.neg (Prenex.imp R hs ht)) (.neg (Prenex.imp R ht hs)))

/-- The proposition for which a ✱10 formula stands is a prenex form of its expression. -/
theorem prenex_toF9 (d : Defs) : ∀ q : QF V, Prenex q.toPE (q.toF9 d)
  | .atom _ _ => .pf _
  | .app1 _ _ => .pf _
  | .app2 _ _ _ => .pf _
  | .neg p => .neg (prenex_toF9 d p)
  | .or p q => Prenex.disj d (prenex_toF9 d p) (prenex_toF9 d q)
  | .all φ => .all fun x => prenex_toF9 d (φ x)

/-! ## With the prenex Switch, every reading's theorems -/

/-- With the prenex Switch, every theorem of a reading `R` without Switch and without ✱8·13 (the
    definitions as printed or the alternative convention) is a theorem of the reading `⟨d, .prenex⟩`,
    for any definitions `d`: each primitive proposition of `R` is a prenex form of the expression of
    which the corresponding primitive proposition of `⟨d, .prenex⟩` is another, and the prenex Switch
    passes between them. -/
theorem Thm9.toSwitch {R : Reading} (hR : R.defs ≠ .plus) (hE : R.rule ≠ .exch) (d : Defs) {p : PF V}
    (h : Thm9 S R p) : Thm9 S ⟨d, .prenex⟩ p := by
  let R' : Reading := ⟨d, .prenex⟩
  induction h with
  | mp _ _ ih1 ih2 =>
    exact Thm9.mp (R := R') ih1 (Thm9.prenexSwitch rfl (Prenex.imp _ (.pf _) (.pf _))
      (Prenex.imp R' (.pf _) (.pf _)) ih2)
  | taut p => exact Thm9.taut p
  | add p q => exact Thm9.add p q
  | perm p q => exact Thm9.perm p q
  | assoc p q r => exact Thm9.assoc p q r
  | sum p q r => exact Thm9.sum p q r
  | ex1 φ x =>
    exact Thm9.prenexSwitch rfl (Prenex.imp R' (.pf _) (.pf _)) (Prenex.imp _ (.pf _) (.pf _))
      (Thm9.ex1 (R := R') φ x)
  | ex2 φ x y =>
    exact Thm9.prenexSwitch rfl (Prenex.imp R' (Prenex.disj R'.defs (.pf _) (.pf _)) (.pf _))
      (Prenex.imp _ (Prenex.disj _ (.pf _) (.pf _)) (.pf _)) (Thm9.ex2 (R := R') φ x y)
  | gen _ ih => exact Thm9.gen ih
  | compr1 hS ψ hψ =>
    exact Thm9.prenexSwitch rfl
      (.ex fun _ => .all fun x => Prenex.iff R' (prenex_toF9 d (ψ x)) (.pf _))
      (.ex fun _ => .all fun x => Prenex.iff _ (prenex_toF9 _ (ψ x)) (.pf _))
      (Thm9.compr1 (R := R') hS ψ hψ)
  | compr2 hS ψ hψ =>
    exact Thm9.prenexSwitch rfl
      (.ex fun _ => .all fun x => .all fun y => Prenex.iff R' (prenex_toF9 d (ψ x y)) (.pf _))
      (.ex fun _ => .all fun x => .all fun y => Prenex.iff _ (prenex_toF9 _ (ψ x y)) (.pf _))
      (Thm9.compr2 (R := R') hS ψ hψ)
  | red1 hS φ =>
    exact Thm9.prenexSwitch rfl (.ex fun _ => .all fun _ => Prenex.iff R' (.pf _) (.pf _))
      (.ex fun _ => .all fun _ => Prenex.iff _ (.pf _) (.pf _)) (Thm9.red1 (R := R') hS φ)
  | red2 hS φ =>
    exact Thm9.prenexSwitch rfl (.ex fun _ => .all fun _ => .all fun _ => Prenex.iff R' (.pf _) (.pf _))
      (.ex fun _ => .all fun _ => .all fun _ => Prenex.iff _ (.pf _) (.pf _))
      (Thm9.red2 (R := R') hS φ)
  | exch h => exact absurd h hE
  | switch h => exact absurd h hR
  | prenexSwitch _ hX hY _ ih => exact Thm9.prenexSwitch rfl hX hY ih

/-- With the prenex Switch, a theorem about an expression t under one reading's definitions (as
    printed or the alternative convention) gives the proposition another reading's definitions make of
    t. -/
theorem Thm9.reread {R : Reading} (hR : R.defs ≠ .plus) (hE : R.rule ≠ .exch) (t : PE V)
    (h : Thm9 S R (t.read R.defs)) (d : Defs) : Thm9 S ⟨d, .prenex⟩ (t.read d) :=
  Thm9.prenexSwitch rfl (prenex_read R.defs t) (prenex_read d t) (h.toSwitch hR hE d)

/-- Every theorem of the alternative convention (B) is a theorem of the definitions as printed with
    the prenex Switch, the same proposition. -/
theorem Thm9.convention_toSwitch {p : PF V} (h : Thm9 S Reading.convention p) :
    Thm9 S Reading.prenexSwitch p :=
  Thm9.toSwitch (R := Reading.convention) nofun nofun .printed h

/-! ## ✱10·12 for every p, with the prenex Switch -/

/-- The expression `(x) . p ∨ φx . ⊃ : p . ∨ . (x) . φx` of ✱9·25 (= ✱10·12). -/
def distribExpr {τ : Ty} (p : PF V) (φ : V τ → PF V) : PE V :=
  PE.imp (.all fun x => .or (.pf p) (.pf (φ x))) (.or (.pf p) (.pf (.all φ)))

/-- ✱9·25 (= ✱10·12) `⊢ :. (x) . p ∨ φx . ⊃ : p . ∨ . (x) . φx` for every p and every function φ, under
    the definitions as printed with the prenex Switch, without `Rep`: the alternative convention proves
    it (`distrib_convention`), and the prenex Switch takes it to the proposition the definitions as
    printed make of it. -/
theorem distrib_switch (p : PF V) {τ : Ty} (φ : V τ → PF V) :
    Thm9 S Reading.prenexSwitch
      (Reading.prenexSwitch.imp (.all fun x => Reading.prenexSwitch.or p (φ x))
        (Reading.prenexSwitch.or p (.all φ))) :=
  Thm9.reread (R := Reading.convention) nofun nofun (distribExpr p φ)
    (distrib_convention (sw := .basic) p φ) .printed

/-! ## Universal quantifiers first -/

/-- Disjunction with the existential quantifiers out first: of the two fronts, an existential before
    a universal, and of two of the same kind the left one first (the dual of `PF.or`). -/
def orE : PF V → PF V → PF V
  | .el a, q => PF.orEl a q
  | .ex φ, q => .ex fun x => orE (φ x) q
  | .all φ, q => orEA (fun x q' => orE (φ x) q') q
where
  /-- (x) . φx . ∨ . q with an existential at the front of q first, given `r x q` = φx ∨ q. -/
  orEA {τ : Ty} (r : V τ → PF V → PF V) : PF V → PF V
    | .ex ψ  => .ex fun y => orEA r (ψ y)
    | .el b  => .all fun x => r x (.el b)
    | .all ψ => .all fun x => r x (.all ψ)

theorem merge_orEA {τ : Ty} (φ : V τ → PF V) (ih : ∀ x Y, Merge (φ x) Y (orE (φ x) Y)) :
    ∀ Y : PF V, Merge (.all φ) Y (orE.orEA (fun x q => orE (φ x) q) Y)
  | .ex ψ  => .exR fun y => merge_orEA φ ih (ψ y)
  | .el b  => .allL fun x => ih x (.el b)
  | .all ψ => .allL fun x => ih x (.all ψ)

theorem merge_orE : ∀ X Y : PF V, Merge X Y (orE X Y)
  | .el a, Y => merge_orEl a Y
  | .ex φ, Y => .exL fun x => merge_orE (φ x) Y
  | .all φ, Y => merge_orEA φ (fun x => merge_orE (φ x)) Y

mutual
/-- The prenex form of an expression with its universal quantifiers out as early as possible. -/
def PE.readU : PE V → PF V
  | .pf X   => X
  | .all t  => .all fun x => (t x).readU
  | .ex t   => .ex fun x => (t x).readU
  | .neg t  => PF.neg t.readE
  | .or s t => PF.or s.readU t.readU
/-- The prenex form of an expression with its existential quantifiers out as early as possible. -/
def PE.readE : PE V → PF V
  | .pf X   => X
  | .all t  => .all fun x => (t x).readE
  | .ex t   => .ex fun x => (t x).readE
  | .neg t  => PF.neg t.readU
  | .or s t => orE s.readE t.readE
end

mutual
theorem prenex_readU : ∀ t : PE V, Prenex t t.readU
  | .pf X => .pf X
  | .all t => .all fun x => prenex_readU (t x)
  | .ex t => .ex fun x => prenex_readU (t x)
  | .neg t => .neg (prenex_readE t)
  | .or s t => .or (prenex_readU s) (prenex_readU t) (merge_or _ _)
theorem prenex_readE : ∀ t : PE V, Prenex t t.readE
  | .pf X => .pf X
  | .all t => .all fun x => prenex_readE (t x)
  | .ex t => .ex fun x => prenex_readE (t x)
  | .neg t => .neg (prenex_readU t)
  | .or s t => .or (prenex_readE s) (prenex_readE t) (merge_orE _ _)
end

/-- With the prenex Switch, an expression whose universal-first prenex form is a theorem: the
    proposition the definitions as printed make of it. -/
theorem Thm9.ofReadU (t : PE V) (h : Thm9 S Reading.prenexSwitch t.readU) :
    Thm9 S Reading.prenexSwitch (t.read .printed) :=
  Thm9.prenexSwitch rfl (prenex_readU t) (prenex_read .printed t) h

end PM.F9
