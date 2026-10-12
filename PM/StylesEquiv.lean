import PM.Pred.Styles
/-!
  `styles_equiv` (Will, 2026-10-11 evening, item (i)): with the axiom of reducibility, the styles of
  predicativity derive exactly the same theorems.

  The styles differ only in which formulas comprehension accepts (PM/Pred/). With ✱12·1 / ✱12·11 every
  use of comprehension in one style can be replayed in another:
  - at a predicative type (`fn1 a 0`, `fn2 a b 0`) the conclusion of comprehension is literally ✱12·1
    (✱12·11), which has no side condition;
  - at a non-predicative type (`fn1 a (k+1)`), ✱12·1 gives a predicative g with ψx ≡ₓ g!x, and every
    style admits g!x at `fn1 a (k+1)` (`Style.AdmitsPredApp`), so comprehension in the target style gives
    an f with g!x ≡ₓ f x; ✱10·301 (✱11·371 for two arguments) joins the two equivalences.
  The proof is an induction over derivations (`restyle`). It USES ✱12·1 and ✱12·11: it takes
  `[Reducibility S']`, and RedCheck.lean reports that it reaches `Reducibility.red`.

  Without reducibility the matrix style admits less (`QThm.matrix_to_lowestOrder`, and the golden tests
  of PM/Pred/Styles.lean). That it then derives strictly fewer theorems (e.g. that `p171` is not a
  theorem of the matrix-style predicative fragment) is NOT proved here: it needs a model that sees
  orders (test F4 of docs/TYPES_DESIGN.md), which the collapse and finite models do not. Skipped.
-/
namespace PM
open QF

variable {V : Ty → Type}

/-- ✱10 bookkeeping: from (∃g) . E g, (g) : (∃f) . T(g, f), and E g . ⊃ : T(g, f) . ⊃ . E' f for all g, f,
    infer (∃f) . E' f. The steps of `q12_1_of_var`: ✱10·11·21, ✱10·28, Comm, ✱10·11·23. -/
theorem qex_chain {S : Sys} {σ ρ : Ty} {E : V σ → QF V} {T : V σ → V ρ → QF V} {E' : V ρ → QF V}
    (hE : QThm S (ex E)) (hT : ∀ g, QThm S (ex (T g)))
    (hstep : ∀ g f, QThm S (imp (E g) (imp (T g f) (E' f)))) : QThm S (ex E') :=
  have step : ∀ g, QThm S (imp (E g) (ex E')) := fun g =>
    have h2 := qsyl (q10_11_21 (hstep g)) (q10_28 _ _)                       -- ✱10·11·21 . ✱10·28
    QThm.mp (hT g) (QThm.mp h2 (QL.t2_04 _ _ _))                             -- Comm
  QThm.mp hE (QThm.mp (q10_11 step) (qiffMp (q10_23 _ (ex E'))))             -- ✱10·11·23

/-- A style admits g!x at every non-predicative type `fn1 a (k+1)` when g is predicative (and likewise
    for two arguments). Every style here does (`admitsPredApp_of`). -/
structure Style.AdmitsPredApp (st : Style) : Prop where
  app1 : ∀ {V : Ty → Type} {a : Ty} {k : Nat} (g : V (Ty.pred1 a)), st.adm1 (k + 1) fun x => .app1 g x
  app2 : ∀ {V : Ty → Type} {a b : Ty} {k : Nat} (g : V (Ty.pred2 a b)),
    st.adm2 (k + 1) fun x y => .app2 g x y

/-- Replay a derivation of one system in another that has reducibility, at least the same comprehension,
    and a style that admits predicative applications at non-predicative types. -/
theorem restyle {S S' : Sys} [Reducibility S'] (hc : S.compr = true → S'.compr = true)
    (hst : S'.style.AdmitsPredApp) {p : QF V} (h : QThm S p) : QThm S' p := by
  induction h with
  | mp _ _ ih1 ih2 => exact .mp ih1 ih2
  | taut p => exact .taut p
  | add p q => exact .add p q
  | perm p q => exact .perm p q
  | assoc p q r => exact .assoc p q r
  | sum p q r => exact .sum p q r
  | inst φ y => exact .inst φ y
  | gen _ ih => exact .gen ih
  | distrib p φ => exact .distrib p φ
  | red1 _ φ => exact .red1 Reducibility.red φ
  | red2 _ φ => exact .red2 Reducibility.red φ
  | @compr1 a k hS ψ _ =>
    cases k with
    | zero => exact .red1 Reducibility.red ψ                                    -- ✱12·1
    | succ k =>
      exact qex_chain (E := fun g => fiff ψ fun x => .app1 g x)
        (T := fun g f => fiff (fun x => .app1 g x) fun x => .app1 f x)
        (.red1 Reducibility.red ψ)                                              -- ✱12·1
        (fun g => .compr1 (hc hS) _ (hst.app1 g))                               -- comprehension
        (fun g f => QThm.mp (q10_301 ψ (fun x => .app1 g x) (fun x => .app1 f x)) (QL.t3_3 _ _ _))
  | @compr2 a b k hS ψ _ =>
    cases k with
    | zero => exact .red2 Reducibility.red ψ                                    -- ✱12·11
    | succ k =>
      exact qex_chain (E := fun g => fiff2 ψ fun x y => .app2 g x y)
        (T := fun g f => fiff2 (fun x y => .app2 g x y) fun x y => .app2 f x y)
        (.red2 Reducibility.red ψ)                                              -- ✱12·11
        (fun g => .compr2 (hc hS) _ (hst.app2 g))                               -- comprehension
        (fun g f => QThm.mp (q11_371 ψ (fun x y => .app2 g x y) (fun x y => .app2 f x y))
          (QL.t3_3 _ _ _))

private theorem le_succ_excess (n k : Nat) : n + 0 ≤ n + (k + 1) :=
  Nat.add_le_add_left (Nat.zero_le _) n

private theorem lt_succ_excess (n k : Nat) : n + 0 < n + (k + 1) :=
  Nat.add_lt_add_left (Nat.succ_pos k) n

/-- Every style here admits predicative applications at non-predicative types. -/
theorem admitsPredApp_of (P : PredReading) (R : RealReading) : (Style.of P R).AdmitsPredApp := by
  cases P <;> cases R
  · exact ⟨fun _ _ => ⟨.app1 (le_succ_excess _ _), fun h => nomatch h⟩,
      fun _ _ _ => ⟨.app2 (le_succ_excess _ _), fun h => nomatch h⟩⟩
  · exact ⟨fun _ _ => ⟨.app1 (lt_succ_excess _ _), fun h => nomatch h⟩,
      fun _ _ _ => ⟨.app2 (lt_succ_excess _ _), fun h => nomatch h⟩⟩
  · exact ⟨fun _ _ => .app1 (le_succ_excess _ _), fun _ _ _ => .app2 (le_succ_excess _ _)⟩
  · exact ⟨fun _ _ => .app1 (lt_succ_excess _ _), fun _ _ _ => .app2 (lt_succ_excess _ _)⟩

/-- **styles_equiv.** With reducibility, the styles of predicativity derive exactly the same theorems:
    for either setting of comprehension `c`, any two of the four styles `Style.of P R` (matrix or lowest
    order; a real function variable at its own order, p. 55, or as an argument, p. 54) have the same
    `QThm`. -/
theorem styles_equiv (c : Bool) (P P' : PredReading) (R R' : RealReading) (p : QF V) :
    QThm (⟨c, true, Style.of P R⟩ : Sys) p ↔ QThm (⟨c, true, Style.of P' R'⟩ : Sys) p :=
  ⟨restyle (S := ⟨c, true, Style.of P R⟩) (S' := ⟨c, true, Style.of P' R'⟩) id (admitsPredApp_of P' R'),
   restyle (S := ⟨c, true, Style.of P' R'⟩) (S' := ⟨c, true, Style.of P R⟩) id (admitsPredApp_of P R)⟩

/-- The case the maintainer asked for (Q1): in PM 1910 as built here (`Sys.full`), the matrix style and the
    lowest-order style derive the same theorems. -/
theorem styles_equiv_full (R : RealReading) (p : QF V) :
    QThm (Sys.full (Style.of .matrix R)) p ↔ QThm (Sys.full (Style.of .lowestOrder R)) p :=
  styles_equiv true .matrix .lowestOrder R R p

/-- The sibling for Q3: in `Sys.full`, the p. 55 reading (a real function variable at its own order) and
    the p. 54 reading (as an argument) derive the same theorems. -/
theorem styles_equiv_real (P : PredReading) (p : QF V) :
    QThm (Sys.full (Style.of P .ownOrder)) p ↔ QThm (Sys.full (Style.of P .asArgument)) p :=
  styles_equiv true P P .ownOrder .asArgument p

end PM
