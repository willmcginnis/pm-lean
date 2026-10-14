import PM.Derived
/-!
  Kalmár-style completeness of PM's ✱1 system (stretch goal):

    `theorem complete (p : F) (h : p.isTaut = true) : Thm p`

  * `kalmar`: for a valuation `v` and a list `xs` containing the variables of `φ`, the literals
    `x^v` (`x` if `v x`, else `∼x`) prove `φ^v` (`φ` if true under `v`, else `∼φ`).
  * `elim`: if every assignment in `assignments xs` gives `Γ_v ⊢ φ`, then `⊢ φ`; one variable
    at a time is discharged by the case split ✱2·11 (`Pf.cases`).
  Only the rules of PM.Derived are used, so the result is an explicit `Thm` derivation, but it is
  not one that follows PM's own proofs. PM.Replay2 does not use this theorem; it is an independent
  check that the replayed system is complete for its truth-table semantics.
-/
namespace PM
open F Pf

/-! ## List lemmas, proved by hand so that nothing beyond the kernel is needed -/

section lists
variable {α : Type} {a : α}

theorem mem_append_left' {l₁ : List α} (l₂ : List α) : a ∈ l₁ → a ∈ l₁ ++ l₂
  | .head _ => .head _
  | .tail _ h => .tail _ (mem_append_left' l₂ h)

theorem mem_append_right' : ∀ (l₁ : List α) {l₂ : List α}, a ∈ l₂ → a ∈ l₁ ++ l₂
  | [], _, h => h
  | _ :: l₁, _, h => .tail _ (mem_append_right' l₁ h)

theorem mem_reverseAux : ∀ (l acc : List α), a ∈ l ∨ a ∈ acc → a ∈ List.reverseAux l acc
  | [], _, .inl h => nomatch h
  | [], _, .inr h => h
  | _ :: l, _, .inl (.head _) => mem_reverseAux l _ (.inr (.head _))
  | _ :: l, _, .inl (.tail _ h) => mem_reverseAux l _ (.inl h)
  | _ :: l, _, .inr h => mem_reverseAux l _ (.inr (.tail _ h))

theorem mem_of_any {a : String} : ∀ (l : List String), l.any (fun b => a == b) = true → a ∈ l
  | [], h => nomatch h
  | b :: l, h => by
    cases hb : (a == b)
    · rw [List.any_cons, hb] at h; exact .tail _ (mem_of_any l h)
    · rw [of_decide_eq_true hb]; exact .head _

theorem mem_loop {a : String} :
    ∀ (l acc : List String), a ∈ l ∨ a ∈ acc → a ∈ List.eraseDupsBy.loop (· == ·) l acc
  | [], acc, h => mem_reverseAux acc [] (match h with | .inl h => nomatch h | .inr h => .inl h)
  | x :: l, acc, h => by
    unfold List.eraseDupsBy.loop
    split
    · next hany =>
      apply mem_loop l acc
      match h with
      | .inl (.head _) => exact .inr (mem_of_any acc hany)
      | .inl (.tail _ h) => exact .inl h
      | .inr h => exact .inr h
    · apply mem_loop l (x :: acc)
      match h with
      | .inl (.head _) => exact .inr (.head _)
      | .inl (.tail _ h) => exact .inl h
      | .inr h => exact .inr (.tail _ h)

theorem mem_eraseDups' {a : String} {l : List String} (h : a ∈ l) : a ∈ l.eraseDups :=
  mem_loop l [] (.inl h)

theorem mem_flatMap' {β : Type} {b : β} {f : α → List β} :
    ∀ {L : List α}, a ∈ L → b ∈ f a → b ∈ L.flatMap f
  | _ :: _, .head _, hb => mem_append_left' _ hb
  | c :: _, .tail _ h, hb => mem_append_right' (f c) (mem_flatMap' h hb)

theorem all_mem {f : α → Bool} : ∀ {l : List α}, l.all f = true → a ∈ l → f a = true
  | b :: l, h, hm => by
    cases hb : f b
    · rw [List.all_cons, hb] at h; exact nomatch h
    · rw [List.all_cons, hb] at h
      match hm with
      | .head _ => exact hb
      | .tail _ hm => exact all_mem h hm

end lists

/-! String-specific facts, proved from `String.decEq` (core's `LawfulBEq String` instance is not
    axiom-free, so it is avoided). -/

theorem mem_or_not (x : String) : ∀ xs : List String, x ∈ xs ∨ ¬ x ∈ xs
  | [] => .inr (fun h => nomatch h)
  | y :: ys => match String.decEq x y with
    | isTrue e => .inl (e ▸ .head _)
    | isFalse ne => match mem_or_not x ys with
      | .inl h => .inl (.tail _ h)
      | .inr h => .inr fun m => match m with
        | .head _ => ne rfl
        | .tail _ m => h m

/-! ## Kalmár's lemma -/

/-- `sgn b φ`: φ itself if `b`, else `∼φ`. -/
def sgn : Bool → F → F
  | true, φ => φ
  | false, φ => .neg φ

/-- The literal of variable `x` under `v`. -/
def lit (v : String → Bool) (x : String) : F := sgn (v x) (.var x)

/-- `lits v [x₁,…,xₙ] = [xₙ^v, …, x₁^v]` (the head variable is the last hypothesis). -/
def lits (v : String → Bool) : List String → List F
  | [] => []
  | x :: xs => lits v xs ++ [lit v x]

theorem mem_lits (v : String → Bool) {x : String} : ∀ {xs : List String}, x ∈ xs → lit v x ∈ lits v xs
  | _ :: xs, .head _ => mem_append_right' (lits v xs) (.head _)
  | _ :: _, .tail _ h => mem_append_left' _ (mem_lits v h)

/-- `∼a ⊃ (∼b ⊃ ∼(a ∨ b))` [✱2·01, ∨-elimination, ✱2·24]. -/
theorem not_or_intro (a b : F) : Thm (imp (.neg a) (imp (.neg b) (.neg (.or a b)))) := ofPf <| by
  intro_; intro_
  exact negI (orE (hy 2 rfl) (absurd _ (hy 3 rfl) (hy 0 rfl)) (absurd _ (hy 3 rfl) (hy 1 rfl)))

theorem kalmar (v : String → Bool) (xs : List String) :
    ∀ φ : F, (∀ s ∈ φ.vars, s ∈ xs) → Pf (lits v xs) (sgn (φ.eval v) φ) := by
  intro φ
  induction φ with
  | var s => intro h; exact hyp (mem_lits v (h s (.head _)))
  | neg ψ ih =>
    intro h
    have k := ih h
    show Pf _ (sgn (!(ψ.eval v)) (.neg ψ))
    cases e : ψ.eval v <;> rw [e] at k
    · exact k
    · exact dni k
  | or a b iha ihb =>
    intro h
    have ka := iha (fun s hs => h s (mem_eraseDups' (mem_append_left' _ hs)))
    have kb := ihb (fun s hs => h s (mem_eraseDups' (mem_append_right' _ hs)))
    show Pf _ (sgn (a.eval v || b.eval v) (.or a b))
    cases ea : a.eval v <;> cases eb : b.eval v <;> rw [ea] at ka <;> rw [eb] at kb
    · exact app2 (not_or_intro a b) ka kb
    · exact orIR kb
    · exact orIL ka
    · exact orIL ka

/-! ## Discharging the hypotheses -/

theorem lits_congr {w v : String → Bool} :
    ∀ (xs : List String), (∀ s ∈ xs, w s = v s) → lits w xs = lits v xs
  | [], _ => rfl
  | y :: ys, h => by
    show lits w ys ++ [sgn (w y) (.var y)] = lits v ys ++ [sgn (v y) (.var y)]
    rw [lits_congr ys (fun s hs => h s (.tail _ hs)), h y (.head _)]

/-- `if s == x then b else v s`, the update used by `assignments`. -/
theorem upd_other {v : String → Bool} {x s : String} (b : Bool) (hne : ¬ s = x) :
    (if s == x then b else v s) = v s := by
  cases e : (s == x)
  · rfl
  · exact absurd (of_decide_eq_true e) hne

theorem upd_self {v : String → Bool} {x s : String} {b : Bool} (hvx : v x = b) :
    (if s == x then b else v s) = v s := by
  cases e : (s == x)
  · rfl
  · show b = v s; rw [of_decide_eq_true e, hvx]

theorem elim (φ : F) :
    ∀ xs : List String, (∀ v, v ∈ assignments xs → Pf (lits v xs) φ) → Thm φ
  | [], h => h (fun _ => false) (.head _)
  | x :: xs, h => elim φ xs fun v hv => by
    have h0 := h (fun s => if s == x then false else v s) (mem_flatMap' hv (.head _))
    have h1 := h (fun s => if s == x then true else v s) (mem_flatMap' hv (.tail _ (.head _)))
    change Pf (lits _ xs ++ [lit _ x]) φ at h0 h1
    rcases mem_or_not x xs with hx | hx
    · -- `x` already has a literal in the context: use the assignment that agrees with `v`
      cases hvx : v x
      · rw [lits_congr xs (fun s _ => upd_self hvx), show lit _ x = lit v x from
          congrArg (sgn · _) (upd_self hvx)] at h0
        exact mp (hyp (mem_lits v hx)) (intro h0)
      · rw [lits_congr xs (fun s _ => upd_self hvx), show lit _ x = lit v x from
          congrArg (sgn · _) (upd_self hvx)] at h1
        exact mp (hyp (mem_lits v hx)) (intro h1)
    · -- `x` is new: case split on it (✱2·11)
      have ne : ∀ s ∈ xs, ¬ s = x := fun s hs e => hx (e ▸ hs)
      rw [lits_congr xs (fun s hs => upd_other _ (ne s hs))] at h0 h1
      have e1 : lit (fun s => if s == x then true else v s) x = .var x := by
        show sgn (if x == x then true else v x) _ = _; rw [show (x == x) = true from decide_eq_true rfl]; rfl
      have e0 : lit (fun s => if s == x then false else v s) x = .neg (.var x) := by
        show sgn (if x == x then false else v x) _ = _; rw [show (x == x) = true from decide_eq_true rfl]; rfl
      rw [e1] at h1; rw [e0] at h0
      exact Pf.cases (.var x) h1 h0

/-- **Completeness**: every truth-table tautology is a theorem of PM's ✱1 system. -/
theorem complete (p : F) (h : p.isTaut = true) : Thm p :=
  elim p p.vars.eraseDups fun v hv => by
    have k := kalmar v p.vars.eraseDups p (fun _ hs => mem_eraseDups' hs)
    rw [all_mem h hv] at k
    exact k

end PM
