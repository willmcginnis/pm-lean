import PM.Replay
import PM.Derived
/-!
  Replay, part 2: the propositions of ✱2–✱5 left UNRESOLVED by the first replay, and the
  FAITHFUL/REPAIRED ones that depended on them. Each theorem is an explicit `Thm` derivation built from
  the primitive propositions, earlier `t…` theorems and the derived rules of PM.Derived. Proofs named
  `ofPf` are natural-deduction derivations; `hy n` is the n-th hypothesis, and `intro_` is the
  deduction theorem (definitional; see PM.Derived).

  Proofs written as `have` lines follow PM's own Dem. (or, where PM prints only a bracketed hint, the
  propositions of the hint in PM's order), one Lean line per PM line; the comment above each line is
  PM's line. Every proposition such a proof cites appears literally (`tX_Y`, `Thm.perm`, …). The only
  steps PM leaves tacit that are done by helpers are:
  * ✱1·1 / ✱1·11 (`Thm.mp`); the definitions ✱1·01, ✱3·01, ✱4·01 (definitional in Lean);
  * ✱3·03, joining two asserted propositions (`andIh`, and `iffIh` for `≡`);
  * Syll in PM's `⊃`-chains `⊢ : a . ⊃ . b : ⊃ . c`, and for a bracketed citation `[✱x·y]` applied to the
    consequent or antecedent of the previous line (`syl`, `sylEnd`, `sylMid`: ✱2·05, ✱2·06);
  * an asserted equivalence used in either direction, and PM's `≡`-chains (`iffMph`, `iffMprh`,
    `iffSymmh`, `iffTransh`).
  Any other proposition PM does not cite is marked `extra` in the docstring, with the reason; the
  same information is in data/replay2_ledger.json.
-/
namespace PM
open F Pf

/-- *2.64 — [✱1·4, ✱2·63 (q,p/p,q)] -/
theorem t2_64 (p : F) (q : F) : Thm (s2_64 p q) :=
  syl (Thm.perm p q) (sylMid (t2_63 q p) (Thm.perm p (.neg q)))

/-- *2.65 — [✱2·64 (∼p/p)] -/
theorem t2_65 (p : F) (q : F) : Thm (s2_65 p q) := t2_64 (.neg p) q

/-- *2.69 — [✱2·68, ✱1·4, ✱2·62 (q,p/p,q)] -/
theorem t2_69 (p : F) (q : F) : Thm (s2_69 p q) :=
  syl (syl (t2_68 p q) (Thm.perm p q)) (t2_62 q p)

/-- *2.73 — [✱2·621, ✱2·38] -/
theorem t2_73 (p : F) (q : F) (r : F) : Thm (s2_73 p q r) := pm2_73 p q r

/-- *2.74 — PM: [✱2·73 (q,p/p,q) . Assoc . Syll].
    extra ✱2·31, ✱2·32: Assoc permutes `p ∨ (q ∨ r)`, but the statement has `p ∨ q ∨ r`, i.e.
    `(p ∨ q) ∨ r` (✱2·33); PM moves the brackets tacitly. -/
theorem t2_74 (p : F) (q : F) (r : F) : Thm (s2_74 p q r) :=
  -- ⊢ . ✱2·73 (q,p/p,q) . ⊃ ⊢ :. q ⊃ p . ⊃ : q ∨ p ∨ r . ⊃ . p ∨ r
  have h1 : Thm (imp (imp q p) (imp (.or (.or q p) r) (.or p r))) := t2_73 q p r
  -- ⊢ . Assoc . ⊃ ⊢ : p ∨ (q ∨ r) . ⊃ . q ∨ (p ∨ r)
  have h2 : Thm (imp (.or p (.or q r)) (.or q (.or p r))) := Thm.assoc p q r
  -- [✱2·32 . ✱2·31] ⊢ : p ∨ q ∨ r . ⊃ . q ∨ p ∨ r
  have h3 : Thm (imp (.or (.or p q) r) (.or (.or q p) r)) :=
    syl (syl (t2_32 p q r) h2) (t2_31 q p r)
  -- ⊢ . (1) . (2) . Syll . ⊃ ⊢ . Prop
  sylMid h1 h3

/-- *2.75 — [✱2·74, ✱2·53, ✱2·31] -/
theorem t2_75 (p : F) (q : F) (r : F) : Thm (s2_75 p q r) := pm2_75 p q r

/-- *2.76 — [✱2·75, ✱2·04] -/
theorem t2_76 (p : F) (q : F) (r : F) : Thm (s2_76 p q r) := comm (t2_75 p q r)

/-- *2.77 — [✱2·76 (∼p/p)] -/
theorem t2_77 (p : F) (q : F) (r : F) : Thm (s2_77 p q r) := t2_76 (.neg p) q r

/-- *2.81 — PM Dem.: Sum; ✱2·76 . Syll; (1) . (2). -/
theorem t2_81 (p : F) (q : F) (r : F) (s : F) : Thm (s2_81 p q r s) :=
  -- ⊢ . Sum . ⊃ ⊢ :: q . ⊃ . r ⊃ s : ⊃ :. p ∨ q . ⊃ : p . ∨ . r ⊃ s   (1)
  have h1 : Thm (imp (imp q (imp r s)) (imp (.or p q) (.or p (imp r s)))) := Thm.sum p q (imp r s)
  -- ⊢ . ✱2·76 . Syll . ⊃ ⊢ :: p ∨ q . ⊃ : p . ∨ . r ⊃ s :. ⊃ :. p ∨ q . ⊃ : p ∨ r . ⊃ . p ∨ s   (2)
  have h2 : Thm (imp (imp (.or p q) (.or p (imp r s))) (imp (.or p q) (imp (.or p r) (.or p s)))) :=
    Thm.mp (t2_76 p r s) (t2_05 (.or p q) _ _)
  -- ⊢ . (1) . (2) . ⊃ ⊢ . Prop
  syl h1 h2

/-- *2.82 — [✱2·8, ✱2·81; ✱2·31/✱2·32 for the bracketing] -/
theorem t2_82 (p : F) (q : F) (r : F) (s : F) : Thm (s2_82 p q r s) := ofPf <| by
  unfold s2_82; intro_; intro_
  exact app (t2_31 p q s)
    (app2 (Thm.mp (t2_8 q r s) (t2_81 p (.or q r) (.or (.neg r) s) (.or q s)))
      (app (t2_32 p q r) (hy 0)) (app (t2_32 p (.neg r) s) (hy 1)))

/-- *2.83 — [✱2·82 (∼p,∼q/p,q); ✱2·31/✱2·32 for the bracketing] -/
theorem t2_83 (p : F) (q : F) (r : F) (s : F) : Thm (s2_83 p q r s) := ofPf <| by
  unfold s2_83; intro_; intro_
  exact app (t2_32 (.neg p) (.neg q) s)
    (app2 (t2_82 (.neg p) (.neg q) r s)
      (app (t2_31 (.neg p) (.neg q) r) (hy 0)) (app (t2_31 (.neg p) (.neg r) s) (hy 1)))

/-- *3.3 — Exp. PM Dem.: Id (✱3·01); Transp; Id (✱1·01); Comm; Transp . Syll. -/
theorem t3_3 (p : F) (q : F) (r : F) : Thm (s3_3 p q r) :=
  -- [Id . (✱3·01)] ⊢ :. p . q . ⊃ . r : ⊃ : ∼(∼p ∨ ∼q) . ⊃ . r :
  have l1 : Thm (imp (imp (and p q) r) (imp (.neg (.or (.neg p) (.neg q))) r)) := t2_08 _
  -- [Transp] ⊃ : ∼r . ⊃ . ∼p ∨ ∼q :
  have l2 : Thm (imp (imp (.neg (.or (.neg p) (.neg q))) r) (imp (.neg r) (.or (.neg p) (.neg q)))) :=
    t2_15 (.or (.neg p) (.neg q)) r
  -- [Id . (✱1·01)] ⊃ : ∼r . ⊃ . p ⊃ ∼q :
  have l3 : Thm (imp (imp (.neg r) (.or (.neg p) (.neg q))) (imp (.neg r) (imp p (.neg q)))) := t2_08 _
  -- [Comm] ⊃ : p . ⊃ . ∼r ⊃ ∼q :
  have l4 : Thm (imp (imp (.neg r) (imp p (.neg q))) (imp p (imp (.neg r) (.neg q)))) :=
    t2_04 (.neg r) p (.neg q)
  -- [Transp . Syll] ⊃ : p . ⊃ . q ⊃ r :. ⊃ ⊢ . Prop
  have l5 : Thm (imp (imp p (imp (.neg r) (.neg q))) (imp p (imp q r))) :=
    Thm.mp (t2_17 q r) (t2_05 p _ _)
  syl (syl (syl (syl l1 l2) l3) l4) l5

/-- *3.37 — PM Dem.: Transp; Syll (1); Exp (2); Imp (3); (2) . (1) . (3) . Syll. -/
theorem t3_37 (p : F) (q : F) (r : F) : Thm (s3_37 p q r) :=
  -- ⊢ . Transp . ⊃ ⊢ : q ⊃ r . ⊃ . ∼r ⊃ ∼q :
  have l1 : Thm (imp (imp q r) (imp (.neg r) (.neg q))) := t2_16 q r
  -- [Syll] ⊃ ⊢ :. p . ⊃ . q ⊃ r : ⊃ : p . ⊃ . ∼r ⊃ ∼q   (1)
  have h1 : Thm (imp (imp p (imp q r)) (imp p (imp (.neg r) (.neg q)))) := Thm.mp l1 (t2_05 p _ _)
  -- ⊢ . Exp . ⊃ ⊢ :. p . q . ⊃ . r : ⊃ : p . ⊃ . q ⊃ r   (2)
  have h2 : Thm (imp (imp (and p q) r) (imp p (imp q r))) := t3_3 p q r
  -- ⊢ . Imp . ⊃ ⊢ :. p . ⊃ . ∼r ⊃ ∼q : ⊃ : p . ∼r . ⊃ . ∼q   (3)
  have h3 : Thm (imp (imp p (imp (.neg r) (.neg q))) (imp (and p (.neg r)) (.neg q))) :=
    t3_31 p (.neg r) (.neg q)
  -- ⊢ . (2) . (1) . (3) . Syll . ⊃ ⊢ . Prop
  syl (syl h2 h1) h3

/-- *3.43 — Comp. PM Dem.: ✱3·2 (1); (1) . Syll; ✱2·77 (2); (2) . Imp. -/
theorem t3_43 (p : F) (q : F) (r : F) : Thm (s3_43 p q r) :=
  -- ⊢ . ✱3·2 . ⊃ ⊢ :. q . ⊃ : r . ⊃ . q . r   (1)
  have h1 : Thm (imp q (imp r (and q r))) := t3_2 q r
  -- ⊢ . (1) . Syll . ⊃ ⊢ :: p ⊃ q . ⊃ :. p . ⊃ : r . ⊃ . q . r :.
  have l1 : Thm (imp (imp p q) (imp p (imp r (and q r)))) := Thm.mp h1 (t2_05 p q _)
  -- [✱2·77] ⊃ :. p ⊃ r . ⊃ : p . ⊃ . q . r   (2)
  have h2 : Thm (imp (imp p q) (imp (imp p r) (imp p (and q r)))) := syl l1 (t2_77 p r (and q r))
  -- ⊢ . (2) . Imp . ⊃ ⊢ . Prop
  Thm.mp h2 (t3_31 (imp p q) (imp p r) (imp p (and q r)))

/-- *3.44 — PM Dem.: Syll; ✱2·6 (1); (1) . Exp; Comm . Imp (2); (2) . Comm; ✱2·53 . Syll. -/
theorem t3_44 (p : F) (q : F) (r : F) : Thm (s3_44 p q r) :=
  -- ⊢ . Syll . ⊃ ⊢ :. ∼q ⊃ r . r ⊃ p . ⊃ : ∼q ⊃ p :
  have l1 : Thm (imp (and (imp (.neg q) r) (imp r p)) (imp (.neg q) p)) := t3_33 (.neg q) r p
  -- [✱2·6] ⊃ : q ⊃ p . ⊃ . p   (1)
  have h1 : Thm (imp (and (imp (.neg q) r) (imp r p)) (imp (imp q p) p)) := syl l1 (t2_6 q p)
  -- ⊢ . (1) . Exp . ⊃ ⊢ :: ∼q ⊃ r . ⊃ :. r ⊃ p . ⊃ : q ⊃ p . ⊃ . p :.
  have l2 : Thm (imp (imp (.neg q) r) (imp (imp r p) (imp (imp q p) p))) :=
    Thm.mp h1 (t3_3 (imp (.neg q) r) (imp r p) (imp (imp q p) p))
  -- [Comm . Imp] ⊃ :. q ⊃ p . r ⊃ p . ⊃ . p   (2)
  have h2 : Thm (imp (imp (.neg q) r) (imp (and (imp q p) (imp r p)) p)) :=
    syl (syl l2 (t2_04 (imp r p) (imp q p) p)) (t3_31 (imp q p) (imp r p) p)
  -- ⊢ . (2) . Comm . ⊃ ⊢ :. q ⊃ p . r ⊃ p . ⊃ : ∼q ⊃ r . ⊃ . p :.
  have l3 : Thm (imp (and (imp q p) (imp r p)) (imp (imp (.neg q) r) p)) :=
    Thm.mp h2 (t2_04 (imp (.neg q) r) (and (imp q p) (imp r p)) p)
  -- [✱2·53 . Syll] ⊃ ⊢ . Prop
  sylMid l3 (t2_53 q r)

/-- *3.47 — PM Dem.: ✱3·26; Fact; ✱3·22 (1); ✱3·27; Fact; ✱3·22 (2); (1) . (2) . ✱3·03 . ✱2·83. -/
theorem t3_47 (p : F) (q : F) (r : F) (s : F) : Thm (s3_47 p q r s) :=
  -- ⊢ . ✱3·26 . ⊃ ⊢ :. p ⊃ r . q ⊃ s . ⊃ : p ⊃ r :
  have l1 : Thm (imp (and (imp p r) (imp q s)) (imp p r)) := t3_26 (imp p r) (imp q s)
  -- [Fact] ⊃ : p . q . ⊃ . r . q :
  have l2 : Thm (imp (and (imp p r) (imp q s)) (imp (and p q) (and r q))) := syl l1 (t3_45 p r q)
  -- [✱3·22] ⊃ : p . q . ⊃ . q . r   (1)
  have h1 : Thm (imp (and (imp p r) (imp q s)) (imp (and p q) (and q r))) := sylEnd l2 (t3_22 r q)
  -- ⊢ . ✱3·27 . ⊃ ⊢ :. p ⊃ r . q ⊃ s . ⊃ : q ⊃ s :
  have l3 : Thm (imp (and (imp p r) (imp q s)) (imp q s)) := t3_27 (imp p r) (imp q s)
  -- [Fact] ⊃ : q . r . ⊃ . s . r :
  have l4 : Thm (imp (and (imp p r) (imp q s)) (imp (and q r) (and s r))) := syl l3 (t3_45 q s r)
  -- [✱3·22] ⊃ : q . r . ⊃ . r . s   (2)
  have h2 : Thm (imp (and (imp p r) (imp q s)) (imp (and q r) (and r s))) := sylEnd l4 (t3_22 s r)
  -- ⊢ . (1) . (2) . ✱3·03 . ✱2·83 . ⊃ ⊢ :. p ⊃ r . q ⊃ s . ⊃ : p . q . ⊃ . r . s :. ⊃ ⊢ . Prop
  Thm.mp h2 (Thm.mp h1 (t2_83 (and (imp p r) (imp q s)) (and p q) (and q r) (and r s)))

/-- *3.48 — PM Dem.: ✱3·26; Sum; Perm (1); ✱3·27; Sum; Perm (2); (1) . (2) . ✱2·83.
    The intermediate lines as transcribed (`p ∨ q . ⊃ . r ∨ q`, `q ∨ r . ⊃ . s ∨ r`) are not what Sum
    gives (`q ∨ p . ⊃ . q ∨ r`, `r ∨ q . ⊃ . r ∨ s`); with Perm on the antecedent the numbered lines
    (1) and (2) come out exactly as printed. -/
theorem t3_48 (p : F) (q : F) (r : F) (s : F) : Thm (s3_48 p q r s) :=
  -- ⊢ . ✱3·26 . ⊃ ⊢ :. p ⊃ r . q ⊃ s . ⊃ : p ⊃ r :
  have l1 : Thm (imp (and (imp p r) (imp q s)) (imp p r)) := t3_26 (imp p r) (imp q s)
  -- [Sum] ⊃ : q ∨ p . ⊃ . q ∨ r :
  have l2 : Thm (imp (and (imp p r) (imp q s)) (imp (.or q p) (.or q r))) := syl l1 (Thm.sum q p r)
  -- [Perm] ⊃ : p ∨ q . ⊃ . q ∨ r   (1)
  have h1 : Thm (imp (and (imp p r) (imp q s)) (imp (.or p q) (.or q r))) := sylMid l2 (Thm.perm p q)
  -- ⊢ . ✱3·27 . ⊃ ⊢ :. p ⊃ r . q ⊃ s . ⊃ : q ⊃ s :
  have l3 : Thm (imp (and (imp p r) (imp q s)) (imp q s)) := t3_27 (imp p r) (imp q s)
  -- [Sum] ⊃ : r ∨ q . ⊃ . r ∨ s :
  have l4 : Thm (imp (and (imp p r) (imp q s)) (imp (.or r q) (.or r s))) := syl l3 (Thm.sum r q s)
  -- [Perm] ⊃ : q ∨ r . ⊃ . r ∨ s   (2)
  have h2 : Thm (imp (and (imp p r) (imp q s)) (imp (.or q r) (.or r s))) := sylMid l4 (Thm.perm q r)
  -- ⊢ . (1) . (2) . ✱2·83 . ⊃ ⊢ :. p ⊃ r . q ⊃ s . ⊃ : p ∨ q . ⊃ . r ∨ s :. ⊃ ⊢ . Prop
  Thm.mp h2 (Thm.mp h1 (t2_83 (and (imp p r) (imp q s)) (.or p q) (.or q r) (.or r s)))

/-- *4.11 — PM: [✱2·16·17 . ✱3·47·22] (hint only; the lines are reconstructed from it). -/
theorem t4_11 (p : F) (q : F) : Thm (s4_11 p q) :=
  -- ⊢ . ✱2·16 . ✱3·03 . ⊃ ⊢ : p ⊃ q . ⊃ . ∼q ⊃ ∼p : q ⊃ p . ⊃ . ∼p ⊃ ∼q :
  have l1 : Thm (and (imp (imp p q) (imp (.neg q) (.neg p))) (imp (imp q p) (imp (.neg p) (.neg q)))) :=
    andIh (t2_16 p q) (t2_16 q p)
  -- [✱3·47] ⊃ ⊢ : p ≡ q . ⊃ . ∼q ⊃ ∼p . ∼p ⊃ ∼q :
  have l2 : Thm (imp (iff p q) (and (imp (.neg q) (.neg p)) (imp (.neg p) (.neg q)))) :=
    Thm.mp l1 (t3_47 (imp p q) (imp q p) (imp (.neg q) (.neg p)) (imp (.neg p) (.neg q)))
  -- [✱3·22] ⊃ ⊢ : p ≡ q . ⊃ . ∼p ≡ ∼q   (1)
  have h1 : Thm (imp (iff p q) (iff (.neg p) (.neg q))) :=
    syl l2 (t3_22 (imp (.neg q) (.neg p)) (imp (.neg p) (.neg q)))
  -- ⊢ . ✱2·17 . ✱3·03 . ⊃ ⊢ : ∼p ⊃ ∼q . ⊃ . q ⊃ p : ∼q ⊃ ∼p . ⊃ . p ⊃ q :
  have l3 : Thm (and (imp (imp (.neg p) (.neg q)) (imp q p)) (imp (imp (.neg q) (.neg p)) (imp p q))) :=
    andIh (t2_17 q p) (t2_17 p q)
  -- [✱3·47] ⊃ ⊢ : ∼p ≡ ∼q . ⊃ . q ⊃ p . p ⊃ q :
  have l4 : Thm (imp (iff (.neg p) (.neg q)) (and (imp q p) (imp p q))) :=
    Thm.mp l3 (t3_47 (imp (.neg p) (.neg q)) (imp (.neg q) (.neg p)) (imp q p) (imp p q))
  -- [✱3·22] ⊃ ⊢ : ∼p ≡ ∼q . ⊃ . p ≡ q   (2)
  have h2 : Thm (imp (iff (.neg p) (.neg q)) (iff p q)) := syl l4 (t3_22 (imp q p) (imp p q))
  -- ⊢ . (1) . (2) . ⊃ ⊢ . Prop
  iffIh h1 h2

/-- *4.12 — [✱2·03, ✱2·15, ✱3·2, ✱3·26, ✱3·27] -/
theorem t4_12 (p : F) (q : F) : Thm (s4_12 p q) := ofPf <| by
  unfold s4_12; split_iff
  · exact iffI (app (t2_03 p q) (iffMp (hy 0))) (app (t2_15 q p) (iffMpr (hy 0)))
  · exact iffI (app (t2_03 q p) (iffMp (hy 0))) (app (t2_15 p q) (iffMpr (hy 0)))

/-- *4.14 — PM: [✱3·37 . ✱4·13] (hint only).
    extra ✱2·16: ✱3·37 (∼r,∼q/q,r) gives `p . ∼∼q . ⊃ . ∼∼r`; ✱4·13 turns `∼∼r` into `r` by Syll,
    but replacing `∼∼q` by `q` inside the product `p . (…)` needs Transp, since
    `p . q = ∼(p ⊃ ∼q)` (✱3·01). PM leaves this replacement tacit. -/
theorem t4_14 (p : F) (q : F) (r : F) : Thm (s4_14 p q r) :=
  -- ⊢ . ✱3·37 . ⊃ ⊢ :. p . q . ⊃ . r : ⊃ : p . ∼r . ⊃ . ∼q   (1)
  have h1 : Thm (imp (imp (and p q) r) (imp (and p (.neg r)) (.neg q))) := t3_37 p q r
  -- ⊢ . ✱3·37 (∼r,∼q/q,r) . ⊃ ⊢ :. p . ∼r . ⊃ . ∼q : ⊃ : p . ∼∼q . ⊃ . ∼∼r :
  have l1 : Thm (imp (imp (and p (.neg r)) (.neg q)) (imp (and p (.neg (.neg q))) (.neg (.neg r)))) :=
    t3_37 p (.neg r) (.neg q)
  -- [✱4·13] ⊃ : p . ∼∼q . ⊃ . r :
  have l2 : Thm (imp (imp (and p (.neg r)) (.neg q)) (imp (and p (.neg (.neg q))) r)) :=
    sylEnd l1 (iffMprh (t4_13 r))
  -- [✱4·13 . Transp] ⊃ : p . q . ⊃ . r   (2)
  have l3 : Thm (imp (and p q) (and p (.neg (.neg q)))) :=
    Thm.mp (sylCons (iffMprh (t4_13 (.neg q)))) (t2_16 (imp p (.neg (.neg (.neg q)))) (imp p (.neg q)))
  have h2 : Thm (imp (imp (and p (.neg r)) (.neg q)) (imp (and p q) r)) := sylMid l2 l3
  -- ⊢ . (1) . (2) . ⊃ ⊢ . Prop
  iffIh h1 h2

/-- *4.15 — PM: [✱3·22 . ✱4·13·14] (hint only).
    extra ✱4·11: ✱4·14 (q,p,∼r/p,q,r) gives `q . ∼∼r . ⊃ . ∼p`; replacing `∼∼r` by `r` inside the
    product `q . (…)` needs ✱4·11, since `q . r = ∼(q ⊃ ∼r)` (✱3·01). PM leaves this tacit. -/
theorem t4_15 (p : F) (q : F) (r : F) : Thm (s4_15 p q r) :=
  -- ⊢ . ✱3·22 . ⊃ ⊢ :. p . q . ⊃ . ∼r : ≡ : q . p . ⊃ . ∼r :
  have l1 : Thm (iff (imp (and p q) (.neg r)) (imp (and q p) (.neg r))) :=
    iffSylAnt (.neg r) (iffIh (t3_22 p q) (t3_22 q p))
  -- [✱4·14] ≡ : q . ∼∼r . ⊃ . ∼p :
  have l2 : Thm (iff (imp (and q p) (.neg r)) (imp (and q (.neg (.neg r))) (.neg p))) :=
    t4_14 q p (.neg r)
  -- [✱4·13] ≡ : q . r . ⊃ . ∼p :. ⊃ ⊢ . Prop
  have l3 : Thm (iff (and q (.neg (.neg r))) (and q r)) :=
    Thm.mp (iffSylCons q (iffSymmh (t4_13 (.neg r)))) (iffMph (t4_11 _ _))
  iffTransh (iffTransh l1 l2) (iffSylAnt (.neg p) l3)

/-- *4.22 — PM Dem.: ✱3·26 . ✱3·26 (1); ✱3·27 . ✱3·26 (2); (1) . (2) . ✱2·83 (3);
    ✱3·27 . ✱3·27 (4); ✱3·26 . ✱3·27 (5); (4) . (5) . ✱2·83 (6); (3) . (6) . Comp. -/
theorem t4_22 (p : F) (q : F) (r : F) : Thm (s4_22 p q r) :=
  -- ⊢ . ✱3·26 . ⊃ ⊢ : p ≡ q . q ≡ r . ⊃ . p ≡ q
  have l1 : Thm (imp (and (iff p q) (iff q r)) (iff p q)) := t3_26 (iff p q) (iff q r)
  -- [✱3·26] ⊃ . p ⊃ q   (1)
  have h1 : Thm (imp (and (iff p q) (iff q r)) (imp p q)) := syl l1 (t3_26 (imp p q) (imp q p))
  -- ⊢ . ✱3·27 . ⊃ ⊢ : p ≡ q . q ≡ r . ⊃ . q ≡ r
  have l2 : Thm (imp (and (iff p q) (iff q r)) (iff q r)) := t3_27 (iff p q) (iff q r)
  -- [✱3·26] ⊃ . q ⊃ r   (2)
  have h2 : Thm (imp (and (iff p q) (iff q r)) (imp q r)) := syl l2 (t3_26 (imp q r) (imp r q))
  -- ⊢ . (1) . (2) . ✱2·83 . ⊃ ⊢ : p ≡ q . q ≡ r . ⊃ . p ⊃ r   (3)
  have h3 : Thm (imp (and (iff p q) (iff q r)) (imp p r)) :=
    Thm.mp h2 (Thm.mp h1 (t2_83 (and (iff p q) (iff q r)) p q r))
  -- ⊢ . ✱3·27 . ⊃ ⊢ : p ≡ q . q ≡ r . ⊃ . q ≡ r
  -- [✱3·27] ⊃ . r ⊃ q   (4)
  have h4 : Thm (imp (and (iff p q) (iff q r)) (imp r q)) := syl l2 (t3_27 (imp q r) (imp r q))
  -- ⊢ . ✱3·26 . ⊃ ⊢ : p ≡ q . q ≡ r . ⊃ . p ≡ q
  -- [✱3·27] ⊃ . q ⊃ p   (5)
  have h5 : Thm (imp (and (iff p q) (iff q r)) (imp q p)) := syl l1 (t3_27 (imp p q) (imp q p))
  -- ⊢ . (4) . (5) . ✱2·83 . ⊃ ⊢ : p ≡ q . q ≡ r . ⊃ . r ⊃ p   (6)
  have h6 : Thm (imp (and (iff p q) (iff q r)) (imp r p)) :=
    Thm.mp h5 (Thm.mp h4 (t2_83 (and (iff p q) (iff q r)) r q p))
  -- ⊢ . (3) . (6) . Comp . ⊃ ⊢ . Prop
  Thm.mp (andIh h3 h6) (t3_43 (and (iff p q) (iff q r)) (imp p r) (imp r p))

/-- *4.32 — PM Dem.: ✱4·15; ✱4·12 (1); (1) . ✱4·11; (✱1·01 . ✱3·01).
    extra ✱2·03: the step `q . r . ⊃ . ∼p : ≡ : p . ⊃ . ∼(q . r)` cited as ✱4·12
    (`p ≡ ∼q . ≡ . q ≡ ∼p`) is not an instance of ✱4·12; it is ✱2·03 taken both ways (the
    ⊃-analogue of ✱4·12). ✱4·12 itself cannot be used, so it stays uncited in the Lean proof. -/
theorem t4_32 (p : F) (q : F) (r : F) : Thm (s4_32 p q r) :=
  -- ⊢ . ✱4·15 . ⊃ ⊢ :. p . q . ⊃ . ∼r : ≡ : q . r . ⊃ . ∼p :
  have l1 : Thm (iff (imp (and p q) (.neg r)) (imp (and q r) (.neg p))) := t4_15 p q r
  -- [✱4·12, read ✱2·03] ≡ : p . ⊃ . ∼(q . r)   (1)
  have l2 : Thm (iff (imp (and q r) (.neg p)) (imp p (.neg (and q r)))) :=
    iffIh (t2_03 (and q r) p) (t2_03 p (and q r))
  have h1 : Thm (iff (imp (and p q) (.neg r)) (imp p (.neg (and q r)))) := iffTransh l1 l2
  -- ⊢ . (1) . ✱4·11 . ⊃ ⊢ : ∼(p . q . ⊃ . ∼r) . ≡ . ∼{p . ⊃ . ∼(q . r)} :
  -- [(✱1·01 . ✱3·01)] ⊃ ⊢ . Prop
  Thm.mp h1 (iffMph (t4_11 (imp (and p q) (.neg r)) (imp p (.neg (and q r)))))

/-- *4.36 — PM: [Fact . ✱3·47] (hint only). -/
theorem t4_36 (p : F) (q : F) (r : F) : Thm (s4_36 p q r) :=
  -- ⊢ . Fact . ✱3·03 . ⊃ ⊢ : p ⊃ q . ⊃ . p . r ⊃ q . r : q ⊃ p . ⊃ . q . r ⊃ p . r :
  have l1 : Thm (and (imp (imp p q) (imp (and p r) (and q r))) (imp (imp q p) (imp (and q r) (and p r)))) :=
    andIh (t3_45 p q r) (t3_45 q p r)
  -- [✱3·47] ⊃ ⊢ :. p ≡ q . ⊃ : p . r . ≡ . q . r
  Thm.mp l1 (t3_47 (imp p q) (imp q p) (imp (and p r) (and q r)) (imp (and q r) (and p r)))

/-- *4.37 — PM: [Sum . ✱3·47] (hint only).
    extra ✱1·4: Sum adds the new disjunct on the left (`r ∨ p . ⊃ . r ∨ q`), but the statement has it
    on the right (`p ∨ r . ≡ . q ∨ r`); Perm is needed at both ends (✱2·38 would replace Sum). -/
theorem t4_37 (p : F) (q : F) (r : F) : Thm (s4_37 p q r) :=
  -- ⊢ . Sum . ⊃ ⊢ : p ⊃ q . ⊃ . r ∨ p ⊃ r ∨ q :
  -- [Perm] ⊃ . p ∨ r ⊃ q ∨ r :
  have l1 : Thm (imp (imp p q) (imp (.or p r) (.or q r))) :=
    sylEnd (sylMid (Thm.sum r p q) (Thm.perm p r)) (Thm.perm r q)
  -- ⊢ . Sum . ⊃ ⊢ : q ⊃ p . ⊃ . r ∨ q ⊃ r ∨ p :
  -- [Perm] ⊃ . q ∨ r ⊃ p ∨ r :
  have l2 : Thm (imp (imp q p) (imp (.or q r) (.or p r))) :=
    sylEnd (sylMid (Thm.sum r q p) (Thm.perm q r)) (Thm.perm r p)
  -- ⊢ . ✱3·03 . ✱3·47 . ⊃ ⊢ :. p ≡ q . ⊃ : p ∨ r . ≡ . q ∨ r
  Thm.mp (andIh l1 l2) (t3_47 (imp p q) (imp q p) (imp (.or p r) (.or q r)) (imp (.or q r) (.or p r)))

/-- *4.38 — PM: [✱3·47 . ✱4·32 . ✱3·22] (hint only).
    extra ✱2·08: ✱4·32 and ✱3·22 bring the hypothesis `(p ⊃ r . r ⊃ p) . (q ⊃ s . s ⊃ q)` into the
    form `(p ⊃ r . q ⊃ s) . (r ⊃ p . s ⊃ q)` only if they may be applied to one factor of a product;
    that replacement is done here with ✱3·47 and Id. -/
theorem t4_38 (p : F) (q : F) (r : F) (s : F) : Thm (s4_38 p q r s) :=
  -- ⊢ . ✱4·32 . ⊃ ⊢ :. p ≡ r . q ≡ s . ⊃ : p ⊃ r : r ⊃ p . (q ⊃ s . s ⊃ q) :
  have r1 : Thm (imp (and (iff p r) (iff q s))
      (and (imp p r) (and (imp r p) (and (imp q s) (imp s q))))) :=
    iffMph (t4_32 (imp p r) (imp r p) (and (imp q s) (imp s q)))
  -- [✱4·32 . ✱3·22 . ✱4·32 (with ✱3·47 . Id)] ⊃ : p ⊃ r : q ⊃ s . (r ⊃ p . s ⊃ q) :
  have u : Thm (imp (and (imp r p) (and (imp q s) (imp s q))) (and (imp q s) (and (imp r p) (imp s q)))) :=
    syl (syl (iffMprh (t4_32 (imp r p) (imp q s) (imp s q)))
      (Thm.mp (andIh (t3_22 (imp r p) (imp q s)) (t2_08 (imp s q)))
        (t3_47 (and (imp r p) (imp q s)) (imp s q) (and (imp q s) (imp r p)) (imp s q))))
      (iffMph (t4_32 (imp q s) (imp r p) (imp s q)))
  have r2 : Thm (imp (and (imp p r) (and (imp r p) (and (imp q s) (imp s q))))
      (and (imp p r) (and (imp q s) (and (imp r p) (imp s q))))) :=
    Thm.mp (andIh (t2_08 (imp p r)) u)
      (t3_47 (imp p r) (and (imp r p) (and (imp q s) (imp s q))) (imp p r)
        (and (imp q s) (and (imp r p) (imp s q))))
  -- [✱4·32] ⊃ : p ⊃ r . q ⊃ s : r ⊃ p . s ⊃ q :
  have hp : Thm (imp (and (iff p r) (iff q s))
      (and (and (imp p r) (imp q s)) (and (imp r p) (imp s q)))) :=
    syl (syl r1 r2) (iffMprh (t4_32 (imp p r) (imp q s) (and (imp r p) (imp s q))))
  -- ⊢ . ✱3·47 . ✱3·03 . ⊃ ⊢ :. p ⊃ r . q ⊃ s . ⊃ : p . q . ⊃ . r . s :. r ⊃ p . s ⊃ q . ⊃ : r . s . ⊃ . p . q
  have c : Thm (and (imp (and (imp p r) (imp q s)) (imp (and p q) (and r s)))
      (imp (and (imp r p) (imp s q)) (imp (and r s) (and p q)))) :=
    andIh (t3_47 p q r s) (t3_47 r s p q)
  -- [✱3·47] ⊃ ⊢ :. p ⊃ r . q ⊃ s : r ⊃ p . s ⊃ q : ⊃ : p . q . ≡ . r . s
  -- ⊢ . (hp) . Syll . ⊃ ⊢ . Prop
  syl hp (Thm.mp c (t3_47 (and (imp p r) (imp q s)) (and (imp r p) (imp s q))
    (imp (and p q) (and r s)) (imp (and r s) (and p q))))

/-- *4.39 — PM: [✱3·48·47 . ✱4·32 . ✱3·22] (hint only).
    extra ✱2·08: as for ✱4·38, the hypothesis is rearranged by ✱4·32 and ✱3·22 inside a factor,
    which is done here with ✱3·47 and Id. -/
theorem t4_39 (p : F) (q : F) (r : F) (s : F) : Thm (s4_39 p q r s) :=
  -- ⊢ . ✱4·32 . ⊃ ⊢ :. p ≡ r . q ≡ s . ⊃ : p ⊃ r : r ⊃ p . (q ⊃ s . s ⊃ q) :
  have r1 : Thm (imp (and (iff p r) (iff q s))
      (and (imp p r) (and (imp r p) (and (imp q s) (imp s q))))) :=
    iffMph (t4_32 (imp p r) (imp r p) (and (imp q s) (imp s q)))
  -- [✱4·32 . ✱3·22 . ✱4·32 (with ✱3·47 . Id)] ⊃ : p ⊃ r : q ⊃ s . (r ⊃ p . s ⊃ q) :
  have u : Thm (imp (and (imp r p) (and (imp q s) (imp s q))) (and (imp q s) (and (imp r p) (imp s q)))) :=
    syl (syl (iffMprh (t4_32 (imp r p) (imp q s) (imp s q)))
      (Thm.mp (andIh (t3_22 (imp r p) (imp q s)) (t2_08 (imp s q)))
        (t3_47 (and (imp r p) (imp q s)) (imp s q) (and (imp q s) (imp r p)) (imp s q))))
      (iffMph (t4_32 (imp q s) (imp r p) (imp s q)))
  have r2 : Thm (imp (and (imp p r) (and (imp r p) (and (imp q s) (imp s q))))
      (and (imp p r) (and (imp q s) (and (imp r p) (imp s q))))) :=
    Thm.mp (andIh (t2_08 (imp p r)) u)
      (t3_47 (imp p r) (and (imp r p) (and (imp q s) (imp s q))) (imp p r)
        (and (imp q s) (and (imp r p) (imp s q))))
  -- [✱4·32] ⊃ : p ⊃ r . q ⊃ s : r ⊃ p . s ⊃ q :
  have hp : Thm (imp (and (iff p r) (iff q s))
      (and (and (imp p r) (imp q s)) (and (imp r p) (imp s q)))) :=
    syl (syl r1 r2) (iffMprh (t4_32 (imp p r) (imp q s) (and (imp r p) (imp s q))))
  -- ⊢ . ✱3·48 . ✱3·03 . ⊃ ⊢ :. p ⊃ r . q ⊃ s . ⊃ : p ∨ q . ⊃ . r ∨ s :. r ⊃ p . s ⊃ q . ⊃ : r ∨ s . ⊃ . p ∨ q
  have c : Thm (and (imp (and (imp p r) (imp q s)) (imp (.or p q) (.or r s)))
      (imp (and (imp r p) (imp s q)) (imp (.or r s) (.or p q)))) :=
    andIh (t3_48 p q r s) (t3_48 r s p q)
  -- [✱3·47] ⊃ ⊢ :. p ⊃ r . q ⊃ s : r ⊃ p . s ⊃ q : ⊃ : p ∨ q . ≡ . r ∨ s
  -- ⊢ . (hp) . Syll . ⊃ ⊢ . Prop
  syl hp (Thm.mp c (t3_47 (and (imp p r) (imp q s)) (and (imp r p) (imp s q))
    (imp (.or p q) (.or r s)) (imp (.or r s) (.or p q))))

/-- *4.4 — PM Dem.: ✱3·2; Comp; ✱3·48 (1); (1) . Imp (2); ✱3·26; ✱3·44 (3); ✱3·27; ✱3·48 (4);
    (3) . (4) . Comp (5); (2) . (5). -/
theorem t4_4 (p : F) (q : F) (r : F) : Thm (s4_4 p q r) :=
  -- ⊢ . ✱3·2 . ⊃ ⊢ :: p . ⊃ : q . ⊃ . p . q :. p . ⊃ : r . ⊃ . p . r ::
  have l1 : Thm (and (imp p (imp q (and p q))) (imp p (imp r (and p r)))) := andIh (t3_2 p q) (t3_2 p r)
  -- [Comp] ⊃ ⊢ :: p . ⊃ :. q . ⊃ . p . q : r . ⊃ . p . r :.
  have l2 : Thm (imp p (and (imp q (and p q)) (imp r (and p r)))) :=
    Thm.mp l1 (t3_43 p (imp q (and p q)) (imp r (and p r)))
  -- [✱3·48] ⊃ :. q ∨ r . ⊃ : p . q . ∨ . p . r   (1)
  have h1 : Thm (imp p (imp (.or q r) (.or (and p q) (and p r)))) :=
    syl l2 (t3_48 q r (and p q) (and p r))
  -- ⊢ . (1) . Imp . ⊃ ⊢ :. p . q ∨ r . ⊃ : p . q . ∨ . p . r   (2)
  have h2 : Thm (imp (and p (.or q r)) (.or (and p q) (and p r))) :=
    Thm.mp h1 (t3_31 p (.or q r) (.or (and p q) (and p r)))
  -- ⊢ . ✱3·26 . ⊃ ⊢ :. p . q . ⊃ . p : p . r . ⊃ . p :.
  have l3 : Thm (and (imp (and p q) p) (imp (and p r) p)) := andIh (t3_26 p q) (t3_26 p r)
  -- [✱3·44] ⊃ ⊢ :. p . q . ∨ . p . r : ⊃ . p   (3)
  have h3 : Thm (imp (.or (and p q) (and p r)) p) := Thm.mp l3 (t3_44 p (and p q) (and p r))
  -- ⊢ . ✱3·27 . ⊃ ⊢ :. p . q . ⊃ . q : p . r . ⊃ . r :.
  have l4 : Thm (and (imp (and p q) q) (imp (and p r) r)) := andIh (t3_27 p q) (t3_27 p r)
  -- [✱3·48] ⊃ ⊢ :. p . q . ∨ . p . r : ⊃ . q ∨ r   (4)
  have h4 : Thm (imp (.or (and p q) (and p r)) (.or q r)) :=
    Thm.mp l4 (t3_48 (and p q) (and p r) q r)
  -- ⊢ . (3) . (4) . Comp . ⊃ ⊢ :. p . q . ∨ . p . r : ⊃ . p . q ∨ r   (5)
  have h5 : Thm (imp (.or (and p q) (and p r)) (and p (.or q r))) :=
    Thm.mp (andIh h3 h4) (t3_43 (.or (and p q) (and p r)) p (.or q r))
  -- ⊢ . (2) . (5) . ⊃ ⊢ . Prop
  iffIh h2 h5

/-- *4.41 — PM Dem.: ✱3·26 . Sum (1); ✱3·27 . Sum (2); (1) . (2) . Comp (3); ✱2·53 . ✱3·47; Comp;
    ✱2·54 (4); (3) . (4). -/
theorem t4_41 (p : F) (q : F) (r : F) : Thm (s4_41 p q r) :=
  -- ⊢ . ✱3·26 . Sum . ⊃ ⊢ :. p . ∨ . q . r : ⊃ . p ∨ q   (1)
  have h1 : Thm (imp (.or p (and q r)) (.or p q)) := Thm.mp (t3_26 q r) (Thm.sum p (and q r) q)
  -- ⊢ . ✱3·27 . Sum . ⊃ ⊢ :. p . ∨ . q . r : ⊃ . p ∨ r   (2)
  have h2 : Thm (imp (.or p (and q r)) (.or p r)) := Thm.mp (t3_27 q r) (Thm.sum p (and q r) r)
  -- ⊢ . (1) . (2) . Comp . ⊃ ⊢ :. p . ∨ . q . r : ⊃ . p ∨ q . p ∨ r   (3)
  have h3 : Thm (imp (.or p (and q r)) (and (.or p q) (.or p r))) :=
    Thm.mp (andIh h1 h2) (t3_43 (.or p (and q r)) (.or p q) (.or p r))
  -- ⊢ . ✱2·53 . ✱3·47 . ⊃ ⊢ :. p ∨ q . p ∨ r . ⊃ : ∼p ⊃ q . ∼p ⊃ r :
  have l1 : Thm (imp (and (.or p q) (.or p r)) (and (imp (.neg p) q) (imp (.neg p) r))) :=
    Thm.mp (andIh (t2_53 p q) (t2_53 p r))
      (t3_47 (.or p q) (.or p r) (imp (.neg p) q) (imp (.neg p) r))
  -- [Comp] ⊃ : ∼p . ⊃ . q . r :
  have l2 : Thm (imp (and (.or p q) (.or p r)) (imp (.neg p) (and q r))) := syl l1 (t3_43 (.neg p) q r)
  -- [✱2·54] ⊃ : p . ∨ . q . r   (4)
  have h4 : Thm (imp (and (.or p q) (.or p r)) (.or p (and q r))) := syl l2 (t2_54 p (and q r))
  -- ⊢ . (3) . (4) . ⊃ ⊢ . Prop
  iffIh h3 h4

/-- *4.42 — PM Dem.: ✱3·21; ✱2·11 (1); (2); (1) . (2); ✱4·4.
    extra ✱3·26: line (2) `p . q ∨ ∼q . ⊃ . p` carries no citation in the transcription; it is ✱3·26
    (Simp). -/
theorem t4_42 (p : F) (q : F) : Thm (s4_42 p q) :=
  -- ⊢ . ✱3·21 . ⊃ ⊢ :. q ∨ ∼q . ⊃ : p . ⊃ . p . q ∨ ∼q :.
  have l1 : Thm (imp (.or q (.neg q)) (imp p (and p (.or q (.neg q))))) := t3_21 p (.or q (.neg q))
  -- [✱2·11] ⊃ ⊢ : p . ⊃ . p . q ∨ ∼q   (1)
  have h1 : Thm (imp p (and p (.or q (.neg q)))) := Thm.mp (t2_11 q) l1
  -- [✱3·26] ⊢ : p . q ∨ ∼q . ⊃ . p   (2)
  have h2 : Thm (imp (and p (.or q (.neg q))) p) := t3_26 p (.or q (.neg q))
  -- ⊢ . (1) . (2) . ⊃ ⊢ :. p . ≡ : p . q ∨ ∼q :
  have l2 : Thm (iff p (and p (.or q (.neg q)))) := iffIh h1 h2
  -- [✱4·4] ≡ : p . q . ∨ . p . ∼q :. ⊃ ⊢ . Prop
  iffTransh l2 (t4_4 p q (.neg q))

/-- *4.43 — PM Dem.: ✱2·2; Comp (1); ✱2·65 (∼p/p); Imp; ✱2·53 . ✱3·47 (2); (1) . (2).
    extra ✱2·14: ✱2·65 (∼p/p) ends in `∼(∼p)`, not `p` as the line prints it; PM drops the
    double negation. -/
theorem t4_43 (p : F) (q : F) : Thm (s4_43 p q) :=
  -- ⊢ . ✱2·2 . ⊃ ⊢ : p . ⊃ . p ∨ q : p . ⊃ . p ∨ ∼q :
  have l1 : Thm (and (imp p (.or p q)) (imp p (.or p (.neg q)))) := andIh (t2_2 p q) (t2_2 p (.neg q))
  -- [Comp] ⊃ ⊢ : p . ⊃ . p ∨ q . p ∨ ∼q   (1)
  have h1 : Thm (imp p (and (.or p q) (.or p (.neg q)))) :=
    Thm.mp l1 (t3_43 p (.or p q) (.or p (.neg q)))
  -- ⊢ . ✱2·65 (∼p/p) . ⊃ ⊢ :. ∼p ⊃ q . ⊃ : ∼p ⊃ ∼q . ⊃ . p :.   [✱2·14]
  have l2 : Thm (imp (imp (.neg p) q) (imp (imp (.neg p) (.neg q)) p)) :=
    sylEnd (t2_65 (.neg p) q) (t2_14 p)
  -- [Imp] ⊃ ⊢ :. ∼p ⊃ q . ∼p ⊃ ∼q . ⊃ . p :.
  have l3 : Thm (imp (and (imp (.neg p) q) (imp (.neg p) (.neg q))) p) :=
    Thm.mp l2 (t3_31 (imp (.neg p) q) (imp (.neg p) (.neg q)) p)
  -- [✱2·53 . ✱3·47] ⊃ ⊢ :. p ∨ q . p ∨ ∼q . ⊃ . p   (2)
  have l4 : Thm (imp (and (.or p q) (.or p (.neg q))) (and (imp (.neg p) q) (imp (.neg p) (.neg q)))) :=
    Thm.mp (andIh (t2_53 p q) (t2_53 p (.neg q)))
      (t3_47 (.or p q) (.or p (.neg q)) (imp (.neg p) q) (imp (.neg p) (.neg q)))
  have h2 : Thm (imp (and (.or p q) (.or p (.neg q))) p) := syl l4 l3
  -- ⊢ . (1) . (2) . ⊃ ⊢ . Prop
  iffIh h1 h2

/-- *4.44 — PM Dem.: ✱2·2 (1); Id . ✱3·26; ✱3·44 (2); (1) . (2). -/
theorem t4_44 (p : F) (q : F) : Thm (s4_44 p q) :=
  -- ⊢ . ✱2·2 . ⊃ ⊢ :. p . ⊃ : p . ∨ . p . q   (1)
  have h1 : Thm (imp p (.or p (and p q))) := t2_2 p (and p q)
  -- ⊢ . Id . ✱3·26 . ⊃ ⊢ :. p ⊃ p : p . q . ⊃ . p :.
  have l1 : Thm (and (imp p p) (imp (and p q) p)) := andIh (t2_08 p) (t3_26 p q)
  -- [✱3·44] ⊃ ⊢ :. p . ∨ . p . q : ⊃ . p   (2)
  have h2 : Thm (imp (.or p (and p q)) p) := Thm.mp l1 (t3_44 p p (and p q))
  -- ⊢ . (1) . (2) . ⊃ ⊢ . Prop
  iffIh h1 h2

/-- *4.45 — [✱2·2, ✱3·2, ✱3·26] -/
theorem t4_45 (p : F) (q : F) : Thm (s4_45 p q) := ofPf <| by
  unfold s4_45; split_iff
  · exact andI (hy 0) (orIL (hy 0))
  · exact andE1 (hy 0)

/-- *4.52 — [cf. ✱4·5 (q/∼q), ✱4·13: proved directly by reductio] -/
theorem t4_52 (p : F) (q : F) : Thm (s4_52 p q) := ofPf <| by
  unfold s4_52; split_iff
  · exact negI (orE (hy 1) (absurd _ (andE1 (hy 0)) (hy 2)) (absurd _ (hy 2) (andE2 (hy 0))))
  · exact andI (byContra (absurd _ (orIL (hy 1)) (hy 0))) (negI (absurd _ (orIR (hy 1)) (hy 0)))

/-- *4.53 — [cf. ✱4·52, ✱4·12: proved directly by cases and reductio] -/
theorem t4_53 (p : F) (q : F) : Thm (s4_53 p q) := ofPf <| by
  unfold s4_53; split_iff
  · exact Pf.cases p (orIR (byContra (absurd _ (andI (hy 1) (hy 2)) (hy 0)))) (orIL (hy 1))
  · exact negI (orE (hy 0) (absurd _ (andE1 (hy 1)) (hy 2)) (absurd _ (hy 2) (andE2 (hy 1))))

/-- *4.56 — [cf. ✱4·54, ✱4·13: proved directly by reductio] -/
theorem t4_56 (p : F) (q : F) : Thm (s4_56 p q) := ofPf <| by
  unfold s4_56; split_iff
  · exact negI (orE (hy 1) (absurd _ (hy 2) (andE1 (hy 0))) (absurd _ (hy 2) (andE2 (hy 0))))
  · exact andI (negI (absurd _ (orIL (hy 1)) (hy 0))) (negI (absurd _ (orIR (hy 1)) (hy 0)))

/-- *4.57 — [cf. ✱4·56, ✱4·12: proved directly by reductio] -/
theorem t4_57 (p : F) (q : F) : Thm (s4_57 p q) := ofPf <| by
  unfold s4_57; split_iff
  · exact byContra (absurd _
      (andI (negI (absurd _ (orIL (hy 2)) (hy 1))) (negI (absurd _ (orIR (hy 2)) (hy 1)))) (hy 0))
  · exact negI (orE (hy 0) (absurd _ (hy 2) (andE1 (hy 1))) (absurd _ (hy 2) (andE2 (hy 1))))

/-- *4.61 — [cf. ✱4·6, ✱4·52: proved directly by reductio] -/
theorem t4_61 (p : F) (q : F) : Thm (s4_61 p q) := ofPf <| by
  unfold s4_61; split_iff
  · exact andI (byContra (absurd _ (Pf.intro (absurd _ (hy 2) (hy 1))) (hy 0)))
      (negI (absurd _ (Pf.intro (hy 1)) (hy 0)))
  · exact negI (absurd _ (mp (andE1 (hy 0)) (hy 1)) (andE2 (hy 0)))

/-- *4.65 — [✱4·61 (∼p/p)] -/
theorem t4_65 (p : F) (q : F) : Thm (s4_65 p q) := t4_61 (.neg p) q

/-- *4.7 — [✱3·2, ✱3·27] -/
theorem t4_7 (p : F) (q : F) : Thm (s4_7 p q) := ofPf <| by
  unfold s4_7; split_iff
  · exact Pf.intro (andI (hy 1) (mp (hy 1) (hy 0)))
  · exact Pf.intro (andE2 (mp (hy 1) (hy 0)))

/-- *4.71 — [✱3·2, ✱3·26, ✱3·27] -/
theorem t4_71 (p : F) (q : F) : Thm (s4_71 p q) := ofPf <| by
  unfold s4_71; split_iff
  · exact iffI (Pf.intro (andI (hy 1) (mp (hy 1) (hy 0)))) (Pf.intro (andE1 (hy 1)))
  · exact Pf.intro (andE2 (mp (hy 1) (iffMp (hy 0))))

/-- *4.72 — [✱1·3, ✱2·2, ∨-elimination, ✱3·2] -/
theorem t4_72 (p : F) (q : F) : Thm (s4_72 p q) := ofPf <| by
  unfold s4_72; split_iff
  · exact iffI (Pf.intro (orIR (hy 1))) (Pf.intro (orE (hy 1) (mp (hy 2) (hy 0)) (hy 2)))
  · exact Pf.intro (mp (orIL (hy 1)) (iffMpr (hy 0)))

/-- *4.73 — [✱3·2, ✱3·26 (cf. ✱4·71)] -/
theorem t4_73 (p : F) (q : F) : Thm (s4_73 p q) := ofPf <| by
  unfold s4_73; intro_
  exact iffI (Pf.intro (andI (hy 1) (hy 0))) (Pf.intro (andE1 (hy 1)))

/-- *4.74 — [✱1·3, ✱2·24, ∨-elimination, ✱3·2 (cf. ✱4·72)] -/
theorem t4_74 (p : F) (q : F) : Thm (s4_74 p q) := ofPf <| by
  unfold s4_74; intro_
  exact iffI (Pf.intro (orIR (hy 1))) (Pf.intro (orE (hy 1) (absurd _ (hy 2) (hy 0)) (hy 2)))

/-- *4.76 — [✱3·43 (→); ← by ✱3·26, ✱3·27] -/
theorem t4_76 (p : F) (q : F) (r : F) : Thm (s4_76 p q r) := ofPf <| by
  unfold s4_76; split_iff
  · exact app (t3_43 p q r) (hy 0)
  · exact andI (Pf.intro (andE1 (mp (hy 1) (hy 0)))) (Pf.intro (andE2 (mp (hy 1) (hy 0))))

/-- *4.77 — [✱3·44 (→); ← by ✱1·3, ✱2·2, ✱3·2] -/
theorem t4_77 (p : F) (q : F) (r : F) : Thm (s4_77 p q r) := ofPf <| by
  unfold s4_77; split_iff
  · exact app (t3_44 p q r) (hy 0)
  · exact andI (Pf.intro (mp (orIL (hy 1)) (hy 0))) (Pf.intro (mp (orIR (hy 1)) (hy 0)))

/-- *4.78 — [∨-elimination, ✱2·11 (cases), ✱1·3, ✱2·2, ✱2·24] -/
theorem t4_78 (p : F) (q : F) (r : F) : Thm (s4_78 p q r) := ofPf <| by
  unfold s4_78; split_iff
  · exact Pf.intro (orE (hy 0) (orIL (mp (hy 1) (hy 2))) (orIR (mp (hy 1) (hy 2))))
  · exact Pf.cases q (orIL (Pf.intro (hy 1)))
      (orIR (Pf.intro (orE (mp (hy 2) (hy 0)) (absurd _ (hy 3) (hy 1)) (hy 3))))

/-- *4.79 — [∨-elimination, ✱2·11 (cases), ✱3·2, ✱3·26, ✱3·27, ✱2·24] -/
theorem t4_79 (p : F) (q : F) (r : F) : Thm (s4_79 p q r) := ofPf <| by
  unfold s4_79; split_iff
  · exact Pf.intro (orE (hy 0) (mp (andE1 (hy 1)) (hy 2)) (mp (andE2 (hy 1)) (hy 2)))
  · exact Pf.cases q (orIR (Pf.intro (mp (andI (hy 1) (hy 2)) (hy 0))))
      (orIL (Pf.intro (absurd _ (hy 2) (hy 1))))

/-- *4.82 — [✱2·65 (→); ← by ✱2·21] -/
theorem t4_82 (p : F) (q : F) : Thm (s4_82 p q) := ofPf <| by
  unfold s4_82; split_iff
  · exact app2 (t2_65 p q) (andE1 (hy 0)) (andE2 (hy 0))
  · exact andI (app (t2_21 p q) (hy 0)) (app (t2_21 p (.neg q)) (hy 0))

/-- *4.83 — [✱2·61 (→); ← by ✱2·02] -/
theorem t4_83 (p : F) (q : F) : Thm (s4_83 p q) := ofPf <| by
  unfold s4_83; split_iff
  · exact app2 (t2_61 p q) (andE1 (hy 0)) (andE2 (hy 0))
  · exact andI (app (t2_02 p q) (hy 0)) (app (t2_02 (.neg p) q) (hy 0))

/-- *4.84 — [✱2·06, ✱3·2] -/
theorem t4_84 (p : F) (q : F) (r : F) : Thm (s4_84 p q r) := ofPf <| by
  unfold s4_84; intro_
  exact iffI (app (t2_06 q p r) (iffMpr (hy 0))) (app (t2_06 p q r) (iffMp (hy 0)))

/-- *4.85 — [✱2·05, ✱3·2] -/
theorem t4_85 (p : F) (q : F) (r : F) : Thm (s4_85 p q r) := ofPf <| by
  unfold s4_85; intro_
  exact iffI (app (t2_05 r p q) (iffMp (hy 0))) (app (t2_05 r q p) (iffMpr (hy 0)))

/-- *4.86 — [✱4·21, ✱4·22, ✱3·2] -/
theorem t4_86 (p : F) (q : F) (r : F) : Thm (s4_86 p q r) := ofPf <| by
  unfold s4_86; intro_
  exact iffI (Pf.intro (app (t4_22 q p r) (andI (iffE (ofThm (t4_21 p q)) (hy 0)) (hy 1))))
    (Pf.intro (app (t4_22 p q r) (andI (hy 0) (hy 1))))

/-- *4.87 — [✱3·3, ✱3·31, ✱2·04, ✱3·2] -/
theorem t4_87 (p : F) (q : F) (r : F) : Thm (s4_87 p q r) :=
  andIh (andIh (iffIh (t3_3 p q r) (t3_31 p q r)) (iffIh (t2_04 p q r) (t2_04 q p r)))
    (iffIh (t3_31 q p r) (t3_3 q p r))

/-- *5.1 — [✱3·26, ✱3·27, ✱2·02, ✱3·2] -/
theorem t5_1 (p : F) (q : F) : Thm (s5_1 p q) := ofPf <| by
  unfold s5_1; intro_
  exact iffI (Pf.intro (andE2 (hy 0))) (Pf.intro (andE1 (hy 0)))

/-- *5.15 — [✱2·11 (cases), ✱2·24, ✱3·2, ✱1·3, ✱2·2] -/
theorem t5_15 (p : F) (q : F) : Thm (s5_15 p q) := ofPf <| by
  unfold s5_15
  exact Pf.cases p
    (Pf.cases q (orIL (iffI (Pf.intro (hy 1)) (Pf.intro (hy 0))))
      (orIR (iffI (Pf.intro (hy 1)) (Pf.intro (hy 0)))))
    (Pf.cases q
      (orIR (iffI (Pf.intro (absurd _ (hy 2) (hy 0))) (Pf.intro (absurd _ (hy 1) (hy 2)))))
      (orIL (iffI (Pf.intro (absurd _ (hy 2) (hy 0))) (Pf.intro (absurd _ (hy 2) (hy 1))))))

/-- *5.16 — [✱2·01, ✱2·11 (cases), ✱2·24, ✱3·26, ✱3·27] -/
theorem t5_16 (p : F) (q : F) : Thm (s5_16 p q) := ofPf <| by
  unfold s5_16
  exact negI (absurd _
    (Pf.cases q (mp (hy 1) (iffMpr (andE1 (hy 0)))) (mp (hy 1) (iffMpr (andE2 (hy 0)))))
    (negI' q (mp (hy 1) (iffMp (andE1 (hy 0)))) (mp (hy 1) (iffMp (andE2 (hy 0))))))

/-- *5.17 — [∨-elimination, ✱2·11 (cases), ✱2·01, ✱2·18, ✱3·2] -/
theorem t5_17 (p : F) (q : F) : Thm (s5_17 p q) := ofPf <| by
  unfold s5_17; split_iff
  · exact iffI (Pf.intro (negI (absurd _ (andI (hy 1) (hy 2)) (andE2 (hy 0)))))
      (Pf.intro (orE (andE1 (hy 0)) (hy 2) (absurd _ (hy 2) (hy 1))))
  · exact andI
      (Pf.cases p (orIL (hy 1)) (orIR (byContra (absurd _ (mp (hy 2) (iffMpr (hy 0))) (hy 1)))))
      (negI (absurd _ (andE2 (hy 1)) (mp (andE1 (hy 1)) (iffMp (hy 0)))))

/-- *5.18 — [✱5·15, ✱5·16] -/
theorem t5_18 (p : F) (q : F) : Thm (s5_18 p q) := ofPf <| by
  unfold s5_18; split_iff
  · exact negI (absurd _ (andI (hy 0) (hy 1)) (ofThm (t5_16 p q)))
  · exact orE (ofThm (t5_15 p q)) (hy 1) (absurd _ (hy 1) (hy 0))

/-- *5.19 — [✱5·18 (p/q), ✱4·2] -/
theorem t5_19 (p : F) : Thm (s5_19 p) := Thm.mp (t4_2 p) (iffMph (t5_18 p p))

/-- *5.21 — [✱5·1 (∼p,∼q/p,q), ✱4·11] -/
theorem t5_21 (p : F) (q : F) : Thm (s5_21 p q) := ofPf <| by
  unfold s5_21; intro_
  exact iffE' (ofThm (t4_11 p q)) (app (t5_1 (.neg p) (.neg q)) (hy 0))

/-- *5.22 — [✱2·11 (cases), ✱2·01, ✱2·24, ∨-elimination, ✱3·2] -/
theorem t5_22 (p : F) (q : F) : Thm (s5_22 p q) := ofPf <| by
  unfold s5_22; split_iff
  · exact Pf.cases p
      (Pf.cases q (absurd _ (iffI (Pf.intro (hy 2)) (Pf.intro (hy 1))) (hy 0))
        (orIL (andI (hy 1) (hy 2))))
      (Pf.cases q (orIR (andI (hy 2) (hy 1)))
        (absurd _ (iffI (Pf.intro (absurd _ (hy 3) (hy 1))) (Pf.intro (absurd _ (hy 3) (hy 2))))
          (hy 0)))
  · exact negI (orE (hy 0) (absurd _ (mp (andE1 (hy 2)) (iffMp (hy 1))) (andE2 (hy 2)))
      (absurd _ (mp (andE1 (hy 2)) (iffMpr (hy 1))) (andE2 (hy 2))))

/-- *5.23 — [✱2·11 (cases); ← by ✱5·1, ✱5·21] -/
theorem t5_23 (p : F) (q : F) : Thm (s5_23 p q) := ofPf <| by
  unfold s5_23; split_iff
  · exact Pf.cases p (orIL (andI (hy 1) (mp (hy 1) (iffMp (hy 0)))))
      (orIR (andI (hy 1) (negI (absurd _ (mp (hy 2) (iffMpr (hy 0))) (hy 1)))))
  · exact orE (hy 0) (app (t5_1 p q) (hy 1)) (app (t5_21 p q) (hy 1))

/-- *5.24 — [✱5·22, ✱5·23] -/
theorem t5_24 (p : F) (q : F) : Thm (s5_24 p q) := ofPf <| by
  unfold s5_24; split_iff
  · exact iffE (ofThm (t5_22 p q)) (negI (absurd _ (iffE (ofThm (t5_23 p q)) (hy 1)) (hy 0)))
  · exact negI (absurd _ (iffE' (ofThm (t5_23 p q)) (hy 1)) (iffE' (ofThm (t5_22 p q)) (hy 0)))

/-- *5.3 — [✱3·2, ✱3·26, ✱3·27] -/
theorem t5_3 (p : F) (q : F) (r : F) : Thm (s5_3 p q r) := ofPf <| by
  unfold s5_3; split_iff
  · exact Pf.intro (andI (andE1 (hy 1)) (mp (hy 1) (hy 0)))
  · exact Pf.intro (andE2 (mp (hy 1) (hy 0)))

/-- *5.31 — [✱3·2, ✱3·26, ✱3·27] -/
theorem t5_31 (p : F) (q : F) (r : F) : Thm (s5_31 p q r) := ofPf <| by
  unfold s5_31; intro_; intro_
  exact andI (mp (hy 1) (andE2 (hy 0))) (andE1 (hy 0))

/-- *5.32 — [✱3·2, ✱3·26, ✱3·27] -/
theorem t5_32 (p : F) (q : F) (r : F) : Thm (s5_32 p q r) := ofPf <| by
  unfold s5_32; split_iff
  · exact iffI
      (Pf.intro (andI (andE1 (hy 1)) (mp (andE2 (hy 1)) (iffMp (mp (andE1 (hy 1)) (hy 0))))))
      (Pf.intro (andI (andE1 (hy 1)) (mp (andE2 (hy 1)) (iffMpr (mp (andE1 (hy 1)) (hy 0))))))
  · exact Pf.intro (iffI (Pf.intro (andE2 (mp (andI (hy 1) (hy 2)) (iffMp (hy 0)))))
      (Pf.intro (andE2 (mp (andI (hy 1) (hy 2)) (iffMpr (hy 0))))))

/-- *5.33 — [✱3·2, ✱3·26, ✱3·27] -/
theorem t5_33 (p : F) (q : F) (r : F) : Thm (s5_33 p q r) := ofPf <| by
  unfold s5_33; split_iff
  · exact andI (andE1 (hy 0)) (Pf.intro (mp (andE2 (hy 1)) (andE2 (hy 0))))
  · exact andI (andE1 (hy 0)) (Pf.intro (mp (andI (andE1 (hy 0)) (hy 1)) (andE2 (hy 0))))

/-- *5.35 — [✱3·26, ✱3·27, ✱3·2] -/
theorem t5_35 (p : F) (q : F) (r : F) : Thm (s5_35 p q r) := ofPf <| by
  unfold s5_35; intro_; intro_
  exact iffI (Pf.intro (mp (hy 1) (andE2 (hy 0)))) (Pf.intro (mp (hy 1) (andE1 (hy 0))))

/-- *5.36 — [✱3·2, ✱3·26, ✱3·27] -/
theorem t5_36 (p : F) (q : F) : Thm (s5_36 p q) := ofPf <| by
  unfold s5_36; split_iff
  · exact andI (mp (andE1 (hy 0)) (iffMp (andE2 (hy 0)))) (andE2 (hy 0))
  · exact andI (mp (andE1 (hy 0)) (iffMpr (andE2 (hy 0)))) (andE2 (hy 0))

/-- *5.41 — [✱2·86 (→), ✱2·77 (←)] -/
theorem t5_41 (p : F) (q : F) (r : F) : Thm (s5_41 p q r) := iffIh (t2_86 p q r) (t2_77 p q r)

/-- *5.42 — [✱3·2, ✱3·27] -/
theorem t5_42 (p : F) (q : F) (r : F) : Thm (s5_42 p q r) := ofPf <| by
  unfold s5_42; split_iff
  · exact Pf.intro (Pf.intro (andI (hy 1) (mp (hy 2) (mp (hy 1) (hy 0)))))
  · exact Pf.intro (Pf.intro (andE2 (mp (hy 2) (mp (hy 1) (hy 0)))))

/-- *5.44 — [✱3·2, ✱3·27] -/
theorem t5_44 (p : F) (q : F) (r : F) : Thm (s5_44 p q r) := ofPf <| by
  unfold s5_44; intro_
  exact iffI (Pf.intro (Pf.intro (andI (mp (hy 2) (hy 0)) (mp (hy 2) (hy 1)))))
    (Pf.intro (Pf.intro (andE2 (mp (hy 2) (hy 1)))))

/-- *5.5 — [✱1·1 under hypotheses, ✱2·02, ✱3·2] -/
theorem t5_5 (p : F) (q : F) : Thm (s5_5 p q) := ofPf <| by
  unfold s5_5; intro_
  exact iffI (Pf.intro (mp (hy 0) (hy 1))) (Pf.intro (Pf.intro (hy 1)))

/-- *5.501 — [✱2·02, ✱3·2, ✱3·26] -/
theorem t5_501 (p : F) (q : F) : Thm (s5_501 p q) := ofPf <| by
  unfold s5_501; intro_
  exact iffI (Pf.intro (iffI (Pf.intro (hy 1)) (Pf.intro (hy 0))))
    (Pf.intro (mp (hy 0) (iffMp (hy 1))))

/-- *5.53 — [cf. ✱4·77: ∨-elimination, ✱1·3, ✱2·2, ✱3·2, ✱3·26, ✱3·27] -/
theorem t5_53 (p : F) (q : F) (r : F) (s : F) : Thm (s5_53 p q r s) := ofPf <| by
  unfold s5_53; split_iff
  · exact andI (andI (Pf.intro (mp (orIL (orIL (hy 1))) (hy 0)))
      (Pf.intro (mp (orIL (orIR (hy 1))) (hy 0)))) (Pf.intro (mp (orIR (hy 1)) (hy 0)))
  · exact Pf.intro (orE (hy 1)
      (orE (hy 2) (mp (hy 3) (andE1 (andE1 (hy 0)))) (mp (hy 3) (andE2 (andE1 (hy 0)))))
      (mp (hy 2) (andE2 (hy 0))))

/-- *5.54 — [✱2·11 (cases), ✱3·2, ✱3·26, ✱3·27, ✱2·24] -/
theorem t5_54 (p : F) (q : F) : Thm (s5_54 p q) := ofPf <| by
  unfold s5_54
  exact Pf.cases p
    (orIR (iffI (Pf.intro (andE2 (hy 1))) (Pf.intro (andI (hy 0) (hy 1)))))
    (orIL (iffI (Pf.intro (andE1 (hy 1))) (Pf.intro (absurd _ (hy 1) (hy 0)))))

/-- *5.55 — [✱2·11 (cases), ∨-elimination, ✱1·3, ✱2·2, ✱2·24] -/
theorem t5_55 (p : F) (q : F) : Thm (s5_55 p q) := ofPf <| by
  unfold s5_55
  exact Pf.cases p
    (orIL (iffI (Pf.intro (hy 0)) (Pf.intro (orIL (hy 1)))))
    (orIR (iffI (Pf.intro (orE (hy 1) (absurd _ (hy 2) (hy 0)) (hy 2))) (Pf.intro (orIR (hy 1)))))

/-- *5.6 — [✱2·11 (cases), ∨-elimination, ✱3·2, ✱3·26, ✱3·27, ✱2·24] -/
theorem t5_6 (p : F) (q : F) (r : F) : Thm (s5_6 p q r) := ofPf <| by
  unfold s5_6; split_iff
  · exact Pf.intro (Pf.cases q (orIL (hy 2)) (orIR (mp (andI (hy 1) (hy 2)) (hy 0))))
  · exact Pf.intro (orE (mp (andE1 (hy 1)) (hy 0)) (absurd _ (hy 2) (andE2 (hy 1))) (hy 2))

/-- *5.61 — [∨-elimination, ✱2·2, ✱3·2, ✱3·26, ✱3·27, ✱2·24] -/
theorem t5_61 (p : F) (q : F) : Thm (s5_61 p q) := ofPf <| by
  unfold s5_61; split_iff
  · exact andI (orE (andE1 (hy 0)) (hy 1) (absurd _ (hy 1) (andE2 (hy 0)))) (andE2 (hy 0))
  · exact andI (orIL (andE1 (hy 0))) (andE2 (hy 0))

/-- *5.63 — [cf. ✱5·62: ∨-elimination, ✱2·11 (cases), ✱1·3, ✱2·2, ✱3·2, ✱3·27] -/
theorem t5_63 (p : F) (q : F) : Thm (s5_63 p q) := ofPf <| by
  unfold s5_63; split_iff
  · exact orE (hy 0) (orIL (hy 1)) (Pf.cases p (orIL (hy 2)) (orIR (andI (hy 2) (hy 1))))
  · exact orE (hy 0) (orIL (hy 1)) (orIR (andE2 (hy 1)))

/-- *5.7 — [✱2·11 (cases), ∨-elimination, ✱1·3, ✱2·2, ✱2·24, ✱3·2] -/
theorem t5_7 (p : F) (q : F) (r : F) : Thm (s5_7 p q r) := ofPf <| by
  unfold s5_7; split_iff
  · exact Pf.cases r (orIL (hy 1)) (orIR (iffI
      (Pf.intro (orE (mp (orIL (hy 2)) (iffMp (hy 0))) (hy 3) (absurd _ (hy 3) (hy 1))))
      (Pf.intro (orE (mp (orIL (hy 2)) (iffMpr (hy 0))) (hy 3) (absurd _ (hy 3) (hy 1))))))
  · exact orE (hy 0) (iffI (Pf.intro (orIR (hy 1))) (Pf.intro (orIR (hy 1))))
      (iffI (Pf.intro (orE (hy 2) (orIL (mp (hy 3) (iffMp (hy 1)))) (orIR (hy 3))))
        (Pf.intro (orE (hy 2) (orIL (mp (hy 3) (iffMpr (hy 1)))) (orIR (hy 3)))))

/-- *5.71 — [∨-elimination, ✱2·2, ✱2·24, ✱3·2, ✱3·26, ✱3·27] -/
theorem t5_71 (p : F) (q : F) (r : F) : Thm (s5_71 p q r) := ofPf <| by
  unfold s5_71; intro_
  exact iffI
    (Pf.intro (andI (orE (andE1 (hy 1)) (hy 2) (absurd _ (andE2 (hy 1)) (mp (hy 2) (hy 0))))
      (andE2 (hy 1))))
    (Pf.intro (andI (orIL (andE1 (hy 1))) (andE2 (hy 1))))

/-- *5.74 — [✱1·1 under hypotheses, ✱3·2, ✱3·26, ✱3·27] -/
theorem t5_74 (p : F) (q : F) (r : F) : Thm (s5_74 p q r) := ofPf <| by
  unfold s5_74; split_iff
  · exact iffI (Pf.intro (Pf.intro (mp (mp (hy 2) (hy 1)) (iffMp (mp (hy 2) (hy 0))))))
      (Pf.intro (Pf.intro (mp (mp (hy 2) (hy 1)) (iffMpr (mp (hy 2) (hy 0))))))
  · exact Pf.intro (iffI (Pf.intro (mp (hy 1) (mp (Pf.intro (hy 2)) (iffMp (hy 0)))))
      (Pf.intro (mp (hy 1) (mp (Pf.intro (hy 2)) (iffMpr (hy 0))))))

/-- *5.75 — [∨-elimination, ✱1·3, ✱2·24, ✱3·2, ✱3·26, ✱3·27] -/
theorem t5_75 (p : F) (q : F) (r : F) : Thm (s5_75 p q r) := ofPf <| by
  unfold s5_75; intro_
  exact iffI
    (Pf.intro (orE (mp (andE1 (hy 1)) (iffMp (andE2 (hy 0)))) (absurd _ (hy 2) (andE2 (hy 1)))
      (hy 2)))
    (Pf.intro (andI (mp (orIR (hy 1)) (iffMpr (andE2 (hy 0)))) (mp (hy 1) (andE1 (hy 0)))))

end PM
