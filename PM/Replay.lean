import PM.Statements
/-!
  Replay, part 1: 103 propositions of ✱2–✱5 as explicit `Thm` terms, tagged as in
  data/replay_ledger.json: FAITHFUL (only the propositions PM cites) or REPAIRED (also those listed as
  `extra`). Most terms were found by a search over PM's cited propositions. Those written as `have`
  lines follow PM's Dem. or bracketed hint, one Lean line per PM line, and use only the tacit steps of
  PM/Replay2.lean's header: Syll in a `⊃`-chain (✱2·05, ✱2·06) and ✱3·03 (by ✱3·2), named in each
  docstring and in the ledger row's `tacit`.
-/
namespace PM
open F

/-- *2.01 — FAITHFUL -/
theorem t2_01 (p : F) : Thm (s2_01 p) :=
  (Thm.taut (.neg p))

/-- *2.02 — FAITHFUL -/
theorem t2_02 (p : F) (q : F) : Thm (s2_02 p q) :=
  (Thm.add (.neg p) q)

/-- *2.03 — FAITHFUL -/
theorem t2_03 (p : F) (q : F) : Thm (s2_03 p q) :=
  (Thm.perm (.neg p) (.neg q))

/-- *2.04 — FAITHFUL -/
theorem t2_04 (p : F) (q : F) (r : F) : Thm (s2_04 p q r) :=
  (Thm.assoc (.neg p) (.neg q) r)

/-- *2.05 — FAITHFUL -/
theorem t2_05 (p : F) (q : F) (r : F) : Thm (s2_05 p q r) :=
  (Thm.sum (.neg p) q r)

/-- *2.06 — FAITHFUL -/
theorem t2_06 (p : F) (q : F) (r : F) : Thm (s2_06 p q r) :=
  (Thm.mp (t2_05 p q r) (t2_04 (.or (.neg q) r) (.or (.neg p) q) (.or (.neg p) r)))

/-- *2.07 — FAITHFUL -/
theorem t2_07 (p : F) : Thm (s2_07 p) :=
  (Thm.add p p)

/-- *2.08 — FAITHFUL. PM Dem.: ✱2·05 (p ∨ p, p / q, r) (1); Taut (2); (1) . (2) . ✱1·11 (3); ✱2·07 (4);
    (3) . (4) . ✱1·11. -/
theorem t2_08 (p : F) : Thm (s2_08 p) :=
  -- [✱2·05 (p ∨ p, p / q, r)] ⊢ :: p ∨ p . ⊃ . p : ⊃ :. p . ⊃ . p ∨ p : ⊃ . p ⊃ p   (1)
  have h1 : Thm (imp (imp (.or p p) p) (imp (imp p (.or p p)) (imp p p))) := t2_05 p (.or p p) p
  -- [Taut] ⊢ : p ∨ p . ⊃ . p   (2)
  have h2 : Thm (imp (.or p p) p) := Thm.taut p
  -- [(1) . (2) . ✱1·11] ⊢ :. p . ⊃ . p ∨ p : ⊃ . p ⊃ p   (3)
  have h3 : Thm (imp (imp p (.or p p)) (imp p p)) := Thm.mp h2 h1
  -- [✱2·07] ⊢ : p . ⊃ . p ∨ p   (4)
  have h4 : Thm (imp p (.or p p)) := t2_07 p
  -- [(3) . (4) . ✱1·11] ⊢ . p ⊃ p
  Thm.mp h4 h3

/-- *2.1 — FAITHFUL -/
theorem t2_1 (p : F) : Thm (s2_1 p) :=
  (t2_08 p)

/-- *2.11 — FAITHFUL -/
theorem t2_11 (p : F) : Thm (s2_11 p) :=
  (Thm.mp (Thm.mp (Thm.mp (t2_1 p) (Thm.perm (.neg p) p)) (t2_1 (.or p (.neg p)))) (t2_1 (.or p (.neg p))))

/-- *2.12 — FAITHFUL -/
theorem t2_12 (p : F) : Thm (s2_12 p) :=
  (t2_11 (.neg p))

/-- *2.13 — FAITHFUL -/
theorem t2_13 (p : F) : Thm (s2_13 p) :=
  (Thm.mp (t2_11 p) (Thm.mp (t2_12 (.neg p)) (Thm.sum p (.neg p) (.neg (.neg (.neg p))))))

/-- *2.14 — FAITHFUL -/
theorem t2_14 (p : F) : Thm (s2_14 p) :=
  (Thm.mp (t2_13 p) (Thm.perm p (.neg (.neg (.neg p)))))

/-- *2.15 — FAITHFUL -/
theorem t2_15 (p : F) (q : F) : Thm (s2_15 p q) :=
  (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (t2_12 q) (Thm.mp (t2_12 (.or (.neg q) (.neg (.neg q)))) (Thm.mp (t2_12 (.neg (.neg (.or (.neg q) (.neg (.neg q)))))) (t2_05 (.or (.neg q) (.neg (.neg q))) (.neg (.neg (.or (.neg q) (.neg (.neg q))))) (.neg (.neg (.neg (.neg (.or (.neg q) (.neg (.neg q))))))))))) (t2_14 (.neg (.neg (.or (.neg q) (.neg (.neg q))))))) (t2_14 (.or (.neg q) (.neg (.neg q))))) (Thm.mp (Thm.mp (Thm.mp (Thm.mp (t2_05 (.neg p) q (.neg (.neg q))) (Thm.mp (t2_12 (.or (.neg (.or (.neg q) (.neg (.neg q)))) (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg p)) (.neg (.neg q)))))) (Thm.mp (t2_12 (.neg (.neg (.or (.neg (.or (.neg q) (.neg (.neg q)))) (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg p)) (.neg (.neg q)))))))) (t2_05 (.or (.neg (.or (.neg q) (.neg (.neg q)))) (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg p)) (.neg (.neg q))))) (.neg (.neg (.or (.neg (.or (.neg q) (.neg (.neg q)))) (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg p)) (.neg (.neg q))))))) (.neg (.neg (.neg (.neg (.or (.neg (.or (.neg q) (.neg (.neg q)))) (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg p)) (.neg (.neg q))))))))))))) (t2_14 (.neg (.neg (.or (.neg (.or (.neg q) (.neg (.neg q)))) (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg p)) (.neg (.neg q))))))))) (t2_14 (.or (.neg (.or (.neg q) (.neg (.neg q)))) (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg p)) (.neg (.neg q))))))) (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (t2_03 (.neg p) (.neg q)) (Thm.mp (t2_12 (.or (.neg (.or (.neg (.neg p)) (.neg (.neg q)))) (.or (.neg (.neg q)) (.neg (.neg p))))) (Thm.mp (t2_12 (.neg (.neg (.or (.neg (.or (.neg (.neg p)) (.neg (.neg q)))) (.or (.neg (.neg q)) (.neg (.neg p))))))) (t2_05 (.or (.neg (.or (.neg (.neg p)) (.neg (.neg q)))) (.or (.neg (.neg q)) (.neg (.neg p)))) (.neg (.neg (.or (.neg (.or (.neg (.neg p)) (.neg (.neg q)))) (.or (.neg (.neg q)) (.neg (.neg p)))))) (.neg (.neg (.neg (.neg (.or (.neg (.or (.neg (.neg p)) (.neg (.neg q)))) (.or (.neg (.neg q)) (.neg (.neg p)))))))))))) (t2_14 (.neg (.neg (.or (.neg (.or (.neg (.neg p)) (.neg (.neg q)))) (.or (.neg (.neg q)) (.neg (.neg p)))))))) (t2_14 (.or (.neg (.or (.neg (.neg p)) (.neg (.neg q)))) (.or (.neg (.neg q)) (.neg (.neg p)))))) (t2_05 (.or (.neg (.neg p)) q) (.or (.neg (.neg p)) (.neg (.neg q))) (.or (.neg (.neg q)) (.neg (.neg p))))) (Thm.mp (t2_12 (.or (.neg (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg p)) (.neg (.neg q))))) (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) (.neg (.neg p)))))) (Thm.mp (t2_12 (.neg (.neg (.or (.neg (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg p)) (.neg (.neg q))))) (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) (.neg (.neg p)))))))) (t2_05 (.or (.neg (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg p)) (.neg (.neg q))))) (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) (.neg (.neg p))))) (.neg (.neg (.or (.neg (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg p)) (.neg (.neg q))))) (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) (.neg (.neg p))))))) (.neg (.neg (.neg (.neg (.or (.neg (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg p)) (.neg (.neg q))))) (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) (.neg (.neg p))))))))))))) (t2_14 (.neg (.neg (.or (.neg (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg p)) (.neg (.neg q))))) (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) (.neg (.neg p))))))))) (t2_14 (.or (.neg (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg p)) (.neg (.neg q))))) (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) (.neg (.neg p))))))) (t2_05 (.or (.neg q) (.neg (.neg q))) (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg p)) (.neg (.neg q)))) (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) (.neg (.neg p)))))))) (Thm.mp (t2_12 (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) (.neg (.neg p))))) (Thm.mp (t2_12 (.neg (.neg (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) (.neg (.neg p))))))) (t2_05 (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) (.neg (.neg p)))) (.neg (.neg (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) (.neg (.neg p)))))) (.neg (.neg (.neg (.neg (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) (.neg (.neg p)))))))))))) (t2_14 (.neg (.neg (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) (.neg (.neg p)))))))) (t2_14 (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) (.neg (.neg p)))))) (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (t2_14 p) (Thm.mp (Thm.mp (Thm.mp (Thm.mp (t2_05 (.neg q) (.neg (.neg p)) p) (Thm.mp (t2_12 (.or (.neg (.or (.neg (.neg (.neg p))) p)) (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p)))) (Thm.mp (t2_12 (.neg (.neg (.or (.neg (.or (.neg (.neg (.neg p))) p)) (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p)))))) (t2_05 (.or (.neg (.or (.neg (.neg (.neg p))) p)) (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p))) (.neg (.neg (.or (.neg (.or (.neg (.neg (.neg p))) p)) (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p))))) (.neg (.neg (.neg (.neg (.or (.neg (.or (.neg (.neg (.neg p))) p)) (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p))))))))))) (t2_14 (.neg (.neg (.or (.neg (.or (.neg (.neg (.neg p))) p)) (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p))))))) (t2_14 (.or (.neg (.or (.neg (.neg (.neg p))) p)) (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p))))) (Thm.mp (t2_12 (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p))) (t2_05 (.or (.neg (.neg (.neg p))) p) (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p)) (.neg (.neg (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p)))))))) (Thm.mp (Thm.mp (t2_12 (.neg (.neg (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p))))) (Thm.mp (t2_12 (.neg (.neg (.neg (.neg (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p))))))) (t2_05 (.neg (.neg (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p)))) (.neg (.neg (.neg (.neg (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p)))))) (.neg (.neg (.neg (.neg (.neg (.neg (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p))))))))))) (Thm.mp (t2_14 (.neg (.neg (.neg (.neg (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p))))))) (t2_05 (.neg (.neg (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p)))) (.neg (.neg (.neg (.neg (.neg (.neg (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p)))))))) (.neg (.neg (.neg (.neg (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p)))))))))) (t2_14 (.neg (.neg (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p)))))) (t2_14 (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p)))) (Thm.mp (Thm.mp (Thm.mp (t2_05 (.or (.neg (.neg p)) q) (.or (.neg (.neg q)) (.neg (.neg p))) (.or (.neg (.neg q)) p)) (Thm.mp (t2_12 (.or (.neg (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p))) (.or (.neg (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) (.neg (.neg p))))) (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) p))))) (Thm.mp (t2_12 (.neg (.neg (.or (.neg (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p))) (.or (.neg (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) (.neg (.neg p))))) (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) p))))))) (t2_05 (.or (.neg (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p))) (.or (.neg (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) (.neg (.neg p))))) (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) p)))) (.neg (.neg (.or (.neg (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p))) (.or (.neg (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) (.neg (.neg p))))) (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) p)))))) (.neg (.neg (.neg (.neg (.or (.neg (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p))) (.or (.neg (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) (.neg (.neg p))))) (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) p)))))))))))) (t2_14 (.neg (.neg (.or (.neg (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p))) (.or (.neg (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) (.neg (.neg p))))) (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) p)))))))) (t2_14 (.or (.neg (.or (.neg (.or (.neg (.neg q)) (.neg (.neg p)))) (.or (.neg (.neg q)) p))) (.or (.neg (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) (.neg (.neg p))))) (.or (.neg (.or (.neg (.neg p)) q)) (.or (.neg (.neg q)) p))))))))

/-- *2.16 — FAITHFUL -/
theorem t2_16 (p : F) (q : F) : Thm (s2_16 p q) :=
  (Thm.mp (t2_03 p (.neg q)) (Thm.mp (Thm.mp (Thm.mp (Thm.mp (t2_12 q) (t2_03 q (.neg q))) (t2_03 (.neg q) q)) (t2_05 p q (.neg (.neg q)))) (t2_06 (.or (.neg p) q) (.or (.neg p) (.neg (.neg q))) (.or (.neg (.neg q)) (.neg p)))))

/-- *2.17 — FAITHFUL -/
theorem t2_17 (p : F) (q : F) : Thm (s2_17 p q) :=
  (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (t2_14 q) (t2_05 p (.neg (.neg q)) q)) (Thm.mp (t2_14 (.neg (.or (.neg (.or (.neg p) (.neg (.neg q)))) (.or (.neg p) q)))) (t2_03 (.neg (.neg (.neg (.or (.neg (.or (.neg p) (.neg (.neg q)))) (.or (.neg p) q))))) (.or (.neg (.or (.neg p) (.neg (.neg q)))) (.or (.neg p) q))))) (t2_14 (.neg (.neg (.or (.neg (.or (.neg p) (.neg (.neg q)))) (.or (.neg p) q)))))) (t2_14 (.or (.neg (.or (.neg p) (.neg (.neg q)))) (.or (.neg p) q)))) (Thm.mp (Thm.mp (Thm.mp (Thm.mp (t2_03 (.neg q) p) (Thm.mp (t2_14 (.neg (.or (.neg (.or (.neg (.neg q)) (.neg p))) (.or (.neg p) (.neg (.neg q)))))) (t2_03 (.neg (.neg (.neg (.or (.neg (.or (.neg (.neg q)) (.neg p))) (.or (.neg p) (.neg (.neg q))))))) (.or (.neg (.or (.neg (.neg q)) (.neg p))) (.or (.neg p) (.neg (.neg q))))))) (t2_14 (.neg (.neg (.or (.neg (.or (.neg (.neg q)) (.neg p))) (.or (.neg p) (.neg (.neg q)))))))) (t2_14 (.or (.neg (.or (.neg (.neg q)) (.neg p))) (.or (.neg p) (.neg (.neg q)))))) (t2_06 (.or (.neg (.neg q)) (.neg p)) (.or (.neg p) (.neg (.neg q))) (.or (.neg p) q)))) (Thm.mp (t2_14 (.neg (.or (.neg (.or (.neg (.neg q)) (.neg p))) (.or (.neg p) q)))) (t2_03 (.neg (.neg (.neg (.or (.neg (.or (.neg (.neg q)) (.neg p))) (.or (.neg p) q))))) (.or (.neg (.or (.neg (.neg q)) (.neg p))) (.or (.neg p) q))))) (t2_14 (.neg (.neg (.or (.neg (.or (.neg (.neg q)) (.neg p))) (.or (.neg p) q)))))) (t2_14 (.or (.neg (.or (.neg (.neg q)) (.neg p))) (.or (.neg p) q))))

/-- *2.18 — FAITHFUL -/
theorem t2_18 (p : F) : Thm (s2_18 p) :=
  (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (t2_12 p) (Thm.mp (t2_12 (.or (.neg p) (.neg (.neg p)))) (Thm.mp (t2_12 (.neg (.neg (.or (.neg p) (.neg (.neg p)))))) (t2_05 (.or (.neg p) (.neg (.neg p))) (.neg (.neg (.or (.neg p) (.neg (.neg p))))) (.neg (.neg (.neg (.neg (.or (.neg p) (.neg (.neg p))))))))))) (t2_14 (.neg (.neg (.or (.neg p) (.neg (.neg p))))))) (t2_14 (.or (.neg p) (.neg (.neg p))))) (t2_05 (.neg p) p (.neg (.neg p)))) (Thm.mp (t2_12 (.or (.neg (.or (.neg (.neg p)) p)) (.or (.neg (.neg p)) (.neg (.neg p))))) (Thm.mp (t2_12 (.neg (.neg (.or (.neg (.or (.neg (.neg p)) p)) (.or (.neg (.neg p)) (.neg (.neg p))))))) (t2_05 (.or (.neg (.or (.neg (.neg p)) p)) (.or (.neg (.neg p)) (.neg (.neg p)))) (.neg (.neg (.or (.neg (.or (.neg (.neg p)) p)) (.or (.neg (.neg p)) (.neg (.neg p)))))) (.neg (.neg (.neg (.neg (.or (.neg (.or (.neg (.neg p)) p)) (.or (.neg (.neg p)) (.neg (.neg p)))))))))))) (t2_14 (.neg (.neg (.or (.neg (.or (.neg (.neg p)) p)) (.or (.neg (.neg p)) (.neg (.neg p)))))))) (t2_14 (.or (.neg (.or (.neg (.neg p)) p)) (.or (.neg (.neg p)) (.neg (.neg p)))))) (Thm.mp (Thm.mp (Thm.mp (Thm.mp (t2_01 (.neg p)) (Thm.mp (t2_12 (.or (.neg (.or (.neg (.neg p)) (.neg (.neg p)))) (.neg (.neg p)))) (Thm.mp (t2_12 (.neg (.neg (.or (.neg (.or (.neg (.neg p)) (.neg (.neg p)))) (.neg (.neg p)))))) (t2_05 (.or (.neg (.or (.neg (.neg p)) (.neg (.neg p)))) (.neg (.neg p))) (.neg (.neg (.or (.neg (.or (.neg (.neg p)) (.neg (.neg p)))) (.neg (.neg p))))) (.neg (.neg (.neg (.neg (.or (.neg (.or (.neg (.neg p)) (.neg (.neg p)))) (.neg (.neg p))))))))))) (t2_14 (.neg (.neg (.or (.neg (.or (.neg (.neg p)) (.neg (.neg p)))) (.neg (.neg p))))))) (t2_14 (.or (.neg (.or (.neg (.neg p)) (.neg (.neg p)))) (.neg (.neg p))))) (t2_05 (.or (.neg (.neg p)) p) (.or (.neg (.neg p)) (.neg (.neg p))) (.neg (.neg p))))) (Thm.mp (t2_12 (.or (.neg (.or (.neg (.neg p)) p)) (.neg (.neg p)))) (Thm.mp (t2_12 (.neg (.neg (.or (.neg (.or (.neg (.neg p)) p)) (.neg (.neg p)))))) (t2_05 (.or (.neg (.or (.neg (.neg p)) p)) (.neg (.neg p))) (.neg (.neg (.or (.neg (.or (.neg (.neg p)) p)) (.neg (.neg p))))) (.neg (.neg (.neg (.neg (.or (.neg (.or (.neg (.neg p)) p)) (.neg (.neg p))))))))))) (t2_14 (.neg (.neg (.or (.neg (.or (.neg (.neg p)) p)) (.neg (.neg p))))))) (t2_14 (.or (.neg (.or (.neg (.neg p)) p)) (.neg (.neg p))))) (Thm.mp (t2_14 p) (t2_05 (.or (.neg (.neg p)) p) (.neg (.neg p)) p))) (Thm.mp (t2_12 (.or (.neg (.or (.neg (.neg p)) p)) p)) (Thm.mp (t2_12 (.neg (.neg (.or (.neg (.or (.neg (.neg p)) p)) p)))) (t2_05 (.or (.neg (.or (.neg (.neg p)) p)) p) (.neg (.neg (.or (.neg (.or (.neg (.neg p)) p)) p))) (.neg (.neg (.neg (.neg (.or (.neg (.or (.neg (.neg p)) p)) p))))))))) (t2_14 (.neg (.neg (.or (.neg (.or (.neg (.neg p)) p)) p))))) (t2_14 (.or (.neg (.or (.neg (.neg p)) p)) p)))

/-- *2.2 — FAITHFUL -/
theorem t2_2 (p : F) (q : F) : Thm (s2_2 p q) :=
  (Thm.mp (Thm.mp (Thm.mp (Thm.perm q p) (Thm.mp (Thm.mp (Thm.mp (Thm.add q p) (Thm.perm (.neg p) (.or q p))) (Thm.perm (.or q p) (.neg p))) (t2_06 p (.or q p) (.or p q)))) (Thm.perm (.neg p) (.or p q))) (Thm.perm (.or p q) (.neg p)))

/-- *2.21 — FAITHFUL -/
theorem t2_21 (p : F) (q : F) : Thm (s2_21 p q) :=
  (t2_2 (.neg p) q)

/-- *2.24 — FAITHFUL -/
theorem t2_24 (p : F) (q : F) : Thm (s2_24 p q) :=
  (Thm.mp (Thm.mp (Thm.mp (t2_21 p q) (t2_04 (.neg p) p q)) (t2_04 p (.neg p) q)) (t2_04 (.neg p) p q))

/-- *2.25 — FAITHFUL -/
theorem t2_25 (p : F) (q : F) : Thm (s2_25 p q) :=
  (Thm.mp (Thm.mp (Thm.mp (t2_1 (.or p q)) (Thm.assoc (.neg (.or p q)) p q)) (Thm.assoc p (.neg (.or p q)) q)) (Thm.assoc (.neg (.or p q)) p q))

/-- *2.26 — FAITHFUL -/
theorem t2_26 (p : F) (q : F) : Thm (s2_26 p q) :=
  (t2_25 (.neg p) q)

/-- *2.27 — FAITHFUL -/
theorem t2_27 (p : F) (q : F) : Thm (s2_27 p q) :=
  (t2_26 p q)

/-- *2.3 — FAITHFUL -/
theorem t2_3 (p : F) (q : F) (r : F) : Thm (s2_3 p q r) :=
  (Thm.mp (Thm.perm q r) (Thm.sum p (.or q r) (.or r q)))

/-- *2.31 — FAITHFUL -/
theorem t2_31 (p : F) (q : F) (r : F) : Thm (s2_31 p q r) :=
  (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.assoc p r q) (Thm.perm (.neg (.or p (.or r q))) (.or r (.or p q)))) (Thm.perm (.or r (.or p q)) (.neg (.or p (.or r q))))) (Thm.mp (Thm.mp (Thm.mp (t2_3 p q r) (Thm.perm (.neg (.or p (.or q r))) (.or p (.or r q)))) (Thm.perm (.or p (.or r q)) (.neg (.or p (.or q r))))) (t2_06 (.or p (.or q r)) (.or p (.or r q)) (.or r (.or p q))))) (Thm.perm (.neg (.or p (.or q r))) (.or r (.or p q)))) (Thm.perm (.or r (.or p q)) (.neg (.or p (.or q r))))) (Thm.mp (Thm.perm r (.or p q)) (t2_05 (.or p (.or q r)) (.or r (.or p q)) (.or (.or p q) r)))) (Thm.perm (.neg (.or p (.or q r))) (.or (.or p q) r))) (Thm.perm (.or (.or p q) r) (.neg (.or p (.or q r)))))

/-- *2.32 — FAITHFUL. PM Dem.: Perm; Assoc; ✱2·3, a ⊃-chain joined by the tacit Syll (✱2·05). -/
theorem t2_32 (p : F) (q : F) (r : F) : Thm (s2_32 p q r) :=
  -- [Perm (p ∨ q, r / p, q)] ⊢ : (p ∨ q) ∨ r . ⊃ . r ∨ (p ∨ q)
  have l1 : Thm (imp (.or (.or p q) r) (.or r (.or p q))) := Thm.perm (.or p q) r
  -- [Assoc (r, p, q / p, q, r)] ⊃ . p ∨ (r ∨ q)
  have l2 : Thm (imp (.or r (.or p q)) (.or p (.or r q))) := Thm.assoc r p q
  have c2 : Thm (imp (.or (.or p q) r) (.or p (.or r q))) :=
    Thm.mp l1 (Thm.mp l2 (t2_05 (.or (.or p q) r) (.or r (.or p q)) (.or p (.or r q))))
  -- [✱2·3] ⊃ . p ∨ (q ∨ r) : ⊃ ⊢ . Prop
  have l3 : Thm (imp (.or p (.or r q)) (.or p (.or q r))) := t2_3 p r q
  Thm.mp c2 (Thm.mp l3 (t2_05 (.or (.or p q) r) (.or p (.or r q)) (.or p (.or q r))))

/-- *2.36 — FAITHFUL -/
theorem t2_36 (p : F) (q : F) (r : F) : Thm (s2_36 p q r) :=
  (Thm.mp (Thm.mp (Thm.mp (Thm.sum p q r) (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.perm p r) (Thm.sum (.neg (.or p q)) (.or p r) (.or r p))) (Thm.perm (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg (.or p q)) (.or r p)))) (Thm.perm (.or (.neg (.or p q)) (.or r p)) (.neg (.or (.neg (.or p q)) (.or p r))))) (Thm.sum (.neg (.or (.neg q) r)) (.or (.neg (.or p q)) (.or p r)) (.or (.neg (.or p q)) (.or r p))))) (Thm.perm (.neg (.or (.neg q) r)) (.or (.neg (.or p q)) (.or r p)))) (Thm.perm (.or (.neg (.or p q)) (.or r p)) (.neg (.or (.neg q) r))))

/-- *2.37 — FAITHFUL -/
theorem t2_37 (p : F) (q : F) (r : F) : Thm (s2_37 p q r) :=
  (Thm.mp (Thm.mp (Thm.mp (Thm.sum p q r) (Thm.mp (Thm.mp (Thm.perm q p) (t2_06 (.or q p) (.or p q) (.or p r))) (Thm.sum (.neg (.or (.neg q) r)) (.or (.neg (.or p q)) (.or p r)) (.or (.neg (.or q p)) (.or p r))))) (Thm.perm (.neg (.or (.neg q) r)) (.or (.neg (.or q p)) (.or p r)))) (Thm.perm (.or (.neg (.or q p)) (.or p r)) (.neg (.or (.neg q) r))))

/-- *2.38 — FAITHFUL. PM: [Syll . Perm . Sum], "exactly analogous" to ✱2·36 (p. 111); ✱2·36's Dem.
    with one more Perm, on the antecedent. -/
theorem t2_38 (p : F) (q : F) (r : F) : Thm (s2_38 p q r) :=
  -- [Perm] ⊢ : p ∨ r . ⊃ . r ∨ p :
  have l1 : Thm (imp (.or p r) (.or r p)) := Thm.perm p r
  -- [Syll] ⊃ ⊢ :. p ∨ q . ⊃ . p ∨ r : ⊃ : p ∨ q . ⊃ . r ∨ p   (1)
  have h1 : Thm (imp (imp (.or p q) (.or p r)) (imp (.or p q) (.or r p))) :=
    Thm.mp l1 (t2_05 (.or p q) (.or p r) (.or r p))
  -- [Sum] ⊢ :. q ⊃ r . ⊃ : p ∨ q . ⊃ . p ∨ r   (2)
  have h2 : Thm (imp (imp q r) (imp (.or p q) (.or p r))) := Thm.sum p q r
  -- [Perm] ⊢ : q ∨ p . ⊃ . p ∨ q :
  have l2 : Thm (imp (.or q p) (.or p q)) := Thm.perm q p
  -- [Syll] ⊃ ⊢ :. p ∨ q . ⊃ . r ∨ p : ⊃ : q ∨ p . ⊃ . r ∨ p   (3)
  have h3 : Thm (imp (imp (.or p q) (.or r p)) (imp (.or q p) (.or r p))) :=
    Thm.mp l2 (t2_06 (.or q p) (.or p q) (.or r p))
  -- ⊢ . (2) . (1) . (3) . Syll . ⊃ ⊢ . Prop
  have h21 : Thm (imp (imp q r) (imp (.or p q) (.or r p))) :=
    Thm.mp h2 (Thm.mp h1 (t2_05 (imp q r) (imp (.or p q) (.or p r)) (imp (.or p q) (.or r p))))
  Thm.mp h21 (Thm.mp h3 (t2_05 (imp q r) (imp (.or p q) (.or r p)) (imp (.or q p) (.or r p))))

/-- *2.4 — FAITHFUL -/
theorem t2_4 (p : F) (q : F) : Thm (s2_4 p q) :=
  (Thm.mp (t2_31 p p q) (Thm.mp (Thm.mp (Thm.taut p) (t2_38 q (.or p p) p)) (t2_05 (.or p (.or p q)) (.or (.or p p) q) (.or p q))))

/-- *2.41 — FAITHFUL -/
theorem t2_41 (p : F) (q : F) : Thm (s2_41 p q) :=
  (Thm.mp (Thm.assoc q p q) (Thm.mp (Thm.mp (Thm.taut q) (Thm.sum p (.or q q) q)) (Thm.sum (.neg (.or q (.or p q))) (.or p (.or q q)) (.or p q))))

/-- *2.42 — FAITHFUL -/
theorem t2_42 (p : F) (q : F) : Thm (s2_42 p q) :=
  (t2_4 (.neg p) q)

/-- *2.43 — FAITHFUL -/
theorem t2_43 (p : F) (q : F) : Thm (s2_43 p q) :=
  (t2_42 p q)

/-- *2.45 — FAITHFUL -/
theorem t2_45 (p : F) (q : F) : Thm (s2_45 p q) :=
  (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (t2_2 p q) (t2_16 p (.or p q))) (Thm.mp (Thm.mp (t2_16 (.neg (.or p q)) (.neg p)) (t2_16 (.or (.neg (.neg (.or p q))) (.neg p)) (.or (.neg (.neg (.neg p))) (.neg (.neg (.or p q)))))) (t2_17 (.or (.neg (.neg (.or p q))) (.neg p)) (.or (.neg (.neg (.neg p))) (.neg (.neg (.or p q))))))) (Thm.mp (Thm.mp (t2_16 (.neg (.neg p)) (.neg (.neg (.or p q)))) (Thm.mp (Thm.mp (t2_16 (.or (.neg (.neg (.neg p))) (.neg (.neg (.or p q)))) (.or (.neg (.neg (.neg (.neg (.or p q))))) (.neg (.neg (.neg p))))) (t2_16 (.or (.neg (.or (.neg (.neg (.neg p))) (.neg (.neg (.or p q))))) (.or (.neg (.neg (.neg (.neg (.or p q))))) (.neg (.neg (.neg p))))) (.or (.neg (.neg (.or (.neg (.neg (.neg (.neg (.or p q))))) (.neg (.neg (.neg p)))))) (.neg (.or (.neg (.neg (.neg p))) (.neg (.neg (.or p q)))))))) (t2_17 (.or (.neg (.or (.neg (.neg (.neg p))) (.neg (.neg (.or p q))))) (.or (.neg (.neg (.neg (.neg (.or p q))))) (.neg (.neg (.neg p))))) (.or (.neg (.neg (.or (.neg (.neg (.neg (.neg (.or p q))))) (.neg (.neg (.neg p)))))) (.neg (.or (.neg (.neg (.neg p))) (.neg (.neg (.or p q))))))))) (t2_17 (.or (.neg (.neg (.neg p))) (.neg (.neg (.or p q)))) (.or (.neg (.neg (.neg (.neg (.or p q))))) (.neg (.neg (.neg p))))))) (t2_17 (.neg (.neg p)) (.neg (.neg (.or p q))))) (t2_17 (.neg (.or p q)) (.neg p)))

/-- *2.46 — FAITHFUL -/
theorem t2_46 (p : F) (q : F) : Thm (s2_46 p q) :=
  (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.add p q) (t2_16 q (.or p q))) (Thm.mp (Thm.mp (t2_16 (.neg (.or p q)) (.neg q)) (t2_16 (.or (.neg (.neg (.or p q))) (.neg q)) (.or (.neg (.neg (.neg q))) (.neg (.neg (.or p q)))))) (t2_17 (.or (.neg (.neg (.or p q))) (.neg q)) (.or (.neg (.neg (.neg q))) (.neg (.neg (.or p q))))))) (Thm.mp (Thm.mp (t2_15 (.neg q) (.neg (.neg (.or p q)))) (Thm.mp (Thm.mp (t2_16 (.or (.neg (.neg (.neg q))) (.neg (.neg (.or p q)))) (.or (.neg (.neg (.neg (.neg (.or p q))))) (.neg q))) (t2_16 (.or (.neg (.or (.neg (.neg (.neg q))) (.neg (.neg (.or p q))))) (.or (.neg (.neg (.neg (.neg (.or p q))))) (.neg q))) (.or (.neg (.neg (.or (.neg (.neg (.neg (.neg (.or p q))))) (.neg q)))) (.neg (.or (.neg (.neg (.neg q))) (.neg (.neg (.or p q)))))))) (t2_17 (.or (.neg (.or (.neg (.neg (.neg q))) (.neg (.neg (.or p q))))) (.or (.neg (.neg (.neg (.neg (.or p q))))) (.neg q))) (.or (.neg (.neg (.or (.neg (.neg (.neg (.neg (.or p q))))) (.neg q)))) (.neg (.or (.neg (.neg (.neg q))) (.neg (.neg (.or p q))))))))) (t2_17 (.or (.neg (.neg (.neg q))) (.neg (.neg (.or p q)))) (.or (.neg (.neg (.neg (.neg (.or p q))))) (.neg q))))) (t2_15 (.neg (.neg (.or p q))) (.neg q))) (t2_17 (.neg (.or p q)) (.neg q)))

/-- *2.47 — FAITHFUL -/
theorem t2_47 (p : F) (q : F) : Thm (s2_47 p q) :=
  (Thm.mp (t2_2 (.neg p) q) (Thm.mp (t2_45 p q) (t2_06 (.neg (.or p q)) (.neg p) (.or (.neg p) q))))

/-- *2.48 — FAITHFUL -/
theorem t2_48 (p : F) (q : F) : Thm (s2_48 p q) :=
  (Thm.mp (Thm.add p (.neg q)) (Thm.mp (t2_46 p q) (t2_06 (.neg (.or p q)) (.neg q) (.or p (.neg q)))))

/-- *2.49 — FAITHFUL -/
theorem t2_49 (p : F) (q : F) : Thm (s2_49 p q) :=
  (Thm.mp (t2_2 (.neg p) (.neg q)) (Thm.mp (t2_45 p q) (t2_06 (.neg (.or p q)) (.neg p) (.or (.neg p) (.neg q)))))

/-- *2.5 — FAITHFUL -/
theorem t2_5 (p : F) (q : F) : Thm (s2_5 p q) :=
  (t2_47 (.neg p) q)

/-- *2.51 — FAITHFUL -/
theorem t2_51 (p : F) (q : F) : Thm (s2_51 p q) :=
  (t2_48 (.neg p) q)

/-- *2.52 — FAITHFUL -/
theorem t2_52 (p : F) (q : F) : Thm (s2_52 p q) :=
  (t2_49 (.neg p) q)

/-- *2.521 — FAITHFUL. PM: [✱2·52·17] (hint only); the two joined by the tacit Syll (✱2·05). -/
theorem t2_521 (p : F) (q : F) : Thm (s2_521 p q) :=
  -- [✱2·52] ⊢ : ∼(p ⊃ q) . ⊃ . ∼p ⊃ ∼q :
  have l1 : Thm (imp (.neg (imp p q)) (imp (.neg p) (.neg q))) := t2_52 p q
  -- [✱2·17 (q, p / p, q)] ⊃ . q ⊃ p
  have l2 : Thm (imp (imp (.neg p) (.neg q)) (imp q p)) := t2_17 q p
  Thm.mp l1 (Thm.mp l2 (t2_05 (.neg (imp p q)) (imp (.neg p) (.neg q)) (imp q p)))

/-- *2.53 — FAITHFUL. PM Dem.: ✱2·12·38; the last line is ∼p ⊃ q by ✱1·01. -/
theorem t2_53 (p : F) (q : F) : Thm (s2_53 p q) :=
  -- ⊢ . ✱2·12 . ✱2·38 . ⊃ ⊢ : p ∨ q . ⊃ . ∼(∼p) ∨ q : ⊃ ⊢ . Prop
  (Thm.mp (t2_12 p) (t2_38 q p (.neg (.neg p))))

/-- *2.54 — FAITHFUL -/
theorem t2_54 (p : F) (q : F) : Thm (s2_54 p q) :=
  (Thm.mp (t2_14 p) (t2_38 q (.neg (.neg p)) p))

/-- *2.55 — FAITHFUL -/
theorem t2_55 (p : F) (q : F) : Thm (s2_55 p q) :=
  (Thm.mp (t2_53 p q) (t2_04 (.or p q) (.neg p) q))

/-- *2.56 — FAITHFUL. PM: [✱2·55 (q, p / p, q) . Perm] (hint only); Perm is applied to the antecedent
    by the tacit Syll (✱2·05, ✱2·06). -/
theorem t2_56 (p : F) (q : F) : Thm (s2_56 p q) :=
  -- [✱2·55 (q, p / p, q)] ⊢ :. ∼q . ⊃ : q ∨ p . ⊃ . p
  have l1 : Thm (imp (.neg q) (imp (.or q p) p)) := t2_55 q p
  -- [Perm] ⊢ : p ∨ q . ⊃ . q ∨ p
  have l2 : Thm (imp (.or p q) (.or q p)) := Thm.perm p q
  -- ⊃ ⊢ :. ∼q . ⊃ : p ∨ q . ⊃ . p
  Thm.mp l1 (Thm.mp (Thm.mp l2 (t2_06 (.or p q) (.or q p) p))
    (t2_05 (.neg q) (imp (.or q p) p) (imp (.or p q) p)))

/-- *2.6 — FAITHFUL -/
theorem t2_6 (p : F) (q : F) : Thm (s2_6 p q) :=
  (Thm.mp (Thm.mp (Thm.taut q) (t2_05 (.or (.neg p) q) (.or q q) q)) (Thm.mp (t2_38 q (.neg p) q) (t2_06 (.or (.neg (.neg p)) q) (.or (.neg (.or (.neg p) q)) (.or q q)) (.or (.neg (.or (.neg p) q)) q))))

/-- *2.61 — FAITHFUL -/
theorem t2_61 (p : F) (q : F) : Thm (s2_61 p q) :=
  (Thm.mp (Thm.mp (Thm.mp (t2_6 p q) (t2_04 (.or (.neg (.neg p)) q) (.or (.neg p) q) q)) (t2_04 (.or (.neg p) q) (.or (.neg (.neg p)) q) q)) (t2_04 (.or (.neg (.neg p)) q) (.or (.neg p) q) q))

/-- *2.62 — FAITHFUL -/
theorem t2_62 (p : F) (q : F) : Thm (s2_62 p q) :=
  (Thm.mp (t2_6 p q) (Thm.mp (t2_53 p q) (t2_06 (.or p q) (.or (.neg (.neg p)) q) (.or (.neg (.or (.neg p) q)) q))))

/-- *2.621 — FAITHFUL -/
theorem t2_621 (p : F) (q : F) : Thm (s2_621 p q) :=
  (Thm.mp (Thm.mp (Thm.mp (t2_62 p q) (t2_04 (.or p q) (.or (.neg p) q) q)) (t2_04 (.or (.neg p) q) (.or p q) q)) (t2_04 (.or p q) (.or (.neg p) q) q))

/-- *2.63 — FAITHFUL -/
theorem t2_63 (p : F) (q : F) : Thm (s2_63 p q) :=
  (t2_62 p q)

/-- *2.67 — FAITHFUL -/
theorem t2_67 (p : F) (q : F) : Thm (s2_67 p q) :=
  (Thm.mp (Thm.mp (t2_54 p q) (Thm.mp (t2_24 p q) (t2_06 p (.or (.neg (.neg p)) q) (.or p q)))) (t2_06 p (.or p q) q))

/-- *2.68 — FAITHFUL. PM Dem.: ✱2·67 (∼p/p) (1); (1) . ✱2·54 (Syll tacit, ✱2·05). -/
theorem t2_68 (p : F) (q : F) : Thm (s2_68 p q) :=
  -- [✱2·67 (∼p/p)] ⊢ :. p ⊃ q . ⊃ . q : ⊃ . ∼p ⊃ q   (1)
  have h1 : Thm (imp (imp (imp p q) q) (imp (.neg p) q)) := t2_67 (.neg p) q
  -- ⊢ . (1) . ✱2·54 . ⊃ ⊢ . Prop
  Thm.mp h1 (Thm.mp (t2_54 p q) (t2_05 (imp (imp p q) q) (imp (.neg p) q) (.or p q)))

/-- *2.8 — FAITHFUL -/
theorem t2_8 (q : F) (r : F) (s : F) : Thm (s2_8 q r s) :=
  (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (t2_53 r q) (Thm.mp (Thm.mp (Thm.mp (Thm.perm q r) (Thm.perm (.neg (.or q r)) (.or r q))) (t2_53 (.or r q) (.neg (.or q r)))) (t2_38 (.or (.neg (.neg r)) q) (.neg (.or r q)) (.neg (.or q r))))) (Thm.perm (.neg (.or q r)) (.or (.neg (.neg r)) q))) (Thm.perm (.or (.neg (.neg r)) q) (.neg (.or q r)))) (Thm.perm (.neg (.or q r)) (.or (.neg (.neg r)) q))) (Thm.mp (t2_38 s (.neg r) q) (t2_38 (.neg (.or q r)) (.or (.neg (.neg r)) q) (.or (.neg (.or (.neg r) s)) (.or q s))))) (Thm.perm (.or (.neg (.or (.neg r) s)) (.or q s)) (.neg (.or q r))))

/-- *2.85 — REPAIRED (extra: *1.5, *1.6) -/
theorem t2_85 (p : F) (q : F) (r : F) : Thm (s2_85 p q r) :=
  (Thm.mp (Thm.mp (Thm.mp (Thm.assoc (.neg (.or p q)) p r) (Thm.assoc (.neg (.or (.neg (.or p q)) (.or p r))) p (.or (.neg (.or p q)) r))) (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.add p q) (Thm.mp (t2_05 q (.or p q) r) (t2_04 (.or (.neg (.or p q)) r) (.or (.neg q) (.or p q)) (.or (.neg q) r)))) (Thm.mp (Thm.mp (t2_55 (.neg (.or (.neg (.or p q)) r)) (.or (.neg q) r)) (Thm.mp (t2_55 (.neg (.neg (.neg (.or (.neg (.or p q)) r)))) (.or (.neg (.or (.neg (.or (.neg (.or p q)) r)) (.or (.neg q) r))) (.or (.neg q) r))) (t2_04 (.neg (.neg (.neg (.neg (.or (.neg (.or p q)) r))))) (.or (.neg (.neg (.neg (.or (.neg (.or p q)) r)))) (.or (.neg (.or (.neg (.or (.neg (.or p q)) r)) (.or (.neg q) r))) (.or (.neg q) r))) (.or (.neg (.or (.neg (.or (.neg (.or p q)) r)) (.or (.neg q) r))) (.or (.neg q) r))))) (t2_04 (.neg (.neg (.neg (.neg (.or (.neg (.or p q)) r))))) (.or (.neg (.or (.neg (.or p q)) r)) (.or (.neg q) r)) (.or (.neg q) r)))) (t2_54 (.neg (.neg (.neg (.or (.neg (.or p q)) r)))) (.or (.neg q) r))) (t2_54 (.neg (.or (.neg (.or p q)) r)) (.or (.neg q) r))) (Thm.mp (t2_06 (.or (.neg (.or p q)) (.or p r)) (.or (.neg (.or p q)) r) (.or (.neg q) r)) (t2_04 (.or (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg (.or p q)) r)) (.or (.neg (.or (.neg (.or p q)) r)) (.or (.neg q) r)) (.or (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg q) r))))) (Thm.mp (Thm.mp (t2_55 (.neg (.or (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg (.or p q)) r))) (.or (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg q) r))) (Thm.mp (t2_55 (.neg (.neg (.neg (.or (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg (.or p q)) r))))) (.or (.neg (.or (.neg (.or (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg (.or p q)) r))) (.or (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg q) r)))) (.or (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg q) r)))) (t2_04 (.neg (.neg (.neg (.neg (.or (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg (.or p q)) r)))))) (.or (.neg (.neg (.neg (.or (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg (.or p q)) r))))) (.or (.neg (.or (.neg (.or (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg (.or p q)) r))) (.or (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg q) r)))) (.or (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg q) r)))) (.or (.neg (.or (.neg (.or (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg (.or p q)) r))) (.or (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg q) r)))) (.or (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg q) r)))))) (t2_04 (.neg (.neg (.neg (.neg (.or (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg (.or p q)) r)))))) (.or (.neg (.or (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg (.or p q)) r))) (.or (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg q) r))) (.or (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg q) r))))) (t2_54 (.neg (.neg (.neg (.or (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg (.or p q)) r))))) (.or (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg q) r)))) (t2_54 (.neg (.or (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg (.or p q)) r))) (.or (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg q) r)))) (Thm.sum p (.or (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg (.or p q)) r)) (.or (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg q) r))))) (Thm.assoc p (.neg (.or (.neg (.or p q)) (.or p r))) (.or (.neg q) r)))

/-- *2.86 — FAITHFUL -/
theorem t2_86 (p : F) (q : F) (r : F) : Thm (s2_86 p q r) :=
  (t2_85 (.neg p) q r)

/-- *3.1 — FAITHFUL -/
theorem t3_1 (p : F) (q : F) : Thm (s3_1 p q) :=
  (t2_08 (.neg (.or (.neg p) (.neg q))))

/-- *3.11 — FAITHFUL -/
theorem t3_11 (p : F) (q : F) : Thm (s3_11 p q) :=
  (t2_08 (.neg (.or (.neg p) (.neg q))))

/-- *3.12 — FAITHFUL -/
theorem t3_12 (p : F) (q : F) : Thm (s3_12 p q) :=
  (t2_11 (.or (.neg p) (.neg q)))

/-- *3.13 — FAITHFUL -/
theorem t3_13 (p : F) (q : F) : Thm (s3_13 p q) :=
  (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (t3_11 p q) (t2_16 (.neg (.or (.neg p) (.neg q))) (.neg (.or (.neg p) (.neg q))))) (Thm.mp (Thm.mp (t2_16 (.neg (.neg (.or (.neg p) (.neg q)))) (.neg (.neg (.or (.neg p) (.neg q))))) (t2_16 (.or (.neg (.neg (.neg (.or (.neg p) (.neg q))))) (.neg (.neg (.or (.neg p) (.neg q))))) (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.neg (.neg (.or (.neg p) (.neg q)))))))) (t2_17 (.or (.neg (.neg (.neg (.or (.neg p) (.neg q))))) (.neg (.neg (.or (.neg p) (.neg q))))) (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.neg (.neg (.or (.neg p) (.neg q))))))))) (Thm.mp (Thm.mp (Thm.mp (t2_15 (.neg (.neg (.or (.neg p) (.neg q)))) (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (t2_16 (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.or (.neg (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q))))))) (.neg (.neg (.or (.neg p) (.neg q))))))) (Thm.mp (Thm.mp (t3_11 (.neg (.or (.neg (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q))))))) (.neg (.neg (.or (.neg p) (.neg q)))))) (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.neg (.neg (.or (.neg p) (.neg q))))))) (Thm.mp (t3_11 (.neg (.or (.neg (.neg (.or (.neg (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q))))))) (.neg (.neg (.or (.neg p) (.neg q))))))) (.neg (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.neg (.neg (.or (.neg p) (.neg q))))))))) (.or (.neg (.neg (.or (.neg (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q))))))) (.neg (.neg (.or (.neg p) (.neg q))))))) (.neg (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.neg (.neg (.or (.neg p) (.neg q))))))))) (t2_17 (.or (.neg (.neg (.or (.neg (.neg (.or (.neg (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q))))))) (.neg (.neg (.or (.neg p) (.neg q))))))) (.neg (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.neg (.neg (.or (.neg p) (.neg q)))))))))) (.neg (.or (.neg (.neg (.or (.neg (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q))))))) (.neg (.neg (.or (.neg p) (.neg q))))))) (.neg (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.neg (.neg (.or (.neg p) (.neg q)))))))))) (.or (.neg (.neg (.or (.neg (.neg (.or (.neg (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q))))))) (.neg (.neg (.or (.neg p) (.neg q))))))) (.neg (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.neg (.neg (.or (.neg p) (.neg q)))))))))) (.neg (.or (.neg (.neg (.or (.neg (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q))))))) (.neg (.neg (.or (.neg p) (.neg q))))))) (.neg (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.neg (.neg (.or (.neg p) (.neg q))))))))))))) (t2_17 (.or (.neg (.neg (.or (.neg (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q))))))) (.neg (.neg (.or (.neg p) (.neg q))))))) (.neg (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.neg (.neg (.or (.neg p) (.neg q)))))))) (.or (.neg (.neg (.or (.neg (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q))))))) (.neg (.neg (.or (.neg p) (.neg q))))))) (.neg (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.neg (.neg (.or (.neg p) (.neg q))))))))))) (t2_17 (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.or (.neg (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q))))))) (.neg (.neg (.or (.neg p) (.neg q)))))))) (t2_17 (.neg (.or (.neg p) (.neg q))) (.neg (.neg (.neg (.or (.neg p) (.neg q))))))) (t2_17 (.neg (.neg (.or (.neg p) (.neg q)))) (.or (.neg p) (.neg q))))

/-- *3.14 — FAITHFUL -/
theorem t3_14 (p : F) (q : F) : Thm (s3_14 p q) :=
  (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (t3_1 p q) (t2_16 (.neg (.or (.neg p) (.neg q))) (.neg (.or (.neg p) (.neg q))))) (Thm.mp (Thm.mp (t2_15 (.neg (.or (.neg p) (.neg q))) (.neg (.neg (.or (.neg p) (.neg q))))) (t2_16 (.or (.neg (.neg (.neg (.or (.neg p) (.neg q))))) (.neg (.neg (.or (.neg p) (.neg q))))) (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.or (.neg p) (.neg q)))))) (t2_17 (.or (.neg (.neg (.neg (.or (.neg p) (.neg q))))) (.neg (.neg (.or (.neg p) (.neg q))))) (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.or (.neg p) (.neg q))))))) (Thm.mp (Thm.mp (Thm.mp (t2_16 (.neg (.neg (.neg (.or (.neg p) (.neg q))))) (.neg (.or (.neg p) (.neg q)))) (t2_16 (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.or (.neg p) (.neg q)))) (.or (.neg (.neg (.neg (.or (.neg p) (.neg q))))) (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q))))))))) (Thm.mp (Thm.mp (t3_1 (.neg (.or (.neg (.neg (.neg (.or (.neg p) (.neg q))))) (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))))) (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.or (.neg p) (.neg q))))) (Thm.mp (t3_1 (.neg (.or (.neg (.neg (.or (.neg (.neg (.neg (.or (.neg p) (.neg q))))) (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q))))))))) (.neg (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.or (.neg p) (.neg q))))))) (.or (.neg (.neg (.or (.neg (.neg (.neg (.or (.neg p) (.neg q))))) (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q))))))))) (.neg (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.or (.neg p) (.neg q))))))) (t2_17 (.or (.neg (.neg (.or (.neg (.neg (.or (.neg (.neg (.neg (.or (.neg p) (.neg q))))) (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q))))))))) (.neg (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.or (.neg p) (.neg q)))))))) (.neg (.or (.neg (.neg (.or (.neg (.neg (.neg (.or (.neg p) (.neg q))))) (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q))))))))) (.neg (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.or (.neg p) (.neg q)))))))) (.or (.neg (.neg (.or (.neg (.neg (.or (.neg (.neg (.neg (.or (.neg p) (.neg q))))) (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q))))))))) (.neg (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.or (.neg p) (.neg q)))))))) (.neg (.or (.neg (.neg (.or (.neg (.neg (.neg (.or (.neg p) (.neg q))))) (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q))))))))) (.neg (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.or (.neg p) (.neg q))))))))))) (t2_17 (.or (.neg (.neg (.or (.neg (.neg (.neg (.or (.neg p) (.neg q))))) (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q))))))))) (.neg (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.or (.neg p) (.neg q)))))) (.or (.neg (.neg (.or (.neg (.neg (.neg (.or (.neg p) (.neg q))))) (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q))))))))) (.neg (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.or (.neg p) (.neg q))))))))) (t2_17 (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.or (.neg p) (.neg q)))) (.or (.neg (.neg (.neg (.or (.neg p) (.neg q))))) (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))))))) (t2_17 (.neg (.neg (.neg (.or (.neg p) (.neg q))))) (.neg (.or (.neg p) (.neg q))))) (t2_17 (.or (.neg p) (.neg q)) (.neg (.neg (.or (.neg p) (.neg q))))))

/-- *3.2 — REPAIRED (extra: *2.32) -/
theorem t3_2 (p : F) (q : F) : Thm (s3_2 p q) :=
  (Thm.mp (t3_12 p q) (t2_32 (.neg p) (.neg q) (.neg (.or (.neg p) (.neg q)))))

/-- *3.21 — FAITHFUL -/
theorem t3_21 (p : F) (q : F) : Thm (s3_21 p q) :=
  (Thm.mp (t3_2 p q) (t2_04 p q (.neg (.or (.neg p) (.neg q)))))

/-- *3.22 — FAITHFUL -/
theorem t3_22 (p : F) (q : F) : Thm (s3_22 p q) :=
  (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.perm (.neg q) (.neg p)) (t2_16 (.or (.neg q) (.neg p)) (.or (.neg p) (.neg q)))) (Thm.mp (Thm.mp (t3_14 (.neg (.or (.neg p) (.neg q))) (.or (.neg q) (.neg p))) (t3_14 (.or (.neg (.neg (.or (.neg p) (.neg q)))) (.neg (.or (.neg q) (.neg p)))) (.neg (.or (.neg (.neg (.or (.neg p) (.neg q)))) (.neg (.or (.neg q) (.neg p))))))) (t3_13 (.or (.neg (.neg (.or (.neg p) (.neg q)))) (.neg (.or (.neg q) (.neg p)))) (.neg (.or (.neg (.neg (.or (.neg p) (.neg q)))) (.neg (.or (.neg q) (.neg p)))))))) (t3_13 (.neg (.or (.neg p) (.neg q))) (.or (.neg q) (.neg p)))) (t2_17 (.or (.neg q) (.neg p)) (.or (.neg p) (.neg q)))) (t2_16 (.or (.neg q) (.neg p)) (.or (.neg p) (.neg q)))) (t2_16 (.neg (.or (.neg p) (.neg q))) (.neg (.or (.neg q) (.neg p))))) (Thm.mp (Thm.mp (Thm.perm (.neg (.neg (.neg (.or (.neg q) (.neg p))))) (.neg (.neg (.or (.neg p) (.neg q))))) (t2_16 (.or (.neg (.neg (.neg (.or (.neg q) (.neg p))))) (.neg (.neg (.or (.neg p) (.neg q))))) (.or (.neg (.neg (.or (.neg p) (.neg q)))) (.neg (.neg (.neg (.or (.neg q) (.neg p)))))))) (t2_03 (.neg (.or (.neg (.neg (.or (.neg p) (.neg q)))) (.neg (.neg (.neg (.or (.neg q) (.neg p))))))) (.or (.neg (.neg (.neg (.or (.neg q) (.neg p))))) (.neg (.neg (.or (.neg p) (.neg q)))))))) (t3_13 (.neg (.or (.neg p) (.neg q))) (.neg (.neg (.or (.neg q) (.neg p)))))) (t2_17 (.neg (.neg (.or (.neg q) (.neg p)))) (.or (.neg p) (.neg q)))) (t2_16 (.neg (.neg (.or (.neg q) (.neg p)))) (.or (.neg p) (.neg q)))) (Thm.perm (.neg (.neg (.or (.neg p) (.neg q)))) (.neg (.neg (.neg (.or (.neg q) (.neg p))))))) (t3_14 (.neg (.neg (.or (.neg q) (.neg p)))) (.neg (.or (.neg p) (.neg q))))) (t3_13 (.neg (.neg (.or (.neg q) (.neg p)))) (.neg (.or (.neg p) (.neg q))))) (t2_17 (.neg (.or (.neg p) (.neg q))) (.neg (.or (.neg q) (.neg p))))) (t3_14 (.neg (.or (.neg p) (.neg q))) (.or (.neg q) (.neg p)))) (t3_13 (.neg (.or (.neg p) (.neg q))) (.or (.neg q) (.neg p))))

/-- *3.24 — FAITHFUL. PM Dem.: ✱2·11 (∼p/p); ✱3·14 (∼p/q). -/
theorem t3_24 (p : F) : Thm (s3_24 p) :=
  -- [✱2·11 (∼p/p)] ⊢ . ∼p ∨ ∼(∼p) . ⊃
  -- [✱3·14 (∼p/q)] ⊢ . ∼(p . ∼p)
  (Thm.mp (t2_11 (.neg p)) (t3_14 p (.neg p)))

/-- *3.26 — FAITHFUL -/
theorem t3_26 (p : F) (q : F) : Thm (s3_26 p q) :=
  (Thm.mp (t2_02 q p) (Thm.mp (Thm.mp (t2_02 q p) (Thm.mp (Thm.mp (Thm.mp (t2_02 q p) (Thm.mp (Thm.mp (t2_02 q p) (Thm.mp (Thm.mp (t2_02 q p) (t2_31 (.neg p) (.neg q) p)) (t2_02 (.or (.neg p) (.or (.neg q) p)) (.or (.or (.neg p) (.neg q)) p)))) (t2_02 (.or (.neg p) (.or (.neg q) p)) (.or (.or (.neg p) (.neg q)) p)))) (t2_53 (.or (.neg p) (.neg q)) p)) (t2_02 (.or (.neg p) (.or (.neg q) p)) (.or (.neg (.neg (.or (.neg p) (.neg q)))) p)))) (t2_02 (.or (.neg p) (.or (.neg q) p)) (.or (.neg (.neg (.or (.neg p) (.neg q)))) p))))

/-- *3.27 — FAITHFUL. PM Dem.: ✱3·22; ✱3·26 (q, p / p, q), a ⊃-chain joined by the tacit Syll (✱2·05). -/
theorem t3_27 (p : F) (q : F) : Thm (s3_27 p q) :=
  -- [✱3·22] ⊢ : p . q . ⊃ . q . p .
  have l1 : Thm (imp (and p q) (and q p)) := t3_22 p q
  -- [✱3·26 (q, p / p, q)] ⊃ . q : ⊃ ⊢ . Prop
  have l2 : Thm (imp (and q p) q) := t3_26 q p
  Thm.mp l1 (Thm.mp l2 (t2_05 (and p q) (and q p) q))

/-- *3.31 — FAITHFUL. PM Dem.: Id (✱1·01); ✱2·31; ✱2·53 (∼p ∨ ∼q, r / p, q); Id (✱3·01), a ⊃-chain
    joined by the tacit Syll (✱2·05). The Id lines restate a definition; they are kept as written. -/
theorem t3_31 (p : F) (q : F) (r : F) : Thm (s3_31 p q r) :=
  -- [Id . (✱1·01)] ⊢ :. p . ⊃ . q ⊃ r : ⊃ : ∼p . ∨ . ∼q ∨ r :
  have l1 : Thm (imp (imp p (imp q r)) (.or (.neg p) (.or (.neg q) r))) := t2_08 (imp p (imp q r))
  -- [✱2·31] ⊃ : ∼p ∨ ∼q . ∨ . r :
  have l2 : Thm (imp (.or (.neg p) (.or (.neg q) r)) (.or (.or (.neg p) (.neg q)) r)) :=
    t2_31 (.neg p) (.neg q) r
  -- [✱2·53 (∼p ∨ ∼q, r / p, q)] ⊃ : ∼(∼p ∨ ∼q) . ⊃ . r :
  have l3 : Thm (imp (.or (.or (.neg p) (.neg q)) r) (imp (.neg (.or (.neg p) (.neg q))) r)) :=
    t2_53 (.or (.neg p) (.neg q)) r
  -- [Id . (✱3·01)] ⊃ : p . q . ⊃ . r :. ⊃ ⊢ . Prop
  have l4 : Thm (imp (imp (.neg (.or (.neg p) (.neg q))) r) (imp (and p q) r)) := t2_08 (imp (and p q) r)
  have c2 : Thm (imp (imp p (imp q r)) (.or (.or (.neg p) (.neg q)) r)) :=
    Thm.mp l1 (Thm.mp l2 (t2_05 (imp p (imp q r)) (.or (.neg p) (.or (.neg q) r)) (.or (.or (.neg p) (.neg q)) r)))
  have c3 : Thm (imp (imp p (imp q r)) (imp (.neg (.or (.neg p) (.neg q))) r)) :=
    Thm.mp c2 (Thm.mp l3 (t2_05 (imp p (imp q r)) (.or (.or (.neg p) (.neg q)) r)
      (imp (.neg (.or (.neg p) (.neg q))) r)))
  Thm.mp c3 (Thm.mp l4 (t2_05 (imp p (imp q r)) (imp (.neg (.or (.neg p) (.neg q))) r) (imp (and p q) r)))

/-- *3.33 — FAITHFUL -/
theorem t3_33 (p : F) (q : F) (r : F) : Thm (s3_33 p q r) :=
  (Thm.mp (t2_06 p q r) (t3_31 (.or (.neg p) q) (.or (.neg q) r) (.or (.neg p) r)))

/-- *3.34 — FAITHFUL -/
theorem t3_34 (p : F) (q : F) (r : F) : Thm (s3_34 p q r) :=
  (Thm.mp (t2_05 p q r) (t3_31 (.or (.neg q) r) (.or (.neg p) q) (.or (.neg p) r)))

/-- *3.35 — FAITHFUL -/
theorem t3_35 (p : F) (q : F) : Thm (s3_35 p q) :=
  (Thm.mp (t2_27 p q) (t3_31 p (.or (.neg p) q) q))

/-- *3.4 — FAITHFUL -/
theorem t3_4 (p : F) (q : F) : Thm (s3_4 p q) :=
  (Thm.mp (Thm.mp (Thm.mp (Thm.mp (Thm.mp (t2_51 p q) (t2_16 (.neg (.or (.neg p) q)) (.or (.neg p) (.neg q)))) (Thm.mp (Thm.mp (t2_16 (.neg (.or (.neg p) (.neg q))) (.neg (.neg (.or (.neg p) q)))) (t2_16 (.or (.neg (.neg (.or (.neg p) (.neg q)))) (.neg (.neg (.or (.neg p) q)))) (.or (.neg (.neg (.neg (.neg (.or (.neg p) q))))) (.neg (.neg (.or (.neg p) (.neg q))))))) (t2_17 (.or (.neg (.neg (.or (.neg p) (.neg q)))) (.neg (.neg (.or (.neg p) q)))) (.or (.neg (.neg (.neg (.neg (.or (.neg p) q))))) (.neg (.neg (.or (.neg p) (.neg q)))))))) (Thm.mp (Thm.mp (t2_15 (.neg (.neg (.or (.neg p) q))) (.neg (.neg (.or (.neg p) (.neg q))))) (Thm.mp (Thm.mp (t2_16 (.or (.neg (.neg (.neg (.neg (.or (.neg p) q))))) (.neg (.neg (.or (.neg p) (.neg q))))) (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.neg (.or (.neg p) q))))) (t2_16 (.or (.neg (.or (.neg (.neg (.neg (.neg (.or (.neg p) q))))) (.neg (.neg (.or (.neg p) (.neg q)))))) (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.neg (.or (.neg p) q))))) (.or (.neg (.neg (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.neg (.or (.neg p) q)))))) (.neg (.or (.neg (.neg (.neg (.neg (.or (.neg p) q))))) (.neg (.neg (.or (.neg p) (.neg q))))))))) (t2_17 (.or (.neg (.or (.neg (.neg (.neg (.neg (.or (.neg p) q))))) (.neg (.neg (.or (.neg p) (.neg q)))))) (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.neg (.or (.neg p) q))))) (.or (.neg (.neg (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.neg (.or (.neg p) q)))))) (.neg (.or (.neg (.neg (.neg (.neg (.or (.neg p) q))))) (.neg (.neg (.or (.neg p) (.neg q)))))))))) (t2_17 (.or (.neg (.neg (.neg (.neg (.or (.neg p) q))))) (.neg (.neg (.or (.neg p) (.neg q))))) (.or (.neg (.neg (.neg (.neg (.or (.neg p) (.neg q)))))) (.neg (.neg (.or (.neg p) q))))))) (t2_17 (.neg (.or (.neg p) q)) (.neg (.neg (.or (.neg p) (.neg q)))))) (t2_17 (.neg (.or (.neg p) (.neg q))) (.or (.neg p) q)))

/-- *3.41 — FAITHFUL -/
theorem t3_41 (p : F) (q : F) (r : F) : Thm (s3_41 p q r) :=
  (Thm.mp (t3_26 p q) (t2_06 (.neg (.or (.neg p) (.neg q))) p r))

/-- *3.42 — FAITHFUL -/
theorem t3_42 (p : F) (q : F) (r : F) : Thm (s3_42 p q r) :=
  (Thm.mp (t3_27 p q) (t2_06 (.neg (.or (.neg p) (.neg q))) q r))

/-- *3.45 — FAITHFUL -/
theorem t3_45 (p : F) (q : F) (r : F) : Thm (s3_45 p q r) :=
  (Thm.mp (Thm.mp (Thm.mp (t2_16 (.or (.neg q) (.neg r)) (.or (.neg p) (.neg r))) (Thm.mp (t2_06 p q (.neg r)) (t2_06 (.or (.neg p) q) (.or (.neg (.or (.neg q) (.neg r))) (.or (.neg p) (.neg r))) (.or (.neg (.neg (.or (.neg p) (.neg r)))) (.neg (.or (.neg q) (.neg r))))))) (t2_16 (.or (.neg p) q) (.or (.neg (.neg (.or (.neg p) (.neg r)))) (.neg (.or (.neg q) (.neg r)))))) (t2_17 (.or (.neg p) q) (.or (.neg (.neg (.or (.neg p) (.neg r)))) (.neg (.or (.neg q) (.neg r))))))

/-- *4.1 — FAITHFUL. PM: [✱2·16·17] (hint only); the two halves joined by the tacit ✱3·03 (by ✱3·2). -/
theorem t4_1 (p : F) (q : F) : Thm (s4_1 p q) :=
  -- [✱2·16] ⊢ : p ⊃ q . ⊃ . ∼q ⊃ ∼p
  have h1 : Thm (imp (imp p q) (imp (.neg q) (.neg p))) := t2_16 p q
  -- [✱2·17] ⊢ : ∼q ⊃ ∼p . ⊃ . p ⊃ q
  have h2 : Thm (imp (imp (.neg q) (.neg p)) (imp p q)) := t2_17 p q
  Thm.mp h2 (Thm.mp h1 (t3_2 (imp (imp p q) (imp (.neg q) (.neg p))) (imp (imp (.neg q) (.neg p)) (imp p q))))

/-- *4.13 — FAITHFUL. PM: [✱2·12·14] (hint only); the two halves joined by the tacit ✱3·03 (by ✱3·2). -/
theorem t4_13 (p : F) : Thm (s4_13 p) :=
  -- [✱2·12] ⊢ : p . ⊃ . ∼(∼p)
  have h1 : Thm (imp p (.neg (.neg p))) := t2_12 p
  -- [✱2·14] ⊢ : ∼(∼p) . ⊃ . p
  have h2 : Thm (imp (.neg (.neg p)) p) := t2_14 p
  Thm.mp h2 (Thm.mp h1 (t3_2 (imp p (.neg (.neg p))) (imp (.neg (.neg p)) p)))

/-- *4.2 — FAITHFUL -/
theorem t4_2 (p : F) : Thm (s4_2 p) :=
  (Thm.mp (t2_08 p) (Thm.mp (t2_08 p) (t3_2 (.or (.neg p) p) (.or (.neg p) p))))

/-- *4.21 — FAITHFUL. PM: [✱3·22] (hint only), taken both ways; the halves joined by the tacit ✱3·03
    (by ✱3·2). -/
theorem t4_21 (p : F) (q : F) : Thm (s4_21 p q) :=
  -- [✱3·22] ⊢ : p ≡ q . ⊃ . q ≡ p
  have h1 : Thm (imp (iff p q) (iff q p)) := t3_22 (imp p q) (imp q p)
  -- [✱3·22] ⊢ : q ≡ p . ⊃ . p ≡ q
  have h2 : Thm (imp (iff q p) (iff p q)) := t3_22 (imp q p) (imp p q)
  Thm.mp h2 (Thm.mp h1 (t3_2 (imp (iff p q) (iff q p)) (imp (iff q p) (iff p q))))

/-- *4.24 — FAITHFUL -/
theorem t4_24 (p : F) : Thm (s4_24 p) :=
  (Thm.mp (t3_26 p p) (Thm.mp (Thm.mp (t3_2 p p) (t2_43 p (.neg (.or (.neg p) (.neg p))))) (t3_2 (.or (.neg p) (.neg (.or (.neg p) (.neg p)))) (.or (.neg (.neg (.or (.neg p) (.neg p)))) p))))

/-- *4.25 — FAITHFUL. PM: [Taut . Add (p/q)] (hint only); the halves joined by the tacit ✱3·03 (by ✱3·2). -/
theorem t4_25 (p : F) : Thm (s4_25 p) :=
  -- [Add (p/q)] ⊢ : p . ⊃ . p ∨ p
  have h1 : Thm (imp p (.or p p)) := Thm.add p p
  -- [Taut] ⊢ : p ∨ p . ⊃ . p
  have h2 : Thm (imp (.or p p) p) := Thm.taut p
  Thm.mp h2 (Thm.mp h1 (t3_2 (imp p (.or p p)) (imp (.or p p) p)))

/-- *4.3 — FAITHFUL. PM: [✱3·22] (hint only), taken both ways (PM's note to ✱4·3); the halves joined
    by the tacit ✱3·03 (by ✱3·2). -/
theorem t4_3 (p : F) (q : F) : Thm (s4_3 p q) :=
  -- [✱3·22] ⊢ : p . q . ⊃ . q . p
  have h1 : Thm (imp (and p q) (and q p)) := t3_22 p q
  -- [✱3·22 (q, p / p, q)] ⊢ : q . p . ⊃ . p . q
  have h2 : Thm (imp (and q p) (and p q)) := t3_22 q p
  Thm.mp h2 (Thm.mp h1 (t3_2 (imp (and p q) (and q p)) (imp (and q p) (and p q))))

/-- *4.31 — FAITHFUL. PM: [Perm] (hint only), taken both ways; the halves joined by the tacit ✱3·03
    (by ✱3·2). -/
theorem t4_31 (p : F) (q : F) : Thm (s4_31 p q) :=
  -- [Perm] ⊢ : p ∨ q . ⊃ . q ∨ p
  have h1 : Thm (imp (.or p q) (.or q p)) := Thm.perm p q
  -- [Perm (q, p / p, q)] ⊢ : q ∨ p . ⊃ . p ∨ q
  have h2 : Thm (imp (.or q p) (.or p q)) := Thm.perm q p
  Thm.mp h2 (Thm.mp h1 (t3_2 (imp (.or p q) (.or q p)) (imp (.or q p) (.or p q))))

/-- *4.33 — FAITHFUL. PM: [✱2·31·32] (hint only); the halves joined by the tacit ✱3·03 (by ✱3·2). -/
theorem t4_33 (p : F) (q : F) (r : F) : Thm (s4_33 p q r) :=
  -- [✱2·32] ⊢ : (p ∨ q) ∨ r . ⊃ . p ∨ (q ∨ r)
  have h1 : Thm (imp (.or (.or p q) r) (.or p (.or q r))) := t2_32 p q r
  -- [✱2·31] ⊢ : p ∨ (q ∨ r) . ⊃ . (p ∨ q) ∨ r
  have h2 : Thm (imp (.or p (.or q r)) (.or (.or p q) r)) := t2_31 p q r
  Thm.mp h2 (Thm.mp h1 (t3_2 (imp (.or (.or p q) r) (.or p (.or q r))) (imp (.or p (.or q r)) (.or (.or p q) r))))

/-- *4.5 — FAITHFUL -/
theorem t4_5 (p : F) (q : F) : Thm (s4_5 p q) :=
  (t4_2 (.neg (.or (.neg p) (.neg q))))

/-- *4.51 — REPAIRED (extra: *1.2, *1.3, *2.11, *2.14, *3.2) -/
theorem t4_51 (p : F) (q : F) : Thm (s4_51 p q) :=
  (Thm.mp (Thm.mp (Thm.mp (t2_11 (.neg (.or (.neg p) (.neg q)))) (Thm.mp (t2_14 (.or (.neg p) (.neg q))) (t3_2 (.or (.neg (.neg (.neg (.or (.neg p) (.neg q))))) (.or (.neg p) (.neg q))) (.or (.neg (.or (.neg p) (.neg q))) (.neg (.neg (.or (.neg p) (.neg q)))))))) (Thm.add (.neg (.or (.neg (.or (.neg (.neg (.neg (.or (.neg p) (.neg q))))) (.or (.neg p) (.neg q)))) (.neg (.or (.neg (.or (.neg p) (.neg q))) (.neg (.neg (.or (.neg p) (.neg q)))))))) (.neg (.or (.neg (.or (.neg (.neg (.neg (.or (.neg p) (.neg q))))) (.or (.neg p) (.neg q)))) (.neg (.or (.neg (.or (.neg p) (.neg q))) (.neg (.neg (.or (.neg p) (.neg q)))))))))) (Thm.taut (.neg (.or (.neg (.or (.neg (.neg (.neg (.or (.neg p) (.neg q))))) (.or (.neg p) (.neg q)))) (.neg (.or (.neg (.or (.neg p) (.neg q))) (.neg (.neg (.or (.neg p) (.neg q))))))))))

/-- *4.54 — REPAIRED (extra: *2.08, *2.16, *2.53, *2.54, *3.2) -/
theorem t4_54 (p : F) (q : F) : Thm (s4_54 p q) :=
  (Thm.mp (Thm.mp (Thm.mp (t2_54 p (.neg q)) (t2_16 (.or (.neg (.neg p)) (.neg q)) (.or p (.neg q)))) (Thm.mp (Thm.mp (t2_53 p (.neg q)) (t2_16 (.or p (.neg q)) (.or (.neg (.neg p)) (.neg q)))) (t3_2 (.or (.neg (.neg (.or (.neg (.neg p)) (.neg q)))) (.neg (.or p (.neg q)))) (.or (.neg (.neg (.or p (.neg q)))) (.neg (.or (.neg (.neg p)) (.neg q))))))) (t2_08 (.neg (.or (.neg (.or (.neg (.neg (.or (.neg (.neg p)) (.neg q)))) (.neg (.or p (.neg q))))) (.neg (.or (.neg (.neg (.or p (.neg q)))) (.neg (.or (.neg (.neg p)) (.neg q)))))))))

/-- *4.55 — REPAIRED (extra: *1.4, *2.08, *2.16, *2.53, *2.54, *3.2) -/
theorem t4_55 (p : F) (q : F) : Thm (s4_55 p q) :=
  (Thm.mp (Thm.mp (Thm.mp (t2_53 p (.neg q)) (t2_16 (.or p (.neg q)) (.or (.neg (.neg p)) (.neg q)))) (Thm.perm (.neg (.neg (.or (.neg (.neg p)) (.neg q)))) (.neg (.or p (.neg q))))) (Thm.mp (Thm.mp (Thm.mp (t2_54 p (.neg q)) (t2_53 (.neg (.or (.neg (.neg p)) (.neg q))) (.or p (.neg q)))) (t2_08 (.or (.neg (.neg (.neg (.or (.neg (.neg p)) (.neg q))))) (.or p (.neg q))))) (t3_2 (.or (.neg (.neg (.neg (.or (.neg (.neg p)) (.neg q))))) (.or p (.neg q))) (.or (.neg (.or p (.neg q))) (.neg (.neg (.or (.neg (.neg p)) (.neg q))))))))

/-- *4.6 — FAITHFUL -/
theorem t4_6 (p : F) (q : F) : Thm (s4_6 p q) :=
  (t4_2 (.or (.neg p) q))

/-- *4.62 — FAITHFUL -/
theorem t4_62 (p : F) (q : F) : Thm (s4_62 p q) :=
  (t4_6 p (.neg q))

/-- *4.63 — FAITHFUL -/
theorem t4_63 (p : F) (q : F) : Thm (s4_63 p q) :=
  (t4_5 p q)

/-- *4.64 — FAITHFUL. PM: [✱2·53·54] (hint only); the halves joined by the tacit ✱3·03 (by ✱3·2). -/
theorem t4_64 (p : F) (q : F) : Thm (s4_64 p q) :=
  -- [✱2·54] ⊢ : ∼p ⊃ q . ⊃ . p ∨ q
  have h1 : Thm (imp (imp (.neg p) q) (.or p q)) := t2_54 p q
  -- [✱2·53] ⊢ : p ∨ q . ⊃ . ∼p ⊃ q
  have h2 : Thm (imp (.or p q) (imp (.neg p) q)) := t2_53 p q
  Thm.mp h2 (Thm.mp h1 (t3_2 (imp (imp (.neg p) q) (.or p q)) (imp (.or p q) (imp (.neg p) q))))

/-- *4.66 — FAITHFUL -/
theorem t4_66 (p : F) (q : F) : Thm (s4_66 p q) :=
  (t4_64 p (.neg q))

/-- *4.67 — REPAIRED (extra: *1.2, *1.3, *2.08, *4.2) -/
theorem t4_67 (p : F) (q : F) : Thm (s4_67 p q) :=
  (Thm.mp (Thm.mp (Thm.mp (t4_2 (.neg (.or (.neg (.neg p)) (.neg q)))) (t2_08 (.neg (.or (.neg (.or (.neg (.neg (.or (.neg (.neg p)) (.neg q)))) (.neg (.or (.neg (.neg p)) (.neg q))))) (.neg (.or (.neg (.neg (.or (.neg (.neg p)) (.neg q)))) (.neg (.or (.neg (.neg p)) (.neg q))))))))) (Thm.add (.neg (.or (.neg (.or (.neg (.neg (.or (.neg (.neg p)) (.neg q)))) (.neg (.or (.neg (.neg p)) (.neg q))))) (.neg (.or (.neg (.neg (.or (.neg (.neg p)) (.neg q)))) (.neg (.or (.neg (.neg p)) (.neg q))))))) (.neg (.or (.neg (.or (.neg (.neg (.or (.neg (.neg p)) (.neg q)))) (.neg (.or (.neg (.neg p)) (.neg q))))) (.neg (.or (.neg (.neg (.or (.neg (.neg p)) (.neg q)))) (.neg (.or (.neg (.neg p)) (.neg q))))))))) (Thm.taut (.neg (.or (.neg (.or (.neg (.neg (.or (.neg (.neg p)) (.neg q)))) (.neg (.or (.neg (.neg p)) (.neg q))))) (.neg (.or (.neg (.neg (.or (.neg (.neg p)) (.neg q)))) (.neg (.or (.neg (.neg p)) (.neg q)))))))))

/-- *4.8 — FAITHFUL. PM: [✱2·01 . Simp] (hint only); Simp is ✱2·02; the halves joined by the tacit
    ✱3·03 (by ✱3·2). -/
theorem t4_8 (p : F) : Thm (s4_8 p) :=
  -- [✱2·01] ⊢ : p ⊃ ∼p . ⊃ . ∼p
  have h1 : Thm (imp (imp p (.neg p)) (.neg p)) := t2_01 p
  -- [Simp (✱2·02)] ⊢ : ∼p . ⊃ . p ⊃ ∼p
  have h2 : Thm (imp (.neg p) (imp p (.neg p))) := t2_02 p (.neg p)
  Thm.mp h2 (Thm.mp h1 (t3_2 (imp (imp p (.neg p)) (.neg p)) (imp (.neg p) (imp p (.neg p)))))

/-- *4.81 — FAITHFUL. PM: [✱2·18 . Simp] (hint only); Simp is ✱2·02; the halves joined by the tacit
    ✱3·03 (by ✱3·2). -/
theorem t4_81 (p : F) : Thm (s4_81 p) :=
  -- [✱2·18] ⊢ : ∼p ⊃ p . ⊃ . p
  have h1 : Thm (imp (imp (.neg p) p) p) := t2_18 p
  -- [Simp (✱2·02)] ⊢ : p . ⊃ . ∼p ⊃ p
  have h2 : Thm (imp p (imp (.neg p) p)) := t2_02 (.neg p) p
  Thm.mp h2 (Thm.mp h1 (t3_2 (imp (imp (.neg p) p) p) (imp p (imp (.neg p) p))))

/-- *5.11 — FAITHFUL -/
theorem t5_11 (p : F) (q : F) : Thm (s5_11 p q) :=
  (Thm.mp (t2_5 p q) (t2_54 (.or (.neg p) q) (.or (.neg (.neg p)) q)))

/-- *5.12 — FAITHFUL -/
theorem t5_12 (p : F) (q : F) : Thm (s5_12 p q) :=
  (Thm.mp (t2_51 p q) (t2_54 (.or (.neg p) q) (.or (.neg p) (.neg q))))

/-- *5.13 — REPAIRED (extra: *1.2, *1.3, *2.54) -/
theorem t5_13 (p : F) (q : F) : Thm (s5_13 p q) :=
  (Thm.mp (Thm.mp (Thm.mp (t2_521 p q) (t2_54 (.or (.neg p) q) (.or (.neg q) p))) (Thm.add (.or (.or (.neg p) q) (.or (.neg q) p)) (.or (.or (.neg p) q) (.or (.neg q) p)))) (Thm.taut (.or (.or (.neg p) q) (.or (.neg q) p))))

/-- *5.14 — REPAIRED (extra: *1.3, *1.5, *2.2, *2.32) -/
theorem t5_14 (p : F) (q : F) (r : F) : Thm (s5_14 p q r) :=
  (Thm.mp (Thm.mp (Thm.mp (Thm.add (.neg p) q) (t2_2 (.or (.neg q) (.or (.neg p) q)) r)) (t2_32 (.neg q) (.or (.neg p) q) r)) (Thm.assoc (.neg q) (.or (.neg p) q) r))

/-- *5.25 — FAITHFUL. PM: [✱2·62·68] (hint only); the halves joined by the tacit ✱3·03 (by ✱3·2). -/
theorem t5_25 (p : F) (q : F) : Thm (s5_25 p q) :=
  -- [✱2·62] ⊢ :. p ∨ q . ⊃ : p ⊃ q . ⊃ . q
  have h1 : Thm (imp (.or p q) (imp (imp p q) q)) := t2_62 p q
  -- [✱2·68] ⊢ :. p ⊃ q . ⊃ . q : ⊃ . p ∨ q
  have h2 : Thm (imp (imp (imp p q) q) (.or p q)) := t2_68 p q
  Thm.mp h2 (Thm.mp h1 (t3_2 (imp (.or p q) (imp (imp p q) q)) (imp (imp (imp p q) q) (.or p q))))

/-- *5.4 — FAITHFUL. PM: [Simp . ✱2·43] (hint only); Simp is ✱2·02; the halves joined by the tacit
    ✱3·03 (by ✱3·2). -/
theorem t5_4 (p : F) (q : F) : Thm (s5_4 p q) :=
  -- [✱2·43] ⊢ :. p . ⊃ . p ⊃ q : ⊃ . p ⊃ q
  have h1 : Thm (imp (imp p (imp p q)) (imp p q)) := t2_43 p q
  -- [Simp (✱2·02)] ⊢ :. p ⊃ q . ⊃ : p . ⊃ . p ⊃ q
  have h2 : Thm (imp (imp p q) (imp p (imp p q))) := t2_02 p (imp p q)
  Thm.mp h2 (Thm.mp h1 (t3_2 (imp (imp p (imp p q)) (imp p q)) (imp (imp p q) (imp p (imp p q)))))

/-- *5.62 — REPAIRED (extra: *1.2, *1.3, *2.62, *2.68, *3.2) -/
theorem t5_62 (p : F) (q : F) : Thm (s5_62 p q) :=
  (Thm.mp (Thm.mp (Thm.mp (t2_62 p (.neg q)) (Thm.mp (t2_68 p (.neg q)) (t3_2 (.or (.neg (.or (.neg (.or (.neg p) (.neg q))) (.neg q))) (.or p (.neg q))) (.or (.neg (.or p (.neg q))) (.or (.neg (.or (.neg p) (.neg q))) (.neg q)))))) (Thm.add (.neg (.or (.neg (.or (.neg (.or (.neg (.or (.neg p) (.neg q))) (.neg q))) (.or p (.neg q)))) (.neg (.or (.neg (.or p (.neg q))) (.or (.neg (.or (.neg p) (.neg q))) (.neg q)))))) (.neg (.or (.neg (.or (.neg (.or (.neg (.or (.neg p) (.neg q))) (.neg q))) (.or p (.neg q)))) (.neg (.or (.neg (.or p (.neg q))) (.or (.neg (.or (.neg p) (.neg q))) (.neg q)))))))) (Thm.taut (.neg (.or (.neg (.or (.neg (.or (.neg (.or (.neg p) (.neg q))) (.neg q))) (.or p (.neg q)))) (.neg (.or (.neg (.or p (.neg q))) (.or (.neg (.or (.neg p) (.neg q))) (.neg q))))))))

end PM
