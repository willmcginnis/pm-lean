import PM.Replay
import PM.Derived
/-!
  Replay, part 2: the propositions of ✱2–✱5 left UNRESOLVED by the first replay, and the
  FAITHFUL/REPAIRED ones that depended on them. Each theorem is an explicit `Thm` derivation built from
  the primitive propositions, earlier `t…` theorems and the derived rules of PM.Derived. Proofs named
  `ofPf` are natural-deduction derivations; `hy n` is the n-th hypothesis, and `intro_` is the
  deduction theorem (definitional; see PM.Derived).
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

/-- *2.74 — [✱2·73, ✱1·4, ✱2·38, ✱2·06] -/
theorem t2_74 (p : F) (q : F) (r : F) : Thm (s2_74 p q r) := pm2_74 p q r

/-- *2.75 — [✱2·74, ✱2·53, ✱2·31] -/
theorem t2_75 (p : F) (q : F) (r : F) : Thm (s2_75 p q r) := pm2_75 p q r

/-- *2.76 — [✱2·75, ✱2·04] -/
theorem t2_76 (p : F) (q : F) (r : F) : Thm (s2_76 p q r) := comm (t2_75 p q r)

/-- *2.77 — [✱2·76 (∼p/p)] -/
theorem t2_77 (p : F) (q : F) (r : F) : Thm (s2_77 p q r) := t2_76 (.neg p) q r

/-- *2.81 — [✱1·6, ✱2·76, ✱2·05] -/
theorem t2_81 (p : F) (q : F) (r : F) (s : F) : Thm (s2_81 p q r s) :=
  sylEnd (Thm.sum p q (imp r s)) (t2_76 p r s)

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

/-- *3.3 — exportation [✱3·2] -/
theorem t3_3 (p : F) (q : F) (r : F) : Thm (s3_3 p q r) := ofPf <| by
  unfold s3_3; intro_; intro_; intro_
  exact mp (andI (hy 1) (hy 2)) (hy 0)

/-- *3.37 — [✱3·2, ✱3·26, ✱3·27, ✱2·01, ✱2·24] -/
theorem t3_37 (p : F) (q : F) (r : F) : Thm (s3_37 p q r) := ofPf <| by
  unfold s3_37; intro_; intro_
  exact negI' r (mp (andI (andE1 (hy 1)) (hy 2)) (hy 0)) (andE2 (hy 1))

/-- *3.43 — composition [✱3·2, ✱3·26, ✱3·27] -/
theorem t3_43 (p : F) (q : F) (r : F) : Thm (s3_43 p q r) := ofPf <| by
  unfold s3_43; intro_; intro_
  exact andI (mp (hy 1) (andE1 (hy 0))) (mp (hy 1) (andE2 (hy 0)))

/-- *3.44 — [✱3·26, ✱3·27, ∨-elimination (✱1·6, ✱1·4, ✱1·2)] -/
theorem t3_44 (p : F) (q : F) (r : F) : Thm (s3_44 p q r) := ofPf <| by
  unfold s3_44; intro_; intro_
  exact orE (hy 1) (mp (hy 2) (andE1 (hy 0))) (mp (hy 2) (andE2 (hy 0)))

/-- *3.47 — [✱3·26, ✱3·27, ✱3·2] -/
theorem t3_47 (p : F) (q : F) (r : F) (s : F) : Thm (s3_47 p q r s) := ofPf <| by
  unfold s3_47; intro_; intro_
  exact andI (mp (andE1 (hy 1)) (andE1 (hy 0))) (mp (andE2 (hy 1)) (andE2 (hy 0)))

/-- *3.48 — [✱3·26, ✱3·27, ✱1·3, ✱2·2, ∨-elimination] -/
theorem t3_48 (p : F) (q : F) (r : F) (s : F) : Thm (s3_48 p q r s) := ofPf <| by
  unfold s3_48; intro_; intro_
  exact orE (hy 1) (orIL (mp (hy 2) (andE1 (hy 0)))) (orIR (mp (hy 2) (andE2 (hy 0))))

/-- *4.11 — [✱2·16, ✱2·17, ✱3·2, ✱3·26, ✱3·27] -/
theorem t4_11 (p : F) (q : F) : Thm (s4_11 p q) := ofPf <| by
  unfold s4_11; split_iff
  · exact iffI (app (t2_16 q p) (iffMpr (hy 0))) (app (t2_16 p q) (iffMp (hy 0)))
  · exact iffI (app (t2_17 p q) (iffMpr (hy 0))) (app (t2_17 q p) (iffMp (hy 0)))

/-- *4.12 — [✱2·03, ✱2·15, ✱3·2, ✱3·26, ✱3·27] -/
theorem t4_12 (p : F) (q : F) : Thm (s4_12 p q) := ofPf <| by
  unfold s4_12; split_iff
  · exact iffI (app (t2_03 p q) (iffMp (hy 0))) (app (t2_15 q p) (iffMpr (hy 0)))
  · exact iffI (app (t2_03 q p) (iffMp (hy 0))) (app (t2_15 p q) (iffMpr (hy 0)))

/-- *4.14 — [✱3·37 (→); ← by reductio ✱2·18] -/
theorem t4_14 (p : F) (q : F) (r : F) : Thm (s4_14 p q r) := ofPf <| by
  unfold s4_14; split_iff
  · exact app (t3_37 p q r) (hy 0)
  · intro_
    exact byContra' q (andE2 (hy 1)) (mp (andI (andE1 (hy 1)) (hy 2)) (hy 0))

/-- *4.15 — [✱3·2, ✱3·26, ✱3·27, ✱2·01, ✱2·24] -/
theorem t4_15 (p : F) (q : F) (r : F) : Thm (s4_15 p q r) := ofPf <| by
  unfold s4_15; split_iff
  · intro_
    exact negI' r (andE2 (hy 1)) (mp (andI (hy 2) (andE1 (hy 1))) (hy 0))
  · intro_
    exact negI' p (andE1 (hy 1)) (mp (andI (andE2 (hy 1)) (hy 2)) (hy 0))

/-- *4.22 — [✱3·26, ✱3·27, ✱3·2] -/
theorem t4_22 (p : F) (q : F) (r : F) : Thm (s4_22 p q r) := ofPf <| by
  unfold s4_22; intro_
  exact iffI (Pf.intro (mp (mp (hy 1) (iffMp (andE1 (hy 0)))) (iffMp (andE2 (hy 0)))))
    (Pf.intro (mp (mp (hy 1) (iffMpr (andE2 (hy 0)))) (iffMpr (andE1 (hy 0)))))

/-- *4.32 — [✱3·2, ✱3·26, ✱3·27] -/
theorem t4_32 (p : F) (q : F) (r : F) : Thm (s4_32 p q r) := ofPf <| by
  unfold s4_32; split_iff
  · exact andI (andE1 (andE1 (hy 0))) (andI (andE2 (andE1 (hy 0))) (andE2 (hy 0)))
  · exact andI (andI (andE1 (hy 0)) (andE1 (andE2 (hy 0)))) (andE2 (andE2 (hy 0)))

/-- *4.36 — [✱3·45, ✱3·2] -/
theorem t4_36 (p : F) (q : F) (r : F) : Thm (s4_36 p q r) := ofPf <| by
  unfold s4_36; intro_
  exact iffI (app (t3_45 p q r) (iffMp (hy 0))) (app (t3_45 q p r) (iffMpr (hy 0)))

/-- *4.37 — [✱2·38 (the ✱1·6 analogue for the left disjunct), ✱3·2] -/
theorem t4_37 (p : F) (q : F) (r : F) : Thm (s4_37 p q r) := ofPf <| by
  unfold s4_37; intro_
  exact iffI (app (t2_38 r p q) (iffMp (hy 0))) (app (t2_38 r q p) (iffMpr (hy 0)))

/-- *4.38 — [✱3·47, ✱3·2, ✱3·26, ✱3·27] -/
theorem t4_38 (p : F) (q : F) (r : F) (s : F) : Thm (s4_38 p q r s) := ofPf <| by
  unfold s4_38; intro_
  exact iffI (app (t3_47 p q r s) (andI (iffMp (andE1 (hy 0))) (iffMp (andE2 (hy 0)))))
    (app (t3_47 r s p q) (andI (iffMpr (andE1 (hy 0))) (iffMpr (andE2 (hy 0)))))

/-- *4.39 — [✱3·48, ✱3·2, ✱3·26, ✱3·27] -/
theorem t4_39 (p : F) (q : F) (r : F) (s : F) : Thm (s4_39 p q r s) := ofPf <| by
  unfold s4_39; intro_
  exact iffI (app (t3_48 p q r s) (andI (iffMp (andE1 (hy 0))) (iffMp (andE2 (hy 0)))))
    (app (t3_48 r s p q) (andI (iffMpr (andE1 (hy 0))) (iffMpr (andE2 (hy 0)))))

/-- *4.4 — [✱3·2, ✱3·26, ✱3·27, ✱1·3, ✱2·2, ∨-elimination] -/
theorem t4_4 (p : F) (q : F) (r : F) : Thm (s4_4 p q r) := ofPf <| by
  unfold s4_4; split_iff
  · exact orE (andE2 (hy 0)) (orIL (andI (andE1 (hy 0)) (hy 1))) (orIR (andI (andE1 (hy 0)) (hy 1)))
  · exact orE (hy 0) (andI (andE1 (hy 1)) (orIL (andE2 (hy 1))))
      (andI (andE1 (hy 1)) (orIR (andE2 (hy 1))))

/-- *4.41 — [✱3·2, ✱3·26, ✱3·27, ✱1·3, ✱2·2, ∨-elimination] -/
theorem t4_41 (p : F) (q : F) (r : F) : Thm (s4_41 p q r) := ofPf <| by
  unfold s4_41; split_iff
  · exact orE (hy 0) (andI (orIL (hy 1)) (orIL (hy 1)))
      (andI (orIR (andE1 (hy 1))) (orIR (andE2 (hy 1))))
  · exact orE (andE1 (hy 0)) (orIL (hy 1))
      (orE (andE2 (hy 0)) (orIL (hy 2)) (orIR (andI (hy 1) (hy 2))))

/-- *4.42 — [✱2·11 (cases), ✱3·2, ✱3·26] -/
theorem t4_42 (p : F) (q : F) : Thm (s4_42 p q) := ofPf <| by
  unfold s4_42; split_iff
  · exact Pf.cases q (orIL (andI (hy 0) (hy 1))) (orIR (andI (hy 0) (hy 1)))
  · exact orE (hy 0) (andE1 (hy 1)) (andE1 (hy 1))

/-- *4.43 — [✱2·2, ✱3·2, ✱3·26, ✱3·27, ✱2·24] -/
theorem t4_43 (p : F) (q : F) : Thm (s4_43 p q) := ofPf <| by
  unfold s4_43; split_iff
  · exact andI (orIL (hy 0)) (orIL (hy 0))
  · exact orE (andE1 (hy 0)) (hy 1) (orE (andE2 (hy 0)) (hy 2) (absurd _ (hy 1) (hy 2)))

/-- *4.44 — [✱2·2, ✱3·26, ∨-elimination] -/
theorem t4_44 (p : F) (q : F) : Thm (s4_44 p q) := ofPf <| by
  unfold s4_44; split_iff
  · exact orIL (hy 0)
  · exact orE (hy 0) (hy 1) (andE1 (hy 1))

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

end PM
