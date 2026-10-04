import PM.Basic
namespace PM
open F
local notation "p" => F.var "p"
local notation "q" => F.var "q"
local notation "r" => F.var "r"

/-- ✱2·02 Simp. ⊢ : q . ⊃ . p ⊃ q.   Dem. [Add ∼p/p] ⊢ : q . ⊃ . ∼p ∨ q, then (✱1·01). -/
theorem thm2_02 : Thm (imp q (imp p q)) := Thm.add (.neg p) q

/-- Gutenberg #78050 printed ✱1·4 as `p ∨ q . ⊃ . p ∨ p`; the 1910 print has `q ∨ p`.
    The transcribed version is refuted: p false, q true. -/
theorem gutenberg_1_4_refuted : ¬ Thm (imp (.or p q) (.or p p)) :=
  not_thm_of_countermodel (fun s => s == "q") (by decide)

end PM
