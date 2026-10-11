import PM.Basic
namespace PM
open F
local notation "p" => F.var "p"
local notation "q" => F.var "q"
local notation "r" => F.var "r"

/-- ✱2·02 Simp. ⊢ : q . ⊃ . p ⊃ q.   Dem. [Add ∼p/p] ⊢ : q . ⊃ . ∼p ∨ q, then (✱1·01). -/
theorem thm2_02 : Thm (imp q (imp p q)) := Thm.add (.neg p) q

/-- ✱1·4 (Perm) is `p ∨ q . ⊃ . q ∨ p` in the 1910 print. The Gutenberg #78050 transcription, which this
    project relies on throughout, has `p ∨ p` in place of `q ∨ p` here, a one-letter slip. This check shows
    the one-letter variant is not a theorem (countermodel: p false, q true), which is how the slip was found. -/
theorem star1_4_variant_not_a_theorem : ¬ Thm (imp (.or p q) (.or p p)) :=
  not_thm_of_countermodel (fun s => s == "q") (by decide)

end PM
