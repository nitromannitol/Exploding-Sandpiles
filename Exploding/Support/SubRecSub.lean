/-
The recurrence odometer of Proposition 7.3 of `paper/exploding.tex`.
-/
import Exploding.Support.SubMax
import Exploding.Support.SubTopple
import Exploding.Support.SubRecOne

namespace Exploding

open LatticeProb
open scoped Classical

variable {d : ℕ}

/-- The set of toppled sites of `V` grows with time. -/
theorem recOdo_subset_succ (d : ℕ) (hd : 1 ≤ d) (V : Finset (Site d)) (t : ℕ) :
    V.filter (fun x => recOdo d V t x = 1) ⊆ V.filter (fun x => recOdo d V (t + 1) x = 1) := by
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  refine ⟨hx.1, ?_⟩
  have h1 := recOdo_mono d V t x
  have h2 := recOdo_le_one d hd V (t + 1) hx.1
  omega

end Exploding
