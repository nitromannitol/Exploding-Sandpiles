/-
A site off the frozen set that has not yet toppled and holds at least `2d` chips
topples at the next step.  This is the step that drives the line propagation in
the proof of Proposition 7.5.
-/
import Exploding.Support.Hypotheses

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- A site off the frozen set with at least `2d` chips topples at the next step. -/
theorem fodo_topple_of_ge (S : Set (Site d)) (s0 w0 : Site d → ℤ) (t : ℕ) {x : Site d}
    (hx : x ∉ S) (h0 : fodo S s0 w0 t x = 0) (hge : 2 * d ≤ fconf S s0 w0 t x) :
    fodo S s0 w0 (t + 1) x = 1 := by
  classical
  rw [Exploding.fodo_succ, if_neg hx, if_pos hge, h0]
  ring

end Exploding
