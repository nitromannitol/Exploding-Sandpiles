/-
The remaining assembly of `aux_box_crossing_core`: the frozen odometer with the
box's complement frozen and the low face lit dominates the layer-`i` constrained
odometer, once layer `i` is permanently lit.

Both ingredients are proved in `Exploding/Support/ReductionShift.lean`:
`cons_zero_mem_faceOut` (the seed, for `i = 0`) and `layer_topples` (the layer
step, with `redOdoUpAt_floor` supplying the permanent lighting of each floor).
`fodo_mono_time` in the same file gives the monotonicity in time that the step
needs.  What remains is the induction on `t` below: its base case is the seed at
`i = 0` and `redOdoUpAt_zero` at `i ≥ 1`, and its step is the layer chain.
-/
import Exploding.Support.ReductionShift
open Exploding LatticeProb MeasureTheory
open scoped Classical
variable {d : ℕ}

/-- The frozen odometer with the box's complement frozen and the low face lit dominates
the layer-`i` constrained odometer, once layer `i` is permanently lit. -/
theorem fodo_dominates_redOdoUpAt (n : ℕ) (hn : 1 ≤ n) (η : Site (d + 1) → ℤ) (i : ℤ)
    (hi0 : 0 ≤ i) (hi : i + 1 ≤ (n : ℤ)) :
    ∀ t x, redOdoUpAt i n η t x ≤
      fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
        (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false) 1)
        t x := by
  intro t
  induction t with
  | zero =>
    intro x
    rw [redOdoUpAt_zero]
    by_cases hx : x 0 = i
    · rw [if_pos hx]
      by_cases hi0' : i = 0
      · subst hi0'
        rw [hx]
        exact Set.indicator_of_mem (cons_zero_mem_faceOut hn (fun _ => 0) (by
          intro l
          exact ⟨by omega, by omega⟩)) 1
      · sorry
    · rw [if_neg hx]
      sorry
  | succ t ih =>
    intro x
    sorry
