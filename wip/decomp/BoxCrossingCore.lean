/-
The remaining assembly of `aux_box_crossing_core`: the frozen odometer with the
box's complement frozen and the low face lit dominates the layer-`i` constrained
odometer, once layer `i` is permanently lit.  The seed (`cons_zero_mem_faceOut`)
and the layer step (`layer_topples`) are both proved in
`Exploding/Support/ReductionShift.lean`; what remains is the induction on `t`
below, whose base case needs the seed and whose step needs the layer chain.
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
      sorry
    · rw [if_neg hx]
      sorry
  | succ t ih =>
    intro x
    sorry
