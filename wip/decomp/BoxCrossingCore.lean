/-
The remaining assembly of `aux_box_crossing_core`: the frozen odometer with the
box's complement frozen and the low face lit dominates the layer-`i` constrained
odometer, once layer `i` is permanently lit.

Three ingredients are proved in `Exploding/Support/ReductionShift.lean`:
`cons_zero_mem_faceOut` (the seed, for `i = 0`), `layer_topples` (the layer step,
with `redOdoUpAt_floor` supplying the permanent lighting of each floor), and
`fodo_mono_time` (monotonicity in time).  What remains is the induction on `t`
below.  Its base case at `i = 0` needs the site `x` with `x 0 = 0` rewritten as
`cons 0 (fun l => x l.succ)` (the `hxeq` step, which is where the current
`OfNat` typeclass error comes from: the `1` in `Set.indicator … 1` needs its
type pinned to `ℤ`); at `i ≥ 1` it is `redOdoUpAt_zero`.  Its step is the layer
chain.
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
        have hx0 : x 0 = 0 := hx
        have hxeq : x = cons 0 (fun l => x l.succ) := by
          funext i
          refine Fin.cases ?_ ?_ i
          · simpa [cons] using hx0
          · intro k; simp [cons]
        rw [hxeq]
        exact Set.indicator_of_mem (cons_zero_mem_faceOut hn (fun l => x l.succ) (by
          intro l
          have hxl := hx0
          sorry)) 1
      · sorry
    · rw [if_neg hx]
      sorry
  | succ t ih =>
    intro x
    sorry
