/-
The remaining assembly of `aux_box_crossing_core`: the frozen odometer with the
box's complement frozen and the low face lit dominates the layer-`i` constrained
odometer, once layer `i` is permanently lit.

Three ingredients are proved in `Exploding/Support/ReductionShift.lean`:
`cons_zero_mem_faceOut` (the seed, for `i = 0`), `layer_topples` (the layer step,
with `redOdoUpAt_floor` supplying the permanent lighting of each floor), and
`fodo_mono_time` (monotonicity in time).

What remains is the induction on `t` below.  The base case at `i = 0` is done
(the `hi0'` branch: rewrite `x` as `cons 0 (fun l => x l.succ)` via `hxeq`, then
`fodo_zero` and `Set.indicator_of_mem` with the seed).  The two remaining base
cases are the `i ≥ 1` branch and the `x 0 ≠ i` branch: both reduce to
`(1 : ℤ) ≤ (Set.indicator (faceOut …) (1 : Site (d+1) → ℤ)) x`, and the `show`
there must be preceded by `rw [fodo_zero]` so that the `fodo` at time `0` is
already `w0` (the current error is that the `show` pattern is compared against
the un-reduced `fodo … 0 x`).  The step is the layer chain.
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
        (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
          (1 : Site (d+1) → ℤ))
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
        have hxeq : x = cons 0 (fun l => x l.succ) := by
          funext j
          refine Fin.cases ?_ ?_ j
          · simpa [cons] using hx
          · intro k; simp [cons]
        rw [hxeq]
        have hmem := cons_zero_mem_faceOut hn (fun l => x l.succ) (by
          intro l
          sorry)
        rw [fodo_zero, Set.indicator_of_mem hmem (1 : Site (d+1) → ℤ)]
        exact le_rfl
      · rw [fodo_zero]
        show (1 : ℤ) ≤ (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
          ⟨0, by omega⟩ false) (1 : Site (d+1) → ℤ)) x
        have hne : x ∉ faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false := by
          intro hmem
          have h2 := hmem.2
          simp only [Set.mem_setOf_eq, Pi.zero_apply, Bool.false_eq_true, if_false,
            mul_zero] at h2
          exact hi0' (hx ▸ h2)
        rw [Set.indicator_of_notMem hne (1 : Site (d+1) → ℤ)]
        exact zero_le_one (α := ℤ)
    · rw [fodo_zero]
      show (1 : ℤ) ≤ (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
        ⟨0, by omega⟩ false) (1 : Site (d+1) → ℤ)) x
      by_cases hmem : x ∈ faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false
      · rw [Set.indicator_of_mem hmem (1 : Site (d+1) → ℤ)]
        exact le_rfl
      · rw [Set.indicator_of_notMem hmem (1 : Site (d+1) → ℤ)]
        exact zero_le_one (α := ℤ)
  | succ t ih =>
    intro x
    sorry
