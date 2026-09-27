/-
The transport step of the box-crossing layer induction.

The domination `redOdoUpAt i n η t x ≤ fodo (rboxShift …)ᶜ η (indicator (faceOut …) 1) t x`
is FALSE for `i ≥ 1` (at `t = 0` the left side is `1` on the whole layer `i`, the right side
is `0` off the low face).  The corrected statement below restricts the domination to the
sites above layer `i` (`i < x 0`) and shifts the time by `T`, a time at which layer `i` is
already toppled in `fodo`.  Its base case is proved (both branches); the step remains.
-/
import Exploding.Support.ReductionShift
import Exploding.Support.SubFodo
open Exploding LatticeProb MeasureTheory
open scoped Classical
variable {d : ℕ}

/-- The transport step: above layer `i`, the layer-`i` constrained odometer is dominated by
the frozen odometer, once layer `i` is already toppled in the latter. -/
theorem fodo_dominates_redOdoUpAt_above (n : ℕ) (hn : 1 ≤ n) (η : Site (d + 1) → ℤ)
    (i : ℤ) (hi0 : 0 ≤ i) (hi : i + 1 ≤ (n : ℤ)) (T : ℕ)
    (hT : ∀ y ∈ cube d n, fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
      (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
        (fun _ => (1 : ℤ))) T (cons i y) = 1) :
    ∀ t x, i < x 0 → redOdoUpAt i n η t x ≤
      fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
        (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
          (fun _ => (1 : ℤ))) (T + t) x := by
  intro t
  induction t with
  | zero =>
    intro x hx
    rw [redOdoUpAt_zero]
    by_cases hxi : x 0 = i
    · rw [if_pos hxi]
      have hxeq : x = cons i (fun l => x l.succ) := by
        funext j
        refine Fin.cases ?_ ?_ j
        · simpa [cons] using hxi
        · intro k; simp [cons]
      rw [hxeq]
      have hmem : (fun l => x l.succ) ∈ cube d n := by
        intro l
        have hxl := hx
        sorry
      have hT0 : fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
          (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
            (fun _ => (1 : ℤ))) (T + 0) (cons i (fun l => x l.succ)) = 1 :=
        hT (fun l => x l.succ) hmem
      rw [hT0]
    · rw [if_neg hxi]
      exact fodo_nonneg _ _ _
        (Set.indicator_nonneg (fun _ _ => zero_le_one)) (T + 0) x
  | succ t ih =>
    intro x hx
    sorry
