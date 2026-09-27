/-
The firing case of the box-crossing transport step.

Setup: `redOdoUpAt i n η t x = 0` (from `redOdoUpAt_zero_or_one`), the inductive hypothesis
gives `redOdoUpAt i n η t y ≤ fodo … (T + t) y` for every `y`, and the threshold
`2(d+1) ≤ η x + lap (redOdoUpAt i n η t) x` holds.  The goal is
`redOdoUpAt i n η (t + 1) x ≤ fodo … (T + (t + 1)) x`.

The proof below splits on whether `fodo … (T + t) x = 0`:
  * if it is 0, the threshold for `fodo` follows from `nbrSumZ_mono` on the inductive
    hypothesis together with the `-1` shift in `redOdoUpAt`'s definition, so `fodo` fires
    at `x` and the right side is `1`, which caps the left side by `redOdoUpAt_le_one`;
  * if it is not 0, then it is at least `1` (by `fodo_nonneg`), and `fodo_mono_time'`
    carries that to `T + (t + 1)`, again capping the left side by `redOdoUpAt_le_one`.

KEY OBSERVATION for the remaining `hxS` sub-case: `x ∈ ((rboxShift (fun _ : Fin (d+1) => n)
(0 : Site (d+1)))ᶜ)` is IMPOSSIBLE here, because `rboxShift (fun _ => n) 0 = cube (d+1) n`
(that is `aux_box_crossing_rboxShift_zero_eq_cube` in `wip/decomp/BoxCrossingAux.lean`) and
the enclosing case has `hc : ¬ x ∉ cube (d + 1) n`, i.e. `x ∈ cube (d+1) n`.  So the
`hxS` branch should be closed by `exfalso` from that identification, not by the indicator
argument the draft attempts.
-/
import Exploding.Support.ReductionShift
import Exploding.Support.SubFodo
open Exploding LatticeProb MeasureTheory
open scoped Classical
variable {d : ℕ}

/-- The firing case of the transport step. -/
theorem fodo_fires_of_redOdoUpAt (n : ℕ) (η : Site (d + 1) → ℤ) (i : ℤ) (T t : ℕ)
    (x : Site (d + 1))
    (hle1 : ∀ y, redOdoUpAt i n η t y ≤
      fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
        (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
          (fun _ => (1 : ℤ))) (T + t) y)
    (h0 : redOdoUpAt i n η t x = 0)
    (hthr : 2 * ((d : ℤ) + 1) ≤ η x + lap (redOdoUpAt i n η t) x) :
    redOdoUpAt i n η (t + 1) x ≤
      fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
        (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
          (fun _ => (1 : ℤ))) (T + (t + 1)) x := by
  by_cases hf : fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
      (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
        (fun _ => (1 : ℤ))) (T + t) x = 0
  · have hthr' : 2 * ((d : ℤ) + 1) ≤ η x + lap (fodo ((rboxShift (fun _ : Fin (d+1) => n)
        (0 : Site (d+1)))ᶜ) η
        (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
          (fun _ => (1 : ℤ))) (T + t)) x := by
      simp only [lap]
      rw [hf, mul_zero, sub_zero]
      have hmono : nbrSumZ (redOdoUpAt i n η t) x ≤
          nbrSumZ (fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
            (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
              ⟨0, by omega⟩ false) (fun _ => (1 : ℤ))) (T + t)) x :=
        nbrSumZ_mono (fun y => hle1 y) x
      simp only [lap] at hthr
      rw [h0, mul_zero, sub_zero] at hthr
      linarith
    have hle1' : redOdoUpAt i n η (t + 1) x ≤ 1 := redOdoUpAt_le_one n η i (t + 1) x
    have hfodo1 : fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
        (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
          (fun _ => (1 : ℤ))) (T + (t + 1)) x = 1 := by
      have hidx : T + (t + 1) = (T + t) + 1 := by omega
      rw [hidx, fodo_succ]
      by_cases hxS : x ∈ ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ)
      · rw [if_pos hxS]
        rw [fodo_of_mem _ _ _ _ hxS] at hf
        by_cases hmem : x ∈ faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
          ⟨0, by omega⟩ false
        · rw [Set.indicator_of_mem hmem] at hf
          exact absurd hf (by norm_num)
        · rw [Set.indicator_of_notMem hmem] at hf
          exact hf
      · rw [if_neg hxS, if_pos hthr', hf]
        ring
    rw [hfodo1]
    exact hle1'
  · have hpos : 1 ≤ fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
        (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
          (fun _ => (1 : ℤ))) (T + t) x := by
      have hnn : (0 : ℤ) ≤ fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
          (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
            ⟨0, by omega⟩ false) (fun _ => (1 : ℤ))) (T + t) x :=
        fodo_nonneg _ _ _
          (Set.indicator_nonneg (fun _ _ => zero_le_one)) (T + t) x
      omega
    exact le_trans (le_trans (redOdoUpAt_le_one n η i (t + 1) x) hpos)
      (fodo_mono_time' _ _ _ (T + t) (T + (t + 1)) x (by omega))
