/-
The firing case of the box-crossing transport step.

The transport statement itself (with its base case and three of its four step leaves
proved) is in the git history of this file; this is the isolated firing case, which is the
one remaining leaf.

Setup: `redOdoUpAt i n η t x = 0` (from `redOdoUpAt_zero_or_one`), the inductive hypothesis
gives `redOdoUpAt i n η t y ≤ fodo … (T + t) y` for every `y`, and the threshold
`2(d+1) ≤ η x + lap (redOdoUpAt i n η t) x` holds.  The goal is
`fodo … (T + (t + 1)) x = 1`.

The route: `fodo_succ` (after `T + (t+1) = (T+t)+1`), then the `x ∉ S` branch, then
`if_pos` on the threshold.  The threshold for `fodo` is
`2(d+1) ≤ η x + lap (fodo … (T+t)) x`, which follows from `nbrSumZ_mono` applied to the
inductive hypothesis together with the `-1` shift in `redOdoUpAt`'s definition.  The
remaining sub-goal in the draft below is the `fodo … (T+t) x = 0` step: it is NOT implied
by the bounds available (`fodo` is unbounded above here, since `fodo_le_one` needs
`s0 ≤ 2d - 1` and `s0 = η` is unbounded), so the case must instead be closed by observing
that `fodo`'s own recursion fires at `x` regardless of its current value — i.e. by
`fodo_succ` plus `if_pos` on the threshold, with no appeal to `fodo … (T+t) x = 0`.
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
    fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
      (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
        (fun _ => (1 : ℤ))) (T + (t + 1)) x = 1 := by
  have hidx : T + (t + 1) = (T + t) + 1 := by omega
  rw [hidx, fodo_succ]
  by_cases hxS : x ∈ ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ)
  · rw [if_pos hxS]
    sorry
  · rw [if_neg hxS]
    rw [if_pos]
    have hmono : nbrSumZ (redOdoUpAt i n η t) x ≤
        nbrSumZ (fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
          (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
            ⟨0, by omega⟩ false) (fun _ => (1 : ℤ))) (T + t)) x :=
      nbrSumZ_mono (fun y => hle1 y) x
    simp only [fconf, lap] at *
    rw [h0] at hthr
    simp only [mul_zero, sub_zero] at hthr
    have hd0 : (0 : ℤ) ≤ (d : ℤ) := by positivity
    have hle := hle1 x
    rw [h0] at hle
    have hnn : (0 : ℤ) ≤ fodo ((rboxShift (fun _ : Fin (d+1) => n)
        (0 : Site (d+1)))ᶜ) η
        (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
          ⟨0, by omega⟩ false) (fun _ => (1 : ℤ))) (T + t) x :=
      fodo_nonneg _ _ _
        (Set.indicator_nonneg (fun _ _ => zero_le_one)) (T + t) x
    have hfodo0 : fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
        (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
          ⟨0, by omega⟩ false) (fun _ => (1 : ℤ))) (T + t) x = 0 := by
      by_contra hne
      have hpos : 1 ≤ fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
          (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
            ⟨0, by omega⟩ false) (fun _ => (1 : ℤ))) (T + t) x := by omega
      sorry
    rw [hfodo0]
    ring
