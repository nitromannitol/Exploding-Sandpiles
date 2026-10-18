/-
The negative-site barrier for the `S`-frozen parallel toppling odometer.

Let `w_t = fodo S η (Set.indicator S 1) t` be the frozen odometer seeded by the
indicator of its own frozen set `S`, on a background `η ≤ 2d - 1`.  A site
`x ∉ S` with `η x < 0` is never toppled: the odometer is at most `1` everywhere
(`fodo_le_one`), so the neighbour sum of `w_t` at `x` is at most `2d`, and the
delivered height `η x + Δ w_t x` stays strictly below the threshold `2d`.

This is the process consumed by `PathFillingHyp`, whose frozen odometer is
`fodo (z '' {i | i < m}) η (Set.indicator (z '' {i | i < m}) 1)`, with the
frozen set and the seed support both equal to the path `z '' {i | i < m}`.
-/
import Exploding.Support.SubFodo

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The negative-site barrier: if `x ∉ S` and `η x < 0`, then the `S`-frozen
odometer seeded by `Set.indicator S 1` vanishes at `x` at every time. -/
theorem fodo_eq_zero_of_neg (S : Set (Site d)) (η : Site d → ℤ) (x : Site d)
    (hη : ∀ y, η y ≤ 2 * (d : ℤ) - 1) (hx : x ∉ S) (hneg : η x < 0)
    (t : ℕ) : fodo S η (Set.indicator S 1) t x = 0 := by
  have hw0 : ∀ y, Set.indicator S (1 : Site d → ℤ) y ≤ 1 := by
    intro y
    by_cases hy : y ∈ S <;> simp [hy]
  have hw0nn : ∀ y, 0 ≤ Set.indicator S (1 : Site d → ℤ) y := by
    intro y
    by_cases hy : y ∈ S <;> simp [hy]
  induction t with
  | zero => rw [fodo_zero]; exact Set.indicator_of_notMem hx _
  | succ t ih =>
    have hle := fodo_le_one S η (Set.indicator S 1) hη hw0 hw0nn t
    have h1 : nbrSumZ (fodo S η (Set.indicator S 1) t) x ≤
        nbrSumZ (fun _ : Site d => (1 : ℤ)) x := nbrSumZ_mono hle x
    have h2 : nbrSumZ (fun _ : Site d => (1 : ℤ)) x = 2 * (d : ℤ) := by
      simp [nbrSumZ]; ring
    have hnot : ¬ (2 * (d : ℤ) ≤ fconf S η (Set.indicator S 1) t x) := by
      simp only [fconf, lap, ih, mul_zero, sub_zero]
      intro h
      linarith
    rw [fodo_succ, if_neg hx, ih, if_neg hnot, add_zero]

end Exploding
