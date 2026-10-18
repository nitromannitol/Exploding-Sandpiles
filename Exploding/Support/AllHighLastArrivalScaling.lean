import Exploding.Support.AllHighLastArrival
import Exploding.Support.Gen

/-!
# Scaling error for the all-high last arrival

The exact all-high arrival formula identifies the positive-time arrival with
the rounded Manhattan distance, including arrival time one at the origin.
Coordinatewise rounding changes the real Manhattan norm by at most the
dimension, and the positive-time clock contributes at most one more.
-/
namespace Exploding

open LatticeProb

/-- The rescaled actual all-high last arrival differs from the real Manhattan
norm by at most the rounding error and the positive-time origin correction. -/
theorem all_high_last_arrival_scaling_error_le
    (d : ℕ) (hd : 2 ≤ d) (n : ℕ) (hn : 1 ≤ n) (y : Fin d → ℝ) :
    |((lastArrival (fun _ : Site d => 2 * (d : ℤ) - 1)
        (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
      - (∑ i : Fin d, |y i|)| ≤ ((d : ℝ) + 1) / (n : ℝ) := by
  let x : Site d := nearestSite ((n : ℝ) • y)
  let τ : ℕ∞ := lastArrival (fun _ : Site d => 2 * (d : ℤ) - 1) 0 x
  let r : ℕ := (mnorm x).toNat
  let b : ℝ := ∑ i : Fin d, |y i|
  have hformula : τ = ((max 1 r : ℕ) : ℕ∞) := by
    simpa [τ, r] using all_high_last_arrival_eq d hd (0 : Site d) x
  have hfinite : τ ≠ ⊤ := by
    rw [hformula]
    simp
  have hfinite_repr : ∃ k : ℕ, τ = (k : ℕ∞) := by
    cases hτ : τ with
    | top => exact (hfinite hτ).elim
    | coe k => exact ⟨k, rfl⟩
  obtain ⟨k, hkcoe⟩ := hfinite_repr
  have hk : k = max 1 r := by
    exact_mod_cast hkcoe.symm.trans hformula
  have harrival_nat : τ.toNat = max 1 r := by
    rw [hkcoe, ENat.toNat_coe, hk]
  have hmnorm_nonneg : 0 ≤ mnorm x := by
    unfold mnorm
    exact Finset.sum_nonneg fun i hi => abs_nonneg _
  have hr_cast : (r : ℝ) = (mnorm x : ℝ) := by
    dsimp [r]
    have hcast : (((mnorm x).toNat : ℕ) : ℤ) = mnorm x :=
      Int.toNat_of_nonneg hmnorm_nonneg
    exact_mod_cast hcast
  have hclock : |(τ.toNat : ℝ) - (mnorm x : ℝ)| ≤ 1 := by
    rw [harrival_nat, ← hr_cast]
    have hr_le : r ≤ max 1 r := Nat.le_max_right 1 r
    have hmax_le : max 1 r ≤ r + 1 := by omega
    have hr_le_real : (r : ℝ) ≤ (max 1 r : ℝ) := by exact_mod_cast hr_le
    have hmax_le_real : (max 1 r : ℝ) ≤ (r : ℝ) + 1 := by
      exact_mod_cast hmax_le
    simp only [Nat.cast_max, Nat.cast_one]
    rw [abs_of_nonneg (sub_nonneg.mpr hr_le_real)]
    linarith
  have hcoordinate (i : Fin d) :
      |(x i : ℝ) - (n : ℝ) * y i| ≤ 1 := by
    have hround : |(x i : ℝ) - ((n : ℝ) • y) i| ≤ 1 := by
      simpa [x] using Gen.nearestSite_sub_le ((n : ℝ) • y) i
    simpa only [Pi.smul_apply, smul_eq_mul] using hround
  have hnorm_real : (mnorm x : ℝ) = ∑ i : Fin d, |(x i : ℝ)| := by
    simp [mnorm]
  have hscaled_sum : (n : ℝ) * b = ∑ i : Fin d, |(n : ℝ) * y i| := by
    dsimp [b]
    calc
      (n : ℝ) * (∑ i : Fin d, |y i|)
          = ∑ i : Fin d, (n : ℝ) * |y i| := by
              simpa using
                (Finset.mul_sum Finset.univ (fun i : Fin d => |y i|) (n : ℝ))
      _ = ∑ i : Fin d, |(n : ℝ) * y i| := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [abs_mul]
            exact (congrArg (fun z : ℝ => z * |y i|)
              (abs_of_nonneg (Nat.cast_nonneg n))).symm
  have hnorm : |(mnorm x : ℝ) - (n : ℝ) * b| ≤ (d : ℝ) := by
    calc
      |(mnorm x : ℝ) - (n : ℝ) * b|
          = |∑ i : Fin d, (|(x i : ℝ)| - |(n : ℝ) * y i|)| := by
              rw [hnorm_real, hscaled_sum, ← Finset.sum_sub_distrib]
      _ ≤ ∑ i : Fin d, |(|(x i : ℝ)| - |(n : ℝ) * y i|)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin d, (1 : ℝ) :=
            Finset.sum_le_sum fun i hi =>
              (abs_abs_sub_abs_le_abs_sub _ _).trans (hcoordinate i)
      _ = (d : ℝ) := by simp
  have htotal : |(τ.toNat : ℝ) - (n : ℝ) * b| ≤ (d : ℝ) + 1 := by
    calc
      |(τ.toNat : ℝ) - (n : ℝ) * b| ≤ 1 + (d : ℝ) :=
        Gen.abs_sub_le_of_le (τ.toNat : ℝ) (mnorm x : ℝ) ((n : ℝ) * b)
          1 (d : ℝ) hclock hnorm
      _ = (d : ℝ) + 1 := by ring
  have hn_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  change |(τ.toNat : ℝ) / (n : ℝ) - b| ≤ ((d : ℝ) + 1) / (n : ℝ)
  have hrewrite : (τ.toNat : ℝ) / (n : ℝ) - b =
      ((τ.toNat : ℝ) - (n : ℝ) * b) / (n : ℝ) := by
    field_simp [ne_of_gt hn_real]
  rw [hrewrite, abs_div, abs_of_pos hn_real, div_le_div_iff₀ hn_real hn_real]
  exact mul_le_mul_of_nonneg_right htotal (le_of_lt hn_real)

end Exploding
