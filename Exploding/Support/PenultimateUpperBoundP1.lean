import Exploding.Support.AllHighLastArrival
import Exploding.Support.ArxivP1Crossing

/-!
# The penultimate upper bound at parameter one

The actual endpoint law is concentrated on the all-high background, where the
last-wave arrival time is the positive-time Manhattan radius.  Taking both
deterministic constants to be one gives the source bound for every site in the
stated window once the logarithm is at least one.
-/

namespace Exploding

open Exploding LatticeProb MeasureTheory

/-- At parameter one, the all-high last-arrival formula gives the penultimate
upper bound with deterministic exponent and coefficient one. -/
theorem penultimate_upper_bound_p1 (d : ℕ) (hd : 2 ≤ d) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧
      ∀ᵐ η ∂(toyLaw d (1 : ℝ)), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        ∀ x : Site d, mnorm x ≤ (n : ℤ) →
          ∃ m : ℕ, lastArrival η (0 : Site d) x = (m : ℕ∞) ∧
            (m : ℝ) ≤ C * (mnorm x : ℝ) + Real.log n ^ γ := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  rw [toyLaw_one_eq_dirac, MeasureTheory.ae_dirac_eq]
  simp only [Filter.Eventually, Filter.mem_pure]
  refine ⟨3, ?_⟩
  intro n hn x _
  let r : ℤ := mnorm x
  let m : ℕ := max 1 r.toNat
  refine ⟨m, ?_, ?_⟩
  · simpa [r, m] using
      (all_high_last_arrival_eq d hd (0 : Site d) x)
  · have hr_nonneg : 0 ≤ r := by
      dsimp [r, mnorm]
      apply Finset.sum_nonneg
      intro i hi
      exact abs_nonneg _
    have hr_cast : (r.toNat : ℝ) = (r : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hr_nonneg)
    have hm_cast : (m : ℝ) = max 1 (r : ℝ) := by
      simp only [m, Nat.cast_max, Nat.cast_one, hr_cast]
    have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
      have h := Real.le_log_one_add_of_nonneg (x := (2 : ℝ)) (by norm_num)
      norm_num at h
      exact h
    have hn_real : (3 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hlog : (1 : ℝ) ≤ Real.log (n : ℝ) :=
      le_trans hlog3 (Real.log_le_log (by norm_num) hn_real)
    have hr_real_nonneg : (0 : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast hr_nonneg
    have hmax_le : max 1 (r : ℝ) ≤ (r : ℝ) + Real.log (n : ℝ) := by
      exact max_le (by linarith) (by linarith)
    have hbound : (m : ℝ) ≤ (mnorm x : ℝ) + Real.log (n : ℝ) := by
      calc
        (m : ℝ) = max 1 (r : ℝ) := hm_cast
        _ ≤ (r : ℝ) + Real.log (n : ℝ) := hmax_le
        _ = (mnorm x : ℝ) + Real.log (n : ℝ) := by simp [r]
    simpa only [one_mul, Real.rpow_one] using hbound

end Exploding
