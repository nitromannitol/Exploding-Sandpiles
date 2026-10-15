import Exploding.Support.AllHighClusterArrival
import Exploding.Support.AllHighLastArrival
import Exploding.Support.ArxivP1Crossing

/-!
# Penultimate arrival closeness at parameter one

At parameter one, the actual law is concentrated on the all-high background.
There the cluster arrival equals the finite last arrival at every target site,
so the requested logarithmic bound holds with exponent one.
-/

namespace Exploding

open Exploding LatticeProb MeasureTheory

/-- At parameter one, equality of the two arrivals gives the penultimate
closeness bound with deterministic exponent one. -/
theorem last_penultimate_close_p1 (d : ℕ) (hd : 2 ≤ d) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ᵐ η ∂(toyLaw d (1 : ℝ)), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        ∀ x : Site d, mnorm x ≤ (n : ℤ) →
          lastArrival η (0 : Site d) x ≤ clusterArrival η (0 : Site d) x ∧
            ∃ a b : ℕ, lastArrival η (0 : Site d) x = (a : ℕ∞) ∧
              clusterArrival η (0 : Site d) x = (b : ℕ∞) ∧
                (b : ℝ) ≤ (a : ℝ) + Real.log n ^ γ := by
  refine ⟨1, by norm_num, ?_⟩
  rw [toyLaw_one_eq_dirac, MeasureTheory.ae_dirac_eq]
  simp only [Filter.Eventually, Filter.mem_pure]
  refine ⟨1, ?_⟩
  intro n hn x _
  let m : ℕ := max 1 (mnorm x).toNat
  have hlast :
      lastArrival (fun _ : Site d => 2 * (d : ℤ) - 1) (0 : Site d) x =
        (m : ℕ∞) := by
    simpa [m] using (all_high_last_arrival_eq d hd (0 : Site d) x)
  have hcluster :=
    all_high_cluster_arrival_eq_last_arrival d hd (0 : Site d) x
  have hlog : (0 : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  refine ⟨hcluster.symm.le, m, m, ?_, ?_, ?_⟩
  · simpa using hlast
  · simpa using hcluster.trans hlast
  · simpa only [Real.rpow_one] using
      (le_add_of_nonneg_right hlog : (m : ℝ) ≤ (m : ℝ) + Real.log (n : ℝ))

end Exploding
