import Exploding.Support.AllHighPenultimateCluster
import Exploding.Support.ArxivP1Crossing

/-!
# The penultimate cluster at parameter one

The actual endpoint law is concentrated on the all-high background, where the
penultimate cluster at each center is a singleton.  This gives the paper-facing
coordinate bound with the deterministic exponent one.
-/

namespace Exploding

open LatticeProb MeasureTheory

/-- At parameter one, the all-high singleton cluster gives the coordinate bound
with deterministic exponent one. -/
theorem last_penultimate_cluster_p1 (d : ℕ) (hd : 2 ≤ d) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ᵐ η ∂(toyLaw d (1 : ℝ)), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        ∀ x : Site d, mnorm x ≤ (n : ℤ) →
          ∀ y ∈ penultimateCluster η x, ∀ i,
            ((|y i - x i| : ℤ) : ℝ) ≤ Real.log n ^ γ := by
  refine ⟨1, by norm_num, ?_⟩
  rw [toyLaw_one_eq_dirac, MeasureTheory.ae_dirac_eq]
  simp only [Filter.Eventually, Filter.mem_pure]
  refine ⟨1, ?_⟩
  intro n hn x _ y hy i
  rw [all_high_penultimate_cluster_eq_singleton d hd x] at hy
  rw [Set.mem_singleton_iff] at hy
  subst y
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hpow : 0 ≤ Real.log (n : ℝ) ^ (1 : ℝ) := Real.rpow_nonneg hlog _
  simpa using hpow

end Exploding
