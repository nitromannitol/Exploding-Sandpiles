import Exploding.Support.RNProofPercolation
import Exploding.Support.RNProofPeierls
import Exploding.External.LSSBoundedDegreeProved
import Exploding.Support.ExtMHHoleVolume

/-!
# Actual bond clusters with finite holes

Existence of an infinite actual bond cluster with the proved hole-volume bound at high density.
The root is allowed to depend on the configuration, and the cluster is the actual reachability
set in the open-bond graph.
-/


namespace Exploding

open LatticeProb

/-- At all sufficiently high bond densities, almost every configuration has an infinite actual
open-bond cluster satisfying `RnHoleProp`. -/
theorem arxiv_actual_bond_cluster_holes_ae (d : ℕ) (hd : 2 ≤ d) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ q : ℝ, r ≤ q → q ≤ 1 →
      ∀ᵐ ζ ∂(bondPercolation d q), ∃ i : Site d,
        {y : Site d | (openBondGraph ζ).Reachable i y}.Infinite ∧
        RnHoleProp d {y : Site d | (openBondGraph ζ).Reachable i y} := by
  have hθ : bondTheta d (255 / 256 : ℝ) ≠ 0 := by
    apply pe_theta_ne_zero hd
    · norm_num
    · norm_num
  obtain ⟨r, hr1, hr⟩ :=
    rn_siteField_ae lssBoundedDegree xmf_proved d hd (255 / 256 : ℝ)
      (by norm_num) (by norm_num) hθ
  refine ⟨max r 0, le_max_right _ _, max_lt hr1 zero_lt_one, ?_⟩
  intro q hq hq1
  have hrq : r ≤ q := (le_max_left _ _).trans hq
  rw [MeasureTheory.ae_iff]
  exact hr q hrq hq1

end Exploding
