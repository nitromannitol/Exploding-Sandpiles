/-
The next step toward the supercritical-density reduction: bounds on the critical
density and the existence of an infinite open cluster for every density above it.

`bondCritical d` is the supremum of the densities at which the percolation
probability vanishes, so it lies in `[0, 1]`; consequently for every `q` with
`bondCritical d < q ≤ 1` the percolation probability of bond percolation is
positive (`xap14_theta_pos_of_gt_bondCritical`).  This is the ingredient every
renormalisation argument needs; the box-crossing half (crossing probabilities
tend to one above `bondCritical d`) and the block argument remain open, as
recorded in `xap12_SupercriticalReduction` and the report.

The file also records that the frozen event forces connectivity, so that the
chemical-distance tail is supported on the open cluster of the origin.
-/
import Exploding.Support.ExtAPProof13
import Exploding.Support.RNProofCore
import Exploding.Support.RNProofPeierls

open Exploding LatticeProb MeasureTheory Filter
open scoped Classical Topology

namespace Exploding

variable {d : ℕ}

/-! ### The critical density lies in `[0, 1]` -/

/-- `bondCritical d = sSup {q ∈ [0,1] : bondTheta d q = 0}` is nonnegative. -/
theorem xap14_bondCritical_nonneg (d : ℕ) : 0 ≤ bondCritical d := by
  rw [bondCritical]
  rcases Set.eq_empty_or_nonempty {q : ℝ | 0 ≤ q ∧ q ≤ 1 ∧ bondTheta d q = 0} with h | h
  · rw [h, Real.sSup_empty]
  · obtain ⟨x, hx⟩ := h
    exact le_trans hx.1 (le_csSup ⟨1, fun y hy => hy.2.1⟩ hx)

/-- `bondCritical d ≤ 1`: every density in the defining set is at most one. -/
theorem xap14_bondCritical_le_one (d : ℕ) : bondCritical d ≤ 1 := by
  rw [bondCritical]
  by_cases h : ({q : ℝ | 0 ≤ q ∧ q ≤ 1 ∧ bondTheta d q = 0}).Nonempty
  · exact csSup_le h fun _y hy => hy.2.1
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sSup_empty]; norm_num

/-! ### An infinite open cluster above the critical density -/

/-- Above `bondCritical d` the percolation probability is nonzero: otherwise the
density would belong to the defining set of the supremum and be at most it. -/
theorem xap14_theta_pos_of_gt_bondCritical {q : ℝ} (h : bondCritical d < q) (hq1 : q ≤ 1) :
    bondTheta d q ≠ 0 := by
  intro hzero
  have hq0 : 0 ≤ q := le_trans (xap14_bondCritical_nonneg d) h.le
  have hbdd : BddAbove {q : ℝ | 0 ≤ q ∧ q ≤ 1 ∧ bondTheta d q = 0} :=
    ⟨1, fun y hy => hy.2.1⟩
  have hmem : q ∈ {q : ℝ | 0 ≤ q ∧ q ≤ 1 ∧ bondTheta d q = 0} := ⟨hq0, hq1, hzero⟩
  have := le_csSup hbdd hmem
  rw [bondCritical] at h
  linarith

/-- Consequently, for `bondCritical d < q ≤ 1` there is an infinite open cluster
with positive probability. -/
theorem xap14_infiniteCluster_pos {q : ℝ} (h : bondCritical d < q) (hq1 : q ≤ 1) :
    bondPercolation d q
        {ω | {x : Site d | (openBondGraph ω).Reachable 0 x}.Infinite} ≠ 0 :=
  xap14_theta_pos_of_gt_bondCritical h hq1

/-! ### The frozen event forces connectivity -/

/-- A finite chemical distance from the origin to `y` makes `y` reachable. -/
theorem xap14_bigDistance_reachable {ρ : ℝ} {ω : Site d × Fin d → Bool} {y : Site d}
    (h : xap12_BigDistance d ρ ω y) : (openBondGraph ω).Reachable (0 : Site d) y := by
  obtain ⟨m, hm, _⟩ := h
  have hne : (openBondGraph ω).edist (0 : Site d) y ≠ ⊤ := by
    rw [hm]; exact ENat.coe_ne_top m
  exact SimpleGraph.edist_ne_top_iff_reachable.mp hne

/-! ### Good connectivity implies open connectivity -/

/-- A good star-walk realises an open path, so every site in the good cluster of
the origin lies in its open cluster. -/
theorem xap14_goodConnected_reachable {ω : Site d × Fin d → Bool} {y : Site d}
    (h : xap3_GoodConnected ω y) : (openBondGraph ω).Reachable (0 : Site d) y := by
  obtain ⟨p, hp⟩ := h
  have hle := xap2_edist_le_of_goodWalk p hp (xap_mem_cube_self (0 : Site d))
    (xap_mem_cube_self y)
  have hcast : ((2 * d : ℕ) : ℕ∞) * ((p.length : ℕ∞) + 2)
      = ((2 * d * (p.length + 2) : ℕ) : ℕ∞) := by push_cast; ring
  rw [hcast] at hle
  exact SimpleGraph.edist_ne_top_iff_reachable.mp
    (ne_of_lt (lt_of_le_of_lt hle (ENat.coe_lt_top _)))

/-- The good cluster of the origin is contained in its open cluster. -/
theorem xap14_goodCluster_subset_openCluster {ω : Site d × Fin d → Bool} :
    {z : Site d | xap3_GoodConnected ω z} ⊆ {z : Site d | (openBondGraph ω).Reachable 0 z} :=
  fun _ hz => xap14_goodConnected_reachable hz

/-- The probability that the good cluster of the origin is infinite is at most the
percolation probability: the good cluster sits inside the open cluster. -/
theorem xap14_goodCluster_prob_le_theta (q : ℝ) :
    bondPercolation d q {ω | {z : Site d | xap3_GoodConnected ω z}.Infinite} ≤ bondTheta d q := by
  rw [bondTheta]
  exact measure_mono fun ω hω => hω.mono xap14_goodCluster_subset_openCluster

end Exploding
