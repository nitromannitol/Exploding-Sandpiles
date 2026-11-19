import Exploding.Support.ArxivBondCubeConnected
import Exploding.Support.ArxivBadStarCluster

/-!
# Good boundaries of enlarged bad clusters

The inner boundary of the unit-cube enlargement of a bad star-cluster
consists of good sites.
-/

open LatticeProb

namespace Exploding

variable {d : ℕ}

/-- If every bad star-neighbor of a finite set belongs to it, the inner
boundary of its unit-cube enlargement consists of good sites. -/
theorem good_of_mem_inner_boundary_unit_cube_enlargement
    {ω : Site d × Fin d → Bool} {F : Finset (Site d)}
    (hclosed : ∀ c ∈ F, ∀ z, ¬ xap_Good ω z → xmh_star c z → z ∈ F)
    {z : Site d} (hz : z ∈ innerBoundary (unitCubeEnlargement F : Set (Site d))) :
    xap_Good ω z := by
  classical
  obtain ⟨hz, w, hw, hzw⟩ := hz
  by_contra hzbad
  obtain ⟨c, hc, hzc⟩ := Finset.mem_biUnion.mp hz
  have hzc' : z ∈ xap_cube c := (xap_mem_cubeFinset c z).1 hzc
  have hzF : z ∈ F := by
    by_cases h : c = z
    · simpa only [h] using hc
    · apply hclosed c hc z hzbad
      refine ⟨h, fun i => ?_⟩
      rw [abs_sub_comm]
      exact hzc' i
  apply hw
  exact Finset.mem_biUnion.mpr ⟨z, hzF, (xap_mem_cubeFinset z w).2
    (xap_lattice_mem_cube hzw)⟩

/-- The enlarged finite bad cluster has a good inner boundary. -/
theorem good_of_mem_inner_boundary_enlarged_bad_star_cluster
    {ω : Site d × Fin d → Bool} {a : Site d}
    (hfin : (badStarCluster ω a).Finite) {z : Site d}
    (hz : z ∈ innerBoundary (unitCubeEnlargement hfin.toFinset : Set (Site d))) :
    xap_Good ω z := by
  apply good_of_mem_inner_boundary_unit_cube_enlargement (F := hfin.toFinset) ?_ hz
  intro c hc v hv hcv
  apply hfin.mem_toFinset.mpr
  exact mem_bad_star_cluster_of_star (hfin.mem_toFinset.mp hc) hv hcv

end Exploding
