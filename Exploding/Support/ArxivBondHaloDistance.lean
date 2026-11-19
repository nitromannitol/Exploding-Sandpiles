import Exploding.Support.ArxivBondClusterHaloTail
import Exploding.Support.ArxivBondReachWalk
import Exploding.Support.ArxivBondEnlargementDistance

/-!
# Chemical distance controlled by the bad-cluster halo

The confined-walk construction and loop erasure bound chemical distance by
the size of the bad-cluster halo.
-/

open LatticeProb

namespace Exploding

/-- Connected endpoints in a star-connected reference set have chemical
distance bounded by a dimension-dependent multiple of the halo size. -/
theorem open_bond_edist_le_bad_cluster_halo {d : ℕ} (hd : 1 ≤ d)
    {ω : Site d × Fin d → Bool} {x y : Site d} {P : Finset (Site d)}
    (hx : x ∈ P) (hy : y ∈ P) (hP : xmh_SConn (P : Set (Site d)))
    (hxy : (openBondGraph ω).Reachable x y) :
    (openBondGraph ω).edist x y ≤ (bondBadClusterHalo ω P).encard * ((3 ^ d) ^ 2 : ℕ) := by
  classical
  by_cases hfin : (bondBadClusterHalo ω P).Finite
  · let F := hfin.toFinset
    have hxF : x ∈ F := hfin.mem_toFinset.mpr (subset_bond_bad_cluster_halo ω P hx)
    have hyF : y ∈ F := hfin.mem_toFinset.mpr (subset_bond_bad_cluster_halo ω P hy)
    have hF : xmh_SConn (F : Set (Site d)) := by
      simpa only [F, Set.Finite.coe_toFinset] using bond_bad_cluster_halo_star_connected hP
    have hclosed : ∀ c ∈ F, ∀ z, ¬ xap_Good ω z → xmh_star c z → z ∈ F := by
      intro c hc z hz hcz
      exact hfin.mem_toFinset.mpr (mem_bond_bad_cluster_halo_of_star
        (hfin.mem_toFinset.mp hc) hz hcz)
    have hreach := open_reach_in_double_cube_enlargement_of_bad_star_closed hd hxF hF hclosed
      (subset_unit_cube_enlargement F hyF) hxy
    obtain ⟨p, hp⟩ := open_walk_of_reach_in_set hreach
    have hdist := open_bond_edist_lt_double_enlargement_bound F p hp
    apply le_of_lt
    simpa only [F, hfin.encard_eq_coe_toFinset_card, Nat.cast_mul] using hdist
  · have henc : (bondBadClusterHalo ω P).encard = ⊤ := Set.Infinite.encard_eq hfin
    rw [henc, ENat.top_mul]
    · exact le_top
    · exact_mod_cast (pow_ne_zero 2 (pow_ne_zero d (by decide : 3 ≠ 0)))

end Exploding
