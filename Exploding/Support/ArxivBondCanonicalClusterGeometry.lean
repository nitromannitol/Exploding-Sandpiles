import Exploding.Support.ArxivBondCanonicalClusterTail

/-!
# Closure of the reference-set cluster enlargement

The union of the reference set and the bad clusters rooted there is closed
under bad star-steps from bad sites.
-/

open LatticeProb

namespace Exploding

variable {d : ℕ}

/-- A bad star-neighbor of a bad site in the cluster enlargement remains in
the enlargement. -/
theorem mem_bond_bad_cluster_enlargement_of_star
    {ω : Site d × Fin d → Bool} {P : Finset (Site d)} {u v : Site d}
    (hu : u ∈ bondBadClusterEnlargement ω P) (hubad : ¬ xap_Good ω u)
    (hvbad : ¬ xap_Good ω v) (huv : xmh_star u v) :
    v ∈ bondBadClusterEnlargement ω P := by
  rcases hu with hu | hu
  · exact Or.inr (Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr
      ⟨hu, mem_bad_star_cluster_of_star (mem_bad_star_cluster_self hubad) hvbad huv⟩⟩)
  · obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hu
    obtain ⟨hzP, huz⟩ := Set.mem_iUnion.mp hz
    exact Or.inr (Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr
      ⟨hzP, mem_bad_star_cluster_of_star huz hvbad huv⟩⟩)

/-- An exterior star-neighbor of a bad site in the cluster enlargement is good. -/
theorem good_of_star_neighbor_outside_bond_bad_cluster_enlargement
    {ω : Site d × Fin d → Bool} {P : Finset (Site d)} {u v : Site d}
    (hu : u ∈ bondBadClusterEnlargement ω P) (hubad : ¬ xap_Good ω u)
    (huv : xmh_star u v) (hv : v ∉ bondBadClusterEnlargement ω P) :
    xap_Good ω v := by
  by_contra hvbad
  exact hv (mem_bond_bad_cluster_enlargement_of_star hu hubad hvbad huv)

end Exploding
