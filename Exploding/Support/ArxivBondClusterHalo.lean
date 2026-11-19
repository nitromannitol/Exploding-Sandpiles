import Exploding.Support.ArxivBondConfinedSurgery
import Exploding.Support.ArxivBondCanonicalClusterTail

/-!
# Bad-cluster halo of a reference set

Adjoining the bad star-clusters meeting the unit-cube enlargement of a
star-connected reference set produces a star-connected set closed under bad
star-steps, with all good sites in the reference set.
-/

open LatticeProb Relation

namespace Exploding

variable {d : ℕ}

/-- A reference set and all bad star-clusters meeting its unit-cube enlargement. -/
def bondBadClusterHalo (ω : Site d × Fin d → Bool) (P : Finset (Site d)) : Set (Site d) :=
  (P : Set (Site d)) ∪ ⋃ z ∈ unitCubeEnlargement P, badStarCluster ω z

/-- The halo contains the reference set. -/
theorem subset_bond_bad_cluster_halo (ω : Site d × Fin d → Bool) (P : Finset (Site d)) :
    (P : Set (Site d)) ⊆ bondBadClusterHalo ω P :=
  Set.subset_union_left

/-- Every halo site outside the reference set is bad. -/
theorem bad_of_mem_bond_bad_cluster_halo {ω : Site d × Fin d → Bool} {P : Finset (Site d)}
    {z : Site d} (hz : z ∈ bondBadClusterHalo ω P) (hzP : z ∉ P) : ¬ xap_Good ω z := by
  rcases hz with hz | hz
  · exact (hzP hz).elim
  · obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hz
    obtain ⟨_, hza⟩ := Set.mem_iUnion.mp ha
    exact hza.1

/-- The halo is closed under bad star-steps. -/
theorem mem_bond_bad_cluster_halo_of_star {ω : Site d × Fin d → Bool} {P : Finset (Site d)}
    {u v : Site d} (hu : u ∈ bondBadClusterHalo ω P) (hv : ¬ xap_Good ω v)
    (huv : xmh_star u v) : v ∈ bondBadClusterHalo ω P := by
  by_cases huP : u ∈ P
  · have hvE : v ∈ unitCubeEnlargement P := mem_unit_cube_enlargement_of_star huP huv
    exact Or.inr (Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr
      ⟨hvE, mem_bad_star_cluster_self hv⟩⟩)
  · rcases hu with hu | hu
    · exact (huP hu).elim
    · obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hu
      obtain ⟨haE, hua⟩ := Set.mem_iUnion.mp ha
      exact Or.inr (Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr
        ⟨haE, mem_bad_star_cluster_of_star hua hv huv⟩⟩)

/-- The bad-cluster halo of a star-connected reference set is star-connected. -/
theorem bond_bad_cluster_halo_star_connected {ω : Site d × Fin d → Bool} {P : Finset (Site d)}
    (hP : xmh_SConn (P : Set (Site d))) : xmh_SConn (bondBadClusterHalo ω P) := by
  classical
  let H := bondBadClusterHalo ω P
  let R : Site d → Site d → Prop := fun u v => u ∈ H ∧ v ∈ H ∧ xmh_star u v
  have hPlift : ∀ u ∈ P, ∀ v ∈ P, ReflTransGen R u v := by
    intro u hu v hv
    exact ReflTransGen.mono (fun a b hab =>
      ⟨subset_bond_bad_cluster_halo ω P hab.1,
        subset_bond_bad_cluster_halo ω P hab.2.1, hab.2.2⟩) u v (hP u hu v hv)
  have hanchor : ∀ u ∈ H, ∃ p ∈ P, ReflTransGen R p u := by
    intro u hu
    rcases hu with huP | huC
    · exact ⟨u, huP, ReflTransGen.refl⟩
    · obtain ⟨z, hz⟩ := Set.mem_iUnion.mp huC
      obtain ⟨hzE, huz⟩ := Set.mem_iUnion.mp hz
      have hzbad : ¬ xap_Good ω z := by
        rcases huz.2.cases_head with hzu | ⟨v, hzv, _⟩
        · rw [hzu]
          exact huz.1
        · exact hzv.1
      have hzz : z ∈ badStarCluster ω z := mem_bad_star_cluster_self hzbad
      have hzH : z ∈ H := Or.inr (Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hzE, hzz⟩⟩)
      obtain ⟨p, hpP, hzp⟩ := Finset.mem_biUnion.mp hzE
      have hzp' : z ∈ xap_cube p := (xap_mem_cubeFinset p z).1 hzp
      have hpz : ReflTransGen R p z := by
        by_cases hpz : p = z
        · rw [hpz]
        · apply ReflTransGen.single
          refine ⟨subset_bond_bad_cluster_halo ω P hpP, hzH, hpz, fun i => ?_⟩
          rw [abs_sub_comm]
          exact hzp' i
      have hzupath : ReflTransGen R z u := by
        apply ReflTransGen.mono (fun a b hab => ?_) z u (bad_star_cluster_connected z hzz u huz)
        exact ⟨Or.inr (Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hzE, hab.1⟩⟩),
          Or.inr (Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hzE, hab.2.1⟩⟩), hab.2.2⟩
      exact ⟨p, hpP, hpz.trans hzupath⟩
  intro u hu v hv
  obtain ⟨p, hp, hpu⟩ := hanchor u hu
  obtain ⟨q, hq, hqv⟩ := hanchor v hv
  exact (xmh_rtg_symm (fun _ _ h => ⟨h.2.1, h.1, xmh_star_symm h.2.2⟩) hpu).trans
    ((hPlift p hp q hq).trans hqv)

end Exploding
