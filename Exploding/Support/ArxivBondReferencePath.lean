import LatticeProb.Graph.Zd
import Exploding.Support.ArxivP1RenormGeometry
import Exploding.Support.ExtMHProof11
import Exploding.Support.ExtAPDefs

/-!
# Short connected reference sets

The support of a shortest lattice walk gives a finite star-connected set whose
size is controlled by the Manhattan distance between its endpoints.
-/

open LatticeProb Relation

namespace Exploding

/-- Two lattice sites belong to a finite star-connected set of at most one more
than their Manhattan distance. -/
theorem exists_short_star_connected_set {d : ℕ} (hd : 1 ≤ d) (x y : Site d) :
    ∃ P : Finset (Site d), x ∈ P ∧ y ∈ P ∧ xmh_SConn (P : Set (Site d)) ∧
      P.card ≤ (mnorm (x - y)).toNat + 1 := by
  classical
  let _ : NeZero d := ⟨by omega⟩
  obtain ⟨p, hp⟩ := (Graph.Zd.latticeConnected d).exists_walk_length_eq_edist x y
  let P := p.support.toFinset
  have hx : x ∈ P := List.mem_toFinset.mpr p.start_mem_support
  have hy : y ∈ P := List.mem_toFinset.mpr p.end_mem_support
  have hconn : ((lattice d).induce (P : Set (Site d))).Connected := by
    have hset : (P : Set (Site d)) = {v | v ∈ p.support} := by
      ext z
      simp only [P, Finset.mem_coe, List.mem_toFinset, Set.mem_ofPred_eq]
    rw [hset]
    exact p.connected_induce_support
  have hcomponent : ∀ z ∈ P, z ∈ componentIn (P : Set (Site d)) x := by
    intro z hz
    exact ⟨hx, hz, hconn ⟨x, hx⟩ ⟨z, hz⟩⟩
  refine ⟨P, hx, hy, ?_, ?_⟩
  · intro u hu v hv
    apply ReflTransGen.mono (fun a b hab => ?_) u v
      (xmh7_componentIn_conn (hcomponent u hu) (hcomponent v hv))
    refine ⟨hab.1.2.1, hab.2.1.2.1, hab.2.2.ne, fun i => ?_⟩
    rw [abs_sub_comm]
    exact xap_lattice_mem_cube hab.2.2 i
  · have hcard := List.toFinset_card_le p.support
    rw [SimpleGraph.Walk.length_support] at hcard
    have hlen : p.length = (mnorm (x - y)).toNat := by
      rw [lattice_edist_eq_mnorm] at hp
      exact_mod_cast hp
    simpa only [P, hlen] using hcard

end Exploding
