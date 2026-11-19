import LatticeProb.Graph.Zd
import Exploding.Support.ArxivBondCubeBoundary
import Exploding.Support.ArxivFilledComplement
import Exploding.Support.ExtMHProof11

/-!
# Good connected interfaces around bad clusters

For a finite bad star-cluster, the interface between any component of the
complement of its cube enlargement and the filled complement is a
star-connected set of good sites.
-/

open LatticeProb Relation

namespace Exploding

/-- Each complement component of the enlargement of a finite star-connected
set closed under bad star-steps has a star-connected interface of good sites. -/
theorem enlarged_bad_star_closed_set_interface {d : ℕ} (hd : 1 ≤ d)
    {ω : Site d × Fin d → Bool} {a x : Site d} {F : Finset (Site d)}
    (ha : a ∈ F) (hF : xmh_SConn (F : Set (Site d)))
    (hclosed : ∀ c ∈ F, ∀ z, ¬ xap_Good ω z → xmh_star c z → z ∈ F) :
    let U : Set (Site d) := unitCubeEnlargement F
    let H := componentIn Uᶜ x
    let I : Set (Site d) := {z | z ∉ H ∧ ∃ w ∈ H, (lattice d).Adj w z}
    xmh_SConn I ∧ ∀ z ∈ I, z ∈ innerBoundary U ∧ xap_Good ω z := by
  classical
  let _ : NeZero d := ⟨by omega⟩
  let U : Set (Site d) := unitCubeEnlargement F
  let H := componentIn Uᶜ x
  let I : Set (Site d) := {z | z ∉ H ∧ ∃ w ∈ H, (lattice d).Adj w z}
  change xmh_SConn I ∧ ∀ z ∈ I, z ∈ innerBoundary U ∧ xap_Good ω z
  have hUconn : ∀ u ∈ U, ∀ v ∈ U,
      ReflTransGen (fun p q => p ∈ U ∧ q ∈ U ∧ (lattice d).Adj p q) u v :=
    unit_cube_enlargement_connected hF
  have haU : a ∈ U := subset_unit_cube_enlargement _ ha
  have hHU : ∀ z, z ∈ U → z ∉ H := fun z hzU hzH => hzH.2.1 hzU
  have hHclose : ∀ u ∈ H, ∀ v, (lattice d).Adj u v → v ∉ U → v ∈ H := by
    intro u hu v huv hv
    exact xmh7_componentIn_close hu hv huv
  have hHconn : ∀ u ∈ H, ∀ v ∈ H,
      ReflTransGen (fun p q => p ∈ H ∧ q ∈ H ∧ (lattice d).Adj p q) u v := by
    intro u hu v hv
    exact xmh7_componentIn_conn hu hv
  have hHcconn : ∀ u ∉ H, ∀ v ∉ H,
      ReflTransGen (fun p q => p ∉ H ∧ q ∉ H ∧ (lattice d).Adj p q) u v :=
    connected_complement_of_complement_component (lattice d) (Graph.Zd.latticeConnected d)
      haU hUconn hHU hHclose
  constructor
  · intro u hu v hv
    apply xmh3_boundaryStar d H Hᶜ hHconn hHcconn (fun z hz hz' => hz' hz)
      (fun _ _ _ _ hz => hz) u v hu hv
  · intro z hz
    obtain ⟨hzH, w, hwH, hwz⟩ := hz
    have hzU : z ∈ U := by
      by_contra hzU
      exact hzH (hHclose w hwH z hwz hzU)
    have hzbdry : z ∈ innerBoundary U := ⟨hzU, w, hwH.2.1, hwz.symm⟩
    exact ⟨hzbdry, good_of_mem_inner_boundary_unit_cube_enlargement hclosed hzbdry⟩

/-- Each complement component of an enlarged finite bad cluster has a
star-connected interface of good sites inside the enlargement. -/
theorem enlarged_bad_star_cluster_interface {d : ℕ} (hd : 1 ≤ d)
    {ω : Site d × Fin d → Bool} {a x : Site d}
    (ha : ¬ xap_Good ω a) (hfin : (badStarCluster ω a).Finite) :
    let U : Set (Site d) := unitCubeEnlargement hfin.toFinset
    let H := componentIn Uᶜ x
    let I : Set (Site d) := {z | z ∉ H ∧ ∃ w ∈ H, (lattice d).Adj w z}
    xmh_SConn I ∧ ∀ z ∈ I, z ∈ innerBoundary U ∧ xap_Good ω z := by
  apply enlarged_bad_star_closed_set_interface hd
    (hfin.mem_toFinset.mpr (mem_bad_star_cluster_self ha))
  · rw [Set.Finite.coe_toFinset]
    exact bad_star_cluster_connected
  · intro c hc z hz hcz
    exact hfin.mem_toFinset.mpr (mem_bad_star_cluster_of_star
      (hfin.mem_toFinset.mp hc) hz hcz)

end Exploding
