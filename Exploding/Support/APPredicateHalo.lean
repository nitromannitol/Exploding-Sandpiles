/-
Bad clusters and halos for an arbitrary predicate on sites.

For a predicate `G` on `ℤ^d` (the good sites), the bad star-cluster of a bad site, the halo of a
finite reference set (the set together with every bad star-cluster meeting its unit-cube
enlargement), and the interfaces between the complement components of the enlargement of a
finite set closed under bad star-steps.  These are the statements of
`Exploding.Support.ArxivBadStarCluster`, `Exploding.Support.ArxivBondClusterHalo` and
`Exploding.Support.ArxivBondClusterBoundary` with the good-cube predicate replaced by `G`; the
proofs are the same.
-/
import Exploding.Support.ArxivBondClusterBoundary

open LatticeProb Relation

namespace Exploding

variable {d : ℕ}

/-! ### Bad star-clusters of a predicate -/

/-- The star-cluster of sites failing `G` that contains `a`. -/
def predBadCluster (G : Site d → Prop) (a : Site d) : Set (Site d) :=
  {z | ¬ G z ∧ ReflTransGen (fun u v => ¬ G u ∧ ¬ G v ∧ xmh_star u v) a z}

theorem mem_predBadCluster_self {G : Site d → Prop} {a : Site d} (ha : ¬ G a) :
    a ∈ predBadCluster G a :=
  ⟨ha, ReflTransGen.refl⟩

theorem mem_predBadCluster_of_star {G : Site d → Prop} {a u v : Site d}
    (hu : u ∈ predBadCluster G a) (hv : ¬ G v) (huv : xmh_star u v) :
    v ∈ predBadCluster G a :=
  ⟨hv, hu.2.tail ⟨hu.1, hv, huv⟩⟩

theorem not_of_mem_predBadCluster {G : Site d → Prop} {a z : Site d}
    (hz : z ∈ predBadCluster G a) : ¬ G a := by
  rcases hz.2.cases_head with hza | ⟨v, hav, _⟩
  · rw [hza]
    exact hz.1
  · exact hav.1

theorem predBadCluster_connected {G : Site d → Prop} {a : Site d} :
    xmh_SConn (predBadCluster G a) := by
  let C := predBadCluster G a
  let R' : Site d → Site d → Prop := fun u v => u ∈ C ∧ v ∈ C ∧ xmh_star u v
  have hpath : ∀ z, z ∈ C → ReflTransGen R' a z := by
    intro z hz
    have h := hz.2
    induction h with
    | refl => exact ReflTransGen.refl
    | @tail u v hprev huv ih =>
      have hu : u ∈ C := ⟨huv.1, hprev⟩
      have hv : v ∈ C := ⟨huv.2.1, hprev.tail huv⟩
      exact (ih hu).tail ⟨hu, hv, huv.2.2⟩
  intro u hu v hv
  exact (xmh_rtg_symm (fun _ _ h => ⟨h.2.1, h.1, xmh_star_symm h.2.2⟩)
    (hpath u hu)).trans (hpath v hv)

/-! ### The halo of a reference set -/

/-- A reference set and all bad star-clusters of `G` meeting its unit-cube enlargement. -/
def predHalo (G : Site d → Prop) (P : Finset (Site d)) : Set (Site d) :=
  (P : Set (Site d)) ∪ ⋃ z ∈ unitCubeEnlargement P, predBadCluster G z

theorem subset_predHalo (G : Site d → Prop) (P : Finset (Site d)) :
    (P : Set (Site d)) ⊆ predHalo G P :=
  Set.subset_union_left

theorem not_of_mem_predHalo {G : Site d → Prop} {P : Finset (Site d)} {z : Site d}
    (hz : z ∈ predHalo G P) (hzP : z ∉ P) : ¬ G z := by
  rcases hz with hz | hz
  · exact (hzP hz).elim
  · obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hz
    obtain ⟨_, hza⟩ := Set.mem_iUnion.mp ha
    exact hza.1

theorem mem_predHalo_of_star {G : Site d → Prop} {P : Finset (Site d)} {u v : Site d}
    (hu : u ∈ predHalo G P) (hv : ¬ G v) (huv : xmh_star u v) : v ∈ predHalo G P := by
  by_cases huP : u ∈ P
  · have hvE : v ∈ unitCubeEnlargement P := mem_unit_cube_enlargement_of_star huP huv
    exact Or.inr (Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr
      ⟨hvE, mem_predBadCluster_self hv⟩⟩)
  · rcases hu with hu | hu
    · exact (huP hu).elim
    · obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hu
      obtain ⟨haE, hua⟩ := Set.mem_iUnion.mp ha
      exact Or.inr (Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr
        ⟨haE, mem_predBadCluster_of_star hua hv huv⟩⟩)

theorem predHalo_star_connected {G : Site d → Prop} {P : Finset (Site d)}
    (hP : xmh_SConn (P : Set (Site d))) : xmh_SConn (predHalo G P) := by
  classical
  let H := predHalo G P
  let R : Site d → Site d → Prop := fun u v => u ∈ H ∧ v ∈ H ∧ xmh_star u v
  have hPlift : ∀ u ∈ P, ∀ v ∈ P, ReflTransGen R u v := by
    intro u hu v hv
    exact ReflTransGen.mono (fun a b hab =>
      ⟨subset_predHalo G P hab.1, subset_predHalo G P hab.2.1, hab.2.2⟩) u v (hP u hu v hv)
  have hanchor : ∀ u ∈ H, ∃ p ∈ P, ReflTransGen R p u := by
    intro u hu
    rcases hu with huP | huC
    · exact ⟨u, huP, ReflTransGen.refl⟩
    · obtain ⟨z, hz⟩ := Set.mem_iUnion.mp huC
      obtain ⟨hzE, huz⟩ := Set.mem_iUnion.mp hz
      have hzbad : ¬ G z := not_of_mem_predBadCluster huz
      have hzz : z ∈ predBadCluster G z := mem_predBadCluster_self hzbad
      have hzH : z ∈ H := Or.inr (Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hzE, hzz⟩⟩)
      obtain ⟨p, hpP, hzp⟩ := Finset.mem_biUnion.mp hzE
      have hzp' : z ∈ xap_cube p := (xap_mem_cubeFinset p z).1 hzp
      have hpz : ReflTransGen R p z := by
        by_cases hpz : p = z
        · rw [hpz]
        · apply ReflTransGen.single
          refine ⟨subset_predHalo G P hpP, hzH, hpz, fun i => ?_⟩
          rw [abs_sub_comm]
          exact hzp' i
      have hzupath : ReflTransGen R z u := by
        apply ReflTransGen.mono (fun a b hab => ?_) z u (predBadCluster_connected z hzz u huz)
        exact ⟨Or.inr (Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hzE, hab.1⟩⟩),
          Or.inr (Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hzE, hab.2.1⟩⟩), hab.2.2⟩
      exact ⟨p, hpP, hpz.trans hzupath⟩
  intro u hu v hv
  obtain ⟨p, hp, hpu⟩ := hanchor u hu
  obtain ⟨q, hq, hqv⟩ := hanchor v hv
  exact (xmh_rtg_symm (fun _ _ h => ⟨h.2.1, h.1, xmh_star_symm h.2.2⟩) hpu).trans
    ((hPlift p hp q hq).trans hqv)

/-! ### Good interfaces -/

/-- If every bad star-neighbour of a finite set belongs to it, the inner boundary of its
unit-cube enlargement consists of good sites. -/
theorem pred_of_mem_innerBoundary_unitCubeEnlargement {G : Site d → Prop}
    {F : Finset (Site d)} (hclosed : ∀ c ∈ F, ∀ z, ¬ G z → xmh_star c z → z ∈ F)
    {z : Site d} (hz : z ∈ innerBoundary (unitCubeEnlargement F : Set (Site d))) : G z := by
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

/-- Each complement component of the unit-cube enlargement of a finite star-connected set
closed under bad star-steps has a star-connected interface of good sites in the inner boundary
of the enlargement. -/
theorem pred_enlarged_closed_set_interface {d : ℕ} (hd : 1 ≤ d) {G : Site d → Prop}
    {a x : Site d} {F : Finset (Site d)}
    (ha : a ∈ F) (hF : xmh_SConn (F : Set (Site d)))
    (hclosed : ∀ c ∈ F, ∀ z, ¬ G z → xmh_star c z → z ∈ F) :
    let U : Set (Site d) := unitCubeEnlargement F
    let H := componentIn Uᶜ x
    let I : Set (Site d) := {z | z ∉ H ∧ ∃ w ∈ H, (lattice d).Adj w z}
    xmh_SConn I ∧ ∀ z ∈ I, z ∈ innerBoundary U ∧ G z := by
  classical
  let _ : NeZero d := ⟨by omega⟩
  let U : Set (Site d) := unitCubeEnlargement F
  let H := componentIn Uᶜ x
  let I : Set (Site d) := {z | z ∉ H ∧ ∃ w ∈ H, (lattice d).Adj w z}
  change xmh_SConn I ∧ ∀ z ∈ I, z ∈ innerBoundary U ∧ G z
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
    exact ⟨hzbdry, pred_of_mem_innerBoundary_unitCubeEnlargement hclosed hzbdry⟩

end Exploding
