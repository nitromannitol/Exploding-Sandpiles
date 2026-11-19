import Exploding.Support.ExtMHBase
import Exploding.Support.ExtAPDefs

/-!
# Bad star-clusters

Bad sites connected by star steps form a star-connected cluster. Every
star-neighbor outside such a cluster is good.
-/

open LatticeProb Relation

namespace Exploding

variable {d : ℕ}

/-- The bad star-cluster rooted at a site. -/
def badStarCluster (ω : Site d × Fin d → Bool) (a : Site d) : Set (Site d) :=
  {z | ¬ xap_Good ω z ∧ ReflTransGen
    (fun u v => ¬ xap_Good ω u ∧ ¬ xap_Good ω v ∧ xmh_star u v) a z}

/-- A bad site belongs to its own bad star-cluster. -/
theorem mem_bad_star_cluster_self {ω : Site d × Fin d → Bool} {a : Site d}
    (ha : ¬ xap_Good ω a) : a ∈ badStarCluster ω a :=
  ⟨ha, ReflTransGen.refl⟩

/-- A bad star-cluster is closed under star steps to bad sites. -/
theorem mem_bad_star_cluster_of_star {ω : Site d × Fin d → Bool} {a u v : Site d}
    (hu : u ∈ badStarCluster ω a) (hv : ¬ xap_Good ω v) (huv : xmh_star u v) :
    v ∈ badStarCluster ω a :=
  ⟨hv, hu.2.tail ⟨hu.1, hv, huv⟩⟩

/-- Every star-neighbor outside a bad star-cluster is good. -/
theorem good_of_star_neighbor_outside_bad_cluster {ω : Site d × Fin d → Bool}
    {a u v : Site d} (hu : u ∈ badStarCluster ω a) (huv : xmh_star u v)
    (hv : v ∉ badStarCluster ω a) : xap_Good ω v := by
  by_contra hbad
  exact hv (mem_bad_star_cluster_of_star hu hbad huv)

/-- A bad star-cluster is star-connected. -/
theorem bad_star_cluster_connected {ω : Site d × Fin d → Bool} {a : Site d} :
    xmh_SConn (badStarCluster ω a) := by
  let C := badStarCluster ω a
  let R' : Site d → Site d → Prop := fun u v => u ∈ C ∧ v ∈ C ∧ xmh_star u v
  have hpath : ∀ z, z ∈ C → ReflTransGen R' a z := by
    intro z hz
    have h := hz.2
    induction h with
    | refl => exact ReflTransGen.refl
    | @tail u v hprev huv ih =>
      have hu : u ∈ C := by
        exact ⟨huv.1, hprev⟩
      have hv : v ∈ C := by
        exact ⟨huv.2.1, hprev.tail huv⟩
      exact (ih hu).tail ⟨hu, hv, huv.2.2⟩
  intro u hu v hv
  exact (xmh_rtg_symm (fun _ _ h => ⟨h.2.1, h.1, xmh_star_symm h.2.2⟩)
    (hpath u hu)).trans (hpath v hv)

end Exploding
