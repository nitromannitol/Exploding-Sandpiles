import Exploding.Support.ArxivBondClusterBoundary

/-!
# Open paths along good interfaces

A star-connected set of good sites inside a finite region gives open paths
confined to the region's unit-cube enlargement.
-/

open LatticeProb Relation

namespace Exploding

variable {d : ℕ}

/-- Good star-connected sites in a finite set are connected by open paths
inside its unit-cube enlargement. -/
theorem open_reach_in_unit_cube_enlargement_of_good_star_connected
    {ω : Site d × Fin d → Bool} {F : Finset (Site d)} {S : Set (Site d)}
    (hS : xmh_SConn S) (hsub : S ⊆ F) (hgood : ∀ z ∈ S, xap_Good ω z)
    {a b : Site d} (ha : a ∈ S) (hb : b ∈ S) :
    xap_Reach ω (unitCubeEnlargement F : Set (Site d)) a b := by
  classical
  have hpath : ∀ z ∈ S, xap_Reach ω (unitCubeEnlargement F : Set (Site d)) a z := by
    intro z hz
    have hchain := hS a ha z hz
    induction hchain with
    | refl => exact xap_reach_refl (subset_unit_cube_enlargement F (hsub ha))
    | @tail u v _ hstep ih =>
      have hlocal : xap_Reach ω (xap_cube u) u v :=
        xap_cube_reach' (hgood u hstep.1) (xap_mem_cube_self u)
          (xap_star_mem_cube hstep.2.2)
      have hlocal' : xap_Reach ω (unitCubeEnlargement F : Set (Site d)) u v := by
        apply xap_reach_mono _ hlocal
        intro w hw
        exact Finset.mem_biUnion.mpr ⟨u, hsub hstep.1, (xap_mem_cubeFinset u w).2 hw⟩
      exact xap_reach_trans (ih hstep.1) hlocal'
  exact hpath b hb

end Exploding
