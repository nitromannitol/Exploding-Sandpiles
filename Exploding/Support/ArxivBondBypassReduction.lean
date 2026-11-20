import Exploding.Support.ArxivBondHighDensityAssembly
import Exploding.Support.ArxivBondEnlargementDistance

/-!
# The confined-walk reduction for the cluster bypass

A walk confined to the double enlargement of the finite union of bad clusters
implies the corresponding distance bound by loop erasure.
-/

open LatticeProb

namespace Exploding

/-- An alternative geometric confined-walk condition for a connected reference set and its
finite bad-cluster enlargement. This condition is not used in the proof of
`xap12_high_density_bound`. -/
def bondClusterConfinedWalk : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (ω : Site d × Fin d → Bool) (x y : Site d)
    (P F : Finset (Site d)), x ∈ P → y ∈ P → xmh_SConn (P : Set (Site d)) →
      ((lattice d).induce (P : Set (Site d))).Connected →
      (F : Set (Site d)) = bondBadClusterEnlargement ω P →
      (openBondGraph ω).Reachable x y →
        ∃ p : (openBondGraph ω).Walk x y,
          ∀ z ∈ p.support, z ∈ unitCubeEnlargement (unitCubeEnlargement F)

/-- The confined-walk property implies the bad-cluster distance bound. -/
theorem bond_cluster_bypass_bound_of_confined_walk (hwalk : bondClusterConfinedWalk) :
    bondClusterBypassBound := by
  intro d hd ω x y P hx hy hstar hconn hreach
  classical
  by_cases hfin : (bondBadClusterEnlargement ω P).Finite
  · obtain ⟨p, hp⟩ := hwalk d hd ω x y P hfin.toFinset hx hy hstar hconn
      (Set.Finite.coe_toFinset hfin) hreach
    have hdist := open_bond_edist_lt_double_enlargement_bound hfin.toFinset p hp
    apply le_of_lt
    simpa only [hfin.encard_eq_coe_toFinset_card, Nat.cast_mul] using hdist
  · have henc : (bondBadClusterEnlargement ω P).encard = ⊤ := Set.Infinite.encard_eq hfin
    rw [henc, ENat.top_mul]
    · exact le_top
    · exact_mod_cast (pow_ne_zero 2 (pow_ne_zero d (by decide : 3 ≠ 0)))

end Exploding
