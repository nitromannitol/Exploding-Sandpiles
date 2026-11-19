import Exploding.Support.ArxivBadStarCluster
import Exploding.Support.ArxivBondReferenceTail

/-!
# Bad clusters meeting a reference set

The union of the bad star-clusters rooted in a short reference set inherits
an exponential size bound at high bond density.
-/

open LatticeProb MeasureTheory

namespace Exploding

/-- A reference set together with the bad star-clusters rooted at its bad sites. -/
def bondBadClusterEnlargement {d : ℕ} (ω : Site d × Fin d → Bool)
    (P : Finset (Site d)) : Set (Site d) :=
  (P : Set (Site d)) ∪ ⋃ z ∈ P, badStarCluster ω z

/-- The canonical bad-cluster enlargement of a short reference set has a
geometric size tail at sufficiently high density. -/
theorem bond_bad_cluster_enlargement_tail (d : ℕ) (hd : 1 ≤ d) :
    ∃ q0 : ℝ, 0 ≤ q0 ∧ q0 < 1 ∧ ∀ (x y : Site d),
      ∃ P : Finset (Site d), x ∈ P ∧ y ∈ P ∧ xmh_SConn (P : Set (Site d)) ∧
        P.card ≤ (mnorm (x - y)).toNat + 1 ∧
        ∀ q : ℝ, q0 ≤ q → q ≤ 1 →
          bondPercolation d q
            {ω | ((2 * 3 ^ d * ((mnorm (x - y)).toNat + 1) : ℕ) : ℕ∞) ≤
              (bondBadClusterEnlargement ω P).encard} ≤
            (1 / 2 : ENNReal) ^ ((mnorm (x - y)).toNat + 1) := by
  obtain ⟨q0, hq0, hq1, htail⟩ := bond_bad_cluster_union_tail_along_reference d hd
  refine ⟨q0, hq0, hq1, fun x y => ?_⟩
  obtain ⟨P, hx, hy, hconn, hcard, hbound⟩ := htail x y
  refine ⟨P, hx, hy, hconn, hcard, fun q hq hq1 => ?_⟩
  refine (measure_mono ?_).trans (hbound q hq hq1)
  intro ω hsize
  let G : Set (Set (Site d)) :=
    {A | ∃ z ∈ P, ¬ xap_Good ω z ∧ A = badStarCluster ω z}
  have hG : ∀ A ∈ G, xmh_SConn A ∧ (∃ z ∈ P, z ∈ A) ∧
      ∀ z ∈ A, ¬ xap_Good ω z := by
    intro A hA
    obtain ⟨z, hz, hbad, rfl⟩ := hA
    exact ⟨bad_star_cluster_connected, ⟨z, hz, mem_bad_star_cluster_self hbad⟩,
      fun _ hw => hw.1⟩
  have hunion : (⋃ A ∈ G, A) = ⋃ z ∈ P, badStarCluster ω z := by
    ext u
    simp only [Set.mem_iUnion, G, Set.mem_setOf_eq]
    constructor
    · rintro ⟨A, ⟨z, hz, _, rfl⟩, hu⟩
      exact ⟨z, hz, hu⟩
    · rintro ⟨z, hz, hu⟩
      have hbad : ¬ xap_Good ω z := by
        rcases hu.2.cases_head with hzu | ⟨v, hzv, _⟩
        · rw [hzu]
          exact hu.1
        · exact hzv.1
      exact ⟨badStarCluster ω z, ⟨z, hz, hbad, rfl⟩, hu⟩
  refine ⟨G, hG, ?_⟩
  simpa only [Set.mem_setOf_eq, hunion, bondBadClusterEnlargement] using hsize

end Exploding
