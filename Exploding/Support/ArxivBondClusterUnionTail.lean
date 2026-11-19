import Exploding.Support.ArxivBondAnimalThreshold
import Exploding.Support.ArxivStarConnectedUnion

/-!
# A geometric tail for unions of bad cube clusters

A union of bad star-connected sets meeting a fixed star-connected finite set
is itself star-connected after adjoining that set. The high-density
connected-set estimate therefore controls its size uniformly over all such
families, including infinite ones.
-/

open LatticeProb MeasureTheory

namespace Exploding

/-- At high bond density, the union of a finite star-connected set and any
family of bad star-connected sets meeting it has a geometric size tail. -/
theorem bond_bad_cluster_union_geometric_at_high_density (d : ℕ) :
    ∃ q0 : ℝ, 0 ≤ q0 ∧ q0 < 1 ∧ ∀ q : ℝ, q0 ≤ q → q ≤ 1 →
      ∀ (p : Site d) (P : Finset (Site d)), p ∈ P → xmh_SConn (P : Set (Site d)) →
        ∀ t : ℕ, 1 ≤ t → P.card ≤ 3 ^ d * t →
        bondPercolation d q
          {ω | ∃ G : Set (Set (Site d)),
            (∀ A ∈ G, xmh_SConn A ∧ (∃ z ∈ P, z ∈ A) ∧
              ∀ z ∈ A, ¬ xap_Good ω z) ∧
            ((2 * 3 ^ d * t : ℕ) : ℕ∞) ≤ ((P : Set (Site d)) ∪ ⋃ A ∈ G, A).encard} ≤
          (1 / 2 : ENNReal) ^ t := by
  obtain ⟨q0, hq0, hq01, htail⟩ := bond_connected_bad_cubes_geometric_at_high_density d
  refine ⟨q0, hq0, hq01, fun q hq hq1 p P hp hP t ht hPcard => ?_⟩
  refine (measure_mono ?_).trans (htail q hq hq1 p P t ht hPcard)
  rintro ω ⟨G, hG, hsize⟩
  let C : {A : Set (Site d) // A ∈ G} → Set (Site d) := fun A => A.1
  have hCe : (⋃ i, C i) = ⋃ A ∈ G, A := by
    ext x
    simp only [Set.mem_iUnion, C]
    constructor
    · rintro ⟨⟨A, hA⟩, hx⟩
      exact ⟨A, hA, hx⟩
    · rintro ⟨A, hA, hx⟩
      exact ⟨⟨A, hA⟩, hx⟩
  have hconn : xmh_SConn ((P : Set (Site d)) ∪ ⋃ A ∈ G, A) := by
    have h := star_connected_union_iUnion (P : Set (Site d)) C hP
      (fun i => (hG i.1 i.2).1) (fun i => (hG i.1 i.2).2.1)
    simpa only [hCe] using h
  refine ⟨(P : Set (Site d)) ∪ ⋃ A ∈ G, A, hconn, ?_, hsize, ?_⟩
  · exact Set.mem_union_left _ hp
  · intro x hx hxP
    rcases hx with hx | hx
    · exact (hxP hx).elim
    · obtain ⟨A, hA⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hAG, hxA⟩ := Set.mem_iUnion.mp hA
      exact (hG A hAG).2.2 x hxA

end Exploding
