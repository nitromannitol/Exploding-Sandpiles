import Exploding.Support.ArxivBondDefectiveAnimals
import Exploding.Support.ExtMHProof8

/-!
# Near-root defective-animal probability

The probability of a finite defective star-animal with an anchor within coordinate distance
`m` of a fixed site is bounded by a union over the translated box of candidate anchors. The
rooted-animal estimate is used with its original constant and its natural-division exponent.
-/

open LatticeProb MeasureTheory

namespace Exploding

/-- A finite union over the translate of `xmh4_centFinset` bounds the near-root event using the
same rooted-animal constant. -/
theorem arxiv_bond_near_defective_animal_prob_le (d : ℕ) :
    ∃ K : ℕ, 1 ≤ K ∧
      ∀ (z : Site d) (m : ℕ) {q : ℝ}, 0 ≤ q → q ≤ 1 →
        bondPercolation d q
          {ζ | ∃ p : Site d,
            (∀ k : Fin d, |p k - z k| ≤ (m : ℤ)) ∧
            ∃ F : Finset (Site d), p ∈ F ∧ F.card = m ∧
              xmh_SConn (F : Set (Site d)) ∧
              ∀ x ∈ F, rn_siteField ζ x = false} ≤
        (((2 * m + 1) ^ d : ℕ) : ENNReal) *
          (K : ENNReal) ^ m *
          (ENNReal.ofReal (2 * (d : ℝ) * (1 - q))) ^ (m / 3 ^ d) := by
  classical
  obtain ⟨K, hK, hroot⟩ := arxiv_bond_defective_star_animal_prob_le d
  refine ⟨K, hK, ?_⟩
  intro z m q hq0 hq1
  let A : Finset (Site d) := (xmh4_centFinset d m).image (fun x => z + x)
  let E : Site d → Set (RnBond d → Bool) := fun p =>
    {ζ | ∃ F : Finset (Site d), p ∈ F ∧ F.card = m ∧
      xmh_SConn (F : Set (Site d)) ∧
      ∀ x ∈ F, rn_siteField ζ x = false}
  have hAcard : A.card = (2 * m + 1) ^ d := by
    dsimp only [A]
    rw [Finset.card_image_of_injective]
    · exact xmh4_centFinset_card d m
    · intro x y hxy
      exact add_left_cancel hxy
  have hsub :
      {ζ | ∃ p : Site d, (∀ k : Fin d, |p k - z k| ≤ (m : ℤ)) ∧ E p ζ} ⊆
        ⋃ p ∈ A, E p := by
    rintro ζ ⟨p, hnear, hanimal⟩
    have hbox : p - z ∈ xmh4_centFinset d m := by
      rw [xmh4_mem_centFinset]
      intro k
      simpa using hnear k
    have hpA : p ∈ A := by
      dsimp only [A]
      rw [Finset.mem_image]
      refine ⟨p - z, hbox, ?_⟩
      ext k
      simp
    exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hpA, hanimal⟩⟩
  calc
    bondPercolation d q
        {ζ | ∃ p : Site d, (∀ k : Fin d, |p k - z k| ≤ (m : ℤ)) ∧ E p ζ} ≤
        bondPercolation d q (⋃ p ∈ A, E p) := measure_mono hsub
    _ ≤ ∑ p ∈ A, bondPercolation d q (E p) := measure_biUnion_finset_le A _
    _ ≤ ∑ _p ∈ A,
          (K : ENNReal) ^ m *
            (ENNReal.ofReal (2 * (d : ℝ) * (1 - q))) ^ (m / 3 ^ d) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hroot p m hq0 hq1
    _ = (A.card : ENNReal) *
          ((K : ENNReal) ^ m *
            (ENNReal.ofReal (2 * (d : ℝ) * (1 - q))) ^ (m / 3 ^ d)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = (((2 * m + 1) ^ d : ℕ) : ENNReal) *
          (K : ENNReal) ^ m *
            (ENNReal.ofReal (2 * (d : ℝ) * (1 - q))) ^ (m / 3 ^ d) := by
      rw [hAcard, ← mul_assoc]

end Exploding
