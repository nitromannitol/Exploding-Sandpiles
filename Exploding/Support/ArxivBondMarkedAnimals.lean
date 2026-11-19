import Exploding.Support.ExtAPProof6
import Exploding.Support.ExtMHCount

/-!
# Star-animals with marked bad cubes

A rooted star-animal with a specified number of bad cubes is controlled by
counting its possible shapes and its marked subsets, then applying the bad-cube
packing estimate to each marked set.
-/

open LatticeProb MeasureTheory ProbabilityTheory

namespace Exploding

/-- The probability of a rooted star-animal of size `m` containing `k` defective
sites is bounded by the number of shapes and marked subsets times the packing bound. -/
theorem arxiv_bond_marked_star_animal_prob_le (d : ℕ) :
    ∃ K : ℕ, ∀ (p : Site d) (m k : ℕ) {q : ℝ}, 0 ≤ q → q ≤ 1 →
      bondPercolation d q
        {ζ | ∃ F B : Finset (Site d), p ∈ F ∧ F.card = m ∧
          xmh_SConn (F : Set (Site d)) ∧ B ⊆ F ∧ B.card = k ∧
          ∀ x ∈ B, ¬ xap_Good ζ x} ≤
        ((K : ENNReal) ^ m * (2 : ENNReal) ^ m) *
          (1 - xap6_delta d q) ^ (k / 3 ^ d) := by
  classical
  obtain ⟨K, hcount⟩ := xmh_starCount d
  refine ⟨K, ?_⟩
  intro p m k q hq0 hq1
  obtain ⟨T, hTcard, hTmem⟩ := hcount p m
  let T' : Finset (Finset (Site d)) := T.filter (fun F => F.card = m)
  let b : ENNReal := 1 - xap6_delta d q
  let marked : Finset (Site d) → Finset (Finset (Site d)) :=
    fun F => F.powerset.filter (fun B => B.card = k)
  have hsub :
      {ζ | ∃ F B : Finset (Site d), p ∈ F ∧ F.card = m ∧
        xmh_SConn (F : Set (Site d)) ∧ B ⊆ F ∧ B.card = k ∧
        ∀ x ∈ B, ¬ xap_Good ζ x} ⊆
        ⋃ F ∈ T', ⋃ B ∈ marked F, {ζ | ∀ x ∈ B, ¬ xap_Good ζ x} := by
    rintro ζ ⟨F, B, hp, hcard, hconn, hBF, hBcard, hdef⟩
    refine Set.mem_iUnion.mpr ⟨F, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨hTmem F hp hcard hconn, hcard⟩
    · refine Set.mem_iUnion.mpr ⟨B, Set.mem_iUnion.mpr ⟨?_, hdef⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hBF, hBcard⟩
  have hmarked (F : Finset (Site d)) (hFm : F.card = m) :
      ((marked F).card : ENNReal) ≤ (2 : ENNReal) ^ m := by
    have hcard : (marked F).card ≤ 2 ^ m := by
      calc
        (marked F).card ≤ F.powerset.card := Finset.card_filter_le _ _
        _ = 2 ^ m := by rw [Finset.card_powerset, hFm]
    exact_mod_cast hcard
  have hsum :
      bondPercolation d q
        (⋃ F ∈ T', ⋃ B ∈ marked F, {ζ | ∀ x ∈ B, ¬ xap_Good ζ x}) ≤
        (T'.card : ENNReal) * ((2 : ENNReal) ^ m * b ^ (k / 3 ^ d)) := by
    calc
      _ ≤ ∑ F ∈ T', bondPercolation d q
            (⋃ B ∈ marked F, {ζ | ∀ x ∈ B, ¬ xap_Good ζ x}) :=
          measure_biUnion_finset_le T' _
      _ ≤ ∑ _F ∈ T', ((2 : ENNReal) ^ m * b ^ (k / 3 ^ d)) := by
        apply Finset.sum_le_sum
        intro F hF
        have hFm : F.card = m := (Finset.mem_filter.mp hF).2
        calc
          _ ≤ ∑ B ∈ marked F, bondPercolation d q
                {ζ | ∀ x ∈ B, ¬ xap_Good ζ x} :=
              measure_biUnion_finset_le (marked F) _
          _ ≤ ∑ _B ∈ marked F, b ^ (k / 3 ^ d) := by
            apply Finset.sum_le_sum
            intro B hB
            have hBk : B.card = k := (Finset.mem_filter.mp hB).2
            simpa only [b, hBk] using xap6_badSet_prob_le hq0 hq1 B
          _ = ((marked F).card : ENNReal) * b ^ (k / 3 ^ d) := by
            rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (2 : ENNReal) ^ m * b ^ (k / 3 ^ d) :=
            mul_le_mul_of_nonneg_right (hmarked F hFm) zero_le
      _ = (T'.card : ENNReal) * ((2 : ENNReal) ^ m * b ^ (k / 3 ^ d)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hT' : (T'.card : ENNReal) ≤ (K : ENNReal) ^ m := by
    have hcard : T'.card ≤ K ^ m := (Finset.card_filter_le _ _).trans hTcard
    exact_mod_cast hcard
  calc
    _ ≤ bondPercolation d q
        (⋃ F ∈ T', ⋃ B ∈ marked F, {ζ | ∀ x ∈ B, ¬ xap_Good ζ x}) :=
      measure_mono hsub
    _ ≤ (T'.card : ENNReal) * ((2 : ENNReal) ^ m * b ^ (k / 3 ^ d)) := hsum
    _ ≤ ((K : ENNReal) ^ m * (2 : ENNReal) ^ m) * b ^ (k / 3 ^ d) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right hT' zero_le

end Exploding
