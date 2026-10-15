import Exploding.Support.ArxivBondDefectPacking
import Exploding.Support.ExtMHCount

/-!
# Rooted finite defective star-animals

The finite-family count for star-connected sets, combined with the prescribed-set bond-defect
estimate, bounds the probability of a rooted defective star-animal. The count constant is the
witness supplied by `xmh_starCount`; no animal-count or independence premise is assumed here.
-/

open LatticeProb MeasureTheory ProbabilityTheory

namespace Exploding

variable {d : ℕ}

/-- The Bernoulli bond probability of a rooted, finite, star-connected defective animal of size
`m` is bounded using the finite-family witness from `xmh_starCount` and the packing estimate. -/
theorem arxiv_bond_defective_star_animal_prob_le (d : ℕ) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ (p : Site d) (m : ℕ) {q : ℝ}, 0 ≤ q → q ≤ 1 →
      bondPercolation d q
        {ζ | ∃ F : Finset (Site d), p ∈ F ∧ F.card = m ∧
          xmh_SConn (F : Set (Site d)) ∧
          ∀ x ∈ F, rn_siteField ζ x = false} ≤
        (K : ENNReal) ^ m *
          (ENNReal.ofReal (2 * (d : ℝ) * (1 - q))) ^ (m / 3 ^ d) := by
  classical
  obtain ⟨K, hcount⟩ :
      ∃ K : ℕ, ∀ (p : Site d) (m : ℕ),
        ∃ T : Finset (Finset (Site d)), T.card ≤ K ^ m ∧
          ∀ F : Finset (Site d), p ∈ F → F.card = m →
            xmh_SConn (F : Set (Site d)) → F ∈ T :=
    xmh_starCount d
  have hKpos : 1 ≤ K := by
    obtain ⟨T, hTcard, hTmem⟩ := hcount (0 : Site d) 1
    have hmem : ({0} : Finset (Site d)) ∈ T := by
      apply hTmem
      · simp
      · simp
      · simpa using xmh_SConn_singleton (0 : Site d)
    have hTpos : 0 < T.card := Finset.card_pos.mpr ⟨{0}, hmem⟩
    have hTK : T.card ≤ K := by simpa using hTcard
    omega
  refine ⟨K, hKpos, ?_⟩
  intro p m q hq0 hq1
  obtain ⟨T, hTcard, hTmem⟩ := hcount p m
  let T' : Finset (Finset (Site d)) := T.filter (fun F => F.card = m)
  let b : ENNReal := ENNReal.ofReal (2 * (d : ℝ) * (1 - q))
  have hsub :
      {ζ | ∃ F : Finset (Site d), p ∈ F ∧ F.card = m ∧
        xmh_SConn (F : Set (Site d)) ∧ ∀ x ∈ F, rn_siteField ζ x = false} ⊆
        ⋃ F ∈ T', {ζ | ∀ x ∈ F, rn_siteField ζ x = false} := by
    rintro ζ ⟨F, hp, hcard, hconn, hdef⟩
    exact Set.mem_iUnion.mpr ⟨F, Set.mem_iUnion.mpr
      ⟨Finset.mem_filter.mpr ⟨hTmem F hp hcard hconn, hcard⟩, hdef⟩⟩
  have hsum :
      bondPercolation d q (⋃ F ∈ T', {ζ | ∀ x ∈ F, rn_siteField ζ x = false}) ≤
        (T'.card : ENNReal) * b ^ (m / 3 ^ d) := by
    calc
      bondPercolation d q (⋃ F ∈ T', {ζ | ∀ x ∈ F, rn_siteField ζ x = false}) ≤
          ∑ F ∈ T', bondPercolation d q
            {ζ | ∀ x ∈ F, rn_siteField ζ x = false} :=
        measure_biUnion_finset_le T' _
      _ ≤ ∑ _F ∈ T', b ^ (m / 3 ^ d) := by
        apply Finset.sum_le_sum
        intro F hF
        have hFm : F.card = m := (Finset.mem_filter.mp hF).2
        have hpack := arxiv_bond_defects_prob_packing_le F hq0 hq1
        simpa only [b, hFm] using hpack
      _ = (T'.card : ENNReal) * b ^ (m / 3 ^ d) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : T'.card ≤ K ^ m := by
    exact le_trans (Finset.card_filter_le _ _) hTcard
  have hcard' : (T'.card : ENNReal) ≤ (K : ENNReal) ^ m := by
    exact_mod_cast hcard
  calc
    bondPercolation d q
        {ζ | ∃ F : Finset (Site d), p ∈ F ∧ F.card = m ∧
          xmh_SConn (F : Set (Site d)) ∧
          ∀ x ∈ F, rn_siteField ζ x = false} ≤
        bondPercolation d q
          (⋃ F ∈ T', {ζ | ∀ x ∈ F, rn_siteField ζ x = false}) :=
      measure_mono hsub
    _ ≤ (T'.card : ENNReal) * b ^ (m / 3 ^ d) := hsum
    _ ≤ (K : ENNReal) ^ m * b ^ (m / 3 ^ d) := by
      exact mul_le_mul_of_nonneg_right hcard' zero_le

end Exploding
