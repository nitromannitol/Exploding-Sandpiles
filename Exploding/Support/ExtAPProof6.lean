/-
The packed bad-set probability of the high-density Peierls estimate: the
probability that a `*`-connected set of `s` bad cubes occurs is at most
`(1 - q^N)^{s / 3^d}`, because a `3`-spaced subpacking of it is independent and
covers a `3^{-d}` fraction of the set.
-/
import Exploding.Support.ExtAPProof5

open Exploding LatticeProb MeasureTheory
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-- The good density `δ = q^N`, `N` being the number of bonds of a cube. -/
noncomputable def xap6_delta (d : ℕ) (q : ℝ) : ENNReal :=
  ENNReal.ofReal q ^ (xap_cubeBonds (0 : Site d)).card

/-- The probability that every cube of a finite set is bad is at most
`(1 - δ)^{s / 3^d}`, where `s` is the number of cubes. -/
theorem xap6_badSet_prob_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (Γ : Finset (Site d)) :
    bondPercolation d q {ω | ∀ z ∈ Γ, ¬ xap_Good ω z} ≤
      (1 - xap6_delta d q) ^ (Γ.card / 3 ^ d) := by
  obtain ⟨Γ', hsub, hfar, hcard⟩ := xap3_exists_packing Γ
  have hmono : {ω : Site d × Fin d → Bool | ∀ z ∈ Γ, ¬ xap_Good ω z}
      ⊆ {ω | ∀ z ∈ Γ', ¬ xap_Good ω z} := by
    intro ω hω z hz
    exact hω z (hsub hz)
  have hbase : 1 - xap6_delta d q ≤ 1 := tsub_le_self
  have hexp : Γ.card / 3 ^ d ≤ Γ'.card := by
    exact Nat.div_le_of_le_mul hcard
  calc bondPercolation d q {ω | ∀ z ∈ Γ, ¬ xap_Good ω z}
      ≤ bondPercolation d q {ω | ∀ z ∈ Γ', ¬ xap_Good ω z} := measure_mono hmono
    _ = (1 - xap6_delta d q) ^ Γ'.card := by
        rw [xap6_delta]
        exact xap4_packing_bad_prob h0 h1 Γ' hfar
    _ ≤ (1 - xap6_delta d q) ^ (Γ.card / 3 ^ d) :=
        pow_le_pow_of_le_one (show (0 : ENNReal) ≤ 1 - xap6_delta d q by simp) hbase hexp

/-- The probability that some member of a finite family of `*`-connected sets of
equal size is all bad is at most the family size times `(1 - δ)^{s/3^d}`. -/
theorem xap6_biUnion_bad_prob_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (S : Finset (Finset (Site d))) (s : ℕ) (hcard : ∀ Γ ∈ S, Γ.card = s) :
    bondPercolation d q {ω | ∃ Γ ∈ S, ∀ z ∈ Γ, ¬ xap_Good ω z} ≤
      (S.card : ENNReal) * (1 - xap6_delta d q) ^ (s / 3 ^ d) := by
  have hsub : {ω : Site d × Fin d → Bool | ∃ Γ ∈ S, ∀ z ∈ Γ, ¬ xap_Good ω z}
      ⊆ ⋃ Γ ∈ S, {ω | ∀ z ∈ Γ, ¬ xap_Good ω z} := by
    intro ω hω
    rcases hω with ⟨Γ, hΓ, hbad⟩
    exact Set.mem_iUnion.2 ⟨Γ, Set.mem_iUnion.2 ⟨hΓ, hbad⟩⟩
  calc bondPercolation d q {ω | ∃ Γ ∈ S, ∀ z ∈ Γ, ¬ xap_Good ω z}
      ≤ bondPercolation d q (⋃ Γ ∈ S, {ω | ∀ z ∈ Γ, ¬ xap_Good ω z}) := measure_mono hsub
    _ ≤ ∑ Γ ∈ S, bondPercolation d q {ω | ∀ z ∈ Γ, ¬ xap_Good ω z} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _Γ ∈ S, (1 - xap6_delta d q) ^ (s / 3 ^ d) := by
        refine Finset.sum_le_sum fun Γ hΓ => ?_
        rw [← hcard Γ hΓ]
        exact xap6_badSet_prob_le h0 h1 Γ
    _ = (S.card : ENNReal) * (1 - xap6_delta d q) ^ (s / 3 ^ d) := by
        rw [Finset.sum_const, nsmul_eq_mul]

end Exploding
