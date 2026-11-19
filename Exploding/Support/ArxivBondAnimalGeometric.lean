import Exploding.Support.ArxivBondAnimalExtraction

/-!
# Geometric tail for connected sets with few good cubes

At a sufficiently small bad-cube probability, the connected-set estimate has
geometric decay in the size of a finite exceptional set.
-/

open LatticeProb MeasureTheory

namespace Exploding

/-- If the bad-cube probability is sufficiently small, a connected set of size
at least `2 * 3^d * t` whose good sites lie in a set of size at most `3^d * t`
has probability at most `2⁻ᵗ`. -/
theorem bond_connected_bad_cubes_prob_le_geometric (d : ℕ) :
    ∃ K : ℕ, ∀ (p : Site d) (P : Finset (Site d)) (t : ℕ),
      1 ≤ t → P.card ≤ 3 ^ d * t → ∀ {q : ℝ}, 0 ≤ q → q ≤ 1 →
      ((K : ENNReal) * 2) ^ (2 * 3 ^ d) * (1 - xap6_delta d q) ≤ 1 / 2 →
      bondPercolation d q
        {ω | ∃ S : Set (Site d), xmh_SConn S ∧ p ∈ S ∧
          ((2 * 3 ^ d * t : ℕ) : ℕ∞) ≤ S.encard ∧
          ∀ x ∈ S, x ∉ P → ¬ xap_Good ω x} ≤ (1 / 2 : ENNReal) ^ t := by
  obtain ⟨K, hK⟩ := bond_connected_bad_cubes_prob_le d
  refine ⟨K, fun p P t ht hP q hq0 hq1 hsmall => ?_⟩
  have hB : 0 < 3 ^ d := by positivity
  have hm : 1 ≤ 2 * 3 ^ d * t := by nlinarith
  have hsize : P.card + 3 ^ d * t ≤ 2 * 3 ^ d * t := by nlinarith
  have hbound := hK p P (2 * 3 ^ d * t) (3 ^ d * t) hm hsize hq0 hq1
  have hdiv : 3 ^ d * t / 3 ^ d = t := by
    simp [Nat.mul_comm]
  have heq :
      ((K : ENNReal) ^ (2 * 3 ^ d * t) * (2 : ENNReal) ^ (2 * 3 ^ d * t)) *
          (1 - xap6_delta d q) ^ (3 ^ d * t / 3 ^ d) =
        (((K : ENNReal) * 2) ^ (2 * 3 ^ d) * (1 - xap6_delta d q)) ^ t := by
    rw [hdiv, ← mul_pow, pow_mul, ← mul_pow]
  rw [heq] at hbound
  exact hbound.trans (pow_le_pow_left₀ (by positivity) hsmall t)

end Exploding
