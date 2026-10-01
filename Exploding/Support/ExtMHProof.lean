/-
The Peierls layer of Lemma 5.2 of Mathieu: the probability that a prescribed finite set of
sites is entirely closed, and the union bound over a family of such sets.  These are the
elementary probabilistic inputs of the finite-cluster expansion on the holes of the infinite
cluster of site percolation.
-/
import Exploding.Support.ExtMHBase

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- The one-site Bernoulli law is a probability measure. -/
theorem xmh_bitLaw_univ {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : bitLaw q Set.univ = 1 := by
  simp only [bitLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  simp

/-- The one-site Bernoulli law of a closed site. -/
theorem xmh_bitLaw_false (q : ℝ) : bitLaw q {false} = ENNReal.ofReal (1 - q) := by
  simp [bitLaw]

/-- **Finite-cluster expansion.**  The probability that a prescribed finite set of sites is
entirely closed is `(1 - q)` to the power of its cardinality. -/
theorem xmh_site_closed_prob {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (S : Finset (Site d)) :
    sitePercolation d q {ω | ∀ x ∈ S, ω x = false} = ENNReal.ofReal (1 - q) ^ S.card := by
  haveI : IsProbabilityMeasure (bitLaw q) := ⟨xmh_bitLaw_univ h0 h1⟩
  have hset : {ω : Site d → Bool | ∀ x ∈ S, ω x = false} =
      Set.pi (↑S : Set (Site d)) (fun _ => ({false} : Set Bool)) := by
    ext ω
    simp
  unfold sitePercolation
  rw [hset, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  simp [xmh_bitLaw_false]

/-- **Peierls union bound.**  The probability that some member of a finite family of
`m`-element sets is entirely closed is at most the size of the family times `(1 - q)^m`. -/
theorem xmh_peierls_union {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (T : Finset (Finset (Site d))) (m : ℕ) (hm : ∀ F ∈ T, F.card = m) :
    sitePercolation d q {ω | ∃ F ∈ T, ∀ x ∈ F, ω x = false}
      ≤ T.card * ENNReal.ofReal (1 - q) ^ m := by
  classical
  have hunion : sitePercolation d q {ω | ∃ F ∈ T, ∀ x ∈ F, ω x = false}
      ≤ ∑ F ∈ T, sitePercolation d q {ω | ∀ x ∈ F, ω x = false} := by
    have heq : {ω : Site d → Bool | ∃ F ∈ T, ∀ x ∈ F, ω x = false}
        = ⋃ F ∈ T, {ω : Site d → Bool | ∀ x ∈ F, ω x = false} := by
      ext ω; simp
    rw [heq]
    exact measure_biUnion_finset_le T _
  calc sitePercolation d q {ω | ∃ F ∈ T, ∀ x ∈ F, ω x = false}
      ≤ ∑ F ∈ T, sitePercolation d q {ω | ∀ x ∈ F, ω x = false} := hunion
    _ = ∑ F ∈ T, ENNReal.ofReal (1 - q) ^ F.card := by
        exact Finset.sum_congr rfl fun F _ => xmh_site_closed_prob h0 h1 F
    _ = ∑ _F ∈ T, ENNReal.ofReal (1 - q) ^ m := by
        refine Finset.sum_congr rfl fun F hF => ?_
        rw [hm F hF]
    _ = T.card * ENNReal.ofReal (1 - q) ^ m := by
        rw [Finset.sum_const, nsmul_eq_mul]

end Exploding
