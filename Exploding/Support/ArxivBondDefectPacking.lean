import Exploding.Support.ArxivBondDefectProbability

/-!
# Probability of defects in a prescribed finite set

A residue class modulo three contains a separated subfamily of every finite set of sites.
The product estimate for separated defects and a split according to whether the one-site bound
is at most one give the stated finite-set estimate for every Bernoulli bond parameter.
-/

open LatticeProb MeasureTheory ProbabilityTheory

namespace Exploding

variable {d : ℕ}

/-- The defect probability on any prescribed finite set is bounded by the residue-class
packing exponent, for every Bernoulli bond parameter in its probability range. -/
theorem arxiv_bond_defects_prob_packing_le (F : Finset (Site d)) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    bondPercolation d q {ζ | ∀ x ∈ F, rn_siteField ζ x = false} ≤
      (ENNReal.ofReal (2 * (d : ℝ) * (1 - q))) ^ (F.card / 3 ^ d) := by
  classical
  haveI : IsProbabilityMeasure (bondPercolation d q) := rn_infinitePi_isProb hq0 hq1
  obtain ⟨F', hsubset, hfar, hcard⟩ := xap3_exists_packing F
  have hsep : ∀ x ∈ F', ∀ y ∈ F', x ≠ y → ¬ (lattice d).Adj x y := by
    intro x hx y hy hxy hadj
    obtain ⟨i, hcoord⟩ := hfar x hx y hy hxy
    obtain ⟨j, hj | hj⟩ := hadj
    · have hsmall : |x i - y i| ≤ 1 := by
        rw [hj]
        by_cases hij : i = j
        · subst i
          norm_num [unit]
        · simp [unit, hij]
      omega
    · have hsmall : |x i - y i| ≤ 1 := by
        rw [hj]
        by_cases hij : i = j
        · subst i
          norm_num [unit]
        · simp [unit, hij]
      omega
  have hexp : F.card / 3 ^ d ≤ F'.card := by
    apply Nat.div_le_of_le_mul
    exact hcard
  let b : ENNReal := ENNReal.ofReal (2 * (d : ℝ) * (1 - q))
  by_cases hb : b ≤ 1
  · have hpow_le_one : ∀ n : ℕ, b ^ n ≤ 1 := by
      intro n
      induction n with
      | zero => simp
      | succ n hn =>
          rw [pow_succ]
          exact (mul_le_mul hn hb (by positivity) (by positivity)).trans_eq (one_mul _)
    have hpower : b ^ F'.card ≤ b ^ (F.card / 3 ^ d) := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hexp
      rw [hk, pow_add]
      calc
        b ^ (F.card / 3 ^ d) * b ^ k ≤ b ^ (F.card / 3 ^ d) * 1 := by
          gcongr
          exact hpow_le_one k
        _ = b ^ (F.card / 3 ^ d) := mul_one _
    have hmono :
        {ζ | ∀ x ∈ F, rn_siteField ζ x = false} ⊆
          {ζ | ∀ x ∈ F', rn_siteField ζ x = false} := by
      intro ζ hζ x hx
      exact hζ x (hsubset hx)
    calc
      bondPercolation d q {ζ | ∀ x ∈ F, rn_siteField ζ x = false} ≤
          bondPercolation d q {ζ | ∀ x ∈ F', rn_siteField ζ x = false} := measure_mono hmono
      _ ≤ b ^ F'.card := by
        simpa only [b] using arxiv_bond_defects_prob_le F' hq0 hq1 hsep
      _ ≤ b ^ (F.card / 3 ^ d) := hpower
  · have hbase : 1 ≤ b := le_of_lt (lt_of_not_ge hb)
    have hprob :
        bondPercolation d q {ζ | ∀ x ∈ F, rn_siteField ζ x = false} ≤ 1 := by
      calc
        bondPercolation d q {ζ | ∀ x ∈ F, rn_siteField ζ x = false} ≤
            bondPercolation d q Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    calc
      bondPercolation d q {ζ | ∀ x ∈ F, rn_siteField ζ x = false} ≤ 1 := hprob
      _ ≤ b ^ (F.card / 3 ^ d) := one_le_pow₀ hbase

end Exploding
