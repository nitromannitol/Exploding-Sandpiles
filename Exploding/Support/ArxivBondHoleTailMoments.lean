import Exploding.Support.ArxivBondFiniteHoleTail
import LatticeProb.Analysis.StretchedExponentialSummability

/-!
# Polynomially weighted summability of the finite-hole tail

The exponential tail `C · exp(-c √s)` of the actual open-bond finite-hole event, from
`arxiv_bond_finite_hole_tail_exp`, dominates every polynomial weight: for each `r`, the
sequence `s ↦ s^r · exp(-c √s)` is summable. Hence `s ↦ s^r · P(finite-hole event at s)` is
summable over `s : ℕ` for every `z`, `q ∈ [q0, 1]`, and `r`, with one common threshold `q0`.

The comparison uses `x^k / k! ≤ exp x` with `x = c √s` and `k = 2r + 4`. This gives
`s^(r+2) · exp(-c √s) ≤ k! / c^k`, so `s^r · exp(-c √s) ≤ (k! / c^k) · s⁻²` for `s ≥ 1`, and
the series `∑ s⁻²` is summable.

This is an analytic consequence of the installed tail only. It does not identify the infinite
cluster, does not give projected chemical-distance integrability, and does not close any
source step.
-/

open LatticeProb MeasureTheory

namespace Exploding

/-- For `d ≥ 2` there is a fixed `q0 ∈ [0, 1)` such that, for every root `z`, every density
`q ∈ [q0, 1]`, and every polynomial weight `s ↦ s^r`, the weighted finite-hole probability
`s^r · P(finite-hole event at threshold s)` is summable over `s : ℕ`. -/
theorem arxiv_bond_finite_hole_weighted_tail_summable (d : ℕ) (hd : 2 ≤ d) :
    ∃ q0 : ℝ, 0 ≤ q0 ∧ q0 < 1 ∧
      ∀ (z : Site d) (q : ℝ), q0 ≤ q → q ≤ 1 → ∀ r : ℕ,
        Summable (fun s : ℕ => (s : ℝ) ^ r *
          (bondPercolation d q
            {ζ | ∃ i : Site d,
              z ∉ {y : Site d | (openBondGraph ζ).Reachable i y} ∧
              (componentIn ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z).Finite ∧
              s ≤ (componentIn ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z).ncard}).toReal) := by
  obtain ⟨_, q0, C, c, _, hq0, hq1, hC, hc, htail⟩ := arxiv_bond_finite_hole_tail_exp d hd
  refine ⟨q0, hq0, hq1, fun z q hq0' hq1' r => ?_⟩
  refine Summable.of_nonneg_of_le (fun s => ?_) (fun s => ?_)
    ((LatticeProb.summable_pow_mul_exp_neg_sqrt c hc r).mul_left C)
  · exact mul_nonneg (pow_nonneg (Nat.cast_nonneg s) r) ENNReal.toReal_nonneg
  · have hb : 0 ≤ C * Real.exp (-c * Real.sqrt (s : ℝ)) :=
      mul_nonneg hC.le (Real.exp_pos _).le
    have hμ := ENNReal.toReal_le_of_le_ofReal hb (htail z s hq0' hq1')
    refine le_trans (mul_le_mul_of_nonneg_left hμ (pow_nonneg (Nat.cast_nonneg s) r)) (le_of_eq ?_)
    ring

end Exploding
