/-
Theorem 0.0 of Liggett, Schonmann and Stacey, domination of a finite-range
dependent field of bits by a product measure, quoted in the proof of
Proposition 5.1 of the paper.
-/
import Exploding.Support.Percolation

open Exploding LatticeProb MeasureTheory

/-- **Theorem 0.0 (i) and (ii)** of T. M. Liggett, R. H. Schonmann and
A. M. Stacey, *Domination by product measures*, Ann. Probab. 25 (1997), cited at
`exploding.tex:1215-1217` in the proof of Proposition 5.1 (label
`prop:convergence_of_the_generalized_last_wave`).

The source: for each `d` and `k`, when `p` is large enough every `k`-dependent
field of bits on `ℤ^d` whose one-site probabilities are at least `p` is
dominated from below by the product field of some density `ρ(d, k, p)`, and
`ρ(d, k, p)` can be made arbitrarily close to `1` by taking `p` large enough.

Domination from below is stated through increasing events: every measurable
increasing event has no larger probability under the product field than under
the given field.  This follows from domination by the coupling of Lemma 1.0 of
the source.  The paper cites the result rather than proving it, so it enters
as an explicit hypothesis. -/
-- FROZEN-STATEMENT-BEGIN
def Exploding.External.LiggettSchonmannStacey : Prop :=
  ∀ d k : ℕ, 1 ≤ d → ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 →
    ∃ p : ℝ, p < 1 ∧ ∀ μ : Measure (Site d → Bool), IsProbabilityMeasure μ →
      KDependent k μ → (∀ s : Site d, ENNReal.ofReal p ≤ μ {ω | ω s = true}) →
      ∀ A : Set (Site d → Bool), MeasurableSet A → IsIncreasingEvent A →
        sitePercolation d ρ A ≤ μ A
-- FROZEN-STATEMENT-END
