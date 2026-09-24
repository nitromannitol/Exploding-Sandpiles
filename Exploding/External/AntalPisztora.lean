/-
Theorem 1.1 of Antal and Pisztora, the linear upper bound on the chemical
distance in supercritical bond percolation, quoted before Proposition 2.2 of
the paper.
-/
import Exploding.Support.Percolation

open Exploding LatticeProb MeasureTheory

/-- **Theorem 1.1** of P. Antal and A. Pisztora, *On the chemical distance for
supercritical Bernoulli percolation*, Ann. Probab. 24 (1996), cited at
`exploding.tex:478` for Proposition 2.2 (label `prop:renormalization_properties`).

The source: for Bernoulli bond percolation on `ℤ^d`, `d ≥ 2`, with density
`p > p_c`, there is `ρ = ρ(p, d) ∈ [1, ∞)` with
`limsup_{|y| → ∞} |y|^{-1} log P(0 ↔ y, D(0, y) > ρ |y|) < 0`,
where `|y|` is the `ℓ^1` norm and `D` is the chemical distance, the least length
of an open path.

`p_c` is `bondCritical d`, the supremum of the densities at which the open
cluster of the origin is almost surely finite, as in `(1.1)` of the source.  The
chemical distance is the graph distance in the graph of open bonds, which is
`⊤` exactly when `0` and `y` are not connected, so the event is that it is a
natural number larger than `ρ |y|`.  A negative `limsup` is written as an
exponential bound beyond some distance `R`, which is equivalent.  The paper
cites the result rather than proving it, so it enters as an explicit
hypothesis. -/
-- FROZEN-STATEMENT-BEGIN
def Exploding.External.AntalPisztoraChemicalDistance : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ q : ℝ, bondCritical d < q → q ≤ 1 →
    ∃ ρ c : ℝ, 1 ≤ ρ ∧ 0 < c ∧ ∃ R : ℕ, ∀ y : Site d, (R : ℤ) ≤ mnorm y →
      bondPercolation d q
          {ω | ∃ m : ℕ, (openBondGraph ω).edist 0 y = (m : ℕ∞) ∧ ρ * (mnorm y : ℝ) < (m : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(c * (mnorm y : ℝ))))
-- FROZEN-STATEMENT-END
