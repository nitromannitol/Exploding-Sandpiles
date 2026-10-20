/-
Corollary 1.4 of Liggett, Schonmann and Stacey, domination of a field of bits
with a bounded-degree dependence graph by a product measure, quoted before
Proposition 2.2 of the paper.
-/
import Exploding.Support.Percolation

open Exploding LatticeProb MeasureTheory

/-- **Corollary 1.4** of T. M. Liggett, R. H. Schonmann and A. M. Stacey,
*Domination by product measures*, Ann. Probab. 25 (1997), with Theorem 1.3 of
the same paper, cited at `exploding-corrected-arxiv.tex` for Proposition 2.2 (label
`prop:renormalization_properties`).

The source: let `G` be a graph with a countable vertex set `S` in which every
vertex has degree at most `Δ ≥ 1`, and in which every finite connected
component contains a vertex of degree strictly less than `Δ`.  Let `G(p)` be the
class of laws of fields of bits on `S` with dependence graph `G` whose one-site
probabilities are at least `p`, and let `σ_G(p)` be the supremum of the
densities `ρ` such that every law in `G(p)` dominates the product law of
density `ρ`.  Then `σ_G(p) → 1` as `p → 1`.

The limit is stated in the form it is used: for every `ρ < 1` there is `p < 1`
such that every law in `G(p)` dominates the product law of density `ρ`.
Domination is stated through increasing events: every measurable increasing
event has no larger probability under the product law than under the given
law.  The dependence graph is stated through finite sets of vertices, which
determine the independence of the generated `σ`-algebras.  The paper cites the
result rather than proving it, so it enters as an explicit hypothesis. -/
-- FROZEN-STATEMENT-BEGIN
def Exploding.External.LiggettSchonmannStaceyBoundedDegree : Prop :=
  ∀ (S : Type) [Countable S] (G : SimpleGraph S) (Δ : ℕ), 1 ≤ Δ →
    (∀ s : S, (G.neighborSet s).Finite ∧ (G.neighborSet s).ncard ≤ Δ) →
    (∀ s : S, (G.connectedComponentMk s).supp.Finite →
      ∃ t ∈ (G.connectedComponentMk s).supp, (G.neighborSet t).ncard < Δ) →
    ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 →
      ∃ p : ℝ, p < 1 ∧ ∀ μ : Measure (S → Bool), IsProbabilityMeasure μ →
        HasDependenceGraph G μ → (∀ s : S, ENNReal.ofReal p ≤ μ {ω | ω s = true}) →
        ∀ A : Set (S → Bool), MeasurableSet A → IsIncreasingSet A →
          bernoulliProduct S ρ A ≤ μ A
-- FROZEN-STATEMENT-END
