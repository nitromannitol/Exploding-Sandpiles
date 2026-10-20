/-
Lemma 5.2 of Mathieu, the polylogarithmic volume of the holes of the infinite
cluster of highly supercritical site percolation, quoted before Proposition 2.2
of the paper.
-/
import Exploding.Support.Percolation

open Exploding LatticeProb MeasureTheory

/-- **Lemma 5.2** of P. Mathieu, *Quenched invariance principles for random
walks with random conductances*, J. Stat. Phys. 130 (2008), cited at
`exploding-corrected-arxiv.tex` for clause (2) of Proposition 2.2 (label
`prop:renormalization_properties`), where it bounds the holes of the infinite
cluster of a high density site percolation process lying inside `C_∞`.

The source: there is `p₂ < 1` such that for site percolation of parameter
`r > p₂`, for almost every realization and for large enough `n`, any connected
component of the complement of the infinite cluster `C` that intersects the box
`[-n, n]^d` has volume smaller than `(log n)^{5/2}`.

The source takes `r` above the uniqueness threshold, so that `C` is the unique
infinite cluster; the bound is stated here for every infinite open cluster,
which almost surely is that one.  A component of volume smaller than
`(log n)^{5/2}` is finite, and its finiteness is stated so that no infinite set
is read through `Set.ncard = 0`.  The paper cites the result rather than proving
it, so it enters as an explicit hypothesis. -/
-- FROZEN-STATEMENT-BEGIN
def Exploding.External.MathieuHoleVolume : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ q₀ : ℝ, q₀ < 1 ∧ ∀ q : ℝ, q₀ < q → q ≤ 1 →
    ∀ᵐ ω ∂(sitePercolation d q), ∀ C : Set (Site d), IsInfiniteOpenCluster ω C →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ C →
        (componentIn Cᶜ x).Finite ∧
          ((componentIn Cᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2)
-- FROZEN-STATEMENT-END
