/-
Proposition 5.1 of the paper: convergence of the last-wave under the general
hypotheses.
-/
import Exploding.Support.Hypotheses

open Exploding LatticeProb MeasureTheory Filter

/-- **Proposition 5.1** (`exploding.tex:1195-1199`, label
`prop:convergence_of_the_generalized_last_wave`).

"Under Hypotheses 5.1, 5.3, and 5.4, on an event of probability 1, `η` is
explosive and the rescaled last-wave arrival times
`n^{-1} T̂_η([nx]) := n^{-1} min{t > 0 : u_t([nx]) > 0}` converge locally
uniformly to `N_η`, a deterministic, continuous, convex, one-homogeneous
function on `ℝ^d` depending only on the law of `η`."

`N_η` depends only on the law, so it is bound before `η` and after `P`.  Locally
uniform convergence is written in its `ε`-form and the finiteness of `T̂` is
asserted, so that no supremum over an empty set and no `ENat.toNat ⊤` is read.
The setting is that of Section 5. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.convergence_of_the_generalized_last_wave (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0)
    (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η)
    (hstat : StationaryOn d L P) (herg : ErgodicOn d L P)
    (h1 : FiniteRangeOfDependence d P) (h3 : PathFillingHyp d P)
    (h4 : StronglyBoxCrossingHyp d P) :
    ∃ N : (Fin d → ℝ) → ℝ,
      Continuous N ∧
      ConvexOn ℝ Set.univ N ∧
      (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
      ∀ᵐ η ∂P,
        Explosive η ∧ (∀ x : Site d, lastArrival η (0 : Site d) x ≠ ⊤) ∧
          ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
            ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
              |((lastArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
                - N y| ≤ ε
-- FROZEN-STATEMENT-END
:= by sorry
