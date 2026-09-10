/-
Theorem 1.3 of the paper: the rescaled arrival times of the exploding sandpile
converge locally uniformly to a continuous, convex, one-homogeneous function.
-/
import Exploding.Support.Vocab

open Exploding LatticeProb MeasureTheory Filter

/-- **Theorem 1.3** (`exploding.tex:259-262`, label `theorem:convergence_of_time_constant`).

"Let `η` be as in (1.2) and let `T_η(x) := min{t ≥ 1 : v_t(x) > 0}`.  On an event
of probability 1, the rescaled arrival times `T̄_η(x) := n^{-1} T_η([n x])`
converge locally uniformly to `N_p`, a continuous, convex, one-homogeneous
function on `ℝ^d`."

`T_η` is `Exploding.arrival`, the arrival time of the parallel toppling odometer
for `η + M_η δ₀`, taken in `ℕ∞`; the almost-sure event asserts that it is finite
at every site, so that reading it as a natural number is not a junk value.
Locally uniform convergence is written in its `ε`-form for the same reason: a
supremum over a compact set would be read through `sSup ∅ = 0`.  `N_p` is
deterministic: it is bound before `η`. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.convergence_of_time_constant (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ N : (Fin d → ℝ) → ℝ,
      Continuous N ∧
      ConvexOn ℝ Set.univ N ∧
      (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
      ∀ᵐ η ∂(toyLaw d p),
        Explosive η ∧ (∀ x : Site d, arrival η x ≠ ⊤) ∧
          ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
            ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
              |((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ) - N y| ≤ ε
-- FROZEN-STATEMENT-END
:= by sorry
