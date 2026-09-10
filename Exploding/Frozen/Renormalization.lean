/-
Proposition 2.2 of the paper: the properties of the infinite cluster of good
cubes on the macroscopic lattice.
-/
import Exploding.Support.Vocab

open Exploding LatticeProb MeasureTheory

/-- **Proposition 2.2** (`exploding.tex:482-497`, label
`prop:renormalization_properties`).

"For fixed `k` large enough, there are constants `c, C` so that the following
hold on an event of probability 1.
 (1) There is a unique infinite cluster `C_∞` of good cubes on the macroscopic
     lattice `{Q_k(i)}`.
 (2) There is `n_0` so that for `n ≥ n_0`, any connected component of `C_∞^c`
     that intersects `[-n,n]^d` has volume smaller than `(log n)^{5/2}`.
 (3) There is `n_0` so that for `n ≥ n_0`, for any `x, y ∈ C_∞` with `|x| ≤ n`
     and `|x-y| ≥ (log n)^2`, `c |x-y| ≤ d(x,y) ≤ C |x-y|`, where `d` is the
     chemical (graph) distance on `C_∞`."

`c` and `C` are fixed before `η`, as the paper fixes them before passing to the
probability-one event.  "Volume" is cardinality, and the finiteness of the
component is asserted alongside the bound so that no infinite set is read
through `Set.ncard = 0`.  The chemical distance is taken in `ℕ∞`, so the upper
bound also says that `x` and `y` are joined inside `C_∞`. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.renormalization_properties (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᵐ η ∂(toyLaw d p),
        ∃! Cinf : Set (Site d), IsInfiniteGoodCluster η k Cinf ∧
          (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)),
            x ∉ Cinf →
              (componentIn Cinfᶜ x).Finite ∧
                ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2)) ∧
          (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ Cinf, ∀ y ∈ Cinf,
            mnorm x ≤ (n : ℤ) → Real.log n ^ (2 : ℕ) ≤ (mnorm (x - y) : ℝ) →
              ∃ m : ℕ, chemDist Cinf x y = (m : ℕ∞) ∧
                c * (mnorm (x - y) : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ C * (mnorm (x - y) : ℝ))
-- FROZEN-STATEMENT-END
:= by sorry
