import Exploding.Support.ArxivCrossingBound

open Exploding LatticeProb MeasureTheory

/-- Proposition 2.1 (`exploding-corrected-arxiv.tex:286-292`, label
`prop:crossing_time`).

"For every `δ > 0`, there is a `k` so that `max_{i,z} 𝔠_k^{(i,z)} ≤ k^d`
with probability at least `(1 - δ)`."

The event expands the terminal condition and positive minimum from source
lines 275-283. The actual product law is specified at source lines 85-94. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.crossing_time (d : ℕ) (hd : 2 ≤ d)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ k : ℕ, 1 ≤ k ∧
      ENNReal.ofReal (1 - δ) ≤ toyLaw d p
        {η : Site d → ℤ |
          ∀ (i : Fin d) (z : Site d), z ∈ closureN (cube d k) →
            (∀ x ∈ cube d k, ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
              crossOdo η k i z t x = 1) ∧
            (∃ n : ℕ, 1 ≤ n ∧ n ≤ k ^ d ∧
              ∀ x ∈ cube d k, crossOdo η k i z n x = 1)
        }
-- FROZEN-STATEMENT-END
:= by
  exact Exploding.crossing_time_terminal_bound d hd p hp hp1 δ hδ
