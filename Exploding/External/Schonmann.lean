/-
Schonmann's large-deviation bound for bootstrap percolation, quoted as
Proposition 7.4 of the paper.
-/
import Exploding.Support.Vocab

open Exploding LatticeProb MeasureTheory

/-- **Proposition 7.4** of the paper (`exploding-corrected-arxiv.tex:2139-2151`, label
`prop:schonnmann_bootstrap`), attributed to R. H. Schonmann, *On the behavior of
some cellular automata related to bootstrap percolation*, Ann. Probab. 20
(1992).

"Let `η'(x) := 2d` with probability `p` and `d` otherwise.  There are constants
`c, C` depending only on dimension and `p > 0` so that
`P(Q_n^{(d)} is η'-internally spanned) ≥ 1 - c exp(-C n)`."

`η'`-internal spanning is `Exploding.InternallySpanned`, the `(Q_n)^c`-frozen
parallel toppling with sites constrained to topple at most once, which is
bootstrap percolation with threshold `d`.  The paper cites this rather than
proving it, so it enters as an explicit hypothesis. -/
-- FROZEN-STATEMENT-BEGIN
def Exploding.External.SchonmannBootstrap : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ p : ℝ, 0 < p → p ≤ 1 →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ,
      ENNReal.ofReal (1 - c * Real.exp (-(C * (n : ℝ)))) ≤
        productLaw d (2 * (d : ℤ)) (d : ℤ) p {η | InternallySpanned η n}
-- FROZEN-STATEMENT-END
