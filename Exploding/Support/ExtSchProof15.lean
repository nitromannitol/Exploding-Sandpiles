/-
Coarse graining and the finite-volume percolation estimate.

`xsch13_Percolates d p` says `xsch8_a d p n → 0`, i.e. the cube `Q_n^d` is
internally spanned with probability tending to one.  This is the finite-volume
form of Schonmann's theorem for `d`-neighbour bootstrap percolation (threshold
`d`, occupied sites `2d`).

The intended proof is the coarse graining of the process to a supercritical
Bernoulli block percolation: one exhibits a `K`-block "seed" that grows for the
critical case `r = d`, checks that seeds percolate for every `p > 0` once `K` is
large, and transfers a percolating seed cluster to a spanning event for `Q_n`.
Constructing the seed and proving its growth in the critical case `r = d` is
Schonmann's argument; it is not available here, and we do not claim it.  The base
scale `xsch8_Base` is exactly the missing one-scale "seed" input, and the earlier
attempt to obtain it from the one-dimensional base and the recursion alone was
refuted in `ExtSchProof14`.

We record the parts that are provable without the critical seed:

* `xsch15_Percolates_of_percolationBound`: the exponential percolation bound
  `xsch3_PercolationBound` implies the finite-volume statement;
* `xsch15_percolates_one`: the unconditional one-dimensional instance
  `xsch13_Percolates 1 p`, via `xsch5_percolation_one`.

Since `xsch13_Percolates` for `d ≥ 2` is not proved, `xsch_proved` is not
assembled.
-/
import Exploding.Support.ExtSchProof14

namespace Exploding

open LatticeProb MeasureTheory Filter Topology

variable {d : ℕ}

/-- The exponential percolation estimate implies the finite-volume statement:
`0 ≤ xsch8_a d p n ≤ c e^{-C n}` and the right-hand side tends to `0`. -/
theorem xsch15_Percolates_of_percolationBound {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)]
    (h : xsch3_PercolationBound d p) : xsch13_Percolates d p := by
  obtain ⟨c, C, _hc, hC, hbound⟩ := h
  rw [xsch13_Percolates]
  refine squeeze_zero' (f := xsch8_a d p)
    (g := fun n : ℕ => c * Real.exp (-(C * (n : ℝ))))
    (Eventually.of_forall fun n => measureReal_nonneg) ?_ ?_
  · filter_upwards with n using hbound n
  · have h1 : Tendsto (fun n : ℕ => Real.exp (-(C * (n : ℝ)))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop hC)
    simpa using h1.const_mul c

/-- The coarse block-percolation estimate likewise gives the finite-volume
statement. -/
theorem xsch15_Percolates_of_blockPercolation {p : ℝ} (_hd : 1 ≤ d) (hp : 0 < p)
    (hp1 : p < 1) (h : xsch7_BlockPercolation d p) : xsch13_Percolates d p := by
  haveI : Fact (0 ≤ p ∧ p ≤ 1) := ⟨⟨hp.le, hp1.le⟩⟩
  obtain ⟨c, C, hc, hC, hbound⟩ := h
  refine xsch15_Percolates_of_percolationBound ⟨c, C, hc, hC, fun n => ?_⟩
  have hsub : {η : Site d → ℤ | ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (cube d n) η}
      ⊆ {η : Site d → ℤ | η ∉ xsch7_BlockCover d n} := by
    intro η hη hcov
    exact hη (xsch7_sp_of_blockCover hcov)
  exact le_trans (measureReal_mono hsub (measure_ne_top _ _)) (hbound n)

/-- **One dimension.**  A single occupied site topples the whole interval, and
the failure probability `(1 - p) ^ n` tends to `0`. -/
theorem xsch15_percolates_one {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)] (hp : 0 < p) :
    xsch13_Percolates 1 p :=
  xsch15_Percolates_of_percolationBound (xsch5_percolation_one hp)

end Exploding
