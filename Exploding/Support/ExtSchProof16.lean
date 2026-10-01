/-
The critical case `r = d`: status of the coarse graining.

`xsch13_Percolates d p` says `xsch8_a d p n → 0`, i.e. `Q_n^d` is internally
spanned with probability tending to one under threshold `d` bootstrap percolation
(occupied sites `2d`).  This is the finite-volume form of Schonmann's theorem for
the critical case `r = d`.

The coarse graining the statement suggests would need a `K`-block "seed" whose
closure grows without bound once the surrounding blocks are good, so that a
supercritical Bernoulli cluster of good blocks yields a spanning event.  In the
critical case `r = d` no finite seed has unbounded closure: a fully occupied box
never grows (a site outside a face has exactly one neighbour inside it), and a
finite diagonal slab grows only up to its own bounding box.  The growth that
drives percolation for `r = d` is therefore a global diagonal structure, not a
local droplet; constructing it and transferring it to `Q_n` is Schonmann's
argument and is not available here.

Consequently `xsch13_Percolates d p` is proved unconditionally only for `d = 1`
(a single occupied site topples the interval).  We record the exact reductions and
do not claim the general case, so `xsch_proved` is not assembled.
-/
import Exploding.Support.ExtSchProof15

namespace Exploding

open LatticeProb MeasureTheory Filter Topology

variable {d : ℕ}

/-- **Reformulation.**  `xsch13_Percolates` is the `ε`-`N` form of the failure
probability tending to zero. -/
theorem xsch16_percolates_iff {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)] :
    xsch13_Percolates d p ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, xsch8_a d p n < ε := by
  rw [xsch13_Percolates, Metric.tendsto_atTop]
  constructor
  · rintro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun n hn => by
      have hd := hN n hn
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (show 0 ≤ xsch8_a d p n from measureReal_nonneg)] at hd
      exact hd⟩
  · rintro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun n hn => by
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (show 0 ≤ xsch8_a d p n from measureReal_nonneg)]
      exact hN n hn⟩

/-- The exponential percolation estimate implies the finite-volume statement. -/
theorem xsch16_Percolates_of_percolationBound {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)]
    (h : xsch3_PercolationBound d p) : xsch13_Percolates d p :=
  xsch15_Percolates_of_percolationBound h

/-- The sharpest reduction of the base scale: it follows from the finite-volume
percolation estimate. -/
theorem xsch16_base_of_Percolates {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)]
    (h : xsch13_Percolates d p) : xsch8_Base d p :=
  xsch13_base_of_Percolates h

/-- The unconditional one-dimensional instance. -/
theorem xsch16_percolates_one {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)] (hp : 0 < p) :
    xsch13_Percolates 1 p :=
  xsch15_percolates_one hp

end Exploding
