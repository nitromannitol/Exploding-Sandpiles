/-
Assembly of the block-percolation estimate.

The pieces are in place: `xsch3_sp_of_block_family` converts a family of
internally-spanned blocks covering the lower boundary of `Q_n^d` into
`xsch_Sp Finset.univ (cube d n)`; `xsch6_sp_indep` says pairwise disjoint good
blocks are independent; `xsch6_sp_prob_ge` (from `xsch_occ_prob`) bounds the
per-block probability below by `p ^ |block|`; and `xsch4_blocks_occ_prob` gives
the block-cover probability for fully occupied blocks.  What remains is the
coarse percolation estimate `xsch7_BlockPercolation`: a good-block cover exists
with probability `1 - c exp(-C n)`.  This file isolates that estimate and shows
it implies `xsch3_PercolationBound` and hence `SchonmannBootstrap`.
-/
import Exploding.Support.ExtSchProof6

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- The event that the lower boundary of `Q_n^d` is covered by internally-spanned
blocks contained in the cube. -/
def xsch7_BlockCover (d : ℕ) (n : ℕ) : Set (Site d → ℤ) :=
  {η | ∃ (ι : Type) (_ : Fintype ι) (R : ι → Set (Site d)),
    (∀ i, xsch_Sp (Finset.univ : Finset (Fin d)) (R i) η) ∧
      (⋃ i, R i) ⊆ cube d n ∧
      (∀ x ∈ cube d n, (∃ j, x j = 1) → x ∈ ⋃ i, R i)}

/-- A block cover spans the cube (`xsch3_sp_of_block_family`). -/
theorem xsch7_sp_of_blockCover {η : Site d → ℤ} {n : ℕ} (h : η ∈ xsch7_BlockCover d n) :
    xsch_Sp (Finset.univ : Finset (Fin d)) (cube d n) η := by
  obtain ⟨ι, _, R, hgood, hsub, hfaces⟩ := h
  exact xsch3_sp_of_block_family R η n hgood hsub hfaces

/-- **The coarse good-block percolation estimate** (a hypothesis of this route).  A
good-block cover of the lower boundary exists with probability `1 - c exp(-C n)`. -/
def xsch7_BlockPercolation (d : ℕ) (p : ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ,
    (xsch_mu d p).real {η : Site d → ℤ | η ∉ xsch7_BlockCover d n} ≤
      c * Real.exp (-(C * (n : ℝ)))

/-- **Assembly.**  The block-percolation estimate implies the percolation
estimate `xsch3_PercolationBound`; the proof is exactly the deterministic
coverage-to-spanning conversion. -/
theorem xsch7_percolation_of_blockPercolation
    (h : ∀ d : ℕ, 1 ≤ d → ∀ p : ℝ, 0 < p → p ≤ 1 → xsch7_BlockPercolation d p) :
    ∀ d : ℕ, 1 ≤ d → ∀ p : ℝ, 0 < p → p ≤ 1 → xsch3_PercolationBound d p := by
  intro d hd p hp hp1
  obtain ⟨c, C, hc, hC, hbound⟩ := h d hd p hp hp1
  refine ⟨c, C, hc, hC, fun n => ?_⟩
  haveI : Fact (0 ≤ p ∧ p ≤ 1) := ⟨⟨hp.le, hp1⟩⟩
  have hsub : {η : Site d → ℤ | ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (cube d n) η}
      ⊆ {η : Site d → ℤ | η ∉ xsch7_BlockCover d n} := by
    intro η hη hcov
    exact hη (xsch7_sp_of_blockCover hcov)
  exact le_trans (measureReal_mono hsub (measure_ne_top _ _)) (hbound n)

/-- **Assembly into the target.** -/
theorem xsch7_schonmann_of_blockPercolation
    (h : ∀ d : ℕ, 1 ≤ d → ∀ p : ℝ, 0 < p → p ≤ 1 → xsch7_BlockPercolation d p) :
    Exploding.External.SchonmannBootstrap :=
  xsch3_schonmann_of_percolation (xsch7_percolation_of_blockPercolation h)

end Exploding
