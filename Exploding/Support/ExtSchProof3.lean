/-
The final step of the Schonmann bootstrap argument.

The deterministic content is unconditional: a family of internally-spanned blocks
whose union covers the lower boundary of `Q_n^d` spans `Q_n^d`.  The probabilistic
content is the percolation estimate that such a cover exists with probability
`1 - c exp(-C n)`; it is isolated as `xsch3_PercolationBound`, and
`xsch3_schonmann_of_percolation` reduces the target `SchonmannBootstrap` to it.
-/
import Exploding.Support.ExtSchProof2
import Exploding.Support.ExtSchProb

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- **Deterministic conversion.**  A union of internally-spanned blocks that
covers the lower boundary of the cube is internally spanned. -/
theorem xsch3_sp_of_block_family {ι : Type*} (R : ι → Set (Site d)) (η : Site d → ℤ) (n : ℕ)
    (h : ∀ i, xsch_Sp (Finset.univ : Finset (Fin d)) (R i) η)
    (hsub : (⋃ i, R i) ⊆ cube d n)
    (hfaces : ∀ x ∈ cube d n, (∃ j, x j = 1) → x ∈ ⋃ i, R i) :
    xsch_Sp (Finset.univ : Finset (Fin d)) (cube d n) η := by
  have hU : xsch_Sp (Finset.univ : Finset (Fin d)) (⋃ i, R i) η := xsch2_sp_union R η h
  exact xsch2_sp_of_faces n η fun x hx hface =>
    xsch_Top_mono hsub (hU x (hfaces x hx hface))

/-- **The percolation estimate of the block argument (the remaining gap).**
Good blocks percolate: the cube is spanned with probability `1 - c exp(-C n)`. -/
def xsch3_PercolationBound (d : ℕ) (p : ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ,
    (xsch_mu d p).real {η : Site d → ℤ |
      ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (cube d n) η} ≤
        c * Real.exp (-(C * (n : ℝ)))

/-- **Reduction of `SchonmannBootstrap` to the percolation estimate.** -/
theorem xsch3_schonmann_of_percolation
    (h : ∀ d : ℕ, 1 ≤ d → ∀ p : ℝ, 0 < p → p < 1 → xsch3_PercolationBound d p) :
    Exploding.External.SchonmannBootstrap := by
  intro d hd p hp hp1
  obtain ⟨c, C, hc, hC, hbound⟩ := h d hd p hp hp1
  haveI : Fact (0 ≤ p ∧ p ≤ 1) := ⟨⟨hp.le, hp1.le⟩⟩
  refine ⟨c, C, hc, hC, fun n => ?_⟩
  exact xsch_final (d := d) (p := p) n (c * Real.exp (-(C * (n : ℝ)))) (hbound n)

end Exploding
