/-
The general block-size layer of the Schonmann argument.

A block is *good* when it is internally spanned, so it topples on its own.  The
goodness of pairwise disjoint blocks is independent (it reads the background only
inside the block), and a block of `k` sites is good with probability at least
`p ^ k` (it is good whenever all its sites carry `2d` chips).  These are the
per-block probability and independence inputs of the block-cover estimate; the
deterministic conversion from a good-block cover to spanning is
`xsch3_sp_of_block_family`, and the general block-size seed is `xsch2_sp_of_box`.
-/
import Exploding.Support.ExtSchProof5

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- **Good-block independence.**  Pairwise disjoint blocks are good independently. -/
theorem xsch6_sp_indep {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)] {ι : Type*}
    (B : ι → Set (Site d)) (s : Finset ι) (hfin : ∀ i, (B i).Finite)
    (hdisj : Pairwise (Function.onFun Disjoint B)) :
    (xsch_mu d p).real
        (⋂ i ∈ s, {η : Site d → ℤ | xsch_Sp (Finset.univ : Finset (Fin d)) (B i) η})
      = ∏ i ∈ s,
          (xsch_mu d p).real {η : Site d → ℤ | xsch_Sp (Finset.univ : Finset (Fin d)) (B i) η} := by
  have hE : ∀ i, xsch_Det (B i)
      {η : Site d → ℤ | xsch_Sp (Finset.univ : Finset (Fin d)) (B i) η} :=
    fun i => xsch_det_Sp (Finset.univ : Finset (Fin d)) (B i)
  exact xsch_indep_iInter B hfin hdisj _ hE s

/-- **Per-block probability.**  A block of `k` sites is internally spanned with
probability at least `p ^ k`. -/
theorem xsch6_sp_prob_ge {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)] (hd : 1 ≤ d)
    (B : Finset (Site d)) :
    p ^ B.card ≤
      (xsch_mu d p).real {η : Site d → ℤ |
        xsch_Sp (Finset.univ : Finset (Fin d)) (↑B : Set (Site d)) η} := by
  have hsub : xsch4_Occ B ⊆
      {η : Site d → ℤ | xsch_Sp (Finset.univ : Finset (Fin d)) (↑B : Set (Site d)) η} := by
    intro η hη
    exact xsch_Sp_of_occ fun x hx => hη x hx
  rw [← xsch4_occ_prob hd B]
  exact measureReal_mono hsub (measure_ne_top _ _)

/-- A block is internally spanned with probability at most one. -/
theorem xsch6_sp_prob_le_one {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)] (B : Set (Site d)) :
    (xsch_mu d p).real {η : Site d → ℤ |
      xsch_Sp (Finset.univ : Finset (Fin d)) B η} ≤ 1 := by
  calc (xsch_mu d p).real {η : Site d → ℤ |
        xsch_Sp (Finset.univ : Finset (Fin d)) B η}
      ≤ (xsch_mu d p).real Set.univ := measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)
    _ = 1 := by rw [measureReal_def, measure_univ, ENNReal.toReal_one]

end Exploding
