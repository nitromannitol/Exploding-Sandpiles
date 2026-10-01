/-
The probabilistic block layer of the Schonmann argument.

A block is a finite set of sites that is *fully occupied* when every site
carries `2d` chips.  Because the background is a product measure, pairwise
disjoint blocks are independent, and the probability that a chosen family of
disjoint blocks is fully occupied is the product of the per-block probabilities
`p ^ |block|`.  These are the inputs of the block-cover estimate
`xsch3_PercolationBound`.
-/
import Exploding.Support.ExtSchProof3

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- The event that every site of the finite set `W` carries `2d` chips. -/
def xsch4_Occ (W : Finset (Site d)) : Set (Site d → ℤ) :=
  {η | ∀ x ∈ W, η x = 2 * (d : ℤ)}

theorem xsch4_det_occ (W : Finset (Site d)) :
    xsch_Det (↑W : Set (Site d)) (xsch4_Occ W) := by
  intro η η' h
  constructor <;> intro hη x hx
  · rw [← h x hx]; exact hη x hx
  · rw [h x hx]; exact hη x hx

variable {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)]

/-- **Per-block probability** (`xsch_occ_prob`): a finite block is fully occupied
with probability `p ^ |block|`. -/
theorem xsch4_occ_prob (hd : 1 ≤ d) (W : Finset (Site d)) :
    (xsch_mu d p).real (xsch4_Occ W) = p ^ W.card :=
  xsch_occ_prob hd W

/-- **Block independence and block-cover probability.**  For a pairwise disjoint
family of finite blocks, the probability that every block in a finite index set
`s` is fully occupied is the product of the per-block probabilities. -/
theorem xsch4_blocks_occ_prob {ι : Type*} (hd : 1 ≤ d) (W : ι → Finset (Site d))
    (hdisj : Pairwise (fun i j => Disjoint (W i) (W j))) (s : Finset ι) :
    (xsch_mu d p).real {η : Site d → ℤ | ∀ i ∈ s, η ∈ xsch4_Occ (W i)}
      = ∏ i ∈ s, p ^ (W i).card := by
  have hE : ∀ i, xsch_Det (↑(W i) : Set (Site d)) (xsch4_Occ (W i)) :=
    fun i => xsch4_det_occ (W i)
  have hdisj' : Pairwise (Function.onFun Disjoint (fun i => (↑(W i) : Set (Site d)))) := by
    intro i j hij
    exact Finset.disjoint_coe.mpr (hdisj hij)
  have hind := xsch_indep_iInter (d := d) (p := p) (fun i => (↑(W i) : Set (Site d)))
    (fun i => (W i).finite_toSet) hdisj' (fun i => xsch4_Occ (W i)) hE s
  rw [show {η : Site d → ℤ | ∀ i ∈ s, η ∈ xsch4_Occ (W i)}
      = ⋂ i ∈ s, xsch4_Occ (W i) from by ext η; simp]
  rw [hind]
  exact Finset.prod_congr rfl fun i _ => xsch4_occ_prob hd (W i)

end Exploding
