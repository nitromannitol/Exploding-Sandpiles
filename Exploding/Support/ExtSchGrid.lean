/-
The failure of a near-cube box from its blocks.  A near-cube box of size `s` along `J` contains a
grid of `(s / Lb) ^ |J|` disjoint blocks of size `Lb`.  If one block is spanned and every layer
of the growth schedule from that block to the box is spanned along the other directions, the box
is spanned.  So the box fails only if no block is spanned, which has probability at most
`(1 - π) ^ N` by independence, or some layer of some schedule fails, which has probability at most
`N` times the union bound over the layers of one schedule.
-/
import Exploding.Support.ExtSchGrow
import Exploding.Support.ExtSchGrowProb
import Exploding.Support.ExtSchSeed

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

section Grid
variable {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)]

/-- **Failure of a near-cube box from its blocks.** -/
theorem xsr_fail_le_blocks {J : Finset (Fin d)} (hJ : J.Nonempty)
    {LO HI : Site d} {s Lb : ℕ} (hLb : 1 ≤ Lb) (hLbs : Lb ≤ s) (hR : xsb_Near J s LO HI)
    {π : ℝ}
    (hblock : ∀ lo hi : Site d, (∀ i ∈ J, hi i - lo i + 1 = (Lb : ℤ)) → (∀ i ∉ J, lo i = hi i) →
      π ≤ (xsch_mu d p).real {η | xsch_Sp J (xsb_box lo hi) η})
    {g : ℕ → ℝ} (hg0 : ∀ a, 0 ≤ g a)
    (hg : ∀ (J' : Finset (Fin d)) (lo hi : Site d) (a : ℕ), J'.card = J.card - 1 → 1 ≤ a →
      xsb_Near J' a lo hi →
        (xsch_mu d p).real {η | ¬ xsch_Sp J' (xsb_box lo hi) η} ≤ g a) :
    (xsch_mu d p).real {η | ¬ xsch_Sp J (xsb_box LO HI) η}
      ≤ (1 - π) ^ ((s / Lb) ^ J.card) +
        (((s / Lb) ^ J.card : ℕ) : ℝ) * ((J.card : ℝ) * ∑ a ∈ Finset.Icc Lb s, g a) := by
  let blo : (J → Fin (s / Lb)) → Site d := fun q => xsp_blo J LO Lb (fun j => (q j : ℕ))
  let bhi : (J → Fin (s / Lb)) → Site d := fun q => xsp_bhi J LO Lb (fun j => (q j : ℕ))
  have hbn : ∀ q, xsb_Near J Lb (blo q) (bhi q) := fun q => xsp_block_near J LO hLb _
  have hbsub : ∀ q, xsb_box (blo q) (bhi q) ⊆ xsb_box LO HI := fun q => xsp_block_subset hLb hR q
  have hle : ∀ q j, blo q j ≤ bhi q j := fun q j => by
    by_cases hj : j ∈ J
    · rcases (hbn q).1 j hj with h | h <;> omega
    · exact ((hbn q).2 j hj).le
  have hcorner : ∀ q j, LO j ≤ blo q j ∧ bhi q j ≤ HI j := fun q j =>
    ⟨(hbsub q (fun i => ⟨le_rfl, hle q i⟩) j).1, (hbsub q (fun i => ⟨hle q i, le_rfl⟩) j).2⟩
  let plan : (J → Fin (s / Lb)) → xss_Plan d := fun q => ⟨J, LO, HI, blo q, bhi q, Lb⟩
  have hvalid : ∀ q, xss_Valid (plan q) s := fun q => ⟨hJ, hR, hbn q, hcorner q, hLbs⟩
  set F : (J → Fin (s / Lb)) → Set (Site d → ℤ) :=
    fun q => {η | xsch_Sp J (xsb_box (blo q) (bhi q)) η} with hF
  set LF : (J → Fin (s / Lb)) → Set (Site d → ℤ) := fun q => {η | ¬ ∀ t < xss_steps (plan q) s,
    xsch_Sp ((plan q).J.erase (xss_dir (plan q) (hvalid q).1 t)) (xss_layer (plan q) t) η}
    with hLF
  have hLFle : ∀ q, (xsch_mu d p).real (LF q)
      ≤ (J.card : ℝ) * ∑ a ∈ Finset.Icc Lb s, g a := fun q =>
    xsr_layers_fail_le (p := p) (plan q) (hvalid q) hLb hg0 hg
  have hsub : {η | ¬ xsch_Sp J (xsb_box LO HI) η} ⊆ (⋂ q, (F q)ᶜ) ∪ ⋃ q, LF q := by
    intro η hη
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have h1' : ∃ q, η ∈ F q := by
      by_contra hh
      exact h1 (Set.mem_iInter.2 fun q hq => hh ⟨q, hq⟩)
    obtain ⟨q, hq⟩ := h1'
    have hl : ∀ t < xss_steps (plan q) s,
        xsch_Sp ((plan q).J.erase (xss_dir (plan q) (hvalid q).1 t)) (xss_layer (plan q) t) η := by
      by_contra hc
      exact h2 (Set.mem_iUnion.2 ⟨q, hc⟩)
    exact hη (xsr_top_of_layers (plan q) (hvalid q) hLb subset_rfl
      (fun x hx => xsch_Top_mono (hbsub q) (hq x hx)) hl)
  have hnone : (xsch_mu d p).real (⋂ q, (F q)ᶜ) ≤ (1 - π) ^ Fintype.card (J → Fin (s / Lb)) :=
    xsp_none_good_le (fun q => xsb_box (blo q) (bhi q)) (fun q => xsb_box_finite _ _)
      (fun _ _ h => xsp_block_disjoint hLb h) F (fun _ => xsch_det_Sp J _) fun q =>
      hblock (blo q) (bhi q)
        (fun i hi => by simp only [blo, bhi, xsp_blo, xsp_bhi, dif_pos hi]; ring)
        (hbn q).2
  have hunion : (xsch_mu d p).real (⋃ q, LF q)
      ≤ (((s / Lb) ^ J.card : ℕ) : ℝ) * ((J.card : ℝ) * ∑ a ∈ Finset.Icc Lb s, g a) := by
    calc (xsch_mu d p).real (⋃ q, LF q) ≤ ∑ q, (xsch_mu d p).real (LF q) :=
          measureReal_iUnion_fintype_le _
      _ ≤ ∑ _q : J → Fin (s / Lb), (J.card : ℝ) * ∑ a ∈ Finset.Icc Lb s, g a :=
          Finset.sum_le_sum fun q _ => hLFle q
      _ = (((s / Lb) ^ J.card : ℕ) : ℝ) * ((J.card : ℝ) * ∑ a ∈ Finset.Icc Lb s, g a) := by
          rw [Finset.sum_const, Finset.card_univ, xsp_card_grid, nsmul_eq_mul]
  rw [xsp_card_grid] at hnone
  calc (xsch_mu d p).real {η | ¬ xsch_Sp J (xsb_box LO HI) η}
      ≤ (xsch_mu d p).real ((⋂ q, (F q)ᶜ) ∪ ⋃ q, LF q) := measureReal_mono hsub
    _ ≤ (xsch_mu d p).real (⋂ q, (F q)ᶜ) + (xsch_mu d p).real (⋃ q, LF q) :=
        measureReal_union_le _ _
    _ ≤ _ := add_le_add hnone hunion

end Grid

end Exploding
