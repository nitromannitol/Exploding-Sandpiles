/-
The doubling recursion for the failure probability of a cube.  A box of size `s` splits into `2^d`
half-boxes, near-cubes of size `s / 2`.  If at most one half-box fails to be spanned the box is
spanned (L-shape lemma), so the box fails only if two distinct half-boxes fail; they are disjoint,
hence independent, and there are at most `(2^d)^2 = 4^d` pairs.
-/
import Exploding.Support.ExtSchLevel
import Exploding.Support.ExtSchHalf

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

section Double
variable {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)]

/-- The box fails to be spanned only if two distinct half-boxes both fail to be spanned. -/
theorem xsr2_fail_subset (hd : 1 ≤ d) {lo hi : Site d} (hn : ∀ i, 2 ≤ hi i - lo i + 1) :
    {η : Site d → ℤ | ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (xsb_box lo hi) η} ⊆
      ⋃ τ ∈ (Finset.univ : Finset ((Fin d → Bool) × (Fin d → Bool))).filter
          (fun τ => τ.1 ≠ τ.2),
        ({η | ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (xsh_sub lo hi τ.1) η} ∩
          {η | ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (xsh_sub lo hi τ.2) η}) := by
  intro η hη
  by_contra hnot
  apply hη
  have hpair : ∀ σ σ' : Fin d → Bool, σ ≠ σ' →
      ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (xsh_sub lo hi σ) η →
      ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (xsh_sub lo hi σ') η → False := by
    intro σ σ' hne h1 h2
    apply hnot
    simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(σ, σ'), hne, h1, h2⟩
  by_cases hex : ∃ σ1, ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (xsh_sub lo hi σ1) η
  · obtain ⟨σ0, hσ0⟩ := hex
    refine xsh_sp_of_all_but_one hd hn σ0 η fun σ hσ => ?_
    by_contra hbad
    exact hpair σ σ0 hσ hbad hσ0
  · push Not at hex
    exact xsh_sp_of_all_but_one hd hn (fun _ => true) η fun σ _ => hex σ

/-- The number of ordered pairs of distinct half-box labels is at most `4 ^ d`. -/
theorem xsr2_card_pairs :
    ((Finset.univ : Finset ((Fin d → Bool) × (Fin d → Bool))).filter
      (fun τ => τ.1 ≠ τ.2)).card ≤ 4 ^ d := by
  calc ((Finset.univ : Finset ((Fin d → Bool) × (Fin d → Bool))).filter
        (fun τ => τ.1 ≠ τ.2)).card
      ≤ (Finset.univ : Finset ((Fin d → Bool) × (Fin d → Bool))).card :=
        Finset.card_filter_le _ _
    _ = 2 ^ d * 2 ^ d := by
        simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin]
    _ = 4 ^ d := by rw [← mul_pow]; norm_num

/-- **Box version of the doubling recursion.** -/
theorem xsr2_box_bound (hd : 1 ≤ d) {s : ℕ} (hs : 2 ≤ s) {lo hi : Site d}
    (hR : xsb_Near (Finset.univ : Finset (Fin d)) s lo hi) :
    (xsch_mu d p).real {η | ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (xsb_box lo hi) η} ≤
      (4 : ℝ) ^ d * xsr_gbound d p d (s / 2) ^ 2 := by
  have hn : ∀ i, 2 ≤ hi i - lo i + 1 := by
    intro i
    have hs' : (2 : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs
    rcases hR.1 i (Finset.mem_univ i) with h | h <;> omega
  set pairs : Finset ((Fin d → Bool) × (Fin d → Bool)) :=
    (Finset.univ : Finset ((Fin d → Bool) × (Fin d → Bool))).filter (fun τ => τ.1 ≠ τ.2)
    with hpairs
  have hfac : ∀ σ : Fin d → Bool,
      (xsch_mu d p).real
        {η | ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (xsh_sub lo hi σ) η} ≤
        xsr_gbound d p d (s / 2) := fun σ =>
    xsr_gbound_ge (J' := Finset.univ) (by simp) (xsh_sub_near hs hR σ)
  have hterm : ∀ τ ∈ pairs,
      (xsch_mu d p).real
        ({η | ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (xsh_sub lo hi τ.1) η} ∩
          {η | ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (xsh_sub lo hi τ.2) η}) ≤
        xsr_gbound d p d (s / 2) ^ 2 := by
    intro τ hτ
    have hne : τ.1 ≠ τ.2 := (Finset.mem_filter.mp hτ).2
    have hind := xsch_indep_two (p := p) (xsb_box_finite _ _) (xsb_box_finite _ _)
      (xsh_sub_disjoint hn hne) (xsch_det_Sp Finset.univ (xsh_sub lo hi τ.1)).compl
      (xsch_det_Sp Finset.univ (xsh_sub lo hi τ.2)).compl
    rw [sq]
    refine hind.trans_le (mul_le_mul (hfac τ.1) (hfac τ.2) measureReal_nonneg ?_)
    exact (measureReal_nonneg).trans (hfac τ.1)
  calc (xsch_mu d p).real
        {η | ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (xsb_box lo hi) η}
      ≤ (xsch_mu d p).real
          (⋃ τ ∈ pairs,
            ({η | ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (xsh_sub lo hi τ.1) η} ∩
              {η | ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (xsh_sub lo hi τ.2) η})) :=
        measureReal_mono (xsr2_fail_subset hd hn) (measure_ne_top _ _)
    _ ≤ ∑ τ ∈ pairs, (xsch_mu d p).real
          ({η | ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (xsh_sub lo hi τ.1) η} ∩
            {η | ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (xsh_sub lo hi τ.2) η}) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _τ ∈ pairs, xsr_gbound d p d (s / 2) ^ 2 := Finset.sum_le_sum hterm
    _ = (pairs.card : ℝ) * xsr_gbound d p d (s / 2) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4 : ℝ) ^ d * xsr_gbound d p d (s / 2) ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        exact_mod_cast xsr2_card_pairs

/-- **Doubling recursion.** -/
theorem xsr_double_rec (hd : 1 ≤ d) {s : ℕ} (hs : 2 ≤ s) :
    xsr_gbound d p d s ≤ (4 : ℝ) ^ d * xsr_gbound d p d (s / 2) ^ 2 := by
  refine Real.sSup_le ?_ ?_
  · rintro x ⟨J', lo, hi, hJ', hn, rfl⟩
    have hJ : J' = Finset.univ := Finset.eq_univ_of_card J' (by simpa using hJ')
    subst hJ
    exact xsr2_box_bound hd hs hn
  · exact mul_nonneg (by positivity) (sq_nonneg _)
end Double

end Exploding
