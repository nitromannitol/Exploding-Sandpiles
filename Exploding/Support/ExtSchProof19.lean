/-
Measure assembly for the non-uniform corner boxes.

`xsch18_sp_of_all_but_one` gives the deterministic L-shape for the `n/2`-split of
`Q_n`.  Here we assemble the measure recursion

  `a n ≤ 2^{2d} · (a (n/2) ∨ a (n/2+1))^2`,

conditional on the single new input `xsch19_BoxBound`: a box of the `n/2`-split
fails to be internally spanned with probability at most `a` at its shorter side.

Numerically the box bound holds for every box whose shorter side is at least `2`
(it fails only for the degenerate single-row `1 × 2` box, where the failure
probability `1 - p^2` exceeds `a 1 = 1 - p`).  Isolating it makes the remaining
probabilistic ingredient of the all-scales recursion precise.  This file does not
claim `xsch13_Percolates`.
-/
import Exploding.Support.ExtSchProof18

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- The remaining input of the all-scales measure recursion: every box of the
`n/2`-split fails with probability at most `a` at its shorter side. -/
def xsch19_BoxBound (d : ℕ) (p : ℝ) : Prop :=
  ∀ (n : ℕ) (σ : Fin d → Bool),
    (xsch_mu d p).real {η | ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (xsch18_sub σ n) η}
      ≤ max (xsch8_a d p (n / 2)) (xsch8_a d p (n / 2 + 1))

/-- The boxes of the `n/2`-split are pairwise disjoint. -/
theorem xsch18_sub_disjoint (n : ℕ) {σ σ' : Fin d → Bool} (h : σ ≠ σ') :
    Disjoint (xsch18_sub σ n) (xsch18_sub σ' n) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  apply h
  funext j
  by_cases hj : σ j = σ' j
  · exact hj
  · exfalso
    have h1 := (hx j).1
    have h2 := (hx j).2
    have h3 := (hx' j).1
    have h4 := (hx' j).2
    simp only [xsch18_lo, xsch18_hi] at h1 h2 h3 h4
    cases hσ : σ j <;> cases hσ' : σ' j <;> simp_all <;> omega

/-- **All-scales measure recursion**, conditional on the box bound. -/
theorem xsch19_recursion_of_boxBound {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)]
    (hd : 1 ≤ d) (hbox : xsch19_BoxBound d p) (n : ℕ) (hn : 2 ≤ n) :
    xsch8_a d p n ≤ (2 : ℝ) ^ (2 * d) *
      (max (xsch8_a d p (n / 2)) (xsch8_a d p (n / 2 + 1))) ^ 2 := by
  set K : ℝ := max (xsch8_a d p (n / 2)) (xsch8_a d p (n / 2 + 1)) with hK
  set Bad : (Fin d → Bool) → Set (Site d → ℤ) :=
    fun σ => {η | ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (xsch18_sub σ n) η} with hBad
  have hKnn : 0 ≤ K := by
    rw [hK]; exact le_max_of_le_left measureReal_nonneg
  have hsubfin : ∀ σ, (xsch18_sub σ n).Finite := fun σ =>
    (xsch10_cube_finite (d := d) n).subset (xsch18_sub_subset σ n)
  have hBadDet : ∀ σ, xsch_Det (xsch18_sub σ n) (Bad σ) := fun σ =>
    (xsch_det_Sp (Finset.univ : Finset (Fin d)) (xsch18_sub σ n)).compl
  have hBadProb : ∀ σ, (xsch_mu d p).real (Bad σ) ≤ K := by
    intro σ
    rw [hK, hBad]
    exact hbox n σ
  have hBadProd : ∀ σ σ', σ ≠ σ' → (xsch_mu d p).real (Bad σ ∩ Bad σ') ≤ K ^ 2 := by
    intro σ σ' hne
    have hdisj : Pairwise (Function.onFun Disjoint (fun i : Fin d → Bool => xsch18_sub i n)) :=
      fun i j hij => xsch18_sub_disjoint n hij
    have hend := xsch_indep_iInter (d := d) (p := p) (fun i : Fin d → Bool => xsch18_sub i n)
      hsubfin hdisj (fun i => Bad i) hBadDet ({σ, σ'} : Finset (Fin d → Bool))
    have hset : (⋂ i ∈ ({σ, σ'} : Finset (Fin d → Bool)), Bad i) = Bad σ ∩ Bad σ' := by
      ext η
      simp only [Set.mem_iInter, Finset.mem_insert, Finset.mem_singleton,
        Set.mem_inter_iff]
      constructor
      · intro hh; exact ⟨hh σ (Or.inl rfl), hh σ' (Or.inr rfl)⟩
      · rintro ⟨h1, h2⟩ i (rfl | rfl)
        · exact h1
        · exact h2
    have hprod : (∏ i ∈ ({σ, σ'} : Finset (Fin d → Bool)), (xsch_mu d p).real (Bad i))
        ≤ K ^ 2 := by
      rw [Finset.prod_insert (by simpa using hne), Finset.prod_singleton]
      have h1 := hBadProb σ
      have h2 := hBadProb σ'
      have h3 : (0 : ℝ) ≤ (xsch_mu d p).real (Bad σ) := measureReal_nonneg
      have h4 : (0 : ℝ) ≤ (xsch_mu d p).real (Bad σ') := measureReal_nonneg
      nlinarith [h1, h2, h3, h4, hKnn]
    rw [← hset, hend]
    exact hprod
  have hcover : {η | ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (cube d n) η} ⊆
      ⋃ σ : Fin d → Bool, ⋃ σ' : Fin d → Bool,
        (if σ ≠ σ' then Bad σ ∩ Bad σ' else (∅ : Set (Site d → ℤ))) := by
    intro η hη
    by_contra hcon
    have hatmost : ∀ σ σ', σ ≠ σ' → ¬ (η ∈ Bad σ ∧ η ∈ Bad σ') := by
      intro σ σ' hne hboth
      apply hcon
      exact Set.mem_iUnion.mpr ⟨σ, Set.mem_iUnion.mpr ⟨σ', by rwa [if_pos hne]⟩⟩
    by_cases hex : ∃ σ, η ∈ Bad σ
    · obtain ⟨σ0, hσ0⟩ := hex
      refine hη (xsch18_sp_of_all_but_one hd n hn σ0 η (fun σ hσ => ?_))
      by_contra hb
      exact hatmost σ0 σ (Ne.symm hσ) ⟨hσ0, hb⟩
    · simp only [not_exists] at hex
      exact hη (xsch18_sp_of_all_but_one hd n hn (fun _ => false) η
        (fun σ _ => by simpa [hBad] using hex σ))
  have hbound : (xsch_mu d p).real
      (⋃ σ : Fin d → Bool, ⋃ σ' : Fin d → Bool,
        (if σ ≠ σ' then Bad σ ∩ Bad σ' else (∅ : Set (Site d → ℤ))))
      ≤ (2 : ℝ) ^ (2 * d) * K ^ 2 := by
    calc (xsch_mu d p).real (⋃ σ : Fin d → Bool, ⋃ σ' : Fin d → Bool,
            (if σ ≠ σ' then Bad σ ∩ Bad σ' else (∅ : Set (Site d → ℤ))))
        ≤ ∑ σ : Fin d → Bool, (xsch_mu d p).real (⋃ σ' : Fin d → Bool,
            (if σ ≠ σ' then Bad σ ∩ Bad σ' else (∅ : Set (Site d → ℤ)))) :=
          measureReal_iUnion_fintype_le _
      _ ≤ ∑ σ : Fin d → Bool, ∑ σ' : Fin d → Bool,
            (xsch_mu d p).real (if σ ≠ σ' then Bad σ ∩ Bad σ' else (∅ : Set (Site d → ℤ))) :=
          Finset.sum_le_sum fun σ _ => measureReal_iUnion_fintype_le _
      _ ≤ ∑ σ : Fin d → Bool, ∑ σ' : Fin d → Bool, (if σ ≠ σ' then K ^ 2 else 0) := by
          refine Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun σ' _ => ?_
          by_cases h : σ = σ'
          · rw [if_neg (fun hh => hh h), if_neg (fun hh => hh h), measureReal_empty]
          · rw [if_pos h, if_pos h]
            exact hBadProd σ σ' h
      _ ≤ ∑ _σ : Fin d → Bool, ∑ _σ' : Fin d → Bool, K ^ 2 := by
          refine Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun σ' _ => ?_
          by_cases h : σ = σ'
          · rw [if_neg (fun hh => hh h)]; exact sq_nonneg K
          · rw [if_pos h]
      _ = (2 : ℝ) ^ (2 * d) * K ^ 2 := by
          have hcard : Fintype.card (Fin d → Bool) = 2 ^ d := by
            rw [Fintype.card_fun]; simp [Fintype.card_fin]
          rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, hcard]
          rw [nsmul_eq_mul, nsmul_eq_mul]
          push_cast
          rw [← mul_assoc, ← pow_add, show d + d = 2 * d by omega]
  rw [xsch8_a]
  exact (measureReal_mono hcover (measure_ne_top _ _)).trans hbound

end Exploding
