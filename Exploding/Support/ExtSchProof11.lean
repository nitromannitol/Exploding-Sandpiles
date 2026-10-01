/-
The Schonmann renormalization recursion, measure step.

`ExtSchProof10` supplies the geometric ingredients: the `2^d` corner sub-cubes
`xsch10_sub σ n` partition `cube d (2 n)`, they are pairwise disjoint, every one
has the same failure probability `xsch8_a d p n`, and if at most one of them is
bad then the whole cube is internally spanned (`xsch10_sp_of_all_but_one`).

Here we turn that into the recursion `a (2n) ≤ 2^{2d} a n ^ 2`.  The whole cube
can fail only if two distinct sub-cubes fail; a union bound over the
`2^d (2^d - 1)` ordered pairs together with the independence of the blocks
(`xsch_indep_two`, the two-block case of `xsch_indep_iInter`) gives the result.
-/
import Exploding.Support.ExtSchProof10

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- The empty cube is internally spanned, so `a 0 = 0`. -/
theorem xsch11_a_zero {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)] (hd : 1 ≤ d) : xsch8_a d p 0 = 0 := by
  rw [xsch8_a]
  have hempty : cube d 0 = (∅ : Set (Site d)) := by
    ext x
    constructor
    · intro hx
      have h1 := (hx ⟨0, hd⟩).1
      have h2 := (hx ⟨0, hd⟩).2
      omega
    · intro hx; exact hx.elim
  have : {η : Site d → ℤ | ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (cube d 0) η} = ∅ := by
    rw [hempty]
    ext η
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact fun x hx => hx.elim
  rw [this, measureReal_empty]

/-- **The renormalization recursion.**  Splitting `Q_{2n}^d` into its `2^d` corner
sub-cubes, at most one of which is bad, gives `a (2n) ≤ 2^{2d} a n ^ 2`. -/
theorem xsch11_recursion {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)] (hd : 1 ≤ d) (n : ℕ) (hn : 1 ≤ n) :
    xsch8_a d p (2 * n) ≤ (2 : ℝ) ^ (2 * d) * (xsch8_a d p n) ^ 2 := by
  set q : ℝ := xsch8_a d p n with hq
  set Bad : (Fin d → Bool) → Set (Site d → ℤ) :=
    fun σ => {η | ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (xsch10_sub σ n) η} with hBad
  have hsubfin : ∀ σ, (xsch10_sub σ n).Finite := fun σ =>
    (xsch10_cube_finite (d := d) (2 * n)).subset (xsch10_sub_subset (d := d) σ n)
  have hBadDet : ∀ σ, xsch_Det (xsch10_sub σ n) (Bad σ) := fun σ =>
    (xsch_det_Sp (Finset.univ : Finset (Fin d)) (xsch10_sub σ n)).compl
  have hBadProb : ∀ σ, (xsch_mu d p).real (Bad σ) = q := by
    intro σ
    rw [hBad, hq, xsch10_bad_prob n σ]
  have hBadProd : ∀ σ σ', σ ≠ σ' → (xsch_mu d p).real (Bad σ ∩ Bad σ') = q ^ 2 := by
    intro σ σ' hne
    have hdisj : Pairwise (Function.onFun Disjoint (fun i : Fin d → Bool => xsch10_sub i n)) :=
      fun i j hij => xsch10_sub_disjoint n hij
    have h := xsch_indep_iInter (d := d) (p := p) (fun i : Fin d → Bool => xsch10_sub i n) hsubfin hdisj
      (fun i => Bad i) hBadDet ({σ, σ'} : Finset (Fin d → Bool))
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
        = q ^ 2 := by
      rw [Finset.prod_insert (by simpa using hne), Finset.prod_singleton,
        hBadProb σ, hBadProb σ']
      ring
    rw [← hset, h, hprod]
  -- Any good cube contains no pair of bad sub-cubes, so the whole cube is spanned.
  have hcover : {η | ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (cube d (2 * n)) η} ⊆
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
      refine hη (xsch10_sp_of_all_but_one hd n hn σ0 η (fun σ hσ => ?_))
      by_contra hb
      exact hatmost σ0 σ (Ne.symm hσ) ⟨hσ0, hb⟩
    · simp only [not_exists] at hex
      exact hη (xsch10_sp_of_all_but_one hd n hn (fun _ => false) η
        (fun σ _ => by simpa [hBad] using hex σ))
  have hbound : (xsch_mu d p).real
      (⋃ σ : Fin d → Bool, ⋃ σ' : Fin d → Bool,
        (if σ ≠ σ' then Bad σ ∩ Bad σ' else (∅ : Set (Site d → ℤ))))
      ≤ (2 : ℝ) ^ (2 * d) * q ^ 2 := by
    calc (xsch_mu d p).real (⋃ σ : Fin d → Bool, ⋃ σ' : Fin d → Bool,
            (if σ ≠ σ' then Bad σ ∩ Bad σ' else (∅ : Set (Site d → ℤ))))
        ≤ ∑ σ : Fin d → Bool, (xsch_mu d p).real (⋃ σ' : Fin d → Bool,
            (if σ ≠ σ' then Bad σ ∩ Bad σ' else (∅ : Set (Site d → ℤ)))) :=
          measureReal_iUnion_fintype_le _
      _ ≤ ∑ σ : Fin d → Bool, ∑ σ' : Fin d → Bool,
            (xsch_mu d p).real (if σ ≠ σ' then Bad σ ∩ Bad σ' else (∅ : Set (Site d → ℤ))) :=
          Finset.sum_le_sum fun σ _ => measureReal_iUnion_fintype_le _
      _ = ∑ σ : Fin d → Bool, ∑ σ' : Fin d → Bool, (if σ ≠ σ' then q ^ 2 else 0) := by
          refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun σ' _ => ?_
          by_cases h : σ = σ'
          · rw [if_neg (fun hh => hh h), if_neg (fun hh => hh h), measureReal_empty]
          · rw [if_pos h, if_pos h, hBadProd σ σ' h]
      _ ≤ ∑ _σ : Fin d → Bool, ∑ _σ' : Fin d → Bool, q ^ 2 := by
          refine Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun σ' _ => ?_
          by_cases h : σ = σ'
          · rw [if_neg (fun hh => hh h)]; exact sq_nonneg q
          · rw [if_pos h]
      _ = (2 : ℝ) ^ (2 * d) * q ^ 2 := by
          have hcard : Fintype.card (Fin d → Bool) = 2 ^ d := by
            rw [Fintype.card_fun]; simp [Fintype.card_fin]
          rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, hcard]
          rw [nsmul_eq_mul, nsmul_eq_mul]
          push_cast
          rw [← mul_assoc, ← pow_add, show d + d = 2 * d by omega]
  rw [xsch8_a]
  exact (measureReal_mono hcover (measure_ne_top _ _)).trans hbound

/-- The recursion as stated by `xsch8_Recursion`, at every scale. -/
theorem xsch11_xsch8_Recursion {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)] (hd : 1 ≤ d) :
    xsch8_Recursion d p := by
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [xsch11_a_zero hd]
    simp
  · exact xsch11_recursion hd n hn

end Exploding
