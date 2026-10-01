/-
Schonmann renormalization recursion — capstone.

This file finishes the second remaining claim of the renormalization argument,
`xsch8_Recursion`: `a (2n) ≤ 2^{2d} a n ^ 2`, where `a n = P(Q_n^d not spanned)`.

The building blocks are already in place: the `2^d` corner sub-cubes
`xsch10_sub σ n` (with covering `xsch10_sub_cover`, pairwise disjointness
`xsch10_sub_disjoint`, and containment `xsch10_sub_subset`), the mixed-face
corner-growth seed `xsch9_corner_growth`, pair independence of disjoint blocks
`xsch_indep_iInter`, and the translation invariance of the field
`xsch10_map_shift`, which makes every sub-cube equally likely to fail
(`xsch10_bad_prob`).

We prove here, under the `xsch12_` prefix:

* `xsch12_sp_of_all_but_one`, the **L-shape lemma**: if at most one corner
  sub-cube fails to be internally spanned, then the whole cube is.  The chosen
  face of `Q_{2n}` in each direction lies inside a good sub-cube, hence is
  toppled, and `xsch9_corner_growth` fills the cube.
* `xsch12_recursion`, the **measure recursion**: the cube can fail only if two
  distinct sub-cubes fail, and a union bound over the `2^d (2^d - 1)` ordered
  pairs, with pair independence from `xsch_indep_iInter`, gives the bound.
* `xsch12_xsch8_Recursion`, the packaged `xsch8_Recursion d p`.
-/
import Exploding.Support.ExtSchProof10

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- **L-shape lemma.**  If at most one of the `2^d` corner sub-cubes of
`cube d (2n)` fails to be internally spanned, then `cube d (2n)` is spanned. -/
theorem xsch12_sp_of_all_but_one (hd : 1 ≤ d) (n : ℕ) (hn : 1 ≤ n) (σ0 : Fin d → Bool)
    (η : Site d → ℤ)
    (hgood : ∀ σ, σ ≠ σ0 → xsch_Sp (Finset.univ : Finset (Fin d)) (xsch10_sub σ n) η) :
    xsch_Sp (Finset.univ : Finset (Fin d)) (cube d (2 * n)) η := by
  refine xsch9_corner_growth hd (2 * n) σ0 η ?_
  intro x hx hface
  obtain ⟨i, hfi⟩ := hface
  set σ' : Fin d → Bool := fun j => decide (n < x j) with hσ'
  have hne : σ' ≠ σ0 := by
    intro heq
    have hii : σ' i = σ0 i := by rw [heq]
    rcases hfi with ⟨hci, hxi⟩ | ⟨hci, hxi⟩
    · have : σ' i = false := by
        simp only [hσ', hxi, decide_eq_false_iff_not]; omega
      rw [this] at hii; rw [hci] at hii; exact Bool.noConfusion hii
    · have : σ' i = true := by
        simp only [hσ', hxi]; exact decide_eq_true (by omega)
      rw [this] at hii
      rw [hci] at hii
      exact Bool.noConfusion hii
  have htop := hgood σ' hne x (xsch10_mem_sub_of n x hx)
  exact xsch_Top_mono (xsch10_sub_subset σ' n) htop

/-- The empty cube is internally spanned, so `a 0 = 0`. -/
theorem xsch12_a_zero {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)] (hd : 1 ≤ d) : xsch8_a d p 0 = 0 := by
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

/-- **The measure recursion.**  Splitting `Q_{2n}^d` into its `2^d` corner
sub-cubes, at most one of which is bad, gives `a (2n) ≤ 2^{2d} a n ^ 2`. -/
theorem xsch12_recursion {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)] (hd : 1 ≤ d) (n : ℕ) (hn : 1 ≤ n) :
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
    have h := xsch_indep_iInter (d := d) (p := p) (fun i : Fin d → Bool => xsch10_sub i n)
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
        = q ^ 2 := by
      rw [Finset.prod_insert (by simpa using hne), Finset.prod_singleton,
        hBadProb σ, hBadProb σ']
      ring
    rw [← hset, h, hprod]
  -- The whole cube can fail only if two distinct sub-cubes fail.
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
      refine hη (xsch12_sp_of_all_but_one hd n hn σ0 η (fun σ hσ => ?_))
      by_contra hb
      exact hatmost σ0 σ (Ne.symm hσ) ⟨hσ0, hb⟩
    · simp only [not_exists] at hex
      exact hη (xsch12_sp_of_all_but_one hd n hn (fun _ => false) η
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

/-- `xsch8_Recursion` follows from the measure recursion, the scale `n = 0` being
trivial because the empty cube is internally spanned. -/
theorem xsch12_xsch8_Recursion {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)] (hd : 1 ≤ d) :
    xsch8_Recursion d p := by
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [xsch12_a_zero hd]
    simp
  · exact xsch12_recursion hd n hn

end Exploding
