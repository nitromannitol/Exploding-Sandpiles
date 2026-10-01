/-
The mixed-face corner-growth seed.

For a choice `c` of one face of `cube d n` in each direction (the lower face in
direction `i` if `c i`, the upper one otherwise), if the chosen face is toppled
in every direction, then the whole cube is spanned.  The toppling spreads from
the chosen corner by induction on `xsch9_dist c n x = ∑ i (x i - 1 or n - x i)`.
-/
import Exploding.Support.ExtSchProof2

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The distance to the corner selected by `c`. -/
def xsch9_dist (c : Fin d → Bool) (n : ℕ) (x : Site d) : ℤ :=
  ∑ i, (if c i = true then x i - 1 else (n : ℤ) - x i)

/-- `x` lies on a face chosen by `c`: the lower face in direction `i` if `c i`,
the upper face otherwise. -/
def xsch9_onFace (c : Fin d → Bool) (n : ℕ) (x : Site d) : Prop :=
  ∃ i, (c i = true ∧ x i = 1) ∨ (c i = false ∧ x i = (n : ℤ))

theorem xsch9_coord_self (x : Site d) (i : Fin d) (c : Fin d → Bool) :
    (x + xsch_dir (i, Bool.not (c i))) i =
      (if c i = true then x i - 1 else x i + 1) := by
  by_cases hci : c i = true
  · simp [xsch_dir, hci, unit, sub_eq_add_neg]
  · have hci' : c i = false := by cases h : c i <;> simp_all
    simp [xsch_dir, hci', unit]

theorem xsch9_coord_ne (x : Site d) (i j : Fin d) (c : Fin d → Bool) (hji : j ≠ i) :
    (x + xsch_dir (i, Bool.not (c i))) j = x j := by
  by_cases hci : c i = true
  · simp [xsch_dir, hci, unit, Pi.single_eq_of_ne hji]
  · have hci' : c i = false := by cases h : c i <;> simp_all
    simp [xsch_dir, hci', unit, Pi.single_eq_of_ne hji]

/-- **Mixed-face corner-growth seed.**  If in each direction the chosen face of
`cube d n` is toppled, then the cube is spanned. -/
theorem xsch9_corner_growth (hd : 1 ≤ d) (n : ℕ) (c : Fin d → Bool) (η : Site d → ℤ)
    (h : ∀ x ∈ cube d n, xsch9_onFace c n x →
      xsch_Top (Finset.univ : Finset (Fin d)) (cube d n) η x) :
    xsch_Sp (Finset.univ : Finset (Fin d)) (cube d n) η := by
  intro x hx
  have hdnn : ∀ y ∈ cube d n, 0 ≤ xsch9_dist c n y := by
    intro y hy
    rw [xsch9_dist]
    refine Finset.sum_nonneg fun i _ => ?_
    by_cases hci : c i = true
    · rw [if_pos hci]; have := (hy i).1; omega
    · rw [if_neg hci]; have := (hy i).2; omega
  have key : ∀ s : ℕ, ∀ x : Site d, x ∈ cube d n → (xsch9_dist c n x).toNat = s →
      xsch_Top (Finset.univ : Finset (Fin d)) (cube d n) η x := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro x hx hs
      by_cases hface : xsch9_onFace c n x
      · exact h x hx hface
      · have hmem : ∀ i, x + xsch_dir (i, Bool.not (c i)) ∈ cube d n := by
          intro i j
          by_cases hji : j = i
          · rw [hji, xsch9_coord_self]
            by_cases hci : c i = true
            · rw [if_pos hci]
              have hxi : x i ≠ 1 := by intro h1; exact hface ⟨i, Or.inl ⟨hci, h1⟩⟩
              have h2 : 2 ≤ x i := by have := (hx i).1; omega
              have h3 : x i ≤ (n : ℤ) := (hx i).2
              exact ⟨by omega, by omega⟩
            · rw [if_neg hci]
              have hci' : c i = false := by cases h : c i <;> simp_all
              have hxi : x i ≠ (n : ℤ) := by intro h1; exact hface ⟨i, Or.inr ⟨hci', h1⟩⟩
              have h1 : 1 ≤ x i := (hx i).1
              have h2 : x i ≤ (n : ℤ) - 1 := by have := (hx i).2; omega
              exact ⟨by omega, by omega⟩
          · rw [xsch9_coord_ne x i j c hji]; exact hx j
        have hpos : 1 ≤ xsch9_dist c n x := by
          have ht : ∀ i, 1 ≤ (if c i = true then x i - 1 else (n : ℤ) - x i) := by
            intro i
            by_cases hci : c i = true
            · rw [if_pos hci]
              have hxi : x i ≠ 1 := by intro h1; exact hface ⟨i, Or.inl ⟨hci, h1⟩⟩
              have := (hx i).1; omega
            · rw [if_neg hci]
              have hci' : c i = false := by cases h : c i <;> simp_all
              have hxi : x i ≠ (n : ℤ) := by intro h1; exact hface ⟨i, Or.inr ⟨hci', h1⟩⟩
              have := (hx i).2; omega
          have hdle : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
          calc (1 : ℤ) ≤ (d : ℤ) := hdle
            _ = ∑ _i : Fin d, (1 : ℤ) := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
            _ ≤ ∑ i, (if c i = true then x i - 1 else (n : ℤ) - x i) :=
                Finset.sum_le_sum (fun i _ => ht i)
            _ = xsch9_dist c n x := by rw [xsch9_dist]
        have hdec : ∀ i, (xsch9_dist c n (x + xsch_dir (i, Bool.not (c i)))).toNat <
            (xsch9_dist c n x).toNat := by
          intro i
          have hnn := hdnn x hx
          have hdeq : xsch9_dist c n (x + xsch_dir (i, Bool.not (c i))) =
              xsch9_dist c n x - 1 := by
            have hsub : (∑ j, ((if c j = true then x j - 1 else (n : ℤ) - x j)
                - (if c j = true then (x + xsch_dir (i, Bool.not (c i))) j - 1
                    else (n : ℤ) - (x + xsch_dir (i, Bool.not (c i))) j))) = 1 := by
              rw [Finset.sum_eq_single i]
              · by_cases hci : c i = true
                · rw [xsch9_coord_self]; simp [hci, sub_eq_add_neg]
                · rw [xsch9_coord_self]; simp [hci, sub_eq_add_neg]; ring
              · intro j _ hji
                rw [xsch9_coord_ne x i j c hji]
                by_cases hcj : c j = true <;> simp [hcj]
              · intro hi; exact absurd (Finset.mem_univ i) hi
            rw [xsch9_dist, xsch9_dist]
            rw [Finset.sum_sub_distrib] at hsub
            linarith
          rw [hdeq]
          have h1 : ((xsch9_dist c n x - 1).toNat : ℤ) = xsch9_dist c n x - 1 :=
            Int.toNat_of_nonneg (by omega)
          have h2 : ((xsch9_dist c n x).toNat : ℤ) = xsch9_dist c n x :=
            Int.toNat_of_nonneg hnn
          omega
        refine xsch_Top.nbr (Finset.univ.image (fun i : Fin d => (i, Bool.not (c i)))) hx ?_ ?_ ?_
        · intro s hs
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hs
          obtain ⟨i, rfl⟩ := hs
          exact Finset.mem_univ i
        · rw [Finset.card_image_of_injective (Finset.univ : Finset (Fin d))
            (fun i j hij => congrArg Prod.fst hij)]
        · intro s hs
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hs
          obtain ⟨i, rfl⟩ := hs
          exact ih _ (by have := hdec i; rw [hs] at this; exact this) _ (hmem i) rfl
  exact key _ x hx rfl

/-- **Ambient mixed-face growth.**  Same seed, but the chosen faces only need to
topple in a larger frozen set `B ⊇ cube d n`; the toppling of the cube then also
happens inside `B`. -/
theorem xsch9_corner_growth_ambient (hd : 1 ≤ d) (n : ℕ) (c : Fin d → Bool) (B : Set (Site d))
    (hB : cube d n ⊆ B) (η : Site d → ℤ)
    (h : ∀ x ∈ cube d n, xsch9_onFace c n x →
      xsch_Top (Finset.univ : Finset (Fin d)) B η x) :
    ∀ x ∈ cube d n, xsch_Top (Finset.univ : Finset (Fin d)) B η x := by
  intro x hx
  have hdnn : ∀ y ∈ cube d n, 0 ≤ xsch9_dist c n y := by
    intro y hy
    rw [xsch9_dist]
    refine Finset.sum_nonneg fun i _ => ?_
    by_cases hci : c i = true
    · rw [if_pos hci]; have := (hy i).1; omega
    · rw [if_neg hci]; have := (hy i).2; omega
  have key : ∀ s : ℕ, ∀ x : Site d, x ∈ cube d n → (xsch9_dist c n x).toNat = s →
      xsch_Top (Finset.univ : Finset (Fin d)) B η x := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro x hx hs
      by_cases hface : xsch9_onFace c n x
      · exact h x hx hface
      · have hmem : ∀ i, x + xsch_dir (i, Bool.not (c i)) ∈ cube d n := by
          intro i j
          by_cases hji : j = i
          · rw [hji, xsch9_coord_self]
            by_cases hci : c i = true
            · rw [if_pos hci]
              have hxi : x i ≠ 1 := by intro h1; exact hface ⟨i, Or.inl ⟨hci, h1⟩⟩
              have h2 : 2 ≤ x i := by have := (hx i).1; omega
              have h3 : x i ≤ (n : ℤ) := (hx i).2
              exact ⟨by omega, by omega⟩
            · rw [if_neg hci]
              have hci' : c i = false := by cases h : c i <;> simp_all
              have hxi : x i ≠ (n : ℤ) := by intro h1; exact hface ⟨i, Or.inr ⟨hci', h1⟩⟩
              have h1 : 1 ≤ x i := (hx i).1
              have h2 : x i ≤ (n : ℤ) - 1 := by have := (hx i).2; omega
              exact ⟨by omega, by omega⟩
          · rw [xsch9_coord_ne x i j c hji]; exact hx j
        have hpos : 1 ≤ xsch9_dist c n x := by
          have ht : ∀ i, 1 ≤ (if c i = true then x i - 1 else (n : ℤ) - x i) := by
            intro i
            by_cases hci : c i = true
            · rw [if_pos hci]
              have hxi : x i ≠ 1 := by intro h1; exact hface ⟨i, Or.inl ⟨hci, h1⟩⟩
              have := (hx i).1; omega
            · rw [if_neg hci]
              have hci' : c i = false := by cases h : c i <;> simp_all
              have hxi : x i ≠ (n : ℤ) := by intro h1; exact hface ⟨i, Or.inr ⟨hci', h1⟩⟩
              have := (hx i).2; omega
          have hdle : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
          calc (1 : ℤ) ≤ (d : ℤ) := hdle
            _ = ∑ _i : Fin d, (1 : ℤ) := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
            _ ≤ ∑ i, (if c i = true then x i - 1 else (n : ℤ) - x i) :=
                Finset.sum_le_sum (fun i _ => ht i)
            _ = xsch9_dist c n x := by rw [xsch9_dist]
        have hdec : ∀ i, (xsch9_dist c n (x + xsch_dir (i, Bool.not (c i)))).toNat <
            (xsch9_dist c n x).toNat := by
          intro i
          have hnn := hdnn x hx
          have hdeq : xsch9_dist c n (x + xsch_dir (i, Bool.not (c i))) =
              xsch9_dist c n x - 1 := by
            have hsub : (∑ j, ((if c j = true then x j - 1 else (n : ℤ) - x j)
                - (if c j = true then (x + xsch_dir (i, Bool.not (c i))) j - 1
                    else (n : ℤ) - (x + xsch_dir (i, Bool.not (c i))) j))) = 1 := by
              rw [Finset.sum_eq_single i]
              · by_cases hci : c i = true
                · rw [xsch9_coord_self]; simp [hci, sub_eq_add_neg]
                · rw [xsch9_coord_self]; simp [hci, sub_eq_add_neg]; ring
              · intro j _ hji
                rw [xsch9_coord_ne x i j c hji]
                by_cases hcj : c j = true <;> simp [hcj]
              · intro hi; exact absurd (Finset.mem_univ i) hi
            rw [xsch9_dist, xsch9_dist]
            rw [Finset.sum_sub_distrib] at hsub
            linarith
          rw [hdeq]
          have h1 : ((xsch9_dist c n x - 1).toNat : ℤ) = xsch9_dist c n x - 1 :=
            Int.toNat_of_nonneg (by omega)
          have h2 : ((xsch9_dist c n x).toNat : ℤ) = xsch9_dist c n x :=
            Int.toNat_of_nonneg hnn
          omega
        refine xsch_Top.nbr (Finset.univ.image (fun i : Fin d => (i, Bool.not (c i)))) (hB hx) ?_ ?_ ?_
        · intro s hs
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hs
          obtain ⟨i, rfl⟩ := hs
          exact Finset.mem_univ i
        · rw [Finset.card_image_of_injective (Finset.univ : Finset (Fin d))
            (fun i j hij => congrArg Prod.fst hij)]
        · intro s hs
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hs
          obtain ⟨i, rfl⟩ := hs
          exact ih _ (by have := hdec i; rw [hs] at this; exact this) _ (hmem i) rfl
  exact key _ x hx rfl

end Exploding
