/-
The down-set (monotone-surface) seed for the bootstrap-percolation bound.

On the cube `Q_n^d` a site topples once `d` of its neighbours have toppled.  If
the whole lower boundary `{x : some coordinate is 1}` has toppled, then the cube
is spanned: a site off the boundary has all `d` of its negative neighbours at a
strictly smaller coordinate sum, so the toppling fills the cube by induction on
that sum.
-/
import Exploding.Support.ExtSchProof

namespace Exploding

open LatticeProb

variable {d : ℕ}

theorem xsch2_coord_sub_unit_self (x : Site d) (i : Fin d) :
    (x - unit i) i = x i - 1 := by
  simp [Pi.sub_apply, unit]

theorem xsch2_coord_sub_unit_ne (x : Site d) {i j : Fin d} (hji : j ≠ i) :
    (x - unit i) j = x j := by
  simp [Pi.sub_apply, unit, Pi.single_eq_of_ne hji]

/-- **Down-set seed.**  If every site of the lower boundary `{x ∈ Q_n^d : ∃ i, x i = 1}`
has already toppled, then the whole cube topples with threshold `d`. -/
theorem xsch2_sp_of_faces (n : ℕ) (η : Site d → ℤ)
    (h : ∀ x ∈ cube d n, (∃ i, x i = 1) → xsch_Top (Finset.univ : Finset (Fin d)) (cube d n) η x) :
    xsch_Sp (Finset.univ : Finset (Fin d)) (cube d n) η := by
  intro x hx
  have key : ∀ s : ℕ, ∀ x : Site d, x ∈ cube d n → (∑ i, (x i).toNat) = s →
      xsch_Top (Finset.univ : Finset (Fin d)) (cube d n) η x := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro x hx hs
      by_cases hface : ∃ i, x i = 1
      · exact h x hx hface
      · have hge2 : ∀ i, 2 ≤ x i := by
          intro i
          have h1 : 1 ≤ x i := (hx i).1
          by_contra hcon
          exact hface ⟨i, by omega⟩
        have hmem : ∀ i : Fin d, x - unit i ∈ cube d n := by
          intro i j
          by_cases hji : j = i
          · rw [hji, xsch2_coord_sub_unit_self x i]
            have h1 : 2 ≤ x i := hge2 i
            have h2 : x i ≤ (n : ℤ) := (hx i).2
            exact ⟨by omega, by omega⟩
          · rw [xsch2_coord_sub_unit_ne x hji]
            exact hx j
        have hle : ∀ i j : Fin d, ((x - unit i) j).toNat ≤ (x j).toNat := by
          intro i j
          apply Int.toNat_le_toNat
          by_cases hji : j = i
          · rw [hji, xsch2_coord_sub_unit_self x i]; omega
          · rw [xsch2_coord_sub_unit_ne x hji]
        have hlt : ∀ i : Fin d, ((x - unit i) i).toNat < (x i).toNat := by
          intro i
          have h1 : 0 < x i := by have := hge2 i; omega
          rw [Int.toNat_lt_toNat h1, xsch2_coord_sub_unit_self x i]
          omega
        refine xsch_Top.nbr (Finset.univ.image (fun i : Fin d => (i, false))) hx ?_ ?_ ?_
        · intro s hs
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hs
          obtain ⟨i, rfl⟩ := hs
          exact Finset.mem_univ i
        · rw [Finset.card_image_of_injective (Finset.univ : Finset (Fin d))
            (fun i j hij => by simpa using hij)]
        · intro s hs
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hs
          obtain ⟨i, rfl⟩ := hs
          have hsum : (∑ j, ((x - unit i) j).toNat) < s := by
            rw [← hs]
            exact Finset.sum_lt_sum (fun j _ => hle i j) ⟨i, Finset.mem_univ i, hlt i⟩
          simpa [xsch_dir, sub_eq_add_neg] using ih _ hsum _ (hmem i) rfl
  exact key _ x hx rfl

end Exploding
