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


open LatticeProb

variable {d : ℕ}

/-- **Block union.**  A union of internally-spanned blocks is internally spanned:
each block topples inside itself, hence inside the larger frozen set. -/
theorem xsch2_sp_union {ι : Type*} (R : ι → Set (Site d)) (η : Site d → ℤ)
    (h : ∀ i, xsch_Sp (Finset.univ : Finset (Fin d)) (R i) η) :
    xsch_Sp (Finset.univ : Finset (Fin d)) (⋃ i, R i) η := by
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, hi⟩ := hx
  exact xsch_Top_mono (Set.subset_iUnion R i) (h i x hi)

/-- **Translation invariance.**  Shifting the frozen set and the background by `a`
does not change the toppling closure. -/
theorem xsch2_Top_shift (J : Finset (Fin d)) (B : Set (Site d)) (η : Site d → ℤ)
    (a x : Site d) :
    xsch_Top J {z | z + a ∈ B} η x ↔ xsch_Top J B (fun y => η (y - a)) (x + a) := by
  constructor
  · intro h
    have key : ∀ x : Site d, xsch_Top J {z | z + a ∈ B} η x →
        xsch_Top J B (fun y => η (y - a)) (x + a) := by
      intro x hx
      exact xsch_Top.rec (motive := fun x _ => xsch_Top J B (fun y => η (y - a)) (x + a))
        (fun {x} hB h2 => xsch_Top.occ hB (by simpa using h2))
        (fun {x} S hB hSJ hcard _ ih => xsch_Top.nbr S hB hSJ hcard (fun s hs => by
          have hthis := ih s hs
          rwa [show x + xsch_dir s + a = (x + a) + xsch_dir s from by abel] at hthis))
        hx
    exact key x h
  · intro h
    have key : ∀ y : Site d, xsch_Top J B (fun y => η (y - a)) y →
        xsch_Top J {z | z + a ∈ B} η (y - a) := by
      intro y hy
      exact xsch_Top.rec (motive := fun y _ => xsch_Top J {z | z + a ∈ B} η (y - a))
        (fun {y} hB h2 => xsch_Top.occ (by simpa using hB) (by simpa using h2))
        (fun {y} S hB hSJ hcard _ ih => xsch_Top.nbr S (by simpa using hB) hSJ hcard (fun s hs => by
          have hthis := ih s hs
          rwa [show y + xsch_dir s - a = (y - a) + xsch_dir s from by abel] at hthis))
        hy
    have hthis := key (x + a) h
    rwa [add_sub_cancel_right] at hthis

/-- **Box recursion.**  A translate `Q_L - a` of the cube whose lower boundary has
toppled is internally spanned.  Its lower boundary is the part of the box adjacent
to the lower neighbouring blocks, so once those blocks topple the box fills. -/
theorem xsch2_sp_of_box (a : Site d) (L : ℕ) (η : Site d → ℤ)
    (h : ∀ x ∈ {z : Site d | z + a ∈ cube d L}, (∃ i, x i = 1 - a i) →
      xsch_Top (Finset.univ : Finset (Fin d)) {z : Site d | z + a ∈ cube d L} η x) :
    xsch_Sp (Finset.univ : Finset (Fin d)) {z : Site d | z + a ∈ cube d L} η := by
  have h' : ∀ y ∈ cube d L, (∃ i, y i = 1) →
      xsch_Top (Finset.univ : Finset (Fin d)) (cube d L) (fun z => η (z - a)) y := by
    intro y hy hface
    have hy' : y - a ∈ {z : Site d | z + a ∈ cube d L} := by
      show y - a + a ∈ cube d L
      rwa [sub_add_cancel]
    have hface' : ∃ i, (y - a) i = 1 - a i := by
      obtain ⟨i, hi⟩ := hface
      exact ⟨i, by simp [hi]⟩
    have h1 := h (y - a) hy' hface'
    simpa using (xsch2_Top_shift (Finset.univ : Finset (Fin d)) (cube d L) η a (y - a)).mp h1
  have h3 := xsch2_sp_of_faces L (fun z => η (z - a)) h'
  intro x hx
  have hy : x + a ∈ cube d L := hx
  have h6 := h3 (x + a) hy
  exact (xsch2_Top_shift (Finset.univ : Finset (Fin d)) (cube d L) η a x).mpr h6

end Exploding
