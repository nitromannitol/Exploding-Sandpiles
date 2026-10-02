/-
Corner growth on a box: if the faces of a box selected by a choice of one face per direction are
toppled inside a frozen set containing the box, the whole box is toppled.  A point off the
chosen faces has all `d` neighbours one step nearer the selected corner inside the box, and
the toppling follows by induction on the distance to that corner.  This is the box version of the
corner growth of the cube.
-/
import Exploding.Support.ExtSchBox

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The distance from `x` to the corner of the box selected by `c`. -/
def xsk_dist (c : Fin d → Bool) (lo hi x : Site d) : ℤ :=
  ∑ i, (if c i = true then x i - lo i else hi i - x i)

/-- `x` lies on a face selected by `c`: the lower face in direction `i` if `c i`, the upper face
otherwise. -/
def xsk_onFace (c : Fin d → Bool) (lo hi x : Site d) : Prop :=
  ∃ i, (c i = true ∧ x i = lo i) ∨ (c i = false ∧ x i = hi i)

/-- The coordinate of the neighbour of `x` one step nearer the corner, in the stepped direction. -/
theorem xsk_coord_self (x : Site d) (i : Fin d) (c : Fin d → Bool) :
    (x + xsch_dir (i, !c i)) i = (if c i = true then x i - 1 else x i + 1) := by
  by_cases hci : c i = true
  · simp [xsch_dir, hci, unit, sub_eq_add_neg]
  · have hci' : c i = false := by cases h : c i <;> simp_all
    simp [xsch_dir, hci', unit]

/-- The coordinates of the neighbour of `x` one step nearer the corner, in the other directions. -/
theorem xsk_coord_ne (x : Site d) (i j : Fin d) (c : Fin d → Bool) (hji : j ≠ i) :
    (x + xsch_dir (i, !c i)) j = x j := by
  by_cases hci : c i = true
  · simp [xsch_dir, hci, unit, Pi.single_eq_of_ne hji]
  · have hci' : c i = false := by cases h : c i <;> simp_all
    simp [xsch_dir, hci', unit, Pi.single_eq_of_ne hji]

/-- The distance to the selected corner is nonnegative on the box. -/
theorem xsk_dist_nonneg {c : Fin d → Bool} {lo hi x : Site d} (hx : x ∈ xsb_box lo hi) :
    0 ≤ xsk_dist c lo hi x := by
  refine Finset.sum_nonneg fun i _ => ?_
  by_cases hci : c i = true
  · rw [if_pos hci]; have := (hx i).1; omega
  · rw [if_neg hci]; have := (hx i).2; omega

/-- Off the chosen faces the neighbour one step nearer the corner in direction `i` lies in the
box. -/
theorem xsk_nbr_mem {c : Fin d → Bool} {lo hi x : Site d} (hx : x ∈ xsb_box lo hi)
    (hface : ¬ xsk_onFace c lo hi x) (i : Fin d) : x + xsch_dir (i, !c i) ∈ xsb_box lo hi := by
  intro j
  by_cases hji : j = i
  · rw [hji, xsk_coord_self]
    by_cases hci : c i = true
    · rw [if_pos hci]
      have hxi : x i ≠ lo i := fun h1 => hface ⟨i, Or.inl ⟨hci, h1⟩⟩
      have h1 := (hx i).1
      have h2 := (hx i).2
      exact ⟨by omega, by omega⟩
    · rw [if_neg hci]
      have hci' : c i = false := by cases h : c i <;> simp_all
      have hxi : x i ≠ hi i := fun h1 => hface ⟨i, Or.inr ⟨hci', h1⟩⟩
      have h1 := (hx i).1
      have h2 := (hx i).2
      exact ⟨by omega, by omega⟩
  · rw [xsk_coord_ne x i j c hji]; exact hx j

/-- Off the chosen faces the distance to the selected corner is positive (here `1 ≤ d`). -/
theorem xsk_one_le_dist (hd : 1 ≤ d) {c : Fin d → Bool} {lo hi x : Site d}
    (hx : x ∈ xsb_box lo hi) (hface : ¬ xsk_onFace c lo hi x) : 1 ≤ xsk_dist c lo hi x := by
  have ht : ∀ i, 1 ≤ (if c i = true then x i - lo i else hi i - x i) := by
    intro i
    by_cases hci : c i = true
    · rw [if_pos hci]
      have hxi : x i ≠ lo i := fun h1 => hface ⟨i, Or.inl ⟨hci, h1⟩⟩
      have := (hx i).1; omega
    · rw [if_neg hci]
      have hci' : c i = false := by cases h : c i <;> simp_all
      have hxi : x i ≠ hi i := fun h1 => hface ⟨i, Or.inr ⟨hci', h1⟩⟩
      have := (hx i).2; omega
  have hdle : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  calc (1 : ℤ) ≤ (d : ℤ) := hdle
    _ = ∑ _i : Fin d, (1 : ℤ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    _ ≤ ∑ i, (if c i = true then x i - lo i else hi i - x i) :=
        Finset.sum_le_sum (fun i _ => ht i)
    _ = xsk_dist c lo hi x := by rw [xsk_dist]

/-- Stepping one unit nearer the corner in direction `i` lowers the distance by exactly one. -/
theorem xsk_dist_nbr (c : Fin d → Bool) (lo hi x : Site d) (i : Fin d) :
    xsk_dist c lo hi (x + xsch_dir (i, !c i)) = xsk_dist c lo hi x - 1 := by
  have hsub : (∑ j, ((if c j = true then x j - lo j else hi j - x j)
      - (if c j = true then (x + xsch_dir (i, !c i)) j - lo j
          else hi j - (x + xsch_dir (i, !c i)) j))) = 1 := by
    rw [Finset.sum_eq_single i]
    · by_cases hci : c i = true
      · rw [xsk_coord_self]; simp [hci, sub_eq_add_neg]
      · rw [xsk_coord_self]; simp [hci, sub_eq_add_neg]; ring
    · intro j _ hji
      rw [xsk_coord_ne x i j c hji]
      by_cases hcj : c j = true <;> simp [hcj]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [xsk_dist, xsk_dist]
  rw [Finset.sum_sub_distrib] at hsub
  linarith

/-- **Corner growth on a box.**  If the faces of the box selected by `c` are toppled inside a
frozen set `B` containing the box, then the whole box is toppled inside `B`. -/
theorem xsk_corner_growth (hd : 1 ≤ d) {lo hi : Site d} (hne : ∀ i, lo i ≤ hi i)
    (c : Fin d → Bool) {B : Set (Site d)} (hB : xsb_box lo hi ⊆ B) (η : Site d → ℤ)
    (h : ∀ x ∈ xsb_box lo hi, xsk_onFace c lo hi x →
      xsch_Top (Finset.univ : Finset (Fin d)) B η x) :
    ∀ x ∈ xsb_box lo hi, xsch_Top (Finset.univ : Finset (Fin d)) B η x := by
  -- `hne` is not needed: the proof only uses points of the box, which force `lo ≤ hi`.
  have _ := hne
  have key : ∀ s : ℕ, ∀ x : Site d, x ∈ xsb_box lo hi → (xsk_dist c lo hi x).toNat = s →
      xsch_Top (Finset.univ : Finset (Fin d)) B η x := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro x hx hs
      by_cases hface : xsk_onFace c lo hi x
      · exact h x hx hface
      · have hdec : ∀ i, (xsk_dist c lo hi (x + xsch_dir (i, !c i))).toNat < s := by
          intro i
          have hnn := xsk_dist_nonneg (c := c) hx
          have hpos := xsk_one_le_dist hd hx hface
          rw [xsk_dist_nbr, ← hs]
          omega
        refine xsch_Top.nbr (Finset.univ.image (fun i : Fin d => (i, !c i))) (hB hx) ?_ ?_ ?_
        · intro s hs
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hs
          obtain ⟨i, rfl⟩ := hs
          exact Finset.mem_univ i
        · rw [Finset.card_image_of_injective (Finset.univ : Finset (Fin d))
            (fun i j hij => congrArg Prod.fst hij)]
        · intro s' hs'
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hs'
          obtain ⟨i, rfl⟩ := hs'
          exact ih _ (hdec i) _ (xsk_nbr_mem hx hface i) rfl
  intro x hx
  exact key _ x hx rfl

end Exploding
