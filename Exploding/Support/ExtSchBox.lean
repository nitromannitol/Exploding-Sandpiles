/-
Boxes along a set of directions, and growth of a toppled box by one layer.

A box `xsb_box lo hi` is a product of intervals.  Along a set of directions `J` its sides have
length `s` or `s + 1` when it is a near-cube `xsb_Near J s lo hi`, and off `J` it is a single
point, so that the toppling along `J` inside it is a `|J|`-dimensional process.  The layer just
above or below a box in a direction `i` is again a box, whose sides in the other directions are
those of the box.  If a box is toppled inside a frozen set and the layer next to it is spanned
along the other directions of `J`, the box grown by that layer is toppled; this is
`xsch_Sp_grow` read on boxes.
-/
import Exploding.Support.ExtSchProb

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The box with corners `lo` and `hi`. -/
def xsb_box (lo hi : Site d) : Set (Site d) := {x | ∀ i, lo i ≤ x i ∧ x i ≤ hi i}

/-- Along the directions of `J` every side of the box has length `s` or `s + 1`, and off `J`
the box is a single point. -/
def xsb_Near (J : Finset (Fin d)) (s : ℕ) (lo hi : Site d) : Prop :=
  (∀ i ∈ J, hi i - lo i + 1 = (s : ℤ) ∨ hi i - lo i + 1 = (s : ℤ) + 1) ∧ ∀ i ∉ J, lo i = hi i

/-- The layer just above the box in direction `i`. -/
def xsb_layerUp (lo hi : Site d) (i : Fin d) : Set (Site d) :=
  xsb_box (Function.update lo i (hi i + 1)) (Function.update hi i (hi i + 1))

/-- The layer just below the box in direction `i`. -/
def xsb_layerDown (lo hi : Site d) (i : Fin d) : Set (Site d) :=
  xsb_box (Function.update lo i (lo i - 1)) (Function.update hi i (lo i - 1))

theorem xsb_mem_box {lo hi x : Site d} : x ∈ xsb_box lo hi ↔ ∀ i, lo i ≤ x i ∧ x i ≤ hi i :=
  Iff.rfl

/-- A box is finite. -/
theorem xsb_box_finite (lo hi : Site d) : (xsb_box lo hi).Finite := by
  have h : xsb_box lo hi = Set.pi Set.univ (fun i => Set.Icc (lo i) (hi i)) := by
    ext x
    simp only [xsb_box, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  rw [h]
  exact Set.Finite.pi fun i => Set.finite_Icc (lo i) (hi i)

/-- Boxes are monotone in the corners. -/
theorem xsb_box_mono {lo hi lo' hi' : Site d} (hlo : ∀ i, lo' i ≤ lo i) (hhi : ∀ i, hi i ≤ hi' i) :
    xsb_box lo hi ⊆ xsb_box lo' hi' :=
  fun _ hx i => ⟨(hlo i).trans (hx i).1, (hx i).2.trans (hhi i)⟩

/-- **Growth by the layer above.**  If the box is toppled inside `B` along `J` and the layer
above it in direction `i ∈ J` lies in `B` and is spanned along `J.erase i`, then the box grown
by that layer is toppled inside `B` along `J`. -/
theorem xsb_grow_up {J : Finset (Fin d)} {i : Fin d} (hiJ : i ∈ J) {B : Set (Site d)}
    {η : Site d → ℤ} {lo hi : Site d} (hne : ∀ j, lo j ≤ hi j)
    (hT : ∀ x ∈ xsb_box lo hi, xsch_Top J B η x) (hLB : xsb_layerUp lo hi i ⊆ B)
    (hL : xsch_Sp (J.erase i) (xsb_layerUp lo hi i) η) :
    ∀ x ∈ xsb_box lo (Function.update hi i (hi i + 1)), xsch_Top J B η x := by
  intro x hx
  by_cases hxi : x i ≤ hi i
  · refine hT x fun j => ?_
    by_cases hj : j = i
    · subst hj
      exact ⟨(hx j).1, hxi⟩
    · refine ⟨(hx j).1, ?_⟩
      have := (hx j).2
      rwa [Function.update_of_ne hj] at this
  · have hxL : x ∈ xsb_layerUp lo hi i := by
      intro j
      by_cases hj : j = i
      · subst hj
        have h2 := (hx j).2
        rw [Function.update_self] at h2 ⊢
        rw [Function.update_self]
        exact ⟨by omega, h2⟩
      · rw [Function.update_of_ne hj, Function.update_of_ne hj]
        refine ⟨(hx j).1, ?_⟩
        have := (hx j).2
        rwa [Function.update_of_ne hj] at this
    refine xsch_Sp_grow hiJ false hLB hT ?_ hL x hxL
    intro y hy
    simp only [xsch_dir, Bool.false_eq_true, if_false]
    intro j
    by_cases hj : j = i
    · subst hj
      have h1 := (hy j)
      rw [Function.update_self, Function.update_self] at h1
      have h2 : y j = hi j + 1 := le_antisymm h1.2 h1.1
      have h3 : (y + -unit j) j = hi j := by simp [unit, h2]
      rw [h3]
      exact ⟨hne j, le_rfl⟩
    · have h1 := (hy j)
      rw [Function.update_of_ne hj, Function.update_of_ne hj] at h1
      have h3 : (y + -unit i) j = y j := by simp [unit, Pi.single_eq_of_ne hj]
      rw [h3]
      exact h1

/-- **Growth by the layer below.** -/
theorem xsb_grow_down {J : Finset (Fin d)} {i : Fin d} (hiJ : i ∈ J) {B : Set (Site d)}
    {η : Site d → ℤ} {lo hi : Site d} (hne : ∀ j, lo j ≤ hi j)
    (hT : ∀ x ∈ xsb_box lo hi, xsch_Top J B η x) (hLB : xsb_layerDown lo hi i ⊆ B)
    (hL : xsch_Sp (J.erase i) (xsb_layerDown lo hi i) η) :
    ∀ x ∈ xsb_box (Function.update lo i (lo i - 1)) hi, xsch_Top J B η x := by
  intro x hx
  by_cases hxi : lo i ≤ x i
  · refine hT x fun j => ?_
    by_cases hj : j = i
    · subst hj
      exact ⟨hxi, (hx j).2⟩
    · refine ⟨?_, (hx j).2⟩
      have := (hx j).1
      rwa [Function.update_of_ne hj] at this
  · have hxL : x ∈ xsb_layerDown lo hi i := by
      intro j
      by_cases hj : j = i
      · subst hj
        have h2 := (hx j).1
        rw [Function.update_self] at h2
        rw [Function.update_self, Function.update_self]
        exact ⟨h2, by omega⟩
      · rw [Function.update_of_ne hj, Function.update_of_ne hj]
        refine ⟨?_, (hx j).2⟩
        have := (hx j).1
        rwa [Function.update_of_ne hj] at this
    refine xsch_Sp_grow hiJ true hLB hT ?_ hL x hxL
    intro y hy
    simp only [xsch_dir, if_true]
    intro j
    by_cases hj : j = i
    · subst hj
      have h1 := (hy j)
      rw [Function.update_self, Function.update_self] at h1
      have h2 : y j = lo j - 1 := le_antisymm h1.2 h1.1
      have h3 : (y + unit j) j = lo j := by simp [unit, h2]
      rw [h3]
      exact ⟨le_rfl, hne j⟩
    · have h1 := (hy j)
      rw [Function.update_of_ne hj, Function.update_of_ne hj] at h1
      have h3 : (y + unit i) j = y j := by simp [unit, Pi.single_eq_of_ne hj]
      rw [h3]
      exact h1

/-- **The induction hypothesis of the dimension induction.**  The probability that a near-cube box
along `k` directions is not internally spanned decays faster than any polynomial in its size,
with constants independent of the position and of the set of directions. -/
def xsb_Decay (d : ℕ) (p : ℝ) (k : ℕ) : Prop :=
  ∀ Q : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ (J : Finset (Fin d)) (lo hi : Site d) (s : ℕ),
    J.card = k → 1 ≤ s → xsb_Near J s lo hi →
      (xsch_mu d p).real {η | ¬ xsch_Sp J (xsb_box lo hi) η} ≤ c / (s : ℝ) ^ Q

end Exploding
