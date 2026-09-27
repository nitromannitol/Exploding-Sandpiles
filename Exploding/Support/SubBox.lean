/-
The bounding rectangle of a finite path, in the form the local-convexity
argument of `paper/exploding.tex` uses it: the coordinatewise minimum and
maximum of the first `j+1` points of a path, and the identification of the
bounding rectangle `br` of the path's image with the box they define.
-/
import Exploding.Support.Vocab

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The minimum of `z k i` over `k ≤ j`. -/
def bmin (z : ℕ → Site d) (j : ℕ) (i : Fin d) : ℤ :=
  (Finset.range (j + 1)).inf' ⟨0, Finset.mem_range.mpr (Nat.succ_pos j)⟩ (fun k => z k i)

/-- The maximum of `z k i` over `k ≤ j`. -/
def bmax (z : ℕ → Site d) (j : ℕ) (i : Fin d) : ℤ :=
  (Finset.range (j + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos j)⟩ (fun k => z k i)

/-- The bounding box of the first `j+1` points of the path. -/
def box (z : ℕ → Site d) (j : ℕ) : Set (Site d) :=
  {p | ∀ i, bmin z j i ≤ p i ∧ p i ≤ bmax z j i}

/-- The minimum is a lower bound for the path's coordinates. -/
theorem bmin_le (z : ℕ → Site d) (j : ℕ) (i : Fin d) {k : ℕ} (hk : k ≤ j) :
    bmin z j i ≤ z k i :=
  Finset.inf'_le (fun k => z k i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

/-- The maximum is an upper bound for the path's coordinates. -/
theorem le_bmax (z : ℕ → Site d) (j : ℕ) (i : Fin d) {k : ℕ} (hk : k ≤ j) :
    z k i ≤ bmax z j i :=
  Finset.le_sup' (fun k => z k i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

/-- The minimum is attained on the path. -/
theorem bmin_attained (z : ℕ → Site d) (j : ℕ) (i : Fin d) :
    ∃ k ≤ j, z k i = bmin z j i := by
  have hne : (Finset.range (j + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos j)⟩
  obtain ⟨k, hk, hk'⟩ := Finset.exists_mem_eq_inf' hne (fun k => z k i)
  exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), hk'.symm⟩

/-- The maximum is attained on the path. -/
theorem bmax_attained (z : ℕ → Site d) (j : ℕ) (i : Fin d) :
    ∃ k ≤ j, z k i = bmax z j i := by
  have hne : (Finset.range (j + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos j)⟩
  obtain ⟨k, hk, hk'⟩ := Finset.exists_mem_eq_sup' hne (fun k => z k i)
  exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), hk'.symm⟩

/-- The bounding rectangle of the first `j+1` points of the path is the box
their coordinatewise extrema define. -/
theorem br_image_eq_box (z : ℕ → Site d) (j : ℕ) :
    br (z '' {i : ℕ | i ≤ j}) = box z j := by
  ext p
  simp only [br, Set.mem_setOf_eq, Set.mem_image, box]
  constructor
  · intro h i
    obtain ⟨⟨y, hy, hyi⟩, ⟨y', hy', hy'i⟩⟩ := h i
    obtain ⟨k, hk, rfl⟩ := hy
    obtain ⟨k', hk', rfl⟩ := hy'
    exact ⟨le_trans (bmin_le z j i hk) hyi, le_trans hy'i (le_bmax z j i hk')⟩
  · intro h i
    obtain ⟨k, hk, hk'⟩ := bmin_attained z j i
    obtain ⟨k', hk'', hk'''⟩ := bmax_attained z j i
    exact ⟨⟨z k, ⟨k, hk, rfl⟩, by rw [hk']; exact (h i).1⟩,
      ⟨z k', ⟨k', hk'', rfl⟩, by rw [hk''']; exact (h i).2⟩⟩

end Exploding
