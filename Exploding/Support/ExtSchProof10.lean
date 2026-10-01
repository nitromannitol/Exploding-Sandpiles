/-
The L-shape renormalization recursion.

Split `Q_{2n}^d` into its `2^d` corner sub-cubes `Q_n^d`.  If at most one
sub-cube fails to be internally spanned, then the whole cube is spanned: the
chosen face of `Q_{2n}` in each direction (lower in direction `i` when the bad
sub-cube is high there, upper otherwise) lies inside a *good* sub-cube, hence is
toppled, and the mixed-face corner-growth seed `xsch9_corner_growth` fills the
cube.
-/
import Exploding.Support.ExtSchProof9
import Exploding.Support.ExtSchProb

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- The translate of `cube d n` by which the sub-cube `σ` is shifted. -/
def xsch10_shift (σ : Fin d → Bool) (n : ℕ) : Site d :=
  fun i => if σ i = true then (n : ℤ) else 0

/-- The corner sub-cube `Q_n^d` selected by `σ`. -/
def xsch10_sub (σ : Fin d → Bool) (n : ℕ) : Set (Site d) :=
  {x | x - xsch10_shift σ n ∈ cube d n}

theorem xsch10_shift_val (σ : Fin d → Bool) (n : ℕ) (i : Fin d) :
    xsch10_shift σ n i = 0 ∨ xsch10_shift σ n i = (n : ℤ) := by
  unfold xsch10_shift; split <;> simp

theorem xsch10_sub_subset (σ : Fin d → Bool) (n : ℕ) : xsch10_sub σ n ⊆ cube d (2 * n) := by
  intro x hx
  have hx' : x - xsch10_shift σ n ∈ cube d n := hx
  intro i
  have h := hx' i
  simp only [Pi.sub_apply] at h
  rcases xsch10_shift_val σ n i with hs | hs
  · have h' : 1 ≤ x i ∧ x i ≤ (n : ℤ) := by simpa [hs] using h
    exact ⟨by omega, by omega⟩
  · have h' : 1 ≤ x i - (n : ℤ) ∧ x i - (n : ℤ) ≤ (n : ℤ) := by simpa [hs] using h
    exact ⟨by omega, by omega⟩

theorem xsch10_mem_sub_of (n : ℕ) (x : Site d) (hx : x ∈ cube d (2 * n)) :
    x ∈ xsch10_sub (fun i => decide (n < x i)) n := by
  intro i
  have h1 : 1 ≤ x i := (hx i).1
  have h2 : x i ≤ 2 * (n : ℤ) := (hx i).2
  have hsh : xsch10_shift (fun i => decide (n < x i)) n i
      = if n < x i then (n : ℤ) else 0 := by
    simp only [xsch10_shift, decide_eq_true_eq]
  rw [Pi.sub_apply, hsh]
  by_cases h : n < x i
  · rw [if_pos h]; constructor <;> omega
  · rw [if_neg h]; constructor <;> omega

/-- **L-shape lemma.**  If at most one of the `2^d` corner sub-cubes fails to be
internally spanned, then `cube d (2n)` is spanned. -/
theorem xsch10_sp_of_all_but_one (hd : 1 ≤ d) (n : ℕ) (hn : 1 ≤ n) (σ0 : Fin d → Bool)
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


/-- Coordinates of a point of a sub-cube. -/
theorem xsch10_sub_coord (σ : Fin d → Bool) (n : ℕ) {x : Site d}
    (hx : x ∈ xsch10_sub σ n) (i : Fin d) :
    xsch10_shift σ n i + 1 ≤ x i ∧ x i ≤ xsch10_shift σ n i + (n : ℤ) := by
  have hx' : x - xsch10_shift σ n ∈ cube d n := hx
  have h := hx' i
  simp only [Pi.sub_apply] at h
  constructor <;> omega

/-- The `2^d` sub-cubes partition `cube d (2 n)`. -/
theorem xsch10_sub_cover (n : ℕ) : cube d (2 * n) = ⋃ σ, xsch10_sub σ n := by
  ext x
  constructor
  · intro hx
    exact Set.mem_iUnion.mpr ⟨fun i => decide (n < x i), xsch10_mem_sub_of n x hx⟩
  · intro hx
    obtain ⟨σ, hσ⟩ := Set.mem_iUnion.mp hx
    exact xsch10_sub_subset σ n hσ

theorem xsch10_sub_disjoint (n : ℕ) {σ σ' : Fin d → Bool} (h : σ ≠ σ') :
    Disjoint (xsch10_sub σ n) (xsch10_sub σ' n) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  apply h
  funext i
  have c1 := xsch10_sub_coord σ n hx i
  have c2 := xsch10_sub_coord σ' n hx' i
  cases hσ : σ i <;> cases hσ' : σ' i
  · rfl
  · exfalso
    have hs1 : xsch10_shift σ n i = 0 := by simp [xsch10_shift, hσ]
    have hs2 : xsch10_shift σ' n i = (n : ℤ) := by simp [xsch10_shift, hσ']
    rw [hs1] at c1; rw [hs2] at c2; omega
  · exfalso
    have hs1 : xsch10_shift σ n i = (n : ℤ) := by simp [xsch10_shift, hσ]
    have hs2 : xsch10_shift σ' n i = 0 := by simp [xsch10_shift, hσ']
    rw [hs1] at c1; rw [hs2] at c2; omega
  · rfl

end Exploding
