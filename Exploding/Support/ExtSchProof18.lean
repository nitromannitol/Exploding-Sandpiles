/-
The corner recursion at every scale.

`ExtSchProof10`/`ExtSchProof12` split `Q_{2n}` into `2^d` equal corner sub-cubes.
For the finite-volume percolation estimate `xsch13_Percolates` one needs the
recursion at *every* scale, not only the even ones: `Q_n` must be split at
`m = n / 2` into the `2^d` boxes whose `j`-th coordinate interval is `[1, m]`
(when `σ j = false`) or `[m + 1, n]` (when `σ j = true`).  The boxes have sides `m`
or `n - m`, so they are not cubes; the deterministic L-shape argument nevertheless
carries over unchanged, because the chosen face of `Q_n` always lands in a box
whose selector differs from the bad one in the face direction.

This file provides the deterministic half of the all-scales recursion:
`xsch18_sub σ n` and the L-shape lemma `xsch18_sp_of_all_but_one`.  It does not
claim `xsch13_Percolates`.
-/
import Exploding.Support.ExtSchProof17

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- Lower corner of the `n/2`-split box selected by `σ`. -/
def xsch18_lo (σ : Fin d → Bool) (n : ℕ) : Site d :=
  fun j => if σ j = true then (n / 2 : ℤ) + 1 else 1

/-- Upper corner of the `n/2`-split box selected by `σ`. -/
def xsch18_hi (σ : Fin d → Bool) (n : ℕ) : Site d :=
  fun j => if σ j = true then (n : ℤ) else (n / 2 : ℤ)

/-- The box of the `n/2`-split selected by `σ`. -/
def xsch18_sub (σ : Fin d → Bool) (n : ℕ) : Set (Site d) :=
  {x | ∀ j, xsch18_lo σ n j ≤ x j ∧ x j ≤ xsch18_hi σ n j}

theorem xsch18_sub_subset (σ : Fin d → Bool) (n : ℕ) : xsch18_sub σ n ⊆ cube d n := by
  intro x hx j
  have h := hx j
  constructor
  · have : (1 : ℤ) ≤ xsch18_lo σ n j := by
      simp only [xsch18_lo]; split <;> omega
    omega
  · have : xsch18_hi σ n j ≤ (n : ℤ) := by
      simp only [xsch18_hi]; split <;> omega
    omega

theorem xsch18_mem_sub (n : ℕ) (x : Site d) (hx : x ∈ cube d n) :
    x ∈ xsch18_sub (fun j => decide (n / 2 < x j)) n := by
  intro j
  have h1 : 1 ≤ x j := (hx j).1
  have h2 : x j ≤ (n : ℤ) := (hx j).2
  have hlo : xsch18_lo (fun j => decide (n / 2 < x j)) n j
      = if (n / 2 : ℤ) < x j then (n / 2 : ℤ) + 1 else 1 := by
    simp only [xsch18_lo, decide_eq_true_eq]
  have hhi : xsch18_hi (fun j => decide (n / 2 < x j)) n j
      = if (n / 2 : ℤ) < x j then (n : ℤ) else (n / 2 : ℤ) := by
    simp only [xsch18_hi, decide_eq_true_eq]
  constructor
  · rw [hlo]
    by_cases h : (n / 2 : ℤ) < x j
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega
  · rw [hhi]
    by_cases h : (n / 2 : ℤ) < x j
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega

/-- **L-shape lemma at every scale.**  If at most one of the `2^d` boxes of the
`n/2`-split of `Q_n` fails to be internally spanned, then `Q_n` is spanned. -/
theorem xsch18_sp_of_all_but_one (hd : 1 ≤ d) (n : ℕ) (hn : 2 ≤ n) (σ0 : Fin d → Bool)
    (η : Site d → ℤ)
    (hgood : ∀ σ, σ ≠ σ0 → xsch_Sp (Finset.univ : Finset (Fin d)) (xsch18_sub σ n) η) :
    xsch_Sp (Finset.univ : Finset (Fin d)) (cube d n) η := by
  refine xsch9_corner_growth hd n σ0 η ?_
  intro x hx hface
  obtain ⟨i, hfi⟩ := hface
  set σ' : Fin d → Bool := fun j => decide (n / 2 < x j) with hσ'
  have hne : σ' ≠ σ0 := by
    intro heq
    have hii : σ' i = σ0 i := by rw [heq]
    rcases hfi with ⟨hci, hxi⟩ | ⟨hci, hxi⟩
    · have hhalf : (1 : ℤ) ≤ (n / 2 : ℤ) := by
        have : 1 ≤ n / 2 := by omega
        exact_mod_cast this
      have : σ' i = false := by
        simp only [hσ', hxi, decide_eq_false_iff_not]; omega
      rw [this] at hii; rw [hci] at hii; exact Bool.noConfusion hii
    · have hhalf : (n / 2 : ℤ) < (n : ℤ) := by
        have : n / 2 < n := by omega
        exact_mod_cast this
      have : σ' i = true := by
        simp only [hσ', hxi]; exact decide_eq_true (by omega)
      rw [this] at hii; rw [hci] at hii; exact Bool.noConfusion hii
  have htop := hgood σ' hne x (xsch18_mem_sub n x hx)
  exact xsch_Top_mono (xsch18_sub_subset σ' n) htop

end Exploding
