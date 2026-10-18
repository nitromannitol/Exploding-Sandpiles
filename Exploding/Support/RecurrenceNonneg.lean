/-
The singleton consequence of recurrence: a recurrent background is nonnegative at every
site.  This is the step in the proof of `prop:explosion_criteria` of
`paper/corrected-arxiv/exploding-corrected-arxiv.tex` (lines 2392-2396): after the `2d`
neighbours of `x` each fire once, the height of `x` is `η x + 2d`, and recurrence of `{x}`
at time `1 = |{x}|` forces this height to reach `2d`.  The proof evaluates the delivered-seed
`fodo` of `RecurrentOn {x}` at time `1` directly from the definitions, and assumes nothing
beyond `Recurrent η`.
-/
import Exploding.Support.Wave

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-! ### The outer boundary of a singleton -/

/-- A unit step from `x` moves it off `x`. -/
theorem add_unit_ne_self (x : Site d) (i : Fin d) : x + unit i ≠ x := fun h =>
  unit_ne_zero i (by simpa using h)

/-- A unit step back from `x` moves it off `x`. -/
theorem sub_unit_ne_self (x : Site d) (i : Fin d) : x - unit i ≠ x := fun h =>
  unit_ne_zero i (by simpa using h)

/-- The site `x` is not in the outer boundary of `{x}`. -/
theorem self_not_mem_outerBoundary (x : Site d) : x ∉ outerBoundary ({x} : Set (Site d)) :=
  fun h => h.1 (Set.mem_singleton x)

/-- The neighbour `x + e_i` of `x` lies in the outer boundary of `{x}`. -/
theorem add_unit_mem_outerBoundary (x : Site d) (i : Fin d) :
    x + unit i ∈ outerBoundary ({x} : Set (Site d)) :=
  ⟨fun h => add_unit_ne_self x i (Set.mem_singleton_iff.mp h), x, Set.mem_singleton x,
    adj_add_unit x i⟩

/-- The neighbour `x - e_i` of `x` lies in the outer boundary of `{x}`. -/
theorem sub_unit_mem_outerBoundary (x : Site d) (i : Fin d) :
    x - unit i ∈ outerBoundary ({x} : Set (Site d)) :=
  ⟨fun h => sub_unit_ne_self x i (Set.mem_singleton_iff.mp h), x, Set.mem_singleton x,
    adj_sub_unit x i⟩

/-! ### The Laplacian of the boundary indicator -/

open scoped Classical in
/-- The indicator of the outer boundary of `{x}` has neighbour sum `2d` at `x`. -/
theorem nbrSumZ_outerBoundary_singleton (x : Site d) :
    nbrSumZ (fun y => if y ∈ outerBoundary ({x} : Set (Site d)) then (1 : ℤ) else 0) x
      = 2 * (d : ℤ) := by
  have h : ∀ i : Fin d,
      (if x + unit i ∈ outerBoundary ({x} : Set (Site d)) then (1 : ℤ) else 0)
        + (if x - unit i ∈ outerBoundary ({x} : Set (Site d)) then (1 : ℤ) else 0) = 2 :=
    fun i => by
      rw [if_pos (add_unit_mem_outerBoundary x i), if_pos (sub_unit_mem_outerBoundary x i)]
      norm_num
  simp only [nbrSumZ]
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

open scoped Classical in
/-- The Laplacian of the indicator of the outer boundary of `{x}` is `2d` at `x`. -/
theorem lap_outerBoundary_singleton (x : Site d) :
    lap (fun y => if y ∈ outerBoundary ({x} : Set (Site d)) then (1 : ℤ) else 0) x
      = 2 * (d : ℤ) := by
  simp only [lap]
  rw [nbrSumZ_outerBoundary_singleton, if_neg (self_not_mem_outerBoundary x)]
  ring

/-! ### The frozen odometer at the singleton -/

open scoped Classical in
/-- The `{x}`-frozen sandpile at time `0` has height `η x + 2d` at `x`. -/
theorem fconf_zero_outerBoundary_singleton (η : Site d → ℤ) (x : Site d) :
    fconf (({x} : Set (Site d))ᶜ) η
        (fun y => if y ∈ outerBoundary ({x} : Set (Site d)) then (1 : ℤ) else 0) 0 x
      = η x + 2 * (d : ℤ) := by
  simp only [fconf, fodo_zero]
  rw [lap_outerBoundary_singleton]

open scoped Classical in
/-- At time `1` the `{x}`-frozen odometer of the boundary indicator is `1` at `x` exactly
when `2d ≤ η x + 2d`. -/
theorem fodo_singleton_one (η : Site d → ℤ) (x : Site d) :
    fodo (({x} : Set (Site d))ᶜ) η
        (fun y => if y ∈ outerBoundary ({x} : Set (Site d)) then (1 : ℤ) else 0) 1 x
      = if 2 * (d : ℤ) ≤ η x + 2 * (d : ℤ) then 1 else 0 := by
  have hx : x ∉ ({x} : Set (Site d))ᶜ := fun h => h (Set.mem_singleton x)
  rw [fodo_succ, if_neg hx, fconf_zero_outerBoundary_singleton]
  simp only [fodo_zero, if_neg (self_not_mem_outerBoundary x), zero_add]

/-- A recurrent background is nonnegative at every site: recurrence of the singleton `{x}`
at time `1` forces the height `η x + 2d` of `x` to reach `2d`. -/
theorem recurrent_nonneg (η : Site d → ℤ) (hrec : Recurrent η) (x : Site d) :
    0 ≤ η x := by
  have h := hrec {x} 1 (by simp) x (Finset.mem_singleton_self x)
  rw [Finset.coe_singleton, fodo_singleton_one] at h
  by_contra hneg
  have hlt : η x + 2 * (d : ℤ) < 2 * (d : ℤ) := by linarith [not_le.mp hneg]
  rw [if_neg (not_le.mpr hlt)] at h
  exact zero_ne_one h

end Exploding
