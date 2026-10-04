/-
The axis-line lower bound for a cut of the two opposite faces of a box.

A cut of the negative and positive `i`-faces meets every line parallel to `i` through the box,
because a line that the cut misses is an avoiding path.  The box partitions into
`(2 n + 1) ^ (d - 1)` such lines, so a cut has at least that many points, and in particular at
least `2 n + 1` for `d ≥ 2`.  This is the size input of the box-crossing reduction.
-/
import Exploding.Support.ExtAPMinCut

open Exploding LatticeProb Relation
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-- The coordinates other than `i`. -/
abbrev xml_trans (d : ℕ) (i : Fin d) := {j : Fin d // j ≠ i}

/-- The site whose transverse coordinates are `t` and whose `i`-coordinate is `k`. -/
def xml_lineSite (d : ℕ) (i : Fin d) (t : xml_trans d i → ℤ) (k : ℤ) : Site d :=
  fun j => if h : j = i then k else t ⟨j, h⟩

theorem xml_lineSite_self (d : ℕ) (i : Fin d) (t : xml_trans d i → ℤ) (k : ℤ) :
    xml_lineSite d i t k i = k := by
  simp [xml_lineSite]

theorem xml_lineSite_of_ne (d : ℕ) (i : Fin d) (t : xml_trans d i → ℤ) (k : ℤ)
    {j : Fin d} (hj : j ≠ i) : xml_lineSite d i t k j = t ⟨j, hj⟩ := by
  simp [xml_lineSite, hj]

theorem xml_lineSite_succ (d : ℕ) (i : Fin d) (t : xml_trans d i → ℤ) (k : ℤ) :
    xml_lineSite d i t (k + 1) = xml_lineSite d i t k + unit i := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [xml_lineSite, unit]
  · simp [xml_lineSite, unit, hj]

theorem xml_lineSite_adj (d : ℕ) (i : Fin d) (t : xml_trans d i → ℤ) (k : ℤ) :
    (lattice d).Adj (xml_lineSite d i t k) (xml_lineSite d i t (k + 1)) :=
  ⟨i, Or.inl (xml_lineSite_succ d i t k)⟩

/-- The transverse box. -/
noncomputable def xml_Trans (d n : ℕ) (i : Fin d) : Finset (xml_trans d i → ℤ) :=
  Fintype.piFinset (fun _ : xml_trans d i => Finset.Icc (-(n : ℤ)) (n : ℤ))

theorem xml_mem_Trans {n : ℕ} {i : Fin d} {t : xml_trans d i → ℤ} :
    t ∈ xml_Trans d n i ↔ ∀ j, t j ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
  simp [xml_Trans]

theorem xml_lineSite_mem_cent {n : ℕ} {i : Fin d} {t : xml_trans d i → ℤ}
    (ht : t ∈ xml_Trans d n i) {k : ℤ} (hk : |k| ≤ (n : ℤ)) :
    xml_lineSite d i t k ∈ cent d n := by
  rw [xml_mem_Trans] at ht
  intro j
  by_cases hj : j = i
  · subst hj; rw [xml_lineSite_self]; exact hk
  · rw [xml_lineSite_of_ne d i t k hj]
    exact abs_le.mpr (Finset.mem_Icc.mp (ht ⟨j, hj⟩))

/-- The `i`-coordinate `-n + k` lies in `[-n, n]` for `k ≤ 2n`. -/
theorem xml_abs_negN_add_cast_le {n k : ℕ} (hk : k ≤ 2 * n) :
    |-(n : ℤ) + (k : ℤ)| ≤ (n : ℤ) := by
  rw [abs_le]
  constructor <;> omega

/-- Along the transverse line through `t`, the box path from `-n` to `-n + k` avoids a finite
set `S` that misses the line. -/
theorem xml_line_avoid {n : ℕ} {i : Fin d} {t : xml_trans d i → ℤ}
    (ht : t ∈ xml_Trans d n i) {S : Finset (Site d)}
    (hmiss : ∀ k : ℤ, |k| ≤ (n : ℤ) → xml_lineSite d i t k ∉ (S : Set (Site d)))
    (k : ℕ) (hk : k ≤ 2 * n) :
    xmc_Avoid d n S (xml_lineSite d i t (-(n : ℤ)))
      (xml_lineSite d i t (-(n : ℤ) + (k : ℤ))) := by
  have key : ∀ k : ℕ, k ≤ 2 * n →
      ReflTransGen (fun x y => (lattice d).Adj x y ∧ x ∈ cent d n ∧ y ∈ cent d n ∧
        x ∉ (S : Set (Site d)) ∧ y ∉ (S : Set (Site d)))
        (xml_lineSite d i t (-(n : ℤ))) (xml_lineSite d i t (-(n : ℤ) + (k : ℤ))) := by
    intro k
    induction k with
    | zero => intro _; simpa using ReflTransGen.refl
    | succ k ih =>
      intro hk
      have hk' : k ≤ 2 * n := by omega
      have h1 : xml_lineSite d i t (-(n : ℤ) + (k : ℤ)) ∈ cent d n :=
        xml_lineSite_mem_cent ht (xml_abs_negN_add_cast_le (k := k) hk')
      have h2 : xml_lineSite d i t (-(n : ℤ) + ((k + 1 : ℕ) : ℤ)) ∈ cent d n :=
        xml_lineSite_mem_cent ht (xml_abs_negN_add_cast_le (k := k + 1) (by omega))
      have hn1 : xml_lineSite d i t (-(n : ℤ) + (k : ℤ)) ∉ (S : Set (Site d)) :=
        hmiss _ (xml_abs_negN_add_cast_le (k := k) hk')
      have hn2 : xml_lineSite d i t (-(n : ℤ) + ((k + 1 : ℕ) : ℤ)) ∉ (S : Set (Site d)) :=
        hmiss _ (xml_abs_negN_add_cast_le (k := k + 1) (by omega))
      have hadj : (lattice d).Adj (xml_lineSite d i t (-(n : ℤ) + (k : ℤ)))
          (xml_lineSite d i t (-(n : ℤ) + ((k + 1 : ℕ) : ℤ))) := by
        have := xml_lineSite_adj d i t (-(n : ℤ) + (k : ℤ))
        rwa [show -(n : ℤ) + (k : ℤ) + 1 = -(n : ℤ) + ((k + 1 : ℕ) : ℤ) by push_cast; ring]
          at this
      exact (ih hk').tail ⟨hadj, h1, h2, hn1, hn2⟩
  exact key k hk

/-- **A cut meets every transverse line.** -/
theorem xml_cut_meets_line {n : ℕ} {i : Fin d} {S : Finset (Site d)} (hcut : xmc_IsCut d n i S)
    {t : xml_trans d i → ℤ} (ht : t ∈ xml_Trans d n i) :
    ∃ z ∈ S, ∀ j : xml_trans d i, z j.val = t j := by
  classical
  by_contra h
  push Not at h
  have hmiss : ∀ k : ℤ, |k| ≤ (n : ℤ) → xml_lineSite d i t k ∉ (S : Set (Site d)) := by
    intro k hk hmem
    obtain ⟨j, hj⟩ := h (xml_lineSite d i t k) hmem
    exact hj (xml_lineSite_of_ne d i t k j.2)
  have havoid := xml_line_avoid (d := d) ht hmiss (2 * n) le_rfl
  have hneg : xml_lineSite d i t (-(n : ℤ)) ∈ xmc_Fneg d n i :=
    ⟨xml_lineSite_mem_cent ht (by simp), xml_lineSite_self d i t _⟩
  have hpos : xml_lineSite d i t (-(n : ℤ) + ((2 * n : ℕ) : ℤ)) ∈ xmc_Fpos d n i := by
    refine ⟨xml_lineSite_mem_cent ht
      (xml_abs_negN_add_cast_le (n := n) (k := 2 * n) le_rfl), ?_⟩
    rw [xml_lineSite_self]
    push_cast
    ring
  exact hcut.2 (xml_lineSite d i t (-(n : ℤ)))
    (xml_lineSite d i t (-(n : ℤ) + ((2 * n : ℕ) : ℤ))) hneg hpos havoid

theorem xml_trans_card (d : ℕ) (i : Fin d) : Fintype.card (xml_trans d i) = d - 1 := by
  rw [Fintype.card_subtype]
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin]

/-- The transverse box has `(2 n + 1) ^ (d - 1)` elements. -/
theorem xml_Trans_card (d n : ℕ) (i : Fin d) :
    (xml_Trans d n i).card = (2 * n + 1) ^ (d - 1) := by
  rw [xml_Trans, Fintype.card_piFinset]
  have hIcc : (Finset.Icc (-(n : ℤ)) (n : ℤ)).card = 2 * n + 1 := by
    rw [Int.card_Icc]; omega
  rw [Finset.prod_const, hIcc]
  congr 1
  exact xml_trans_card d i

/-- **A cut has at least `(2 n + 1) ^ (d - 1) ≥ 2 n + 1` points.** -/
theorem xml_cut_card_ge {n : ℕ} {i : Fin d} {S : Finset (Site d)} (hd : 2 ≤ d)
    (hcut : xmc_IsCut d n i S) : 2 * n + 1 ≤ S.card := by
  classical
  have hex : ∀ t : ↥(xml_Trans d n i), ∃ z ∈ S, ∀ j : xml_trans d i, z j.val = t.1 j :=
    fun t => xml_cut_meets_line hcut t.2
  choose g hgS hgt using hex
  let g' : ↥(xml_Trans d n i) → ↥S := fun t => ⟨g t, hgS t⟩
  have hinj : Function.Injective g' := by
    intro a b hab
    have hgab : g a = g b := congrArg Subtype.val hab
    have hfun : (fun j : xml_trans d i => (g a) j.val) = fun j => (g b) j.val := by
      rw [hgab]
    refine Subtype.ext ?_
    funext j
    have := congrFun hfun j
    rw [hgt a j, hgt b j] at this
    exact this
  have hcard := Fintype.card_le_of_injective g' hinj
  rw [Fintype.card_coe, Fintype.card_coe, xml_Trans_card] at hcard
  have hpow : 2 * n + 1 ≤ (2 * n + 1) ^ (d - 1) := by
    have hpos : 1 ≤ d - 1 := by omega
    calc 2 * n + 1 = (2 * n + 1) ^ 1 := (pow_one _).symm
      _ ≤ (2 * n + 1) ^ (d - 1) := Nat.pow_le_pow_right (by omega) hpos
  exact hpow.trans hcard

end Exploding
