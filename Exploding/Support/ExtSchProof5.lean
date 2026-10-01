/-
The one-dimensional base case of the percolation estimate `xsch3_PercolationBound`:
a single occupied site topples the whole interval, so the probability that the
interval is not spanned equals the probability that no site is occupied.
-/
import Exploding.Support.ExtSchProof4

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- The probability that no site of a finite set carries `2d` chips is
`(1 - p) ^ |W|`. -/
theorem xsch5_not_occ_prob {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)] (hd : 1 ≤ d)
    (W : Finset (Site d)) :
    (xsch_mu d p).real {η : Site d → ℤ | ∀ x ∈ W, η x ≠ 2 * (d : ℤ)}
      = (1 - p) ^ W.card := by
  have hp := (Fact.out : 0 ≤ p ∧ p ≤ 1)
  have hset : {η : Site d → ℤ | ∀ x ∈ W, η x ≠ 2 * (d : ℤ)}
      = Set.pi (↑W : Set (Site d)) (fun _ => {2 * (d : ℤ)}ᶜ) := by
    ext η; simp [Set.pi]
  haveI := xsch_chip_isProb (2 * (d : ℤ)) (d : ℤ) hp.1 hp.2
  have hne : (d : ℤ) ≠ 2 * (d : ℤ) := by omega
  have h1 : chipLaw (2 * (d : ℤ)) (d : ℤ) p {2 * (d : ℤ)}ᶜ = ENNReal.ofReal (1 - p) := by
    simp only [chipLaw, Measure.add_apply, Measure.smul_apply]
    rw [Measure.dirac_apply' _ (measurableSet_singleton (2 * (d : ℤ))).compl,
      Measure.dirac_apply' _ (measurableSet_singleton (2 * (d : ℤ))).compl]
    simp [Set.mem_compl_iff, hne, Set.mem_singleton_iff]
  rw [measureReal_def, hset]
  unfold xsch_mu productLaw
  rw [Measure.infinitePi_pi _ (fun i _ => (measurableSet_singleton _).compl)]
  simp only [h1, Finset.prod_const]
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1 - p)]

/-- Membership in the one-dimensional cube, read on the single coordinate. -/
theorem xsch5_cube_one_iff (n : ℕ) (y : Site 1) :
    y ∈ cube 1 n ↔ 1 ≤ y 0 ∧ y 0 ≤ (n : ℤ) := by
  constructor
  · intro h; exact h 0
  · intro h i; fin_cases i; exact h

/-- In one dimension an occupied site topples the whole cube. -/
theorem xsch5_sp_one (n : ℕ) (η : Site 1 → ℤ) (h : ∃ x ∈ cube 1 n, η x = 2) :
    xsch_Sp (Finset.univ : Finset (Fin 1)) (cube 1 n) η := by
  obtain ⟨x, hx, hx2⟩ := h
  have hplus : ∀ y : Site 1, (y + unit (0 : Fin 1)) 0 = y 0 + 1 := by intro y; simp [unit]
  have hminus : ∀ y : Site 1, (y - unit (0 : Fin 1)) 0 = y 0 - 1 := by intro y; simp [unit]
  have hx1 : 1 ≤ x 0 := (xsch5_cube_one_iff n x).mp hx |>.1
  have hxn : x 0 ≤ (n : ℤ) := (xsch5_cube_one_iff n x).mp hx |>.2
  have hyx : ∀ y : Site 1, y 0 = x 0 → y = x := by
    intro y h; funext i; fin_cases i; simpa using h
  have key1 : ∀ k : ℕ, ∀ y ∈ cube 1 n, y 0 = x 0 + (k : ℤ) →
      xsch_Top (Finset.univ : Finset (Fin 1)) (cube 1 n) η y := by
    intro k
    induction k with
    | zero =>
      intro y hy h
      rw [hyx y (by simpa using h)]; exact xsch_Top.occ hx hx2
    | succ k ih =>
      intro y hy h
      have hy0 : 1 ≤ y 0 := (xsch5_cube_one_iff n y).mp hy |>.1
      have hyn : y 0 ≤ (n : ℤ) := (xsch5_cube_one_iff n y).mp hy |>.2
      have hy' : y - unit (0 : Fin 1) ∈ cube 1 n := by
        rw [xsch5_cube_one_iff, hminus]
        constructor <;> omega
      have hd' : (y - unit (0 : Fin 1)) 0 = x 0 + (k : ℤ) := by
        rw [hminus]; push_cast at h ⊢; omega
      exact xsch_Top.nbr {(0, false)} hy (by intro s hs; rw [Finset.mem_singleton] at hs; subst hs; simp) (by simp)
        (by intro s hs; simp only [Finset.mem_singleton] at hs; subst hs
            simpa [xsch_dir, sub_eq_add_neg] using ih _ hy' hd')
  have key2 : ∀ k : ℕ, ∀ y ∈ cube 1 n, x 0 = y 0 + (k : ℤ) →
      xsch_Top (Finset.univ : Finset (Fin 1)) (cube 1 n) η y := by
    intro k
    induction k with
    | zero =>
      intro y hy h
      rw [hyx y (by omega)]; exact xsch_Top.occ hx hx2
    | succ k ih =>
      intro y hy h
      have hy0 : 1 ≤ y 0 := (xsch5_cube_one_iff n y).mp hy |>.1
      have hyn : y 0 ≤ (n : ℤ) := (xsch5_cube_one_iff n y).mp hy |>.2
      have hy' : y + unit (0 : Fin 1) ∈ cube 1 n := by
        rw [xsch5_cube_one_iff, hplus]
        constructor <;> omega
      have hd' : x 0 = (y + unit (0 : Fin 1)) 0 + (k : ℤ) := by
        rw [hplus]; push_cast at h ⊢; omega
      exact xsch_Top.nbr {(0, true)} hy (by intro s hs; rw [Finset.mem_singleton] at hs; subst hs; simp) (by simp)
        (by intro s hs; simp only [Finset.mem_singleton] at hs; subst hs
            simpa [xsch_dir, sub_eq_add_neg] using ih _ hy' hd')
  intro y hy
  rcases le_total (x 0) (y 0) with hle | hle
  · exact key1 ((y 0 - x 0).toNat) y hy (by omega)
  · exact key2 ((x 0 - y 0).toNat) y hy (by omega)

end Exploding
