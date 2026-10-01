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


/-- The one-dimensional cube as a finite set of sites. -/
def xsch5_cubeFin (n : ℕ) : Finset (Site 1) :=
  (Finset.range n).image (fun k : ℕ => fun _ : Fin 1 => (k : ℤ) + 1)

theorem xsch5_cubeFin_card (n : ℕ) : (xsch5_cubeFin n).card = n := by
  rw [xsch5_cubeFin, Finset.card_image_of_injective]
  · simp
  · intro k l hkl
    have h := congrFun hkl 0
    simp at h
    omega

theorem xsch5_cubeFin_eq (n : ℕ) (x : Site 1) :
    x ∈ xsch5_cubeFin n ↔ x ∈ cube 1 n := by
  rw [xsch5_cube_one_iff]
  constructor
  · intro hx
    rw [xsch5_cubeFin, Finset.mem_image] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [Finset.mem_range] at hk
    constructor
    · simp
    · simp; omega
  · intro hx
    rw [xsch5_cubeFin, Finset.mem_image]
    refine ⟨(x 0 - 1).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · funext i; fin_cases i; simp; omega

/-- **Percolation estimate in one dimension.** -/
theorem xsch5_percolation_one {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)] (hp : 0 < p) :
    xsch3_PercolationBound 1 p := by
  refine ⟨1, p, by norm_num, hp, fun n => ?_⟩
  have hdet : xsch_Det (↑(xsch5_cubeFin n) : Set (Site 1))
      {η : Site 1 → ℤ | ∀ x ∈ xsch5_cubeFin n, η x ≠ 2 * ((1 : ℕ) : ℤ)} := by
    intro η η' h
    constructor <;> intro hη x hx
    · rw [← h x hx]; exact hη x hx
    · rw [h x hx]; exact hη x hx
  have hmeas := hdet.measurableSet (xsch5_cubeFin n).finite_toSet
  have hsub : {η : Site 1 → ℤ | ¬ xsch_Sp (Finset.univ : Finset (Fin 1)) (cube 1 n) η}
      ⊆ {η : Site 1 → ℤ | ∀ x ∈ xsch5_cubeFin n, η x ≠ 2 * ((1 : ℕ) : ℤ)} := by
    intro η hη x hx hx2
    exact hη (xsch5_sp_one n η ⟨x, (xsch5_cubeFin_eq n x).mp hx, by simpa using hx2⟩)
  calc (xsch_mu 1 p).real {η : Site 1 → ℤ |
        ¬ xsch_Sp (Finset.univ : Finset (Fin 1)) (cube 1 n) η}
      ≤ (xsch_mu 1 p).real {η : Site 1 → ℤ |
          ∀ x ∈ xsch5_cubeFin n, η x ≠ 2 * ((1 : ℕ) : ℤ)} := measureReal_mono hsub (measure_ne_top _ _)
    _ = (1 - p) ^ n := by
        rw [xsch5_not_occ_prob (d := 1) (p := p) le_rfl (xsch5_cubeFin n),
          xsch5_cubeFin_card]
    _ ≤ 1 * Real.exp (-(p * (n : ℝ))) := by
        rw [one_mul]
        have h1 : (0 : ℝ) ≤ 1 - p := by linarith [(Fact.out : 0 ≤ p ∧ p ≤ 1).2]
        have h2 : 1 - p ≤ Real.exp (-p) := by
          have := Real.add_one_le_exp (-p); linarith
        calc (1 - p) ^ n ≤ (Real.exp (-p)) ^ n := pow_le_pow_left₀ h1 h2 n
          _ = Real.exp (-(p * (n : ℝ))) := by rw [← Real.exp_nat_mul]; ring_nf

end Exploding
