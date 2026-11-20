/-
The Antal–Pisztora bound from the box estimate, and the reduction of
`Exploding.External.AntalPisztoraChemicalDistance` to the box estimate in dimensions `d ≥ 3`.

By translation invariance a box-good block is bad with probability at most `3^d` times the
probability that `[0, N)^d` has no large open path plus the probability that uniqueness fails in
`[-N, 2N)^d` (`boxGood_bad_prob_le`).  Under `PisztoraBoxEstimate d` both are small at some
scale, so the renormalization step gives the chemical-distance bound in dimension `d`
(`chemicalDistance_of_boxEstimate`).  Together with the planar case `antalPisztora_dim_two`,
the full statement follows from the box estimate in dimensions at least three
(`antalPisztoraChemicalDistance_of_boxEstimate`).
-/
import Exploding.Support.APBoxScheme
import Exploding.Support.APPlanarChemical
import Exploding.Support.ExtAPProof14

open LatticeProb Relation MeasureTheory Filter Topology
open scoped ENNReal

namespace Exploding

variable {d : ℕ}

theorem mem_coarseWindow_sub_iff {N r : ℕ} (hN : 0 < N) {b z : Site d} :
    z - (fun i => (N : ℤ) * b i) ∈ coarseWindow N r 0 ↔ z ∈ coarseWindow N r b := by
  rw [mem_coarseWindow_iff, mem_coarseWindow_iff, coarseSite_sub_smul hN]
  simp only [Pi.sub_apply, Pi.zero_apply, sub_zero]

theorem coarseSite_sub_eq_zero_iff {N : ℕ} (hN : 0 < N) {b z : Site d} :
    coarseSite N (z - fun i => (N : ℤ) * b i) = 0 ↔ coarseSite N z = b := by
  rw [coarseSite_sub_smul hN, sub_eq_zero]

theorem measurableSet_cubeCrossing {N : ℕ} (hN : 0 < N) :
    MeasurableSet {ω : Site d × Fin d → Bool | CubeCrossing N ω} := by
  have hsub : lowerCube d N ⊆ coarseWindow N 1 0 := by
    rw [lowerCube_eq hN]
    exact coarseRegion_singleton_subset_window (mem_coarseCube_self 1 0)
  refine measurableSet_of_local (windowBonds_finite hN 1 (0 : Site d)) fun ω ω' h => ?_
  have h' : ∀ e ∈ windowBonds N 1 (0 : Site d), ω' e = ω e := fun e he => (h e he).symm
  constructor
  · rintro ⟨x, y, hxy, hi⟩
    exact ⟨x, y, xap_reach_congr_of_window h hsub hxy, hi⟩
  · rintro ⟨x, y, hxy, hi⟩
    exact ⟨x, y, xap_reach_congr_of_window h' hsub hxy, hi⟩

theorem measurableSet_boxUniqueness {N : ℕ} (hN : 0 < N) :
    MeasurableSet {ω : Site d × Fin d → Bool | BoxUniqueness N ω} := by
  have hsub : tripleBox d N ⊆ coarseWindow N 1 0 := (tripleBox_eq hN).le
  have key : ∀ ω ω' : Site d × Fin d → Bool, (∀ e ∈ windowBonds N 1 (0 : Site d), ω e = ω' e) →
      BoxUniqueness N ω → BoxUniqueness N ω' := by
    intro ω ω' h hu x y z w hxy hzw
    have h' : ∀ e ∈ windowBonds N 1 (0 : Site d), ω' e = ω e := fun e he => (h e he).symm
    exact xap_reach_congr_of_window h hsub (hu x y z w
      ⟨xap_reach_congr_of_window h' hsub hxy.1, hxy.2⟩
      ⟨xap_reach_congr_of_window h' hsub hzw.1, hzw.2⟩)
  exact measurableSet_of_local (windowBonds_finite hN 1 (0 : Site d)) fun ω ω' h =>
    ⟨key ω ω' h, key ω' ω fun e he => (h e he).symm⟩

/-- A box-good block is bad with probability at most `3^d` times the probability that the cube
`[0, N)^d` has no large open path plus the probability that uniqueness fails in `[-N, 2N)^d`. -/
theorem boxGood_bad_prob_le {N : ℕ} (hN : 0 < N) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (b : Site d) :
    bondPercolation d q {ω | ¬ boxGood N ω b} ≤
      3 ^ d * bondPercolation d q {ω | ¬ CubeCrossing N ω} +
        bondPercolation d q {ω | ¬ BoxUniqueness N ω} := by
  classical
  have hshift : ∀ (v : Site d) {A : Set (Site d × Fin d → Bool)}, MeasurableSet A →
      bondPercolation d q (rn_shiftBond v ⁻¹' A) = bondPercolation d q A := by
    intro v A hA
    rw [← Measure.map_apply (rn_shiftBond_measurable v) hA, rn_shiftBond_map hq0 hq1 v]
  have hcross : ∀ b' : Site d,
      bondPercolation d q {ω | ¬ ∃ x y, LargePair N ω (coarseRegion N {b'}) x y} ≤
        bondPercolation d q {ω | ¬ CubeCrossing N ω} := by
    intro b'
    set v : Site d := fun i => (N : ℤ) * b' i
    refine le_of_le_of_eq (measure_mono ?_) (hshift v (measurableSet_cubeCrossing hN).compl)
    intro ω hω hcc
    obtain ⟨x, y, hxy⟩ := hcc
    rw [largePair_shift_iff] at hxy
    refine hω ⟨x + v, y + v, largePair_mono ?_ hxy⟩
    intro z hz
    rw [Set.mem_ofPred_eq, lowerCube_eq hN, coarseRegion, Set.mem_ofPred_eq,
      Set.mem_singleton_iff, coarseSite_sub_eq_zero_iff hN] at hz
    exact hz
  have huniq : bondPercolation d q {ω | ¬ ∀ x y z w,
      LargePair N ω (coarseWindow N 1 b) x y → LargePair N ω (coarseWindow N 1 b) z w →
        xap_Reach ω (coarseWindow N 1 b) x z} ≤
      bondPercolation d q {ω | ¬ BoxUniqueness N ω} := by
    set v : Site d := fun i => (N : ℤ) * b i
    refine le_of_le_of_eq (measure_mono ?_) (hshift v (measurableSet_boxUniqueness hN).compl)
    intro ω hω hu
    apply hω
    intro x y z w hxy hzw
    have hset : {z' : Site d | z' - v ∈ tripleBox d N} = coarseWindow N 1 b := by
      ext z'
      rw [Set.mem_ofPred_eq, tripleBox_eq hN, mem_coarseWindow_sub_iff hN]
    have hxy' : LargePair N (rn_shiftBond v ω) (tripleBox d N) (x - v) (y - v) := by
      rw [largePair_shift_iff, hset, sub_add_cancel, sub_add_cancel]
      exact hxy
    have hzw' : LargePair N (rn_shiftBond v ω) (tripleBox d N) (z - v) (w - v) := by
      rw [largePair_shift_iff, hset, sub_add_cancel, sub_add_cancel]
      exact hzw
    have := hu (x - v) (y - v) (z - v) (w - v) hxy' hzw'
    rwa [xap_reach_shift_iff, hset, sub_add_cancel, sub_add_cancel] at this
  have hsub : {ω | ¬ boxGood N ω b} ⊆
      (⋃ b' ∈ coarseCubeFinset 1 b,
        {ω | ¬ ∃ x y, LargePair N ω (coarseRegion N {b'}) x y}) ∪
      {ω | ¬ ∀ x y z w,
        LargePair N ω (coarseWindow N 1 b) x y → LargePair N ω (coarseWindow N 1 b) z w →
          xap_Reach ω (coarseWindow N 1 b) x z} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists,
      not_not] at hcon
    refine hω ⟨fun b' hb' => ?_, hcon.2⟩
    have := hcon.1 b' (mem_coarseCubeFinset.mpr hb')
    push Not at this
    exact this
  calc
    bondPercolation d q {ω | ¬ boxGood N ω b}
        ≤ bondPercolation d q (⋃ b' ∈ coarseCubeFinset 1 b,
            {ω | ¬ ∃ x y, LargePair N ω (coarseRegion N {b'}) x y}) +
          bondPercolation d q {ω | ¬ ∀ x y z w,
            LargePair N ω (coarseWindow N 1 b) x y → LargePair N ω (coarseWindow N 1 b) z w →
              xap_Reach ω (coarseWindow N 1 b) x z} :=
      (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ (∑ _b' ∈ coarseCubeFinset 1 b, bondPercolation d q {ω | ¬ CubeCrossing N ω}) +
          bondPercolation d q {ω | ¬ BoxUniqueness N ω} := by
      gcongr
      exact (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun b' _ => hcross b')
    _ = 3 ^ d * bondPercolation d q {ω | ¬ CubeCrossing N ω} +
          bondPercolation d q {ω | ¬ BoxUniqueness N ω} := by
      rw [Finset.sum_const, card_coarseCubeFinset, nsmul_eq_mul]
      norm_num

/-- **The Antal–Pisztora bound from the box estimate** in dimension `d ≥ 2`. -/
theorem chemicalDistance_of_boxEstimate (hd : 2 ≤ d) (hB : PisztoraBoxEstimate d) {q : ℝ}
    (hq : bondCritical d < q) (hq1 : q ≤ 1) :
    ∃ ρ c : ℝ, 1 ≤ ρ ∧ 0 < c ∧ ∃ R : ℕ, ∀ y : Site d, (R : ℤ) ≤ mnorm y →
      bondPercolation d q
          {ω | ∃ m : ℕ, (openBondGraph ω).edist 0 y = (m : ℕ∞) ∧ ρ * (mnorm y : ℝ) < (m : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(c * (mnorm y : ℝ)))) := by
  obtain ⟨ε₀, hε₀, hred⟩ := chemicalDistance_of_blockScheme d hd 1
  have hq0 : 0 ≤ q := (xap14_bondCritical_nonneg d).trans hq.le
  have h3 : (3 : ℝ≥0∞) ^ d ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3' : (3 : ℝ≥0∞) ^ d ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  have hε₂ : 0 < ε₀ / 2 := ENNReal.div_pos hε₀.ne' (by norm_num)
  have hε₁ : 0 < ε₀ / 2 / 3 ^ d := ENNReal.div_pos hε₂.ne' h3'
  have hε₁₂ : ε₀ / 2 / 3 ^ d ≤ ε₀ / 2 :=
    ENNReal.div_le_of_le_mul (le_mul_of_one_le_right zero_le (one_le_pow₀ (by norm_num)))
  obtain ⟨N, hN1, hNc, hNu⟩ := hB q hq hq1 _ hε₁
  refine hred hq0 hq1 (box_isBlockScheme hN1) fun b =>
    (boxGood_bad_prob_le hN1 hq0 hq1 b).trans ?_
  calc
    3 ^ d * bondPercolation d q {ω | ¬ CubeCrossing N ω} +
        bondPercolation d q {ω | ¬ BoxUniqueness N ω}
        ≤ 3 ^ d * (ε₀ / 2 / 3 ^ d) + ε₀ / 2 := by gcongr; exact hNu.trans hε₁₂
    _ = ε₀ := by rw [ENNReal.mul_div_cancel h3 h3', ENNReal.add_halves]

/-- **Reduction of the Antal–Pisztora theorem to the box estimate.**  The planar case is
`antalPisztora_dim_two`; in dimensions `d ≥ 3` the box estimate gives the bound through the
renormalization step. -/
theorem antalPisztoraChemicalDistance_of_boxEstimate
    (h : ∀ d : ℕ, 3 ≤ d → PisztoraBoxEstimate d) :
    Exploding.External.AntalPisztoraChemicalDistance := by
  intro d hd q hq hq1
  rcases (show d = 2 ∨ 3 ≤ d by omega) with rfl | hd3
  · exact antalPisztora_dim_two hq hq1
  · exact chemicalDistance_of_boxEstimate hd (h d hd3) hq hq1

end Exploding
