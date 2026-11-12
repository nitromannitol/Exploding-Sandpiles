/-
Pushing the Antal–Pisztora assembly: the critical density is strictly below one,
and the finite- and infinite-cluster halves of the high-density estimate are
formulated with the event `xap12_BigDistance`.

The finite-cluster half is stated with `xap12_BigDistance`, for which the
origin-bad event alone is not enough (the distance must also be finite); the
event `SmallCluster ∧ ShortWalkFails` would be too large, since when the origin
itself is bad there is no good star-walk at all.

The supercritical-density reduction (the box-crossing renormalisation extending
the high-density estimate down to `bondCritical`) remains isolated in
`xap12_SupercriticalReduction`; the file records that `bondCritical d < 1` and
that the q-range is non-vacuous.
-/
import Exploding.Support.ExtAPProof12
import Exploding.Support.RNProofCore
import Exploding.Support.RNProofPeierls

open Exploding LatticeProb MeasureTheory Filter
open scoped Classical Topology

namespace Exploding

variable {d : ℕ}

/-! ### The critical density is strictly below one -/

/-- `bondCritical d < 1` for `d ≥ 2`: the percolation probability is positive at
density `255/256` by the Peierls argument, so the critical density is at most it. -/
theorem xap13_bondCritical_lt_one (hd : 2 ≤ d) : bondCritical d < 1 := by
  have hPE : ∀ q : ℝ, 255 / 256 ≤ q → q ≤ 1 → bondTheta d q ≠ 0 :=
    fun q hq0 hq1 => pe_theta_ne_zero hd hq0 hq1
  have hle : bondCritical d ≤ 255 / 256 := rn_bondCritical_le (by norm_num) hPE
  linarith

/-! ### The origin being bad -/

theorem xap13_not_good_zero_smallCluster {ω : Site d × Fin d → Bool}
    (h : ¬ xap_Good ω (0 : Site d)) : xap5_SmallCluster ω := by
  rw [xap5_SmallCluster]
  refine Set.Finite.subset (Set.finite_empty) ?_
  intro z hz
  obtain ⟨p, hp⟩ := hz
  exact h (hp 0 (SimpleGraph.Walk.start_mem_support p))

theorem xap13_not_good_zero_shortWalkFails {ρ : ℝ} {ω : Site d × Fin d → Bool}
    {y : Site d} (h : ¬ xap_Good ω (0 : Site d)) :
    xap12_ShortWalkFails d ρ ω y := by
  rintro ⟨p, hgood, _⟩
  exact h (hgood 0 (SimpleGraph.Walk.start_mem_support p))

/-! ### The finite- and infinite-cluster halves -/

/-- The finite-cluster half: a finite good cluster cannot by itself give a
long open path, exponentially in `|y|`. -/
def xap13_FiniteClusterBound : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ q0 : ℝ, q0 < 1 ∧ ∀ q : ℝ, q0 < q → q ≤ 1 →
    ∃ ρ c : ℝ, 1 ≤ ρ ∧ 0 < c ∧ ∃ R : ℕ, ∀ y : Site d, (R : ℤ) ≤ mnorm y →
      bondPercolation d q {ω | xap5_SmallCluster ω ∧ xap12_BigDistance d ρ ω y} ≤
        ENNReal.ofReal (Real.exp (-(c * (mnorm y : ℝ))))

/-- The infinite-cluster half. -/
def xap13_InfiniteClusterBound : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ q0 : ℝ, q0 < 1 ∧ ∀ q : ℝ, q0 < q → q ≤ 1 →
    ∃ ρ c : ℝ, 1 ≤ ρ ∧ 0 < c ∧ ∃ R : ℕ, ∀ y : Site d, (R : ℤ) ≤ mnorm y →
      bondPercolation d q {ω | ¬ xap5_SmallCluster ω ∧ xap12_BigDistance d ρ ω y} ≤
        ENNReal.ofReal (Real.exp (-(c * (mnorm y : ℝ))))

/-- `xap12_BigDistance` is antitone in `ρ`. -/
theorem xap13_bigDistance_mono {ρ ρ' : ℝ} (h : ρ' ≤ ρ) {ω : Site d × Fin d → Bool}
    {y : Site d} : xap12_BigDistance d ρ ω y → xap12_BigDistance d ρ' ω y := by
  rintro ⟨m, hm, hlt⟩
  exact ⟨m, hm, lt_of_le_of_lt (mul_le_mul_of_nonneg_right h (xap12_mnorm_nonneg y)) hlt⟩

/-- The finite and infinite cluster halves of the split give the
high-density bound. -/
theorem xap13_highDensity_of_bounds (hFin : xap13_FiniteClusterBound)
    (hInf : xap13_InfiniteClusterBound) : xap12_HighDensityBound := by
  intro d hd
  obtain ⟨q0₁, hq0₁, h₁⟩ := hFin d hd
  obtain ⟨q0₂, hq0₂, h₂⟩ := hInf d hd
  refine ⟨max q0₁ q0₂, max_lt hq0₁ hq0₂, fun q hq hq1 => ?_⟩
  have hqq₁ : q0₁ < q := lt_of_le_of_lt (le_max_left _ _) hq
  have hqq₂ : q0₂ < q := lt_of_le_of_lt (le_max_right _ _) hq
  obtain ⟨ρ₁, c₁, hρ₁, hc₁, R₁, hR₁⟩ := h₁ q hqq₁ hq1
  obtain ⟨ρ₂, c₂, hρ₂, hc₂, R₂, hR₂⟩ := h₂ q hqq₂ hq1
  obtain ⟨c, hc, Rc, hRc⟩ := xap12_two_exp_le hc₁ hc₂
  refine ⟨max ρ₁ ρ₂, c, le_trans hρ₁ (le_max_left _ _), hc, max (max R₁ R₂) ⌈Rc⌉₊,
    fun y hy => ?_⟩
  have hy1 : (R₁ : ℤ) ≤ mnorm y :=
    le_trans (by exact_mod_cast le_trans (le_max_left R₁ R₂) (le_max_left _ _)) hy
  have hy2 : (R₂ : ℤ) ≤ mnorm y :=
    le_trans (by exact_mod_cast le_trans (le_max_right R₁ R₂) (le_max_left _ _)) hy
  have hyRc : Rc ≤ (mnorm y : ℝ) := by
    have h1 : Rc ≤ (⌈Rc⌉₊ : ℝ) := by exact_mod_cast Nat.le_ceil Rc
    have h2 : (⌈Rc⌉₊ : ℝ) ≤ ((max (max R₁ R₂) ⌈Rc⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast le_max_right (max R₁ R₂) ⌈Rc⌉₊
    have h3 : ((max (max R₁ R₂) ⌈Rc⌉₊ : ℕ) : ℝ) ≤ (mnorm y : ℝ) := by exact_mod_cast hy
    linarith
  have hsub : {ω | xap12_BigDistance d (max ρ₁ ρ₂) ω y}
      ⊆ {ω | ¬ xap5_SmallCluster ω ∧ xap12_BigDistance d ρ₂ ω y}
        ∪ {ω | xap5_SmallCluster ω ∧ xap12_BigDistance d ρ₁ ω y} := by
    intro ω hω
    have h₁ω : xap12_BigDistance d ρ₁ ω y := xap13_bigDistance_mono (le_max_left ρ₁ ρ₂) hω
    have h₂ω : xap12_BigDistance d ρ₂ ω y := xap13_bigDistance_mono (le_max_right ρ₁ ρ₂) hω
    by_cases hs : xap5_SmallCluster ω
    · exact Or.inr ⟨hs, h₁ω⟩
    · exact Or.inl ⟨hs, h₂ω⟩
  calc bondPercolation d q {ω | xap12_BigDistance d (max ρ₁ ρ₂) ω y}
      ≤ bondPercolation d q ({ω | ¬ xap5_SmallCluster ω ∧ xap12_BigDistance d ρ₂ ω y}
          ∪ {ω | xap5_SmallCluster ω ∧ xap12_BigDistance d ρ₁ ω y}) :=
        measure_mono hsub
    _ ≤ bondPercolation d q {ω | ¬ xap5_SmallCluster ω ∧ xap12_BigDistance d ρ₂ ω y}
          + bondPercolation d q {ω | xap5_SmallCluster ω ∧ xap12_BigDistance d ρ₁ ω y} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(c₂ * (mnorm y : ℝ))))
          + ENNReal.ofReal (Real.exp (-(c₁ * (mnorm y : ℝ)))) :=
        add_le_add (hR₂ y hy2) (hR₁ y hy1)
    _ = ENNReal.ofReal (Real.exp (-(c₂ * (mnorm y : ℝ)))
          + Real.exp (-(c₁ * (mnorm y : ℝ)))) := by
        rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
    _ = ENNReal.ofReal (Real.exp (-(c₁ * (mnorm y : ℝ)))
          + Real.exp (-(c₂ * (mnorm y : ℝ)))) := by rw [add_comm]
    _ ≤ ENNReal.ofReal (Real.exp (-(c * (mnorm y : ℝ)))) :=
        ENNReal.ofReal_le_ofReal (hRc (mnorm y : ℝ) hyRc)

/-- The frozen statement follows from the two-cluster bounds and the
supercritical-density reduction. -/
theorem xap13_AntalPisztora_of_bounds (hSuper : xap12_SupercriticalReduction)
    (hFin : xap13_FiniteClusterBound) (hInf : xap13_InfiniteClusterBound) :
    Exploding.External.AntalPisztoraChemicalDistance :=
  xap12_AntalPisztora_of_highDensity hSuper (xap13_highDensity_of_bounds hFin hInf)

end Exploding
