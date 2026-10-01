/-
Pushing the Antal–Pisztora assembly: the critical density is strictly below one,
and the finite-cluster half of `ExtAPProof12` is corrected (the old formulation
is refuted below).

The old `xap12_FiniteClusterBound` bounded the event `SmallCluster ∧ ShortWalkFails`.
That event is too large: when the origin itself is bad there is no good star-walk
at all, so `ShortWalkFails` holds and `SmallCluster` holds (the good cluster is
empty), and `P(xap_Good ω 0 = false) = 1 - q^N > 0` is a constant independent of
`y`.  The correct split uses `xap12_BigDistance` itself, for which the origin-bad
event alone is not enough (the distance must also be finite).

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

/-! ### The origin being bad puts one in the old finite-cluster event -/

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

theorem xap13_not_finiteClusterBound (d : ℕ) (hd : 2 ≤ d) : ¬ xap12_FiniteClusterBound := by
  intro h
  obtain ⟨q0, hq0, hq⟩ := h d hd
  have hmax1 : max q0 0 < 1 := max_lt hq0 zero_lt_one
  set q : ℝ := (max q0 0 + 1) / 2 with hqdef
  have hqq0 : q0 < q := by have := le_max_left q0 0; rw [hqdef]; linarith
  have hq1 : q ≤ 1 := by rw [hqdef]; linarith [hmax1]
  have hqpos : 0 < q := by have := le_max_right q0 0; rw [hqdef]; linarith
  have hqlt : q < 1 := by rw [hqdef]; linarith [hmax1]
  obtain ⟨ρ, c, hρ, hc, R, hR⟩ := hq q hqq0 hq1
  haveI : IsProbabilityMeasure (bondPercolation d q) := rn_infinitePi_isProb hqpos.le hq1
  have i0 : Fin d := ⟨0, by omega⟩
  set N : ℕ := (xap_cubeBonds (0 : Site d)).card with hN
  have hNpos : 0 < N := by
    rw [hN]
    refine Finset.card_pos.mpr ⟨(0, i0), ?_⟩
    rw [xap_mem_cubeBonds]
    refine ⟨xap_mem_cube_self (0 : Site d), ?_⟩
    rw [zero_add]
    intro j
    simp only [unit, Pi.single_apply]
    split_ifs <;> norm_num
  have hqN1 : q ^ N < 1 := by
    calc q ^ N ≤ q ^ 1 := pow_le_pow_of_le_one hqpos.le hq1 hNpos
      _ = q := pow_one q
      _ < 1 := hqlt
  have hgood0 : bondPercolation d q {ω | xap_Good ω (0 : Site d)} = ENNReal.ofReal (q ^ N) := by
    rw [xap_good_prob hqpos.le hq1, ← hN, ← ENNReal.ofReal_pow hqpos.le]
  have hcompl : bondPercolation d q {ω | ¬ xap_Good ω (0 : Site d)}
      = ENNReal.ofReal (1 - q ^ N) := by
    rw [show {ω : Site d × Fin d → Bool | ¬ xap_Good ω (0 : Site d)}
        = {ω | xap_Good ω (0 : Site d)}ᶜ from by ext ω; simp]
    rw [measure_compl (xap_good_measurable (0 : Site d))
        (by rw [hgood0]; exact ENNReal.ofReal_ne_top), measure_univ, hgood0,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub (1 : ℝ) (pow_nonneg hqpos.le N)]
  obtain ⟨M, hM⟩ : ∃ M : ℕ, Real.exp (-(c * (M : ℝ))) < 1 - q ^ N := by
    have hpos : 0 < 1 - q ^ N := by linarith [hqN1]
    have hlim : Filter.Tendsto (fun M : ℕ => Real.exp (-(c * (M : ℝ)))) Filter.atTop (𝓝 0) := by
      have hc' : Filter.Tendsto (fun M : ℕ => -(c * (M : ℝ))) Filter.atTop Filter.atBot :=
        Filter.tendsto_neg_atTop_atBot.comp
          (Filter.Tendsto.const_mul_atTop hc tendsto_natCast_atTop_atTop)
      exact Real.tendsto_exp_atBot.comp hc'
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp
      (hlim.eventually (eventually_lt_nhds hpos))
    exact ⟨N0, hN0 N0 le_rfl⟩
  set M' : ℕ := max M R with hM'
  set y : Site d := Pi.single i0 (M' : ℤ) with hy
  have hymnorm : mnorm y = (M' : ℤ) := by
    rw [hy, mnorm]
    rw [Finset.sum_eq_single i0]
    · rw [Pi.single_eq_same, abs_of_nonneg (by positivity)]
    · intro j _ hj; rw [Pi.single_eq_of_ne hj, abs_zero]
    · intro h0; exact absurd (Finset.mem_univ i0) h0
  have hyR : (R : ℤ) ≤ mnorm y := by
    rw [hymnorm]; exact_mod_cast le_max_right M R
  have hyexp : Real.exp (-(c * (mnorm y : ℝ))) < 1 - q ^ N := by
    rw [hymnorm]
    have hle : (M : ℝ) ≤ (M' : ℝ) := by exact_mod_cast le_max_left M R
    have : -(c * (M' : ℝ)) ≤ -(c * (M : ℝ)) := by nlinarith [hc]
    exact lt_of_le_of_lt (Real.exp_le_exp.mpr this) hM
  have hsub : {ω : Site d × Fin d → Bool | ¬ xap_Good ω (0 : Site d)}
      ⊆ {ω | xap5_SmallCluster ω ∧ xap12_ShortWalkFails d ρ ω y} := fun ω hω =>
    ⟨xap13_not_good_zero_smallCluster hω, xap13_not_good_zero_shortWalkFails hω⟩
  have hchain : bondPercolation d q {ω | ¬ xap_Good ω (0 : Site d)}
      ≤ ENNReal.ofReal (Real.exp (-(c * (mnorm y : ℝ)))) :=
    le_trans (measure_mono hsub) (hR y hyR)
  rw [hcompl] at hchain
  have hreal : (1 : ℝ) - q ^ N ≤ Real.exp (-(c * (mnorm y : ℝ))) :=
    (ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg _)).mp hchain
  linarith [hyexp]

/-! ### The corrected finite- and infinite-cluster halves -/

/-- The correct finite-cluster half: a finite good cluster cannot by itself give a
long open path, exponentially in `|y|`. -/
def xap13_FiniteClusterBound : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ q0 : ℝ, q0 < 1 ∧ ∀ q : ℝ, q0 < q → q ≤ 1 →
    ∃ ρ c : ℝ, 1 ≤ ρ ∧ 0 < c ∧ ∃ R : ℕ, ∀ y : Site d, (R : ℤ) ≤ mnorm y →
      bondPercolation d q {ω | xap5_SmallCluster ω ∧ xap12_BigDistance d ρ ω y} ≤
        ENNReal.ofReal (Real.exp (-(c * (mnorm y : ℝ))))

/-- The corrected infinite-cluster half. -/
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

/-- The finite and infinite cluster halves of the corrected split give the
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

/-- The frozen statement follows from the corrected two-cluster bounds and the
supercritical-density reduction. -/
theorem xap13_AntalPisztora_of_bounds (hSuper : xap12_SupercriticalReduction)
    (hFin : xap13_FiniteClusterBound) (hInf : xap13_InfiniteClusterBound) :
    Exploding.External.AntalPisztoraChemicalDistance :=
  xap12_AntalPisztora_of_highDensity hSuper (xap13_highDensity_of_bounds hFin hInf)

end Exploding
