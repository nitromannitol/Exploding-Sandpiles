/-
Assembly of the Antal–Pisztora chemical-distance bound, pushing the
infinite-cluster case and isolating the supercritical-density reduction.

The frozen statement `Exploding.External.AntalPisztoraChemicalDistance` quantifies
over every `q > bondCritical d`, while the Peierls estimate is available only at
high density.  The two named claims whose proofs are the hard percolation inputs
are:

* `xap12_SupercriticalReduction` — the high-density bound implies the frozen
  statement for every `q > bondCritical d` (the box-crossing / renormalisation
  step);
* `xap12_FiniteClusterBound` and `xap12_InfiniteClusterBound` — the two halves of
  the high-density estimate, obtained by splitting on whether the good cluster of
  the origin is finite.

`xap12_highDensity_of_bounds` glues the two cluster cases (a union bound plus an
exponential-comparison lemma), and `xap12_AntalPisztora_of_bounds` then yields the
frozen statement from the three claims.  Everything except the three claims is
proved here.
-/
import Exploding.Support.ExtAPProof11
import Exploding.External.AntalPisztora

open Exploding LatticeProb MeasureTheory
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-! ### The two events of the Peierls split -/

/-- The chemical distance from `0` to `y` is finite and exceeds `ρ |y|`. -/
def xap12_BigDistance (d : ℕ) (ρ : ℝ) (ω : Site d × Fin d → Bool) (y : Site d) : Prop :=
  ∃ m : ℕ, (openBondGraph ω).edist (0 : Site d) y = (m : ℕ∞) ∧
    ρ * (mnorm y : ℝ) < (m : ℝ)

/-- No good star-walk from `0` to `y` is short enough that its open realisation
would beat `ρ |y|`. -/
def xap12_ShortWalkFails (d : ℕ) (ρ : ℝ) (ω : Site d × Fin d → Bool) (y : Site d) : Prop :=
  ¬ ∃ p : (xap2_kingGraph d).Walk (0 : Site d) y,
    (∀ z ∈ p.support, xap_Good ω z) ∧
      ((2 * d * (p.length + 2) : ℕ) : ℝ) ≤ ρ * (mnorm y : ℝ)

theorem xap12_mnorm_nonneg (y : Site d) : (0 : ℝ) ≤ (mnorm y : ℝ) := by
  have : (0 : ℤ) ≤ mnorm y := Finset.sum_nonneg fun i _ => abs_nonneg (y i)
  exact_mod_cast this

/-- A large chemical distance forbids a short good star-walk. -/
theorem xap12_bigDistance_subset_shortWalkFails {ρ : ℝ} {ω : Site d × Fin d → Bool}
    {y : Site d} : xap12_BigDistance d ρ ω y → xap12_ShortWalkFails d ρ ω y := by
  rintro ⟨m, hm, hlt⟩ ⟨p, hgood, hlen⟩
  have hle := xap5_goodWalk_edist_le (M := p.length) ⟨p, hgood, le_rfl⟩
  rw [hm] at hle
  have hlt' : ((2 * d * (p.length + 2) : ℕ) : ℝ) < (m : ℝ) := lt_of_le_of_lt hlen hlt
  have hnat : 2 * d * (p.length + 2) < m := by exact_mod_cast hlt'
  have hcast : ((2 * d * (p.length + 2) : ℕ) : ℕ∞) < (m : ℕ∞) := by exact_mod_cast hnat
  exact not_le.mpr hcast hle

/-- `xap12_ShortWalkFails` is antitone in `ρ`. -/
theorem xap12_shortWalkFails_mono {ρ ρ' : ℝ} (h : ρ' ≤ ρ) {ω : Site d × Fin d → Bool}
    {y : Site d} : xap12_ShortWalkFails d ρ ω y → xap12_ShortWalkFails d ρ' ω y := by
  intro hsw hp
  exact hsw (by
    obtain ⟨p, hgood, hlen⟩ := hp
    exact ⟨p, hgood, le_trans hlen (mul_le_mul_of_nonneg_right h (xap12_mnorm_nonneg y))⟩)

/-! ### The high-density bound and its three named claims -/

/-- The high-density chemical-distance bound: for `q` close enough to `1`, the
distance tail decays exponentially at rate `ρ` per unit `mnorm`. -/
def xap12_HighDensityBound : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ q0 : ℝ, q0 < 1 ∧ ∀ q : ℝ, q0 < q → q ≤ 1 →
    ∃ ρ c : ℝ, 1 ≤ ρ ∧ 0 < c ∧ ∃ R : ℕ, ∀ y : Site d, (R : ℤ) ≤ mnorm y →
      bondPercolation d q {ω | xap12_BigDistance d ρ ω y} ≤
        ENNReal.ofReal (Real.exp (-(c * (mnorm y : ℝ))))

/-- The finite-cluster half of the high-density estimate. -/
def xap12_FiniteClusterBound : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ q0 : ℝ, q0 < 1 ∧ ∀ q : ℝ, q0 < q → q ≤ 1 →
    ∃ ρ c : ℝ, 1 ≤ ρ ∧ 0 < c ∧ ∃ R : ℕ, ∀ y : Site d, (R : ℤ) ≤ mnorm y →
      bondPercolation d q {ω | xap5_SmallCluster ω ∧ xap12_ShortWalkFails d ρ ω y} ≤
        ENNReal.ofReal (Real.exp (-(c * (mnorm y : ℝ))))

/-- The infinite-cluster half of the high-density estimate: the renormalisation
step of the Antal–Pisztora proof. -/
def xap12_InfiniteClusterBound : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ q0 : ℝ, q0 < 1 ∧ ∀ q : ℝ, q0 < q → q ≤ 1 →
    ∃ ρ c : ℝ, 1 ≤ ρ ∧ 0 < c ∧ ∃ R : ℕ, ∀ y : Site d, (R : ℤ) ≤ mnorm y →
      bondPercolation d q {ω | ¬ xap5_SmallCluster ω ∧ xap12_ShortWalkFails d ρ ω y} ≤
        ENNReal.ofReal (Real.exp (-(c * (mnorm y : ℝ))))

/-- The supercritical-density reduction: the high-density bound implies the
frozen statement, which asks for **every** `q > bondCritical d`. -/
def xap12_SupercriticalReduction : Prop :=
  xap12_HighDensityBound → Exploding.External.AntalPisztoraChemicalDistance

/-! ### Comparing two exponential tails -/

theorem xap12_two_exp_le {c1 c2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) :
    ∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, ∀ r : ℝ, R ≤ r →
      Real.exp (-(c1 * r)) + Real.exp (-(c2 * r)) ≤ Real.exp (-(c * r)) := by
  set m := min c1 c2 with hm
  have hmpos : 0 < m := lt_min hc1 hc2
  refine ⟨m / 4, by positivity, 4 * Real.log 2 / m, fun r hr => ?_⟩
  have hRpos : 0 ≤ 4 * Real.log 2 / m := by positivity
  have hr0 : 0 ≤ r := le_trans hRpos hr
  have hlog : Real.log 2 ≤ m / 4 * r := by
    rw [div_le_iff₀ hmpos] at hr
    nlinarith
  have h1 : Real.exp (-(c1 * r)) ≤ Real.exp (-(m / 2 * r)) := by
    apply Real.exp_le_exp.mpr
    have hle : m / 2 ≤ c1 := by have := min_le_left c1 c2; rw [← hm] at this; linarith
    nlinarith [mul_le_mul_of_nonneg_right hle hr0]
  have h2 : Real.exp (-(c2 * r)) ≤ Real.exp (-(m / 2 * r)) := by
    apply Real.exp_le_exp.mpr
    have hle : m / 2 ≤ c2 := by have := min_le_right c1 c2; rw [← hm] at this; linarith
    nlinarith [mul_le_mul_of_nonneg_right hle hr0]
  have h3 : 2 * Real.exp (-(m / 2 * r)) ≤ Real.exp (-(m / 4 * r)) := by
    have h2e : Real.exp (Real.log 2) = (2 : ℝ) := Real.exp_log (by norm_num)
    calc 2 * Real.exp (-(m / 2 * r))
        = Real.exp (Real.log 2) * Real.exp (-(m / 2 * r)) := by rw [h2e]
      _ = Real.exp (Real.log 2 + -(m / 2 * r)) :=
          (Real.exp_add (Real.log 2) (-(m / 2 * r))).symm
      _ ≤ Real.exp (-(m / 4 * r)) := by
          apply Real.exp_le_exp.mpr
          linarith [hlog]
  linarith [h1, h2, h3]

/-! ### Gluing the two cluster cases -/

theorem xap12_highDensity_of_bounds (hFin : xap12_FiniteClusterBound)
    (hInf : xap12_InfiniteClusterBound) : xap12_HighDensityBound := by
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
      ⊆ {ω | ¬ xap5_SmallCluster ω ∧ xap12_ShortWalkFails d ρ₂ ω y}
        ∪ {ω | xap5_SmallCluster ω ∧ xap12_ShortWalkFails d ρ₁ ω y} := by
    intro ω hω
    have hsw := xap12_bigDistance_subset_shortWalkFails hω
    have hsw₁ : xap12_ShortWalkFails d ρ₁ ω y :=
      xap12_shortWalkFails_mono (le_max_left ρ₁ ρ₂) hsw
    have hsw₂ : xap12_ShortWalkFails d ρ₂ ω y :=
      xap12_shortWalkFails_mono (le_max_right ρ₁ ρ₂) hsw
    by_cases hs : xap5_SmallCluster ω
    · exact Or.inr ⟨hs, hsw₁⟩
    · exact Or.inl ⟨hs, hsw₂⟩
  calc bondPercolation d q {ω | xap12_BigDistance d (max ρ₁ ρ₂) ω y}
      ≤ bondPercolation d q ({ω | ¬ xap5_SmallCluster ω ∧ xap12_ShortWalkFails d ρ₂ ω y}
          ∪ {ω | xap5_SmallCluster ω ∧ xap12_ShortWalkFails d ρ₁ ω y}) :=
        measure_mono hsub
    _ ≤ bondPercolation d q {ω | ¬ xap5_SmallCluster ω ∧ xap12_ShortWalkFails d ρ₂ ω y}
          + bondPercolation d q {ω | xap5_SmallCluster ω ∧ xap12_ShortWalkFails d ρ₁ ω y} :=
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

/-! ### The assembly -/

/-- The frozen statement follows from the high-density bound and the
supercritical-density reduction. -/
theorem xap12_AntalPisztora_of_highDensity (hSuper : xap12_SupercriticalReduction)
    (hHigh : xap12_HighDensityBound) :
    Exploding.External.AntalPisztoraChemicalDistance := hSuper hHigh

/-- The frozen statement follows from the finite- and infinite-cluster bounds and
the supercritical-density reduction. -/
theorem xap12_AntalPisztora_of_bounds (hSuper : xap12_SupercriticalReduction)
    (hFin : xap12_FiniteClusterBound) (hInf : xap12_InfiniteClusterBound) :
    Exploding.External.AntalPisztoraChemicalDistance :=
  xap12_AntalPisztora_of_highDensity hSuper (xap12_highDensity_of_bounds hFin hInf)

end Exploding
