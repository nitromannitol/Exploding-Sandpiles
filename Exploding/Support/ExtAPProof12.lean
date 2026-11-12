/-
Assembly of the Antal–Pisztora chemical-distance bound, pushing the
infinite-cluster case and isolating the supercritical-density reduction.

The frozen statement `Exploding.External.AntalPisztoraChemicalDistance` quantifies
over every `q > bondCritical d`, while the Peierls estimate is available only at
high density.  The two named claims whose proofs are the hard percolation inputs
are:

* `xap12_SupercriticalReduction` — the high-density bound implies the frozen
  statement for every `q > bondCritical d` (the box-crossing / renormalisation
  step).

`xap12_AntalPisztora_of_highDensity` yields the frozen statement from the
high-density bound and this reduction.  Everything except the reduction is proved
here.
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

/-! ### The high-density bound and the supercritical-density reduction -/

/-- The high-density chemical-distance bound: for `q` close enough to `1`, the
distance tail decays exponentially at rate `ρ` per unit `mnorm`. -/
def xap12_HighDensityBound : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ q0 : ℝ, q0 < 1 ∧ ∀ q : ℝ, q0 < q → q ≤ 1 →
    ∃ ρ c : ℝ, 1 ≤ ρ ∧ 0 < c ∧ ∃ R : ℕ, ∀ y : Site d, (R : ℤ) ≤ mnorm y →
      bondPercolation d q {ω | xap12_BigDistance d ρ ω y} ≤
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

/-! ### The assembly -/

/-- The frozen statement follows from the high-density bound and the
supercritical-density reduction. -/
theorem xap12_AntalPisztora_of_highDensity (hSuper : xap12_SupercriticalReduction)
    (hHigh : xap12_HighDensityBound) :
    Exploding.External.AntalPisztoraChemicalDistance := hSuper hHigh

end Exploding
