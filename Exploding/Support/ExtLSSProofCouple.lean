/-
Finite-coordinate domination from the thinning, and the consistent projective
family of couplings giving the unconditional bounded-degree theorem.
-/
import Exploding.Support.ExtLSSProofFinal

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Exploding

attribute [local instance] Classical.propDecidable

variable {S : Type}

/-- The pointwise thinning bound: the weighted indicators of the subsets lying in `A` never
exceed the indicator of `A`. -/
theorem xlss7_pointwise [DecidableEq S] (μ : Measure (S → Bool)) [IsProbabilityMeasure μ]
    (ρ γ : ℝ) (T : Finset S) (w : S → Bool → Finset S → ℝ) (hw : XlssThin μ ρ γ T w)
    (A : Set (S → Bool)) (hinc : IsIncreasingSet A) (x : S → Bool) :
    ∑ V ∈ T.powerset, (if (fun s => decide (s ∈ V)) ∈ A then 1 else 0) *
      ENNReal.ofReal (∏ l ∈ T, w l (x l) V) ≤ Set.indicator A (fun _ => 1) x := by
  classical
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx]
    calc ∑ V ∈ T.powerset, (if (fun s => decide (s ∈ V)) ∈ A then 1 else 0) *
          ENNReal.ofReal (∏ l ∈ T, w l (x l) V)
        ≤ ∑ V ∈ T.powerset, ENNReal.ofReal (∏ l ∈ T, w l (x l) V) := by
          refine Finset.sum_le_sum fun V _ => ?_
          by_cases hVA : (fun s => decide (s ∈ V)) ∈ A
          · rw [if_pos hVA, one_mul]
          · rw [if_neg hVA, zero_mul]
            positivity
      _ = 1 := xlss_thin_norm_ofReal μ ρ γ T w hw x
  · rw [Set.indicator_of_notMem hx]
    refine le_of_eq (Finset.sum_eq_zero fun V hVT => ?_)
    by_cases hVA : (fun s => decide (s ∈ V)) ∈ A
    · rw [if_pos hVA]
      have hVsub : V ⊆ T := Finset.mem_powerset.mp hVT
      have hex : ∃ l ∈ V, x l = false := by
        by_contra hcon
        push Not at hcon
        exact hx (hinc (fun s => decide (s ∈ V)) x hVA fun s hs => by
          have hsV : s ∈ V := by simpa using hs
          cases h : x s <;> simp_all [hcon s hsV])
      obtain ⟨l, hlV, hxl⟩ := hex
      rw [Finset.prod_eq_zero (hVsub hlV)
        (by rw [hxl, (hw.pos l (hVsub hlV) V hVsub hlV).1]), ENNReal.ofReal_zero, mul_zero]
    · rw [if_neg hVA, zero_mul]

/-- Finite-coordinate domination: the thinning on `T` bounds the product law of a
`T`-determined increasing set by the given law. -/
theorem xlss7_dom_fin [DecidableEq S] (μ : Measure (S → Bool)) [IsProbabilityMeasure μ]
    (ρ γ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (T : Finset S) (w : S → Bool → Finset S → ℝ)
    (hw : XlssThin μ ρ γ T w) (A : Set (S → Bool)) (hA : MeasurableSet A)
    (hinc : IsIncreasingSet A)
    (hdet : ∀ x y, (∀ t ∈ T, x t = y t) → (x ∈ A ↔ y ∈ A)) :
    bernoulliProduct S ρ A ≤ μ A := by
  classical
  rw [xlss6_bernoulli_powerset ρ hρ0 hρ1 T A hA hdet]
  calc ∑ V ∈ T.powerset, (if (fun s : S => decide (s ∈ V)) ∈ A then
          ENNReal.ofReal (ρ ^ V.card * (1 - ρ) ^ (T.card - V.card)) else 0)
      = ∑ V ∈ T.powerset, (if (fun s : S => decide (s ∈ V)) ∈ A then
          ∫⁻ x, ENNReal.ofReal (∏ l ∈ T, w l (x l) V) ∂μ else 0) := by
          refine Finset.sum_congr rfl fun V hV => ?_
          rw [xlss_thin_marg_ofReal μ ρ γ T w hw V (Finset.mem_powerset.mp hV)]
    _ = ∑ V ∈ T.powerset, (if (fun s : S => decide (s ∈ V)) ∈ A then 1 else 0) *
          ∫⁻ x, ENNReal.ofReal (∏ l ∈ T, w l (x l) V) ∂μ := by
          refine Finset.sum_congr rfl fun V _ => ?_
          by_cases hV : (fun s : S => decide (s ∈ V)) ∈ A <;> simp [hV]
    _ = ∫⁻ x, ∑ V ∈ T.powerset, (if (fun s : S => decide (s ∈ V)) ∈ A then 1 else 0) *
          ENNReal.ofReal (∏ l ∈ T, w l (x l) V) ∂μ := by
          rw [lintegral_finsetSum]
          case hf =>
            intro V _
            exact measurable_const.mul
              ((xlss_meas_prod T (fun l b => w l b V)).ennreal_ofReal)
          refine Finset.sum_congr rfl fun V _ => ?_
          rw [lintegral_const_mul]
          exact (xlss_meas_prod T (fun l b => w l b V)).ennreal_ofReal
    _ ≤ ∫⁻ x, Set.indicator A (fun _ => 1) x ∂μ :=
          lintegral_mono fun x => xlss7_pointwise μ ρ γ T w hw A hinc x
    _ = μ A := by
          rw [show (fun x : S → Bool => (1 : ENNReal)) = 1 from rfl,
            lintegral_indicator_one hA]

end Exploding
