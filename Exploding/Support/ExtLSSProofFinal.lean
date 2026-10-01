/-
Finishing the bounded-degree domination: the finite-coordinate product expansion,
finite-coordinate domination from the thinning, and the unconditional theorem.
-/
import Exploding.Support.ExtLSSProofContent

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Exploding

attribute [local instance] Classical.propDecidable

variable {S : Type}

/-- The one-site Bernoulli law is a probability measure. -/
theorem xlss6_bitLaw_isProb {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    IsProbabilityMeasure (bitLaw q) := by
  refine ⟨?_⟩
  unfold bitLaw
  simp only [Measure.add_apply, Measure.smul_apply, MeasureTheory.measure_univ, smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  norm_num

/-- The product law of a `T`-determined set, expanded over the subsets of `T`. -/
theorem xlss6_bernoulli_powerset [DecidableEq S] (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (T : Finset S) (A : Set (S → Bool))
    (hA : MeasurableSet A)
    (hdet : ∀ x y, (∀ t ∈ T, x t = y t) → (x ∈ A ↔ y ∈ A)) :
    bernoulliProduct S ρ A =
      ∑ V ∈ T.powerset, (if (fun s => decide (s ∈ V)) ∈ A then
        ENNReal.ofReal (ρ ^ V.card * (1 - ρ) ^ (T.card - V.card)) else 0) := by
  classical
  haveI : IsProbabilityMeasure (bitLaw ρ) := xlss6_bitLaw_isProb hρ0 hρ1
  set B : Set (T → Bool) := T.restrict '' A with hB
  have hBmeas : MeasurableSet B := by
    have hpre : B = (fun v : T → Bool => fun s : S => decide (s ∈ xlss_Vof T v)) ⁻¹' A := by
      ext v
      rw [hB, Set.mem_preimage]
      exact xlss_mem_proj T A hdet v
    rw [hpre]
    exact (xlss_meas_Phi T) hA
  have hpre : T.restrict ⁻¹' B = A := by
    ext x
    rw [hB, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact (hdet y x (fun t ht => congrFun hyx ⟨t, ht⟩)).mp hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hν : bernoulliProduct S ρ A = Measure.pi (fun _ : T => bitLaw ρ) B := by
    have hmap : (bernoulliProduct S ρ).map T.restrict = Measure.pi (fun _ : T => bitLaw ρ) := by
      change (Measure.infinitePi (fun _ : S => bitLaw ρ)).map T.restrict = _
      rw [Measure.infinitePi_map_restrict]
    have hmeas : Measurable (Finset.restrict T : (S → Bool) → (T → Bool)) :=
      measurable_pi_lambda _ fun t => measurable_pi_apply (t : S)
    rw [← hpre, ← hmap, Measure.map_apply hmeas hBmeas]
  calc bernoulliProduct S ρ A
      = Measure.pi (fun _ : T => bitLaw ρ) B := hν
    _ = ∑ v ∈ B.toFinset, ∏ t : T, bitLaw ρ {v t} := by
          conv_lhs => rw [← Set.coe_toFinset B]
          exact xlss_pi_eq_sum (fun _ : T => bitLaw ρ) B.toFinset
    _ = ∑ v : T → Bool, (if v ∈ B then ∏ t : T, bitLaw ρ {v t} else 0) := by
          rw [show B.toFinset = Finset.univ.filter (fun v : T → Bool => v ∈ B) from by
            ext v
            simp, Finset.sum_filter]
    _ = ∑ v : T → Bool, (fun V : Finset S =>
          if (fun s : S => decide (s ∈ V)) ∈ A then
            ENNReal.ofReal (ρ ^ V.card * (1 - ρ) ^ (T.card - V.card)) else 0) (xlss_Vof T v) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [xlss_mem_proj T A hdet v, xlss_bitLaw_prod ρ hρ0 hρ1 T v]
    _ = ∑ V ∈ T.powerset, (if (fun s : S => decide (s ∈ V)) ∈ A then
          ENNReal.ofReal (ρ ^ V.card * (1 - ρ) ^ (T.card - V.card)) else 0) :=
          xlss_sum_Vof T (fun V : Finset S =>
            if (fun s : S => decide (s ∈ V)) ∈ A then
              ENNReal.ofReal (ρ ^ V.card * (1 - ρ) ^ (T.card - V.card)) else 0)

end Exploding
