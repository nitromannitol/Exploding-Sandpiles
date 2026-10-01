/-
The conditional bound of Liggett, Schonmann and Stacey for a field of bits with a bounded-degree
dependence graph, in the form of a Lovász local lemma for weighted expectations.
-/
import Mathlib
import Exploding.Support.Percolation

open MeasureTheory ProbabilityTheory

namespace Exploding

variable {S : Type}

/-- A function of one coordinate is measurable. -/
theorem xlss_meas_coord (f : Bool → ℝ) (s : S) : Measurable fun x : S → Bool => f (x s) :=
  (measurable_of_finite f).comp (measurable_pi_apply s)

/-- A finite product of functions of single coordinates is measurable. -/
theorem xlss_meas_prod (U : Finset S) (w : S → Bool → ℝ) :
    Measurable fun x : S → Bool => ∏ l ∈ U, w l (x l) :=
  Finset.measurable_prod U fun l _ => xlss_meas_coord (w l) l

/-- A finite product of values in `[0,1]` is integrable. -/
theorem xlss_integrable_prod (μ : Measure (S → Bool)) [IsProbabilityMeasure μ] (U : Finset S)
    (w : S → Bool → ℝ) (hw : ∀ l ∈ U, ∀ b, 0 ≤ w l b ∧ w l b ≤ 1) :
    Integrable (fun x : S → Bool => ∏ l ∈ U, w l (x l)) μ := by
  refine Integrable.of_bound (C := 1) (xlss_meas_prod U w).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have h0 : 0 ≤ ∏ l ∈ U, w l (x l) := Finset.prod_nonneg fun l hl => (hw l hl _).1
  have h1 : ∏ l ∈ U, w l (x l) ≤ 1 := Finset.prod_le_one (fun l hl => (hw l hl _).1)
    (fun l hl => (hw l hl _).2)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1


/-- Independence of one coordinate from the coordinates in a finite set of non-neighbours. -/
theorem xlss_indep_integral [DecidableEq S] (G : SimpleGraph S) (μ : Measure (S → Bool))
    [IsProbabilityMeasure μ] (hdep : HasDependenceGraph G μ) (j : S) (U : Finset S) (hjU : j ∉ U)
    (hadj : ∀ b ∈ U, ¬ G.Adj j b) (φ : Bool → ℝ) (ψ : S → Bool → ℝ) :
    ∫ x, φ (x j) * ∏ l ∈ U, ψ l (x l) ∂μ =
      (∫ x, φ (x j) ∂μ) * ∫ x, ∏ l ∈ U, ψ l (x l) ∂μ := by
  have hind := hdep {j} U (by simpa using hjU) (by simpa using hadj)
  let φ' : (({j} : Finset S) → Bool) → ℝ := fun v => φ (v ⟨j, Finset.mem_singleton_self j⟩)
  let ψ' : (U → Bool) → ℝ := fun v => ∏ k : U, ψ k (v k)
  have hφ' : Measurable φ' := measurable_of_finite _
  have hψ' : Measurable ψ' := measurable_of_finite _
  have h2 := (hind.comp hφ' hψ').integral_fun_mul_eq_mul_integral
    ((hφ'.comp (measurable_pi_lambda _ fun i => measurable_pi_apply _)).aestronglyMeasurable)
    ((hψ'.comp (measurable_pi_lambda _ fun i => measurable_pi_apply _)).aestronglyMeasurable)
  have e1 : ∀ x : S → Bool, φ' (fun i : ({j} : Finset S) => x (i : S)) = φ (x j) :=
    fun x => rfl
  have e2 : ∀ x : S → Bool, ψ' (fun k : U => x (k : S)) = ∏ l ∈ U, ψ l (x l) := by
    intro x
    simp only [ψ']
    exact Finset.prod_coe_sort U fun l => ψ l (x l)
  simpa only [Function.comp_apply, e1, e2] using h2

end Exploding
