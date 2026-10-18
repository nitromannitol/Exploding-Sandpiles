import Exploding.Support.AllHighLastArrivalScaling
import Exploding.Support.ArxivP1Crossing

/-!
# Convergence of the last-wave at parameter one

At parameter one the actual toy law is concentrated on the all-high
configuration. Its last-arrival time differs from the Manhattan norm by a
uniform rounding error, so the locally uniform limit is the real Manhattan
norm.
-/

namespace Exploding

open LatticeProb MeasureTheory Filter

/-- **Proposition 3.1** (`exploding-arxiv.tex`, label
`prop:convergence_of_the_last_wave`) at parameter one. -/
theorem convergence_of_the_last_wave_p1 (d : ℕ) (hd : 2 ≤ d) :
    ∃ N : (Fin d → ℝ) → ℝ,
      Continuous N ∧
      ConvexOn ℝ Set.univ N ∧
      (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
      ∀ᵐ η ∂(toyLaw d (1 : ℝ)),
        (∀ x : Site d, lastArrival η (0 : Site d) x ≠ ⊤) ∧
          ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
            ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
              |((lastArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
                - N y| ≤ ε := by
  let N : (Fin d → ℝ) → ℝ := fun y => ∑ i : Fin d, |y i|
  have hNcontinuous : Continuous N := by
    dsimp [N]
    fun_prop
  have hNconvex : ConvexOn ℝ Set.univ N := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    change (∑ i : Fin d, |a * x i + b * y i|) ≤
      a * (∑ i : Fin d, |x i|) + b * (∑ i : Fin d, |y i|)
    calc
      (∑ i : Fin d, |a * x i + b * y i|) ≤
          ∑ i : Fin d, (a * |x i| + b * |y i|) := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          |a * x i + b * y i| ≤ |a * x i| + |b * y i| := abs_add_le _ _
          _ = a * |x i| + b * |y i| := by
            simp [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ = a * (∑ i : Fin d, |x i|) + b * (∑ i : Fin d, |y i|) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hNhomogeneous : ∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y := by
    intro c hc y
    dsimp [N]
    calc
      (∑ i : Fin d, |c * y i|) = ∑ i : Fin d, c * |y i| := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul, abs_of_nonneg hc]
      _ = c * (∑ i : Fin d, |y i|) := by rw [← Finset.mul_sum]
  refine ⟨N, hNcontinuous, hNconvex, hNhomogeneous, ?_⟩
  rw [toyLaw_one_eq_dirac, MeasureTheory.ae_dirac_eq]
  simp only [Filter.Eventually, Filter.mem_pure]
  constructor
  · intro x
    rw [all_high_last_arrival_eq d hd (0 : Site d) x]
    simp
  · intro K hK ε hε
    let n₀ : ℕ := Nat.ceil (((d : ℝ) + 1) / ε) + 1
    refine Filter.eventually_atTop.2 ⟨n₀, ?_⟩
    intro n hn y hy
    have hn₁ : 1 ≤ n := by
      dsimp [n₀] at hn
      omega
    have hnceil : Nat.ceil (((d : ℝ) + 1) / ε) ≤ n := by
      dsimp [n₀] at hn
      omega
    have hceilR : (((d : ℝ) + 1) / ε) ≤ (Nat.ceil (((d : ℝ) + 1) / ε) : ℝ) :=
      Nat.le_ceil _
    have hnceilR : (Nat.ceil (((d : ℝ) + 1) / ε) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hnceil
    have hq : ((d : ℝ) + 1) / ε ≤ (n : ℝ) := hceilR.trans hnceilR
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn₁
    have hmul : (d : ℝ) + 1 ≤ (n : ℝ) * ε := (div_le_iff₀ hε).1 hq
    have herr := all_high_last_arrival_scaling_error_le d hd n hn₁ y
    have herror : ((d : ℝ) + 1) / (n : ℝ) ≤ ε := by
      apply (div_le_iff₀ hnreal).2
      nlinarith [hmul]
    exact le_trans herr herror

end Exploding
