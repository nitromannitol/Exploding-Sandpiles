import Exploding.Support.ApproximateSubadditiveP1
import Exploding.Support.AllHighLastArrivalScaling
import Exploding.Support.ManhattanProfile

/-!
# The time constant at parameter one

At the endpoint the background is deterministic. Its arrival profile is the Manhattan norm
up to a uniformly bounded lattice-rounding error, so the endpoint time constant is that norm.
-/

namespace Exploding

open MeasureTheory Filter LatticeProb

/-- At parameter one, the exact all-high arrival formula and the rounding bound give a
uniform estimate for the rescaled arrival times. -/
theorem all_high_arrival_scaling_error_le
    (d : ℕ) (hd : 2 ≤ d) (n : ℕ) (hn : 1 ≤ n) (y : Fin d → ℝ) :
    |((arrival (fun _ : Site d => 2 * (d : ℤ) - 1)
        (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
      - (∑ i : Fin d, |y i|)| ≤ ((d : ℝ) + 2) / (n : ℝ) := by
  let x : Site d := nearestSite ((n : ℝ) • y)
  let r : ℕ := (mnorm x).toNat
  have harrival :
      (arrival (fun _ : Site d => 2 * (d : ℤ) - 1) x).toNat = r + 1 := by
    rw [all_high_arrival d hd x]
    simp [r]
  have hlast :
      (lastArrival (fun _ : Site d => 2 * (d : ℤ) - 1) 0 x).toNat = max 1 r := by
    rw [all_high_last_arrival_eq d hd 0 x]
    simp [r]
  have hmax_le : max 1 r ≤ r + 1 := by omega
  have hsucc_le : r + 1 ≤ max 1 r + 1 :=
    Nat.add_le_add_right (Nat.le_max_right 1 r) 1
  have hgap : |((r + 1 : ℕ) : ℝ) - (max 1 r : ℝ)| ≤ 1 := by
    have hmax_leR : (max 1 r : ℝ) ≤ (r : ℝ) + 1 := by
      exact_mod_cast hmax_le
    have hsucc_leR : (r : ℝ) + 1 ≤ (max 1 r : ℝ) + 1 := by
      exact_mod_cast hsucc_le
    have hlower : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) - (max 1 r : ℝ) := by
      push_cast
      linarith
    have hupper : ((r + 1 : ℕ) : ℝ) - (max 1 r : ℝ) ≤ 1 := by
      push_cast
      linarith
    rw [abs_of_nonneg hlower]
    exact hupper
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hgap_scaled :
      |((arrival (fun _ : Site d => 2 * (d : ℤ) - 1) x).toNat : ℝ) / (n : ℝ)
        - ((lastArrival (fun _ : Site d => 2 * (d : ℤ) - 1) 0 x).toNat : ℝ) /
            (n : ℝ)| ≤ 1 / (n : ℝ) := by
    rw [harrival, hlast, ← sub_div, abs_div, abs_of_pos hnreal]
    exact div_le_div_of_nonneg_right
      (by simpa only [Nat.cast_max, Nat.cast_one] using hgap) hnreal.le
  have hlast_scaled := all_high_last_arrival_scaling_error_le d hd n hn y
  have hsum := Gen.abs_sub_le_of_le
    (((arrival (fun _ : Site d => 2 * (d : ℤ) - 1) x).toNat : ℝ) / (n : ℝ))
    (((lastArrival (fun _ : Site d => 2 * (d : ℤ) - 1) 0 x).toNat : ℝ) / (n : ℝ))
    (∑ i : Fin d, |y i|) (1 / (n : ℝ)) (((d : ℝ) + 1) / (n : ℝ))
    hgap_scaled (by simpa [x] using hlast_scaled)
  have hsum' :
      |((arrival (fun _ : Site d => 2 * (d : ℤ) - 1) x).toNat : ℝ) / (n : ℝ)
        - (∑ i : Fin d, |y i|)| ≤ 1 / (n : ℝ) + ((d : ℝ) + 1) / (n : ℝ) := hsum
  convert hsum' using 1
  ring

/-- Theorem 1.3 at `p = 1`: the deterministic endpoint law has Manhattan time constant,
with finite arrivals and locally uniform convergence. -/
theorem convergence_of_time_constant_p1 (d : ℕ) (hd : 2 ≤ d) :
    ∃ N : (Fin d → ℝ) → ℝ,
      Continuous N ∧
      ConvexOn ℝ Set.univ N ∧
      (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
      ∀ᵐ η ∂(toyLaw d (1 : ℝ)),
        Explosive η ∧ (∀ x : Site d, arrival η x ≠ ⊤) ∧
          ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
            ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
              |((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ) - N y| ≤ ε := by
  rcases ManhattanProfile.sum_abs_continuous_convexOn_smul d with
    ⟨hcontinuous, hconvex, hhomogeneous⟩
  refine ⟨fun y : Fin d → ℝ => ∑ i : Fin d, |y i|,
    hcontinuous, hconvex, hhomogeneous, ?_⟩
  rw [toyLaw_one_eq_dirac, MeasureTheory.ae_dirac_eq]
  simp only [Filter.Eventually, Filter.mem_pure]
  constructor
  · intro hrobust
    apply all_high_pile_not_stabilizable d hd
    simpa only [Nat.cast_one, one_mul] using hrobust 1 (by norm_num)
  constructor
  · intro x
    rw [all_high_arrival d hd x]
    simp
  · intro K hK ε hε
    let n₀ : ℕ := Nat.ceil (((d : ℝ) + 2) / ε) + 1
    refine Filter.eventually_atTop.2 ⟨n₀, ?_⟩
    intro n hn y hy
    have hn₁ : 1 ≤ n := by
      dsimp [n₀] at hn
      omega
    have hnceil : Nat.ceil (((d : ℝ) + 2) / ε) ≤ n := by
      dsimp [n₀] at hn
      omega
    have hceilR : ((d : ℝ) + 2) / ε ≤ (Nat.ceil (((d : ℝ) + 2) / ε) : ℝ) :=
      Nat.le_ceil _
    have hnceilR : (Nat.ceil (((d : ℝ) + 2) / ε) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hnceil
    have hq : ((d : ℝ) + 2) / ε ≤ (n : ℝ) := hceilR.trans hnceilR
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn₁
    have hmul : (d : ℝ) + 2 ≤ (n : ℝ) * ε := (div_le_iff₀ hε).1 hq
    have herror : ((d : ℝ) + 2) / (n : ℝ) ≤ ε := by
      apply (div_le_iff₀ hnreal).2
      nlinarith [hmul]
    have herr := all_high_arrival_scaling_error_le d hd n hn₁ y
    exact le_trans herr herror

end Exploding
