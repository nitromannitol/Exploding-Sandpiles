/-
Proposition 5.1 of the paper (generalized last wave), the Section-3 assembly, part C:
the limit of the rescaled arrival times along every integer direction, from the limits
along directions in the sublattice `L` and the Lipschitz bound.
-/
import Exploding.Support.GLWSec3B

open Exploding LatticeProb MeasureTheory Filter
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-- **Convergence along a subsequence of multiples.**  If the rescaled values converge along the
multiples of `q • v`, the Lipschitz bound makes them converge along all multiples of `v`. -/
theorem glws_subseq_conv {f : Site d → ℝ} {C γ : ℝ} (hC : 0 ≤ C)
    (hlip : ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x x' : Site d, x ∈ cent d n → x' ∈ cent d n →
        |f x - f x'| ≤ C * (mnorm (x - x') : ℝ) + Real.log n ^ γ)
    (v : Site d) (q : ℕ) (hq : 1 ≤ q) (ℓ : ℝ)
    (h : Tendsto (fun n : ℕ => f ((n : ℤ) • ((q : ℤ) • v)) / (n : ℝ)) atTop (nhds ℓ)) :
    Tendsto (fun m : ℕ => f ((m : ℤ) • v) / (m : ℝ)) atTop (nhds (ℓ * (q : ℝ)⁻¹)) := by
  obtain ⟨n0, hn0⟩ := hlip
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  set M : ℕ := (mnorm v).toNat + 1 with hM
  have hMpos : 0 < M := by omega
  have hnorm0 : 0 ≤ mnorm v := lwc2_mnorm_nonneg v
  have hgap : Tendsto (fun m : ℕ => f ((m : ℤ) • v) / (m : ℝ) -
      f (((m / q * q : ℕ) : ℤ) • v) / (m : ℝ)) atTop (nhds 0) := by
    have hb : ∀ m : ℕ, max n0 1 ≤ m →
        |f ((m : ℤ) • v) / (m : ℝ) - f (((m / q * q : ℕ) : ℤ) • v) / (m : ℝ)|
          ≤ (C * ((q : ℝ) * (mnorm v : ℝ)) + Real.log ((M : ℝ) * (m : ℝ)) ^ γ) / (m : ℝ) := by
      intro m hm
      have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
      have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
      have hMm : n0 ≤ M * m := by
        have h1 : n0 ≤ m := le_trans (le_max_left _ _) hm
        exact le_trans h1 (Nat.le_mul_of_pos_left m hMpos)
      have hx1 : ((m : ℤ) • v) ∈ cent d (M * m) := glws_smul_mem_cent v m m le_rfl
      have hx2 : (((m / q * q : ℕ) : ℤ) • v) ∈ cent d (M * m) :=
        glws_smul_mem_cent v _ m (Nat.div_mul_le_self m q)
      have hbnd := hn0 (M * m) hMm _ _ hx1 hx2
      have hcastM : ((M * m : ℕ) : ℝ) = (M : ℝ) * (m : ℝ) := by push_cast; ring
      rw [hcastM] at hbnd
      have hdiff : (m : ℤ) • v - ((m / q * q : ℕ) : ℤ) • v = ((m % q : ℕ) : ℤ) • v := by
        rw [← sub_smul]
        congr 1
        have := Nat.div_add_mod m q
        have h2 : ((q * (m / q) + m % q : ℕ) : ℤ) = (m : ℤ) := by exact_mod_cast this
        push_cast at h2 ⊢
        linarith
      rw [hdiff, lwc2_mnorm_nat_smul] at hbnd
      have hmod : ((m % q : ℕ) : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast le_of_lt (Nat.mod_lt m (by omega : 0 < q))
      have hnR : (0 : ℝ) ≤ (mnorm v : ℝ) := by exact_mod_cast hnorm0
      have hCm : C * ((((m % q : ℕ) : ℤ) * mnorm v : ℤ) : ℝ) ≤ C * ((q : ℝ) * (mnorm v : ℝ)) := by
        have : ((((m % q : ℕ) : ℤ) * mnorm v : ℤ) : ℝ) ≤ (q : ℝ) * (mnorm v : ℝ) := by
          rw [Int.cast_mul, Int.cast_natCast]
          exact mul_le_mul_of_nonneg_right hmod hnR
        exact mul_le_mul_of_nonneg_left this hC
      rw [div_sub_div_same, abs_div, abs_of_pos hmpos]
      apply div_le_div_of_nonneg_right _ hmpos.le
      linarith [hbnd, hCm]
    have hlim : Tendsto (fun m : ℕ =>
        (C * ((q : ℝ) * (mnorm v : ℝ)) + Real.log ((M : ℝ) * (m : ℝ)) ^ γ) / (m : ℝ))
        atTop (nhds 0) := by
      have h1 : Tendsto (fun m : ℕ => (C * ((q : ℝ) * (mnorm v : ℝ))) / (m : ℝ))
          atTop (nhds 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      have h2 : Tendsto (fun m : ℕ => Real.log (M * m) ^ γ / (m : ℝ)) atTop (nhds 0) :=
        lwc_transfer_4 γ M hMpos
      simpa only [add_div, add_zero] using h1.add h2
    have habs : Tendsto (fun m : ℕ =>
        |f ((m : ℤ) • v) / (m : ℝ) - f (((m / q * q : ℕ) : ℤ) • v) / (m : ℝ)|)
        atTop (nhds 0) :=
      squeeze_zero' (Eventually.of_forall fun m => abs_nonneg _)
        (Eventually.mono (eventually_ge_atTop (max n0 1)) hb) hlim
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [Real.norm_eq_abs, sub_zero] using habs
  have hx2lim : Tendsto (fun m : ℕ => f (((m / q * q : ℕ) : ℤ) • v) / (m : ℝ)) atTop
      (nhds (ℓ * (q : ℝ)⁻¹)) := by
    have h1 : Tendsto (fun m : ℕ => f (((m / q : ℕ) : ℤ) • ((q : ℤ) • v)) / ((m / q : ℕ) : ℝ))
        atTop (nhds ℓ) := h.comp (lwc2_div_atTop q hq)
    have h2 : Tendsto (fun m : ℕ => ((m / q : ℕ) : ℝ) / (m : ℝ)) atTop (nhds ((q : ℝ)⁻¹)) :=
      lwc2_div_div_tendsto q hq
    have h3 := h1.mul h2
    refine h3.congr' ?_
    filter_upwards [eventually_ge_atTop q] with m hm
    have hm1 : 1 ≤ m / q := (Nat.one_le_div_iff (by omega : 0 < q)).mpr hm
    have hmpos : (0 : ℝ) < ((m / q : ℕ) : ℝ) := by exact_mod_cast hm1
    have hnpos : (0 : ℝ) < m := by exact_mod_cast (le_trans hq hm)
    have hidx : (((m / q : ℕ) : ℤ) • ((q : ℤ) • v)) = (((m / q * q : ℕ) : ℤ) • v) := by
      rw [smul_smul]; push_cast; rfl
    rw [hidx]
    field_simp
  have hsum := hgap.add hx2lim
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards with m
  ring

/-- **Lipschitz bound for limits.**  Two directional limits differ by at most the Lipschitz
constant times the `ℓ¹`-distance of the directions. -/
theorem glws_lip_limit {f : Site d → ℝ} {C γ : ℝ}
    (hlip : ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x x' : Site d, x ∈ cent d n → x' ∈ cent d n →
        |f x - f x'| ≤ C * (mnorm (x - x') : ℝ) + Real.log n ^ γ)
    (v w : Site d) (a b : ℝ)
    (hv : Tendsto (fun n : ℕ => f ((n : ℤ) • v) / (n : ℝ)) atTop (nhds a))
    (hw : Tendsto (fun n : ℕ => f ((n : ℤ) • w) / (n : ℝ)) atTop (nhds b)) :
    |a - b| ≤ C * (mnorm (v - w) : ℝ) := by
  obtain ⟨n0, hn0⟩ := hlip
  set M : ℕ := max ((mnorm v).toNat + 1) ((mnorm w).toNat + 1) with hM
  have hMpos : 0 < M := lt_of_lt_of_le (Nat.succ_pos _) (le_max_left _ _)
  have hb : ∀ n : ℕ, max n0 1 ≤ n →
      |f ((n : ℤ) • v) / (n : ℝ) - f ((n : ℤ) • w) / (n : ℝ)| ≤
        C * (mnorm (v - w) : ℝ) + Real.log ((M : ℝ) * (n : ℝ)) ^ γ / (n : ℝ) := by
    intro n hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hMn : n0 ≤ M * n := by
      have h1 : n0 ≤ n := le_trans (le_max_left _ _) hn
      exact le_trans h1 (Nat.le_mul_of_pos_left n hMpos)
    have hx1 : ((n : ℤ) • v) ∈ cent d (M * n) := by
      have := glws_smul_mem_cent v n n le_rfl
      exact lwc3_cent_mono (Nat.mul_le_mul_right n (le_max_left _ _)) this
    have hx2 : ((n : ℤ) • w) ∈ cent d (M * n) := by
      have := glws_smul_mem_cent w n n le_rfl
      exact lwc3_cent_mono (Nat.mul_le_mul_right n (le_max_right _ _)) this
    have hbnd := hn0 (M * n) hMn _ _ hx1 hx2
    have hcastM : ((M * n : ℕ) : ℝ) = (M : ℝ) * (n : ℝ) := by push_cast; ring
    rw [hcastM] at hbnd
    have hdiff : (n : ℤ) • v - (n : ℤ) • w = (n : ℤ) • (v - w) := by rw [smul_sub]
    rw [hdiff, lwc2_mnorm_nat_smul] at hbnd
    rw [div_sub_div_same, abs_div, abs_of_pos hnpos, div_le_iff₀ hnpos]
    have : C * ((((n : ℤ) * mnorm (v - w) : ℤ)) : ℝ) = C * (mnorm (v - w) : ℝ) * (n : ℝ) := by
      push_cast; ring
    rw [add_mul, div_mul_cancel₀ _ hnpos.ne']
    linarith
  have hlim : Tendsto (fun n : ℕ =>
      C * (mnorm (v - w) : ℝ) + Real.log ((M : ℝ) * (n : ℝ)) ^ γ / (n : ℝ)) atTop
      (nhds (C * (mnorm (v - w) : ℝ) + 0)) :=
    tendsto_const_nhds.add (lwc_transfer_4 γ M hMpos)
  have habs : Tendsto (fun n : ℕ =>
      |f ((n : ℤ) • v) / (n : ℝ) - f ((n : ℤ) • w) / (n : ℝ)|) atTop (nhds |a - b|) :=
    (hv.sub hw).abs
  rw [add_zero] at hlim
  exact le_of_tendsto_of_tendsto habs hlim
    (Eventually.mono (eventually_ge_atTop (max n0 1)) hb)

end Exploding
