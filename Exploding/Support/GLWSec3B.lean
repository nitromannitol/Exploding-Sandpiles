/-
Proposition 5.1 of the paper (generalized last wave), the Section-3 assembly, part B:
the subadditive cocycle `n ↦ T̃(0, n y)` over the translation by `y ∈ L`, its linear upper
bound, and the almost sure limit along `y` from the moment-free Kingman theorem.
-/
import Exploding.Support.GLWSec3A

open Exploding LatticeProb MeasureTheory Filter
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-- The cocycle `g_n(η) = T̃(0, n y)(η)` on the good event, `0` off it. -/
noncomputable def glws_g (ηmin : ℤ) (y : Site d) (n : ℕ) (η : Site d → ℤ) : ℝ :=
  if η ∈ glws_G d ηmin then glws_f η ((n : ℤ) • y) else 0

theorem glws_g_nonneg (ηmin : ℤ) (y : Site d) (n : ℕ) (η : Site d → ℤ) :
    0 ≤ glws_g ηmin y n η := by
  unfold glws_g
  split_ifs
  · exact Nat.cast_nonneg _
  · exact le_refl _

theorem glws_g_measurable (ηmin : ℤ) (y : Site d) (n : ℕ) :
    Measurable (glws_g ηmin y n) := by
  unfold glws_g
  exact Measurable.ite (glws_G_measurable d ηmin) (lwc_measurable d 0 ((n : ℤ) • y))
    measurable_const

/-- The cocycle inequality, for every background. -/
theorem glws_g_subadd (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin) (y : Site d) (m n : ℕ)
    (η : Site d → ℤ) :
    glws_g ηmin y (m + n) η ≤
      glws_g ηmin y m η + glws_g ηmin y n (((fun η : Site d → ℤ => fun z => η (y + z))^[m]) η) := by
  by_cases hη : η ∈ glws_G d ηmin
  · have hT : ((fun η : Site d → ℤ => fun z => η (y + z))^[m]) η ∈ glws_G d ηmin :=
      glws_iterate_mem hη y m
    unfold glws_g
    rw [if_pos hη, if_pos hη, if_pos hT]
    unfold glws_f
    rw [glw_shift_ergodic_iterate, lwc_cluster_shift]
    have h := glws_f_subadd hd ηmin hηmin hη (0 : Site d) ((m : ℤ) • y) (((m + n : ℕ) : ℤ) • y)
    have e1 : (m : ℤ) • y + (0 : Site d) = (m : ℤ) • y := add_zero _
    have e2 : (m : ℤ) • y + (n : ℤ) • y = ((m + n : ℕ) : ℤ) • y := by
      rw [← add_smul]; push_cast; rfl
    rw [e1, e2]
    exact h
  · have h1 := glws_g_nonneg ηmin y m η
    have h2 := glws_g_nonneg ηmin y n (((fun η : Site d → ℤ => fun z => η (y + z))^[m]) η)
    have h0 : glws_g ηmin y (m + n) η = 0 := by
      unfold glws_g
      rw [if_neg hη]
    rw [h0]
    linarith

/-- `(log t)^γ ≤ t + B` for all natural `t`, for some constant `B`. -/
theorem glws_log_pow_le (γ : ℝ) : ∃ B : ℝ, ∀ t : ℕ, Real.log t ^ γ ≤ (t : ℝ) + B := by
  have hlo : (fun x : ℝ => Real.log x ^ γ) =o[atTop] fun x : ℝ => x ^ (1 : ℝ) :=
    isLittleO_log_rpow_rpow_atTop γ one_pos
  have hdiv := hlo.bound (by norm_num : (0 : ℝ) < 1)
  simp only [Real.rpow_one, Real.norm_eq_abs, one_mul] at hdiv
  obtain ⟨T0, hT0⟩ := Filter.eventually_atTop.mp hdiv
  refine ⟨∑ t ∈ Finset.range (⌈T0⌉₊ + 1), |Real.log (t : ℝ) ^ γ|, fun t => ?_⟩
  by_cases ht : ⌈T0⌉₊ + 1 ≤ t
  · have hge : T0 ≤ (t : ℝ) := by
      have h1 : T0 ≤ (⌈T0⌉₊ : ℝ) := Nat.le_ceil T0
      have h2 : ((⌈T0⌉₊ + 1 : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
      push_cast at h2
      linarith
    have h := hT0 (t : ℝ) hge
    have hnn : 0 ≤ ∑ t ∈ Finset.range (⌈T0⌉₊ + 1), |Real.log (t : ℝ) ^ γ| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    have h3 : Real.log (t : ℝ) ^ γ ≤ |Real.log (t : ℝ) ^ γ| := le_abs_self _
    have h4 : |(t : ℝ)| = (t : ℝ) := abs_of_nonneg (Nat.cast_nonneg t)
    rw [h4] at h
    linarith
  · have hmem : t ∈ Finset.range (⌈T0⌉₊ + 1) := Finset.mem_range.mpr (by omega)
    have h1 : |Real.log (t : ℝ) ^ γ| ≤ ∑ t ∈ Finset.range (⌈T0⌉₊ + 1), |Real.log (t : ℝ) ^ γ| :=
      Finset.single_le_sum (f := fun t : ℕ => |Real.log (t : ℝ) ^ γ|)
        (fun _ _ => abs_nonneg _) hmem
    have h2 : Real.log (t : ℝ) ^ γ ≤ |Real.log (t : ℝ) ^ γ| := le_abs_self _
    have h3 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    linarith

/-- The linear upper bound of the cocycle, on the local good event. -/
theorem glws_g_linear {γ C : ℝ} (ηmin : ℤ) {η : Site d → ℤ}
    (hG : η ∈ glws_G d ηmin) (hloc : glws_Loc d γ C η) (y : Site d) :
    ∃ K : ℝ, ∀ n : ℕ, glws_g ηmin y n η ≤
      (C * (mnorm y : ℝ) + ((mnorm y).toNat + 1 : ℕ)) * n + K := by
  obtain ⟨B, hB⟩ := glws_log_pow_le γ
  obtain ⟨_, n0, hn0⟩ := hloc
  refine ⟨(n0 : ℝ) + B, fun n => ?_⟩
  set Y : ℕ := (mnorm y).toNat + 1 with hY
  set n' : ℕ := max n0 (n * Y) with hn'
  have hn0le : n0 ≤ n' := le_max_left _ _
  have hcentx : ((n : ℤ) • y) ∈ cent d (n * Y) := by
    intro i
    have h1 : |((n : ℤ) • y) i| = (n : ℤ) * |y i| := by
      rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (Int.natCast_nonneg n)]
    have h2 : |y i| ≤ mnorm y := glws_abs_le_mnorm y i
    have h3 : mnorm y ≤ (Y : ℤ) := by rw [hY]; push_cast; omega
    have h4 : (n : ℤ) * |y i| ≤ (n : ℤ) * (Y : ℤ) :=
      mul_le_mul_of_nonneg_left (le_trans h2 h3) (Int.natCast_nonneg n)
    rw [h1]
    push_cast
    exact h4
  have hcentx' : ((n : ℤ) • y) ∈ cent d n' := lwc3_cent_mono (le_max_right _ _) hcentx
  have hcent0 : (0 : Site d) ∈ cent d n' := by intro i; simp
  obtain ⟨a, ha, hloc0⟩ := hn0 n' hn0le 0 hcent0
  obtain ⟨c, hc, hcb⟩ := hloc0 ((n : ℤ) • y) hcentx'
  unfold glws_g
  rw [if_pos hG]
  unfold glws_f
  rw [hc, ENat.toNat_coe]
  have hnorm : mnorm ((0 : Site d) - (n : ℤ) • y) = (n : ℤ) * mnorm y := by
    unfold mnorm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply, Pi.zero_apply, zero_sub, abs_neg, Pi.smul_apply, smul_eq_mul]
    rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg n)]
  rw [hnorm] at hcb
  have hlog := hB n'
  have hn'le : (n' : ℝ) ≤ (n0 : ℝ) + (n : ℝ) * (Y : ℝ) := by
    rcases le_total n0 (n * Y) with h | h
    · rw [hn', max_eq_right h]
      have : ((n * Y : ℕ) : ℝ) = (n : ℝ) * (Y : ℝ) := by push_cast; ring
      rw [this]
      have : (0 : ℝ) ≤ (n0 : ℝ) := Nat.cast_nonneg _
      linarith
    · rw [hn', max_eq_left h]
      have : ((n * Y : ℕ) : ℝ) ≤ (n : ℝ) * (Y : ℝ) := by push_cast; exact le_refl _
      have h' : (n0 : ℝ) ≤ (n0 : ℝ) + (n : ℝ) * (Y : ℝ) := by
        have : (0 : ℝ) ≤ (n : ℝ) * (Y : ℝ) := by positivity
        linarith
      exact h'
  have hcb' : (c : ℝ) ≤ C * ((n : ℝ) * (mnorm y : ℝ)) + Real.log (n' : ℝ) ^ γ := by
    have : (((n : ℤ) * mnorm y : ℤ) : ℝ) = (n : ℝ) * (mnorm y : ℝ) := by push_cast; ring
    rw [this] at hcb
    exact hcb
  have hY' : ((Y : ℕ) : ℝ) = (((mnorm y).toNat + 1 : ℕ) : ℝ) := by rw [hY]
  rw [← hY']
  nlinarith [hcb', hlog, hn'le]

/-- A single translation by `y ∈ L` is ergodic: the mixing hypothesis `(B)` is only needed
for this `y`. -/
theorem glws_shift_ergodic (d : ℕ) (L : AddSubgroup (Site d))
    (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hstat : StationaryOn d L P) (y : Site d) (hy : y ∈ L)
    (hmix : ∀ (s : Finset (Site d)) (S : Set (s → ℤ)),
      MeasurableSet S → ∃ n : ℕ, P (cylinder s S ∩
        (fun η : Site d → ℤ => fun z => η (y + z))^[n] ⁻¹' cylinder s S) =
      P (cylinder s S) * P (cylinder s S)) :
    Ergodic (fun η : Site d → ℤ => fun z => η (y + z)) P := by
  haveI := hP
  refine ergodic_of_mixing_on_isSetRing (C := measurableCylinders fun _ : Site d => ℤ)
    isSetRing_measurableCylinders ?_ generateFrom_measurableCylinders.symm
    (glw_shift_ergodic_meas_pres d L P hstat y hy) ?_
  · exact ⟨{Set.univ}, Set.countable_singleton _,
      Set.singleton_subset_iff.2 isSetAlgebra_measurableCylinders.univ_mem, by simp⟩
  · intro B hB
    obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders B).1 hB
    obtain ⟨n, hn⟩ := hmix s S hS
    exact ⟨n, hn⟩

/-- **The limit along a lattice vector `y ∈ L`, `y ≠ 0`.** -/
theorem glws_direction_limit (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (L : AddSubgroup (Site d)) (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hstat : StationaryOn d L P) (hKing : glw2_KingmanCore)
    (hG : ∀ᵐ η ∂P, η ∈ glws_G d ηmin) {γ C : ℝ} (hloc : ∀ᵐ η ∂P, glws_Loc d γ C η)
    (y : Site d) (hy : y ∈ L)
    (hmix : ∀ (s : Finset (Site d)) (S : Set (s → ℤ)),
      MeasurableSet S → ∃ n : ℕ, P (cylinder s S ∩
        (fun η : Site d → ℤ => fun z => η (y + z))^[n] ⁻¹' cylinder s S) =
      P (cylinder s S) * P (cylinder s S)) :
    ∃ ℓ : ℝ, ∀ᵐ η ∂P,
      Tendsto (fun n : ℕ => glws_f η ((n : ℤ) • y) / (n : ℝ)) atTop (nhds ℓ) := by
  haveI := hP
  have hmp := glw_shift_ergodic_meas_pres d L P hstat y hy
  have herg := glws_shift_ergodic d L P hP hstat y hy hmix
  set C' : ℝ := C * (mnorm y : ℝ) + (((mnorm y).toNat + 1 : ℕ) : ℝ) with hC'
  have hlin : ∀ᵐ η ∂P, ∃ K : ℝ, ∀ n : ℕ, glws_g ηmin y n η ≤ C' * n + K := by
    filter_upwards [hG, hloc] with η h1 h2
    exact glws_g_linear ηmin h1 h2 y
  obtain ⟨K, hA, hApos⟩ := glw_kingman_linear_setA P (glws_g ηmin y)
    (glws_g_measurable ηmin y) C' hlin
  obtain ⟨ℓ, hℓ⟩ := hKing (μ := P) (fun η z => η (y + z)) hmp herg (glws_g ηmin y)
    (glws_g_subadd hd ηmin hηmin y) (glws_g_nonneg ηmin y) (glws_g_measurable ηmin y) C' hlin
    K hA hApos
  refine ⟨ℓ, ?_⟩
  filter_upwards [hℓ, hG] with η h1 h2
  refine h1.congr (fun n => ?_)
  unfold glws_g
  rw [if_pos h2]

end Exploding
