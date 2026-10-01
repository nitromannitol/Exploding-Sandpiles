/-
Proposition 5.1 of the paper (generalized last wave), the Section-3 assembly, part B:
the subadditive cocycle `n ↦ T̃(0, n y)` over the translation by `y ∈ L`, its linear upper
bound, and the almost sure limit along `y` from the moment-free Kingman theorem.
-/
import Exploding.Support.GLWSec3A
import Exploding.Support.KingmanBALip

open Exploding LatticeProb MeasureTheory Filter
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-- The cocycle `g_n(η) = T̃(0, n y)(η)` on the good event, `0` off it. -/
noncomputable def glws_g (ηmin : ℤ) (L : AddSubgroup (Site d)) (y : Site d) (n : ℕ) (η : Site d → ℤ) : ℝ :=
  if η ∈ glws_G d ηmin L then glws_f η ((n : ℤ) • y) else 0

theorem glws_g_nonneg (ηmin : ℤ) (L : AddSubgroup (Site d)) (y : Site d) (n : ℕ) (η : Site d → ℤ) :
    0 ≤ glws_g ηmin L y n η := by
  unfold glws_g
  split_ifs
  · exact Nat.cast_nonneg _
  · exact le_refl _

theorem glws_g_measurable (ηmin : ℤ) (L : AddSubgroup (Site d)) (y : Site d) (n : ℕ) :
    Measurable (glws_g ηmin L y n) := by
  unfold glws_g
  exact Measurable.ite (glws_G_measurable d ηmin L) (lwc_measurable d 0 ((n : ℤ) • y))
    measurable_const

/-- The cocycle inequality, for every background (`y` in the sublattice). -/
theorem glws_g_subadd (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin) (L : AddSubgroup (Site d))
    {y : Site d} (hy : y ∈ L) (m n : ℕ)
    (η : Site d → ℤ) :
    glws_g ηmin L y (m + n) η ≤
      glws_g ηmin L y m η + glws_g ηmin L y n (((fun η : Site d → ℤ => fun z => η (y + z))^[m]) η) := by
  by_cases hη : η ∈ glws_G d ηmin L
  · have hT : ((fun η : Site d → ℤ => fun z => η (y + z))^[m]) η ∈ glws_G d ηmin L :=
      glws_iterate_mem hη hy m
    unfold glws_g
    rw [if_pos hη, if_pos hη, if_pos hT]
    unfold glws_f
    rw [glw_shift_ergodic_iterate, lwc_cluster_shift]
    have h := glws_f_subadd hd ηmin hηmin hη L.zero_mem (L.zsmul_mem hy m)
      (((m + n : ℕ) : ℤ) • y)
    have e1 : (m : ℤ) • y + (0 : Site d) = (m : ℤ) • y := add_zero _
    have e2 : (m : ℤ) • y + (n : ℤ) • y = ((m + n : ℕ) : ℤ) • y := by
      rw [← add_smul]; push_cast; rfl
    rw [e1, e2]
    exact h
  · have h1 := glws_g_nonneg ηmin L y m η
    have h2 := glws_g_nonneg ηmin L y n (((fun η : Site d → ℤ => fun z => η (y + z))^[m]) η)
    have h0 : glws_g ηmin L y (m + n) η = 0 := by
      unfold glws_g
      rw [if_neg hη]
    rw [h0]
    linarith

/-- A natural multiple `k ≤ n` of a site `v` lies in the box of radius `((|v|)+1) n`. -/
theorem glws_smul_mem_cent (v : Site d) (k n : ℕ) (hk : k ≤ n) :
    ((k : ℤ) • v) ∈ cent d (((mnorm v).toNat + 1) * n) := by
  intro i
  have hA : 0 ≤ mnorm v := lwc2_mnorm_nonneg v
  have hAtoNat : (((mnorm v).toNat : ℤ)) = mnorm v := Int.toNat_of_nonneg hA
  have hvi : |v i| ≤ mnorm v := lwc2_abs_coord_le_mnorm v i
  have h1 : |(k : ℤ) * v i| ≤ (n : ℤ) * mnorm v := by
    rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
    have hkn : (k : ℤ) ≤ (n : ℤ) := by exact_mod_cast hk
    have hv0 : 0 ≤ |v i| := abs_nonneg _
    nlinarith
  have h2 : (n : ℤ) * mnorm v ≤ ((((mnorm v).toNat + 1) * n : ℕ) : ℤ) := by
    push_cast
    rw [hAtoNat]
    have hn0 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
    nlinarith
  calc |(((k : ℤ) • v) i)| = |(k : ℤ) * v i| := rfl
    _ ≤ (n : ℤ) * mnorm v := h1
    _ ≤ _ := h2

theorem glws_g_eq_of_mem {ηmin : ℤ} {L : AddSubgroup (Site d)} {η : Site d → ℤ}
    (hη : η ∈ glws_G d ηmin L) (y : Site d)
    (n : ℕ) : glws_g ηmin L y n η = glws_f η ((n : ℤ) • y) := by
  unfold glws_g
  rw [if_pos hη]

/-- **The upward Lipschitz bound of the cocycle.**  On the local good event the paper's second bound
`T̃(x') ≤ T̃(x) + C |x - x'| + (log N)^γ` along the ray `n ↦ n y` gives the hypothesis of the
Lipschitz-transfer Kingman theorem. -/
theorem glws_g_lip {γ C : ℝ} (ηmin : ℤ) {L : AddSubgroup (Site d)} {η : Site d → ℤ}
    (hG : η ∈ glws_G d ηmin L) (hloc : glws_Loc0 d γ C η) (y : Site d) :
    ∃ C' : ℝ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ n' : ℕ, n ≤ n' → n' ≤ 2 * n →
      glws_g ηmin L y n' η ≤ glws_g ηmin L y n η + C' * ((n' : ℝ) - n) + ε * n := by
  obtain ⟨_, n0, hn0⟩ := hloc
  refine ⟨C * (mnorm y : ℝ), ?_⟩
  refine king_lip_of_log (fun n => glws_g ηmin L y n η) (C * (mnorm y : ℝ)) γ
    ((mnorm y).toNat + 1) (by omega) n0 ?_
  intro N hN n₁ n₂ h12 hmN
  have hx1 : ((n₁ : ℤ) • y) ∈ cent d N := by
    have := glws_smul_mem_cent y n₁ n₂ h12
    exact lwc3_cent_mono (by rw [mul_comm]; exact hmN) this
  have hx2 : ((n₂ : ℤ) • y) ∈ cent d N := by
    have := glws_smul_mem_cent y n₂ n₂ le_rfl
    exact lwc3_cent_mono (by rw [mul_comm]; exact hmN) this
  obtain ⟨a, ha, _, hloc2⟩ := hn0 N hN _ hx1
  obtain ⟨b, hb, hbb⟩ := hloc2 _ hx2
  have hnorm : mnorm ((n₁ : ℤ) • y - (n₂ : ℤ) • y) = ((n₂ : ℤ) - n₁) * mnorm y := by
    unfold mnorm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [← sub_mul, abs_mul]
    have h12' : (n₁ : ℤ) ≤ n₂ := by exact_mod_cast h12
    have : (0 : ℤ) ≤ (n₂ : ℤ) - n₁ := by linarith
    rw [abs_sub_comm, abs_of_nonneg this]
  rw [hnorm] at hbb
  have hga : glws_g ηmin L y n₁ η = (a : ℝ) := by
    rw [glws_g_eq_of_mem hG _ _]; unfold glws_f; rw [ha, ENat.toNat_coe]
  have hgb : glws_g ηmin L y n₂ η = (b : ℝ) := by
    rw [glws_g_eq_of_mem hG _ _]; unfold glws_f; rw [hb, ENat.toNat_coe]
  show glws_g ηmin L y n₂ η ≤ glws_g ηmin L y n₁ η + C * (mnorm y : ℝ) * ((n₂ : ℝ) - n₁) +
    Real.log N ^ γ
  rw [hga, hgb]
  have : ((((n₂ : ℤ) - n₁) * mnorm y : ℤ) : ℝ) = ((n₂ : ℝ) - n₁) * (mnorm y : ℝ) := by
    push_cast; ring
  rw [this] at hbb
  nlinarith [hbb]

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

/-- **The limit along a lattice vector `y ∈ L`.** -/
theorem glws_direction_limit (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (L : AddSubgroup (Site d)) (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hstat : StationaryOn d L P)
    (hG : ∀ᵐ η ∂P, η ∈ glws_G d ηmin L) {γ C : ℝ} (hloc : ∀ᵐ η ∂P, glws_Loc0 d γ C η)
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
  obtain ⟨ℓ, hℓ⟩ := king_lipKingman P (fun η z => η (y + z)) hmp herg (glws_g ηmin L y)
    (glws_g_subadd hd ηmin hηmin L hy) (glws_g_nonneg ηmin L y) (glws_g_measurable ηmin L y)
    (by
      filter_upwards [hG, hloc] with η h1 h2
      exact glws_g_lip ηmin h1 h2 y)
  refine ⟨ℓ, ?_⟩
  filter_upwards [hℓ, hG] with η h1 h2
  refine h1.congr (fun n => ?_)
  unfold glws_g
  rw [if_pos h2]

end Exploding
