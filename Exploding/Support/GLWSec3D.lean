/-
Proposition 5.1 of the paper (generalized last wave), the Section-3 assembly, part D:
every integer direction has an almost sure limit `N₀ v`, and `N₀` is nonnegative,
Lipschitz and homogeneous under natural scaling.
-/
import Exploding.Support.GLWSec3C

open Exploding LatticeProb MeasureTheory Filter
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-- The mixing hypothesis `(B)` of `glw2_Section3Convergence`, for the given sublattice. -/
def glws_Mix (d : ℕ) (L : AddSubgroup (Site d)) (P : Measure (Site d → ℤ)) : Prop :=
  ∀ (y : Site d), y ∈ L → y ≠ 0 →
    ∀ (s : Finset (Site d)) (S : Set (s → ℤ)), MeasurableSet S →
      ∃ n : ℕ, P (cylinder s S ∩
        (fun η : Site d → ℤ => fun z => η (y + z))^[n] ⁻¹' cylinder s S) =
        P (cylinder s S) * P (cylinder s S)

/-- A nonzero natural multiple of a nonzero site is nonzero. -/
theorem glws_nsmul_ne_zero {v : Site d} (hv : v ≠ 0) {q : ℕ} (hq : 0 < q) :
    (q : ℤ) • v ≠ 0 := by
  intro h
  apply hv
  funext i
  have := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  simpa using (mul_eq_zero.mp this).resolve_left hq'

/-- **The limit along every integer direction.** -/
theorem glws_lattice_limit (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0) (P : Measure (Site d → ℤ))
    (hP : IsProbabilityMeasure P) (hstat : StationaryOn d L P) (hKing : glw2_KingmanCore)
    (hG : ∀ᵐ η ∂P, η ∈ glws_G d ηmin L) {γ C : ℝ} (hC : 0 ≤ C)
    (hloc : ∀ᵐ η ∂P, glws_Loc0 d γ C η) (hmix : glws_Mix d L P) (v : Site d) :
    ∃ ℓ : ℝ, ∀ᵐ η ∂P,
      Tendsto (fun n : ℕ => glws_f η ((n : ℤ) • v) / (n : ℝ)) atTop (nhds ℓ) := by
  by_cases hv : v = 0
  · refine ⟨0, Eventually.of_forall fun η => ?_⟩
    subst hv
    have heq : (fun n : ℕ => glws_f η ((n : ℤ) • (0 : Site d)) / (n : ℝ))
        = fun n : ℕ => glws_f η 0 / (n : ℝ) := by
      funext n; simp
    rw [heq]
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  · obtain ⟨q, hq0, _, hqL⟩ := AddSubgroup.exists_nsmul_mem_of_index_ne_zero hL v
    have hyL : (q : ℤ) • v ∈ L := by rw [natCast_zsmul]; exact hqL
    have hy0 : (q : ℤ) • v ≠ 0 := glws_nsmul_ne_zero hv hq0
    obtain ⟨ℓy, hℓy⟩ := glws_direction_limit hd ηmin hηmin L P hP hstat hKing hG hloc
      ((q : ℤ) • v) hyL (hmix _ hyL hy0)
    refine ⟨ℓy * (q : ℝ)⁻¹, ?_⟩
    filter_upwards [hℓy, hG, hloc] with η h1 h2 h3
    exact glws_subseq_conv hC (glws_two_sided h3) v q hq0 ℓy h1

/-- The limits `N₀ v` along all integer directions, chosen. -/
theorem glws_lattice_data (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0) (P : Measure (Site d → ℤ))
    (hP : IsProbabilityMeasure P) (hstat : StationaryOn d L P) (hKing : glw2_KingmanCore)
    (hG : ∀ᵐ η ∂P, η ∈ glws_G d ηmin L) {γ C : ℝ} (hC : 0 ≤ C)
    (hloc : ∀ᵐ η ∂P, glws_Loc0 d γ C η) (hmix : glws_Mix d L P) :
    ∃ N0 : Site d → ℝ, ∀ v : Site d, ∀ᵐ η ∂P,
      Tendsto (fun n : ℕ => glws_f η ((n : ℤ) • v) / (n : ℝ)) atTop (nhds (N0 v)) := by
  have h := fun v => glws_lattice_limit hd ηmin hηmin L hL P hP hstat hKing hG hC hloc hmix v
  exact ⟨fun v => (h v).choose, fun v => (h v).choose_spec⟩

/-- A single background on which everything holds. -/
theorem glws_exists_good (L : AddSubgroup (Site d)) (P : Measure (Site d → ℤ))
    (hP : IsProbabilityMeasure P) (ηmin : ℤ) (hG : ∀ᵐ η ∂P, η ∈ glws_G d ηmin L) {γ C : ℝ} (hloc : ∀ᵐ η ∂P, glws_Loc0 d γ C η)
    (N0 : Site d → ℝ)
    (hN0 : ∀ v : Site d, ∀ᵐ η ∂P,
      Tendsto (fun n : ℕ => glws_f η ((n : ℤ) • v) / (n : ℝ)) atTop (nhds (N0 v))) :
    ∃ η : Site d → ℤ, η ∈ glws_G d ηmin L ∧ glws_Loc0 d γ C η ∧
      ∀ v : Site d,
        Tendsto (fun n : ℕ => glws_f η ((n : ℤ) • v) / (n : ℝ)) atTop (nhds (N0 v)) := by
  haveI := hP
  have hall : ∀ᵐ η ∂P, ∀ v : Site d,
      Tendsto (fun n : ℕ => glws_f η ((n : ℤ) • v) / (n : ℝ)) atTop (nhds (N0 v)) :=
    ae_all_iff.mpr hN0
  obtain ⟨η, h1, h2, h3⟩ := (hG.and (hloc.and hall)).exists
  exact ⟨η, h1, h2, h3⟩

/-- `N₀` is nonnegative. -/
theorem glws_N0_nonneg {η : Site d → ℤ} {N0 : Site d → ℝ}
    (hlat : ∀ v : Site d,
      Tendsto (fun n : ℕ => glws_f η ((n : ℤ) • v) / (n : ℝ)) atTop (nhds (N0 v)))
    (v : Site d) : 0 ≤ N0 v := by
  refine ge_of_tendsto' (hlat v) fun n => ?_
  unfold glws_f
  positivity

/-- `N₀` is Lipschitz for the `ℓ¹` norm. -/
theorem glws_N0_lip {γ C : ℝ} {η : Site d → ℤ}
    {N0 : Site d → ℝ} (hloc : glws_Loc0 d γ C η)
    (hlat : ∀ v : Site d,
      Tendsto (fun n : ℕ => glws_f η ((n : ℤ) • v) / (n : ℝ)) atTop (nhds (N0 v)))
    (v w : Site d) : |N0 v - N0 w| ≤ C * (mnorm (v - w) : ℝ) := by
  exact glws_lip_limit (glws_two_sided hloc) v w _ _ (hlat v) (hlat w)

/-- `N₀` is homogeneous under natural scaling. -/
theorem glws_N0_nsmul {η : Site d → ℤ} {N0 : Site d → ℝ}
    (hlat : ∀ v : Site d,
      Tendsto (fun n : ℕ => glws_f η ((n : ℤ) • v) / (n : ℝ)) atTop (nhds (N0 v)))
    (v : Site d) (k : ℕ) : N0 ((k : ℤ) • v) = (k : ℝ) * N0 v := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 : N0 0 = 0 := by
      have h1 := hlat 0
      have heq : (fun n : ℕ => glws_f η ((n : ℤ) • (0 : Site d)) / (n : ℝ))
          = fun n : ℕ => glws_f η 0 / (n : ℝ) := by
        funext n; simp
      rw [heq] at h1
      exact tendsto_nhds_unique h1
        (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
    simpa using h0
  · have hpt : ∀ n : ℕ, glws_f η ((n : ℤ) • ((k : ℤ) • v)) / (n : ℝ)
        = (k : ℝ) * (glws_f η (((n * k : ℕ) : ℤ) • v) / ((n * k : ℕ) : ℝ)) ∨ n = 0 := by
      intro n
      rcases Nat.eq_zero_or_pos n with h0 | hn0
      · exact Or.inr h0
      · left
        have hidx : (n : ℤ) • ((k : ℤ) • v) = (((n * k : ℕ) : ℤ)) • v := by
          rw [smul_smul, Nat.cast_mul]
        rw [hidx]
        have hk0 : (k : ℝ) ≠ 0 := by positivity
        have hn0' : (n : ℝ) ≠ 0 := by positivity
        have hcast : ((n * k : ℕ) : ℝ) = (n : ℝ) * (k : ℝ) := by push_cast; ring
        rw [hcast]
        field_simp
    have hcomp : Tendsto (fun n : ℕ => n * k) atTop atTop :=
      Filter.tendsto_atTop_atTop_of_monotone (fun a b hab => Nat.mul_le_mul_right k hab)
        (fun b => ⟨b, Nat.le_mul_of_pos_right b hk⟩)
    have h2' : Tendsto (fun n : ℕ => glws_f η (((n * k : ℕ) : ℤ) • v) / ((n * k : ℕ) : ℝ))
        atTop (nhds (N0 v)) := (hlat v).comp hcomp
    have h3 := h2'.const_mul (k : ℝ)
    have h4 : Tendsto (fun n : ℕ => glws_f η ((n : ℤ) • ((k : ℤ) • v)) / (n : ℝ)) atTop
        (nhds ((k : ℝ) * N0 v)) := by
      refine h3.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      rcases hpt n with h | h
      · exact h.symm
      · omega
    exact tendsto_nhds_unique (hlat ((k : ℤ) • v)) h4

end Exploding
