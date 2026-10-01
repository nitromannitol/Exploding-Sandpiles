/-
Proposition 5.1 of the paper (generalized last wave), the Section-3 assembly, part F:
a nonnegative-homogeneous, subadditive, Lipschitz function on the integer lattice extends to a
continuous, convex, one-homogeneous function on `ℝ^d`.  This is the passage from the integer
directions to the limit shape `N`.
-/
import Exploding.Support.GLWSec3E

open Exploding LatticeProb MeasureTheory Filter
open scoped Classical NNReal

namespace Exploding

variable {d : ℕ}

/-- The rational points `v / q` of `ℝ^d`. -/
def glws_D (d : ℕ) : Set (Fin d → ℝ) :=
  Set.range (fun p : Site d × ℕ => ((p.2 + 1 : ℕ) : ℝ)⁻¹ • lwc2_toReal p.1)

/-- The value of the limit shape at a rational point, read from any representation. -/
noncomputable def glws_Nt (N0 : Site d → ℝ) (y : Fin d → ℝ) : ℝ :=
  if h : ∃ p : Site d × ℕ, ((p.2 + 1 : ℕ) : ℝ)⁻¹ • lwc2_toReal p.1 = y then
    N0 (Classical.choose h).1 / (((Classical.choose h).2 + 1 : ℕ) : ℝ)
  else 0

/-- Clearing denominators: `v / q = v' / q'` forces `q' v = q v'`. -/
theorem glws_cross {v v' : Site d} {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (h : (q' : ℝ)⁻¹ • lwc2_toReal v' = (q : ℝ)⁻¹ • lwc2_toReal v) :
    (q : ℤ) • v' = (q' : ℤ) • v := by
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, lwc2_toReal, smul_eq_mul] at hi
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hq'R : (q' : ℝ) ≠ 0 := by exact_mod_cast hq'.ne'
  have h2 : (q : ℝ) * (v' i : ℝ) = (q' : ℝ) * (v i : ℝ) := by
    field_simp at hi
    linarith
  have h3 : ((q : ℤ) * v' i : ℤ) = ((q' : ℤ) * v i : ℤ) := by exact_mod_cast h2
  simpa using h3

/-- The value at a rational point is independent of the representation. -/
theorem glws_Nt_rep {N0 : Site d → ℝ} (hhom : ∀ (k : ℕ) (v : Site d), N0 ((k : ℤ) • v) = k * N0 v)
    (v : Site d) {q : ℕ} (hq : 0 < q) :
    glws_Nt N0 ((q : ℝ)⁻¹ • lwc2_toReal v) = N0 v / (q : ℝ) := by
  have hex : ∃ p : Site d × ℕ, ((p.2 + 1 : ℕ) : ℝ)⁻¹ • lwc2_toReal p.1 =
      (q : ℝ)⁻¹ • lwc2_toReal v := by
    refine ⟨(v, q - 1), ?_⟩
    simp [Nat.sub_add_cancel hq]
  unfold glws_Nt
  rw [dif_pos hex]
  have hspec := Classical.choose_spec hex
  set v' := (Classical.choose hex).1 with hv'
  set q' := (Classical.choose hex).2 + 1 with hq'
  have hq'pos : 0 < q' := Nat.succ_pos _
  have hvec := glws_cross hq hq'pos hspec
  have e1 := hhom q v'
  have e2 := hhom q' v
  rw [hvec] at e1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'R : (0 : ℝ) < q' := by exact_mod_cast hq'pos
  rw [div_eq_div_iff hq'R.ne' hqR.ne']
  linarith

/-- The `ℓ¹` distance of two rational points, in terms of the integer data. -/
theorem glws_cross_dist (v v' : Site d) {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') :
    ((mnorm ((q' : ℤ) • v - (q : ℤ) • v') : ℤ) : ℝ) / ((q : ℝ) * (q' : ℝ)) =
      ∑ i : Fin d, |((q : ℝ)⁻¹ • lwc2_toReal v) i - ((q' : ℝ)⁻¹ • lwc2_toReal v') i| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'R : (0 : ℝ) < q' := by exact_mod_cast hq'
  unfold mnorm
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, lwc2_toReal]
  push_cast
  rw [show ((q' : ℝ) * (v i : ℝ) - (q : ℝ) * (v' i : ℝ)) = ((q : ℝ) * (q' : ℝ)) *
      ((q : ℝ)⁻¹ * (v i : ℝ) - (q' : ℝ)⁻¹ * (v' i : ℝ)) by field_simp]
  rw [abs_mul, abs_of_pos (mul_pos hqR hq'R)]
  field_simp

theorem glws_inv_succ_tendsto :
    Tendsto (fun m : ℕ => (((m + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) := by
  have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  refine this.congr fun m => ?_
  push_cast
  rw [one_div]

/-- The rational points are dense. -/
theorem glws_D_dense (d : ℕ) : Dense (glws_D d) := by
  intro y
  rw [mem_closure_iff_seq_limit]
  refine ⟨fun m : ℕ => ((m + 1 : ℕ) : ℝ)⁻¹ • lwc2_toReal (nearestSite (((m + 1 : ℕ) : ℝ) • y)),
    fun m => ⟨(nearestSite (((m + 1 : ℕ) : ℝ) • y), m), rfl⟩, ?_⟩
  rw [tendsto_pi_nhds]
  intro i
  have hb : ∀ m : ℕ, |((((m + 1 : ℕ) : ℝ)⁻¹ • lwc2_toReal
      (nearestSite (((m + 1 : ℕ) : ℝ) • y))) i) - y i| ≤ (((m + 1 : ℕ) : ℝ))⁻¹ := by
    intro m
    have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have h1 := lwc2_nearestSite_sub_le (((m + 1 : ℕ) : ℝ) • y) i
    simp only [Pi.smul_apply, smul_eq_mul, lwc2_toReal] at h1 ⊢
    have : (((m + 1 : ℕ) : ℝ))⁻¹ * ((nearestSite (((m + 1 : ℕ) : ℝ) • y) i : ℤ) : ℝ) - y i =
        (((m + 1 : ℕ) : ℝ))⁻¹ * (((nearestSite (((m + 1 : ℕ) : ℝ) • y) i : ℤ) : ℝ) -
          ((m + 1 : ℕ) : ℝ) * y i) := by field_simp
    rw [this, abs_mul, abs_of_pos (inv_pos.mpr hpos)]
    have h2 : |(((nearestSite (((m + 1 : ℕ) : ℝ) • y) i : ℤ) : ℝ) -
          ((m + 1 : ℕ) : ℝ) * y i)| ≤ 1 := by
      simpa [Pi.smul_apply, smul_eq_mul] using h1
    calc (((m + 1 : ℕ) : ℝ))⁻¹ * |(((nearestSite (((m + 1 : ℕ) : ℝ) • y) i : ℤ) : ℝ) -
          ((m + 1 : ℕ) : ℝ) * y i)| ≤ (((m + 1 : ℕ) : ℝ))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left h2 (inv_pos.mpr hpos).le
      _ = _ := mul_one _
  have hlim : Tendsto (fun m : ℕ => (((m + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) := by
    exact glws_inv_succ_tendsto
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_) hlim
  simpa [Real.norm_eq_abs] using hb m

/-- **Extension.**  A nonnegative-homogeneous, subadditive, Lipschitz function on the integer
lattice extends to a continuous, convex, one-homogeneous function on `ℝ^d`. -/
theorem glws_extend (C : ℝ) (hC : 0 ≤ C) (N0 : Site d → ℝ)
    (hlip : ∀ v w : Site d, |N0 v - N0 w| ≤ C * (mnorm (v - w) : ℝ))
    (hhom : ∀ (k : ℕ) (v : Site d), N0 ((k : ℤ) • v) = k * N0 v)
    (hsub : ∀ v w : Site d, N0 (v + w) ≤ N0 v + N0 w) :
    ∃ N : (Fin d → ℝ) → ℝ, Continuous N ∧ ConvexOn ℝ Set.univ N ∧
      (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
      ∀ v : Site d, N (lwc2_toReal v) = N0 v := by
  -- the function on the rational points is Lipschitz
  have hLipD : LipschitzOnWith (Real.toNNReal (C * (d : ℝ))) (glws_Nt N0) (glws_D d) := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_
    obtain ⟨⟨v, m⟩, rfl⟩ := hy
    obtain ⟨⟨v', m'⟩, rfl⟩ := hy'
    simp only at *
    set q : ℕ := m + 1
    set q' : ℕ := m' + 1
    have hq : 0 < q := Nat.succ_pos _
    have hq' : 0 < q' := Nat.succ_pos _
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hq'R : (0 : ℝ) < q' := by exact_mod_cast hq'
    rw [glws_Nt_rep hhom v hq, glws_Nt_rep hhom v' hq', Real.dist_eq]
    have h1 : N0 v / (q : ℝ) - N0 v' / (q' : ℝ) =
        (N0 ((q' : ℤ) • v) - N0 ((q : ℤ) • v')) / ((q : ℝ) * (q' : ℝ)) := by
      rw [hhom q' v, hhom q v']
      field_simp
    rw [h1, abs_div, abs_of_pos (mul_pos hqR hq'R), div_le_iff₀ (mul_pos hqR hq'R)]
    have h2 := hlip ((q' : ℤ) • v) ((q : ℤ) • v')
    have h3 := glws_cross_dist v v' hq hq'
    rw [div_eq_iff (mul_pos hqR hq'R).ne'] at h3
    -- the `ℓ¹` distance is at most `d` times the sup distance
    have h4 : ∑ i : Fin d, |((q : ℝ)⁻¹ • lwc2_toReal v) i - ((q' : ℝ)⁻¹ • lwc2_toReal v') i|
        ≤ (d : ℝ) * dist ((q : ℝ)⁻¹ • lwc2_toReal v) ((q' : ℝ)⁻¹ • lwc2_toReal v') := by
      calc _ ≤ ∑ _i : Fin d, dist ((q : ℝ)⁻¹ • lwc2_toReal v) ((q' : ℝ)⁻¹ • lwc2_toReal v') :=
            Finset.sum_le_sum fun i _ => by
              rw [← Real.dist_eq]
              exact dist_le_pi_dist _ _ i
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hK : ((Real.toNNReal (C * (d : ℝ)) : ℝ≥0) : ℝ) = C * (d : ℝ) :=
      Real.coe_toNNReal _ (mul_nonneg hC (Nat.cast_nonneg d))
    rw [hK]
    have h5 := mul_le_mul_of_nonneg_left h4 hC
    have hdist0 : 0 ≤ dist ((q : ℝ)⁻¹ • lwc2_toReal v) ((q' : ℝ)⁻¹ • lwc2_toReal v') := dist_nonneg
    nlinarith [h2, h3, h5, mul_pos hqR hq'R]
  obtain ⟨N, hNlip, hNeq⟩ := hLipD.extend_real
  have hNcont : Continuous N := hNlip.continuous
  have hDN : ∀ {y : Fin d → ℝ}, y ∈ glws_D d → N y = glws_Nt N0 y := fun hy => (hNeq hy).symm
  -- values at rational points
  have hrat : ∀ (v : Site d) {q : ℕ}, 0 < q →
      N ((q : ℝ)⁻¹ • lwc2_toReal v) = N0 v / (q : ℝ) := by
    intro v q hq
    have hmem : (q : ℝ)⁻¹ • lwc2_toReal v ∈ glws_D d :=
      ⟨(v, q - 1), by simp [Nat.sub_add_cancel hq]⟩
    rw [hDN hmem, glws_Nt_rep hhom v hq]
  have hdense := glws_D_dense d
  -- lattice values
  have hlattice : ∀ v : Site d, N (lwc2_toReal v) = N0 v := by
    intro v
    have := hrat v (q := 1) Nat.one_pos
    simpa using this
  -- homogeneity at rational scalars on rational points
  have hhomD : ∀ (a b : ℕ), 0 < b → ∀ y ∈ glws_D d, N (((a : ℝ) / (b : ℝ)) • y) = ((a : ℝ) / (b : ℝ)) * N y := by
    intro a b hb y hy
    obtain ⟨⟨v, m⟩, rfl⟩ := hy
    simp only
    set q : ℕ := m + 1
    have hq : 0 < q := Nat.succ_pos _
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have hscal : ((a : ℝ) / (b : ℝ)) • ((q : ℝ)⁻¹ • lwc2_toReal v) =
        ((b * q : ℕ) : ℝ)⁻¹ • lwc2_toReal ((a : ℤ) • v) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, lwc2_toReal]
      push_cast
      field_simp
    rw [hscal, hrat _ (Nat.mul_pos hb hq), hrat v hq, hhom a v]
    push_cast
    field_simp
  -- homogeneity at rational scalars
  have hhomQ : ∀ (a b : ℕ), 0 < b → ∀ y : Fin d → ℝ,
      N (((a : ℝ) / (b : ℝ)) • y) = ((a : ℝ) / (b : ℝ)) * N y := by
    intro a b hb
    have hc1 : Continuous fun y : Fin d → ℝ => N (((a : ℝ) / (b : ℝ)) • y) :=
      hNcont.comp (continuous_const_smul _)
    have hc2 : Continuous fun y : Fin d → ℝ => ((a : ℝ) / (b : ℝ)) * N y :=
      continuous_const.mul hNcont
    have := Continuous.ext_on hdense hc1 hc2 (fun y hy => hhomD a b hb y hy)
    exact fun y => congrFun this y
  -- homogeneity at real scalars
  have hhomR : ∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y := by
    intro c hc y
    have hseq : Tendsto (fun k : ℕ => ((⌈(k + 1 : ℝ) * c⌉₊ : ℕ) : ℝ) / (((k + 1 : ℕ)) : ℝ))
        atTop (nhds c) := by
      have hb : ∀ k : ℕ, |((⌈(k + 1 : ℝ) * c⌉₊ : ℕ) : ℝ) / (((k + 1 : ℕ)) : ℝ) - c| ≤
          (((k + 1 : ℕ) : ℝ))⁻¹ := by
        intro k
        have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
        have h1 : (k + 1 : ℝ) * c ≤ ⌈(k + 1 : ℝ) * c⌉₊ := Nat.le_ceil _
        have h2 : (⌈(k + 1 : ℝ) * c⌉₊ : ℝ) < (k + 1 : ℝ) * c + 1 := Nat.ceil_lt_add_one (by positivity)
        have h3 : ((⌈(k + 1 : ℝ) * c⌉₊ : ℕ) : ℝ) / (((k + 1 : ℕ)) : ℝ) - c =
            ((⌈(k + 1 : ℝ) * c⌉₊ : ℝ) - (k + 1 : ℝ) * c) / ((k + 1 : ℕ) : ℝ) := by
          push_cast; field_simp
        rw [h3, abs_div, abs_of_pos hpos, div_le_iff₀ hpos, inv_mul_cancel₀ hpos.ne']
        rw [abs_le]
        constructor <;> linarith
      have hlim : Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) := by
        exact glws_inv_succ_tendsto
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hlim
      simpa [Real.norm_eq_abs] using hb k
    have h1 : Tendsto (fun k : ℕ => N ((((⌈(k + 1 : ℝ) * c⌉₊ : ℕ) : ℝ) / (((k + 1 : ℕ)) : ℝ)) • y))
        atTop (nhds (N (c • y))) :=
      (hNcont.tendsto _).comp (hseq.smul_const y)
    have h2 : Tendsto (fun k : ℕ => (((⌈(k + 1 : ℝ) * c⌉₊ : ℕ) : ℝ) / (((k + 1 : ℕ)) : ℝ)) * N y)
        atTop (nhds (c * N y)) := hseq.mul_const _
    have h3 : (fun k : ℕ => N ((((⌈(k + 1 : ℝ) * c⌉₊ : ℕ) : ℝ) / (((k + 1 : ℕ)) : ℝ)) • y)) =
        fun k : ℕ => (((⌈(k + 1 : ℝ) * c⌉₊ : ℕ) : ℝ) / (((k + 1 : ℕ)) : ℝ)) * N y :=
      funext fun k => hhomQ _ _ (Nat.succ_pos k) y
    rw [h3] at h1
    exact tendsto_nhds_unique h1 h2
  -- subadditivity on rational points
  have hsubD : ∀ y ∈ glws_D d, ∀ y' ∈ glws_D d, N (y + y') ≤ N y + N y' := by
    intro y hy y' hy'
    obtain ⟨⟨v, m⟩, rfl⟩ := hy
    obtain ⟨⟨v', m'⟩, rfl⟩ := hy'
    simp only
    set q : ℕ := m + 1
    set q' : ℕ := m' + 1
    have hq : 0 < q := Nat.succ_pos _
    have hq' : 0 < q' := Nat.succ_pos _
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hq'R : (0 : ℝ) < q' := by exact_mod_cast hq'
    have hsum : (q : ℝ)⁻¹ • lwc2_toReal v + (q' : ℝ)⁻¹ • lwc2_toReal v' =
        ((q * q' : ℕ) : ℝ)⁻¹ • lwc2_toReal ((q' : ℤ) • v + (q : ℤ) • v') := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, lwc2_toReal]
      push_cast
      field_simp
    rw [hsum, hrat _ (Nat.mul_pos hq hq'), hrat v hq, hrat v' hq']
    have h1 := hsub ((q' : ℤ) • v) ((q : ℤ) • v')
    rw [hhom q' v, hhom q v'] at h1
    push_cast
    rw [div_le_iff₀ (mul_pos hqR hq'R)]
    have : (N0 v / (q : ℝ) + N0 v' / (q' : ℝ)) * ((q : ℝ) * (q' : ℝ)) =
        (q' : ℝ) * N0 v + (q : ℝ) * N0 v' := by field_simp
    rw [this]
    linarith
  have hsubA : ∀ y y' : Fin d → ℝ, N (y + y') ≤ N y + N y' := by
    have hclosed : IsClosed {p : (Fin d → ℝ) × (Fin d → ℝ) | N (p.1 + p.2) ≤ N p.1 + N p.2} :=
      isClosed_le (hNcont.comp (continuous_fst.add continuous_snd))
        (hNcont.comp continuous_fst |>.add (hNcont.comp continuous_snd))
    have hprod : Dense (glws_D d ×ˢ glws_D d) := hdense.prod hdense
    have hsubset : glws_D d ×ˢ glws_D d ⊆
        {p : (Fin d → ℝ) × (Fin d → ℝ) | N (p.1 + p.2) ≤ N p.1 + N p.2} :=
      fun p hp => hsubD p.1 hp.1 p.2 hp.2
    have hall := hprod.closure_eq ▸ closure_minimal hsubset hclosed
    intro y y'
    exact hall (Set.mem_univ (y, y'))
  refine ⟨N, hNcont, ?_, hhomR, hlattice⟩
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  calc N (a • x + b • y) ≤ N (a • x) + N (b • y) := hsubA _ _
    _ = a * N x + b * N y := by rw [hhomR a ha, hhomR b hb]

end Exploding
