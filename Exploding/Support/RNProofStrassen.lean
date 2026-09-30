/-
Strassen's theorem for a closed preorder on a second countable compact Hausdorff space, and the
consequence used in the proof of Proposition 2.2: a measurable event of the larger coordinate that
contains a measurable almost sure event of the smaller one.
-/
import Mathlib
import Exploding.Support.Percolation

open MeasureTheory Set
open scoped CompactlySupported

set_option linter.unusedSectionVars false

namespace Exploding

theorem rn_integral_le_of_superlevel {X : Type*} [MeasurableSpace X] (ν μ : Measure X)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] (φ : X → ℝ) (hφ : Measurable φ)
    (a b : ℝ) (hab : ∀ x, a ≤ φ x ∧ φ x ≤ b)
    (h : ∀ t : ℝ, ν {x | t < φ x} ≤ μ {x | t < φ x}) :
    ∫ x, φ x ∂ν ≤ ∫ x, φ x ∂μ := by
  have hψm : Measurable (fun x => φ x - a) := hφ.sub_const a
  have hψnn : ∀ κ : Measure X, 0 ≤ᵐ[κ] (fun x => φ x - a) := fun κ =>
    Filter.Eventually.of_forall (fun x => by simp only [Pi.zero_apply]; linarith [(hab x).1])
  have hφint : ∀ (κ : Measure X) [IsProbabilityMeasure κ], Integrable φ κ := by
    intro κ _
    refine Integrable.of_bound (C := max |a| |b|) hφ.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs]
    exact abs_le_max_abs_abs (hab x).1 (hab x).2
  have key : ∀ (κ : Measure X) [IsProbabilityMeasure κ],
      ∫ x, φ x ∂κ = a + (∫⁻ t in Ioi (0:ℝ), κ {x | t < φ x - a}).toReal := by
    intro κ _
    have h1 : ∫ x, φ x ∂κ = a + ∫ x, (φ x - a) ∂κ := by
      rw [integral_sub (hφint κ) (integrable_const a)]
      simp
    rw [h1, integral_eq_lintegral_of_nonneg_ae (hψnn κ) hψm.aestronglyMeasurable,
      lintegral_eq_lintegral_meas_lt κ (hψnn κ) hψm.aemeasurable]
  have hfin : ∀ (κ : Measure X) [IsProbabilityMeasure κ],
      (∫⁻ t in Ioi (0:ℝ), κ {x | t < φ x - a}) ≠ ⊤ := by
    intro κ _
    rw [← lintegral_eq_lintegral_meas_lt κ (hψnn κ) hψm.aemeasurable]
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono (g := fun _ => ENNReal.ofReal (b - a)) (fun x => ?_)) ?_)
    · exact ENNReal.ofReal_le_ofReal (by linarith [(hab x).2])
    · simp
  rw [key ν, key μ]
  refine add_le_add_right (ENNReal.toReal_mono (hfin μ) (lintegral_mono fun t => ?_)) a
  have := h (t + a)
  have e : {x | t + a < φ x} = {x | t < φ x - a} := by
    ext x; simp only [mem_setOf_eq]; constructor <;> intro hh <;> linarith
  rwa [e] at this


section Strassen

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω]
  [SecondCountableTopology Ω] [MeasurableSpace Ω] [BorelSpace Ω]

noncomputable def rn_intLin (ν : Measure Ω) [IsFiniteMeasure ν] : C(Ω, ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ x, f x ∂ν
  map_add' f g := integral_add
    (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f))
    (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g))
  map_smul' c f := by simp [integral_const_mul]

noncomputable def rn_sumLin : (C(Ω, ℝ) × C(Ω, ℝ)) →ₗ[ℝ] C(Ω × Ω, ℝ) where
  toFun fg := fg.1.comp ⟨Prod.fst, continuous_fst⟩ + fg.2.comp ⟨Prod.snd, continuous_snd⟩
  map_add' f g := by ext z; simp; ring
  map_smul' c f := by ext z; simp

noncomputable def rn_sup (D : Set (Ω × Ω)) (F : C(Ω × Ω, ℝ)) : ℝ := sSup (F '' D)

theorem rn_sup_le {D : Set (Ω × Ω)} (hne : D.Nonempty) {F : C(Ω × Ω, ℝ)} {c : ℝ}
    (h : ∀ z ∈ D, F z ≤ c) : rn_sup D F ≤ c :=
  csSup_le (hne.image _) (by rintro _ ⟨z, hz, rfl⟩; exact h z hz)

theorem rn_le_sup {D : Set (Ω × Ω)} (hD : IsCompact D) {F : C(Ω × Ω, ℝ)} {z : Ω × Ω}
    (hz : z ∈ D) : F z ≤ rn_sup D F :=
  le_csSup ((hD.image F.continuous).bddAbove) ⟨z, hz, rfl⟩

/-- The key inequality of Strassen's theorem. -/
theorem rn_strassen_ineq (le : Ω → Ω → Prop) (hrefl : ∀ x, le x x)
    (htrans : ∀ x y z, le x y → le y z → le x z)
    (hclosed : IsClosed {z : Ω × Ω | le z.1 z.2})
    (ν μ : Measure Ω) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hdom : ∀ A : Set Ω, MeasurableSet A → (∀ x y, le x y → x ∈ A → y ∈ A) → ν A ≤ μ A)
    (f g : C(Ω, ℝ)) :
    ∫ x, f x ∂ν + ∫ x, g x ∂μ ≤ rn_sup {z : Ω × Ω | le z.1 z.2} (rn_sumLin (f, g)) := by
  set D : Set (Ω × Ω) := {z | le z.1 z.2} with hD
  have hDc : IsCompact D := hclosed.isCompact
  set s := rn_sup D (rn_sumLin (f, g)) with hs
  -- sections
  have hsec : ∀ x, IsCompact {y | le x y} := fun x =>
    (hclosed.preimage (continuous_const.prodMk continuous_id)).isCompact
  have hsne : ∀ x, ({y | le x y}).Nonempty := fun x => ⟨x, hrefl x⟩
  set gu : Ω → ℝ := fun x => sSup (g '' {y | le x y}) with hgu
  have hgu_ge : ∀ x y, le x y → g y ≤ gu x := fun x y hxy =>
    le_csSup (((hsec x).image g.continuous).bddAbove) ⟨y, hxy, rfl⟩
  have hgu_mem : ∀ x, ∃ y, le x y ∧ g y = gu x := fun x => by
    have := ((hsec x).image g.continuous).sSup_mem ((hsne x).image g)
    obtain ⟨y, hy, hyeq⟩ := this
    exact ⟨y, hy, hyeq⟩
  have hgu_anti : ∀ x x', le x x' → gu x' ≤ gu x := fun x x' hxx' =>
    csSup_le ((hsne x').image g) (by
      rintro _ ⟨y, hy, rfl⟩
      exact hgu_ge x y (htrans _ _ _ hxx' hy))
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x, |g x| ≤ C := by
    have := (isCompact_range g.continuous).isBounded
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp this
    exact ⟨C, fun x => by simpa using hC (g x) ⟨x, rfl⟩⟩
  have hgu_le : ∀ x, gu x ≤ C := fun x =>
    csSup_le ((hsne x).image g) (by rintro _ ⟨y, hy, rfl⟩; exact (le_abs_self _).trans (hC y))
  have hgu_ge' : ∀ x, g x ≤ gu x := fun x => hgu_ge x x (hrefl x)
  have hgu_meas : Measurable gu := by
    refine measurable_of_Ici (fun t => ?_)
    have : gu ⁻¹' Ici t = Prod.fst '' (D ∩ {z | t ≤ g z.2}) := by
      ext x
      simp only [mem_preimage, mem_Ici, mem_image, mem_inter_iff, mem_setOf_eq, hD, Prod.exists,
        exists_and_right, exists_eq_right]
      constructor
      · intro ht
        obtain ⟨y, hy, hyeq⟩ := hgu_mem x
        exact ⟨y, ⟨hy, by rw [hyeq]; exact ht⟩⟩
      · rintro ⟨y, hy, hty⟩
        exact hty.trans (hgu_ge x y hy)
    rw [this]
    exact ((hDc.inter_right (isClosed_le continuous_const (g.continuous.comp continuous_snd))).image
      continuous_fst).isClosed.measurableSet
  -- the function φ
  set φ : Ω → ℝ := fun x => s - gu x with hφ
  have hφm : Measurable φ := measurable_const.sub hgu_meas
  have hf_le : ∀ x, f x ≤ φ x := fun x => by
    have : f x + gu x ≤ s := by
      have h2 : gu x ≤ s - f x := csSup_le ((hsne x).image g) (by
        rintro _ ⟨y, hy, rfl⟩
        have hz : (rn_sumLin (f, g)) (x, y) = f x + g y := by simp [rn_sumLin]
        have h4 := rn_le_sup (F := rn_sumLin (f, g)) hDc (z := (x, y)) hy
        rw [hz] at h4
        have h5 : f x + g y ≤ s := h4
        linarith)
      linarith
    simp only [hφ]; linarith
  have hφ_mono : ∀ x y, le x y → φ x ≤ φ y := fun x y hxy => by
    simp only [hφ]; linarith [hgu_anti x y hxy]
  have hdom' : ∀ t : ℝ, ν {x | t < φ x} ≤ μ {x | t < φ x} := fun t =>
    hdom _ (measurableSet_lt measurable_const hφm) (fun x y hxy hx => by
      simp only [mem_setOf_eq] at hx ⊢; exact lt_of_lt_of_le hx (hφ_mono x y hxy))
  have hφint : ∀ (κ : Measure Ω) [IsProbabilityMeasure κ], Integrable φ κ := by
    intro κ _
    refine Integrable.of_bound (C := |s| + C) hφm.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    have h1 := hgu_le x
    have h2 := hgu_ge' x
    have h3 := hC x
    rw [Real.norm_eq_abs, abs_le]
    have := abs_le.mp h3
    constructor <;> simp only [hφ] <;> cases abs_cases s <;> linarith [this.1, this.2]
  have hguint : ∀ (κ : Measure Ω) [IsProbabilityMeasure κ], Integrable gu κ := by
    intro κ _
    refine Integrable.of_bound (C := C) hgu_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    have h3 := abs_le.mp (hC x)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hgu_le x, hgu_ge' x, h3.1, h3.2]
  have hcint : ∀ (κ : Measure Ω) [IsProbabilityMeasure κ] (h : C(Ω, ℝ)), Integrable h κ :=
    fun κ _ h => h.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace h)
  have step1 : ∫ x, φ x ∂ν ≤ ∫ x, φ x ∂μ := by
    refine rn_integral_le_of_superlevel ν μ φ hφm (s - C) (s + |C|) (fun x => ?_) hdom'
    have := hgu_le x
    have h3 := abs_le.mp (hC x)
    simp only [hφ]
    constructor <;> linarith [le_abs_self C, hgu_ge' x, h3.1, h3.2]
  have step2 : ∫ x, f x ∂ν ≤ ∫ x, φ x ∂ν := integral_mono (hcint ν f) (hφint ν) hf_le
  have step3 : ∫ x, φ x ∂μ = s - ∫ x, gu x ∂μ := by
    simp only [hφ]
    rw [integral_sub (integrable_const s) (hguint μ)]
    simp
  have step4 : ∫ x, g x ∂μ ≤ ∫ x, gu x ∂μ := integral_mono (hcint μ g) (hguint μ) hgu_ge'
  have hlhs : rn_sup D (rn_sumLin (f, g)) = s := rfl
  linarith


theorem rn_sup_zero {D : Set (Ω × Ω)} (hD : IsCompact D) (hne : D.Nonempty) :
    rn_sup D (0 : C(Ω × Ω, ℝ)) = 0 := by
  apply le_antisymm
  · exact rn_sup_le hne (fun z _ => le_refl _)
  · obtain ⟨z, hz⟩ := hne
    exact rn_le_sup hD (F := 0) hz

theorem rn_sup_add_le {D : Set (Ω × Ω)} (hD : IsCompact D) (hne : D.Nonempty)
    (F G : C(Ω × Ω, ℝ)) : rn_sup D (F + G) ≤ rn_sup D F + rn_sup D G :=
  rn_sup_le hne (fun z hz => by
    simp only [ContinuousMap.add_apply]
    exact add_le_add (rn_le_sup hD hz) (rn_le_sup hD hz))

theorem rn_sup_smul {D : Set (Ω × Ω)} (hD : IsCompact D) (hne : D.Nonempty)
    {c : ℝ} (hc : 0 < c) (F : C(Ω × Ω, ℝ)) : rn_sup D (c • F) = c * rn_sup D F := by
  apply le_antisymm
  · refine rn_sup_le hne (fun z hz => ?_)
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (rn_le_sup hD hz) hc.le
  · have : rn_sup D F ≤ c⁻¹ * rn_sup D (c • F) := by
      refine rn_sup_le hne (fun z hz => ?_)
      have := rn_le_sup hD (F := c • F) hz
      simp only [ContinuousMap.smul_apply, smul_eq_mul] at this
      rw [le_inv_mul_iff₀ hc]; linarith
    rw [le_inv_mul_iff₀ hc] at this; linarith

/-- Existence of the extended functional (Hahn-Banach step). -/
theorem rn_strassen_functional (le : Ω → Ω → Prop) (hrefl : ∀ x, le x x)
    (htrans : ∀ x y z, le x y → le y z → le x z)
    (hclosed : IsClosed {z : Ω × Ω | le z.1 z.2})
    (ν μ : Measure Ω) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hdom : ∀ A : Set Ω, MeasurableSet A → (∀ x y, le x y → x ∈ A → y ∈ A) → ν A ≤ μ A) :
    ∃ Λ : C(Ω × Ω, ℝ) →ₗ[ℝ] ℝ,
      (∀ F, Λ F ≤ rn_sup {z : Ω × Ω | le z.1 z.2} F) ∧
      (∀ f g : C(Ω, ℝ), Λ (rn_sumLin (f, g)) = ∫ x, f x ∂ν + ∫ x, g x ∂μ) := by
  set D : Set (Ω × Ω) := {z | le z.1 z.2} with hD
  have hDc : IsCompact D := hclosed.isCompact
  haveI : Nonempty Ω := nonempty_of_isProbabilityMeasure ν
  obtain ⟨x0⟩ := this
  have hDne : D.Nonempty := ⟨(x0, x0), hrefl x0⟩
  set Φ : (C(Ω, ℝ) × C(Ω, ℝ)) →ₗ[ℝ] ℝ := (rn_intLin ν).coprod (rn_intLin μ) with hΦ
  have hΦapp : ∀ fg : C(Ω, ℝ) × C(Ω, ℝ), Φ fg = ∫ x, fg.1 x ∂ν + ∫ x, fg.2 x ∂μ := fun fg => rfl
  have hineq : ∀ fg : C(Ω, ℝ) × C(Ω, ℝ), Φ fg ≤ rn_sup D (rn_sumLin fg) := fun fg => by
    rw [hΦapp]
    exact rn_strassen_ineq le hrefl htrans hclosed ν μ hdom fg.1 fg.2
  have hker : LinearMap.ker (rn_sumLin (Ω := Ω)) ≤ LinearMap.ker Φ := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have h1 := hineq v
    have h2 := hineq (-v)
    rw [hv, rn_sup_zero hDc hDne] at h1
    rw [map_neg Φ, map_neg (rn_sumLin (Ω := Ω)), hv, neg_zero, rn_sup_zero hDc hDne] at h2
    linarith
  set Φ' := (LinearMap.ker (rn_sumLin (Ω := Ω))).liftQ Φ hker with hΦ'
  set e := (rn_sumLin (Ω := Ω)).quotKerEquivRange with he
  let fp : C(Ω × Ω, ℝ) →ₗ.[ℝ] ℝ := ⟨LinearMap.range (rn_sumLin (Ω := Ω)), Φ'.comp e.symm.toLinearMap⟩
  have hfp : ∀ v : C(Ω, ℝ) × C(Ω, ℝ), ∀ h : rn_sumLin v ∈ LinearMap.range (rn_sumLin (Ω := Ω)),
      fp ⟨rn_sumLin v, h⟩ = Φ v := by
    intro v h
    show Φ'.comp e.symm.toLinearMap ⟨rn_sumLin v, h⟩ = Φ v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, he]
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    simp [hΦ']
  obtain ⟨Λ, hΛ1, hΛ2⟩ := exists_extension_of_le_sublinear fp (rn_sup D)
    (fun c hc F => rn_sup_smul hDc hDne hc F) (fun F G => rn_sup_add_le hDc hDne F G)
    (by
      rintro ⟨w, v, rfl⟩
      rw [hfp v ⟨v, rfl⟩]
      exact hineq v)
  refine ⟨Λ, hΛ2, fun f g => ?_⟩
  have := hΛ1 ⟨rn_sumLin (f, g), ⟨(f, g), rfl⟩⟩
  rw [hfp (f, g) ⟨(f, g), rfl⟩] at this
  simpa [hΦapp] using this

/-- **Strassen's theorem** for a closed preorder on a second countable compact Hausdorff space:
if `ν A ≤ μ A` for every measurable increasing set `A`, there is a coupling of `ν` and `μ` supported
on `{x ≤ y}`. -/
theorem rn_strassen (le : Ω → Ω → Prop) (hrefl : ∀ x, le x x)
    (htrans : ∀ x y z, le x y → le y z → le x z)
    (hclosed : IsClosed {z : Ω × Ω | le z.1 z.2})
    (ν μ : Measure Ω) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hdom : ∀ A : Set Ω, MeasurableSet A → (∀ x y, le x y → x ∈ A → y ∈ A) → ν A ≤ μ A) :
    ∃ π : Measure (Ω × Ω), IsProbabilityMeasure π ∧ π.map Prod.fst = ν ∧ π.map Prod.snd = μ ∧
      π {z | ¬ le z.1 z.2} = 0 := by
  obtain ⟨Λ, hΛle, hΛ⟩ := rn_strassen_functional le hrefl htrans hclosed ν μ hdom
  set D : Set (Ω × Ω) := {z | le z.1 z.2} with hD
  have hDc : IsCompact D := hclosed.isCompact
  haveI : Nonempty Ω := nonempty_of_isProbabilityMeasure ν
  obtain ⟨x0⟩ := this
  have hDne : D.Nonempty := ⟨(x0, x0), hrefl x0⟩
  -- positivity
  have hpos : ∀ F : C(Ω × Ω, ℝ), (∀ z, 0 ≤ F z) → 0 ≤ Λ F := by
    intro F hF
    have h1 := hΛle (-F)
    have h2 : rn_sup D (-F) ≤ 0 := rn_sup_le hDne (fun z _ => by simpa using hF z)
    rw [map_neg] at h1
    linarith
  let Λ' : C_c(Ω × Ω, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun g => Λ g.toContinuousMap
      map_add' := fun g g' => by
        rw [← map_add]; rfl
      map_smul' := fun c g => by
        rw [← map_smul]; rfl
      monotone' := fun g g' hgg' => by
        have : 0 ≤ Λ (g'.toContinuousMap - g.toContinuousMap) :=
          hpos _ (fun z => sub_nonneg.mpr (hgg' z))
        rw [map_sub] at this
        linarith }
  set π : Measure (Ω × Ω) := RealRMK.rieszMeasure Λ' with hπ
  have hint : ∀ F : C(Ω × Ω, ℝ), ∫ z, F z ∂π = Λ F := by
    intro F
    exact RealRMK.integral_rieszMeasure Λ' (CompactlySupportedContinuousMap.continuousMapEquiv F)
  have hone : Λ (rn_sumLin ((1 : C(Ω, ℝ)), 0)) = 1 := by
    rw [hΛ]; simp
  have hπprob : IsProbabilityMeasure π := by
    refine ⟨?_⟩
    have h2 : (rn_sumLin ((1 : C(Ω, ℝ)), 0)) = 1 := by ext z; simp [rn_sumLin]
    have h1 := hint (rn_sumLin ((1 : C(Ω, ℝ)), 0))
    rw [hone, h2] at h1
    have h3 : (π univ).toReal = 1 := by simpa [measureReal_def] using h1
    exact (ENNReal.toReal_eq_one_iff _).mp h3
  have hmarg : ∀ (f : C(Ω, ℝ)), ∫ z, f z.1 ∂π = ∫ x, f x ∂ν := by
    intro f
    have h1 := hint (rn_sumLin (f, 0))
    rw [hΛ] at h1
    have h2 : (fun z : Ω × Ω => (rn_sumLin (f, 0)) z) = fun z => f z.1 := by
      funext z; simp [rn_sumLin]
    simp only [h2] at h1
    simpa using h1
  have hmarg2 : ∀ (f : C(Ω, ℝ)), ∫ z, f z.2 ∂π = ∫ x, f x ∂μ := by
    intro f
    have h1 := hint (rn_sumLin (0, f))
    rw [hΛ] at h1
    have h2 : (fun z : Ω × Ω => (rn_sumLin (0, f)) z) = fun z => f z.2 := by
      funext z; simp [rn_sumLin]
    simp only [h2] at h1
    simpa using h1
  refine ⟨π, hπprob, ?_, ?_, ?_⟩
  · haveI : IsProbabilityMeasure (π.map Prod.fst) := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure (fun f => ?_)
    rw [integral_map measurable_fst.aemeasurable f.continuous.aestronglyMeasurable]
    exact hmarg f.toContinuousMap
  · haveI : IsProbabilityMeasure (π.map Prod.snd) := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure (fun f => ?_)
    rw [integral_map measurable_snd.aemeasurable f.continuous.aestronglyMeasurable]
    exact hmarg2 f.toContinuousMap
  · have hopen : IsOpen Dᶜ := hclosed.isOpen_compl
    have : {z : Ω × Ω | ¬ le z.1 z.2} = Dᶜ := rfl
    rw [this, hopen.measure_eq_iSup_isCompact]
    simp only [ENNReal.iSup_eq_zero]
    intro K hKD hK
    obtain ⟨F, hF0, hF1, hFI⟩ := exists_continuous_zero_one_of_isClosed hclosed hK.isClosed
      (Set.disjoint_left.mpr (fun z hzD hzK => hKD hzK hzD))
    have hFnn : ∀ z, 0 ≤ F z := fun z => (hFI z).1
    have hΛF : Λ F ≤ 0 := by
      refine (hΛle F).trans (rn_sup_le hDne (fun z hz => ?_))
      rw [hF0 hz]; rfl
    have hFint : Integrable F π :=
      F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)
    have h1 : π K ≤ ENNReal.ofReal (∫ z, F z ∂π) := by
      rw [ofReal_integral_eq_lintegral_ofReal hFint (Filter.Eventually.of_forall hFnn)]
      calc π K = ∫⁻ z, K.indicator 1 z ∂π := by
            rw [lintegral_indicator_one hK.measurableSet]
        _ ≤ ∫⁻ z, ENNReal.ofReal (F z) ∂π := by
            refine lintegral_mono (fun z => ?_)
            by_cases hz : z ∈ K
            · simp [hz, hF1 hz]
            · simp [hz]
    rw [hint F] at h1
    have h2 : ENNReal.ofReal (Λ F) = 0 := ENNReal.ofReal_of_nonpos hΛF
    rw [h2] at h1
    exact nonpos_iff_eq_zero.mp h1

/-- **The coupling transfers almost sure events.**  Under the hypotheses of Strassen's theorem, if `Z`
is a measurable event of the smaller law `ν` of full measure, then the larger law `μ` almost surely
lies above some element of `Z`, and this is witnessed by a measurable set. -/
theorem rn_strassen_ae (le : Ω → Ω → Prop) (hrefl : ∀ x, le x x)
    (htrans : ∀ x y z, le x y → le y z → le x z)
    (hclosed : IsClosed {z : Ω × Ω | le z.1 z.2})
    (ν μ : Measure Ω) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hdom : ∀ A : Set Ω, MeasurableSet A → (∀ x y, le x y → x ∈ A → y ∈ A) → ν A ≤ μ A)
    (Z : Set Ω) (hZ : MeasurableSet Z) (hνZ : ν Zᶜ = 0) :
    ∃ B : Set Ω, MeasurableSet B ∧ μ Bᶜ = 0 ∧ ∀ ω ∈ B, ∃ ζ ∈ Z, le ζ ω := by
  obtain ⟨π, hπ, hfst, hsnd, hsupp⟩ := rn_strassen le hrefl htrans hclosed ν μ hdom
  set M : Set (Ω × Ω) := {z | z.1 ∈ Z} ∩ {z | le z.1 z.2} with hM
  have hMm : MeasurableSet M :=
    (measurable_fst hZ).inter hclosed.measurableSet
  have hMc : π Mᶜ = 0 := by
    have h1 : Mᶜ ⊆ (Prod.fst ⁻¹' Zᶜ) ∪ {z : Ω × Ω | ¬ le z.1 z.2} := by
      intro z hz
      simp only [hM, mem_compl_iff, mem_inter_iff, mem_setOf_eq, not_and_or] at hz
      rcases hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr hz
    refine measure_mono_null h1 (measure_union_null ?_ hsupp)
    rw [← Measure.map_apply measurable_fst hZ.compl, hfst]
    exact hνZ
  have hπM : π M = 1 := by
    have := measure_add_measure_compl (μ := π) hMm
    rw [hMc, add_zero, measure_univ] at this
    exact this
  have hex : ∀ n : ℕ, ∃ K : Set (Ω × Ω), K ⊆ M ∧ IsCompact K ∧
      (1 : ENNReal) - (n + 1 : ENNReal)⁻¹ < π K := by
    intro n
    refine hMm.exists_lt_isCompact ?_
    rw [hπM]
    refine ENNReal.sub_lt_self (by simp) (by simp) (by simp)
  choose K hKM hKc hKlt using hex
  refine ⟨⋃ n, Prod.snd '' K n, ?_, ?_, ?_⟩
  · exact MeasurableSet.iUnion fun n => ((hKc n).image continuous_snd).isClosed.measurableSet
  · have hlow : ∀ n : ℕ, (1 : ENNReal) - (n + 1 : ENNReal)⁻¹ ≤ μ (⋃ n, Prod.snd '' K n) := by
      intro n
      calc (1 : ENNReal) - (n + 1 : ENNReal)⁻¹ ≤ π (K n) := (hKlt n).le
        _ ≤ π (Prod.snd ⁻¹' (Prod.snd '' K n)) := measure_mono (subset_preimage_image _ _)
        _ = μ (Prod.snd '' K n) := by
            rw [← hsnd, Measure.map_apply measurable_snd
              ((hKc n).image continuous_snd).isClosed.measurableSet]
        _ ≤ μ (⋃ n, Prod.snd '' K n) := measure_mono (subset_iUnion (fun n => Prod.snd '' K n) n)
    have h1 : (1 : ENNReal) ≤ μ (⋃ n, Prod.snd '' K n) := by
      have htend : Filter.Tendsto (fun n : ℕ => (1 : ENNReal) - (n + 1 : ENNReal)⁻¹)
          Filter.atTop (nhds 1) := by
        have : Filter.Tendsto (fun n : ℕ => (n + 1 : ENNReal)⁻¹) Filter.atTop (nhds 0) := by
          have h0 : Filter.Tendsto (fun n : ℕ => ((n : ENNReal) + 1)) Filter.atTop (nhds ⊤) := by
            have := ENNReal.tendsto_nat_nhds_top.add_const (1 : ENNReal)
            simpa using this
          simpa using tendsto_inv_iff.mpr h0
        simpa using ENNReal.Tendsto.sub tendsto_const_nhds this (Or.inl (by simp))
      exact le_of_tendsto' htend hlow
    have h3 : μ (⋃ n, Prod.snd '' K n) = 1 := le_antisymm prob_le_one h1
    exact (prob_compl_eq_zero_iff (MeasurableSet.iUnion fun n =>
      ((hKc n).image continuous_snd).isClosed.measurableSet)).mpr h3
  · intro ω hω
    obtain ⟨n, hn⟩ := mem_iUnion.mp hω
    obtain ⟨z, hz, rfl⟩ := hn
    have := hKM n hz
    exact ⟨z.1, this.1, this.2⟩

end Strassen

section BoolField

open Exploding

/-- **Strassen's theorem for fields of bits**: if a law `μ` on `S → Bool` dominates the law `ν` on
every measurable increasing event, then `μ` almost surely lies above some configuration from any
full-measure measurable event of `ν`. -/
theorem rn_strassen_bool {S : Type} [Countable S] (ν μ : Measure (S → Bool))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hdom : ∀ A : Set (S → Bool), MeasurableSet A → IsIncreasingSet A → ν A ≤ μ A)
    (Z : Set (S → Bool)) (hZ : MeasurableSet Z) (hνZ : ν Zᶜ = 0) :
    ∃ B : Set (S → Bool), MeasurableSet B ∧ μ Bᶜ = 0 ∧
      ∀ ω ∈ B, ∃ ζ ∈ Z, ∀ s, ζ s = true → ω s = true := by
  refine rn_strassen_ae (fun x y : S → Bool => ∀ s, x s = true → y s = true)
    (fun x s h => h) (fun x y z hxy hyz s h => hyz s (hxy s h)) ?_ ν μ
    (fun A hA hinc => hdom A hA (fun x y hxy hx => hinc x y hx hxy)) Z hZ hνZ
  have : {z : (S → Bool) × (S → Bool) | ∀ s, z.1 s = true → z.2 s = true} =
      ⋂ s, {z | z.1 s = true → z.2 s = true} := by
    ext z; simp
  rw [this]
  refine isClosed_iInter fun s => ?_
  have h1 : IsClopen {z : (S → Bool) × (S → Bool) | z.1 s = true} :=
    (isClopen_discrete ({true} : Set Bool)).preimage ((continuous_apply s).comp continuous_fst)
  have h3' : IsClopen {z : (S → Bool) × (S → Bool) | z.2 s = true} :=
    (isClopen_discrete ({true} : Set Bool)).preimage ((continuous_apply s).comp continuous_snd)
  have h3 : IsClosed {z : (S → Bool) × (S → Bool) | z.2 s = true} := h3'.isClosed
  have : {z : (S → Bool) × (S → Bool) | z.1 s = true → z.2 s = true} =
      {z : (S → Bool) × (S → Bool) | z.1 s = true}ᶜ ∪ {z | z.2 s = true} := by
    ext z; simp [imp_iff_not_or]
  rw [this]
  exact h1.compl.isClosed.union h3

end BoolField

end Exploding
