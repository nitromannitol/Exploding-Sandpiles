/-
Proposition 7.1 of `paper/corrected-arxiv/exploding-corrected-arxiv.tex` (label
`prop:explosion_criteria`, lines 1956-1958) in dimension one, following the paragraph after its
proof (line 1985).

A recurrent background with `η ≤ 1` has at most one zero: an interval whose two endpoints have
height zero is not recurrent, because firing its two external neighbours starts no toppling
(`not_recurrent_of_two_zeros`). Stationarity under a finite-index sublattice then makes the
probability of a zero at every site vanish (`measure_zero_eq_zero_of_stationary`), so `η ≡ 1`
almost surely. The constant background `1` is explosive because the odometer front of
`1 + δ₀` reaches sites of every norm (`all_high_pile_not_stabilizable_of_pos`).

The main statements are `Exploding.explosion_criteria_dim_one`, with the hypotheses of the
published proposition, and `Exploding.explosion_criteria_of_one_le`, which combines it with
`Exploding.Frozen.explosion_criteria` for `d ≥ 2`.
-/
import Exploding.Frozen.ExplosionCriteria
import Exploding.Support.ApproximateSubadditiveP1

namespace Exploding

open LatticeProb MeasureTheory

/-! ### Frozen odometers that never move -/

/-- If no site off the frozen set `S` is unstable at time `0`, the frozen odometer stays at its
initial value. -/
theorem fodo_eq_of_stable {d : ℕ} (S : Set (Site d)) (s0 w0 : Site d → ℤ)
    (h : ∀ x, x ∉ S → fconf S s0 w0 0 x < 2 * (d : ℤ)) (t : ℕ) :
    fodo S s0 w0 t = w0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext x
    rw [fodo_succ]
    split_ifs with hx hc
    · rfl
    · exfalso
      have h0 := h x hx
      simp only [fconf, fodo_zero] at h0
      simp only [fconf, ih] at hc
      exact absurd hc (not_le.mpr h0)
    · rw [ih, add_zero]

/-! ### Two zeros obstruct recurrence in dimension one -/

/-- Two sites of `ℤ¹` with the same coordinate are equal. -/
theorem site_one_ext {a b : Site 1} (h : a 0 = b 0) : a = b :=
  funext fun i => by rw [Fin.fin_one_eq_zero i]; exact h

open scoped Classical in
/-- In dimension one, a background with `η ≤ 1` and two zeros `x < y` is not recurrent: on the
interval `[x, y]`, firing the two external neighbours leaves every height below `2`. -/
theorem not_recurrent_of_two_zeros {η : Site 1 → ℤ} (hle : ∀ z, η z ≤ 1) {x y : Site 1}
    (hxy : x 0 < y 0) (hx : η x = 0) (hy : η y = 0) : ¬ Recurrent η := by
  intro hrec
  obtain ⟨V, hV⟩ : ∃ V : Finset (Site 1),
      V = (Finset.Icc (x 0) (y 0)).image fun n : ℤ => (fun _ : Fin 1 => n) := ⟨_, rfl⟩
  have hmem : ∀ z : Site 1, z ∈ (V : Set (Site 1)) ↔ x 0 ≤ z 0 ∧ z 0 ≤ y 0 := by
    intro z
    rw [Finset.mem_coe, hV, Finset.mem_image]
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact Finset.mem_Icc.mp hn
    · intro hz
      exact ⟨z 0, Finset.mem_Icc.mpr hz, site_one_ext rfl⟩
  obtain ⟨w0, hw0⟩ : ∃ w0 : Site 1 → ℤ,
      w0 = fun z => if z ∈ outerBoundary (V : Set (Site 1)) then 1 else 0 := ⟨_, rfl⟩
  have hw0V : ∀ z, z ∈ (V : Set (Site 1)) → w0 z = 0 := by
    intro z hz
    simp only [hw0]
    exact ite_eq_right fun h => h.1 hz
  have hw0le : ∀ z, w0 z ≤ 1 := by
    intro z
    simp only [hw0]
    split_ifs <;> norm_num
  have hplus : ∀ z : Site 1, x 0 ≤ z 0 → z 0 < y 0 → w0 (z + unit 0) = 0 := by
    intro z hxz hzy
    simp only [hw0]
    refine ite_eq_right fun h => h.1 ((hmem _).2 ?_)
    simp only [Pi.add_apply, unit, Pi.single_eq_same]
    omega
  have hminus : ∀ z : Site 1, x 0 < z 0 → z 0 ≤ y 0 → w0 (z - unit 0) = 0 := by
    intro z hxz hzy
    simp only [hw0]
    refine ite_eq_right fun h => h.1 ((hmem _).2 ?_)
    simp only [Pi.sub_apply, unit, Pi.single_eq_same]
    omega
  have hstable : ∀ z, z ∉ (V : Set (Site 1))ᶜ →
      fconf (V : Set (Site 1))ᶜ η w0 0 z < 2 * ((1 : ℕ) : ℤ) := by
    intro z hz
    rw [Set.notMem_compl_iff] at hz
    have hb := (hmem z).1 hz
    simp only [fconf, fodo_zero, lap, nbrSumZ, Fin.sum_univ_one, hw0V z hz, Nat.cast_one,
      mul_zero, sub_zero, mul_one]
    have hp := hw0le (z + unit 0)
    have hm := hw0le (z - unit 0)
    have hηz := hle z
    rcases lt_or_eq_of_le hb.1 with hxz | hxz
    · rw [hminus z hxz hb.2]
      rcases lt_or_eq_of_le hb.2 with hzy | hzy
      · rw [hplus z hb.1 hzy]
        omega
      · have hz0 : η z = 0 := by rw [site_one_ext hzy]; exact hy
        omega
    · have hz0 : η z = 0 := by rw [← site_one_ext hxz]; exact hx
      rw [hplus z hb.1 (by omega)]
      omega
  have h := hrec V V.card le_rfl x (Finset.mem_coe.mp ((hmem x).2 ⟨le_rfl, hxy.le⟩))
  rw [← hw0, fodo_eq_of_stable _ _ _ hstable] at h
  rw [hw0V x ((hmem x).2 ⟨le_rfl, hxy.le⟩)] at h
  exact zero_ne_one h

/-- In dimension one, a recurrent background with `η ≤ 1` has at most one zero. -/
theorem eq_of_recurrent_of_zero {η : Site 1 → ℤ} (hrec : Recurrent η) (hle : ∀ z, η z ≤ 1)
    {x y : Site 1} (hx : η x = 0) (hy : η y = 0) : x = y := by
  rcases lt_trichotomy (x 0) (y 0) with h | h | h
  · exact absurd hrec (not_recurrent_of_two_zeros hle h hx hy)
  · exact site_one_ext h
  · exact absurd hrec (not_recurrent_of_two_zeros hle h hy hx)

/-! ### Stationarity excludes a unique zero -/

/-- If almost surely `η` has at most one zero and the law of `η` is stationary under a
finite-index sublattice of `ℤ¹`, then every site is a zero with probability `0`: the translates
of the event by the multiples of `[ℤ : L]` are almost surely disjoint and have equal
probability. -/
theorem measure_zero_eq_zero_of_stationary {L : AddSubgroup (Site 1)} (hL : L.index ≠ 0)
    {P : Measure (Site 1 → ℤ)} [IsProbabilityMeasure P] (hstat : StationaryOn 1 L P)
    (huniq : ∀ᵐ η ∂P, ∀ a b : Site 1, η a = 0 → η b = 0 → a = b) (x : Site 1) :
    P {η | η x = 0} = 0 := by
  obtain ⟨y, hy⟩ : ∃ y : ℕ → Site 1, y = fun k => k • (L.index • unit 0) := ⟨_, rfl⟩
  have hyL : ∀ k, y k ∈ L := fun k => by
    rw [hy]
    exact L.nsmul_mem (L.nsmul_index_mem (unit 0)) k
  have hy0 : ∀ k, (y k + x) 0 = (k : ℤ) * L.index + x 0 := by
    intro k
    simp [hy, unit, nsmul_eq_mul]
  have hinj : ∀ k l, y k + x = y l + x → k = l := by
    intro k l h
    have h0 := congrFun h 0
    rw [hy0, hy0] at h0
    have hn : (L.index : ℤ) ≠ 0 := by exact_mod_cast hL
    have hkl : (k : ℤ) = l := mul_right_cancel₀ hn (by linarith)
    exact_mod_cast hkl
  have hmeasE : ∀ z : Site 1, MeasurableSet {η : Site 1 → ℤ | η z = 0} := fun z =>
    measurableSet_eq_fun (measurable_pi_apply z) measurable_const
  have hE : ∀ k, P {η | η (y k + x) = 0} = P {η | η x = 0} := by
    intro k
    have hf : Measurable fun η : Site 1 → ℤ => fun z => η (y k + z) :=
      Measurable.of_eval fun z => measurable_pi_apply (y k + z)
    calc P {η | η (y k + x) = 0}
        = P ((fun η : Site 1 → ℤ => fun z => η (y k + z)) ⁻¹' {η | η x = 0}) := rfl
      _ = (P.map fun η : Site 1 → ℤ => fun z => η (y k + z)) {η | η x = 0} :=
          (Measure.map_apply hf (hmeasE x)).symm
      _ = P {η | η x = 0} := by rw [hstat (y k) (hyL k)]
  have hdisj : Pairwise (Function.onFun (AEDisjoint P)
      fun k => {η : Site 1 → ℤ | η (y k + x) = 0}) := by
    intro k l hkl
    show P (_ ∩ _) = 0
    refine measure_mono_null ?_ (ae_iff.mp huniq)
    intro η hη
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hη ⊢
    intro h
    exact hkl (hinj k l (h _ _ hη.1 hη.2))
  by_contra hp
  have hU := measure_iUnion₀ hdisj fun k => (hmeasE (y k + x)).nullMeasurableSet
  simp only [hE] at hU
  rw [ENNReal.tsum_const_eq_top_of_ne_zero hp] at hU
  exact measure_ne_top P _ hU

/-! ### The constant background `1` explodes -/

/-- In dimension one the constant background `1 = 2d - 1` is explosive. -/
theorem explosive_dim_one_const : Explosive (fun _ : Site 1 => (1 : ℤ)) := by
  intro hrob
  refine all_high_pile_not_stabilizable_of_pos 1 one_pos ?_
  have hfun : (fun x : Site 1 => 2 * ((1 : ℕ) : ℤ) - 1 + (1 : ℤ) * dirac (0 : Site 1) x)
      = fun x => (fun _ : Site 1 => (1 : ℤ)) x + ((1 : ℕ) : ℤ) * dirac (0 : Site 1) x := by
    funext x
    norm_num
  rw [hfun]
  exact hrob 1 le_rfl

/-! ### Proposition 7.1 in dimension one -/

/-- In dimension one, a law that is almost surely bounded above by `1 = 2d - 1`, stationary
under a finite-index sublattice and recurrent is explosive; almost surely `η ≡ 1`. -/
theorem explosiveLaw_dim_one {ηmin : ℤ} {L : AddSubgroup (Site 1)} (hL : L.index ≠ 0)
    {P : Measure (Site 1 → ℤ)} [IsProbabilityMeasure P]
    (hsupp : ∀ᵐ η ∂P, InOmega 1 ηmin η) (hstat : StationaryOn 1 L P)
    (hrec : RecurrentLaw 1 P) :
    ExplosiveLaw 1 P := by
  have hrec' : ∀ᵐ η ∂P, Recurrent η := hrec
  have hle : ∀ᵐ η ∂P, ∀ z, η z ≤ 1 := by
    filter_upwards [hsupp] with η hη z
    have h := (hη z).2
    simp only [Nat.cast_one] at h
    linarith
  have huniq : ∀ᵐ η ∂P, ∀ a b : Site 1, η a = 0 → η b = 0 → a = b := by
    filter_upwards [hrec', hle] with η hr hl a b ha hb
    exact eq_of_recurrent_of_zero hr hl ha hb
  have hnz : ∀ᵐ η ∂P, ∀ z : Site 1, η z ≠ 0 := by
    rw [ae_all_iff]
    intro z
    rw [ae_iff]
    simpa only [ne_eq, not_not] using measure_zero_eq_zero_of_stationary hL hstat huniq z
  have hone : ∀ᵐ η ∂P, η = fun _ => 1 := by
    filter_upwards [hrec', hle, hnz] with η hr hl hn
    funext z
    have h0 := recurrent_nonneg η hr z
    have h1 := hl z
    have h2 := hn z
    show η z = 1
    omega
  show ∀ᵐ η ∂P, Explosive η
  filter_upwards [hone] with η hη
  rw [hη]
  exact explosive_dim_one_const

end Exploding

open Exploding LatticeProb MeasureTheory

/-- **Proposition 7.1** (`paper/corrected-arxiv/exploding-corrected-arxiv.tex:1956-1958`, label
`prop:explosion_criteria`) in dimension one, as argued in the paragraph after its proof (line 1985).

"If Hypotheses `hyp:finite_range_of_dependence` and `hyp:box_crossing` are satisfied and `P` is
recurrent then `P` is explosive."

The premises are those of `Exploding.Frozen.explosion_criteria` with `d = 1`. The proof uses
the upper bound of `hsupp`, stationarity under the finite-index sublattice `L` and recurrence;
the premises `herg`, `h1` and `h2` are not needed in dimension one. -/
theorem Exploding.explosion_criteria_dim_one (ηmin : ℤ)
    (L : AddSubgroup (Site 1)) (hL : L.index ≠ 0) (P : Measure (Site 1 → ℤ))
    (hP : IsProbabilityMeasure P)
    (hsupp : ∀ᵐ η ∂P, InOmega 1 ηmin η)
    (hstat : StationaryOn 1 L P) (herg : MeasurableErgodicOn 1 L P)
    (h1 : FiniteRangeOfDependence 1 P) (h2 : BoxCrossingHyp 1 P)
    (hrec : RecurrentLaw 1 P) :
    ExplosiveLaw 1 P := by
  have _unused := And.intro herg (And.intro h1 h2)
  exact explosiveLaw_dim_one hL hsupp hstat hrec

/-- **Proposition 7.1** (`prop:explosion_criteria`) in every dimension `d ≥ 1`: the case `d ≥ 2`
is `Exploding.Frozen.explosion_criteria` and the case `d = 1` is
`Exploding.explosion_criteria_dim_one`. -/
theorem Exploding.explosion_criteria_of_one_le (d : ℕ) (hd : 1 ≤ d) (ηmin : ℤ)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0) (P : Measure (Site d → ℤ))
    (hP : IsProbabilityMeasure P)
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η)
    (hstat : StationaryOn d L P) (herg : MeasurableErgodicOn d L P)
    (h1 : FiniteRangeOfDependence d P) (h2 : BoxCrossingHyp d P)
    (hrec : RecurrentLaw d P) :
    ExplosiveLaw d P := by
  obtain rfl | hd2 : d = 1 ∨ 2 ≤ d := by omega
  · exact Exploding.explosion_criteria_dim_one ηmin L hL P hP hsupp hstat herg h1 h2 hrec
  · exact Exploding.Frozen.explosion_criteria d hd2 ηmin L hL P hP hsupp hstat herg h1 h2 hrec
