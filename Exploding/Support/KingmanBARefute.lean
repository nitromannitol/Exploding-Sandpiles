/-
The bounded-above Kingman statement `mk4_boundedAboveKingman` is false.

A subadditive cocycle over an ergodic map that is bounded below by a linear function and
bounded above by an a.s. finite random variable need not satisfy `h n / n → L`.  For every
measurable `Λ ≥ 0` and every `ε > 0` the cocycle
`h n x = Λ x - min (ε n) (Λ (T^[n] x))` is subadditive, satisfies `h n x ≥ -ε n` and
`h n x ≤ Λ x`.  If `Λ` is a heavy-tailed coordinate of an i.i.d. sequence, then
`Λ (T^[n] x) > n` infinitely often and `Λ (T^[n] x) < n / 2` infinitely often, so
`h n / n` has two different limit points.

The same cocycle (shifted by the linear term) refutes `mk_kingman_linear` and
`glw2_KingmanCore`.  The consequence for the project: the paper's transfer from the
return times to all `n` needs the second Lipschitz bound, so it cannot be isolated as a
Lipschitz-free statement about subadditive cocycles.
-/
import Exploding.Support.MKingman4
import Exploding.Support.GLWProof2
import LatticeProb.Prob.ZeroOne
import Mathlib.Probability.BorelCantelli
import Mathlib.MeasureTheory.Constructions.UnitInterval

open Exploding LatticeProb MeasureTheory Filter ProbabilityTheory Topology
open scoped ENNReal

namespace Exploding

section Cocycle

variable {Ω : Type}

/-- The counterexample cocycle `h n x = Λ x - min n (Λ (T^[n] x))`. -/
noncomputable def king_h (T : Ω → Ω) (Λ : Ω → ℝ) (n : ℕ) (x : Ω) : ℝ :=
  Λ x - min (n : ℝ) (Λ (T^[n] x))

/-- The counterexample cocycle is subadditive. -/
theorem king_h_subadditive (T : Ω → Ω) (Λ : Ω → ℝ) (hΛ : ∀ x, 0 ≤ Λ x) (m n : ℕ) (x : Ω) :
    king_h T Λ (m + n) x ≤ king_h T Λ m x + king_h T Λ n (T^[m] x) := by
  have hcomm : T^[n] (T^[m] x) = T^[m + n] x := by
    rw [← Function.iterate_add_apply, Nat.add_comm]
  unfold king_h
  rw [hcomm]
  have h1 := hΛ (T^[m] x)
  have h2 := hΛ (T^[m + n] x)
  push_cast
  rcases le_total (Λ (T^[m + n] x)) ((m : ℝ) + n) with h | h
  · rw [min_eq_right h]
    have e1 : min (m : ℝ) (Λ (T^[m] x)) ≤ Λ (T^[m] x) := min_le_right _ _
    have e2 : min (n : ℝ) (Λ (T^[m + n] x)) ≤ Λ (T^[m + n] x) := min_le_right _ _
    linarith
  · rw [min_eq_left h]
    have e1 : min (m : ℝ) (Λ (T^[m] x)) ≤ (m : ℝ) := min_le_left _ _
    have e2 : min (n : ℝ) (Λ (T^[m + n] x)) ≤ (n : ℝ) := min_le_left _ _
    linarith

/-- The counterexample cocycle is bounded below by `-n`. -/
theorem king_h_ge (T : Ω → Ω) (Λ : Ω → ℝ) (hΛ : ∀ x, 0 ≤ Λ x) (n : ℕ) (x : Ω) :
    -(1 : ℝ) * n ≤ king_h T Λ n x := by
  unfold king_h
  have := hΛ x
  have : min (n : ℝ) (Λ (T^[n] x)) ≤ n := min_le_left _ _
  linarith

/-- The counterexample cocycle is bounded above by `Λ`. -/
theorem king_h_le (T : Ω → Ω) (Λ : Ω → ℝ) (hΛ : ∀ x, 0 ≤ Λ x) (n : ℕ) (x : Ω) :
    king_h T Λ n x ≤ Λ x := by
  unfold king_h
  have : 0 ≤ min (n : ℝ) (Λ (T^[n] x)) := le_min (Nat.cast_nonneg n) (hΛ _)
  linarith

/-- The counterexample cocycle is measurable. -/
theorem king_h_measurable [MeasurableSpace Ω] (T : Ω → Ω) (hT : Measurable T) (Λ : Ω → ℝ)
    (hΛ : Measurable Λ) (n : ℕ) : Measurable (king_h T Λ n) :=
  hΛ.sub (measurable_const.min (hΛ.comp (hT.iterate n)))

end Cocycle


section Bernoulli

open unitInterval

/-- The configuration space of the counterexample: i.i.d. uniform coordinates. -/
abbrev king_Ω : Type := ℕ → unitInterval

/-- The product measure with uniform coordinates. -/
noncomputable def king_μ : Measure king_Ω :=
  Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)

instance : IsProbabilityMeasure king_μ := by unfold king_μ; infer_instance

/-- The coordinate shift. -/
def king_T : king_Ω → king_Ω := coordShift (X := unitInterval) Nat.succ

theorem king_succ_iterate (n i : ℕ) : Nat.succ^[n] i = i + n := by
  induction n generalizing i with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, ih]; omega

theorem king_T_iterate (n : ℕ) (ω : king_Ω) (i : ℕ) : (king_T^[n] ω) i = ω (i + n) := by
  have : king_T^[n] = coordShift (X := unitInterval) (Nat.succ^[n]) := coordShift_iterate _ _
  rw [this]
  show ω (Nat.succ^[n] i) = ω (i + n)
  rw [king_succ_iterate]

theorem king_ergodic : Ergodic king_T king_μ := by
  refine ergodic_coordShift_infinitePi (fun _ : ℕ => (volume : Measure unitInterval))
    Nat.succ_injective (fun _ => rfl) ?_
  intro s
  refine ⟨s.sup id + 1, fun i hi => ?_⟩
  rw [king_succ_iterate]
  intro hmem
  have := Finset.le_sup (f := id) hmem
  simp only [id] at this
  omega

/-- The heavy-tailed variable `Λ = 1 / u₀`, which is not integrable. -/
noncomputable def king_Λ (ω : king_Ω) : ℝ := ((ω 0 : unitInterval) : ℝ)⁻¹

theorem king_Λ_nonneg (ω : king_Ω) : 0 ≤ king_Λ ω := by
  unfold king_Λ
  exact inv_nonneg.mpr (ω 0).2.1

theorem king_Λ_measurable : Measurable king_Λ :=
  ((measurable_subtype_coe).comp (measurable_pi_apply 0)).inv

theorem king_T_measurable : Measurable king_T := measurable_coordShift _

theorem king_Λ_iterate (n : ℕ) (ω : king_Ω) : king_Λ (king_T^[n] ω) = ((ω n : unitInterval) : ℝ)⁻¹ := by
  unfold king_Λ
  rw [king_T_iterate]
  simp

/-- Coordinate events of the i.i.d. sequence are independent. -/
theorem king_iIndepSet (S : ℕ → Set unitInterval) (hS : ∀ n, MeasurableSet (S n)) :
    iIndepSet (fun n => (fun ω : king_Ω => ω n) ⁻¹' S n) king_μ := by
  have hX : iIndepFun (fun (i : ℕ) (ω : king_Ω) => ω i) king_μ :=
    iIndepFun_infinitePi (P := fun _ : ℕ => (volume : Measure unitInterval))
      (X := fun _ x => x) (fun _ => measurable_id)
  rw [iIndepSet_iff]
  intro s' f hf
  refine hX.meas_biInter (fun i hi => ?_)
  have hle : MeasurableSpace.generateFrom {(fun ω : king_Ω => ω i) ⁻¹' S i} ≤
      MeasurableSpace.comap (fun ω : king_Ω => ω i) inferInstance := by
    refine MeasurableSpace.generateFrom_le ?_
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact ⟨S i, hS i, rfl⟩
  exact hle _ (hf i hi)

/-- The marginal law of each coordinate is the uniform law. -/
theorem king_coord_measure (n : ℕ) {S : Set unitInterval} (hS : MeasurableSet S) :
    king_μ ((fun ω : king_Ω => ω n) ⁻¹' S) = volume S := by
  have h := Measure.infinitePi_map_eval (fun _ : ℕ => (volume : Measure unitInterval)) n
  rw [← Measure.map_apply (measurable_pi_apply n) hS]
  exact congrArg (fun m => m S) h

/-- **Second Borel-Cantelli for the coordinates**: if the events `ω n ∈ S n` have divergent
total probability, then almost surely they happen infinitely often. -/
theorem king_ae_frequently (S : ℕ → Set unitInterval) (hS : ∀ n, MeasurableSet (S n))
    (hsum : ∑' n, (volume : Measure unitInterval) (S n) = ∞) :
    ∀ᵐ ω ∂king_μ, ∃ᶠ n in atTop, ω n ∈ S n := by
  have hsm : ∀ n, MeasurableSet ((fun ω : king_Ω => ω n) ⁻¹' S n) :=
    fun n => measurable_pi_apply n (hS n)
  have hsum' : ∑' n, king_μ ((fun ω : king_Ω => ω n) ⁻¹' S n) = ∞ := by
    simpa only [king_coord_measure _ (hS _)] using hsum
  have h1 := measure_limsup_eq_one hsm (king_iIndepSet S hS) hsum'
  have hmeas : MeasurableSet (limsup (fun n => (fun ω : king_Ω => ω n) ⁻¹' S n) atTop) :=
    MeasurableSet.measurableSet_limsup hsm
  have h0 : king_μ (limsup (fun n => (fun ω : king_Ω => ω n) ⁻¹' S n) atTop)ᶜ = 0 :=
    (prob_compl_eq_zero_iff hmeas).2 h1
  have : ∀ᵐ ω ∂king_μ, ω ∈ limsup (fun n => (fun ω : king_Ω => ω n) ⁻¹' S n) atTop := by
    rw [ae_iff]
    exact h0
  filter_upwards [this] with ω hω
  rw [mem_limsup_iff_frequently_mem] at hω
  exact hω


/-- The threshold `1/(n+1)` as a point of the unit interval. -/
noncomputable def king_pt (n : ℕ) : unitInterval :=
  ⟨1 / ((n : ℝ) + 1), by
    have h : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact ⟨by positivity, by rw [div_le_one h]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]⟩⟩

/-- Heavy-tail events: `0 < u < 1/(n+1)`, of probability `1/(n+1)`. -/
def king_E (n : ℕ) : Set unitInterval := Set.Ioo 0 (king_pt n)

/-- Light-tail events: `u > 1/2`, of probability `1/2`. -/
noncomputable def king_F : Set unitInterval := Set.Ioi (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)

theorem king_E_measurable (n : ℕ) : MeasurableSet (king_E n) := measurableSet_Ioo

theorem king_F_measurable : MeasurableSet king_F := measurableSet_Ioi

theorem king_E_volume (n : ℕ) : (volume : Measure unitInterval) (king_E n) =
    ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
  unfold king_E
  rw [unitInterval.volume_Ioo]
  congr 1
  show 1 / ((n : ℝ) + 1) - 0 = _
  ring

theorem king_F_volume : (volume : Measure unitInterval) king_F = ENNReal.ofReal (1 / 2) := by
  unfold king_F
  rw [unitInterval.volume_Ioi]
  congr 1
  show 1 - (1 / 2 : ℝ) = 1 / 2
  norm_num

theorem king_E_sum : ∑' n : ℕ, (volume : Measure unitInterval) (king_E n) = ∞ := by
  by_contra hne
  have hsum : Summable (fun n : ℕ => ((volume : Measure unitInterval) (king_E n)).toReal) :=
    ENNReal.summable_toReal hne
  have heq : ∀ n : ℕ, ((volume : Measure unitInterval) (king_E n)).toReal = 1 / ((n : ℝ) + 1) := by
    intro n
    rw [king_E_volume, ENNReal.toReal_ofReal (by positivity)]
  simp_rw [heq] at hsum
  have h2 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ)) := by
    rw [← summable_nat_add_iff 1]
    simpa using hsum
  exact Real.not_summable_one_div_natCast h2

theorem king_F_sum : ∑' _n : ℕ, (volume : Measure unitInterval) king_F = ∞ := by
  rw [king_F_volume]
  exact ENNReal.tsum_const_eq_top_of_ne_zero (by simp)


/-- Almost surely `Λ (T^n ω) > n` for infinitely many `n`. -/
theorem king_ae_large : ∀ᵐ ω ∂king_μ, ∃ᶠ n : ℕ in atTop, (n : ℝ) < king_Λ (king_T^[n] ω) := by
  filter_upwards [king_ae_frequently king_E king_E_measurable king_E_sum] with ω hω
  refine hω.mono fun n hn => ?_
  rw [king_Λ_iterate]
  obtain ⟨h0, h1⟩ := hn
  have hpos : (0 : ℝ) < ((ω n : unitInterval) : ℝ) := h0
  have hlt : ((ω n : unitInterval) : ℝ) < 1 / ((n : ℝ) + 1) := h1
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simpa using hpos
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
    rw [lt_inv_comm₀ hnpos hpos]
    calc ((ω n : unitInterval) : ℝ) < 1 / ((n : ℝ) + 1) := hlt
      _ ≤ ((n : ℝ))⁻¹ := by
        rw [one_div]
        exact inv_anti₀ hnpos (by linarith)

/-- Almost surely `Λ (T^n ω) < 2` for infinitely many `n`. -/
theorem king_ae_small : ∀ᵐ ω ∂king_μ, ∃ᶠ n : ℕ in atTop, king_Λ (king_T^[n] ω) < 2 := by
  filter_upwards [king_ae_frequently (fun _ => king_F) (fun _ => king_F_measurable)
    king_F_sum] with ω hω
  refine hω.mono fun n hn => ?_
  rw [king_Λ_iterate]
  have hn' : (1 / 2 : ℝ) < ((ω n : unitInterval) : ℝ) := hn
  have hpos : (0 : ℝ) < ((ω n : unitInterval) : ℝ) := by linarith
  rw [inv_lt_comm₀ hpos (by norm_num)]
  linarith

/-- The counterexample cocycle has no almost-sure limit. -/
theorem king_not_converge : ¬ ∃ L : ℝ, ∀ᵐ ω ∂king_μ,
    Tendsto (fun n : ℕ => king_h king_T king_Λ n ω / (n : ℝ)) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  obtain ⟨ω, hω, hEω, hFω⟩ := (hL.and (king_ae_large.and king_ae_small)).exists
  have h0 : Tendsto (fun n : ℕ => king_Λ ω / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hu : Tendsto (fun n : ℕ => king_h king_T king_Λ n ω / (n : ℝ) - king_Λ ω / (n : ℝ))
      atTop (𝓝 (L - 0)) := hω.sub h0
  -- along the large times the difference equals `-1`
  have h1 : ∃ᶠ n : ℕ in atTop,
      (king_h king_T king_Λ n ω / (n : ℝ) - king_Λ ω / (n : ℝ)) ∈ ({-1} : Set ℝ) := by
    refine (hEω.and_eventually (eventually_ge_atTop 1)).mono fun n ⟨hn, hn1⟩ => ?_
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp only [Set.mem_singleton_iff, king_h]
    rw [min_eq_left hn.le]
    field_simp
    ring
  have hL1 : L - 0 ∈ ({-1} : Set ℝ) := isClosed_singleton.mem_of_frequently_of_tendsto h1 hu
  -- along the small times the difference is at least `-2/n`
  have h2tend : Tendsto (fun n : ℕ => (king_h king_T king_Λ n ω / (n : ℝ) - king_Λ ω / (n : ℝ))
      + 2 / (n : ℝ)) atTop (𝓝 (L - 0 + 0)) :=
    hu.add (tendsto_const_div_atTop_nhds_zero_nat 2)
  have h2 : ∃ᶠ n : ℕ in atTop,
      (king_h king_T king_Λ n ω / (n : ℝ) - king_Λ ω / (n : ℝ)) + 2 / (n : ℝ) ∈ Set.Ici (0 : ℝ) := by
    refine (hFω.and_eventually (eventually_ge_atTop 1)).mono fun n ⟨hn, hn1⟩ => ?_
    have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    simp only [Set.mem_Ici, king_h]
    have hmin : min (n : ℝ) (king_Λ (king_T^[n] ω)) ≤ 2 := by
      refine le_trans (min_le_right _ _) hn.le
    have : king_Λ ω - min (n : ℝ) (king_Λ (king_T^[n] ω)) + 2 ≥ king_Λ ω := by linarith
    have hdiv : 0 ≤ (king_Λ ω - min (n : ℝ) (king_Λ (king_T^[n] ω)) + 2 - king_Λ ω) / (n : ℝ) :=
      div_nonneg (by linarith) hnpos.le
    have : (king_Λ ω - min (n : ℝ) (king_Λ (king_T^[n] ω))) / (n : ℝ) - king_Λ ω / (n : ℝ)
        + 2 / (n : ℝ) =
        (king_Λ ω - min (n : ℝ) (king_Λ (king_T^[n] ω)) + 2 - king_Λ ω) / (n : ℝ) := by
      field_simp
      ring
    rw [this]
    exact hdiv
  have hL2 : L - 0 + 0 ∈ Set.Ici (0 : ℝ) := isClosed_Ici.mem_of_frequently_of_tendsto h2 h2tend
  rw [Set.mem_singleton_iff] at hL1
  rw [Set.mem_Ici] at hL2
  linarith

/-- **`mk4_boundedAboveKingman` is false.** -/
theorem king_not_boundedAbove : ¬ mk4_boundedAboveKingman := by
  intro hBA
  obtain ⟨L, hL⟩ := hBA king_μ king_T king_ergodic.toMeasurePreserving king_ergodic
    (king_h king_T king_Λ) (king_h_subadditive king_T king_Λ king_Λ_nonneg)
    ⟨1, king_h_ge king_T king_Λ king_Λ_nonneg⟩
    (king_h_measurable king_T king_T_measurable king_Λ king_Λ_measurable)
    (ae_of_all _ fun x => ⟨king_Λ x, fun n => king_h_le king_T king_Λ king_Λ_nonneg n x⟩)
  exact king_not_converge ⟨L, hL⟩

/-- **`mk_kingman_linear` is false.** -/
theorem king_not_kingman_linear : ¬ mk_kingman_linear :=
  fun h => king_not_boundedAbove (mk4_boundedAboveKingman_of_kingman h)


/-- **`glw2_KingmanCore` is false**, even with the extra positive-measure hypothesis. -/
theorem king_not_glw2_KingmanCore : ¬ glw2_KingmanCore := by
  intro hcore
  set g : ℕ → king_Ω → ℝ := fun n x => king_h king_T king_Λ n x + n with hg
  have hsub : ∀ m n x, g (m + n) x ≤ g m x + g n (king_T^[m] x) := by
    intro m n x
    have := king_h_subadditive king_T king_Λ king_Λ_nonneg m n x
    simp only [hg]
    push_cast
    linarith
  have hnn : ∀ n x, 0 ≤ g n x := by
    intro n x
    have := king_h_ge king_T king_Λ king_Λ_nonneg n x
    simp only [hg]
    linarith
  have hmeas : ∀ n, Measurable (g n) := fun n =>
    (king_h_measurable king_T king_T_measurable king_Λ king_Λ_measurable n).add measurable_const
  have hle : ∀ n x, g n x ≤ 1 * n + king_Λ x := by
    intro n x
    have := king_h_le king_T king_Λ king_Λ_nonneg n x
    simp only [hg]
    linarith
  have hae : ∀ᵐ x ∂king_μ, ∃ K : ℝ, ∀ n : ℕ, g n x ≤ 1 * n + K :=
    ae_of_all _ fun x => ⟨king_Λ x, fun n => hle n x⟩
  have hAmeas : MeasurableSet {x | ∀ n : ℕ, g n x ≤ 1 * n + 2} := by
    have : {x | ∀ n : ℕ, g n x ≤ 1 * n + 2} = ⋂ n : ℕ, {x | g n x ≤ 1 * n + 2} := by
      ext x; simp
    rw [this]
    exact MeasurableSet.iInter fun n => measurableSet_le (hmeas n) measurable_const
  have hsub0 : (fun ω : king_Ω => ω 0) ⁻¹' king_F ⊆ {x | ∀ n : ℕ, g n x ≤ 1 * n + 2} := by
    intro x hx n
    have hx' : (1 / 2 : ℝ) < ((x 0 : unitInterval) : ℝ) := hx
    have hpos : (0 : ℝ) < ((x 0 : unitInterval) : ℝ) := by linarith
    have hΛ : king_Λ x < 2 := by
      unfold king_Λ
      rw [inv_lt_comm₀ hpos (by norm_num)]
      linarith
    exact (hle n x).trans (by linarith)
  have hApos : 0 < king_μ {x | ∀ n : ℕ, g n x ≤ 1 * n + 2} := by
    refine lt_of_lt_of_le ?_ (measure_mono hsub0)
    rw [king_coord_measure 0 king_F_measurable, king_F_volume]
    simp
  obtain ⟨L, hL⟩ := hcore king_μ king_T king_ergodic.toMeasurePreserving king_ergodic g hsub hnn
    hmeas 1 hae 2 hAmeas hApos
  refine king_not_converge ⟨L - 1, ?_⟩
  filter_upwards [hL] with ω hω
  have h1 : Tendsto (fun n : ℕ => g n ω / (n : ℝ) - 1) atTop (𝓝 (L - 1)) := hω.sub_const 1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [hg]
  field_simp
  ring

end Bernoulli

end Exploding
