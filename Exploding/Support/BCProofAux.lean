/-
Auxiliary lemmas for the box-crossing proof (Proposition 7.5 of
`paper/corrected-arxiv/exploding-corrected-arxiv.tex`): monotonicity of the frozen odometer in the background,
the reduction of a general one-site law `ν` with `ν(m ≥ d) = 1` and `ν{2d-1} > 0`
to the two-point law `chipLaw (2d-1) d p₀` ("by monotonicity we may assume
`η ∈ {d, 2d-1}`"), and measurability of the crossing event.
-/
import Exploding.Support.Hypotheses

open Exploding LatticeProb MeasureTheory


/-- `fodo` is monotone in the background, on the SAME frozen set and initial data:
a pointwise-larger `s0` can only make firing easier, so an induction on `t` (`Int.ediv_le_ediv`
against the inductive hypothesis, exactly as in `Exploding.Support.SubWave.wave_le_fodo`'s and
`Exploding.Support.Toppling.wave_mono_n`'s proofs, which use the identical technique for a
different pair of varying arguments) gives `fodo S s0 w0 t x <= fodo S s0' w0 t x` whenever `s0 <=
s0'` pointwise. -/
theorem bc_fodo_mono_background {d : ℕ} (S : Set (Site d)) (s0 s0' w0 : Site d → ℤ)
    (hs0 : ∀ x, s0 x ≤ s0' x) : ∀ t x, fodo S s0 w0 t x ≤ fodo S s0' w0 t x := by
  intro t
  induction t with
  | zero =>
    intro x
    rfl
  | succ t ih =>
    intro x
    by_cases hx : x ∈ S
    · rw [Exploding.fodo_succ, Exploding.fodo_succ, if_pos hx, if_pos hx]
    · rw [Exploding.fodo_succ, Exploding.fodo_succ, if_neg hx, if_neg hx]
      have h_ih := ih x
      by_cases hc : 2 * (d : ℤ) ≤ fconf S s0 w0 t x
      · by_cases hc' : 2 * (d : ℤ) ≤ fconf S s0' w0 t x
        · rw [if_pos hc, if_pos hc']
          omega
        · rw [if_pos hc, if_neg hc']
          have hlt : fodo S s0 w0 t x < fodo S s0' w0 t x := by
            by_contra! heq
            have heq' : fodo S s0 w0 t x = fodo S s0' w0 t x := by omega
            have h_nbrSumZ : nbrSumZ (fodo S s0 w0 t) x ≤ nbrSumZ (fodo S s0' w0 t) x :=
              Exploding.nbrSumZ_mono (fun y => ih y) x
            have hle : fconf S s0 w0 t x ≤ fconf S s0' w0 t x := by
              dsimp [Exploding.fconf, Exploding.lap]
              rw [heq']
              have h1 : s0 x ≤ s0' x := hs0 x
              have h2 : nbrSumZ (fodo S s0 w0 t) x ≤ nbrSumZ (fodo S s0' w0 t) x := h_nbrSumZ
              linarith
            have : 2 * (d : ℤ) ≤ fconf S s0' w0 t x := by linarith
            exact hc' this
          omega
      · by_cases hc' : 2 * (d : ℤ) ≤ fconf S s0' w0 t x
        · rw [if_neg hc, if_pos hc']
          omega
        · rw [if_neg hc, if_neg hc']
          simpa

/-- `Measure.infinitePi` commutes with a coordinatewise pushforward: applying a
measurable map `T` to every coordinate of an i.i.d. field has the same law as an i.i.d. field of
the pushed-forward law `ν.map T`. Proof: `MeasureTheory.eq_infinitePi`, checking the
projective-limit property against `Measure.pi (fun i : I => ν.map T)` for each finite `I` -- the
finite marginal of the LHS is `(Measure.pi (fun _ : I => ν)).map (fun f i => T (f i))`
(`MeasureTheory.Measure.infinitePi_map_restrict` composed with `Measure.map_map`), which equals
`Measure.pi (fun _ : I => ν.map T)` by a finite-product-pushforward identity (a `Measure.pi`/`Measure.map`
composition, or an explicit induction over `I` using `Measure.map_map`/`Measure.pi_pi`). -/
theorem bc_infinitePi_map_coord {V : Type*} [MeasurableSpace V] [Countable V]
    (ν : Measure ℤ) [IsProbabilityMeasure ν] (T : ℤ → ℤ) (hT : Measurable T) :
    (Measure.infinitePi fun _ : V => ν).map (fun (η : V → ℤ) x => T (η x))
      = Measure.infinitePi fun _ : V => ν.map T := by
  simpa using Measure.infinitePi_map_pi (μ := fun _ : V => ν) (f := fun _ : V => T) (hf := fun _ => hT)

/-- For `ν` with `ν {m | (d:ℤ) ≤ m} = 1` and writing `p₀ := ν {2d-1}`, the
deterministic map `T x := if x = 2d-1 then 2d-1 else d` pushes `ν` forward to the two-point law
`chipLaw (2d-1) d p₀`: `(ν.map T) {2d-1} = ν (T⁻¹' {2d-1}) = ν {2d-1} = p₀`
(`Measure.map_apply`, `T`'s definition) and `(ν.map T) {d} = ν (T⁻¹' {d}) = ν {m | m ≠ 2d-1} =
1 - p₀` using `hlow` to discard the `ν`-null set `{m < d}` from `T⁻¹'{d} = {m ≠ 2d-1}`
(`measure_compl`, `ν {2d-1} + ν {m | m ≠ 2d-1} = 1`), matching `chipLaw`'s two-atom definition via
`Measure.ext` on the generating singletons (or a direct case split on membership of `2d-1`). -/
theorem bc_two_point_pushforward (d : ℕ) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (_hlow : ν {m : ℤ | (d : ℤ) ≤ m} = 1) :
    ν.map (fun x => if x = 2 * (d : ℤ) - 1 then 2 * (d : ℤ) - 1 else (d : ℤ))
      = chipLaw (2 * (d : ℤ) - 1) (d : ℤ) (ν {(2 * (d : ℤ) - 1)}).toReal := by
  set a := 2 * (d : ℤ) - 1
  set b := (d : ℤ)
  set p₀ := (ν {a}).toReal
  set T := (fun x : ℤ => if x = a then a else b)
  have hT_meas : Measurable T := by
    refine Measurable.ite (measurableSet_singleton a) measurable_const measurable_const
  have ha_fin : ν {a} ≠ ⊤ := (measure_lt_top ν {a}).ne
  have ha_le_one : ν {a} ≤ 1 := by
    calc
      ν {a} ≤ ν Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := by simp
  have h_univ : ν Set.univ = 1 := by simp
  have h_compl : ν ({a}ᶜ) = 1 - ν {a} := by
    rw [measure_compl (measurableSet_singleton a) ha_fin, h_univ]
  have hp₀_nonneg : 0 ≤ p₀ := ENNReal.toReal_nonneg
  have hp₀_le_one : p₀ ≤ 1 := by
    dsimp [p₀]
    -- ν {a} ≤ 1, so (ν {a}).toReal ≤ 1
    have h := ha_le_one
    -- h : ν {a} ≤ 1 in ENNReal, where 1 is coerced from ℝ≥0
    have h' := ENNReal.toReal_le_coe_of_le_coe h
    -- h' : (ν {a}).toReal ≤ (1 : ℝ≥0)
    simpa using h'
  have h_ofReal_p₀ : ENNReal.ofReal p₀ = ν {a} := by
    rw [ENNReal.ofReal_toReal ha_fin]
  have h_ofReal_one_sub_p₀ : ENNReal.ofReal (1 - p₀) = 1 - ν {a} := by
    calc
      ENNReal.ofReal (1 - p₀) = ENNReal.ofReal 1 - ENNReal.ofReal p₀ := by
        refine ENNReal.ofReal_sub 1 ?_
        -- need 0 ≤ p₀, which we have
        exact hp₀_nonneg
      _ = 1 - ENNReal.ofReal p₀ := by simp
      _ = 1 - ν {a} := by rw [h_ofReal_p₀]
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hT_meas hs]
  rw [chipLaw]
  simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' a hs,
    Measure.dirac_apply' b hs]
  -- Goal: ν (T⁻¹' s) = ENNReal.ofReal p₀ * (if a ∈ s then 1 else 0) + ENNReal.ofReal (1 - p₀) * (if b ∈ s then 1 else 0)
  by_cases ha_s : a ∈ s
  · by_cases hb_s : b ∈ s
    · -- both a and b in s
      have h_preimage : T⁻¹' s = Set.univ := by
        ext x
        simp [T]
        by_cases hx : x = a
        · simp [hx, ha_s]
        · simp [hx, hb_s]
      rw [h_preimage, h_univ]
      simp [ha_s, hb_s]
      -- Goal: 1 = ENNReal.ofReal p₀ + ENNReal.ofReal (1 - p₀)
      rw [h_ofReal_p₀, h_ofReal_one_sub_p₀]
      -- Goal: 1 = ν {a} + (1 - ν {a})
      rw [add_comm, tsub_add_cancel_of_le ha_le_one]
    · -- a in s, b not in s
      have h_preimage : T⁻¹' s = {a} := by
        ext x
        simp [T]
        by_cases hx : x = a
        · simp [hx, ha_s]
        · simp [hx, hb_s]
      rw [h_preimage]
      simp [ha_s, hb_s, h_ofReal_p₀]
  · by_cases hb_s : b ∈ s
    · -- a not in s, b in s
      have h_preimage : T⁻¹' s = {a}ᶜ := by
        ext x
        simp [T]
        by_cases hx : x = a
        · simp [hx, ha_s]
        · simp [hx, hb_s]
      rw [h_preimage]
      simp [ha_s, hb_s, h_compl, h_ofReal_one_sub_p₀]
    · -- neither a nor b in s
      have h_preimage : T⁻¹' s = ∅ := by
        ext x
        simp [T]
        by_cases hx : x = a
        · simp [hx, ha_s]
        · simp [hx, hb_s]
      rw [h_preimage]
      simp [ha_s, hb_s]

/-- The `S`-frozen odometer is a measurable function of the background, at every
time and site: induction on `t`, with `fodo_zero` for the base and `fodo_succ`
plus `Measurable.ite` on the measurable set `{η | 2d ≤ fconf S η w0 t x}` for
the step. -/
theorem bc_fodo_measurable {d : ℕ} (S : Set (Site d)) (w0 : Site d → ℤ)
    (t : ℕ) (x : Site d) :
    Measurable (fun η : Site d → ℤ => fodo S η w0 t x) := by
  induction t generalizing x with
  | zero =>
    simp only [fodo_zero]
    exact measurable_const
  | succ t ih =>
    simp only [fodo_succ]
    by_cases hx : x ∈ S
    · simp only [hx, if_true]
      exact measurable_const
    · simp only [hx, if_false]
      apply Measurable.add (ih x)
      apply Measurable.ite
      · apply measurableSet_le measurable_const
        unfold fconf lap nbrSumZ
        apply Measurable.add
        · exact measurable_pi_apply x
        · apply Measurable.sub
          · apply Finset.measurable_sum
            intro i _
            apply Measurable.add
            · exact ih (x + unit i)
            · exact ih (x - unit i)
          · apply Measurable.mul measurable_const (ih x)
      · exact measurable_const
      · exact measurable_const

/-- `{η | BoxCrossed η k j}` is measurable: `BoxCrossed`/`CrossedInDirection` are
built from countably many `fodo`-value comparisons (`fodo` itself built, at each finite time, from
finitely many `if`/`nbrSumZ`/`lap` operations on the coordinate projections `η ↦ η x`, all
measurable) intersected over the countable index sets `Fin d`, `Bool`, `ℕ`, and `rboxShift k j`
(countable, a subset of `Site d`); a routine but tedious `measurability`-style closure argument, or
an explicit induction on `t` showing `fun η => fodo S η w0 t x` is measurable for each fixed `t x`. -/

theorem bc_boxcrossed_measurable {d : ℕ} (k : Fin d → ℕ) (j : Site d) :
    MeasurableSet {η : Site d → ℤ | BoxCrossed η k j} := by
  have h : {η : Site d → ℤ | BoxCrossed η k j} =
      ⋂ (i : Fin d) (hi : Bool) (t : ℕ), ⋂ (_ : (∏ l, k l) ≤ t),
        ⋂ (x : Site d), ⋂ (_ : x ∈ rboxShift k j),
          {η : Site d → ℤ | 1 ≤ fodo (rboxShift k j)ᶜ η (Set.indicator (faceOut k j i hi) 1) t x} := by
    ext η; simp [BoxCrossed, CrossedInDirection]
  rw [h]
  refine MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun hi => MeasurableSet.iInter (fun t => ?_)))
  refine MeasurableSet.iInter (fun _ => ?_)
  refine MeasurableSet.iInter (fun x => ?_)
  refine MeasurableSet.iInter (fun _ => ?_)
  exact measurableSet_le measurable_const (bc_fodo_measurable _ _ _ _)

/-- `ν`-a.e. every coordinate of an `ν`-i.i.d. field is `≥ d`: each one-site
marginal `(Measure.infinitePi fun _ => ν).map (fun η => η x)` equals `ν` (`Measure.infinitePi_
map_restrict'`/an evaluation-map special case, matching the technique of `aux_finite_exploding_bounds`
in `Exploding/Support/SubFinite.lean`), so `hlow` gives each single-coordinate
event `{η | (d:ℤ) ≤ η x}` full measure, and `MeasureTheory.ae_all_iff` over the countable index
`Site d` combines them into full measure for the intersection. -/
theorem bc_nu_good (d : ℕ) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hlow : ν {m : ℤ | (d : ℤ) ≤ m} = 1) :
    (Measure.infinitePi fun _ : Site d => ν) {η : Site d → ℤ | ∀ x, (d : ℤ) ≤ η x} = 1 := by
  let μ := Measure.infinitePi fun _ : Site d => ν
  have h_eval (x : Site d) : μ.map (fun η : Site d → ℤ => η x) = ν := by
    simpa [μ] using (measurePreserving_eval_infinitePi (fun _ : Site d => ν) x).map_eq
  have h_single_prob (x : Site d) : μ {η | (d : ℤ) ≤ η x} = 1 := by
    have h_meas_cod : MeasurableSet {m : ℤ | (d : ℤ) ≤ m} :=
      measurableSet_le measurable_const measurable_id
    calc
      μ {η | (d : ℤ) ≤ η x} = μ ((fun η : Site d → ℤ => η x) ⁻¹' {m | (d : ℤ) ≤ m}) := by
        simp
      _ = (μ.map (fun η => η x)) {m | (d : ℤ) ≤ m} := by
        rw [Measure.map_apply (measurable_pi_apply x) h_meas_cod]
      _ = ν {m | (d : ℤ) ≤ m} := by rw [h_eval x]
      _ = 1 := hlow
  have h_single_null (x : Site d) : μ {η | η x < (d : ℤ)} = 0 := by
    have h_meas : MeasurableSet {η : Site d → ℤ | (d : ℤ) ≤ η x} :=
      measurableSet_le measurable_const (measurable_pi_apply x)
    have h_compl : μ ({η | (d : ℤ) ≤ η x}ᶜ) = 0 := by
      calc
        μ ({η | (d : ℤ) ≤ η x}ᶜ) = μ Set.univ - μ {η | (d : ℤ) ≤ η x} := by
          rw [measure_compl h_meas (measure_ne_top _ _)]
        _ = 1 - 1 := by rw [measure_univ, h_single_prob x]
        _ = 0 := by simp
    simpa [Set.compl_setOf, not_le] using h_compl
  have h_all_null : μ {η | ∃ x, η x < (d : ℤ)} = 0 := by
    have h_union : {f : Site d → ℤ | ∃ x, f x < (d : ℤ)} = ⋃ (x : Site d), {f : Site d → ℤ | f x < (d : ℤ)} := by
      ext f; simp
    rw [h_union]
    simp [h_single_null]
  have h_target_compl : ({η | ∀ x, (d : ℤ) ≤ η x}ᶜ : Set (Site d → ℤ)) = {η | ∃ x, η x < (d : ℤ)} := by
    ext η; simp
  have h_meas_target : MeasurableSet {η : Site d → ℤ | ∀ x, (d : ℤ) ≤ η x} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun x =>
      measurableSet_le measurable_const (measurable_pi_apply x)
  have h_compl_null : μ ({η | ∀ x, (d : ℤ) ≤ η x}ᶜ) = 0 := by
    rw [h_target_compl]
    exact h_all_null
  have h_add := measure_add_measure_compl (μ := μ) h_meas_target
  rw [h_compl_null, measure_univ, add_zero] at h_add
  simpa [μ] using h_add

/-- (`exploding-corrected-arxiv.tex:1926-1928`, "by monotonicity, we may assume `η ∈ {d,
2d-1}`"), now assembled from the pieces above. A general one-site law `ν` with `ν(η ≥ d) = 1`
and `ν(η = 2d-1) = p₀ > 0` pointwise-dominates the two-point law `chipLaw (2d-1) d p₀` under the
coupling `T` that keeps the atom at `2d-1` and collapses every other value to `d`; parallel
toppling is monotone in the background (`T x ≤ x` whenever `x ≥ d`,
`bc_fodo_mono_background`), so the box-crossing probability under `ν` is at least
that under the two-point law. -/
theorem bc_two_point_reduction (d : ℕ) (_hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] (hlow : ν {m : ℤ | (d : ℤ) ≤ m} = 1)
    (k : Fin d → ℕ) (j : Site d) :
    productLaw d (2 * (d : ℤ) - 1) (d : ℤ) (ν {(2 * (d : ℤ) - 1)}).toReal
        {η | BoxCrossed η k j}
      ≤ (Measure.infinitePi fun _ : Site d => ν) {η | BoxCrossed η k j} := by
  classical
  set T : ℤ → ℤ := fun x => if x = 2 * (d : ℤ) - 1 then 2 * (d : ℤ) - 1 else (d : ℤ) with hTdef
  have hTmeas : Measurable T :=
    Measurable.ite (measurableSet_singleton _) measurable_const measurable_const
  have hpush : ν.map T = chipLaw (2 * (d : ℤ) - 1) (d : ℤ) (ν {(2 * (d : ℤ) - 1)}).toReal :=
    bc_two_point_pushforward d ν hlow
  have heq : productLaw d (2 * (d : ℤ) - 1) (d : ℤ) (ν {(2 * (d : ℤ) - 1)}).toReal
      = (Measure.infinitePi fun _ : Site d => ν).map (fun η x => T (η x)) := by
    rw [productLaw, ← hpush]
    exact (bc_infinitePi_map_coord ν T hTmeas).symm
  rw [heq]
  have hmeas := bc_boxcrossed_measurable (d := d) k j
  rw [MeasureTheory.Measure.map_apply (by fun_prop) hmeas]
  set Good : Set (Site d → ℤ) := {η | ∀ x, (d : ℤ) ≤ η x} with hGooddef
  have hgood1 := bc_nu_good d ν hlow
  have hGoodEq : Good = ⋂ x : Site d, {η : Site d → ℤ | (d : ℤ) ≤ η x} := (Set.iInter_setOf _).symm
  have hGoodMeas : MeasurableSet Good := by
    rw [hGoodEq]
    exact MeasurableSet.iInter (fun x => measurableSet_le measurable_const (measurable_pi_apply x))
  have hgoodc0 : (Measure.infinitePi fun _ : Site d => ν) Goodᶜ = 0 := by
    have hsum := MeasureTheory.measure_add_measure_compl (μ := Measure.infinitePi fun _ : Site d => ν)
      hGoodMeas
    rw [hgood1, MeasureTheory.measure_univ] at hsum
    have h1ne : (1 : ENNReal) ≠ ⊤ := by norm_num
    exact (ENNReal.add_right_inj h1ne).mp (by rw [hsum]; ring)
  have hinter : (Measure.infinitePi fun _ : Site d => ν)
      ((fun (η : Site d → ℤ) x => T (η x)) ⁻¹' {η | BoxCrossed η k j} ∩ Good)
      = (Measure.infinitePi fun _ : Site d => ν)
        ((fun (η : Site d → ℤ) x => T (η x)) ⁻¹' {η | BoxCrossed η k j}) :=
    MeasureTheory.measure_inter_conull hgoodc0
  rw [← hinter]
  apply MeasureTheory.measure_mono
  intro ω hω
  obtain ⟨hω1, hω2⟩ := hω
  show BoxCrossed ω k j
  intro i hi t ht x hx
  have hTle : ∀ z, T (ω z) ≤ ω z := by
    intro z
    by_cases hz : ω z = 2 * (d : ℤ) - 1
    · simp [hTdef, hz]
    · simp only [hTdef, if_neg hz]
      exact hω2 z
  have hdom := bc_fodo_mono_background (d := d) (rboxShift k j)ᶜ
    (fun z => T (ω z)) ω (Set.indicator (faceOut k j i hi) 1) hTle t x
  have hcapped : (1 : ℤ) ≤ fodo (rboxShift k j)ᶜ (fun z => T (ω z))
      (Set.indicator (faceOut k j i hi) 1) t x := hω1 i hi t ht x hx
  exact le_trans hcapped (hdom)

