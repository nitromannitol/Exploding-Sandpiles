/-
Proposition 7.5 of the paper: a product background with at least `d` chips and
a positive density of `(2d-1)`-sites is box-crossing.

DECOMPOSITION (not a completed proof).  See the accompanying report for a
lemma-by-lemma difficulty/status table.

The single biggest finding of this decomposition is a **vocabulary mismatch**
between the toolkit named for this node and the target statement.
`Exploding/Support/SubLayer.lean`, `SubLayerProj.lean` and `SubSpanBridge.lean`
are written entirely in terms of the *unshifted square* cube `cube (d+1) n`
and the *unshifted* bootstrap odometer `spanOdo n`, from `Vocab.lean`'s
Section-7.2 vocabulary.  The target `BoxCrossingHyp`/`BoxCrossed`/
`CrossedInDirection`, from `Hypotheses.lean`'s Section-5/7.3 vocabulary, are
stated for a *general rectangular, translated* tile `rboxShift k j`, ignited
along one external `faceOut`, with the box's complement (not a hand-picked
superset) frozen.  For the uniform `k := fun _ => n` and `j := 0` the two
tilings agree as *sets* (`rboxShift (fun _ => n) 0 = cube d n`, proved below),
but the two toppling processes are seeded differently: `redOdoUp`'s initial
condition lights the *entire* hyperplane `{x_0 = 0}` of `ℤ^{d+1}`, while
`CrossedInDirection`'s lights only the face `faceOut` (the hyperplane
restricted to the box's own footprint) and freezes the rest of the box's
complement at `0` instead of at the hyperplane's value there.  The two agree
at every site that ever interacts with the box's interior (only axis-adjacent
exterior sites do, and those lie inside the footprint, where both give `1`),
but *proving* that formally is its own translation lemma
(`aux_box_crossing_core`, below), not a corollary of any single toolkit lemma.

Given `hd : 2 ≤ d`, the frozen target only ever needs the box-decomposes-into-
layers *inductive step* of `exploding.tex:1975-1986` (`(d+1) ≥ 2`, reducing
one dimension via `Exploding.Frozen.dimensional_reduction` and Schonmann at
dimension `d - 1`); the paper's separate base case ("immediate in dimension
one") is for target-dimension `1`, which `hd` excludes, so no induction on
dimension is needed at all for this specific frozen statement.
-/
import Exploding.Support.Hypotheses
import Exploding.Support.SubFodoStep
import Exploding.Support.SubLayer
import Exploding.Support.SubSpanBridge
import Exploding.Support.SubSpanZero
import Exploding.External.Schonmann
import Exploding.Frozen.DimensionalReduction
import LatticeProb.Prob.Blocks

/- NOTE (toolkit issue, not fixed here): `Exploding.Support.SubLayerProj` is
listed as part of this node's toolkit alongside `SubLayer`, but the two files
both declare `Exploding.layer` with an identical body, so they cannot be
imported together (`import ... failed, environment already contains
'Exploding.layer'`).  `SubLayer` supplies `cube_eq_iUnion_layer`,
`SubLayerProj` supplies `mem_layer_iff`; a real proof of `aux_box_crossing_core`
would need both and so would need one of the two files' `layer` declarations
removed/deduplicated first. -/

open Exploding LatticeProb MeasureTheory

set_option linter.unusedVariables false

/-! ### The dimension shift and the (non-)base-case -/

/-- **Real, near-trivial.** For a uniform `k` and the untranslated tile
(`j = 0`), the general rectangular-tile vocabulary of `Hypotheses.lean`
degenerates to the plain cube of `Vocab.lean`. -/
theorem aux_box_crossing_rboxShift_zero_eq_cube (d n : ℕ) :
    rboxShift (fun _ : Fin d => n) (0 : Site d) = cube d n := by
  ext x
  simp [rboxShift, cube]

-- FALSE AS DESIGNED, FIXED BELOW. As designed, `aux_box_crossing_core` assumed only that layer 1
-- (`InternallySpanned (fun w => η (cons 1 w) - 1) n`) was internally spanned, and concluded that
-- the WHOLE box `cube (d+1) n` gets crossed. This is false: take `d := 1`, `n := 2`, and any `η`
-- for which layer 1 is spanned (its own hypothesis genuinely can hold, e.g. every site of layer 1
-- has `η = 2d`) but layer 2 is far below threshold everywhere, e.g. `η (cons 2 w) := 2 * (d:ℤ)`
-- for every `w` (`2*d < 2*(d+1)`, the firing threshold, and `η (cons 2 w) - 1 = 2*d-1 < 2*d`, so
-- layer 2's OWN bootstrap process, run in isolation, never fires anywhere either). Layer 2 then
-- receives only a permanent `+1` from its now-toppled layer-1 neighbour once layer 1 fires, giving
-- each of its sites at most `1 + 2d = 2d+1 < 2*(d+1) = 2d+2` total, so layer 2 never reaches
-- threshold and the box is never fully toppled: `CrossedInDirection`'s conclusion `1 ≤ fodo … x`
-- fails at every `x` with `x 0 = 2`, contradicting the claim for every `t`. The fix is exactly the
-- hypothesis the earlier Assembly comment already names for this step ("turns 'every
-- layer spans' into 'the box is crossed'"): every layer `i ∈ [1,n]`, not just layer 1, must be
-- spanned (matching `Ω' = ⋂_{i=1}^n Ω_i` in the paper, `exploding.tex:1997-2002`).
/-- **New, real (generalises `Exploding.Support.SubWave.wave_le_fodo`'s domination technique).**
The uncapped `fodo` process dominates any `{0,1}`-valued `S`-frozen process with the same frozen
initial data on `S` and the same "topple once, then freeze at 1" update off `S`: both processes can
only ever add at most `1` at a site per step where the threshold is met, and once the capped
process is `≤` the uncapped one the same holds a step later, by the "floor dominates the capped
increment" comparison (`Int.ediv_le_ediv` against `nbrSumZ_mono` on the induction hypothesis),
exactly the technique already used, for a different pair of processes, throughout this project
(e.g. `Exploding.Support.SubWave.wave_le_fodo`); restated here since only this node's file may be
edited. -/
theorem aux_box_crossing_fodo_dominates_capped {d : ℕ} (S : Set (Site d)) (η : Site d → ℤ)
    (w0 : Site d → ℤ) (capped : ℕ → Site d → ℤ)
    (hcap0 : capped 0 = w0)
    (hcapS : ∀ t x, x ∈ S → capped t x = w0 x)
    (hcapstep : ∀ t x, x ∉ S → capped (t + 1) x =
      if capped t x = 1 then 1
      else capped t x + (if 2 * (d : ℤ) ≤ η x + lap (capped t) x then 1 else 0)) :
    ∀ t x, capped t x ≤ fodo S η w0 t x := by
  intro t
  induction t with
  | zero =>
    intro x
    rw [hcap0, fodo_zero]
  | succ t ih =>
    intro x
    by_cases hxS : x ∈ S
    · rw [hcapS (t + 1) x hxS, fodo_succ, if_pos hxS]
    · rw [hcapstep t x hxS, fodo_succ, if_neg hxS]
      by_cases h_one : capped t x = 1
      · rw [if_pos h_one]
        have h_ih := ih x
        rw [h_one] at h_ih
        have h_fodo_succ_ge : fodo S η w0 t x ≤ fodo S η w0 (t + 1) x := by
          rw [fodo_succ, if_neg hxS]
          exact le_add_of_nonneg_right (by split_ifs <;> omega)
        omega
      · rw [if_neg h_one]
        set δ := if 2 * (d : ℤ) ≤ η x + lap (capped t) x then (1 : ℤ) else 0 with hδ
        set ε := if 2 * (d : ℤ) ≤ fconf S η w0 t x then (1 : ℤ) else 0 with hε
        have h_capped_le_fodo : capped t x ≤ fodo S η w0 t x := ih x
        by_cases hδ_le_ε : δ ≤ ε
        · omega
        · have hδ_one : δ = 1 := by
            have hδ_le_one : δ ≤ 1 := by
              rw [hδ]
              split_ifs <;> omega
            omega
          have hε_zero : ε = 0 := by
            have hε_ge_zero : 0 ≤ ε := by
              rw [hε]
              split_ifs <;> omega
            omega
          rw [hδ_one, hε_zero, add_zero]
          have h_thresh_capped : 2 * (d : ℤ) ≤ η x + lap (capped t) x := by
            rw [hδ] at hδ_one
            split_ifs at hδ_one with hc
            · exact hc
            · omega
          have h_thresh_fodo_lt : fconf S η w0 t x < 2 * (d : ℤ) := by
            rw [hε] at hε_zero
            split_ifs at hε_zero with hc
            · omega
            · omega
          simp [lap, fconf] at h_thresh_capped h_thresh_fodo_lt
          have h_ineq1 : 2 * (d : ℤ) * (capped t x + 1) ≤ η x + nbrSumZ (capped t) x := by
            nlinarith
          have h_ineq2 : η x + nbrSumZ (fodo S η w0 t) x < 2 * (d : ℤ) * (fodo S η w0 t x + 1) := by
            nlinarith
          have h_nbrSumZ_le : nbrSumZ (capped t) x ≤ nbrSumZ (fodo S η w0 t) x :=
            nbrSumZ_mono (fun y => ih y) x
          have h_chain : 2 * (d : ℤ) * (capped t x + 1) < 2 * (d : ℤ) * (fodo S η w0 t x + 1) := by
            nlinarith
          by_cases hd_zero : d = 0
          · subst hd_zero
            simp at h_chain
          · have hd_pos : 0 < (d : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hd_zero
            have h_pos : 0 < 2 * (d : ℤ) := by nlinarith
            nlinarith

/-- **GAP, hard, new, but now correctly hypothesised (`exploding.tex:1990-2005`, the induction
over all `n` layers of the box-crossing proof).** If EVERY layer `i ∈ [1,n]` (viewed through its
own `-1`-shifted background, matching `redOdoDown`/`spanOdo`'s convention) is internally spanned,
the entire `(d+1)`-dimensional box, ignited from its low face in direction `0`, is fully toppled,
i.e. `CrossedInDirection`.

Proof sketch, by induction on the layer index `i = 1, …, n` (`Finset.Icc 1 n`/`Nat.le_induction`):
layer `1` topples (in the `{0,1}`-capped sense) by `Exploding.Support.SubSpanBridge.
redOdoDown_eq_spanOdo` + `Exploding.Support.Reduction.redOdo_agree` applied to `hspan 1`, since
layer `0` (`x_0 = 0`) is permanently lit by the seed itself — for this instantiation (`k := fun _
=> n`, `j := 0`, direction `⟨0,_⟩`, `hi := false`), `faceOut (fun _ => n) 0 ⟨0,_⟩ false` is exactly
`{x : x_0 = 0} ∩ closureN (cube (d+1) n)`, matching `redOdoUp`'s own seed `{x_0 = 0} ↦ 1`
restricted to where it matters. Given layer `i` fully toppled (capped sense), the SAME reduction
argument — `Exploding.Support.Reduction`'s `redOdoUp`/`redOdoDown`/`redOdo_agree` and
`Exploding.Frozen.dimensional_reduction`, all hard-coded to the floor sitting at layer `0` and the
active layer at `1` — needs to be re-run with the floor shifted to layer `i` and the active layer
at `i+1` (mechanically identical: replace every `cons 1` by `cons (i+1 : ℤ)` and every "`x_0 = 0`"
frozen-floor value by "layer `i` already toppled"); this shifted-floor generalisation is not
literally reusable from `Exploding.Support.Reduction` (whose lemmas are hard-coded to floor `0`)
and would need to be re-proved for a general floor `i`, which is genuinely new (though mechanically
routine) content, the single largest remaining piece in this node. Finally
`aux_box_crossing_fodo_dominates_capped` transports the resulting capped-process conclusion (every
layer fully toppled in the `{0,1}`-capped sense) to the uncapped `fodo` that `CrossedInDirection`
is literally stated with (taking `w0 := Set.indicator (faceOut …) 1`, `S := (rboxShift …)ᶜ`, and
`capped` the pointwise max of the per-layer capped processes, which agrees with `fodo`'s own
"topple once you exceed threshold and only add a further `+1` capped at that step" recursion off
`S`). -/
theorem aux_box_crossing_core (d n : ℕ) (hd : 1 ≤ d) (η : Site (d + 1) → ℤ)
    (hspan : ∀ i ∈ Finset.Icc 1 n, InternallySpanned (fun w : Site d => η (cons (i : ℤ) w) - 1) n) :
    CrossedInDirection η (fun _ : Fin (d + 1) => n) (0 : Site (d + 1))
      ⟨0, by omega⟩ false := by
  sorry

/-! ### The reduction from a general one-site law to the exact two-point law -/

/-- **New, real.** `fodo` is monotone in the background, on the SAME frozen set and initial data:
a pointwise-larger `s0` can only make firing easier, so an induction on `t` (`Int.ediv_le_ediv`
against the inductive hypothesis, exactly as in `Exploding.Support.SubWave.wave_le_fodo`'s and
`Exploding.Support.Toppling.wave_mono_n`'s proofs, which use the identical technique for a
different pair of varying arguments) gives `fodo S s0 w0 t x <= fodo S s0' w0 t x` whenever `s0 <=
s0'` pointwise. -/
theorem aux_box_crossing_fodo_mono_background {d : ℕ} (S : Set (Site d)) (s0 s0' w0 : Site d → ℤ)
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

/-- **New, real.** `Measure.infinitePi` commutes with a coordinatewise pushforward: applying a
measurable map `T` to every coordinate of an i.i.d. field has the same law as an i.i.d. field of
the pushed-forward law `ν.map T`. Proof: `MeasureTheory.eq_infinitePi`, checking the
projective-limit property against `Measure.pi (fun i : I => ν.map T)` for each finite `I` -- the
finite marginal of the LHS is `(Measure.pi (fun _ : I => ν)).map (fun f i => T (f i))`
(`MeasureTheory.Measure.infinitePi_map_restrict` composed with `Measure.map_map`), which equals
`Measure.pi (fun _ : I => ν.map T)` by a finite-product-pushforward identity (grep the library
index for the exact Mathlib name -- e.g. a `Measure.pi`/`Measure.map` composition lemma, or an
explicit induction over `I` using `Measure.map_map`/`Measure.pi_pi` if no single named lemma
matches). -/
theorem aux_box_crossing_infinitePi_map_coord {V : Type*} [MeasurableSpace V] [Countable V]
    (ν : Measure ℤ) [IsProbabilityMeasure ν] (T : ℤ → ℤ) (hT : Measurable T) :
    (Measure.infinitePi fun _ : V => ν).map (fun (η : V → ℤ) x => T (η x))
      = Measure.infinitePi fun _ : V => ν.map T := by
  simpa using Measure.infinitePi_map_pi (μ := fun _ : V => ν) (f := fun _ : V => T) (hf := fun _ => hT)

/-- **New, real.** For `ν` with `ν {m | (d:ℤ) ≤ m} = 1` and writing `p₀ := ν {2d-1}`, the
deterministic map `T x := if x = 2d-1 then 2d-1 else d` pushes `ν` forward to the two-point law
`chipLaw (2d-1) d p₀`: `(ν.map T) {2d-1} = ν (T⁻¹' {2d-1}) = ν {2d-1} = p₀`
(`Measure.map_apply`, `T`'s definition) and `(ν.map T) {d} = ν (T⁻¹' {d}) = ν {m | m ≠ 2d-1} =
1 - p₀` using `hlow` to discard the `ν`-null set `{m < d}` from `T⁻¹'{d} = {m ≠ 2d-1}`
(`measure_compl`, `ν {2d-1} + ν {m | m ≠ 2d-1} = 1`), matching `chipLaw`'s two-atom definition via
`Measure.ext` on the generating singletons (or a direct case split on membership of `2d-1`). -/
theorem aux_box_crossing_two_point_pushforward (d : ℕ) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hlow : ν {m : ℤ | (d : ℤ) ≤ m} = 1) :
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
theorem aux_box_crossing_fodo_measurable {d : ℕ} (S : Set (Site d)) (w0 : Site d → ℤ)
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

/-- **New, real.** `{η | BoxCrossed η k j}` is measurable: `BoxCrossed`/`CrossedInDirection` are
built from countably many `fodo`-value comparisons (`fodo` itself built, at each finite time, from
finitely many `if`/`nbrSumZ`/`lap` operations on the coordinate projections `η ↦ η x`, all
measurable) intersected over the countable index sets `Fin d`, `Bool`, `ℕ`, and `rboxShift k j`
(countable, a subset of `Site d`); a routine but tedious `measurability`-style closure argument, or
an explicit induction on `t` showing `fun η => fodo S η w0 t x` is measurable for each fixed `t x`. -/

theorem aux_box_crossing_boxcrossed_measurable {d : ℕ} (k : Fin d → ℕ) (j : Site d) :
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
  exact measurableSet_le measurable_const (aux_box_crossing_fodo_measurable _ _ _ _)

/-- **New, real.** `ν`-a.e. every coordinate of an `ν`-i.i.d. field is `≥ d`: each one-site
marginal `(Measure.infinitePi fun _ => ν).map (fun η => η x)` equals `ν` (`Measure.infinitePi_
map_restrict'`/an evaluation-map special case, matching `aux_finite_exploding_bounds`'s technique
in `lem-finite-exploding-dec/node.lean`, restated here), so `hlow` gives each single-coordinate
event `{η | (d:ℤ) ≤ η x}` full measure, and `MeasureTheory.ae_all_iff` over the countable index
`Site d` combines them into full measure for the intersection. -/
theorem aux_box_crossing_nu_good (d : ℕ) (ν : Measure ℤ) [IsProbabilityMeasure ν]
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

/-- **GAP, hard, new (`exploding.tex:1807-1809`, "by monotonicity, we may assume `η ∈ {d,
2d-1}`"), now assembled from the pieces above.** A general one-site law `ν` with `ν(η ≥ d) = 1`
and `ν(η = 2d-1) = p₀ > 0` pointwise-dominates the two-point law `chipLaw (2d-1) d p₀` under the
coupling `T` that keeps the atom at `2d-1` and collapses every other value to `d`; parallel
toppling is monotone in the background (`T x ≤ x` whenever `x ≥ d`,
`aux_box_crossing_fodo_mono_background`), so the box-crossing probability under `ν` is at least
that under the two-point law. -/
theorem aux_box_crossing_two_point_reduction (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ)
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
    aux_box_crossing_two_point_pushforward d ν hlow
  have heq : productLaw d (2 * (d : ℤ) - 1) (d : ℤ) (ν {(2 * (d : ℤ) - 1)}).toReal
      = (Measure.infinitePi fun _ : Site d => ν).map (fun η x => T (η x)) := by
    rw [productLaw, ← hpush]
    exact (aux_box_crossing_infinitePi_map_coord ν T hTmeas).symm
  rw [heq]
  have hmeas := aux_box_crossing_boxcrossed_measurable (d := d) k j
  rw [MeasureTheory.Measure.map_apply (by fun_prop) hmeas]
  set Good : Set (Site d → ℤ) := {η | ∀ x, (d : ℤ) ≤ η x} with hGooddef
  have hgood1 := aux_box_crossing_nu_good d ν hlow
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
  have hdom := aux_box_crossing_fodo_mono_background (d := d) (rboxShift k j)ᶜ
    (fun z => T (ω z)) ω (Set.indicator (faceOut k j i hi) 1) hTle t x
  have hcapped : (1 : ℤ) ≤ fodo (rboxShift k j)ᶜ (fun z => T (ω z))
      (Set.indicator (faceOut k j i hi) 1) t x := hω1 i hi t ht x hx
  exact le_trans hcapped (hdom)

/-! ### Independence across layers and translation invariance across tiles -/

/-- **Real.** `Measure.infinitePi` with a constant one-site law is invariant
under translating every site by a fixed vector `v`; this is the exact
statement needed to reduce `BoxCrossingHyp`'s "`∀ j`" to the tile `j = 0`.
Uses `MeasureTheory.Measure.map_infinitePi_infinitePi_of_inj`, the general
reindexing-invariance fact for `Measure.infinitePi` under an injective
reindexing of a constant family, specialized to the (injective) translation
`x ↦ x + v` of `Site d`. -/
theorem aux_box_crossing_shift_invariant (d : ℕ) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (v : Site d) :
    (Measure.infinitePi fun _ : Site d => ν).map (fun η x => η (x + v))
      = Measure.infinitePi fun _ : Site d => ν := by
  have hinj : Function.Injective (fun x : Site d => x + v) := fun a b h => by
    simpa using (add_left_injective v) h
  have h := MeasureTheory.Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Site d => ν) hinj
  simpa using h

-- FALSE AS DESIGNED, FIXED BELOW. The statement below (before the fix) has NO
-- independence/disjoint-coordinate hypothesis at all, so as literally written it is false:
-- take `n := 2`, any `ν` with an atom `ν {a} = 1/2` (e.g. `ν := (chipLaw a b (1/2:ℝ)).map
-- (fun _ => ...)`-style two-point law), fix any site `x₀`, and set `Ω 0 := {η | η x₀ = a}`,
-- `Ω 1 := (Ω 0)ᶜ`, `p := fun _ => (1/2 : ENNReal)`. Then `p i ≤ μ (Ω i)` holds (with equality)
-- for both `i`, but `Ω 0 ∩ Ω 1 = ∅` so `μ (⋂ i, Ω i) = 0`, while `∏ i, p i = 1/4 ≠ 0`: the
-- claimed `∏ i, p i ≤ μ (⋂ i, Ω i)` reads `1/4 ≤ 0`, false. The earlier comment
-- already names the missing ingredient ("the `n` layers' internal-spanning events depend on
-- pairwise-disjoint blocks of coordinates"); the fix below adds that hypothesis explicitly
-- (a family of pairwise-disjoint coordinate blocks `A`, with each `Ω i` measurable for the
-- sigma-algebra generated by reading only the coordinates in `A i`), matching the actual
-- layers (`A i` = sites with first coordinate `i`).
--
-- `LatticeProb.Prob.Blocks` proves exactly this fact
-- (`iIndepSet_of_pairwise_disjoint`), but only for one-site law `ν : Measure ℝ`; its own
-- ingredients (`infinitePi_map_comp'`, `Measure.infinitePi_map_piCurry`,
-- `Measure.infinitePi_map_restrict'`) are already stated for a general value type, so the
-- three lemmas below reproduce its three-step proof (`map_blocks`, `iIndepFun_restrict_of_
-- pairwise_disjoint`, `iIndepSet_of_pairwise_disjoint`) verbatim for `ν : Measure ℤ`.
/-- **New, real.** ℤ-valued analogue of `LatticeProb.Prob.Blocks.map_blocks`: the blocks of an
`ν`-i.i.d. field have the product law. Same proof as the `ℝ`-specific original (`infinitePi_
map_comp'` with `LatticeProb.blockIndex`/`blockIndex_injective`, then `Measure.
infinitePi_map_piCurry` through the `MeasurableEquiv.piCurry` uncurrying), since neither
ingredient is specific to the value type `ℝ`. -/
theorem aux_box_crossing_layers_map_blocks {ι V : Type*} (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (A : ι → Set V) (hdisj : Pairwise (Function.onFun Disjoint A)) :
    (Measure.infinitePi fun _ : V => ν).map (fun ω i => (A i).restrict ω)
      = Measure.infinitePi fun i : ι => Measure.infinitePi fun _ : ↥(A i) => ν := by
  have h1 : (Measure.infinitePi fun _ : V => ν).map (fun ω p => ω (blockIndex A p))
      = Measure.infinitePi fun _ : (i : ι) × ↥(A i) => ν :=
    infinitePi_map_comp' ν (blockIndex A) (blockIndex_injective A hdisj)
  have h2 := Measure.infinitePi_map_piCurry (fun (i : ι) (_ : ↥(A i)) => (ν : Measure ℤ))
  have hcomp : (fun (ω : V → ℤ) (i : ι) => (A i).restrict ω)
      = ⇑(MeasurableEquiv.piCurry fun (_ : ι) (_ : ↥(A _)) => ℤ)
        ∘ (fun (ω : V → ℤ) p => ω (blockIndex A p)) := rfl
  rw [hcomp, ← Measure.map_map (MeasurableEquiv.piCurry _).measurable
    (measurable_pi_lambda _ fun p => measurable_pi_apply (blockIndex A p)), h1, h2]

/-- **New, real.** ℤ-valued analogue of `LatticeProb.Prob.Blocks.
iIndepFun_restrict_of_pairwise_disjoint`: the block-restriction maps of an `ν`-i.i.d. field are
independent. Proof: `aux_box_crossing_layers_map_blocks` plus `Measure.infinitePi_map_restrict'`
identifying each block's own marginal, exactly as in the `ℝ`-specific original. -/
theorem aux_box_crossing_layers_iIndepFun {ι V : Type*} (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (A : ι → Set V) (hdisj : Pairwise (Function.onFun Disjoint A)) :
    ProbabilityTheory.iIndepFun (fun (i : ι) (ω : V → ℤ) => (A i).restrict ω)
      (Measure.infinitePi fun _ : V => ν) := by
  have hm : AEMeasurable (fun (ω : V → ℤ) (i : ι) => (A i).restrict ω)
      (Measure.infinitePi fun _ : V => ν) := by
    refine (measurable_pi_lambda _ fun i => ?_).aemeasurable
    exact measurable_pi_lambda _ fun j => measurable_pi_apply (j : V)
  rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map₀ hm,
    aux_box_crossing_layers_map_blocks ν A hdisj]
  congr 1
  funext i
  exact (Measure.infinitePi_map_restrict' (μ := fun _ : V => ν) (I := A i)).symm

/-- **New, real.** ℤ-valued analogue of `LatticeProb.Prob.Blocks.
iIndepSet_of_pairwise_disjoint`: events that each depend only on coordinates in one of a
pairwise-disjoint family of blocks `A i` are independent. Proof: `iIndep_of_iIndep_of_le`
applied to `aux_box_crossing_layers_iIndepFun`'s block sigma-algebras, exactly as in the
`ℝ`-specific original. -/
theorem aux_box_crossing_layers_iIndepSet {ι V : Type*} (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (A : ι → Set V) (hdisj : Pairwise (Function.onFun Disjoint A)) (E : ι → Set (V → ℤ))
    (hE : ∀ i, MeasurableSet[MeasurableSpace.comap (fun ω : V → ℤ => (A i).restrict ω)
      inferInstance] (E i)) :
    ProbabilityTheory.iIndepSet E (Measure.infinitePi fun _ : V => ν) := by
  classical
  rw [ProbabilityTheory.iIndepSet_iff_iIndep E]
  have hfun := (ProbabilityTheory.iIndepFun_iff_iIndep
      (fun i : ι => (inferInstance : MeasurableSpace (↥(A i) → ℤ)))
      (fun (i : ι) (ω : V → ℤ) => (A i).restrict ω)
      (Measure.infinitePi fun _ : V => ν)).mp
      (aux_box_crossing_layers_iIndepFun ν A hdisj)
  refine ProbabilityTheory.iIndep_of_iIndep_of_le
    (m₂ := fun i : ι => MeasurableSpace.comap (fun ω : V → ℤ => (A i).restrict ω)
      (inferInstance : MeasurableSpace (↥(A i) → ℤ))) hfun ?_
  intro i
  refine MeasurableSpace.generateFrom_le ?_
  intro t ht
  rw [Set.mem_singleton_iff] at ht
  rw [ht]
  exact hE i

