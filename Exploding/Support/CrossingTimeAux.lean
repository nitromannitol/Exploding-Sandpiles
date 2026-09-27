/-
Proposition 2.1 of the paper (`exploding.tex:416-449`, `prop:crossing_time`):
a large box is crossed quickly with high probability.

DECOMPOSITION (not a proof attempt).  The paper's proof outline:

  (a) a deterministic "domino" propagation fact: if every line of `Q_k`, in
      every direction, carries a `(2d-1)`-chip catalyst, then `Q_k` is a good
      cube (every crossing time is `≤ k^d`);
  (b) Hoeffding's inequality bounds, for one fixed line, the probability that
      its count of `(2d-1)`-chip sites falls at or below `(p-ε)k`;
  (c) a union bound over the (at most `|cube d k|`) choices of a line's
      off-axis point, for one fixed direction, turns (b) into a bound on the
      probability that *some* line in that direction has no catalyst at all;
  (d) the paper reduces "some direction is bad" to "a fixed direction is bad"
      by Harris' inequality and symmetry.  That machinery is not needed: (c)'s
      argument is already uniform in the direction (nothing in the per-line
      computation used which coordinate the line runs in), so a further union
      bound over the `d` directions is literally the same bound applied `d`
      times, each of the `d` terms being *equal* (not merely comparable) by
      the direction-symmetry of the toy law.  No Harris/FKG positive-
      association fact is used anywhere below, only Boole's inequality;
  (e) assembly: pick `ε ∈ (0,p)` and `k` large enough that (d)'s bound is
      `< δ`, using the standard polynomial-times-geometric decay
      (`tendsto_pow_const_mul_const_pow_of_lt_one`,
      `Mathlib.Analysis.SpecificLimits.Normed`, confirmed present); intersect
      the resulting `≥ 1-δ` event with the a.s. pointwise bound on `η`
      (needed since (a) takes `η` bounded *everywhere*, not merely a.e.), and
      apply (a) pointwise.

Where this decomposition differs in shape from a byte-for-byte transcription
of the paper: the union bound in (c)+(d) is taken over *every* `y ∈ cube d k`
in *every* direction, giving a factor `d · |cube d k|` rather than the paper's
tighter `d · k^{d-1}` (the paper only counts the `k^{d-1}` distinct lines in a
direction, since a line depends solely on the off-axis coordinates of `y`).
The looser count still `→ 0`, so no mathematical content is lost; only the
paper's display `(eq:crossing_time_bound)`'s exact rate is not reproduced,
which the target theorem does not ask for (it only asserts *existence* of a
good `k`).

Prior full-proof attempt at `scratch/leanstral/work/prop-crossing-time/node.lean`
got stuck at exactly the boundary between (c)/(e) [fully worked, down to a
correct real-analysis decay argument] and (a) [left as an unstarted `sorry`,
the fleet's own log noting "I cannot complete any of these. The key missing
piece is the deterministic inclusion"]. It also has a fully proved *exact*
alternative to (b): `prob_line_no_high_chip` computes the no-catalyst
probability on a line exactly as `(1-p)^k` via `Measure.infinitePi_pi`, which
is simpler than Hoeffding and already closes the gap between "no catalyst"
and the tail event without invoking a concentration inequality at all. That
route is a legitimate, easier substitute for (b)+(c) below if a prover finds
it more tractable; both are stated here since the task calls specifically for
the paper's own Hoeffding argument.
-/
import Exploding.Support.Vocab
import Exploding.Support.Wave
import Exploding.Support.SubFodo
import Exploding.Support.SubFodoStep
import Exploding.Support.SubFodoTopple

open Exploding LatticeProb MeasureTheory Filter
open scoped Classical

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

variable {d : ℕ}

/-! ### (b) Hoeffding's inequality, one line -/

-- GAP-closing pieces (both new, both real), used by `aux_ct_hoeffding` below:
/-- **New, real.** The coordinates of `toyLaw d p` at the `k` sites of the line
`j ↦ Function.update y i j`, viewed through `v ↦ p - 1{v = 2d-1}`, are
independent: `toyLaw d p` is `Measure.infinitePi` of the same one-site law at
every site (`Toppling`/`Vocab`), so `ProbabilityTheory.iIndepFun_infinitePi`
(with the constant, measurable map `v ↦ p - if v = 2d-1 then 1 else 0`,
measurable via `Measurable.const_sub`/`Measurable.ite`/`MeasurableSet.singleton`)
gives independence of the family indexed by `Site d`; reindexing along the
injective `j ↦ Function.update y i j` (injective by evaluating at coordinate
`i`, `Function.update_self`) with `ProbabilityTheory.iIndepFun.precomp` gives
the family indexed by `j : ℤ`. -/
theorem aux_ct_hoeffding_indep (d : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (i : Fin d) (y : Site d) :
    ProbabilityTheory.iIndepFun (fun j : ℤ => fun η : Site d → ℤ =>
        p - (if η (Function.update y i j) = 2 * (d : ℤ) - 1 then (1 : ℝ) else 0))
      (toyLaw d p) := by
  have hchip : IsProbabilityMeasure (chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p) := by
    refine ⟨?_⟩
    unfold chipLaw
    simp only [Measure.add_apply, Measure.smul_apply, MeasureTheory.measure_univ, smul_eq_mul,
      mul_one]
    rw [← ENNReal.ofReal_add hp (by linarith)]
    norm_num
  haveI : ∀ _ : Site d, IsProbabilityMeasure (chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p) :=
    fun _ => hchip
  have hbase : ProbabilityTheory.iIndepFun (fun (i : Site d) (ω : Site d → ℤ) => ω i)
      (Measure.infinitePi fun _ : Site d => chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p) :=
    ProbabilityTheory.iIndepFun_infinitePi (fun _ => measurable_id)
  have hbase' : ProbabilityTheory.iIndepFun (fun (i : Site d) (ω : Site d → ℤ) => ω i)
      (toyLaw d p) := by
    simpa [toyLaw, productLaw] using hbase
  have hpre := hbase'.precomp (g := fun j : ℤ => Function.update y i j) (by
    intro a b hab
    have := congrFun hab i
    simpa [Function.update_self] using this)
  refine hpre.comp (fun _ v => p - (if v = 2 * (d : ℤ) - 1 then (1 : ℝ) else 0)) (fun _ => ?_)
  exact Measurable.sub measurable_const (Measurable.ite (measurableSet_singleton _)
    measurable_const measurable_const)

/-- **New, real.** Each `η ↦ p - 1{η(Function.update y i j) = 2d-1}` has a
sub-Gaussian MGF with parameter `1/4` under `toyLaw d p`: it is (everywhere,
not just a.e.) valued in `Set.Icc (p-1) p`, is measurable (as above), and has
mean `0` (the marginal of `toyLaw d p` at any one site is `chipLaw (2d-1)
(2d-2) p`, `Measure.infinitePi_map_eval`/`LatticeProb.integral_eval`, whose
`{2d-1}`-probability is exactly `p` by unfolding `chipLaw` as a sum of scaled
Dirac measures, `MeasureTheory.integral_dirac`); apply
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` with
`a := p - 1`, `b := p`, so `((‖b-a‖₊/2)^2 : NNReal) = 1/4`. -/
theorem aux_ct_hoeffding_subgauss (d : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (i : Fin d)
    (y : Site d) (j : ℤ) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun η : Site d → ℤ =>
        p - (if η (Function.update y i j) = 2 * (d : ℤ) - 1 then (1 : ℝ) else 0))
      (1 / 4 : NNReal) (toyLaw d p) := by
  set z := Function.update y i j with hz
  set f : ℤ → ℝ := fun v => p - (if v = 2 * (d : ℤ) - 1 then (1 : ℝ) else 0) with hf
  have hmeas_f : Measurable f := by fun_prop
  have hmeas_eval : Measurable (fun (η : Site d → ℤ) => η z) := by fun_prop
  have hmeas_X : Measurable (fun (η : Site d → ℤ) => f (η z)) :=
    hmeas_f.comp hmeas_eval
  have h_range : ∀ (ω : Site d → ℤ), f (ω z) ∈ Set.Icc (p - 1) p := by
    intro ω
    dsimp [f, Set.Icc, Set.mem_setOf_eq]
    by_cases h : ω z = 2 * (d : ℤ) - 1
    · simp [h]
    · simp [h]
  have hμ : ∀ i : Site d, IsProbabilityMeasure (chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p) := by
    intro i
    refine ⟨?_⟩
    have h_add : ENNReal.ofReal p + ENNReal.ofReal (1 - p) = 1 := by
      calc
        ENNReal.ofReal p + ENNReal.ofReal (1 - p) = ENNReal.ofReal (p + (1 - p)) := by
          rw [ENNReal.ofReal_add hp.le (by linarith)]
        _ = ENNReal.ofReal 1 := by simp
        _ = 1 := ENNReal.ofReal_one
    dsimp [chipLaw]
    simp [h_add]
  haveI : IsProbabilityMeasure (toyLaw d p) := by
    dsimp [toyLaw, productLaw]
    -- Need to provide the hμ instance
    have : IsProbabilityMeasure (Measure.infinitePi (fun _ : Site d => chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p)) := by
      -- Use the instance from the context
      infer_instance
    exact this
  have h_int : (∫ η : Site d → ℤ, f (η z) ∂(toyLaw d p)) = 0 := by
    have h1mp : 0 ≤ 1 - p := by linarith
    have h_int_chip : (∫ v : ℤ, f v ∂(chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p)) = 0 := by
      dsimp [chipLaw, f]
      have h_int_dirac1 : Integrable (fun (v : ℤ) => p - (if v = 2 * (d : ℤ) - 1 then (1 : ℝ) else 0))
          (Measure.dirac (2 * (d : ℤ) - 1)) :=
        integrable_dirac (by simp)
      have h_int_dirac2 : Integrable (fun (v : ℤ) => p - (if v = 2 * (d : ℤ) - 1 then (1 : ℝ) else 0))
          (Measure.dirac (2 * (d : ℤ) - 2)) :=
        integrable_dirac (by simp)
      rw [integral_add_measure
        (h_int_dirac1.smul_measure (by simp))
        (h_int_dirac2.smul_measure (by simp))]
      rw [integral_smul_measure _ (ENNReal.ofReal p)]
      rw [integral_smul_measure _ (ENNReal.ofReal (1 - p))]
      have hp_toReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
      have h1mp_toReal : (ENNReal.ofReal (1 - p)).toReal = 1 - p := ENNReal.toReal_ofReal h1mp
      simp [integral_dirac, hp_toReal, h1mp_toReal]
      ring
    -- Use integral_map to reduce to the one-dimensional integral
    set φ := fun (η : Site d → ℤ) => η z with hφ
    have h_ae : AEMeasurable φ (toyLaw d p) := hmeas_eval.aemeasurable
    rw [← integral_map h_ae hmeas_f.aestronglyMeasurable]
    -- Now the integral is ∫ v, f v ∂((toyLaw d p).map φ)
    -- But (toyLaw d p).map φ = chipLaw (2*d-1) (2*d-2) p
    have h_map_eq : (toyLaw d p).map φ = chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p := by
      dsimp [toyLaw, productLaw, φ]
      rw [@Measure.infinitePi_map_eval (Site d) (fun _ => ℤ) (fun _ => inferInstance)
        (fun _ : Site d => chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p) hμ z]
    rw [h_map_eq]
    exact h_int_chip
  have h_subgauss := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    hmeas_X.aemeasurable (ae_of_all _ h_range) h_int
  -- h_subgauss : HasSubgaussianMGF (fun η => f (η z)) ((‖p - (p-1)‖₊ / 2) ^ 2 : NNReal) (toyLaw d p)
  -- Goal : HasSubgaussianMGF (fun η => p - if η (Function.update y i j) = 2*d-1 then 1 else 0) (1/4 : NNReal) (toyLaw d p)
  dsimp [f, z] at h_subgauss ⊢
  -- Now both sides should have the same function
  -- The parameter simplifies to (2 ^ 2)⁻¹ in h_subgauss but 4⁻¹ in the goal
  simpa [show ((2 : NNReal) ^ 2)⁻¹ = (4⁻¹ : NNReal) by norm_num] using h_subgauss

/-- **(b)** (`exploding.tex:433-436`). Fix a direction `i` and an off-axis
point `y`. Parametrize the line `line d k i y` by `j ↦ Function.update y i j`,
`j ∈ Finset.Icc 1 k` (so `j` ranges over exactly the `k` values the paper's
line takes in coordinate `i`). Under the toy law, the count of sites along the
line with `η = 2d - 1` is, for `0 < ε < p`, at most `(p - ε) k` with
probability at most `exp(-2 ε² k)`.

This is `ProbabilityTheory`'s Hoeffding inequality for i.i.d. sub-Gaussian
sums (`Mathlib.Probability.Moments.SubGaussian`), applied to the family
`x ↦ p - 1{η x = 2d-1}` via `aux_ct_hoeffding_indep` (independence) and
`aux_ct_hoeffding_subgauss` (sub-Gaussianity, mean `0`, valued in
`Icc (p-1) p`), assembled with
`ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun` on
`s := Finset.Icc (1:ℤ) (k:ℤ)`, rewriting the resulting event and exponent by
direct arithmetic (`Finset.sum_sub_distrib`, `Int.card_Icc`) and converting
the `Measure.real` bound to the `ENNReal` one via `ENNReal.ofReal_toReal` /
`ENNReal.ofReal_le_ofReal` (`toyLaw d p` is a probability measure by the same
`chipLaw`/`Measure.infinitePi` unfolding already used for
`aux_prop_approximate_subadditive_eta_bounds`, so the event has finite
measure). -/
theorem aux_ct_hoeffding (d k : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (i : Fin d) (y : Site d) (ε : ℝ) (hε0 : 0 < ε) (hεp : ε < p) :
    toyLaw d p
        {η : Site d → ℤ |
          (∑ j ∈ Finset.Icc (1 : ℤ) (k : ℤ),
              if η (Function.update y i j) = 2 * (d : ℤ) - 1 then (1 : ℝ) else 0)
            ≤ (p - ε) * (k : ℝ)}
      ≤ ENNReal.ofReal (Real.exp (-2 * ε ^ 2 * (k : ℝ))) := by
  have hIPM : IsProbabilityMeasure (chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p) := by
    refine ⟨?_⟩
    unfold chipLaw
    simp only [Measure.add_apply, Measure.smul_apply, MeasureTheory.measure_univ, smul_eq_mul,
      mul_one]
    rw [← ENNReal.ofReal_add hp.le (by linarith)]
    norm_num
  haveI hIPM' : IsProbabilityMeasure (toyLaw d p) := by
    unfold toyLaw productLaw
    infer_instance
  set X : ℤ → (Site d → ℤ) → ℝ := fun j η =>
    p - (if η (Function.update y i j) = 2 * (d : ℤ) - 1 then (1 : ℝ) else 0) with hXdef
  set s : Finset ℤ := Finset.Icc (1 : ℤ) (k : ℤ) with hsdef
  have hindep := aux_ct_hoeffding_indep d p hp.le hp1.le i y
  have hsubG : ∀ j ∈ s, ProbabilityTheory.HasSubgaussianMGF (X j) (1 / 4 : NNReal) (toyLaw d p) :=
    fun j _ => aux_ct_hoeffding_subgauss d p hp hp1 i y j
  have hεk : (0 : ℝ) ≤ ε * (k : ℝ) := by positivity
  have hHoeff := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    hindep hsubG hεk
  have hsetEq : {η : Site d → ℤ | ε * (k : ℝ) ≤ ∑ j ∈ s, X j η}
      = {η : Site d → ℤ |
          (∑ j ∈ s, if η (Function.update y i j) = 2 * (d : ℤ) - 1 then (1 : ℝ) else 0)
            ≤ (p - ε) * (k : ℝ)} := by
    have hscard : (s.card : ℝ) = (k : ℝ) := by
      rw [hsdef, Int.card_Icc, show ((k : ℤ) + 1 - 1).toNat = k by omega]
    ext η
    simp only [Set.mem_setOf_eq, hXdef]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hscard]
    constructor <;> intro h <;> nlinarith [h]
  rw [hsetEq] at hHoeff
  have hcardsum : ((∑ _j ∈ s, (1 / 4 : NNReal) : NNReal) : ℝ) = (k : ℝ) / 4 := by
    rw [hsdef, Finset.sum_const, Int.card_Icc, show ((k : ℤ) + 1 - 1).toNat = k by omega]
    push_cast
    ring
  rw [hcardsum] at hHoeff
  have harith : -(ε * (k : ℝ)) ^ 2 / (2 * ((k : ℝ) / 4)) = -2 * ε ^ 2 * (k : ℝ) := by
    rcases eq_or_ne (k : ℝ) 0 with hk | hk
    · simp [hk]
    · field_simp; ring
  rw [harith] at hHoeff
  have hne : toyLaw d p {η : Site d → ℤ |
      (∑ j ∈ s, if η (Function.update y i j) = 2 * (d : ℤ) - 1 then (1 : ℝ) else 0)
        ≤ (p - ε) * (k : ℝ)} ≠ ⊤ := (measure_lt_top _ _).ne
  calc toyLaw d p {η : Site d → ℤ |
      (∑ j ∈ s, if η (Function.update y i j) = 2 * (d : ℤ) - 1 then (1 : ℝ) else 0)
        ≤ (p - ε) * (k : ℝ)}
      = ENNReal.ofReal ((toyLaw d p {η : Site d → ℤ |
          (∑ j ∈ s, if η (Function.update y i j) = 2 * (d : ℤ) - 1 then (1 : ℝ) else 0)
            ≤ (p - ε) * (k : ℝ)}).toReal) := (ENNReal.ofReal_toReal hne).symm
    _ ≤ ENNReal.ofReal (Real.exp (-2 * ε ^ 2 * (k : ℝ))) := ENNReal.ofReal_le_ofReal hHoeff

/-! ### (c) Union bound over the lines of one direction -/

/-- **(c)**. The "no catalyst on this line" event is a *subset* of (b)'s tail
event, since `0 ≤ (p-ε)k` (from `ε < p`): a line with zero `(2d-1)`-sites in
particular has a count `≤ (p-ε)k`. Union bounding (b) over every `y` in the
(finite) cube for a fixed direction `i` gives: the probability that *some*
line in direction `i` has no catalyst at all is at most
`|cube d k| · exp(-2 ε² k)`.

(Looser than the paper's `k^{d-1}`, which counts only the distinct lines
rather than every `y ∈ Q_k`; see the file header.) -/
theorem aux_ct_union_bound (d k : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (ε : ℝ) (hε0 : 0 < ε) (hεp : ε < p) (i : Fin d) (hfin : (cube d k).Finite) :
    toyLaw d p
        {η : Site d → ℤ | ¬ ∀ y ∈ cube d k, ∃ x ∈ line d k i y, η x = 2 * (d : ℤ) - 1}
      ≤ ENNReal.ofReal ((hfin.toFinset.card : ℝ) * Real.exp (-2 * ε ^ 2 * (k : ℝ))) := by
  have hpos_sub : 0 ≤ p - ε := by linarith
  have h_event_eq : {η : Site d → ℤ | ¬ ∀ y ∈ cube d k, ∃ x ∈ line d k i y, η x = 2 * (d : ℤ) - 1} =
      ⋃ y ∈ hfin.toFinset, {η : Site d → ℤ | ¬ ∃ x ∈ line d k i y, η x = 2 * (d : ℤ) - 1} := by
    ext η; simp [hfin.mem_toFinset]
  rw [h_event_eq]
  have h_subset (y : Site d) : {η : Site d → ℤ | ¬ ∃ x ∈ line d k i y, η x = 2 * (d : ℤ) - 1} ⊆
      {η : Site d → ℤ |
        (∑ j ∈ Finset.Icc (1 : ℤ) (k : ℤ),
          if η (Function.update y i j) = 2 * (d : ℤ) - 1 then (1 : ℝ) else 0)
        ≤ (p - ε) * (k : ℝ)} := by
    intro η hη
    have hη' : ∀ x ∈ line d k i y, η x ≠ 2 * (d : ℤ) - 1 := by
      intro x hx heq
      exact hη ⟨x, hx, heq⟩
    have hsum : (∑ j ∈ Finset.Icc (1 : ℤ) (k : ℤ),
        if η (Function.update y i j) = 2 * (d : ℤ) - 1 then (1 : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hmem : Function.update y i j ∈ line d k i y := by
        refine ⟨?_, ?_⟩
        · have hmemIcc := Finset.mem_Icc.mp hj
          have h1 : 1 ≤ (Function.update y i j) i := by
            simpa [Function.update_self] using hmemIcc.1
          have h2 : (Function.update y i j) i ≤ (k : ℤ) := by
            simpa [Function.update_self] using hmemIcc.2
          exact ⟨h1, h2⟩
        · intro l hl
          simp [Function.update_of_ne hl]
      have hneq := hη' (Function.update y i j) hmem
      simp [hneq]
    dsimp
    rw [hsum]
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
    nlinarith
  calc
    toyLaw d p (⋃ y ∈ hfin.toFinset, {η | ¬ ∃ x ∈ line d k i y, η x = 2 * (d : ℤ) - 1})
        ≤ ∑ y ∈ hfin.toFinset, toyLaw d p {η | ¬ ∃ x ∈ line d k i y, η x = 2 * (d : ℤ) - 1} :=
      measure_biUnion_finset_le (μ := toyLaw d p) hfin.toFinset _
    _ ≤ ∑ y ∈ hfin.toFinset, ENNReal.ofReal (Real.exp (-2 * ε ^ 2 * (k : ℝ))) := by
      refine Finset.sum_le_sum fun y hy => ?_
      refine le_trans (measure_mono (h_subset y)) (aux_ct_hoeffding d k hd p hp hp1 i y ε hε0 hεp)
    _ = (hfin.toFinset.card : ENNReal) * ENNReal.ofReal (Real.exp (-2 * ε ^ 2 * (k : ℝ))) := by
      simp [Finset.sum_const, smul_eq_mul]
    _ = ENNReal.ofReal ((hfin.toFinset.card : ℝ) * Real.exp (-2 * ε ^ 2 * (k : ℝ))) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-! ### (d) Uniformity across directions ("symmetry", no Harris/FKG needed) -/

/-- **(d)**. `aux_ct_union_bound` did not use any special property of the
direction `i`; the identical computation gives the identical bound
`|cube d k| · exp(-2 ε² k)` for every one of the `d` directions (this *is* the
paper's "by symmetry" step, realized as literal syntactic uniformity in `i`
rather than as an appeal to a measure-preserving coordinate permutation). A
further union (Boole's inequality) over the `d` directions therefore bounds
the probability that *some* direction has a catalyst-free line by `d` times
the single-direction bound; no Harris/FKG correlation inequality is invoked
anywhere in (c) or here. -/
theorem aux_ct_all_directions (d k : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (ε : ℝ) (hε0 : 0 < ε) (hεp : ε < p) (hfin : (cube d k).Finite) :
    toyLaw d p
        {η : Site d → ℤ |
          ¬ ∀ (i : Fin d) (y : Site d), y ∈ cube d k → ∃ x ∈ line d k i y,
            η x = 2 * (d : ℤ) - 1}
      ≤ ENNReal.ofReal
          ((d : ℝ) * (hfin.toFinset.card : ℝ) * Real.exp (-2 * ε ^ 2 * (k : ℝ))) := by
  set A : Fin d → Set (Site d → ℤ) := fun i =>
    {η | ¬ ∀ y ∈ cube d k, ∃ x ∈ line d k i y, η x = 2 * (d : ℤ) - 1}
  have h_target_eq : {η | ¬ ∀ (i : Fin d) (y : Site d), y ∈ cube d k → ∃ x ∈ line d k i y,
      η x = 2 * (d : ℤ) - 1} = ⋃ i, A i := by
    ext η; simp [A]
  rw [h_target_eq]
  have h_bound : ∀ i, toyLaw d p (A i) ≤
      ENNReal.ofReal ((hfin.toFinset.card : ℝ) * Real.exp (-2 * ε ^ 2 * (k : ℝ))) := by
    intro i
    exact aux_ct_union_bound d k hd p hp hp1 ε hε0 hεp i hfin
  calc
    toyLaw d p (⋃ i, A i) ≤ ∑ i : Fin d, toyLaw d p (A i) :=
      measure_iUnion_fintype_le (toyLaw d p) A
    _ ≤ ∑ i : Fin d, ENNReal.ofReal ((hfin.toFinset.card : ℝ) * Real.exp (-2 * ε ^ 2 * (k : ℝ))) :=
      Finset.sum_le_sum fun i _ => h_bound i
    _ = ENNReal.ofReal ((d : ℝ) * (hfin.toFinset.card : ℝ) * Real.exp (-2 * ε ^ 2 * (k : ℝ))) := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-! ### A technical bridge: `η` is pointwise bounded almost surely -/

/-- Needed to apply (a) (a *pointwise*, not almost-sure, hypothesis on `η`)
inside a positive-probability event of the toy law. Each one-site marginal
`chipLaw` gives probability *exactly* `1` (not merely a.e.) to `{2d-2, 2d-1}`,
being a two-point Dirac combination; a countable (the sites of `ℤ^d`)
intersection of probability-`1` events under the product law `toyLaw` still
has probability `1`. -/
theorem aux_ct_ae_bounded (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∀ᵐ η ∂(toyLaw d p), ∀ x : Site d, 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1 := by
  have hp_nonneg : 0 ≤ p := by linarith
  have hp1_nonneg : 0 ≤ 1 - p := by linarith
  set a := 2 * (d : ℤ) - 1
  set b := 2 * (d : ℤ) - 2
  have ha_ne_b : a ≠ b := by
    intro h
    have : (2 * (d : ℤ) - 1) = (2 * (d : ℤ) - 2) := h
    omega
  have h_ofReal_add : ENNReal.ofReal p + ENNReal.ofReal (1 - p) = 1 := by
    calc
      ENNReal.ofReal p + ENNReal.ofReal (1 - p) = ENNReal.ofReal (p + (1 - p)) := by
        rw [ENNReal.ofReal_add hp_nonneg hp1_nonneg]
      _ = ENNReal.ofReal 1 := by ring
      _ = 1 := ENNReal.ofReal_one
  have h_chip_ab : (chipLaw a b p) ({b, a} : Set ℤ) = 1 := by
    unfold chipLaw
    simp [ha_ne_b, h_ofReal_add]
  haveI : IsProbabilityMeasure (chipLaw a b p) := by
    refine { measure_univ := ?_ }
    unfold chipLaw
    simp [h_ofReal_add]
  have h_meas : toyLaw d p (Set.pi Set.univ (fun _ : Site d => ({b, a} : Set ℤ))) = 1 := by
    unfold toyLaw productLaw
    have h_measurable : ∀ i : Site d, MeasurableSet (({b, a} : Set ℤ) : Set ℤ) := by
      intro i
      exact (MeasurableSet.singleton a).insert b
    rw [Measure.infinitePi_pi_univ (μ := fun _ : Site d => chipLaw a b p) h_measurable]
    simp [h_chip_ab]
  have h_meas_set : MeasurableSet (Set.pi Set.univ (fun _ : Site d => ({b, a} : Set ℤ))) := by
    refine MeasurableSet.pi Set.countable_univ ?_
    intro i _
    exact (MeasurableSet.singleton a).insert b
  haveI : IsProbabilityMeasure (toyLaw d p) := by
    unfold toyLaw productLaw
    infer_instance
  have h_ae : ∀ᵐ η ∂(toyLaw d p), η ∈ Set.pi Set.univ (fun _ : Site d => ({b, a} : Set ℤ)) := by
    rw [MeasureTheory.ae_iff]
    have h_set : {η : Site d → ℤ | η ∉ Set.pi Set.univ (fun _ : Site d => ({b, a} : Set ℤ))} =
        (Set.pi Set.univ (fun _ : Site d => ({b, a} : Set ℤ)))ᶜ := by
      ext η; simp
    rw [h_set, MeasureTheory.prob_compl_eq_zero_iff h_meas_set]
    exact h_meas
  filter_upwards [h_ae] with η hη
  intro x
  have hx := hη x (Set.mem_univ x)
  -- hx : η x ∈ {b, a}
  rcases hx with (hx | hx)
  · -- η x = b
    rw [hx]
    constructor
    · rfl
    · -- b ≤ a, i.e., 2d-2 ≤ 2d-1
      omega
  · -- η x = a
    rw [hx]
    constructor
    · -- b ≤ a, i.e., 2d-2 ≤ 2d-1
      omega
    · rfl

/-! ### (a) The deterministic propagation lemma -/

/-- **New, real.** `fodo` is nondecreasing in time, for any frozen set,
background, and initial condition: on the frozen set the value never moves
(`fodo_of_mem`), and off it each step only ever adds `0` or `1`
(`fodo_succ_of_notMem`).  Induction on the time gap exactly mirrors
`Exploding.Support.Wave.wave_mono_time`. -/
theorem aux_ct_propagate_fodo_mono_time {d : ℕ} (S : Set (Site d)) (s0 w0 : Site d → ℤ)
    {s t : ℕ} (hst : s ≤ t) (x : Site d) :
    fodo S s0 w0 s x ≤ fodo S s0 w0 t x := by
  induction t, hst using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih =>
    refine le_trans ih ?_
    by_cases hx : x ∈ S
    · rw [fodo_of_mem S s0 w0 t hx, fodo_of_mem S s0 w0 (t + 1) hx]
    · rw [fodo_succ_of_notMem S s0 w0 t hx]
      split_ifs <;> linarith

def OffGood {d : ℕ} (i : Fin d) (k : ℕ) (y : Site d) : Prop :=
  (∀ l, l ≠ i → 1 ≤ y l ∧ y l ≤ (k : ℤ)) ∨
  ∃ l, l ≠ i ∧ (y l = 0 ∨ y l = (k : ℤ) + 1) ∧
    ∀ l', l' ≠ i → l' ≠ l → 1 ≤ y l' ∧ y l' ≤ (k : ℤ)

theorem aux_ct_offgood_cube {d k : ℕ} {i : Fin d} {y : Site d} (hy : y ∈ cube d k) :
    OffGood i k y :=
  Or.inl fun l _ => hy l

theorem aux_ct_offgood_ob {d k : ℕ} (hk1 : 1 ≤ k) {i : Fin d} {y : Site d}
    (hy : y ∈ outerBoundary (cube d k)) : OffGood i k y := by
  obtain ⟨hyc, y0, hy0c, hadj⟩ := hy
  rcases hadj with ⟨j, hj | hj⟩
  · by_cases hji : j = i
    · left
      intro l hl
      have hyl : y l = y0 l := by
        have := congrFun hj l
        simp only [Pi.add_apply, unit, Pi.single_eq_of_ne (fun h => hl (h.trans hji))] at this
        omega
      rw [hyl]; exact hy0c l
    · right
      refine ⟨j, hji, ?_, ?_⟩
      · have h0 := hy0c j
        have hyj : y j = y0 j - 1 := by
          have := congrFun hj j
          simp only [Pi.add_apply, unit, Pi.single_eq_same] at this
          omega
        have hnot : ¬(1 ≤ y j ∧ y j ≤ (k : ℤ)) := by
          intro hcon
          exact hyc (fun l => by
            by_cases hl : l = j
            · rw [hl]; exact hcon
            · have hyl : y l = y0 l := by
                have := congrFun hj l
                simp only [Pi.add_apply, unit, Pi.single_eq_of_ne hl] at this
                omega
              rw [hyl]; exact hy0c l)
        omega
      · intro l' hl'i hl'j
        have hyl : y l' = y0 l' := by
          have := congrFun hj l'
          simp only [Pi.add_apply, unit, Pi.single_eq_of_ne hl'j] at this
          omega
        rw [hyl]; exact hy0c l'
  · by_cases hji : j = i
    · left
      intro l hl
      have hyl : y l = y0 l := by
        have := congrFun hj l
        simp only [Pi.add_apply, unit, Pi.single_eq_of_ne (fun h => hl (h.trans hji))] at this
        omega
      rw [hyl]; exact hy0c l
    · right
      refine ⟨j, hji, ?_, ?_⟩
      · have h0 := hy0c j
        have hyj : y j = y0 j + 1 := by
          have := congrFun hj j
          simp only [Pi.add_apply, unit, Pi.single_eq_same] at this
          omega
        have hnot : ¬(1 ≤ y j ∧ y j ≤ (k : ℤ)) := by
          intro hcon
          exact hyc (fun l => by
            by_cases hl : l = j
            · rw [hl]; exact hcon
            · have hyl : y l = y0 l := by
                have := congrFun hj l
                simp only [Pi.add_apply, unit, Pi.single_eq_of_ne hl] at this
                omega
              rw [hyl]; exact hy0c l)
        omega
      · intro l' hl'i hl'j
        have hyl : y l' = y0 l' := by
          have := congrFun hj l'
          simp only [Pi.add_apply, unit, Pi.single_eq_of_ne hl'j] at this
          omega
        rw [hyl]; exact hy0c l'

theorem aux_ct_offgood_closureN {d k : ℕ} (hk1 : 1 ≤ k) {i : Fin d} {y : Site d}
    (hy : y ∈ closureN (cube d k)) : OffGood i k y := by
  rcases hy with hyc | hyb
  · exact aux_ct_offgood_cube hyc
  · exact aux_ct_offgood_ob hk1 hyb


theorem aux_ct_off_step4 {d k : ℕ} (i : Fin d) (x y : Site d)
    (hx : x ∈ cube d k) (hy : OffGood i k y) (n : ℕ)
    (hn : (∑ l ∈ Finset.univ.erase i, (y l - x l).natAbs) = n + 1) :
    ∃ y' : Site d, y' i = y i ∧ (lattice d).Adj y y' ∧ OffGood i k y' ∧
      (∑ l ∈ Finset.univ.erase i, (y' l - x l).natAbs) = n := by
  classical
  have hk1 : 1 ≤ k := by have := hx i; omega
  have hpos : 0 < ∑ l ∈ Finset.univ.erase i, (y l - x l).natAbs := by omega
  have hex : ∃ l ∈ Finset.univ.erase i, (y l - x l).natAbs ≠ 0 := by
    by_contra hc
    push Not at hc
    have hz : (∑ l ∈ Finset.univ.erase i, (y l - x l).natAbs) = 0 :=
      Finset.sum_eq_zero fun l hl => hc l hl
    omega
  obtain ⟨l, hlmem, hlne⟩ := hex
  have hli : l ≠ i := (Finset.mem_erase.mp hlmem).1
  have hyl : y l ≠ x l := by
    intro h; rw [h, sub_self, Int.natAbs_zero] at hlne; exact hlne rfl
  set s : ℤ := if y l < x l then 1 else -1 with hs
  have hsval : s = 1 ∨ s = -1 := by rw [hs]; split_ifs <;> simp
  have hdir : s = 1 → y l < x l := by
    intro h
    by_contra hc
    rw [hs, if_neg hc] at h; omega
  have hdir' : s = -1 → x l < y l := by
    intro h
    by_cases hc : y l < x l
    · rw [hs, if_pos hc] at h; omega
    · omega
  have hxl := hx l
  have hylrange : (1 ≤ y l ∧ y l ≤ (k : ℤ)) ∨ y l = 0 ∨ y l = (k : ℤ) + 1 := by
    rcases hy with hgood | ⟨j, hji, hjbad, hjrest⟩
    · exact Or.inl (hgood l hli)
    · by_cases hjl : j = l
      · subst hjl; exact Or.inr hjbad
      · exact Or.inl (hjrest l hli (fun h => hjl h.symm))
  refine ⟨Function.update y l (y l + s), ?_, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne (Ne.symm hli)]
  · rcases hsval with h | h
    · refine ⟨l, Or.inl ?_⟩
      funext j
      by_cases hj : j = l
      · subst hj
        simp only [Pi.add_apply, Function.update_self, unit, Pi.single_eq_same, h]
      · rw [Pi.add_apply, Function.update_of_ne hj, unit, Pi.single_eq_of_ne hj, add_zero]
    · refine ⟨l, Or.inr ?_⟩
      funext j
      by_cases hj : j = l
      · subst hj
        simp only [Pi.add_apply, Function.update_self, unit, Pi.single_eq_same, h]
        ring
      · rw [Pi.add_apply, Function.update_of_ne hj, unit, Pi.single_eq_of_ne hj, add_zero]
  · rcases hy with hgood | ⟨j, hji, hjbad, hjrest⟩
    · left
      intro l' hl'i
      by_cases hl'l : l' = l
      · rw [hl'l, Function.update_self]
        have hxl := hx l
        rcases hsval with h | h
        · rw [h]; have hlt := hdir h; have := hgood l hli; omega
        · rw [h]; have hlt := hdir' h; have := hgood l hli; omega
      · rw [Function.update_of_ne hl'l]; exact hgood l' hl'i
    · by_cases hjl : j = l
      · rw [hjl] at hjbad
        left
        intro l' hl'i
        by_cases hl'l : l' = l
        · rw [hl'l, Function.update_self]
          rcases hsval with h | h
          · rw [h]
            rcases hjbad with h0 | hk
            · omega
            · omega
          · rw [h]
            rcases hjbad with h0 | hk
            · omega
            · omega
        · rw [Function.update_of_ne hl'l]
          exact hjrest l' hl'i (fun h => hl'l (h.trans hjl))
      · right
        refine ⟨j, hji, ?_, ?_⟩
        · rw [Function.update_of_ne (fun h => hjl h)]
          exact hjbad
        · intro l' hl'i hl'j
          by_cases hl'l : l' = l
          · rw [hl'l, Function.update_self]
            rcases hsval with h | h
            · rw [h]; have hlt := hdir h; have := hjrest l hli (fun hh => hjl hh.symm); omega
            · rw [h]; have hlt := hdir' h; have := hjrest l hli (fun hh => hjl hh.symm); omega
          · rw [Function.update_of_ne hl'l]
            exact hjrest l' hl'i (fun h => hl'j h)
  · have hsingle : (Function.update y l (y l + s) l - x l).natAbs = (y l - x l).natAbs - 1 := by
      rw [Function.update_self]
      rcases hsval with h | h <;> rw [h]
      · have : (y l + 1 - x l).natAbs = (y l - x l).natAbs - 1 := by omega
        exact this
      · have : (y l + -1 - x l).natAbs = (y l - x l).natAbs - 1 := by omega
        exact this
    have hother : (∑ l' ∈ (Finset.univ.erase i).erase l,
          (Function.update y l (y l + s) l' - x l').natAbs)
        = (∑ l' ∈ (Finset.univ.erase i).erase l, (y l' - x l').natAbs) := by
      refine Finset.sum_congr rfl fun l' hl' => ?_
      have hl'l : l' ≠ l := (Finset.mem_erase.mp hl').1
      rw [Function.update_of_ne hl'l]
    have h1 := Finset.sum_erase_add (Finset.univ.erase i)
      (fun l' => (Function.update y l (y l + s) l' - x l').natAbs) hlmem
    have h2 := Finset.sum_erase_add (Finset.univ.erase i)
      (fun l' => (y l' - x l').natAbs) hlmem
    rw [hsingle, hother] at h1
    omega

-- GAP-closing piece for the domino mechanism (`exploding.tex:446-447`), the
-- crux of the whole propagation lemma.
/-- **New, sorry** (real content, not a literature gap: this is the paper's
own one-paragraph mechanism, made precise).  If the off-axis-adjacent line
through `Yref` (agreeing with `Y` on axis `i`, `(lattice d).Adj Y Yref`) is
already entirely toppled by time `T`, and `Y`'s own off-axis coordinates are a
genuine row of the cube (`hYoff`, so every point of `line d k i Y` lies in
`cube d k`) carrying a `(2d-1)`-chip catalyst (`hcat`), then the whole line
through `Y` topples `k` steps later.  Mechanism: writing `x_t` for the point
of `line d k i Y` with axis-`i` coordinate `t`, every `x_t` has a *permanent*
neighbour on `Yref`'s line at the same axis-`i` value (since `Y, Yref` agree
off exactly one coordinate, pointwise for every `t`), which is `1` from time
`T` on by hypothesis and stays `≥ 1` after (`aux_ct_propagate_fodo_mono_time`).
The catalyst itself thus has `nbrSumZ ≥ 1` from `T` on, enough since its own
`η = 2d - 1` (`fodo_topple_of_ge`), so it topples at `T + 1`.  Each subsequent
point of the line topples one step after its already-toppled along-line
neighbour, since it too carries the same permanent `+1`, giving `nbrSumZ ≥ 2`,
enough for either baseline `2d - 2` or `2d - 1` (`fodo_topple_of_ge` again).
A double induction on the distance along the line from the catalyst (outward
in each of the two directions), capped by `k` since the line has at most `k`
points, closes the bound; recommended further split along exactly those two
inductions if a future pass needs pieces smaller than this one. -/
theorem aux_ct_bad_peel {d k : ℕ} (i : Fin d) (x y : Site d) (l0 : Fin d)
    (hx : x ∈ cube d k) (hl0i : l0 ≠ i)
    (hbad : y l0 = 0 ∨ y l0 = (k : ℤ) + 1)
    (hrest : ∀ l, l ≠ i → l ≠ l0 → 1 ≤ y l ∧ y l ≤ (k : ℤ))
    (n : ℕ) (hn : (∑ l ∈ Finset.univ.erase i, (y l - x l).natAbs) = n + 1) :
    ∃ y' : Site d, y' i = y i ∧ (lattice d).Adj y y' ∧
      (∀ l, l ≠ i → 1 ≤ y' l ∧ y' l ≤ (k : ℤ)) ∧
      (∑ l ∈ Finset.univ.erase i, (y' l - x l).natAbs) = n := by
  classical
  have hk1 : 1 ≤ k := by have := hx i; omega
  have hxl0 := hx l0
  set s : ℤ := if y l0 < x l0 then 1 else -1 with hs
  have hsval : s = 1 ∨ s = -1 := by rw [hs]; split_ifs <;> simp
  have hdir : s = 1 → y l0 < x l0 := by
    intro h; by_contra hc; rw [hs, if_neg hc] at h; omega
  have hdir' : s = -1 → x l0 < y l0 := by
    intro h; by_cases hc : y l0 < x l0
    · rw [hs, if_pos hc] at h; omega
    · omega
  refine ⟨Function.update y l0 (y l0 + s), ?_, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne (Ne.symm hl0i)]
  · rcases hsval with h | h
    · refine ⟨l0, Or.inl ?_⟩
      funext j
      by_cases hj : j = l0
      · subst hj
        simp only [Pi.add_apply, Function.update_self, unit, Pi.single_eq_same, h]
      · rw [Pi.add_apply, Function.update_of_ne hj, unit, Pi.single_eq_of_ne hj, add_zero]
    · refine ⟨l0, Or.inr ?_⟩
      funext j
      by_cases hj : j = l0
      · subst hj
        simp only [Pi.add_apply, Function.update_self, unit, Pi.single_eq_same, h]
        ring
      · rw [Pi.add_apply, Function.update_of_ne hj, unit, Pi.single_eq_of_ne hj, add_zero]
  · intro l hl
    by_cases hl0 : l = l0
    · rw [hl0, Function.update_self]
      rcases hsval with h | h
      · rw [h]; have hlt := hdir h; rcases hbad with h0 | hk <;> omega
      · rw [h]; have hlt := hdir' h; rcases hbad with h0 | hk <;> omega
    · rw [Function.update_of_ne hl0]
      exact hrest l hl hl0
  · have hsingle : (Function.update y l0 (y l0 + s) l0 - x l0).natAbs
        = (y l0 - x l0).natAbs - 1 := by
      rw [Function.update_self]
      rcases hsval with h | h <;> rw [h]
      · have : (y l0 + 1 - x l0).natAbs = (y l0 - x l0).natAbs - 1 := by omega
        exact this
      · have : (y l0 + -1 - x l0).natAbs = (y l0 - x l0).natAbs - 1 := by omega
        exact this
    have hother : (∑ l' ∈ (Finset.univ.erase i).erase l0,
          (Function.update y l0 (y l0 + s) l' - x l').natAbs)
        = (∑ l' ∈ (Finset.univ.erase i).erase l0, (y l' - x l').natAbs) := by
      refine Finset.sum_congr rfl fun l' hl' => ?_
      have hl'l : l' ≠ l0 := (Finset.mem_erase.mp hl').1
      rw [Function.update_of_ne hl'l]
    have hmem : l0 ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hl0i, Finset.mem_univ l0⟩
    have h1 := Finset.sum_erase_add (Finset.univ.erase i)
      (fun l' => (Function.update y l0 (y l0 + s) l' - x l').natAbs) hmem
    have h2 := Finset.sum_erase_add (Finset.univ.erase i)
      (fun l' => (y l' - x l').natAbs) hmem
    rw [hsingle, hother] at h1
    omega

theorem aux_ct_off_step5 {d k : ℕ} (i : Fin d) (x y : Site d)
    (hx : x ∈ cube d k) (hy : OffGood i k y) (n : ℕ)
    (hn : (∑ l ∈ Finset.univ.erase i, (y l - x l).natAbs) = n + 1) :
    ∃ y' : Site d, y' i = y i ∧ (lattice d).Adj y y' ∧
      (∀ l, l ≠ i → 1 ≤ y' l ∧ y' l ≤ (k : ℤ)) ∧
      (∑ l ∈ Finset.univ.erase i, (y' l - x l).natAbs) = n := by
  rcases hy with hgood | ⟨l0, hl0i, hl0bad, hl0rest⟩
  · -- good: peel any coordinate with nonzero distance
    classical
    have hpos : 0 < ∑ l ∈ Finset.univ.erase i, (y l - x l).natAbs := by omega
    have hex : ∃ l ∈ Finset.univ.erase i, (y l - x l).natAbs ≠ 0 := by
      by_contra hc
      push Not at hc
      have hz : (∑ l ∈ Finset.univ.erase i, (y l - x l).natAbs) = 0 :=
        Finset.sum_eq_zero fun l hl => hc l hl
      omega
    obtain ⟨l, hlmem, hlne⟩ := hex
    have hli : l ≠ i := (Finset.mem_erase.mp hlmem).1
    have hyl : y l ≠ x l := by
      intro h; rw [h, sub_self, Int.natAbs_zero] at hlne; exact hlne rfl
    set s : ℤ := if y l < x l then 1 else -1 with hs
    have hsval : s = 1 ∨ s = -1 := by rw [hs]; split_ifs <;> simp
    have hdir : s = 1 → y l < x l := by
      intro h; by_contra hc; rw [hs, if_neg hc] at h; omega
    have hdir' : s = -1 → x l < y l := by
      intro h; by_cases hc : y l < x l
      · rw [hs, if_pos hc] at h; omega
      · omega
    refine ⟨Function.update y l (y l + s), ?_, ?_, ?_, ?_⟩
    · rw [Function.update_of_ne (Ne.symm hli)]
    · rcases hsval with h | h
      · refine ⟨l, Or.inl ?_⟩
        funext j
        by_cases hj : j = l
        · subst hj
          simp only [Pi.add_apply, Function.update_self, unit, Pi.single_eq_same, h]
        · rw [Pi.add_apply, Function.update_of_ne hj, unit, Pi.single_eq_of_ne hj, add_zero]
      · refine ⟨l, Or.inr ?_⟩
        funext j
        by_cases hj : j = l
        · subst hj
          simp only [Pi.add_apply, Function.update_self, unit, Pi.single_eq_same, h]
          ring
        · rw [Pi.add_apply, Function.update_of_ne hj, unit, Pi.single_eq_of_ne hj, add_zero]
    · intro l' hl'i
      by_cases hl'l : l' = l
      · rw [hl'l, Function.update_self]
        have hxl := hx l
        rcases hsval with h | h
        · rw [h]; have hlt := hdir h; have := hgood l hli; omega
        · rw [h]; have hlt := hdir' h; have := hgood l hli; omega
      · rw [Function.update_of_ne hl'l]; exact hgood l' hl'i
    · have hsingle : (Function.update y l (y l + s) l - x l).natAbs = (y l - x l).natAbs - 1 := by
        rw [Function.update_self]
        rcases hsval with h | h <;> rw [h]
        · have : (y l + 1 - x l).natAbs = (y l - x l).natAbs - 1 := by omega
          exact this
        · have : (y l + -1 - x l).natAbs = (y l - x l).natAbs - 1 := by omega
          exact this
      have hother : (∑ l' ∈ (Finset.univ.erase i).erase l,
            (Function.update y l (y l + s) l' - x l').natAbs)
          = (∑ l' ∈ (Finset.univ.erase i).erase l, (y l' - x l').natAbs) := by
        refine Finset.sum_congr rfl fun l' hl' => ?_
        have hl'l : l' ≠ l := (Finset.mem_erase.mp hl').1
        rw [Function.update_of_ne hl'l]
      have h1 := Finset.sum_erase_add (Finset.univ.erase i)
        (fun l' => (Function.update y l (y l + s) l' - x l').natAbs) hlmem
      have h2 := Finset.sum_erase_add (Finset.univ.erase i)
        (fun l' => (y l' - x l').natAbs) hlmem
      rw [hsingle, hother] at h1
      omega
  · exact aux_ct_bad_peel i x y l0 hx hl0i hl0bad hl0rest n hn

theorem aux_ct_propagate_line_fill (d k : ℕ) (hd : 2 ≤ d) (η : Site d → ℤ)
    (hbdd : ∀ x, 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1)
    (i : Fin d) (z Y Yref : Site d)
    (hcat : ∃ x ∈ line d k i Y, η x = 2 * (d : ℤ) - 1)
    (hYoff : ∀ l, l ≠ i → 1 ≤ Y l ∧ Y l ≤ (k : ℤ))
    (hadj : (lattice d).Adj Y Yref) (hieq : Y i = Yref i)
    (T : ℕ) (hT : ∀ w ∈ line d k i Yref, crossOdo η k i z T w = 1) :
    ∀ w ∈ line d k i Y, crossOdo η k i z (T + k) w = 1 := by
  classical
  set S : Set (Site d) := (cube d k)ᶜ ∪ line d k i z with hS
  set w0 : Site d → ℤ := fun x => if x ∈ line d k i z then 1 else 0 with hw0
  have hw0le : ∀ y, w0 y ≤ 1 := fun y => by simp only [hw0]; split_ifs <;> omega
  have hw0nn : ∀ y, 0 ≤ w0 y := fun y => by simp only [hw0]; split_ifs <;> omega
  have hle1 : ∀ t x, crossOdo η k i z t x ≤ 1 := fun t x =>
    fodo_le_one S η w0 (fun y => (hbdd y).2) hw0le hw0nn t x
  have hnn : ∀ t x, 0 ≤ crossOdo η k i z t x := fun t x =>
    fodo_nonneg S η w0 hw0nn t x
  have hmono : ∀ {s t : ℕ}, s ≤ t → ∀ x, crossOdo η k i z s x ≤ crossOdo η k i z t x :=
    fun hst x => aux_ct_propagate_fodo_mono_time S η w0 hst x
  obtain ⟨l0, hl0i, hl0step, hl0eq⟩ : ∃ l0 : Fin d, l0 ≠ i ∧
      (Yref l0 = Y l0 + 1 ∨ Yref l0 = Y l0 - 1) ∧
      ∀ m, m ≠ l0 → Yref m = Y m := by
    rcases hadj with ⟨j, hj | hj⟩
    · refine ⟨j, ?_, ?_, ?_⟩
      · intro hji
        rw [hji] at hj
        have := congrFun hj i
        simp only [Pi.add_apply, unit, Pi.single_eq_same] at this
        omega
      · left
        have := congrFun hj j
        simp only [Pi.add_apply, unit, Pi.single_eq_same] at this
        omega
      · intro m hm
        have := congrFun hj m
        simp only [Pi.add_apply, unit, Pi.single_eq_of_ne hm] at this
        omega
    · refine ⟨j, ?_, ?_, ?_⟩
      · intro hji
        rw [hji] at hj
        have := congrFun hj i
        simp only [Pi.add_apply, unit, Pi.single_eq_same] at this
        omega
      · right
        have := congrFun hj j
        simp only [Pi.add_apply, unit, Pi.single_eq_same] at this
        omega
      · intro m hm
        have := congrFun hj m
        simp only [Pi.add_apply, unit, Pi.single_eq_of_ne hm] at this
        omega
  have hperm : ∀ w ∈ line d k i Y, ∃ w' ∈ line d k i Yref, (lattice d).Adj w w' := by
    intro w hw
    refine ⟨Function.update w l0 (Yref l0), ?_, ?_⟩
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [Function.update_of_ne (Ne.symm hl0i)]; exact hw.1.1
      · rw [Function.update_of_ne (Ne.symm hl0i)]; exact hw.1.2
      · intro m hm
        by_cases hml : m = l0
        · rw [hml, Function.update_self]
        · rw [Function.update_of_ne hml, hw.2 m hm, hl0eq m hml]
    · rcases hl0step with h | h
      · refine ⟨l0, Or.inl ?_⟩
        funext m
        by_cases hml : m = l0
        · rw [hml]
          simp only [Function.update_self, Pi.add_apply, unit, Pi.single_eq_same]
          rw [hw.2 l0 hl0i]; omega
        · rw [Pi.add_apply, Function.update_of_ne hml, unit, Pi.single_eq_of_ne hml, add_zero]
      · refine ⟨l0, Or.inr ?_⟩
        funext m
        by_cases hml : m = l0
        · rw [hml]
          simp only [Function.update_self, Pi.add_apply, unit, Pi.single_eq_same]
          rw [hw.2 l0 hl0i]; omega
        · rw [Pi.add_apply, Function.update_of_ne hml, unit, Pi.single_eq_of_ne hml, add_zero]
  have hplus : ∀ t, T ≤ t → ∀ w ∈ line d k i Y, 1 ≤ nbrSumZ (crossOdo η k i z t) w := by
    intro t ht w hw
    obtain ⟨w', hw', hadj'⟩ := hperm w hw
    have h1 : crossOdo η k i z t w' = 1 := by
      have hge : 1 ≤ crossOdo η k i z t w' := by
        rw [← hT w' hw']; exact hmono ht w'
      exact le_antisymm (hle1 t w') hge
    have h2 : crossOdo η k i z t w' ≤ nbrSumZ (crossOdo η k i z t) w := by
      have hsum : nbrSumZ (crossOdo η k i z t) w
          = ∑ j : Fin d, (crossOdo η k i z t (w + unit j) + crossOdo η k i z t (w - unit j)) := rfl
      rw [hsum]
      obtain ⟨j, hj⟩ := hadj'
      have hnn' : ∀ y, 0 ≤ crossOdo η k i z t y := fun y => hnn t y
      have hterm : crossOdo η k i z t w' ≤
          crossOdo η k i z t (w + unit j) + crossOdo η k i z t (w - unit j) := by
        rcases hj with hj | hj
        · rw [hj]
          have h3 : 0 ≤ crossOdo η k i z t (w - unit j) := hnn' _
          omega
        · have h6 : w' = w - unit j := by rw [hj]; abel
          rw [h6]
          have h3 : 0 ≤ crossOdo η k i z t (w + unit j) := hnn' _
          omega
      exact le_trans hterm (Finset.single_le_sum
        (f := fun j : Fin d => crossOdo η k i z t (w + unit j) + crossOdo η k i z t (w - unit j))
        (fun b _ => by
          have h4 := hnn' (w + unit b)
          have h5 := hnn' (w - unit b)
          omega)
        (Finset.mem_univ j))
    omega
  obtain ⟨x0, hx0line, hx0cat⟩ := hcat
  have hx0cube : x0 ∈ cube d k := by
    intro m
    by_cases hm : m = i
    · rw [hm]; exact hx0line.1
    · rw [hx0line.2 m hm]; exact hYoff m hm
  -- the catalyst fires at T+1
  have hx0fire : crossOdo η k i z (T + 1) x0 = 1 := by
    by_cases hz0 : x0 ∈ line d k i z
    · rw [crossOdo, fodo_of_mem S η w0 (T + 1) (Or.inr hz0)]
      simp only [hw0, if_pos hz0]
    · have hx0notS : x0 ∉ S := by
        intro hmem
        rcases hmem with hmem | hmem
        · exact hmem hx0cube
        · exact hz0 hmem
      rcases eq_or_ne (crossOdo η k i z T x0) 0 with hzero | hne
      · have hconf : 2 * (d : ℤ) ≤ fconf S η w0 T x0 := by
          have h1 := hplus T le_rfl x0 hx0line
          have h2 : η x0 = 2 * (d : ℤ) - 1 := hx0cat
          have h3 : fodo S η w0 T x0 = 0 := hzero
          have h1' : 1 ≤ nbrSumZ (fodo S η w0 T) x0 := h1
          simp only [fconf, lap] at h1' ⊢
          rw [h2, h3]
          simp only [mul_zero, sub_zero]
          omega
        have := fodo_topple_of_ge S η w0 T hx0notS hzero hconf
        rw [crossOdo]
        exact this
      · have hpos : 1 ≤ crossOdo η k i z T x0 := by have := hnn T x0; omega
        have hone : crossOdo η k i z T x0 = 1 := le_antisymm (hle1 T x0) hpos
        have hge : 1 ≤ crossOdo η k i z (T + 1) x0 := by
          rw [← hone]; exact hmono (Nat.le_succ T) x0
        exact le_antisymm (hle1 (T + 1) x0) hge
  -- the along-line spread
  have hspread : ∀ (s : ℕ), s ≤ k → ∀ w ∈ line d k i Y,
      (w i - x0 i).natAbs = (s : ℤ) →
      crossOdo η k i z (T + 1 + s) w = 1 := by
    intro s
    induction s with
    | zero =>
      intro _ w hw hwi
      have hweq : w = x0 := by
        funext m
        by_cases hm : m = i
        · rw [hm]
          have h0 : (w i - x0 i).natAbs = 0 := by omega
          omega
        · rw [hw.2 m hm, hx0line.2 m hm]
      rw [hweq]
      simpa using hx0fire
    | succ s ih =>
      intro hsk w hw hwi
      have hsk' : s ≤ k := by omega
      by_cases hdone : crossOdo η k i z (T + 1 + s) w = 1
      · have heq : T + 1 + (s + 1) = (T + 1 + s) + 1 := by ring
        rw [heq]
        refine le_antisymm (hle1 _ w) ?_
        have hmono' := hmono (Nat.le_succ (T + 1 + s)) w
        rw [hdone] at hmono'
        exact hmono'
      · have hw0t : crossOdo η k i z (T + 1 + s) w = 0 := by
          have hnn' := hnn (T + 1 + s) w
          have hle' := hle1 (T + 1 + s) w
          omega
        have hwi1 : 1 ≤ w i := hw.1.1
        have hwik : w i ≤ (k : ℤ) := hw.1.2
        have hne : w i ≠ x0 i := by
          intro heq
          have : (w i - x0 i).natAbs = 0 := by omega
          omega
        -- the neighbour towards the catalyst
        set v : Site d := if w i < x0 i then w + unit i else w - unit i with hv
        have hvi : v i = if w i < x0 i then w i + 1 else w i - 1 := by
          rw [hv]; split_ifs <;> simp [Pi.add_apply, Pi.sub_apply, unit, Pi.single_eq_same]
        have hx0i1 : 1 ≤ x0 i := hx0line.1.1
        have hx0ik : x0 i ≤ (k : ℤ) := hx0line.1.2
        have hvline : v ∈ line d k i Y := by
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · rw [hvi]
            by_cases hlt : w i < x0 i
            · simp only [if_pos hlt]; omega
            · simp only [if_neg hlt]; omega
          · rw [hvi]
            by_cases hlt : w i < x0 i
            · simp only [if_pos hlt]; omega
            · simp only [if_neg hlt]; omega
          · intro m hm
            rw [hv]
            by_cases hlt : w i < x0 i
            · simp only [if_pos hlt, Pi.add_apply, unit, Pi.single_eq_of_ne hm, add_zero]
              exact hw.2 m hm
            · simp only [if_neg hlt, Pi.sub_apply, unit, Pi.single_eq_of_ne hm, sub_zero]
              exact hw.2 m hm
        have hnat : ((w i - x0 i).natAbs : ℤ) = (s : ℤ) + 1 := hwi
        have hvdist : (v i - x0 i).natAbs = (s : ℤ) := by
          rw [hvi]
          split_ifs with hlt
          · have h1 : (w i - x0 i).natAbs = x0 i - w i := by omega
            have h2 : (w i + 1 - x0 i).natAbs = x0 i - (w i + 1) := by omega
            omega
          · have h1 : (w i - x0 i).natAbs = w i - x0 i := by omega
            have h2 : (w i - 1 - x0 i).natAbs = (w i - 1) - x0 i := by omega
            omega
        have hv1 : crossOdo η k i z (T + 1 + s) v = 1 := ih hsk' v hvline hvdist
        have hadjv : (lattice d).Adj w v := by
          rw [hv]
          split_ifs with hlt
          · exact ⟨i, Or.inl (by simp [Pi.add_apply, unit, Pi.single_eq_same])⟩
          · exact ⟨i, Or.inr (by simp [Pi.sub_apply, unit, Pi.single_eq_same])⟩
        have hwcube : w ∈ cube d k := by
          intro m
          by_cases hm : m = i
          · rw [hm]; exact hw.1
          · rw [hw.2 m hm]; exact hYoff m hm
        have hnotS : w ∉ S := by
          intro hmem
          rcases hmem with hmem | hmem
          · exact hmem hwcube
          · have h1 : crossOdo η k i z (T + 1 + s) w = 1 := by
              show fodo S η w0 (T + 1 + s) w = 1
              rw [fodo_of_mem S η w0 (T + 1 + s) (Or.inr hmem)]
              simp only [hw0, if_pos hmem]
            omega
        have hconf : 2 * (d : ℤ) ≤ fconf S η w0 (T + 1 + s) w := by
          have h2 : 2 * (d : ℤ) - 2 ≤ η w := (hbdd w).1
          have hsingle : fodo S η w0 (T + 1 + s) (w + unit l0)
              + fodo S η w0 (T + 1 + s) (w - unit l0)
              + fodo S η w0 (T + 1 + s) (w + unit i)
              + fodo S η w0 (T + 1 + s) (w - unit i)
              ≤ nbrSumZ (fodo S η w0 (T + 1 + s)) w := by
            have hsub : ({l0, i} : Finset (Fin d)) ⊆ Finset.univ := Finset.subset_univ _
            have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
              (f := fun j : Fin d => fodo S η w0 (T + 1 + s) (w + unit j)
                + fodo S η w0 (T + 1 + s) (w - unit j))
              (fun b _ _ => by
                have h7 : 0 ≤ fodo S η w0 (T + 1 + s) (w + unit b) := hnn (T + 1 + s) (w + unit b)
                have h8 : 0 ≤ fodo S η w0 (T + 1 + s) (w - unit b) := hnn (T + 1 + s) (w - unit b)
                omega)
            have hpair : (∑ j ∈ ({l0, i} : Finset (Fin d)),
                (fodo S η w0 (T + 1 + s) (w + unit j)
                  + fodo S η w0 (T + 1 + s) (w - unit j)))
                = fodo S η w0 (T + 1 + s) (w + unit l0)
                  + fodo S η w0 (T + 1 + s) (w - unit l0)
                  + fodo S η w0 (T + 1 + s) (w + unit i)
                  + fodo S η w0 (T + 1 + s) (w - unit i) := by
              rw [Finset.sum_insert (by simp [hl0i]), Finset.sum_singleton]
              ring
            rw [hpair] at hsum
            simpa only [nbrSumZ] using hsum
          have hvterm : fodo S η w0 (T + 1 + s) v
              = fodo S η w0 (T + 1 + s) (w + unit i)
                ∨ fodo S η w0 (T + 1 + s) v
                  = fodo S η w0 (T + 1 + s) (w - unit i) := by
            rw [hv]
            split_ifs with hlt
            · left; rfl
            · right; rfl
          have hv1' : fodo S η w0 (T + 1 + s) v = 1 := hv1
          -- the permanent neighbour on the neighbouring line has value 1
          have hperm1 : fodo S η w0 (T + 1 + s) (w + unit l0) = 1
              ∨ fodo S η w0 (T + 1 + s) (w - unit l0) = 1 := by
            have hwl0 : w l0 = Y l0 := hw.2 l0 hl0i
            have h1 : crossOdo η k i z (T + 1 + s) (Function.update w l0 (Yref l0)) = 1 := by
              have hge : 1 ≤ crossOdo η k i z (T + 1 + s) (Function.update w l0 (Yref l0)) := by
                have hmem : Function.update w l0 (Yref l0) ∈ line d k i Yref := by
                  refine ⟨⟨?_, ?_⟩, ?_⟩
                  · rw [Function.update_of_ne (Ne.symm hl0i)]; exact hw.1.1
                  · rw [Function.update_of_ne (Ne.symm hl0i)]; exact hw.1.2
                  · intro m hm
                    by_cases hml : m = l0
                    · rw [hml, Function.update_self]
                    · rw [Function.update_of_ne hml, hw.2 m hm, hl0eq m hml]
                rw [← hT _ hmem]
                exact hmono (by omega) _
              exact le_antisymm (hle1 (T + 1 + s) _) hge
            rcases hl0step with hstep | hstep
            · left
              have heq : Function.update w l0 (Yref l0) = w + unit l0 := by
                funext m
                by_cases hml : m = l0
                · rw [hml]
                  simp only [Function.update_self, Pi.add_apply, unit, Pi.single_eq_same]
                  omega
                · rw [Pi.add_apply, Function.update_of_ne hml, unit, Pi.single_eq_of_ne hml, add_zero]
              rw [heq] at h1
              exact h1
            · right
              have heq : Function.update w l0 (Yref l0) = w - unit l0 := by
                funext m
                by_cases hml : m = l0
                · rw [hml]
                  simp only [Function.update_self, Pi.sub_apply, unit, Pi.single_eq_same]
                  omega
                · rw [Pi.sub_apply, Function.update_of_ne hml, unit, Pi.single_eq_of_ne hml, sub_zero]
              rw [heq] at h1
              exact h1
          simp only [fconf, lap]
          have hw0t' : fodo S η w0 (T + 1 + s) w = 0 := hw0t
          rw [hw0t']
          simp only [mul_zero, sub_zero]
          have h2d : 2 * (d : ℤ) - 2 ≤ η w := (hbdd w).1
          have hnnl : 0 ≤ fodo S η w0 (T + 1 + s) (w + unit l0) := hnn (T + 1 + s) (w + unit l0)
          have hnnl' : 0 ≤ fodo S η w0 (T + 1 + s) (w - unit l0) := hnn (T + 1 + s) (w - unit l0)
          have hnni : 0 ≤ fodo S η w0 (T + 1 + s) (w + unit i) := hnn (T + 1 + s) (w + unit i)
          have hnni' : 0 ≤ fodo S η w0 (T + 1 + s) (w - unit i) := hnn (T + 1 + s) (w - unit i)
          rcases hvterm with hvterm | hvterm
          · rw [hvterm] at hv1'
            rcases hperm1 with hp | hp
            · rw [hp, hv1'] at hsingle
              omega
            · rw [hp, hv1'] at hsingle
              omega
          · rw [hvterm] at hv1'
            rcases hperm1 with hp | hp
            · rw [hp, hv1'] at hsingle
              omega
            · rw [hp, hv1'] at hsingle
              omega
        have hfire := fodo_topple_of_ge S η w0 (T + 1 + s) hnotS hw0t hconf
        have heq : T + 1 + (s + 1) = (T + 1 + s) + 1 := by ring
        rw [heq]
        exact hfire
  intro w hw
  have hwi : w i = x0 i + ((w i - x0 i).natAbs : ℤ) ∨ w i = x0 i - ((w i - x0 i).natAbs : ℤ) := by
    rcases lt_or_ge (w i) (x0 i) with h | h
    · right
      have h1 : ((w i - x0 i).natAbs : ℤ) = x0 i - w i := by omega
      omega
    · left
      have h1 : ((w i - x0 i).natAbs : ℤ) = w i - x0 i := by omega
      omega
  have hk : (w i - x0 i).natAbs ≤ k := by
    have h1 := hw.1.1
    have h2 := hw.1.2
    have h3 := hx0line.1.1
    have h4 := hx0line.1.2
    omega
  have hk1 : (w i - x0 i).natAbs + 1 ≤ k := by
    have h1 := hw.1.1
    have h2 := hw.1.2
    have h3 := hx0line.1.1
    have h4 := hx0line.1.2
    omega
  have h1 := hspread ((w i - x0 i).natAbs) hk w hw (by rfl)
  refine le_antisymm (hle1 _ w) ?_
  rw [← h1]
  exact hmono (by omega) w


-- GAP-closing piece: the paper's own chain-length count
-- (`exploding.tex:447-449`, "every line in `Q_k` is joined to `L_k^{(1,z)}`
-- by a chain of at most `(d-1)(k-1)+1` neighbouring lines").
/-- **New, sorry** (elementary case analysis on `closureN`/`outerBoundary`,
not a literature gap).  For `x` a genuine row of the cube and `z` anywhere in
its closed neighbourhood, the off-axis `ℓ¹` distance from `z` to `x` is at
most `(d-1)(k-1) + 1`: on the (at most one) coordinate where `z` strays
outside `[1,k]` the gap to `x`'s in-range value is at most `k` rather than
`k-1`, and there is at most one such coordinate. -/
theorem aux_ct_off_coord (k : ℕ) (hk : 1 ≤ k) (a b : ℤ) (ha1 : 1 ≤ a) (hak : a ≤ (k : ℤ))
    (hb1 : 1 ≤ b) (hbk : b ≤ (k : ℤ)) : (a - b).natAbs ≤ k - 1 := by
  have hcast : (↑(k - 1) : ℤ) = (k : ℤ) - 1 := by
    rw [Nat.cast_sub hk]
    simp
  have hmain : |a - b| ≤ (↑(k - 1) : ℤ) := by
    rw [hcast, abs_le]
    constructor <;> omega
  rw [Int.abs_eq_natAbs] at hmain
  exact Int.ofNat_le.mp hmain

theorem aux_ct_exc_coord (k : ℕ) (a b y : ℤ) (hy1 : 1 ≤ y) (hyk : y ≤ (k : ℤ))
    (ha : a = y + 1 ∨ a = y - 1) (hb1 : 1 ≤ b) (hbk : b ≤ (k : ℤ)) : (a - b).natAbs ≤ k := by
  have hcast : ((k : ℤ)) = (k : ℤ) := rfl
  rcases ha with h | h
  · rw [h]
    have hmain : |y + 1 - b| ≤ (k : ℤ) := by
      rw [abs_le]; constructor <;> omega
    rw [Int.abs_eq_natAbs] at hmain
    exact Int.ofNat_le.mp hmain
  · rw [h]
    have hmain : |y - 1 - b| ≤ (k : ℤ) := by
      rw [abs_le]; constructor <;> omega
    rw [Int.abs_eq_natAbs] at hmain
    exact Int.ofNat_le.mp hmain

theorem aux_ct_bd_gen (d k : ℕ) (i : Fin d) (z x : Site d)
    (hx : x ∈ cube d k) (hz : z ∈ closureN (cube d k)) :
    (∑ l ∈ Finset.univ.erase i, (z l - x l).natAbs) ≤ (d - 1) * (k - 1) + 1 := by
  have hk1 : 1 ≤ k := by
    have h1 : (1 : ℤ) ≤ (k : ℤ) := le_trans (hx i).1 (hx i).2
    omega
  have hzcase : z ∈ cube d k ∨ z ∈ outerBoundary (cube d k) := by
    simpa [closureN] using hz
  have hfinal : ∀ j : Fin d,
      (∀ l : Fin d, (z l - x l).natAbs ≤ (k - 1) + (if l = j then 1 else 0)) →
      (∑ l ∈ Finset.univ.erase i, (z l - x l).natAbs) ≤ (d - 1) * (k - 1) + 1 := by
    intro j hb
    calc (∑ l ∈ Finset.univ.erase i, (z l - x l).natAbs)
        ≤ ∑ l ∈ Finset.univ.erase i, ((k - 1) + (if l = j then 1 else 0)) :=
          Finset.sum_le_sum fun l _ => hb l
      _ = (∑ l ∈ Finset.univ.erase i, (k - 1))
            + ∑ l ∈ Finset.univ.erase i, (if l = j then 1 else 0) := Finset.sum_add_distrib
      _ = (Finset.univ.erase i).card * (k - 1)
            + (if j ∈ Finset.univ.erase i then 1 else 0) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.sum_ite_eq']
      _ ≤ (d - 1) * (k - 1) + 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
          split_ifs <;> omega
  rcases hzcase with hzc | hzb
  · exact hfinal i (fun l => by
      have h1 : (z l - x l).natAbs ≤ k - 1 :=
        aux_ct_off_coord k hk1 (z l) (x l) (hzc l).1 (hzc l).2 (hx l).1 (hx l).2
      by_cases hl : l = i
      · rw [if_pos hl]; omega
      · rw [if_neg hl]; omega)
  · have hzb' : ∃ y ∈ cube d k, (lattice d).Adj z y := by
      have h := hzb
      simp only [outerBoundary, Set.mem_setOf_eq] at h
      exact h.2
    obtain ⟨y, hy, hadj⟩ := hzb'
    have hkey : ∃ j : Fin d,
        (∀ l : Fin d, l ≠ j → z l = y l) ∧ (z j = y j + 1 ∨ z j = y j - 1) := by
      rcases hadj with ⟨j, hj⟩
      refine ⟨j, ?_, ?_⟩
      · intro l hl
        rcases hj with h | h
        · rw [h]; simp [Pi.add_apply, unit, Pi.single_apply, hl]
        · rw [h]; simp [Pi.add_apply, unit, Pi.single_apply, hl]
      · rcases hj with h | h
        · right
          have h1 := congrFun h j
          simp [Pi.add_apply, unit, Pi.single_eq_same] at h1
          omega
        · left
          have h1 := congrFun h j
          simp [Pi.add_apply, unit, Pi.single_eq_same] at h1
          omega
    obtain ⟨j, hzeq, hzJ⟩ := hkey
    exact hfinal j (fun l => by
      by_cases hl : l = j
      · rw [if_pos hl]
        have h1 : (z l - x l).natAbs ≤ k := by
          rw [hl]
          exact aux_ct_exc_coord k (z j) (x j) (y j) (hy j).1 (hy j).2 hzJ (hx j).1 (hx j).2
        have h2 : k = (k - 1) + 1 := (Nat.sub_add_cancel hk1).symm
        omega
      · rw [if_neg hl]
        have h1 : (z l - x l).natAbs ≤ k - 1 := by
          rw [hzeq l hl]
          exact aux_ct_off_coord k hk1 (y l) (x l) (hy l).1 (hy l).2 (hx l).1 (hx l).2
        omega)

theorem aux_ct_propagate_bound_off_dist (d k : ℕ) (i : Fin d) (z x : Site d)
    (hx : x ∈ cube d k) (hz : z ∈ closureN (cube d k)) :
    (∑ l ∈ Finset.univ.erase i, (z l - x l).natAbs) ≤ (d - 1) * (k - 1) + 1 := by
  exact aux_ct_bd_gen d k i z x hx hz


/-- **New, real.** The arithmetic close of the chain-length bound: for
`d ≥ 2` (any `k`), `((d-1)k + 1)(k+1) ≤ (k+1)^d`.  Induction on `d` (written
as `d0 + 2`), the base case an equality (`ring`), the step reducing to
`k ≤ (k+1)^{d0+2}` via `Nat.le_self_pow`. -/
theorem aux_ct_propagate_key_ineq (d0 k : ℕ) :
    ((d0 + 1) * k + 1) * (k + 1) ≤ (k + 1) ^ (d0 + 2) := by
  induction d0 with
  | zero => exact le_of_eq (by ring)
  | succ d0 ih =>
    have hpow : (k + 1) ^ (d0 + 1 + 2) = (k + 1) * (k + 1) ^ (d0 + 2) := by ring
    have hself : (k + 1) ≤ (k + 1) ^ (d0 + 2) :=
      Nat.le_self_pow (by omega) (k + 1)
    rw [hpow]
    nlinarith [ih, hself]

/-- **New, real.** By induction on `n`, using `aux_ct_propagate_off_step` and
`aux_ct_propagate_line_fill`: `n` steps of coordinate-peeling from `z` towards
a fixed `x ∈ cube d k` reach a point at off-axis distance `(off-dist z x) - n`
from `x`, whose line is toppled by time `n * k`.  The base case (`n = 0`) is
the seed line itself (`w0`'s own value, unconditionally `1` there). -/
theorem aux_ct_propagate_chain (d k : ℕ) (hd : 2 ≤ d) (η : Site d → ℤ)
    (hbdd : ∀ x, 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1)
    (hgood : ∀ (i : Fin d) (y : Site d), y ∈ cube d k → ∃ x ∈ line d k i y,
      η x = 2 * (d : ℤ) - 1)
    (i : Fin d) (z x : Site d) (hx : x ∈ cube d k) (hz : z ∈ closureN (cube d k)) :
    ∀ m : ℕ, m ≤ (∑ l ∈ Finset.univ.erase i, (z l - x l).natAbs) →
      ∃ y : Site d, OffGood i k y ∧
        (∑ l ∈ Finset.univ.erase i, (y l - x l).natAbs)
          = (∑ l ∈ Finset.univ.erase i, (z l - x l).natAbs) - m ∧
        ∀ w ∈ line d k i y, crossOdo η k i z (m * k) w = 1 := by
  have hk1 : 1 ≤ k := by have := hx i; omega
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨z, aux_ct_offgood_closureN hk1 hz, by simp, fun w hw => ?_⟩
    simp only [Nat.zero_mul]
    show crossOdo η k i z 0 w = 1
    simp [crossOdo, hw]
  | succ m ih =>
    intro hm
    obtain ⟨y, hyoff, hydist, hylit⟩ := ih (by omega)
    have hrem : (∑ l ∈ Finset.univ.erase i, (y l - x l).natAbs)
        = ((∑ l ∈ Finset.univ.erase i, (z l - x l).natAbs) - m - 1) + 1 := by omega
    obtain ⟨y', hy'i, hadj, hy'range, hy'dist⟩ :=
      aux_ct_off_step5 i x y hx hyoff
        ((∑ l ∈ Finset.univ.erase i, (z l - x l).natAbs) - m - 1) hrem
    have hcube : (fun l => if l = i then (1 : ℤ) else y' l) ∈ cube d k := by
      intro l
      by_cases hl : l = i
      · simp [hl, hk1]
      · simpa [hl] using hy'range l hl
    have hlineeq : line d k i (fun l => if l = i then (1 : ℤ) else y' l) = line d k i y' := by
      ext w
      simp only [line, Set.mem_setOf_eq]
      refine and_congr_right fun _ => ?_
      constructor
      · intro h l hl; have := h l hl; simpa [hl] using this
      · intro h l hl; simpa [hl] using h l hl
    have hcat : ∃ p ∈ line d k i y', η p = 2 * (d : ℤ) - 1 := by
      obtain ⟨p, hp, hpη⟩ := hgood i _ hcube
      exact ⟨p, hlineeq ▸ hp, hpη⟩
    have hfill := aux_ct_propagate_line_fill d k hd η hbdd i z y' y hcat hy'range
      hadj.symm hy'i (m * k) hylit
    refine ⟨y', Or.inl hy'range, hy'dist, fun w hw => ?_⟩
    have := hfill w hw
    have heq : m * k + k = (m + 1) * k := by ring
    rwa [heq] at this

/-- **(a)** (`exploding.tex:445-449`).  If `η` is pointwise bounded as in
`(1.2)` and every line of `Q_k`, in every direction, carries a `(2d-1)`-chip
catalyst, then `Q_k` is a good cube: every crossing time `𝔠_k^{(i,z)}`,
`z ∈ closureN (cube d k)`, is at most `k^d`.  Assembled from
`aux_ct_propagate_chain` (reach `x` from `z` by peeling off-axis coordinates
one at a time), `aux_ct_propagate_bound_off_dist` (the chain is short) and
`aux_ct_propagate_key_ineq` (short chains times `k` fit inside `k^d`),
squeezed up to a uniform time bound via `fodo_le_one` and
`aux_ct_propagate_fodo_mono_time`. -/
theorem aux_ct_propagate (d k : ℕ) (hd : 2 ≤ d) (η : Site d → ℤ)
    (hbdd : ∀ x, 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1)
    (hgood : ∀ (i : Fin d) (y : Site d), y ∈ cube d k → ∃ x ∈ line d k i y,
      η x = 2 * (d : ℤ) - 1) :
    GoodCube η k := by
  intro i z hz
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · exfalso
      subst hk0
      simp only [closureN, outerBoundary, cube] at hz
      obtain hz | ⟨_, y, hy, _⟩ := hz
      · exact absurd (hz i) (by omega)
      · exact absurd (hy i) (by omega)
    · omega
  have key : ∀ x ∈ cube d k, ∃ m : ℕ, m ≤ (d - 1) * (k - 1) + 1 ∧
      crossOdo η k i z (m * k) x = 1 := by
    intro x hx
    obtain ⟨y, _hyoff, hydist, hylit⟩ := aux_ct_propagate_chain d k hd η hbdd hgood i z x hx hz
      (∑ l ∈ Finset.univ.erase i, (z l - x l).natAbs) le_rfl
    have hxline : x ∈ line d k i y := by
      have hyeq : ∀ l, l ≠ i → y l = x l := by
        intro l hl
        have h0 : (y l - x l).natAbs = 0 := by
          have hsum := Finset.sum_eq_zero_iff_of_nonneg
            (s := Finset.univ.erase i) (f := fun l => (y l - x l).natAbs)
            (fun l _ => Nat.zero_le _)
          have : (∑ l ∈ Finset.univ.erase i, (y l - x l).natAbs) = 0 := by omega
          exact (hsum.mp this) l (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩)
        omega
      refine ⟨hx i, fun l hl => ?_⟩
      rw [← hyeq l hl]
    refine ⟨(∑ l ∈ Finset.univ.erase i, (z l - x l).natAbs), ?_, hylit x hxline⟩
    exact aux_ct_propagate_bound_off_dist d k i z x hx hz
  set M : ℕ := ((d - 1) * (k - 1) + 1) * k with hMdef
  refine le_trans (sInf_le ⟨M, rfl, ?_, ?_⟩) ?_
  · rw [hMdef]
    have h1 : (d - 1) * (k - 1) + 1 ≠ 0 := by omega
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero h1 (by omega))
  · intro x hx
    obtain ⟨m, hmle, hmx⟩ := key x hx
    have hmono := aux_ct_propagate_fodo_mono_time
      ((cube d k)ᶜ ∪ line d k i z) η (fun w => if w ∈ line d k i z then (1 : ℤ) else 0)
      (show m * k ≤ M from Nat.mul_le_mul_right k hmle) x
    have hle1 : crossOdo η k i z M x ≤ 1 :=
      fodo_le_one _ η _ (fun w => (hbdd w).2)
        (by intro w; split_ifs <;> norm_num) (by intro w; split_ifs <;> norm_num) M x
    have hge1 : (1 : ℤ) ≤ crossOdo η k i z M x := hmx ▸ hmono
    omega
  · obtain ⟨d0, hd0⟩ : ∃ d0, d = d0 + 2 := ⟨d - 2, by omega⟩
    obtain ⟨k0, hk0⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
    have hineq := aux_ct_propagate_key_ineq d0 k0
    have hd1 : d - 1 = d0 + 1 := by omega
    have hk1' : k - 1 = k0 := by omega
    have hMeq : M = ((d0 + 1) * k0 + 1) * (k0 + 1) := by
      rw [hMdef, hd1, hk1', hk0]
    have hkdeq : k ^ d = (k0 + 1) ^ (d0 + 2) := by rw [hk0, hd0]
    have hcast : M ≤ k ^ d := by rw [hMeq, hkdeq]; exact hineq
    exact_mod_cast hcast

/-! ### (e) Assembly -/

-- GAP-closing pieces (all new, all real except `aux_ct_decay_eventually`),
-- used by `aux_ct_assemble` below.

/-- **New, real.** `cube d k` is the `Fin d`-indexed product of `d` copies of
`Set.Icc (1:ℤ) k`, so its finiteness and cardinality reduce to
`Set.Finite.pi`/`Set.encard_pi_eq_prod_encard`. -/
theorem aux_ct_assemble_cube_eq_pi (d k : ℕ) :
    cube d k = Set.pi Set.univ (fun _ : Fin d => (Set.Icc (1 : ℤ) (k : ℤ) : Set ℤ)) := by
  ext x
  simp [cube, Pi.le_def, forall_and]

/-- **New, real.** `cube d k` is finite: it is the product (via
`aux_ct_assemble_cube_eq_pi`) of `d` copies of the finite set `Set.Icc 1 k`
(`Set.finite_Icc`), and `Set.Finite.pi` gives finiteness of the product. -/
theorem aux_ct_assemble_cube_finite (d k : ℕ) : (cube d k).Finite := by
  refine (Set.Finite.pi (fun _ : Fin d => Set.finite_Icc (1 : ℤ) (k : ℤ))).subset ?_
  intro x hx i _
  exact hx i

/-- **New, real.** `(cube d k).ncard = k ^ d`: rewrite via
`aux_ct_assemble_cube_eq_pi`, compute `(Set.Icc (1:ℤ) k).encard = k` (`Finset.
coe_Icc`/`Set.encard_coe_eq_coe_finsetCard`, `Int.card_Icc`), multiply the `d`
equal factors with `Set.encard_pi_eq_prod_encard`/`Finset.prod_const`, and
unfold `Set.ncard = ENat.toNat ∘ Set.encard` (`ENat.toNat_coe`). -/
theorem aux_ct_enat_toNat_pow (k d : ℕ) : ((k : ℕ∞) ^ d).toNat = k ^ d := by
  induction d with
  | zero => simp
  | succ n ih => rw [pow_succ, ENat.toNat_mul, ih, ENat.toNat_coe, pow_succ]

theorem aux_ct_setIcc_encard (k : ℕ) : (Set.Icc (1 : ℤ) (k : ℤ) : Set ℤ).encard = (k : ℕ∞) := by
  rw [← Finset.coe_Icc, Set.encard_coe_eq_coe_finsetCard, Int.card_Icc]
  congr 1
  omega

theorem aux_ct_assemble_cube_ncard (d k : ℕ) : (cube d k).ncard = k ^ d := by
  rw [aux_ct_assemble_cube_eq_pi, Set.ncard_def, Set.encard_pi_eq_prod_encard,
    aux_ct_setIcc_encard, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact aux_ct_enat_toNat_pow k d


/-- **New, real (standard).** The polynomial-times-geometric decay
`n^d · r^n → 0` for `r := exp(-2ε²) ∈ [0,1)`
(`tendsto_pow_const_mul_const_pow_of_lt_one`, `Mathlib.Analysis.
SpecificLimits.Normed`), unwound via `Filter.Tendsto.eventually` at the
threshold `δ/(d+1)` and `Filter.Eventually.exists_forall_of_atTop` into an
explicit `N`. -/
theorem aux_ct_decay_eventually (d : ℕ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (n : ℝ) ^ d * (Real.exp (-2 * ε ^ 2)) ^ n < δ / ((d : ℝ) + 1) := by
  set r := Real.exp (-2 * ε ^ 2) with hrdef
  have hr_nonneg : 0 ≤ r := Real.exp_nonneg _
  have hr_lt_one : r < 1 := by
    rw [hrdef, Real.exp_lt_one_iff]
    have hneg : -2 * ε ^ 2 < 0 := by nlinarith
    exact hneg
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ d * r ^ n) atTop (nhds 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one d hr_nonneg hr_lt_one
  have hpos : 0 < δ / ((d : ℝ) + 1) := by
    refine div_pos hδ ?_
    have hd_nonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
    nlinarith
  have h_event : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ d * r ^ n < δ / ((d : ℝ) + 1) :=
    hlim.eventually (eventually_lt_nhds hpos)
  rcases h_event.exists_forall_of_atTop with ⟨N, hN⟩
  exact ⟨N, hN⟩

/-- **New, real (the "(e)" real-analysis step, modulo
`aux_ct_decay_eventually`).** From `aux_ct_decay_eventually`'s `N`, take
`k := max N 1`; `Real.exp_nat_mul` turns `r^k` back into `exp(-2ε²k)`, and
`(d:ℝ) < (d:ℝ)+1` closes the final bound. -/
theorem aux_ct_decay (d : ℕ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ k : ℕ, 1 ≤ k ∧ (d : ℝ) * (k : ℝ) ^ d * Real.exp (-2 * ε ^ 2 * (k : ℝ)) < δ := by
  obtain ⟨N, hN⟩ := aux_ct_decay_eventually d ε δ hε hδ
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  have hb := hN (max N 1) (le_max_left _ _)
  have hrn : (Real.exp (-2 * ε ^ 2)) ^ (max N 1) = Real.exp (-2 * ε ^ 2 * ((max N 1 : ℕ) : ℝ)) := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [hrn] at hb
  have hdpos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  calc (d : ℝ) * ((max N 1 : ℕ) : ℝ) ^ d * Real.exp (-2 * ε ^ 2 * ((max N 1 : ℕ) : ℝ))
      ≤ ((d : ℝ) + 1) * (((max N 1 : ℕ) : ℝ) ^ d * Real.exp (-2 * ε ^ 2 * ((max N 1 : ℕ) : ℝ))) := by
        nlinarith [Real.exp_pos (-2 * ε ^ 2 * ((max N 1 : ℕ) : ℝ)),
          pow_nonneg (Nat.cast_nonneg (max N 1) : (0 : ℝ) ≤ ((max N 1 : ℕ) : ℝ)) d]
    _ < ((d : ℝ) + 1) * (δ / ((d : ℝ) + 1)) := mul_lt_mul_of_pos_left hb hdpos
    _ = δ := by field_simp

/-- **(e)**. Pick `ε := p / 2` (so `0 < ε < p`), and `k` from `aux_ct_decay`
so that `aux_ct_all_directions`'s bound `d · (cube d k).ncard · exp(-2ε²k)`
(rewritten via `aux_ct_assemble_cube_ncard`) is `< δ`. The "bad" event (some
direction/line has no catalyst) then has probability `< ofReal δ`, and the
"unbounded" event has probability `0` (`aux_ct_ae_bounded`); their union
covers `{η | GoodCube η k}ᶜ` by the contrapositive of `aux_ct_propagate`, so
`measure_union_le` bounds `toyLaw d p {GoodCube η k}ᶜ ≤ ofReal δ`, and
`measure_union_le` again on `{GoodCube} ∪ {GoodCube}ᶜ = univ` (no measurability
needed) gives the final `1 - δ` bound in `ℝ≥0∞`-arithmetic. -/
theorem aux_ct_assemble (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ k : ℕ, 1 ≤ k ∧ ENNReal.ofReal (1 - δ) ≤ toyLaw d p {η | GoodCube η k} := by
  haveI hIPM' : IsProbabilityMeasure (toyLaw d p) := by
    unfold toyLaw productLaw
    have hIPM : IsProbabilityMeasure (chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p) := by
      refine ⟨?_⟩
      unfold chipLaw
      simp only [Measure.add_apply, Measure.smul_apply, MeasureTheory.measure_univ, smul_eq_mul,
        mul_one]
      rw [← ENNReal.ofReal_add hp.le (by linarith)]
      norm_num
    infer_instance
  set ε : ℝ := p / 2 with hεdef
  have hε0 : 0 < ε := by positivity
  have hεp : ε < p := by rw [hεdef]; linarith
  obtain ⟨k, hk1, hkbound⟩ := aux_ct_decay d ε δ hε0 hδ
  refine ⟨k, hk1, ?_⟩
  set Bad : Set (Site d → ℤ) := {η | ¬ ∀ (i : Fin d) (y : Site d), y ∈ cube d k →
    ∃ x ∈ line d k i y, η x = 2 * (d : ℤ) - 1} with hBaddef
  set Unbdd : Set (Site d → ℤ) :=
    {η | ¬ ∀ x : Site d, 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1} with hUdef
  have hfin := aux_ct_assemble_cube_finite d k
  have hcardeq : (hfin.toFinset.card : ℝ) = (k : ℝ) ^ d := by
    rw [← Set.ncard_eq_toFinset_card (cube d k) hfin, aux_ct_assemble_cube_ncard]
    push_cast; ring
  have hbad := aux_ct_all_directions d k hd p hp hp1 ε hε0 hεp hfin
  rw [hcardeq] at hbad
  have hbadlt : toyLaw d p Bad < ENNReal.ofReal δ :=
    lt_of_le_of_lt hbad (ENNReal.ofReal_lt_ofReal_iff hδ |>.mpr hkbound)
  have hUzero : toyLaw d p Unbdd = 0 := by
    have hae := aux_ct_ae_bounded d hd p hp hp1
    rwa [MeasureTheory.ae_iff] at hae
  have hsub : {η : Site d → ℤ | GoodCube η k}ᶜ ⊆ Bad ∪ Unbdd := by
    intro η hη
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    apply hη
    simp only [hBaddef, hUdef, Set.mem_setOf_eq, not_not] at hcon
    exact aux_ct_propagate d k hd η hcon.2 hcon.1
  have hcompl_le : toyLaw d p {η : Site d → ℤ | GoodCube η k}ᶜ ≤ ENNReal.ofReal δ := by
    calc toyLaw d p {η : Site d → ℤ | GoodCube η k}ᶜ
        ≤ toyLaw d p (Bad ∪ Unbdd) := measure_mono hsub
      _ ≤ toyLaw d p Bad + toyLaw d p Unbdd := measure_union_le _ _
      _ ≤ ENNReal.ofReal δ := by rw [hUzero, add_zero]; exact hbadlt.le
  have htot : (1 : ENNReal) ≤ toyLaw d p {η : Site d → ℤ | GoodCube η k}
      + toyLaw d p {η : Site d → ℤ | GoodCube η k}ᶜ := by
    have hu := measure_union_le (μ := toyLaw d p)
      {η : Site d → ℤ | GoodCube η k} {η : Site d → ℤ | GoodCube η k}ᶜ
    rw [Set.union_compl_self, measure_univ] at hu
    exact hu
  rcases le_total δ 1 with hδ1 | hδ1
  · have h1 : ENNReal.ofReal (1 - δ) + ENNReal.ofReal δ = 1 := by
      rw [← ENNReal.ofReal_add (by linarith) hδ.le]
      norm_num
    have hstep : (1 : ENNReal) ≤ toyLaw d p {η : Site d → ℤ | GoodCube η k} + ENNReal.ofReal δ := by
      calc (1 : ENNReal) ≤ toyLaw d p {η : Site d → ℤ | GoodCube η k}
            + toyLaw d p {η : Site d → ℤ | GoodCube η k}ᶜ := htot
        _ ≤ toyLaw d p {η : Site d → ℤ | GoodCube η k} + ENNReal.ofReal δ := by gcongr
    rw [← h1] at hstep
    exact (ENNReal.add_le_add_iff_right (a := ENNReal.ofReal δ)
      (by simp [ENNReal.ofReal_ne_top])).mp hstep
  · have hnonpos : (1 - δ) ≤ 0 := by linarith
    rw [ENNReal.ofReal_of_nonpos hnonpos]
    exact zero_le
