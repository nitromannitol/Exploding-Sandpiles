/-
Theorem 1.4 of the paper: a product background with at least `d` chips
everywhere and a positive density of sites with `2d - 1` chips is explosive.

DECOMPOSITION (not a proof attempt).  Paper proof: exploding.tex:1806-1811
plus all of Section 7 ("we show P is recurrent and box-crossing... by
monotonicity, we may assume η → {d, 2d-1}").  This node is mostly assembly
of three already-identified pieces (`Exploding.Frozen.recurrence`, SEALED;
`Exploding.Frozen.box_crossing`, node `prop-box-crossing`;
`Exploding.Frozen.explosion_criteria`, node `prop-explosion-criteria`, this
campaign) PLUS one genuinely new ingredient: the paper's own reduction "by
monotonicity, we may assume η → {d, 2d-1}" needs a monotonicity-of-
explosiveness lemma (bigger background explodes at least as easily) that is
NOT formalised anywhere in Exploding/Support/*.lean.  This is the SAME
foundational gap flagged in `lem-square-lower-bound`'s decomposition
(the `eq:odometer_wave_comp` domination principle, exploding.tex:386-391)
and in `prop-generalized-last-wave`'s (`aux_glw_wave_to_explosive`'s
implicit domination); recorded here as its own aux lemma rather than assumed
solved, since none of those three files actually discharges it either.
-/
import Exploding.Support.Hypotheses
import Exploding.Support.SubFodoStep
import Exploding.Support.SubFodo
import Exploding.Frozen.Recurrence
import Exploding.Frozen.BoxCrossing
import Exploding.Frozen.ExplosionCriteria
import Exploding.External.Schonmann

open Exploding LatticeProb MeasureTheory

namespace Exploding.Frozen.ExplosiveDec

variable {d : ℕ}

/-- Step 1a (TRUE, general, no gap): the parallel toppling odometer is
monotone in the background, pointwise, at every time.  PROOF PLAN: induction
on `t` with the IH universally quantified over `x` (needed since the
successor step at `x` reads the IH at `x`'s neighbours too, via `nbrSumZ`).
At the successor step, case on `podo η1 t x < podo η2 t x` (strict: then
`podo η1 (t+1) x ≤ podo η1 t x + 1 ≤ podo η2 t x ≤ podo η2 (t+1) x`, using
`podo_mono_step` on both sides) or `podo η1 t x = podo η2 t x =: v` (then
`pconf η1 t x ≤ pconf η2 t x` follows from `hle x` and `nbrSumZ_mono (fun y
=> ih y)`, since the `-2d*v` terms in `pconf`'s unfolding, `lap_eq`, cancel
exactly; so `η1` firing at `x` forces `η2` to fire there too, and either way
`podo η1 (t+1) x ≤ podo η2 (t+1) x`). -/
theorem aux_podo_step {η1 η2 : Site d → ℤ} (hle : ∀ x, η1 x ≤ η2 x) (t : ℕ)
    (ih : ∀ x, podo η1 t x ≤ podo η2 t x) : ∀ x, podo η1 (t + 1) x ≤ podo η2 (t + 1) x := by
  intro x
  rw [podo_succ, podo_succ]
  by_cases hlt : podo η1 t x < podo η2 t x
  · have ha1 : (if 2 * d ≤ pconf η1 t x then (1 : ℤ) else 0) ≤ 1 := by
      split <;> omega
    have ha2 : (0 : ℤ) ≤ (if 2 * d ≤ pconf η2 t x then (1 : ℤ) else 0) := by
      split <;> omega
    linarith
  · have heq : podo η1 t x = podo η2 t x := le_antisymm (ih x) (not_lt.mp hlt)
    have hp : pconf η1 t x ≤ pconf η2 t x := by
      simp only [pconf, lap_eq]
      have hn : nbrSumZ (podo η1 t) x ≤ nbrSumZ (podo η2 t) x := nbrSumZ_mono ih x
      have hv : 2 * (d : ℤ) * podo η1 t x = 2 * (d : ℤ) * podo η2 t x := by rw [heq]
      linarith [hle x]
    have hc : (if 2 * d ≤ pconf η1 t x then (1 : ℤ) else 0) ≤
        (if 2 * d ≤ pconf η2 t x then (1 : ℤ) else 0) := by
      by_cases h : 2 * d ≤ pconf η1 t x
      · rw [if_pos h, if_pos (le_trans h hp)]
      · rw [if_neg h]
        split <;> omega
    rw [heq]
    linarith

theorem aux_te_podo_mono {η1 η2 : Site d → ℤ} (hle : ∀ x, η1 x ≤ η2 x) :
    ∀ t : ℕ, ∀ x, podo η1 t x ≤ podo η2 t x := by
  intro t
  induction t with
  | zero => intro x; simp
  | succ t ih => exact aux_podo_step hle t ih


/-- Step 1b, NEEDS-PROOF-DESIGN: the genuine remaining gap, isolated from the
(TRUE, above) monotonicity fact.  Even granting `aux_te_podo_mono`'s pointwise
domination `podo η1 t x ≤ podo η2 t x` for every `t, x`, and that `η2`'s
odometer freezes at a single time `T` (`Stabilizable η2`, equivalently
`∀ x, pconf η2 T x < 2d` from then on), the per-site sequences `t ↦ podo η1 t
x` are only pinned down as nondecreasing and bounded above by `podo η2 T x`
(itself `≤` the same bound for every earlier `t` too, by `podo_mono_step`
chained forward from `t` to `T`).  A bounded nondecreasing INTEGER sequence
must eventually be constant, but the time at which it settles can a priori
depend on `x`, and `Stabilizable` demands a SINGLE time working for every `x`
simultaneously — exactly the phenomenon this paper's OWN Theorem 6.1
counterexample exhibits (every site eventually quiets, yet no uniform time
works).  Closing this needs either a genuinely different, non-parallel-
toppling least-action argument (the general form of the "parabolic least
action principle", Lemma 2.3 in [bou2020dynamic], cited but unformalized
elsewhere in this repository: `lem-square-lower-bound`'s
`eq:odometer_wave_comp` and `prop-generalized-last-wave`'s
`aux_glw_wave_to_explosive`), or an extra finite-range/propagation-speed
hypothesis on `η1`/`η2` that this lemma's fully general signature does not
carry.  Neither route is carried out here. -/
theorem aux_te_domination_stabilizes {η1 η2 : Site d → ℤ}
    (hpodo : ∀ t : ℕ, ∀ x, podo η1 t x ≤ podo η2 t x) (h2 : Stabilizable η2) :
    Stabilizable η1 := by
  sorry

/-- Step 1 (foundational, shared with `lem-square-lower-bound` and
`prop-generalized-last-wave`'s decompositions).  Domination of `Explosive`
under a pointwise-larger background: bigger chip counts can only cause MORE
firing, so a background dominating an explosive one is itself explosive.
Assembled from `aux_te_podo_mono` (TRUE, the easy monotonicity half) and
`aux_te_domination_stabilizes` (the genuine, flagged gap): contrapositive on
`Robust η2`, reduce to `Stabilizable (η2 + nδ0) → Stabilizable (η1 + nδ0)` for
the SAME `n`, which is exactly `aux_te_domination_stabilizes` fed the podo
domination for the shifted backgrounds `η1 + nδ0 ≤ η2 + nδ0` (immediate from
`hle`). -/
theorem aux_te_explosive_mono {η1 η2 : Site d → ℤ} (hle : ∀ x, η1 x ≤ η2 x)
    (h1 : Explosive η1) : Explosive η2 := by
  intro hrob
  apply h1
  intro n hn
  apply aux_te_domination_stabilizes _ (hrob n hn)
  intro t x
  refine aux_te_podo_mono (fun y => ?_) t x
  linarith [hle y]

/-- Step 2 (the paper's "by monotonicity, we may assume `η → {d, 2d-1}`").
Given the product law `ν` with `ν{m : d ≤ m} = 1` and `ν{2d-1} > 0`, the
coordinatewise clamp `ν' := Measure.map (fun m => min m (2*(d:ℤ)-1)) ν` is
again a probability measure with `ν'{m : d ≤ m} = 1` and `ν'{2d-1} > 0`
(clamping never drops a value below `d`, since `d ≤ 2d-1` for `d ≥ 1`, and
the event `{m = 2d-1}` maps into `{2d-1}` under the clamp).  Also, if `β` is
sampled coordinatewise from `ν` and `β' x := min (β x) (2*(d:ℤ)-1)`
pointwise, then `β'` has law `Measure.infinitePi (fun _ => ν')` and
`β' x ≤ β x` for every `x`. -/
theorem aux_te_clamp_measure (d : ℕ) (ν : Measure ℤ) (hν : IsProbabilityMeasure ν)
    (hlow : ν {m : ℤ | (d : ℤ) ≤ m} = 1) (hhit : 0 < ν {(2 * (d : ℤ) - 1)}) :
    ∃ ν' : Measure ℤ, IsProbabilityMeasure ν' ∧
      ν' {m : ℤ | (d : ℤ) ≤ m} = 1 ∧ 0 < ν' {(2 * (d : ℤ) - 1)} ∧
      ν' = Measure.map (fun m : ℤ => min m (2 * (d : ℤ) - 1)) ν ∧
      Measure.map (fun β : Site d → ℤ => fun x => min (β x) (2 * (d : ℤ) - 1))
          (Measure.infinitePi fun _ : Site d => ν)
        = Measure.infinitePi fun _ : Site d => ν' := by
  sorry

/-- Step 3 (should be straightforward from `Measure.infinitePi` being a
product measure; check Mathlib's `ProbabilityTheory.IndepFun`/
`MeasureTheory.Measure.infinitePi` API before flagging as a GAP).  Distinct
coordinate projections of an independent product measure are independent, so the
restrictions to disjoint finite sets are independent and `FiniteRangeOfDependence` holds
with `K = 0`. -/
theorem aux_te_finite_range (d : ℕ) (ν' : Measure ℤ) (hν' : IsProbabilityMeasure ν') :
    FiniteRangeOfDependence d (Measure.infinitePi fun _ : Site d => ν') := by
  refine ⟨0, fun I J hIJ => ?_⟩
  haveI : ∀ i : Site d, IsProbabilityMeasure (ν' : Measure ℤ) := fun _ => hν'
  have h : ProbabilityTheory.iIndepFun (fun (i : Site d) (ω : Site d → ℤ) => ω i)
      (Measure.infinitePi fun _ : Site d => ν') :=
    ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : Site d => ν')
      (X := fun (_ : Site d) (m : ℤ) => m) (by fun_prop)
  have hdisj : Disjoint I J := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have := hIJ a ha a hb
    simp [mnorm] at this
  exact ProbabilityTheory.iIndepFun.indepFun_finset I J hdisj h (fun i => measurable_pi_apply i)


/-- Step 4 (monotonicity of `Recurrent`, the same family of fact as Step 1 --
bigger backgrounds fire at least as much, so a domain that is recurrent for
a smaller background is recurrent for a bigger one).  Combined with the
SEALED `Exploding.Frozen.recurrence` (`∀ d ≥ 1, η ≡ d` is recurrent) and
`d ≤ η' x` a.s. (Step 2's `ν'{m : d ≤ m} = 1`), gives `RecurrentLaw` for the
clamped measure. -/
theorem aux_te_fodo_mono {d : ℕ} (S : Set (Site d)) (s0 s0' w0 : Site d → ℤ)
    (hle : ∀ x, s0 x ≤ s0' x) (t : ℕ) (x : Site d) :
    fodo S s0 w0 t x ≤ fodo S s0' w0 t x := by
  induction t generalizing x with
  | zero => simp [fodo_zero]
  | succ t ih =>
    rw [fodo_succ, fodo_succ]
    by_cases hx : x ∈ S
    · rw [if_pos hx, if_pos hx]
    · rw [if_neg hx, if_neg hx]
      by_cases hlt : fodo S s0 w0 t x < fodo S s0' w0 t x
      · have h1 : (if 2 * (d : ℤ) ≤ fconf S s0 w0 t x then (1 : ℤ) else 0) ≤ 1 := by
          split <;> omega
        have h2 : (0 : ℤ) ≤ (if 2 * (d : ℤ) ≤ fconf S s0' w0 t x then (1 : ℤ) else 0) := by
          split <;> omega
        linarith
      · have heq : fodo S s0 w0 t x = fodo S s0' w0 t x := le_antisymm (ih x) (not_lt.mp hlt)
        have hconf : fconf S s0 w0 t x ≤ fconf S s0' w0 t x := by
          simp only [fconf, lap_eq]
          have hn : nbrSumZ (fodo S s0 w0 t) x ≤ nbrSumZ (fodo S s0' w0 t) x :=
            nbrSumZ_mono (fun y => ih y) x
          have hv : 2 * (d : ℤ) * fodo S s0 w0 t x = 2 * (d : ℤ) * fodo S s0' w0 t x := by rw [heq]
          linarith [hle x]
        have h3 : (if 2 * (d : ℤ) ≤ fconf S s0 w0 t x then (1 : ℤ) else 0) ≤
            (if 2 * (d : ℤ) ≤ fconf S s0' w0 t x then (1 : ℤ) else 0) := by
          by_cases h : 2 * (d : ℤ) ≤ fconf S s0 w0 t x
          · rw [if_pos h, if_pos (le_trans h hconf)]
          · rw [if_neg h]; split <;> omega
        linarith

theorem aux_te_recurrent_mono {η1 η2 : Site d → ℤ} (hle : ∀ x, η1 x ≤ η2 x)
    (hub : ∀ x, η2 x ≤ 2 * (d : ℤ) - 1) (h1 : Recurrent η1) : Recurrent η2 := by
  classical
  intro V t ht x hx
  have hle1 : fodo ((↑V : Set (Site d))ᶜ) η1
      (fun y => if y ∈ outerBoundary (↑V : Set (Site d)) then 1 else 0) t x
      ≤ fodo ((↑V : Set (Site d))ᶜ) η2
      (fun y => if y ∈ outerBoundary (↑V : Set (Site d)) then 1 else 0) t x :=
    aux_te_fodo_mono _ η1 η2 _ hle t x
  have hup : fodo ((↑V : Set (Site d))ᶜ) η2
      (fun y => if y ∈ outerBoundary (↑V : Set (Site d)) then 1 else 0) t x ≤ 1 :=
    fodo_le_one _ η2 _ hub (fun y => by split_ifs <;> omega)
      (fun y => by split_ifs <;> omega) t x
  rw [h1 V t ht x hx] at hle1
  exact le_antisymm hup hle1

theorem aux_ae_prod (d : ℕ) (μ : Measure ℤ) (hμ : IsProbabilityMeasure μ) (p : ℤ → Prop)
    (hpmeas : MeasurableSet {m : ℤ | p m}) (hp : μ {m : ℤ | p m} = 1) :
    ∀ᵐ β ∂(Measure.infinitePi fun _ : Site d => μ), ∀ x : Site d, p (β x) := by
  haveI : IsProbabilityMeasure μ := hμ
  haveI hinst : ∀ i : Site d, IsProbabilityMeasure ((fun _ : Site d => μ) i) := fun _ => hμ
  rw [ae_all_iff]
  intro x
  have hmapx := Measure.infinitePi_map_eval (μ := fun _ : Site d => μ) x
  have hmeas : Measurable fun β : Site d → ℤ => β x := measurable_pi_apply x
  have hzero : μ {m : ℤ | p m}ᶜ = 0 := by
    rw [measure_compl hpmeas (measure_ne_top _ _), hp]
    simp
  rw [ae_iff]
  have hpre : {β : Site d → ℤ | ¬ p (β x)} = (fun β : Site d → ℤ => β x) ⁻¹' {m : ℤ | p m}ᶜ := by
    ext β; simp
  rw [hpre, ← Measure.map_apply hmeas hpmeas.compl, hmapx]
  exact hzero

theorem aux_te_recurrent_law (d : ℕ) (hd : 1 ≤ d) (ν' : Measure ℤ) (hν' : IsProbabilityMeasure ν')
    (hlow : ν' {m : ℤ | (d : ℤ) ≤ m} = 1)
    (hupper : ν' {m : ℤ | m ≤ 2 * (d : ℤ) - 1} = 1) :
    RecurrentLaw d (Measure.infinitePi fun _ : Site d => ν') := by
  rw [RecurrentLaw]
  have hconst : Recurrent (fun _ : Site d => (d : ℤ)) := Exploding.Frozen.recurrence d hd
  have hlow_ae : ∀ᵐ η ∂(Measure.infinitePi fun _ : Site d => ν'), ∀ x : Site d, (d : ℤ) ≤ η x :=
    (by
      rw [ae_all_iff]
      intro x
      rw [ae_iff]
      rw [show {η : Site d → ℤ | ¬ (d : ℤ) ≤ η x} =
          (Function.eval x) ⁻¹' {m : ℤ | ¬ (d : ℤ) ≤ m} from rfl]
      rw [← Measure.map_apply (measurable_pi_apply x)
          (show MeasurableSet {m : ℤ | ¬ (d : ℤ) ≤ m} from measurableSet_Ici.compl)]
      rw [(measurePreserving_eval_infinitePi (fun _ : Site d => ν') x).map_eq]
      rw [show {m : ℤ | ¬ (d : ℤ) ≤ m} = {m : ℤ | (d : ℤ) ≤ m}ᶜ from rfl]
      rw [measure_compl (s := {m : ℤ | (d : ℤ) ≤ m}) measurableSet_Ici
          (by rw [hlow]; exact ENNReal.one_ne_top), measure_univ, hlow, tsub_self])
  have hupper_ae : ∀ᵐ η ∂(Measure.infinitePi fun _ : Site d => ν'), ∀ x : Site d,
      η x ≤ 2 * (d : ℤ) - 1 := aux_ae_prod d ν' hν' (fun m : ℤ => m ≤ 2 * (d : ℤ) - 1)
        measurableSet_Iic hupper
  filter_upwards [hlow_ae, hupper_ae] with η hη hηu
  exact aux_te_recurrent_mono (fun x => hη x) (fun x => hηu x) hconst


/-- Step 5 (`-- GAP:` ergodicity of an i.i.d. product measure under the full
lattice shift, i.e. a Kolmogorov 0-1 law for the tail σ-algebra of an
independent field).  Checked: neither `Mathlib.Dynamics.Ergodic.*` nor
`Mathlib.Probability.*` in this checkout has a ready "product measures are
ergodic under translation" instance (`ErgodicVAdd`/`ErgodicSMul` are generic
typeclasses with no i.i.d.-field instance found by grep); this is standard
but unformalized. Stationarity (`StationaryOn`) by contrast IS immediate
from `Measure.infinitePi` being genuinely translation-invariant and should
NOT be flagged as a gap. CORRECTION (orchestrator, after cross-check): NOT a gap.  `LatticeProb.ergodic_coordShift_infinitePi`
(~/Lattice-Probability/LatticeProb/Prob/ZeroOne.lean:220) and its lattice-translation specialisation in
LatticeProb/Prob/Translation.lean prove ergodicity of i.i.d. product measures under coordinate shifts;
`aux_te_ergodic` should be a bridge from that to `ErgodicOn` (whose invariance clause is set-image based).
-/
theorem aux_te_piCongrLeft_addLeft (d : ℕ) (y : Site d) :
    (fun η : Site d → ℤ => fun z => η (y + z))
      = ⇑(MeasurableEquiv.piCongrLeft (fun _ : Site d => ℤ) (Equiv.addLeft y).symm) := by
  funext η z
  have h1 := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Site d => ℤ)
    (Equiv.addLeft y).symm η ((Equiv.addLeft y) z)
  rw [Equiv.symm_apply_apply] at h1
  rw [h1, Equiv.coe_addLeft]

theorem aux_te_stationary (d : ℕ) (ν' : Measure ℤ) :
    StationaryOn d (⊤ : AddSubgroup (Site d)) (Measure.infinitePi fun _ : Site d => ν') := by
  unfold StationaryOn
  intro y hy
  by_cases hν : IsProbabilityMeasure ν'
  · haveI : IsProbabilityMeasure ν' := hν
    rw [aux_te_piCongrLeft_addLeft d y]
    exact Measure.infinitePi_map_piCongrLeft (μ := fun _ : Site d => ν')
      (X := fun _ : Site d => ℤ) (Equiv.addLeft y).symm
  · have hne : ¬ ∀ i : Site d, IsProbabilityMeasure ((fun _ : Site d => ν') i) :=
      fun hh => hν (hh default)
    simp only [Measure.infinitePi, dif_neg hne, Measure.map_zero]


theorem aux_te_ergodic (d : ℕ) (ν' : Measure ℤ) (hν' : IsProbabilityMeasure ν') :
    ErgodicOn d (⊤ : AddSubgroup (Site d)) (Measure.infinitePi fun _ : Site d => ν') := by
  sorry

/-- Step 6 (assembly).  Combine Steps 2-5 to get `Exploding.Frozen.
explosion_criteria`'s hypotheses for the clamped measure `ν'` with
`L = ⊤`, `ηmin = d`; combine with `Exploding.Frozen.box_crossing` (cited
directly, since it needs no upper bound on `ν`) applied to `ν'` (Step 2 gives
`ν'` also satisfies `box_crossing`'s hypotheses) to get
`BoxCrossingHyp d P'`; apply `Exploding.Frozen.explosion_criteria` to
conclude `∀ᵐ η' ∂P', Explosive η'`; transport back along the clamp coupling
of Step 2 and `aux_te_explosive_mono` (since the original `β ≥ β' =
min(β, 2d-1)` pointwise, for the SAME sample `β`) to conclude
`∀ᵐ β ∂(infinitePi ν), Explosive β`.  Pure bookkeeping given Steps 1-5; not
attempted here since it inherits their `sorry`s. -/
theorem aux_te_assemble (d : ℕ) (hd : 2 ≤ d) (ν : Measure ℤ) (hν : IsProbabilityMeasure ν)
    (hlow : ν {m : ℤ | (d : ℤ) ≤ m} = 1) (hhit : 0 < ν {(2 * (d : ℤ) - 1)})
    (hSch : Exploding.External.SchonmannBootstrap) :
    ∀ᵐ β ∂(Measure.infinitePi fun _ : Site d => ν), Explosive β := by
  haveI : IsProbabilityMeasure ν := hν
  obtain ⟨ν', hν'prob, hν'low, hν'hit, hν'eq, hmap⟩ := aux_te_clamp_measure d ν hν hlow hhit
  haveI : IsProbabilityMeasure ν' := hν'prob
  have hupper : ν' {m : ℤ | m ≤ 2 * (d : ℤ) - 1} = 1 := (by
    rw [hν'eq]
    change (Measure.map (fun m : ℤ => min m (2 * (d : ℤ) - 1)) ν) (Set.Iic (2 * (d : ℤ) - 1)) = 1
    rw [Measure.map_apply (f := fun m : ℤ => min m (2 * (d : ℤ) - 1)) (measurable_id.min measurable_const) measurableSet_Iic]
    rw [show (fun m : ℤ => min m (2 * (d : ℤ) - 1)) ⁻¹' Set.Iic (2 * (d : ℤ) - 1) = Set.univ from Set.eq_univ_iff_forall.mpr (fun m => min_le_right m _)]
    simp)
  haveI hinst : ∀ i : Site d, IsProbabilityMeasure ((fun _ : Site d => ν') i) := fun _ => hν'prob
  have hP'prob : IsProbabilityMeasure (Measure.infinitePi fun _ : Site d => ν') := inferInstance
  have hPt : ∀ᵐ η ∂(Measure.infinitePi fun _ : Site d => ν'), InOmega d (d : ℤ) η := (by
    have ha1 := aux_ae_prod d ν' hν'prob (fun m : ℤ => (d : ℤ) ≤ m) measurableSet_Ici hν'low
    have ha2 := aux_ae_prod d ν' hν'prob (fun m : ℤ => m ≤ 2 * (d : ℤ) - 1) measurableSet_Iic hupper
    filter_upwards [ha1, ha2] with η h1' h2'
    intro x
    exact ⟨h1' x, h2' x⟩)
  have hbox : BoxCrossingHyp d (Measure.infinitePi fun _ : Site d => ν') := Exploding.Frozen.box_crossing d hd ν' hν'prob hν'low hν'hit hSch
  have hstat : StationaryOn d (⊤ : AddSubgroup (Site d)) (Measure.infinitePi fun _ : Site d => ν') := aux_te_stationary d ν'
  have herg : ErgodicOn d (⊤ : AddSubgroup (Site d)) (Measure.infinitePi fun _ : Site d => ν') := aux_te_ergodic d ν' hν'prob
  have hrange : FiniteRangeOfDependence d (Measure.infinitePi fun _ : Site d => ν') := aux_te_finite_range d ν' hν'prob
  have hrec : RecurrentLaw d (Measure.infinitePi fun _ : Site d => ν') := aux_te_recurrent_law d (by omega) ν' hν'prob hν'low hupper
  have hlaw : ExplosiveLaw d (Measure.infinitePi fun _ : Site d => ν') := Exploding.Frozen.explosion_criteria d hd (d : ℤ) (Int.natCast_nonneg d) (⊤ : AddSubgroup (Site d)) (by rw [AddSubgroup.index_top]; norm_num) (Measure.infinitePi fun _ : Site d => ν') hP'prob hPt hstat herg hrange hbox hrec
  have hlaw' : ∀ᵐ η ∂(Measure.map (fun β : Site d → ℤ => fun x => min (β x) (2 * (d : ℤ) - 1)) (Measure.infinitePi fun _ : Site d => ν)), Explosive η := (by
    rw [hmap]
    exact hlaw)
  have hmeas : AEMeasurable (fun β : Site d → ℤ => fun x => min (β x) (2 * (d : ℤ) - 1)) (Measure.infinitePi fun _ : Site d => ν) := (measurable_pi_iff.mpr fun x => (measurable_pi_apply x).min measurable_const).aemeasurable
  have hae := ae_of_ae_map hmeas hlaw'
  filter_upwards [hae] with β hβ
  exact aux_te_explosive_mono (fun x => min_le_left _ _) hβ


end Exploding.Frozen.ExplosiveDec

open Exploding LatticeProb MeasureTheory
