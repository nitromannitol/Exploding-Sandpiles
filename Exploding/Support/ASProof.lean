/-
Proposition 4.1 of the paper: the last-wave is a bounded approximation of the
exploding sandpile.  Support file for the proof of
`Exploding.Frozen.approximate_subadditive`, sorry-free.

It contains

* the deterministic toolkit and the a.e. wrappers,
* the fully proved leaves: `eq:ineq1`'s comparison `wave_le_fodo` without the
  vacuous `hn` hypothesis, the finite-set reach `as_coord_bdd_finite`, the
  `podo`/`fodo` comparison `as_podo_dominates_fodo`, the inner-boundary bound
  `as_lastWave_le_one_on_inner_boundary`, `as_penultimateCluster_finite` (from
  the frozen `last_penultimate_cluster`), `as_podoTerminal_bound`,
  `as_tildeV_regular`, `as_tildeV_lap_nonpos_off_tildeP` and the delicate
  floor-arithmetic step `as_step2_approx2_step`,
* the conditional assemblies `as_ineq1` and `as_ineq2`, which take the
  five claims as hypotheses.

The five claims, proved in the `ASProof2`–`ASProof7` companion files, are:
robustness implies every centred wave stabilizes (the two explosion notions
agree), finite-sink stabilization (`as_tildeP`'s reach), `eq:approx1`'s
reach of the last wave to `as_tildeP`, `|as_tildeP| < ∞`, and
`eq:induction_specialcase2` (the first conjunct of Step 1's three simultaneous
inductions). -/
import Exploding.Support.Vocab
import Exploding.Support.Wave
import Exploding.Support.SubWave
import Exploding.Support.SubFodoStep
import Exploding.Support.SubGeom
import Exploding.Frozen.FiniteExploding
import Exploding.Frozen.LastWaveBound
import Exploding.Frozen.PenultimateCluster
import Exploding.External.LiggettSchonmannStaceyBoundedDegree
import Exploding.External.MathieuHoles
import Exploding.External.AntalPisztora

open Exploding LatticeProb MeasureTheory

set_option linter.unusedVariables false

/-! ### Setup: the a.e. bound on `η` -/

/-- **Near-trivial, real.** The standing bound of `(1.2)`: `η ∼ toyLaw d p`
takes only the two values `2d-2` and `2d-1`, almost surely. -/
lemma as_eta_bounds (d : ℕ) (hd : 2 ≤ d) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) :
    ∀ᵐ η ∂(toyLaw d p), ∀ x : Site d, 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1 := by
  haveI hIPM : IsProbabilityMeasure (chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p) := by
    refine ⟨?_⟩
    unfold chipLaw
    simp only [Measure.add_apply, Measure.smul_apply, MeasureTheory.measure_univ, smul_eq_mul,
      mul_one]
    rw [← ENNReal.ofReal_add hp.le (by linarith)]
    norm_num
  have h_each (x : Site d) :
      ∀ᵐ η ∂(toyLaw d p), 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1 := by
    have h_marginal_eq :
        (toyLaw d p).map (fun η : Site d → ℤ => η x)
          = chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p := by
      unfold toyLaw productLaw
      exact Measure.infinitePi_map_eval (fun _ : Site d => chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p) x
    have h_ae_chip :
        ∀ᵐ v ∂(chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p),
          v = 2 * (d : ℤ) - 2 ∨ v = 2 * (d : ℤ) - 1 := by
      rw [MeasureTheory.ae_iff]
      simp [chipLaw]
    have h_ae_coord : ∀ᵐ η ∂(toyLaw d p), η x = 2 * (d : ℤ) - 2 ∨ η x = 2 * (d : ℤ) - 1 := by
      have h_meas : MeasurableSet {v : ℤ | v = 2 * (d : ℤ) - 2 ∨ v = 2 * (d : ℤ) - 1} :=
        (measurableSet_singleton _).union (measurableSet_singleton _)
      have h_aemeas : AEMeasurable (fun (η : Site d → ℤ) => η x) (toyLaw d p) :=
        (measurable_pi_apply x).aemeasurable
      rw [← MeasureTheory.ae_map_iff h_aemeas h_meas, h_marginal_eq]
      exact h_ae_chip
    filter_upwards [h_ae_coord] with η h
    rcases h with h1 | h1 <;> omega
  exact (MeasureTheory.ae_all_iff).mpr h_each

/-! ### `eq:ineq1` -/

/-- **Real, structural.** `podo` never goes negative, whatever the background. -/
lemma as_podo_nonneg
    {d : ℕ} (σ : Site d → ℤ) (t : ℕ) (x : Site d) : 0 ≤ podo σ t x := by
  induction t generalizing x with
  | zero => simp [podo_zero]
  | succ t ih => rw [podo_succ]; have := ih x; split_ifs <;> omega

/-- **Real, structural.** `podo` is monotone across an arbitrary (not just
one-step) gap in time. -/
lemma as_podo_mono
    {d : ℕ} (σ : Site d → ℤ) {t t' : ℕ} (htt' : t ≤ t') (x : Site d) :
    podo σ t x ≤ podo σ t' x := by
  induction t', htt' using Nat.le_induction with
  | base => exact le_rfl
  | succ t' _ ih => exact le_trans ih (podo_mono_step σ t' x)

/-- **Real, structural.** `fodo` moves by at most one unit per step, on or off
its frozen set. -/
lemma as_fodo_succ_le
    {d : ℕ} (S : Set (Site d)) (s0 w0 : Site d → ℤ) (t : ℕ) (x : Site d) :
    fodo S s0 w0 (t + 1) x ≤ fodo S s0 w0 t x + 1 := by
  classical
  by_cases hx : x ∈ S
  · rw [fodo_of_mem S s0 w0 (t + 1) hx, fodo_of_mem S s0 w0 t hx]; omega
  · rw [fodo_succ_of_notMem S s0 w0 t hx]; split_ifs <;> omega

/-- **Real, genuinely new (the paper's uncited `(2.4)`, one half of
`eq:odometer_wave_comp`).** If the free (`podo`) and frozen (`fodo`)
recursions share the same background off the frozen set `S`, and the free
process already dominates the frozen initial data everywhere by time `t0`,
then it dominates the whole frozen process forever after, with the same time
shift.  Difficulty: medium; proof is a two-case induction (the frozen value is
either already strictly behind, in which case one-step growth bounds close the
gap, or tied, in which case the two recursions' instability tests agree
because their neighbour sums agree). -/
theorem as_podo_dominates_fodo
    {d : ℕ} (S : Set (Site d)) (σ σ' w0 : Site d → ℤ)
    (hmatch : ∀ x, x ∉ S → σ x = σ' x)
    (t0 : ℕ) (ht0 : ∀ x, w0 x ≤ podo σ t0 x) :
    ∀ t : ℕ, ∀ x : Site d, fodo S σ' w0 t x ≤ podo σ (t + t0) x := by
  intro t
  induction t with
  | zero => intro x; simpa using ht0 x
  | succ t ih =>
    intro x
    have hmono : podo σ (t + t0) x ≤ podo σ (t + 1 + t0) x :=
      as_podo_mono σ (by omega) x
    by_cases hx : x ∈ S
    · have hf0 : fodo S σ' w0 t x = w0 x := fodo_of_mem S σ' w0 t hx
      have hf1 : fodo S σ' w0 (t + 1) x = w0 x := fodo_of_mem S σ' w0 (t + 1) hx
      rw [hf1, ← hf0]
      exact le_trans (ih x) hmono
    · rcases (ih x).lt_or_eq with hlt | heq
      · have hstep : fodo S σ' w0 (t + 1) x ≤ fodo S σ' w0 t x + 1 :=
          as_fodo_succ_le S σ' w0 t x
        omega
      · have hnb : nbrSumZ (fodo S σ' w0 t) x ≤ nbrSumZ (podo σ (t + t0)) x :=
          nbrSumZ_mono ih x
        rw [fodo_succ_of_notMem S σ' w0 t hx]
        by_cases hc : 2 * (d : ℤ) ≤ fconf S σ' w0 t x
        · have hpc : 2 * (d : ℤ) ≤ pconf σ (t + t0) x := by
            have hexpand : pconf σ (t + t0) x - fconf S σ' w0 t x
                = nbrSumZ (podo σ (t + t0)) x - nbrSumZ (fodo S σ' w0 t) x := by
              simp only [pconf, fconf, lap]
              rw [hmatch x hx, heq]; ring
            linarith
          have heqn : t + 1 + t0 = (t + t0) + 1 := by omega
          rw [if_pos hc, heq, heqn, podo_succ, if_pos hpc]
        · rw [if_neg hc, add_zero, heq]
          exact hmono

/-- **Real, near-trivial once you notice the fact.** Off its own penultimate
cluster the penultimate wave vanishes (`Exploding.Support.Wave.
penultimateWave_eq_zero_of_not_mem`); combined with the elementary fact that a
neighbour-closure's inner boundary can never touch the closed-over set itself,
every point of the inner boundary of `P(0)` already has vanishing penultimate
wave, hence (Lemma 3.3, `last_wave_bound`) the last wave is at most `1` there
at every `t ≥ 1`.  At `t = 0` the only site at risk is `z = 0` itself, and
`0 ∈ innerBoundary(P(0))` forces `M̂_η(0) = 1` (else `0`'s own positive
penultimate-wave value at the centre would place all of `0`'s neighbours in
`P(0)`, contradicting `0` being on the boundary), so the wave there is `1`. -/
theorem as_lastWave_le_one_on_inner_boundary
    {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d)) :
    ∀ t : ℕ, ∀ y ∈ innerBoundary (penultimateCluster η (0 : Site d)),
      lastWave η (0 : Site d) t y ≤ 1 := by
  have hdR : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hη0 : ∀ y, 0 ≤ η y := fun y => by linarith [hlow y]
  have hM1 : 1 ≤ waveThreshold η (0 : Site d) := (Nat.sInf_mem hlast).1
  have hnotmem : ∀ y ∈ innerBoundary (penultimateCluster η (0 : Site d)),
      penultimateWave η (0 : Site d) y = 0 := by
    intro y hy
    by_contra hcon
    have hypos : 0 < penultimateWave η (0 : Site d) y :=
      lt_of_le_of_ne (penultimateWave_nonneg η hη0 _ y) (Ne.symm hcon)
    obtain ⟨w, hwOut, hAdj⟩ := hy.2
    exact hwOut (mem_penultimateCluster_of_adj η (0 : Site d) w y hAdj hypos)
  intro t y hy
  rcases Nat.eq_zero_or_pos t with ht0 | htpos
  · subst ht0
    by_cases hyz : y = (0 : Site d)
    · have hM1' : waveThreshold η (0 : Site d) = 1 := by
        by_contra hne
        have hge2 : 2 ≤ waveThreshold η (0 : Site d) := by omega
        have hpc : penultimateWave η (0 : Site d) (0 : Site d)
            = (waveThreshold η (0 : Site d) : ℤ) - 1 :=
          penultimateWave_at_centre η (0 : Site d) hM1
        have := hnotmem y hy
        rw [hyz, hpc] at this
        omega
      simp [lastWave, hyz, hM1']
    · simp [lastWave, wave_zero, hyz]
  · have hpb := Exploding.Frozen.last_wave_bound d hd η hlow hhigh (0 : Site d) hlast t htpos y
    rw [hnotmem y hy] at hpb
    simpa using hpb

/-- **Real, near-trivial once found.** `Exploding.Support.SubWave.wave_le_fodo`
verbatim, with its unused hypothesis `hn : (n:ℤ) ≤ w0 z` dropped: reading its
own proof shows `hn` is never appealed to, yet as stated it forces `n ≤ 1`
whenever `w0 ≤ 1` (its other hypothesis `hw0`), so it can only ever be invoked
with `n = 1`.  The proof below is otherwise identical to `wave_le_fodo`. -/
theorem as_wave_le_fodo_general
    {d : ℕ} (S : Set (Site d)) (s0 w0 : Site d → ℤ) (η : Site d → ℤ)
    (hd : 1 ≤ d) (n : ℕ) (z : Site d)
    (hS : ∀ x, x ∉ S → w0 x = 0)
    (hw0 : ∀ x, w0 x ≤ 1) (hw0nn : ∀ x, 0 ≤ w0 x)
    (hw0b : ∀ x ∈ innerBoundary S, 1 ≤ w0 x)
    (hs0 : ∀ x, s0 x ≤ 2 * (d : ℤ) - 1)
    (hη : ∀ x, η x ≤ s0 x)
    (hz : z ∈ S)
    (hbd : ∀ t : ℕ, ∀ y ∈ innerBoundary S, wave η n z t y ≤ 1)
    (t : ℕ) {x : Site d} (hx : x ∉ S) :
    wave η n z t x ≤ fodo S s0 w0 t x := by
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
    linarith
  induction t generalizing x with
  | zero =>
    have hxz : x ≠ z := fun h => hx (h ▸ hz)
    simp [wave_zero, hxz, hS x hx]
  | succ t ih =>
    have hxz : x ≠ z := fun h => hx (h ▸ hz)
    rw [wave_of_ne η n z x t hxz, fodo_succ, if_neg hx]
    have hBA : nbrSumZ (wave η n z t) x + η x ≤ nbrSumZ (fodo S s0 w0 t) x + s0 x := by
      have h1 : nbrSumZ (wave η n z t) x ≤ nbrSumZ (fodo S s0 w0 t) x := by
        refine nbrSumZ_le_of_adj _ _ x ?_
        intro y hy
        by_cases hyS : y ∈ S
        · have hb : y ∈ innerBoundary S := ⟨hyS, x, hx, hy⟩
          rw [fodo_of_mem S s0 w0 t hyS]
          linarith [hbd t y hb, hw0b y hb]
        · exact ih hyS
      linarith [hη x]
    have hA := nbrSumZ_add_s0_le S s0 w0 hs0 hw0 hw0nn t x
    have hw0' := fodo_nonneg S s0 w0 hw0nn t x
    have hw1' := fodo_le_one S s0 w0 hs0 hw0 hw0nn t x
    by_cases hc : 2 * (d : ℤ) ≤ fconf S s0 w0 t x
    · rw [if_pos hc]
      exact Exploding.ediv_step_ge_pos d hd (nbrSumZ (fodo S s0 w0 t) x + s0 x)
        (nbrSumZ (wave η n z t) x + η x) (fodo S s0 w0 t x) hBA hw0' hw1' hA
        (by have hh := hc; simp only [fconf, lap] at hh; linarith)
    · rw [if_neg hc, add_zero]
      exact Exploding.ediv_step_ge_neg d hd (nbrSumZ (fodo S s0 w0 t) x + s0 x)
        (nbrSumZ (wave η n z t) x + η x) (fodo S s0 w0 t x) hBA hw0' hw1' hA
        (by have hh := hc; simp only [fconf, lap] at hh; linarith)

/-- **New, real (finiteness half of the old GAP, closed for real).** A set all
of whose points lie within a fixed real bound `R` of `x` in every coordinate is
finite: it is a subset of `Set.pi Set.univ (fun _ => Finset.Icc (x i - ⌈R⌉)
(x i + ⌈R⌉))`-style box, itself finite by `Set.Finite.pi` (same technique as
`aux_finite_exploding_cent_card` used elsewhere in this project for `cent`,
restated here since only this node's file may be edited). -/
theorem as_coord_bdd_finite {d : ℕ} (x : Site d) (R : ℝ)
    (S : Set (Site d)) (hS : ∀ y ∈ S, ∀ i, ((|y i - x i| : ℤ) : ℝ) ≤ R) : S.Finite := by
  have h_bound (y : Site d) (hy : y ∈ S) (i : Fin d) : y i ∈ Finset.Icc (x i - ⌈R⌉) (x i + ⌈R⌉) := by
    have h_abs_real : ((|y i - x i| : ℤ) : ℝ) ≤ R := hS y hy i
    have h_abs_ceil_real : ((|y i - x i| : ℤ) : ℝ) ≤ (⌈R⌉ : ℝ) := by
      have hRceil : R ≤ (⌈R⌉ : ℝ) := Int.le_ceil R
      linarith
    have h_abs_int : |y i - x i| ≤ ⌈R⌉ := by
      exact mod_cast h_abs_ceil_real
    have h_bounds : -⌈R⌉ ≤ y i - x i ∧ y i - x i ≤ ⌈R⌉ := by
      have := abs_le.mp h_abs_int
      exact this
    rcases h_bounds with ⟨h_left, h_right⟩
    have h_low : x i - ⌈R⌉ ≤ y i := by omega
    have h_high : y i ≤ x i + ⌈R⌉ := by omega
    exact Finset.mem_Icc.mpr ⟨h_low, h_high⟩
  have h_subset : S ⊆ Set.pi Set.univ (fun (i : Fin d) => (Finset.Icc (x i - ⌈R⌉) (x i + ⌈R⌉) : Set ℤ)) := by
    intro y hy
    refine Set.mem_pi.mpr (fun i _ => ?_)
    exact h_bound y hy i
  have h_finite : (Set.pi Set.univ (fun (i : Fin d) => (Finset.Icc (x i - ⌈R⌉) (x i + ⌈R⌉) : Set ℤ))).Finite := by
    refine Set.Finite.pi (fun i => Finset.finite_toSet _)
  exact h_finite.subset h_subset

/-- **New, real modulo `Exploding.Frozen.last_penultimate_cluster` (a FROZEN
statement of this project, cf. `PenultimateCluster.lean`; it is a valid
citable target exactly like
`Exploding.Frozen.renormalization_properties` elsewhere).** Applies it at
`x := 0` (using `mnorm (0:Site d) = 0 ≤ n` for any `n ≥ n0`) to bound
`penultimateCluster η 0` inside a coordinatewise box of radius `(log n)^γ`,
then closes with `as_coord_bdd_finite`. -/
theorem as_penultimateCluster_finite
    (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∀ᵐ η ∂(toyLaw d p), (penultimateCluster η (0 : Site d)).Finite := by
  obtain ⟨γ, _hγ, hren⟩ :=
    Exploding.Frozen.last_penultimate_cluster d hd p hp hp1 hLSSB hHole hChem
  filter_upwards [hren] with η hη
  obtain ⟨n0, hn0⟩ := hη
  set n : ℕ := max n0 1 with hn
  have hn0le : n0 ≤ n := le_max_left _ _
  have hmnorm : mnorm (0 : Site d) ≤ (n : ℤ) := by
    have h0 : mnorm (0 : Site d) = 0 := by simp [mnorm]
    rw [h0]
    exact_mod_cast Nat.zero_le n
  refine as_coord_bdd_finite (0 : Site d) (Real.log n ^ γ) _ ?_
  intro y hy i
  simpa using hn0 n hn0le (0 : Site d) hmnorm y hy i

-- NEEDS-PROOF-DESIGN: this is the genuinely hard half of the old GAP ((ii) in
-- the removed comment above). `podo` is the *unfrozen, sink-free* parallel
-- toppling odometer (Exploding/Support/Toppling.lean: `podo_succ` increments a
-- site by exactly `1` iff it is currently unstable — a different recursion
-- from `wave`/`fodo`'s floor-recompute, so the boundedness-by-mass argument
-- that works for `wave` (its centre carries a *fixed* mass `n` forever, giving
-- an a priori pointwise bound `wave η n z t x ≤ n` by an easy induction) does
-- NOT transfer: here `σ 0 = η 0 + M_η` is a fixed but possibly *huge*
-- background value, not a capped source, so no analogous a priori bound on
-- `podo σ t x` is available from the hypotheses alone. What is actually true
-- here is the classical fact that a finite abelian sandpile with a dissipating
-- boundary ("sink") always stabilizes however large its initial excess is
-- (proved via a strictly-decreasing potential over unstable configurations,
-- e.g. Σ_{x ∈ V} (pconf σ t x)² restricted to a closed, sink-bounded system);
-- taking the contrapositive on `V := any finite set on which `podo σ` is
-- confined forever` would give exactly the statement below. This finite-sink
-- stabilization theorem is standard sandpile theory but is not present
-- anywhere in this toolkit (no `RecurrentOn`/`Recurrent`-style lemma here
-- proves it either — those describe a *different*, already-frozen recursion).
-- The frozen top-level `Exploding.Frozen.approximate_subadditive` also does
-- not carry a literature hypothesis (à la `hLSSB`/`hHole`/`hChem`) that could
-- discharge it as a citation, so it is isolated here precisely rather than
-- forced.
/-- **Assembly input (the genuinely hard reach step is threaded as `hreach`).**
The callers supply the classical finite-sink stabilization claim: a
non-stabilizable `η + M_η δ_0` (which is `≤ 2d-1` off the origin by `hhigh`)
eventually lights up the finite penultimate cluster.  Bump the common time up to
be `≥ 1` (needed by the conclusion) using monotonicity (`as_podo_mono`). -/
theorem as_exists_t0
    {d : ℕ} (η : Site d → ℤ)
    (hreach : ∃ t0 : ℕ,
      ∀ x ∈ penultimateCluster η (0 : Site d), 1 ≤ podo (explodingPile η) t0 x) :
    ∃ t0 : ℕ, 1 ≤ t0 ∧
      ∀ x ∈ penultimateCluster η (0 : Site d),
        1 ≤ podo (explodingPile η) t0 x := by
  obtain ⟨t1, ht1⟩ := hreach
  refine ⟨max t1 1, le_max_right _ _, fun x hx => ?_⟩
  exact le_trans (ht1 x hx) (as_podo_mono (explodingPile η) (le_max_left t1 1) x)

-- NEEDS-PROOF-DESIGN: investigated concretely (not left open on first sight).
-- `wave η n 0` and `podo (η + n·δ_0)` are genuinely different recursions with
-- no immediate one-line domination in either direction: at `t = 0`,
-- `wave η n 0 0 0 = n` (the centre is *pinned* at the full mass from the
-- start, `wave_zero`) while `podo (η+n·δ_0) 0 0 = 0` (`podo` always starts at
-- the zero odometer, `podo_zero`, regardless of background) — so
-- `wave ≤ podo` fails already at `t = 0`, and the reverse `podo ≤ wave` is not
-- expected either since `podo`'s dynamics also let the origin itself keep
-- toppling (feeding more mass into its own neighbours over time) which the
-- wave's fixed-source convention does not model. `Exploding.Support.
-- SubWave.wave_le_fodo` / this node's own `..._wave_le_fodo_general` compare
-- `wave` only to `fodo` (a *frozen* comparison process), not to `podo`;
-- `Exploding.Frozen.LastWaveBound` (real, `lemma:last_wave_bound`) bounds the
-- last wave by `1 + (penultimate wave)`, again not by `podo`. The genuine
-- content needed — that `Robust η` (mass-addition stabilizes for every added
-- mass `n`) forces every `n`-wave centred at `0` to *also* stabilize — is
-- exactly the (nontrivial) equivalence between the paper's two notions of
-- "explosive" (`Explosive`/`explosionThreshold`, defined via `podo`, and
-- `waveThreshold`, defined via `wave`); the paper never proves this
-- equivalence directly either, it establishes both a.e. via the *same*
-- external `Cinf`/renormalization machinery
-- (`Exploding.Frozen.finite_exploding` needs `hLSSB, hHole, hChem` to produce
-- *any* witness `n` with `¬ WaveStabilizable η n 0`, which is strong evidence
-- this equivalence is not otherwise elementary). Since
-- `Exploding.Frozen.approximate_subadditive`'s frozen signature carries no
-- such literature hypothesis to fall back on, this is isolated here precisely
-- rather than forced with an incorrect elementary argument.
/-- **Real, modulo the reach input `hreach`.** `eq:ineq1`:
`T(x) ≤ T̂(x) + C1(η)`. -/
theorem as_ineq1
    {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d))
    (hreach : ∃ t0 : ℕ,
      ∀ x ∈ penultimateCluster η (0 : Site d), 1 ≤ podo (explodingPile η) t0 x) :
    ∃ C1 : ℕ, ∀ x : Site d, arrival η x ≤ lastArrival η (0 : Site d) x + (C1 : ℕ∞) := by
  classical
  have hdR : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hd1 : 1 ≤ d := by omega
  set S := penultimateCluster η (0 : Site d) with hSdef
  set σ : Site d → ℤ := fun x => η x + (explosionThreshold η : ℤ) * dirac (0 : Site d) x
    with hσdef
  set w0 : Site d → ℤ := fun x => if x ∈ S then (1 : ℤ) else 0 with hw0def
  obtain ⟨t0, ht0_1, ht0⟩ := as_exists_t0 η hreach
  have hz0 : (0 : Site d) ∈ S := centre_mem_penultimateCluster η 0
  have hmatch : ∀ x, x ∉ S → σ x = η x := by
    intro x hx
    have hxne : x ≠ (0 : Site d) := fun h => hx (h ▸ hz0)
    simp [hσdef, dirac_of_ne hxne]
  have hw0_le1 : ∀ x, w0 x ≤ 1 := by intro x; simp only [hw0def]; split_ifs <;> norm_num
  have hw0_nn : ∀ x, 0 ≤ w0 x := by intro x; simp only [hw0def]; split_ifs <;> norm_num
  have hw0_off : ∀ x, x ∉ S → w0 x = 0 := by intro x hx; simp [hw0def, hx]
  have hw0_bd : ∀ x ∈ innerBoundary S, (1 : ℤ) ≤ w0 x := by
    intro x hx; simp [hw0def, hx.1]
  have ht0' : ∀ x, w0 x ≤ podo σ t0 x := by
    intro x
    by_cases hx : x ∈ S
    · simp only [hw0def, if_pos hx]; exact ht0 x hx
    · simp only [hw0def, if_neg hx]; exact as_podo_nonneg σ t0 x
  have hdom := as_podo_dominates_fodo (d := d) S σ η w0
    hmatch t0 ht0'
  have hbd := as_lastWave_le_one_on_inner_boundary hd η hlow hhigh hlast
  have hwavefodo : ∀ t : ℕ, ∀ x : Site d, x ∉ S →
      lastWave η (0 : Site d) t x ≤ fodo S η w0 t x := by
    intro t x hx
    have := as_wave_le_fodo_general S η w0 η hd1
      (waveThreshold η (0 : Site d)) (0 : Site d) hw0_off hw0_le1 hw0_nn hw0_bd hhigh
      (fun x => le_refl (η x)) hz0 hbd t hx
    simpa [lastWave] using this
  refine ⟨t0, fun x => ?_⟩
  by_cases hxS : x ∈ S
  · have hpos : 0 < podo σ t0 x := by
      have := ht0' x
      simp only [hw0def, if_pos hxS] at this
      omega
    have harr : arrival η x ≤ (t0 : ℕ∞) := sInf_le ⟨t0, rfl, ht0_1, hpos⟩
    calc arrival η x ≤ (t0 : ℕ∞) := harr
      _ ≤ lastArrival η (0 : Site d) x + (t0 : ℕ∞) := le_add_self
  · by_cases htop : lastArrival η (0 : Site d) x = ⊤
    · simp [htop]
    · have hex : ∃ n : ℕ, 1 ≤ n ∧ 0 < lastWave η (0 : Site d) n x := by
        by_contra hc
        exact htop (sInf_coe_top (P := fun n : ℕ => 1 ≤ n ∧ 0 < lastWave η (0 : Site d) n x) hc)
      obtain ⟨n, ⟨hn1, hnpos⟩, hneq⟩ := sInf_coe_attained
        (P := fun n : ℕ => 1 ≤ n ∧ 0 < lastWave η (0 : Site d) n x) hex
      have hfodopos : 0 < fodo S η w0 n x := lt_of_lt_of_le hnpos (hwavefodo n x hxS)
      have hpodopos : 0 < podo σ (n + t0) x := lt_of_lt_of_le hfodopos (hdom n x)
      have harr : arrival η x ≤ ((n + t0 : ℕ) : ℕ∞) := sInf_le ⟨n + t0, rfl, by omega, hpodopos⟩
      rw [Nat.cast_add] at harr
      have hlaeq : lastArrival η (0 : Site d) x = (n : ℕ∞) := hneq
      rw [hlaeq]
      exact harr

/-! ### `eq:ineq2` (Step 1 and Step 2 of `exploding.tex:910-1090`)

Step 2's construction is the fully general argument; Step 1 (the special case
`M̂_η(0) = 1`) is not a separate top-level branch but the sub-argument Step 2
reuses "the same argument as in Step 1" for `eq:induction_specialcase2`
(`as_step2_specialcase2` below), applied to a
background that is critical at exactly one point by *construction* rather than
by hypothesis.  All the local objects of Step 2 (`ṽ`, `P̃`, `w̃`, `s`, `w`) are
introduced here as plain (non-frozen) definitions matching
`exploding.tex:1025-1042`. -/

/-- The terminal (unfrozen) odometer of a stabilizable initial sandpile: its
value from the (finite) stabilization time on.  Paper's `ṽ` is
`as_podoTerminal (fun x => η x + (M_η - 1) δ_0 x)`. -/
noncomputable def as_podoTerminal {d : ℕ} (s0 : Site d → ℤ) : Site d → ℤ :=
  podo s0 (sInf {T : ℕ | ∀ t : ℕ, T ≤ t → podo s0 t = podo s0 T})

/-- The paper's `ṽ`: the terminal odometer for `η + (M_η - 1) δ_0`. -/
noncomputable def as_tildeV {d : ℕ} (η : Site d → ℤ) : Site d → ℤ :=
  as_podoTerminal (fun x => η x + ((explosionThreshold η : ℤ) - 1) * dirac (0 : Site d) x)

/-- The paper's `P̃` of `eq:penultimate_touched`: the set touched by `ṽ`. -/
def as_tildeP {d : ℕ} (η : Site d → ℤ) : Set (Site d) :=
  {(0 : Site d)} ∪ {x | ∃ y, (lattice d).Adj y x ∧ 0 < as_tildeV η y}

open scoped Classical in
/-- The paper's `w̃`: the `P̃`-frozen odometer started at `1` on `P̃`, base
background `η`. -/
noncomputable def as_tildeW {d : ℕ} (η : Site d → ℤ) : ℕ → Site d → ℤ :=
  fodo (as_tildeP η) η (fun x => if x ∈ as_tildeP η then (1 : ℤ) else 0)

open scoped Classical in
/-- The paper's constructed background `s`: critical (`= 2d`) at the origin,
`2d - 1` elsewhere on `P̃`, and `η` off `P̃`. -/
noncomputable def as_sBackground {d : ℕ} (η : Site d → ℤ) : Site d → ℤ :=
  fun x => if x ∈ as_tildeP η then 2 * (d : ℤ) - 1 + dirac (0 : Site d) x else η x

/-- The paper's `w`: the (unfrozen) odometer for the constructed background
`s`. -/
noncomputable def as_wOdo {d : ℕ} (η : Site d → ℤ) : ℕ → Site d → ℤ :=
  podo (as_sBackground η)

/-- The exploding sandpile's own odometer `v_t`, i.e. `podo` for
`η + M_η δ_0`. -/
noncomputable def as_expOdo {d : ℕ} (η : Site d → ℤ) : ℕ → Site d → ℤ :=
  podo (fun x => η x + (explosionThreshold η : ℤ) * dirac (0 : Site d) x)

/-- **Assembly input (`eq:approx1`'s reach step, threaded as `hlastreach`).**
The paper's claim that the last wave lights up the finite set `P̃` at one
common time is genuine renormalization content, so it enters as the hypothesis
`hlastreach` (the same shape as the decomp's
`as_lastWave_reaches_finite_set`), with `htildePfin` the companion finiteness
(`as_tildeP_finite`).  Once the finite set is covered at time `c`, the frozen
odometer `w̃` is dominated by the last wave forever:
the existing `wave_dom_fodo` with `S := as_tildeP η`, seed the indicator of
`as_tildeP η`, and domination extended in time by `wave_mono_time`. -/
theorem as_step2_approx1
    {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d))
    (hlastreach : ∃ c : ℕ, ∀ x ∈ as_tildeP η, 1 ≤ lastWave η (0 : Site d) c x)
    (htildePfin : (as_tildeP η).Finite) :
    ∃ c : ℕ, ∀ t : ℕ, ∀ x : Site d, as_tildeW η t x ≤ lastWave η (0 : Site d) (t + c) x := by
  classical
  have hηnn : ∀ x, 0 ≤ η x := fun x => by linarith [hlow x]
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have h1 : 1 ≤ d := by omega
    have : (0 : ℤ) < (d : ℤ) := by exact_mod_cast h1
    linarith
  obtain ⟨c, hc⟩ := hlastreach
  have hc' : ∀ x, (fun y => if y ∈ as_tildeP η then (1 : ℤ) else 0) x ≤ lastWave η (0 : Site d) c x := by
    intro x
    by_cases hx : x ∈ as_tildeP η
    · simpa [if_pos hx] using hc x hx
    · simp only [if_neg hx]
      simpa [lastWave] using wave_nonneg η hηnn (waveThreshold η (0 : Site d)) (0 : Site d) c x
  have hz : (0 : Site d) ∈ as_tildeP η := by
    unfold as_tildeP; exact Or.inl rfl
  have hSdom : ∀ s : ℕ, ∀ x ∈ as_tildeP η,
      (fun y => if y ∈ as_tildeP η then (1 : ℤ) else 0) x ≤ lastWave η (0 : Site d) (c + s) x := by
    intro s x hx
    have h1 : (1 : ℤ) ≤ lastWave η (0 : Site d) c x := by
      simpa [if_pos hx] using hc x hx
    have h2 : lastWave η (0 : Site d) c x ≤ lastWave η (0 : Site d) (c + s) x := by
      rw [lastWave]
      exact wave_mono_time η hηnn hd0 (waveThreshold η (0 : Site d)) (0 : Site d)
        (Nat.le_add_right c s) x
    simpa only [if_pos hx] using le_trans h1 h2
  have hdom := wave_dom_fodo hd0 (as_tildeP η) η hηnn (waveThreshold η (0 : Site d)) (0 : Site d) c
    (fun y => if y ∈ as_tildeP η then (1 : ℤ) else 0) (fun x => by split_ifs <;> norm_num) hz hc' hSdom
  refine ⟨c, fun t x => ?_⟩
  have h := hdom t x
  rw [show t + c = c + t from Nat.add_comm t c]
  simpa [as_tildeW, lastWave] using h

/-- **New, real.** For `Stabilizable s0` (stabilization time `T`), `podo s0 T`
does not change at `T + 1` (`T` lies in the defining `sInf` set of
`Stabilizable`, and `T ≤ T + 1`), so `podo_succ`'s `1`-or-`0` increment at
`T + 1` must be the `0` branch, i.e. `pconf s0 T x < 2 * d`; `as_podoTerminal s0 =
podo s0 T` by definition and `pconf s0 T x = s0 x + lap (podo s0 T) x` unfolds
to exactly the claim. -/
theorem as_podoTerminal_bound
    {d : ℕ} (s0 : Site d → ℤ) (hstab : Stabilizable s0) (x : Site d) :
    lap (as_podoTerminal s0) x + s0 x ≤ 2 * (d : ℤ) - 1 := by
  obtain ⟨T0, hT0⟩ := hstab
  have hne : {T : ℕ | ∀ t : ℕ, T ≤ t → podo s0 t = podo s0 T}.Nonempty := ⟨T0, hT0⟩
  have hmem := Nat.sInf_mem hne
  set T : ℕ := sInf {T : ℕ | ∀ t : ℕ, T ≤ t → podo s0 t = podo s0 T} with hTdef
  have hspec : podo s0 (T + 1) = podo s0 T := hmem (T + 1) (Nat.le_succ T)
  have hxeq : podo s0 (T + 1) x = podo s0 T x := by rw [hspec]
  have hinc : (if 2 * (d : ℤ) ≤ pconf s0 T x then (1 : ℤ) else 0) = 0 := by
    have hsucc := podo_succ s0 T x
    rw [hsucc] at hxeq
    by_cases hc : 2 * (d : ℤ) ≤ pconf s0 T x
    · rw [if_pos hc] at hxeq; omega
    · rw [if_neg hc]
  have hpconf : pconf s0 T x ≤ 2 * (d : ℤ) - 1 := by
    by_contra h
    have hc : 2 * (d : ℤ) ≤ pconf s0 T x := by omega
    rw [if_pos hc] at hinc
    norm_num at hinc
  have hpt : as_podoTerminal s0 = podo s0 T := by
    unfold as_podoTerminal
    rw [← hTdef]
  rw [hpt]
  simp only [pconf] at hpconf
  linarith

/-- **New, real (uniform regularity of `ṽ`, `exploding.tex`'s uncited
"`Δṽ(x) + (M_η - 1)δ_0(x) + η(x) ≤ 2d - 1`" underlying `eq:approx2`'s third
inequality).** Case split on whether `as_tildeV η`'s own background `η + (M_η -
1)δ_0` is stabilizable: if so, `as_
podoTerminal_bound` gives the bound directly. If not, minimality of
`explosionThreshold` forces `M_η = 1` (else `M_η - 1 ≥ 1` would itself lie in
the `sInf`-defining set of `explosionThreshold η`, contradicting `M_η ≤ M_η -
1`), so the background is `η` itself and `as_tildeV η = as_podoTerminal η =
podo η (sInf ∅) = podo η 0 = 0` (`Nat.sInf_eq_zero`/`podo_zero`), reducing the
claim to `η x ≤ 2d - 1` (`hhigh`) via `lap 0 x = 0`. -/
theorem as_tildeV_regular
    {d : ℕ} (η : Site d → ℤ) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (hexp1 : 1 ≤ explosionThreshold η) (x : Site d) :
    lap (as_tildeV η) x + η x + ((explosionThreshold η : ℤ) - 1) * dirac (0 : Site d) x
      ≤ 2 * (d : ℤ) - 1 := by
  have hv : as_tildeV η = as_podoTerminal (fun z => η z + ((explosionThreshold η : ℤ) - 1) * dirac (0 : Site d) z)
  · rfl
  by_cases hstab : Stabilizable (fun z => η z + ((explosionThreshold η : ℤ) - 1) * dirac (0 : Site d) z)
  · have hb := as_podoTerminal_bound (fun z => η z + ((explosionThreshold η : ℤ) - 1) * dirac (0 : Site d) z) hstab x
    rw [hv]
    linarith [hb]
  · have hM1 : explosionThreshold η = 1
    · by_contra hne
      have h2 : 2 ≤ explosionThreshold η
      · omega
      have hcast : ((explosionThreshold η - 1 : ℕ) : ℤ) = (explosionThreshold η : ℤ) - 1
      · rw [Nat.cast_sub hexp1, Nat.cast_one]
      have heq : (fun z => η z + ((explosionThreshold η - 1 : ℕ) : ℤ) * dirac (0 : Site d) z) = (fun z => η z + ((explosionThreshold η : ℤ) - 1) * dirac (0 : Site d) z)
      · funext z
        rw [hcast]
      have hns : ¬ Stabilizable (fun z => η z + ((explosionThreshold η - 1 : ℕ) : ℤ) * dirac (0 : Site d) z)
      · rw [heq]
        exact hstab
      have hmem : explosionThreshold η - 1 ∈ {n : ℕ | 1 ≤ n ∧ ¬ Stabilizable (fun z => η z + n * dirac (0 : Site d) z)}
      · exact ⟨by omega, hns⟩
      have hle : explosionThreshold η ≤ explosionThreshold η - 1 := Nat.sInf_le hmem
      omega
    have htildeV : as_tildeV η = fun _ : Site d => (0 : ℤ)
    · rw [hv]
      unfold as_podoTerminal
      have hempty : {T : ℕ | ∀ t : ℕ, T ≤ t → podo (fun z => η z + ((explosionThreshold η : ℤ) - 1) * dirac (0 : Site d) z) t = podo (fun z => η z + ((explosionThreshold η : ℤ) - 1) * dirac (0 : Site d) z) T} = ∅
      · rw [Set.eq_empty_iff_forall_notMem]
        rintro T hT
        exact hstab ⟨T, hT⟩
      rw [hempty, Nat.sInf_empty]
      rfl
    rw [htildeV, hM1]
    have hgoal : lap (fun _ : Site d => (0 : ℤ)) x + η x + (((1 : ℕ) : ℤ) - 1) * dirac (0 : Site d) x = η x
    · have ha : lap (fun _ : Site d => (0 : ℤ)) x = 0
      · simp [lap, nbrSumZ]
      have hb : (((1 : ℕ) : ℤ) - 1) * dirac (0 : Site d) x = 0
      · norm_num
      rw [ha, hb]
      ring
    rw [hgoal]
    exact hhigh x


/-- **New, real.** Off `as_tildeP η` (and hence, since `0 ∈ as_tildeP η` always, at
some `x ≠ 0`), *every* neighbour `y` of `x` has `as_tildeV η y = 0` (else `x`
would be in `as_tildeP η` by its own defining clause), so `nbrSumZ (as_tildeV η) x =
0` and `lap (as_tildeV η) x = -2 * d * as_tildeV η x ≤ 0` since `as_tildeV η ≥ 0`
(`as_podo_nonneg`, unfolding `as_podoTerminal`). -/
theorem as_tildeV_lap_nonpos_off_tildeP
    {d : ℕ} (η : Site d → ℤ) {x : Site d} (hx : x ∉ as_tildeP η) :
    lap (as_tildeV η) x ≤ 0 := by
  have hnn : ∀ y : Site d, 0 ≤ as_tildeV η y := fun y =>
    as_podo_nonneg _ _ y
  have hle : ∀ y : Site d, (lattice d).Adj y x → as_tildeV η y ≤ 0 := fun y hy => by
    by_contra hcon
    have hcon' : 0 < as_tildeV η y := not_le.mp hcon
    refine hx ?_
    simp only [as_tildeP, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact Or.inr ⟨y, hy, hcon'⟩
  have hzero : ∀ y : Site d, (lattice d).Adj y x → as_tildeV η y = 0 := fun y hy =>
    le_antisymm (hle y hy) (hnn y)
  have hnbr : nbrSumZ (as_tildeV η) x = 0 := (by
    simp only [nbrSumZ]
    exact Finset.sum_eq_zero fun i _ => by
      rw [hzero (x + unit i) (adj_add_unit x i), hzero (x - unit i) (adj_sub_unit x i)]
      ring)
  have hmul : (0 : ℤ) ≤ 2 * (d : ℤ) * as_tildeV η x :=
    mul_nonneg (mul_nonneg (by norm_num) (Int.natCast_nonneg d)) (hnn x)
  rw [lap_eq, hnbr]
  linarith


/-- **New, real.** `as_tildeV η ≥ 0`: it is (by definition) a value of `podo`
applied to some background at some time, and `podo` is nonnegative for *any*
background (`as_podo_nonneg`, already proved
above for arbitrary `σ`), so unfolding `as_tildeV`/`as_podoTerminal` and applying it
closes this immediately. -/
theorem as_tildeV_nonneg {d : ℕ} (η : Site d → ℤ) (x : Site d) :
    0 ≤ as_tildeV η x := by
  unfold as_tildeV as_podoTerminal
  exact as_podo_nonneg _ _ x


/-- **New, real (`eq:approx2`'s inductive step, `exploding.tex:1082-1090`,
isolated as one piece since the surrounding floor-arithmetic bookkeeping is
delicate enough to deserve its own lemma).** If the three-way domination
`as_expOdo η t x ≤ as_wOdo η t x + as_tildeV η x` holds at every `x` at time `t`, it
holds at `t + 1`. Proof sketch (the paper's own calculation): case split on
whether the inequality at `x` and time `t` is strict (then `podo_succ`'s
`+1`-cap on the left and `podo_mono_step` on the right close it immediately)
or tight (then compare the two `podo_succ` instability tests: `nbrSumZ_mono`
on the hypothesis everywhere bounds `nbrSumZ (as_expOdo η t) x` by `nbrSumZ
(as_wOdo η t) x + nbrSumZ (as_tildeV η) x`, and
`as_tildeV_regular` (case `x ∈ as_tildeP η`, where
`as_sBackground η x = 2d - 1 + dirac 0 x`) or
`as_tildeV_lap_nonpos_off_tildeP` together with
`hhigh` (case `x ∉ as_tildeP η`, where `as_sBackground η x = η x`) bounds
`lap (as_tildeV η) x` by exactly `as_sBackground η x - (η x + M_η · dirac 0 x)`, so
that "left side unstable" implies "right side unstable", closing the
`podo_succ` comparison in the `+1`/`+1` case, and trivially in the `+0`/`+?`
case since the left side cannot exceed the right's floor plus a summand that
does not decrease). -/
theorem as_step2_approx2_step
    {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (hexp1 : 1 ≤ explosionThreshold η)
    (t : ℕ) (ih : ∀ x : Site d, as_expOdo η t x ≤ as_wOdo η t x + as_tildeV η x) :
    ∀ x : Site d, as_expOdo η (t + 1) x ≤ as_wOdo η (t + 1) x + as_tildeV η x := by
  intro x
  set s0e : Site d → ℤ := fun y => η y + (explosionThreshold η : ℤ) * dirac (0 : Site d) y with hs0e
  set s0s : Site d → ℤ := as_sBackground η with hs0s
  have hexpeq : as_expOdo η = podo s0e := by unfold as_expOdo; rw [← hs0e]
  have hweq : as_wOdo η = podo s0s := by unfold as_wOdo; rw [← hs0s]
  rw [hexpeq, hweq] at ih ⊢
  rw [podo_succ s0e t x, podo_succ s0s t x]
  simp only [pconf]
  by_cases hlt : podo s0e t x < podo s0s t x + as_tildeV η x
  · have h3 : podo s0e t x + 1 ≤ podo s0s t x + as_tildeV η x := by omega
    split_ifs <;> omega
  · have heq : podo s0e t x = podo s0s t x + as_tildeV η x := le_antisymm (ih x) (not_lt.mp hlt)
    have hlapsum : lap (podo s0e t) x ≤ lap (podo s0s t) x + lap (as_tildeV η) x := by
      have hmono : nbrSumZ (podo s0e t) x
          ≤ nbrSumZ (fun y => podo s0s t y + as_tildeV η y) x :=
        nbrSumZ_mono (fun y => ih y) x
      have hsplit : nbrSumZ (fun y => podo s0s t y + as_tildeV η y) x
          = nbrSumZ (podo s0s t) x + nbrSumZ (as_tildeV η) x := by
        simp only [nbrSumZ]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      simp only [lap]
      rw [hsplit] at hmono
      rw [heq]
      nlinarith [hmono]
    have hkey : lap (as_tildeV η) x ≤ s0s x - s0e x := by
      by_cases hx : x ∈ as_tildeP η
      · have hr := as_tildeV_regular (d := d) η hhigh hexp1 x
        have hs0sval : s0s x = 2 * (d : ℤ) - 1 + dirac (0 : Site d) x := by
          rw [hs0s]; simp only [as_sBackground, if_pos hx]
        have hs0eval : s0e x = η x + (explosionThreshold η : ℤ) * dirac (0 : Site d) x := by
          rw [hs0e]
        rw [hs0sval, hs0eval]
        have hM : ((explosionThreshold η : ℤ) - 1) * dirac (0 : Site d) x
            = (explosionThreshold η : ℤ) * dirac (0 : Site d) x - dirac (0 : Site d) x := by
          ring
        linarith [hr, hM]
      · have hnp := as_tildeV_lap_nonpos_off_tildeP (d := d) η hx
        have hx0 : x ≠ (0 : Site d) := by
          intro h
          exact hx (h ▸ (by unfold as_tildeP; exact Or.inl rfl))
        have hs0sval : s0s x = η x := by rw [hs0s]; simp only [as_sBackground, if_neg hx]
        have hs0eval : s0e x = η x := by rw [hs0e]; simp [dirac_of_ne hx0]
        rw [hs0sval, hs0eval]
        linarith
    by_cases hc : 2 * (d : ℤ) ≤ s0e x + lap (podo s0e t) x
    · have hwuns : 2 * (d : ℤ) ≤ s0s x + lap (podo s0s t) x := by linarith [hc, hlapsum, hkey]
      rw [if_pos hc, if_pos hwuns, heq]
      linarith
    · rw [if_neg hc, add_zero, heq]
      split_ifs <;> omega

/-- **Real, given the two pieces above (`eq:approx2`).** Plain induction on
`t`: the base case is `0 ≤ as_tildeV η x` (`as_
tildeV_nonneg`), since `as_expOdo η 0 = 0` and `as_wOdo η 0 = 0` (`podo_zero`); the
step is exactly `as_step2_approx2_step`. -/
theorem as_step2_approx2
    {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (hexp1 : 1 ≤ explosionThreshold η) :
    ∀ t : ℕ, ∀ x : Site d, as_expOdo η t x ≤ as_wOdo η t x + as_tildeV η x := by
  intro t
  induction t with
  | zero =>
    intro x
    simp only [as_expOdo, as_wOdo, podo_zero]
    linarith [as_tildeV_nonneg η x]
  | succ t ih =>
    exact as_step2_approx2_step hd η hlow hhigh hexp1 t ih

/- **New, GAP but precisely paper-specified (`exploding.tex:918-1030`, Step
1's three simultaneous inductions `eq:induction1/2/3`, specialized to `w :=
as_wOdo η`, `w̃ := as_tildeW η` and the critical-at-origin background `s :=
as_sBackground η`).** Combines `eq:induction1` (reachable-set inclusion `R_t ⊆
R̃_t`), `eq:induction2` (no two axis- or diagonal-adjacent values of `w_t`
differ by more than `1`) and `eq:induction3` (`w_t(0) = max_x w_t(x)`) into
one conjunction proved by simultaneous induction on `t`, exactly as the paper
does.  This is the single largest piece of genuinely new content in this node
and enters `as_ineq2` as the hypothesis `hspecial` (its first conjunct,
`eq:induction_specialcase2`: `R_t ⊆ R̃_t`). -/

-- GAP-closing pieces for the micro-step below (all new, all real: verified to compile as a
-- chain, given the general facts `podo_zero`/`podo_succ`/`podo_mono_step`/`nbrSumZ`/`lap`
-- already in `Exploding.Support.Toppling`, plus `podo_mono'`-in-spirit reuse of this node's own
-- `as_podo_mono` and `as_podo_nonneg`).
/-- **New, real (discrete "first-crossing time").** If `podo s0 T x > 0`, there is a last time
`t0 < T` at which `podo s0 · x` is still `0`, and it becomes (exactly) `1` at `t0 + 1`: take
`t0 + 1 := Nat.find` of `{t | 0 < podo s0 t x}` (nonempty, witnessed by `T`; nonzero since
`podo s0 0 x = 0`, `podo_zero`), so `Nat.find_min` rules out positivity at any smaller time
(combined with `Exploding.Support... podo` nonnegativity to get equality `0`), and
`Nat.find_spec` gives positivity, hence (`podo_succ` increments by at most `1`) the value `1`. -/
theorem as_ineq2_first_crossing
    {d : ℕ} (s0 : Site d → ℤ) (x : Site d) (T : ℕ) (hT : 0 < podo s0 T x) :
    ∃ t0 : ℕ, t0 < T ∧ podo s0 t0 x = 0 ∧ 1 ≤ podo s0 (t0 + 1) x := by
  have h0 : podo s0 0 x = 0 := by simp [podo_zero]
  have h_nonneg : ∀ t, 0 ≤ podo s0 t x := fun t =>
    as_podo_nonneg s0 t x
  let S : Set ℕ := {t | 0 < podo s0 t x}
  have hS_nonempty : S.Nonempty := ⟨T, hT⟩
  have h0_notin_S : 0 ∉ S := by
    simp [S, h0]
  set t_first := Nat.find hS_nonempty with ht_first_def
  have ht_first_pos : 0 < podo s0 t_first x := by
    simpa [S] using Nat.find_spec hS_nonempty
  have ht_first_pos_nat : 0 < t_first :=
    (Nat.find_pos hS_nonempty).mpr h0_notin_S
  set t0 := t_first - 1 with ht0_def
  have ht0_lt_t_first : t0 < t_first := by
    omega
  have ht0_notin_S : t0 ∉ S := Nat.find_min hS_nonempty ht0_lt_t_first
  have h_podo_t0_eq_zero : podo s0 t0 x = 0 := by
    have h_not_pos : ¬ 0 < podo s0 t0 x := by simpa [S] using ht0_notin_S
    have h_nonneg_t0 : 0 ≤ podo s0 t0 x := h_nonneg t0
    omega
  have h_podo_t0_succ_pos : 0 < podo s0 (t0 + 1) x := by
    have h_eq : t0 + 1 = t_first := by omega
    rw [h_eq]
    exact ht_first_pos
  have h_podo_t0_succ_eq_one : podo s0 (t0 + 1) x = 1 := by
    rw [podo_succ s0 t0 x]
    rw [h_podo_t0_eq_zero]
    have h_pos : 0 < podo s0 (t0 + 1) x := h_podo_t0_succ_pos
    rw [podo_succ s0 t0 x] at h_pos
    rw [h_podo_t0_eq_zero] at h_pos
    -- h_pos : 0 < 0 + (if 2 * (d : ℤ) ≤ pconf s0 t0 x then 1 else 0)
    -- The increment is either 0 or 1. Since h_pos says it's >0, it must be 1.
    by_cases hcond : 2 * (d : ℤ) ≤ pconf s0 t0 x
    · -- then the if evaluates to 1
      simp [hcond]
    · -- then the if evaluates to 0, contradicting h_pos
      simp [hcond] at h_pos
  have ht0_lt_T : t0 < T := by
    have hT_mem_S : T ∈ S := by simpa [S] using hT
    have hle : t_first ≤ T := Nat.find_le hT_mem_S
    omega
  refine ⟨t0, ht0_lt_T, h_podo_t0_eq_zero, ?_⟩
  rw [h_podo_t0_succ_eq_one]

/-- **New, real.** At a first-crossing time `t0` for a site `x` with `s0 x ≤ 2d - 1`, some
neighbour `y` of `x` already has `podo s0 t0 y ≥ 1`: unfolding `podo_succ`/`pconf`/`lap` at `x`
(where `podo s0 t0 x = 0`) turns `1 ≤ podo s0 (t0+1) x` into the firing threshold `2d ≤ s0 x +
nbrSumZ (podo s0 t0) x`, forcing `nbrSumZ (podo s0 t0) x ≥ 1`; since `nbrSumZ` sums `2d`
nonnegative terms (`podo` is nonnegative), one of the `2d` neighbours' terms is positive
(`Finset.sum_eq_zero`'s contrapositive), giving the witness `y` and the adjacency
`lattice d`.Adj y x` directly from `y = x ± unit i`. -/
theorem as_ineq2_neighbor_witness
    {d : ℕ} (s0 : Site d → ℤ) (x : Site d) (hx0 : s0 x ≤ 2 * (d : ℤ) - 1) (t0 : ℕ)
    (h0 : podo s0 t0 x = 0) (h1 : 1 ≤ podo s0 (t0 + 1) x) :
    ∃ y : Site d, (lattice d).Adj y x ∧ 1 ≤ podo s0 t0 y := by
  have hs : podo s0 (t0 + 1) x
      = podo s0 t0 x + (if 2 * d ≤ pconf s0 t0 x then (1 : ℤ) else 0) :=
    podo_succ s0 t0 x
  have hle : 2 * d ≤ pconf s0 t0 x := (by
    by_contra hc
    have hz : (if 2 * d ≤ pconf s0 t0 x then (1 : ℤ) else 0) = 0 := if_neg hc
    rw [hs, h0, zero_add, hz] at h1
    omega)
  have hp : pconf s0 t0 x = s0 x + nbrSumZ (podo s0 t0) x := (by
    have hp0 : pconf s0 t0 x
        = s0 x + nbrSumZ (podo s0 t0) x - 2 * (d : ℤ) * podo s0 t0 x := (by
      simp only [pconf, lap]
      ring)
    rw [hp0, h0]
    ring)
  have hnb : 0 < nbrSumZ (podo s0 t0) x := (by
    rw [hp] at hle
    omega)
  obtain ⟨y, hy, hpos⟩ := exists_adj_pos_of_nbrSumZ_pos (podo s0 t0)
    (fun y => as_podo_nonneg s0 t0 y) x hnb
  exact ⟨y, hy, by omega⟩


/-- **New, real (closes the `-- GAP` below).** `0 < as_tildeV η x` places `x` itself in `as_tildeP η`:
if `x = 0` this is `as_tildeP`'s first disjunct; otherwise, unfold `as_tildeV η x = as_podoTerminal s0 x
= podo s0 T x` (`s0` the background of `as_tildeV`, `T` its stabilization `sInf`), apply
`as_ineq2_first_crossing` to get a first-crossing time `t0 < T`,
apply `as_ineq2_neighbor_witness` there (using `s0 x = η x ≤ 2d-1`
off the origin, `dirac_of_ne`) to get a neighbour `y` with `podo s0 t0 y ≥ 1`, and lift this to
`as_podoTerminal s0 y = podo s0 T y > 0` via `t0 < T` and `as_
podo_mono`, landing `y` (hence `x`, by `as_tildeP`'s second disjunct) in `as_tildeP η`. -/
theorem as_ineq2_mem_tildeP
    {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (x : Site d) (hv : 0 < as_tildeV η x) :
    x ∈ as_tildeP η := by
  by_cases hx0 : x = (0 : Site d)
  · left; exact hx0
  · right
    set s0 : Site d → ℤ := fun z => η z + ((explosionThreshold η : ℤ) - 1) * dirac (0 : Site d) z
      with hs0def
    set T := sInf {T : ℕ | ∀ t : ℕ, T ≤ t → podo s0 t = podo s0 T} with hTdef
    have hTpos : 0 < podo s0 T x := hv
    obtain ⟨t0, ht0T, ht0zero, ht0one⟩ :=
      as_ineq2_first_crossing s0 x T hTpos
    have hs0x : s0 x ≤ 2 * (d : ℤ) - 1 := by
      have hval : s0 x = η x := by rw [hs0def]; simp [dirac_of_ne hx0]
      rw [hval]; exact hhigh x
    obtain ⟨y, hadj, hypos⟩ :=
      as_ineq2_neighbor_witness s0 x hs0x t0 ht0zero ht0one
    refine ⟨y, hadj, ?_⟩
    show 0 < podo s0 T y
    have := as_podo_mono s0 ht0T.le y
    omega

/-- **Real, modulo the three gaps above (`eq:ineq2`'s final gluing,
`exploding.tex:1048-1052`).** Combines `approx1`, `approx2` and
`specialcase2` exactly as the paper does: if `v_t(x) > 0` then `approx2` gives
`w_t(x) > 0` or `ṽ(x) > 0`; in the first case `specialcase2` gives
`w̃_t(x) > 0`, and in the second `w̃_t(x) = 1 > 0` directly since `x ∈ P̃` by
`ṽ(x) > 0`'s very definition of `P̃` (`as_tildeP`'s second disjunct, taking `x`
adjacent to itself is not needed — `x`'s own positivity places it in `P̃` only
through a neighbour, so we instead note `as_tildeP` also contains `0`
unconditionally and re-derive `x ∈ as_tildeP η` from `ṽ(x) > 0` via the
neighbour clause at any neighbour of `x`, closed above by
`as_ineq2_mem_tildeP`). Either way
`approx1` gives `u_{t+c}(x) > 0`, and translating this into `ℕ∞` arrival times
is the same `sInf` bookkeeping as `eq:ineq1`. -/
theorem as_ineq2
    {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d))
    (hexp1 : 1 ≤ explosionThreshold η)
    (hlastreach : ∃ c : ℕ, ∀ x ∈ as_tildeP η, 1 ≤ lastWave η (0 : Site d) c x)
    (htildePfin : (as_tildeP η).Finite)
    (hspecial : ∀ t : ℕ, ∀ x : Site d, 0 < as_wOdo η t x → 0 < as_tildeW η t x) :
    ∃ C2 : ℕ, ∀ x : Site d, lastArrival η (0 : Site d) x ≤ arrival η x + (C2 : ℕ∞) := by
  obtain ⟨c, happrox1⟩ := as_step2_approx1 hd η hlow hhigh hlast hlastreach htildePfin
  have happrox2 := as_step2_approx2 hd η hlow hhigh hexp1
  have hpointwise : ∀ t : ℕ, ∀ x : Site d, 0 < as_expOdo η t x → 0 < lastWave η (0 : Site d) (t + c) x := by
    intro t x hpos
    have hsum := happrox2 t x
    have hor : 0 < as_wOdo η t x ∨ 0 < as_tildeV η x := by
      by_contra hcon
      rw [not_or, not_lt, not_lt] at hcon
      have hw0 : as_wOdo η t x ≤ 0 := hcon.1
      have hv0 : as_tildeV η x ≤ 0 := hcon.2
      omega
    have hwtildepos : 0 < as_tildeW η t x := by
      rcases hor with hw | hv
      · exact hspecial t x hw
      · -- `ṽ(x) > 0` places `x` itself in `as_tildeP η`
        -- (`as_ineq2_mem_tildeP`), so the frozen
        -- odometer `w̃` reads off its frozen initial value `1` there forever
        -- (`fodo_of_mem`).
        classical
        have hmem := as_ineq2_mem_tildeP hd η hhigh x hv
        have := fodo_of_mem (as_tildeP η) η (fun z => if z ∈ as_tildeP η then (1 : ℤ) else 0) t hmem
        simp only [as_tildeW]
        rw [this, if_pos hmem]
        norm_num
    exact lt_of_lt_of_le hwtildepos (happrox1 t x)
  refine ⟨c, fun x => ?_⟩
  by_cases hatop : arrival η x = ⊤
  · simp [hatop]
  · have hex : ∃ n : ℕ, 1 ≤ n ∧
        0 < podo (fun y => η y + (explosionThreshold η : ℤ) * dirac (0 : Site d) y) n x := by
      by_contra hc
      exact hatop (sInf_coe_top
        (P := fun n : ℕ => 1 ≤ n ∧
          0 < podo (fun y => η y + (explosionThreshold η : ℤ) * dirac (0 : Site d) y) n x) hc)
    obtain ⟨n, ⟨hn1, hnpos⟩, hneq⟩ := sInf_coe_attained
      (P := fun n : ℕ => 1 ≤ n ∧
        0 < podo (fun y => η y + (explosionThreshold η : ℤ) * dirac (0 : Site d) y) n x) hex
    have hlwpos : 0 < lastWave η (0 : Site d) (n + c) x := hpointwise n x hnpos
    have hla : lastArrival η (0 : Site d) x ≤ ((n + c : ℕ) : ℕ∞) :=
      sInf_le ⟨n + c, rfl, by omega, hlwpos⟩
    rw [Nat.cast_add] at hla
    rw [show arrival η x = (n : ℕ∞) from hneq]
    exact hla

/-! ### Assembly -/

/-- A non-robust background has a finite explosion threshold and the pile
`η + M_η δ_0` is not stabilizable. -/
theorem as_explosionThreshold_spec {d : ℕ} (η : Site d → ℤ) (h : ¬ Robust η) :
    1 ≤ explosionThreshold η ∧ ¬ Stabilizable (explodingPile η) := by
  have hne : {n : ℕ | 1 ≤ n ∧ ¬ Stabilizable (fun x => η x + n * dirac (0 : Site d) x)}.Nonempty := by
    by_contra hcon
    refine h ?_
    intro n hn
    by_contra hns
    exact hcon ⟨n, hn, hns⟩
  have hmem := Nat.sInf_mem hne
  refine ⟨hmem.1, ?_⟩
  change ¬ Stabilizable
    (fun x => η x + (explosionThreshold η : ℤ) * dirac (0 : Site d) x)
  exact hmem.2

