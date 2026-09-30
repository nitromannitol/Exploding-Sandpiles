/-
Proposition 3.8 of the paper: the rescaled last-wave arrival times converge.

DECOMPOSITION (not a proof of the theorem).  The paper's proof
(`exploding.tex:846-850`) is three sentences:

  "In light of Lemma 3.7 it suffices to prove the result for `T̃`.  Convergence
  in integer directions follows from the subadditive ergodic theorem.
  Everywhere convergence then follows from continuity and approximation.  The
  properties of `N_p` are immediate from the scaling and microscopic
  subadditivity."

Decomposed into:

  (a) `aux_lwc_kingman`  -- Kingman's theorem applied to `clusterArrival` along
                            each lattice direction (GAP: see the report below)
  (b) `aux_lwc_homog`    -- `N` is homogeneous under integer scaling of a
                            lattice direction (real, proved from (a)'s
                            conclusion alone)
  (c) `aux_lwc_uniform`  -- everywhere convergence, locally uniform on compacts
                            of `ℝ^d`, by continuity/convexity extension from
                            the countable set of lattice directions (GAP)
  (d) `aux_lwc_transfer` -- transfers the `clusterArrival` statement to
                            `lastArrival` via `Exploding.Frozen.last_penultimate_close`
                            (GAP: stated precisely, believed a routine
                            compactness argument, not attempted here for time)

### Verdict on Kingman's subadditive ergodic theorem

Grepped `.lake/packages/mathlib/Mathlib` for "Kingman" and for
"subadditive ergodic": **no hits**.  `Mathlib/Analysis/Subadditive.lean` is
confirmed to be *only* Fekete's lemma, the deterministic statement that a
subadditive real sequence bounded below converges (`Subadditive.tendsto_lim`);
it has no measure, no transformation, no a.e. statement.  Kingman's theorem is
**absent from this Mathlib checkout**.

It is, however, **present and fully proved (no `sorry`) in
`~/Lattice-Probability/LatticeProb/Prob/Kingman.lean`**, in the classical
single-measure-preserving-transformation form: for `T : Ω → Ω` measure
preserving and `g : ℕ → Ω → ℝ` `SubadditiveAlong T` (`g (m+n) x ≤ g m x +
g n (T^[m] x)`), nonnegative or bounded below linearly, `g n x / n` converges
a.e. to a `T`-invariant limit (`LatticeProb.ae_tendsto_gLow`,
`LatticeProb.ae_tendsto_div`).  Combined with
`LatticeProb.ergodic_coordShift_infinitePi` (`LatticeProb/IID.lean`), which
gives that translation by a fixed nonzero lattice vector is *ergodic* — not
just measure preserving — for an i.i.d. field such as `toyLaw`, and with
Mathlib's own `Ergodic.ae_eq_const_of_ae_eq_comp₀`
(`Mathlib/Dynamics/Ergodic/Function.lean`), which turns an a.e.-invariant
function under an ergodic map into an a.e.-*constant* one, the *entire*
machinery needed for "convergence in a fixed integer direction, to a
deterministic constant" is present and unconditionally proved somewhere in
this workspace.

What is **not** proved anywhere is the bridge from these general theorems to
`clusterArrival` on `toyLaw`: (i) the shift-equivariance
`clusterArrival (η ∘ (· + v)) a b = clusterArrival η (a + v) (b + v)`, needed
to view `n ↦ clusterArrival η 0 (n • v)` as `SubadditiveAlong` the shift-by-`v`
map (the sealed `approx_subadditivity` gives subadditivity in the *basepoint*
argument at a *fixed* `η`, not the cocycle identity across a shifted `η`,
which is a different, translation-equivariance fact about the whole toppling
construction); and (ii) a first-moment bound
`Integrable (fun η => (clusterArrival η 0 v).toNat) (toyLaw d p)`, needed to
invoke `LatticeProb.ae_tendsto_div` at all.  Neither is a Mathlib gap — (i) is
routine but unformalized equivariance of every definition in
`Exploding/Support/{Toppling,Vocab,Wave}.lean` under a lattice shift, and (ii)
is a genuine, unformalized probabilistic fact (a tail estimate) that
`renormalization_properties` does not by itself supply.  `aux_lwc_kingman`
below states exactly this combined gap.

### Repair of the proof (2026-09-24, exploding.tex, proof of Proposition 3.1)

The paper's proof applied Kingman's theorem with no moment bound, and no moment bound is
available: Proposition 2.2 and Lemmas 3.6, 3.7 hold only on an event of probability one,
and the only bound on `M̂_η(0)` (Lemma 3.1) is exponential in the distance to `C_∞`.  The
corrected proof (the same argument as the proof of Proposition 5.1, with Lemma 2.1 in place
of Hypothesis 5.3) needs no integrability.  It uses

  * `aux_lwc_shift_ergodic`     -- translation by `v ≠ 0` is ergodic for `toyLaw`
                                   (from `LatticeProb.ergodic_coordShift_infinitePi`);
  * `aux_lwc_cluster_shift`     -- translation covariance of `clusterArrival`;
  * `aux_lwc_good_event`        -- a shift-invariant event of full measure on which the
                                   hypotheses of `approx_subadditivity` hold and every
                                   `clusterArrival` is finite, so `toNat` reads no junk;
  * `aux_lwc_measurable`        -- measurability of `clusterArrival`;
  * `aux_lwc_cluster_lipschitz` -- the two bounds `eq:lastwave_lipschitz`, the second from
                                   any point `x`, proved with Lemma 2.1 and Proposition 2.2;
  * `aux_lwc_kingman_linear`    -- Kingman's theorem without a moment bound, through the
                                   transformation induced on `{g n ≤ C n + K for all n}`
                                   and Kac's lemma (a general result, to be added to
                                   Lattice-Probability next to `LatticeProb.ae_tendsto_div`).

`aux_lwc_kingman` (its statement unchanged) follows from these with `approx_subadditivity`,
`penultimate_upper_bound` and `last_penultimate_close`; `aux_lwc_uniform` uses the second
bound of `aux_lwc_cluster_lipschitz` in place of "continuity".
-/
import Exploding.Support.Vocab
import Exploding.Support.Wave
import Exploding.Frozen.ApproxSubadditivity
import Exploding.Frozen.PenultimateClose
import Exploding.Frozen.PenultimateUpperBound
import Exploding.Frozen.FiniteExploding
import Exploding.External.LiggettSchonmannStaceyBoundedDegree
import Exploding.External.MathieuHoles
import Exploding.External.AntalPisztora
import Mathlib.Dynamics.Ergodic.Ergodic
import LatticeProb.Prob.Translation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

open Exploding LatticeProb MeasureTheory Filter

/-! ### (a0) the ingredients of the repaired proof -/

/-- `chipLaw a b p` is a probability measure for `0 ≤ p ≤ 1`: it is a convex combination of
two Dirac masses with weights `p` and `1 - p`, which sum to `1`
(`ENNReal.ofReal_add`, `Measure.dirac_apply'`). -/
theorem aux_lwc_isProbabilityMeasure_chipLaw (a b : ℤ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (chipLaw a b p) := by
  constructor
  simp only [chipLaw, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ, Pi.one_apply, smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_add hp (by linarith)]
  norm_num

/-- Translation by a nonzero lattice vector is ergodic for the i.i.d. field `iidLaw d (chipLaw
a b p)` with ANY one-site law `chipLaw a b p`, not just the specific `a = 2d-1`, `b = 2d-2` of
`toyLaw`: this isolates the general application of `LatticeProb.ergodic_coordShift_infinitePi`
(with `LatticeProb.exists_add_nsmul_notMem` supplying the "moves every finite set off itself"
hypothesis) from the bookkeeping of unfolding `toyLaw`, so that the probability-measure
instance for `chipLaw a b p` is registered for literally the term `chipLaw a b p` appearing in
the goal, with no numeral-elaboration mismatch against a separately-written copy. -/
theorem aux_lwc_chipLaw_shift_ergodic {d : ℕ} (a b : ℤ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (v : Site d) (hv : v ≠ 0) :
    Ergodic (fun η : Site d → ℤ => fun z => η (v + z)) (LatticeProb.iidLaw d (chipLaw a b p)) := by
  haveI : IsProbabilityMeasure (chipLaw a b p) :=
    aux_lwc_isProbabilityMeasure_chipLaw a b p hp.le hp1.le
  have heq : (fun η : Site d → ℤ => fun z => η (v + z))
      = LatticeProb.coordShift (fun x : Site d => x + v) := by
    funext η z; simp [LatticeProb.coordShift, add_comm]
  rw [heq]
  refine LatticeProb.ergodic_coordShift_infinitePi (fun _ : Site d => chipLaw a b p)
      (fun x y hxy => by simpa using hxy) (fun _ => rfl) fun s => ?_
  obtain ⟨n, hn⟩ := LatticeProb.exists_add_nsmul_notMem hv s
  exact ⟨n, fun x hx => by rw [LatticeProb.iterate_add_right]; exact hn x hx⟩

/-- Translation by a fixed nonzero lattice vector preserves the product measure `toyLaw` and
is mixing, hence ergodic (proof of Proposition 3.1).  Available through
`LatticeProb.ergodic_coordShift_infinitePi`, since `toyLaw` is an `infinitePi` and
`z ↦ v + z` moves every finite set of sites off itself after finitely many steps. -/
theorem aux_lwc_shift_ergodic (d : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (v : Site d) (hv : v ≠ 0) :
    Ergodic (fun η : Site d → ℤ => fun z => η (v + z)) (toyLaw d p) :=
  aux_lwc_chipLaw_shift_ergodic (2 * (d:ℤ) - 1) (2 * (d:ℤ) - 2) p hp hp1 v hv

/-- Neighbour sums shift along a translated background: if `u y = w (v + y)` for all `y`, then
`nbrSumZ u x = nbrSumZ w (v + x)`. -/
theorem aux_lwc_nbrSumZ_shift {d : ℕ} (v : Site d) (u w : Site d → ℤ)
    (h : ∀ y, u y = w (v + y)) (x : Site d) :
    nbrSumZ u x = nbrSumZ w (v + x) := by
  simp only [nbrSumZ, h]
  congr 1
  funext i
  congr 2 <;> abel

/-- The `n`-wave shifts along a translated background: the `n`-wave of `η ∘ (v + ·)` started
at `z` equals, at `x`, the `n`-wave of `η` started at `v + z`, evaluated at `v + x`. -/
theorem aux_lwc_wave_shift {d : ℕ} (η : Site d → ℤ) (v : Site d) (n : ℕ) (z : Site d) (t : ℕ)
    (x : Site d) :
    wave (fun w => η (v + w)) n z t x = wave η n (v + z) t (v + x) := by
  induction t generalizing x with
  | zero =>
    simp only [wave_zero]
    congr 1
    exact propext ⟨fun h => by rw [h], fun h => add_left_cancel h⟩
  | succ t ih =>
    by_cases hxz : x = z
    · subst hxz; simp [wave_at_centre]
    · have hxz' : v + x ≠ v + z := fun h => hxz (add_left_cancel h)
      rw [wave_of_ne _ _ _ _ _ hxz, wave_of_ne _ _ _ _ _ hxz',
        aux_lwc_nbrSumZ_shift v _ _ (fun y => ih y) x]

/-- The `n`-wave of `η ∘ (v + ·)` started at `z` equals, at time `t`, the `n`-wave of `η`
started at `v + z`, at time `T`, iff the same holds after the shift (`aux_lwc_wave_shift`
applied at `y := x - v` and `x := v + x`, using that `y ↦ v + y` is a bijection). -/
theorem aux_lwc_wave_eq_shift_iff {d : ℕ} (η : Site d → ℤ) (v : Site d) (n : ℕ) (z : Site d)
    (t T : ℕ) :
    wave (fun w => η (v + w)) n z t = wave (fun w => η (v + w)) n z T ↔
      wave η n (v + z) t = wave η n (v + z) T := by
  constructor
  · intro h; funext y
    have := congrFun h (y - v)
    simpa [aux_lwc_wave_shift] using this
  · intro h; funext x
    have := congrFun h (v + x)
    simpa [aux_lwc_wave_shift] using this

/-- `WaveStabilizable` shifts along a translated background. -/
theorem aux_lwc_waveStabilizable_shift {d : ℕ} (η : Site d → ℤ) (v : Site d) (n : ℕ)
    (z : Site d) :
    WaveStabilizable (fun w => η (v + w)) n z ↔ WaveStabilizable η n (v + z) := by
  simp only [WaveStabilizable]
  exact exists_congr fun T => forall_congr' fun t => forall_congr' fun _ =>
    aux_lwc_wave_eq_shift_iff η v n z t T

/-- `waveTerminal` shifts along a translated background. -/
theorem aux_lwc_waveTerminal_shift {d : ℕ} (η : Site d → ℤ) (v : Site d) (n : ℕ) (z : Site d)
    (x : Site d) :
    waveTerminal (fun w => η (v + w)) n z x = waveTerminal η n (v + z) (v + x) := by
  simp only [waveTerminal]
  have hset : {T : ℕ | ∀ t, T ≤ t → wave (fun w => η (v+w)) n z t = wave (fun w => η (v+w)) n z T}
      = {T : ℕ | ∀ t, T ≤ t → wave η n (v+z) t = wave η n (v+z) T} := by
    ext T; exact forall_congr' fun t => forall_congr' fun _ => aux_lwc_wave_eq_shift_iff η v n z t T
  rw [hset, aux_lwc_wave_shift]

/-- `waveThreshold` shifts along a translated background: the defining sets of `n` are equal,
via `aux_lwc_waveStabilizable_shift`. -/
theorem aux_lwc_waveThreshold_shift {d : ℕ} (η : Site d → ℤ) (v z : Site d) :
    waveThreshold (fun w => η (v + w)) z = waveThreshold η (v + z) := by
  simp only [waveThreshold]
  congr 1
  ext n
  simp [aux_lwc_waveStabilizable_shift]

/-- `lastWave` shifts along a translated background. -/
theorem aux_lwc_lastWave_shift {d : ℕ} (η : Site d → ℤ) (v z : Site d) (t : ℕ) (x : Site d) :
    lastWave (fun w => η (v + w)) z t x = lastWave η (v + z) t (v + x) := by
  simp only [lastWave, aux_lwc_waveThreshold_shift, aux_lwc_wave_shift]

/-- `penultimateWave` shifts along a translated background. -/
theorem aux_lwc_penultimateWave_shift {d : ℕ} (η : Site d → ℤ) (v z x : Site d) :
    penultimateWave (fun w => η (v + w)) z x = penultimateWave η (v + z) (v + x) := by
  simp only [penultimateWave, aux_lwc_waveThreshold_shift]
  split
  · rfl
  · exact aux_lwc_waveTerminal_shift η v _ z x

/-- `(lattice d).Adj` is translation invariant. -/
theorem aux_lwc_adj_shift {d : ℕ} (v x y : Site d) :
    (lattice d).Adj x y ↔ (lattice d).Adj (v + x) (v + y) := by
  show (∃ i : Fin d, y = x + unit i ∨ x = y + unit i) ↔
    (∃ i : Fin d, v + y = (v + x) + unit i ∨ v + x = (v + y) + unit i)
  constructor
  · rintro ⟨i, h | h⟩
    · exact ⟨i, Or.inl (by rw [h]; abel)⟩
    · exact ⟨i, Or.inr (by rw [h]; abel)⟩
  · rintro ⟨i, h | h⟩
    · refine ⟨i, Or.inl (add_left_cancel (a := v) ?_)⟩
      rw [h]; abel
    · refine ⟨i, Or.inr (add_left_cancel (a := v) ?_)⟩
      rw [h]; abel

/-- `penultimateCluster` shifts along a translated background: `x` lies in the cluster of `ηv`
around `z` iff `v + x` lies in the cluster of `η` around `v + z`. -/
theorem aux_lwc_penultimateCluster_shift {d : ℕ} (η : Site d → ℤ) (v z x : Site d) :
    x ∈ penultimateCluster (fun w => η (v + w)) z ↔ (v + x) ∈ penultimateCluster η (v + z) := by
  simp only [penultimateCluster, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro (h | ⟨y, hadj, hpos⟩)
    · left; rw [h]
    · right
      exact ⟨v + y, (aux_lwc_adj_shift v y x).1 hadj, by rwa [aux_lwc_penultimateWave_shift] at hpos⟩
  · rintro (h | ⟨y, hadj, hpos⟩)
    · left; exact add_left_cancel h
    · right
      obtain ⟨y', rfl⟩ : ∃ y', y = v + y' := ⟨y - v, by abel⟩
      exact ⟨y', (aux_lwc_adj_shift v y' x).2 hadj, by rwa [aux_lwc_penultimateWave_shift]⟩

/-- `lastArrival` shifts along a translated background. -/
theorem aux_lwc_lastArrival_shift {d : ℕ} (η : Site d → ℤ) (v y x : Site d) :
    lastArrival (fun w => η (v + w)) y x = lastArrival η (v + y) (v + x) := by
  simp only [lastArrival, aux_lwc_lastWave_shift]

/-- Translation covariance of the penultimate-cluster arrival times: every object of
`(3.1)`-`(3.5)` is defined from the background and the starting site only, so shifting the
background by `v` shifts both sites by `v`.  This makes `n ↦ T̃(0, n v)` a process over the
shift by `v`, as Kingman's theorem needs. -/
theorem aux_lwc_cluster_shift (d : ℕ) (η : Site d → ℤ) (v a b : Site d) :
    clusterArrival (fun z => η (v + z)) a b = clusterArrival η (v + a) (v + b) := by
  simp only [clusterArrival]
  congr 1
  ext t
  refine exists_congr fun n => and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h w hw
    obtain ⟨w', rfl⟩ : ∃ w', w = v + w' := ⟨w - v, by abel⟩
    rw [← aux_lwc_lastWave_shift]
    exact h w' ((aux_lwc_penultimateCluster_shift η v b w').mpr hw)
  · intro h w hw
    rw [aux_lwc_lastWave_shift]
    exact h (v + w) ((aux_lwc_penultimateCluster_shift η v b w).mp hw)

/-- The background is a.s. in its allowed range `{2d-2, 2d-1}` at every site: the marginal of
`toyLaw d p` at each coordinate is `chipLaw (2d-1) (2d-2) p` (`Measure.infinitePi_map_eval`),
supported on `{2d-1, 2d-2}`, and `Site d` is countable (`ae_all_iff`). -/
theorem aux_lwc_good_event_1 (d : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∀ᵐ η ∂(toyLaw d p), ∀ x : Site d, 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1 := by
  haveI hprob : IsProbabilityMeasure (chipLaw (2 * (d:ℤ) - 1) (2 * (d:ℤ) - 2) p) :=
    aux_lwc_isProbabilityMeasure_chipLaw _ _ p hp.le hp1.le
  rw [ae_all_iff]
  intro x
  have hmap : (toyLaw d p).map (fun η : Site d → ℤ => η x) =
      chipLaw (2 * (d:ℤ) - 1) (2 * (d:ℤ) - 2) p := by
    show (Measure.infinitePi (fun _ : Site d => chipLaw (2*(d:ℤ)-1) (2*(d:ℤ)-2) p)).map
      (fun η => η x) = _
    exact Measure.infinitePi_map_eval _ x
  have hSmeas : MeasurableSet {v : ℤ | ¬ (2 * (d:ℤ) - 2 ≤ v ∧ v ≤ 2 * (d:ℤ) - 1)} := by
    have : DiscreteMeasurableSpace ℤ := inferInstance
    exact DiscreteMeasurableSpace.forall_measurableSet _
  rw [ae_iff, show {η : Site d → ℤ | ¬ (2*(d:ℤ)-2 ≤ η x ∧ η x ≤ 2*(d:ℤ)-1)}
        = (fun η : Site d → ℤ => η x) ⁻¹' {v : ℤ | ¬ (2*(d:ℤ)-2 ≤ v ∧ v ≤ 2*(d:ℤ)-1)} from rfl,
    ← Measure.map_apply (measurable_pi_apply x) hSmeas, hmap]
  simp only [chipLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hSmeas,
    Set.indicator_apply, Set.mem_setOf_eq]
  norm_num

/-- Every `clusterArrival` from the origin is a.s. finite: read off
`Exploding.Frozen.last_penultimate_close`'s conclusion at the scale `n := max n0 (mnorm x)`
(Lemma 3.7). -/
theorem aux_lwc_good_event_2 (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∀ᵐ η ∂(toyLaw d p), ∀ x : Site d, clusterArrival η (0 : Site d) x ≠ ⊤ := by
  obtain ⟨γ, hγ, hclose⟩ := Exploding.Frozen.last_penultimate_close d hd p hp hp1 hLSSB hHole hChem
  filter_upwards [hclose] with η hη x
  obtain ⟨n0, hn0⟩ := hη
  obtain ⟨_, b, _, hb, _⟩ := (hn0 (max n0 (mnorm x).toNat) (le_max_left _ _) x (by omega)).2
  rw [hb]; exact ENat.coe_ne_top b

/-- Promotes an a.s. property `Q` (possibly not itself known to be a measurable predicate) to
an honest measurable, full-measure set on which `Q` holds, via a measurable null superset of
`{¬ Q}` (`MeasureTheory.exists_measurable_superset`). -/
theorem aux_lwc_good_event_3 {d : ℕ} (p : ℝ) (Q : (Site d → ℤ) → Prop)
    (hQ : ∀ᵐ η ∂(toyLaw d p), Q η) :
    ∃ E0 : Set (Site d → ℤ), MeasurableSet E0 ∧ toyLaw d p E0ᶜ = 0 ∧ ∀ η ∈ E0, Q η := by
  obtain ⟨N, hNsub, hNmeas, hNeq⟩ :=
    MeasureTheory.exists_measurable_superset (toyLaw d p) {η | ¬ Q η}
  refine ⟨Nᶜ, hNmeas.compl, ?_, ?_⟩
  · rw [compl_compl, hNeq]; exact (MeasureTheory.ae_iff).mp hQ
  · intro η hη
    by_contra hQη
    exact hη (hNsub hQη)

/-- Saturates a measurable full-measure set `E0` into the shift-invariant set `E := ⋂_v
(shift_v)⁻¹ E0`: measurable (`Site d` countable), full measure (each preimage has the same
measure as `E0` since every shift, including `v = 0`, preserves `toyLaw`, by
`aux_lwc_shift_ergodic` and `MeasurePreserving.id`), and shift invariant by the cocycle
identity `shift_v ∘ shift_w = shift_{w+v}`. -/
theorem aux_lwc_good_event_4 (d : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (E0 : Set (Site d → ℤ)) (hE0meas : MeasurableSet E0) (hE0full : toyLaw d p E0ᶜ = 0)
    (hshiftmeas : ∀ v : Site d, Measurable (fun η : Site d → ℤ => fun z => η (v + z)))
    (hshiftmp : ∀ v : Site d, MeasurePreserving (fun η : Site d → ℤ => fun z => η (v + z))
      (toyLaw d p) (toyLaw d p)) :
    ∃ E : Set (Site d → ℤ), MeasurableSet E ∧ toyLaw d p Eᶜ = 0 ∧
      (∀ v : Site d, ∀ η ∈ E, (fun z => η (v + z)) ∈ E) ∧
      ∀ η ∈ E, ∀ v : Site d, (fun z => η (v + z)) ∈ E0 := by
  set E : Set (Site d → ℤ) := ⋂ v : Site d, (fun η : Site d → ℤ => fun z => η (v + z)) ⁻¹' E0
    with hEdef
  have hEmeas : MeasurableSet E := MeasurableSet.iInter (fun v => hE0meas.preimage (hshiftmeas v))
  have hEcompl : Eᶜ = ⋃ v : Site d, (fun η : Site d → ℤ => fun z => η (v + z)) ⁻¹' E0ᶜ := by
    simp only [hEdef, Set.compl_iInter, Set.preimage_compl]
  have hEfull : toyLaw d p Eᶜ = 0 := by
    rw [hEcompl]
    refine measure_iUnion_null (fun v => ?_)
    exact ((hshiftmp v).measure_preimage hE0meas.compl.nullMeasurableSet).trans hE0full
  have hmem_iff : ∀ η : Site d → ℤ, η ∈ E ↔ ∀ v : Site d, (fun z => η (v + z)) ∈ E0 := by
    intro η; simp only [hEdef, Set.mem_iInter, Set.mem_preimage]
  refine ⟨E, hEmeas, hEfull, ?_, fun η hη v => (hmem_iff η).mp hη v⟩
  intro v η hη
  rw [hmem_iff] at hη ⊢
  intro w
  have hcomp : (fun z => (fun z' => η (v + z')) (w + z)) = fun z => η ((w + v) + z) := by
    funext z; abel
  rw [hcomp]
  exact hη (w + v)

/-- The event on which the proof runs.  It has full `toyLaw` measure, is mapped into itself
by every translation, and on it the background takes the values `2d - 2`, `2d - 1`, every
site has a last wave, and every `clusterArrival` is finite (Lemmas 3.2, 3.6 and 3.7, moved
to any starting site by `aux_lwc_cluster_shift`).  On it `n ↦ (T̃(0, n v)).toNat` is
subadditive by `approx_subadditivity`, with no junk value.

Built by taking `Q η` to be the conjunction of the three properties at the origin (`hQae`,
combining `aux_lwc_good_event_1`, Lemma 3.2 `Exploding.Frozen.finite_exploding` and
`aux_lwc_good_event_2`), promoting `Q` to a measurable full-measure `E0`
(`aux_lwc_good_event_3`) and shift-saturating it to `E` (`aux_lwc_good_event_4`); the general
site `y` and the general pair `a, b` are then reached from `Q` at the shifted backgrounds
`shift_y η` and `shift_a η` via `aux_lwc_waveStabilizable_shift` and `aux_lwc_cluster_shift`. -/
theorem aux_lwc_good_event (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ E : Set (Site d → ℤ), MeasurableSet E ∧ toyLaw d p Eᶜ = 0 ∧
      (∀ v : Site d, ∀ η ∈ E, (fun z => η (v + z)) ∈ E) ∧
      ∀ η ∈ E, (∀ x, 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1) ∧
        (∀ y : Site d, ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n y) ∧
        ∀ a b : Site d, clusterArrival η a b ≠ ⊤ := by
  set Q : (Site d → ℤ) → Prop := fun η => (∀ x, 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1) ∧
    (∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d)) ∧
    (∀ x, clusterArrival η (0 : Site d) x ≠ ⊤) with hQdef
  have hQae : ∀ᵐ η ∂(toyLaw d p), Q η := by
    filter_upwards [aux_lwc_good_event_1 d p hp hp1,
      Exploding.Frozen.finite_exploding d hd p hp hp1 hLSSB hHole hChem,
      aux_lwc_good_event_2 d hd p hp hp1 hLSSB hHole hChem] with η h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨E0, hE0meas, hE0full, hE0Q⟩ := aux_lwc_good_event_3 p Q hQae
  have hshiftmeas : ∀ v : Site d, Measurable (fun η : Site d → ℤ => fun z => η (v + z)) :=
    fun v => measurable_pi_lambda _ (fun z => measurable_pi_apply (v + z))
  have hshiftmp : ∀ v : Site d, MeasurePreserving (fun η : Site d → ℤ => fun z => η (v + z))
      (toyLaw d p) (toyLaw d p) := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · have hid : (fun η : Site d → ℤ => fun z => η ((0 : Site d) + z)) = id := by
        funext η; funext z; simp
      rw [hid]; exact MeasurePreserving.id (toyLaw d p)
    · exact (aux_lwc_shift_ergodic d p hp hp1 v hv).toMeasurePreserving
  obtain ⟨E, hEmeas, hEfull, hEshift, hEmemQ⟩ :=
    aux_lwc_good_event_4 d p hp hp1 E0 hE0meas hE0full hshiftmeas hshiftmp
  refine ⟨E, hEmeas, hEfull, hEshift, ?_⟩
  intro η hη
  have hQ0 : Q η := by
    have h0 := hE0Q _ (hEmemQ η hη 0)
    have hid : (fun z : Site d => η ((0 : Site d) + z)) = η := by funext z; simp
    rwa [hid] at h0
  refine ⟨hQ0.1, fun y => ?_, fun a b => ?_⟩
  · obtain ⟨n, hn1, hnstab⟩ := (hE0Q _ (hEmemQ η hη y)).2.1
    refine ⟨n, hn1, fun hcon => hnstab ?_⟩
    have hiff := aux_lwc_waveStabilizable_shift η y n (0 : Site d)
    rw [add_zero] at hiff
    exact hiff.mpr hcon
  · have hfin := (hE0Q _ (hEmemQ η hη a)).2.2 (b - a)
    have heq := aux_lwc_cluster_shift d η a (0 : Site d) (b - a)
    rw [add_zero, show a + (b - a) = b from by abel] at heq
    rwa [heq] at hfin

/-- `clusterArrival` is measurable in the background.  `wave η n z t x` depends on finitely
many coordinates of `η` (`aux_lwc_wave_measurable`, by induction on `t`); a set of naturals
defined by a measurable-in-`η` condition has a measurable `sInf`-level-set
(`aux_lwc_sInf_le_measurableSet`/`aux_lwc_sInf_eq_measurableSet`, via `S = ∅ ∨ ∃ n ∈ S, n ≤ m`);
`WaveStabilizable` reduces to a single-step stability condition
(`aux_lwc_waveStabilizable_iff_step`, since the wave recursion is a deterministic function of
the previous state), making it a countable union of measurable sets; `waveThreshold`,
`waveTerminal`'s own stabilization time, `lastWave` and `penultimateWave` are each measurable by
the diagonal trick `{η | f η (g η) = k} = ⋃ n, {η | g η = n} ∩ {η | f η n = k}`; membership in
`penultimateCluster η x` is, for a fixed site, a finite (`2d`-way) disjunction over neighbours;
`clusterArrival`'s `ℕ∞`-valued `sInf` is handled via `ENat.measurable_iff` and the identity
`sInf ((Nat.cast : ℕ → ℕ∞) '' S) = (n : ℕ∞) ↔ S.Nonempty ∧ sInf S = n`; finally `ENat.toNat` and
`Nat.cast : ℕ → ℝ` are measurable for free since `ℕ∞` and `ℕ` are discrete measurable spaces. -/
theorem aux_lwc_measurable_finset_sum {α : Type*} [MeasurableSpace α] {ι : Type*} (s : Finset ι)
    (f : ι → α → ℤ) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (fun a => ∑ i ∈ s, f i a) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hnotmem ih =>
    simp only [Finset.sum_insert hnotmem]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem aux_lwc_wave_measurable {d : ℕ} (n : ℕ) (z : Site d) :
    ∀ t : ℕ, ∀ x : Site d, Measurable (fun η : Site d → ℤ => wave η n z t x) := by
  intro t
  induction t with
  | zero =>
    intro x
    simp only [wave_zero]
    split <;> exact measurable_const
  | succ t ih =>
    intro x
    by_cases hxz : x = z
    · simp [hxz]
    · have h1 : Measurable (fun η : Site d → ℤ => nbrSumZ (wave η n z t) x) := by
        unfold nbrSumZ
        exact aux_lwc_measurable_finset_sum Finset.univ
          (fun i η => wave η n z t (x + unit i) + wave η n z t (x - unit i))
          (fun i _ => (ih (x + unit i)).add (ih (x - unit i)))
      have h2 : Measurable (fun η : Site d → ℤ => nbrSumZ (wave η n z t) x + η x) :=
        h1.add (measurable_pi_apply x)
      have h3 : Measurable (fun η : Site d → ℤ =>
          (nbrSumZ (wave η n z t) x + η x) / (2 * (d:ℤ))) :=
        (Measurable.of_discrete (f := fun k : ℤ => k / (2 * (d:ℤ)))).comp h2
      simpa [wave_of_ne _ _ _ _ _ hxz] using h3

theorem aux_lwc_wave_eq_measurableSet {d : ℕ} (n : ℕ) (z : Site d) (t T : ℕ) :
    MeasurableSet {η : Site d → ℤ | wave η n z t = wave η n z T} := by
  have heq : {η : Site d → ℤ | wave η n z t = wave η n z T}
      = ⋂ x : Site d, {η : Site d → ℤ | wave η n z t x = wave η n z T x} := by
    ext η; simp [funext_iff]
  rw [heq]
  refine MeasurableSet.iInter fun x => ?_
  show MeasurableSet {η : Site d → ℤ | wave η n z t x = wave η n z T x}
  have hset : {η : Site d → ℤ | wave η n z t x = wave η n z T x}
      = (fun η : Site d → ℤ => wave η n z t x - wave η n z T x) ⁻¹' ({0} : Set ℤ) := by
    ext η; simp [sub_eq_zero]
  rw [hset]
  have hm : Measurable (fun η : Site d → ℤ => wave η n z t x - wave η n z T x) :=
    (aux_lwc_wave_measurable n z t x).sub (aux_lwc_wave_measurable n z T x)
  exact hm (MeasurableSet.of_discrete)

theorem aux_lwc_wave_fixed_of_step {d : ℕ} (η : Site d → ℤ) (n : ℕ) (z : Site d) (T : ℕ)
    (h : wave η n z (T+1) = wave η n z T) (x : Site d) (hxz : x ≠ z) :
    (nbrSumZ (wave η n z T) x + η x) / (2 * (d:ℤ)) = wave η n z T x := by
  have := congrFun h x
  rwa [wave_of_ne _ _ _ _ _ hxz] at this

theorem aux_lwc_wave_stable_of_step {d : ℕ} (η : Site d → ℤ) (n : ℕ) (z : Site d) (T : ℕ)
    (h : wave η n z (T+1) = wave η n z T) :
    ∀ k, wave η n z (T + k) = wave η n z T := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    funext x
    by_cases hxz : x = z
    · subst hxz; simp [wave_at_centre]
    · show wave η n z (T + k + 1) x = wave η n z T x
      rw [wave_of_ne _ _ _ _ _ hxz,
        show nbrSumZ (wave η n z (T+k)) x = nbrSumZ (wave η n z T) x from
          nbrSumZ_congr (fun y => congrFun ih y) x]
      exact aux_lwc_wave_fixed_of_step η n z T h x hxz

theorem aux_lwc_waveStabilizable_iff_step {d : ℕ} (η : Site d → ℤ) (n : ℕ) (z : Site d) :
    WaveStabilizable η n z ↔ ∃ T : ℕ, wave η n z (T+1) = wave η n z T := by
  constructor
  · rintro ⟨T, hT⟩
    exact ⟨T, hT (T+1) (by omega)⟩
  · rintro ⟨T, hT⟩
    refine ⟨T, fun t ht => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
    exact aux_lwc_wave_stable_of_step η n z T hT k

theorem aux_lwc_waveStabilizable_measurableSet {d : ℕ} (n : ℕ) (z : Site d) :
    MeasurableSet {η : Site d → ℤ | WaveStabilizable η n z} := by
  have heq : {η : Site d → ℤ | WaveStabilizable η n z}
      = ⋃ T : ℕ, {η | wave η n z (T+1) = wave η n z T} := by
    ext η; simp [aux_lwc_waveStabilizable_iff_step]
  rw [heq]
  exact MeasurableSet.iUnion fun T => aux_lwc_wave_eq_measurableSet n z (T+1) T

theorem aux_lwc_sInf_nat_le_iff (S : Set ℕ) (m : ℕ) :
    sInf S ≤ m ↔ S = ∅ ∨ ∃ n ∈ S, n ≤ m := by
  constructor
  · intro h
    rcases Set.eq_empty_or_nonempty S with hS | hS
    · exact Or.inl hS
    · exact Or.inr ⟨sInf S, Nat.sInf_mem hS, h⟩
  · rintro (rfl | ⟨n, hnS, hnm⟩)
    · simp
    · exact le_trans (Nat.sInf_le hnS) hnm

theorem aux_lwc_sInf_le_measurableSet {d : ℕ} (Q : ℕ → (Site d → ℤ) → Prop)
    (hQ : ∀ n, MeasurableSet {η : Site d → ℤ | Q n η}) (m : ℕ) :
    MeasurableSet {η : Site d → ℤ | sInf {n : ℕ | Q n η} ≤ m} := by
  have heq : {η : Site d → ℤ | sInf {n : ℕ | Q n η} ≤ m} =
      {η | {n : ℕ | Q n η} = ∅} ∪ ⋃ n ∈ Finset.range (m+1), {η | Q n η} := by
    ext η
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion, Finset.mem_range,
      aux_lwc_sInf_nat_le_iff]
    constructor
    · rintro (h | ⟨n, hn, hm⟩)
      · exact Or.inl h
      · exact Or.inr ⟨n, by omega, hn⟩
    · rintro (h | ⟨n, hn, hQ'⟩)
      · exact Or.inl h
      · exact Or.inr ⟨n, hQ', by omega⟩
  rw [heq]
  refine MeasurableSet.union ?_ (MeasurableSet.biUnion (Finset.range (m+1)).countable_toSet
    (fun n _ => hQ n))
  have heq2 : {η : Site d → ℤ | {n : ℕ | Q n η} = ∅} = ⋂ n : ℕ, {η | Q n η}ᶜ := by
    ext η; simp [Set.eq_empty_iff_forall_notMem]
  rw [heq2]
  exact MeasurableSet.iInter fun n => (hQ n).compl

theorem aux_lwc_sInf_eq_measurableSet {d : ℕ} (Q : ℕ → (Site d → ℤ) → Prop)
    (hQ : ∀ n, MeasurableSet {η : Site d → ℤ | Q n η}) (m : ℕ) :
    MeasurableSet {η : Site d → ℤ | sInf {n : ℕ | Q n η} = m} := by
  cases m with
  | zero => simpa using aux_lwc_sInf_le_measurableSet Q hQ 0
  | succ m =>
    have heq : {η : Site d → ℤ | sInf {n : ℕ | Q n η} = m + 1} =
        {η | sInf {n : ℕ | Q n η} ≤ m+1} \ {η | sInf {n : ℕ | Q n η} ≤ m} := by
      ext η; simp only [Set.mem_setOf_eq, Set.mem_sdiff]; omega
    rw [heq]
    exact (aux_lwc_sInf_le_measurableSet Q hQ (m+1)).diff (aux_lwc_sInf_le_measurableSet Q hQ m)

theorem aux_lwc_waveThreshold_measurableSet_le {d : ℕ} (z : Site d) (m' : ℕ) :
    MeasurableSet {η : Site d → ℤ | waveThreshold η z ≤ m'} := by
  simp only [waveThreshold]
  refine aux_lwc_sInf_le_measurableSet (fun n η => 1 ≤ n ∧ ¬ WaveStabilizable η n z) ?_ m'
  intro n
  by_cases hn : 1 ≤ n
  · have hset : {η : Site d → ℤ | 1 ≤ n ∧ ¬ WaveStabilizable η n z}
        = {η | WaveStabilizable η n z}ᶜ := by
      ext η; simp [hn]
    rw [hset]
    exact (aux_lwc_waveStabilizable_measurableSet n z).compl
  · have hset : {η : Site d → ℤ | 1 ≤ n ∧ ¬ WaveStabilizable η n z} = ∅ := by
      ext η; simp [hn]
    rw [hset]; exact MeasurableSet.empty

theorem aux_lwc_waveThreshold_measurableSet {d : ℕ} (z : Site d) (m : ℕ) :
    MeasurableSet {η : Site d → ℤ | waveThreshold η z = m} := by
  cases m with
  | zero => simpa using aux_lwc_waveThreshold_measurableSet_le z 0
  | succ m =>
    have heq : {η : Site d → ℤ | waveThreshold η z = m + 1} =
        {η | waveThreshold η z ≤ m+1} \ {η | waveThreshold η z ≤ m} := by
      ext η; simp only [Set.mem_setOf_eq, Set.mem_sdiff]; omega
    rw [heq]
    exact (aux_lwc_waveThreshold_measurableSet_le z (m+1)).diff
      (aux_lwc_waveThreshold_measurableSet_le z m)

theorem aux_lwc_waveThreshold_measurable {d : ℕ} (z : Site d) :
    Measurable (fun η : Site d → ℤ => waveThreshold η z) :=
  measurable_to_countable' (aux_lwc_waveThreshold_measurableSet z)

/-- The `wave`-stabilization time for fixed `n`, `z` (the sInf inside `waveTerminal`). -/
noncomputable def aux_lwc_Tstar {d : ℕ} (η : Site d → ℤ) (n : ℕ) (z : Site d) : ℕ :=
  sInf {T : ℕ | ∀ t, T ≤ t → wave η n z t = wave η n z T}

theorem aux_lwc_Tstar_eq_step {d : ℕ} (η : Site d → ℤ) (n : ℕ) (z : Site d) :
    {T : ℕ | ∀ t, T ≤ t → wave η n z t = wave η n z T} = {T | wave η n z (T+1) = wave η n z T} := by
  ext T
  constructor
  · intro h; exact h (T+1) (by omega)
  · intro h t ht
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
    exact aux_lwc_wave_stable_of_step η n z T h k

theorem aux_lwc_Tstar_measurableSet_le {d : ℕ} (n : ℕ) (z : Site d) (m : ℕ) :
    MeasurableSet {η : Site d → ℤ | aux_lwc_Tstar η n z ≤ m} := by
  show MeasurableSet {η : Site d → ℤ |
      sInf {T : ℕ | ∀ t, T ≤ t → wave η n z t = wave η n z T} ≤ m}
  refine aux_lwc_sInf_le_measurableSet (fun T η => ∀ t, T ≤ t → wave η n z t = wave η n z T) ?_ m
  intro T
  have heq : {η : Site d → ℤ | ∀ t, T ≤ t → wave η n z t = wave η n z T} =
      {η | wave η n z (T+1) = wave η n z T} := by
    ext η; simpa using Set.ext_iff.mp (aux_lwc_Tstar_eq_step η n z) T
  rw [heq]
  exact aux_lwc_wave_eq_measurableSet n z (T+1) T

theorem aux_lwc_Tstar_measurable {d : ℕ} (n : ℕ) (z : Site d) :
    Measurable (fun η : Site d → ℤ => aux_lwc_Tstar η n z) := by
  refine measurable_to_countable' fun m => ?_
  show MeasurableSet {η : Site d → ℤ | aux_lwc_Tstar η n z = m}
  cases m with
  | zero => simpa using aux_lwc_Tstar_measurableSet_le n z 0
  | succ m =>
    have heq : {η : Site d → ℤ | aux_lwc_Tstar η n z = m + 1} =
        {η | aux_lwc_Tstar η n z ≤ m+1} \ {η | aux_lwc_Tstar η n z ≤ m} := by
      ext η; simp only [Set.mem_setOf_eq, Set.mem_sdiff]; omega
    rw [heq]
    exact (aux_lwc_Tstar_measurableSet_le n z (m+1)).diff (aux_lwc_Tstar_measurableSet_le n z m)

theorem aux_lwc_waveTerminal_eq {d : ℕ} (η : Site d → ℤ) (n : ℕ) (z : Site d) (x : Site d) :
    waveTerminal η n z x = wave η n z (aux_lwc_Tstar η n z) x := rfl

theorem aux_lwc_waveTerminal_measurable {d : ℕ} (n : ℕ) (z : Site d) (x : Site d) :
    Measurable (fun η : Site d → ℤ => waveTerminal η n z x) := by
  simp only [aux_lwc_waveTerminal_eq]
  refine measurable_to_countable' fun k => ?_
  show MeasurableSet {η : Site d → ℤ | wave η n z (aux_lwc_Tstar η n z) x = k}
  have heq : {η : Site d → ℤ | wave η n z (aux_lwc_Tstar η n z) x = k}
      = ⋃ T : ℕ, {η | aux_lwc_Tstar η n z = T} ∩ {η | wave η n z T x = k} := by
    ext η
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨aux_lwc_Tstar η n z, rfl, h⟩
    · rintro ⟨T, hT, hk⟩; rw [hT]; exact hk
  rw [heq]
  refine MeasurableSet.iUnion fun T => ?_
  refine MeasurableSet.inter ?_ ?_
  · exact aux_lwc_Tstar_measurable n z (MeasurableSet.of_discrete (s := ({T} : Set ℕ)))
  · exact aux_lwc_wave_measurable n z T x (MeasurableSet.of_discrete (s := ({k} : Set ℤ)))

theorem aux_lwc_penultimateWave_measurable {d : ℕ} (z : Site d) (x : Site d) :
    Measurable (fun η : Site d → ℤ => penultimateWave η z x) := by
  unfold penultimateWave
  simp only [apply_ite (fun (f : Site d → ℤ) => f x), Pi.zero_apply]
  apply Measurable.ite (aux_lwc_waveThreshold_measurableSet z 1) measurable_const
  refine measurable_to_countable' fun k => ?_
  show MeasurableSet {η : Site d → ℤ | waveTerminal η (waveThreshold η z - 1) z x = k}
  have heq : {η : Site d → ℤ | waveTerminal η (waveThreshold η z - 1) z x = k}
      = ⋃ n : ℕ, {η | waveThreshold η z = n} ∩ {η | waveTerminal η (n-1) z x = k} := by
    ext η
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨waveThreshold η z, rfl, h⟩
    · rintro ⟨n, hn, hk⟩; rw [hn]; exact hk
  rw [heq]
  exact MeasurableSet.iUnion fun n =>
    MeasurableSet.inter (aux_lwc_waveThreshold_measurableSet z n)
      (aux_lwc_waveTerminal_measurable (n-1) z x (MeasurableSet.of_discrete (s := ({k} : Set ℤ))))

theorem aux_lwc_penultimateCluster_mem_measurableSet {d : ℕ} (z w : Site d) :
    MeasurableSet {η : Site d → ℤ | w ∈ penultimateCluster η z} := by
  by_cases hwz : w = z
  · have hu : {η : Site d → ℤ | w ∈ penultimateCluster η z} = Set.univ := by
      ext η; simp [penultimateCluster, hwz]
    rw [hu]; exact MeasurableSet.univ
  · have heq : {η : Site d → ℤ | w ∈ penultimateCluster η z}
        = ⋃ i : Fin d, ({η : Site d → ℤ | 0 < penultimateWave η z (w + unit i)} ∪
            {η : Site d → ℤ | 0 < penultimateWave η z (w - unit i)}) := by
      ext η
      simp only [penultimateCluster, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, hwz,
        false_or, Set.mem_iUnion]
      constructor
      · rintro ⟨y, hadj, hpos⟩
        obtain ⟨i, hi | hi⟩ := hadj
        · refine ⟨i, Or.inr ?_⟩
          have hyi : w - unit i = y := by rw [hi]; abel
          rwa [hyi]
        · refine ⟨i, Or.inl ?_⟩
          rwa [hi.symm]
      · rintro ⟨i, hi | hi⟩
        · exact ⟨w + unit i, ⟨i, Or.inr rfl⟩, hi⟩
        · exact ⟨w - unit i, ⟨i, Or.inl (by abel)⟩, hi⟩
    rw [heq]
    exact MeasurableSet.iUnion fun i =>
      MeasurableSet.union
        ((aux_lwc_penultimateWave_measurable z (w+unit i)) (MeasurableSet.of_discrete (s := Set.Ioi (0:ℤ))))
        ((aux_lwc_penultimateWave_measurable z (w-unit i)) (MeasurableSet.of_discrete (s := Set.Ioi (0:ℤ))))

theorem aux_lwc_lastWave_measurable {d : ℕ} (z : Site d) (t : ℕ) (x : Site d) :
    Measurable (fun η : Site d → ℤ => lastWave η z t x) := by
  simp only [lastWave]
  refine measurable_to_countable' fun k => ?_
  show MeasurableSet {η : Site d → ℤ | wave η (waveThreshold η z) z t x = k}
  have heq : {η : Site d → ℤ | wave η (waveThreshold η z) z t x = k}
      = ⋃ n : ℕ, {η | waveThreshold η z = n} ∩ {η | wave η n z t x = k} := by
    ext η
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨waveThreshold η z, rfl, h⟩
    · rintro ⟨n, hn, hk⟩; rw [hn]; exact hk
  rw [heq]
  exact MeasurableSet.iUnion fun n =>
    MeasurableSet.inter (aux_lwc_waveThreshold_measurableSet z n)
      (aux_lwc_wave_measurable n z t x (MeasurableSet.of_discrete (s := ({k} : Set ℤ))))

theorem aux_lwc_sInf_natCast_le (S : Set ℕ) :
    ((sInf S : ℕ) : ℕ∞) ≤ sInf ((Nat.cast : ℕ → ℕ∞) '' S) := by
  refine le_sInf ?_
  rintro k ⟨m, hm, rfl⟩
  exact_mod_cast Nat.sInf_le hm

theorem aux_lwc_sInf_natCast_ge (S : Set ℕ) (hS : S.Nonempty) :
    sInf ((Nat.cast : ℕ → ℕ∞) '' S) ≤ ((sInf S : ℕ) : ℕ∞) :=
  sInf_le ⟨sInf S, Nat.sInf_mem hS, rfl⟩

theorem aux_lwc_sInf_natCast_eq_iff (S : Set ℕ) (n : ℕ) :
    sInf ((Nat.cast : ℕ → ℕ∞) '' S) = (n : ℕ∞) ↔ S.Nonempty ∧ sInf S = n := by
  constructor
  · intro h
    rcases Set.eq_empty_or_nonempty S with hS | hS
    · simp [hS] at h
    · refine ⟨hS, ?_⟩
      have h1 := aux_lwc_sInf_natCast_le S
      have h2 := aux_lwc_sInf_natCast_ge S hS
      rw [h] at h1 h2
      exact_mod_cast le_antisymm h1 h2
  · rintro ⟨hS, hn⟩
    have h1 := aux_lwc_sInf_natCast_le S
    have h2 := aux_lwc_sInf_natCast_ge S hS
    rw [hn] at h1 h2
    exact le_antisymm h2 h1

theorem aux_lwc_clusterCond_measurableSet {d : ℕ} (y x : Site d) (m : ℕ) :
    MeasurableSet {η : Site d → ℤ | 1 ≤ m ∧ ∀ w ∈ penultimateCluster η x, 0 < lastWave η y m w} := by
  have heq : {η : Site d → ℤ | 1 ≤ m ∧ ∀ w ∈ penultimateCluster η x, 0 < lastWave η y m w}
      = (if 1 ≤ m then Set.univ else ∅) ∩
        ⋂ w : Site d, ({η : Site d → ℤ | w ∈ penultimateCluster η x}ᶜ ∪
          {η : Site d → ℤ | 0 < lastWave η y m w}) := by
    ext η
    by_cases hm : 1 ≤ m <;> simp [hm, imp_iff_not_or]
  rw [heq]
  refine MeasurableSet.inter (by split <;> simp) ?_
  refine MeasurableSet.iInter fun w => MeasurableSet.union
    (aux_lwc_penultimateCluster_mem_measurableSet x w).compl
    ((aux_lwc_lastWave_measurable y m w) (MeasurableSet.of_discrete (s := Set.Ioi (0:ℤ))))

theorem aux_lwc_clusterArrival_measurable {d : ℕ} (y x : Site d) :
    Measurable (fun η : Site d → ℤ => clusterArrival η y x) := by
  rw [ENat.measurable_iff]
  intro n
  show MeasurableSet {η : Site d → ℤ | clusterArrival η y x = (n:ℕ∞)}
  have hrw : ∀ η : Site d → ℤ, clusterArrival η y x =
      sInf ((Nat.cast : ℕ → ℕ∞) ''
        {m : ℕ | 1 ≤ m ∧ ∀ w ∈ penultimateCluster η x, 0 < lastWave η y m w}) := by
    intro η
    unfold clusterArrival
    congr 1
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨m, rfl, h1, h2⟩; exact ⟨m, ⟨h1, h2⟩, rfl⟩
    · rintro ⟨m, ⟨h1, h2⟩, rfl⟩; exact ⟨m, rfl, h1, h2⟩
  have heq : {η : Site d → ℤ | clusterArrival η y x = (n:ℕ∞)}
      = {η | {m : ℕ | 1 ≤ m ∧ ∀ w ∈ penultimateCluster η x, 0 < lastWave η y m w}.Nonempty ∧
          sInf {m : ℕ | 1 ≤ m ∧ ∀ w ∈ penultimateCluster η x, 0 < lastWave η y m w} = n} := by
    ext η
    rw [Set.mem_setOf_eq, hrw η, aux_lwc_sInf_natCast_eq_iff]
    rfl
  rw [heq]
  refine MeasurableSet.inter ?_ (aux_lwc_sInf_eq_measurableSet _ (aux_lwc_clusterCond_measurableSet y x) n)
  show MeasurableSet {η : Site d → ℤ |
      {m : ℕ | 1 ≤ m ∧ ∀ w ∈ penultimateCluster η x, 0 < lastWave η y m w}.Nonempty}
  have heq2 : {η : Site d → ℤ |
      {m : ℕ | 1 ≤ m ∧ ∀ w ∈ penultimateCluster η x, 0 < lastWave η y m w}.Nonempty}
      = ⋃ m : ℕ, {η | 1 ≤ m ∧ ∀ w ∈ penultimateCluster η x, 0 < lastWave η y m w} := by
    ext η; simp [Set.Nonempty]
  rw [heq2]
  exact MeasurableSet.iUnion fun m => aux_lwc_clusterCond_measurableSet y x m

theorem aux_lwc_measurable (d : ℕ) (a b : Site d) :
    Measurable (fun η : Site d → ℤ => ((clusterArrival η a b).toNat : ℝ)) :=
  (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp
    ((Measurable.of_discrete (f := (ENat.toNat : ℕ∞ → ℕ))).comp
      (aux_lwc_clusterArrival_measurable a b))

/-- `(log n)^γ1 + (log n)^γ2 ≤ (log n)^(max γ1 γ2 + 1)` for `n` large: each summand is at most
`(log n)^(max γ1 γ2)` once `log n ≥ 1`, and `2 t ≤ t^{1}·t = t^{max+1}/t^{max}` scaling once
`log n ≥ 2` folds the factor `2` into one extra power. -/
theorem aux_lwc_cluster_lipschitz_1_1 (γ1 γ2 : ℝ) :
    ∀ᶠ n : ℕ in atTop, Real.log n ^ γ1 + Real.log n ^ γ2 ≤ Real.log n ^ (max γ1 γ2 + 1) := by
  have htend : Filter.Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [htend.eventually_ge_atTop 2] with n hn
  have h1 : Real.log n ^ γ1 ≤ Real.log n ^ (max γ1 γ2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
  have h2 : Real.log n ^ γ2 ≤ Real.log n ^ (max γ1 γ2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_right _ _)
  have h3 : 2 * Real.log n ^ (max γ1 γ2) ≤ Real.log n ^ (max γ1 γ2 + 1) := by
    rw [Real.rpow_add (by linarith), Real.rpow_one]
    nlinarith [Real.rpow_nonneg (show (0:ℝ) ≤ Real.log n by linarith) (max γ1 γ2)]
  linarith

/-- Lemma 3.6 (`penultimate_upper_bound`) and Lemma 3.7 (`last_penultimate_close`) combined:
`clusterArrival η 0 x = b ≤ a + (log n)^γ2 ≤ C·mnorm x + (log n)^γ1 + (log n)^γ2`, with `a :=
lastArrival η 0 x`; the two polylog error terms are folded into one via
`aux_lwc_cluster_lipschitz_1_1`. -/
theorem aux_lwc_cluster_lipschitz_1_2 (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧ ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ∀ x : Site d, mnorm x ≤ (n:ℤ) → ∃ a : ℕ, clusterArrival η (0:Site d) x = (a:ℕ∞) ∧
        (a:ℝ) ≤ C * (mnorm x : ℝ) + Real.log n ^ γ := by
  obtain ⟨γ1, C, hγ1, hC, hub⟩ :=
    Exploding.Frozen.penultimate_upper_bound d hd p hp hp1 hLSSB hHole hChem
  obtain ⟨γ2, hγ2, hclose⟩ :=
    Exploding.Frozen.last_penultimate_close d hd p hp hp1 hLSSB hHole hChem
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (aux_lwc_cluster_lipschitz_1_1 γ1 γ2)
  refine ⟨max γ1 γ2 + 1, C, by positivity, hC, ?_⟩
  filter_upwards [hub, hclose] with η hηub hηclose
  obtain ⟨n0, hn0⟩ := hηub
  obtain ⟨n0', hn0'⟩ := hηclose
  refine ⟨max (max n0 n0') N, fun n hn x hx => ?_⟩
  obtain ⟨m, hma, hmb⟩ := hn0 n (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn) x hx
  obtain ⟨_, a, b, hla, hcb, hab⟩ :=
    hn0' n (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn) x hx
  refine ⟨b, hcb, ?_⟩
  have hae : a = m := by exact_mod_cast hla.symm.trans hma
  rw [hae] at hab
  have hlog := hN n (le_trans (le_max_right _ _) hn)
  linarith

/-- `Real.log (d * n) ≤ 2 * Real.log n` once `n ≥ d` (so `d * n ≥ 1`), via `Real.log_mul` and
`Real.log_le_log` applied to `d ≤ n`. -/
theorem aux_lwc_cluster_lipschitz_1_3 (d : ℕ) (hd : 1 ≤ d) :
    ∀ᶠ n : ℕ in atTop, Real.log ((d:ℝ) * n) ≤ 2 * Real.log n := by
  have hntend : Filter.Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hntend.eventually_ge_atTop (d:ℝ)] with n hn
  have hdpos : (0:ℝ) < d := by exact_mod_cast hd
  have hnpos : (0:ℝ) < n := lt_of_lt_of_le hdpos hn
  rw [Real.log_mul (by positivity) (by positivity)]
  have hle : Real.log d ≤ Real.log n := Real.log_le_log hdpos hn
  linarith

/-- `c * (log n)^γ ≤ (log n)^(γ+1)` for `n` large (once `log n ≥ max c 1`): a fixed constant
multiple is absorbed by one extra power of `log n`. -/
theorem aux_lwc_cluster_lipschitz_1_4 (γ c : ℝ) :
    ∀ᶠ n : ℕ in atTop, c * Real.log n ^ γ ≤ Real.log n ^ (γ+1) := by
  have htend : Filter.Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [htend.eventually_ge_atTop (max c 1)] with n hn
  rw [Real.rpow_add (by linarith [le_max_right c (1:ℝ)]), Real.rpow_one]
  have hlog1 : (1:ℝ) ≤ Real.log n := le_trans (le_max_right c 1) hn
  have hlogc : c ≤ Real.log n := le_trans (le_max_left c 1) hn
  have hpow_nonneg : 0 ≤ Real.log n ^ γ := Real.rpow_nonneg (by linarith) γ
  nlinarith

/-- `(log (d*n))^γ ≤ (log n)^(γ+1)` for `n` large: combines
`aux_lwc_cluster_lipschitz_1_3` (`log (dn) ≤ 2 log n`), `Real.rpow_le_rpow` (monotone in the
base) and `aux_lwc_cluster_lipschitz_1_4` (absorbing the factor `2^γ`). -/
theorem aux_lwc_cluster_lipschitz_1_5 (d : ℕ) (hd : 1 ≤ d) (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ n : ℕ in atTop, Real.log ((d:ℝ) * n) ^ γ ≤ Real.log n ^ (γ+1) := by
  have hntend : Filter.Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [aux_lwc_cluster_lipschitz_1_3 d hd, hntend.eventually_ge_atTop 1,
    aux_lwc_cluster_lipschitz_1_4 γ (2^γ)] with n h1 h2 h3
  have hdpos : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hdn1 : (1:ℝ) ≤ (d:ℝ) * n := by nlinarith
  have h4 : Real.log ((d:ℝ)*n) ^ γ ≤ (2 * Real.log n) ^ γ :=
    Real.rpow_le_rpow (Real.log_nonneg hdn1) h1 hγ.le
  have h5 : (2 * Real.log n) ^ γ = 2 ^ γ * Real.log n ^ γ :=
    Real.mul_rpow (by norm_num) (Real.log_nonneg h2)
  rw [h5] at h4
  linarith

/-- `cent d n ⊆ {x | mnorm x ≤ d*n}`: the sup-norm box of radius `n` has `L¹`-norm at most
`d * n`, summing the `d` coordinate bounds via `Finset.sum_le_sum`. -/
theorem aux_lwc_cluster_lipschitz_1_6 (d n : ℕ) (x : Site d) (hx : x ∈ cent d n) :
    mnorm x ≤ (d : ℤ) * n := by
  have h1 : mnorm x ≤ ∑ _i : Fin d, (n : ℤ) := by
    apply Finset.sum_le_sum
    intro i _
    exact hx i
  simpa [Finset.sum_const, Finset.card_univ] using h1

/-- Step 1 (the first bound alone, `T̃(x) ≤ C|x| + (log n)^γ`, `x ∈ cent d n`).  Applies
`aux_lwc_cluster_lipschitz_1_2` at the rescaled threshold `d * n` (since `x ∈ cent d n` only
gives `mnorm x ≤ d * n`, by `aux_lwc_cluster_lipschitz_1_6`), then folds `Real.log (d*n)^γ`
back down to `Real.log n^(γ+1)` via `aux_lwc_cluster_lipschitz_1_5`. -/
theorem aux_lwc_cluster_lipschitz_1 (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧ ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ∀ x ∈ cent d n, ∃ a : ℕ, clusterArrival η (0 : Site d) x = (a : ℕ∞) ∧
        (a : ℝ) ≤ C * (mnorm x : ℝ) + Real.log n ^ γ := by
  obtain ⟨γ, C, hγ, hC, hbase⟩ := aux_lwc_cluster_lipschitz_1_2 d hd p hp hp1 hLSSB hHole hChem
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.mp (aux_lwc_cluster_lipschitz_1_5 d (by omega) γ hγ)
  refine ⟨γ+1, C, by positivity, hC, ?_⟩
  filter_upwards [hbase] with η hη
  obtain ⟨n0, hn0⟩ := hη
  refine ⟨max ((d + 1) * n0 + 1) N, fun n hn x hx => ?_⟩
  have hxm : mnorm x ≤ ((d:ℤ) * n) := aux_lwc_cluster_lipschitz_1_6 d n x hx
  obtain ⟨a, ha, hab⟩ := hn0 (d * n) (by nlinarith [le_trans (le_max_left _ _) hn]) x
    (by push_cast; linarith)
  refine ⟨a, ha, le_trans hab ?_⟩
  have := hN n (le_trans (le_max_right _ _) hn)
  push_cast
  linarith

/-- Step 2 (the "near" case of the second bound: `T̃(x') ≤ T̃(x) + C|x - x'| + (log n)^γ`).
CORRECTION (2026-09-24): the previous note above claimed this is "immediate from Step 1
applied at `x'` alone", but that is FALSE as it stands: `Step 1` only gives an UPPER bound
`b ≤ C mnorm x' + (log n)^γ`, and `mnorm x' ≤ mnorm x + mnorm (x - x')` (triangle inequality)
only lets you bound `b` by `C mnorm x + C mnorm (x-x') + (log n)^γ`, not by `a + C mnorm
(x-x') + (log n)^γ` — that substitution needs a LOWER bound `C mnorm x ≤ a`, which `Step 1`
does not supply (`a` could be much smaller than `C mnorm x`). The routine substitution the old
note describes does not exist; this GAP needs either `Exploding.Frozen.approx_subadditivity`
applied at `(0, x, x')` (giving `clusterArrival η 0 x' ≤ clusterArrival η 0 x + clusterArrival
η x x'`, itself circular unless `clusterArrival η x x'` is bounded directly, e.g. by
`Exploding.Frozen.local_convexity` alone when `mnorm (x - x')` is within a `(log n)^{γ'}`-type
budget) or the same connectivity argument as `aux_lwc_cluster_lipschitz_3`; a genuine
unformalized geometric fact, not attempted here for time. -/
theorem aux_lwc_cluster_lipschitz_2 (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧ ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ∀ x ∈ cent d n, ∀ x' ∈ cent d n, ∃ a b : ℕ,
        clusterArrival η (0 : Site d) x = (a : ℕ∞) ∧ clusterArrival η (0 : Site d) x' = (b : ℕ∞) ∧
          (a : ℝ) ≤ C * (mnorm x : ℝ) + Real.log n ^ γ ∧
          (b : ℝ) ≤ (a : ℝ) + C * (mnorm (x - x') : ℝ) + Real.log n ^ γ := by
  sorry

/-- **GAP** (genuine new geometric content, absent from this file and from `Support/*.lean`):
the "far" case of the second bound, where `T̂(x) ≤ T̃(x)` and the support of the last wave from
`0` (connected, since `η ≤ 2d - 1` makes every toppled site's cause a toppled neighbour)
contains a path of distinct points from `0` to `x`.  `Exploding.Frozen.local_convexity`
(Lemma 2.1, itself still `sorry` in `Exploding/Frozen/LocalConvexity.lean`, a DIFFERENT node's
frozen statement, citable here regardless) fills the bounding rectangle of the path's last
`(log n)^{γ'}` points within `(log n)^{dγ'}` steps; that rectangle, of side at least
`(log n)^{γ'/d}`, meets a cube of the infinite cluster `C_∞` of `renormalization_properties`
(Proposition 2.2) by its hole bound, within distance `(log n)^{γ'}` of `x`; from there the
chemical-distance bound of Proposition 2.2 and a repeat of Lemma 3.6's argument reach and fill
`P(x')` within `C|x - x'| + (log n)^γ` further steps.  This is a genuinely new multi-step
geometric construction (connectivity of the last-wave's support, extracting a path, applying
`local_convexity` to a *sub*-path of the last `(log n)^{γ'}` points, then bridging into the
renormalization cluster) that does not reduce to any single already-available lemma; it is the
true mathematical core of Lemma 3.6's "from any point" extension and needs its own further
decomposition (path-extraction, rectangle side-length, hole-to-cluster bridge, chemical-distance
bound) before any piece of it is small enough to attempt. -/
theorem aux_lwc_cluster_lipschitz_3 (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧ ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ∀ x ∈ cent d n, ∀ x' ∈ cent d n, ∃ a b : ℕ,
        clusterArrival η (0 : Site d) x = (a : ℕ∞) ∧ clusterArrival η (0 : Site d) x' = (b : ℕ∞) ∧
          (b : ℝ) ≤ (a : ℝ) + C * (mnorm (x - x') : ℝ) + Real.log n ^ γ := by
  have h2 := aux_lwc_cluster_lipschitz_2 d hd p hp hp1 hLSSB hHole hChem
  rcases h2 with ⟨γ, C, hγ, hC, h⟩
  refine ⟨γ, C, hγ, hC, ?_⟩
  filter_upwards [h] with η hη
  rcases hη with ⟨n0, hn0⟩
  refine ⟨n0, ?_⟩
  intro n hn x hx x' hx'
  rcases hn0 n hn x hx x' hx' with ⟨a, b, ha, hb, ha_bound, hb_bound⟩
  exact ⟨a, b, ha, hb, hb_bound⟩

/-- The two bounds `eq:lastwave_lipschitz` of the proof of Proposition 3.1: on an event of
probability one, for `n` large and `x, x' ∈ [-n, n]^d`, `T̃(x) ≤ C|x| + (log n)^γ` and
`T̃(x') ≤ T̃(x) + C|x - x'| + (log n)^γ`.  The first is Lemmas 3.6 and 3.7
(`aux_lwc_cluster_lipschitz_1`).  The second splits into the "near" case
(`aux_lwc_cluster_lipschitz_2`, immediate from the first) and the "far" case
(`aux_lwc_cluster_lipschitz_3`, the genuine geometric GAP): assembly needs only intersecting
the a.e. events of `_1` and `_3` (both already stated with the shared `γ, C`, at the cost of
picking the larger of the two witnesses first) and case-splitting on `mnorm (x - x') ≤ (log
n)^{γ'}` for some auxiliary `γ'` between the two regimes; not attempted here for time, since it
inherits `_1` and `_3`'s `sorry`s regardless. -/
theorem aux_lwc_cluster_lipschitz (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧ ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ∀ x ∈ cent d n, ∀ x' ∈ cent d n, ∃ a b : ℕ,
        clusterArrival η (0 : Site d) x = (a : ℕ∞) ∧ clusterArrival η (0 : Site d) x' = (b : ℕ∞) ∧
          (a : ℝ) ≤ C * (mnorm x : ℝ) + Real.log n ^ γ ∧
          (b : ℝ) ≤ (a : ℝ) + C * (mnorm (x - x') : ℝ) + Real.log n ^ γ := by
  sorry

/-- The event `A_K = {x : ∀ n, g n x ≤ C n + K}` has positive measure for some natural `K`:
each `A_K` is measurable (`measurableSet_le`, countable intersection over `n`), and if every
`A_K` had measure `0` the countable union `⋃ K, A_K` would too (`measure_iUnion_null`), which
contradicts `hlin` making that union a.e. all of `Ω` (`prob_compl_eq_zero_iff`). -/
theorem aux_lwc_kingman_linear_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (C : ℝ) (g : ℕ → Ω → ℝ) (hgm : ∀ n, Measurable (g n))
    (hlin : ∀ᵐ x ∂μ, ∃ K : ℝ, ∀ n : ℕ, g n x ≤ C * n + K) :
    ∃ K : ℕ, 0 < μ {x | ∀ n : ℕ, g n x ≤ C * n + K} := by
  have hmeas : ∀ K : ℕ, MeasurableSet {x : Ω | ∀ n : ℕ, g n x ≤ C * n + K} := by
    intro K
    have hset : {x : Ω | ∀ n : ℕ, g n x ≤ C * (n:ℝ) + K} = ⋂ n, {x | g n x ≤ C * (n:ℝ) + K} := by
      ext x; simp
    rw [hset]
    exact MeasurableSet.iInter (fun n => measurableSet_le (hgm n) measurable_const)
  have hmeasU : MeasurableSet (⋃ K : ℕ, {x : Ω | ∀ n : ℕ, g n x ≤ C * (n:ℝ) + K}) :=
    MeasurableSet.iUnion hmeas
  have hmem : ∀ᵐ x ∂μ, x ∈ ⋃ K : ℕ, {x : Ω | ∀ n : ℕ, g n x ≤ C * (n:ℝ) + K} := by
    filter_upwards [hlin] with x hx
    obtain ⟨K, hK⟩ := hx
    exact Set.mem_iUnion.mpr ⟨⌈K⌉₊, fun n => le_trans (hK n) (by gcongr; exact Nat.le_ceil K)⟩
  have hcompl_null : μ (⋃ K : ℕ, {x : Ω | ∀ n : ℕ, g n x ≤ C * (n:ℝ) + K})ᶜ = 0 := hmem
  have hfull : μ (⋃ K : ℕ, {x : Ω | ∀ n : ℕ, g n x ≤ C * (n:ℝ) + K}) = 1 :=
    (prob_compl_eq_zero_iff hmeasU).mp hcompl_null
  by_contra hcon
  push_neg at hcon
  have hzero : ∀ K : ℕ, μ {x | ∀ n : ℕ, g n x ≤ C * (n:ℝ) + K} = 0 :=
    fun K => nonpos_iff_eq_zero.mp (hcon K)
  rw [measure_iUnion_null hzero] at hfull
  exact zero_ne_one hfull

/-- The a.e.-defined first return time to `A` under `T`: `0` (junk) off the a.e.-full set of
points that return.  Needs `T`'s conservativity on `A` (from `herg.toConservative` / Poincaré
recurrence, `MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem`) to know the defining
set is a.e. nonempty; the definition itself needs no such hypothesis. -/
noncomputable def aux_lwc_returnTime {Ω : Type*} (T : Ω → Ω) (A : Set Ω) (x : Ω) : ℕ :=
  sInf {n : ℕ | 1 ≤ n ∧ T^[n] x ∈ A}

/-- The induced (first-return) map on `A`. -/
noncomputable def aux_lwc_inducedMap {Ω : Type*} (T : Ω → Ω) (A : Set Ω) (x : Ω) : Ω :=
  T^[aux_lwc_returnTime T A x] x

/-- GAP (needs ergodic-theory content absent from Mathlib and from Lattice-Probability): the
induced map on `A` is a.e. well defined, measurable, and is measure preserving and ergodic for
the renormalized restriction of `μ` to `A`.  Textbook fact (e.g. Walters, *An Introduction to
Ergodic Theory*, Theorem 1.5), not present in Mathlib's `Dynamics/Ergodic/Conservative.lean`
(only the weaker a.e.-recurrence `Conservative.ae_mem_imp_frequently_image_mem`) or anywhere
searched in `Lattice-Probability`. -/
theorem aux_lwc_kingman_linear_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (T : Ω → Ω) (herg : Ergodic T μ) (A : Set Ω)
    (hAmeas : MeasurableSet A) (hApos : 0 < μ A) :
    ∃ T' : Ω → Ω, Measurable T' ∧ (∀ᵐ x ∂μ, x ∈ A → aux_lwc_inducedMap T A x = T' x) ∧
      MeasurePreserving T' (ENNReal.ofReal (μ A).toReal⁻¹ • μ.restrict A)
        (ENNReal.ofReal (μ A).toReal⁻¹ • μ.restrict A) ∧
      Ergodic T' (ENNReal.ofReal (μ A).toReal⁻¹ • μ.restrict A) := by
  sorry

/-- **Kac's return-time lemma** (GAP: absent from Mathlib and from Lattice-Probability; exactly
the "general result, to be added to Lattice-Probability next to `LatticeProb.ae_tendsto_div`"
that the top-of-file report names): the first return time to `A` is integrable on `A`, with
`∫_A (aux_lwc_returnTime T A) ∂μ = μ A` (so mean `1` under the renormalized restriction of
`aux_lwc_kingman_linear_2`). -/
theorem aux_lwc_kingman_linear_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (T : Ω → Ω) (herg : Ergodic T μ) (A : Set Ω)
    (hAmeas : MeasurableSet A) (hApos : 0 < μ A) :
    IntegrableOn (fun x => (aux_lwc_returnTime T A x : ℝ)) A μ ∧
      ∫ x in A, (aux_lwc_returnTime T A x : ℝ) ∂μ = (μ A).toReal := by
  sorry

/-- Kingman's subadditive ergodic theorem without a moment bound (proof of Proposition 3.1;
the same statement as `aux_glw_kingman_linear` in the design of Proposition 5.1).  For an
ergodic `T` and a nonnegative measurable subadditive `g` with an almost sure linear bound
`hlin` and the Lipschitz control `hlip`, `g n / n` converges a.e. to a constant.

DECOMPOSITION.  `aux_lwc_kingman_linear_1` gives the event `A = A_K` of positive measure.  The
remaining steps, in order, are:

  (i)   `G j := g ∘ (aux_lwc_returnTime T A)`-iterated, i.e. `G j x = g (r_j x) x` where
        `r_j` is the `j`-th iterate return time (`r_j = r_{j-1} + r ∘ T'^[j-1]`, `T'` from
        `aux_lwc_kingman_linear_2`); `G` is `SubadditiveAlong T'` by telescoping `hsub` along
        the `r_j`-step blocks (routine given `aux_lwc_kingman_linear_2`, not attempted here);
  (ii)  `G 1 = g ∘ r ≤ C * r + K` on `A` (from `hlin` at the witness `K`), integrable on `A` by
        `aux_lwc_kingman_linear_3` and `IntegrableOn.const_mul`/`add`;
  (iii) `LatticeProb.ae_tendsto_div` (`Kingman.lean`), applied to `G`, `T'` and the
        renormalized restriction, gives `G j / j → L'` a.e. on `A`;
  (iv)  Birkhoff (`LatticeProb/Prob/Birkhoff.lean`) applied to `r` under `T'` gives
        `r_j / j → (μ A)⁻¹ ∫_A r = 1` a.e. on `A` (`aux_lwc_kingman_linear_3`), so
        `g (r_j x) x / r_j x = (G j x / j) / (r_j x / j) → L'` a.e. on `A`, and
        `r_{j+1} / r_j → 1`;
  (v)   `hlip` extends `g n x / n → L'` from the subsequence `n = r_j x` to every `n`, for
        a.e. `x ∈ A` (sandwiching `n` between consecutive `r_j x`, `r_{j+1} x`, both `o(n)`
        apart by `r_{j+1}/r_j → 1`);
  (vi)  `limsup` and `liminf` of `g n x / n` (over all `x ∈ Ω`, using `hsub` and `hg ≥ 0`)
        satisfy `f ≤ f ∘ T` pointwise (as in the deleted per-point-Fekete attempt, but for
        `limsup`/`liminf` rather than a literal limit, which does not need subadditivity along
        a fixed point), hence are a.e. `T`-invariant (`hT` and equal integrals) and a.e.
        constant (`herg.ae_eq_const_of_ae_eq_comp₀`), equal a.e. on `A` to the common value
        `L'` of (v), and hence equal `μ`-a.e. on all of `Ω` since `μ A > 0` and an ergodic
        a.e.-constant function is determined by its value on any positive-measure set.

None of (i)-(vi) is attempted here for time; (i), (ii), (v), (vi) are routine manipulation
given `aux_lwc_kingman_linear_2`-`_3`, while (iii)-(iv) are direct citations of sealed
`Lattice-Probability` theorems.  The genuine, load-bearing gaps are exactly
`aux_lwc_kingman_linear_2` and `aux_lwc_kingman_linear_3`. -/
theorem aux_lwc_kingman_linear {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (herg : Ergodic T μ)
    (g : ℕ → Ω → ℝ) (hsub : ∀ m n x, g (m + n) x ≤ g m x + g n (T^[m] x))
    (hg : ∀ n x, 0 ≤ g n x) (hgm : ∀ n, Measurable (g n))
    (hlin : ∃ C : ℝ, ∀ᵐ x ∂μ, ∃ K : ℝ, ∀ n : ℕ, g n x ≤ C * n + K)
    (hlip : ∃ C : ℝ, ∀ᵐ x ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, n ≤ m →
      m ≤ 2 * n → |g m x - g n x| ≤ C * ((m : ℝ) - n) + ε * n) :
    ∃ L : ℝ, ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => g n x / (n : ℝ)) atTop (nhds L) := by
  sorry

/-! ### (a) Kingman's theorem applied to `clusterArrival` -/

/-- **Real, fully proved**: for `v = 0` the sequence `n • v` is constantly `0`, so
`clusterArrival η 0 (n • 0) = clusterArrival η 0 0` for every `n` and every `η`, a single fixed
`ℕ∞`; the rescaled sequence is a constant natural divided by `n`, which tends to `0` regardless
of whether that constant is finite (`.toNat` reading the honest value) or `⊤` (`.toNat` reading
the junk value `0`, giving the already-constant-zero sequence). No a.e. restriction is needed. -/
theorem aux_lwc_kingman_zero_case (d : ℕ) (p : ℝ) :
    ∀ᵐ η ∂(toyLaw d p),
      Tendsto (fun n : ℕ => ((clusterArrival η (0 : Site d) ((n : ℤ) • (0 : Site d))).toNat : ℝ) / (n : ℝ))
        atTop (nhds 0) := by
  filter_upwards with η
  have heq : (fun n : ℕ => ((clusterArrival η (0 : Site d) ((n:ℤ) • (0:Site d))).toNat : ℝ) / (n : ℝ))
      = (fun n : ℕ => ((clusterArrival η (0 : Site d) (0:Site d)).toNat : ℝ) / (n : ℝ)) := by
    funext n; simp
  rw [heq]
  exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

/-- **GAP / needs further split** (repaired proof, 2026-09-24; no first-moment bound is used):
for `v ≠ 0`, take `E` from `aux_lwc_good_event` and `g n η := if η ∈ E then ((clusterArrival η 0
(n • v)).toNat : ℝ) else 0`, over the shift `η ↦ fun z => η (v + z)`, ergodic by
`aux_lwc_shift_ergodic` (`v ≠ 0` here is exactly where that hypothesis is used). `g` is
subadditive by `Exploding.Frozen.approx_subadditivity` and `aux_lwc_cluster_shift` (`E` is
shift invariant, by `aux_lwc_good_event`'s own shift-invariance clause), measurable by
`aux_lwc_measurable`, linearly bounded by the first bound of `aux_lwc_cluster_lipschitz`
(`aux_lwc_cluster_lipschitz_1`), and satisfies the Lipschitz hypothesis of
`aux_lwc_kingman_linear` by the second bound (`aux_lwc_cluster_lipschitz_2`/`_3`) applied at
scale `2 n * mnorm v`.  `aux_lwc_kingman_linear` then gives the deterministic limit `N v`.  Not
attempted here for time; it inherits `sorry` from `aux_lwc_cluster_lipschitz` and
`aux_lwc_kingman_linear` regardless, and the construction of `g` and verification of its four
hypotheses (subadditivity, nonnegativity, measurability, the two a.e. bounds) is itself a
genuine multi-step bookkeeping argument not yet written out. -/
theorem aux_lwc_kingman_nonzero_case (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree) (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ N : Site d → ℝ, ∀ v : Site d, v ≠ 0 →
      ∀ᵐ η ∂(toyLaw d p),
        Tendsto (fun n : ℕ => ((clusterArrival η (0 : Site d) ((n : ℤ) • v)).toNat : ℝ) / (n : ℝ))
          atTop (nhds (N v)) := by
  sorry

/-- The a.s. existence of the rescaled limit of `clusterArrival` along every
lattice direction, to a single deterministic function `N`. -/
theorem aux_lwc_kingman (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree) (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ N : Site d → ℝ, ∀ v : Site d,
      ∀ᵐ η ∂(toyLaw d p),
        Tendsto (fun n : ℕ => ((clusterArrival η (0 : Site d) ((n : ℤ) • v)).toNat : ℝ) / (n : ℝ))
          atTop (nhds (N v)) := by
  obtain ⟨N, hN⟩ := aux_lwc_kingman_nonzero_case d hd p hp hp1 hLSSB hHole hChem
  refine ⟨fun v => if v = 0 then 0 else N v, fun v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simpa using aux_lwc_kingman_zero_case d p
  · simpa [hv] using hN v hv

/-! ### (b) homogeneity under integer scaling of a lattice direction -/

/-- **Real, proved from (a)'s conclusion alone** (no further citation needed):
if `N v` is the a.s. limit of the rescaled `clusterArrival` in direction `v`
for every `v`, then `N` is homogeneous under scaling `v` by a positive
integer.  This is exploding.tex's "the properties of `N_p` are immediate from
the scaling", specialized to integer scaling of a lattice vector; the
paper's passage to general nonnegative real scaling of `N` on `ℝ^d` needs the
continuity from (c) as well, since `ℤ^d` is not scaled by irrational
constants. -/
theorem aux_lwc_homog (d : ℕ) (p : ℝ)
    [MeasureTheory.IsProbabilityMeasure (toyLaw d p)]
    (N : Site d → ℝ)
    (hN : ∀ v : Site d, ∀ᵐ η ∂(toyLaw d p),
      Tendsto (fun n : ℕ => ((clusterArrival η (0 : Site d) ((n : ℤ) • v)).toNat : ℝ) / (n : ℝ))
        atTop (nhds (N v)))
    (v : Site d) (k : ℕ) (hk : 1 ≤ k) :
    N ((k : ℤ) • v) = (k : ℝ) * N v := by
  haveI : NeZero (toyLaw d p) := ⟨MeasureTheory.IsProbabilityMeasure.ne_zero _⟩
  obtain ⟨η, h1, h2⟩ := ((hN v).and (hN ((k : ℤ) • v))).exists
  set g : ℕ → Site d → ℝ := fun n w => ((clusterArrival η (0 : Site d) ((n : ℤ) • w)).toNat : ℝ)
    with hg
  have hpt : ∀ n : ℕ, g n ((k : ℤ) • v) / (n : ℝ) = (k : ℝ) * (g (n * k) v / ((n * k : ℕ) : ℝ)) := by
    intro n
    have hidx : (n : ℤ) • ((k : ℤ) • v) = (((n * k : ℕ) : ℤ)) • v := by
      rw [smul_smul, Nat.cast_mul]
    show ((clusterArrival η (0 : Site d) ((n : ℤ) • ((k : ℤ) • v))).toNat : ℝ) / (n : ℝ)
      = (k : ℝ) * (((clusterArrival η (0 : Site d) (((n * k : ℕ) : ℤ) • v)).toNat : ℝ)
          / ((n * k : ℕ) : ℝ))
    rw [hidx]
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · simp [hn0]
    · have hk0 : (k : ℝ) ≠ 0 := by positivity
      have hn0' : (n : ℝ) ≠ 0 := by positivity
      have hcast : ((n * k : ℕ) : ℝ) = (n : ℝ) * (k : ℝ) := by push_cast; ring
      rw [hcast]
      field_simp
  have hcomp : Tendsto (fun n : ℕ => n * k) atTop atTop :=
    Filter.tendsto_atTop_atTop_of_monotone (fun a b hab => Nat.mul_le_mul_right k hab)
      (fun b => ⟨b, Nat.le_mul_of_pos_right b hk⟩)
  have h2' : Tendsto (fun n : ℕ => g (n * k) v / ((n * k : ℕ) : ℝ)) atTop (nhds (N v)) :=
    h1.comp hcomp
  have h3 : Tendsto (fun n : ℕ => (k : ℝ) * (g (n * k) v / ((n * k : ℕ) : ℝ))) atTop
      (nhds ((k : ℝ) * N v)) := h2'.const_mul (k : ℝ)
  have h4 : Tendsto (fun n : ℕ => g n ((k : ℤ) • v) / (n : ℝ)) atTop (nhds ((k : ℝ) * N v)) :=
    h3.congr (fun n => (hpt n).symm)
  exact tendsto_nhds_unique h2 h4

/-! ### (c) everywhere, locally uniform convergence -/

-- GAP: exploding.tex's "everywhere convergence then follows from the second bound
-- in eq:lastwave_lipschitz and approximation" (the arXiv text said "continuity"): the
-- second bound of `aux_lwc_cluster_lipschitz`, applied in both directions, makes the
-- rescaled `clusterArrival` uniformly Lipschitz up to `o(1)` on compacts, which with
-- `aux_lwc_kingman` on a finite net of lattice directions gives locally uniform convergence.
-- The older notes follow.  Standard tool available for this: `ConvexOn` functions
-- are `LocallyLipschitz` (`Mathlib/Analysis/Convex/Continuous.lean`,
-- `ConvexOn.locallyLipschitz`), which is the usual way to upgrade convergence
-- on a dense set to locally uniform convergence for a convex limit.  What is
-- missing is (i) the discrete-`n` family `y ↦ n⁻¹ (clusterArrival η 0
-- (nearestSite (n•y))).toNat` is itself uniformly (in `n`) close to convex /
-- Lipschitz on compacts, which should follow from `approx_subadditivity`
-- (sealed) plus a bound relating `clusterArrival` to `mnorm` on nearby points,
-- neither combination formalized; and (ii) the routine but unwritten
-- extension of `aux_lwc_homog` from positive-integer to nonnegative-real
-- scalars via continuity.  Both are left to whoever discharges this GAP.
/-- Everywhere, locally uniform a.s. convergence of the rescaled
`clusterArrival`, granted (a) and (b). -/
theorem aux_lwc_uniform (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree) (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ N : (Fin d → ℝ) → ℝ,
      Continuous N ∧
      ConvexOn ℝ Set.univ N ∧
      (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
      ∀ᵐ η ∂(toyLaw d p),
        (∀ x : Site d, clusterArrival η (0 : Site d) x ≠ ⊤) ∧
          ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
            ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
              |((clusterArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
                - N y| ≤ ε := by
  sorry

/-! ### (d) transfer from `clusterArrival` to `lastArrival` -/

/-- A compact subset of `Fin d → ℝ` is bounded in sup norm: `IsCompact.isBounded` gives a
norm bound, and `norm_le_pi_norm` reads it off coordinatewise. -/
theorem aux_lwc_transfer_1 (d : ℕ) (K : Set (Fin d → ℝ)) (hK : IsCompact K) :
    ∃ M : ℕ, ∀ y ∈ K, ∀ i, |y i| ≤ (M : ℝ) := by
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  refine ⟨⌈M⌉₊, fun y hy i => ?_⟩
  calc |y i| = ‖y i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖y‖ := norm_le_pi_norm y i
    _ ≤ M := hM y hy
    _ ≤ ⌈M⌉₊ := Nat.le_ceil M

/-- `nearestSite ((n:ℝ) • y) i = ⌈n * y i - 1/2⌉` is within `2` of `n * y i` in each
coordinate (`Int.le_ceil`, `Int.ceil_lt_add_one`), so a coordinatewise bound on `y` gives one
on `nearestSite (n • y)`. -/
theorem aux_lwc_transfer_2 (d : ℕ) (M : ℕ) (y : Fin d → ℝ) (hy : ∀ i, |y i| ≤ (M : ℝ))
    (n : ℕ) (i : Fin d) :
    |nearestSite ((n : ℝ) • y) i| ≤ (n * M + 2 : ℤ) := by
  show |⌈(n : ℝ) • y i - 1 / 2⌉| ≤ (n * M + 2 : ℤ)
  simp only [smul_eq_mul]
  have h1 : ((n : ℝ) * y i - 1 / 2 : ℝ) ≤ ⌈(n : ℝ) * y i - 1 / 2⌉ := Int.le_ceil _
  have h2 : (⌈(n : ℝ) * y i - 1 / 2⌉ : ℝ) < (n : ℝ) * y i - 1 / 2 + 1 := Int.ceil_lt_add_one _
  have hyi := hy i
  rw [abs_le]
  constructor
  · have hb : -(((n * M + 2 : ℤ) : ℝ)) ≤ (⌈(n : ℝ) * y i - 1 / 2⌉ : ℝ) := by
      push_cast; nlinarith [neg_abs_le (y i)]
    exact_mod_cast hb
  · have hb : (⌈(n : ℝ) * y i - 1 / 2⌉ : ℝ) ≤ ((n * M + 2 : ℤ) : ℝ) := by
      push_cast; nlinarith [le_abs_self (y i)]
    exact_mod_cast hb

/-- `mnorm (nearestSite (n • y))` is at most `C * n` for `n ≥ 1`, uniformly over `y ∈ K`,
for a compact `K` (`aux_lwc_transfer_1`, `aux_lwc_transfer_2` summed over the `d` coordinates
via `Finset.sum_le_sum`). -/
theorem aux_lwc_transfer_3 (d : ℕ) (K : Set (Fin d → ℝ)) (hK : IsCompact K) :
    ∃ C : ℕ, ∀ y ∈ K, ∀ n : ℕ, 1 ≤ n → mnorm (nearestSite ((n : ℝ) • y)) ≤ (C : ℤ) * n := by
  obtain ⟨M, hM⟩ := aux_lwc_transfer_1 d K hK
  refine ⟨d * (M + 2), fun y hy n hn => ?_⟩
  have hsum : mnorm (nearestSite ((n : ℝ) • y)) ≤ (d : ℤ) * (n * M + 2) := by
    have := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
      (f := fun i => |nearestSite ((n : ℝ) • y) i|) (g := fun _ => (n * M + 2 : ℤ))
      (fun i _ => aux_lwc_transfer_2 d M y (hM y hy) n i)
    simpa [mnorm, Finset.sum_const, Finset.card_univ, mul_comm] using this
  calc mnorm (nearestSite ((n : ℝ) • y)) ≤ (d : ℤ) * (n * M + 2) := hsum
    _ ≤ (d * (M + 2) : ℕ) * n := by
        have : (1 : ℤ) ≤ n := by exact_mod_cast hn
        push_cast
        nlinarith

/-- The polylogarithmic-over-linear tail estimate: `(log (C n))^γ / n → 0`, from
`isLittleO_log_rpow_rpow_atTop` (with `s := 1`) via `IsLittleO.tendsto_div_nhds_zero`, composed
with `n ↦ C * n → ∞` and rescaled by the constant `C`. -/
theorem aux_lwc_transfer_4 (γ : ℝ) (C : ℕ) (hC : 0 < C) :
    Filter.Tendsto (fun n : ℕ => Real.log ((C : ℝ) * n) ^ γ / (n : ℝ)) atTop (nhds 0) := by
  have hlo : (fun x : ℝ => Real.log x ^ γ) =o[atTop] fun x : ℝ => x ^ (1 : ℝ) :=
    isLittleO_log_rpow_rpow_atTop γ one_pos
  have hdiv : Filter.Tendsto (fun x : ℝ => Real.log x ^ γ / x ^ (1 : ℝ)) atTop (nhds 0) :=
    hlo.tendsto_div_nhds_zero
  simp only [Real.rpow_one] at hdiv
  have hcomp : Filter.Tendsto (fun n : ℕ => (C : ℝ) * n) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by exact_mod_cast hC) tendsto_natCast_atTop_atTop
  have h1 : Filter.Tendsto (fun n : ℕ => Real.log ((C : ℝ) * n) ^ γ / ((C : ℝ) * n)) atTop
      (nhds 0) := hdiv.comp hcomp
  have h2 := h1.const_mul (C : ℝ)
  simp only [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hC0 : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp

/-- Finiteness of `lastArrival η 0 x`, read off a single point of
`Exploding.Frozen.last_penultimate_close`'s a.e. event at the scale `n := max n0 (mnorm x)`. -/
theorem aux_lwc_transfer_5 {d : ℕ} (η : Site d → ℤ) (γ : ℝ)
    (hη : ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
      lastArrival η (0 : Site d) x ≤ clusterArrival η (0 : Site d) x ∧
        ∃ a b : ℕ, lastArrival η (0 : Site d) x = (a : ℕ∞) ∧
          clusterArrival η (0 : Site d) x = (b : ℕ∞) ∧ (b : ℝ) ≤ (a : ℝ) + Real.log n ^ γ)
    (x : Site d) : lastArrival η (0 : Site d) x ≠ ⊤ := by
  obtain ⟨n0, hn0⟩ := hη
  obtain ⟨a, b, ha, _⟩ := (hn0 (max n0 (mnorm x).toNat) (le_max_left _ _) x
    (by omega)).2
  rw [ha]; exact ENat.coe_ne_top a

/-- The pointwise gap between `lastArrival.toNat` and `clusterArrival.toNat` at a single site,
read off `Exploding.Frozen.last_penultimate_close`'s conclusion at that site and scale. -/
theorem aux_lwc_transfer_6 {d : ℕ} (η : Site d → ℤ) (γ : ℝ) (n0 : ℕ)
    (hn0 : ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
      lastArrival η (0 : Site d) x ≤ clusterArrival η (0 : Site d) x ∧
        ∃ a b : ℕ, lastArrival η (0 : Site d) x = (a : ℕ∞) ∧
          clusterArrival η (0 : Site d) x = (b : ℕ∞) ∧ (b : ℝ) ≤ (a : ℝ) + Real.log n ^ γ)
    (n : ℕ) (hn : n0 ≤ n) (x : Site d) (hx : mnorm x ≤ (n : ℤ)) :
    |((lastArrival η (0 : Site d) x).toNat : ℝ) - ((clusterArrival η (0 : Site d) x).toNat : ℝ)|
      ≤ Real.log n ^ γ := by
  obtain ⟨hle, a, b, ha, hb, hab⟩ := hn0 n hn x hx
  have hab' : (a : ℝ) ≤ (b : ℝ) := by
    have : (a : ℕ∞) ≤ (b : ℕ∞) := ha ▸ hb ▸ hle
    exact_mod_cast this
  rw [ha, hb, ENat.toNat_coe, ENat.toNat_coe, abs_of_nonpos (by linarith)]
  linarith

/-- The locally uniform convergence of (c), transferred from `clusterArrival`
to `lastArrival` via `Exploding.Frozen.last_penultimate_close`.  Every compact `K` has
`mnorm (nearestSite (n • y)) ≤ C n` uniformly over `y ∈ K` (`aux_lwc_transfer_3`), so
`last_penultimate_close` applies at scale `(C+1) n`, and its polylogarithmic error divided
by `n` still tends to `0` (`aux_lwc_transfer_4`); the triangle inequality against `hunif`
finishes. -/
theorem aux_lwc_transfer (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree) (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance)
    (N : (Fin d → ℝ) → ℝ)
    (hunif : ∀ᵐ η ∂(toyLaw d p),
      (∀ x : Site d, clusterArrival η (0 : Site d) x ≠ ⊤) ∧
        ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
            |((clusterArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
              - N y| ≤ ε) :
    ∀ᵐ η ∂(toyLaw d p),
      (∀ x : Site d, lastArrival η (0 : Site d) x ≠ ⊤) ∧
        ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
            |((lastArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
              - N y| ≤ ε := by
  obtain ⟨γ, hγ, hclose⟩ := Exploding.Frozen.last_penultimate_close d hd p hp hp1 hLSSB hHole hChem
  filter_upwards [hclose, hunif] with η hηclose hηunif
  refine ⟨aux_lwc_transfer_5 η γ hηclose, fun K hK ε hε => ?_⟩
  obtain ⟨C, hCbd⟩ := aux_lwc_transfer_3 d K hK
  obtain ⟨n0, hn0⟩ := hηclose
  have hCpos : (0 : ℕ) < C + 1 := Nat.succ_pos C
  have htail : ∀ᶠ n : ℕ in atTop, Real.log (((C + 1 : ℕ) : ℝ) * n) ^ γ / (n : ℝ) ≤ ε / 2 :=
    (aux_lwc_transfer_4 γ (C + 1) hCpos).eventually_le_const (by linarith)
  have hev2 : ∀ᶠ n : ℕ in atTop, n0 ≤ (C + 1) * n := by
    have hm : Filter.Tendsto (fun n : ℕ => (C + 1) * n) atTop atTop :=
      Filter.tendsto_atTop_atTop_of_monotone (fun a b hab => Nat.mul_le_mul_left (C+1) hab)
        (fun b => ⟨b, Nat.le_mul_of_pos_left b hCpos⟩)
    exact hm.eventually_ge_atTop n0
  have hev3 := hηunif.2 K hK (ε / 2) (by linarith)
  filter_upwards [htail, hev2, hev3, eventually_ge_atTop 1] with n h1 h2 h3 h4
  intro y hy
  set x : Site d := nearestSite ((n : ℝ) • y) with hxdef
  have hmnorm : mnorm x ≤ ((C + 1 : ℕ) : ℤ) * n := by
    have hcx := hCbd y hy n h4
    have : (C : ℤ) * n ≤ ((C + 1 : ℕ) : ℤ) * n := by push_cast; nlinarith [Int.natCast_nonneg n]
    linarith
  have hbound := aux_lwc_transfer_6 η γ n0 hn0 ((C + 1) * n) h2 x
    (by rw [hxdef]; push_cast; push_cast at hmnorm; linarith)
  have hcast : (((C + 1) * n : ℕ) : ℝ) = ((C + 1 : ℕ) : ℝ) * n := by push_cast; ring
  rw [hcast] at hbound
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h4
  have hstep1 : |((lastArrival η 0 x).toNat : ℝ) / n - ((clusterArrival η 0 x).toNat : ℝ) / n|
      ≤ ε / 2 := by
    rw [div_sub_div_same, abs_div, abs_of_pos hnpos]
    calc |((lastArrival η 0 x).toNat : ℝ) - ((clusterArrival η 0 x).toNat : ℝ)| / n
        ≤ Real.log (((C + 1 : ℕ) : ℝ) * n) ^ γ / n := by gcongr
      _ ≤ ε / 2 := h1
  calc |((lastArrival η 0 x).toNat : ℝ) / n - N y|
      ≤ |((lastArrival η 0 x).toNat : ℝ) / n - ((clusterArrival η 0 x).toNat : ℝ) / n|
          + |((clusterArrival η 0 x).toNat : ℝ) / n - N y| := abs_sub_le _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hstep1 (h3 y hy)
    _ = ε := by ring

/-! ### Assembly -/
