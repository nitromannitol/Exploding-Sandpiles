/-
The penultimate cluster of `paper/exploding.tex` Section 3: the a.e. background
bounds, the connectedness of the penultimate cluster to its centre, and the
path-filling closure of the penultimate wave.

The two remaining inputs of Lemma 3.5 are the propagation of penultimate-wave
positivity through the infinite good cluster and the pigeonhole step that finds
a good cube on a long line; both are recorded in `FINDINGS.md`.
-/
import Exploding.Support.Vocab
import Exploding.Support.SubFinite
import Exploding.Support.SubCross
import Exploding.Frozen.LastWaveBound
import Exploding.Support.Wave
import Exploding.Frozen.LocalConvexity
import Exploding.Frozen.Renormalization
import Exploding.External.LiggettSchonmannStaceyBoundedDegree
import Exploding.External.MathieuHoles
import Exploding.External.AntalPisztora

open Exploding LatticeProb MeasureTheory

theorem aux_penultimate_bounds (d : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∀ᵐ η ∂(toyLaw d p), ∀ x : Site d, 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1 := by
  have hpos_p : (0 : ℝ) ≤ p := by linarith
  have hle_p : (0 : ℝ) ≤ 1 - p := by linarith
  haveI hprob : IsProbabilityMeasure (chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p) := by
    constructor
    simp only [chipLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply',
      MeasurableSet.univ, Set.indicator_univ, Pi.one_apply, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hpos_p hle_p]
    norm_num
  haveI hprob' : ∀ _ : Site d, IsProbabilityMeasure (chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p) :=
    fun _ => hprob
  have h_each (x : Site d) : ∀ᵐ η ∂(toyLaw d p), 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1 := by
    have h_marginal_eq : (toyLaw d p).map (fun η : Site d → ℤ => η x) =
        chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p := by
      rw [toyLaw, productLaw, Measure.infinitePi_map_eval]
    have h_ae_chip : ∀ᵐ v ∂(chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p),
        v = 2 * (d : ℤ) - 2 ∨ v = 2 * (d : ℤ) - 1 := by
      have h_support : chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p
          {v : ℤ | ¬ (v = 2 * (d : ℤ) - 2 ∨ v = 2 * (d : ℤ) - 1)} = 0 := by
        simp [chipLaw]
      rw [MeasureTheory.ae_iff]
      exact h_support
    have h_ae_coord : ∀ᵐ η ∂(toyLaw d p), η x = 2 * (d : ℤ) - 2 ∨ η x = 2 * (d : ℤ) - 1 := by
      have h_meas : MeasurableSet {v : ℤ | v = 2 * (d : ℤ) - 2 ∨ v = 2 * (d : ℤ) - 1} :=
        (measurableSet_singleton _).union (measurableSet_singleton _)
      have h_aemeas : AEMeasurable (fun (η : Site d → ℤ) => η x) (toyLaw d p) :=
        (measurable_pi_apply x).aemeasurable
      rw [← MeasureTheory.ae_map_iff h_aemeas h_meas, h_marginal_eq]
      exact h_ae_chip
    filter_upwards [h_ae_coord] with η h
    rcases h with h_eq | h_eq
    · rw [h_eq]; exact ⟨by omega, by omega⟩
    · rw [h_eq]; exact ⟨by omega, by omega⟩
  exact (MeasureTheory.ae_all_iff).mpr h_each

/-! ### (a1) The penultimate wave's positive set is connected back to its centre -/

/- `aux_penultimate_connected_to_centre`: every site where the penultimate
wave is positive is joined to the centre `zc` by a lattice path all of whose
vertices already carry positive penultimate-wave mass.

This is *not* immediate from `mem_penultimateCluster_of_adj`
(`Support/Wave.lean`): that lemma only says a site adjacent to a positive site
belongs to the *cluster*, not that the site itself is positive, so it does not
by itself produce a path of positive sites.  The right induction is on the
*first time* `y` turns positive along the underlying time-indexed
`(M̂_η(zc)-1)`-wave (`waveThreshold η zc - 1`): if `y ≠ zc` first turns positive
at step `t+1`, `exists_adj_pos_of_nbrSumZ_pos` gives a neighbour `y'` already
positive at step `t`, i.e. with a *strictly earlier* first-positive-time, so
strong induction on that first-positive-time terminates (at `zc`, whose
first-positive-time is `0`).  By monotonicity in time (`wave_mono_t`) every
site visited along the resulting chain, once positive, stays positive forever,
in particular in the terminal `penultimateWave`.

-- GAP (real, not literature): needs a well-founded induction on
-- `sInf {t | 0 < wave η (waveThreshold η zc - 1) zc t y}` that is not yet in
-- `Support/Wave.lean`.  I am confident the statement is true and the sketch
-- above is correct; formalizing the strong induction is genuine additional
-- work.  Split below: `aux_penultimate_hlast` recovers the missing `hlast`
-- witness that `Support/Wave.lean`'s own lemmas need from bare positivity of
-- `penultimateWave`, and `aux_penultimate_wave_pos_implies_terminal` upgrades
-- a positive value at *some* finite time to positivity of the terminal
-- `penultimateWave`; the strong induction itself is assembled directly in
-- this lemma's own proof (it is the natural home for it, not a separable
-- ≤15-line fact). -/

/-- If the penultimate wave is positive anywhere, `waveThreshold η zc ≥ 2`
and in particular the `hlast` witness that `penultimateWave_fixed`/
`penultimate_stabilizable` (`Support/Wave.lean`) need is available.  If
`waveThreshold η zc = 1`, `penultimateWave η zc` is *by definition* the
constant function `0` (`penultimateWave`'s `if`), contradicting positivity
directly.  If `waveThreshold η zc = 0`, `waveThreshold η zc - 1 = 0` too (`ℕ`
subtraction), so `penultimateWave η zc = waveTerminal η 0 zc`; the `0`-wave is
identically `0` (`wave η 0 zc t x = 0` for every `t, x`, by induction on `t`:
at `t = 0` either `x = zc` giving the cast `(0:ℕ) = (0:ℤ)`, or `0`
outright; at `t + 1`, `η x < 2d` caps the floor `⌊(nbrSum + ηx)/2d⌋` at `0`
since the sum of `0`s is `0`), so this again contradicts positivity. Hence
`waveThreshold η zc ∉ {0, 1}`. -/
theorem aux_penultimate_wave_zero_eq_zero {d : ℕ} (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (zc : Site d) :
    ∀ t : ℕ, ∀ x : Site d, wave η 0 zc t x = 0 := by
  intro t
  induction t with
  | zero =>
    intro x
    simp [wave_zero]
  | succ t ih =>
    intro x
    by_cases h : x = zc
    · simp [h]
    · rw [wave_of_ne _ _ _ _ _ h]
      have hsum : nbrSumZ (wave η 0 zc t) x = 0 := by
        simp [nbrSumZ, ih]
      rw [hsum]
      have hlt : η x < 2 * (d : ℤ) := by
        have : η x ≤ 2 * (d : ℤ) - 1 := hhigh x
        omega
      simp [Int.ediv_eq_zero_of_lt (hlow x) hlt]

theorem aux_penultimate_hlast {d : ℕ} (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (zc x : Site d) (hx : 0 < penultimateWave η zc x) :
    2 ≤ waveThreshold η zc ∧ ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n zc := by
  have h_not_one : waveThreshold η zc ≠ 1 := by
    intro h
    have hp : penultimateWave η zc = 0 := by
      simp [penultimateWave, h]
    rw [hp] at hx
    simp at hx
  have h_not_zero : waveThreshold η zc ≠ 0 := by
    intro h
    have hp : penultimateWave η zc = 0 := by
      unfold penultimateWave
      simp [h]
      have hw : waveTerminal η 0 zc = fun _ : Site d => (0 : ℤ) := by
        have hzero : ∀ t : ℕ, ∀ x : Site d, wave η 0 zc t x = 0 :=
          aux_penultimate_wave_zero_eq_zero η hlow hhigh zc
        have hstab : ∀ t : ℕ, wave η 0 zc t = wave η 0 zc 0 := by
          intro t; ext y; simp [hzero t y, hzero 0 y]
        have hS : (0 : ℕ) ∈ {T : ℕ | ∀ t : ℕ, T ≤ t → wave η 0 zc t = wave η 0 zc T} := by
          intro t ht; exact hstab t
        have hsInf_eq : sInf {T : ℕ | ∀ t : ℕ, T ≤ t → wave η 0 zc t = wave η 0 zc T} = 0 := by
          have hle : sInf {T : ℕ | ∀ t : ℕ, T ≤ t → wave η 0 zc t = wave η 0 zc T} ≤ 0 :=
            Nat.sInf_le hS
          omega
        ext y
        simp [waveTerminal, hsInf_eq, hzero 0 y]
      exact hw
    rw [hp] at hx
    simp at hx
  have h_two : 2 ≤ waveThreshold η zc := by
    omega
  have h_exists : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n zc := by
    have hpos : 0 < waveThreshold η zc := by omega
    have hne : {n : ℕ | 1 ≤ n ∧ ¬ WaveStabilizable η n zc}.Nonempty := by
      by_contra hempty
      have hsInf_zero : waveThreshold η zc = 0 := by
        unfold waveThreshold
        have h_empty : {n : ℕ | 1 ≤ n ∧ ¬ WaveStabilizable η n zc} = (∅ : Set ℕ) := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro n hn
          rcases hn with ⟨hn1, hn2⟩
          exact hempty ⟨n, hn1, hn2⟩
        simp [h_empty]
      exact h_not_zero hsInf_zero
    have hmem : waveThreshold η zc ∈ {n : ℕ | 1 ≤ n ∧ ¬ WaveStabilizable η n zc} :=
      Nat.sInf_mem hne
    exact ⟨waveThreshold η zc, hmem.1, hmem.2⟩
  exact ⟨h_two, h_exists⟩

/-- A finite-time positive value of the `(M-1)`-wave upgrades to positivity
of the terminal `penultimateWave`: with `T` the stabilization time of
`WaveStabilizable η (waveThreshold η zc - 1) zc` (from `hlast`,
`penultimate_stabilizable`), either `t ≤ T` (then `wave_mono_t`/monotonicity
in time, or the induction underlying `wave_mono_time`, gives
`wave t x ≤ wave T x`) or `t > T` (then `waveTerminal_spec` gives
`wave t x = wave T x` directly, `T` already being past stabilization); either
way `wave T x > 0`, i.e. `penultimateWave η zc x = waveTerminal η (M-1) zc x
= wave η (M-1) zc T x > 0`. -/
theorem aux_penultimate_wave_pos_implies_terminal {d : ℕ} (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (zc x : Site d)
    (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n zc) (h1 : waveThreshold η zc ≠ 1)
    (t : ℕ) (ht : 0 < wave η (waveThreshold η zc - 1) zc t x) :
    0 < penultimateWave η zc x := by
  have hd : (0 : ℤ) < 2 * (d : ℤ) := (by linarith [hlow zc, hhigh zc])
  obtain ⟨T, hT⟩ := penultimate_stabilizable η zc hlast h1
  have hstab : WaveStabilizable η (waveThreshold η zc - 1) zc := ⟨T, hT⟩
  set S : Set ℕ := {N : ℕ | ∀ t : ℕ, N ≤ t →
    wave η (waveThreshold η zc - 1) zc t = wave η (waveThreshold η zc - 1) zc N} with hS
  have hmem : sInf S ∈ S := Nat.sInf_mem ⟨T, hT⟩
  have hwt : waveTerminal η (waveThreshold η zc - 1) zc =
      wave η (waveThreshold η zc - 1) zc (sInf S) :=
    waveTerminal_spec η (waveThreshold η zc - 1) zc hstab (sInf S) (le_refl (sInf S))
  have hpos : 0 < wave η (waveThreshold η zc - 1) zc (sInf S) x := (by
    rcases le_total t (sInf S) with hle | hle
    · refine lt_of_lt_of_le ht ?_
      exact wave_mono_time η hlow hd (waveThreshold η zc - 1) zc hle x
    · rw [← hmem t hle]
      exact ht)
  simp only [penultimateWave, if_neg h1]
  rw [hwt]
  exact hpos


theorem aux_penultimate_connected_to_centre {d : ℕ} (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (zc y : Site d) (hy : 0 < penultimateWave η zc y) :
    ∃ (r : ℕ) (path : ℕ → Site d), path 0 = zc ∧ path r = y ∧
      (∀ j, j < r → (lattice d).Adj (path j) (path (j + 1))) ∧
      ∀ j, j ≤ r → 0 < penultimateWave η zc (path j) := by
  obtain ⟨hM2, hlast⟩ := aux_penultimate_hlast η hlow hhigh zc y hy
  have h1ne : waveThreshold η zc ≠ 1 := by omega
  have hzcpos : 0 < penultimateWave η zc zc := by
    rw [penultimateWave_at_centre η zc (by omega)]; omega
  have main : ∀ t : ℕ, ∀ x : Site d, 0 < wave η (waveThreshold η zc - 1) zc t x →
      ∃ (r : ℕ) (path : ℕ → Site d), path 0 = zc ∧ path r = x ∧
        (∀ j, j < r → (lattice d).Adj (path j) (path (j + 1))) ∧
        ∀ j, j ≤ r → 0 < penultimateWave η zc (path j) := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro x hx
      by_cases hxzc : x = zc
      · refine ⟨0, fun _ => zc, rfl, hxzc.symm, fun j hj => absurd hj (Nat.not_lt_zero j),
          fun j hj => ?_⟩
        rw [show j = 0 by omega]; exact hzcpos
      · match t, hx with
        | 0, hx => exact absurd hx (by simp [wave_zero, hxzc])
        | t0 + 1, hx =>
          rw [wave_of_ne η _ zc x t0 hxzc] at hx
          have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
            rcases Nat.eq_zero_or_pos d with h0 | hpos
            · exfalso
              apply hxzc
              subst h0
              exact funext fun i => i.elim0
            · have : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hpos
              linarith
          have hnbr : 0 < nbrSumZ (wave η (waveThreshold η zc - 1) zc t0) x := by
            by_contra hcon
            simp only [not_lt] at hcon
            have hsumnn : 0 ≤ nbrSumZ (wave η (waveThreshold η zc - 1) zc t0) x :=
              nbrSumZ_nonneg _ (fun z => wave_nonneg η hlow _ zc t0 z) x
            have hlt : nbrSumZ (wave η (waveThreshold η zc - 1) zc t0) x + η x < 2 * (d : ℤ) := by
              linarith [hhigh x]
            have := Int.ediv_eq_zero_of_lt (by linarith [hlow x]) hlt
            omega
          obtain ⟨y', hadjy', hy'pos⟩ :=
            exists_adj_pos_of_nbrSumZ_pos _ (fun z => wave_nonneg η hlow _ zc t0 z) x hnbr
          obtain ⟨r', path', hp0, hpr', hstep', hinv'⟩ := ih t0 (by omega) y' hy'pos
          have hxpos : 0 < penultimateWave η zc x :=
            aux_penultimate_wave_pos_implies_terminal η hlow hhigh zc x hlast h1ne (t0 + 1)
              (by rw [wave_of_ne η _ zc x t0 hxzc]; exact hx)
          refine ⟨r' + 1, fun j => if j = r' + 1 then x else path' j, ?_, by simp, ?_, ?_⟩
          · simp [hp0]
          · intro j hj
            by_cases hjr' : j = r'
            · subst hjr'; simp [hpr']; exact hadjy'
            · have h1 : j ≠ r' + 1 := by omega
              have h2 : j + 1 ≠ r' + 1 := by omega
              simp only [h1, h2, if_false]
              exact hstep' j (by omega)
          · intro j hj
            by_cases hjeq : j = r' + 1
            · simp [hjeq]; exact hxpos
            · simp only [hjeq, if_false]
              exact hinv' j (by omega)
  have hyt : 0 < wave η (waveThreshold η zc - 1) zc
      (sInf {T : ℕ | ∀ t : ℕ, T ≤ t →
        wave η (waveThreshold η zc - 1) zc t = wave η (waveThreshold η zc - 1) zc T}) y := by
    have heq : penultimateWave η zc y = wave η (waveThreshold η zc - 1) zc
        (sInf {T : ℕ | ∀ t : ℕ, T ≤ t →
          wave η (waveThreshold η zc - 1) zc t = wave η (waveThreshold η zc - 1) zc T}) y := by
      simp only [penultimateWave, if_neg h1ne, waveTerminal]
    rwa [heq] at hy
  exact main _ y hyt

/-! ### (a2) A path of positive sites forces its whole bounding rectangle positive -/

/- `aux_penultimate_path_box_closure`: if a finite lattice path lies entirely
in `{ũ > 0}` (the positive set of the penultimate wave centred at `zc`), so
does its whole bounding rectangle.

Sketch, citing `Exploding.Frozen.local_convexity` exactly as the paper's
one-line proof does: let `A` be the path's image.  Since `penultimateWave η zc`
is `≥ 1` on `A` and satisfies the *same* recursion off `zc` that
`fodo A η (Set.indicator A 1)` satisfies off `A` (`penultimateWave_fixed`), a
domination induction exactly like `aux_square_lower_bound_compare` in
`lem-square-lower-bound-dec/node.lean` (there for `podo` against `wave`; here
for `fodo A` against `penultimateWave η zc`) gives
`fodo A η (Set.indicator A 1) t ≤ penultimateWave η zc` pointwise for every
`t`.  `local_convexity` gives `fodo A η (Set.indicator A 1) t = 1` throughout
`br A` once `t ≥ |br A|`, so `penultimateWave η zc ≥ 1` throughout `br A` too.
-- GAP (real, not literature): the domination induction is not yet written;
-- it is the same recipe as `aux_square_lower_bound_compare`, adapted from a
-- single frozen point to a frozen path `A`, so I rate this the same
-- provable-but-unformalized confidence as that lemma. -/
/-- `fodo A η (indicator A 1)` is dominated by `penultimateWave η zc`
pointwise at every time: the domination induction of `aux_square_lower_bound_
compare` (`lem-square-lower-bound-dec/node.lean`, there for `podo` against
`wave`), adapted from a single frozen point to a frozen set `A`.  At `x ∈ A`
the frozen odometer is pinned at `w0 x = 1 ≤ penultimateWave η zc x`
(`hApos`); at `x = zc ∉ A` (if any) the global cap `fodo_le_one`
(`Support/SubFodo.lean`, needs `η ≤ 2d - 1`, `w0 ≤ 1`, `w0 ≥ 0`, all
immediate from `hApos`/`Set.indicator`) bounds the frozen odometer by
`1 ≤ penultimateWave η zc zc` (`hzcpos`) with no induction needed; at every
other `x ∉ A` (so `x ≠ zc`), compare via `nbrSumZ_mono` on the induction
hypothesis and `Int.ediv_le_ediv`, using `penultimateWave_fixed`
(`Support/Wave.lean`, valid since `x ≠ zc`, needs `hlast`) in place of
`wave`'s own one-step floor formula (`wave_of_ne`) — the recursions coincide
in shape (`fodo_succ` increments by `1{config ≥ 2d}` just as `podo_succ`
does). -/
theorem aux_penultimate_path_box_closure_dominates {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (zc : Site d) (A : Set (Site d)) (hApos : ∀ x ∈ A, 1 ≤ penultimateWave η zc x)
    (hzcpos : 1 ≤ penultimateWave η zc zc)
    (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n zc) :
    ∀ t x, fodo A η (Set.indicator A 1) t x ≤ penultimateWave η zc x := by
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  have hη0 : ∀ x, 0 ≤ η x := fun x => by linarith [hlow x]
  have hw0le : ∀ x, (Set.indicator A (1 : Site d → ℤ)) x ≤ 1 := by
    intro x
    by_cases hx : x ∈ A
    · simp [hx]
    · simp [hx]
  have hw0nn : ∀ x, 0 ≤ (Set.indicator A (1 : Site d → ℤ)) x := by
    intro x
    by_cases hx : x ∈ A
    · simp [hx]
    · simp [hx]
  intro t
  induction t with
  | zero =>
    intro x
    simp only [Exploding.fodo_zero]
    by_cases hx : x ∈ A
    · simp [hx]; exact hApos x hx
    · simp [hx]; exact penultimateWave_nonneg η hη0 zc x
  | succ t ih =>
    intro x
    by_cases hxA : x ∈ A
    · rw [Exploding.fodo_succ, if_pos hxA]
      simpa [hxA] using hApos x hxA
    · rw [Exploding.fodo_succ, if_neg hxA]
      by_cases hxzc : x = zc
      · have hxA' : zc ∉ A := by rwa [← hxzc]
        have h_fodo_nonneg : ∀ (t' : ℕ) (x' : Site d), 0 ≤ fodo A η (Set.indicator A 1) t' x' := by
          intro t' x'
          induction t' generalizing x' with
          | zero => exact hw0nn x'
          | succ t'' ih =>
            rw [Exploding.fodo_succ]
            by_cases hx' : x' ∈ A
            · simp [hx']
            · simp [hx']; split_ifs <;> linarith [ih x']
        have hpos : 0 ≤ fodo A η (Set.indicator A 1) t zc := h_fodo_nonneg t zc
        have h_fodo_le_one : ∀ (t' : ℕ) (x' : Site d), fodo A η (Set.indicator A 1) t' x' ≤ 1 := by
          intro t'
          induction t' with
          | zero => intro x'; simpa [Exploding.fodo_zero] using hw0le x'
          | succ t'' ih' =>
            intro x'
            rw [Exploding.fodo_succ]
            by_cases hx' : x' ∈ A
            · rw [if_pos hx']
              exact hw0le x'
            · simp [hx']
              split_ifs with hcap'
              · by_cases h_one : fodo A η (Set.indicator A 1) t'' x' = 1
                · have hconf_eq' : fconf A η (Set.indicator A 1) t'' x' =
                      η x' + nbrSumZ (fodo A η (Set.indicator A 1) t'') x' -
                        2 * (d : ℤ) * fodo A η (Set.indicator A 1) t'' x' := by
                    unfold fconf lap; ring
                  rw [hconf_eq', h_one] at hcap'
                  have hnbr_bound : nbrSumZ (fodo A η (Set.indicator A 1) t'') x' ≤ 2 * (d : ℤ) := by
                    have h_each : ∀ y, fodo A η (Set.indicator A 1) t'' y ≤ 1 := ih'
                    have : nbrSumZ (fodo A η (Set.indicator A 1) t'') x' ≤
                        nbrSumZ (fun _ : Site d => (1 : ℤ)) x' :=
                      nbrSumZ_mono h_each x'
                    simpa [nbrSumZ, mul_comm] using this
                  have hη_bound : η x' ≤ 2 * (d : ℤ) - 1 := hhigh x'
                  nlinarith
                · have h_zero : fodo A η (Set.indicator A 1) t'' x' = 0 := by
                    have hle1' : fodo A η (Set.indicator A 1) t'' x' ≤ 1 := ih' x'
                    have hge0 : 0 ≤ fodo A η (Set.indicator A 1) t'' x' :=
                      h_fodo_nonneg t'' x'
                    omega
                  simp [h_zero]
              · simpa [add_zero] using ih' x'
        have hle1 : fodo A η (Set.indicator A 1) t zc ≤ 1 := h_fodo_le_one t zc
        have hnext : fodo A η (Set.indicator A 1) (t + 1) zc ≤ 1 := by
          rw [Exploding.fodo_succ, if_neg hxA']
          split_ifs with hcap
          · have hfodo0 : fodo A η (Set.indicator A 1) t zc = 0 := by
              by_contra hgt
              have hge1 : 1 ≤ fodo A η (Set.indicator A 1) t zc := by omega
              have hconf_eq : fconf A η (Set.indicator A 1) t zc =
                  η zc + nbrSumZ (fodo A η (Set.indicator A 1) t) zc -
                    2 * (d : ℤ) * fodo A η (Set.indicator A 1) t zc := by
                unfold fconf lap; ring
              rw [hconf_eq] at hcap
              have hnbr_bound : nbrSumZ (fodo A η (Set.indicator A 1) t) zc ≤ 2 * (d : ℤ) := by
                have h_each : ∀ y, fodo A η (Set.indicator A 1) t y ≤ 1 := h_fodo_le_one t
                have : nbrSumZ (fodo A η (Set.indicator A 1) t) zc ≤
                    nbrSumZ (fun _ : Site d => (1 : ℤ)) zc :=
                  nbrSumZ_mono h_each zc
                simpa [nbrSumZ, mul_comm] using this
              have hη_bound : η zc ≤ 2 * (d : ℤ) - 1 := hhigh zc
              nlinarith
            rw [hfodo0]
            omega
          · simpa [add_zero] using hle1
        have hgoal : fodo A η (Set.indicator A 1) (t + 1) zc ≤ penultimateWave η zc zc :=
          le_trans hnext hzcpos
        simpa [hxzc, Exploding.fodo_succ, if_neg hxA'] using hgoal
      · have hfix := penultimateWave_fixed η hη0 hhigh zc hlast hxzc
        have hN_mono : nbrSumZ (fodo A η (Set.indicator A 1) t) x ≤
            nbrSumZ (penultimateWave η zc) x :=
          nbrSumZ_mono ih x
        by_cases hcap : 2 * (d : ℤ) ≤ fconf A η (Set.indicator A 1) t x
        · rw [if_pos hcap]
          have hineq : (fodo A η (Set.indicator A 1) t x + 1) * (2 * (d : ℤ)) ≤
              nbrSumZ (penultimateWave η zc) x + η x := by
            have hcap_unfolded : 2 * (d : ℤ) ≤
                η x + nbrSumZ (fodo A η (Set.indicator A 1) t) x -
                  2 * (d : ℤ) * fodo A η (Set.indicator A 1) t x := by
              have h := hcap
              unfold fconf lap at h
              omega
            have htemp : 2 * (d : ℤ) * (fodo A η (Set.indicator A 1) t x + 1) ≤
                η x + nbrSumZ (fodo A η (Set.indicator A 1) t) x := by
              linarith
            have : η x + nbrSumZ (fodo A η (Set.indicator A 1) t) x ≤
                nbrSumZ (penultimateWave η zc) x + η x := by
              linarith
            linarith
          rw [hfix]
          rw [Int.le_ediv_iff_mul_le hd0]
          nlinarith
        · rw [if_neg hcap]
          linarith [ih x]

theorem aux_penultimate_path_box_closure {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (zc : Site d) (m : ℕ) (path : ℕ → Site d)
    (hpath : ∀ i : ℕ, i < m → (lattice d).Adj (path i) (path (i + 1)))
    (hApos : ∀ i, i ≤ m → 0 < penultimateWave η zc (path i))
    (hfin : (br (path '' {i : ℕ | i ≤ m})).Finite)
    (y : Site d) (hy : y ∈ br (path '' {i : ℕ | i ≤ m})) :
    0 < penultimateWave η zc y := by
  have hd2 : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  set A := path '' {i : ℕ | i ≤ m} with hAdef
  have hApos' : ∀ x ∈ A, 1 ≤ penultimateWave η zc x := by
    rintro x ⟨i, hi, rfl⟩; exact hApos i hi
  have h0 : 0 < penultimateWave η zc (path 0) := hApos 0 (Nat.zero_le m)
  obtain ⟨hM2, hlast⟩ :=
    aux_penultimate_hlast η (fun x => by linarith [hlow x]) hhigh zc (path 0) h0
  have hzcpos : 1 ≤ penultimateWave η zc zc := by
    rw [penultimateWave_at_centre η zc (by omega)]; omega
  have hdom := aux_penultimate_path_box_closure_dominates hd η hlow hhigh zc A hApos' hzcpos hlast
  have hlc := Exploding.Frozen.local_convexity d hd η hlow hhigh m path hpath A hAdef hfin
    hfin.toFinset.card (le_refl _) y hy
  have hkey := hdom hfin.toFinset.card y
  rw [hlc] at hkey
  omega

/-! ### (b) A long straight run of positivity overlaps the infinite cluster and
contradicts stability -/

/- `aux_penultimate_overlap_contradiction`: the mechanism named in the task
(and in the one-sentence paper proof): if the penultimate wave centred at `zc`
(which *does* stabilize, by `penultimate_stabilizable`, since `zc`'s last-wave
index is one more than its own) is positive along an entire straight run of
`> (log n)^{5/2}` consecutive *macroscopic good cubes* in direction `i`, that
run cannot lie entirely in a single finite complementary component of `Cinf`
(clause (2) of `renormalization_properties` bounds every such component's
cardinality by `(log n)^{5/2}`, exactly as in
`aux_finite_exploding_meets_cluster` of `lem-finite-exploding-dec/node.lean`,
applied to a line instead of a box), so the run must contain a macroscopic
site of `Cinf` itself; combined with `aux_penultimate_path_box_closure`, the
whole macroscopic cube there is then forced positive, and the *same*
propagation mechanism as `lem-finite-exploding`'s
`aux_finite_exploding_step`/`aux_finite_exploding_propagate`
(`lem-finite-exploding-dec/node.lean`) forces `¬ WaveStabilizable η
(waveThreshold η zc - 1) zc`, contradicting `hstab`.

`a`/`b` bound the run along axis `i`, based at `zc`. -/

-- PINNED DOWN (this pass), from the paper's ACTUAL proof of Lemma 3.5
-- (exploding.tex:799-804, the short one, no `Hypothesis path_filling`):
-- "By Lemma [local_convexity], `1{ũ^(x) > 0}` IS a rectangle [not merely
-- CONTAINS one], therefore it suffices to bound the maximal side length. By
-- Proposition [renormalization_properties], ... if any side length of the
-- rectangle exceeds `(2k log n)^{5/2}` then it must overlap a good cube,
-- contradicting stability." So `a`, `b` are meant to be the ACTUAL min/max
-- of `P(zc)`'s own bounding rectangle along axis `i` (`P(zc) = br(P(zc))`,
-- since `P(zc)` is connected through `zc` by `aux_penultimate_connected_to_
-- centre` and `aux_penultimate_path_box_closure` then forces the whole
-- bounding rectangle positive, so `P(zc)` cannot be a PROPER subset of its
-- own `br`). This pins down `a ≤ zc i ∧ zc i ≤ b` (since `zc ∈ P(zc)`, a
-- point of its own bounding rectangle) as the "based at `zc`" relation the
-- original doc-comment named but never wrote down -- CONFIRMED needed by a
-- future assembly of `Exploding.Frozen.last_penultimate_cluster` (to build
-- `a`, `b`, `hline` in the first place), though NOT needed by the internal
-- logic of `aux_penultimate_overlap_contradiction` itself (see below).
--
-- FALSE/UNDER-SPECIFIED STATEMENT FIX: the design's `hnz : (0 < mnorm zc) →
-- (mnorm zc : ℝ) ≤ n` is genuinely insufficient to discharge (i)'s `hin`
-- (`∀ v, a ≤ v → v ≤ b → (shifted point) ∈ cent d n`): `mnorm zc ≤ n` bounds
-- `zc` alone, not `a` or `b`, and `hab` only bounds the DIFFERENCE `b - a`,
-- not either endpoint individually, so no combination of `hnz`, `hab`, and a
-- hypothetical `a ≤ zc i ≤ b` forces `|a| ≤ n` or `|b| ≤ n`. (The paper's own
-- proof is silent on this because, read literally, its "if any side length
-- exceeds `(2k log n)^{5/2}`" already implicitly re-chooses which radius
-- `renormalization_properties` is applied at, e.g. `n' := n + (b - a)`, a
-- genuinely separate, self-referential radius-choice argument -- since
-- `log(n + (b-a))` still grows far slower than `b - a` once `b - a` is large
-- -- that this pass does not carry out.) FIXED by replacing `hnz` with the
-- SAME direct `hin` hypothesis `aux_penultimate_overlap_line_meets_cinf`
-- already needs: this is exactly, precisely, what is needed here, with no
-- guessing about the radius trade-off; discharging `hin` itself (via the
-- `n' := n + (b - a)` argument sketched above, or otherwise) is left to
-- whichever future pass assembles `Exploding.Frozen.last_penultimate_
-- cluster`, which is where the genuine remaining difficulty lives.
--
-- Split into the two genuinely separable halves below: (i)
-- `aux_penultimate_overlap_line_meets_cinf`, the pigeonhole argument (a line
-- longer than the hole bound cannot avoid `Cinf`, no positivity involved,
-- purely the geometry of `Cinfᶜ`'s components -- same recipe as
-- `aux_close_long_path`/`aux_finite_exploding_meets_cluster`); and (ii) the
-- propagation step, `aux_penultimate_overlap_propagate`, a re-centred
-- instance of `aux_finite_exploding_propagate`'s own mechanism
-- (`lem-finite-exploding-dec/node.lean`, itself still open at
-- `aux_finite_exploding_step`) and rated at the same difficulty. With `hin`
-- now correctly in the signature, `aux_penultimate_overlap_contradiction`
-- ITSELF is real (not `sorry`): a direct two-line composition of (i) and
-- (ii), needing no dynamics reasoning of its own.

/-- The pigeonhole half of `aux_penultimate_overlap_contradiction`: a line
longer than the hole bound cannot avoid `Cinf`.  Same recipe as
`aux_close_long_path`/`aux_finite_exploding_meets_cluster`: if it did, all its
(integer, hence `⌈b-a⌉+1`-many distinct) points would lie in a single
component of `Cinfᶜ` (`aux_close_long_path_chain`-style connectivity along
the `i`-direction unit steps, `componentIn`), whose cardinality `hcomp`
bounds by `Real.log n ^ (5/2) ≤ b - a`, a contradiction via
`Set.le_ncard_of_inj_on_range` on `v ↦ (fun j => if j = i then v else zc j)`
(injective since coordinate `i` differs). -/
theorem aux_penultimate_overlap_line_meets_cinf {d : ℕ} (Cinf : Set (Site d)) (n0 : ℕ)
    (hcomp : ∀ n, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ Cinf →
      (componentIn Cinfᶜ x).Finite ∧
        ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2))
    (n : ℕ) (hn : n0 ≤ n) (zc : Site d) (i : Fin d) (a b : ℤ)
    (hab : Real.log n ^ ((5 : ℝ) / 2) ≤ ((b - a : ℤ) : ℝ))
    (hin : ∀ v : ℤ, a ≤ v → v ≤ b →
      (fun j => if j = i then v else zc j) ∈ (cent d n : Set (Site d))) :
    ∃ v : ℤ, a ≤ v ∧ v ≤ b ∧ (fun j => if j = i then v else zc j) ∈ Cinf := by
  -- From `hab` we get `a ≤ b` since `Real.log n ^ (5/2) ≥ 0`
  have hab_le : a ≤ b := by
    by_contra h_lt
    have h_neg : ((b - a : ℤ) : ℝ) < 0 := by
      have : (b : ℤ) < a := by omega
      have h_neg' : (b : ℝ) < (a : ℝ) := by exact_mod_cast this
      push_cast
      linarith
    have h_nonneg : 0 ≤ Real.log (n : ℝ) ^ ((5 : ℝ) / 2) :=
      Real.rpow_nonneg (Real.log_natCast_nonneg _) _
    linarith [hab, h_nonneg, h_neg]
  -- The line function
  set f : ℤ → Site d := fun v => (fun j => if j = i then v else zc j) with hf
  have hf_inj : Function.Injective f := by
    intro v w h_eq
    have hcoords : f v i = f w i := by rw [h_eq]
    simp [f] at hcoords
    exact hcoords
  have hf_cent : ∀ v, a ≤ v → v ≤ b → f v ∈ (cent d n : Set (Site d)) := by
    intro v hva hvb
    simpa [f, hf] using hin v hva hvb
  by_contra h_no_Cinf
  simp only [not_exists, not_and] at h_no_Cinf
  -- h_no_Cinf : ∀ v, a ≤ v → v ≤ b → f v ∉ Cinf
  have hf_compl : ∀ v, a ≤ v → v ≤ b → f v ∈ Cinfᶜ := by
    intro v hva hvb
    -- Cinfᶜ is definitionally Cinfᶜ, so h_no_Cinf gives exactly membership
    exact h_no_Cinf v hva hvb
  -- Pick v₀ = a, get the component and its cardinality bound
  have ha_cent : f a ∈ (cent d n : Set (Site d)) := hf_cent a (le_refl a) hab_le
  have ha_compl : f a ∈ Cinfᶜ := hf_compl a (le_refl a) hab_le
  obtain ⟨h_fin_comp, h_card_comp⟩ := hcomp n hn (f a) ha_cent ha_compl
  -- h_fin_comp : (componentIn Cinfᶜ (f a)).Finite
  -- h_card_comp : ((componentIn Cinfᶜ (f a)).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2)
  -- Show that for any v ∈ [a, b], f v is in the same component as f a
  have h_chain (v : ℤ) (hva : a ≤ v) (hvb : v ≤ b) : f v ∈ componentIn Cinfᶜ (f a) := by
    -- Use Int.le_induction: prove P(w) := w ≤ b → f w ∈ componentIn Cinfᶜ (f a)
    -- for all w ≥ a, then apply to v
    have h_base : a ≤ b → f a ∈ componentIn Cinfᶜ (f a) := by
      intro _
      refine ⟨ha_compl, ha_compl, ?_⟩
      exact SimpleGraph.Reachable.refl (G := (lattice d).induce Cinfᶜ) ⟨f a, ha_compl⟩
    have h_step (w : ℤ) (hw : a ≤ w) (h_prev : w ≤ b → f w ∈ componentIn Cinfᶜ (f a)) :
        (w + 1 ≤ b → f (w + 1) ∈ componentIn Cinfᶜ (f a)) := by
      intro hw1_le_b
      have hw_le_b : w ≤ b := by omega
      have h_fw : f w ∈ componentIn Cinfᶜ (f a) := h_prev hw_le_b
      rcases h_fw with ⟨hx, hy, hreach⟩
      -- hx : f a ∈ Cinfᶜ, hy : f w ∈ Cinfᶜ, hreach : Reachable from f a to f w
      have h_adj : (lattice d).Adj (f w) (f (w + 1)) := by
        have h_eq : f (w + 1) = f w + unit i := by
          ext j
          dsimp [f]
          by_cases hj : j = i
          · subst hj; simp [unit]
          · simp [unit, hj]
        rw [h_eq]
        exact (adj_add_unit (f w) i).symm
      have h_fw1_compl : f (w + 1) ∈ Cinfᶜ := hf_compl (w + 1) (by omega) hw1_le_b
      have h_adj_induce : ((lattice d).induce Cinfᶜ).Adj ⟨f w, hy⟩ ⟨f (w + 1), h_fw1_compl⟩ := by
        simpa [SimpleGraph.induce_adj] using h_adj
      have h_reach_ext : ((lattice d).induce Cinfᶜ).Reachable ⟨f a, hx⟩ ⟨f (w + 1), h_fw1_compl⟩ :=
        hreach.trans ⟨SimpleGraph.Walk.cons h_adj_induce SimpleGraph.Walk.nil⟩
      exact ⟨hx, h_fw1_compl, h_reach_ext⟩
    have h_all : ∀ n, a ≤ n → (n ≤ b → f n ∈ componentIn Cinfᶜ (f a)) :=
      Int.leInduction h_base h_step
    exact h_all v hva hvb
  -- Now we have that the image of Icc a b under f is contained in the component
  have h_image_subset : (Finset.image f (Finset.Icc a b) : Set (Site d)) ⊆ componentIn Cinfᶜ (f a) := by
    intro x hx
    simp only [Finset.mem_coe, Finset.mem_image] at hx
    rcases hx with ⟨v, hv, rfl⟩
    rcases Finset.mem_Icc.mp hv with ⟨hva, hvb⟩
    exact h_chain v hva hvb
  -- Cardinality argument
  have h_card_image : ((Finset.image f (Finset.Icc a b) : Set (Site d)).ncard : ℝ) = ((Finset.Icc a b).card : ℝ) := by
    have h : (Finset.image f (Finset.Icc a b) : Set (Site d)).ncard = (Finset.Icc a b).card := by
      simpa [Finset.card_image_of_injective _ hf_inj] using Set.ncard_coe_finset (Finset.image f (Finset.Icc a b))
    exact mod_cast h
  have h_card_Icc : (Finset.Icc a b).card = (b + 1 - a).toNat := by
    simp [Int.card_Icc]
  have h_card_Icc_val : ((Finset.Icc a b).card : ℝ) = ((b + 1 - a).toNat : ℝ) := by
    norm_cast
  -- The component's ncard is at least the image's ncard
  have h_ncard_le : ((Finset.image f (Finset.Icc a b) : Set (Site d)).ncard : ℝ) ≤
      ((componentIn Cinfᶜ (f a)).ncard : ℝ) := by
    have : ((Finset.image f (Finset.Icc a b) : Set (Site d)).ncard : ℕ) ≤
        (componentIn Cinfᶜ (f a)).ncard :=
      Set.ncard_le_ncard h_image_subset h_fin_comp
    exact mod_cast this
  -- Combine the inequalities
  have h_bound : ((b + 1 - a).toNat : ℝ) < Real.log n ^ ((5 : ℝ) / 2) := by
    linarith [h_card_image, h_card_Icc_val, h_ncard_le, h_card_comp]
  have h_bound2 : Real.log n ^ ((5 : ℝ) / 2) ≤ ((b - a : ℤ) : ℝ) := hab
  -- But (b + 1 - a).toNat ≥ b + 1 - a as integers, and b + 1 - a > b - a
  have h_ineq : ((b - a : ℤ) : ℝ) < ((b + 1 - a).toNat : ℝ) := by
    have hpos : 0 ≤ b + 1 - a := by omega
    have h_eq : ((b + 1 - a).toNat : ℤ) = b + 1 - a := Int.toNat_of_nonneg hpos
    have h_eq' : ((b + 1 - a).toNat : ℝ) = ((b + 1 - a : ℤ) : ℝ) := by exact_mod_cast h_eq
    rw [h_eq']
    push_cast
    linarith
  linarith [h_bound, h_bound2, h_ineq]

/-- **The strengthened pigeonhole.**  A run meets `Cinf` outside the interval
`[lo, hi]`, provided one of the two pieces the interval cuts off is still longer
than the hole bound.  This is the form the `M̂ = 2` case of the side-length bound
needs: the cube's image occupies a contiguous interval of the run's
`dir`-coordinate, so a run long enough to leave a piece longer than the hole
bound on either side meets `Cinf` outside the cube. -/
theorem aux_penultimate_overlap_line_meets_cinf_outside {d : ℕ} (Cinf : Set (Site d)) (n0 : ℕ)
    (hcomp : ∀ n, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ Cinf →
      (componentIn Cinfᶜ x).Finite ∧
        ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2))
    (n : ℕ) (hn : n0 ≤ n) (zc : Site d) (i : Fin d) (a b : ℤ)
    (hin : ∀ v : ℤ, a ≤ v → v ≤ b →
      (fun j => if j = i then v else zc j) ∈ (cent d n : Set (Site d)))
    (lo hi : ℤ) (hlo : a ≤ lo) (hhi : hi ≤ b) (hlohi : lo ≤ hi)
    (hlen : Real.log n ^ ((5 : ℝ) / 2) ≤ ((lo - 1 - a : ℤ) : ℝ) ∨
            Real.log n ^ ((5 : ℝ) / 2) ≤ ((b - (hi + 1) : ℤ) : ℝ)) :
    ∃ u : ℤ, a ≤ u ∧ u ≤ b ∧ (fun j => if j = i then u else zc j) ∈ Cinf ∧
      (u < lo ∨ hi < u) := by
  rcases hlen with h | h
  · obtain ⟨u, hua, hub, huC⟩ :=
      aux_penultimate_overlap_line_meets_cinf Cinf n0 hcomp n hn zc i a (lo - 1) h
        (fun v hv hv' => hin v hv (by omega))
    exact ⟨u, hua, by omega, huC, Or.inl (by omega)⟩
  · obtain ⟨u, hua, hub, huC⟩ :=
      aux_penultimate_overlap_line_meets_cinf Cinf n0 hcomp n hn zc i (hi + 1) b h
        (fun v hv hv' => hin v (by omega) hv')
    exact ⟨u, by omega, hub, huC, Or.inr (by omega)⟩

/-- **The penultimate-cluster propagation, first step.**  If the penultimate
wave is positive at a site `v0` of the infinite good cluster, then the
`(M-1)`-wave from `zc` is positive at `v0` at some finite time.  This is
`aux_penultimate_wave_pos_implies_terminal`'s converse direction, and it is the
first step of `aux_penultimate_overlap_propagate`. -/
theorem penultimate_pos_at_time {d : ℕ} (η : Site d → ℤ) (_hlow : ∀ x, 0 ≤ η x)
    (_hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (zc v0 : Site d)
    (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n zc)
    (h1 : waveThreshold η zc ≠ 1) (hv0 : 0 < penultimateWave η zc v0) :
    ∃ t : ℕ, 0 < wave η (waveThreshold η zc - 1) zc t v0 := by
  obtain ⟨T, hT⟩ := penultimate_stabilizable η zc hlast h1
  refine ⟨T, ?_⟩
  rw [penultimateWave, if_neg h1] at hv0
  have hle : sInf {T : ℕ | ∀ t : ℕ, T ≤ t →
      wave η (waveThreshold η zc - 1) zc t = wave η (waveThreshold η zc - 1) zc T} ≤ T :=
    Nat.sInf_le hT
  have h := waveTerminal_spec η (waveThreshold η zc - 1) zc ⟨T, hT⟩ T hle
  rw [h]
  exact hv0

/-- The macroscopic cube index containing the microscopic site `x` at scale
`k ≥ 1`: the unique `i` with `x - k•i ∈ cube d k`. -/
noncomputable def macroIdx {d : ℕ} (k : ℕ) (x : Site d) : Site d :=
  fun i => (x i - 1) / (k : ℤ)

theorem key_up (k : ℤ) (hk : 0 < k) (a : ℤ) :
    (a + 1 - 1) / k = (a - 1) / k ∨ (a + 1 - 1) / k = (a - 1) / k + 1 := by
  have h1 := Int.emod_add_ediv_mul (a - 1) k
  have h2 : 0 ≤ (a - 1) % k := Int.emod_nonneg _ (ne_of_gt hk)
  have h3 : (a - 1) % k < k := Int.emod_lt_of_pos _ hk
  have h4 : (a + 1 - 1) = (a - 1) + 1 := by ring
  rw [h4]
  by_cases h : (a - 1) % k + 1 < k
  · left
    have h6 : (a - 1) + 1 = ((a - 1) / k) * k + ((a - 1) % k + 1) := by linarith
    rw [h6]
    rw [show ((a - 1) / k) * k + ((a - 1) % k + 1)
        = ((a - 1) % k + 1) + ((a - 1) / k) * k from by ring]
    rw [Int.add_mul_ediv_right _ _ (ne_of_gt hk)]
    rw [Int.ediv_eq_zero_of_lt (by omega) (by omega)]
    ring
  · right
    have h6 : (a - 1) % k + 1 = k := by omega
    have h7 : (a - 1) + 1 = ((a - 1) / k + 1) * k + 0 := by
      have := Int.emod_add_ediv_mul (a - 1) k
      nlinarith
    rw [h7]
    rw [show ((a - 1) / k + 1) * k + 0 = 0 + ((a - 1) / k + 1) * k from by ring]
    rw [Int.add_mul_ediv_right _ _ (ne_of_gt hk)]
    rw [Int.ediv_eq_zero_of_lt (by omega) (by omega)]
    ring

theorem key_down (k : ℤ) (hk : 0 < k) (a : ℤ) :
    (a - 1 - 1) / k = (a - 1) / k ∨ (a - 1 - 1) / k = (a - 1) / k - 1 := by
  have h1 := Int.emod_add_ediv_mul (a - 1) k
  have h2 : 0 ≤ (a - 1) % k := Int.emod_nonneg _ (ne_of_gt hk)
  have h3 : (a - 1) % k < k := Int.emod_lt_of_pos _ hk
  have h4 : (a - 1 - 1) = (a - 1) - 1 := by ring
  rw [h4]
  by_cases h : 0 < (a - 1) % k
  · left
    have h6 : (a - 1) - 1 = ((a - 1) / k) * k + ((a - 1) % k - 1) := by
      have h8 : (a - 1) / k * k = a - 1 - (a - 1) % k := by linarith
      rw [h8]
      ring
    rw [h6]
    rw [show ((a - 1) / k) * k + ((a - 1) % k - 1)
        = ((a - 1) % k - 1) + ((a - 1) / k) * k from by ring]
    rw [Int.add_mul_ediv_right _ _ (ne_of_gt hk)]
    have h7 : ((a - 1) % k - 1) / k = 0 := by
      apply Int.ediv_eq_zero_of_lt
      · omega
      · omega
    rw [h7]
    ring
  · right
    have h6 : (a - 1) % k = 0 := by omega
    have h7 : (a - 1) - 1 = ((a - 1) / k - 1) * k + (k - 1) := by
      have h8 : (a - 1) / k * k = a - 1 := by linarith
      have h9 : ((a - 1) / k - 1) * k = (a - 1) / k * k - k := by ring
      rw [h9, h8]
      ring
    rw [h7]
    rw [show ((a - 1) / k - 1) * k + (k - 1)
        = (k - 1) + ((a - 1) / k - 1) * k from by ring]
    rw [Int.add_mul_ediv_right _ _ (ne_of_gt hk)]
    have h8 : (k - 1) / k = 0 := by
      apply Int.ediv_eq_zero_of_lt
      · omega
      · omega
    rw [h8]
    ring

/-- One micro-step changes the macro index by at most one edge. -/
theorem macroIdx_adj {d : ℕ} (k : ℕ) (hk : 1 ≤ k) (x : Site d) (i : Fin d) :
    (macroIdx k (x + unit i) = macroIdx k x ∨
      (lattice d).Adj (macroIdx k (x + unit i)) (macroIdx k x)) ∧
    (macroIdx k (x - unit i) = macroIdx k x ∨
      (lattice d).Adj (macroIdx k (x - unit i)) (macroIdx k x)) := by
  have hk' : (0 : ℤ) < (k : ℤ) := Nat.cast_pos.mpr hk
  have hcoord : ∀ (y : Site d) (j : Fin d), j ≠ i → y j = x j →
      macroIdx k y j = macroIdx k x j := by
    intro y j hj h
    simp only [macroIdx, h]
  have hplus : (x + unit i) i = x i + 1 := by
    simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_same]
  have hminus : (x - unit i) i = x i - 1 := by
    simp only [Pi.sub_apply, LatticeProb.unit, Pi.single_eq_same]
  constructor
  · by_cases h : (macroIdx k (x + unit i)) i = (macroIdx k x) i + 1
    · right
      refine ⟨i, Or.inr ?_⟩
      funext j
      by_cases hj : j = i
      · rw [hj]
        simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_same]
        exact h
      · have h1 : (x + unit i) j = x j := by
          simp only [Pi.add_apply, LatticeProb.unit]
          rw [Pi.single_eq_of_ne hj]
          simp
        rw [hcoord _ j hj h1]
        have h2 : (LatticeProb.unit i : Site d) j = 0 := by
          simp only [LatticeProb.unit, Pi.single_eq_of_ne hj]
        simp only [Pi.add_apply, h2, add_zero]
    · left
      funext j
      by_cases hj : j = i
      · rw [hj]
        simp only [macroIdx, hplus] at h ⊢
        rcases key_up (k : ℤ) hk' (x i) with hk1 | hk1
        · exact hk1
        · exact absurd hk1 h
      · have h1 : (x + unit i) j = x j := by
          simp only [Pi.add_apply, LatticeProb.unit]
          rw [Pi.single_eq_of_ne hj]
          simp
        rw [hcoord _ j hj h1]
  · by_cases h : (macroIdx k (x - unit i)) i = (macroIdx k x) i - 1
    · right
      refine ⟨i, Or.inl ?_⟩
      funext j
      by_cases hj : j = i
      · rw [hj]
        simp only [macroIdx, Pi.add_apply, Pi.sub_apply, LatticeProb.unit,
          Pi.single_eq_same] at h ⊢
        omega
      · have h1 : (x - unit i) j = x j := by
          simp only [Pi.sub_apply, LatticeProb.unit]
          rw [Pi.single_eq_of_ne hj]
          simp
        have h2 : (LatticeProb.unit i : Site d) j = 0 := by
          simp only [LatticeProb.unit, Pi.single_eq_of_ne hj]
        have h3 : macroIdx k (x - unit i) j = macroIdx k x j := hcoord _ j hj h1
        simp only [Pi.add_apply, h2, add_zero]
        exact h3.symm
    · left
      funext j
      by_cases hj : j = i
      · rw [hj]
        simp only [macroIdx, hminus] at h ⊢
        rcases key_down (k : ℤ) hk' (x i) with hk1 | hk1
        · exact hk1
        · exact absurd hk1 h
      · have h1 : (x - unit i) j = x j := by
          simp only [Pi.sub_apply, LatticeProb.unit]
          rw [Pi.single_eq_of_ne hj]
          simp
        rw [hcoord _ j hj h1]

/-- The key implication: with `η ≤ 2d-1`, a positive wave value at `t+1` forces a
positive neighbour at `t`. -/
theorem nbrSum_pos_of_wave_pos {d : ℕ} (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (n : ℕ) (t : ℕ) (x : Site d)
    (hx : 0 < wave η n (0 : Site d) (t + 1) x) (hx0 : x ≠ 0) :
    0 < nbrSumZ (wave η n (0 : Site d) t) x := by
  rw [wave_of_ne η n 0 x t hx0] at hx
  by_contra hcon
  have hle : nbrSumZ (wave η n (0 : Site d) t) x ≤ 0 := le_of_not_gt hcon
  have hnn : 0 ≤ nbrSumZ (wave η n (0 : Site d) t) x :=
    nbrSumZ_nonneg _ (fun y => wave_nonneg η hlow n 0 t y) x
  have h0 : nbrSumZ (wave η n (0 : Site d) t) x = 0 := le_antisymm hle hnn
  rw [h0, zero_add] at hx
  have h2d : (0 : ℤ) < 2 * (d : ℤ) := by
    have hd1 : (1 : ℤ) ≤ (d : ℤ) := by
      by_contra hc
      have hd0 : d = 0 := by omega
      subst hd0
      simp at hx
    linarith
  -- 0 < η x / (2d) with 2d > 0 forces η x ≥ 2d, contradicting η x ≤ 2d-1.
  have hge : 2 * (d : ℤ) ≤ η x := by
    by_contra hc
    have h1 : η x ≤ 2 * (d : ℤ) - 1 := by omega
    have h3 : η x / (2 * (d : ℤ)) ≤ (2 * (d : ℤ) - 1) / (2 * (d : ℤ)) :=
      Int.ediv_le_ediv h2d h1
    have h4 : (2 * (d : ℤ) - 1) / (2 * (d : ℤ)) = 0 := by
      apply Int.ediv_eq_zero_of_lt
      · linarith
      · linarith
    rw [h4] at h3
    linarith
  have hh := hhigh x
  omega

/-- **The macro-level reachability.** -/
theorem macro_reach {d : ℕ} (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (_hn : 1 ≤ n) (Cinf : Set (Site d))
    (havoid : ∀ t x, 0 < wave η n (0 : Site d) t x → macroIdx k x ∉ Cinf) :
    ∀ t x, 0 < wave η n (0 : Site d) t x →
      macroIdx k x ∈ componentIn Cinfᶜ (macroIdx k (0 : Site d)) := by
  intro t
  induction t with
  | zero =>
    intro x hx
    rw [wave_zero] at hx
    by_cases h : x = 0
    · subst h
      exact ⟨havoid 0 0 hx, havoid 0 0 hx, SimpleGraph.Reachable.refl _⟩
    · simp [h] at hx
  | succ t ih =>
    intro x hx
    rw [wave_succ] at hx
    by_cases h : x = 0
    · subst h
      exact ⟨havoid (t + 1) 0 hx, havoid (t + 1) 0 hx, SimpleGraph.Reachable.refl _⟩
    · have hxorig : 0 < wave η n (0 : Site d) (t + 1) x := hx
      rw [if_neg h] at hx
      by_cases hx' : 0 < wave η n (0 : Site d) t x
      · exact ih x hx'
      · have hsum : 0 < nbrSumZ (wave η n (0 : Site d) t) x :=
          nbrSum_pos_of_wave_pos η hlow hhigh n t x hxorig h
        obtain ⟨y, hy, hypos⟩ :=
          exists_adj_pos_of_nbrSumZ_pos (wave η n (0 : Site d) t)
            (fun y => wave_nonneg η hlow n 0 t y) x hsum
        have hrec := ih y hypos
        rcases hrec with ⟨h0c, hyc, h3⟩
        have hxnot : macroIdx k x ∉ Cinf := havoid (t + 1) x hxorig
        have hxcompl : macroIdx k x ∈ Cinfᶜ := hxnot
        obtain ⟨i, hi | hi⟩ := hy
        · -- hi : x = y + unit i, so y = x - unit i
          have hyeq : y = x - unit i := by rw [hi]; abel
          subst hyeq
          rcases (macroIdx_adj k hk x i).2 with heq | hadj
          · rw [← heq]
            exact ⟨h0c, hyc, h3⟩
          · have hadj' : ((lattice d).induce Cinfᶜ).Adj
                ⟨macroIdx k (x - unit i), hyc⟩ ⟨macroIdx k x, hxcompl⟩ := by
              simpa [SimpleGraph.induce_adj] using hadj
            exact ⟨h0c, hxcompl,
              h3.trans ⟨SimpleGraph.Walk.cons hadj' SimpleGraph.Walk.nil⟩⟩
        · -- hi : y = x + unit i
          subst hi
          rcases (macroIdx_adj k hk x i).1 with heq | hadj
          · rw [← heq]
            exact ⟨h0c, hyc, h3⟩
          · have hadj' : ((lattice d).induce Cinfᶜ).Adj
                ⟨macroIdx k (x + unit i), hyc⟩ ⟨macroIdx k x, hxcompl⟩ := by
              simpa [SimpleGraph.induce_adj] using hadj
            exact ⟨h0c, hxcompl,
              h3.trans ⟨SimpleGraph.Walk.cons hadj' SimpleGraph.Walk.nil⟩⟩

/-- The last wave dominates the penultimate wave at any time past the penultimate
wave's stabilization. -/
theorem penultimate_le_last {d : ℕ} (η : Site d → ℤ) (_hlow0 : ∀ y, 0 ≤ η y)
    (hd : (0 : ℤ) < 2 * (d : ℤ))
    (z : Site d) (_hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n z)
    (h1 : waveThreshold η z ≠ 1) (T : ℕ)
    (hT : ∀ t : ℕ, T ≤ t → wave η (waveThreshold η z - 1) z t =
      wave η (waveThreshold η z - 1) z T)
    (t : ℕ) (ht : T ≤ t) (x : Site d) :
    penultimateWave η z x ≤ lastWave η z t x := by
  rw [penultimateWave, if_neg h1, lastWave]
  have hspec := waveTerminal_spec η (waveThreshold η z - 1) z ⟨T, hT⟩ T
    (Nat.sInf_le (show T ∈ {T : ℕ | ∀ t : ℕ, T ≤ t →
      wave η (waveThreshold η z - 1) z t = wave η (waveThreshold η z - 1) z T} from hT))
  rw [← hspec]
  rw [← hT t ht]
  exact wave_mono_n η hd z (Nat.sub_le (waveThreshold η z) 1) t x

/-- **The penultimate wave is positive on the bounding box of a path from `zc` to
`v0`.** -/
theorem pen_box_pos {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (zc v0 : Site d) (hv0pos : 0 < penultimateWave η zc v0) :
    ∃ (m : ℕ) (path : ℕ → Site d), path 0 = zc ∧ path m = v0 ∧
      (∀ i : ℕ, i < m → (lattice d).Adj (path i) (path (i + 1))) ∧
      (br (path '' {i : ℕ | i ≤ m})).Finite ∧
      ∀ y ∈ br (path '' {i : ℕ | i ≤ m}), 0 < penultimateWave η zc y := by
  have hlow0 : ∀ x, 0 ≤ η x := fun x => by have := hlow x; linarith
  obtain ⟨r, path, h0, hr, hadj, hpos⟩ :=
    aux_penultimate_connected_to_centre η hlow0 hhigh zc v0 hv0pos
  have hfin : (br (path '' {i : ℕ | i ≤ r})).Finite :=
    br_finite _ (Set.Finite.image _ (Set.finite_Iic r))
  exact ⟨r, path, h0, hr, hadj, hfin,
    aux_penultimate_path_box_closure hd η hlow hhigh zc r path hadj hpos hfin⟩

open Exploding LatticeProb in
theorem abs_coord_le_mnorm {d : ℕ} (x : Site d) (i : Fin d) : |x i| ≤ mnorm x := by
  rw [mnorm]
  exact Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)

/-- **A box containing a cube contains a line of that cube.**  The line is read in
the cube's local coordinates: `line d k dir z + k•i`. -/
theorem box_line_of_cube {d : ℕ} (k : ℕ) (hk : 1 ≤ k) (R : Set (Site d)) (m M : Site d)
    (_hR : R = {x | ∀ i, m i ≤ x i ∧ x i ≤ M i})
    (dir : Fin d) (i : Site d)
    (hsub : ∀ x ∈ cube d k, x + (k : ℤ) • i ∈ R) :
    ∃ z : Site d, z + (k : ℤ) • i ∈ R ∧
      ∀ y ∈ line d k dir z, y + (k : ℤ) • i ∈ R := by
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  refine ⟨fun _ => (1 : ℤ), ?_, ?_⟩
  · exact hsub _ (fun l => ⟨le_refl 1, hk1⟩)
  · intro y hy
    exact hsub _ (fun l => by
      by_cases hl : l = dir
      · rw [hl]; exact hy.1
      · rw [hy.2 l hl]
        exact ⟨le_refl 1, hk1⟩)

/-- The terminal odometer of a stabilizable wave vanishes far from its centre. -/
theorem waveTerminal_eq_zero_far {d : ℕ} (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (n : ℕ) (z : Site d)
    (hs : WaveStabilizable η n z) (x : Site d)
    (hx : ((sInf {T : ℕ | ∀ t : ℕ, T ≤ t → wave η n z t = wave η n z T} : ℕ) : ℤ) <
      mnorm (x - z)) :
    waveTerminal η n z x = 0 := by
  set T := sInf {T : ℕ | ∀ t : ℕ, T ≤ t → wave η n z t = wave η n z T} with hT
  have hspec := waveTerminal_spec η n z hs T le_rfl
  simp only [waveTerminal]
  rw [hspec]
  exact aux_finite_exploding_speed η hlow hhigh n z T x hx

/-- **The geometric step.**  Let `zc` be the fixed other-coordinates of a run of
positivity of the penultimate wave in direction `dir`, and let `i ∈ Cinf` be a
cube index whose cube the run passes through, in the sense that `i` agrees with
`zc` in the other coordinates after the cube-index change of variables
`i l = (zc l - 1) / k` and the run's `dir`-coordinates `[1 + k * i dir, k + k * i dir]`
lie inside the run `[a, b]`.  Then the line of `Q_k(i)` in direction `dir` based
at the cube's lower corner maps into the run. -/
theorem aux_penultimate_run_meets_cube {d : ℕ} (η : Site d → ℤ)
    (k : ℕ) (hk : 1 ≤ k) (zc : Site d) (dir : Fin d) (a b : ℤ)
    (i : Site d)
    (hi : ∀ l, l ≠ dir → i l = (zc l - 1) / (k : ℤ))
    (hlo : a ≤ 1 + (k : ℤ) * i dir)
    (hhi : (k : ℤ) + (k : ℤ) * i dir ≤ b)
    (hline : ∀ v : ℤ, a ≤ v → v ≤ b →
      0 < penultimateWave η zc (fun j => if j = dir then v else zc j)) :
    ∃ z : Site d, z ∈ cube d k ∧
      ∀ w ∈ line d k dir z, 0 < penultimateWave η zc (w + (k : ℤ) • i) := by
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hk0 : (0 : ℤ) < (k : ℤ) := by linarith
  -- the base point: the cube's lower corner in the other coordinates
  refine ⟨fun l => if l = dir then 1 else ((zc l - 1) % (k : ℤ)) + 1, ?_, ?_⟩
  · -- the base point lies in the cube
    intro l
    simp only
    by_cases hl : l = dir
    · rw [if_pos hl]; exact ⟨le_refl 1, hk1⟩
    · rw [if_neg hl]
      have hmod0 : 0 ≤ (zc l - 1) % (k : ℤ) := Int.emod_nonneg _ (by linarith)
      have hmodk : (zc l - 1) % (k : ℤ) < (k : ℤ) := Int.emod_lt_of_pos _ hk0
      constructor <;> linarith
  · -- the line maps into the run
    intro w hw
    -- the other coordinates of `w + k•i` are `zc`'s
    have hother : ∀ l, l ≠ dir → (w + (k : ℤ) • i) l = zc l := by
      intro l hl
      have hwl : w l = ((zc l - 1) % (k : ℤ)) + 1 := by
        have := hw.2 l hl
        simpa only [if_neg hl] using this
      have hdiv : (k : ℤ) * ((zc l - 1) / (k : ℤ)) = zc l - 1 - ((zc l - 1) % (k : ℤ)) := by
        have := Int.ediv_mul_add_emod (zc l - 1) (k : ℤ)
        linarith
      have hik : (k : ℤ) * i l = zc l - 1 - ((zc l - 1) % (k : ℤ)) := by
        rw [hi l hl]; exact hdiv
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hwl]
      linarith
    -- the `dir`-coordinate of `w + k•i` lies in the run
    have hdir : (w + (k : ℤ) • i) dir = w dir + (k : ℤ) * i dir := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hwlo : (1 : ℤ) ≤ w dir := hw.1.1
    have hwhi : w dir ≤ (k : ℤ) := hw.1.2
    have hge : a ≤ w dir + (k : ℤ) * i dir := by linarith
    have hle : w dir + (k : ℤ) * i dir ≤ b := by linarith
    -- identify the point with the run point at that coordinate
    have hfun : (fun j => if j = dir then w dir + (k : ℤ) * i dir else zc j)
        = (w + (k : ℤ) • i) := by
      ext l
      by_cases hl : l = dir
      · subst hl; simp only [if_true, hdir]
      · simp only [if_neg hl, hother l hl]
    rw [← hfun]
    exact hline _ hge hle

/-- **The geometric fact for the `N = 1` propagation.**  If `zc` lies in the
image `cube d k + k•b` of a macroscopic cube, then `b` is exactly `zc`'s own cube
index `macroIdx k zc`: writing `zc j = y j + k * b j` with `1 ≤ y j ≤ k` gives
`zc j - 1 = (y j - 1) + k * b j` with `0 ≤ y j - 1 < k`, so
`(zc j - 1) / k = b j`.  Hence `mnorm (b - macroIdx k zc) = 0`. -/
theorem macroIdx_eq_of_mem_image {d : ℕ} (k : ℕ) (hk : 1 ≤ k) (zc : Site d)
    (b : Site d) (hb : ∃ y ∈ cube d k, y + (k : ℤ) • b = zc) :
    b = macroIdx k zc := by
  obtain ⟨y, hy, hyb⟩ := hb
  have hk0 : (0 : ℤ) < (k : ℤ) := Nat.cast_pos.mpr hk
  ext j
  have hyj : 1 ≤ y j ∧ y j ≤ (k : ℤ) := hy j
  have hzj : zc j = y j + (k : ℤ) * b j := by
    have := congrFun hyb j
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this.symm
  have h1 : zc j - 1 = (y j - 1) + (k : ℤ) * b j := by linarith
  have h2 : 0 ≤ y j - 1 ∧ y j - 1 < (k : ℤ) := by omega
  have h4 : (y j - 1) / (k : ℤ) = 0 := Int.ediv_eq_zero_of_lt h2.1 h2.2
  simp only [macroIdx]
  rw [h1]
  rw [Int.add_mul_ediv_left _ _ (ne_of_gt hk0)]
  rw [h4, zero_add]

theorem aux_penultimate_overlap_propagate_line {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (k : ℕ) (hk : 1 ≤ k) (Cinf : Set (Site d)) (hCinf : IsInfiniteConnectedGoodSet η k Cinf)
    (zc : Site d) (i : Site d) (hiCinf : i ∈ Cinf)
    (dir : Fin d) (z : Site d) (hz : z ∈ cube d k)
    (hline : ∀ w ∈ line d k dir z, 0 < penultimateWave η zc (w + (k : ℤ) • i))
    (hN : 2 ≤ waveThreshold η zc - 1)
    (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n zc) : False := by
  have hlow0 : ∀ x, 0 ≤ η x := fun x => by have := hlow x; linarith
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  -- the penultimate wave is positive at the line's base point
  have hzpos : 0 < penultimateWave η zc (z + (k : ℤ) • i) := hline z (by
    exact ⟨hz dir, fun l hl => rfl⟩)
  have h1 : waveThreshold η zc ≠ 1 := by
    intro h
    have hp : penultimateWave η zc = 0 := by simp [penultimateWave, h]
    rw [hp] at hzpos
    simp at hzpos
  have hN' : 2 ≤ waveThreshold η zc - 1 := hN
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  -- the penultimate wave is stabilizable, so its support is finite
  have hpenstab : WaveStabilizable η (waveThreshold η zc - 1) zc :=
    penultimate_stabilizable η zc hlast h1
  have hpenstab' := hpenstab
  obtain ⟨T, hT⟩ := hpenstab
  have hpen_eq : ∀ x : Site d,
      penultimateWave η zc x = wave η (waveThreshold η zc - 1) zc T x := by
    intro x
    simp only [penultimateWave, if_neg h1, waveTerminal]
    exact (congrFun (waveTerminal_spec η (waveThreshold η zc - 1) zc hpenstab' T
      (Nat.sInf_le hT)) x).symm
  have hpenfin : {x : Site d | 0 < penultimateWave η zc x}.Finite := by
    refine Set.Finite.subset (Set.finite_Icc (zc - fun _ => (T : ℤ)) (zc + fun _ => (T : ℤ))) ?_
    intro x hx
    have hx' : 0 < penultimateWave η zc x := hx
    rw [hpen_eq x] at hx'
    constructor
    · intro i
      by_contra hcon
      have hcon' : zc i - (T : ℤ) > x i := not_le.mp hcon
      have hsp := aux_finite_exploding_speed η hlow0 hhigh (waveThreshold η zc - 1) zc T x
      have hm : (T : ℤ) < mnorm (x - zc) := by
        have h1' : (T : ℤ) < zc i - x i := by linarith
        have h2' : zc i - x i ≤ mnorm (x - zc) := by
          have := abs_coord_le_mnorm (x - zc) i
          rw [show (x - zc) i = x i - zc i from rfl] at this
          rw [abs_of_neg (by linarith : x i - zc i < 0)] at this
          linarith
        linarith
      rw [hsp hm] at hx'
      exact lt_irrefl 0 hx'
    · intro i
      by_contra hcon
      have hcon' : x i > zc i + (T : ℤ) := not_le.mp hcon
      have hsp := aux_finite_exploding_speed η hlow0 hhigh (waveThreshold η zc - 1) zc T x
      have hm : (T : ℤ) < mnorm (x - zc) := by
        have h1' : (T : ℤ) < x i - zc i := by linarith
        have h2' : x i - zc i ≤ mnorm (x - zc) := by
          have := abs_coord_le_mnorm (x - zc) i
          rw [show (x - zc) i = x i - zc i from rfl] at this
          rw [abs_of_pos (by linarith : 0 < x i - zc i)] at this
          exact this
        linarith
      rw [hsp hm] at hx'
      exact lt_irrefl 0 hx'
  -- the (M̂-1)-wave is positive on the line at time T
  have hline' : ∀ w ∈ line d k dir z,
      0 < wave η (waveThreshold η zc - 1) zc T (w + (k : ℤ) • i) := by
    intro w hw
    rw [← hpen_eq]
    exact hline w hw
  obtain ⟨t', ht'⟩ := wave_covers_of_line hd η hlow0 hhigh (waveThreshold η zc - 1) k hN' zc i
    (hCinf.2.1 hiCinf) dir z (Or.inl hz) T hline'
  -- the penultimate wave is positive on Q_k(i)
  have hcov : ∀ x ∈ cube d k, 0 < penultimateWave η zc (x + (k : ℤ) • i) := by
    intro x hx
    rw [hpen_eq]
    have hpos := ht'.2 x hx
    have hmono := wave_mono_time η hlow0 hd0 (waveThreshold η zc - 1) zc (le_max_right T t')
      (x + (k : ℤ) • i)
    have hmax : 0 < wave η (waveThreshold η zc - 1) zc (max T t') (x + (k : ℤ) • i) := by linarith
    rw [← hT (max T t') (le_max_left T t')]
    exact hmax
  -- propagate to every cube of the cluster
  have hreach' : ∀ y ∈ Cinf, ∃ t, ∀ x ∈ cube d k,
      0 < wave η (waveThreshold η zc - 1) zc t (x + (k : ℤ) • y) := by
    intro y hy
    have hstep : ∀ (a b : Site d), GoodAt η k b → (lattice d).Adj a b → ∀ s : ℕ,
        (∀ x ∈ cube d k, 0 < wave η (waveThreshold η zc - 1) zc s (x + (k : ℤ) • a)) →
        ∃ s' : ℕ, s ≤ s' ∧
          ∀ x ∈ cube d k, 0 < wave η (waveThreshold η zc - 1) zc s' (x + (k : ℤ) • b) := by
      intro a b hgood hadj s hs
      obtain ⟨dir', hdir'⟩ := hadj
      obtain ⟨dir'', hne⟩ : ∃ dir'' : Fin d, dir'' ≠ dir' := by
        by_contra hcon
        simp only [not_exists, not_not] at hcon
        have hcard : Fintype.card (Fin d) = 1 := Fintype.card_eq_one_iff.mpr ⟨dir', hcon⟩
        rw [Fintype.card_fin] at hcard
        omega
      exact finite_exploding_step hd η hlow0 hhigh (waveThreshold η zc - 1) k hN' hk zc a b
        hgood dir' hdir' dir'' hne s hs
    obtain ⟨t'', ht''⟩ := aux_finite_exploding_propagate_walk η hlow0 hhigh
      (waveThreshold η zc - 1) k zc Cinf hCinf.2.1 hstep i y (hCinf.2.2 i hiCinf y hy) t' ht'.2
    exact ⟨t'', ht''⟩
  -- so the penultimate wave is positive on Q_k(y) for every y in the cluster
  have hpeninf : {x : Site d | 0 < penultimateWave η zc x}.Infinite := by
    have hinj : Function.Injective (fun y : Site d => (fun _ => (1 : ℤ)) + (k : ℤ) • y) := by
      intro y1 y2 h
      have h1 := congrFun h
      ext i
      have h2 := h1 i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h2
      have hk0 : (k : ℤ) ≠ 0 := by
        intro hkz
        have : k = 0 := by exact_mod_cast hkz
        omega
      have : (k : ℤ) * y1 i = (k : ℤ) * y2 i := by linarith
      exact mul_left_cancel₀ hk0 this
    have himg : (fun y : Site d => (fun _ => (1 : ℤ)) + (k : ℤ) • y) '' Cinf ⊆
        {x : Site d | 0 < penultimateWave η zc x} := by
      rintro x ⟨y, hy, rfl⟩
      obtain ⟨t, ht⟩ := hreach' y hy
      have hpos := ht _ (fun l => ⟨le_refl 1, hk1⟩)
      have hmono := wave_mono_time η hlow0 hd0 (waveThreshold η zc - 1) zc (le_max_right T t)
        ((fun _ => (1 : ℤ)) + (k : ℤ) • y)
      have hmax : 0 < wave η (waveThreshold η zc - 1) zc (max T t)
          ((fun _ => (1 : ℤ)) + (k : ℤ) • y) := by linarith
      show 0 < penultimateWave η zc ((fun _ => (1 : ℤ)) + (k : ℤ) • y)
      rw [hpen_eq, ← hT (max T t) (le_max_left T t)]
      exact hmax
    exact (hCinf.1.image hinj.injOn).mono himg
  exact hpeninf hpenfin


/-- **The side-length bound (Lemma 3.5's core).**  If the penultimate wave
centred at `zc` is positive on a run of `> (log n)^{5/2}` consecutive
*macroscopic* sites in direction `dir`, then `zc`'s last-wave index exceeds two.
The run is stated in cube-index coordinates: its points are
`fun j => if j = dir then 1 + k * v else 1 + k * (i j)` for `v ∈ [a, b]`, so the
line of `Q_k(i)` in direction `dir` based at the cube's lower corner is exactly
the sub-run `v ∈ [0, k-1]` shifted by `i`.  The run crosses more than
`(log n)^{5/2}` macroscopic cubes, so by the hole bound one of them lies in the
infinite cluster, and the propagation half then contradicts stabilizability. -/
theorem aux_penultimate_side_bound {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (k : ℕ) (hk : 1 ≤ k) (Cinf : Set (Site d)) (hCinf : IsInfiniteConnectedGoodSet η k Cinf)
    (zc : Site d)
    (hN : 2 ≤ waveThreshold η zc - 1)
    (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n zc)
    (n0 : ℕ)
    (hcomp : ∀ n, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ Cinf →
      (componentIn Cinfᶜ x).Finite ∧
        ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2))
    (n : ℕ) (hn : n0 ≤ n) (dir : Fin d) (a b : ℤ)
    (hab : Real.log n ^ ((5 : ℝ) / 2) ≤ ((b - a : ℤ) : ℝ))
    (hin : ∀ v : ℤ, a ≤ v → v ≤ b →
      (fun j => if j = dir then v else (zc j - 1) / (k : ℤ)) ∈ (cent d n : Set (Site d)))
    (w0 : Site d)
    (hw0 : ∀ j, j ≠ dir → w0 j = 1 + (k : ℤ) * ((zc j - 1) / (k : ℤ)))
    (lo hi : ℤ)
    (hcont : ∀ w ∈ line d k dir (fun _ => (1 : ℤ)), ∀ v : ℤ, a ≤ v → v ≤ b →
      lo ≤ w dir + (k : ℤ) * v ∧ w dir + (k : ℤ) * v ≤ hi)
    (hline : ∀ u : ℤ, lo ≤ u → u ≤ hi →
      0 < penultimateWave η zc (fun j => if j = dir then u else w0 j)) :
    False := by
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  obtain ⟨v, hva, hvb, hvCinf⟩ :=
    aux_penultimate_overlap_line_meets_cinf Cinf n0 hcomp n hn
      (fun j => (zc j - 1) / (k : ℤ)) dir a b hab hin
  -- the cube index `i` is the run point at `v`
  set i : Site d := fun j => if j = dir then v else (zc j - 1) / (k : ℤ) with hidef
  -- the line of `Q_k(i)` maps into the run
  have hline' : ∀ w ∈ line d k dir (fun _ => (1 : ℤ)),
      0 < penultimateWave η zc (w + (k : ℤ) • i) := by
    intro w hw
    have hother : ∀ l, l ≠ dir → (w + (k : ℤ) • i) l
        = 1 + (k : ℤ) * ((zc l - 1) / (k : ℤ)) := by
      intro l hl
      have hwl : w l = 1 := by
        have := hw.2 l hl
        simpa using this
      have hil : i l = (zc l - 1) / (k : ℤ) := by simp only [hidef, if_neg hl]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hwl, hil]
    have hdir : (w + (k : ℤ) • i) dir = w dir + (k : ℤ) * v := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hidef, if_true]
    have hge : 1 + (k : ℤ) * a ≤ w dir + (k : ℤ) * v := by
      have h1 : (k : ℤ) * a ≤ (k : ℤ) * v := mul_le_mul_of_nonneg_left hva (by linarith)
      linarith [hw.1.1]
    have hle : w dir + (k : ℤ) * v ≤ (k : ℤ) + (k : ℤ) * b := by
      have h1 : (k : ℤ) * v ≤ (k : ℤ) * b := mul_le_mul_of_nonneg_left hvb (by linarith)
      linarith [hw.1.2]
    have hfun : (fun j => if j = dir then w dir + (k : ℤ) * v else w0 j) =
        (w + (k : ℤ) • i) := by
      ext l
      by_cases hl : l = dir
      · subst hl; simp only [if_true, hdir]
      · simp only [if_neg hl, hother l hl, hw0 l hl]
    rw [← hfun]
    exact hline _ (hcont w hw v hva hvb).1 (hcont w hw v hva hvb).2
  exact aux_penultimate_overlap_propagate_line hd η hlow hhigh k hk Cinf hCinf zc i hvCinf
    dir (fun _ => (1 : ℤ)) (fun l => ⟨le_refl 1, hk1⟩) hline' hN hlast

/-- **The support of a wave at a fixed time is finite.**  The wave started at
`z` with mass `n` cannot be positive further than `t` steps away, by
`aux_finite_exploding_speed`. -/
theorem aux_pub_reach_support_finite {d : ℕ} (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (_hd0 : (0 : ℤ) < 2 * (d : ℤ))
    (n : ℕ) (z : Site d) (t : ℕ) :
    {x : Site d | 0 < wave η n z t x}.Finite := by
  have hfin : ({x : Site d | ∀ i, x i ∈ Set.Icc (-(t : ℤ) + z i) ((t : ℤ) + z i)}).Finite := by
    refine Set.Finite.pi' ?_
    intro i
    exact Set.finite_Icc _ _
  refine hfin.subset ?_
  intro x hx
  by_contra hcon
  have h1 : (t : ℤ) < mnorm (x - z) := by
    by_contra h2
    push Not at h2
    exact hcon (fun i => by
      have h3 : |(x - z) i| ≤ mnorm (x - z) := abs_coord_le_mnorm (x - z) i
      have h4 : (x - z) i ≤ (t : ℤ) := le_trans (le_abs_self _) (le_trans h3 h2)
      have h5 : -((t : ℤ)) ≤ (x - z) i := by
        have := neg_abs_le ((x - z) i)
        linarith
      simp only [Pi.sub_apply] at h4 h5
      constructor <;> linarith)
  have h2 := aux_finite_exploding_speed η hlow hhigh n z t x h1
  simp only [Set.mem_setOf_eq] at hx
  rw [h2] at hx
  exact lt_irrefl 0 hx

theorem wave_covers_of_line_one'' {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (k : ℕ) (hk : 1 ≤ k)
    (zc i : Site d) (hgoodi : GoodAt η k i) (dir : Fin d) (z : Site d)
    (hz : z ∈ cube d k) (t : ℕ)
    (hline : ∀ w ∈ line d k dir z, 0 < wave η 1 zc t (w + (k : ℤ) • i))
    (hcov_zc : ∃ T0 : ℕ, ∀ t : ℕ, T0 ≤ t → ∀ x ∈ cube d k,
      0 < wave η 1 zc t (x + (k : ℤ) • macroIdx k zc)) :
    ∃ t' : ℕ, t ≤ t' ∧ ∀ x ∈ cube d k, 0 < wave η 1 zc t' (x + (k : ℤ) • i) := by
  by_cases hi : i = macroIdx k zc
  · obtain ⟨T0, hT0⟩ := hcov_zc
    refine ⟨max T0 t, le_max_right _ _, fun x hx => ?_⟩
    rw [hi]
    exact hT0 (max T0 t) (le_max_left _ _) x hx
  · exact wave_covers_of_line_one' hd η hlow hhigh k zc i hgoodi dir z (Or.inl hz) t hline
      (fun y hy hcon => hi (macroIdx_eq_of_mem_image k hk zc i ⟨y, hy, hcon⟩))

/-- **The `N = 1` propagation half.**  The analogue of
`aux_penultimate_overlap_propagate_line` for the `1`-wave.  If the `1`-wave from
`zc` is positive on a line of a good cube `Q_k(i)` with `i ∈ Cinf`, and `zc` is
not in the image of `Q_k(i)`, then the `1`-wave reaches the whole cluster,
contradicting its stabilizability. -/
theorem aux_penultimate_overlap_propagate_line_one {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (k : ℕ) (hk : 1 ≤ k) (Cinf : Set (Site d)) (hCinf : IsInfiniteConnectedGoodSet η k Cinf)
    (zc : Site d) (i : Site d) (hiCinf : i ∈ Cinf)
    (dir : Fin d) (z : Site d) (hz : z ∈ cube d k)
    (hline : ∀ w ∈ line d k dir z,
      0 < penultimateWave η zc (w + (k : ℤ) • i))
    (hM2 : waveThreshold η zc = 2)
    (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n zc)
    (hcov_zc : ∃ T0 : ℕ, ∀ t : ℕ, T0 ≤ t → ∀ x ∈ cube d k,
      0 < wave η 1 zc t (x + (k : ℤ) • macroIdx k zc)) : False := by
  have hlow0 : ∀ x, 0 ≤ η x := fun x => by linarith [hlow x]
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hzpos : 0 < penultimateWave η zc (z + (k : ℤ) • i) :=
    hline _ ⟨hz dir, fun l hl => rfl⟩
  obtain ⟨h2, hlast'⟩ := aux_penultimate_hlast η hlow0 hhigh zc _ hzpos
  have h1 : waveThreshold η zc ≠ 1 := by omega
  have hstab : WaveStabilizable η 1 zc := by
    have h := penultimate_stabilizable η zc hlast' h1
    rwa [hM2] at h
  obtain ⟨T, hT⟩ := hstab
  have hstab' : WaveStabilizable η 1 zc := ⟨T, hT⟩
  have hstab0 : WaveStabilizable η 1 zc := hstab' 
  have hpenT : ∀ x : Site d, penultimateWave η zc x = wave η 1 zc T x := by
    intro x
    simp only [penultimateWave, if_neg h1, waveTerminal]
    rw [show waveThreshold η zc - 1 = 1 by omega]
    exact (congrFun (waveTerminal_spec η 1 zc hstab' T (Nat.sInf_le hT)) x).symm
  have hline'' : ∀ w ∈ line d k dir z,
      0 < wave η 1 zc T (w + (k : ℤ) • i) := by
    intro w hw
    rw [← hpenT]
    exact hline w hw
  -- the line of `Q_k(i)` is crossed by the `1`-wave
  obtain ⟨T0, hT0⟩ := wave_covers_of_line_one'' hd η hlow0 hhigh k hk zc i
    (hCinf.2.1 hiCinf) dir z hz T hline'' hcov_zc
  have hreach : ∀ y ∈ Cinf, ∃ t, ∀ x ∈ cube d k,
      0 < wave η 1 zc t (x + (k : ℤ) • y) := by
    intro y hy
    have hstep : ∀ (a b : Site d), b ∈ Cinf → (b = macroIdx k zc ∨ b ≠ macroIdx k zc) →
        GoodAt η k b → (lattice d).Adj a b →
        ∀ s : ℕ, (∀ x ∈ cube d k, 0 < wave η 1 zc s (x + (k : ℤ) • a)) →
        ∃ s' : ℕ, s ≤ s' ∧ ∀ x ∈ cube d k, 0 < wave η 1 zc s' (x + (k : ℤ) • b) := by
      intro a b hbC hbm hgood hadj s hs
      by_cases hb : b = macroIdx k zc
      · -- `b` is `zc`'s own cube: the wave is positive at `zc` itself, and
        -- `zc` lies in `Q_k(b)`'s image, so the cube is covered
        obtain ⟨T1, hT1⟩ := hcov_zc
        refine ⟨max (max s T0) T1, le_trans (le_max_left s T0) (le_max_left _ _), fun x hx => ?_⟩
        have h2' : 0 < wave η 1 zc (max (max s T0) T1) (x + (k : ℤ) • b) := by
          -- `zc` lies in `Q_k(b)`'s image, and the wave is positive at `zc`
          -- `zc` lies in `Q_k(b)`'s image, and the wave is positive at `zc`
          obtain ⟨y0, hy0, hy0eq⟩ : ∃ y0 ∈ cube d k, y0 + (k : ℤ) • b = zc := by
            refine ⟨fun j => zc j - (k : ℤ) * b j, ?_, ?_⟩
            · intro j
              have h1' : zc j = (zc j - 1) / (k : ℤ) * (k : ℤ) + (zc j - 1) % (k : ℤ) + 1 := by
                have := Int.mul_ediv_add_emod (zc j - 1) (k : ℤ)
                linarith
              have h2' : 0 ≤ (zc j - 1) % (k : ℤ) := Int.emod_nonneg _ (by omega)
              have h3' : (zc j - 1) % (k : ℤ) < (k : ℤ) := Int.emod_lt_of_pos _ (by omega)
              have h4' : b j = (zc j - 1) / (k : ℤ) := by
                rw [hb]
                rfl
              simp only [h4']
              constructor
              · linarith [h1', h2']
              · linarith [h1', h3']
            · ext j
              simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              ring
          -- the wave is positive at `zc`, and `zc` lies in `Q_k(b)`'s image,
          -- so the cube is covered once the wave reaches `zc`
          have hzc : 0 < wave η 1 zc (max s T0) zc := by
            have h1' : 0 < wave η 1 zc T zc := by
              rw [← hpenT zc]
              rw [penultimateWave_at_centre η zc (by omega)]
              omega
            have h2'' : 0 < wave η 1 zc (max T T0) zc := by
              have := wave_mono_time η hlow0 hd0 1 zc (le_max_left T T0) zc
              linarith
            have h3'' : max T T0 ≤ max s T0 := by omega
            have := wave_mono_time η hlow0 hd0 1 zc h3'' zc
            linarith
          -- the cube `Q_k(b)` is covered by the wave at `zc`: the wave is
          have hcov : ∀ x ∈ cube d k, 0 < wave η 1 zc (max (max s T0) T1) (x + (k : ℤ) • b) := by
            intro x hx
            rw [hb]
            exact hT1 (max (max s T0) T1) (le_max_right _ _) x hx
          exact hcov x hx
        exact h2'
      · obtain ⟨dir', hdir'⟩ := hadj
        have hfar_b : ∀ y ∈ cube d k, y + (k : ℤ) • b ≠ zc := by
          intro y hy hcon
          exact hb (macroIdx_eq_of_mem_image k hk zc b ⟨y, hy, hcon⟩)
        -- a direction different from the adjacency direction `dir'`
        have hne' : ∃ dir'' : Fin d, dir'' ≠ dir' := by
          by_cases h0 : dir' = (⟨0, by omega⟩ : Fin d)
          · exact ⟨⟨1, by omega⟩, by rw [h0]; intro hc; simp at hc⟩
          · exact ⟨⟨0, by omega⟩, fun hc => h0 hc.symm⟩
        obtain ⟨dir'', hdir''⟩ := hne'
        exact finite_exploding_step_one hd η hlow0 hhigh k hk zc a b hgood dir' hdir'
          dir'' hdir'' s hs hfar_b
    obtain ⟨t', ht'⟩ := aux_finite_exploding_propagate_walk_seed η hlow0 hhigh 1 k zc
      Cinf (fun x hx => hCinf.2.1 hx) (macroIdx k zc) hstep i y
      (hCinf.2.2 i hiCinf y hy) T0 hT0.2
    exact ⟨t', ht'⟩
  have hinf : {x : Site d | ∃ t, 0 < wave η 1 zc t x}.Infinite := by
    have himg : (fun y : Site d => (fun _ => (1 : ℤ)) + (k : ℤ) • y) '' Cinf ⊆
        {x : Site d | ∃ t, 0 < wave η 1 zc t x} := by
      rintro x ⟨y, hy, rfl⟩
      obtain ⟨t, ht⟩ := hreach y hy
      exact ⟨t, ht _ (fun l => ⟨le_refl 1, hk1⟩)⟩
    have hinj : Function.Injective (fun y : Site d => (fun _ => (1 : ℤ)) + (k : ℤ) • y) := by
      intro y1 y2 h
      have h1 := congrFun h
      have h2 : ∀ l, (k : ℤ) * y1 l = (k : ℤ) * y2 l := by
        intro l
        have := h1 l
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
        linarith
      funext l
      have := h2 l
      exact mul_left_cancel₀ (by omega : (k : ℤ) ≠ 0) this
    exact (hCinf.1.image hinj.injOn).mono himg
  have hfin : {x : Site d | ∃ t, 0 < wave η 1 zc t x}.Finite := by
    have hsub : {x : Site d | ∃ t, 0 < wave η 1 zc t x} ⊆
        {x : Site d | 0 < wave η 1 zc T x} := by
      rintro x ⟨t, ht⟩
      rcases Nat.le_total t T with h | h
      · have h1 := wave_mono_time η hlow0 hd0 1 zc h x
        exact lt_of_lt_of_le ht h1
      · have h1 := hT t h
        rw [h1] at ht
        exact ht
    exact (aux_pub_reach_support_finite η hlow0 hhigh hd0 1 zc T).subset hsub
  exact hinf hfin

/-- **The `M̂ = 2` case of the side-length bound.**  When the last-wave index
at `zc` is two, the penultimate wave is the `1`-wave, and the same argument as
`aux_penultimate_side_bound` applies with `wave_covers_of_line_one'` in place of
`wave_covers_of_line`.  The one extra input is that the run must extend beyond
`zc`'s own cube: the cube's image occupies the run's `dir`-coordinates
`[1 + k*v0, k + k*v0]` with `v0 := (zc dir - 1)/k`, so the pigeonhole is applied
with that interval excluded, and the good cube it returns is a different cube,
for which `wave_covers_of_line_one'`'s `hfar` holds by
`macroIdx_eq_of_mem_image`. -/
theorem aux_penultimate_side_bound_one {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (k : ℕ) (hk : 1 ≤ k) (Cinf : Set (Site d)) (hCinf : IsInfiniteConnectedGoodSet η k Cinf)
    (zc : Site d)
    (hM2 : waveThreshold η zc = 2)
    (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n zc)
    (n0 : ℕ)
    (hcomp : ∀ n, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ Cinf →
      (componentIn Cinfᶜ x).Finite ∧
        ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2))
    (n : ℕ) (hn : n0 ≤ n) (dir : Fin d) (a b : ℤ)
    (hin : ∀ v : ℤ, a ≤ v → v ≤ b →
      (fun j => if j = dir then v else (zc j - 1) / (k : ℤ)) ∈ (cent d n : Set (Site d)))
    (w0 : Site d)
    (hw0 : ∀ j, j ≠ dir → w0 j = 1 + (k : ℤ) * ((zc j - 1) / (k : ℤ)))
    (lo hi : ℤ)
    (hcont : ∀ w ∈ line d k dir (fun _ => (1 : ℤ)), ∀ v : ℤ, a ≤ v → v ≤ b →
      lo ≤ w dir + (k : ℤ) * v ∧ w dir + (k : ℤ) * v ≤ hi)
    (hline : ∀ u : ℤ, lo ≤ u → u ≤ hi →
      0 < penultimateWave η zc (fun j => if j = dir then u else w0 j))
    (hlo : a ≤ (zc dir - 1) / (k : ℤ))
    (hhi : (zc dir - 1) / (k : ℤ) ≤ b)
    (hlen : Real.log n ^ ((5 : ℝ) / 2) ≤
      (((zc dir - 1) / (k : ℤ)) - 1 - a : ℤ) ∨
      Real.log n ^ ((5 : ℝ) / 2) ≤
      ((b - ((zc dir - 1) / (k : ℤ) + 1) : ℤ) : ℝ))
    (hcov_zc : ∃ T0 : ℕ, ∀ t : ℕ, T0 ≤ t → ∀ x ∈ cube d k,
      0 < wave η 1 zc t (x + (k : ℤ) • macroIdx k zc)) :
    False := by
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  set v0 : ℤ := (zc dir - 1) / (k : ℤ) with hv0def
  -- the excluded interval is the cube index, intersected with the run
  obtain ⟨v, hva, hvb, hvCinf, hvout⟩ :=
    aux_penultimate_overlap_line_meets_cinf_outside Cinf n0 hcomp n hn
      (fun j => (zc j - 1) / (k : ℤ)) dir a b hin
      ((zc dir - 1) / (k : ℤ)) ((zc dir - 1) / (k : ℤ))
      hlo hhi le_rfl hlen
  set i : Site d := fun j => if j = dir then v else (zc j - 1) / (k : ℤ) with hidef
  have hi_ne : i ≠ macroIdx k zc := by
    intro hcon
    have h1 : i dir = macroIdx k zc dir := by rw [hcon]
    have h2 : macroIdx k zc dir = v0 := by
      simp only [macroIdx, hv0def]
    have h3 : i dir = v := by simp only [hidef, if_true]
    rw [h3, h2] at h1
    rcases hvout with hlt | hgt
    · omega
    · omega
  have hline' : ∀ w ∈ line d k dir (fun _ => (1 : ℤ)),
      0 < penultimateWave η zc (w + (k : ℤ) • i) := by
    intro w hw
    have hother : ∀ l, l ≠ dir → (w + (k : ℤ) • i) l
        = 1 + (k : ℤ) * ((zc l - 1) / (k : ℤ)) := by
      intro l hl
      have hwl : w l = 1 := by
        have := hw.2 l hl
        simpa using this
      have hil : i l = (zc l - 1) / (k : ℤ) := by simp only [hidef, if_neg hl]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hwl, hil]
    have hdir : (w + (k : ℤ) • i) dir = w dir + (k : ℤ) * v := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hidef, if_true]
    have hge : 1 + (k : ℤ) * a ≤ w dir + (k : ℤ) * v := by
      have h1 : (k : ℤ) * a ≤ (k : ℤ) * v := mul_le_mul_of_nonneg_left hva (by linarith)
      linarith [hw.1.1]
    have hle : w dir + (k : ℤ) * v ≤ (k : ℤ) + (k : ℤ) * b := by
      have h1 : (k : ℤ) * v ≤ (k : ℤ) * b := mul_le_mul_of_nonneg_left hvb (by linarith)
      linarith [hw.1.2]
    have hfun : (fun j => if j = dir then w dir + (k : ℤ) * v else w0 j) =
        (w + (k : ℤ) • i) := by
      ext l
      by_cases hl : l = dir
      · subst hl; simp only [if_true, hdir]
      · simp only [if_neg hl, hother l hl, hw0 l hl]
    rw [← hfun]
    exact hline _ (hcont w hw v hva hvb).1 (hcont w hw v hva hvb).2
  exact aux_penultimate_overlap_propagate_line_one hd η hlow hhigh k hk Cinf hCinf zc i
    hvCinf dir (fun _ => (1 : ℤ)) (fun l => ⟨le_refl 1, hk1⟩) hline' hM2 hlast hcov_zc


/-- **Segment-to-line.**  A segment of length `(log n)^(5/2) * k + 4k` in a
coordinate direction, inside `cent d n`, contains a full line of a cube of
`Cinf`.  The line is read at the cube's own base coordinates. -/
theorem aux_segment_meets_cinf_line {d : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (Cinf : Set (Site d)) (n0 : ℕ)
    (hcomp : ∀ n, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ Cinf →
      (componentIn Cinfᶜ x).Finite ∧
        ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2))
    (n : ℕ) (hn : n0 ≤ n) (l : Fin d) (c : Site d) (a b : ℤ)
    (hlog : 0 ≤ Real.log n ^ ((5 : ℝ) / 2))
    (hab : ((2 * Real.log n ^ ((5 : ℝ) / 2) + 6) * (k : ℝ)) ≤ ((b - a : ℤ) : ℝ))
    (hin' : ∀ v : ℤ, (a - 1) / (k : ℤ) + 1 ≤ v → v ≤ (b - (k : ℤ)) / (k : ℤ) →
      (fun j => if j = l then v else (c j - 1) / (k : ℤ)) ∈ (cent d n : Set (Site d)))
    (j0 : ℤ)
    (hj0lo : (a - 1) / (k : ℤ) + 1 ≤ j0) (hj0hi : j0 ≤ (b - (k : ℤ)) / (k : ℤ)) :
    ∃ i ∈ Cinf, i l ≠ j0 ∧
      ∀ w ∈ line d k l (fun j => if j = l then 1 else 1 + (c j - 1) % (k : ℤ)),
      a ≤ (w + (k : ℤ) • i) l ∧ (w + (k : ℤ) • i) l ≤ b ∧
        ∀ j, j ≠ l → (w + (k : ℤ) • i) j = c j := by
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hk0 : (0 : ℤ) < (k : ℤ) := by linarith
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  set m : ℤ := ((b - (k : ℤ)) / (k : ℤ)) - ((a - 1) / (k : ℤ) + 1) with hm
  have hlen : Real.log n ^ ((5 : ℝ) / 2) ≤ ((m : ℤ) : ℝ) := by
    have h1 : (k : ℤ) * ((b - (k : ℤ)) / (k : ℤ)) =
        (b - (k : ℤ)) - ((b - (k : ℤ)) % (k : ℤ)) := by
      have := Int.ediv_mul_add_emod (b - (k : ℤ)) (k : ℤ); linarith
    have h2 : (k : ℤ) * ((a - 1) / (k : ℤ)) = (a - 1) - ((a - 1) % (k : ℤ)) := by
      have := Int.ediv_mul_add_emod (a - 1) (k : ℤ); linarith
    have h4 : (b - (k : ℤ)) % (k : ℤ) ≤ (k : ℤ) - 1 := by
      have := Int.emod_lt_of_pos (b - (k : ℤ)) hk0; omega
    have h6 : (a - 1) % (k : ℤ) ≤ (k : ℤ) - 1 := by
      have := Int.emod_lt_of_pos (a - 1) hk0; omega
    have h7 : (k : ℤ) * m ≥ (b - a) - 3 * (k : ℤ) := by
      rw [hm]
      have h7a : (k : ℤ) * (((b - (k : ℤ)) / (k : ℤ)) - ((a - 1) / (k : ℤ) + 1)) =
          (k : ℤ) * ((b - (k : ℤ)) / (k : ℤ)) - (k : ℤ) * ((a - 1) / (k : ℤ)) - (k : ℤ) := by
        ring
      rw [h7a, h1, h2]
      have h3' : 0 ≤ (b - (k : ℤ)) % (k : ℤ) := Int.emod_nonneg _ (by linarith)
      have h5' : 0 ≤ (a - 1) % (k : ℤ) := Int.emod_nonneg _ (by linarith)
      omega
    have h8 : (((b - a) - 3 * (k : ℤ) : ℤ) : ℝ) ≤ ((k : ℤ) : ℝ) * ((m : ℤ) : ℝ) := by
      exact_mod_cast h7
    have h9 : (((b - a) - 3 * (k : ℤ) : ℤ) : ℝ) = ((b - a : ℤ) : ℝ) - 3 * (k : ℝ) := by
      push_cast; ring
    rw [h9] at h8
    have h10 : (2 * Real.log n ^ ((5 : ℝ) / 2) + 3) * (k : ℝ) ≤ ((k : ℤ) : ℝ) * ((m : ℤ) : ℝ) := by
      have hkR' : (0 : ℝ) < ((k : ℤ) : ℝ) := by exact_mod_cast hk
      have h8' : ((b - a : ℤ) : ℝ) - 3 * (k : ℝ) ≤ ((k : ℤ) : ℝ) * ((m : ℤ) : ℝ) := h8
      nlinarith [hab, h8', hkR']
    have h10' : ((k : ℤ) : ℝ) * (2 * Real.log n ^ ((5 : ℝ) / 2) + 3) ≤
        ((k : ℤ) : ℝ) * ((m : ℤ) : ℝ) := by
      rw [mul_comm ((k : ℤ) : ℝ) (2 * Real.log n ^ ((5 : ℝ) / 2) + 3)]
      exact h10
    have hkR' : (0 : ℝ) < ((k : ℤ) : ℝ) := by exact_mod_cast hk
    have h11 : 2 * Real.log n ^ ((5 : ℝ) / 2) + 3 ≤ ((m : ℤ) : ℝ) :=
      le_of_mul_le_mul_left h10' hkR'
    linarith
  have hm_ge : 2 * Real.log n ^ ((5 : ℝ) / 2) + 3 ≤ ((m : ℤ) : ℝ) := by
    have h1 : (k : ℤ) * ((b - (k : ℤ)) / (k : ℤ)) =
        (b - (k : ℤ)) - ((b - (k : ℤ)) % (k : ℤ)) := by
      have := Int.ediv_mul_add_emod (b - (k : ℤ)) (k : ℤ); linarith
    have h2 : (k : ℤ) * ((a - 1) / (k : ℤ)) = (a - 1) - ((a - 1) % (k : ℤ)) := by
      have := Int.ediv_mul_add_emod (a - 1) (k : ℤ); linarith
    have h4 : (b - (k : ℤ)) % (k : ℤ) ≤ (k : ℤ) - 1 := by
      have := Int.emod_lt_of_pos (b - (k : ℤ)) hk0; omega
    have h6 : (a - 1) % (k : ℤ) ≤ (k : ℤ) - 1 := by
      have := Int.emod_lt_of_pos (a - 1) hk0; omega
    have h7 : (k : ℤ) * m ≥ (b - a) - 3 * (k : ℤ) := by
      rw [hm]
      have h7a : (k : ℤ) * (((b - (k : ℤ)) / (k : ℤ)) - ((a - 1) / (k : ℤ) + 1)) =
          (k : ℤ) * ((b - (k : ℤ)) / (k : ℤ)) - (k : ℤ) * ((a - 1) / (k : ℤ)) - (k : ℤ) := by
        ring
      rw [h7a, h1, h2]
      have h3' : 0 ≤ (b - (k : ℤ)) % (k : ℤ) := Int.emod_nonneg _ (by linarith)
      have h5' : 0 ≤ (a - 1) % (k : ℤ) := Int.emod_nonneg _ (by linarith)
      omega
    have h8 : (((b - a) - 3 * (k : ℤ) : ℤ) : ℝ) ≤ ((k : ℤ) : ℝ) * ((m : ℤ) : ℝ) := by
      exact_mod_cast h7
    have h9 : (((b - a) - 3 * (k : ℤ) : ℤ) : ℝ) = ((b - a : ℤ) : ℝ) - 3 * (k : ℝ) := by
      push_cast; ring
    rw [h9] at h8
    have h10 : (2 * Real.log n ^ ((5 : ℝ) / 2) + 3) * (k : ℝ) ≤ ((k : ℤ) : ℝ) * ((m : ℤ) : ℝ) := by
      have hkR' : (0 : ℝ) < ((k : ℤ) : ℝ) := by exact_mod_cast hk
      nlinarith [hab, h8, hkR']
    have h10' : ((k : ℤ) : ℝ) * (2 * Real.log n ^ ((5 : ℝ) / 2) + 3) ≤
        ((k : ℤ) : ℝ) * ((m : ℤ) : ℝ) := by
      rw [mul_comm ((k : ℤ) : ℝ) (2 * Real.log n ^ ((5 : ℝ) / 2) + 3)]
      exact h10
    exact le_of_mul_le_mul_left h10' hkR
  have hlen' : Real.log n ^ ((5 : ℝ) / 2) ≤
      ((j0 - 1 - ((a - 1) / (k : ℤ) + 1) : ℤ) : ℝ) ∨
      Real.log n ^ ((5 : ℝ) / 2) ≤
      (((b - (k : ℤ)) / (k : ℤ) - (j0 + 1) : ℤ) : ℝ) := by
    have hsum : (((j0 - 1 - ((a - 1) / (k : ℤ) + 1) : ℤ) : ℝ)) +
        ((((b - (k : ℤ)) / (k : ℤ) - (j0 + 1) : ℤ) : ℝ)) =
        ((m : ℤ) : ℝ) - 2 := by
      rw [hm]; push_cast; ring
    have hmax : Real.log n ^ ((5 : ℝ) / 2) ≤
        max (((j0 - 1 - ((a - 1) / (k : ℤ) + 1) : ℤ) : ℝ))
          ((((b - (k : ℤ)) / (k : ℤ) - (j0 + 1) : ℤ) : ℝ)) := by
      by_contra hcon
      rw [not_le] at hcon
      have h1 : (((j0 - 1 - ((a - 1) / (k : ℤ) + 1) : ℤ) : ℝ)) +
          ((((b - (k : ℤ)) / (k : ℤ) - (j0 + 1) : ℤ) : ℝ)) <
          2 * Real.log n ^ ((5 : ℝ) / 2) := by
        have h2 : (((j0 - 1 - ((a - 1) / (k : ℤ) + 1) : ℤ) : ℝ)) ≤
            max (((j0 - 1 - ((a - 1) / (k : ℤ) + 1) : ℤ) : ℝ))
              ((((b - (k : ℤ)) / (k : ℤ) - (j0 + 1) : ℤ) : ℝ)) := le_max_left _ _
        have h3 : ((((b - (k : ℤ)) / (k : ℤ) - (j0 + 1) : ℤ) : ℝ)) ≤
            max (((j0 - 1 - ((a - 1) / (k : ℤ) + 1) : ℤ) : ℝ))
              ((((b - (k : ℤ)) / (k : ℤ) - (j0 + 1) : ℤ) : ℝ)) := le_max_right _ _
        linarith [hsum, hcon, h2, h3]
      linarith [hsum, h1, hlen, hm_ge]
    rcases le_total (((j0 - 1 - ((a - 1) / (k : ℤ) + 1) : ℤ) : ℝ))
        ((((b - (k : ℤ)) / (k : ℤ) - (j0 + 1) : ℤ) : ℝ)) with h | h
    · right
      have h' : max (((j0 - 1 - ((a - 1) / (k : ℤ) + 1) : ℤ) : ℝ))
          ((((b - (k : ℤ)) / (k : ℤ) - (j0 + 1) : ℤ) : ℝ)) =
          ((((b - (k : ℤ)) / (k : ℤ) - (j0 + 1) : ℤ) : ℝ)) := max_eq_right h
      rw [h'] at hmax
      exact hmax
    · left
      have h' : max (((j0 - 1 - ((a - 1) / (k : ℤ) + 1) : ℤ) : ℝ))
          ((((b - (k : ℤ)) / (k : ℤ) - (j0 + 1) : ℤ) : ℝ)) =
          (((j0 - 1 - ((a - 1) / (k : ℤ) + 1) : ℤ) : ℝ)) := max_eq_left h
      rw [h'] at hmax
      exact hmax
  obtain ⟨v, hv0, hv1, hvC, hvout⟩ := aux_penultimate_overlap_line_meets_cinf_outside Cinf n0 hcomp
    n hn (fun j => (c j - 1) / (k : ℤ)) l ((a - 1) / (k : ℤ) + 1) ((b - (k : ℤ)) / (k : ℤ))
    hin' j0 j0 hj0lo hj0hi le_rfl hlen'
  refine ⟨fun j => if j = l then v else (c j - 1) / (k : ℤ), hvC, ?_, ?_⟩
  · intro hcon
    have h1 : (fun j => if j = l then v else (c j - 1) / (k : ℤ)) l = v := if_pos rfl
    rw [h1] at hcon
    rcases hvout with hlt | hgt <;> omega
  · intro w hw
    have hwl : (1 : ℤ) ≤ w l := hw.1.1
    have hwh : w l ≤ (k : ℤ) := hw.1.2
    have hwj : ∀ j, j ≠ l → w j = 1 + (c j - 1) % (k : ℤ) := by
      intro j hj
      have := hw.2 j hj
      simpa only [if_neg hj] using this
    have h1 : (k : ℤ) * ((a - 1) / (k : ℤ) + 1) ≥ a := by
      have := Int.ediv_mul_add_emod (a - 1) (k : ℤ)
      have h2 : 0 ≤ (a - 1) % (k : ℤ) := Int.emod_nonneg _ (by linarith)
      have h3 : (a - 1) % (k : ℤ) < (k : ℤ) := Int.emod_lt_of_pos _ hk0
      nlinarith [this, h2, h3]
    have h2 : (k : ℤ) * ((b - (k : ℤ)) / (k : ℤ)) ≤ b - (k : ℤ) := by
      have := Int.ediv_mul_add_emod (b - (k : ℤ)) (k : ℤ)
      have h3 : 0 ≤ (b - (k : ℤ)) % (k : ℤ) := Int.emod_nonneg _ (by linarith)
      linarith
    have h3 : (k : ℤ) * ((a - 1) / (k : ℤ) + 1) ≤ (k : ℤ) * v :=
      mul_le_mul_of_nonneg_left hv0 (by linarith)
    have h4 : (k : ℤ) * v ≤ (k : ℤ) * ((b - (k : ℤ)) / (k : ℤ)) :=
      mul_le_mul_of_nonneg_left hv1 (by linarith)
    refine ⟨?_, ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, if_true]
      linarith
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, if_true]
      linarith
    · intro j hj
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, if_neg hj]
      rw [hwj j hj]
      have h6 : (k : ℤ) * ((c j - 1) / (k : ℤ)) = c j - 1 - ((c j - 1) % (k : ℤ)) := by
        have := Int.ediv_mul_add_emod (c j - 1) (k : ℤ); linarith
      linarith


/-- **The side bound, in the form the frozen proof needs.**  If the penultimate
wave from `zc` is positive on a long coordinate segment whose cube-base points
lie in `cent d n`, then the `(M̂-1)`-wave is not stabilizable. -/
theorem aux_segment_meets_cinf_line' {d : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (Cinf : Set (Site d)) (n0 : ℕ)
    (hcomp : ∀ n, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ Cinf →
      (componentIn Cinfᶜ x).Finite ∧
        ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2))
    (n : ℕ) (hn : n0 ≤ n) (l : Fin d) (c : Site d) (a b : ℤ)
    (hlog : 0 ≤ Real.log n ^ ((5 : ℝ) / 2))
    (hab : ((2 * Real.log n ^ ((5 : ℝ) / 2) + 6) * (k : ℝ)) ≤ ((b - a : ℤ) : ℝ))
    (hin' : ∀ v : ℤ, (a - 1) / (k : ℤ) + 1 ≤ v → v ≤ (b - (k : ℤ)) / (k : ℤ) →
      (fun j => if j = l then v else (c j - 1) / (k : ℤ)) ∈ (cent d n : Set (Site d)))
    :
    ∃ i ∈ Cinf,
      ∀ w ∈ line d k l (fun j => if j = l then 1 else 1 + (c j - 1) % (k : ℤ)),
      a ≤ (w + (k : ℤ) • i) l ∧ (w + (k : ℤ) • i) l ≤ b ∧
        ∀ j, j ≠ l → (w + (k : ℤ) • i) j = c j := by
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hk0 : (0 : ℤ) < (k : ℤ) := by linarith
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  set m : ℤ := ((b - (k : ℤ)) / (k : ℤ)) - ((a - 1) / (k : ℤ) + 1) with hm
  have hlen : Real.log n ^ ((5 : ℝ) / 2) ≤ ((m : ℤ) : ℝ) := by
    have h1 : (k : ℤ) * ((b - (k : ℤ)) / (k : ℤ)) =
        (b - (k : ℤ)) - ((b - (k : ℤ)) % (k : ℤ)) := by
      have := Int.ediv_mul_add_emod (b - (k : ℤ)) (k : ℤ); linarith
    have h2 : (k : ℤ) * ((a - 1) / (k : ℤ)) = (a - 1) - ((a - 1) % (k : ℤ)) := by
      have := Int.ediv_mul_add_emod (a - 1) (k : ℤ); linarith
    have h4 : (b - (k : ℤ)) % (k : ℤ) ≤ (k : ℤ) - 1 := by
      have := Int.emod_lt_of_pos (b - (k : ℤ)) hk0; omega
    have h6 : (a - 1) % (k : ℤ) ≤ (k : ℤ) - 1 := by
      have := Int.emod_lt_of_pos (a - 1) hk0; omega
    have h7 : (k : ℤ) * m ≥ (b - a) - 3 * (k : ℤ) := by
      rw [hm]
      have h7a : (k : ℤ) * (((b - (k : ℤ)) / (k : ℤ)) - ((a - 1) / (k : ℤ) + 1)) =
          (k : ℤ) * ((b - (k : ℤ)) / (k : ℤ)) - (k : ℤ) * ((a - 1) / (k : ℤ)) - (k : ℤ) := by
        ring
      rw [h7a, h1, h2]
      have h3' : 0 ≤ (b - (k : ℤ)) % (k : ℤ) := Int.emod_nonneg _ (by linarith)
      have h5' : 0 ≤ (a - 1) % (k : ℤ) := Int.emod_nonneg _ (by linarith)
      omega
    have h8 : (((b - a) - 3 * (k : ℤ) : ℤ) : ℝ) ≤ ((k : ℤ) : ℝ) * ((m : ℤ) : ℝ) := by
      exact_mod_cast h7
    have h9 : (((b - a) - 3 * (k : ℤ) : ℤ) : ℝ) = ((b - a : ℤ) : ℝ) - 3 * (k : ℝ) := by
      push_cast; ring
    rw [h9] at h8
    have h10 : (2 * Real.log n ^ ((5 : ℝ) / 2) + 3) * (k : ℝ) ≤ ((k : ℤ) : ℝ) * ((m : ℤ) : ℝ) := by
      have hkR' : (0 : ℝ) < ((k : ℤ) : ℝ) := by exact_mod_cast hk
      have h8' : ((b - a : ℤ) : ℝ) - 3 * (k : ℝ) ≤ ((k : ℤ) : ℝ) * ((m : ℤ) : ℝ) := h8
      nlinarith [hab, h8', hkR']
    have h10' : ((k : ℤ) : ℝ) * (2 * Real.log n ^ ((5 : ℝ) / 2) + 3) ≤
        ((k : ℤ) : ℝ) * ((m : ℤ) : ℝ) := by
      rw [mul_comm ((k : ℤ) : ℝ) (2 * Real.log n ^ ((5 : ℝ) / 2) + 3)]
      exact h10
    have hkR' : (0 : ℝ) < ((k : ℤ) : ℝ) := by exact_mod_cast hk
    have h11 : 2 * Real.log n ^ ((5 : ℝ) / 2) + 3 ≤ ((m : ℤ) : ℝ) :=
      le_of_mul_le_mul_left h10' hkR'
    linarith
  have hm_ge : 2 * Real.log n ^ ((5 : ℝ) / 2) + 3 ≤ ((m : ℤ) : ℝ) := by
    have h1 : (k : ℤ) * ((b - (k : ℤ)) / (k : ℤ)) =
        (b - (k : ℤ)) - ((b - (k : ℤ)) % (k : ℤ)) := by
      have := Int.ediv_mul_add_emod (b - (k : ℤ)) (k : ℤ); linarith
    have h2 : (k : ℤ) * ((a - 1) / (k : ℤ)) = (a - 1) - ((a - 1) % (k : ℤ)) := by
      have := Int.ediv_mul_add_emod (a - 1) (k : ℤ); linarith
    have h4 : (b - (k : ℤ)) % (k : ℤ) ≤ (k : ℤ) - 1 := by
      have := Int.emod_lt_of_pos (b - (k : ℤ)) hk0; omega
    have h6 : (a - 1) % (k : ℤ) ≤ (k : ℤ) - 1 := by
      have := Int.emod_lt_of_pos (a - 1) hk0; omega
    have h7 : (k : ℤ) * m ≥ (b - a) - 3 * (k : ℤ) := by
      rw [hm]
      have h7a : (k : ℤ) * (((b - (k : ℤ)) / (k : ℤ)) - ((a - 1) / (k : ℤ) + 1)) =
          (k : ℤ) * ((b - (k : ℤ)) / (k : ℤ)) - (k : ℤ) * ((a - 1) / (k : ℤ)) - (k : ℤ) := by
        ring
      rw [h7a, h1, h2]
      have h3' : 0 ≤ (b - (k : ℤ)) % (k : ℤ) := Int.emod_nonneg _ (by linarith)
      have h5' : 0 ≤ (a - 1) % (k : ℤ) := Int.emod_nonneg _ (by linarith)
      omega
    have h8 : (((b - a) - 3 * (k : ℤ) : ℤ) : ℝ) ≤ ((k : ℤ) : ℝ) * ((m : ℤ) : ℝ) := by
      exact_mod_cast h7
    have h9 : (((b - a) - 3 * (k : ℤ) : ℤ) : ℝ) = ((b - a : ℤ) : ℝ) - 3 * (k : ℝ) := by
      push_cast; ring
    rw [h9] at h8
    have h10 : (2 * Real.log n ^ ((5 : ℝ) / 2) + 3) * (k : ℝ) ≤ ((k : ℤ) : ℝ) * ((m : ℤ) : ℝ) := by
      have hkR' : (0 : ℝ) < ((k : ℤ) : ℝ) := by exact_mod_cast hk
      nlinarith [hab, h8, hkR']
    have h10' : ((k : ℤ) : ℝ) * (2 * Real.log n ^ ((5 : ℝ) / 2) + 3) ≤
        ((k : ℤ) : ℝ) * ((m : ℤ) : ℝ) := by
      rw [mul_comm ((k : ℤ) : ℝ) (2 * Real.log n ^ ((5 : ℝ) / 2) + 3)]
      exact h10
    exact le_of_mul_le_mul_left h10' hkR
  obtain ⟨v, hv0, hv1, hvC⟩ := aux_penultimate_overlap_line_meets_cinf Cinf n0 hcomp n hn
    (fun j => (c j - 1) / (k : ℤ)) l ((a - 1) / (k : ℤ) + 1) ((b - (k : ℤ)) / (k : ℤ))
    hlen hin'
  refine ⟨fun j => if j = l then v else (c j - 1) / (k : ℤ), hvC, ?_⟩
  · intro w hw
    have hwl : (1 : ℤ) ≤ w l := hw.1.1
    have hwh : w l ≤ (k : ℤ) := hw.1.2
    have hwj : ∀ j, j ≠ l → w j = 1 + (c j - 1) % (k : ℤ) := by
      intro j hj
      have := hw.2 j hj
      simpa only [if_neg hj] using this
    have h1 : (k : ℤ) * ((a - 1) / (k : ℤ) + 1) ≥ a := by
      have := Int.ediv_mul_add_emod (a - 1) (k : ℤ)
      have h2 : 0 ≤ (a - 1) % (k : ℤ) := Int.emod_nonneg _ (by linarith)
      have h3 : (a - 1) % (k : ℤ) < (k : ℤ) := Int.emod_lt_of_pos _ hk0
      nlinarith [this, h2, h3]
    have h2 : (k : ℤ) * ((b - (k : ℤ)) / (k : ℤ)) ≤ b - (k : ℤ) := by
      have := Int.ediv_mul_add_emod (b - (k : ℤ)) (k : ℤ)
      have h3 : 0 ≤ (b - (k : ℤ)) % (k : ℤ) := Int.emod_nonneg _ (by linarith)
      linarith
    have h3 : (k : ℤ) * ((a - 1) / (k : ℤ) + 1) ≤ (k : ℤ) * v :=
      mul_le_mul_of_nonneg_left hv0 (by linarith)
    have h4 : (k : ℤ) * v ≤ (k : ℤ) * ((b - (k : ℤ)) / (k : ℤ)) :=
      mul_le_mul_of_nonneg_left hv1 (by linarith)
    refine ⟨?_, ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, if_true]
      linarith
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, if_true]
      linarith
    · intro j hj
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, if_neg hj]
      rw [hwj j hj]
      have h6 : (k : ℤ) * ((c j - 1) / (k : ℤ)) = c j - 1 - ((c j - 1) % (k : ℤ)) := by
        have := Int.ediv_mul_add_emod (c j - 1) (k : ℤ); linarith
      linarith


/-- **The side bound, in the form the frozen proof needs.**  If the penultimate
wave from `zc` is positive on a long coordinate segment whose cube-base points
lie in `cent d n`, then the `(M̂-1)`-wave is not stabilizable. -/
theorem aux_penultimate_segment_bound {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (k : ℕ) (hk : 1 ≤ k) (Cinf : Set (Site d)) (hCinf : IsInfiniteConnectedGoodSet η k Cinf)
    (zc : Site d)
    (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n zc)
    (n0 : ℕ)
    (hcomp : ∀ n, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ Cinf →
      (componentIn Cinfᶜ x).Finite ∧
        ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2))
    (n : ℕ) (hn : n0 ≤ n) (l : Fin d) (c : Site d) (a b : ℤ)
    (hlog : 0 ≤ Real.log n ^ ((5 : ℝ) / 2))
    (hab : ((2 * Real.log n ^ ((5 : ℝ) / 2) + 6) * (k : ℝ)) ≤ ((b - a : ℤ) : ℝ))
    (hin' : ∀ v : ℤ, (a - 1) / (k : ℤ) + 1 ≤ v → v ≤ (b - (k : ℤ)) / (k : ℤ) →
      (fun j => if j = l then v else (c j - 1) / (k : ℤ)) ∈ (cent d n : Set (Site d)))
    (j0 : ℤ)
    (hj0lo : (a - 1) / (k : ℤ) + 1 ≤ j0) (hj0hi : j0 ≤ (b - (k : ℤ)) / (k : ℤ))
    (hj0 : j0 = (zc l - 1) / (k : ℤ))
    (hpos : ∀ v : ℤ, a ≤ v → v ≤ b →
      0 < penultimateWave η zc (fun j => if j = l then v else c j))
    (hcov_zc : ∃ T0 : ℕ, ∀ t : ℕ, T0 ≤ t → ∀ x ∈ cube d k,
      0 < wave η 1 zc t (x + (k : ℤ) • macroIdx k zc)) :
    False := by
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hk0 : (0 : ℤ) < (k : ℤ) := by linarith
  obtain ⟨i, hiC, hi_ne, hline⟩ :=
    aux_segment_meets_cinf_line k hk Cinf n0 hcomp n hn l c a b hlog hab hin' j0 hj0lo hj0hi
  have hz : (fun j => if j = l then 1 else 1 + (c j - 1) % (k : ℤ)) ∈ cube d k := by
    intro j
    have hval : (fun j' => if j' = l then (1 : ℤ) else 1 + (c j' - 1) % (k : ℤ)) j =
        (if j = l then (1 : ℤ) else 1 + (c j - 1) % (k : ℤ)) := rfl
    rw [hval]
    split_ifs with hj
    · exact ⟨le_refl 1, hk1⟩
    · have h2 : 0 ≤ (c j - 1) % (k : ℤ) := Int.emod_nonneg _ (by linarith)
      have h3 : (c j - 1) % (k : ℤ) < (k : ℤ) := Int.emod_lt_of_pos _ hk0
      constructor <;> linarith
  have hline' : ∀ w ∈ line d k l (fun j => if j = l then 1 else 1 + (c j - 1) % (k : ℤ)),
      0 < penultimateWave η zc (w + (k : ℤ) • i) := by
    intro w hw
    obtain ⟨hlo, hhi, hoth⟩ := hline w hw
    have hfun : (fun j => if j = l then (w + (k : ℤ) • i) l else c j) = (w + (k : ℤ) • i) := by
      ext j
      by_cases hj : j = l
      · subst hj; simp only [if_true]
      · simp only [if_neg hj]
        exact (hoth j hj).symm
    rw [← hfun]
    exact hpos _ hlo hhi
  have hi_ne' : i ≠ macroIdx k zc := by
    intro hcon
    have h1 : i l = macroIdx k zc l := by rw [hcon]
    have h2 : macroIdx k zc l = (zc l - 1) / (k : ℤ) := rfl
    rw [h2, ← hj0] at h1
    exact hi_ne h1
  by_cases hN : 2 ≤ waveThreshold η zc - 1
  · exact aux_penultimate_overlap_propagate_line hd η hlow hhigh k hk Cinf hCinf zc i hiC
      l (fun j => if j = l then 1 else 1 + (c j - 1) % (k : ℤ)) hz hline' hN hlast
  · have hM2 : waveThreshold η zc = 2 := by
      have hlow0 : ∀ x, 0 ≤ η x := fun x => by linarith [hlow x]
      have hzpos : 0 < penultimateWave η zc ((fun j => if j = l then 1 else 1 + (c j - 1) % (k : ℤ)) + (k : ℤ) • i) :=
        hline' _ (by
          refine ⟨⟨?_, ?_⟩, fun j hj => rfl⟩
          · show (1 : ℤ) ≤ (if l = l then (1 : ℤ) else 1 + (c l - 1) % (k : ℤ))
            rw [if_pos rfl]
          · show (if l = l then (1 : ℤ) else 1 + (c l - 1) % (k : ℤ)) ≤ (k : ℤ)
            rw [if_pos rfl]; exact hk1)
      obtain ⟨h2, _⟩ := aux_penultimate_hlast η hlow0 hhigh zc _ hzpos
      omega
    exact aux_penultimate_overlap_propagate_line_one hd η hlow hhigh k hk Cinf hCinf zc i hiC
      l (fun j => if j = l then 1 else 1 + (c j - 1) % (k : ℤ)) hz hline'
      hM2 hlast hcov_zc


/-- **The radius re-choice, reduced to its content.**  If the side bound's
hypotheses hold at the radius `n'` for a run of length `L`, then `L` is below the
side bound's threshold.  This is the contrapositive of
`aux_penultimate_segment_bound`, and it is what the frozen proof of Lemma 3.5
needs: the caller supplies `hin'` at `n' := n + L + 2` from the rectangle. -/
theorem aux_penultimate_segment_bound' {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (k : ℕ) (hk : 1 ≤ k) (Cinf : Set (Site d)) (hCinf : IsInfiniteConnectedGoodSet η k Cinf)
    (zc : Site d)
    (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n zc)
    (n0 : ℕ)
    (hcomp : ∀ n, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ Cinf →
      (componentIn Cinfᶜ x).Finite ∧
        ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2))
    (n : ℕ) (hn : n0 ≤ n) (l : Fin d) (c : Site d) (a b : ℤ)
    (hlog : 0 ≤ Real.log n ^ ((5 : ℝ) / 2))
    (hab : ((2 * Real.log n ^ ((5 : ℝ) / 2) + 6) * (k : ℝ)) ≤ ((b - a : ℤ) : ℝ))
    (hin' : ∀ v : ℤ, (a - 1) / (k : ℤ) + 1 ≤ v → v ≤ (b - (k : ℤ)) / (k : ℤ) →
      (fun j => if j = l then v else (c j - 1) / (k : ℤ)) ∈ (cent d n : Set (Site d)))
    (hpos : ∀ v : ℤ, a ≤ v → v ≤ b →
      0 < penultimateWave η zc (fun j => if j = l then v else c j))
    (hcov_zc : ∃ T0 : ℕ, ∀ t : ℕ, T0 ≤ t → ∀ x ∈ cube d k,
      0 < wave η 1 zc t (x + (k : ℤ) • macroIdx k zc)) :
    False := by
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hk0 : (0 : ℤ) < (k : ℤ) := by linarith
  obtain ⟨i, hiC, hline⟩ :=
    aux_segment_meets_cinf_line' k hk Cinf n0 hcomp n hn l c a b hlog hab hin'
  have hz : (fun j => if j = l then 1 else 1 + (c j - 1) % (k : ℤ)) ∈ cube d k := by
    intro j
    have hval : (fun j' => if j' = l then (1 : ℤ) else 1 + (c j' - 1) % (k : ℤ)) j =
        (if j = l then (1 : ℤ) else 1 + (c j - 1) % (k : ℤ)) := rfl
    rw [hval]
    split_ifs with hj
    · exact ⟨le_refl 1, hk1⟩
    · have h2 : 0 ≤ (c j - 1) % (k : ℤ) := Int.emod_nonneg _ (by linarith)
      have h3 : (c j - 1) % (k : ℤ) < (k : ℤ) := Int.emod_lt_of_pos _ hk0
      constructor <;> linarith
  have hline' : ∀ w ∈ line d k l (fun j => if j = l then 1 else 1 + (c j - 1) % (k : ℤ)),
      0 < penultimateWave η zc (w + (k : ℤ) • i) := by
    intro w hw
    obtain ⟨hlo, hhi, hoth⟩ := hline w hw
    have hfun : (fun j => if j = l then (w + (k : ℤ) • i) l else c j) = (w + (k : ℤ) • i) := by
      ext j
      by_cases hj : j = l
      · subst hj; simp only [if_true]
      · simp only [if_neg hj]
        exact (hoth j hj).symm
    rw [← hfun]
    exact hpos _ hlo hhi
  by_cases hN : 2 ≤ waveThreshold η zc - 1
  · exact aux_penultimate_overlap_propagate_line hd η hlow hhigh k hk Cinf hCinf zc i hiC
      l (fun j => if j = l then 1 else 1 + (c j - 1) % (k : ℤ)) hz hline' hN hlast
  · have hM2 : waveThreshold η zc = 2 := by
      have hlow0 : ∀ x, 0 ≤ η x := fun x => by linarith [hlow x]
      have hzpos : 0 < penultimateWave η zc ((fun j => if j = l then 1 else 1 + (c j - 1) % (k : ℤ)) + (k : ℤ) • i) :=
        hline' _ (by
          refine ⟨⟨?_, ?_⟩, fun j hj => rfl⟩
          · show (1 : ℤ) ≤ (if l = l then (1 : ℤ) else 1 + (c l - 1) % (k : ℤ))
            rw [if_pos rfl]
          · show (if l = l then (1 : ℤ) else 1 + (c l - 1) % (k : ℤ)) ≤ (k : ℤ)
            rw [if_pos rfl]; exact hk1)
      obtain ⟨h2, _⟩ := aux_penultimate_hlast η hlow0 hhigh zc _ hzpos
      omega
    exact aux_penultimate_overlap_propagate_line_one hd η hlow hhigh k hk Cinf hCinf zc i hiC
      l (fun j => if j = l then 1 else 1 + (c j - 1) % (k : ℤ)) hz hline'
      hM2 hlast hcov_zc


/-- **The radius re-choice, reduced to its content.**  If the side bound's
hypotheses hold at the radius `n'` for a run of length `L`, then `L` is below the
side bound's threshold.  This is the contrapositive of
`aux_penultimate_segment_bound`, and it is what the frozen proof of Lemma 3.5
needs: the caller supplies `hin'` at `n' := n + L + 2` from the rectangle. -/
theorem aux_penultimate_segment_length_bound {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (k : ℕ) (hk : 1 ≤ k) (Cinf : Set (Site d)) (hCinf : IsInfiniteConnectedGoodSet η k Cinf)
    (zc : Site d)
    (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n zc)
    (n0 : ℕ)
    (hcomp : ∀ n, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ Cinf →
      (componentIn Cinfᶜ x).Finite ∧
        ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2))
    (n' : ℕ) (hn' : n0 ≤ n') (l : Fin d) (c : Site d) (a b : ℤ)
    (hlog : 0 ≤ Real.log n' ^ ((5 : ℝ) / 2))
    (hin' : ∀ v : ℤ, (a - 1) / (k : ℤ) + 1 ≤ v → v ≤ (b - (k : ℤ)) / (k : ℤ) →
      (fun j => if j = l then v else (c j - 1) / (k : ℤ)) ∈ (cent d n' : Set (Site d)))
    (j0 : ℤ)
    (hj0lo : (a - 1) / (k : ℤ) + 1 ≤ j0) (hj0hi : j0 ≤ (b - (k : ℤ)) / (k : ℤ))
    (hj0 : j0 = (zc l - 1) / (k : ℤ))
    (hpos : ∀ v : ℤ, a ≤ v → v ≤ b →
      0 < penultimateWave η zc (fun j => if j = l then v else c j))
    (hcov_zc : ∃ T0 : ℕ, ∀ t : ℕ, T0 ≤ t → ∀ x ∈ cube d k,
      0 < wave η 1 zc t (x + (k : ℤ) • macroIdx k zc)) :
    ¬ (((2 * Real.log n' ^ ((5 : ℝ) / 2) + 6) * (k : ℝ)) ≤ ((b - a : ℤ) : ℝ)) := by
  intro hbig
  exact aux_penultimate_segment_bound hd η hlow hhigh k hk Cinf hCinf zc hlast n0 hcomp
    n' hn' l c a b hlog hbig hin' j0 hj0lo hj0hi hj0 hpos hcov_zc

/-- The quotient of an integer by a positive integer is no larger in absolute
value than the integer itself. -/


theorem div_abs_le (k : ℤ) (hk : 1 ≤ k) (a : ℤ) : |a / k| ≤ |a| := by
  have hk0 : (0 : ℤ) < k := by linarith
  rcases le_total 0 a with hp | hnn
  · rw [abs_of_nonneg hp, abs_of_nonneg (Int.ediv_nonneg hp (by linarith))]
    rw [Int.ediv_le_iff_le_mul hk0]
    nlinarith
  · rw [abs_of_nonpos hnn]
    have h1 : a / k ≤ 0 := by
      rw [Int.ediv_le_iff_le_mul hk0]
      nlinarith
    rw [abs_of_nonpos h1]
    have h2 : a ≤ a / k := by
      rw [Int.le_ediv_iff_mul_le hk0]
      nlinarith
    omega

/-- The run of cube indices of a segment of length `a` lies within `|a| + k` of
the origin. -/


theorem div_run_abs_le (k : ℤ) (hk : 1 ≤ k) (a : ℤ) :
    |(a - 1) / k + 1| ≤ |a| + 2 ∧ |(a - k) / k| ≤ |a| + k := by
  have hk0 : (0 : ℤ) < k := by linarith
  have h1 : |(a - 1) / k| ≤ |a - 1| := div_abs_le k hk (a - 1)
  have h2 : |a - 1| ≤ |a| + 1 := by
    rw [abs_sub_le_iff]
    constructor
    · have := le_abs_self a; omega
    · have := neg_le_abs a; omega
  have h3 : |(a - k) / k| ≤ |a - k| := div_abs_le k hk (a - k)
  have h4 : |a - k| ≤ |a| + k := by
    rw [abs_sub_le_iff]
    constructor
    · have := le_abs_self a; omega
    · have := neg_le_abs a; omega
  constructor
  · have h5 : |(a - 1) / k + 1| ≤ |(a - 1) / k| + 1 := by
      have h6 : |(a - 1) / k + 1| ≤ |(a - 1) / k| + |(1 : ℤ)| := by
        have := abs_add_le ((a - 1) / k) 1
        simpa using this
      simpa using h6
    have h6 : |(a - 1) / k| ≤ |a| + 1 := le_trans h1 h2
    linarith
  · exact le_trans h3 h4

/-- The endpoints of a box containing `x` are within `|x|` plus the box's
side length of the origin. -/


theorem box_end_le (m M x : ℤ) (h1 : m ≤ x) (h2 : x ≤ M) :
    |m| ≤ |x| + (M - m) ∧ |M| ≤ |x| + (M - m) := by
  have hL : 0 ≤ M - m := by omega
  have hx : -|x| ≤ x ∧ x ≤ |x| := abs_le.mp (le_refl |x|)
  constructor
  · rw [abs_le]
    constructor
    · have h3 : -|x| - (M - m) ≤ m := by omega
      omega
    · have h3 : m ≤ x := h1
      omega
  · rw [abs_le]
    constructor
    · omega
    · have h3 : M ≤ x + (M - m) := by omega
      omega


/-- **The self-referential length bound.**  If `L` is a nonnegative integer with
`(2 (log n')^(5/2) + 6) k ≤ L` where `n' := n + L + K + 4`, and `L ≤ 2n + 1`,
then `L ≤ (2 (log n + log 8)^(5/2) + 6) k`. -/
theorem aux_length_bound (k K : ℕ) (hk : 1 ≤ k) (n L : ℤ)
    (hn : 2 ≤ n) (hKle : (K : ℤ) ≤ n) (hL0 : 0 ≤ L) (hL2 : L ≤ 2 * n + 1)
    (hbig : (L : ℝ) < (2 * Real.log ((n + L + (K : ℤ) + 4).toNat : ℝ) ^ ((5 : ℝ) / 2) + 6) * (k : ℝ)) :
    (L : ℝ) ≤ (2 * (Real.log n + Real.log 8) ^ ((5 : ℝ) / 2) + 6) * (k : ℝ) := by
  by_contra hcon
  rw [not_le] at hcon
  have h1 : ((n + L + (K : ℤ) + 4).toNat : ℝ) ≤ 8 * (n : ℝ) := by
    have h2 : ((n + L + (K : ℤ) + 4).toNat : ℤ) ≤ 8 * n := by
      have h7 : (0 : ℤ) ≤ (K : ℤ) := by positivity
      have h8 : (0 : ℤ) ≤ L := hL0
      have h10 : (2 : ℤ) ≤ n := hn
      have h11 : (0 : ℤ) ≤ n + L + (K : ℤ) + 4 := by linarith
      rw [Int.toNat_of_nonneg h11]
      have h12 : n + L + (K : ℤ) + 4 ≤ 8 * n := by
        have h13 : L ≤ 2 * n + 1 := hL2
        have h14 : (K : ℤ) ≤ n := hKle
        linarith
      linarith [h12]
    exact_mod_cast h2
  have h3 : (1 : ℝ) ≤ ((n + L + (K : ℤ) + 4).toNat : ℝ) := by
    have h7 : (0 : ℤ) ≤ (K : ℤ) := by positivity
    have h8 : (0 : ℤ) ≤ L := hL0
    have h10 : (2 : ℤ) ≤ n := hn
    have h11 : (0 : ℤ) ≤ n + L + (K : ℤ) + 4 := by linarith
    have h4 : (1 : ℤ) ≤ ((n + L + (K : ℤ) + 4).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg h11]
      linarith
    exact_mod_cast h4
  have hlog : Real.log ((n + L + (K : ℤ) + 4).toNat : ℝ) ≤ Real.log n + Real.log 8 := by
    have h5 : Real.log ((n + L + (K : ℤ) + 4).toNat : ℝ) ≤ Real.log (8 * (n : ℝ)) :=
      Real.log_le_log (by linarith [h3]) h1
    rw [Real.log_mul (by norm_num) (by positivity)] at h5
    linarith
  have h6 : Real.log ((n + L + (K : ℤ) + 4).toNat : ℝ) ^ ((5 : ℝ) / 2) ≤
      (Real.log n + Real.log 8) ^ ((5 : ℝ) / 2) := by
    apply Real.rpow_le_rpow
    · exact Real.log_nonneg (by linarith [h3])
    · exact hlog
    · norm_num
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h7 : (2 * Real.log ((n + L + (K : ℤ) + 4).toNat : ℝ) ^ ((5 : ℝ) / 2) + 6) * (k : ℝ) ≤
      (2 * (Real.log n + Real.log 8) ^ ((5 : ℝ) / 2) + 6) * (k : ℝ) := by
    nlinarith [h6, hkR]
  have h8 : (L : ℝ) < (2 * (Real.log n + Real.log 8) ^ ((5 : ℝ) / 2) + 6) * (k : ℝ) :=
    lt_of_lt_of_le hbig h7
  exact absurd h8 (not_lt.mpr (le_of_lt hcon))

