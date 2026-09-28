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

/-- The `n`-wave is bounded by its index `n`. -/
theorem wave_le_index {d : ℕ} (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (n : ℕ) (z : Site d) (t : ℕ) (x : Site d) :
    wave η n z t x ≤ (n : ℤ) := by
  induction t generalizing x with
  | zero =>
    rw [wave_zero]
    by_cases h : x = z <;> simp [h]
  | succ t ih =>
    by_cases h : x = z
    · rw [h, wave_at_centre]
    · rw [wave_of_ne η n z x t h]
      have hsum : nbrSumZ (wave η n z t) x ≤ 2 * (d : ℤ) * (n : ℤ) := by
        have h1 := nbrSumZ_mono (fun y => ih y) x
        have h2 : nbrSumZ (fun _ : Site d => (n : ℤ)) x = 2 * (d : ℤ) * (n : ℤ) := by
          simp only [nbrSumZ, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          ring
        rwa [h2] at h1
      have hlt : nbrSumZ (wave η n z t) x + η x < ((n : ℤ) + 1) * (2 * (d : ℤ)) := by
        nlinarith [hsum, hhigh x]
      rcases Nat.eq_zero_or_pos d with hd | hd
      · subst hd
        simp only [Nat.cast_zero, mul_zero] at hlt ⊢
        omega
      · have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
          have : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
          linarith
        rw [Int.ediv_le_iff_le_mul hd0]
        linarith

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
