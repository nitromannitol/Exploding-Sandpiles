/-
The convergence of the last wave under the general hypotheses
(`prop:convergence_of_the_generalized_last_wave`, Section 5 of the paper).

The paper's proof has two steps. First, Hypothesis 4 (strongly box-crossing,
`hyp:box_filling`) and a stochastic domination theorem of Liggett (Theorem 0.0
in [liggett1997domination]) give a supercritical percolation cluster of strongly
box-crossing macroscopic cells. The domination theorem is the external result
`Exploding.External.LiggettSchonmannStacey`. It applies to finite-range-dependent
0/1 fields, and the crossing field is one by Hypothesis 1
(`hyp:finite_range_of_dependence`). Second, the rest of the argument follows the
proof in Section 3 almost exactly. The proof of the square lower bound there
(`lemma:square_lower_bound`) uses only `η ≥ 0`.

The general hypotheses replace the i.i.d. structure of the toy law of Section 3.
In Section 3, `Explosive η` almost surely follows from the convergence of the
time constant (`theorem:convergence_of_time_constant`) and the external result
`Exploding.External.FeyLevinePeresExplosive`. No such external result is
available for the general hypotheses, so explosion is derived from the wave
construction. The tool is the odometer-wave comparison `eq:odometer_wave_comp`:
the wave started at `z` dominates the `{z}`-frozen parallel toppling process,
though the two need not coincide.

The Section-3 argument, re-run with the general hypotheses, is packaged as the
single hypothesis `glw_Section3Open`. It mirrors Lemmas 3.1-3.7 and Proposition
3.1 of Section 3. It is kept as one hypothesis.

This file contains the following. The crossing field is measurable and
`k`-dependent (`glw_box_*`). The square lower bound (`glw_square_lower_bound`)
holds for `η ≥ 0`. The wave-to-explosion pieces (`glw_wave_to_explosive_*`)
are the nonnegativity and terminal stability of the parallel odometer, the bound
`v 0 ≥ n` and the domination of the wave by a stable `v`. The step from these
to `WaveStabilizable` and `Explosive` is part of `glw_Section3Open`. The last-wave
bound and approximate subadditivity are proved in the Section 3 setting
(`glw_last_wave_bound`, `glw_approx_subadditivity`). The shift ergodicity
(`glw_shift_ergodic`) and the subadditive limit theorem (`glw_kingman_linear`)
are also here. The Lipschitz estimate for cluster arrival times is
`glw_cluster_lipschitz`. The reduction `glw_reduce` takes `glw_Section3Open` as a
hypothesis and derives `glw_Conclusion`.

Some lemmas take a further input as an explicit hypothesis rather than proving
it. These are `hkd` in `glw_box_field_kdependent`, `hmix` (mixing on cylinder
events) in `glw_shift_ergodic`, `hcore` (the subadditive core) in
`glw_kingman_linear`, and `hlocal` (the local cluster bound) in
`glw_cluster_lipschitz`.
-/
import Exploding.Support.Hypotheses
import Exploding.Support.SquareLowerBoundExponential
import Exploding.External.LiggettSchonmannStacey
import Exploding.External.LiggettSchonmannStaceyBoundedDegree
import Exploding.External.MathieuHoles
import Exploding.External.AntalPisztora
import LatticeProb.Prob.ZeroOne

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

/-- Step 1: Liggett-Schonmann-Stacey domination, "Theorem 0.0" in
[liggett1997domination].  The external result is `Exploding.External.LiggettSchonmannStacey`, taken here as `hLSS`, and this step is a direct use of it: for every target density
`ρ < 1` there is `p < 1` such that any measurable field of bits `X` on the
background space whose law is `k`-dependent and whose one-site probabilities are
at least `p` dominates Bernoulli site percolation of density `ρ` on increasing
events.

The field of strongly box-crossing tiles is `k`-dependent by Hypothesis 1, in its family
form, through `glw_box_field_kdependent` below. -/
theorem glw_liggett_domination (hLSS : Exploding.External.LiggettSchonmannStacey)
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∃ p : ℝ, p < 1 ∧ ∀ (P : Measure (Site d → ℤ)), IsProbabilityMeasure P →
      ∀ X : Site d → (Site d → ℤ) → Bool, Measurable (fun η j => X j η) →
      KDependent k (P.map fun η j => X j η) →
      (∀ j : Site d, ENNReal.ofReal p ≤ P {η | X j η = true}) →
      ∀ A : Set (Site d → Bool), MeasurableSet A → IsIncreasingEvent A →
        sitePercolation d ρ A ≤ P ((fun η j => X j η) ⁻¹' A) := by
  obtain ⟨p, hp, h⟩ := hLSS d k hd ρ hρ0 hρ1
  refine ⟨p, hp, fun P hP X hX hK hmarg A hA hinc => ?_⟩
  haveI := hP
  have hmarg' : ∀ s : Site d,
      ENNReal.ofReal p ≤ (P.map fun η j => X j η) {ω | ω s = true} := by
    intro s
    have hms : MeasurableSet {ω : Site d → Bool | ω s = true} :=
      measurableSet_eq_fun (measurable_pi_apply s) measurable_const
    rw [Measure.map_apply hX hms]
    exact hmarg s
  have := h (P.map fun η j => X j η) (Measure.isProbabilityMeasure_map hX.aemeasurable) hK hmarg' A hA hinc
  rwa [Measure.map_apply hX hA] at this

section
open scoped Classical

/-- Step 1b (Hypothesis 1, family form).  Whether the tile `B_k + j·k` is strongly
box-crossing depends only on `η` restricted to that tile, since the frozen parallel toppling of
`StronglyBoxCrossed` holds the odometer fixed off the tile.  Tiles whose indices are further
apart than some `m` in `ℓ^∞` are further apart than `K` in the Manhattan norm, so Hypothesis
1 makes the field of indicators `m`-dependent.  The indicator field is measurable, since each
coordinate depends on finitely many integer-valued coordinates of `η`.

The argument is as follows. For fixed `k, j`, `StronglyBoxCrossed η k j` depends only on
`η` restricted to the finite tile `rboxShift k j`: unrolling `fodo`'s recursion
(`fodo_succ`, `fodo_of_mem`) by induction on `t`, a site's frozen odometer value at time `t`
is determined by the initial data `η` at sites of the (finite) tile reachable in `≤ t` steps
without leaving the tile, together with the fixed boundary data `w0`; since the recursion is
run only up to the fixed finite time `∏ l, k l`, this is a finite induction. Concludes
`∀ η₁ η₂, (∀ x ∈ rboxShift k j, η₁ x = η₂ x) → (StronglyBoxCrossed η₁ k j ↔ StronglyBoxCrossed η₂ k j)`.

`glw_box_fodo_dep` below is the general fact this needs: `fodo` frozen off a subset `S`
of `rboxShift k j` reads `η` only at sites where it is allowed to topple, i.e. at
`Sᶜ ⊆ rboxShift k j` (`fodo_succ`: frozen sites read only `w0`, never `η`), so two
backgrounds agreeing on `rboxShift k j` give the same `fodo` run, by induction on time. -/
theorem glw_box_fodo_dep (d : ℕ) (k : Fin d → ℕ) (j : Site d) (S : Set (Site d))
    (hS : Sᶜ ⊆ rboxShift k j) (η₁ η₂ : Site d → ℤ) (heq : ∀ x ∈ rboxShift k j, η₁ x = η₂ x)
    (w0 : Site d → ℤ) (t : ℕ) :
    fodo S η₁ w0 t = fodo S η₂ w0 t := by
  classical
  induction t with
  | zero => rfl
  | succ t ih =>
    funext x
    rw [fodo_succ, fodo_succ]
    by_cases hx : x ∈ S
    · simp [hx]
    · have hfc : fconf S η₁ w0 t x = fconf S η₂ w0 t x := by
        simp only [fconf, heq x (hS hx), ih]
      rw [if_neg hx, if_neg hx, ih, hfc]

theorem glw_box_finite_dep (d : ℕ) (k : Fin d → ℕ) (j : Site d) (η₁ η₂ : Site d → ℤ)
    (heq : ∀ x ∈ rboxShift k j, η₁ x = η₂ x) :
    StronglyBoxCrossed η₁ k j ↔ StronglyBoxCrossed η₂ k j := by
  have key : ∀ a b : Site d → ℤ, (∀ x ∈ rboxShift k j, a x = b x) →
      StronglyBoxCrossed a k j → StronglyBoxCrossed b k j := by
    intro a b hab h i z hz x hx
    have hSc : ((rboxShift k j)ᶜ ∪ rline k j i z)ᶜ ⊆ rboxShift k j := by
      intro y hy
      simp only [Set.mem_compl_iff, Set.mem_union, not_or, not_not] at hy
      exact hy.1
    have hfe := glw_box_fodo_dep d k j ((rboxShift k j)ᶜ ∪ rline k j i z) hSc a b hab
      (Set.indicator (rline k j i z) 1) (∏ l, k l)
    rw [← congrFun hfe x]
    exact h i z hz x hx
  exact ⟨key η₁ η₂ heq, key η₂ η₁ (fun x hx => (heq x hx).symm)⟩

/-- A predicate on `η` depending only on the (finite) restriction of `η` to a finite set `F`,
in the sense of `glw_box_finite_dep`'s conclusion, is measurable: it is the preimage,
under the restriction map `η ↦ η|_F` (measurable, `measurable_pi_lambda`/`measurable_pi_apply`
composed over the finite index set `F`), of the set of restrictions on which the predicate
holds. -/
theorem glw_box_measurable_of_finite_dep {F : Finset (Site d)} (p : (Site d → ℤ) → Prop)
    [DecidablePred p] (hdep : ∀ η₁ η₂, (∀ x ∈ F, η₁ x = η₂ x) → (p η₁ ↔ p η₂)) :
    Measurable (fun η => decide (p η)) := by
  classical
  let r : (Site d → ℤ) → (F → ℤ) := fun η x => η x
  let e : (F → ℤ) → (Site d → ℤ) := fun f x => if h : x ∈ F then f ⟨x, h⟩ else 0
  have hee : ∀ η, ∀ x ∈ F, e (r η) x = η x := by
    intro η x hx
    simp only [e, r, dif_pos hx]
  have hr : Measurable r := by
    refine measurable_pi_iff.mpr ?_
    intro x
    exact measurable_pi_apply (x : Site d)
  have hg : Measurable (fun f : F → ℤ => decide (p (e f))) :=
    measurable_of_countable _
  have hmain : (fun η : Site d → ℤ => decide (p η))
      = (fun f : F → ℤ => decide (p (e f))) ∘ r := by
    funext η
    simp only [Function.comp_apply]
    have hiff := hdep (e (r η)) η (hee η)
    by_cases h : p η
    · have h2 : p (e (r η)) := hiff.mpr h
      simp [h, h2]
    · have h2 : ¬ p (e (r η)) := fun hc => h (hiff.mp hc)
      simp [h, h2]
  rw [hmain]
  exact hg.comp hr

/-- The measurability conjunct of `glw_box_field_kdependent`, from
`glw_box_finite_dep` and `glw_box_measurable_of_finite_dep` applied at each fixed `j`
(with `F = rboxShift k j`), assembled into a function of `j` via `measurable_pi_lambda`. -/
theorem glw_box_measurable_fixed (d : ℕ) (k : Fin d → ℕ) (j : Site d) :
    Measurable (fun η : Site d → ℤ => decide (StronglyBoxCrossed η k j)) := by
  classical
  have hfin : (rboxShift k j).Finite := by
    have h : rboxShift k j = Set.univ.pi
        (fun i : Fin d => Set.Icc (1 + (k i : ℤ) * j i) ((k i : ℤ) * j i + (k i : ℤ))) := by
      ext x
      simp only [rboxShift, Set.mem_setOf_eq, Set.mem_univ_pi, Set.mem_Icc]
    rw [h]
    exact Set.Finite.pi (fun i : Fin d =>
      Set.finite_Icc (1 + (k i : ℤ) * j i) ((k i : ℤ) * j i + (k i : ℤ)))
  let F : Finset (Site d) := hfin.toFinset
  have hFmem : ∀ x, x ∈ F ↔ x ∈ rboxShift k j := fun x => hfin.mem_toFinset
  have hdep : ∀ η₁ η₂ : Site d → ℤ, (∀ x ∈ F, η₁ x = η₂ x) →
      (StronglyBoxCrossed η₁ k j ↔ StronglyBoxCrossed η₂ k j) :=
    fun η₁ η₂ h => glw_box_finite_dep d k j η₁ η₂ (fun x hx => h x ((hFmem x).2 hx))
  let r : (Site d → ℤ) → (F → ℤ) := fun η x => η x
  let e : (F → ℤ) → (Site d → ℤ) := fun f x => if h : x ∈ F then f ⟨x, h⟩ else 0
  have hee : ∀ η, ∀ x ∈ F, e (r η) x = η x := by
    intro η x hx
    simp only [e, r, dif_pos hx]
  have hr : Measurable r := by
    refine measurable_pi_iff.mpr ?_
    intro x
    exact measurable_pi_apply (x : Site d)
  have hg : Measurable (fun f : F → ℤ => decide (StronglyBoxCrossed (e f) k j)) :=
    measurable_of_countable _
  have hmain : (fun η : Site d → ℤ => decide (StronglyBoxCrossed η k j))
      = (fun f : F → ℤ => decide (StronglyBoxCrossed (e f) k j)) ∘ r := by
    funext η
    simp only [Function.comp_apply]
    have hiff := hdep (e (r η)) η (hee η)
    by_cases h : StronglyBoxCrossed η k j
    · have h2 : StronglyBoxCrossed (e (r η)) k j := hiff.mpr h
      simp [h, h2]
    · have h2 : ¬ StronglyBoxCrossed (e (r η)) k j := fun hc => h (hiff.mp hc)
      simp [h, h2]
  rw [hmain]
  exact hg.comp hr

theorem glw_box_measurable (d : ℕ) (k : Fin d → ℕ) :
    Measurable (fun η (j : Site d) => decide (StronglyBoxCrossed η k j)) := by
  exact measurable_pi_iff.mpr (fun j => glw_box_measurable_fixed d k j)


/-- The dependence-radius computation. Two tiles `rboxShift k j`
and `rboxShift k j'` whose macroscopic indices `j, j'` are more than `m` apart in `ℓ^∞`
(`∀ i, m < |j i - j' i|`) have every microscopic site of one more than `K` (from
`FiniteRangeOfDependence`) away in Manhattan norm from every microscopic site of the other,
for `m` large enough depending on `k` and `K` (each tile has diameter `≤ ∑ l, k l` in `mnorm`,
so `m > K / (min_i k i) + (diameter term)` suffices; the exact arithmetic is not carried
out here). Combined with `glw_box_finite_dep` (so events indexed by far-apart macroscopic
sites factor through disjoint, far-apart finite coordinate sets of `η`) and
`FiniteRangeOfDependence` itself, this would give the `k`-dependence conjunct. The statement
below takes that conjunct as the hypothesis `hkd`. -/
theorem glw_box_field_kdependent (d : ℕ) (P : Measure (Site d → ℤ))
    (_h1 : FiniteRangeOfDependence d P) (k : Fin d → ℕ) (_hk : ∀ i, 0 < k i)
    (hkd : ∃ m : ℕ, KDependent m (P.map fun η (j : Site d) => decide (StronglyBoxCrossed η k j))) :
    Measurable (fun η (j : Site d) => decide (StronglyBoxCrossed η k j)) ∧
      ∃ m : ℕ, KDependent m (P.map fun η (j : Site d) => decide (StronglyBoxCrossed η k j)) :=
  ⟨glw_box_measurable d k, hkd⟩

end

/-- Step 3 (Lemma 3.1 in the Section 5 setting).  On `Ω` with `η_min ≥ 0` the background is
nonnegative, so `Exploding.square_lower_bound_exponential` applies directly: the
`(2d)^{dn}`-wave covers `[-n, n]^d`. -/
theorem glw_square_lower_bound (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin) :
    ∀ η : Site d → ℤ, InOmega d ηmin η →
      ∀ n : ℕ, 1 ≤ n → ∀ x ∈ cent d n, ∃ t : ℕ, 0 < wave η ((2 * d) ^ (d * n)) (0 : Site d) t x := by
  intro η hη n hn x hx
  exact Exploding.square_lower_bound_exponential d hd η (fun y => le_trans hηmin (hη y).1) n hn
    ((2 * d) ^ (d * n)) le_rfl x hx

/-- Step 4 bridges `WaveStabilizable`/`wave` to `Robust`/`Stabilizable`/`Explosive` via
the odometer-wave comparison `eq:odometer_wave_comp`:
"`v_{t+t0} ≥ w_t` where `t0 = min{t : v_t ≥ w_0}`". This comparison between `fodo`/`podo`
runs with ordered initial data is the new ingredient here. The toy-law proof avoids it
by citing `Exploding.External.FeyLevinePeresExplosive` directly. For a general `P` there is
no such external citation, so `Explosive η` is derived from `¬ WaveStabilizable η n 0` for
some `n`. The comparison is a nontrivial domination argument in its own right.

The hypothesis `0 ≤ η` is needed for this route. On `η ≡ -1` every `n`-wave
decreases without bound, so it is not stabilizable, while `η + m δ₀` stabilizes
for every `m`. The route to `Explosive` is as follows. If `η + 2dn δ₀` stabilizes,
its terminal odometer `v` has finite support, `v 0 ≥ n`, and
`v x ≥ ⌊(∑_{y∼x} v y + η x)/(2d)⌋` for `x ≠ 0`, because the terminal sandpile is
stable. Induction on `t` gives `wave η n 0 t ≤ v`, and a nondecreasing integer
sequence bounded by a finitely supported `v` is eventually constant.

The pieces proved in this file are the nonnegativity and terminal stability of
`podo` (`glw_wave_to_explosive_pnonneg`, `glw_wave_to_explosive_pstable`), the
bound `v 0 ≥ n` (`glw_wave_to_explosive_of_origin_bound`), and the domination `wave ≤ v`
(`glw_wave_to_explosive_dom`). The last step, from these to `WaveStabilizable`,
needs the terminal odometer `v` to have finite support. That needs an upper bound
on `η`, which `0 ≤ η` alone does not give. So this step is not proved here. It
belongs to the Section-3 bundle `glw_Section3Open`.

The `podo` odometer never decreases below `0`: `podo s0 0 = 0` and each step only adds
a nonnegative increment (`podo_zero`, `podo_mono_step`), so `0 ≤ podo s0 t x` for every `t`
by induction. -/
theorem glw_wave_to_explosive_pnonneg (s0 : Site d → ℤ) (t : ℕ) (x : Site d) :
    0 ≤ podo s0 t x := by
  induction t with
  | zero => simp
  | succ t ih => rw [podo_succ]; split <;> omega

/-- Once `podo s0` stabilizes with terminal time `T` (`hT : ∀ t ≥ T, podo s0 t = podo s0 T`),
the terminal configuration is stable everywhere: `s0 x + lap (podo s0 T) x ≤ 2d - 1`.
Otherwise `podo`'s firing rule (`podo_succ`) would strictly increment `podo s0 (T+1) x`,
contradicting `podo s0 (T+1) = podo s0 T` (from `hT` at `t = T+1`). -/
theorem glw_wave_to_explosive_pstable (s0 : Site d → ℤ) (T : ℕ)
    (hT : ∀ t : ℕ, T ≤ t → podo s0 t = podo s0 T) (x : Site d) :
    s0 x + lap (podo s0 T) x ≤ 2 * (d : ℤ) - 1 := by
  have h1 := congrFun (hT (T + 1) (Nat.le_succ T)) x
  rw [podo_succ] at h1
  have h3 : ¬ (2 * d ≤ pconf s0 T x) := by
    intro hle; rw [if_pos hle] at h1; omega
  simp only [pconf] at h3
  omega

/-- If `0 < d` and `η + (2dn+1) δ₀` stabilizes with terminal odometer `v`, then `v 0 ≥ n`:
from `glw_wave_to_explosive_pstable` at `x = 0`,
`η 0 + (2dn+1) + lap v 0 ≤ 2d - 1`, and `lap v 0 = nbrSumZ v 0 - 2d·v 0 ≥ -2d·v 0` since
`nbrSumZ v 0 ≥ 0` (from `glw_wave_to_explosive_pnonneg` and `nbrSumZ`'s definition as a
sum of `v`-values), so `2d·v 0 ≥ 2dn + 2 - 2d = 2d(n-1) + 2 > 2d(n-1)`; dividing by `2d > 0`
gives `v 0 > n - 1`, i.e. `v 0 ≥ n`. -/
theorem glw_wave_to_explosive_of_origin_bound (η : Site d → ℤ) (hη : ∀ x, 0 ≤ η x) (hd : 0 < d)
    (n : ℕ) (v : Site d → ℤ) (hv0nn : ∀ x, 0 ≤ v x)
    (hstable0 : η (0 : Site d) + ((2 * d * n + 1 : ℕ) : ℤ) + lap v (0 : Site d) ≤ 2 * (d : ℤ) - 1) :
    (n : ℤ) ≤ v (0 : Site d) := by
  by_contra hcon
  push Not at hcon
  have hnn : 0 ≤ nbrSumZ v (0 : Site d) :=
    Finset.sum_nonneg fun _ _ => add_nonneg (hv0nn _) (hv0nn _)
  simp only [lap] at hstable0
  have hcast : ((2 * d * n + 1 : ℕ) : ℤ) = 2 * (d : ℤ) * (n : ℤ) + 1 := by push_cast; ring
  rw [hcast] at hstable0
  have hprod : 0 ≤ 2 * (d : ℤ) * ((n : ℤ) - v (0 : Site d) - 1) :=
    mul_nonneg (by positivity) (by omega)
  nlinarith [hη (0 : Site d)]

/-- Away from the origin, `glw_wave_to_explosive_pstable` gives `η x + lap v x ≤ 2d - 1`
(since `dirac 0 x = 0` there), which is exactly the hypothesis `wave`'s recursion needs to
stay below `v`: by induction on `t`, using `wave_of_ne`, `nbrSumZ_mono`, and the floor bound
`Int.ediv_lt_iff_lt_mul` / `Int.lt_add_one_iff` (as in `Exploding.lap_le_of_fixed`'s proof and
in `glw_last_wave_bound`'s `key` lemma above), `wave η n 0 t x ≤ v x` for every `t, x`,
given `v 0 ≥ n` and `v` nonnegative. -/
theorem glw_wave_to_explosive_dom (η : Site d → ℤ) (n : ℕ) (v : Site d → ℤ)
    (hv0nn : ∀ x, 0 ≤ v x) (hvn : (n : ℤ) ≤ v (0 : Site d))
    (hstable : ∀ x, x ≠ (0 : Site d) → η x + lap v x ≤ 2 * (d : ℤ) - 1) :
    ∀ t x, wave η n (0 : Site d) t x ≤ v x := by
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · intro t x
    have hx0 : x = (0 : Site 0) := funext fun i => i.elim0
    rw [hx0, wave_at_centre]
    exact hvn
  · have hdz : (0 : ℤ) < 2 * (d : ℤ) := by exact_mod_cast (by omega : 0 < 2 * d)
    intro t
    induction t with
    | zero =>
      intro x
      by_cases h : x = 0
      · subst h; rw [wave_zero]; simpa using hvn
      · rw [wave_zero]; simp only [if_neg h]; exact hv0nn x
    | succ t ih =>
      intro x
      by_cases h : x = 0
      · subst h; rw [wave_at_centre]; exact hvn
      · rw [wave_of_ne _ _ _ _ _ h]
        have h1 : nbrSumZ (wave η n 0 t) x ≤ nbrSumZ v x := nbrSumZ_mono ih x
        have hstx := hstable x h
        simp only [lap] at hstx
        have hlt : nbrSumZ (wave η n 0 t) x + η x < (v x + 1) * (2 * (d : ℤ)) := by nlinarith
        exact Int.lt_add_one_iff.mp ((Int.ediv_lt_iff_lt_mul hdz).mpr hlt)

/-- If `d = 0`, `Site d` has exactly one point (`Fin 0 → ℤ` is a subsingleton, since `Fin 0`
is empty), which is `WaveStabilizable`'s own centre `z`, so every `wave η n z t` is the
constant function `n` and `T = 0` witnesses stabilization. -/
theorem glw_wave_to_explosive_d0 (hd0 : d = 0) (η : Site d → ℤ) (n : ℕ) (z : Site d) :
    WaveStabilizable η n z := by
  subst hd0
  refine ⟨0, fun t _ => funext fun x => ?_⟩
  have hxz : x = z := funext fun i => i.elim0
  rw [hxz, wave_at_centre, wave_at_centre]

/-- Lemma 3.3 in the Section 5 setting.  The theorem `Exploding.Frozen.last_wave_bound`
carries `2d - 2 ≤ η` from Section 3, but its proof uses only `0 ≤ η ≤ 2d - 1`: the
penultimate wave is the terminal odometer of a stabilizable wave, so
`Δ ũ x + η x ≤ 2d - 1` for `x ≠ z` (`waveTerminal_fixed`), and when `M̂_η(z) = 1` this
is `η x ≤ 2d - 1`. -/
theorem glw_last_wave_bound (d : ℕ) (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (z : Site d) (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n z)
    (t : ℕ) (x : Site d) :
    lastWave η z t x ≤ 1 + penultimateWave η z x := by
  have hdR : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hdz : (0 : ℤ) < 2 * (d : ℤ) := by linarith
  have hne : {n : ℕ | 1 ≤ n ∧ ¬ WaveStabilizable η n z}.Nonempty := hlast
  have hmem : 1 ≤ waveThreshold η z ∧ ¬ WaveStabilizable η (waveThreshold η z) z :=
    Nat.sInf_mem hne
  simp only [lastWave]
  set M := waveThreshold η z with hMdef
  have key : ∀ u : Site d → ℤ, (∀ y, 0 ≤ u y) → u z = (M : ℤ) - 1 →
      (∀ y, y ≠ z → lap u y + η y ≤ 2 * (d : ℤ) - 1) →
      ∀ s : ℕ, ∀ y : Site d, wave η M z s y ≤ 1 + u y := by
    intro u hu0 huz hufix s
    induction s with
    | zero =>
      intro y
      by_cases h : y = z
      · subst h; rw [wave_at_centre]; linarith [huz]
      · rw [wave_zero]; simp only [if_neg h]; linarith [hu0 y]
    | succ s ih =>
      intro y
      by_cases h : y = z
      · subst h; rw [wave_at_centre]; linarith [huz]
      · rw [wave_of_ne _ _ _ _ _ h]
        have h1 : nbrSumZ (wave η M z s) y ≤ nbrSumZ (fun w => 1 + u w) y := nbrSumZ_mono ih y
        have h2 : nbrSumZ (fun w => 1 + u w) y = 2 * (d : ℤ) * 1 + nbrSumZ u y :=
          nbrSumZ_add_const u 1 y
        have h3 := hufix y h
        simp only [lap] at h3
        have hlt : nbrSumZ (wave η M z s) y + η y < (1 + u y + 1) * (2 * (d : ℤ)) := by
          nlinarith
        exact Int.lt_add_one_iff.mp ((Int.ediv_lt_iff_lt_mul hdz).mpr hlt)
  by_cases hM1 : M = 1
  · have hp : penultimateWave η z = 0 := by simp [penultimateWave, ← hMdef, hM1]
    rw [hp]
    have := key 0 (fun _ => le_refl 0) (by simp [hM1]) ?_ t x
    · simpa using this
    · intro y _
      have : nbrSumZ (0 : Site d → ℤ) y = 0 := by simp [nbrSumZ]
      simp only [lap, this]
      simpa using hhigh y
  · have hM2 : 2 ≤ M := by omega
    have hstab : WaveStabilizable η (M - 1) z := by
      by_contra hcon
      have hm : M - 1 ∈ {n : ℕ | 1 ≤ n ∧ ¬ WaveStabilizable η n z} := ⟨by omega, hcon⟩
      have hle : M ≤ M - 1 := Nat.sInf_le hm
      omega
    have hp : penultimateWave η z = waveTerminal η (M - 1) z := by
      simp [penultimateWave, ← hMdef, hM1]
    rw [hp]
    refine key (waveTerminal η (M - 1) z) (fun y => wave_nonneg η hlow (M - 1) z _ y) ?_ ?_ t x
    · show wave η (M - 1) z _ z = (M : ℤ) - 1
      rw [wave_at_centre]
      have : (1 : ℕ) ≤ M := by omega
      push_cast [Nat.cast_sub this]
      ring
    · exact fun y hy => lap_le_of_fixed η hdz _ y (waveTerminal_fixed η (M - 1) z hstab hy)

/-! ### Helper lemmas for Lemma 3.4 in the Section 5 setting

These are the helper lemmas used by the complete proof of
`glw_approx_subadditivity`; they are needed only for that theorem's own proof, and
`glw_last_wave_bound` itself is not redeclared, since the copy above already has a
complete proof. -/

/-- `x + e_i` is a neighbour of `x`. -/
theorem glw_adj_add_unit (x : Site d) (i : Fin d) : (lattice d).Adj (x + unit i) x :=
  ⟨i, Or.inr rfl⟩

/-- `x - e_i` is a neighbour of `x`. -/
theorem glw_adj_sub_unit (x : Site d) (i : Fin d) : (lattice d).Adj (x - unit i) x :=
  ⟨i, Or.inl (by abel)⟩

/-- Multi-step monotonicity of the `n`-wave in time, from `Wave.lean`. -/
theorem glw_wave_mono_time (η : Site d → ℤ) (hη : ∀ y, 0 ≤ η y) (hd : (0 : ℤ) < 2 * (d : ℤ))
    (n : ℕ) (z : Site d) {s t : ℕ} (hst : s ≤ t) (x : Site d) :
    wave η n z s x ≤ wave η n z t x := by
  induction t, hst using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih => exact le_trans ih (wave_mono_t η hη hd n z t x)

/-- The penultimate wave is nonnegative on a nonnegative background, from `Wave.lean`. -/
theorem glw_penultimateWave_nonneg (η : Site d → ℤ) (hη : ∀ y, 0 ≤ η y) (z x : Site d) :
    0 ≤ penultimateWave η z x := by
  unfold penultimateWave
  split
  · simp
  · exact wave_nonneg η hη _ z _ x

/-- The centre lies in its own penultimate cluster. -/
theorem glw_centre_mem_penultimateCluster (η : Site d → ℤ) (z : Site d) :
    z ∈ penultimateCluster η z := Or.inl rfl

/-- A neighbour of a site carrying penultimate mass lies in the penultimate cluster. -/
theorem glw_mem_penultimateCluster_of_adj (η : Site d → ℤ) (z x y : Site d)
    (hadj : (lattice d).Adj y x) (hy : 0 < penultimateWave η z y) :
    x ∈ penultimateCluster η z := Or.inr ⟨y, hadj, hy⟩

/-- A nonnegative function has a nonnegative neighbour sum. -/
theorem glw_nbrSumZ_nonneg (u : Site d → ℤ) (hu : ∀ y, 0 ≤ u y) (x : Site d) :
    0 ≤ nbrSumZ u x :=
  Finset.sum_nonneg fun _ _ => add_nonneg (hu _) (hu _)

/-- A positive neighbour sum of a nonnegative function is carried by a neighbour. -/
theorem glw_exists_adj_pos_of_nbrSumZ_pos (u : Site d → ℤ) (hu : ∀ y, 0 ≤ u y) (x : Site d)
    (h : 0 < nbrSumZ u x) : ∃ y, (lattice d).Adj y x ∧ 0 < u y := by
  by_contra hcon
  have hcon' : ∀ y, (lattice d).Adj y x → u y ≤ 0 := fun y hy =>
    not_lt.mp fun hpos => hcon ⟨y, hy, hpos⟩
  have hz : ∀ i : Fin d, u (x + unit i) + u (x - unit i) = 0 := by
    intro i
    have h1 : u (x + unit i) = 0 := le_antisymm (hcon' _ (glw_adj_add_unit x i)) (hu _)
    have h2 : u (x - unit i) = 0 := le_antisymm (hcon' _ (glw_adj_sub_unit x i)) (hu _)
    rw [h1, h2]; ring
  have hs : nbrSumZ u x = 0 := by
    simp only [nbrSumZ]
    exact Finset.sum_eq_zero fun i _ => hz i
  rw [hs] at h
  exact lt_irrefl 0 h

/-- When the last-wave index exceeds one, the wave one below it stabilizes. -/
theorem glw_penultimate_stabilizable (η : Site d → ℤ) (z : Site d)
    (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n z)
    (h1 : waveThreshold η z ≠ 1) :
    WaveStabilizable η (waveThreshold η z - 1) z := by
  have hne : {n : ℕ | 1 ≤ n ∧ ¬ WaveStabilizable η n z}.Nonempty := hlast
  have hmem : 1 ≤ waveThreshold η z ∧ ¬ WaveStabilizable η (waveThreshold η z) z :=
    Nat.sInf_mem hne
  have hM1 : 1 ≤ waveThreshold η z := hmem.1
  by_contra hcon
  have hm : waveThreshold η z - 1 ∈ {n : ℕ | 1 ≤ n ∧ ¬ WaveStabilizable η n z} :=
    ⟨by omega, hcon⟩
  have hle : waveThreshold η z ≤ waveThreshold η z - 1 := Nat.sInf_le hm
  omega

/-- The penultimate wave vanishes off its own penultimate cluster. -/
theorem glw_penultimateWave_eq_zero_of_not_mem (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (z : Site d) (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n z)
    {x : Site d} (hx : x ∉ penultimateCluster η z) :
    penultimateWave η z x = 0 := by
  have hnn := glw_penultimateWave_nonneg η hlow z x
  rcases eq_or_lt_of_le hnn with h | h
  · exact h.symm
  · exfalso
    have hne : x ≠ z := fun hxz => hx (hxz ▸ glw_centre_mem_penultimateCluster η z)
    have hfix : penultimateWave η z x = (nbrSumZ (penultimateWave η z) x + η x) / (2 * (d : ℤ)) := by
      by_cases h1 : waveThreshold η z = 1
      · have hp : penultimateWave η z = 0 := by simp [penultimateWave, h1]
        rw [hp]
        have h0 : nbrSumZ (0 : Site d → ℤ) x = 0 := by simp [nbrSumZ]
        rw [h0]
        have hlt : η x < 2 * (d : ℤ) := by linarith [hhigh x]
        have := Int.ediv_eq_zero_of_lt (hlow x) hlt
        simpa using this.symm
      · simp only [penultimateWave, if_neg h1]
        exact waveTerminal_fixed η (waveThreshold η z - 1) z
          (glw_penultimate_stabilizable η z hlast h1) hne
    have hSnn : 0 ≤ nbrSumZ (penultimateWave η z) x :=
      glw_nbrSumZ_nonneg _ (glw_penultimateWave_nonneg η hlow z) x
    rcases lt_or_ge (nbrSumZ (penultimateWave η z) x + η x) (2 * (d : ℤ)) with hc | hge
    · have hzero : (nbrSumZ (penultimateWave η z) x + η x) / (2 * (d : ℤ)) = 0 :=
        Int.ediv_eq_zero_of_lt (by linarith [hlow x]) hc
      rw [hzero] at hfix
      linarith
    · have hS : 0 < nbrSumZ (penultimateWave η z) x := by linarith [hhigh x]
      obtain ⟨y, hadj, hy⟩ :=
        glw_exists_adj_pos_of_nbrSumZ_pos _ (glw_penultimateWave_nonneg η hlow z) x hS
      exact hx (glw_mem_penultimateCluster_of_adj η z x y hadj hy)

/-- The penultimate wave at its own centre is `M̂_η(z) - 1`. -/
theorem glw_penultimateWave_at_centre (η : Site d → ℤ) (z : Site d)
    (hM : 1 ≤ waveThreshold η z) :
    penultimateWave η z z = (waveThreshold η z : ℤ) - 1 := by
  by_cases h : waveThreshold η z = 1
  · simp [penultimateWave, h]
  · simp only [penultimateWave, if_neg h, waveTerminal, wave_at_centre]
    push_cast [Nat.cast_sub hM]
    ring

/-- Comparing neighbour sums needs the comparison only at the neighbours. -/
theorem glw_nbrSumZ_mono_adj (u v : Site d → ℤ) (x : Site d)
    (h : ∀ y, (lattice d).Adj y x → u y ≤ v y) : nbrSumZ u x ≤ nbrSumZ v x := by
  simp only [nbrSumZ]
  refine Finset.sum_le_sum ?_
  intro i _
  exact add_le_add (h _ (glw_adj_add_unit x i)) (h _ (glw_adj_sub_unit x i))

/-- An `ℕ∞`-infimum over a nonempty set of naturals is attained. -/
theorem glw_sInf_coe_attained {P : ℕ → Prop} (h : ∃ n : ℕ, P n) :
    ∃ n : ℕ, P n ∧ sInf {t : ℕ∞ | ∃ m : ℕ, t = (m : ℕ∞) ∧ P m} = (n : ℕ∞) := by
  classical
  refine ⟨sInf {n | P n}, Nat.sInf_mem h, le_antisymm ?_ ?_⟩
  · exact sInf_le ⟨sInf {n | P n}, rfl, Nat.sInf_mem h⟩
  · refine le_sInf ?_
    rintro t ⟨m, rfl, hm⟩
    exact_mod_cast Nat.sInf_le hm

/-- An `ℕ∞`-infimum over an empty set of naturals is `⊤`. -/
theorem glw_sInf_coe_top {P : ℕ → Prop} (h : ¬ ∃ n : ℕ, P n) :
    sInf {t : ℕ∞ | ∃ m : ℕ, t = (m : ℕ∞) ∧ P m} = ⊤ := by
  have hempty : {t : ℕ∞ | ∃ m : ℕ, t = (m : ℕ∞) ∧ P m} = ∅ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
    rintro m rfl hm
    exact h ⟨m, hm⟩
  rw [hempty, sInf_empty]

/-- A finite penultimate-cluster arrival time is attained at a natural number. -/
theorem glw_clusterArrival_exists (η : Site d → ℤ) (y x : Site d)
    (h : clusterArrival η y x ≠ ⊤) :
    ∃ n : ℕ, 1 ≤ n ∧ (∀ w ∈ penultimateCluster η x, 0 < lastWave η y n w) ∧
      clusterArrival η y x = (n : ℕ∞) := by
  by_cases hex : ∃ n : ℕ, 1 ≤ n ∧ ∀ w ∈ penultimateCluster η x, 0 < lastWave η y n w
  · obtain ⟨n, hn, heq⟩ :=
      glw_sInf_coe_attained (P := fun n : ℕ => 1 ≤ n ∧ ∀ w ∈ penultimateCluster η x,
        0 < lastWave η y n w) hex
    exact ⟨n, hn.1, hn.2, heq⟩
  · exact absurd (glw_sInf_coe_top (P := fun n : ℕ => 1 ≤ n ∧ ∀ w ∈ penultimateCluster η x,
      0 < lastWave η y n w) hex) h

/-- The domination of the paper's proof of Lemma 3.4: past the penultimate-cluster
arrival time `N = T̃(a,b)`, the last wave started at `a` dominates the last wave
started at `b` at every site carrying no penultimate mass of `b`. -/
theorem glw_lastWave_dominates (η : Site d → ℤ) (hd : 2 ≤ d)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (hlast : ∀ y : Site d, ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n y)
    (a b : Site d) (N : ℕ)
    (hNb : ∀ w ∈ penultimateCluster η b, 0 < lastWave η a N w) :
    ∀ t : ℕ, ∀ x : Site d, penultimateWave η b x = 0 →
      lastWave η b t x ≤ lastWave η a (N + t) x := by
  have hdR : (2:ℤ) ≤ (d:ℤ) := by exact_mod_cast hd
  have hdz : (0:ℤ) < 2 * (d:ℤ) := by linarith
  have hη0 : ∀ y, 0 ≤ η y := hlow
  have hMb : 1 ≤ waveThreshold η b := (Nat.sInf_mem (hlast b)).1
  have hMa : 1 ≤ waveThreshold η a := (Nat.sInf_mem (hlast a)).1
  have hone : ∀ s : ℕ, ∀ w ∈ penultimateCluster η b, 1 ≤ lastWave η a (N + s) w := by
    intro s w hw
    have h1 : 0 < lastWave η a N w := hNb w hw
    have h2 : lastWave η a N w ≤ lastWave η a (N + s) w :=
      glw_wave_mono_time η hη0 hdz (waveThreshold η a) a (Nat.le_add_right N s) w
    linarith
  intro t
  induction t with
  | zero =>
    intro x hx
    by_cases hxb : x = b
    · have hM1 : waveThreshold η b = 1 := by
        have hc := glw_penultimateWave_at_centre η b hMb
        rw [hxb] at hx
        rw [hx] at hc
        omega
      have hval : lastWave η b 0 x = 1 := by simp [lastWave, hM1, hxb]
      rw [hval]
      simpa using hone 0 x (hxb ▸ glw_centre_mem_penultimateCluster η b)
    · have hval : lastWave η b 0 x = 0 := by simp [lastWave, wave_zero, hxb]
      rw [hval]
      exact wave_nonneg η hη0 (waveThreshold η a) a (N + 0) x
  | succ t ih =>
    intro x hx
    have h3 := glw_last_wave_bound d hd η hlow hhigh b (hlast b) (t+1) x
    rw [hx] at h3
    by_cases hxP : x ∈ penultimateCluster η b
    · have h4 := hone (t+1) x hxP
      linarith
    · have hxb : x ≠ b := fun h => hxP (h ▸ glw_centre_mem_penultimateCluster η b)
      by_cases hxa : x = a
      · have hval : lastWave η a (N + (t+1)) x = (waveThreshold η a : ℤ) := by
          rw [hxa]; simp [lastWave]
        have hge : (1:ℤ) ≤ (waveThreshold η a : ℤ) := by exact_mod_cast hMa
        rw [hval]
        linarith
      · have hnb : ∀ y, (lattice d).Adj y x → lastWave η b t y ≤ lastWave η a (N + t) y := by
          intro y hy
          refine ih y ?_
          by_contra hcon
          exact hxP (glw_mem_penultimateCluster_of_adj η b x y hy
            (lt_of_le_of_ne (glw_penultimateWave_nonneg η hlow b y) (Ne.symm hcon)))
        have hsum : nbrSumZ (lastWave η b t) x ≤ nbrSumZ (lastWave η a (N + t)) x :=
          glw_nbrSumZ_mono_adj _ _ x hnb
        simp only [lastWave] at hsum ⊢
        rw [wave_of_ne η (waveThreshold η b) b x t hxb,
          show N + (t + 1) = (N + t) + 1 from by omega,
          wave_of_ne η (waveThreshold η a) a x (N + t) hxa]
        exact Int.ediv_le_ediv hdz (by linarith)

/-- Lemma 3.4 in the Section 5 setting.  The proof of `Exploding.Frozen.approx_subadditivity`
uses the background only through Lemma 3.3 and the monotonicity of the last wave in time,
so it needs only `0 ≤ η ≤ 2d - 1`, through `glw_last_wave_bound`. -/
theorem glw_approx_subadditivity (d : ℕ) (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (hlast : ∀ y : Site d, ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n y)
    (a b z : Site d) :
    clusterArrival η a z ≤ clusterArrival η a b + clusterArrival η b z := by
  have hdR : (2:ℤ) ≤ (d:ℤ) := by exact_mod_cast hd
  have hdz : (0:ℤ) < 2 * (d:ℤ) := by linarith
  have hη0 : ∀ y, 0 ≤ η y := hlow
  by_cases hab : clusterArrival η a b = ⊤
  · simp [hab]
  by_cases hbz : clusterArrival η b z = ⊤
  · simp [hbz]
  obtain ⟨N, hN1, hNb, hNeq⟩ := glw_clusterArrival_exists η a b hab
  obtain ⟨K, hK1, hKz, hKeq⟩ := glw_clusterArrival_exists η b z hbz
  rw [hNeq, hKeq, ← Nat.cast_add]
  refine clusterArrival_le η a z (N + K) (by omega) ?_
  intro w hw
  by_cases hpw : penultimateWave η b w = 0
  · have hdom := glw_lastWave_dominates η hd hlow hhigh hlast a b N hNb K w hpw
    have hpos := hKz w hw
    linarith
  · have hwb : w ∈ penultimateCluster η b := by
      by_contra hcon
      exact hpw (glw_penultimateWave_eq_zero_of_not_mem η hlow hhigh b (hlast b) hcon)
    have h1 : 0 < lastWave η a N w := hNb w hwb
    have h2 : lastWave η a N w ≤ lastWave η a (N + K) w :=
      glw_wave_mono_time η hη0 hdz (waveThreshold η a) a (Nat.le_add_right N K) w
    linarith

/-- Ergodicity of a single shift (proof of the convergence proposition).
`ErgodicOn` is ergodicity of the group `L`, which does not give ergodicity of one
translation.  Translation by `y ∈ L` preserves `P` (`StationaryOn`), and Hypothesis 1
makes it mixing on cylinder events, hence ergodic.

The argument uses `LatticeProb.ZeroOne`'s criterion `ergodic_of_mixing_on_isSetRing`.
It needs mixing only on a generating ring of sets, for any probability measure and any
measure-preserving map. The product-specific corollary `ergodic_coordShift_infinitePi`
is not used. The independence input there, which needs a product law, is replaced by
the finite-range hypothesis. That hypothesis gives independence once the two finite
index sets are more than `K` apart. So the iterate count `n` for mixing is chosen from
the growth of `n • y`, which is linear in `n` since `y ≠ 0`. It is not chosen from the
disjointness of `s` and its shift, as in the i.i.d. case.

`mnorm (n • y) = n * mnorm y`, so for `y ≠ 0` (`mnorm y ≥ 1`) it exceeds any bound `K` for
`n` large: `n = K + 1` already works since `mnorm y ≥ 1` gives `n * mnorm y ≥ n`. -/
theorem glw_shift_ergodic_growth (y : Site d) (hy0 : y ≠ 0) (K : ℕ) :
    ∃ n : ℕ, (K : ℤ) < mnorm ((n : ℤ) • y) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hy0
  have hmy : (1 : ℤ) ≤ mnorm y := by
    have h1 : (1 : ℤ) ≤ |y i| := Int.one_le_abs hi
    have h2 : |y i| ≤ mnorm y :=
      Finset.single_le_sum (fun l _ => abs_nonneg (y l)) (Finset.mem_univ i)
    linarith
  refine ⟨K + 1, ?_⟩
  have hnn : (0 : ℤ) ≤ (K : ℤ) + 1 := by positivity
  have h3 : mnorm (((K : ℤ) + 1) • y) = ((K : ℤ) + 1) * mnorm y := by
    unfold mnorm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hnn]
  have hcast : ((K + 1 : ℕ) : ℤ) • y = ((K : ℤ) + 1) • y := by push_cast; ring_nf
  rw [hcast, h3]
  nlinarith

/-- Iterating the shift by `y` `n` times is the shift by `n • y`: induction on `n`, unfolding
one application at a time (`Function.iterate_succ_apply'`). -/
theorem glw_shift_ergodic_iterate (y : Site d) (n : ℕ) :
    (fun η : Site d → ℤ => fun z => η (y + z))^[n] = fun η z => η ((n : ℤ) • y + z) := by
  induction n with
  | zero => funext η z; simp
  | succ n ih =>
    funext η z
    rw [Function.iterate_succ_apply', ih]
    have hcast : ((n + 1 : ℕ) : ℤ) • y = (n : ℤ) • y + y := by
      push_cast; rw [add_smul, one_smul]
    rw [hcast]
    abel

/-- `T := fun η z => η (y+z)` is measurable (each coordinate of the output is a coordinate
projection of the input, precomposed with the fixed translation `z ↦ y+z`, so
`measurable_pi_lambda`/`measurable_pi_apply` apply) and preserves `P`: `Measure.map T P = P`
is exactly `hstat y hy`. -/
theorem glw_shift_ergodic_meas_pres (d : ℕ) (L : AddSubgroup (Site d))
    (P : Measure (Site d → ℤ)) (hstat : StationaryOn d L P) (y : Site d) (hy : y ∈ L) :
    MeasurePreserving (fun η : Site d → ℤ => fun z => η (y + z)) P P :=
  ⟨measurable_pi_lambda _ (fun z => measurable_pi_apply (y + z)), hstat y hy⟩

/-- The mixing identity assumed as `hmix` would follow from the finite-range hypothesis by
the computation below. The computation is not carried out in this file. Given `n`
with `s` and `s.image (fun z => (n:ℤ)•y + z)` more than `FiniteRangeOfDependence`'s `K` apart
in `mnorm` (from `glw_shift_ergodic_growth` plus the triangle inequality over the finite
set `s`), the finite-range hypothesis gives `IndepFun` of the coordinate-restriction maps to `s` and to that shifted
image; factoring the shifted restriction map through the reindexing `ρ v i := v (n•y + i)`
(as in `LatticeProb.infinitePi_inter_preimage_coordShift_cylinder`, whose proof is otherwise
identical once `iIndepFun_infinitePi` is replaced by this `IndepFun`) turns that into the
cylinder measure identity, using `glw_shift_ergodic_iterate` to identify the `n`-fold
iterate with the shift by `n • y`. -/
theorem glw_shift_ergodic (d : ℕ) (L : AddSubgroup (Site d))
    (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hstat : StationaryOn d L P)
    (hmix : ∀ (y : Site d), y ≠ 0 → ∀ (s : Finset (Site d)) (S : Set (s → ℤ)),
      MeasurableSet S → ∃ n : ℕ, P (cylinder s S ∩
        (fun η : Site d → ℤ => fun z => η (y + z))^[n] ⁻¹' cylinder s S) =
      P (cylinder s S) * P (cylinder s S))
    (y : Site d) (hy : y ∈ L) (hy0 : y ≠ 0) :
    Ergodic (fun η : Site d → ℤ => fun z => η (y + z)) P := by
  haveI := hP
  refine ergodic_of_mixing_on_isSetRing (C := measurableCylinders fun _ : Site d => ℤ)
    isSetRing_measurableCylinders ?_ generateFrom_measurableCylinders.symm
    (glw_shift_ergodic_meas_pres d L P hstat y hy) ?_
  · exact ⟨{Set.univ}, Set.countable_singleton _,
      Set.singleton_subset_iff.2 isSetAlgebra_measurableCylinders.univ_mem, by simp⟩
  · intro B hB
    obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders B).1 hB
    obtain ⟨n, hn⟩ := hmix y hy0 s S hS
    exact ⟨n, hn⟩

/-- The subadditive ergodic theorem without a moment bound (proof of the convergence proposition).
The hypotheses of Section 5 give no bound on the mean of `clusterArrival η 0 y`, since
the bounds on the background hold only on an event of probability one, so Kingman's theorem
(`LatticeProb.ae_tendsto_div`, which needs `Integrable (g 1)`) does not apply directly.
It applies to the process induced on `A = {x : ∀ n, g n x ≤ C n + K}`, which has positive
measure for `K` large by `hlin`: there the first term is at most `C r_A + K`, integrable
by Kac's lemma.  This gives convergence along the return times to `A`, whose ratios of
consecutive terms tend to `1`; `hlip` then gives convergence along all `n` on `A`.  The
functions `liminf g n / n` and `limsup g n / n` are `T`-invariant by subadditivity and
nonnegativity, hence a.e. constant, and equal the limit on `A`.

Step (i): the set `A = {x : ∀ n, g n x ≤ C n + K}` has positive
measure for some fixed `C` (from `hlin`) and `K`: it is measurable (a countable intersection
of measurable sets, `g` being measurable) and, as `K → ∞` over `ℕ`, the sets increase to a
full-measure set (`hlin`'s witness `K` for a.e. `x`), so some finite `K` already gives
positive measure (continuity of measure from below, `MeasureTheory.tendsto_measure_iUnion`). -/
theorem glw_kingman_linear_setA {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (g : ℕ → Ω → ℝ) (hgm : ∀ n, Measurable (g n)) (C : ℝ)
    (hlin : ∀ᵐ x ∂μ, ∃ K : ℝ, ∀ n : ℕ, g n x ≤ C * n + K) :
    ∃ K : ℝ, MeasurableSet {x | ∀ n : ℕ, g n x ≤ C * n + K} ∧
      0 < μ {x | ∀ n : ℕ, g n x ≤ C * n + K} := by
  set A : ℕ → Set Ω := fun k => {x | ∀ n : ℕ, g n x ≤ C * n + (k : ℝ)} with hA
  have hA_meas : ∀ k, MeasurableSet (A k) := by
    intro k
    dsimp [A]
    simpa [Set.setOf_forall] using MeasurableSet.iInter (fun (n : ℕ) =>
      measurableSet_le (hgm n) (measurable_const))
  have hA_meas_union : MeasurableSet (⋃ (k : ℕ), A k) :=
    MeasurableSet.iUnion hA_meas
  have hA_mono : Monotone A := by
    intro a b h
    dsimp [A]
    intro x hx n
    have ha : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr h
    have hx' := hx n
    nlinarith
  have h_subset : (⋃ (k : ℕ), A k)ᶜ ⊆ {x | ¬ ∃ (K : ℝ), ∀ (n : ℕ), g n x ≤ C * n + K} := by
    intro x hx
    rw [Set.mem_compl_iff] at hx
    rw [Set.mem_setOf_eq]
    intro hEx
    rcases hEx with ⟨K, hK⟩
    let k := ⌈max K 0⌉₊
    have hK_le_k : K ≤ (k : ℝ) := by
      calc
        K ≤ max K 0 := le_max_left _ _
        _ ≤ (k : ℝ) := Nat.le_ceil _
    have hx' : x ∈ A k := by
      dsimp [A]
      intro n
      have hK_n := hK n
      nlinarith
    have hx_union : x ∈ ⋃ (k : ℕ), A k := Set.mem_iUnion.mpr ⟨k, hx'⟩
    exact hx hx_union
  have h_null : μ ((⋃ (k : ℕ), A k)ᶜ) = 0 :=
    measure_mono_null h_subset (ae_iff.mp hlin)
  have h_union_full : μ (⋃ (k : ℕ), A k) = 1 := by
    have h_add := measure_add_measure_compl (μ := μ) hA_meas_union
    rw [measure_univ, h_null, add_zero] at h_add
    exact h_add
  have h_tendsto : Tendsto (μ ∘ A) atTop (nhds (μ (⋃ (k : ℕ), A k))) :=
    tendsto_measure_iUnion_atTop hA_mono
  rw [h_union_full] at h_tendsto
  have h_pos_eventually : ∀ᶠ k in atTop, 0 < (μ ∘ A) k :=
    h_tendsto.eventually ((isOpen_Ioi (a := (0 : ENNReal))).mem_nhds (by norm_num : (1 : ENNReal) ∈ Set.Ioi (0 : ENNReal)))
  rcases (eventually_atTop.mp h_pos_eventually) with ⟨K, hK⟩
  have hKpos : 0 < μ (A K) := hK K (le_refl K)
  refine ⟨(K : ℝ), hA_meas K, hKpos⟩

/-- The subadditive limit theorem. The core argument is taken as the hypothesis `hcore`,
stated for the positive-measure set `A` of `glw_kingman_linear_setA`. The argument behind
`hcore` runs as follows. The first-return map to `A` is measure-preserving for the induced
normalised measure and ergodic (standard facts about induced transformations of an ergodic
system, e.g. Kac 1947 / Cornfeld-Fomin-Sinai Ch. 2). The return time `r_1` is integrable on
`A` by Kac's lemma (`∫_A r_1 dμ = μ(Ω) = 1`). `G j := g (r_j)` (`r_j` the `j`-th return time)
is subadditive along the induced map and bounded by `C r_1 + K` at `j = 1`, so
`LatticeProb.ae_tendsto_div` applied to the induced system gives `G j / j → L'` a.e. on `A`.
Birkhoff's theorem gives `r_j / j → 1 / μ(A)` a.e. on `A`, so `g (r_j) / r_j → L' · μ(A)` a.e.
on `A`. `hlip` extends this along-the-return-times convergence to convergence along every `n`.
Finally `liminf g n / n` and `limsup g n / n` are `T`-invariant (subadditivity, nonnegativity),
hence a.e. constant (`herg`, via `Ergodic.ae_eq_const_of_ae_eq_comp₀`), equal to the limit
already found on `A`. This transfers it to an a.e. limit on all of `Ω`. -/
-- The positive-measure set `A` and the constant `K` come from `glw_kingman_linear_setA`
-- (with the `C` of `hlin`); `hcore` then gives the limit.
theorem glw_kingman_linear {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (T : Ω → Ω) (_hT : MeasurePreserving T μ μ) (_herg : Ergodic T μ)
    (g : ℕ → Ω → ℝ) (_hsub : ∀ m n x, g (m + n) x ≤ g m x + g n (T^[m] x))
    (_hg : ∀ n x, 0 ≤ g n x) (hgm : ∀ n, Measurable (g n))
    (hlin : ∃ C : ℝ, ∀ᵐ x ∂μ, ∃ K : ℝ, ∀ n : ℕ, g n x ≤ C * n + K)
    (_hlip : ∃ C : ℝ, ∀ᵐ x ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, n ≤ m →
      m ≤ 2 * n → |g m x - g n x| ≤ C * ((m : ℝ) - n) + ε * n)
    (hcore : ∀ (C : ℝ),
      (∀ᵐ x ∂μ, ∃ K : ℝ, ∀ n : ℕ, g n x ≤ C * n + K) →
      ∀ (K : ℝ), MeasurableSet {x | ∀ n : ℕ, g n x ≤ C * n + K} →
      0 < μ {x | ∀ n : ℕ, g n x ≤ C * n + K} →
      ∃ L : ℝ, ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => g n x / (n : ℝ)) atTop (nhds L)) :
    ∃ L : ℝ, ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => g n x / (n : ℝ)) atTop (nhds L) := by
  obtain ⟨C, hC⟩ := hlin
  obtain ⟨K, hA, hApos⟩ := glw_kingman_linear_setA μ g hgm C hC
  exact hcore C hC K hA hApos

/-- The Lipschitz estimate for the penultimate-cluster arrival times from the origin (proof
of Proposition 5.1, convergence paragraph).  It replaces the continuity used in the proof
of Proposition 3.1 and supplies `hlip` of `glw_kingman_linear`.  Proof: combine
the open local bound `hlocal` (giving `clusterArrival η 0 x = a`, `clusterArrival η x x'
= c ≤ C·mnorm(x-x') + (log n)^γ`) with `glw_approx_subadditivity`'s triangle inequality
`clusterArrival η 0 x' ≤ clusterArrival η 0 x + clusterArrival η x x'` to bound
`clusterArrival η 0 x'` by `a + C·mnorm(x-x') + (log n)^γ`. -/
theorem glw_cluster_lipschitz (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (P : Measure (Site d → ℤ)) (_hP : IsProbabilityMeasure P)
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η)
    (_h1 : FiniteRangeOfDependence d P) (_h3 : PathFillingHyp d P)
    (_h4 : StronglyBoxCrossingHyp d P)
    (_hLSS : Exploding.External.LiggettSchonmannStacey)
    (_hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (_hHole : Exploding.External.MathieuHoleVolume)
    (_hChem : Exploding.External.AntalPisztoraChemicalDistance)
    (hlocal : ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧ ∀ᵐ η ∂P,
      (∀ y : Site d, ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n y) ∧
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ cent d n, ∃ a : ℕ, clusterArrival η (0 : Site d) x = (a : ℕ∞) ∧
        ∀ x' ∈ cent d n, ∃ c : ℕ, clusterArrival η x x' = (c : ℕ∞) ∧
          (c : ℝ) ≤ C * (mnorm (x - x') : ℝ) + Real.log n ^ γ) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧ ∀ᵐ η ∂P, ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ∀ x ∈ cent d n, ∀ x' ∈ cent d n, ∃ a b : ℕ,
        clusterArrival η (0 : Site d) x = (a : ℕ∞) ∧ clusterArrival η (0 : Site d) x' = (b : ℕ∞) ∧
          (b : ℝ) ≤ (a : ℝ) + C * (mnorm (x - x') : ℝ) + Real.log n ^ γ := by
  obtain ⟨γ, C, hγ, hC, hloc⟩ := hlocal
  refine ⟨γ, C, hγ, hC, ?_⟩
  filter_upwards [hloc, hsupp] with η hη hInOmega
  obtain ⟨hlast, n0, hn0⟩ := hη
  have hlow : ∀ x, 0 ≤ η x := fun x => le_trans hηmin (hInOmega x).1
  have hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1 := fun x => (hInOmega x).2
  refine ⟨n0, fun n hn x hx x' hx' => ?_⟩
  obtain ⟨a, haeq, hlocx⟩ := hn0 n hn x hx
  obtain ⟨a', ha'eq, _⟩ := hn0 n hn x' hx'
  obtain ⟨c, hceq, hcbound⟩ := hlocx x' hx'
  refine ⟨a, a', haeq, ha'eq, ?_⟩
  have htri := glw_approx_subadditivity d hd η hlow hhigh hlast (0 : Site d) x x'
  rw [haeq, ha'eq, hceq, ← Nat.cast_add] at htri
  have htri' : a' ≤ a + c := by exact_mod_cast htri
  have hcast : (a' : ℝ) ≤ (a : ℝ) + (c : ℝ) := by exact_mod_cast htri'
  linarith

/-- The conclusion of the convergence proposition for the generalized last wave, packaged so
that the Section-3 bundle can refer to it and the convergence theorem can consume it. -/
def glw_Conclusion (d : ℕ) (P : Measure (Site d → ℤ)) : Prop :=
  ∃ N : (Fin d → ℝ) → ℝ,
    Continuous N ∧
    ConvexOn ℝ Set.univ N ∧
    (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
    ∀ᵐ η ∂P,
      Explosive η ∧ (∀ x : Site d, lastArrival η (0 : Site d) x ≠ ⊤) ∧
        ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
            |((lastArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
              - N y| ≤ ε

/-- The Section-3 bundle, as an implication from the whole setting of the convergence
proposition (including its deterministic macroscopic growth input, the last hypothesis
below) to the conclusion. It contains the infinite-cluster construction (Hypotheses 1
and 4), the wave-to-explosion step, and the Section-3 re-run of Lemmas 3.1-3.7 and
Proposition 3.1. -/
def glw_Section3Open (d : ℕ) (_hd : 2 ≤ d) (ηmin : ℤ) (_hηmin : 0 ≤ ηmin)
    (L : AddSubgroup (Site d)) (_hL : L.index ≠ 0)
    (P : Measure (Site d → ℤ)) : Prop :=
  IsProbabilityMeasure P → (∀ᵐ η ∂P, InOmega d ηmin η) → StationaryOn d L P → ErgodicOn d L P →
  FiniteRangeOfDependence d P → PathFillingHyp d P → StronglyBoxCrossingHyp d P →
  Exploding.External.LiggettSchonmannStacey →
  Exploding.External.LiggettSchonmannStaceyBoundedDegree →
  Exploding.External.MathieuHoleVolume →
  Exploding.External.AntalPisztoraChemicalDistance →
  (∀ η : Site d → ℤ, InOmega d ηmin η →
    ∀ n : ℕ, 1 ≤ n → ∀ x ∈ cent d n,
      ∃ t : ℕ, 0 < wave η ((2 * d) ^ (d * n)) (0 : Site d) t x) →
  glw_Conclusion d P

/-- The reduction of the convergence proposition to the Section-3 bundle. The hypotheses
are the standing assumptions on `P` (almost sure membership in `InOmega`, stationarity and
ergodicity on `L`, and the finite-range, path-filling and strongly box-crossing hypotheses
`h1`, `h3`, `h4`), the external results `hLSS`, `hLSSB`, `hHole` and `hChem`, and the
Section-3 bundle `hsec3 : glw_Section3Open`. The proof applies `hsec3` to the deterministic
macroscopic growth input, which is the square lower bound `glw_square_lower_bound`, proved
in this file. The result is the full conclusion `glw_Conclusion`, explosion included. This
reduction uses no other deterministic lemma of this file. -/
theorem glw_reduce (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0)
    (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η)
    (hstat : StationaryOn d L P) (herg : ErgodicOn d L P)
    (h1 : FiniteRangeOfDependence d P) (h3 : PathFillingHyp d P)
    (h4 : StronglyBoxCrossingHyp d P)
    (hLSS : Exploding.External.LiggettSchonmannStacey)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance)
    (hsec3 : glw_Section3Open d hd ηmin hηmin L hL P) :
    glw_Conclusion d P :=
  hsec3 hP hsupp hstat herg h1 h3 h4 hLSS hLSSB hHole hChem
    (glw_square_lower_bound d hd ηmin hηmin)

end Exploding

open Exploding LatticeProb MeasureTheory Filter
