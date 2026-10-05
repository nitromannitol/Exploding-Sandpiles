/-
Assembling the bond box-crossing input from the good-site box crossing.

The bond box-crossing input `Exploding.xap15_BoxCrossing` asks that at every
density above `bondCritical d` the two opposite faces of a large box are joined by
an open path confined to the box, with probability tending to one.  The good-site
bridge `xbb_bond_box_crossing` produces, at high good-site density, almost sure
crossings by open paths that are free to leave the box.  Since `xbc_StarDuality`
is available unconditionally as `xmh_starDuality`, the bridge itself is now
unconditional.

This file supplies

* `xmj2_tendsto_measure_one_of_ae_eventually`, the Fatou transfer from an almost
  sure eventual event to the convergence of its probabilities to one;
* `xmj2_bond_box_crossing`, the unconditional form of the bridge;
* `xmj2_highDensity_openCrosses`, the high-density confined crossing obtained from
  it together with the confinement transfer;
* `xmj2_boxCrossing_of_transfers`, the reduction of `xap15_BoxCrossing` to the
  confinement transfer `xmj2_ConfinementTransfer` and the supercritical crossing
  extension `xmj2_SupercriticalCrossingExtension`.

The confinement transfer is the standard duality step relating a free crossing
`xbb_BondCrosses` to a crossing confined to the box `xap15_OpenCrosses`; the
supercritical extension is the RSW step extending the high-density range to all
densities above the critical one.
-/
import Exploding.Support.ExtAPBridge
import Exploding.Support.ExtAPMinCutStarFinal
import Exploding.Support.ExtAPSupercritical

open Exploding LatticeProb MeasureTheory Filter
open scoped Classical Topology ENNReal

namespace Exploding

variable {d : ℕ}

/-! ### An almost-sure eventual event has probabilities tending to one -/

/-- If an event sequence holds eventually almost surely, then its probabilities
tend to one.  This is Fatou's lemma applied to the indicator functions. -/
theorem xmj2_tendsto_measure_one_of_ae_eventually {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {A : ℕ → Set Ω} (hA : ∀ n, MeasurableSet (A n))
    (h : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∈ A n) :
    Tendsto (fun n => μ (A n)) atTop (𝓝 1) := by
  set E : Set Ω := {ω | ∀ᶠ n in atTop, ω ∈ A n} with hE
  have hEmeas : MeasurableSet E := by
    have hset : E = ⋃ N : ℕ, ⋂ n ∈ Set.Ici N, {ω : Ω | ω ∈ A n} := by
      ext ω
      simp only [hE, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, Set.mem_Ici]
      exact Filter.eventually_atTop
    rw [hset]
    exact MeasurableSet.iUnion fun N =>
      MeasurableSet.biInter (Set.to_countable (Set.Ici N)) (fun n _ => hA n)
  have hE1 : μ E = 1 := by
    rw [← prob_compl_eq_zero_iff hEmeas]
    have h' : μ {ω : Ω | ¬ (∀ᶠ n in atTop, ω ∈ A n)} = 0 := (ae_iff).mp h
    convert h' using 2
    ext ω
    simp [hE]
  have hfmeas : ∀ n, Measurable (fun ω : Ω => (A n).indicator (fun _ => (1 : ENNReal)) ω) :=
    fun n => Measurable.indicator measurable_const (hA n)
  have hpoint : (fun ω : Ω => E.indicator (fun _ => (1 : ENNReal)) ω) ≤
      fun ω => liminf (fun n => (A n).indicator (fun _ => (1 : ENNReal)) ω) atTop := by
    intro ω
    change E.indicator (fun _ => (1 : ENNReal)) ω ≤
      liminf (fun n => (A n).indicator (fun _ => (1 : ENNReal)) ω) atTop
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω (fun _ => (1 : ENNReal))]
      exact le_liminf_of_le (by isBoundedDefault)
        (by filter_upwards [hω] with n hn; simp [Set.indicator_of_mem hn])
    · rw [Set.indicator_of_notMem hω (fun _ => (1 : ENNReal))]
      exact bot_le
  have hInt : (1 : ENNReal) ≤
      ∫⁻ ω, liminf (fun n => (A n).indicator (fun _ => (1 : ENNReal)) ω) atTop ∂μ := by
    calc (1 : ENNReal) = ∫⁻ ω, E.indicator (fun _ => (1 : ENNReal)) ω ∂μ := by
          rw [lintegral_indicator_const hEmeas 1, one_mul, hE1]
      _ ≤ ∫⁻ ω, liminf (fun n => (A n).indicator (fun _ => (1 : ENNReal)) ω) atTop ∂μ :=
          lintegral_mono hpoint
  have hfatou := lintegral_liminf_le (μ := μ) (u := atTop)
    (f := fun n ω => (A n).indicator (fun _ => (1 : ENNReal)) ω) hfmeas
  have hint : (fun n => ∫⁻ ω, (A n).indicator (fun _ => (1 : ENNReal)) ω ∂μ) =
      fun n => μ (A n) := by
    funext n
    rw [lintegral_indicator_const (hA n) 1, one_mul]
  rw [hint] at hfatou
  have hge : (1 : ENNReal) ≤ liminf (fun n => μ (A n)) atTop := le_trans hInt hfatou
  rw [tendsto_order]
  constructor
  · intro a' ha'
    exact eventually_lt_of_lt_liminf (lt_of_lt_of_le ha' hge)
  · intro a' ha'
    filter_upwards with n
    exact lt_of_le_of_lt prob_le_one ha'

/-! ### The unconditional good-site bridge -/

/-- The good-site bridge with the star duality discharged by `xmh_starDuality`:
for `ρ < 1` with `xbc_rho d ρ < 1` there is `p < 1` such that whenever the good-site
marginal `q ^ (xap_cubeBonds 0).card` is at least `p`, the bond field of density `q`
almost surely crosses every large box. -/
theorem xmj2_bond_box_crossing (hd : 2 ≤ d) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hrho : xbc_rho d ρ < 1) :
    ∃ p : ℝ, 0 ≤ p ∧ p < 1 ∧ ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      p ≤ q ^ (xap_cubeBonds (0 : Site d)).card →
      ∀ i : Fin d, ∀ᵐ ω ∂(bondPercolation d q),
        ∀ᶠ n : ℕ in atTop, xbb_BondCrosses d n i ω :=
  xbb_bond_box_crossing (xmh_starDuality d hd) (by omega) hρ0 hρ1 hrho

/-! ### The two transfers relating free and confined crossings -/

/-- The confinement transfer: at high good-site density, the almost sure free
crossings of the box supplied by the bridge yield crossings confined to the box
with probability tending to one.  This is the standard duality step relating
`xbb_BondCrosses` to `xap15_OpenCrosses`. -/
def xmj2_ConfinementTransfer (d : ℕ) : Prop :=
  ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 → xbc_rho d ρ < 1 →
    ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      (∀ i : Fin d, ∀ᵐ ω ∂(bondPercolation d q),
        ∀ᶠ n : ℕ in atTop, xbb_BondCrosses d n i ω) →
      ∀ i : Fin d,
        Tendsto (fun n : ℕ => bondPercolation d q {ω | xap15_OpenCrosses d n i ω})
          Filter.atTop (𝓝 1)

/-- The supercritical crossing extension: the high-density confined crossing bound
extends to every density above the critical one.  This is the RSW step of the
box-crossing theorem. -/
def xmj2_SupercriticalCrossingExtension (d : ℕ) : Prop :=
  (∃ p : ℝ, 0 ≤ p ∧ p < 1 ∧ ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      p ≤ q ^ (xap_cubeBonds (0 : Site d)).card →
      ∀ i : Fin d,
        Tendsto (fun n : ℕ => bondPercolation d q {ω | xap15_OpenCrosses d n i ω})
          Filter.atTop (𝓝 1)) →
    xap15_BoxCrossing d

/-- The high-density confined crossing, unconditional in the star duality: pick
`ρ` with `xbc_rho d ρ < 1`, apply the bridge, and transfer free crossings to
confined ones. -/
theorem xmj2_highDensity_openCrosses (hconf : xmj2_ConfinementTransfer d) (hd : 2 ≤ d) :
    ∃ p : ℝ, 0 ≤ p ∧ p < 1 ∧ ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      p ≤ q ^ (xap_cubeBonds (0 : Site d)).card →
      ∀ i : Fin d,
        Tendsto (fun n : ℕ => bondPercolation d q {ω | xap15_OpenCrosses d n i ω})
          Filter.atTop (𝓝 1) := by
  set ρ : ℝ := 1 - (1 / 3 : ℝ) ^ (2 * d + 1) with hρdef
  have hkpos : 0 < (1 / 3 : ℝ) ^ (2 * d + 1) := by positivity
  have hkle : (1 / 3 : ℝ) ^ (2 * d + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; linarith
  have hρ1 : ρ < 1 := by rw [hρdef]; linarith
  have hrho : xbc_rho d ρ < 1 := by
    rw [xbc_rho, hρdef]
    have hpow : (3 : ℝ) ^ (2 * d) * (1 / 3 : ℝ) ^ (2 * d + 1) = 1 / 3 := by
      rw [pow_succ, ← mul_assoc, ← mul_pow]
      norm_num
    linarith
  obtain ⟨p, hp0, hp1, hp⟩ := xmj2_bond_box_crossing (d := d) hd hρ0 hρ1 hrho
  exact ⟨p, hp0, hp1, fun q hq0 hq1 hpq i =>
    hconf ρ hρ0 hρ1 hrho q hq0 hq1 (fun i => hp q hq0 hq1 hpq i) i⟩

/-- **The sharpest reduction.**  The bond box-crossing input `xap15_BoxCrossing`
follows from the confinement transfer and the supercritical crossing extension.
The good-site bridge is applied with the unconditional star duality
`xmh_starDuality`, so no star-duality hypothesis remains. -/
theorem xmj2_boxCrossing_of_transfers (hd : 2 ≤ d)
    (hconf : xmj2_ConfinementTransfer d) (hext : xmj2_SupercriticalCrossingExtension d) :
    xap15_BoxCrossing d :=
  hext (xmj2_highDensity_openCrosses hconf hd)

/-- The supercritical reduction assembled with the bond box-crossing supplied by
the two transfers, and the coarse-graining input of the high-density estimate. -/
theorem xmj2_supercriticalReduction_of_transfers
    (hconf : ∀ d : ℕ, 2 ≤ d → xmj2_ConfinementTransfer d)
    (hext : ∀ d : ℕ, 2 ≤ d → xmj2_SupercriticalCrossingExtension d)
    (hcg : xmj_BoxCrossingCoarseGraining) : xap12_SupercriticalReduction :=
  xmj_supercriticalReduction_of_boxCrossing
    (fun d hd => xmj2_boxCrossing_of_transfers hd (hconf d hd) (hext d hd)) hcg

end Exploding
