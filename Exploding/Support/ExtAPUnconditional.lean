/-
Unconditional corollaries of the box-crossing star duality.

The star duality `xbc_StarDuality d` is now available in every dimension `d ≥ 2`
(`Exploding.xmh_starDuality`), so the high-density site box-crossing statements that
were phrased conditionally on it can be instantiated: the site crossing probability
tends to one, and almost surely every large box is eventually crossed.  The
good-site field of high-density bond percolation gives the corresponding bond
crossing. The extension from high density down to the critical density
`bondCritical d`, needed for `xap15_BoxCrossing d`, is not proved here.

The general measure-theoretic step used below: if `A n` are measurable events and
almost surely `ω ∈ A n` for all large `n`, then `P(A n) → 1` along `atTop`.
-/
import Exploding.Support.ExtAPBridge
import Exploding.Support.ExtAPMinCutStarFinal

open Exploding LatticeProb MeasureTheory Filter
open scoped Classical Topology ENNReal

namespace Exploding

variable {d : ℕ}

/-! ### The site box crossing is unconditional -/

/-- **The high-density site box-crossing probability tends to one.** -/
theorem xmu_crossing_tendsto (d : ℕ) (hd : 2 ≤ d) {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (hr : xbc_rho d q < 1) (i : Fin d) :
    Tendsto (fun n : ℕ => sitePercolation d q {ω | xbc_Crosses d n i ω}) atTop (𝓝 1) :=
  xbc_crossing_tendsto (xmh_starDuality d hd) h0 h1 hr i

/-- **Almost surely every large box is eventually crossed, at high density.** -/
theorem xmu_ae_eventually_crosses (d : ℕ) (hd : 2 ≤ d) {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (hr : xbc_rho d q < 1) (i : Fin d) :
    ∀ᵐ ω ∂(sitePercolation d q), ∀ᶠ n : ℕ in atTop, xbc_Crosses d n i ω :=
  xbc_ae_eventually_crosses (xmh_starDuality d hd) h0 h1 hr i

/-- **The good-site bond box crossing at high density.** -/
theorem xmu_bond_box_crossing (d : ℕ) (hd : 2 ≤ d) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hrho : xbc_rho d ρ < 1) :
    ∃ p : ℝ, 0 ≤ p ∧ p < 1 ∧ ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      p ≤ q ^ (xap_cubeBonds (0 : Site d)).card →
      ∀ i : Fin d, ∀ᵐ ω ∂(bondPercolation d q),
        ∀ᶠ n : ℕ in atTop, xbb_BondCrosses d n i ω :=
  xbb_bond_box_crossing (xmh_starDuality d hd) (by omega) hρ0 hρ1 hrho

/-! ### From an almost-sure eventual event to a limit in probability -/

/-- If the measurable events `A n` hold almost surely for all large `n`, then their
probabilities tend to one. -/
theorem xmu_tendsto_of_ae_eventually {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A : ℕ → Set Ω} (hA : ∀ n, MeasurableSet (A n))
    (h : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, ω ∈ A n) :
    Tendsto (fun n : ℕ => μ (A n)) atTop (𝓝 1) := by
  classical
  set C : ℕ → Set Ω := fun N => ⋂ n ∈ Set.Ici N, A n with hCdef
  have hCmono : Monotone C := by
    intro N M hNM x hx
    exact Set.mem_iInter₂.2 fun n hn => Set.mem_iInter₂.1 hx n (le_trans hNM hn)
  have hUnion : (⋃ N, C N) = {ω | ∀ᶠ n : ℕ in atTop, ω ∈ A n} := by
    ext ω
    simp only [hCdef, Set.mem_iUnion, Set.mem_iInter, Set.mem_Ici, Set.mem_setOf_eq,
      Filter.eventually_atTop]
  have hBmeas : MeasurableSet (⋃ N, C N) :=
    MeasurableSet.iUnion fun N => MeasurableSet.biInter (Set.to_countable (Set.Ici N))
      (fun n _ => hA n)
  have hB1 : μ (⋃ N, C N) = 1 :=
    (mem_ae_iff_prob_eq_one hBmeas).mp (hUnion.symm ▸ h)
  have hlim : Tendsto (fun N : ℕ => μ (C N)) atTop (𝓝 1) := by
    simpa [Function.comp_def, hB1] using tendsto_measure_iUnion_atTop (μ := μ) hCmono
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb
    have hb' : ∀ᶠ N : ℕ in atTop, b < μ (C N) := (tendsto_order.1 hlim).1 b hb
    obtain ⟨N, hN⟩ := eventually_atTop.1 hb'
    filter_upwards [eventually_ge_atTop N] with n hn
    exact lt_of_lt_of_le (hN n hn)
      (measure_mono fun x hx => Set.mem_iInter₂.1 hx n (le_refl n))
  · intro b hb
    filter_upwards with n
    exact lt_of_le_of_lt (measure_mono (Set.subset_univ _)) (by rw [measure_univ]; exact hb)

end Exploding
