/-
Assembly of the high-density Bernoulli site box-crossing lemma from the star-duality
input `xbc_StarDuality`.

If the box `xap11_ball d n` had no open nearest-neighbour crossing in direction `i`,
the star duality would produce a `*`-connected all-closed set of size `s ≥ 2n + 1`
inside the box.  Splitting on the excess size `j = s - (2n + 1)`, the failure
probability is bounded by the geometric tail
`|ball| · r ^ (2n + 1) · (1 - r)⁻¹`, `r = 3 ^ (2d) (1 - q)`, which tends to zero; hence
at such densities almost surely every large box is crossed.
-/
import Exploding.Support.ExtBCBernoulli2
import Exploding.Support.ExtMHProof3

open Exploding LatticeProb MeasureTheory Filter
open scoped Classical Topology ENNReal

namespace Exploding

variable {d : ℕ}

/-- The geometric ratio of the Bernoulli box-crossing estimate: `3 ^ (2d) (1 - q)`. -/
noncomputable def xbc_rho (d : ℕ) (q : ℝ) : ℝ := (3 : ℝ) ^ (2 * d) * (1 - q)

/-- The all-closed `*`-connected set of excess size `j` inside the box. -/
def xbc_badSet (d n : ℕ) (j : ℕ) (ω : Site d → Bool) : Prop :=
  ∃ Γ ∈ xap11_starSets (xap11_ball d n) (2 * n + 1 + j), ∀ z ∈ Γ, ω z = false

/-- **Star duality gives the failure/size reduction.**  If the box `xap11_ball d n`
has no open crossing in direction `i`, then some excess size `j` carries an
all-closed `*`-connected set of size `2n + 1 + j` in the box. -/
theorem xbc_failure_subset_starSets (hdual : xbc_StarDuality d) (n : ℕ) (i : Fin d)
    (ω : Site d → Bool) (h : ¬ xbc_Crosses d n i ω) :
    ∃ j : ℕ, xbc_badSet d n j ω := by
  obtain ⟨s, hs, Γ, hΓ, hclosed⟩ := hdual n i ω h
  refine ⟨s - (2 * n + 1), Γ, ?_, hclosed⟩
  have hs' : 2 * n + 1 + (s - (2 * n + 1)) = s := by omega
  rwa [hs']

/-- **The high-density box-crossing bound.**  Conditional on the star duality, at density
`q` the probability that the box `xap11_ball d n` has no open crossing in direction `i` is
at most `|ball| · r ^ (2n + 1) · (1 - r)⁻¹` with `r = 3 ^ (2d) (1 - q)`. -/
theorem xbc_failure_prob_le (hdual : xbc_StarDuality d) {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (n : ℕ) (i : Fin d) :
    sitePercolation d q {ω | ¬ xbc_Crosses d n i ω} ≤
      ((xap11_ball d n).card : ENNReal) * (ENNReal.ofReal (xbc_rho d q)) ^ (2 * n + 1) *
        (1 - ENNReal.ofReal (xbc_rho d q))⁻¹ := by
  set r : ENNReal := ENNReal.ofReal (xbc_rho d q) with hr
  have hq : (0 : ℝ) ≤ 1 - q := by linarith
  have hbase : ENNReal.ofReal (xbc_rho d q) = (3 : ENNReal) ^ (2 * d) * ENNReal.ofReal (1 - q) := by
    rw [xbc_rho, ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [show ((3 : ℝ) ^ (2 * d)) = ((3 : ℕ) : ℝ) ^ (2 * d) by norm_num]
    rw [ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ ((3 : ℕ) : ℝ))]
    norm_num
  -- the per-excess bound
  have hterm : ∀ j : ℕ, sitePercolation d q {ω | xbc_badSet d n j ω} ≤
      ((xap11_ball d n).card : ENNReal) * r ^ (2 * n + 1 + j) := by
    intro j
    have hof : ENNReal.ofReal ((1 - q) ^ (2 * n + 1 + j)) =
        ENNReal.ofReal (1 - q) ^ (2 * n + 1 + j) :=
      ENNReal.ofReal_pow hq _
    have hprod : ((xap11_ball d n).card * (3 ^ d) ^ (2 * (2 * n + 1 + j)) : ℕ) =
        (xap11_ball d n).card * (3 ^ (2 * d)) ^ (2 * n + 1 + j) := by
      rw [show (3 ^ d) ^ (2 * (2 * n + 1 + j)) = (3 ^ (2 * d)) ^ (2 * n + 1 + j) by
        rw [← pow_mul, ← pow_mul]
        congr 1
        ring]
    refine (xbc_bad_starSets_prob_le h0 h1 (xap11_ball d n) (2 * n + 1 + j)).trans
      (le_of_eq ?_)
    rw [hof, hprod, hr, hbase, mul_pow]
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
    norm_num
    ring
  -- the union over the excesses
  have hsub : {ω : Site d → Bool | ¬ xbc_Crosses d n i ω} ⊆
      ⋃ j : ℕ, {ω : Site d → Bool | xbc_badSet d n j ω} := by
    intro ω hω
    obtain ⟨j, hj⟩ := xbc_failure_subset_starSets hdual n i ω hω
    exact Set.mem_iUnion.2 ⟨j, hj⟩
  calc sitePercolation d q {ω : Site d → Bool | ¬ xbc_Crosses d n i ω}
      ≤ sitePercolation d q (⋃ j : ℕ, {ω : Site d → Bool | xbc_badSet d n j ω}) :=
        measure_mono hsub
    _ ≤ ∑' j : ℕ, sitePercolation d q {ω : Site d → Bool | xbc_badSet d n j ω} :=
        measure_iUnion_le _
    _ ≤ ∑' j : ℕ, ((xap11_ball d n).card : ENNReal) * r ^ (2 * n + 1 + j) :=
        ENNReal.tsum_le_tsum hterm
    _ = ((xap11_ball d n).card : ENNReal) * r ^ (2 * n + 1) *
          (1 - r)⁻¹ := by
        rw [ENNReal.tsum_mul_left]
        rw [show (fun j : ℕ => r ^ (2 * n + 1 + j)) =
            (fun j : ℕ => r ^ (2 * n + 1) * r ^ j) by
          funext j; rw [pow_add]]
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
        ring

/-- The real polynomial-times-geometric sequence of the box-crossing bound is summable. -/
theorem xbc_summable (d : ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Summable (fun n : ℕ => (((2 * n + 1 : ℕ) : ℝ)) ^ d * ρ ^ (2 * n + 1) * (1 - ρ)⁻¹) := by
  have hρ2 : ‖ρ ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hρ0 2)]
    nlinarith
  refine Summable.of_norm_bounded_eventually_nat
    ((summable_pow_mul_geometric_of_norm_lt_one d hρ2).mul_left
      ((3 : ℝ) ^ d * ρ * (1 - ρ)⁻¹)) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hpow : (2 * n + 1 : ℕ) ^ d ≤ (3 * n) ^ d := Nat.pow_le_pow_left (by omega) d
  have hcast : (((2 * n + 1 : ℕ) : ℝ)) ^ d ≤ ((3 * n : ℕ) : ℝ) ^ d := by
    rw [← Nat.cast_pow, ← Nat.cast_pow]
    exact_mod_cast hpow
  have hcast' : ((3 * n : ℕ) : ℝ) ^ d = (3 : ℝ) ^ d * (n : ℝ) ^ d := by
    push_cast
    ring
  have hgeom : ρ ^ (2 * n + 1) = ρ * (ρ ^ 2) ^ n := by
    rw [pow_succ, pow_mul]
    ring
  have hinv : 0 ≤ (1 - ρ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hnonneg : 0 ≤ (((2 * n + 1 : ℕ) : ℝ)) ^ d * ρ ^ (2 * n + 1) * (1 - ρ)⁻¹ :=
    mul_nonneg (mul_nonneg (pow_nonneg (by positivity) d) (pow_nonneg hρ0 _)) hinv
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hinner : (((2 * n + 1 : ℕ) : ℝ)) ^ d * ρ ^ (2 * n + 1)
      ≤ ((3 : ℝ) ^ d * (n : ℝ) ^ d) * (ρ * (ρ ^ 2) ^ n) := by
    rw [hgeom]
    exact mul_le_mul_of_nonneg_right (hcast.trans_eq hcast')
      (mul_nonneg hρ0 (pow_nonneg (pow_nonneg hρ0 2) n))
  calc (((2 * n + 1 : ℕ) : ℝ)) ^ d * ρ ^ (2 * n + 1) * (1 - ρ)⁻¹
      ≤ (((3 : ℝ) ^ d * (n : ℝ) ^ d) * (ρ * (ρ ^ 2) ^ n)) * (1 - ρ)⁻¹ :=
        mul_le_mul_of_nonneg_right hinner hinv
    _ = ((3 : ℝ) ^ d * ρ * (1 - ρ)⁻¹) * ((n : ℝ) ^ d * (ρ ^ 2) ^ n) := by ring

/-- The pointwise box-crossing failure bound with the right-hand side written as the
`ofReal` of a real geometric expression. -/
theorem xbc_failure_prob_le_ofReal (hdual : xbc_StarDuality d) {q : ℝ} (h0 : 0 ≤ q)
    (h1 : q ≤ 1) (hr : xbc_rho d q < 1) (n : ℕ) (i : Fin d) :
    sitePercolation d q {ω | ¬ xbc_Crosses d n i ω} ≤
      ENNReal.ofReal ((((2 * n + 1 : ℕ) : ℝ)) ^ d * (xbc_rho d q) ^ (2 * n + 1) *
        (1 - xbc_rho d q)⁻¹) := by
  have hρ0 : 0 ≤ xbc_rho d q := by
    rw [xbc_rho]
    exact mul_nonneg (pow_nonneg (by norm_num) _) (by linarith)
  refine (xbc_failure_prob_le hdual h0 h1 n i).trans (le_of_eq ?_)
  set r : ENNReal := ENNReal.ofReal (xbc_rho d q) with hr
  have hcard : (((xap11_ball d n).card : ℕ) : ENNReal) =
      ENNReal.ofReal ((((2 * n + 1 : ℕ) : ℝ)) ^ d) := by
    rw [xap11_ball_card, Nat.cast_pow, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ))]
  have hpow : r ^ (2 * n + 1) = ENNReal.ofReal ((xbc_rho d q) ^ (2 * n + 1)) := by
    rw [hr, ENNReal.ofReal_pow hρ0]
  have h1r : (1 : ENNReal) - r = ENNReal.ofReal (1 - xbc_rho d q) := by
    rw [hr, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub (1 : ℝ) hρ0]
  have hinv : (1 - r)⁻¹ = ENNReal.ofReal ((1 - xbc_rho d q)⁻¹) := by
    rw [h1r, ENNReal.ofReal_inv_of_pos (by linarith)]
  have hM0 : 0 ≤ (((2 * n + 1 : ℕ) : ℝ)) ^ d := pow_nonneg (by positivity) d
  have hρp0 : 0 ≤ (xbc_rho d q) ^ (2 * n + 1) := pow_nonneg hρ0 _
  rw [hcard, hpow, hinv, ← ENNReal.ofReal_mul hM0,
    ← ENNReal.ofReal_mul (mul_nonneg hM0 hρp0)]

/-- **Almost sure eventual crossing at high density.**  Conditional on the star duality,
whenever `3 ^ (2d) (1 - q) < 1` almost surely every large box is crossed. -/
theorem xbc_ae_eventually_crosses (hdual : xbc_StarDuality d) {q : ℝ} (h0 : 0 ≤ q)
    (h1 : q ≤ 1) (hr : xbc_rho d q < 1) (i : Fin d) :
    ∀ᵐ ω ∂(sitePercolation d q), ∀ᶠ n : ℕ in atTop, xbc_Crosses d n i ω := by
  have hρ0 : 0 ≤ xbc_rho d q := by
    rw [xbc_rho]
    exact mul_nonneg (pow_nonneg (by norm_num) _) (by linarith)
  have hne : (∑' n : ℕ, sitePercolation d q {ω | ¬ xbc_Crosses d n i ω}) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ((xbc_summable d hρ0 hr).tsum_ofReal_ne_top) ?_
    exact ENNReal.tsum_le_tsum (fun n => xbc_failure_prob_le_ofReal hdual h0 h1 hr n i)
  simpa using xmh2_ae_eventually_notMem (sitePercolation d q)
    (fun n => {ω | ¬ xbc_Crosses d n i ω}) hne

end Exploding
