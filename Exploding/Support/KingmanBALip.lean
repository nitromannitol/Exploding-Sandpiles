/-
Kingman's subadditive ergodic theorem with a Lipschitz transfer, and no integrability.

The Lipschitz-free statement `mk4_boundedAboveKingman` is false (`KingmanBARefute.lean`).  The
true statement uses the second Lipschitz bound of the paper: a nonnegative measurable
subadditive cocycle `g` over an ergodic measure-preserving map, which is Lipschitz upward up
to a sublinear error,
`g n' x ≤ g n x + C (n' - n) + ε n` for `n ≤ n' ≤ 2 n` and `n` large, converges:
`g n x / n → L` almost surely.

The proof follows the paper.  The Lipschitz bound gives an almost sure linear bound
`g n ≤ C' n + K`, so the set `A = {∀ n, g n ≤ C' n + K}` has positive measure for `K` large.
The induced cocycle `G_k = g (r_k)` on `A` is subadditive, nonnegative, and integrable (Kac),
so the subadditive ergodic theorem and Birkhoff's theorem give convergence of
`g (r_k) / r_k` on `A`; the transfer lemma `king_transfer` extends it to all `n`; and the
invariance of the lower limit `gLow` makes the limit constant and extends the convergence
from `A` to almost every point.
-/
import Exploding.Support.KingmanBAKac
import Exploding.Support.KingmanBATransfer

open Exploding LatticeProb MeasureTheory Filter ProbabilityTheory Topology
open scoped ENNReal

namespace Exploding

/-- A one-point Lipschitz bound gives a linear bound at all times. -/
theorem king_linear_bound_of_lip (g : ℕ → ℝ) (C : ℝ)
    (hlip : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ n' : ℕ, n ≤ n' → n' ≤ 2 * n →
      g n' ≤ g n + C * ((n' : ℝ) - n) + ε * n) :
    ∃ B : ℝ, ∀ n : ℕ, g n ≤ (4 * |C| + 4) * n + B := by
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hlip 1 one_pos)
  set M0 : ℕ := max (2 * N0) 4 with hM0
  set B : ℝ := ∑ n ∈ Finset.range (M0 + 1), |g n| with hB
  refine ⟨B, fun m => ?_⟩
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m ≤ M0
    · have h1 : |g m| ≤ B := by
        rw [hB]
        exact Finset.single_le_sum (f := fun n => |g n|) (fun n _ => abs_nonneg _)
          (Finset.mem_range.2 (by omega))
      have h2 : 0 ≤ (4 * |C| + 4) * (m : ℝ) := by positivity
      linarith [le_abs_self (g m)]
    · push Not at hm
      set n : ℕ := (m + 1) / 2 with hn
      have hnN : N0 ≤ n := by omega
      have hnm : n ≤ m := by omega
      have hmn : m ≤ 2 * n := by omega
      have hnlt : n < m := by omega
      have h1 := hN0 n hnN m hnm hmn
      have h2 := ih n hnlt
      have h5 : (5 : ℝ) ≤ m := by exact_mod_cast (by omega : 5 ≤ m)
      have h2n : (2 : ℝ) * n ≤ m + 1 := by exact_mod_cast (by omega : 2 * n ≤ m + 1)
      have hn3 : (n : ℝ) ≤ 3 * m / 5 := by linarith
      have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
      have hCle : C * ((m : ℝ) - n) ≤ |C| * m := by
        calc C * ((m : ℝ) - n) ≤ |C| * ((m : ℝ) - n) :=
              mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
          _ ≤ |C| * m := mul_le_mul_of_nonneg_left (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
              (abs_nonneg C)
      have hC0 : 0 ≤ |C| := abs_nonneg C
      have h3 : (4 * |C| + 5) * (n : ℝ) ≤ (4 * |C| + 5) * (3 * m / 5) :=
        mul_le_mul_of_nonneg_left hn3 (by positivity)
      have hcast : ((1 : ℝ)) * (n : ℝ) = n := one_mul _
      nlinarith [h1, h2, hCle, h3, mul_nonneg hC0 (by linarith : (0 : ℝ) ≤ m)]


section Invariance

variable {Ω : Type}

/-- The lower limit does not decrease along `T` where the averages at `T x` are bounded above. -/
theorem king_gLow_le_comp {T : Ω → Ω} {g : ℕ → Ω → ℝ} (hsub : SubadditiveAlong T g)
    (hg : ∀ n y, 1 ≤ n → 0 ≤ g n y) {x : Ω}
    (hub : IsBoundedUnder (· ≤ ·) atTop fun n => g n (T x) / (n : ℝ)) :
    gLow g x ≤ gLow g (T x) := by
  set u : ℕ → ℝ := fun n => g n (T x) / (n : ℝ) with hu
  set v : ℕ → ℝ := fun n => g (n + 1) x / ((n + 1 : ℕ) : ℝ) with hv
  have hvb : IsBoundedUnder (· ≥ ·) atTop v :=
    isBoundedUnder_ge_of fun n => div_nonneg_of hg x (n + 1)
  have hδ : Tendsto (fun n : ℕ => g 1 x / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat (g 1 x)
    exact h.comp (tendsto_add_atTop_nat 1)
  have hle : ∀ᶠ n in atTop, v n ≤ u n + g 1 x / ((n + 1 : ℕ) : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hstep : g (n + 1) x ≤ g 1 x + g n (T x) := by
      have h := hsub 1 n x
      rw [Nat.add_comm 1 n] at h
      simpa using h
    have hmid : g n (T x) / ((n + 1 : ℕ) : ℝ) ≤ u n := by
      rw [hu]
      refine div_le_div_of_nonneg_left (hg n (T x) hn) hn0 ?_
      push_cast
      linarith
    rw [hv]
    simp only
    rw [div_le_iff₀ hn1]
    have hexp : (u n + g 1 x / ((n + 1 : ℕ) : ℝ)) * ((n + 1 : ℕ) : ℝ)
        = u n * ((n + 1 : ℕ) : ℝ) + g 1 x := by field_simp
    rw [hexp]
    have hmid' : g n (T x) ≤ u n * ((n + 1 : ℕ) : ℝ) := by
      rw [← div_le_iff₀ hn1] at *
      exact hmid
    linarith
  have h1 : liminf v atTop ≤ liminf u atTop :=
    liminf_le_liminf_of_le_add hub hvb hδ hle
  have h2 : liminf v atTop = gLow g x := by
    rw [hv, gLow]
    exact liminf_nat_add (fun n => g n x / (n : ℝ)) 1
  rwa [h2] at h1

/-- If the orbit of `x` reaches a point `T^[m] x` along which `g n / n → c`, the upper limit
at `x` is at most `c`, by subadditivity. -/
theorem king_limsup_le {T : Ω → Ω} {g : ℕ → Ω → ℝ}
    (hsub : ∀ m n x, g (m + n) x ≤ g m x + g n (T^[m] x)) (hg : ∀ n x, 0 ≤ g n x)
    (x : Ω) (m : ℕ) (c : ℝ)
    (hc : Tendsto (fun n : ℕ => g n (T^[m] x) / (n : ℝ)) atTop (𝓝 c)) :
    limsup (fun n : ℕ => g n x / (n : ℝ)) atTop ≤ c := by
  set w : ℕ → ℝ := fun n => g m x / (n : ℝ)
    + (g (n - m) (T^[m] x) / ((n - m : ℕ) : ℝ)) * (((n - m : ℕ) : ℝ) / n) with hw
  have h1 : Tendsto (fun n : ℕ => g m x / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have h2 : Tendsto (fun n : ℕ => g (n - m) (T^[m] x) / ((n - m : ℕ) : ℝ)) atTop (𝓝 c) :=
    hc.comp (tendsto_sub_atTop_nat m)
  have h3 : Tendsto (fun n : ℕ => ((n - m : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => 1 - (m : ℝ) / n) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat _)
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop (m + 1)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    rw [Nat.cast_sub (by omega)]
    field_simp
  have hwt : Tendsto w atTop (𝓝 (0 + c * 1)) := h1.add (h2.mul h3)
  rw [zero_add, mul_one] at hwt
  have hle : (fun n : ℕ => g n x / (n : ℝ)) ≤ᶠ[atTop] w := by
    filter_upwards [eventually_ge_atTop (m + 1)] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hnm : (0 : ℝ) < ((n - m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - m)
    have hs := hsub m (n - m) x
    rw [Nat.add_sub_cancel' (by omega : m ≤ n)] at hs
    simp only [hw]
    rw [div_mul_div_cancel₀ hnm.ne']
    rw [← add_div]
    exact div_le_div_of_nonneg_right hs hn0.le
  have hcob : IsCoboundedUnder (· ≤ ·) atTop fun n : ℕ => g n x / (n : ℝ) :=
    isCoboundedUnder_le_of_le atTop (x := 0) fun n => by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · exact div_nonneg (hg n x) (Nat.cast_nonneg n)
  calc limsup (fun n : ℕ => g n x / (n : ℝ)) atTop ≤ limsup w atTop :=
        limsup_le_limsup hle hcob hwt.isBoundedUnder_le
    _ = c := hwt.limsup_eq

variable [MeasurableSpace Ω]

/-- The lower limit is almost everywhere invariant, assuming only that the averages are
almost surely bounded above (no integrability of `g 1`). -/
theorem king_ae_gLow_comp {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {g : ℕ → Ω → ℝ} (hsub : SubadditiveAlong T g)
    (hg : ∀ n y, 1 ≤ n → 0 ≤ g n y) (hgm : ∀ n, Measurable (g n))
    (hbdd : ∀ᵐ x ∂μ, IsBoundedUnder (· ≤ ·) atTop fun n => g n x / (n : ℝ)) :
    ∀ᵐ x ∂μ, gLow g (T x) = gLow g x := by
  have hbddT : ∀ᵐ x ∂μ, IsBoundedUnder (· ≤ ·) atTop fun n => g n (T x) / (n : ℝ) :=
    hT.quasiMeasurePreserving.ae hbdd
  have hmono : ∀ᵐ x ∂μ, gLow g x ≤ gLow g (T x) := by
    filter_upwards [hbddT] with x hx
    exact king_gLow_le_comp hsub hg hx
  set A : Ω → ℝ := fun x => Real.arctan (gLow g x) with hA
  have hAm : Measurable A := Real.continuous_arctan.measurable.comp (measurable_gLow hgm)
  have hAb : ∀ x, ‖A x‖ ≤ Real.pi / 2 := by
    intro x
    rw [hA, Real.norm_eq_abs, abs_le]
    exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _),
      le_of_lt (Real.arctan_lt_pi_div_two _)⟩
  have hAi : Integrable A μ :=
    Integrable.of_bound hAm.aestronglyMeasurable (Real.pi / 2)
      (Filter.Eventually.of_forall hAb)
  have hATi : Integrable (fun x => A (T x)) μ := by
    have hcopy := hAi
    rw [← hT.map_eq] at hcopy
    exact (integrable_map_measure hcopy.aestronglyMeasurable
      hT.measurable.aemeasurable).mp hcopy
  have hint : ∫ x, (A (T x) - A x) ∂μ = 0 := by
    have hTA : ∫ x, A (T x) ∂μ = ∫ x, A x ∂μ := by
      have h := integral_comp_iterate (m := 1) hT hAi
      simpa using h
    rw [integral_sub hATi hAi, hTA]
    ring
  have hnn : 0 ≤ᵐ[μ] fun x => A (T x) - A x := by
    filter_upwards [hmono] with x hx
    have := Real.arctan_le_arctan_iff.mpr hx
    simpa [hA] using this
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnn (hATi.sub hAi)).mp hint
  filter_upwards [hzero] with x hx
  have : Real.arctan (gLow g (T x)) = Real.arctan (gLow g x) := by
    have h := hx
    simp only [Pi.zero_apply, hA, sub_eq_zero] at h
    exact h
  exact Real.arctan_injective this

/-- An ergodic map visits every set of positive measure almost surely. -/
theorem king_ae_visit {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} (herg : Ergodic T μ)
    {A : Set Ω} (hA : MeasurableSet A) (hA0 : μ A ≠ 0) :
    ∀ᵐ x ∂μ, ∃ m : ℕ, T^[m] x ∈ A := by
  set B : Set Ω := ⋃ m : ℕ, (T^[m]) ⁻¹' A with hB
  have hBm : MeasurableSet B :=
    MeasurableSet.iUnion fun m => (herg.measurable.iterate m) hA
  have hsub : T ⁻¹' B ⊆ B := by
    intro x hx
    simp only [hB, Set.mem_preimage, Set.mem_iUnion] at hx ⊢
    obtain ⟨m, hm⟩ := hx
    refine ⟨m + 1, ?_⟩
    simpa [Function.iterate_succ_apply] using hm
  rcases herg.ae_empty_or_univ_of_preimage_ae_le hBm.nullMeasurableSet
    (Filter.Eventually.of_forall hsub) with h | h
  · exfalso
    have hAB : A ⊆ B := fun x hx => Set.mem_iUnion.2 ⟨0, by simpa using hx⟩
    have hB0 : μ B = 0 := by rw [measure_congr h, measure_empty]
    exact hA0 (measure_mono_null hAB hB0)
  · filter_upwards [Filter.eventuallyEq_set.1 h] with x hx
    exact Set.mem_iUnion.1 (hx.2 trivial)


end Invariance

section Core

variable {Ω : Type} [MeasurableSpace Ω]

/-- The set where the linear bound `g n ≤ C' n + K` holds from time `0`. -/
def king_A (g : ℕ → Ω → ℝ) (C' K : ℝ) : Set Ω := {x | ∀ n : ℕ, g n x ≤ C' * n + K}

omit [MeasurableSpace Ω] in
theorem king_A_mem {g : ℕ → Ω → ℝ} {C' K : ℝ} {x : Ω} :
    x ∈ king_A g C' K ↔ ∀ n : ℕ, g n x ≤ C' * n + K := Iff.rfl

theorem king_A_measurable {g : ℕ → Ω → ℝ} (hgm : ∀ n, Measurable (g n)) (C' K : ℝ) :
    MeasurableSet (king_A g C' K) := by
  have : king_A g C' K = ⋂ n : ℕ, {x | g n x ≤ C' * n + K} := by
    ext x; simp [king_A]
  rw [this]
  exact MeasurableSet.iInter fun n => measurableSet_le (hgm n) measurable_const

/-- **Convergence on the good set.**  On the set `A = {∀ n, g n ≤ C' n + K}` of positive
measure, the induced cocycle converges by Kac and Kingman, and the Lipschitz transfer
extends the convergence to all times. -/
theorem king_convergence_on_A {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) (g : ℕ → Ω → ℝ)
    (hsub : ∀ m n x, g (m + n) x ≤ g m x + g n (T^[m] x)) (hg : ∀ n x, 0 ≤ g n x)
    (hgm : ∀ n, Measurable (g n)) (C' K : ℝ) (hC' : 0 ≤ C') (hK : 0 ≤ K)
    (hA0 : μ (king_A g C' K) ≠ 0)
    (hlip : ∀ᵐ x ∂μ, ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ n' : ℕ, n ≤ n' →
      n' ≤ 2 * n → g n' x ≤ g n x + C * ((n' : ℝ) - n) + ε * n) :
    ∀ᵐ x ∂μ, x ∈ king_A g C' K →
      ∃ ℓ : ℝ, Tendsto (fun n : ℕ => g n x / (n : ℝ)) atTop (𝓝 ℓ) := by
  have hA : MeasurableSet (king_A g C' K) := king_A_measurable hgm C' K
  set A := king_A g C' K with hAdef
  haveI hνprob : IsProbabilityMeasure (mk3_normalizedRestrict μ A) :=
    mk3_normalizedRestrict_isProbability μ hA hA0
  have hmpA : MeasurePreserving (mk2_inducedMap T A) (mk3_normalizedRestrict μ A)
      (mk3_normalizedRestrict μ A) := king_inducedMap_measurePreserving_normalized hT hA
  have hrm : Measurable (mk2_returnTime T A) := king_returnTime_measurable hT.measurable hA
  have hrint := king_returnTime_integrable hT hA hA0
  -- transfer almost-sure statements from `μ` to `ν = μ_A`
  have hae : ∀ {p : Ω → Prop}, (∀ᵐ x ∂μ, p x) → ∀ᵐ x ∂(mk3_normalizedRestrict μ A), p x :=
    fun h => Measure.ae_smul_measure (ae_restrict_of_ae h) _
  have hmemA : ∀ᵐ x ∂(mk3_normalizedRestrict μ A), x ∈ A :=
    Measure.ae_smul_measure (ae_restrict_mem hA) _
  have hret : ∀ᵐ x ∂μ, x ∈ A → ∃ n : ℕ, 1 ≤ n ∧ T^[n] x ∈ A :=
    mk2_ae_return μ T hT.conservative A hA.nullMeasurableSet
  have hbase : ∀ᵐ x ∂(mk3_normalizedRestrict μ A), x ∈ A ∧ ∃ n : ℕ, 1 ≤ n ∧ T^[n] x ∈ A := by
    filter_upwards [hmemA, hae hret] with x h1 h2
    exact ⟨h1, h2 h1⟩
  have hgood : ∀ᵐ x ∂(mk3_normalizedRestrict μ A), ∀ k : ℕ,
      (mk2_inducedMap T A)^[k] x ∈ A ∧
        ∃ n : ℕ, 1 ≤ n ∧ T^[n] ((mk2_inducedMap T A)^[k] x) ∈ A := by
    rw [ae_all_iff]
    intro k
    exact (hmpA.iterate k).quasiMeasurePreserving.ae hbase
  -- the induced cocycle
  have hRmeas : ∀ k, Measurable (fun x => mk2_returnSeq T A x k) := by
    intro k
    simp only [mk4_returnSeq_eq_sum]
    exact Finset.measurable_sum _ fun j _ => hrm.comp (hmpA.measurable.iterate j)
  have hGm : ∀ k, Measurable (fun x => g (mk2_returnSeq T A x k) x) := by
    intro k
    have h1 : Measurable (fun p : ℕ × Ω => g p.1 p.2) := measurable_from_prod_countable_right hgm
    exact h1.comp ((hRmeas k).prodMk measurable_id)
  have hGsub : SubadditiveAlong (mk2_inducedMap T A)
      (fun k x => g (mk2_returnSeq T A x k) x) :=
    fun m n x => mk2_return_cocycle_subadditive T A g hsub x m n
  have hGnn : ∀ k y, 1 ≤ k → 0 ≤ (fun k x => g (mk2_returnSeq T A x k) x) k y :=
    fun k y _ => hg _ _
  have hG1 : Integrable (fun x => g (mk2_returnSeq T A x 1) x) (mk3_normalizedRestrict μ A) := by
    have hbound : Integrable (fun x => C' * (mk2_returnTime T A x : ℝ) + K)
        (mk3_normalizedRestrict μ A) := (hrint.const_mul C').add (integrable_const K)
    refine hbound.mono' (hGm 1).aestronglyMeasurable ?_
    filter_upwards [hmemA] with x hx
    have hR1 : mk2_returnSeq T A x 1 = mk2_returnTime T A x := by simp [mk2_returnSeq]
    rw [hR1, Real.norm_eq_abs, abs_of_nonneg (hg _ x)]
    exact king_A_mem.1 hx _
  have hKing := ae_tendsto_gLow hmpA hGsub hGnn hGm hG1
  have hBirk := ae_tendsto_bAvg hmpA (measurable_from_top.comp hrm) hrint
  have hmain : ∀ᵐ x ∂(mk3_normalizedRestrict μ A),
      ∃ ℓ : ℝ, Tendsto (fun n : ℕ => g n x / (n : ℝ)) atTop (𝓝 ℓ) := by
    filter_upwards [hKing, hBirk, hgood, hae hlip] with x hKx hBx hgx hlipx
    obtain ⟨ρ, hρ⟩ := hBx
    obtain ⟨C, hCx⟩ := hlipx
    have hRmono : ∀ k, mk2_returnSeq T A x k < mk2_returnSeq T A x (k + 1) := by
      intro k
      have hpos := mk2_returnTime_pos T A ((mk2_inducedMap T A)^[k] x) (hgx k).2
      simp only [mk2_returnSeq]
      omega
    have hR0 : mk2_returnSeq T A x 0 = 0 := rfl
    have hle := king_le_R (fun k => mk2_returnSeq T A x k) hRmono
    have hρlim : Tendsto (fun k : ℕ => (mk2_returnSeq T A x k : ℝ) / k) atTop (𝓝 ρ) := by
      refine hρ.congr fun k => ?_
      simp only [bAvg, birkhoffSum, mk4_returnSeq_eq_sum, Nat.cast_sum, Function.comp_apply]
    have hρ1 : 1 ≤ ρ := by
      refine ge_of_tendsto hρlim ?_
      filter_upwards [eventually_ge_atTop 1] with k hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      rw [le_div_iff₀ hk0, one_mul]
      exact_mod_cast hle k
    have hret' := mk4_tendsto_div_of_div (fun k => g (mk2_returnSeq T A x k) x)
      (fun k => (mk2_returnSeq T A x k : ℝ)) _ ρ (by linarith) hKx hρlim
    have hup : ∀ k n, mk2_returnSeq T A x k ≤ n →
        g n x ≤ g (mk2_returnSeq T A x k) x + C' * ((n : ℝ) - mk2_returnSeq T A x k) + K := by
      intro k n hkn
      have hxk : T^[mk2_returnSeq T A x k] x ∈ A := by
        have := (hgx k).1
        rwa [mk2_inducedMap_iterate] at this
      have hs := hsub (mk2_returnSeq T A x k) (n - mk2_returnSeq T A x k) x
      rw [Nat.add_sub_cancel' hkn] at hs
      have hb := king_A_mem.1 hxk (n - mk2_returnSeq T A x k)
      rw [Nat.cast_sub hkn] at hb
      linarith
    exact ⟨_, king_transfer (fun n => g n x) (fun k => mk2_returnSeq T A x k) ρ _ C' K C
      (fun n => hg n x) hC' hK hR0 hRmono (by linarith) hρlim hret' hup hCx⟩
  have hc0 : (μ A)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (measure_ne_top μ A)
  unfold mk3_normalizedRestrict at hmain
  have hrestr : ∀ᵐ x ∂(μ.restrict A), ∃ ℓ : ℝ,
      Tendsto (fun n : ℕ => g n x / (n : ℝ)) atTop (𝓝 ℓ) := by
    rw [ae_iff] at hmain ⊢
    rw [Measure.smul_apply, smul_eq_mul, mul_eq_zero] at hmain
    exact hmain.resolve_left hc0
  exact (ae_restrict_iff' hA).1 hrestr

end Core

section Main

variable {Ω : Type} [MeasurableSpace Ω]

/-- Linear growth gives bounded averages. -/
theorem king_isBoundedUnder_of_linear {g : ℕ → ℝ} {C' B : ℝ} (hB : ∀ n : ℕ, g n ≤ C' * n + B) :
    IsBoundedUnder (· ≤ ·) atTop fun n : ℕ => g n / (n : ℝ) := by
  refine ⟨C' + |B|, ?_⟩
  rw [Filter.eventually_map]
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [div_le_iff₀ hn0]
  have h1 : |B| ≤ |B| * n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [abs_nonneg B]
  have := hB n
  nlinarith [le_abs_self B]

/-- **Kingman's subadditive ergodic theorem with a Lipschitz transfer.**  A nonnegative
measurable subadditive cocycle over an ergodic measure-preserving map that is Lipschitz upward up
to a sublinear error, `g n' x ≤ g n x + C (n' - n) + ε n` for `n ≤ n' ≤ 2 n` and `n` large
(with a Lipschitz constant `C` that may depend on `x`), has an almost sure limit
`g n x / n → L`.  No integrability is assumed. -/
theorem king_lipKingman (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) (herg : Ergodic T μ) (g : ℕ → Ω → ℝ)
    (hsub : ∀ m n x, g (m + n) x ≤ g m x + g n (T^[m] x)) (hg : ∀ n x, 0 ≤ g n x)
    (hgm : ∀ n, Measurable (g n))
    (hlip : ∀ᵐ x ∂μ, ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ n' : ℕ, n ≤ n' →
      n' ≤ 2 * n → g n' x ≤ g n x + C * ((n' : ℝ) - n) + ε * n) :
    ∃ L : ℝ, ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => g n x / (n : ℝ)) atTop (𝓝 L) := by
  -- the almost sure linear bound
  have hlin : ∀ᵐ x ∂μ, ∃ C' B : ℝ, ∀ n : ℕ, g n x ≤ C' * n + B := by
    filter_upwards [hlip] with x hx
    obtain ⟨C, hC⟩ := hx
    obtain ⟨B, hB⟩ := king_linear_bound_of_lip (fun n => g n x) C hC
    exact ⟨_, B, hB⟩
  -- a good set of positive measure
  have hex : ∃ p : ℕ × ℕ, μ (king_A g (4 * (p.1 : ℝ) + 4) p.2) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hnull : μ (⋃ p : ℕ × ℕ, king_A g (4 * (p.1 : ℝ) + 4) p.2) = 0 :=
      measure_iUnion_null hcon
    have hcov : ∀ᵐ x ∂μ, x ∈ ⋃ p : ℕ × ℕ, king_A g (4 * (p.1 : ℝ) + 4) p.2 := by
      filter_upwards [hlip] with x hx
      obtain ⟨C, hC⟩ := hx
      obtain ⟨B, hB⟩ := king_linear_bound_of_lip (fun n => g n x) C hC
      refine Set.mem_iUnion.2 ⟨(⌈|C|⌉₊, ⌈B⌉₊), fun n => ?_⟩
      have h1 := Nat.le_ceil B
      have h2 := Nat.le_ceil |C|
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h3 : (4 * |C| + 4) * (n : ℝ) ≤ (4 * (⌈|C|⌉₊ : ℝ) + 4) * n :=
        mul_le_mul_of_nonneg_right (by linarith) hn
      have := hB n
      simp only
      linarith
    have hcomp : μ (⋃ p : ℕ × ℕ, king_A g (4 * (p.1 : ℝ) + 4) p.2)ᶜ = 0 := ae_iff.1 hcov
    have : μ Set.univ = 0 := by
      have h1 : (Set.univ : Set Ω) = (⋃ p : ℕ × ℕ, king_A g (4 * (p.1 : ℝ) + 4) p.2) ∪
          (⋃ p : ℕ × ℕ, king_A g (4 * (p.1 : ℝ) + 4) p.2)ᶜ :=
        (Set.union_compl_self _).symm
      rw [h1]
      exact measure_union_null hnull hcomp
    simp at this
  obtain ⟨⟨M0, K0⟩, hK0⟩ := hex
  have hC'0 : (0 : ℝ) ≤ 4 * (M0 : ℝ) + 4 := by positivity
  have hconvA := king_convergence_on_A hT g hsub hg hgm (4 * (M0 : ℝ) + 4) K0 hC'0
    (Nat.cast_nonneg K0) hK0 hlip
  -- the lower limit is a.s. constant
  have hg' : ∀ n y, 1 ≤ n → 0 ≤ g n y := fun n y _ => hg n y
  have hbdd : ∀ᵐ x ∂μ, IsBoundedUnder (· ≤ ·) atTop fun n : ℕ => g n x / (n : ℝ) := by
    filter_upwards [hlin] with x hx
    obtain ⟨C', B, hB⟩ := hx
    exact king_isBoundedUnder_of_linear hB
  have hinv : gLow g ∘ T =ᵐ[μ] gLow g := king_ae_gLow_comp hT hsub hg' hgm hbdd
  obtain ⟨c, hc⟩ := herg.ae_eq_const_of_ae_eq_comp₀ (measurable_gLow hgm).nullMeasurable hinv
  refine ⟨c, ?_⟩
  have hA : MeasurableSet (king_A g (4 * (M0 : ℝ) + 4) K0) := king_A_measurable hgm _ _
  -- along the orbit
  have hvis := king_ae_visit herg hA hK0
  have horb : ∀ᵐ x ∂μ, ∀ m : ℕ, (T^[m] x ∈ king_A g (4 * (M0 : ℝ) + 4) K0 →
      ∃ ℓ : ℝ, Tendsto (fun n : ℕ => g n (T^[m] x) / (n : ℝ)) atTop (𝓝 ℓ)) ∧
      gLow g (T^[m] x) = c := by
    rw [ae_all_iff]
    intro m
    exact (hT.iterate m).quasiMeasurePreserving.ae (hconvA.and hc)
  filter_upwards [hvis, horb, hlin, hc] with x hvx hox hlx hcx
  obtain ⟨m, hm⟩ := hvx
  obtain ⟨ℓ, hℓ⟩ := (hox m).1 hm
  have hℓc : ℓ = c := by
    have h1 : gLow g (T^[m] x) = ℓ := hℓ.liminf_eq
    rw [← h1]
    exact (hox m).2
  rw [hℓc] at hℓ
  have hup : limsup (fun n : ℕ => g n x / (n : ℝ)) atTop ≤ c := king_limsup_le hsub hg x m c hℓ
  have hlow : c ≤ liminf (fun n : ℕ => g n x / (n : ℝ)) atTop := by
    have : gLow g x = c := hcx
    rw [← this]
    rfl
  refine tendsto_of_le_liminf_of_limsup_le hlow hup ?_ ?_
  · obtain ⟨C', B, hB⟩ := hlx
    exact king_isBoundedUnder_of_linear hB
  · refine ⟨0, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards with n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact div_nonneg (hg n x) (Nat.cast_nonneg n)

/-- The statement `king_lipKingman` as a proposition, to be used in place of the false
Lipschitz-free statements `mk4_boundedAboveKingman`, `mk_kingman_linear` and
`glw2_KingmanCore`. -/
def king_LipKingman : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω), MeasurePreserving T μ μ → Ergodic T μ →
    ∀ (g : ℕ → Ω → ℝ), (∀ m n x, g (m + n) x ≤ g m x + g n (T^[m] x)) →
    (∀ n x, 0 ≤ g n x) → (∀ n, Measurable (g n)) →
    (∀ᵐ x ∂μ, ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ n' : ℕ, n ≤ n' → n' ≤ 2 * n →
      g n' x ≤ g n x + C * ((n' : ℝ) - n) + ε * n) →
    ∃ L : ℝ, ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => g n x / (n : ℝ)) atTop (𝓝 L)

theorem king_LipKingman_true : king_LipKingman :=
  fun μ _ T hT herg g hsub hg hgm hlip => king_lipKingman μ T hT herg g hsub hg hgm hlip

/-- The form closest to `mk4_boundedAboveKingman`: a subadditive cocycle bounded below by a
linear function, with the upward Lipschitz bound, converges. -/
theorem king_lipKingman_linear (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) (herg : Ergodic T μ) (h : ℕ → Ω → ℝ)
    (hsub : ∀ m n x, h (m + n) x ≤ h m x + h n (T^[m] x))
    (hlow : ∃ c : ℝ, ∀ n x, -c * n ≤ h n x) (hgm : ∀ n, Measurable (h n))
    (hlip : ∀ᵐ x ∂μ, ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ n' : ℕ, n ≤ n' →
      n' ≤ 2 * n → h n' x ≤ h n x + C * ((n' : ℝ) - n) + ε * n) :
    ∃ L : ℝ, ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => h n x / (n : ℝ)) atTop (𝓝 L) := by
  obtain ⟨c, hc⟩ := hlow
  have hsub' : ∀ m n x, (fun n x => h n x + c * n) (m + n) x ≤
      (fun n x => h n x + c * n) m x + (fun n x => h n x + c * n) n (T^[m] x) := by
    intro m n x
    have := hsub m n x
    simp only
    push_cast
    linarith
  obtain ⟨L, hL⟩ := king_lipKingman μ T hT herg (fun n x => h n x + c * n) hsub'
    (fun n x => by have := hc n x; linarith)
    (fun n => (hgm n).add measurable_const) (by
      filter_upwards [hlip] with x hx
      obtain ⟨C, hC⟩ := hx
      refine ⟨C + c, fun ε hε => ?_⟩
      filter_upwards [hC ε hε] with n hn n' hnn' hn'2
      have := hn n' hnn' hn'2
      linarith)
  refine ⟨L - c, ?_⟩
  filter_upwards [hL] with x hx
  have h1 : Tendsto (fun n : ℕ => (h n x + c * n) / (n : ℝ) - c) atTop (𝓝 (L - c)) :=
    hx.sub_const c
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  ring

end Main

section LogError

/-- A logarithmic error term is sublinear: `(log N)^γ ≤ ε n` for `N = 2 m n` and `n` large. -/
theorem king_log_rpow_le (γ : ℝ) (m : ℕ) (hm : 1 ≤ m) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.log ((2 * m * n : ℕ) : ℝ) ^ γ ≤ ε * n := by
  have hlo := isLittleO_log_rpow_rpow_atTop γ (zero_lt_one : (0 : ℝ) < 1)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have htend : Tendsto (fun n : ℕ => ((2 * m * n : ℕ) : ℝ)) atTop atTop := by
    refine tendsto_natCast_atTop_atTop.comp ?_
    exact tendsto_id.const_mul_atTop' (by omega : 0 < 2 * m)
  have hev : ∀ᶠ n : ℕ in atTop, ‖Real.log ((2 * m * n : ℕ) : ℝ) ^ γ‖
      ≤ ε / (2 * m) * ‖((2 * m * n : ℕ) : ℝ) ^ (1 : ℝ)‖ :=
    htend.eventually (hlo.def (show 0 < ε / (2 * m) by positivity))
  filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
  simp only [Real.rpow_one, Real.norm_eq_abs] at hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hNpos : (0 : ℝ) ≤ ((2 * m * n : ℕ) : ℝ) := Nat.cast_nonneg _
  calc Real.log ((2 * m * n : ℕ) : ℝ) ^ γ ≤ |Real.log ((2 * m * n : ℕ) : ℝ) ^ γ| := le_abs_self _
    _ ≤ ε / (2 * m) * |((2 * m * n : ℕ) : ℝ)| := hn
    _ = ε * n := by
        rw [abs_of_nonneg hNpos]
        push_cast
        field_simp

/-- **From a logarithmic Lipschitz bound along a ray to the form used by
`king_lipKingman`.**  If, for all box sizes `N ≥ n0` and all `n₁ ≤ n₂` with `n₂ m ≤ N`,
`a n₂ ≤ a n₁ + C (n₂ - n₁) + (log N)^γ`, then `a` is Lipschitz upward up to a sublinear
error. -/
theorem king_lip_of_log (a : ℕ → ℝ) (C γ : ℝ) (m : ℕ) (hm : 1 ≤ m) (n0 : ℕ)
    (h : ∀ N : ℕ, n0 ≤ N → ∀ n₁ n₂ : ℕ, n₁ ≤ n₂ → n₂ * m ≤ N →
      a n₂ ≤ a n₁ + C * ((n₂ : ℝ) - n₁) + Real.log N ^ γ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ n' : ℕ, n ≤ n' → n' ≤ 2 * n →
      a n' ≤ a n + C * ((n' : ℝ) - n) + ε * n := by
  intro ε hε
  filter_upwards [king_log_rpow_le γ m hm ε hε, eventually_ge_atTop n0] with n hn hn0
  intro n' hnn' hn'2
  have hN : n0 ≤ 2 * m * n := by
    have : n ≤ 2 * m * n := by nlinarith
    omega
  have := h (2 * m * n) hN n n' hnn' (by nlinarith)
  linarith

end LogError

end Exploding
