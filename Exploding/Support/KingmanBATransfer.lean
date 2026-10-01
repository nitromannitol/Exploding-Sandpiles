/-
The deterministic transfer from convergence along a sparse sequence of times to convergence
along all times.

Let `R k` be a strictly increasing sequence of times with `R k / k → ρ ∈ (0, ∞)`, so that the
gaps `R (k+1) - R k` are `o (R k)`.  Suppose a nonnegative sequence `u` converges along `R`,
satisfies `u n ≤ u (R k) + C' (n - R k) + K` for `n ≥ R k` (the upper bound that subadditivity
gives from a good time), and is Lipschitz upward up to a sublinear error,
`u n' ≤ u n + C (n' - n) + ε n` for `n ≤ n' ≤ 2 n` and `n` large.  Then `u n / n` converges to
the same limit.
-/
import Mathlib

open Filter Topology

namespace Exploding

/-- A strictly increasing sequence of naturals starting at `0` dominates the identity. -/
theorem king_le_R (R : ℕ → ℕ) (hRmono : ∀ k, R k < R (k + 1)) :
    ∀ k, k ≤ R k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih => have := hRmono k; omega

/-- The gaps of a sequence with `R k / k → ρ > 0` are negligible against `R k`. -/
theorem king_gap_ratio (R : ℕ → ℕ) (ρ : ℝ) (hρpos : 0 < ρ)
    (hρ : Tendsto (fun k : ℕ => (R k : ℝ) / k) atTop (𝓝 ρ)) (hle : ∀ k, k ≤ R k) :
    Tendsto (fun k : ℕ => ((R (k + 1) : ℝ) - R k) / R k) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ => (R (k + 1) : ℝ) / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 ρ) :=
    hρ.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun k : ℕ => ((k : ℝ) + 1) / k) atTop (𝓝 1) := by
    have : Tendsto (fun k : ℕ => 1 + 1 / (k : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    field_simp
  have h3 : Tendsto (fun k : ℕ => (k : ℝ) / R k) atTop (𝓝 ρ⁻¹) := by
    have := hρ.inv₀ hρpos.ne'
    refine this.congr' ?_
    filter_upwards with k
    simp [inv_div]
  have h4 := (h1.mul h2).mul h3
  rw [show ρ * 1 * ρ⁻¹ = 1 by field_simp] at h4
  have h5 := h4.sub_const 1
  rw [sub_self] at h5
  refine h5.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hRk : (R k : ℝ) ≠ 0 := by
    have := hle k
    exact_mod_cast (by omega : R k ≠ 0)
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

/-- **The transfer from the sparse times `R k` to all times.** -/
theorem king_transfer (u : ℕ → ℝ) (R : ℕ → ℕ) (ρ ℓ C' K C : ℝ)
    (hu0 : ∀ n, 0 ≤ u n) (hC' : 0 ≤ C') (hK : 0 ≤ K)
    (hR0 : R 0 = 0) (hRmono : ∀ k, R k < R (k + 1))
    (hρpos : 0 < ρ) (hρ : Tendsto (fun k : ℕ => (R k : ℝ) / k) atTop (𝓝 ρ))
    (hℓ : Tendsto (fun k : ℕ => u (R k) / (R k : ℝ)) atTop (𝓝 ℓ))
    (hup : ∀ k n, R k ≤ n → u n ≤ u (R k) + C' * ((n : ℝ) - R k) + K)
    (hlip : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ n' : ℕ, n ≤ n' → n' ≤ 2 * n →
      u n' ≤ u n + C * ((n' : ℝ) - n) + ε * n) :
    Tendsto (fun n : ℕ => u n / (n : ℝ)) atTop (𝓝 ℓ) := by
  have hle := king_le_R R hRmono
  have hgap := king_gap_ratio R ρ hρpos hρ hle
  have hRtop : Tendsto (fun k : ℕ => (R k : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_) tendsto_natCast_atTop_atTop
    exact_mod_cast hle k
  have hRpos : ∀ k : ℕ, 1 ≤ k → (0 : ℝ) < R k := by
    intro k hk
    have := hle k
    exact_mod_cast (by omega : 0 < R k)
  -- the index of the interval containing `n`
  set kk : ℕ → ℕ := fun n => Nat.findGreatest (fun k => R k ≤ n) n with hkk
  have hkk1 : ∀ n, R (kk n) ≤ n := fun n =>
    Nat.findGreatest_spec (P := fun k => R k ≤ n) (Nat.zero_le n) (by simp [hR0])
  have hkk2 : ∀ n, n < R (kk n + 1) := by
    intro n
    by_contra h
    push Not at h
    have h1 : kk n + 1 ≤ n := le_trans (hle _) h
    have h2 : kk n + 1 ≤ kk n := Nat.le_findGreatest h1 h
    omega
  have hkk_top : Tendsto kk atTop atTop := by
    refine tendsto_atTop_atTop.2 fun K0 => ⟨R K0, fun n hn => ?_⟩
    exact Nat.le_findGreatest (le_trans (hle K0) hn) hn
  -- the upper envelope
  set Up : ℕ → ℝ := fun k => u (R k) / R k + C' * (((R (k + 1) : ℝ) - R k) / R k) + K / R k
    with hUp
  have hUp_tendsto : Tendsto Up atTop (𝓝 ℓ) := by
    have h1 : Tendsto (fun k : ℕ => K / (R k : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hRtop
    have := (hℓ.add (hgap.const_mul C')).add h1
    simpa using this
  have hupper_n : ∀ n : ℕ, 1 ≤ kk n → u n / n ≤ Up (kk n) := by
    intro n hn1
    set k := kk n with hk
    have hRk : (0 : ℝ) < R k := hRpos k hn1
    have hkn : (R k : ℝ) ≤ n := by exact_mod_cast hkk1 n
    have hnlt : (n : ℝ) ≤ R (k + 1) := by exact_mod_cast (hkk2 n).le
    have hnpos : (0 : ℝ) < n := lt_of_lt_of_le hRk hkn
    have hbound := hup k n (hkk1 n)
    have hgapk : (n : ℝ) - R k ≤ (R (k + 1) : ℝ) - R k := by linarith
    have hnum : u n ≤ u (R k) + C' * ((R (k + 1) : ℝ) - R k) + K := by
      have := mul_le_mul_of_nonneg_left hgapk hC'
      linarith
    have hnum0 : 0 ≤ u (R k) + C' * ((R (k + 1) : ℝ) - R k) + K := by
      have h0 := hu0 (R k)
      have h1 : 0 ≤ C' * ((R (k + 1) : ℝ) - R k) := by
        refine mul_nonneg hC' ?_
        have : R k < R (k + 1) := hRmono k
        have : (R k : ℝ) < R (k + 1) := by exact_mod_cast this
        linarith
      linarith
    calc u n / n ≤ (u (R k) + C' * ((R (k + 1) : ℝ) - R k) + K) / n :=
          div_le_div_of_nonneg_right hnum hnpos.le
      _ ≤ (u (R k) + C' * ((R (k + 1) : ℝ) - R k) + K) / R k :=
          div_le_div_of_nonneg_left hnum0 hRk hkn
      _ = Up k := by
          rw [hUp]
          simp only
          field_simp
  -- the conclusion, bound by bound
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · -- lower bound
    set ε : ℝ := (ℓ - a) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    set Low : ℕ → ℝ := fun k =>
      u (R (k + 1)) / (R (k + 1) : ℝ) - |C| * (((R (k + 1) : ℝ) - R k) / R k) - ε with hLow
    have hLow_tendsto : Tendsto Low atTop (𝓝 (ℓ - |C| * 0 - ε)) := by
      have h1 : Tendsto (fun k : ℕ => u (R (k + 1)) / (R (k + 1) : ℝ)) atTop (𝓝 ℓ) :=
        hℓ.comp (tendsto_add_atTop_nat 1)
      exact (h1.sub (hgap.const_mul |C|)).sub_const ε
    have hLow_gt : ∀ᶠ k : ℕ in atTop, a < Low k := by
      refine hLow_tendsto.eventually (lt_mem_nhds ?_)
      rw [mul_zero, sub_zero, hε]
      linarith
    have hhalf : ∀ᶠ k : ℕ in atTop, ((R (k + 1) : ℝ) - R k) / R k ≤ 1 :=
      hgap.eventually (ge_mem_nhds (by norm_num))
    have hN := hlip ε hεpos
    filter_upwards [hkk_top.eventually hLow_gt, hkk_top.eventually hhalf, hN,
      hkk_top.eventually (eventually_ge_atTop 1)] with n hLn hhn hNn hk1
    set k := kk n with hk
    have hRk : (0 : ℝ) < R k := hRpos k hk1
    have hkn : (R k : ℝ) ≤ n := by exact_mod_cast hkk1 n
    have hnlt : (n : ℝ) ≤ R (k + 1) := by exact_mod_cast (hkk2 n).le
    have hnpos : (0 : ℝ) < n := lt_of_lt_of_le hRk hkn
    have hdk : (R (k + 1) : ℝ) ≤ 2 * R k := by
      have := (div_le_one hRk).1 hhn
      linarith
    have hn2 : R (k + 1) ≤ 2 * n := by
      have : (R (k + 1) : ℝ) ≤ 2 * n := by linarith
      exact_mod_cast this
    have hlip' := hNn (R (k + 1)) (hkk2 n).le hn2
    have hCle : C * ((R (k + 1) : ℝ) - n) ≤ |C| * ((R (k + 1) : ℝ) - R k) := by
      calc C * ((R (k + 1) : ℝ) - n) ≤ |C| * ((R (k + 1) : ℝ) - n) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
        _ ≤ |C| * ((R (k + 1) : ℝ) - R k) :=
            mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C)
    have hu1 := hu0 (R (k + 1))
    -- `u n ≥ u (R (k+1)) - |C| d - ε n`
    have hmain : u (R (k + 1)) - |C| * ((R (k + 1) : ℝ) - R k) - ε * n ≤ u n := by
      linarith
    have hdiv1 : u (R (k + 1)) / (R (k + 1) : ℝ) ≤ u (R (k + 1)) / n := by
      have hRk1 : (0 : ℝ) < R (k + 1) := lt_of_lt_of_le hnpos hnlt
      exact div_le_div_of_nonneg_left hu1 hnpos hnlt
    have hdiv2 : (|C| * ((R (k + 1) : ℝ) - R k)) / n ≤
        |C| * (((R (k + 1) : ℝ) - R k) / R k) := by
      have hd0 : (0 : ℝ) ≤ |C| * ((R (k + 1) : ℝ) - R k) := by
        refine mul_nonneg (abs_nonneg C) ?_
        have : (R k : ℝ) < R (k + 1) := by exact_mod_cast hRmono k
        linarith
      calc (|C| * ((R (k + 1) : ℝ) - R k)) / n ≤ (|C| * ((R (k + 1) : ℝ) - R k)) / R k :=
            div_le_div_of_nonneg_left hd0 hRk hkn
        _ = |C| * (((R (k + 1) : ℝ) - R k) / R k) := by ring
    have hfinal : Low k ≤ u n / n := by
      have h1 : (u (R (k + 1)) - |C| * ((R (k + 1) : ℝ) - R k) - ε * n) / n ≤ u n / n :=
        div_le_div_of_nonneg_right hmain hnpos.le
      have h2 : (u (R (k + 1)) - |C| * ((R (k + 1) : ℝ) - R k) - ε * n) / n =
          u (R (k + 1)) / n - (|C| * ((R (k + 1) : ℝ) - R k)) / n - ε := by
        field_simp
      rw [h2] at h1
      rw [hLow]
      simp only
      linarith
    exact lt_of_lt_of_le hLn hfinal
  · -- upper bound
    filter_upwards [hkk_top.eventually (hUp_tendsto.eventually (gt_mem_nhds ha)),
      hkk_top.eventually (eventually_ge_atTop 1)] with n hn hk1
    exact lt_of_le_of_lt (hupper_n n hk1) hn

end Exploding
