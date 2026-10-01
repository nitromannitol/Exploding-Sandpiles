/-
Proposition 5.1 (generalized last wave), closeness of the arrival times, part C:
a calculus for quantities bounded by a power of the logarithm.

`s3k_PL f e` says that `0 ≤ f n ≤ c (log n)^e` for `n` large, for some constant `c`.  The class is
closed under sums, products, powers and ceilings, and a quantity in the class is eventually below
`(log n)^(e+1)` and eventually below `n` after multiplication by any constant.
-/
import Exploding.Support.S3CloseB
import Exploding.Support.GLWSec3V

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

/-- `f` is bounded by a constant multiple of `(log n)^e` for `n` large. -/
def s3k_PL (f : ℕ → ℝ) (e : ℝ) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n : ℕ in atTop, 0 ≤ f n ∧ f n ≤ c * Real.log n ^ e

theorem s3k_ev_log_ge (c : ℝ) : ∀ᶠ n : ℕ in atTop, c ≤ Real.log n :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop c

theorem s3k_PL_const (c : ℝ) (hc : 0 ≤ c) : s3k_PL (fun _ => c) 0 :=
  ⟨c, hc, Eventually.of_forall fun _ => ⟨hc, by simp⟩⟩

theorem s3k_PL_mono {f : ℕ → ℝ} {e e' : ℝ} (h : s3k_PL f e) (hee : e ≤ e') : s3k_PL f e' := by
  obtain ⟨c, hc, hev⟩ := h
  refine ⟨c, hc, ?_⟩
  filter_upwards [hev, s3k_ev_log_ge 1] with n hn hL
  refine ⟨hn.1, le_trans hn.2 ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL hee) hc

theorem s3k_PL_add_same {f g : ℕ → ℝ} {e : ℝ} (hf : s3k_PL f e) (hg : s3k_PL g e) :
    s3k_PL (fun n => f n + g n) e := by
  obtain ⟨c, hc, hevf⟩ := hf
  obtain ⟨c', hc', hevg⟩ := hg
  refine ⟨c + c', by positivity, ?_⟩
  filter_upwards [hevf, hevg] with n h1 h2
  exact ⟨add_nonneg h1.1 h2.1, by nlinarith [h1.2, h2.2]⟩

theorem s3k_PL_add {f g : ℕ → ℝ} {e e' : ℝ} (hf : s3k_PL f e) (hg : s3k_PL g e') :
    s3k_PL (fun n => f n + g n) (max e e') :=
  s3k_PL_add_same (s3k_PL_mono hf (le_max_left _ _)) (s3k_PL_mono hg (le_max_right _ _))

theorem s3k_PL_mul {f g : ℕ → ℝ} {e e' : ℝ} (hf : s3k_PL f e) (hg : s3k_PL g e') :
    s3k_PL (fun n => f n * g n) (e + e') := by
  obtain ⟨c, hc, hevf⟩ := hf
  obtain ⟨c', hc', hevg⟩ := hg
  refine ⟨c * c', by positivity, ?_⟩
  filter_upwards [hevf, hevg, s3k_ev_log_ge 1] with n h1 h2 hL
  have hL0 : 0 < Real.log n := by linarith
  refine ⟨mul_nonneg h1.1 h2.1, ?_⟩
  rw [Real.rpow_add hL0]
  calc f n * g n ≤ (c * Real.log n ^ e) * (c' * Real.log n ^ e') :=
        mul_le_mul h1.2 h2.2 h2.1 (by positivity)
    _ = c * c' * (Real.log n ^ e * Real.log n ^ e') := by ring

theorem s3k_PL_pow {f : ℕ → ℝ} {e : ℝ} (hf : s3k_PL f e) (m : ℕ) :
    s3k_PL (fun n => f n ^ m) ((m : ℝ) * e) := by
  induction m with
  | zero => simpa using s3k_PL_const 1 zero_le_one
  | succ m ih =>
    have := s3k_PL_mul ih hf
    have e1 : ((m : ℝ) * e + e) = (((m + 1 : ℕ) : ℝ) * e) := by push_cast; ring
    rw [e1] at this
    simpa [pow_succ] using this

theorem s3k_PL_nsmul {f : ℕ → ℝ} {e : ℝ} (hf : s3k_PL f e) (c : ℝ) (hc : 0 ≤ c) :
    s3k_PL (fun n => c * f n) e := by
  have := s3k_PL_mul (s3k_PL_const c hc) hf
  simpa using this

/-- `log (2 n) ≤ 2 log n` once `log n ≥ 1`. -/
theorem s3k_log_two_mul_le (n : ℕ) (hn : 1 ≤ n) (hL : 1 ≤ Real.log n) :
    Real.log ((2 * n : ℕ) : ℝ) ≤ 2 * Real.log n := by
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  push_cast
  rw [Real.log_mul (by norm_num) hn0.ne']
  linarith

theorem s3k_log_two_mul_add_one_le (n : ℕ) (hn : 3 ≤ n) :
    Real.log ((2 * n + 1 : ℕ) : ℝ) ≤ 2 * Real.log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hle : ((2 * n + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    push_cast; nlinarith
  calc Real.log ((2 * n + 1 : ℕ) : ℝ) ≤ Real.log ((n : ℝ) ^ 2) :=
        Real.log_le_log (by positivity) hle
    _ = 2 * Real.log n := by rw [Real.log_pow]; push_cast; ring

theorem s3k_PL_log2 (a : ℝ) (ha : 0 ≤ a) :
    s3k_PL (fun n : ℕ => Real.log ((2 * n : ℕ) : ℝ) ^ a) a := by
  refine ⟨2 ^ a, by positivity, ?_⟩
  filter_upwards [s3k_ev_log_ge 1, eventually_ge_atTop 1] with n hL hn
  have h0 : 0 ≤ Real.log ((2 * n : ℕ) : ℝ) := Real.log_natCast_nonneg _
  refine ⟨Real.rpow_nonneg h0 a, ?_⟩
  calc Real.log ((2 * n : ℕ) : ℝ) ^ a ≤ (2 * Real.log n) ^ a :=
        Real.rpow_le_rpow h0 (s3k_log_two_mul_le n hn hL) ha
    _ = 2 ^ a * Real.log n ^ a := Real.mul_rpow (by norm_num) (by linarith)

theorem s3k_PL_log2' (a : ℝ) (ha : 0 ≤ a) :
    s3k_PL (fun n : ℕ => Real.log ((2 * n + 1 : ℕ) : ℝ) ^ a) a := by
  refine ⟨2 ^ a, by positivity, ?_⟩
  filter_upwards [s3k_ev_log_ge 1, eventually_ge_atTop 3] with n hL hn
  have h0 : 0 ≤ Real.log ((2 * n + 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
  refine ⟨Real.rpow_nonneg h0 a, ?_⟩
  calc Real.log ((2 * n + 1 : ℕ) : ℝ) ^ a ≤ (2 * Real.log n) ^ a :=
        Real.rpow_le_rpow h0 (s3k_log_two_mul_add_one_le n hn) ha
    _ = 2 ^ a * Real.log n ^ a := Real.mul_rpow (by norm_num) (by linarith)

theorem s3k_PL_logn (a : ℝ) (_ha : 0 ≤ a) : s3k_PL (fun n : ℕ => Real.log n ^ a) a := by
  refine ⟨1, zero_le_one, ?_⟩
  filter_upwards [s3k_ev_log_ge 1] with n hL
  exact ⟨Real.rpow_nonneg (by linarith) a, by simp⟩

/-- The ceiling of a quantity of the class is in the class. -/
theorem s3k_PL_ceil {f : ℕ → ℝ} {e : ℝ} (hf : s3k_PL f e) (he : 0 ≤ e) :
    s3k_PL (fun n => ((⌈f n⌉₊ : ℕ) : ℝ)) e := by
  obtain ⟨c, hc, hev⟩ := hf
  refine ⟨c + 1, by positivity, ?_⟩
  filter_upwards [hev, s3k_ev_log_ge 1] with n h1 hL
  refine ⟨Nat.cast_nonneg _, ?_⟩
  have hceil : ((⌈f n⌉₊ : ℕ) : ℝ) < f n + 1 := Nat.ceil_lt_add_one h1.1
  have hone : (1 : ℝ) ≤ Real.log n ^ e := Real.one_le_rpow hL he
  nlinarith [h1.2, hceil, hone]

/-- A quantity of the class is eventually at most `(log n)^(e+1)`. -/
theorem s3k_PL_le {f : ℕ → ℝ} {e : ℝ} (hf : s3k_PL f e) :
    ∀ᶠ n : ℕ in atTop, f n ≤ Real.log n ^ (e + 1) := by
  obtain ⟨c, hc, hev⟩ := hf
  filter_upwards [hev, s3k_ev_log_ge (max c 1)] with n h1 hL
  have hL1 : 1 ≤ Real.log n := le_trans (le_max_right _ _) hL
  have hcL : c ≤ Real.log n := le_trans (le_max_left _ _) hL
  have hL0 : 0 < Real.log n := by linarith
  rw [Real.rpow_add_one hL0.ne']
  calc f n ≤ c * Real.log n ^ e := h1.2
    _ ≤ Real.log n * Real.log n ^ e :=
        mul_le_mul_of_nonneg_right hcL (Real.rpow_nonneg hL0.le e)
    _ = Real.log n ^ e * Real.log n := by ring

/-- A quantity of the class is eventually small against `n`, with any constant. -/
theorem s3k_PL_le_n {f : ℕ → ℝ} {e : ℝ} (hf : s3k_PL f e) (c0 : ℝ) (hc0 : 0 ≤ c0) :
    ∀ᶠ n : ℕ in atTop, c0 * f n ≤ (n : ℝ) := by
  obtain ⟨c, hc, hev⟩ := hf
  filter_upwards [hev, glws_eventually_polylog_le e (c0 * c)] with n h1 h2
  calc c0 * f n ≤ c0 * (c * Real.log n ^ e) := mul_le_mul_of_nonneg_left h1.2 hc0
    _ = c0 * c * Real.log n ^ e := by ring
    _ ≤ n := h2

end Exploding
