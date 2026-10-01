/-
Proposition 5.1 of the paper (generalized last wave): the length of the lit paths and the first lit
tile of the last wave.

`glws_Pn` is the number of sites of a lit path needed at scale `2n` for path-filling and for a long
side that contains a row of more than `(log 2n)^{5/2}` macroscopic sites; it is polylogarithmic.  The
last wave, not stabilizing, has unbounded support, whence a lit path of `glws_Pn` sites and a lit
tile of the cluster.
-/
import Exploding.Support.GLWSec3U

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

/-- The length of the rows of macroscopic sites searched at scale `2 n`. -/
noncomputable def glws_r2 (n : ℕ) : ℕ := ⌈Real.log ((2 * n + 1 : ℕ) : ℝ) ^ ((5 : ℝ) / 2)⌉₊

/-- The number of sites of the lit paths at scale `2 n`. -/
noncomputable def glws_Pn (γp : ℝ) (kmax d n : ℕ) : ℕ :=
  (kmax * (glws_r2 n + 2)) ^ d + ⌈Real.log ((2 * n : ℕ) : ℝ) ^ γp⌉₊

/-- A power of the logarithm is eventually below `n`, with any constant. -/
theorem glws_eventually_polylog_le (a c : ℝ) :
    ∀ᶠ n : ℕ in atTop, c * Real.log n ^ a ≤ (n : ℝ) := by
  have h := lwc_transfer_4 a 1 one_pos
  simp only [Nat.cast_one, one_mul] at h
  have hc : (0 : ℝ) < 1 / (|c| + 1) := by positivity
  filter_upwards [h.eventually_le_const hc, eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
    with n hn hn1 hL1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hL1' : 1 ≤ Real.log n := hL1
  rw [div_le_iff₀ hnpos] at hn
  have hLa : 0 ≤ Real.log n ^ a := Real.rpow_nonneg (by linarith) _
  have h1 : c * Real.log n ^ a ≤ |c| * Real.log n ^ a :=
    mul_le_mul_of_nonneg_right (le_abs_self c) hLa
  have h2 : Real.log n ^ a * (|c| + 1) ≤ n := by
    have := hn
    rw [show 1 / (|c| + 1) * (n : ℝ) = (n : ℝ) / (|c| + 1) by ring, le_div_iff₀ (by positivity)] at this
    exact this
  nlinarith [abs_nonneg c]

/-- `glws_Pn` is at most `n`, for `n` large. -/
theorem glws_asymp_Pn (γp : ℝ) (hγp : 0 < γp) (kmax d : ℕ) :
    ∃ n1 : ℕ, ∀ n : ℕ, n1 ≤ n → 3 ≤ n ∧ glws_Pn γp kmax d n ≤ n := by
  set c0 : ℝ := (2 : ℝ) ^ ((5 : ℝ) / 2) + 3 with hc0
  set c1 : ℝ := ((kmax : ℝ) * c0) ^ d with hc1
  set c2 : ℝ := (2 : ℝ) ^ γp with hc2
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨n1, hn1⟩ := eventually_atTop.mp ((glws_eventually_polylog_le ((5 : ℝ) / 2 * d) (3 * c1)).and
    (((glws_eventually_polylog_le γp (3 * c2)).and
    ((hlog.eventually_ge_atTop 1).and (eventually_ge_atTop 3)))))
  refine ⟨n1, fun n hn => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hn1 n hn
  refine ⟨h4, ?_⟩
  set L := Real.log n with hL
  have hL0 : 0 < L := by linarith
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast h4
  have hlog2n : Real.log ((2 * n + 1 : ℕ) : ℝ) ≤ 2 * L := by
    have hle : ((2 * n + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
      push_cast; nlinarith
    calc Real.log ((2 * n + 1 : ℕ) : ℝ) ≤ Real.log ((n : ℝ) ^ 2) :=
          Real.log_le_log (by positivity) hle
      _ = 2 * L := by rw [Real.log_pow]; push_cast; ring
  have hlog2n' : Real.log ((2 * n : ℕ) : ℝ) ≤ 2 * L := by
    have hle : ((2 * n : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
      push_cast; nlinarith
    calc Real.log ((2 * n : ℕ) : ℝ) ≤ Real.log ((n : ℝ) ^ 2) :=
          Real.log_le_log (by positivity) hle
      _ = 2 * L := by rw [Real.log_pow]; push_cast; ring
  have hlog_nn1 : 0 ≤ Real.log ((2 * n + 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hlog_nn2 : 0 ≤ Real.log ((2 * n : ℕ) : ℝ) := Real.log_natCast_nonneg _
  -- the row length
  have hr2 : (glws_r2 n : ℝ) + 2 ≤ c0 * L ^ ((5 : ℝ) / 2) := by
    have e1 : (glws_r2 n : ℝ) ≤ Real.log ((2 * n + 1 : ℕ) : ℝ) ^ ((5 : ℝ) / 2) + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    have e2 : Real.log ((2 * n + 1 : ℕ) : ℝ) ^ ((5 : ℝ) / 2) ≤ (2 * L) ^ ((5 : ℝ) / 2) :=
      Real.rpow_le_rpow hlog_nn1 hlog2n (by norm_num)
    have e3 : (2 * L) ^ ((5 : ℝ) / 2) = 2 ^ ((5 : ℝ) / 2) * L ^ ((5 : ℝ) / 2) :=
      Real.mul_rpow (by norm_num) hL0.le
    have e4 : (1 : ℝ) ≤ L ^ ((5 : ℝ) / 2) := Real.one_le_rpow h3 (by norm_num)
    rw [hc0]
    nlinarith [e1, e2, e3, e4]
  have hk0 : (0 : ℝ) ≤ (kmax : ℝ) := Nat.cast_nonneg _
  have hmain : (((kmax * (glws_r2 n + 2)) ^ d : ℕ) : ℝ) ≤ c1 * L ^ ((5 : ℝ) / 2 * d) := by
    have e1 : (((kmax * (glws_r2 n + 2) : ℕ) : ℝ)) ≤ (kmax : ℝ) * c0 * L ^ ((5 : ℝ) / 2) := by
      push_cast
      calc (kmax : ℝ) * ((glws_r2 n : ℝ) + 2) ≤ (kmax : ℝ) * (c0 * L ^ ((5 : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hr2 hk0
        _ = (kmax : ℝ) * c0 * L ^ ((5 : ℝ) / 2) := by ring
    push_cast
    calc ((kmax : ℝ) * ((glws_r2 n : ℝ) + 2)) ^ d
        ≤ ((kmax : ℝ) * c0 * L ^ ((5 : ℝ) / 2)) ^ d := by
          apply pow_le_pow_left₀ (by positivity)
          push_cast at e1
          exact e1
      _ = ((kmax : ℝ) * c0) ^ d * (L ^ ((5 : ℝ) / 2)) ^ d := mul_pow _ _ _
      _ = c1 * L ^ ((5 : ℝ) / 2 * d) := by
          rw [hc1]
          congr 1
          rw [← Real.rpow_natCast (L ^ ((5 : ℝ) / 2)) d, ← Real.rpow_mul hL0.le]
  have hcl : ((⌈Real.log ((2 * n : ℕ) : ℝ) ^ γp⌉₊ : ℕ) : ℝ) ≤ c2 * L ^ γp + 1 := by
    have e1 : ((⌈Real.log ((2 * n : ℕ) : ℝ) ^ γp⌉₊ : ℕ) : ℝ) ≤
        Real.log ((2 * n : ℕ) : ℝ) ^ γp + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have e2 : Real.log ((2 * n : ℕ) : ℝ) ^ γp ≤ (2 * L) ^ γp :=
      Real.rpow_le_rpow hlog_nn2 hlog2n' hγp.le
    have e3 : (2 * L) ^ γp = 2 ^ γp * L ^ γp := Real.mul_rpow (by norm_num) hL0.le
    rw [hc2]
    linarith
  unfold glws_Pn
  have : (((kmax * (glws_r2 n + 2)) ^ d + ⌈Real.log ((2 * n : ℕ) : ℝ) ^ γp⌉₊ : ℕ) : ℝ) ≤ n := by
    push_cast at hmain hcl ⊢
    have hc1n : 0 ≤ c1 := by rw [hc1]; positivity
    have hc2n : 0 ≤ c2 := by rw [hc2]; positivity
    linarith
  exact_mod_cast this

end Exploding
