/-
A sequence with the doubling recursion `a s ≤ C * a (s / 2) ^ 2` and `C * a s ≤ 1 / 2` from the
scale `s0` on decays exponentially: halving the scale `j` times, as long as the scale stays
above `s0`, squares the bound `C * a` `2^j` times, and `2^j` is of the order of `s / s0`.
-/
import Mathlib

namespace Exploding

/-- Halving the scale `j` times, as long as it stays above `s0`, raises the bound to the
power `2^j`. -/
theorem xse_iterate (b : ℕ → ℝ) (hb0 : ∀ s, 0 ≤ b s)
    (hb : ∀ s, 2 ≤ s → b s ≤ b (s / 2) ^ 2) (s0 : ℕ) (hs0 : 1 ≤ s0) :
    ∀ j s : ℕ, s0 ≤ s / 2 ^ j → b s ≤ b (s / 2 ^ j) ^ (2 ^ j) := by
  intro j
  induction j with
  | zero => intro s _; simp
  | succ j ih =>
    intro s hs
    have hdiv : s / 2 ^ (j + 1) = s / 2 / 2 ^ j := by
      rw [pow_succ', Nat.div_div_eq_div_mul]
    have hle : 2 ^ (j + 1) * s0 ≤ s := by
      have := (Nat.le_div_iff_mul_le (by positivity)).1 hs
      rwa [mul_comm]
    have h2 : 2 ≤ s := by
      have : 2 ≤ 2 ^ (j + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      nlinarith
    rw [hdiv] at hs ⊢
    calc b s ≤ b (s / 2) ^ 2 := hb s h2
      _ ≤ (b (s / 2 / 2 ^ j) ^ (2 ^ j)) ^ 2 :=
          pow_le_pow_left₀ (hb0 _) (ih (s / 2) hs) 2
      _ = b (s / 2 / 2 ^ j) ^ (2 ^ (j + 1)) := by rw [← pow_mul, pow_succ]

/-- For `s0 ≤ s`, there is a level `J` with `s / 2^J` still above `s0` and `s / 2^(J+1)` below. -/
theorem xse_level (s s0 : ℕ) (hs0 : 1 ≤ s0) (h : s0 ≤ s) :
    ∃ J : ℕ, s0 ≤ s / 2 ^ J ∧ s / 2 ^ (J + 1) < s0 := by
  have hex : ∃ j : ℕ, s / 2 ^ j < s0 :=
    ⟨s, by rw [Nat.div_eq_of_lt Nat.lt_two_pow_self]; omega⟩
  have hN : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0] at this
    simp only [pow_zero, Nat.div_one] at this
    omega
  obtain ⟨J, hJ⟩ := Nat.exists_eq_succ_of_ne_zero hN
  refine ⟨J, ?_, ?_⟩
  · have := Nat.find_min hex (show J < Nat.find hex by omega)
    omega
  · have := Nat.find_spec hex
    rwa [hJ] at this

/-- The tail bound: from the scale `s0` on, `b s ≤ exp (-(log 2 / (2 * s0) * s))`. -/
theorem xse_tail (b : ℕ → ℝ) (hb0 : ∀ s, 0 ≤ b s)
    (hb : ∀ s, 2 ≤ s → b s ≤ b (s / 2) ^ 2) (s0 : ℕ) (hs0 : 1 ≤ s0)
    (hbase : ∀ s, s0 ≤ s → b s ≤ 1 / 2) (s : ℕ) (hs : s0 ≤ s) :
    b s ≤ Real.exp (-(Real.log 2 / (2 * (s0 : ℝ)) * (s : ℝ))) := by
  obtain ⟨J, hJ1, hJ2⟩ := xse_level s s0 hs0 hs
  have h1 : b s ≤ (1 / 2 : ℝ) ^ (2 ^ J) :=
    calc b s ≤ b (s / 2 ^ J) ^ (2 ^ J) := xse_iterate b hb0 hb s0 hs0 J s hJ1
      _ ≤ (1 / 2 : ℝ) ^ (2 ^ J) :=
          pow_le_pow_left₀ (hb0 _) (hbase _ hJ1) _
  have h2 : (s : ℝ) ≤ 2 * (s0 : ℝ) * 2 ^ J := by
    have : s < s0 * 2 ^ (J + 1) := (Nat.div_lt_iff_lt_mul (by positivity)).1 hJ2
    have h' : (s : ℝ) < (s0 : ℝ) * 2 ^ (J + 1) := by exact_mod_cast this
    rw [pow_succ] at h'
    nlinarith
  have h3 : (1 / 2 : ℝ) ^ (2 ^ J) = Real.exp (-(((2 ^ J : ℕ) : ℝ) * Real.log 2)) := by
    rw [Real.exp_neg, ← mul_comm, mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    simp
  refine h1.trans ?_
  rw [h3, Real.exp_le_exp, neg_le_neg_iff]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs0' : (0 : ℝ) < s0 := by exact_mod_cast hs0
  push_cast
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  calc Real.log 2 * (s : ℝ) ≤ Real.log 2 * (2 * (s0 : ℝ) * 2 ^ J) :=
        mul_le_mul_of_nonneg_left h2 hlog.le
    _ = 2 ^ J * Real.log 2 * (2 * (s0 : ℝ)) := by ring

/-- **Exponential decay from a doubling recursion and a base scale.** -/
theorem xse_exp_of_recursion (a : ℕ → ℝ) (C : ℝ) (hC : 1 ≤ C) (ha0 : ∀ s, 0 ≤ a s)
    (hrec : ∀ s, 2 ≤ s → a s ≤ C * a (s / 2) ^ 2) (s0 : ℕ) (hs0 : 1 ≤ s0)
    (hbase : ∀ s, s0 ≤ s → C * a s ≤ 1 / 2) :
    ∃ c c' : ℝ, 0 < c ∧ 0 < c' ∧ ∀ s : ℕ, 1 ≤ s → a s ≤ c * Real.exp (-(c' * (s : ℝ))) := by
  have hC0 : 0 < C := by linarith
  have hb0 : ∀ s, 0 ≤ C * a s := fun s => mul_nonneg hC0.le (ha0 s)
  have hb : ∀ s, 2 ≤ s → C * a s ≤ (C * a (s / 2)) ^ 2 := by
    intro s hs
    calc C * a s ≤ C * (C * a (s / 2) ^ 2) := mul_le_mul_of_nonneg_left (hrec s hs) hC0.le
      _ = (C * a (s / 2)) ^ 2 := by ring
  have htail := xse_tail (fun s => C * a s) hb0 hb s0 hs0 hbase
  have hs0' : (0 : ℝ) < s0 := by exact_mod_cast hs0
  have hc' : 0 < Real.log 2 / (2 * (s0 : ℝ)) :=
    div_pos (Real.log_pos (by norm_num)) (by positivity)
  set c' : ℝ := Real.log 2 / (2 * (s0 : ℝ)) with hc'def
  set M : ℝ := ∑ s ∈ Finset.range s0, a s * Real.exp (c' * (s : ℝ)) with hM
  refine ⟨max 1 (M + 1), c', lt_max_of_lt_left one_pos, hc', ?_⟩
  intro s _
  have hexp : 0 < Real.exp (-(c' * (s : ℝ))) := Real.exp_pos _
  by_cases h : s0 ≤ s
  · calc a s ≤ C * a s := by nlinarith [ha0 s]
      _ ≤ Real.exp (-(c' * (s : ℝ))) := htail s h
      _ ≤ max 1 (M + 1) * Real.exp (-(c' * (s : ℝ))) :=
          le_mul_of_one_le_left hexp.le (le_max_left _ _)
  · have hlt : s < s0 := not_le.1 h
    have hterm : a s * Real.exp (c' * (s : ℝ)) ≤ M :=
      Finset.single_le_sum (f := fun s : ℕ => a s * Real.exp (c' * (s : ℝ)))
        (fun i _ => mul_nonneg (ha0 i) (Real.exp_pos _).le) (Finset.mem_range.2 hlt)
    have hmax : M ≤ max 1 (M + 1) := (by linarith : M ≤ M + 1).trans (le_max_right _ _)
    calc a s = a s * Real.exp (c' * (s : ℝ)) * Real.exp (-(c' * (s : ℝ))) := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ M * Real.exp (-(c' * (s : ℝ))) := mul_le_mul_of_nonneg_right hterm hexp.le
      _ ≤ max 1 (M + 1) * Real.exp (-(c' * (s : ℝ))) :=
          mul_le_mul_of_nonneg_right hmax hexp.le

end Exploding
