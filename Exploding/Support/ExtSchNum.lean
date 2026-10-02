/-
The arithmetic of one step of the induction on the number of directions: a sequence decaying
faster than any polynomial is summable with a tail below `1/(2k)` from some index on, and the
bound `(1 - π)^N + N k Σ g`, with `N` the number of blocks of side `⌊√s⌋ + 1` in a box of side
`s`, again decays faster than any polynomial.
-/
import Mathlib

namespace Exploding

/-- The inverse squares over a final segment `[L, M]` of the positive integers sum to at most
`2 / L`. -/
theorem xsn_inv_sq_tail (L M : ℕ) (hL : 1 ≤ L) :
    ∑ a ∈ Finset.Icc L M, ((a : ℝ) ^ 2)⁻¹ ≤ 2 / (L : ℝ) := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  rcases le_or_gt L M with h | h
  · rw [Finset.Icc_eq_cons_Ioc h, Finset.sum_cons]
    have h1 := sum_Ioc_inv_sq_le_sub (α := ℝ) (Nat.pos_iff_ne_zero.mp hL) h
    have h2 : ((L : ℝ) ^ 2)⁻¹ ≤ (L : ℝ)⁻¹ := by
      apply inv_anti₀ hL0
      nlinarith
    have h3 : 0 ≤ ((M : ℝ))⁻¹ := by positivity
    rw [div_eq_mul_inv]
    linarith
  · rw [Finset.Icc_eq_empty_of_lt h, Finset.sum_empty]
    positivity

/-- The tail of a sequence bounded by `c / a ^ (j + 2)` from index `1` on sums, over `[L, M]`
with `1 ≤ L`, to at most `2 c / L ^ (j + 1)`. -/
theorem xsn_tail_sum (g : ℕ → ℝ) (j : ℕ) (c : ℝ) (hc : 0 < c)
    (hg : ∀ a : ℕ, 1 ≤ a → g a ≤ c / (a : ℝ) ^ (j + 2)) (L M : ℕ) (hL : 1 ≤ L) :
    ∑ a ∈ Finset.Icc L M, g a ≤ 2 * c / (L : ℝ) ^ (j + 1) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hLj : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have key : ∀ a ∈ Finset.Icc L M, g a ≤ c / (L : ℝ) ^ j * ((a : ℝ) ^ 2)⁻¹ := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    have ha1 : 1 ≤ a := le_trans hL ha.1
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
    have hLa : (L : ℝ) ^ j ≤ (a : ℝ) ^ j := by
      have : (L : ℝ) ≤ a := by exact_mod_cast ha.1
      gcongr
    calc g a ≤ c / (a : ℝ) ^ (j + 2) := hg a ha1
      _ = c / ((a : ℝ) ^ j * (a : ℝ) ^ 2) := by rw [pow_add]
      _ ≤ c / ((L : ℝ) ^ j * (a : ℝ) ^ 2) := by
        apply div_le_div_of_nonneg_left hc.le (by positivity)
        gcongr
      _ = c / (L : ℝ) ^ j * ((a : ℝ) ^ 2)⁻¹ := by
        rw [div_eq_mul_inv, mul_inv, ← mul_assoc, div_eq_mul_inv]
  calc ∑ a ∈ Finset.Icc L M, g a
      ≤ ∑ a ∈ Finset.Icc L M, c / (L : ℝ) ^ j * ((a : ℝ) ^ 2)⁻¹ := Finset.sum_le_sum key
    _ = c / (L : ℝ) ^ j * ∑ a ∈ Finset.Icc L M, ((a : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ c / (L : ℝ) ^ j * (2 / (L : ℝ)) :=
        mul_le_mul_of_nonneg_left (xsn_inv_sq_tail L M hL) (by positivity)
    _ = 2 * c / (L : ℝ) ^ (j + 1) := by
        rw [pow_succ]
        field_simp

/-- The geometric sequence `(1 - π) ^ m` decays faster than any polynomial in `m`. -/
theorem xsn_geom_poly (π : ℝ) (hπ0 : 0 < π) (hπ1 : π < 1) (K : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 1 ≤ m → (1 - π) ^ m ≤ c / (m : ℝ) ^ K := by
  have hr : |1 - π| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  obtain ⟨B, hB⟩ := (tendsto_pow_const_mul_const_pow_of_abs_lt_one K hr).bddAbove_range
  refine ⟨max B 1, lt_max_of_lt_right one_pos, fun m hm => ?_⟩
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmK : (0 : ℝ) < (m : ℝ) ^ K := by positivity
  have h1 : (m : ℝ) ^ K * (1 - π) ^ m ≤ max B 1 := le_max_of_le_left (hB ⟨m, rfl⟩)
  rw [le_div_iff₀ hmK]
  linarith [mul_comm ((m : ℝ) ^ K) ((1 - π) ^ m)]

/-- Facts about `r = ⌊√s⌋` and the number `s / (r + 1)` of blocks along one direction. -/
theorem xsn_sqrt_facts (s : ℕ) :
    Nat.sqrt s ^ 2 ≤ s ∧ s < (Nat.sqrt s + 1) ^ 2 ∧
      Nat.sqrt s - 1 ≤ s / (Nat.sqrt s + 1) ∧ s / (Nat.sqrt s + 1) ≤ Nat.sqrt s := by
  have h1 := Nat.sqrt_le' s
  have h2 := Nat.lt_succ_sqrt' s
  generalize Nat.sqrt s = r at h1 h2 ⊢
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [Nat.le_div_iff_mul_le (Nat.succ_pos r)]
    rcases r with _ | r
    · simp
    · simp only [Nat.add_sub_cancel]
      nlinarith
  · refine Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (Nat.succ_pos r)).2 ?_)
    nlinarith

/-- The seed size: the tail of the decaying sequence is small. -/
theorem xsn_exists_seed_size (k : ℕ) (g : ℕ → ℝ) (_hg0 : ∀ a, 0 ≤ g a)
    (hg : ∀ Q : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ a : ℕ, 1 ≤ a → g a ≤ c / (a : ℝ) ^ Q) :
    ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ∀ M : ℕ, (k : ℝ) * ∑ a ∈ Finset.Icc ℓ M, g a ≤ 1 / 2 := by
  obtain ⟨c, hc, hgc⟩ := hg 2
  refine ⟨⌈6 * k * c⌉₊ + 1, Nat.succ_pos _, fun M => ?_⟩
  have hℓ : (6 * k * c : ℝ) < ((⌈6 * k * c⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast
    linarith [Nat.le_ceil (6 * (k : ℝ) * c)]
  have hℓ0 : (0 : ℝ) < ((⌈6 * k * c⌉₊ + 1 : ℕ) : ℝ) := by positivity
  have htail := xsn_tail_sum g 0 c hc (fun a ha => by simpa using hgc a ha)
    (⌈6 * k * c⌉₊ + 1) M (Nat.succ_pos _)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc (k : ℝ) * ∑ a ∈ Finset.Icc (⌈6 * k * c⌉₊ + 1) M, g a
      ≤ k * (2 * c / (((⌈6 * k * c⌉₊ + 1 : ℕ) : ℝ)) ^ (0 + 1)) :=
        mul_le_mul_of_nonneg_left htail hk0
    _ ≤ 1 / 2 := by
        rw [zero_add, pow_one, ← mul_div_assoc, div_le_iff₀ hℓ0]
        nlinarith

/-- One step of the induction: the failure bound again decays faster than any polynomial. -/
theorem xsn_decay_step (k : ℕ) (hk : 1 ≤ k) (π : ℝ) (hπ0 : 0 < π) (hπ1 : π < 1)
    (g : ℕ → ℝ) (hg0 : ∀ a, 0 ≤ g a)
    (hg : ∀ Q : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ a : ℕ, 1 ≤ a → g a ≤ c / (a : ℝ) ^ Q) (Q : ℕ) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ s : ℕ, 1 ≤ s →
      min 1 ((1 - π) ^ ((s / (Nat.sqrt s + 1)) ^ k) +
        (((s / (Nat.sqrt s + 1)) ^ k : ℕ) : ℝ) *
          ((k : ℝ) * ∑ a ∈ Finset.Icc (Nat.sqrt s + 1) s, g a)) ≤ c' / (s : ℝ) ^ Q := by
  obtain ⟨c₀, hc₀, hgeom⟩ := xsn_geom_poly π hπ0 hπ1 (2 * Q)
  obtain ⟨c, hc, hgc⟩ := hg (k + 2 * Q + 2)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨16 ^ Q + c₀ * 4 ^ Q + 2 * c * k, by positivity, fun s hs => ?_⟩
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hspow : (0 : ℝ) < (s : ℝ) ^ Q := by positivity
  rcases lt_or_ge s 16 with h16 | h16
  · refine (min_le_left _ _).trans ?_
    rw [le_div_iff₀ hspow]
    have h1 : (s : ℝ) ^ Q ≤ 16 ^ Q := by
      have : (s : ℝ) ≤ 16 := by exact_mod_cast h16.le
      gcongr
    have h2 : (0 : ℝ) ≤ c₀ * 4 ^ Q + 2 * c * k := by positivity
    linarith
  · refine (min_le_right _ _).trans ?_
    obtain ⟨hr1, hr2, hr3, hr4⟩ := xsn_sqrt_facts s
    generalize Nat.sqrt s = r at hr1 hr2 hr3 hr4 ⊢
    have hr : 4 ≤ r := by
      by_contra h
      have : r + 1 ≤ 4 := by omega
      nlinarith
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    have hm : 3 ≤ m := by omega
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hN : m ≤ (s / (m + 1 + 1)) ^ k := by
      refine le_trans ?_ (Nat.le_self_pow (by omega) _)
      simpa using hr3
    -- the first term
    have hs4 : s ≤ 4 * m ^ 2 := by nlinarith
    have hs4' : (s : ℝ) ^ Q ≤ 4 ^ Q * (m : ℝ) ^ (2 * Q) := by
      have h1 : (s : ℝ) ≤ 4 * (m : ℝ) ^ 2 := by exact_mod_cast hs4
      calc (s : ℝ) ^ Q ≤ (4 * (m : ℝ) ^ 2) ^ Q := pow_le_pow_left₀ hs0.le h1 Q
        _ = 4 ^ Q * (m : ℝ) ^ (2 * Q) := by rw [mul_pow, ← pow_mul]
    have hx1 : (1 - π) ^ ((s / (m + 1 + 1)) ^ k) ≤ c₀ * 4 ^ Q / (s : ℝ) ^ Q := by
      calc (1 - π) ^ ((s / (m + 1 + 1)) ^ k) ≤ (1 - π) ^ m :=
            pow_le_pow_of_le_one (by linarith) (by linarith) hN
        _ ≤ c₀ / (m : ℝ) ^ (2 * Q) := hgeom m (by omega)
        _ ≤ c₀ * 4 ^ Q / (s : ℝ) ^ Q := by
            rw [div_le_div_iff₀ (by positivity) hspow]
            calc c₀ * (s : ℝ) ^ Q ≤ c₀ * (4 ^ Q * (m : ℝ) ^ (2 * Q)) :=
                  mul_le_mul_of_nonneg_left hs4' hc₀.le
              _ = c₀ * 4 ^ Q * (m : ℝ) ^ (2 * Q) := by ring
    -- the second term
    have hR : (1 : ℝ) ≤ (m : ℝ) + 1 + 1 := by linarith
    have hN2 : (((s / (m + 1 + 1)) ^ k : ℕ) : ℝ) ≤ ((m : ℝ) + 1 + 1) ^ k := by
      have : (s / (m + 1 + 1)) ^ k ≤ (m + 1 + 1) ^ k := Nat.pow_le_pow_left (by omega) k
      exact_mod_cast this
    have htail := xsn_tail_sum g (k + 2 * Q) c hc (fun a ha => hgc a ha) (m + 1 + 1) s
      (by omega)
    push_cast at htail
    have hsR : (s : ℝ) ^ Q ≤ ((m : ℝ) + 1 + 1) ^ (2 * Q + 1) := by
      have h1 : (s : ℝ) ≤ ((m : ℝ) + 1 + 1) ^ 2 := by exact_mod_cast hr2.le
      calc (s : ℝ) ^ Q ≤ (((m : ℝ) + 1 + 1) ^ 2) ^ Q := pow_le_pow_left₀ hs0.le h1 Q
        _ = ((m : ℝ) + 1 + 1) ^ (2 * Q) := by rw [← pow_mul]
        _ ≤ ((m : ℝ) + 1 + 1) ^ (2 * Q + 1) := pow_le_pow_right₀ hR (Nat.le_succ _)
    have hsum : 0 ≤ (k : ℝ) * ∑ a ∈ Finset.Icc (m + 1 + 1) s, g a :=
      mul_nonneg hk0.le (Finset.sum_nonneg fun a _ => hg0 a)
    have hx2 : (((s / (m + 1 + 1)) ^ k : ℕ) : ℝ) *
        ((k : ℝ) * ∑ a ∈ Finset.Icc (m + 1 + 1) s, g a) ≤ 2 * c * k / (s : ℝ) ^ Q := by
      calc (((s / (m + 1 + 1)) ^ k : ℕ) : ℝ) *
            ((k : ℝ) * ∑ a ∈ Finset.Icc (m + 1 + 1) s, g a)
          ≤ ((m : ℝ) + 1 + 1) ^ k *
            ((k : ℝ) * (2 * c / ((m : ℝ) + 1 + 1) ^ (k + 2 * Q + 1))) :=
            mul_le_mul hN2 (mul_le_mul_of_nonneg_left htail hk0.le) hsum (by positivity)
        _ = 2 * c * k / ((m : ℝ) + 1 + 1) ^ (2 * Q + 1) := by
            rw [show k + 2 * Q + 1 = k + (2 * Q + 1) by ring, pow_add]
            field_simp
        _ ≤ 2 * c * k / (s : ℝ) ^ Q := div_le_div_of_nonneg_left (by positivity) hspow hsR
    refine (add_le_add hx1 hx2).trans ?_
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hspow.le
    have : (0 : ℝ) ≤ 16 ^ Q := by positivity
    linarith

end Exploding
