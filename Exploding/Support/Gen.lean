/-
Support lemmas for the assembly of Theorem 5.2 and Theorem 1.3: the nearest
lattice point is within one of the point it rounds, and the arithmetic that
combines a locally uniform estimate with an `o(n)` estimate.
-/
import Exploding.Support.Vocab

namespace Exploding

open LatticeProb MeasureTheory Filter

variable {d : ℕ}

/-- The nearest lattice point to `y` is within `1` of `y` in every coordinate. -/
theorem Gen.nearestSite_sub_le (y : Fin d → ℝ) (i : Fin d) :
    |(nearestSite y i : ℝ) - y i| ≤ 1 := by
  simp only [nearestSite]
  rw [abs_sub_le_iff]
  constructor
  · have h := Int.ceil_lt_add_one (y i - 1/2)
    linarith
  · have h := Int.le_ceil (y i - 1/2)
    linarith

/-- If every coordinate of `y` is bounded by `m`, then every coordinate of
`nearestSite y` is bounded by `m + 1`. -/
theorem Gen.nearestSite_abs_le (y : Fin d → ℝ) (m : ℤ) (h : ∀ i, |y i| ≤ (m : ℝ))
    (i : Fin d) : |nearestSite y i| ≤ m + 1 := by
  rw [abs_le]
  constructor
  · have hy := (abs_le.mp (h i)).1
    simp only [nearestSite]
    have hlt : ((-(m + 1) - 1 : ℤ) : ℝ) < y i - 1 / 2 := by
      push_cast
      linarith
    have : (-(m + 1) - 1 : ℤ) < ⌈y i - 1 / 2⌉ := by
      rw [Int.lt_ceil]
      exact hlt
    omega
  · have hy := (abs_le.mp (h i)).2
    simp only [nearestSite]
    rw [Int.ceil_le]
    push_cast
    linarith

/-- Dividing a difference by a positive `n` divides its absolute value by `n`. -/
theorem Gen.div_sub_div_abs_le (a b c : ℝ) (n : ℕ) (hn : 0 < n)
    (h : |a - b| ≤ c * (n : ℝ)) : |a / (n : ℝ) - b / (n : ℝ)| ≤ c := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [← sub_div, abs_div, abs_of_pos hn']
  rw [div_le_iff₀ hn']
  exact h

/-- The triangle inequality in the form used to combine the last-wave estimate
with the wave-approximation estimate. -/
theorem Gen.abs_sub_le_of_le (a b c x y : ℝ) (h1 : |a - b| ≤ x) (h2 : |b - c| ≤ y) :
    |a - c| ≤ x + y := by
  have h := abs_sub_le a b c
  linarith

/-- A compact subset of `ℝ^d` is contained in a coordinate box of natural side
length. -/
theorem Gen.exists_nat_bound_of_isCompact {K : Set (Fin d → ℝ)} (hK : IsCompact K) :
    ∃ C : ℕ, ∀ y ∈ K, ∀ i, |y i| ≤ (C : ℝ) := by
  obtain ⟨R, hR⟩ := Bornology.IsBounded.exists_norm_le (IsCompact.isBounded hK)
  refine ⟨⌈max R 0⌉₊, fun y hy i => ?_⟩
  have h1 : ‖y i‖ ≤ ‖y‖ := norm_le_pi_norm y i
  have h2 : ‖y‖ ≤ R := hR y hy
  have h3 : |y i| ≤ R := by
    rw [← Real.norm_eq_abs]
    linarith
  have h4 : R ≤ (⌈max R 0⌉₊ : ℝ) := le_trans (le_max_left _ _) (Nat.le_ceil _)
  linarith

/-- If every coordinate of `y` is bounded by `C`, then `nearestSite (n • y)` lies
in the coordinate box of side length `n * (C + 1) + 1`. -/
theorem Gen.nearestSite_smul_mem_cent (y : Fin d → ℝ) (C n : ℕ)
    (h : ∀ i, |y i| ≤ (C : ℝ)) :
    nearestSite ((n : ℝ) • y) ∈ cent d (n * (C + 1) + 1) := by
  simp only [cent, Set.mem_setOf_eq]
  intro i
  have hm : ∀ j, |((n : ℝ) • y) j| ≤ (((n : ℤ) * (C + 1) : ℤ) : ℝ) := by
    intro j
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    have hC1 : |y j| ≤ ((C : ℝ) + 1) := by linarith [h j]
    have := mul_le_mul_of_nonneg_left hC1 (Nat.cast_nonneg n)
    push_cast at this ⊢
    linarith
  have hb := Gen.nearestSite_abs_le ((n : ℝ) • y) ((n : ℤ) * (C + 1)) hm i
  have hcast : (((n * (C + 1) + 1 : ℕ)) : ℤ) = (n : ℤ) * (C + 1) + 1 := by push_cast; ring
  rw [hcast]
  exact hb

/-- A finite `ℕ∞`-valued arrival time plus a natural constant is finite. -/
theorem Gen.add_nat_ne_top {a : ℕ∞} (ha : a ≠ ⊤) (C : ℕ) : a + (C : ℕ∞) ≠ ⊤ := by
  intro h
  rw [ENat.add_eq_top] at h
  exact h.elim ha (by simp)

/-- The `toNat` of a sum of a finite `ℕ∞` and a natural is the sum of the
`toNat`s. -/
theorem Gen.toNat_add_nat {a : ℕ∞} (ha : a ≠ ⊤) (C : ℕ) :
    (a + (C : ℕ∞)).toNat = a.toNat + C := by
  cases a with
  | top => exact absurd rfl ha
  | coe n => simp [ENat.toNat_add]

/-- If `a ≤ b + C` in `ℕ∞` with `b` finite, then `a.toNat ≤ b.toNat + C`. -/
theorem Gen.toNat_le_add {a b : ℕ∞} {C : ℕ} (h : a ≤ b + (C : ℕ∞)) (hb : b ≠ ⊤) :
    a.toNat ≤ b.toNat + C := by
  have hfin : b + (C : ℕ∞) ≠ ⊤ := Gen.add_nat_ne_top hb C
  have h1 : a.toNat ≤ (b + (C : ℕ∞)).toNat := ENat.toNat_le_toNat h hfin
  rwa [Gen.toNat_add_nat hb C] at h1

end Exploding
