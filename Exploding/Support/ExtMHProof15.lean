/-
The arithmetic comparison behind the isoperimetric size of the hole boundary: `Nat.log 2 n`
is bounded by `(log n)^{5(d-1)/(2d)}/d` for large `n`, since the logarithm outweighs the
double logarithm.
-/
import Exploding.Support.ExtMHProof14

namespace Exploding

open LatticeProb MeasureTheory Filter
open scoped BigOperators

variable {d : ℕ}
variable {q : ℝ}

/-- `Nat.log 2 n ≤ log n / log 2`. -/
theorem xmh11_log_bound {n : ℕ} (hn : n ≠ 0) :
    (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
  have h : (2 : ℝ) ^ (Nat.log 2 n) ≤ (n : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hn
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (Nat.log 2 n)) h
  rw [Real.log_pow] at hlog
  rw [le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  linarith

end Exploding

namespace Exploding

open LatticeProb MeasureTheory Filter

variable {d : ℕ}
variable {q : ℝ}

/-- The isoperimetric size of the hole boundary, in the eventual form used by the assembly:
for `n` above `N` the threshold `xmh4_m n` is below the inner boundary, by the
edge-isoperimetric inequality and the arithmetic comparison. -/
theorem xmh11_Size (hd : 2 ≤ d) (h : xmh4_edgeIso d) (N : ℕ)
    (harith : ∀ n : ℕ, N ≤ n → (xmh4_m n : ℝ) ≤ (xmh3_V n) ^ (((d : ℝ) - 1) / d) / d)
    (huniq : xmh8_UniqueOpen d q) :
    ∀ᵐ ω ∂(sitePercolation d q), ∀ C : Set (Site d), IsInfiniteOpenCluster ω C →
      ∀ n : ℕ, N ≤ n → ∀ x ∈ cent d n, x ∉ C →
        xmh3_V n ≤ ((componentIn Cᶜ x).ncard : ℝ) →
        xmh4_m n ≤ (innerBoundary (componentIn Cᶜ x)).ncard := by
  filter_upwards [huniq] with ω huniq C hC n hN x hx hxC hvol
  set B := componentIn Cᶜ x with hBdef
  have hxcompl : x ∈ Cᶜ := by simpa using hxC
  have hBfin : B.Finite := huniq C hC x hxC
  have hxB : x ∈ B := ⟨hxcompl, hxcompl, SimpleGraph.Reachable.refl _⟩
  have htofin : hBfin.toFinset.Nonempty := by
    rw [Set.Finite.toFinset_nonempty]; exact ⟨x, hxB⟩
  have hiso := xmh4_innerBoundary_iso hd h hBfin.toFinset htofin
  have hbnd_eq : innerBoundary B = innerBoundary (hBfin.toFinset : Set (Site d)) := by
    rw [hBfin.coe_toFinset]
  have hcard : (hBfin.toFinset.card : ℝ) = (B.ncard : ℝ) := by
    rw [Set.ncard_eq_toFinset_card B hBfin]
  rw [hbnd_eq]
  have hnonneg : (0 : ℝ) ≤ xmh3_V n := by rw [xmh3_V]; positivity
  have he : (0 : ℝ) ≤ ((d : ℝ) - 1) / d := by
    apply div_nonneg
    · have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
      linarith
    · positivity
  have h1 : (xmh3_V n) ^ (((d : ℝ) - 1) / d) ≤ (B.ncard : ℝ) ^ (((d : ℝ) - 1) / d) :=
    Real.rpow_le_rpow hnonneg hvol he
  have hreal : (xmh4_m n : ℝ) ≤ ((innerBoundary (hBfin.toFinset : Set (Site d))).ncard : ℝ) := by
    calc (xmh4_m n : ℝ) ≤ (xmh3_V n) ^ (((d : ℝ) - 1) / d) / d := harith n hN
      _ ≤ (B.ncard : ℝ) ^ (((d : ℝ) - 1) / d) / d := by
          apply div_le_div_of_nonneg_right h1; positivity
      _ = (hBfin.toFinset.card : ℝ) ^ (((d : ℝ) - 1) / d) / d := by rw [hcard]
      _ ≤ ((innerBoundary (hBfin.toFinset : Set (Site d))).ncard : ℝ) := by exact_mod_cast hiso
  exact_mod_cast hreal

end Exploding
