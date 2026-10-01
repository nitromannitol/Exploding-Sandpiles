/-
Proposition 5.1 (generalized last wave), closeness of the arrival times, part D:
the macroscopic site of a microscopic site, the tiles around it, and the reversal of a lit path.
-/
import Exploding.Support.S3CloseC

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

/-- The macroscopic site of a microscopic site: the index of the tile containing it. -/
def s3k_nu (k : Fin d → ℕ) (x : Site d) : Site d := fun m => (x m - 1) / (k m : ℤ)

theorem s3k_mem_tile_nu (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (x : Site d) :
    x ∈ rboxShift k (s3k_nu k x) := by
  intro m
  obtain ⟨h1, h2⟩ := glws_floor_div (x m - 1) (k m) (hk m)
  simp only [s3k_nu]
  constructor <;> linarith

theorem s3k_nu_abs (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (x : Site d) (m : Fin d) :
    |s3k_nu k x m| ≤ |x m| + 1 := by
  simp only [s3k_nu]
  exact pclose_ediv_abs (x m) (k m) (hk m)

theorem s3k_mnorm_nu_le (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (x : Site d) :
    mnorm (s3k_nu k x) ≤ mnorm x + d := by
  unfold mnorm
  calc ∑ m, |s3k_nu k x m| ≤ ∑ m, (|x m| + 1) := Finset.sum_le_sum fun m _ => s3k_nu_abs k hk x m
    _ = ∑ m, |x m| + d := by
        rw [Finset.sum_add_distrib]; simp

/-- A site within `Z` of `x` in every coordinate lies in the tiles of macroscopic distance `Z`
around the macroscopic site of `x`. -/
theorem s3k_region (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (x y : Site d) (Z : ℤ)
    (h : ∀ i, |y i - x i| ≤ Z) (m : Fin d) :
    (k m : ℤ) * (s3k_nu k x m - Z) + 1 ≤ y m ∧ y m ≤ (k m : ℤ) * (s3k_nu k x m + Z + 1) := by
  have hx := s3k_mem_tile_nu k hk x m
  have hk1 : (1 : ℤ) ≤ (k m : ℤ) := by exact_mod_cast hk m
  have hZ : 0 ≤ Z := le_trans (abs_nonneg _) (h m)
  have h1 := abs_le.mp (h m)
  have hkZ : Z ≤ (k m : ℤ) * Z := by nlinarith
  constructor <;> nlinarith [hx.1, hx.2, h1.1, h1.2]

/-- Tiles meeting a ball around `x` have macroscopic sites close to that of `x`. -/
theorem s3k_tile_close (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (x : Site d) (j : Site d)
    (q : ℤ) (hj : ∀ y ∈ rboxShift k j, ∀ m, |y m - x m| ≤ q) (m : Fin d) :
    |j m - s3k_nu k x m| ≤ q + (k m : ℤ) := by
  have hy := hj (glws_corner k j) (glws_corner_mem k hk j) m
  have hx := s3k_mem_tile_nu k hk x m
  have hk1 : (1 : ℤ) ≤ (k m : ℤ) := by exact_mod_cast hk m
  have hcorner : glws_corner k j m = 1 + (k m : ℤ) * j m := rfl
  rw [hcorner] at hy
  have h1 := abs_le.mp hy
  have hq : 0 ≤ q := le_trans (abs_nonneg _) hy
  -- `k m * (j m - ν m)` is bounded by `q + k m`
  have hb1 : (k m : ℤ) * (j m - s3k_nu k x m) ≤ q + (k m : ℤ) := by nlinarith [hx.1, hx.2]
  have hb2 : -(q + (k m : ℤ)) ≤ (k m : ℤ) * (j m - s3k_nu k x m) := by nlinarith [hx.1, hx.2]
  have hnorm : |j m - s3k_nu k x m| ≤ |(k m : ℤ) * (j m - s3k_nu k x m)| := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℤ) < (k m : ℤ))]
    nlinarith [abs_nonneg (j m - s3k_nu k x m)]
  exact le_trans hnorm (abs_le.mpr ⟨by linarith, by linarith⟩)

/-! ### Reversing a path -/

/-- The first `p + 1` sites of the reversed path from `x`: the sites are adjacent, distinct, within
`i` of `x` for the `i`-th one, and as lit as the original path. -/
theorem s3k_path_back (η : Site d → ℤ) (N : ℕ) (s : ℕ) (m : ℕ) (z : ℕ → Site d)
    (hadj : ∀ i, i < m → (lattice d).Adj (z i) (z (i + 1)))
    (hinj : ∀ i j, i ≤ m → j ≤ m → z i = z j → i = j)
    (hlit : ∀ i, i ≤ m → 0 < wave η N (0 : Site d) s (z i)) (p : ℕ) (hp : p ≤ m) :
    ∃ zr : ℕ → Site d, zr 0 = z m ∧
      (∀ i, i < p → (lattice d).Adj (zr i) (zr (i + 1))) ∧
      (∀ i j, i ≤ p → j ≤ p → zr i = zr j → i = j) ∧
      (∀ i, i ≤ p → 0 < wave η N (0 : Site d) s (zr i)) ∧
      (∀ i, i ≤ p → ∀ l, |zr i l - z m l| ≤ i) := by
  refine ⟨fun i => z (m - i), by simp, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have h1 := hadj (m - (i + 1)) (by omega)
    have h2 : m - (i + 1) + 1 = m - i := by omega
    rw [h2] at h1
    exact h1.symm
  · intro i j hi hj hij
    have := hinj (m - i) (m - j) (by omega) (by omega) hij
    omega
  · intro i hi
    exact hlit (m - i) (by omega)
  · intro i hi l
    have hadj' : ∀ q, q < m → (lattice d).Adj (z (m - q)) (z (m - (q + 1))) := by
      intro q hq
      have h1 := hadj (m - (q + 1)) (by omega)
      have h2 : m - (q + 1) + 1 = m - q := by omega
      rw [h2] at h1
      exact h1.symm
    have := glws_path_coord (fun q => z (m - q)) hadj' l i (by omega)
    simpa using this

end Exploding
