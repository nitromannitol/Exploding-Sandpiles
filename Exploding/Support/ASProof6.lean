/-
Packet AS-6: the last claim `hpodo` of
`Exploding.Frozen.approximate_subadditive`.  Sorry-free support file.

## The reduction

Write `σ = explodingPile η`.  The penultimate cluster is
`P(0) = {0} ∪ {x | ∃ y ∼ x, 0 < penultimateWave η 0 y}`.  If the pile topples
every positive-penultimate-wave site at least twice by a common time `T`, then
every `x ∈ P(0) \ {0}` is lit by time `T + 1`: with `y ∼ x` and
`0 < penultimateWave y`, the two topplings of `y` send two chips to `x`, and
`σ x ≥ 2d - 2`, so `x` becomes unstable.  The origin is lit separately by
`as5_origin_topples_of_not_stabilizable`.

This isolates the remaining content of `hpodo` as the sharper claim that the
pile topples the positive-penultimate-wave support twice, which the extra chip
of `σ` over `η + (M-1) δ_0` is meant to supply.
-/
import Exploding.Support.ASProof
import Exploding.Support.ASProof5

open Exploding LatticeProb MeasureTheory

set_option linter.unusedVariables false

/-- If the pile topples every positive-penultimate-wave site twice by time `T`,
then it lights the whole penultimate cluster by time `T + 1` (up to the origin,
which is lit separately). -/
theorem as6_cluster_lit_of_double_support {d : ℕ} (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (T : ℕ)
    (hdom : ∀ y : Site d, 0 < penultimateWave η (0 : Site d) y →
      2 ≤ podo (explodingPile η) T y) :
    ∀ x ∈ penultimateCluster η (0 : Site d), x ≠ (0 : Site d) →
      1 ≤ podo (explodingPile η) (T + 1) x := by
  intro x hx hx0
  rcases hx with hx0' | ⟨y, hyx, hypos⟩
  · exact absurd hx0' hx0
  · have h2 : 2 ≤ podo (explodingPile η) T y := hdom y hypos
    by_cases hxT : 0 < podo (explodingPile η) T x
    · have hxT1 : 1 ≤ podo (explodingPile η) T x := by omega
      exact le_trans hxT1 (podo_mono_step (explodingPile η) T x)
    · have hxT0 : podo (explodingPile η) T x = 0 := by
        have := as_podo_nonneg (explodingPile η) T x; omega
      have hnr : podo (explodingPile η) T y ≤ nbrSumZ (podo (explodingPile η) T) x := by
        have hle : ∀ j : Fin d, podo (explodingPile η) T (x + unit j) +
            podo (explodingPile η) T (x - unit j) ≤ nbrSumZ (podo (explodingPile η) T) x := by
          intro j
          rw [nbrSumZ]
          exact Finset.single_le_sum
            (f := fun j : Fin d => podo (explodingPile η) T (x + unit j) +
              podo (explodingPile η) T (x - unit j))
            (fun j _ => by
              have h3 := as_podo_nonneg (explodingPile η) T (x + unit j)
              have h4 := as_podo_nonneg (explodingPile η) T (x - unit j)
              linarith) (Finset.mem_univ j)
        obtain ⟨i, hi | hi⟩ := hyx
        · have hy : y = x - unit i := by rw [hi]; abel
          rw [hy]
          have h1 : podo (explodingPile η) T (x - unit i) ≤
              podo (explodingPile η) T (x + unit i) + podo (explodingPile η) T (x - unit i) := by
            have h := as_podo_nonneg (explodingPile η) T (x + unit i); linarith
          exact le_trans h1 (hle i)
        · rw [hi]
          have h1 : podo (explodingPile η) T (x + unit i) ≤
              podo (explodingPile η) T (x + unit i) + podo (explodingPile η) T (x - unit i) := by
            have h := as_podo_nonneg (explodingPile η) T (x - unit i); linarith
          exact le_trans h1 (hle i)
      have hpconf : 2 * (d : ℤ) ≤ pconf (explodingPile η) T x := by
        have hsx : 2 * (d : ℤ) - 2 ≤ explodingPile η x := by
          have h := hlow x
          show 2 * (d : ℤ) - 2 ≤ η x + (explosionThreshold η : ℤ) * dirac (0 : Site d) x
          have hd0 : 0 ≤ (explosionThreshold η : ℤ) * dirac (0 : Site d) x := by
            have h1 : 0 ≤ (explosionThreshold η : ℤ) := by positivity
            have h2 : 0 ≤ dirac (0 : Site d) x := by unfold dirac; split_ifs <;> norm_num
            exact mul_nonneg h1 h2
          linarith
        simp only [pconf, lap, hxT0, mul_zero, sub_zero]
        linarith
      have hstep : podo (explodingPile η) (T + 1) x = podo (explodingPile η) T x + 1 := by
        rw [podo_succ, if_pos hpconf]
      omega
