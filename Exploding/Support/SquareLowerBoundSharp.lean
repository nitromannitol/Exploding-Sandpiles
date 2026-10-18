import Exploding.Support.SquareRadiusGreen
import Exploding.Support.SquareWaveComparison
import Exploding.Support.Vocab
import LatticeProb.Analysis.SandpileScale
import LatticeProb.External.FeyDenBoerRedigCubicalCluster
import LatticeProb.External.FeyLevinePeresRadius

/-!
# Sharp square lower bound

For `d ≥ 2` there is a constant `C > 0`, depending only on `d`, such that for every background
`η` with `2d - 2 ≤ η(x) ≤ 2d - 1` at every site, every `n ≥ 1` and every `m ≥ 1` with
`m ≥ ⌈C n^d⌉` (and `m ≥ ⌈C n^2 log(n+1)⌉` when `d = 2`), there is a finite time `T` after which
the `m`-wave from the origin is positive at every site of the cube `[-n, n]^d`.

The proof runs the parallel toppling process of the pile `(2d - 2) + N δ₀` with
`N = (2n + 3)^d + N₀`. The radius and Green-origin estimate gives a common stabilization time `T`
and a positive terminal cube of radius `r`. The scalar root bound gives `n ≤ r`, and the scalar
scale bound gives an origin value at most `m`. The comparison with the wave then transfers
positivity from time `T` to every later time, since the wave is nondecreasing in time.

The two cited inputs `LatticeProb.External.FeyDenBoerRedigCubicalCluster` and
`LatticeProb.External.FeyLevinePeresRadius` are explicit hypotheses and are not proved here.
-/

open Exploding LatticeProb

/-- **Sharp square lower bound.** Assume `d ≥ 2` and the two cited propositions. There is a
constant `C > 0`, chosen before every background, `n` and `m`, such that for every `η` with
`2d - 2 ≤ η ≤ 2d - 1`, every `n ≥ 1` and every `m ≥ 1` with `⌈C n^d (log (n+1) if d = 2)⌉ ≤ m`,
there is a finite time `T` such that the `m`-wave from the origin is positive at every site of
`[-n, n]^d` at every time `t ≥ T`. -/
theorem Exploding.square_lower_bound_sharp (d : ℕ) (hd : 2 ≤ d)
    (hFdBR : LatticeProb.External.FeyDenBoerRedigCubicalCluster)
    (hFLP : LatticeProb.External.FeyLevinePeresRadius) :
    ∃ C : ℝ, 0 < C ∧
      ∀ η : Site d → ℤ,
        (∀ x, 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1) →
        ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, 1 ≤ m →
          Nat.ceil (C * (n : ℝ) ^ d *
            (if d = 2 then Real.log ((n : ℝ) + 1) else 1)) ≤ m →
          ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
            ∀ x ∈ cent d n, 0 < wave η m (0 : Site d) t x := by
  obtain ⟨A, hA, N0, _, B, hB, E, hE, hprod⟩ :=
    squareRadiusGreen_terminal_bound d hd hFdBR hFLP
  obtain ⟨C, hC, hscale⟩ := exists_sandpile_scale_bound d N0 A B E hd hA hB hE
  refine ⟨C, hC, ?_⟩
  intro η hη n hn m _ hmC
  have h2 : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hdpos : 0 < d := by omega
  have hd2 : (0 : ℤ) < 2 * (d : ℤ) := by linarith
  have hηlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x := fun x => (hη x).1
  have hηnn : ∀ x, 0 ≤ η x := fun x => by linarith [hηlow x]
  -- The parameter `N` is fixed after `n`, and is at least `N₀`.
  set N : ℕ := Nat.pow (2 * n + 3) d + N0 with hNdef
  have hNN0 : N0 ≤ N := Nat.le_add_left _ _
  set L : ℕ := Nat.ceil (A * (N : ℝ) ^ (1 / (d : ℝ))) with hLdef
  set s0 : Site d → ℤ := fun x => (2 * (d : ℤ) - 2) + (N : ℤ) * LatticeProb.Sandpile.dirac (0 : Site d) x
    with hs0def
  -- The radius and Green estimate for this pile.
  obtain ⟨T, r, hstab, hsupp, hrad, horig⟩ := hprod N hNN0
  -- The scalar root bound gives `n ≤ r`.
  have hnr : (n : ℝ) ≤ (r : ℝ) := le_trans (le_sandpile_scale_root d n N0 hd hn) hrad
  have hnr' : n ≤ r := by exact_mod_cast hnr
  -- The positive terminal support contains the cube `[-n, n]^d`.
  have hpos : ∀ x ∈ cent d n, 0 < Exploding.podo s0 T x := by
    intro x hx
    have hx' : ∀ i, |x i| ≤ (n : ℤ) := hx
    have hxr : ∀ i : Fin d, |x i| ≤ (r : ℤ) := fun i => le_trans (hx' i) (by exact_mod_cast hnr')
    exact (Set.ext_iff.mp hsupp x).mpr hxr
  -- The scalar scale bound at the origin.
  have hsc : (N : ℝ) * B * (if d = 2 then Real.log ((L : ℝ) + 2) else 1)
      + (2 * (d : ℝ) - 2) * E * ((L : ℝ) + 1) ^ 2
      ≤ C * (n : ℝ) ^ d * (if d = 2 then Real.log ((n : ℝ) + 1) else 1) := by
    have h := hscale n hn
    simp only [Real.rpow_eq_pow, Real.rpow_two, Real.rpow_natCast] at h
    exact h
  have hY : ((Exploding.podo s0 T 0 : ℤ) : ℝ)
      ≤ C * (n : ℝ) ^ d * (if d = 2 then Real.log ((n : ℝ) + 1) else 1) :=
    le_trans horig hsc
  have hceil : ((Nat.ceil (C * (n : ℝ) ^ d * (if d = 2 then Real.log ((n : ℝ) + 1) else 1)) : ℕ)
      : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmC
  have hpod0 : ((Exploding.podo s0 T 0 : ℤ) : ℝ) ≤ (m : ℝ) :=
    le_trans hY (le_trans (Nat.le_ceil _) hceil)
  have hpodm : Exploding.podo s0 T 0 ≤ (m : ℤ) := by exact_mod_cast hpod0
  -- The pile is nonnegative and equal to the background off the origin.
  have hs0 : ∀ x : Site d, 0 ≤ s0 x := fun x =>
    add_nonneg (by linarith) (mul_nonneg (Nat.cast_nonneg N)
      (LatticeProb.Sandpile.dirac_nonneg (0 : Site d) x))
  have hoff : ∀ x : Site d, x ≠ 0 → s0 x = 2 * (d : ℤ) - 2 := by
    intro x hx
    simp [s0, LatticeProb.Sandpile.dirac, hx]
  -- Comparison with the wave, at the common stabilization time `T`.
  have hcomp := sqw_podo_le_wave_of_stabilized_origin s0 (2 * (d : ℤ) - 2) m hdpos η hηlow
    (by linarith) hs0 hoff T hstab hpodm
  -- The wave is nondecreasing in time on a nonnegative background.
  have hmono : ∀ x : Site d, ∀ k : ℕ,
      wave η m (0 : Site d) T x ≤ wave η m (0 : Site d) (T + k) x := by
    intro x k
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact le_trans ih (wave_mono_t η hηnn hd2 m (0 : Site d) (T + k) x)
  refine ⟨T, fun t hTt x hx => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hTt
  exact lt_of_lt_of_le (hpos x hx) (le_trans (hcomp T x) (hmono x k))
