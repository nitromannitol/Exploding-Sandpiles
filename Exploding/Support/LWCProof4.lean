/-
Follow-up to `Exploding/Support/LWCProof3.lean` (packet LWC-4).

Conjunct (2) of the last-wave reduction: the far Lipschitz bound on the penultimate-cluster
arrival time `T̃`.  This file starts from the elementary lower bound that the `N`-wave spreads at
speed at most one, `mnorm (x - z) ≤ t` whenever `wave η N z t x > 0`, which is the ingredient the
"near" half of the far-bound split uses together with Lemma 3.6.  All declarations are
`lwc4_`-prefixed.
-/
import Exploding.Support.LWCProof3
import Exploding.Support.Wave

open Exploding LatticeProb MeasureTheory Filter

variable {d : ℕ}

/-- **The wave spreads at speed at most one.**  If the `N`-wave started at `z` is positive at
`x` at time `t`, then `x` is within the `L¹`-distance `t` of `z`.  The proof is the induction
on `t`: a positive value away from the centre forces a positive neighbour sum, hence a positive
value at a neighbour at the previous time. -/
theorem lwc4_wave_pos_mnorm_le (hd : 0 < d) (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (N : ℕ) (z : Site d) (t : ℕ) (x : Site d) (hpos : 0 < wave η N z t x) :
    mnorm (x - z) ≤ (t : ℤ) := by
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
    linarith
  induction t generalizing x with
  | zero =>
    rw [wave_zero] at hpos
    by_cases hxz : x = z
    · subst hxz; simp [mnorm]
    · simp [hxz] at hpos
  | succ t ih =>
    by_cases hxz : x = z
    · subst hxz; simp [mnorm]; omega
    · rw [wave_of_ne _ _ _ _ _ hxz] at hpos
      have hle : (1 : ℤ) ≤ (nbrSumZ (wave η N z t) x + η x) / (2 * (d : ℤ)) := by omega
      have hmul := (Int.le_ediv_iff_mul_le hd0).mp hle
      have hsum : 0 < nbrSumZ (wave η N z t) x := by linarith [hhigh x]
      obtain ⟨y, hyadj, hypos⟩ :=
        exists_adj_pos_of_nbrSumZ_pos _ (fun y => wave_nonneg η hlow N z t y) x hsum
      have hy := ih y hypos
      have hxy : mnorm (x - y) = 1 := pub_adj_mnorm hyadj
      calc mnorm (x - z) ≤ mnorm (x - y) + mnorm (y - z) := pub_mnorm_sub_le x y z
        _ ≤ 1 + (t : ℤ) := by linarith
        _ = ((t + 1 : ℕ) : ℤ) := by push_cast; ring

/-- **The penultimate-cluster arrival is at least the lattice distance.**  Since the centre is
in its own penultimate cluster and the wave spreads at speed at most one, a finite
`clusterArrival η z x` is at least `mnorm (x - z)`. -/
theorem lwc4_clusterArrival_ge_mnorm (hd : 0 < d) (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (z : Site d) (x : Site d) (hfin : clusterArrival η z x ≠ ⊤) :
    mnorm (x - z) ≤ ((clusterArrival η z x).toNat : ℤ) := by
  obtain ⟨n, hn1, hcov, heq⟩ := clusterArrival_exists η z x hfin
  have hpos : 0 < lastWave η z n x := hcov x (centre_mem_penultimateCluster η x)
  have hpos' : 0 < wave η (waveThreshold η z) z n x := hpos
  have h := lwc4_wave_pos_mnorm_le hd η hlow hhigh (waveThreshold η z) z n x hpos'
  rw [heq, ENat.toNat_coe]
  exact h
