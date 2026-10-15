import Exploding.Support.AllHighWaveThreshold

/-!
# Last arrival for the all-high background

The all-high wave has threshold one at every center, and its translated front
identifies positive times with the integer Manhattan ball. The lower bound uses
every member of the defining infimum; the upper bound exhibits the finite
admissible time `max 1 ...`.
-/
namespace Exploding

open LatticeProb

/-- The all-high last-wave arrival time is the Manhattan distance, with the
source clock restricted to positive times. -/
theorem all_high_last_arrival_eq
    (d : ℕ) (hd : 2 ≤ d) (z x : Site d) :
    lastArrival (fun _ : Site d => 2 * (d : ℤ) - 1) z x =
      ((max 1 (mnorm (x - z)).toNat : ℕ) : ℕ∞) := by
  let η : Site d → ℤ := fun _ => 2 * (d : ℤ) - 1
  let r : ℤ := mnorm (x - z)
  let k : ℕ := max 1 r.toNat
  have hthreshold : waveThreshold η z = 1 := by
    dsimp [η]
    exact all_high_wave_threshold_eq_one d hd z
  have hfront (n : ℕ) :
      lastWave η z n x = if r ≤ (n : ℤ) then 1 else 0 := by
    rw [lastWave, hthreshold]
    simpa [r] using allHigh_wave_one_eq_indicator_ball d hd z x n
  have hr_nonneg : 0 ≤ r := by
    dsimp [r, mnorm]
    apply Finset.sum_nonneg
    intro i hi
    exact abs_nonneg _
  have hcast : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr_nonneg
  have hk_pos : 1 ≤ k := by
    dsimp [k]
    exact Nat.le_max_left 1 r.toNat
  have hrnat_le_k : r.toNat ≤ k := by
    dsimp [k]
    exact Nat.le_max_right 1 r.toNat
  have hr_le_k : r ≤ (k : ℤ) := by
    rw [← hcast]
    exact_mod_cast hrnat_le_k
  have hwave_k : lastWave η z k x = 1 := by
    rw [hfront k]
    simp [hr_le_k]
  have hk_mem :
      (k : ℕ∞) ∈
        {t : ℕ∞ | ∃ n : ℕ, t = (n : ℕ∞) ∧ 1 ≤ n ∧
          0 < lastWave η z n x} := by
    refine ⟨k, rfl, hk_pos, ?_⟩
    rw [hwave_k]
    norm_num
  have hupper : lastArrival η z x ≤ (k : ℕ∞) := by
    unfold lastArrival
    exact sInf_le hk_mem
  have hlower : (k : ℕ∞) ≤ lastArrival η z x := by
    unfold lastArrival
    refine le_sInf ?_
    intro t ht
    rcases ht with ⟨n, htn, hn, hpos⟩
    rw [htn]
    have hr_le_n : r ≤ (n : ℤ) := by
      by_contra hnot
      have hzero : lastWave η z n x = 0 := by
        rw [hfront n]
        simp [hnot]
      rw [hzero] at hpos
      exact (lt_irrefl 0 hpos)
    have hrnat_le_n : r.toNat ≤ n := by
      have hcast_le : (r.toNat : ℤ) ≤ (n : ℤ) := by
        rw [hcast]
        exact hr_le_n
      exact_mod_cast hcast_le
    have hk_le_n : k ≤ n := by
      dsimp [k]
      exact max_le hn hrnat_le_n
    exact ENat.coe_le_coe.mpr hk_le_n
  have hresult : lastArrival η z x = (k : ℕ∞) := le_antisymm hupper hlower
  simpa [η, r, k] using hresult

end Exploding
