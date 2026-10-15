import Exploding.Support.AllHighWaveTranslation

/-!
# The all-high one-wave threshold

The all-high one-wave never stabilizes at any center: at each time its front
continues to reach a site one step farther away. Thus mass one belongs to the
defining nonstabilizable set, and the two bounds for its natural infimum give
the threshold exactly.
-/
namespace Exploding

open LatticeProb

/-- The all-high one-wave is not stabilizable at any center. -/
private theorem all_high_wave_one_not_stabilizable_at_center
    (d : ℕ) (hd : 2 ≤ d) (z : Site d) :
    ¬ WaveStabilizable (fun _ : Site d => 2 * (d : ℤ) - 1) 1 z := by
  intro hstab
  apply arxivAllHigh_wave_not_stabilizable d hd
  rcases hstab with ⟨T, hstable⟩
  refine ⟨T, ?_⟩
  intro t ht
  funext w
  have hEq := congrFun (hstable t ht) (w + z)
  rw [wave_centre_eq (fun _ : Site d => 2 * (d : ℤ) - 1) 1 z t (w + z),
    wave_centre_eq (fun _ : Site d => 2 * (d : ℤ) - 1) 1 z T (w + z)] at hEq
  simpa using hEq

/-- At every center, the all-high one-wave has threshold one. -/
theorem all_high_wave_threshold_eq_one (d : ℕ) (hd : 2 ≤ d) (z : Site d) :
    waveThreshold (fun _ : Site d => 2 * (d : ℤ) - 1) z = 1 := by
  have hnonstab :
      ¬ WaveStabilizable (fun _ : Site d => 2 * (d : ℤ) - 1) 1 z :=
    all_high_wave_one_not_stabilizable_at_center d hd z
  have hmem : 1 ∈ {n : ℕ | 1 ≤ n ∧
      ¬ WaveStabilizable (fun _ : Site d => 2 * (d : ℤ) - 1) n z} :=
    ⟨le_rfl, hnonstab⟩
  have hge :
      1 ≤ waveThreshold (fun _ : Site d => 2 * (d : ℤ) - 1) z := by
    unfold waveThreshold
    exact (Nat.sInf_mem ⟨1, hmem⟩).1
  have hle :
      waveThreshold (fun _ : Site d => 2 * (d : ℤ) - 1) z ≤ 1 := by
    unfold waveThreshold
    exact Nat.sInf_le hmem
  omega

end Exploding
