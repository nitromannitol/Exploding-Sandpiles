import Exploding.Support.AllHighWaveThreshold

/-!
# The all-high penultimate cluster

At every center, the all-high pile has threshold one. Its penultimate wave is
therefore zero by definition, while its penultimate cluster still contains
the center.
-/
namespace Exploding

open LatticeProb

/-- The all-high penultimate cluster consists of its center. -/
theorem all_high_penultimate_cluster_eq_singleton
    (d : ℕ) (hd : 2 ≤ d) (z : Site d) :
    penultimateCluster (fun _ : Site d => 2 * (d : ℤ) - 1) z = {z} := by
  have hthreshold := all_high_wave_threshold_eq_one d hd z
  simp [penultimateCluster, penultimateWave, hthreshold]

end Exploding
