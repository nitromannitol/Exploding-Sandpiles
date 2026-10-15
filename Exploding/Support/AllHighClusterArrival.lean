import Exploding.Support.AllHighPenultimateCluster

/-!
# Cluster arrival for the all-high background

The all-high penultimate cluster at a target is its singleton. Substituting
that characterization into the defining infimum gives the ordinary last arrival.
-/
namespace Exploding

open LatticeProb

/-- Cluster arrival in the all-high background equals last arrival. -/
theorem all_high_cluster_arrival_eq_last_arrival
    (d : ℕ) (hd : 2 ≤ d) (z x : Site d) :
    clusterArrival (fun _ : Site d => 2 * (d : ℤ) - 1) z x =
      lastArrival (fun _ : Site d => 2 * (d : ℤ) - 1) z x := by
  have hcluster := all_high_penultimate_cluster_eq_singleton d hd x
  simp [clusterArrival, lastArrival, hcluster]

end Exploding
