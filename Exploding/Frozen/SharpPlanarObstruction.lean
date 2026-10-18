import Exploding.External.FeyDenBoerRedigCubicalCluster
import Exploding.External.FeyLevinePeresRadius
import Exploding.Support.PlanarWaveOptimality

/-!
# Sharp planar obstruction

The remark "Sharp planar obstruction" after `lemma:square_lower_bound` in the corrected paper. On
the homogeneous height-two background in dimension two, the least positive order `M₂(n)` whose
wave from the origin reaches every site of the cube `B_n = [-n, n]²` satisfies
`c n² log (n + 1) ≤ M₂(n) ≤ C n² log (n + 1)` for every `n ≥ 1`.

No minimum function is defined. For each `n ≥ 1` the statement gives a positive covering order
`M` that is at most every positive covering order, so `M` is the least one, and it bounds that
same `M` on both sides. The constants `c` and `C` are chosen before `n`.

The two cited inputs are the explicit hypotheses `hFDR` and `hFLP`. They are cited propositions
of other papers and are not proved here. The proof is `Exploding.planar_wave_order_bounds`.
-/

open Exploding LatticeProb

/-- **Sharp planar obstruction** (remark after `lemma:square_lower_bound`). Assume the two cited
inputs. There are `c, C > 0` such that for every `n ≥ 1` the least positive order `M` whose wave
from the origin on the background `2` reaches each site of `[-n, n]²` at some time satisfies
`c n² log (n + 1) ≤ M ≤ C n² log (n + 1)`. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.sharp_planar_obstruction
    (hFDR : Exploding.External.FeyDenBoerRedigCubicalCluster)
    (hFLP : Exploding.External.FeyLevinePeresRadius) :
    ∃ c C : Real, 0 < c ∧ 0 < C ∧
      ∀ n : Nat, 1 ≤ n → ∃ M : Nat,
        1 ≤ M ∧
        (∀ x ∈ cent 2 n, ∃ t : Nat,
          0 < wave (fun _ : Site 2 => (2 : Int)) M (0 : Site 2) t x) ∧
        (∀ m : Nat, 1 ≤ m →
          (∀ x ∈ cent 2 n, ∃ t : Nat,
            0 < wave (fun _ : Site 2 => (2 : Int)) m (0 : Site 2) t x) → M ≤ m) ∧
        c * (n : Real)^2 * Real.log ((n : Real) + 1) ≤ (M : Real) ∧
        (M : Real) ≤ C * (n : Real)^2 * Real.log ((n : Real) + 1)
-- FROZEN-STATEMENT-END
:= by
  exact Exploding.planar_wave_order_bounds hFDR hFLP
