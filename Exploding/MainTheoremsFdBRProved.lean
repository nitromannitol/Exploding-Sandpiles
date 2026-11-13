import Exploding.MainTheorems
import Exploding.External.FeyDenBoerRedigCubicalClusterProved

/-!
# Main results with the result of Fey, den Boer and Redig proved

Lemma 3.1 (`Exploding.square_lower_bound`) and the remark after it
(`Exploding.sharp_planar_obstruction`) carry Theorem 4.1 of Fey, den Boer and Redig
(`Exploding.External.FeyDenBoerRedigCubicalCluster`) and the radius bound of Fey, Levine and Peres
(`Exploding.External.FeyLevinePeresRadius`) as hypotheses.  The first is proved from
Lattice-Probability by `Exploding.External.feyDenBoerRedigCubicalCluster_holds`
(`Exploding/External/FeyDenBoerRedigCubicalClusterProved.lean`); the two statements below are the
original ones with that hypothesis removed, each proved by applying the original theorem.
-/

open Exploding LatticeProb

/-- **Lemma 3.1** (`lemma:square_lower_bound`): for `d ≥ 2` there is `C > 0` such that for every
background with `2d - 2 ≤ η ≤ 2d - 1`, every `n ≥ 1` and every `m ≥ C n^d` (`m ≥ C n² log (n + 1)`
when `d = 2`), the `m`-wave from the origin is eventually positive on `[-n, n]^d`. Theorem 4.1
of Fey, den Boer and Redig is proved here
(`Exploding.External.feyDenBoerRedigCubicalCluster_holds`); the radius bound of Fey, Levine and Peres is a hypothesis. -/
theorem Exploding.square_lower_bound_of_radius (d : ℕ) (hd : 2 ≤ d)
    (hFLP : Exploding.External.FeyLevinePeresRadius) :
    ∃ C : ℝ, 0 < C ∧
      ∀ η : Site d → ℤ,
        (∀ x, 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1) →
        ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, 1 ≤ m →
          Nat.ceil (C * (n : ℝ) ^ d *
            (if d = 2 then Real.log ((n : ℝ) + 1) else 1)) ≤ m →
          ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
            ∀ x ∈ cent d n, 0 < wave η m (0 : Site d) t x := by
  exact Exploding.square_lower_bound d hd
    Exploding.External.feyDenBoerRedigCubicalCluster_holds hFLP

/-- **The remark after Lemma 3.1** (sharp planar obstruction): on the constant background `2` in
dimension two, the least order `M` whose wave from the origin covers `[-n, n]²` satisfies
`c n² log (n + 1) ≤ M ≤ C n² log (n + 1)`, so the logarithm in Lemma 3.1 cannot be removed.
The result of Fey, den Boer and Redig is proved here
(`Exploding.External.feyDenBoerRedigCubicalCluster_holds`); the radius bound of Fey, Levine and Peres is a hypothesis. -/
theorem Exploding.sharp_planar_obstruction_of_radius
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
        (M : Real) ≤ C * (n : Real)^2 * Real.log ((n : Real) + 1) := by
  exact Exploding.sharp_planar_obstruction
    Exploding.External.feyDenBoerRedigCubicalCluster_holds hFLP
