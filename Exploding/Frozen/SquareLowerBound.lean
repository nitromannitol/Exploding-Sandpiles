import Exploding.External.FeyDenBoerRedigCubicalCluster
import Exploding.External.FeyLevinePeresRadius
import Exploding.Support.SquareLowerBoundSharp

/-!
# Sharp square lower bound

The sharp square lower bound, `lemma:square_lower_bound` of the corrected paper. For `d ≥ 2` and
the two cited inputs, there is a constant `C > 0`, chosen before every background, `n` and `m`,
such that for every background `η` with `2d - 2 ≤ η(x) ≤ 2d - 1`, every `n ≥ 1` and every `m ≥ 1`
with `⌈C n^d (log (n+1) if d = 2)⌉ ≤ m`, there is a finite time `T` after which the `m`-wave from the
origin is positive at every site of `[-n, n]^d`.

The two cited inputs are the explicit hypotheses `hFdBR` and `hFLP`. They are cited propositions
of other papers and are not proved here. The proof is `Exploding.square_lower_bound_sharp`.
-/

open Exploding LatticeProb

/-- **Lemma 3.1, sharp form** (`lemma:square_lower_bound`). Assume `d ≥ 2` and the two cited
inputs. There is `C > 0` such that for every `η` with `2d - 2 ≤ η ≤ 2d - 1`, every `n ≥ 1` and
every `m ≥ 1` with `⌈C n^d (log (n+1) if d = 2)⌉ ≤ m`, there is a finite `T` such that the
`m`-wave from the origin is positive at every site of `[-n, n]^d` at every time `t ≥ T`. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.square_lower_bound (d : ℕ) (hd : 2 ≤ d)
    (hFdBR : Exploding.External.FeyDenBoerRedigCubicalCluster)
    (hFLP : Exploding.External.FeyLevinePeresRadius) :
    ∃ C : ℝ, 0 < C ∧
      ∀ η : Site d → ℤ,
        (∀ x, 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1) →
        ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, 1 ≤ m →
          Nat.ceil (C * (n : ℝ) ^ d *
            (if d = 2 then Real.log ((n : ℝ) + 1) else 1)) ≤ m →
          ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
            ∀ x ∈ cent d n, 0 < wave η m (0 : Site d) t x
-- FROZEN-STATEMENT-END
:= by
  exact Exploding.square_lower_bound_sharp d hd hFdBR hFLP
