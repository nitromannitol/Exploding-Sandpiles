/-
Proposition 4.1 of the official arXiv version: the last-wave is a bounded approximation
of the exploding sandpile.
-/
import Exploding.Support.Vocab
import Exploding.Support.ASProof2
import Exploding.Support.ASProof3
import Exploding.Support.ASProof4
import Exploding.Support.ASProof7
import Exploding.Support.ASSpecial
import Exploding.Support.ASDouble
import Exploding.Support.ApproximateSubadditiveP1
import Exploding.External.LiggettSchonmannStaceyBoundedDegree
import Exploding.External.MathieuHoles
import Exploding.External.AntalPisztora

open Exploding LatticeProb MeasureTheory

/-- **Proposition 4.1** (`paper/exploding-arxiv.tex:740-752`, arXiv:2102.04422v2,
label `prop:approximate_subadditive`). The source bytes have SHA-256
`f12deba6e481a3d81c6967bc48ecbbdae1df4fa1c5f6248a38990030b308072d`; its pinned input
`paper/defs.tex` has SHA-256 `9aba2c73246d79e3c6b87cb1f01cf3e2f636e27c8afd97ccb8ba5c032a9ee65b`.

"On an event of probability 1, there are constants `C_1(η), C_2(η)` so that for all
`x ∈ ℤ^d`, `T(x) ≤ T̂(x) + C_1(η)` and `T̂(x) ≤ T(x) + C_2(η)`, where the last-wave
arrival time `T̂` is defined in (3.4) and `T(x) := min{t ≥ 0 : v_t(x) > 0}`."

The source fixes `p > 0`, with `p` a probability parameter, so the endpoint `p = 1` is in
scope. The strict branch uses the three cited inputs for the existing proof, while the
endpoint branch follows from `Exploding.approximate_subadditive_p1`. Constants are bound
inside the almost-sure quantifier, and both arrival times are valued in `ℕ∞`.
-/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.approximate_subadditive (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∀ᵐ η ∂(toyLaw d p), ∃ C1 C2 : ℕ, ∀ x : Site d,
      arrival η x ≤ lastArrival η (0 : Site d) x + (C1 : ℕ∞) ∧
        lastArrival η (0 : Site d) x ≤ arrival η x + (C2 : ℕ∞)
-- FROZEN-STATEMENT-END
:= by
  rcases lt_or_eq_of_le hp1 with h | rfl
  · exact asd_approximate_subadditive d hd p hp h hLSSB hHole hChem
  · exact Exploding.approximate_subadditive_p1 d hd
