/-
Proposition 4.1 of the paper: the last-wave is a bounded approximation of the
exploding sandpile.
-/
import Exploding.Support.Vocab
import Exploding.Support.ASProof2
import Exploding.Support.ASProof3
import Exploding.Support.ASProof4
import Exploding.Support.ASSpecial
import Exploding.External.LiggettSchonmannStaceyBoundedDegree
import Exploding.External.MathieuHoles
import Exploding.External.AntalPisztora

open Exploding LatticeProb MeasureTheory

/-- **Proposition 4.1** (`exploding.tex:886-898`, label
`prop:approximate_subadditive`).

"On an event of probability 1, there are constants `C_1(η), C_2(η)` so that for
all `x ∈ ℤ^d`, `T(x) ≤ T̂(x) + C_1(η)` and `T̂(x) ≤ T(x) + C_2(η)`, where the
last-wave arrival time `T̂` is defined in (3.4) and
`T(x) := min{t ≥ 0 : v_t(x) > 0}`."

The constants depend on `η`, so they are bound after it, inside the almost-sure
quantifier.  Both arrival times are taken in `ℕ∞`, where the two inequalities
say exactly what the paper's do.

Section 3 runs on the event of Proposition 2.2, so the results the paper cites
for it enter as explicit hypotheses: `hLSSB` (Liggett, Schonmann and Stacey,
Corollary 1.4), `hHole` (Mathieu, Lemma 5.2) and `hChem` (Antal and Pisztora,
Theorem 1.1). -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.approximate_subadditive (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∀ᵐ η ∂(toyLaw d p), ∃ C1 C2 : ℕ, ∀ x : Site d,
      arrival η x ≤ lastArrival η (0 : Site d) x + (C1 : ℕ∞) ∧
        lastArrival η (0 : Site d) x ≤ arrival η x + (C2 : ℕ∞)
-- FROZEN-STATEMENT-END
:= by
  -- The remaining open claim is finite-sink stabilization; the finiteness of
  -- `P̃`, the last-wave reach and robustness are proved in
  -- `Exploding/Support/ASProof3.lean` and `Exploding/Support/ASProof4.lean`.
  have hpodo : ∀ η : Site d → ℤ, (∀ x, 2 * (d : ℤ) - 2 ≤ η x) →
      (∀ x, η x ≤ 2 * (d : ℤ) - 1) → ¬ Robust η →
        (penultimateCluster η (0 : Site d)).Finite →
          ∃ t0 : ℕ, ∀ x ∈ penultimateCluster η (0 : Site d),
            1 ≤ podo (explodingPile η) t0 x := by
    intro η hlow hhigh hnr hfin
    sorry
  exact as3_approximate_subadditive_of_gaps d hd p hp hp1 hLSSB hHole hChem
    (as4_hrobust d hd) hpodo
