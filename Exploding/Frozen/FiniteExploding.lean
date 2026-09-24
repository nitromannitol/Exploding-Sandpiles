/-
Lemma 3.2 of the paper: the last wave is well defined.
-/
import Exploding.Support.Vocab
import Exploding.External.LiggettSchonmannStaceyBoundedDegree
import Exploding.External.MathieuHoles
import Exploding.External.AntalPisztora

open Exploding LatticeProb MeasureTheory

/-- **Lemma 3.2** (`exploding.tex:720-722`, label `lemma:finite_exploding`).

"The last-wave is well-defined, `M̂_η(0) < ∞`."

`M̂_η(0)` is the least `n ≥ 1` whose `n`-wave at the origin does not stabilize;
it is finite exactly when such an `n` exists, which is the conclusion here.
Section 3 draws `η` from the probability-one event of Proposition 2.2, so the
statement is almost sure under the law `(1.2)`.

Section 3 runs on the event of Proposition 2.2, so the results the paper cites
for it enter as explicit hypotheses: `hLSSB` (Liggett, Schonmann and Stacey,
Corollary 1.4), `hHole` (Mathieu, Lemma 5.2) and `hChem` (Antal and Pisztora,
Theorem 1.1). -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.finite_exploding (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∀ᵐ η ∂(toyLaw d p), ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d)
-- FROZEN-STATEMENT-END
:= by sorry
