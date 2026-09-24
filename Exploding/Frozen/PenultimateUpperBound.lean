/-
Lemma 3.6 of the paper: a linear upper bound on the last-wave arrival times.
-/
import Exploding.Support.Vocab
import Exploding.External.LiggettSchonmannStaceyBoundedDegree
import Exploding.External.MathieuHoles
import Exploding.External.AntalPisztora

open Exploding LatticeProb MeasureTheory

/-- **Lemma 3.6** (`exploding.tex:807-812`, label
`lemma:penultimate_upper_bound`).

"There are constants `γ` and `C` so that on an event of probability 1, for all
`n` sufficiently large and `|x| ≤ n`, `T̂(x) ≤ C |x| + (log n)^γ`."

`γ` and `C` are deterministic, so they are bound before `η`; the threshold in
`n` may depend on `η`, so it is bound inside.  `T̂` is `lastArrival η 0`, taken
in `ℕ∞`; the bound is stated through a natural number equal to it, which also
records that it is finite.

Section 3 runs on the event of Proposition 2.2, so the results the paper cites
for it enter as explicit hypotheses: `hLSSB` (Liggett, Schonmann and Stacey,
Corollary 1.4), `hHole` (Mathieu, Lemma 5.2) and `hChem` (Antal and Pisztora,
Theorem 1.1). -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.penultimate_upper_bound (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧
      ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
        ∃ m : ℕ, lastArrival η (0 : Site d) x = (m : ℕ∞) ∧
          (m : ℝ) ≤ C * (mnorm x : ℝ) + Real.log n ^ γ
-- FROZEN-STATEMENT-END
:= by sorry
