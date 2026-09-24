/-
Lemma 3.5 of the paper: penultimate clusters are polylogarithmically small.
-/
import Exploding.Support.Vocab
import Exploding.External.LiggettSchonmannStaceyBoundedDegree
import Exploding.External.MathieuHoles
import Exploding.External.AntalPisztora

open Exploding LatticeProb MeasureTheory

/-- **Lemma 3.5** (`exploding.tex:792-798`, label
`lemma:last_penultimate_cluster`).

"There is a constant `γ > 0` so that for all `n` sufficiently large and
`|x| ≤ n`, `P(x) ⊂ x + [-(log n)^γ, (log n)^γ]^d`."

`γ` is deterministic, so it is bound before `η`; "for all `n` sufficiently
large" is a threshold that may depend on `η`, so it is bound inside.  `|x|` is
the Manhattan norm.

Section 3 runs on the event of Proposition 2.2, so the results the paper cites
for it enter as explicit hypotheses: `hLSSB` (Liggett, Schonmann and Stacey,
Corollary 1.4), `hHole` (Mathieu, Lemma 5.2) and `hChem` (Antal and Pisztora,
Theorem 1.1). -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.last_penultimate_cluster (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
        ∀ y ∈ penultimateCluster η x, ∀ i, ((|y i - x i| : ℤ) : ℝ) ≤ Real.log n ^ γ
-- FROZEN-STATEMENT-END
:= by sorry
