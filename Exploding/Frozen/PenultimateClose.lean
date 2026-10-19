/-
Lemma 3.7 of the paper: the last-wave and penultimate-cluster arrival times are
polylogarithmically close.
-/
import Exploding.Support.Vocab
import Exploding.Support.Wave
import Exploding.Support.SubPub
import Exploding.Support.PCloseProofFinal
import Exploding.Frozen.PenultimateUpperBound
import Exploding.Support.PenultimateCloseP1
import Exploding.External.LiggettSchonmannStaceyBoundedDegree
import Exploding.External.MathieuHoles
import Exploding.External.AntalPisztora

open Exploding LatticeProb MeasureTheory

/-- **Lemma 3.7** (`paper/corrected-arxiv/exploding-corrected-arxiv.tex:960-965`, label `lemma:last_penultimate_close`).

"There exists a constant `γ > 0` so that on an event of probability 1, for all
`n` sufficiently large and `|x| ≤ n`, `T̂(x) ≤ T̃(x) ≤ T̂(x) + (log n)^γ`."

Both arrival times are taken in `ℕ∞`.  The first inequality is stated there;
the second is stated through natural numbers equal to them, which also records
that both are finite.

Section 3 runs on the event of Proposition 2.2, so the results the paper cites
for it enter as explicit hypotheses: `hLSSB` (Liggett, Schonmann and Stacey,
Corollary 1.4), `hHole` (Mathieu, Lemma 5.2) and `hChem` (Antal and Pisztora,
Theorem 1.1). -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.last_penultimate_close (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
        lastArrival η (0 : Site d) x ≤ clusterArrival η (0 : Site d) x ∧
          ∃ a b : ℕ, lastArrival η (0 : Site d) x = (a : ℕ∞) ∧
            clusterArrival η (0 : Site d) x = (b : ℕ∞) ∧ (b : ℝ) ≤ (a : ℝ) + Real.log n ^ γ
-- FROZEN-STATEMENT-END
:= by
  rcases lt_or_eq_of_le hp1 with hlt | heq
  · obtain ⟨γ, hγ, hcore⟩ := pclose_second d hd p hp hlt hLSSB hHole hChem
    refine ⟨γ, hγ, ?_⟩
    filter_upwards [hcore] with η hη
    obtain ⟨n0, hn0⟩ := hη
    exact ⟨n0, fun n hn x hx =>
      ⟨lastArrival_le_clusterArrival η (0 : Site d) x, hn0 n hn x hx⟩⟩
  · subst heq
    exact last_penultimate_close_p1 d hd
