/-
Lemma 3.2 of the paper: the last wave is well defined.
-/
import Exploding.Support.Vocab
import Exploding.Support.SubFinite
import Exploding.Support.SubCross
import Exploding.Support.ArxivP1FiniteExploding
import Exploding.External.LiggettSchonmannStaceyBoundedDegree
import Exploding.External.MathieuHoles
import Exploding.External.AntalPisztora

open Exploding LatticeProb MeasureTheory

/-- **Lemma 3.2** (`paper/corrected-arxiv/exploding-corrected-arxiv.tex:848-850`, label `lemma:finite_exploding`).

"The last-wave is well-defined, `M̂_η(0) < ∞`."

`M̂_η(0)` is the least `n ≥ 1` whose `n`-wave at the origin does not stabilize;
it is finite exactly when such an `n` exists, which is the conclusion here.
Section 3 draws `η` from the probability-one event of Proposition 2.2, so the
statement is almost sure under the law `(2)`.

Section 3 runs on the event of Proposition 2.2, so the results the paper cites
for it enter as explicit hypotheses: `hLSSB` (Liggett, Schonmann and Stacey,
Corollary 1.4), `hHole` (Mathieu, Lemma 5.2) and `hChem` (Antal and Pisztora,
Theorem 1.1). -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.finite_exploding (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∀ᵐ η ∂(toyLaw d p), ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d)
-- FROZEN-STATEMENT-END
:= by
  rcases lt_or_eq_of_le hp1 with hp1 | heq
  ·
    filter_upwards [aux_finite_exploding_covers d hd p hp hp1 hLSSB hHole hChem,
      aux_finite_exploding_bounds d p hp hp1] with η hη hbounds
    obtain ⟨N, t0, k, hN, hk, Cinf, i, hCinf, hi, hcover⟩ := hη
    refine ⟨N, Nat.one_le_of_lt hN, ?_⟩
    refine aux_finite_exploding_propagate d hd η
      (fun x => by have := (hbounds x).1; linarith) (fun x => (hbounds x).2) N t0 k hk
      (fun a b hgood hadj s hs => ?_) Cinf i hCinf hi hcover
    obtain ⟨dir, hdir⟩ := hadj
    obtain ⟨dir', hne⟩ : ∃ dir' : Fin d, dir' ≠ dir := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      have hcard : Fintype.card (Fin d) = 1 := Fintype.card_eq_one_iff.mpr ⟨dir, hcon⟩
      rw [Fintype.card_fin] at hcard
      omega
    exact finite_exploding_step hd η (fun x => by have := (hbounds x).1; linarith)
      (fun x => (hbounds x).2) N k hN hk (0 : Site d) a b hgood dir hdir dir' hne s hs
  · subst p
    exact finite_exploding_p1 d hd
