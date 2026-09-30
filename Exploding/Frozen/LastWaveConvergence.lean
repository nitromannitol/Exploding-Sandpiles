/-
Proposition 3.1 of the paper: the rescaled last-wave arrival times converge.
-/
import Exploding.Support.Vocab
import Exploding.Support.LWCProof
import Exploding.External.LiggettSchonmannStaceyBoundedDegree
import Exploding.External.MathieuHoles
import Exploding.External.AntalPisztora

open Exploding LatticeProb MeasureTheory Filter

/-- **Proposition 3.1** (`exploding.tex:846-852`, label
`prop:convergence_of_the_last_wave`).

"On an event of probability 1, the rescaled last-wave arrival times
`n^{-1} T̂_η([n x])` converge locally uniformly to `N_p`, a continuous, convex,
one-homogeneous function on `ℝ^d`."

`N_p` is deterministic, so it is bound before `η`.  Locally uniform convergence
is written in its `ε`-form, and the finiteness of `T̂` is asserted, so that no
supremum over an empty set and no `ENat.toNat ⊤` is read.

Section 3 runs on the event of Proposition 2.2, so the results the paper cites
for it enter as explicit hypotheses: `hLSSB` (Liggett, Schonmann and Stacey,
Corollary 1.4), `hHole` (Mathieu, Lemma 5.2) and `hChem` (Antal and Pisztora,
Theorem 1.1). -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.convergence_of_the_last_wave (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ N : (Fin d → ℝ) → ℝ,
      Continuous N ∧
      ConvexOn ℝ Set.univ N ∧
      (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
      ∀ᵐ η ∂(toyLaw d p),
        (∀ x : Site d, lastArrival η (0 : Site d) x ≠ ⊤) ∧
          ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
            ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
              |((lastArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
                - N y| ≤ ε
-- FROZEN-STATEMENT-END
:= by
  -- The locally uniform convergence of the rescaled penultimate-cluster arrival
  -- times, with the continuity, convexity and one-homogeneity of the limit: the
  -- quantitative core of the paper's proof (Lemmas 3.6 and 3.7, the far Lipschitz
  -- bound of (eq:lastwave_lipschitz), and the repaired moment-free Kingman argument
  -- of the 2026-09-24 note).  The transfer from the penultimate-cluster arrival
  -- times to the last-wave arrival times is proved in `Exploding.Support.LWCProof`.
  have hunif : ∃ N : (Fin d → ℝ) → ℝ,
      Continuous N ∧ ConvexOn ℝ Set.univ N ∧
      (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
      ∀ᵐ η ∂(toyLaw d p),
        (∀ x : Site d, clusterArrival η (0 : Site d) x ≠ ⊤) ∧
          ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
            ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
              |((clusterArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
                - N y| ≤ ε := by
    sorry
  obtain ⟨N, hcont, hconv, hhom, hcluster⟩ := hunif
  exact ⟨N, hcont, hconv, hhom,
    lwc_transfer d hd p hp hp1 hLSSB hHole hChem N hcluster⟩
