/-
Proposition 5.1 of the paper: convergence of the last-wave under the general
hypotheses.
-/
import Exploding.Support.Hypotheses
import Exploding.Support.GLWProofAux
import Exploding.Support.GLWProof2
import Exploding.Support.MKingman
import Exploding.Support.MKingman4
import Exploding.External.LiggettSchonmannStacey
import Exploding.External.LiggettSchonmannStaceyBoundedDegree
import Exploding.External.MathieuHoles
import Exploding.External.AntalPisztora
import Exploding.Support.KingmanBAWireGlw
import Exploding.Support.GLWSec3J
import Exploding.Support.GLWSec3AI
import Exploding.Support.S3CloseI
import Exploding.Support.PathFillingNonneg

open Exploding LatticeProb MeasureTheory Filter

/-- **Proposition 5.1** (`paper/corrected-arxiv/exploding-corrected-arxiv.tex:1325-1329`,
label `prop:convergence_of_the_generalized_last_wave`; setting at lines 1233-1248).

"Under Hypotheses 5.1, 5.3, and 5.4, on an event of probability 1, `η` is explosive and the
rescaled last-wave arrival times `n^{-1} T̂_η([nx]) := n^{-1} min{t > 0 : u_t([nx]) > 0}`
converge locally uniformly to `N_η`, a deterministic, continuous, convex, one-homogeneous
function on `ℝ^d` depending only on the law of `η`."

`N_η` depends only on the law, so it is bound before `η` and after `P`.  Locally
uniform convergence is written in its `ε`-form and the finiteness of `T̂` is
asserted, so that no supremum over an empty set and no `ENat.toNat ⊤` is read.
The setting is that of Section 5 with an arbitrary integer `η_min`: no sign is assumed
for `η_min`, and the background satisfies `η_min ≤ η ≤ 2d - 1` almost surely (`hsupp`).
The ergodicity premise is measurable ergodicity (`MeasurableErgodicOn`), which tests the
measurable events invariant under the translations in `L`, as the ergodicity on `(Ω, F)`
of the source does.  The premise `herg` is kept as the source states it; the proof does
not use it.  Nonnegativity of the background is not assumed: it is derived almost surely
from `hsupp` and `h3` by `Exploding.pathFillingHyp_nonneg`.

The results the paper cites in the proof enter as explicit hypotheses: `hLSS`
(Liggett, Schonmann and Stacey, Theorem 0.0), and, for the rerun of Section 3,
`hLSSB` (Liggett, Schonmann and Stacey, Corollary 1.4), `hHole` (Mathieu,
Lemma 5.2) and `hChem` (Antal and Pisztora, Theorem 1.1). -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.convergence_of_the_generalized_last_wave (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0)
    (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η)
    (hstat : StationaryOn d L P) (herg : MeasurableErgodicOn d L P)
    (h1 : FiniteRangeOfDependence d P) (h3 : PathFillingHyp d P)
    (h4 : StronglyBoxCrossingHyp d P)
    (hLSS : Exploding.External.LiggettSchonmannStacey)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ N : (Fin d → ℝ) → ℝ,
      Continuous N ∧
      ConvexOn ℝ Set.univ N ∧
      (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
      ∀ᵐ η ∂P,
        Explosive η ∧ (∀ x : Site d, lastArrival η (0 : Site d) x ≠ ⊤) ∧
          ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
            ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
              |((lastArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
                - N y| ≤ ε
-- FROZEN-STATEMENT-END
:= by
  -- The ergodicity premise is kept as the source states it; this argument does not use it.
  have _ := herg
  -- Almost surely `η ≤ 2d - 1` by `hsupp`, so the path-filling producer gives `0 ≤ η`.
  have hup : ∀ᵐ η ∂P, ∀ x : Site d, η x ≤ 2 * (d : ℤ) - 1 :=
    hsupp.mono fun η h x => (h x).2
  have hnn : ∀ᵐ η ∂P, ∀ x : Site d, 0 ≤ η x :=
    Exploding.pathFillingHyp_nonneg hd P hup h3
  -- Hence almost surely `η ∈ Ω` with minimum `0`; the zero-minimum argument below applies.
  have hsupp0 : ∀ᵐ η ∂P, InOmega d 0 η :=
    (hnn.and hup).mono fun η h x => ⟨h.1 x, h.2 x⟩
  -- Combine the origin estimate and the penultimate-to-last-wave estimate.
  -- The Lipschitz subadditive theorem supplies the limit.
  obtain ⟨horig, hclose⟩ : glws_Origin d 0 P ∧ glws_Close d 0 P :=
    ⟨glws_origin d hd 0 le_rfl P, s3k_close d hd 0 le_rfl P⟩
  exact glws_conclusion d hd 0 le_rfl L hL P hP hsupp0 hstat h1 h3 h4 hLSS hLSSB hHole hChem
    horig hclose
