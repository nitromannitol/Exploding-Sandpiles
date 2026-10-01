/-
Proposition 3.1 of the paper: the rescaled last-wave arrival times converge.
-/
import Exploding.Support.Vocab
import Exploding.Support.LWCProof
import Exploding.Support.LWCProof2
import Exploding.Support.LWCProof3
import Exploding.External.LiggettSchonmannStaceyBoundedDegree
import Exploding.External.MathieuHoles
import Exploding.External.AntalPisztora
import Exploding.Support.LWCLipE

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
  -- The one open conjunction (gate rule 11): the moment-free Kingman step producing the
  -- limit shape `N`; the far bound of `eq:lastwave_lipschitz` is `lwcl_far_lipschitz`.  The real-analysis
  -- upgrade from lattice directions to locally uniform convergence is proved in
  -- `Exploding.Support.LWCProof3`, and the transfer to the last wave is proved below.
  obtain ⟨hking, hlip⟩ :
      (∃ N : (Fin d → ℝ) → ℝ,
        Continuous N ∧ ConvexOn ℝ Set.univ N ∧
        (∀ (c : ℝ), 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
        ∀ᵐ η ∂(toyLaw d p),
          (∀ x : Site d, clusterArrival η (0 : Site d) x ≠ ⊤) ∧
          ∀ v : Site d,
            Tendsto (fun n : ℕ =>
                ((clusterArrival η (0 : Site d) ((n : ℤ) • v)).toNat : ℝ) / (n : ℝ))
              atTop (nhds (N (lwc2_toReal v))))
      ∧
      (∀ᵐ η ∂(toyLaw d p), ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        ∀ x x' : Site d, x ∈ cent d n → x' ∈ cent d n →
          |((clusterArrival η (0 : Site d) x).toNat : ℝ) -
            ((clusterArrival η (0 : Site d) x').toNat : ℝ)|
              ≤ C * (mnorm (x - x') : ℝ) + Real.log n ^ γ) :=
    ⟨by sorry, Exploding.lwcl_far_lipschitz d hd p hp hp1 hLSSB hHole hChem⟩
  obtain ⟨N, hcont, hconvex, hhom, hking_ae⟩ := hking
  refine ⟨N, hcont, hconvex, hhom, ?_⟩
  apply lwc_transfer d hd p hp hp1 hLSSB hHole hChem N
  filter_upwards [hking_ae, hlip] with η hk hl
  obtain ⟨C, γ, hC, hγ, hrest⟩ := hl
  obtain ⟨n0, hn0⟩ := hrest
  exact ⟨hk.1, fun K hK ε hε =>
    lwc3_lattice_upgrade (fun x => ((clusterArrival η (0 : Site d) x).toNat : ℝ)) N (by omega)
      hcont hhom hk.2 C γ hC hγ ⟨n0, hn0⟩ K hK ε hε⟩
