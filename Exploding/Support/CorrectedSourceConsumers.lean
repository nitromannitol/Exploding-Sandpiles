/-
Consumers of Proposition 2.2 (`prop:renormalization_properties`) and of the statements that
depend on it: Lemmas 3.2, 3.5, 3.6 and 3.7, Proposition 3.8 and Proposition 4.1 of the paper.

The projection `renormalization_standing_fields` reads the standing-event fields of
Proposition 2.2.  Each named consumer discharges the Liggett–Schonmann–Stacey and Mathieu
hypotheses by the in-repository producers `xlse_lss_bounded_degree` and `xmf_proved`, and
keeps the Antal–Pisztora chemical-distance hypothesis as its only explicit input.
-/
import Exploding.Frozen.Renormalization
import Exploding.Frozen.FiniteExploding
import Exploding.Frozen.PenultimateCluster
import Exploding.Frozen.PenultimateUpperBound
import Exploding.Frozen.PenultimateClose
import Exploding.Frozen.LastWaveConvergence
import Exploding.Frozen.ApproximateSubadditive
import Exploding.Support.ExtLSSCountable
import Exploding.Support.ExtMHHoleVolume

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding.CorrectedSource

/-- The standing-event fields of Proposition 2.2: the infinite connected good set, the
whole-complement hole bound and the induced chemical-distance bound, with the same `k0`,
constants `c`, `C`, almost-sure event and law. The unique-component clauses of
Proposition 2.2 are not used. -/
theorem renormalization_standing_fields (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᵐ η ∂(toyLaw d p),
        ∃ Cinf : Set (Site d), IsInfiniteConnectedGoodSet η k Cinf ∧
          (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)),
            x ∉ Cinf →
              (componentIn Cinfᶜ x).Finite ∧
                ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2)) ∧
          (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ Cinf, ∀ y ∈ Cinf,
            mnorm x ≤ (n : ℤ) → Real.log n ^ (2 : ℕ) ≤ (mnorm (x - y) : ℝ) →
              ∃ m : ℕ, chemDist Cinf x y = (m : ℕ∞) ∧
                c * (mnorm (x - y) : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ C * (mnorm (x - y) : ℝ)) := by
  obtain ⟨k0, hk⟩ := Exploding.Frozen.renormalization_properties d hd p hp hp1 hLSSB hHole hChem
  refine ⟨k0, fun k hk' => ?_⟩
  obtain ⟨c, C, hc, hC, hae⟩ := hk k hk'
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [hae] with η hη
  obtain ⟨Cinf, h1, h2, h3, -, -⟩ := hη
  exact ⟨Cinf, h1, h2, h3⟩

/-- Lemma 3.2 (`lemma:finite_exploding`): the whole conclusion of
`Exploding.Frozen.finite_exploding`, with the in-repository producers supplied. -/
theorem finite_exploding (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∀ᵐ η ∂(toyLaw d p), ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d) :=
  Exploding.Frozen.finite_exploding d hd p hp hp1 Exploding.xlse_lss_bounded_degree
    Exploding.xmf_proved hChem

/-- Lemma 3.5 (`lemma:last_penultimate_cluster`): the whole conclusion of
`Exploding.Frozen.last_penultimate_cluster`, with the in-repository producers supplied. -/
theorem last_penultimate_cluster (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
        ∀ y ∈ penultimateCluster η x, ∀ i, ((|y i - x i| : ℤ) : ℝ) ≤ Real.log n ^ γ :=
  Exploding.Frozen.last_penultimate_cluster d hd p hp hp1 Exploding.xlse_lss_bounded_degree
    Exploding.xmf_proved hChem

/-- Lemma 3.6 (`lemma:penultimate_upper_bound`): the whole conclusion of
`Exploding.Frozen.penultimate_upper_bound`, with the in-repository producers supplied. -/
theorem penultimate_upper_bound (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧
      ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
        ∃ m : ℕ, lastArrival η (0 : Site d) x = (m : ℕ∞) ∧
          (m : ℝ) ≤ C * (mnorm x : ℝ) + Real.log n ^ γ :=
  Exploding.Frozen.penultimate_upper_bound d hd p hp hp1 Exploding.xlse_lss_bounded_degree
    Exploding.xmf_proved hChem

/-- Lemma 3.7 (`lemma:last_penultimate_close`): the whole conclusion of
`Exploding.Frozen.last_penultimate_close`, with the in-repository producers supplied. -/
theorem last_penultimate_close (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
        lastArrival η (0 : Site d) x ≤ clusterArrival η (0 : Site d) x ∧
          ∃ a b : ℕ, lastArrival η (0 : Site d) x = (a : ℕ∞) ∧
            clusterArrival η (0 : Site d) x = (b : ℕ∞) ∧ (b : ℝ) ≤ (a : ℝ) + Real.log n ^ γ :=
  Exploding.Frozen.last_penultimate_close d hd p hp hp1 Exploding.xlse_lss_bounded_degree
    Exploding.xmf_proved hChem

/-- Proposition 3.8 (`prop:convergence_of_the_last_wave`): the whole conclusion of
`Exploding.Frozen.convergence_of_the_last_wave`, with the in-repository producers supplied. -/
theorem convergence_of_the_last_wave (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
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
                - N y| ≤ ε :=
  Exploding.Frozen.convergence_of_the_last_wave d hd p hp hp1 Exploding.xlse_lss_bounded_degree
    Exploding.xmf_proved hChem

/-- Proposition 4.1 (`prop:approximate_subadditive`): the whole conclusion of
`Exploding.Frozen.approximate_subadditive`, with the in-repository producers supplied. -/
theorem approximate_subadditive (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∀ᵐ η ∂(toyLaw d p), ∃ C1 C2 : ℕ, ∀ x : Site d,
      arrival η x ≤ lastArrival η (0 : Site d) x + (C1 : ℕ∞) ∧
        lastArrival η (0 : Site d) x ≤ arrival η x + (C2 : ℕ∞) :=
  Exploding.Frozen.approximate_subadditive d hd p hp hp1 Exploding.xlse_lss_bounded_degree
    Exploding.xmf_proved hChem

end Exploding.CorrectedSource
