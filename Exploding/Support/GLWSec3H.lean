/-
Proposition 5.1 of the paper (generalized last wave), the Section-3 assembly, part H:
`glw_Conclusion` from the paper's local bound `eq:generalized_lipschitz`, the moment-free Kingman
theorem and the closeness of the two arrival times (`glws_Close`); and `glw2_Section3Convergence`
from the stronger local bound of `glw2_LipschitzLocal`.
-/
import Exploding.Support.GLWSec3G
import Exploding.Support.MKingman

open Exploding LatticeProb MeasureTheory Filter
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-- **The local bound of the paper** (`eq:generalized_lipschitz`, with finiteness of the last
wave at every site): under the hypotheses of Proposition 5.1 there are constants `γ, C` such that,
on an event of probability one, every site has a last wave and, for all `n` large and
`x, x' ∈ [-n,n]^d`,
`T̃(x) ≤ C |x| + (log n)^γ` and `T̃(x') ≤ T̃(x) + C |x - x'| + (log n)^γ`,
all arrival times being measured from the origin. -/
def glws_Origin (d : ℕ) (ηmin : ℤ) (P : Measure (Site d → ℤ)) : Prop :=
  IsProbabilityMeasure P → (∀ᵐ η ∂P, InOmega d ηmin η) →
  FiniteRangeOfDependence d P → PathFillingHyp d P → StronglyBoxCrossingHyp d P →
  Exploding.External.LiggettSchonmannStacey →
  Exploding.External.LiggettSchonmannStaceyBoundedDegree →
  Exploding.External.MathieuHoleVolume →
  Exploding.External.AntalPisztoraChemicalDistance →
  ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧ ∀ᵐ η ∂P, glws_Loc0 d γ C η

/-- **The Section-3 assembly, core form.**  The paper's local bound, the moment-free Kingman
theorem and the closeness of the two arrival times give the conclusion of Proposition 5.1. -/
theorem glws_core (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0) (P : Measure (Site d → ℤ))
    (hP : IsProbabilityMeasure P) (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η)
    (hstat : StationaryOn d L P) (hmix : glws_Mix d L P) (hKing : glw2_KingmanCore)
    {γ C : ℝ} (hγ : 0 < γ) (hC : 0 < C) (hlocae : ∀ᵐ η ∂P, glws_Loc0 d γ C η)
    {γ' : ℝ} (hcl : ∀ᵐ η ∂P, ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
      lastArrival η (0 : Site d) x ≤ clusterArrival η (0 : Site d) x ∧
        ∃ a b : ℕ, lastArrival η (0 : Site d) x = (a : ℕ∞) ∧
          clusterArrival η (0 : Site d) x = (b : ℕ∞) ∧ (b : ℝ) ≤ (a : ℝ) + Real.log n ^ γ') :
    glw_Conclusion d P := by
  -- the good event: finiteness of the arrival times from the points of `L`
  have hshift : ∀ a : Site d, ∀ᵐ η ∂P, a ∈ L →
      ∀ b : Site d, clusterArrival η a b ≠ ⊤ := by
    intro a
    by_cases ha : a ∈ L
    · have hq := (glw_shift_ergodic_meas_pres d L P hstat a ha).quasiMeasurePreserving
      filter_upwards [hq.ae hlocae] with η hη _ b
      have h := glws_loc0_finite hη (b - a)
      have heq := lwc_cluster_shift d η a (0 : Site d) (b - a)
      rw [add_zero, show a + (b - a) = b from by abel] at heq
      rw [← heq]
      exact h
    · exact Eventually.of_forall fun η h => absurd h ha
  have hGae : ∀ᵐ η ∂P, η ∈ glws_G d ηmin L := by
    have hall : ∀ᵐ η ∂P, ∀ a : Site d, a ∈ L → ∀ b : Site d, clusterArrival η a b ≠ ⊤ :=
      ae_all_iff.mpr hshift
    filter_upwards [hlocae, hsupp, hall] with η h h' h''
    exact ⟨h', h.1, h''⟩
  obtain ⟨N0, hN0⟩ := glws_lattice_data hd ηmin hηmin L hL P hP hstat hKing hGae hC.le hlocae hmix
  obtain ⟨η₀, hη₀G, hη₀loc, hη₀lat⟩ :=
    glws_exists_good L P hP ηmin hGae hlocae N0 hN0
  have hlipN0 := glws_N0_lip hη₀loc hη₀lat
  have hhomN0 := fun (k : ℕ) (v : Site d) => glws_N0_nsmul hη₀lat v k
  have hsubN0 := glws_N0_subadd hd ηmin hηmin L hL P hP hstat hGae N0 hN0 hη₀lat
  obtain ⟨N, hNcont, hNconv, hNhom, hNlat⟩ := glws_extend C hC.le N0 hlipN0 hhomN0 hsubN0
  refine ⟨N, hNcont, hNconv, hNhom, ?_⟩
  -- the penultimate-cluster statement
  have hunif : ∀ᵐ η ∂P,
      (∀ x : Site d, clusterArrival η (0 : Site d) x ≠ ⊤) ∧
        ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
            |((clusterArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
              - N y| ≤ ε := by
    have hall : ∀ᵐ η ∂P, ∀ v : Site d,
        Tendsto (fun n : ℕ => glws_f η ((n : ℤ) • v) / (n : ℝ)) atTop (nhds (N0 v)) :=
      ae_all_iff.mpr hN0
    filter_upwards [hlocae, hall] with η hLoc hlat
    refine ⟨fun x => glws_loc0_finite hLoc x, fun K hK ε hε => ?_⟩
    have hlat' : ∀ v : Site d,
        Tendsto (fun n : ℕ => glws_f η ((n : ℤ) • v) / (n : ℝ)) atTop
          (nhds (N (lwc2_toReal v))) := by
      intro v
      rw [hNlat v]
      exact hlat v
    exact lwc3_lattice_upgrade (glws_f η) N (by omega) hNcont hNhom hlat' C γ hC hγ
      (glws_two_sided hLoc) K hK ε hε
  have htrans := glws_transfer P N γ' hcl hunif
  filter_upwards [htrans, hGae, hsupp] with η hη hG hΩ
  have hlow : ∀ x, 0 ≤ η x := fun x => le_trans hηmin (hΩ x).1
  have hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1 := fun x => (hΩ x).2
  obtain ⟨n, hn, hns⟩ := hG.2.1 (0 : Site d)
  exact ⟨glws_explosive hd η hlow hhigh ⟨n, hn, hns⟩, hη⟩

/-- **The conclusion of Proposition 5.1** from the paper's local bound, the moment-free Kingman
theorem and the closeness of the two arrival times.  The finite-range mixing (B) is derived
here from Hypothesis 5.1, and the standing hypotheses are those of the frozen statement. -/
theorem glws_conclusion (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0) (P : Measure (Site d → ℤ))
    (hP : IsProbabilityMeasure P) (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η)
    (hstat : StationaryOn d L P)
    (h1 : FiniteRangeOfDependence d P) (h3 : PathFillingHyp d P)
    (h4 : StronglyBoxCrossingHyp d P)
    (hLSS : Exploding.External.LiggettSchonmannStacey)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance)
    (hmk : mk_kingman_linear) (horig : glws_Origin d ηmin P) (hclose : glws_Close d ηmin P) :
    glw_Conclusion d P := by
  obtain ⟨γ, C, hγ, hC, hloc⟩ := horig hP hsupp h1 h3 h4 hLSS hLSSB hHole hChem
  obtain ⟨γ', _, hcl⟩ := hclose hP hsupp h1 h3 h4 hLSS hLSSB hHole hChem
  have hmix : glws_Mix d L P := fun y hy hy0 s S hS =>
    glw2_shift_mixing d P h1 y (glw_shift_ergodic_meas_pres d L P hstat y hy) hy0 s S hS
  exact glws_core d hd ηmin hηmin L hL P hP hsupp hstat hmix (glw2_KingmanCore_of_mk hmk)
    hγ hC hloc hcl

/-- **The Section-3 assembly of Proposition 5.1**, in the form of `glw2_Section3Convergence`:
given the closeness of the penultimate-cluster and last-wave arrival times, the conclusion follows
from the subadditive ergodic core and the local Lipschitz bound `glw2_LipschitzLocal`, the
finite-range facts (A) and (B) and the setting.  The local bound is used only through the paper's
weaker form `glws_Loc0`. -/
theorem glws_section3 (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0) (P : Measure (Site d → ℤ))
    (hclose : glws_Close d ηmin P) :
    glw2_Section3Convergence d hd ηmin hηmin L hL P := by
  intro hP hsupp hstat _herg h1 h3 h4 hLSS hLSSB hHole hChem _hA hB hKing hlips
  obtain ⟨γ, C, hγ, hC, hloc⟩ := hlips hP hsupp h1 h3 h4 hLSS hLSSB hHole hChem
  obtain ⟨γ', _, hcl⟩ := hclose hP hsupp h1 h3 h4 hLSS hLSSB hHole hChem
  have hloc0 : ∀ᵐ η ∂P, glws_Loc0 d γ C η := by
    filter_upwards [hloc, hsupp] with η h h'
    exact glws_Loc_to_Loc0 hd (fun x => le_trans hηmin (h' x).1) (fun x => (h' x).2) h
  exact glws_core d hd ηmin hηmin L hL P hP hsupp hstat hB hKing hγ hC hloc0 hcl

end Exploding
