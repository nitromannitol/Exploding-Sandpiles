/-
Proposition 5.1 of the paper (generalized last wave), the Section-3 assembly, part H:
`glw2_Section3Convergence` from the local Lipschitz bound, the moment-free Kingman theorem and
the closeness of the two arrival times (`glws_Close`).
-/
import Exploding.Support.GLWSec3G

open Exploding LatticeProb MeasureTheory Filter
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-- **The Section-3 assembly of Proposition 5.1.**  Given the closeness of the penultimate-cluster
and last-wave arrival times, the conclusion follows from the finite-range facts (A) and (B), the
subadditive ergodic core and the local Lipschitz bound; it uses neither (A) nor the other
hypotheses beyond what (B) and `hlips` already carry. -/
theorem glws_section3 (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0) (P : Measure (Site d → ℤ))
    (hclose : glws_Close d ηmin P) :
    glw2_Section3Convergence d hd ηmin hηmin L hL P := by
  intro hP hsupp hstat _herg h1 h3 h4 hLSS hLSSB hHole hChem _hA hB hKing hlips
  obtain ⟨γ, C, hγ, hC, hloc⟩ := hlips hP hsupp h1 h3 h4 hLSS hLSSB hHole hChem
  have hmix : glws_Mix d L P := hB
  have hGae : ∀ᵐ η ∂P, η ∈ glws_G d ηmin := by
    filter_upwards [hloc, hsupp] with η h h'
    exact ⟨h', h.1, fun a b => glws_loc_finite h a b⟩
  have hlocae : ∀ᵐ η ∂P, glws_Loc d γ C η := hloc
  obtain ⟨N0, hN0⟩ := glws_lattice_data hd ηmin hηmin L hL P hP hstat hKing hGae hC.le hlocae hmix
  obtain ⟨η₀, hη₀G, hη₀loc, hη₀lat⟩ :=
    glws_exists_good P hP ηmin hGae hlocae N0 hN0
  have hlipN0 := glws_N0_lip hd ηmin hηmin hη₀G hη₀loc hη₀lat
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
    filter_upwards [hGae, hlocae, hall] with η hG hLoc hlat
    refine ⟨fun x => hG.2.2 0 x, fun K hK ε hε => ?_⟩
    have hlow : ∀ x, 0 ≤ η x := fun x => le_trans hηmin (hG.1 x).1
    have hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1 := fun x => (hG.1 x).2
    have hlat' : ∀ v : Site d,
        Tendsto (fun n : ℕ => glws_f η ((n : ℤ) • v) / (n : ℝ)) atTop
          (nhds (N (lwc2_toReal v))) := by
      intro v
      rw [hNlat v]
      exact hlat v
    exact lwc3_lattice_upgrade (glws_f η) N (by omega) hNcont hNhom hlat' C γ hC hγ
      (glws_two_sided hd hlow hhigh hLoc) K hK ε hε
  obtain ⟨γ', _hγ', hcl⟩ := hclose hP hsupp h1 h3 h4 hLSS hLSSB hHole hChem
  have htrans := glws_transfer P N γ' hcl hunif
  filter_upwards [htrans, hGae, hlocae] with η hη hG hLoc
  have hlow : ∀ x, 0 ≤ η x := fun x => le_trans hηmin (hG.1 x).1
  have hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1 := fun x => (hG.1 x).2
  obtain ⟨n, hn, hns⟩ := hLoc.1 (0 : Site d)
  exact ⟨glws_explosive hd η hlow hhigh ⟨n, hn, hns⟩, hη⟩

end Exploding
