import Exploding.Support.ArxivBondHoleGeometry
import Exploding.Support.ArxivBondHoleTail

/-!
# A series bound for finite holes of actual bond clusters

For a finite component of the complement of an actual open-bond reachability
cluster, its volume is bounded by the square of its inner-boundary size. The
boundary is a star-connected defective set, so summing the near-root animal
estimate over its actual cardinality gives the stated series bound. The
outside-cluster condition and finiteness remain inside the event.
-/

open LatticeProb MeasureTheory

namespace Exploding

/-- Sum the near-root defective-animal bound over the inner-boundary sizes of
finite holes of actual open-bond reachability components. -/
theorem arxiv_bond_finite_hole_volume_prob_le_tsum (d : ℕ) (hd : 2 ≤ d) :
    ∃ K : ℕ, 1 ≤ K ∧
      ∀ (z : Site d) (s : ℕ) {q : ℝ}, 0 ≤ q → q ≤ 1 →
        bondPercolation d q
          {ζ | ∃ i : Site d,
            z ∉ {y : Site d | (openBondGraph ζ).Reachable i y} ∧
            (componentIn
              ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z).Finite ∧
            s ≤ (componentIn
              ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z).ncard} ≤
        ∑' m : ℕ, if s ≤ m ^ 2 then
          (((2 * m + 1) ^ d : ℕ) : ENNReal) *
            (K : ENNReal) ^ m *
            (ENNReal.ofReal (2 * (d : ℝ) * (1 - q))) ^ (m / 3 ^ d)
          else 0 := by
  classical
  obtain ⟨K, hK, hnear⟩ := arxiv_bond_near_defective_animal_prob_le d
  refine ⟨K, hK, ?_⟩
  intro z s q hq0 hq1
  let E : Set (RnBond d → Bool) := {ζ | ∃ i : Site d,
    z ∉ {y : Site d | (openBondGraph ζ).Reachable i y} ∧
    (componentIn
      ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z).Finite ∧
    s ≤ (componentIn
      ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z).ncard}
  let A : ℕ → Set (RnBond d → Bool) := fun m =>
    {ζ | s ≤ m ^ 2 ∧ ∃ p : Site d,
      (∀ k : Fin d, |p k - z k| ≤ (m : ℤ)) ∧
      ∃ F : Finset (Site d), p ∈ F ∧ F.card = m ∧
        xmh_SConn (F : Set (Site d)) ∧
        ∀ x ∈ F, rn_siteField ζ x = false}
  have hsub : E ⊆ ⋃ m : ℕ, A m := by
    rintro ζ ⟨i, hz, hfin, hs⟩
    let H : Set (Site d) :=
      componentIn ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z
    have hgeom := arxiv_bond_hole_size_and_anchor hd ζ i z hz hfin
    change H.ncard ≤ (innerBoundary H).ncard ^ 2 ∧
      ∃ p ∈ innerBoundary H,
        ∀ k : Fin d, |p k - z k| ≤ ((innerBoundary H).ncard : ℤ) at hgeom
    obtain ⟨hsize, p, hp, hnear'⟩ := hgeom
    let m : ℕ := (innerBoundary H).ncard
    have hsm : s ≤ m ^ 2 := by
      exact hs.trans (by simpa only [m] using hsize)
    have hboundaryFinite : (innerBoundary H).Finite :=
      hfin.subset fun _ hb => hb.1
    let F : Finset (Site d) := hboundaryFinite.toFinset
    have hF : (F : Set (Site d)) = innerBoundary H :=
      hboundaryFinite.coe_toFinset
    have hpF : p ∈ F := hboundaryFinite.mem_toFinset.mpr hp
    have hcard : F.card = m := by
      dsimp only [F, m]
      exact (Set.ncard_eq_toFinset_card (innerBoundary H) hboundaryFinite).symm
    have hnearF : ∀ k : Fin d, |p k - z k| ≤ (m : ℤ) := by
      simpa only [m] using hnear'
    have hstar : xmh_SConn (innerBoundary H) := by
      simpa only [H] using arxiv_innerBoundary_bond_star_connected ζ i z
    have hstarF : xmh_SConn (F : Set (Site d)) := by
      rw [hF]
      exact hstar
    have hdefective : ∀ x ∈ F, rn_siteField ζ x = false := by
      intro x hx
      have hxBoundary : x ∈ innerBoundary H := by
        rw [← hF]
        exact hx
      have hxBoundary' : x ∈ innerBoundary
          (componentIn
            ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z) := by
        simpa only [H] using hxBoundary
      exact arxiv_innerBoundary_bond_defective ζ i z x hxBoundary'
    refine Set.mem_iUnion.mpr ⟨m, ?_⟩
    exact ⟨hsm, p, hnearF, F, hpF, hcard, hstarF, hdefective⟩
  have hterm (m : ℕ) : bondPercolation d q (A m) ≤
      if s ≤ m ^ 2 then
        (((2 * m + 1) ^ d : ℕ) : ENNReal) *
          (K : ENNReal) ^ m *
          (ENNReal.ofReal (2 * (d : ℝ) * (1 - q))) ^ (m / 3 ^ d)
      else 0 := by
    by_cases hm : s ≤ m ^ 2
    · rw [if_pos hm]
      calc
        bondPercolation d q (A m) ≤ bondPercolation d q
            {ζ | ∃ p : Site d,
              (∀ k : Fin d, |p k - z k| ≤ (m : ℤ)) ∧
              ∃ F : Finset (Site d), p ∈ F ∧ F.card = m ∧
                xmh_SConn (F : Set (Site d)) ∧
                ∀ x ∈ F, rn_siteField ζ x = false} := by
          apply measure_mono
          intro ζ hζ
          exact hζ.2
        _ ≤ (((2 * m + 1) ^ d : ℕ) : ENNReal) *
              (K : ENNReal) ^ m *
              (ENNReal.ofReal (2 * (d : ℝ) * (1 - q))) ^ (m / 3 ^ d) :=
          hnear z m hq0 hq1
    · rw [if_neg hm]
      have hempty : A m = ∅ := by
        ext ζ
        constructor
        · rintro ⟨hsm, _⟩
          exact (hm hsm).elim
        · intro hfalse
          exact hfalse.elim
      rw [hempty]
      simp
  change bondPercolation d q E ≤ _
  calc
    bondPercolation d q E ≤ bondPercolation d q (⋃ m : ℕ, A m) :=
      measure_mono hsub
    _ ≤ ∑' m : ℕ, bondPercolation d q (A m) := measure_iUnion_le _
    _ ≤ ∑' m : ℕ,
        if s ≤ m ^ 2 then
          (((2 * m + 1) ^ d : ℕ) : ENNReal) *
            (K : ENNReal) ^ m *
            (ENNReal.ofReal (2 * (d : ℝ) * (1 - q))) ^ (m / 3 ^ d)
        else 0 := ENNReal.tsum_le_tsum hterm

end Exploding
