/-
The reduction of the Bernoulli box-crossing star duality to the minimal-cut input.

If a box has no open nearest-neighbour crossing, the set of its closed sites is a cut of the
two faces; a finite minimisation produces a minimal cut, which the minimal-cut input makes
`*`-connected, and the axis-line bound makes it at least the side length long.  Hence
`xbc_StarDuality` holds in every dimension at least two from `xmc_MinCutStarConnected`.
-/
import Exploding.Support.ExtAPMinCutLine
import Exploding.Support.ExtBCBernoulli2

open Exploding LatticeProb Relation
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-- The set of closed sites of the box is a cut of the two faces whenever there is no open
crossing. -/
theorem xml_closedSet_isCut {n : ℕ} {i : Fin d} {ω : Site d → Bool}
    (hnc : ¬ xbc_Crosses d n i ω) :
    xmc_IsCut d n i ((xap11_ball d n).filter (fun z => ω z = false)) := by
  constructor
  · exact Finset.filter_subset _ _
  · intro x y hx hy havoid
    apply hnc
    refine ⟨x, y, hx.2, hy.2, hx.1, hy.1, ?_⟩
    refine xap_rtg_mono (fun a b hab => ?_) havoid
    obtain ⟨hadj, ha, hb, haS, hbS⟩ := hab
    have haopen : ω a = true := by
      cases hwa : ω a with
      | false => exact absurd (Finset.mem_filter.mpr ⟨xbc_mem_ball.mpr ha, hwa⟩) haS
      | true => rfl
    have hbopen : ω b = true := by
      cases hwb : ω b with
      | false => exact absurd (Finset.mem_filter.mpr ⟨xbc_mem_ball.mpr hb, hwb⟩) hbS
      | true => rfl
    exact ⟨hadj, ha, hb, haopen, hbopen⟩

/-- A finite cut contains a minimal cut. -/
theorem xml_minCut_exists {n : ℕ} {i : Fin d} {T : Finset (Site d)} (hTcut : xmc_IsCut d n i T) :
    ∃ S : Finset (Site d), S ⊆ T ∧ xmc_Minimal d n i S := by
  classical
  have main : ∀ k : ℕ, ∀ T : Finset (Site d), T.card = k → xmc_IsCut d n i T →
      ∃ U : Finset (Site d), U ⊆ T ∧ xmc_Minimal d n i U := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro T hTcard hTcut
      by_cases hmin : ∀ U : Finset (Site d), U ⊂ T → ¬ xmc_IsCut d n i U
      · exact ⟨T, subset_rfl, hTcut, hmin⟩
      · push Not at hmin
        obtain ⟨U, hUT, hUcut⟩ := hmin
        have hUlt : U.card < k := by
          rw [← hTcard]
          exact Finset.card_lt_card hUT
        obtain ⟨V, hVU, hVmin⟩ := ih U.card hUlt U rfl hUcut
        exact ⟨V, hVU.trans hUT.1, hVmin⟩
  exact main T.card T rfl hTcut

/-- **The box-crossing star duality follows from the minimal-cut input in dimensions at least
two.** -/
theorem xml_starDuality_of_minCut (hd : 2 ≤ d) (h : xmc_MinCutStarConnected d) :
    xbc_StarDuality d := by
  intro n i ω hnc
  have hcut := xml_closedSet_isCut (d := d) (n := n) (i := i) (ω := ω) hnc
  obtain ⟨S, hSsub, hSmin⟩ := xml_minCut_exists hcut
  have hSis : xmc_IsCut d n i S := hSmin.1
  have hSconn := h n i S hSmin
  refine ⟨S.card, xml_cut_card_ge hd hSis, S, ?_, ?_⟩
  · rw [xap11_starSets, Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr hSis.1, rfl, hSconn⟩
  · intro z hz
    exact (Finset.mem_filter.mp (hSsub hz)).2

end Exploding
