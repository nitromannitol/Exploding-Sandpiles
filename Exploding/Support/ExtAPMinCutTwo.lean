/-
Minimal box cuts and the planar star-duality.

The star-connectedness of a minimal vertex cut of two opposite faces of a box is
equivalent to the statement that every cut contains a `*`-connected sub-cut.  This file
records the equivalence, which isolates the planar star-duality as the single remaining
geometric input: the boundary theorem `Exploding.xmh3_boundaryStar` shows that a
`*`-connected boundary is produced by a *connected* complement component, while the box
separator itself need not be such a boundary.

Nothing here is asserted without proof: the reduction below is unconditional, and it
uses only the elementary minimality consequences already available in
`Exploding.Support.ExtAPMinCut`.  The reverse implication runs a finite descent over the
sub-cuts of a cut, using the fact that the sub-cut relation on a finite set `Finset` is
well founded.
-/
import Exploding.Support.ExtAPMinCut

open Exploding LatticeProb
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-- Every cut contains a `*`-connected sub-cut.  This is the strong planar duality from
which the star-connectedness of a minimal cut follows, and it is in fact equivalent to
it. -/
def xmd_CutContainsStarCut (d : ℕ) : Prop :=
  ∀ (n : ℕ) (i : Fin d) (S : Finset (Site d)), xmc_IsCut d n i S →
    ∃ T : Finset (Site d), T ⊆ S ∧ xmc_IsCut d n i T ∧
      ((xap2_kingGraph d).induce (T : Set (Site d))).Connected

/-- A cut contains an inclusion-minimal sub-cut. -/
theorem xmd_exists_minimal_subcut (d n : ℕ) (i : Fin d) (S : Finset (Site d))
    (hS : xmc_IsCut d n i S) :
    ∃ T : Finset (Site d), T ⊆ S ∧ xmc_IsCut d n i T ∧ xmc_Minimal d n i T := by
  have key : ∀ S : Finset (Site d), xmc_IsCut d n i S →
      ∃ T : Finset (Site d), T ⊆ S ∧ xmc_IsCut d n i T ∧ xmc_Minimal d n i T := by
    intro S
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      intro hS
      by_cases hmin : xmc_Minimal d n i S
      · exact ⟨S, subset_rfl, hS, hmin⟩
      · have hnot : ∃ T : Finset (Site d), T ⊂ S ∧ xmc_IsCut d n i T := by
          by_contra hc
          push Not at hc
          exact hmin ⟨hS, fun T hT => hc T hT⟩
        obtain ⟨T, hTsub, hTcut⟩ := hnot
        obtain ⟨U, hUT, hUcut, hUmin⟩ := ih T hTsub hTcut
        exact ⟨U, hUT.trans hTsub.le, hUcut, hUmin⟩
  exact key S hS

/-- The star-connectedness of every minimal cut is equivalent to every cut containing a
`*`-connected sub-cut. -/
theorem xmd_cutContainsStarCut_iff_minCutStarConnected (d : ℕ) :
    xmd_CutContainsStarCut d ↔ xmc_MinCutStarConnected d := by
  constructor
  · intro h n i S hS
    obtain ⟨T, hTS, hTcut, hTconn⟩ := h n i S hS.1
    by_cases hEq : T = S
    · rw [hEq] at hTconn; exact hTconn
    · exact absurd hTcut
        (hS.2 T (Finset.ssubset_iff_subset_ne.mpr ⟨hTS, hEq⟩))
  · intro h n i S hS
    obtain ⟨T, hTS, hTcut, hTmin⟩ := xmd_exists_minimal_subcut d n i S hS
    exact ⟨T, hTS, hTcut, h n i T hTmin⟩

/-- The star-connectedness of every minimal cut follows from the strong planar duality. -/
theorem xmd_minCutStarConnected_of_cutContainsStarCut (d : ℕ)
    (h : xmd_CutContainsStarCut d) : xmc_MinCutStarConnected d :=
  (xmd_cutContainsStarCut_iff_minCutStarConnected d).1 h

end Exploding
