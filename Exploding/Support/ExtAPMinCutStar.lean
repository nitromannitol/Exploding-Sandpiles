/-
The minimal vertex cut of the two opposite faces of a box is `*`-connected, hence the
box-crossing star duality holds in every dimension at least two.
-/
import Exploding.Support.ExtAPBoxBoundaryStar
import Exploding.Support.ExtAPMinCutTwo

namespace Exploding

open LatticeProb Relation
open scoped Classical

variable {d : ℕ}

/-! ### A path through a forbidden vertex -/

theorem xmg_rtg_connect {α : Type*} {R : α → α → Prop} {x y c0 : α}
    (h : ReflTransGen R x y)
    (hpre : ¬ ReflTransGen (fun a c => R a c ∧ a ≠ c0 ∧ c ≠ c0) x y) :
    ReflTransGen R c0 y := by
  induction h with
  | refl => exact absurd ReflTransGen.refl hpre
  | tail hpref hbc ih =>
    rename_i finv midv
    by_cases hyc : midv = c0
    · subst hyc; exact ReflTransGen.refl
    · by_cases hmid : finv = c0
      · subst hmid; exact ReflTransGen.refl.tail hbc
      · exact (ih (fun hcon => hpre (hcon.tail ⟨hbc, hmid, hyc⟩))).tail hbc

/-! ### The negative-face side of a cut -/

/-- The `Fneg`-side of a cut: the sites reachable from the negative face without
meeting the cut, and not in the cut. -/
def xmg_C (d n : ℕ) (i : Fin d) (S : Finset (Site d)) : Set (Site d) :=
  {z | z ∉ (S : Set (Site d)) ∧ ∃ x ∈ xmc_Fneg d n i, xmc_Avoid d n S x z}

theorem xmg_C_subset (d n : ℕ) (i : Fin d) (S : Finset (Site d)) :
    xmg_C d n i S ⊆ cent d n := by
  rintro z ⟨hzS, x, hx, havoid⟩
  rcases ReflTransGen.cases_tail havoid with h | ⟨v, _, hv⟩
  · rw [h]; exact hx.1
  · exact hv.2.2.1

/-- Every site of the `Fneg`-side is joined to the negative face inside the side. -/
theorem xmg_C_meets (d n : ℕ) (i : Fin d) (S : Finset (Site d)) :
    ∀ u ∈ xmg_C d n i S, ∃ f1 ∈ xmg_C d n i S, f1 ∈ xmc_Fneg d n i ∧
      ReflTransGen (fun a b => a ∈ xmg_C d n i S ∧ b ∈ xmg_C d n i S ∧
        (lattice d).Adj a b) u f1 := by
  rintro u ⟨huS, x, hx, havoid⟩
  have hxS : x ∉ (S : Set (Site d)) := by
    intro hxS
    rcases ReflTransGen.cases_head havoid with h | ⟨v, hv, _⟩
    · rw [h] at hxS; exact huS hxS
    · exact hv.2.2.2.1 hxS
  have key : ∀ w, xmc_Avoid d n S x w → w ∈ xmg_C d n i S := by
    intro w hw
    refine ⟨?_, x, hx, hw⟩
    intro hwS
    rcases ReflTransGen.cases_tail hw with h | ⟨v, _, hv⟩
    · rw [h] at hwS; exact hxS hwS
    · exact hv.2.2.2.2 hwS
  have pathC : ReflTransGen (fun a b => a ∈ xmg_C d n i S ∧ b ∈ xmg_C d n i S ∧
      (lattice d).Adj a b) x u := by
    induction havoid with
    | refl => exact ReflTransGen.refl
    | tail hpref hbc ih =>
      exact (ih (key _ hpref).1).tail ⟨key _ hpref, key _ (hpref.tail hbc), hbc.1⟩
  exact ⟨x, key x (xmc_Avoid_refl d n S x), hx,
    xmh_rtg_symm (fun a b h => ⟨h.2.1, h.1, h.2.2.symm⟩) pathC⟩

end Exploding
