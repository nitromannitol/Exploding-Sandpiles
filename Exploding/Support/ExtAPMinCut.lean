/-
The minimal vertex cut of the two opposite faces of the box.

Fix a dimension `d`, a box radius `n` and a direction `i`.  The box `cent d n` is a finite
graph for nearest-neighbour adjacency, with two opposite faces `xmc_Fneg` and `xmc_Fpos`.
A finite set `S` of sites is a cut when every box path from the negative face to the
positive face meets `S`, and it is minimal when no proper subset is a cut.

This file fixes the vocabulary and proves the elementary consequences of minimality.  The
substantive combinatorial input of the star-duality, that a minimal cut is `*`-connected, is
recorded as `xmc_MinCutStarConnected`.
-/
import Exploding.Support.ExtAPStarDuality

open Exploding LatticeProb Relation
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-! ### The two faces -/

/-- The negative `i`-face of the box: the sites of `cent d n` with `i`-coordinate `-n`. -/
def xmc_Fneg (d n : ℕ) (i : Fin d) : Set (Site d) :=
  {x | x ∈ cent d n ∧ x i = -(n : ℤ)}

/-- The positive `i`-face of the box: the sites of `cent d n` with `i`-coordinate `n`. -/
def xmc_Fpos (d n : ℕ) (i : Fin d) : Set (Site d) :=
  {x | x ∈ cent d n ∧ x i = (n : ℤ)}

theorem xmc_Fneg_subset_cent (d n : ℕ) (i : Fin d) : xmc_Fneg d n i ⊆ cent d n :=
  fun _ hx => hx.1

theorem xmc_Fpos_subset_cent (d n : ℕ) (i : Fin d) : xmc_Fpos d n i ⊆ cent d n :=
  fun _ hx => hx.1

/-! ### Box paths avoiding a finite set -/

/-- A nearest-neighbour path of the box that avoids the finite set `S`. -/
def xmc_Avoid (d n : ℕ) (S : Finset (Site d)) (a b : Site d) : Prop :=
  Relation.ReflTransGen
    (fun x y => (lattice d).Adj x y ∧ x ∈ cent d n ∧ y ∈ cent d n ∧
      x ∉ (S : Set (Site d)) ∧ y ∉ (S : Set (Site d))) a b

theorem xmc_Avoid_refl (d n : ℕ) (S : Finset (Site d)) (a : Site d) :
    xmc_Avoid d n S a a :=
  Relation.ReflTransGen.refl

theorem xmc_Avoid_trans (d n : ℕ) (S : Finset (Site d)) {a b c : Site d}
    (h₁ : xmc_Avoid d n S a b) (h₂ : xmc_Avoid d n S b c) : xmc_Avoid d n S a c :=
  h₁.trans h₂

theorem xmc_Avoid_symm (d n : ℕ) (S : Finset (Site d)) {a b : Site d}
    (h : xmc_Avoid d n S a b) : xmc_Avoid d n S b a :=
  xmh_rtg_symm
    (fun _ _ hxy => ⟨hxy.1.symm, hxy.2.2.1, hxy.2.1, hxy.2.2.2.2, hxy.2.2.2.1⟩) h

/-- Removing more sites makes avoidance harder: if `S ⊆ T` then every path avoiding `T`
also avoids `S`. -/
theorem xmc_Avoid_anti (d n : ℕ) {S T : Finset (Site d)} (hST : S ⊆ T) {a b : Site d}
    (h : xmc_Avoid d n T a b) : xmc_Avoid d n S a b := by
  refine xap_rtg_mono (fun x y hxy => ?_) h
  exact ⟨hxy.1, hxy.2.1, hxy.2.2.1, fun hx => hxy.2.2.2.1 (hST hx),
    fun hy => hxy.2.2.2.2 (hST hy)⟩

/-! ### Cuts and minimal cuts -/

/-- `S` is a vertex cut of the two opposite faces inside the box: it lies in the ball and
every box path from the negative face to the positive face meets it. -/
def xmc_IsCut (d n : ℕ) (i : Fin d) (S : Finset (Site d)) : Prop :=
  S ⊆ xap11_ball d n ∧
    ∀ x y, x ∈ xmc_Fneg d n i → y ∈ xmc_Fpos d n i → ¬ xmc_Avoid d n S x y

/-- `S` is a minimal vertex cut when it is a cut and no proper subset is. -/
def xmc_Minimal (d n : ℕ) (i : Fin d) (S : Finset (Site d)) : Prop :=
  xmc_IsCut d n i S ∧ ∀ T, T ⊂ S → ¬ xmc_IsCut d n i T

/-- Supersets of a cut are cuts. -/
theorem xmc_IsCut_mono (d n : ℕ) (i : Fin d) {S T : Finset (Site d)} (hST : S ⊆ T)
    (hT : T ⊆ xap11_ball d n) (hS : xmc_IsCut d n i S) : xmc_IsCut d n i T :=
  ⟨hT, fun x y hx hy havoid => hS.2 x y hx hy (xmc_Avoid_anti d n hST havoid)⟩

/-- Deleting a site of a minimal cut destroys the cut. -/
theorem xmc_Minimal_erase_not_cut (d n : ℕ) (i : Fin d) {S : Finset (Site d)}
    (hS : xmc_Minimal d n i S) {s : Site d} (hs : s ∈ S) :
    ¬ xmc_IsCut d n i (S.erase s) :=
  hS.2 (S.erase s) (Finset.erase_ssubset hs)

/-- Every site of a minimal cut has a box path from the negative face to the positive face
that avoids all other sites of the cut. -/
theorem xmc_Minimal_exists_avoid (d n : ℕ) (i : Fin d) {S : Finset (Site d)}
    (hS : xmc_Minimal d n i S) {s : Site d} (hs : s ∈ S) :
    ∃ x y, x ∈ xmc_Fneg d n i ∧ y ∈ xmc_Fpos d n i ∧ xmc_Avoid d n (S.erase s) x y := by
  have hnot := xmc_Minimal_erase_not_cut d n i hS hs
  rw [xmc_IsCut] at hnot
  push Not at hnot
  have hsub : S.erase s ⊆ xap11_ball d n := (Finset.erase_subset s S).trans hS.1.1
  exact hnot hsub

/-! ### The star-duality input -/

/-- The graph-theoretic input of the star duality: in dimension at least two, a minimal
vertex cut of the two opposite faces of the box is `*`-connected. -/
def xmc_MinCutStarConnected (d : ℕ) : Prop :=
  ∀ (n : ℕ) (i : Fin d) (S : Finset (Site d)), xmc_Minimal d n i S →
    ((xap2_kingGraph d).induce (S : Set (Site d))).Connected

end Exploding
