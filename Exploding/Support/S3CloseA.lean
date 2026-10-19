/-
Proposition 5.1 (generalized last wave), the infinite cluster of strongly box-crossing tiles, part A:
the field of strongly box-crossing tiles is `(K + 1)`-dependent with `K` the range of Hypothesis 1,
uniformly in the side lengths of the tiles.  The uniformity is what lets the side lengths be chosen
after the range of dependence in the Liggett-Schonmann-Stacey domination.
-/
import Exploding.Support.GLWSec3W

open Exploding LatticeProb MeasureTheory Filter ProbabilityTheory
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-- **(A) uniformly in the tile.**  Hypothesis 1 makes the field of strongly box-crossing tiles
`(K + 1)`-dependent, with `K` independent of the side lengths. -/
theorem s3k_kdep (d : ℕ) (P : Measure (Site d → ℤ))
    (h1 : FiniteRangeOfDependence d P) :
    ∃ K : ℕ, ∀ k : Fin d → ℕ, (∀ i, 0 < k i) →
      KDependent (K + 1) (P.map fun η (j : Site d) => decide (StronglyBoxCrossed η k j)) := by
  classical
  obtain ⟨K, hK⟩ := h1
  refine ⟨K, fun k hk => ?_⟩
  have hfin : ∀ j : Site d, (rboxShift k j).Finite := by
    intro j
    rw [show rboxShift k j = Set.univ.pi
        (fun i : Fin d => Set.Icc (1 + (k i : ℤ) * j i) ((k i : ℤ) * j i + (k i : ℤ))) from by
      ext x
      simp only [rboxShift, Set.mem_setOf_eq, Set.mem_univ_pi, Set.mem_Icc]]
    exact Set.Finite.pi (fun i => Set.finite_Icc _ _)
  let tileFin : Site d → Finset (Site d) := fun j => (hfin j).toFinset
  have tileFin_mem : ∀ j x, x ∈ tileFin j ↔ x ∈ rboxShift k j := fun j x => (hfin j).mem_toFinset
  intro I J hdij
  let bigI : Finset (Site d) := I.biUnion tileFin
  let bigJ : Finset (Site d) := J.biUnion tileFin
  have hsubI : ∀ i ∈ I, tileFin i ⊆ bigI := by
    intro i hi x hx
    simp only [bigI, Finset.mem_biUnion]
    exact ⟨i, hi, hx⟩
  have hsubJ : ∀ j ∈ J, tileFin j ⊆ bigJ := by
    intro j hj x hx
    simp only [bigJ, Finset.mem_biUnion]
    exact ⟨j, hj, hx⟩
  have hsep : ∀ a ∈ bigI, ∀ b ∈ bigJ, (K : ℤ) < mnorm (a - b) := by
    intro a ha b hb
    simp only [bigI, Finset.mem_biUnion] at ha
    obtain ⟨i, hi, hai⟩ := ha
    simp only [bigJ, Finset.mem_biUnion] at hb
    obtain ⟨j, hj, hbj⟩ := hb
    obtain ⟨l, hl⟩ := hdij i hi j hj
    exact glw2_tile_sep k hk hl ((tileFin_mem i a).mp hai) ((tileFin_mem j b).mp hbj)
  have hind := hK bigI bigJ hsep
  let F : (Site d → ℤ) → (Site d → Bool) :=
    fun η j => decide (StronglyBoxCrossed η k j)
  have hF : Measurable F := glw_box_measurable d k
  let rI : (Site d → ℤ) → (bigI → ℤ) := fun η x => η x
  let rJ : (Site d → ℤ) → (bigJ → ℤ) := fun η x => η x
  let eI : (bigI → ℤ) → (Site d → ℤ) := fun f x => if h : x ∈ bigI then f ⟨x, h⟩ else 0
  let eJ : (bigJ → ℤ) → (Site d → ℤ) := fun f x => if h : x ∈ bigJ then f ⟨x, h⟩ else 0
  let ΦI : (bigI → ℤ) → (I → Bool) := fun f i => decide (StronglyBoxCrossed (eI f) k i)
  let ΦJ : (bigJ → ℤ) → (J → Bool) := fun f j => decide (StronglyBoxCrossed (eJ f) k j)
  have hΦI : Measurable ΦI := measurable_of_countable ΦI
  have hΦJ : Measurable ΦJ := measurable_of_countable ΦJ
  have hRI : ((fun ω : Site d → Bool => fun i : I => ω i) ∘ F) = ΦI ∘ rI := by
    funext η i
    show decide (StronglyBoxCrossed η k (i : Site d))
      = decide (StronglyBoxCrossed (eI (rI η)) k (i : Site d))
    have hiff := glw_box_finite_dep d k (i : Site d) (eI (rI η)) η (fun x hx => ?_)
    · by_cases h : StronglyBoxCrossed η k (i : Site d)
      · have h2 := hiff.mpr h
        simp [h, h2]
      · have h2 : ¬ StronglyBoxCrossed (eI (rI η)) k (i : Site d) := fun hc => h (hiff.mp hc)
        simp [h, h2]
    · have hxI : x ∈ bigI := hsubI (i : Site d) i.2 ((tileFin_mem (i : Site d) x).mpr hx)
      simp only [eI, rI, dif_pos hxI]
  have hRJ : ((fun ω : Site d → Bool => fun j : J => ω j) ∘ F) = ΦJ ∘ rJ := by
    funext η j
    show decide (StronglyBoxCrossed η k (j : Site d))
      = decide (StronglyBoxCrossed (eJ (rJ η)) k (j : Site d))
    have hiff := glw_box_finite_dep d k (j : Site d) (eJ (rJ η)) η (fun x hx => ?_)
    · by_cases h : StronglyBoxCrossed η k (j : Site d)
      · have h2 := hiff.mpr h
        simp [h, h2]
      · have h2 : ¬ StronglyBoxCrossed (eJ (rJ η)) k (j : Site d) := fun hc => h (hiff.mp hc)
        simp [h, h2]
    · have hxJ : x ∈ bigJ := hsubJ (j : Site d) j.2 ((tileFin_mem (j : Site d) x).mpr hx)
      simp only [eJ, rJ, dif_pos hxJ]
  have hcomp : IndepFun (ΦI ∘ rI) (ΦJ ∘ rJ) P := hind.comp hΦI hΦJ
  refine (glw2_indepFun_map_iff F hF P
    (fun ω : Site d → Bool => fun i : I => ω i)
    (fun ω : Site d → Bool => fun j : J => ω j)
    (measurable_pi_lambda _ (fun i => measurable_pi_apply (i : Site d)))
    (measurable_pi_lambda _ (fun j => measurable_pi_apply (j : Site d)))).mpr ?_
  rw [hRI, hRJ]
  exact hcomp

end Exploding
