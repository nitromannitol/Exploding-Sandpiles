/-
Proposition 5.1 of the paper (generalized last wave): fields of bits that depend on the background
through finitely many coordinates, and their dependence graph under finite range of dependence
(Hypothesis 5.1).
-/
import Exploding.Support.GLWSec3AD
import Exploding.Support.GLWSec3AB

open MeasureTheory ProbabilityTheory Exploding LatticeProb Filter

namespace Exploding

variable {d : ℕ}

/-- A function of the background that depends on finitely many coordinates is measurable. -/
theorem glws_local_meas (V : Finset (Site d)) (Φ : (Site d → ℤ) → Bool)
    (hΦ : ∀ η η' : Site d → ℤ, (∀ a ∈ V, η a = η' a) → Φ η = Φ η') : Measurable Φ := by
  classical
  have h1 : Φ = (fun v : (V → ℤ) => Φ (fun a => if h : a ∈ V then v ⟨a, h⟩ else 0)) ∘
      (fun η (t : V) => η t) := by
    funext η
    simp only [Function.comp]
    refine hΦ _ _ (fun t ht => ?_)
    simp [ht]
  rw [h1]
  exact (measurable_of_countable _).comp (measurable_pi_lambda _ (fun t => measurable_pi_apply _))

/-- **The dependence graph of a local field of bits.**  If the law of the background has finite range
of dependence `K`, and the bits `Φ s` depend only on the coordinates of the finite sets `vs s`, with
`vs s` and `vs t` more than `K` apart whenever `s ≠ t` are not adjacent in `G`, then the field of
bits has dependence graph `G`. -/
theorem glws_dependence_graph {S : Type} (P : Measure (Site d → ℤ)) [IsProbabilityMeasure P]
    (K : ℕ)
    (hFR : ∀ I J : Finset (Site d), (∀ a ∈ I, ∀ b ∈ J, (K : ℤ) < mnorm (a - b)) →
      IndepFun (fun η : Site d → ℤ => fun i : I => η i)
        (fun η : Site d → ℤ => fun j : J => η j) P)
    (G : SimpleGraph S) (vs : S → Finset (Site d)) (Φ : S → (Site d → ℤ) → Bool)
    (hΦ : ∀ s (η η' : Site d → ℤ), (∀ a ∈ vs s, η a = η' a) → Φ s η = Φ s η')
    (hloc : ∀ s t, s ≠ t → ¬ G.Adj s t → ∀ a ∈ vs s, ∀ b ∈ vs t, (K : ℤ) < mnorm (a - b)) :
    Measurable (fun (η : Site d → ℤ) (s : S) => Φ s η) ∧
      HasDependenceGraph G (P.map (fun (η : Site d → ℤ) (s : S) => Φ s η)) := by
  classical
  have hmeasF : Measurable (fun (η : Site d → ℤ) (s : S) => Φ s η) :=
    measurable_pi_iff.mpr (fun s => glws_local_meas (vs s) (Φ s) (hΦ s))
  refine ⟨hmeasF, ?_⟩
  intro I J hIJ hadj
  have hfar : ∀ a ∈ I.biUnion vs, ∀ b ∈ J.biUnion vs, (K : ℤ) < mnorm (a - b) := by
    intro a haI b hbJ
    obtain ⟨s, hs, has⟩ := Finset.mem_biUnion.mp haI
    obtain ⟨t, ht, hbt⟩ := Finset.mem_biUnion.mp hbJ
    have hst : s ≠ t := fun h => (Finset.disjoint_left.mp hIJ) hs (h ▸ ht)
    exact hloc s t hst (hadj s hs t ht) a has b hbt
  have hind2 := hFR (I.biUnion vs) (J.biUnion vs) hfar
  let ΨI : (↥(I.biUnion vs) → ℤ) → (I → Bool) := fun v i =>
    Φ i (fun a => if h : a ∈ I.biUnion vs then v ⟨a, h⟩ else 0)
  let ΨJ : (↥(J.biUnion vs) → ℤ) → (J → Bool) := fun v i =>
    Φ i (fun a => if h : a ∈ J.biUnion vs then v ⟨a, h⟩ else 0)
  have hΨI : Measurable ΨI := measurable_of_countable _
  have hΨJ : Measurable ΨJ := measurable_of_countable _
  have hcomp := hind2.comp hΨI hΨJ
  set F := (fun (η : Site d → ℤ) (s : S) => Φ s η) with hF
  have huI : (fun η (i : I) => F η i) = ΨI ∘ (fun η (a : I.biUnion vs) => η a) := by
    funext η i
    simp only [Function.comp, hF, ΨI]
    refine hΦ i _ _ (fun t ht => ?_)
    have : t ∈ I.biUnion vs := Finset.mem_biUnion.mpr ⟨i, i.2, ht⟩
    simp [this]
  have huJ : (fun η (j : J) => F η j) = ΨJ ∘ (fun η (a : J.biUnion vs) => η a) := by
    funext η i
    simp only [Function.comp, hF, ΨJ]
    refine hΦ i _ _ (fun t ht => ?_)
    have : t ∈ J.biUnion vs := Finset.mem_biUnion.mpr ⟨i, i.2, ht⟩
    simp [this]
  have hmI : Measurable (fun (ω' : S → Bool) (i : I) => ω' i) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  have hmJ : Measurable (fun (ω' : S → Bool) (j : J) => ω' j) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  haveI : IsProbabilityMeasure (P.map F) := Measure.isProbabilityMeasure_map hmeasF.aemeasurable
  rw [indepFun_iff_map_prod_eq_prod_map_map hmI.aemeasurable hmJ.aemeasurable]
  have hPI : (fun η (i : I) => F η i) = (fun (ω' : S → Bool) (i : I) => ω' i) ∘ F := rfl
  have hPJ : (fun η (j : J) => F η j) = (fun (ω' : S → Bool) (j : J) => ω' j) ∘ F := rfl
  rw [huI] at hPI
  rw [huJ] at hPJ
  have hc2 : IndepFun ((fun (ω' : S → Bool) (i : I) => ω' i) ∘ F)
      ((fun (ω' : S → Bool) (j : J) => ω' j) ∘ F) P := by
    rw [← hPI, ← hPJ]
    exact hcomp
  rw [indepFun_iff_map_prod_eq_prod_map_map (hmI.comp hmeasF).aemeasurable
    (hmJ.comp hmeasF).aemeasurable] at hc2
  rw [Measure.map_map (hmI.prodMk hmJ) hmeasF, Measure.map_map hmI hmeasF,
    Measure.map_map hmJ hmeasF]
  exact hc2

/-- One coordinate of `glws_tile_dist`. -/
theorem glws_tile_dist_coord (k : ℤ) (hk : 1 ≤ k) {j j' a b : ℤ}
    (ha1 : 1 + k * j ≤ a) (ha2 : a ≤ k * j + k) (hb1 : 1 + k * j' ≤ b) (hb2 : b ≤ k * j' + k) :
    |j - j'| ≤ |a - b| := by
  rcases le_total j j' with h | h
  · rw [abs_of_nonpos (by linarith : j - j' ≤ 0)]
    rcases eq_or_lt_of_le h with he | hlt
    · rw [he]; simp
    · have hm : (0 : ℤ) ≤ j' - j - 1 := by linarith
      have e : k * (j' - j - 1) ≥ (j' - j - 1) := by nlinarith
      have h1 : b - a ≥ j' - j := by nlinarith
      have h2 : b - a ≤ |a - b| := by rw [abs_sub_comm]; exact le_abs_self _
      linarith
  · rw [abs_of_nonneg (by linarith : 0 ≤ j - j')]
    rcases eq_or_lt_of_le h with he | hlt
    · rw [he]; simp
    · have hm : (0 : ℤ) ≤ j - j' - 1 := by linarith
      have e : k * (j - j' - 1) ≥ (j - j' - 1) := by nlinarith
      have h1 : a - b ≥ j - j' := by nlinarith
      have h2 : a - b ≤ |a - b| := le_abs_self _
      linarith

/-- The distance between two tiles bounds below the distance between their macroscopic indices. -/
theorem glws_tile_dist (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {j j' a b : Site d}
    (ha : a ∈ rboxShift k j) (hb : b ∈ rboxShift k j') : mnorm (j - j') ≤ mnorm (a - b) := by
  unfold mnorm
  refine Finset.sum_le_sum fun l _ => ?_
  simp only [Pi.sub_apply]
  have hk1 : (1 : ℤ) ≤ (k l : ℤ) := by exact_mod_cast hk l
  obtain ⟨ha1, ha2⟩ := ha l
  obtain ⟨hb1, hb2⟩ := hb l
  exact glws_tile_dist_coord (k l) hk1 ha1 ha2 hb1 hb2

end Exploding
