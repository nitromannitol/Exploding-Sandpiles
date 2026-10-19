/-
Follow-up to `GLWProofAux.lean`: the two concrete open conjuncts of the
reduction of Proposition 5.1 (convergence of the generalized last wave).

* **(A)** the field of strongly box-crossing tiles is `m`-dependent, and
* **(B)** the translation `y ↦ η(y + ·)` is mixing on cylinder events.

Both follow from Hypothesis 1 (finite range of dependence).
-/
import Exploding.Support.GLWProofAux

open Exploding LatticeProb MeasureTheory Filter ProbabilityTheory
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-! ### Elementary `mnorm` arithmetic -/

theorem glw2_mnorm_nonneg (x : Site d) : 0 ≤ mnorm x :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem glw2_mnorm_add_le (x y : Site d) : mnorm (x + y) ≤ mnorm x + mnorm y := by
  unfold mnorm
  calc ∑ i, |(x + y) i| = ∑ i, |x i + y i| := by simp
    _ ≤ ∑ i, (|x i| + |y i|) := Finset.sum_le_sum (fun i _ => abs_add_le _ _)
    _ = (∑ i, |x i|) + (∑ i, |y i|) := Finset.sum_add_distrib

theorem glw2_mnorm_sub_le (x y : Site d) : mnorm (x - y) ≤ mnorm x + mnorm y := by
  calc mnorm (x - y) = mnorm (x + -y) := by rw [sub_eq_add_neg]
    _ ≤ mnorm x + mnorm (-y) := glw2_mnorm_add_le x (-y)
    _ = mnorm x + mnorm y := by
      congr 1
      unfold mnorm
      simp only [Pi.neg_apply, abs_neg]

/-! ### (B) Mixing on cylinders -/

/-- Pushing an independence statement through a measurable map. -/
theorem glw2_indepFun_map_iff {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (F : α → β) (hF : Measurable F) (μ : Measure α) (X : β → γ) (Y : β → δ)
    (hX : Measurable X) (hY : Measurable Y) :
    IndepFun X Y (μ.map F) ↔ IndepFun (X ∘ F) (Y ∘ F) μ := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul, indepFun_iff_measure_inter_preimage_eq_mul]
  refine ⟨fun h s t hs ht => ?_, fun h s t hs ht => ?_⟩
  · have h1 := h s t hs ht
    rw [Measure.map_apply hF (hX hs), Measure.map_apply hF (hY ht),
      Measure.map_apply hF ((hX hs).inter (hY ht))] at h1
    simpa only [Set.preimage_inter, Set.preimage_comp] using h1
  · have h1 := h s t hs ht
    rw [Measure.map_apply hF (hX hs), Measure.map_apply hF (hY ht),
      Measure.map_apply hF ((hX hs).inter (hY ht))]
    simpa only [Set.preimage_inter, Set.preimage_comp] using h1

/-- **(B)** Finite range of dependence makes the shift by a nonzero lattice
vector mixing on cylinder events: some iterate sends the cylinder off itself
far enough that the finite-range independence forces the product identity. -/
theorem glw2_shift_mixing (d : ℕ) (P : Measure (Site d → ℤ))
    (h1 : FiniteRangeOfDependence d P)
    (y : Site d)
    (hmp : MeasurePreserving (fun η : Site d → ℤ => fun z => η (y + z)) P P)
    (hy0 : y ≠ 0)
    (s : Finset (Site d)) (S : Set (s → ℤ)) (hS : MeasurableSet S) :
    ∃ n : ℕ, P (cylinder s S ∩
        (fun η : Site d → ℤ => fun z => η (y + z))^[n] ⁻¹' cylinder s S) =
      P (cylinder s S) * P (cylinder s S) := by
  classical
  obtain ⟨K, hK⟩ := h1
  set D : ℤ := 2 * ∑ a ∈ s, mnorm a with hD
  have hDnn : 0 ≤ D := by
    rw [hD]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun a _ => glw2_mnorm_nonneg a))
  have hdiam : ∀ a ∈ s, ∀ a' ∈ s, mnorm (a - a') ≤ D := by
    intro a ha a' ha'
    have ha_sum : mnorm a ≤ ∑ b ∈ s, mnorm b :=
      Finset.single_le_sum (fun b _ => glw2_mnorm_nonneg b) ha
    have ha'_sum : mnorm a' ≤ ∑ b ∈ s, mnorm b :=
      Finset.single_le_sum (fun b _ => glw2_mnorm_nonneg b) ha'
    have := glw2_mnorm_sub_le a a'
    rw [hD]
    linarith
  obtain ⟨n, hn⟩ := glw_shift_ergodic_growth y hy0 (((K : ℤ) + D).toNat)
  have hKD_nonneg : 0 ≤ (K : ℤ) + D := by linarith
  have hn' : (K : ℤ) + D < mnorm ((n : ℤ) • y) := by
    have hcast : (((((K : ℤ) + D).toNat : ℕ)) : ℤ) = (K : ℤ) + D :=
      Int.toNat_of_nonneg hKD_nonneg
    rw [hcast] at hn
    exact hn
  set s' : Finset (Site d) := s.image (fun a => (n : ℤ) • y + a) with hs'
  have hsep : ∀ a ∈ s, ∀ b ∈ s', (K : ℤ) < mnorm (a - b) := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hb
    have htri : mnorm ((n : ℤ) • y) ≤ mnorm ((n : ℤ) • y - (a - a')) + mnorm (a - a') := by
      have := glw2_mnorm_add_le ((n : ℤ) • y - (a - a')) (a - a')
      simpa [sub_add_cancel] using this
    have hmn : mnorm (a - ((n : ℤ) • y + a')) = mnorm ((n : ℤ) • y - (a - a')) := by
      have heq : a - ((n : ℤ) • y + a') = -((n : ℤ) • y - (a - a')) := by abel
      rw [heq]
      unfold mnorm
      simp only [Pi.neg_apply, abs_neg]
    have hb2 := hdiam a ha a' ha'
    rw [hmn]
    linarith
  have hind := hK s s' hsep
  let e : s → s' := fun i => ⟨(n : ℤ) • y + i, Finset.mem_image.mpr ⟨i, i.2, rfl⟩⟩
  let S'' : Set (s' → ℤ) := {τ | (fun i : s => τ (e i)) ∈ S}
  have hS'' : MeasurableSet S'' :=
    Set.Countable.measurableSet (Set.Countable.mono (Set.subset_univ S'') Set.countable_univ)
  have hpre : (fun η : Site d → ℤ => fun z => η ((n : ℤ) • y + z)) ⁻¹' cylinder s S
      = cylinder s' S'' := by
    ext η
    rw [Set.mem_preimage, mem_cylinder, mem_cylinder]
    change (s.restrict (fun z => η ((n : ℤ) • y + z)) ∈ S) ↔
      ((fun i : s => (s'.restrict η) (e i)) ∈ S)
    have hf : s.restrict (fun z => η ((n : ℤ) • y + z))
        = (fun i : s => (s'.restrict η) (e i)) := by
      ext i
      simp [e]
    rw [hf]
  refine ⟨n, ?_⟩
  have hiterate := glw_shift_ergodic_iterate y n
  rw [hiterate, hpre]
  have hshift : P (cylinder s' S'') = P (cylinder s S) := by
    have hcyl : MeasurableSet (cylinder s S) :=
      MeasurableSet.cylinder (α := fun _ : Site d => ℤ) s hS
    have hTmeas : Measurable ((fun η : Site d → ℤ => fun z => η (y + z))^[n]) :=
      (hmp.iterate n).measurable
    rw [← hpre, ← hiterate, ← Measure.map_apply hTmeas hcyl, (hmp.iterate n).map_eq]
  have hprod := hind.measure_inter_preimage_eq_mul S S'' hS hS''
  have hprod' : P (cylinder s S ∩ cylinder s' S'')
      = P (cylinder s S) * P (cylinder s' S'') := by
    simpa [cylinder, Finset.restrict_def] using hprod
  rw [hprod', hshift]

/-! ### (A) The strongly box-crossing field is `m`-dependent -/

/-- Two macroscopic tiles whose indices differ by more than `K + 1` in some
coordinate have all their microscopic sites more than `K` apart in `mnorm`. -/
theorem glw2_tile_sep (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {K : ℕ}
    {i j : Site d} {l : Fin d} (h : (K : ℤ) + 1 < |i l - j l|)
    {x y : Site d} (hx : x ∈ rboxShift k i) (hy : y ∈ rboxShift k j) :
    (K : ℤ) < mnorm (x - y) := by
  have hxl : 1 + (k l : ℤ) * i l ≤ x l ∧ x l ≤ (k l : ℤ) * i l + (k l : ℤ) := by
    have := hx l
    simpa [rboxShift] using this
  have hyl : 1 + (k l : ℤ) * j l ≤ y l ∧ y l ≤ (k l : ℤ) * j l + (k l : ℤ) := by
    have := hy l
    simpa [rboxShift] using this
  have hkl : (1 : ℤ) ≤ (k l : ℤ) := by exact_mod_cast hk l
  have hcoord : (K : ℤ) < |x l - y l| := by
    have hcases : (K : ℤ) + 2 ≤ i l - j l ∨ (K : ℤ) + 2 ≤ j l - i l := by
      rcases lt_or_ge (0 : ℤ) (i l - j l) with hpos | hneg
      · left
        rw [abs_of_nonneg (le_of_lt hpos)] at h
        linarith
      · right
        have hle : i l - j l ≤ 0 := hneg
        have : |i l - j l| = -(i l - j l) := abs_of_nonpos hle
        rw [this] at h
        linarith
    rcases hcases with hd | hd
    · have hge : (k l : ℤ) * ((K : ℤ) + 1) + 1 ≤ x l - y l := by
        nlinarith [hxl.1, hyl.2, hkl, hd]
      have hpos : 0 ≤ x l - y l := by nlinarith
      rw [abs_of_nonneg hpos]
      nlinarith
    · have hge : (k l : ℤ) * ((K : ℤ) + 1) + 1 ≤ y l - x l := by
        nlinarith [hyl.1, hxl.2, hkl, hd]
      have hneg : x l - y l ≤ 0 := by nlinarith
      rw [abs_of_nonpos hneg]
      nlinarith
  calc (K : ℤ) < |x l - y l| := hcoord
    _ ≤ mnorm (x - y) := by
        simpa [mnorm] using
          Finset.single_le_sum (fun i _ => abs_nonneg ((x - y) i)) (Finset.mem_univ l)

/-- **(A)** Hypothesis 1 makes the field of strongly box-crossing tiles
`m`-dependent: for tiles more than `K + 1` apart in `ℓ^∞`, the events factor
through disjoint, far-apart finite restrictions of `η`. -/
theorem glw2_kdep (d : ℕ) (P : Measure (Site d → ℤ))
    (h1 : FiniteRangeOfDependence d P) (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) :
    ∃ m : ℕ, KDependent m (P.map fun η (j : Site d) => decide (StronglyBoxCrossed η k j)) := by
  classical
  obtain ⟨K, hK⟩ := h1
  have hfin : ∀ j : Site d, (rboxShift k j).Finite := by
    intro j
    rw [show rboxShift k j = Set.univ.pi
        (fun i : Fin d => Set.Icc (1 + (k i : ℤ) * j i) ((k i : ℤ) * j i + (k i : ℤ))) from by
      ext x
      simp only [rboxShift, Set.mem_setOf_eq, Set.mem_univ_pi, Set.mem_Icc]]
    exact Set.Finite.pi (fun i => Set.finite_Icc _ _)
  let tileFin : Site d → Finset (Site d) := fun j => (hfin j).toFinset
  have tileFin_mem : ∀ j x, x ∈ tileFin j ↔ x ∈ rboxShift k j := fun j x => (hfin j).mem_toFinset
  refine ⟨K + 1, ?_⟩
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

/-- The subadditive ergodic core of Lemma 3.4/Kingman (open Section-3 piece). -/
def glw2_KingmanCore : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω), MeasurePreserving T μ μ → Ergodic T μ →
    ∀ (g : ℕ → Ω → ℝ), (∀ m n x, g (m + n) x ≤ g m x + g n (T^[m] x)) →
    (∀ n x, 0 ≤ g n x) → (∀ n, Measurable (g n)) →
    ∀ (C : ℝ), (∀ᵐ x ∂μ, ∃ K : ℝ, ∀ n : ℕ, g n x ≤ C * n + K) →
      ∀ (K : ℝ), MeasurableSet {x | ∀ n : ℕ, g n x ≤ C * n + K} →
      0 < μ {x | ∀ n : ℕ, g n x ≤ C * n + K} →
      ∃ L : ℝ, ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => g n x / (n : ℝ)) atTop (nhds L)

/-- The local Lipschitz bound for the penultimate-cluster arrival times
(open Section-3 piece, the general-hypothesis analogue of Lemma 3.7).  It is
stated as an implication from the Section 5 setting, so it is not vacuous for
an arbitrary `P`. -/
def glw2_LipschitzLocal (d : ℕ) (ηmin : ℤ) (P : Measure (Site d → ℤ)) : Prop :=
  IsProbabilityMeasure P → (∀ᵐ η ∂P, InOmega d ηmin η) →
  FiniteRangeOfDependence d P → PathFillingHyp d P → StronglyBoxCrossingHyp d P →
  Exploding.External.LiggettSchonmannStacey →
  Exploding.External.LiggettSchonmannStaceyBoundedDegree →
  Exploding.External.MathieuHoleVolume →
  Exploding.External.AntalPisztoraChemicalDistance →
  ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧ ∀ᵐ η ∂P,
    (∀ y : Site d, ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n y) ∧
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ cent d n, ∃ a : ℕ,
      clusterArrival η (0 : Site d) x = (a : ℕ∞) ∧
      ∀ x' ∈ cent d n, ∃ c : ℕ, clusterArrival η x x' = (c : ℕ∞) ∧
        (c : ℝ) ≤ C * (mnorm (x - x') : ℝ) + Real.log n ^ γ

/-- The Section-3 convergence assembly (open).  It consumes the two finite-range
facts (A) and (B), the subadditive ergodic core and the local Lipschitz bound,
and returns the Proposition 5.1 conclusion. -/
def glw2_Section3Convergence (d : ℕ) (_hd : 2 ≤ d) (ηmin : ℤ) (_hηmin : 0 ≤ ηmin)
    (L : AddSubgroup (Site d)) (_hL : L.index ≠ 0) (P : Measure (Site d → ℤ)) : Prop :=
  IsProbabilityMeasure P → (∀ᵐ η ∂P, InOmega d ηmin η) → StationaryOn d L P → ErgodicOn d L P →
  FiniteRangeOfDependence d P → PathFillingHyp d P → StronglyBoxCrossingHyp d P →
  Exploding.External.LiggettSchonmannStacey →
  Exploding.External.LiggettSchonmannStaceyBoundedDegree →
  Exploding.External.MathieuHoleVolume →
  Exploding.External.AntalPisztoraChemicalDistance →
  (∀ (k : Fin d → ℕ), (∀ i, 0 < k i) →
    ∃ m : ℕ, KDependent m (P.map fun η (j : Site d) => decide (StronglyBoxCrossed η k j))) →
  (∀ (y : Site d), y ∈ L → y ≠ 0 →
    ∀ (s : Finset (Site d)) (S : Set (s → ℤ)), MeasurableSet S →
      ∃ n : ℕ, P (cylinder s S ∩
        (fun η : Site d → ℤ => fun z => η (y + z))^[n] ⁻¹' cylinder s S) =
        P (cylinder s S) * P (cylinder s S)) →
  glw2_KingmanCore → glw2_LipschitzLocal d ηmin P → glw_Conclusion d P


end Exploding
