/-
Probabilistic tools for the background `η` with `η(x) = 2d` with probability `p` and
`η(x) = d` otherwise: events that read the background only on a finite set of sites,
independence of such events on disjoint sets, the probability that a finite set of sites is
fully occupied, and the fact that the background is almost surely at least `d`.
-/
import Exploding.Support.ExtSchTop
import Exploding.Support.ReductionShift

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- The background law: `2d` with probability `p`, and `d` otherwise, independently. -/
noncomputable abbrev xsch_mu (d : ℕ) (p : ℝ) : Measure (Site d → ℤ) :=
  productLaw d (2 * (d : ℤ)) (d : ℤ) p

theorem xsch_chip_isProb (a b : ℤ) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    IsProbabilityMeasure (chipLaw a b p) := by
  refine ⟨?_⟩
  unfold chipLaw
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  norm_num

instance xsch_instProb (d : ℕ) (p : ℝ) [hp : Fact (0 ≤ p ∧ p ≤ 1)] :
    IsProbabilityMeasure (xsch_mu d p) := by
  haveI := xsch_chip_isProb (2 * (d : ℤ)) (d : ℤ) hp.out.1 hp.out.2
  unfold xsch_mu productLaw
  infer_instance

/-- An event that reads the background only on the set `A`. -/
def xsch_Det (A : Set (Site d)) (E : Set (Site d → ℤ)) : Prop :=
  ∀ η η' : Site d → ℤ, (∀ x ∈ A, η x = η' x) → (η ∈ E ↔ η' ∈ E)

theorem xsch_Det.compl {A : Set (Site d)} {E : Set (Site d → ℤ)} (h : xsch_Det A E) :
    xsch_Det A Eᶜ := fun η η' hη => by
  simp only [Set.mem_compl_iff]
  exact not_congr (h η η' hη)

theorem xsch_Det.mono {A B : Set (Site d)} {E : Set (Site d → ℤ)} (h : xsch_Det A E)
    (hAB : A ⊆ B) : xsch_Det B E := fun η η' hη => h η η' (fun x hx => hη x (hAB hx))

theorem xsch_Det.measurableSet_comap {A : Set (Site d)} {E : Set (Site d → ℤ)}
    (hA : A.Finite) (h : xsch_Det A E) :
    @MeasurableSet (Site d → ℤ)
      (MeasurableSpace.comap (fun ω : Site d → ℤ => A.restrict ω) inferInstance) E := by
  haveI : Fintype ↥A := hA.fintype
  haveI : Countable (↥A → ℤ) := inferInstance
  have hE : E = (fun ω : Site d → ℤ => A.restrict ω) ⁻¹'
      ((fun ω : Site d → ℤ => A.restrict ω) '' E) := by
    ext η
    constructor
    · intro hη
      exact ⟨η, hη, rfl⟩
    · rintro ⟨η', hη', heq⟩
      have : ∀ x ∈ A, η' x = η x := fun x hx => congrFun heq ⟨x, hx⟩
      exact (h η' η this).1 hη'
  rw [hE]
  exact (Set.to_countable _).measurableSet.preimage (measurable_iff_comap_le.mpr le_rfl)

theorem xsch_Det.measurableSet {A : Set (Site d)} {E : Set (Site d → ℤ)}
    (hA : A.Finite) (h : xsch_Det A E) : MeasurableSet E := by
  have hf : Measurable (fun ω : Site d → ℤ => A.restrict ω) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply (j : Site d)
  exact hf.comap_le _ (h.measurableSet_comap hA)

theorem xsch_det_Sp (J : Finset (Fin d)) (R : Set (Site d)) :
    xsch_Det R {η | xsch_Sp J R η} := fun _ _ h =>
  ⟨xsch_Sp_congr h, xsch_Sp_congr (fun y hy => (h y hy).symm)⟩

theorem xsch_det_occ (W : Set (Site d)) :
    xsch_Det W {η : Site d → ℤ | ∀ x ∈ W, η x = 2 * (d : ℤ)} := fun _ _ h =>
  ⟨fun hη x hx => by rw [← h x hx]; exact hη x hx,
   fun hη x hx => by rw [h x hx]; exact hη x hx⟩

variable {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)]

/-- Events reading pairwise disjoint finite blocks of sites are independent. -/
theorem xsch_indep_iInter {ι : Type*} (A : ι → Set (Site d)) (hfin : ∀ i, (A i).Finite)
    (hdisj : Pairwise (Function.onFun Disjoint A)) (E : ι → Set (Site d → ℤ))
    (hE : ∀ i, xsch_Det (A i) (E i)) (s : Finset ι) :
    (xsch_mu d p).real (⋂ i ∈ s, E i) = ∏ i ∈ s, (xsch_mu d p).real (E i) := by
  have hν := xsch_chip_isProb (2 * (d : ℤ)) (d : ℤ) (Fact.out : 0 ≤ p ∧ p ≤ 1).1
    (Fact.out : 0 ≤ p ∧ p ≤ 1).2
  have hind : ProbabilityTheory.iIndepSet E (xsch_mu d p) := by
    unfold xsch_mu productLaw
    exact iIndepSet_of_pairwise_disjoint_int (chipLaw (2 * (d : ℤ)) (d : ℤ) p) hν A hdisj E
      (fun i => (hE i).measurableSet_comap (hfin i))
  rw [measureReal_def, hind.meas_biInter s, ENNReal.toReal_prod]
  rfl

/-- Two events reading disjoint finite blocks of sites are independent. -/
theorem xsch_indep_two {A B : Set (Site d)} {E F : Set (Site d → ℤ)}
    (hA : A.Finite) (hB : B.Finite) (hAB : Disjoint A B)
    (hE : xsch_Det A E) (hF : xsch_Det B F) :
    (xsch_mu d p).real (E ∩ F) = (xsch_mu d p).real E * (xsch_mu d p).real F := by
  have h := xsch_indep_iInter (d := d) (p := p) (ι := Bool) (fun b => cond b A B)
    (fun b => by cases b <;> simpa using ‹_›) (by
      intro i j hij
      cases i <;> cases j
      · exact absurd rfl hij
      · exact hAB.symm
      · exact hAB
      · exact absurd rfl hij)
    (fun b => cond b E F) (fun b => by cases b <;> simpa using ‹_›) Finset.univ
  have h' : (⋂ i ∈ (Finset.univ : Finset Bool), bif i then E else F) = E ∩ F := by
    ext η
    simp only [Set.mem_iInter, Finset.mem_univ, true_implies, Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨h true, h false⟩
    · intro h i; cases i with
      | true => exact h.1
      | false => exact h.2
  rw [h'] at h
  simpa [Fintype.prod_bool, Set.inter_comm] using h

/-- The probability that a finite set of sites is fully occupied is `p ^ |W|`. -/
theorem xsch_occ_prob (hd : 1 ≤ d) (W : Finset (Site d)) :
    (xsch_mu d p).real {η | ∀ x ∈ W, η x = 2 * (d : ℤ)} = p ^ W.card := by
  have hp := (Fact.out : 0 ≤ p ∧ p ≤ 1)
  have hset : {η : Site d → ℤ | ∀ x ∈ W, η x = 2 * (d : ℤ)}
      = Set.pi (↑W : Set (Site d)) (fun _ => {2 * (d : ℤ)}) := by
    ext η
    simp [Set.pi]
  haveI := xsch_chip_isProb (2 * (d : ℤ)) (d : ℤ) hp.1 hp.2
  have h1 : chipLaw (2 * (d : ℤ)) (d : ℤ) p {2 * (d : ℤ)} = ENNReal.ofReal p := by
    have hne : (d : ℤ) ≠ 2 * (d : ℤ) := by omega
    simp [chipLaw, hne]
  rw [measureReal_def, hset]
  unfold xsch_mu productLaw
  rw [Measure.infinitePi_pi _ (fun i _ => measurableSet_singleton _)]
  simp only [h1, Finset.prod_const]
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hp.1]

/-- Almost surely the background is at least `d` everywhere. -/
theorem xsch_ae_ge : ∀ᵐ η ∂(xsch_mu d p), ∀ x : Site d, (d : ℤ) ≤ η x := by
  have hp := (Fact.out : 0 ≤ p ∧ p ≤ 1)
  haveI := xsch_chip_isProb (2 * (d : ℤ)) (d : ℤ) hp.1 hp.2
  rw [ae_all_iff]
  intro x
  rw [ae_iff]
  have hmeas : MeasurableSet {m : ℤ | ¬ (d : ℤ) ≤ m} :=
    (measurableSet_le measurable_const measurable_id).compl
  have hset : {η : Site d → ℤ | ¬ (d : ℤ) ≤ η x}
      = (fun η : Site d → ℤ => η x) ⁻¹' {m : ℤ | ¬ (d : ℤ) ≤ m} := rfl
  rw [hset, ← Measure.map_apply (measurable_pi_apply x) hmeas]
  unfold xsch_mu productLaw
  rw [Measure.infinitePi_map_eval]
  have h1 : (2 * (d : ℤ)) ∉ {m : ℤ | ¬ (d : ℤ) ≤ m} := by simp; omega
  have h2 : (d : ℤ) ∉ {m : ℤ | ¬ (d : ℤ) ≤ m} := by simp
  have hdirac1 : Measure.dirac (2 * (d : ℤ)) {m : ℤ | ¬ (d : ℤ) ≤ m} = 0 := by
    rw [Measure.dirac_apply' _ hmeas, Set.indicator_of_notMem h1]
  have hdirac2 : Measure.dirac (d : ℤ) {m : ℤ | ¬ (d : ℤ) ≤ m} = 0 := by
    rw [Measure.dirac_apply' _ hmeas, Set.indicator_of_notMem h2]
  change (chipLaw (2 * (d : ℤ)) (d : ℤ) p) {m : ℤ | ¬ (d : ℤ) ≤ m} = 0
  rw [chipLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, hdirac1, hdirac2]
  simp

/-- Spanning along all directions inside the cube bounds the probability that the cube
is internally spanned. -/
theorem xsch_final (n : ℕ) (x : ℝ)
    (h : (xsch_mu d p).real {η | ¬ xsch_Sp Finset.univ (cube d n) η} ≤ x) :
    ENNReal.ofReal (1 - x) ≤ xsch_mu d p {η | InternallySpanned η n} := by
  have hfin : (cube d n).Finite := by
    have : cube d n ⊆ Set.Icc (fun _ : Fin d => (1 : ℤ)) (fun _ => (n : ℤ)) := by
      intro y hy
      exact ⟨fun i => (hy i).1, fun i => (hy i).2⟩
    exact (Set.finite_Icc _ _).subset this
  have hSmeas : MeasurableSet {η : Site d → ℤ | xsch_Sp Finset.univ (cube d n) η} :=
    (xsch_det_Sp _ _).measurableSet hfin
  have hsub : {η : Site d → ℤ | xsch_Sp Finset.univ (cube d n) η}
      ≤ᵐ[xsch_mu d p] {η : Site d → ℤ | InternallySpanned η n} := by
    filter_upwards [xsch_ae_ge (d := d) (p := p)] with η hη hS
    exact xsch_internallySpanned n η hη hS
  have h1 := measure_mono_ae hsub
  have h2 : (xsch_mu d p).real {η | xsch_Sp Finset.univ (cube d n) η}
      = 1 - (xsch_mu d p).real {η | ¬ xsch_Sp Finset.univ (cube d n) η} := by
    have := probReal_compl_eq_one_sub (μ := xsch_mu d p) hSmeas
    have hc : {η : Site d → ℤ | xsch_Sp Finset.univ (cube d n) η}ᶜ
        = {η | ¬ xsch_Sp Finset.univ (cube d n) η} := rfl
    rw [hc] at this
    linarith
  calc ENNReal.ofReal (1 - x)
      ≤ ENNReal.ofReal ((xsch_mu d p).real {η | xsch_Sp Finset.univ (cube d n) η}) := by
        apply ENNReal.ofReal_le_ofReal
        linarith
    _ = xsch_mu d p {η | xsch_Sp Finset.univ (cube d n) η} := ofReal_measureReal
    _ ≤ _ := h1

end Exploding
