import Exploding.Support.ArxivBondHoleBoundary
import Exploding.Support.ExtAPProof4

/-!
# Probability of separated bond defects

The defect event for one site is a union of its closed incident bonds.  Separated sites read
disjoint bond coordinates, so their defect events are independent under Bernoulli bond measure.
-/

open LatticeProb MeasureTheory ProbabilityTheory

namespace Exploding

/-- A one-site defect event is measurable in the sigma-algebra of its incident bonds. -/
private theorem arxiv_bond_defect_comap {d : ℕ} (x : Site d) :
    MeasurableSet[MeasurableSpace.comap
      (fun ζ : RnBond d → Bool => (rn_incident d x : Set (RnBond d)).restrict ζ)
      inferInstance]
      {ζ | rn_siteField ζ x = false} := by
  classical
  let A : Set (RnBond d) := rn_incident d x
  let E : Set (RnBond d → Bool) := {ζ | rn_siteField ζ x = false}
  have hA : A.Finite := (rn_incident d x).finite_toSet
  have hdet : ∀ ζ ζ' : RnBond d → Bool,
      (∀ b ∈ A, ζ b = ζ' b) → (ζ ∈ E ↔ ζ' ∈ E) := by
    intro ζ ζ' h
    change (rn_siteField ζ x = false) ↔ (rn_siteField ζ' x = false)
    have hlocal : (∀ b ∈ rn_incident d x, ζ b = true) ↔
        (∀ b ∈ rn_incident d x, ζ' b = true) := by
      constructor
      · intro hζ b hb
        rw [← h b hb]
        exact hζ b hb
      · intro hζ b hb
        rw [h b hb]
        exact hζ b hb
    change (decide (∀ b ∈ rn_incident d x, ζ b = true) = false) ↔
      (decide (∀ b ∈ rn_incident d x, ζ' b = true) = false)
    simp only [decide_eq_false_iff_not]
    exact not_congr hlocal
  have himage : E = (fun ζ : RnBond d → Bool => A.restrict ζ) ⁻¹'
      ((fun ζ : RnBond d → Bool => A.restrict ζ) '' E) := by
    ext ζ
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro hζ
      exact ⟨ζ, hζ, rfl⟩
    · rintro ⟨ζ', hζ', heq⟩
      apply (hdet ζ' ζ (fun b hb => congrFun heq ⟨b, hb⟩)).mp
      exact hζ'
  haveI : Fintype ↥A := hA.fintype
  haveI : Countable (↥A → Bool) := inferInstance
  change MeasurableSet[MeasurableSpace.comap
    (fun ζ : RnBond d → Bool => A.restrict ζ) inferInstance] E
  rw [himage]
  exact (Set.to_countable _).measurableSet.preimage
    (measurable_iff_comap_le.mpr le_rfl)

/-- The closed incident bonds give the one-site defect probability bound. -/
private theorem arxiv_bond_defect_probability_le {d : ℕ} (x : Site d)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    bondPercolation d q {ζ | rn_siteField ζ x = false} ≤
      ENNReal.ofReal (2 * (d : ℝ) * (1 - q)) := by
  classical
  haveI : IsProbabilityMeasure (bitLaw q) := rn_bitLaw_isProb hq0 hq1
  haveI : IsProbabilityMeasure (bondPercolation d q) := rn_infinitePi_isProb hq0 hq1
  have hclosed : ∀ b : RnBond d,
      bondPercolation d q {ζ | ζ b = false} = ENNReal.ofReal (1 - q) := by
    intro b
    have hopen : bondPercolation d q {ζ | ζ b = true} = ENNReal.ofReal q := by
      simpa [bondPercolation] using
        (rn_bernoulli_marg (ι := RnBond d) hq0 hq1 b)
    rw [show {ζ : RnBond d → Bool | ζ b = false} =
        ({ζ | ζ b = true})ᶜ by ext ζ; simp,
      measure_compl (measurableSet_eq_fun (measurable_pi_apply b) measurable_const)
        (measure_ne_top _ _), measure_univ, hopen]
    have hsub : (1 : ENNReal) - ENNReal.ofReal q = ENNReal.ofReal (1 - q) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hq0]
    exact hsub
  have hunion : {ζ : RnBond d → Bool | rn_siteField ζ x = false} =
      ⋃ b ∈ rn_incident d x, {ζ | ζ b = false} := by
    ext ζ
    simp [rn_siteField, decide_eq_false_iff_not]
  rw [hunion]
  calc
    bondPercolation d q (⋃ b ∈ rn_incident d x, {ζ | ζ b = false}) ≤
        ∑ b ∈ rn_incident d x, bondPercolation d q {ζ | ζ b = false} :=
      measure_biUnion_finset_le _ _
    _ = ∑ b ∈ rn_incident d x, ENNReal.ofReal (1 - q) := by
      refine Finset.sum_congr rfl fun b _ => hclosed b
    _ = ((rn_incident d x).card : ENNReal) * ENNReal.ofReal (1 - q) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * d : ℕ) * ENNReal.ofReal (1 - q) := by
      gcongr
      exact_mod_cast rn_card_incident_le x
    _ = ENNReal.ofReal (2 * (d : ℝ) * (1 - q)) := by
      rw [← ENNReal.ofReal_natCast (2 * d),
        ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (2 * d : ℕ) by positivity)]
      congr 1
      norm_num

/-- For pairwise nonadjacent sites, all incident bond blocks are disjoint and their defect
events multiply.  Each factor is bounded by the union bound over at most `2d` closed bonds. -/
theorem arxiv_bond_defects_prob_le {d : ℕ} (F : Finset (Site d))
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → ¬ (lattice d).Adj x y) :
    bondPercolation d q {ζ | ∀ x ∈ F, rn_siteField ζ x = false} ≤
      (ENNReal.ofReal (2 * (d : ℝ) * (1 - q))) ^ F.card := by
  classical
  haveI : IsProbabilityMeasure (bitLaw q) := rn_bitLaw_isProb hq0 hq1
  haveI : IsProbabilityMeasure (bondPercolation d q) := rn_infinitePi_isProb hq0 hq1
  let I := {x // x ∈ F}
  let A : I → Set (RnBond d) := fun x => rn_incident d x.1
  let E : I → Set (RnBond d → Bool) := fun x => {ζ | rn_siteField ζ x.1 = false}
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro x y hxy
    apply Finset.disjoint_coe.mpr
    apply rn_incident_disjoint
    · intro h
      exact hxy (Subtype.ext h)
    · exact hsep x.1 x.2 y.1 y.2 (fun h => hxy (Subtype.ext h))
  have hE : ∀ x : I, MeasurableSet[MeasurableSpace.comap
      (fun ζ : RnBond d → Bool => (A x).restrict ζ) inferInstance] (E x) := by
    intro x
    simpa only [A, E] using arxiv_bond_defect_comap x.1
  have hind : ProbabilityTheory.iIndepSet E (bondPercolation d q) := by
    change ProbabilityTheory.iIndepSet E (Measure.infinitePi fun _ : RnBond d => bitLaw q)
    exact xap4_iIndepSet_of_pairwise_disjoint_bool (bitLaw q) A hdisj E hE
  have hevent : {ζ : RnBond d → Bool | ∀ x ∈ F, rn_siteField ζ x = false} =
      ⋂ x : I, E x := by
    ext ζ
    simp only [Set.mem_setOf_eq, Set.mem_iInter, E, I]
    constructor
    · intro h x
      exact h x.1 x.2
    · intro h x hx
      exact h ⟨x, hx⟩
  have hevent' : (⋂ x : I, E x) =
      ⋂ x ∈ (Finset.univ : Finset I), E x := by simp
  have hsingle : ∀ x : I,
      bondPercolation d q (E x) ≤ ENNReal.ofReal (2 * (d : ℝ) * (1 - q)) := by
    intro x
    simpa only [E] using arxiv_bond_defect_probability_le x.1 hq0 hq1
  rw [hevent, hevent']
  calc
    bondPercolation d q (⋂ x ∈ (Finset.univ : Finset I), E x) =
        ∏ x ∈ (Finset.univ : Finset I), bondPercolation d q (E x) :=
      hind.meas_biInter Finset.univ
    _ ≤ ∏ x ∈ (Finset.univ : Finset I), ENNReal.ofReal (2 * (d : ℝ) * (1 - q)) := by
      refine Finset.prod_le_prod' fun x _ => ?_
      exact hsingle x
    _ = (ENNReal.ofReal (2 * (d : ℝ) * (1 - q))) ^ F.card := by
      rw [Finset.prod_const, Finset.card_univ]
      congr 1
      exact Finset.card_attach

end Exploding
