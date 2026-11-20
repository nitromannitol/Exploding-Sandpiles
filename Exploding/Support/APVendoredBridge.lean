/-
Bond percolation of this repository and the Bernoulli bond percolation of the percolation library
vendored in Lattice-Probability (`Percolation.Literature`, from `anthropics/formal-math`).

A configuration `ω : Site d × Fin d → Bool` opens the edge `{x, x + e_i}` when `ω (x, i) = true`.
Its set of open edges `openEdges ω` has open graph `openBondGraph ω`, and the image of
`bondPercolation d q` under `openEdges` is `Percolation.Literature.bondPercolation (zdGraph d) q`,
the product measure `setBer(E(ℤ^d), q)` on sets of edges.  Results proved for the vendored model
(Kesten's theorem, the Bollobás–Riordan crossing estimate) therefore transfer.
-/
import Exploding.Support.Percolation
import LatticeProb.Vendor.FormalMathPercolation

open LatticeProb MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Exploding

variable {d : ℕ}

/-! ### Edges of `ℤ^d` indexed by bonds -/

/-- The edge `{x, x + e_i}` of `ℤ^d` indexed by the bond `(x, i)`. -/
def bondEdge (a : Site d × Fin d) : Sym2 (Site d) := s(a.1, a.1 + unit a.2)

theorem unit_eq_single (i : Fin d) : (unit i : Site d) = Pi.single i 1 := rfl

theorem unit_injective : Function.Injective (unit : Fin d → Site d) := by
  intro i j h
  have := congrFun h i
  by_contra hij
  simp [unit, Pi.single_eq_of_ne hij] at this

theorem bondEdge_injective : Function.Injective (bondEdge (d := d)) := by
  rintro ⟨x, i⟩ ⟨y, j⟩ h
  simp only [bondEdge, Sym2.eq_iff] at h
  rcases h with ⟨rfl, h2⟩ | ⟨h1, h2⟩
  · rw [add_right_inj] at h2
    rw [unit_injective h2]
  · exfalso
    have h3 : x = x + unit i + unit j := by rw [← h2] at h1; exact h1
    have h4 := congrFun h3 i
    simp only [Pi.add_apply, unit] at h4
    by_cases hij : i = j
    · subst hij
      rw [Pi.single_eq_same] at h4
      omega
    · rw [Pi.single_eq_same, Pi.single_eq_of_ne hij] at h4
      omega

theorem bondEdge_mem_edgeSet (a : Site d × Fin d) :
    bondEdge a ∈ (Percolation.Literature.LatticeModels.zdGraph d).edgeSet := by
  rw [bondEdge, SimpleGraph.mem_edgeSet, Percolation.Literature.LatticeModels.zdGraph_adj_iff]
  exact ⟨a.2, Or.inl rfl⟩

theorem exists_bondEdge_eq {e : Sym2 (Site d)} (he : e ∈ (Percolation.Literature.LatticeModels.zdGraph d).edgeSet) :
    ∃ a, bondEdge a = e := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [SimpleGraph.mem_edgeSet, Percolation.Literature.LatticeModels.zdGraph_adj_iff] at he
    obtain ⟨j, hj | hj⟩ := he
    · exact ⟨(x, j), by rw [bondEdge, hj]; rfl⟩
    · exact ⟨(y, j), by rw [bondEdge, Sym2.eq_swap, hj]; rfl⟩

/-! ### Open edges -/

/-- The set of open edges of a bond configuration. -/
def openEdges (ω : Site d × Fin d → Bool) : Set (Sym2 (Site d)) :=
  {e | ∃ a, bondEdge a = e ∧ ω a = true}

theorem bondEdge_mem_openEdges {ω : Site d × Fin d → Bool} {a : Site d × Fin d} :
    bondEdge a ∈ openEdges ω ↔ ω a = true := by
  constructor
  · rintro ⟨b, hb, hωb⟩
    rwa [bondEdge_injective hb] at hωb
  · intro h
    exact ⟨a, rfl, h⟩

theorem notMem_openEdges {ω : Site d × Fin d → Bool} {e : Sym2 (Site d)}
    (he : e ∉ (Percolation.Literature.LatticeModels.zdGraph d).edgeSet) : e ∉ openEdges ω := by
  rintro ⟨a, rfl, -⟩
  exact he (bondEdge_mem_edgeSet a)

theorem openGraph_openEdges (ω : Site d × Fin d → Bool) :
    Percolation.Literature.openGraph (openEdges ω) = openBondGraph ω := by
  ext x y
  rw [Percolation.Literature.openGraph_adj, openBondGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨⟨⟨z, i⟩, hzi, hω⟩, hxy⟩
    refine ⟨hxy, ?_⟩
    simp only [bondEdge, Sym2.eq_iff] at hzi
    rcases hzi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨i, rfl, hω⟩
    · exact Or.inr ⟨i, rfl, hω⟩
  · rintro ⟨hxy, ⟨i, rfl, hω⟩ | ⟨i, rfl, hω⟩⟩
    · exact ⟨⟨(x, i), rfl, hω⟩, hxy⟩
    · exact ⟨⟨(y, i), Sym2.eq_swap, hω⟩, hxy⟩

theorem measurable_openEdges : Measurable (openEdges (d := d)) := by
  rw [measurable_set_iff]
  intro e
  rw [← measurableSet_setOfPred]
  have h : {ω : Site d × Fin d → Bool | e ∈ openEdges ω} =
      ⋃ a ∈ {a : Site d × Fin d | bondEdge a = e}, {ω | ω a = true} := by
    ext ω
    simp only [openEdges, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  rw [h]
  exact MeasurableSet.biUnion (Set.to_countable _) fun a _ =>
    measurableSet_eq_fun (measurable_pi_apply a) measurable_const

/-! ### The law of the open edges -/

theorem bitLaw_eq_bernoulli {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (S : Set Prop) :
    bitLaw q {b : Bool | (b = true) ∈ S} =
      bernoulliMeasure True False (⟨q, hq0, hq1⟩ : unitInterval) S := by
  rw [bernoulliMeasure_def, bitLaw]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (MeasurableSet.of_discrete)]
  have h1 : ((unitInterval.toNNReal ⟨q, hq0, hq1⟩ : NNReal) : ℝ≥0∞) = ENNReal.ofReal q := by
    rw [ENNReal.ofReal, Real.toNNReal_of_nonneg hq0]
    rfl
  have h2 : ((unitInterval.toNNReal (unitInterval.symm ⟨q, hq0, hq1⟩) : NNReal) : ℝ≥0∞) =
      ENNReal.ofReal (1 - q) := by
    rw [ENNReal.ofReal, Real.toNNReal_of_nonneg (by linarith)]
    rfl
  have et : ((true = true) : Prop) = True := eq_true rfl
  have ef : ((false = true) : Prop) = False := eq_false (by decide)
  have ht : {b : Bool | (b = true) ∈ S}.indicator (1 : Bool → ℝ≥0∞) true =
      S.indicator (1 : Prop → ℝ≥0∞) True := by
    by_cases hT : True ∈ S
    · have h' : true ∈ {b : Bool | (b = true) ∈ S} := by
        change (true = true) ∈ S
        rw [et]
        exact hT
      rw [Set.indicator_of_mem h', Set.indicator_of_mem hT]
      rfl
    · have h' : true ∉ {b : Bool | (b = true) ∈ S} := by
        change ¬ (true = true) ∈ S
        rw [et]
        exact hT
      rw [Set.indicator_of_notMem h', Set.indicator_of_notMem hT]
  have hf : {b : Bool | (b = true) ∈ S}.indicator (1 : Bool → ℝ≥0∞) false =
      S.indicator (1 : Prop → ℝ≥0∞) False := by
    by_cases hF : False ∈ S
    · have h' : false ∈ {b : Bool | (b = true) ∈ S} := by
        change (false = true) ∈ S
        rw [ef]
        exact hF
      rw [Set.indicator_of_mem h', Set.indicator_of_mem hF]
      rfl
    · have h' : false ∉ {b : Bool | (b = true) ∈ S} := by
        change ¬ (false = true) ∈ S
        rw [ef]
        exact hF
      rw [Set.indicator_of_notMem h', Set.indicator_of_notMem hF]
  simp only [ENNReal.smul_def, smul_eq_mul, h1, h2, ht, hf]

theorem bernoulli_false_false_apply (p : unitInterval) (S : Set Prop) [Decidable (False ∈ S)] :
    bernoulliMeasure False False p S = if False ∈ S then 1 else 0 := by
  rw [bernoulliMeasure_def, ← add_smul, unitInterval.toNNReal_add_toNNReal_symm, one_smul,
    Measure.dirac_apply' _ (MeasurableSet.of_discrete), Set.indicator_apply]
  rfl

/-- **The image of `bondPercolation d q` under `openEdges` is the vendored Bernoulli bond
percolation `setBer(E(ℤ^d), q)`.** -/
theorem map_openEdges_bondPercolation {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (bondPercolation d q).map openEdges =
      Percolation.Literature.bondPercolation (Percolation.Literature.LatticeModels.zdGraph d) ⟨q, hq0, hq1⟩ := by
  classical
  set p : unitInterval := ⟨q, hq0, hq1⟩
  set E := (Percolation.Literature.LatticeModels.zdGraph d).edgeSet
  set g : (Site d × Fin d → Bool) → Sym2 (Site d) → Prop := fun ω e => e ∈ openEdges ω with hg
  have hgm : Measurable g := measurable_openEdges
  have : IsProbabilityMeasure (bitLaw q) := by
    refine ⟨?_⟩
    simp only [bitLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hq0 (by linarith)]
    simp
  have hlaw : (bondPercolation d q).map g =
      Measure.infinitePi fun e : Sym2 (Site d) => bernoulliMeasure (e ∈ E) False p := by
    refine Measure.eq_infinitePi _ fun s t ht => ?_
    rw [Measure.map_apply hgm (MeasurableSet.pi (Set.to_countable _) fun e _ => ht e)]
    let sI : Finset (Site d × Fin d) := s.preimage bondEdge bondEdge_injective.injOn
    by_cases h : ∀ e ∈ s, e ∉ E → False ∈ t e
    · have hpre : g ⁻¹' Set.pi (s : Set (Sym2 (Site d))) t =
          Set.pi (sI : Set (Site d × Fin d)) fun a => {b : Bool | (b = true) ∈ t (bondEdge a)} := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_ofPred_eq, sI,
          Finset.mem_preimage, hg]
        constructor
        · intro hω a ha
          have := hω _ ha
          rwa [show (bondEdge a ∈ openEdges ω) = (ω a = true) from
            propext bondEdge_mem_openEdges] at this
        · intro hω e he
          by_cases heE : e ∈ E
          · obtain ⟨a, rfl⟩ := exists_bondEdge_eq heE
            rw [show (bondEdge a ∈ openEdges ω) = (ω a = true) from
              propext bondEdge_mem_openEdges]
            exact hω a he
          · rw [show (e ∈ openEdges ω) = False from eq_false (notMem_openEdges heE)]
            exact h e he heE
      rw [hpre, bondPercolation, Measure.infinitePi_pi _ fun _ _ => MeasurableSet.of_discrete,
        ← Finset.prod_filter_mul_prod_filter_not s (· ∈ E)]
      have hsE : s.filter (· ∈ E) = sI.image bondEdge := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_image, sI, Finset.mem_preimage]
        constructor
        · rintro ⟨he, heE⟩
          obtain ⟨a, rfl⟩ := exists_bondEdge_eq heE
          exact ⟨a, he, rfl⟩
        · rintro ⟨a, ha, rfl⟩
          exact ⟨ha, bondEdge_mem_edgeSet a⟩
      have hnot : ∏ e ∈ s.filter (· ∉ E), bernoulliMeasure (e ∈ E) False p (t e) = 1 := by
        refine Finset.prod_eq_one fun e he => ?_
        obtain ⟨he, heE⟩ := Finset.mem_filter.mp he
        rw [show (e ∈ E) = False from eq_false heE, bernoulli_false_false_apply,
          ite_eq_left (h e he heE)]
      rw [hnot, mul_one, hsE, Finset.prod_image fun a _ b _ hab => bondEdge_injective hab]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [show (bondEdge a ∈ E) = True from eq_true (bondEdge_mem_edgeSet a)]
      exact bitLaw_eq_bernoulli hq0 hq1 _
    · push Not at h
      obtain ⟨e, he, heE, hFalse⟩ := h
      have hpre : g ⁻¹' Set.pi (s : Set (Sym2 (Site d))) t = ∅ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_empty_iff_false,
          iff_false, not_forall, hg]
        refine ⟨e, he, ?_⟩
        rwa [show (e ∈ openEdges ω) = False from eq_false (notMem_openEdges heE)]
      rw [hpre, measure_empty]
      symm
      refine Finset.prod_eq_zero he ?_
      rw [show (e ∈ E) = False from eq_false heE, bernoulli_false_false_apply, ite_eq_right hFalse]
  rw [show Percolation.Literature.bondPercolation (Percolation.Literature.LatticeModels.zdGraph d) p =
      setBernoulli E p from rfl, setBernoulli_eq_map, ← hlaw,
    Measure.map_map measurable_setOfPred hgm]
  rfl

end Exploding
