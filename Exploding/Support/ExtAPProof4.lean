/-
Two inputs of the high-density Peierls estimate.

First, events that read disjoint blocks of bond coordinates are independent, so
for a `3`-spaced packing of sites the bad-cube events are independent and the
probability that all cubes of the packing are bad is `(1 - q^N)^{|packing|}`,
with `N` the number of bonds in a cube.

Second, the geometric lower bound that a `*`-connected bad separator between `0`
and `y` has size at least a constant times `mnorm y` is **false**: the `*`-neighbours
of the origin form a `*`-connected separator of the origin from every `y ≠ 0` whose
size is `3^d - 1`, independent of `y`.
-/
import Exploding.Support.ExtAPProof3
import LatticeProb.Prob.Blocks
import Mathlib.Probability.Independence.InfinitePi

open Exploding LatticeProb MeasureTheory ProbabilityTheory

namespace Exploding

variable {d : ℕ}

/-! ### Independence of events on disjoint blocks of bonds -/

/-- Reading a Bernoulli field along the disjoint union of a family of blocks is
reading it along an injective family of indices. -/
theorem xap4_map_blocks_bool {ι V : Type*} (ν : Measure Bool) [IsProbabilityMeasure ν]
    (A : ι → Set V) (hdisj : Pairwise (Function.onFun Disjoint A)) :
    (Measure.infinitePi fun _ : V => ν).map (fun ω (i : ι) => (A i).restrict ω)
      = Measure.infinitePi fun i : ι => Measure.infinitePi fun _ : ↥(A i) => ν := by
  have h1 : (Measure.infinitePi fun _ : V => ν).map
      (fun ω p => ω (blockIndex A p))
      = Measure.infinitePi fun _ : (i : ι) × ↥(A i) => ν :=
    infinitePi_map_comp' ν (blockIndex A) (blockIndex_injective A hdisj)
  have h2 := Measure.infinitePi_map_piCurry (fun (i : ι) (_ : ↥(A i)) => (ν : Measure Bool))
  have hcomp : (fun (ω : V → Bool) (i : ι) => (A i).restrict ω)
      = ⇑(MeasurableEquiv.piCurry fun (_ : ι) (_ : ↥(A _)) => Bool)
        ∘ (fun (ω : V → Bool) p => ω (blockIndex A p)) := rfl
  rw [hcomp, ← Measure.map_map (MeasurableEquiv.piCurry _).measurable
    (measurable_pi_lambda _ fun p => measurable_pi_apply (blockIndex A p)), h1, h2]

/-- The functions restricting to the blocks of a pairwise-disjoint family are
independent. -/
theorem xap4_iIndepFun_restrict_of_pairwise_disjoint_bool {ι V : Type*}
    (ν : Measure Bool) [IsProbabilityMeasure ν] (A : ι → Set V)
    (hdisj : Pairwise (Function.onFun Disjoint A)) :
    ProbabilityTheory.iIndepFun (fun (i : ι) (ω : V → Bool) => (A i).restrict ω)
      (Measure.infinitePi fun _ : V => ν) := by
  have hm : AEMeasurable (fun (ω : V → Bool) (i : ι) => (A i).restrict ω)
      (Measure.infinitePi fun _ : V => ν) := by
    refine (measurable_pi_lambda _ fun i => ?_).aemeasurable
    exact measurable_pi_lambda _ fun j => measurable_pi_apply (j : V)
  rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map₀ hm,
    xap4_map_blocks_bool ν A hdisj]
  congr 1
  funext i
  exact (Measure.infinitePi_map_restrict' (μ := fun _ : V => ν) (I := A i)).symm

theorem xap4_iIndep_comap_of_pairwise_disjoint_bool {ι V : Type*}
    (ν : Measure Bool) [IsProbabilityMeasure ν] (A : ι → Set V)
    (hdisj : Pairwise (Function.onFun Disjoint A)) :
    ProbabilityTheory.iIndep
      (fun i : ι => MeasurableSpace.comap (fun ω : V → Bool => (A i).restrict ω) inferInstance)
      (Measure.infinitePi fun _ : V => ν) :=
  xap4_iIndepFun_restrict_of_pairwise_disjoint_bool ν A hdisj

/-- Events reading the blocks of a pairwise-disjoint family are independent. -/
theorem xap4_iIndepSet_of_pairwise_disjoint_bool {ι V : Type*}
    (ν : Measure Bool) [IsProbabilityMeasure ν] (A : ι → Set V)
    (hdisj : Pairwise (Function.onFun Disjoint A)) (E : ι → Set (V → Bool))
    (hE : ∀ i, MeasurableSet[MeasurableSpace.comap
      (fun ω : V → Bool => (A i).restrict ω) inferInstance] (E i)) :
    ProbabilityTheory.iIndepSet E (Measure.infinitePi fun _ : V => ν) := by
  rw [ProbabilityTheory.iIndepSet_iff_iIndep]
  refine ProbabilityTheory.iIndep_of_iIndep_of_le
    (xap4_iIndep_comap_of_pairwise_disjoint_bool ν A hdisj) fun i => ?_
  exact MeasurableSpace.generateFrom_le fun s hs => by
    rw [Set.mem_singleton_iff] at hs
    exact hs ▸ hE i

/-! ### Disjoint cubes carry disjoint bond blocks -/

/-- Far sites of the cube lattice have disjoint bond blocks. -/
theorem xap4_cubeBonds_disjoint {z w : Site d} (hfar : ∃ i, 3 ≤ |z i - w i|) :
    Disjoint (xap_cubeBonds z) (xap_cubeBonds w) := by
  rw [Finset.disjoint_left]
  intro e hez hew
  rw [xap_mem_cubeBonds] at hez hew
  obtain ⟨i, hi⟩ := hfar
  have h1 : |e.1 i - z i| ≤ 1 := hez.1 i
  have h2 : |e.1 i - w i| ≤ 1 := hew.1 i
  have hle : |z i - w i| ≤ 2 := by
    calc |z i - w i| = |(z i - e.1 i) + (e.1 i - w i)| := by ring_nf
      _ ≤ |z i - e.1 i| + |e.1 i - w i| := abs_add_le _ _
      _ = |e.1 i - z i| + |e.1 i - w i| := by rw [abs_sub_comm]
      _ ≤ 1 + 1 := add_le_add h1 h2
  omega

/-- Translating by `z` is a bijection from the origin's bond block to `z`'s. -/
theorem xap4_mem_cubeBonds_add (z : Site d) (e : Site d × Fin d) :
    (e.1 + z, e.2) ∈ xap_cubeBonds z ↔ e ∈ xap_cubeBonds (0 : Site d) := by
  simp only [xap_mem_cubeBonds, xap_cube, Set.mem_setOf_eq, Pi.add_apply, Pi.zero_apply, sub_zero]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => by have := h1 i; rwa [add_sub_cancel_right] at this,
      fun i => by
        have := h2 i
        rw [show e.1 i + z i + unit e.2 i - z i = e.1 i + unit e.2 i by ring] at this
        exact this⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => by rw [add_sub_cancel_right]; exact h1 i,
      fun i => by
        rw [show e.1 i + z i + unit e.2 i - z i = e.1 i + unit e.2 i by ring]
        exact h2 i⟩

/-- Every cube has the same number of bonds as the cube about the origin. -/
theorem xap4_cubeBonds_card_eq (z : Site d) :
    (xap_cubeBonds z).card = (xap_cubeBonds (0 : Site d)).card := by
  symm
  have himg : (xap_cubeBonds (0 : Site d)).image (fun e : Site d × Fin d => (e.1 + z, e.2))
      = xap_cubeBonds z := by
    ext e
    rw [Finset.mem_image]
    constructor
    · rintro ⟨e', he', rfl⟩
      exact (xap4_mem_cubeBonds_add z e').mpr he'
    · intro he
      refine ⟨(e.1 - z, e.2), ?_, ?_⟩
      · exact (xap4_mem_cubeBonds_add z (e.1 - z, e.2)).mp
          (by simpa [Pi.sub_apply, Pi.add_apply] using he)
      · ext i <;> simp [Pi.sub_apply, Pi.add_apply]
  rw [← himg, Finset.card_image_of_injective]
  intro e e' h
  exact Prod.ext (add_right_cancel (Prod.mk.inj h).1) (Prod.mk.inj h).2

/-! ### The probability that a packing is all bad -/

/-- The good event of a cube reads only that cube's bonds. -/
theorem xap4_goodSet_comap (z : Site d) :
    MeasurableSet[MeasurableSpace.comap
      (fun ω : Site d × Fin d → Bool => (xap_cubeBonds z).restrict ω) inferInstance]
      {ω : Site d × Fin d → Bool | xap_Good ω z} := by
  classical
  refine (MeasurableSpace.measurableSet_comap (f := fun ω : Site d × Fin d → Bool =>
    (xap_cubeBonds z).restrict ω)).mpr
      ⟨{v : ↥(xap_cubeBonds z) → Bool | ∀ e, v e = true}, ?_, ?_⟩
  · rw [show {v : ↥(xap_cubeBonds z) → Bool | ∀ e, v e = true}
        = ⋂ e, {v | v e = true} by ext v; simp]
    exact MeasurableSet.iInter (fun e : ↥(xap_cubeBonds z) => by
      change MeasurableSet ((fun v : ↥(xap_cubeBonds z) → Bool => v e) ⁻¹' {true})
      exact (measurable_pi_apply e) (measurableSet_singleton true))
  · ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Finset.restrict]
    rw [xap_good_iff]
    constructor
    · intro h e he; exact h ⟨e, he⟩
    · intro h e; exact h e.1 e.2

/-- The bad event of a cube reads only that cube's bonds. -/
theorem xap4_badSet_comap (z : Site d) :
    MeasurableSet[MeasurableSpace.comap
      (fun ω : Site d × Fin d → Bool => (xap_cubeBonds z).restrict ω) inferInstance]
      {ω : Site d × Fin d → Bool | ¬ xap_Good ω z} :=
  (xap4_goodSet_comap z).compl

/-- A `3`-spaced packing of bad cubes has probability `(1 - q^N)^{|packing|}`,
where `N` is the number of bonds in a cube. -/
theorem xap4_packing_bad_prob {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (Γ' : Finset (Site d))
    (hfar : ∀ z ∈ Γ', ∀ w ∈ Γ', z ≠ w → ∃ i, 3 ≤ |z i - w i|) :
    bondPercolation d q {ω | ∀ z ∈ Γ', ¬ xap_Good ω z} =
      (1 - ENNReal.ofReal q ^ (xap_cubeBonds (0 : Site d)).card) ^ Γ'.card := by
  classical
  haveI : IsProbabilityMeasure (bitLaw q) := rn_bitLaw_isProb h0 h1
  haveI : IsProbabilityMeasure (bondPercolation d q) := rn_infinitePi_isProb h0 h1
  set ι := {z // z ∈ Γ'} with hι
  have hind : ProbabilityTheory.iIndepSet (fun z : ι => {ω | ¬ xap_Good ω z.1})
      (bondPercolation d q) := by
    refine xap4_iIndepSet_of_pairwise_disjoint_bool (bitLaw q)
      (fun z : ι => (xap_cubeBonds z.1 : Set (Site d × Fin d))) ?_ _ ?_
    · intro z w hne
      exact Finset.disjoint_coe.mpr
        (xap4_cubeBonds_disjoint (hfar z.1 z.2 w.1 w.2 (fun h => hne (Subtype.ext h))))
    · intro z
      exact xap4_badSet_comap z.1
  have heq : {ω : Site d × Fin d → Bool | ∀ z ∈ Γ', ¬ xap_Good ω z}
      = ⋂ z : ι, {ω | ¬ xap_Good ω z.1} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h z; exact h z.1 z.2
    · intro h z hz; exact h ⟨z, hz⟩
  rw [heq, show (⋂ z : ι, {ω | ¬ xap_Good ω z.1})
      = ⋂ z ∈ (Finset.univ : Finset ι), {ω | ¬ xap_Good ω z.1} by simp,
    hind.meas_biInter Finset.univ]
  have hfactor : ∀ z : ι, bondPercolation d q {ω | ¬ xap_Good ω z.1}
      = 1 - ENNReal.ofReal q ^ (xap_cubeBonds (0 : Site d)).card := by
    intro z
    rw [show {ω : Site d × Fin d → Bool | ¬ xap_Good ω z.1}
        = {ω | xap_Good ω z.1}ᶜ by ext; simp,
      measure_compl (xap_good_measurable z.1) (measure_ne_top _ _), measure_univ,
      xap_good_prob h0 h1 z.1, xap4_cubeBonds_card_eq z.1]
  rw [Finset.prod_congr rfl (fun z _ => hfactor z), Finset.prod_const, Finset.card_univ]
  congr 1
  exact Finset.card_attach

/-! ### The geometric lower bound is false -/

/-- The `*`-neighbours of the origin. -/
def xap4_starNeighbors (d : ℕ) : Set (Site d) := {z | xap_Star (0 : Site d) z}

theorem xap4_starNeighbors_finite (d : ℕ) : (xap4_starNeighbors d).Finite := by
  refine (Finset.finite_toSet (xap_cubeFinset (0 : Site d))).subset ?_
  intro z hz
  change z ∈ xap_cubeFinset (0 : Site d)
  rw [xap_mem_cubeFinset, xap_cube, Set.mem_setOf_eq]
  intro i
  have := hz.2 i
  rw [Pi.zero_apply, abs_sub_comm] at this
  exact this

/-- The neighbours of the origin separate it from every other site. -/
theorem xap4_starNeighbors_separates {y : Site d} (hy : y ≠ 0) :
    xap3_Separates (xap4_starNeighbors d) y := by
  intro p
  obtain ⟨v, h, p', rfl⟩ :=
    SimpleGraph.Walk.exists_eq_cons_of_ne (G := xap2_kingGraph d)
      (fun h0 => hy h0.symm) p
  refine ⟨v, ?_, h⟩
  rw [SimpleGraph.Walk.support_cons]
  exact List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support p')

/-- A `*`-connected set: any two of its sites are joined by a star-walk. -/
def xap4_StarConnected (Γ : Set (Site d)) : Prop :=
  ∀ z ∈ Γ, ∀ w ∈ Γ, (xap2_kingGraph d).Reachable z w

theorem xap4_starConnected_singleton (a : Site d) :
    xap4_StarConnected ({a} : Set (Site d)) := by
  intro z hz w hw
  have hz' : z = a := Set.mem_singleton_iff.mp hz
  have hw' : w = a := Set.mem_singleton_iff.mp hw
  rw [hz', hw']

/-- **The claimed geometric lower bound is false.**  For every `c > 0` there is a
`*`-connected separator of the origin from a far site `y` whose cardinality is
smaller than `c · mnorm y`: the singleton `{0}` (and, without the origin, the
`*`-neighbours of the origin, of cardinality at most `3^d`).  Hence no
`*`-connected separator has size at least a constant times `mnorm y`. -/
theorem xap4_no_linear_separator_lower_bound (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) :
    ∃ y : Site d, (2 : ℤ) ≤ mnorm y ∧ ∃ Γ : Finset (Site d),
      xap4_StarConnected (↑Γ : Set (Site d)) ∧ xap3_Separates (↑Γ : Set (Site d)) y ∧
        (Γ.card : ℝ) < c * (mnorm y : ℝ) := by
  obtain ⟨N, hN, hN2⟩ : ∃ N : ℕ, (1 : ℝ) < c * (N : ℝ) ∧ 2 ≤ N := by
    obtain ⟨M, hM⟩ := exists_nat_gt (1 / c)
    refine ⟨max M 2, ?_, le_max_right M 2⟩
    rw [div_lt_iff₀ hc] at hM
    have hle : (M : ℝ) * c ≤ (max M 2 : ℕ) * c :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left M 2) hc.le
    calc (1 : ℝ) < (M : ℝ) * c := hM
      _ ≤ (max M 2 : ℕ) * c := hle
      _ = c * (max M 2 : ℕ) := by rw [mul_comm]
  set y : Site d := Pi.single (⟨0, by omega⟩ : Fin d) (N : ℤ) with hy
  have hynorm : mnorm y = (N : ℤ) := by
    rw [hy]
    simp only [mnorm, Pi.single_apply]
    rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin d)]
    · rw [if_pos rfl, abs_of_nonneg (Nat.cast_nonneg N)]
    · intro i _ hi; rw [if_neg hi, abs_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  refine ⟨y, ?_, ({0} : Finset (Site d)), ?_, ?_, ?_⟩
  · rw [hynorm]; exact_mod_cast hN2
  · rw [Finset.coe_singleton]
    exact xap4_starConnected_singleton 0
  · intro p
    rw [Finset.coe_singleton]
    exact ⟨0, SimpleGraph.Walk.start_mem_support p, Set.mem_singleton 0⟩
  · rw [Finset.card_singleton, hynorm]
    push_cast
    exact hN

end Exploding
