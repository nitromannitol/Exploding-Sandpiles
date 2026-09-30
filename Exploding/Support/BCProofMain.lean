/-
The assembly of the box-crossing proof (Proposition 7.5 of `paper/exploding.tex`,
`exploding.tex:1986-2005`): the layer law at every layer, the union bound over the `n`
layers, the degenerate case `p = 1`, and the symmetry and translation reductions from the
low face of the base box to all `2d` faces of all tiles.
-/
import Exploding.Support.ReductionShift
import Exploding.Support.Hypotheses
import Exploding.Support.BCProofAux
import Exploding.Support.BCProofSym
import Exploding.External.Schonmann

open Exploding LatticeProb MeasureTheory
open scoped Classical

/-! ### Elementary probability -/

theorem bc_chipLaw_prob (a b : ℤ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (chipLaw a b p) := by
  refine ⟨?_⟩
  unfold chipLaw
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp (by linarith)]
  norm_num

/-- **The union bound.**  If each of the events `A i`, `i ∈ s`, has probability at least
`1 - ε`, their intersection has probability at least `1 - |s| ε`. -/
theorem bc_inter_prob_ge {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset ι) (A : ι → Set Ω) (hA : ∀ i ∈ s, MeasurableSet (A i)) (ε : ℝ) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) (h : ∀ i ∈ s, ENNReal.ofReal (1 - ε) ≤ μ (A i)) :
    ENNReal.ofReal (1 - (s.card : ℝ) * ε) ≤ μ (⋂ i ∈ s, A i) := by
  have hper : ∀ i ∈ s, μ (A i)ᶜ ≤ ENNReal.ofReal ε := by
    intro i hi
    rw [measure_compl (hA i hi) (measure_ne_top _ _), measure_univ]
    have h3 : (1 : ENNReal) - ENNReal.ofReal (1 - ε) = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
      congr 1
      ring
    rw [← h3]
    exact tsub_le_tsub_left (h i hi) 1
  have hcompl : μ (⋂ i ∈ s, A i)ᶜ ≤ ENNReal.ofReal ((s.card : ℝ) * ε) := by
    rw [Set.compl_iInter₂]
    refine le_trans (measure_biUnion_finset_le s _) ?_
    refine le_trans (Finset.sum_le_sum hper) ?_
    rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity)]
    simp
  have hmeas : MeasurableSet (⋂ i ∈ s, A i) :=
    Finset.measurableSet_biInter s hA
  rw [measure_compl hmeas (measure_ne_top _ _), measure_univ] at hcompl
  have hx : ENNReal.ofReal (1 - (s.card : ℝ) * ε)
      = 1 - ENNReal.ofReal ((s.card : ℝ) * ε) := by
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
  rw [hx, tsub_le_iff_left]
  exact tsub_le_iff_right.mp hcompl

/-! ### The layer law at every layer -/

/-- **The layer law at layer `i` is Schonmann's law at dimension `d`.**  The paper's two-point
law at dimension `d + 1` is `{d + 1, 2d + 1}`, and the layer background `η(i,·) - 1` is
`chipLaw (2d) d p`, for every layer `i`. -/
theorem bc_layer_law (d : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (i : ℤ) :
    (productLaw (d + 1) (2 * ((d + 1 : ℕ) : ℤ) - 1) ((d + 1 : ℕ) : ℤ) p).map
        (fun ω : Site (d + 1) → ℤ => fun w : Site d => ω (cons i w) - 1)
      = productLaw d (2 * (d : ℤ)) (d : ℤ) p := by
  have hchip := bc_chipLaw_prob (2 * ((d + 1 : ℕ) : ℤ) - 1) ((d + 1 : ℕ) : ℤ) p hp.le hp1
  haveI := hchip
  rw [productLaw, productLaw]
  rw [show (fun ω : Site (d + 1) → ℤ => fun w : Site d => ω (cons i w) - 1)
      = (fun (ζ : Site d → ℤ) => fun w : Site d => (fun m : ℤ => m - 1) (ζ w))
        ∘ (fun ω : Site (d + 1) → ℤ => fun w : Site d => ω (cons i w)) from rfl]
  rw [← MeasureTheory.Measure.map_map
    (hg := measurable_pi_lambda _ fun w => (measurable_pi_apply w).sub measurable_const)
    (g := fun (ζ : Site d → ℤ) => fun w : Site d => (fun m : ℤ => m - 1) (ζ w))
    (hf := measurable_pi_lambda _ fun w => measurable_pi_apply (cons i w))
    (f := fun ω : Site (d + 1) → ℤ => fun w : Site d => ω (cons i w))]
  rw [layer_restrict_eq d (chipLaw (2 * ((d + 1 : ℕ) : ℤ) - 1) ((d + 1 : ℕ) : ℤ) p) hchip i]
  rw [MeasureTheory.Measure.infinitePi_map_pi (μ := fun _ : Site d =>
    chipLaw (2 * ((d + 1 : ℕ) : ℤ) - 1) ((d + 1 : ℕ) : ℤ) p)
    (f := fun _ : Site d => (fun m : ℤ => m - 1))]
  · congr 1
    funext _
    rw [layer_one_site_law (d + 1) p]
    congr 2 <;> omega
  · intro _
    exact (measurable_id.sub measurable_const)

/-- Schonmann's bound for every layer: each layer `η(i,·) - 1` is internally spanned with
probability at least `1 - c exp(-C n)`. -/
theorem bc_layer_spanning_prob (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hSch : Exploding.External.SchonmannBootstrap) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n : ℕ) (i : ℤ),
      ENNReal.ofReal (1 - c * Real.exp (-(C * (n : ℝ)))) ≤
        productLaw (d + 1) (2 * ((d + 1 : ℕ) : ℤ) - 1) ((d + 1 : ℕ) : ℤ) p
          {η | InternallySpanned (fun w : Site d => η (cons i w) - 1) n} := by
  obtain ⟨c, C, hc, hC, hbound⟩ := hSch d hd p hp hp1
  refine ⟨c, C, hc, hC, fun n i => ?_⟩
  have hmeas : MeasurableSet {η : Site d → ℤ | InternallySpanned η n} := by
    rw [show {η : Site d → ℤ | InternallySpanned η n}
        = ⋂ (x : Site d), ⋂ (_ : x ∈ cube d n),
            ⋃ (t : ℕ), {η : Site d → ℤ | spanOdo n η t x = 1} from by
      ext η
      simp only [InternallySpanned, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]]
    refine MeasurableSet.iInter (fun x => MeasurableSet.iInter (fun _ => ?_))
    refine MeasurableSet.iUnion (fun t => ?_)
    exact measurableSet_eq_fun (spanOdo_measurable n t x) measurable_const
  let f : (Site (d + 1) → ℤ) → (Site d → ℤ) := fun ω w => ω (cons i w) - 1
  have hf : Measurable f :=
    measurable_pi_lambda _ fun w => (measurable_pi_apply (cons i w)).sub measurable_const
  have hmap : (productLaw (d + 1) (2 * ((d + 1 : ℕ) : ℤ) - 1) ((d + 1 : ℕ) : ℤ) p).map f
      = productLaw d (2 * (d : ℤ)) (d : ℤ) p := bc_layer_law d p hp hp1.le i
  have hval := congrArg (fun μ : MeasureTheory.Measure (Site d → ℤ) =>
    μ {η : Site d → ℤ | InternallySpanned η n}) hmap
  rw [MeasureTheory.Measure.map_apply hf hmeas] at hval
  rw [show {η : Site (d + 1) → ℤ | InternallySpanned (fun w : Site d => η (cons i w) - 1) n}
      = f ⁻¹' {η : Site d → ℤ | InternallySpanned η n} from rfl]
  rw [hval]
  exact hbound n

theorem bc_productLaw_prob (d : ℕ) (a b : ℤ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (productLaw d a b p) := by
  haveI := bc_chipLaw_prob a b p hp hp1
  rw [productLaw]
  infer_instance

/-! ### Choosing the box size -/

/-- The Schonmann tail `n c exp(-C n)` tends to `0`: some `n ≥ 1` makes it smaller than `δ`. -/
theorem bc_exists_large_n (c C : ℝ) (_hc : 0 < c) (hC : 0 < C) (δ : ℝ) (hδ : 0 < δ) :
    ∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) * (c * Real.exp (-(C * (n : ℝ)))) < δ := by
  have hlim : Filter.Tendsto (fun n : ℕ => (n : ℝ) * (c * Real.exp (-(C * (n : ℝ)))))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => x * Real.exp (-(C * x))) Filter.atTop (nhds 0) := by
      have h2 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
      have h3 : Filter.Tendsto (fun x : ℝ => (C * x) * Real.exp (-(C * x)))
          Filter.atTop (nhds 0) := by
        refine (h2.comp (Filter.tendsto_id.const_mul_atTop hC)).congr' ?_
        filter_upwards with x
        simp only [Function.comp_apply, id_eq, pow_one]
      have h4 : Filter.Tendsto (fun x : ℝ => ((C * x) * Real.exp (-(C * x))) / C)
          Filter.atTop (nhds (0 / C)) := h3.div_const C
      rw [zero_div] at h4
      refine h4.congr' ?_
      filter_upwards with x
      rw [div_eq_iff (ne_of_gt hC)]
      ring
    have h5 : Filter.Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-(C * (n : ℝ))))
        Filter.atTop (nhds 0) := h1.comp tendsto_natCast_atTop_atTop
    have h6 := h5.const_mul c
    rw [mul_zero] at h6
    refine h6.congr' ?_
    filter_upwards with n
    ring
  have hev := hlim.eventually (eventually_lt_nhds hδ)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  exact ⟨max N 1, le_max_right _ _, hN _ (le_max_left _ _)⟩

/-- **All layers are spanned with high probability** (`p < 1`).  By Schonmann's bound each
of the `n` layers fails with probability at most `c exp(-C n)`, and `n c exp(-C n) → 0`. -/
theorem bc_layers_prob_lt (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hSch : Exploding.External.SchonmannBootstrap) :
    ∀ δ : ℝ, 0 < δ → ∃ n : ℕ, 1 ≤ n ∧
      ENNReal.ofReal (1 - δ) <
        productLaw (d + 1) (2 * ((d + 1 : ℕ) : ℤ) - 1) ((d + 1 : ℕ) : ℤ) p
          {η | ∀ i ∈ Finset.Icc 1 n,
            InternallySpanned (fun w : Site d => η (cons (i : ℤ) w) - 1) n} := by
  intro δ hδ
  obtain ⟨c, C, hc, hC, hbound⟩ := bc_layer_spanning_prob d hd p hp hp1 hSch
  haveI := bc_productLaw_prob (d + 1) (2 * ((d + 1 : ℕ) : ℤ) - 1) ((d + 1 : ℕ) : ℤ) p hp.le hp1.le
  obtain ⟨n, hn1, hn⟩ := bc_exists_large_n c C hc hC (min δ (1 / 2)) (lt_min hδ (by norm_num))
  have hmin1 : min δ (1 / 2) ≤ δ := min_le_left _ _
  have hmin2 : min δ (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hε0 : 0 ≤ c * Real.exp (-(C * (n : ℝ))) := by
    have := Real.exp_pos (-(C * (n : ℝ)))
    positivity
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hε1 : c * Real.exp (-(C * (n : ℝ))) ≤ 1 := by
    nlinarith
  have hinter := bc_inter_prob_ge
    (productLaw (d + 1) (2 * ((d + 1 : ℕ) : ℤ) - 1) ((d + 1 : ℕ) : ℤ) p)
    (Finset.Icc 1 n)
    (fun i : ℕ => {η : Site (d + 1) → ℤ |
      InternallySpanned (fun w : Site d => η (cons (i : ℤ) w) - 1) n})
    (fun i _ => layer_spanning_measurable d (i : ℤ) n) _ hε0 hε1
    (fun i _ => hbound n (i : ℤ))
  refine ⟨n, hn1, lt_of_lt_of_le ?_ (le_of_le_of_eq hinter ?_)⟩
  · rw [ENNReal.ofReal_lt_ofReal_iff (by rw [Nat.card_Icc]; simp; nlinarith)]
    rw [Nat.card_Icc]
    simp
    nlinarith
  · congr 1
    ext η
    simp only [Set.mem_iInter, Set.mem_setOf_eq]

/-! ### The degenerate case `p = 1` -/

/-- Almost surely every coordinate of a product field lies in any set of full one-site measure. -/
theorem bc_ae_coord {V : Type*} [Countable V] (μ : Measure ℤ) [IsProbabilityMeasure μ]
    (A : Set ℤ) (h : ∀ᵐ m ∂μ, m ∈ A) :
    ∀ᵐ η ∂(Measure.infinitePi fun _ : V => μ), ∀ x : V, η x ∈ A := by
  rw [ae_all_iff]
  intro x
  exact (measurePreserving_eval_infinitePi (fun _ : V => μ) x).quasiMeasurePreserving.ae h

/-- A background that is at least `2d` everywhere is internally spanned: every site of the box
topples at the first step. -/
theorem bc_spanned_of_large {d : ℕ} (n : ℕ) (bg : Site d → ℤ) (h : ∀ w, 2 * (d : ℤ) ≤ bg w) :
    InternallySpanned bg n := by
  intro x hx
  refine ⟨1, ?_⟩
  show (if x ∉ cube d n then 0
      else if spanOdo n bg 0 x = 1 then 1
      else spanOdo n bg 0 x + (if 2 * (d : ℤ) ≤ bg x + lap (spanOdo n bg 0) x then 1 else 0)) = 1
  rw [if_neg (not_not.mpr hx)]
  have h0 : spanOdo n bg 0 = fun _ => 0 := rfl
  have hlap : lap (spanOdo n bg 0) x = 0 := by
    rw [h0]
    simp [lap, nbrSumZ]
  rw [hlap, h0]
  simp only [zero_add, if_neg (show ¬ ((0 : ℤ) = 1) by norm_num)]
  rw [if_pos (by linarith [h x])]

/-- **All layers are spanned with probability `1`** when `p = 1`: every site carries `2d + 1`
chips, so every layer background is `2d`. -/
theorem bc_layers_prob_one (d : ℕ) :
    ∀ δ : ℝ, 0 < δ → ∃ n : ℕ, 1 ≤ n ∧
      ENNReal.ofReal (1 - δ) <
        productLaw (d + 1) (2 * ((d + 1 : ℕ) : ℤ) - 1) ((d + 1 : ℕ) : ℤ) 1
          {η | ∀ i ∈ Finset.Icc 1 n,
            InternallySpanned (fun w : Site d => η (cons (i : ℤ) w) - 1) n} := by
  intro δ hδ
  haveI := bc_productLaw_prob (d + 1) (2 * ((d + 1 : ℕ) : ℤ) - 1) ((d + 1 : ℕ) : ℤ) 1
    zero_le_one le_rfl
  haveI := bc_chipLaw_prob (2 * ((d + 1 : ℕ) : ℤ) - 1) ((d + 1 : ℕ) : ℤ) 1 zero_le_one le_rfl
  refine ⟨1, le_rfl, ?_⟩
  have hae : ∀ᵐ m ∂(chipLaw (2 * ((d + 1 : ℕ) : ℤ) - 1) ((d + 1 : ℕ) : ℤ) 1),
      m ∈ ({2 * ((d + 1 : ℕ) : ℤ) - 1} : Set ℤ) := by
    rw [ae_iff]
    simp [chipLaw]
  have hall := bc_ae_coord (V := Site (d + 1))
    (chipLaw (2 * ((d + 1 : ℕ) : ℤ) - 1) ((d + 1 : ℕ) : ℤ) 1) _ hae
  have hle : (1 : ENNReal) ≤ productLaw (d + 1) (2 * ((d + 1 : ℕ) : ℤ) - 1) ((d + 1 : ℕ) : ℤ) 1
      {η | ∀ i ∈ Finset.Icc (1 : ℕ) 1,
        InternallySpanned (fun w : Site d => η (cons (i : ℤ) w) - 1) 1} := by
    rw [← measure_univ (μ := productLaw (d + 1) (2 * ((d + 1 : ℕ) : ℤ) - 1) ((d + 1 : ℕ) : ℤ) 1)]
    refine measure_mono_ae ?_
    filter_upwards [hall] with η hη _ i _
    refine bc_spanned_of_large 1 _ (fun w => ?_)
    have := hη (cons (i : ℤ) w)
    rw [Set.mem_singleton_iff] at this
    rw [this]
    push_cast
    linarith
  refine lt_of_lt_of_le ?_ hle
  rw [← ENNReal.ofReal_one]
  rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  linarith

/-- **All layers are spanned with high probability**, for every `p ∈ (0, 1]`. -/
theorem bc_layers_prob (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hSch : Exploding.External.SchonmannBootstrap) :
    ∀ δ : ℝ, 0 < δ → ∃ n : ℕ, 1 ≤ n ∧
      ENNReal.ofReal (1 - δ) <
        productLaw (d + 1) (2 * ((d + 1 : ℕ) : ℤ) - 1) ((d + 1 : ℕ) : ℤ) p
          {η | ∀ i ∈ Finset.Icc 1 n,
            InternallySpanned (fun w : Site d => η (cons (i : ℤ) w) - 1) n} := by
  rcases hp1.lt_or_eq with h | h
  · exact bc_layers_prob_lt d hd p hp h hSch
  · subst h
    exact bc_layers_prob_one d

/-! ### From the low face of the base box to all faces of all tiles -/

/-- **Box-crossing for the two-point law.**  For every `p ∈ (0, 1]` and `δ > 0` there is a box
side `n ≥ 1` such that, for every tile `j`, the tile is crossed in all `2(d+1)` directions with
probability greater than `1 - δ`.  The `n` layers are spanned with high probability, which crosses
the low face of the base box (`box_crossing_core`); every other face of every other tile is the
image of that event under a lattice symmetry, which preserves the product law. -/
theorem bc_boxcrossed_prob (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hSch : Exploding.External.SchonmannBootstrap) :
    ∀ δ : ℝ, 0 < δ → ∃ n : ℕ, 1 ≤ n ∧ ∀ j : Site (d + 1),
      ENNReal.ofReal (1 - δ) <
        productLaw (d + 1) (2 * ((d + 1 : ℕ) : ℤ) - 1) ((d + 1 : ℕ) : ℤ) p
          {η | BoxCrossed η (fun _ : Fin (d + 1) => n) j} := by
  intro δ hδ
  set K : ℕ := (d + 1) * 2 with hK
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  set δ₀ : ℝ := min δ 1 with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min hδ one_pos
  have hδ₀δ : δ₀ ≤ δ := min_le_left _ _
  have hδ₀1 : δ₀ ≤ 1 := min_le_right _ _
  set ε : ℝ := δ₀ / ((K : ℝ) + 1) with hε
  have hε0 : 0 < ε := div_pos hδ₀pos (by positivity)
  have hKε : (K : ℝ) * ε < δ₀ := by
    rw [hε, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  have hε1 : ε ≤ 1 := by
    have : ε ≤ δ₀ := by
      rw [hε]
      exact div_le_self hδ₀pos.le (by linarith)
    linarith
  haveI := bc_productLaw_prob (d + 1) (2 * ((d + 1 : ℕ) : ℤ) - 1) ((d + 1 : ℕ) : ℤ) p hp.le hp1
  haveI := bc_chipLaw_prob (2 * ((d + 1 : ℕ) : ℤ) - 1) ((d + 1 : ℕ) : ℤ) p hp.le hp1
  obtain ⟨n, hn1, hn⟩ := bc_layers_prob d hd p hp hp1 hSch ε hε0
  refine ⟨n, hn1, fun j => ?_⟩
  set E : Set (Site (d + 1) → ℤ) := {η | ∀ i ∈ Finset.Icc 1 n,
    InternallySpanned (fun w : Site d => η (cons (i : ℤ) w) - 1) n} with hE
  have hEm : MeasurableSet E := layer_all_spanning_measurable d n
  choose hfun hsym hcross using fun q : Fin (d + 1) × Bool =>
    bc_exists_sym_for_face (d := d + 1) n (⟨0, by omega⟩ : Fin (d + 1)) q.1 q.2 j
  set A : Fin (d + 1) × Bool → Set (Site (d + 1) → ℤ) :=
    fun q => (fun (η : Site (d + 1) → ℤ) (x : Site (d + 1)) => η (hfun q x)) ⁻¹' E with hA
  have hfm : ∀ q, Measurable (fun (η : Site (d + 1) → ℤ) (x : Site (d + 1)) => η (hfun q x)) :=
    fun q => measurable_pi_lambda _ fun x => measurable_pi_apply _
  have hAm : ∀ q ∈ (Finset.univ : Finset (Fin (d + 1) × Bool)), MeasurableSet (A q) :=
    fun q _ => hEm.preimage (hfm q)
  have hAp : ∀ q ∈ (Finset.univ : Finset (Fin (d + 1) × Bool)),
      ENNReal.ofReal (1 - ε) ≤
        productLaw (d + 1) (2 * ((d + 1 : ℕ) : ℤ) - 1) ((d + 1 : ℕ) : ℤ) p (A q) := by
    intro q _
    have hmap := bc_map_infinitePi (hsym q)
      (chipLaw (2 * ((d + 1 : ℕ) : ℤ) - 1) ((d + 1 : ℕ) : ℤ) p)
    have hval : productLaw (d + 1) (2 * ((d + 1 : ℕ) : ℤ) - 1) ((d + 1 : ℕ) : ℤ) p (A q)
        = productLaw (d + 1) (2 * ((d + 1 : ℕ) : ℤ) - 1) ((d + 1 : ℕ) : ℤ) p E := by
      conv_rhs => rw [productLaw, ← hmap]
      rw [Measure.map_apply (hfm q) hEm]
      rfl
    rw [hval]
    exact (hn).le
  have hinter := bc_inter_prob_ge
    (productLaw (d + 1) (2 * ((d + 1 : ℕ) : ℤ) - 1) ((d + 1 : ℕ) : ℤ) p)
    Finset.univ A hAm ε hε0.le hε1 hAp
  have hcard : (Finset.univ : Finset (Fin (d + 1) × Bool)).card = K := by
    simp [hK]
  rw [hcard] at hinter
  refine lt_of_lt_of_le ?_ (le_trans hinter (measure_mono ?_))
  · rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)]
    linarith
  · intro η hη
    simp only [Set.mem_iInter] at hη
    intro i hi
    have hq := hη (i, hi) (Finset.mem_univ _)
    exact hcross (i, hi) η
      (box_crossing_core n hn1 (fun y => η (hfun (i, hi) y)) hq)

/-- **Proposition 7.5**, assembled: a product background with `ν(m ≥ d) = 1` and
`ν{2d-1} > 0` is box-crossing. -/
theorem bc_box_crossing (d : ℕ) (hd : 2 ≤ d) (ν : Measure ℤ) (hν : IsProbabilityMeasure ν)
    (hlow : ν {m : ℤ | (d : ℤ) ≤ m} = 1) (hhit : 0 < ν {(2 * (d : ℤ) - 1)})
    (hSch : Exploding.External.SchonmannBootstrap) :
    BoxCrossingHyp d (Measure.infinitePi fun _ : Site d => ν) := by
  haveI := hν
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hd' : 1 ≤ d' := by omega
  have hne : ν {(2 * ((d' + 1 : ℕ) : ℤ) - 1)} ≠ ⊤ := measure_ne_top _ _
  have hp : 0 < (ν {(2 * ((d' + 1 : ℕ) : ℤ) - 1)}).toReal :=
    ENNReal.toReal_pos (ne_of_gt hhit) hne
  have hp1 : (ν {(2 * ((d' + 1 : ℕ) : ℤ) - 1)}).toReal ≤ 1 := by
    have h1 : ν {(2 * ((d' + 1 : ℕ) : ℤ) - 1)} ≤ 1 := by
      calc ν {(2 * ((d' + 1 : ℕ) : ℤ) - 1)} ≤ ν Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have h2 := ENNReal.toReal_mono (by simp) h1
    simpa using h2
  intro δ hδ
  obtain ⟨n, hn1, hn⟩ := bc_boxcrossed_prob d' hd' _ hp hp1 hSch δ hδ
  refine ⟨fun _ => n, fun _ => Nat.lt_of_lt_of_le one_pos hn1, fun j => ?_⟩
  exact lt_of_lt_of_le (hn j) (bc_two_point_reduction (d' + 1) (by omega) ν hlow
    (fun _ => n) j)
