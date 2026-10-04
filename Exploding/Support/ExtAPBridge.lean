/-
Bridge from the Antal–Pisztora good sites of high-density bond percolation to the
box-crossing interface of the site field.

The good sites `xap_Good ω z` — the sites whose whole unit cube of bonds is open —
form a field of bits on `ℤ^d` that is `2`-dependent: two good sites at `ℓ^∞`-distance at
least three depend on disjoint sets of bonds.  Its one-site marginals are powers of the
density, `q ^ (xap_cubeBonds z).card`.  The Liggett–Schonmann–Stacey transfer
`xbc_lss_transfer` applied to this field, together with the site box-crossing
`xbc_ae_eventually_crosses`, shows that at high density almost surely every large box
has an open bond crossing.
-/
import Exploding.Support.ExtAPProof15
import Exploding.Support.ExtBCBernoulli3
import Exploding.Support.RNProofGraph

open Exploding LatticeProb MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal

namespace Exploding

variable {d : ℕ}

/-! ### The field of good sites -/

/-- The field of bits recording which sites are good. -/
noncomputable def xbb_goodField (d : ℕ) (ω : Site d × Fin d → Bool) : Site d → Bool :=
  fun z => decide (xap_Good ω z)

/-- The law of the good-site field of bond percolation of density `q`. -/
noncomputable def xbb_goodLaw (d : ℕ) (q : ℝ) : Measure (Site d → Bool) :=
  (bondPercolation d q).map (xbb_goodField d)

theorem xbb_goodField_measurable (d : ℕ) : Measurable (xbb_goodField d) := by
  classical
  refine measurable_pi_iff.mpr (fun z => ?_)
  apply measurable_to_bool
  have h : (fun ω : Site d × Fin d → Bool => xbb_goodField d ω z) ⁻¹' {true}
      = {ω | xap_Good ω z} := by
    ext ω; simp [xbb_goodField]
  rw [h]
  exact xap_good_measurable z

theorem xbb_goodLaw_isProbability {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    IsProbabilityMeasure (xbb_goodLaw d q) := by
  haveI : IsProbabilityMeasure (bondPercolation d q) := rn_infinitePi_isProb h0 h1
  exact Measure.isProbabilityMeasure_map (xbb_goodField_measurable d).aemeasurable

/-! ### Independence of the good sites -/

/-- A `k`-dependent field of bits has the dependence graph joining distinct sites at
`ℓ^∞`-distance at most `k`, so `HasDependenceGraph` for that graph is `KDependent k`. -/
theorem xbb_kdependent_of_hasDependenceGraph {k : ℕ} {μ : Measure (Site d → Bool)}
    (h : HasDependenceGraph (xlssg_graph d k) μ) : KDependent k μ := by
  intro I J hsep
  refine h I J ?_ ?_
  · rw [Finset.disjoint_left]
    intro a haI haJ
    obtain ⟨l, hl⟩ := hsep a haI a haJ
    have hz : |a l - a l| = 0 := by simp
    rw [hz] at hl
    omega
  · intro a haI b haJ hadj
    obtain ⟨l, hl⟩ := hsep a haI b haJ
    exact absurd (hadj.2 l) (not_le.mpr hl)

theorem xbb_good_law_hasDependenceGraph {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    HasDependenceGraph (xlssg_graph d 2) (xbb_goodLaw d q) := by
  classical
  haveI : IsProbabilityMeasure (bondPercolation d q) := rn_infinitePi_isProb h0 h1
  have hX : ∀ a : Site d × Fin d, Measurable (fun ω : Site d × Fin d → Bool => ω a) :=
    fun a => measurable_pi_apply a
  have hind : iIndepFun (fun (a : Site d × Fin d) (ω : Site d × Fin d → Bool) => ω a)
      (bondPercolation d q) := rn_bernoulli_iIndep h0 h1
  have hdep := (rn_dependence_graph (bondPercolation d q)
    (fun (a : Site d × Fin d) (ω : Site d × Fin d → Bool) => ω a) hX hind
    (xlssg_graph d 2) (fun z : Site d => xap_cubeBonds z)
    (fun (z : Site d) (v : Site d × Fin d → Bool) =>
      decide (∀ e ∈ xap_cubeBonds z, v e = true))
    (fun _ a a' hagree => by
      rw [decide_eq_decide]
      exact forall₂_congr (fun e he => by rw [hagree e he]))
    (fun s t hst hnot => by
      rw [Finset.disjoint_left]
      intro e hes het
      rw [xap_mem_cubeBonds] at hes het
      have hsep : ∃ l : Fin d, (2 : ℤ) < |s l - t l| := by
        by_contra hc
        push Not at hc
        exact hnot ⟨hst, fun l => hc l⟩
      obtain ⟨l, hl⟩ := hsep
      have h1 : |s l - e.1 l| ≤ 1 := by
        rw [abs_sub_comm]; exact hes.1 l
      have h2 : |e.1 l - t l| ≤ 1 := het.1 l
      have htri : |s l - t l| ≤ |s l - e.1 l| + |e.1 l - t l| := by
        have h : s l - t l = (s l - e.1 l) + (e.1 l - t l) := by ring
        rw [h]; exact abs_add_le _ _
      linarith)).2
  have hfun : (fun (ω : Site d × Fin d → Bool) (z : Site d) =>
      decide (∀ e ∈ xap_cubeBonds z, ω e = true)) = xbb_goodField d := by
    funext ω z
    simp only [xbb_goodField]
    rw [decide_eq_decide]
    exact (xap_good_iff ω z).symm
  rw [hfun] at hdep
  simpa [xbb_goodLaw] using hdep

/-- The good sites form a `2`-dependent field: cubes at `ℓ^∞`-distance at least three
carry disjoint sets of bonds. -/
theorem xbb_good_indep {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    KDependent 2 (xbb_goodLaw d q) :=
  xbb_kdependent_of_hasDependenceGraph (xbb_good_law_hasDependenceGraph h0 h1)

/-! ### The density of good sites -/

theorem xbb_good_marginal {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (z : Site d) :
    xbb_goodLaw d q {β | β z = true} = ENNReal.ofReal (q ^ (xap_cubeBonds z).card) := by
  haveI : IsProbabilityMeasure (bondPercolation d q) := rn_infinitePi_isProb h0 h1
  have hm : MeasurableSet {β : Site d → Bool | β z = true} :=
    measurableSet_eq_fun (measurable_pi_apply z) measurable_const
  rw [xbb_goodLaw, Measure.map_apply (xbb_goodField_measurable d) hm]
  have hpre : xbb_goodField d ⁻¹' {β : Site d → Bool | β z = true} = {ω | xap_Good ω z} := by
    ext ω; simp [xbb_goodField]
  rw [hpre, xap_good_prob h0 h1 z, ← ENNReal.ofReal_pow h0]

/-! ### Measurability and monotonicity of the site crossing -/

theorem xbb_crosses_measurable (n : ℕ) (i : Fin d) :
    MeasurableSet {β : Site d → Bool | xbc_Crosses d n i β} :=
  xbc_measurableSet_Crosses n i

theorem xbb_crosses_increasing (n : ℕ) (i : Fin d) :
    IsIncreasingEvent {β : Site d → Bool | xbc_Crosses d n i β} :=
  fun _ _ hmem hmono => xbc_Crosses_mono hmono hmem

/-! ### From a good crossing to an open crossing -/

/-- A pair of box faces joined by open bonds. -/
def xbb_BondCrosses (d n : ℕ) (i : Fin d) (ω : Site d × Fin d → Bool) : Prop :=
  ∃ x y : Site d, x i = -(n : ℤ) ∧ y i = (n : ℤ) ∧ x ∈ cent d n ∧ y ∈ cent d n ∧
    (openBondGraph ω).Reachable x y

/-- Nearest-neighbour neighbours are star-adjacent. -/
theorem xbb_star_of_lattice_adj {x y : Site d} (h : (lattice d).Adj x y) : xap_Star x y := by
  refine ⟨h.ne, fun i => ?_⟩
  rw [abs_sub_comm]
  exact xap_lattice_mem_cube h i

/-- A `*`-walk of good sites across the box is an open path joining the two faces. -/
theorem xbb_good_crossing_open (n : ℕ) (i : Fin d) (ω : Site d × Fin d → Bool)
    (h : xbc_Crosses d n i (xbb_goodField d ω)) : xbb_BondCrosses d n i ω := by
  obtain ⟨x, y, hx, hy, hxb, hyb, hpath⟩ := h
  refine ⟨x, y, hx, hy, hxb, hyb, ?_⟩
  refine xap_reachable_of_goodChain (xap_rtg_mono (fun a b hab => ?_) hpath)
  exact ⟨xbb_star_of_lattice_adj hab.1, of_decide_eq_true (by simpa [xbb_goodField] using hab.2.2.2.1),
    of_decide_eq_true (by simpa [xbb_goodField] using hab.2.2.2.2)⟩

/-! ### Almost sure box crossing at high density -/

/-- **High-density bond box crossing.**  For every `ρ < 1` with `3 ^ (2d) (1 - ρ) < 1`
there is `p < 1` such that whenever `q ∈ [0, 1]` has `q ^ (xap_cubeBonds 0).card ≥ p`,
the bond field of density `q` almost surely crosses every large box in every direction. -/
theorem xbb_bond_box_crossing (hdual : xbc_StarDuality d) (hd : 1 ≤ d) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hrho : xbc_rho d ρ < 1) :
    ∃ p : ℝ, 0 ≤ p ∧ p < 1 ∧ ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      p ≤ q ^ (xap_cubeBonds (0 : Site d)).card →
      ∀ i : Fin d, ∀ᵐ ω ∂(bondPercolation d q),
        ∀ᶠ n : ℕ in atTop, xbb_BondCrosses d n i ω := by
  classical
  obtain ⟨p₀, hp₀1, hp₀⟩ := xbc_lss_transfer (d := d) (k := 2) hd ρ hρ0 hρ1
  refine ⟨max p₀ 0, le_max_right _ _, max_lt hp₀1 zero_lt_one, ?_⟩
  intro q hq0 hq1 hpq i
  haveI : IsProbabilityMeasure (bondPercolation d q) := rn_infinitePi_isProb hq0 hq1
  haveI : IsProbabilityMeasure (xbb_goodLaw d q) := xbb_goodLaw_isProbability hq0 hq1
  haveI : IsProbabilityMeasure (sitePercolation d ρ) := rn_infinitePi_isProb hρ0 hρ1.le
  have hkd : KDependent 2 (xbb_goodLaw d q) := xbb_good_indep hq0 hq1
  have hmarg : ∀ s : Site d,
      ENNReal.ofReal (max p₀ 0) ≤ (xbb_goodLaw d q) {ω | ω s = true} := by
    intro s
    rw [xbb_good_marginal hq0 hq1 s, xap4_cubeBonds_card_eq s]
    exact ENNReal.ofReal_le_ofReal hpq
  set A : Set (Site d → Bool) := {β | ∀ᶠ n : ℕ in atTop, xbc_Crosses d n i β} with hA
  have hAmeas : MeasurableSet A := by
    have hset : A = ⋃ N : ℕ, ⋂ n ∈ Set.Ici N, {β : Site d → Bool | xbc_Crosses d n i β} := by
      ext β
      simp only [hA, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, Set.mem_Ici]
      exact Filter.eventually_atTop
    rw [hset]
    exact MeasurableSet.iUnion fun N =>
      MeasurableSet.biInter (Set.to_countable (Set.Ici N))
        (fun n _ => xbc_measurableSet_Crosses n i)
  have hAinc : IsIncreasingEvent A := by
    intro β β' hβ hmono
    exact Filter.Eventually.mono (by simpa [hA] using hβ)
      (fun n hn => xbc_Crosses_mono hmono hn)
  have hsite : sitePercolation d ρ A = 1 := by
    have hae : ∀ᵐ ω ∂(sitePercolation d ρ), ω ∈ A :=
      by simpa [hA] using xbc_ae_eventually_crosses hdual hρ0 hρ1.le hrho i
    rw [← mem_ae_iff_prob_eq_one hAmeas]
    exact hae
  have hmu : (xbb_goodLaw d q) A = 1 := by
    refine le_antisymm prob_le_one ?_
    rw [← hsite]
    exact hp₀ (xbb_goodLaw d q) hkd
      (fun s => (ENNReal.ofReal_le_ofReal (le_max_left p₀ 0)).trans (hmarg s)) A hAmeas hAinc
  have hmap : (bondPercolation d q) (xbb_goodField d ⁻¹' A) = 1 := by
    rw [← Measure.map_apply (xbb_goodField_measurable d) hAmeas, ← xbb_goodLaw]
    exact hmu
  have hsub : (xbb_goodField d ⁻¹' A)
      ⊆ {ω | ∀ᶠ n : ℕ in atTop, xbb_BondCrosses d n i ω} := by
    intro ω hω
    exact Filter.Eventually.mono (by simpa [hA] using hω)
      (fun n hn => xbb_good_crossing_open n i ω hn)
  rw [MeasureTheory.ae_iff]
  refine le_antisymm ?_ zero_le
  calc (bondPercolation d q) {ω | ¬ ∀ᶠ n : ℕ in atTop, xbb_BondCrosses d n i ω}
      ≤ (bondPercolation d q) ((xbb_goodField d ⁻¹' A)ᶜ) := by
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_compl_iff]
        exact fun hmem => hω (hsub hmem)
    _ = 0 := by
        rw [measure_compl (hAmeas.preimage (xbb_goodField_measurable d)) (measure_ne_top _ _),
          hmap, measure_univ]
        simp

end Exploding
