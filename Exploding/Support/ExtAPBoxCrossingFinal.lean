/-
The bond box-crossing interface at the critical density.

For bond percolation of density `q` on `ℤ^d`, the star duality now gives an
unconditional high-density box crossing.  The remaining step toward
`xap15_BoxCrossing d` — the extension from high density down to every density
`q > bondCritical d` — is the block (renormalisation) argument, isolated below as
`xmw_HighToCritical`.

This file supplies the parts that are unconditionally available.  It proves that the
in-box crossing event `xap15_OpenCrosses` depends only on the bonds inside the box
(hence is measurable), that a good star-crossing of the box realises an open bond
crossing that stays inside the box (`xbc_Crosses` of the good-site field implies
`xap15_OpenCrosses`), and that this high-density crossing is almost sure.  Applying
the almost-sure-to-limit step `xmu_tendsto_of_ae_eventually` then converts the
almost-sure statement into the limit of probabilities appearing in
`xap15_BoxCrossing d`.
-/
import Exploding.Support.ExtAPUnconditional
import Exploding.Support.ExtAPProof16

open Exploding LatticeProb MeasureTheory Filter Relation
open scoped Classical Topology ENNReal

namespace Exploding

variable {d : ℕ}

/-! ### The bonds inside the box -/

/-- The bonds with both endpoints in the box `xap11_ball d n`. -/
noncomputable def xmw_boxBonds (d n : ℕ) : Finset (Site d × Fin d) :=
  (((xap11_ball d n).product (Finset.univ : Finset (Fin d))).filter
    (fun e : Site d × Fin d => e.1 + unit e.2 ∈ xap11_ball d n))

theorem xmw_mem_boxBonds {n : ℕ} {z : Site d} {i : Fin d} :
    (z, i) ∈ xmw_boxBonds d n ↔
      z ∈ xap11_ball d n ∧ z + unit i ∈ xap11_ball d n := by
  simp [xmw_boxBonds, Finset.mem_filter, Finset.mem_product]

/-- Agreement on the bonds inside the box gives the same open adjacency for any two sites
of the box. -/
theorem xmw_openBonds_agree {n : ℕ} {ω ω' : Site d × Fin d → Bool}
    (h : ∀ e ∈ xmw_boxBonds d n, ω e = ω' e) {a b : Site d}
    (ha : a ∈ xap11_ball d n) (hb : b ∈ xap11_ball d n) :
    (openBondGraph ω).Adj a b ↔ (openBondGraph ω').Adj a b := by
  rw [openBondGraph, SimpleGraph.fromRel_adj, openBondGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, hrel⟩
    refine ⟨hne, ?_⟩
    rcases hrel with ⟨i, hb', hω⟩ | ⟨i, ha', hω⟩
    · left
      refine ⟨i, hb', ?_⟩
      rw [← h (a, i) (xmw_mem_boxBonds.mpr ⟨ha, by rw [← hb']; exact hb⟩)]
      exact hω
    · right
      refine ⟨i, ha', ?_⟩
      rw [← h (b, i) (xmw_mem_boxBonds.mpr ⟨hb, by rw [← ha']; exact ha⟩)]
      exact hω
  · rintro ⟨hne, hrel⟩
    refine ⟨hne, ?_⟩
    rcases hrel with ⟨i, hb', hω⟩ | ⟨i, ha', hω⟩
    · left
      refine ⟨i, hb', ?_⟩
      rw [h (a, i) (xmw_mem_boxBonds.mpr ⟨ha, by rw [← hb']; exact hb⟩)]
      exact hω
    · right
      refine ⟨i, ha', ?_⟩
      rw [h (b, i) (xmw_mem_boxBonds.mpr ⟨hb, by rw [← ha']; exact ha⟩)]
      exact hω

/-- The in-box crossing event depends only on the bonds inside the box. -/
theorem xmw_openCrosses_determined (n : ℕ) (i : Fin d) (ω ω' : Site d × Fin d → Bool)
    (h : ∀ e ∈ xmw_boxBonds d n, ω e = ω' e) :
    xap15_OpenCrosses d n i ω ↔ xap15_OpenCrosses d n i ω' := by
  constructor
  · rintro ⟨x, y, hx, hy, hxb, hyb, hpath⟩
    refine ⟨x, y, hx, hy, hxb, hyb, ?_⟩
    refine xap_rtg_mono (fun a b hab => ?_) hpath
    exact ⟨(xmw_openBonds_agree h hab.2.1 hab.2.2).mp hab.1, hab.2.1, hab.2.2⟩
  · rintro ⟨x, y, hx, hy, hxb, hyb, hpath⟩
    refine ⟨x, y, hx, hy, hxb, hyb, ?_⟩
    refine xap_rtg_mono (fun a b hab => ?_) hpath
    exact ⟨(xmw_openBonds_agree h hab.2.1 hab.2.2).mpr hab.1, hab.2.1, hab.2.2⟩

/-- The in-box crossing event is measurable. -/
theorem xmw_openCrosses_measurable (n : ℕ) (i : Fin d) :
    MeasurableSet {ω : Site d × Fin d → Bool | xap15_OpenCrosses d n i ω} :=
  xbc_measurableSet_of_determined (xmw_boxBonds d n) _
    (fun ω ω' h => xmw_openCrosses_determined n i ω ω' h)

end Exploding

namespace Exploding

variable {d : ℕ}

/-! ### A good star-step realises an open path inside the box -/

/-- The sites of the cube of a good box site can be joined to it by open bonds that stay in
the box, provided the other endpoint also lies in the box. -/
theorem xmw_cube_reach_box {n : ℕ} {ω : Site d × Fin d → Bool} {a : Site d}
    (ha : a ∈ xap11_ball d n) (hgood : xap_Good ω a) :
    ∀ b ∈ xap_cube a, b ∈ xap11_ball d n →
      ReflTransGen (fun x y => (openBondGraph ω).Adj x y ∧
        x ∈ xap11_ball d n ∧ y ∈ xap11_ball d n) a b := by
  intro b hb hbb
  have hacent : a ∈ cent d n := xbc_mem_ball.mp ha
  have key : ∀ s : Finset (Fin d), ∀ c ∈ xap_cube a, c ∈ xap11_ball d n →
      (∀ i, i ∉ s → c i = a i) →
      ReflTransGen (fun x y => (openBondGraph ω).Adj x y ∧
        x ∈ xap11_ball d n ∧ y ∈ xap11_ball d n) a c := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro c _ _ hcs
      have hca : c = a := funext fun i => hcs i (Finset.notMem_empty i)
      subst hca
      exact ReflTransGen.refl
    | insert j s hj ih =>
      intro c hc hcb hcs
      set c' : Site d := Function.update c j (a j) with hc'def
      have hccent : c ∈ cent d n := xbc_mem_ball.mp hcb
      have hc'cube : c' ∈ xap_cube a := by
        intro i
        by_cases hij : i = j
        · subst hij; simp [hc'def]
        · simp only [hc'def, Function.update_of_ne hij]; exact hc i
      have hc'box : c' ∈ xap11_ball d n := by
        refine xbc_mem_ball.mpr ?_
        intro i
        by_cases hij : i = j
        · subst hij; rw [hc'def, Function.update_self]; exact hacent _
        · rw [hc'def, Function.update_of_ne hij]; exact hccent i
      have hc's : ∀ i, i ∉ s → c' i = a i := by
        intro i his
        by_cases hij : i = j
        · subst hij; rw [hc'def, Function.update_self]
        · rw [hc'def, Function.update_of_ne hij]
          exact hcs i (by simp [hij, his])
      have h1 := ih c' hc'cube hc'box hc's
      by_cases hcj : c j = a j
      · have hceq : c' = c := by
          funext i
          by_cases hij : i = j
          · subst hij; rw [hc'def, Function.update_self, hcj]
          · rw [hc'def, Function.update_of_ne hij]
        rw [hceq] at h1; exact h1
      · refine h1.tail ⟨?_, hc'box, hcb⟩
        have hj1 : |c j - a j| ≤ 1 := hc j
        have hcases : c j = a j + 1 ∨ c j = a j - 1 := by
          rcases abs_cases (c j - a j) with ⟨h, _⟩ | ⟨h, _⟩
          · left; omega
          · right; omega
        rcases hcases with hc1 | hc1
        · have hbe : c = c' + unit j := by
            funext i
            by_cases hij : i = j
            · subst hij; simp [hc'def, hc1, unit]
            · simp [hc'def, unit, hij]
          have hlat : (lattice d).Adj c' c := ⟨j, Or.inl hbe⟩
          exact xap_open_adj_of_good hgood hc'cube hc hlat
        · have hbe : c' = c + unit j := by
            funext i
            by_cases hij : i = j
            · subst hij; simp [hc'def, hc1, unit]
            · simp [hc'def, unit, hij]
          have hlat : (lattice d).Adj c' c := ⟨j, Or.inr hbe⟩
          exact xap_open_adj_of_good hgood hc'cube hc hlat
  exact key Finset.univ b hb hbb (fun i hi => absurd (Finset.mem_univ i) hi)

/-- A star-step between two good box sites is realised by an open path inside the box. -/
theorem xmw_star_reach_box {n : ℕ} {ω : Site d × Fin d → Bool} {a b : Site d}
    (ha : a ∈ xap11_ball d n) (hb : b ∈ xap11_ball d n)
    (hgood : xap_Good ω a) (hstar : xap_Star a b) :
    ReflTransGen (fun x y => (openBondGraph ω).Adj x y ∧
      x ∈ xap11_ball d n ∧ y ∈ xap11_ball d n) a b :=
  xmw_cube_reach_box ha hgood b (xap_star_mem_cube hstar) hb

/-- A chain of star-steps between good box sites is realised by an open path inside the box. -/
theorem xmw_goodChain_inBox {n : ℕ} {ω : Site d × Fin d → Bool} {x y : Site d}
    (h : ReflTransGen (fun a b => xap_Star a b ∧ a ∈ xap11_ball d n ∧ b ∈ xap11_ball d n ∧
      xap_Good ω a ∧ xap_Good ω b) x y) :
    ReflTransGen (fun a b => (openBondGraph ω).Adj a b ∧
      a ∈ xap11_ball d n ∧ b ∈ xap11_ball d n) x y := by
  induction h with
  | refl => exact ReflTransGen.refl
  | @tail mid b hpref hstep ih =>
    rcases hstep with ⟨hstar, hmid, hb, hgoodmid, _⟩
    exact ih.trans (xmw_star_reach_box hmid hb hgoodmid hstar)

/-- A good star-crossing of the box is an open bond crossing that stays inside the box. -/
theorem xmw_good_crossing_open (n : ℕ) (i : Fin d) (ω : Site d × Fin d → Bool)
    (h : xbc_Crosses d n i (xbb_goodField d ω)) : xap15_OpenCrosses d n i ω := by
  obtain ⟨x, y, hx, hy, hxb, hyb, hpath⟩ := h
  refine ⟨x, y, hx, hy, xbc_mem_ball.mpr hxb, xbc_mem_ball.mpr hyb, ?_⟩
  refine xmw_goodChain_inBox (xap_rtg_mono (fun a b hab => ?_) hpath)
  exact ⟨xbb_star_of_lattice_adj hab.1, xbc_mem_ball.mpr hab.2.1, xbc_mem_ball.mpr hab.2.2.1,
    of_decide_eq_true (by simpa [xbb_goodField] using hab.2.2.2.1),
    of_decide_eq_true (by simpa [xbb_goodField] using hab.2.2.2.2)⟩

end Exploding

namespace Exploding

variable {d : ℕ}

/-! ### The high-density almost-sure in-box crossing -/

/-- A density close to one whose geometric ratio is below one. -/
noncomputable def xmw_rho (d : ℕ) : ℝ := 1 - (1 / 2) * (1 / 3 : ℝ) ^ (2 * d)

theorem xmw_rho_spec (d : ℕ) :
    0 ≤ xmw_rho d ∧ xmw_rho d < 1 ∧ xbc_rho d (xmw_rho d) < 1 := by
  have h3 : (1 / 3 : ℝ) ^ (2 * d) ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have hle : (1 / 2 : ℝ) * (1 / 3 : ℝ) ^ (2 * d) ≤ 1 := by nlinarith
  have hhalf : xbc_rho d (xmw_rho d) = 1 / 2 := by
    rw [xbc_rho, xmw_rho]
    have h1 : (1 : ℝ) - (1 - (1 / 2) * (1 / 3 : ℝ) ^ (2 * d))
        = (1 / 2) * (1 / 3 : ℝ) ^ (2 * d) := by ring
    rw [h1]
    have h2 : (3 : ℝ) ^ (2 * d) * ((1 / 2) * (1 / 3 : ℝ) ^ (2 * d))
        = (1 / 2) * ((3 : ℝ) * (1 / 3)) ^ (2 * d) := by
      rw [mul_pow]; ring
    rw [h2, show (3 : ℝ) * (1 / 3) = 1 by norm_num, one_pow, mul_one]
  have hpos : 0 < (1 / 2 : ℝ) * (1 / 3 : ℝ) ^ (2 * d) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [xmw_rho]; linarith
  · rw [xmw_rho]; linarith
  · rw [hhalf]; norm_num

/-- **High-density almost-sure in-box bond crossing.**  There is a density threshold below
one such that, above it, almost surely every large box has an open bond crossing that stays
inside the box. -/
theorem xmw_highDensity_ae (d : ℕ) (hd : 2 ≤ d) :
    ∃ p : ℝ, 0 ≤ p ∧ p < 1 ∧ ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      p ≤ q ^ (xap_cubeBonds (0 : Site d)).card →
      ∀ i : Fin d, ∀ᵐ ω ∂(bondPercolation d q),
        ∀ᶠ n : ℕ in atTop, xap15_OpenCrosses d n i ω := by
  classical
  obtain ⟨hρ0', hρ1', hrho'⟩ := xmw_rho_spec d
  set ρ : ℝ := xmw_rho d with hρdef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; exact hρ0'
  have hρ1 : ρ < 1 := by rw [hρdef]; exact hρ1'
  have hrho : xbc_rho d ρ < 1 := by rw [hρdef]; exact hrho'
  obtain ⟨p₀, hp₀1, hp₀⟩ := xbc_lss_transfer (d := d) (k := 2) (by omega) ρ hρ0 hρ1
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
      by simpa [hA] using xmu_ae_eventually_crosses d hd hρ0 hρ1.le hrho i
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
      ⊆ {ω | ∀ᶠ n : ℕ in atTop, xap15_OpenCrosses d n i ω} := by
    intro ω hω
    exact Filter.Eventually.mono (by simpa [hA] using hω)
      (fun n hn => xmw_good_crossing_open n i ω hn)
  rw [MeasureTheory.ae_iff]
  refine le_antisymm ?_ zero_le
  calc (bondPercolation d q) {ω | ¬ ∀ᶠ n : ℕ in atTop, xap15_OpenCrosses d n i ω}
      ≤ (bondPercolation d q) ((xbb_goodField d ⁻¹' A)ᶜ) := by
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_compl_iff]
        exact fun hmem => hω (hsub hmem)
    _ = 0 := by
        rw [measure_compl (hAmeas.preimage (xbb_goodField_measurable d)) (measure_ne_top _ _),
          hmap, measure_univ]
        simp

end Exploding
