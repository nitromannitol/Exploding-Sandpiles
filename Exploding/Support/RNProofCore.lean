/-
The percolation content of Proposition 2.2: the coupling of the good-edge field with Bernoulli bond
percolation, the infinite cluster of the coupled configuration with its holes and chemical distance,
and the resulting set of good cubes.
-/
import Exploding.Support.RNProofGraph
import Exploding.Support.RNProofStrassen
import Exploding.Support.RNProofPercolation
import Exploding.Support.RNProofChem

open MeasureTheory ProbabilityTheory Exploding LatticeProb Filter

namespace Exploding

variable {d : ℕ}

theorem rn_mnorm_add_le (a b : Site d) : mnorm (a + b) ≤ mnorm a + mnorm b := by
  simp only [mnorm, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => abs_add_le _ _

theorem rn_mnorm_neg (a : Site d) : mnorm (-a) = mnorm a := by
  simp [mnorm]

theorem rn_mnorm_unit (i : Fin d) : mnorm (unit i : Site d) = 1 := by
  simp only [mnorm, unit]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem rn_mnorm_sub_le_of_adj {u w : Site d} (y : Site d) (h : (lattice d).Adj u w) :
    mnorm (u - y) ≤ mnorm (w - y) + 1 := by
  obtain ⟨i, hi | hi⟩ := h
  · have : u - y = (w - y) + (-(unit i)) := by rw [hi]; abel
    rw [this]
    calc mnorm ((w - y) + -(unit i)) ≤ mnorm (w - y) + mnorm (-(unit i) : Site d) :=
          rn_mnorm_add_le _ _
      _ = _ := by rw [rn_mnorm_neg, rn_mnorm_unit]
  · have : u - y = (w - y) + unit i := by rw [hi]; abel
    rw [this]
    calc mnorm ((w - y) + unit i) ≤ mnorm (w - y) + mnorm (unit i : Site d) := rn_mnorm_add_le _ _
      _ = _ := by rw [rn_mnorm_unit]

theorem rn_walk_length_ge {S : Set (Site d)} :
    ∀ (u v : S) (p : ((lattice d).induce S).Walk u v), mnorm (u.1 - v.1) ≤ (p.length : ℤ) := by
  intro u v p
  induction p with
  | nil => simp [mnorm]
  | @cons a b c h p ih =>
    simp only [SimpleGraph.Walk.length_cons]
    have : mnorm (a.1 - c.1) ≤ mnorm (b.1 - c.1) + 1 := rn_mnorm_sub_le_of_adj (c : Site d) h
    push_cast
    linarith

/-- The chemical distance clause of Proposition 2.2 for a set of sites. -/
def RnChemClause (d : ℕ) (C : ℝ) (S : Set (Site d)) : Prop :=
  ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ S, ∀ y ∈ S, mnorm x ≤ (n : ℤ) →
    Real.log n ^ (2 : ℕ) ≤ (mnorm (x - y) : ℝ) →
      ∃ m : ℕ, chemDist S x y = (m : ℕ∞) ∧ (1 : ℝ) * (mnorm (x - y) : ℝ) ≤ (m : ℝ) ∧
        (m : ℝ) ≤ C * (mnorm (x - y) : ℝ)

theorem rn_chemDist_ge (S : Set (Site d)) (x y : Site d) :
    (((mnorm (x - y)).toNat : ℕ) : ℕ∞) ≤ chemDist S x y := by
  unfold chemDist
  refine le_sInf ?_
  rintro t ⟨n, rfl, hx, hy, w, rfl⟩
  have h4 : mnorm (x - y) ≤ (w.length : ℤ) := rn_walk_length_ge ⟨x, hx⟩ ⟨y, hy⟩ w
  have h2 : (mnorm (x - y)).toNat ≤ w.length := by
    have h3 : 0 ≤ mnorm (x - y) := Finset.sum_nonneg fun i _ => abs_nonneg _
    omega
  exact_mod_cast h2

theorem rn_chemDist_le_walk (S : Set (Site d)) {x y : Site d} (hx : x ∈ S) (hy : y ∈ S)
    (w : ((lattice d).induce S).Walk ⟨x, hx⟩ ⟨y, hy⟩) : chemDist S x y ≤ (w.length : ℕ∞) := by
  unfold chemDist
  exact sInf_le ⟨w.length, rfl, hx, hy, w, rfl⟩

theorem rn_lift_walk {ζ : RnBond d → Bool} {i : Site d} :
    ∀ {u v : Site d} (p : (openBondGraph ζ).Walk u v)
      (hu : u ∈ {y | (openBondGraph ζ).Reachable i y}) (hv : v ∈ {y | (openBondGraph ζ).Reachable i y}),
      ∃ w : ((lattice d).induce {y | (openBondGraph ζ).Reachable i y}).Walk ⟨u, hu⟩ ⟨v, hv⟩,
        w.length = p.length := by
  intro u v p
  induction p with
  | nil => intro hu hv; exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons a b c h p ih =>
    intro hu hv
    have hb : b ∈ {y | (openBondGraph ζ).Reachable i y} := hu.trans h.reachable
    obtain ⟨w, hw⟩ := ih hb hv
    exact ⟨SimpleGraph.Walk.cons (G := (lattice d).induce {y | (openBondGraph ζ).Reachable i y})
      (u := ⟨a, hu⟩) (v := ⟨b, hb⟩) (rn_openBond_adj h).1 w, by
      rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_cons, hw]⟩

theorem rn_nonIso_le_of_le {g : Site d → Bool} {ζ : RnBond d → Bool}
    (hζ : ∀ b, ζ b = true → g b.1 = true ∧ g (b.1 + unit b.2) = true) (z : Site d)
    (hz : rn_nonIso ζ z = true) : g z = true := by
  simp only [rn_nonIso, decide_eq_true_eq] at hz
  obtain ⟨b, hb, hb2⟩ := hz
  have h := hζ b hb2
  simp only [rn_incident, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hb
  rcases hb with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact h.1
  · have : z - unit j + unit j = z := by abel
    simpa [this] using h.2

/-- **The deterministic conclusion.**  An infinite open cluster of a bond configuration lying below
the good-edge field of `g`, with small holes and the chemical distance bound, is the set of cubes
asked for in Proposition 2.2. -/
theorem rn_conclude {ζ : RnBond d → Bool} {g : Site d → Bool}
    (hζ : ∀ b, ζ b = true → g b.1 = true ∧ g (b.1 + unit b.2) = true) {i : Site d} {C : ℝ}
    (hinf : {y | (openBondGraph ζ).Reachable i y}.Infinite)
    (hhole : RnHoleProp d {y | (openBondGraph ζ).Reachable i y}) (hchem : RnChemProp d C ζ) :
    ∃ S : Set (Site d), S.Infinite ∧ (∀ x ∈ S, g x = true) ∧
      (∀ x ∈ S, ∀ y ∈ S, y ∈ componentIn S x) ∧ RnHoleProp d S ∧ RnChemClause d C S := by
  set K : Set (Site d) := {y | (openBondGraph ζ).Reachable i y} with hK
  refine ⟨K, hinf, ?_, ?_, hhole, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := (hinf.sdiff (Set.finite_singleton x)).nonempty
    have hyx : y ≠ x := hyx
    have hreach : (openBondGraph ζ).Reachable x y := hx.symm.trans hy
    obtain ⟨p⟩ := hreach
    cases p with
    | nil => exact absurd rfl hyx
    | cons h _ => exact rn_nonIso_le_of_le hζ x (rn_openBond_adj h).2.1
  · intro x hx y hy
    obtain ⟨p⟩ : (openBondGraph ζ).Reachable x y := hx.symm.trans hy
    obtain ⟨w, _⟩ := rn_lift_walk (i := i) p hx hy
    exact ⟨hx, hy, ⟨w⟩⟩
  · obtain ⟨n0, hn0⟩ := hchem
    refine ⟨n0, fun n hn x hx y hy hxn hlog => ?_⟩
    have hreach : (openBondGraph ζ).Reachable x y := hx.symm.trans hy
    obtain ⟨m, hm, hmC⟩ := hn0 n hn x y hxn hlog hreach
    obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_eq_coe hm
    obtain ⟨w, hw⟩ := rn_lift_walk (i := i) p hx hy
    have hle : chemDist K x y ≤ (m : ℕ∞) := by
      have := rn_chemDist_le_walk K hx hy w
      rwa [hw, hp] at this
    have hge := rn_chemDist_ge K x y
    have hne : chemDist K x y ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top m) hle
    obtain ⟨m', hm'⟩ := ENat.ne_top_iff_exists.mp hne
    have h1 : m' ≤ m := by
      rw [← hm'] at hle; exact_mod_cast hle
    have h2 : (mnorm (x - y)).toNat ≤ m' := by
      rw [← hm'] at hge; exact_mod_cast hge
    refine ⟨m', hm'.symm, ?_, ?_⟩
    · have h3 : 0 ≤ mnorm (x - y) := Finset.sum_nonneg fun i _ => abs_nonneg _
      have h4 : (mnorm (x - y) : ℤ) ≤ (m' : ℤ) := by omega
      have h5 : (mnorm (x - y) : ℝ) ≤ (m' : ℝ) := by exact_mod_cast h4
      linarith
    · exact (by exact_mod_cast h1 : (m' : ℝ) ≤ m).trans hmC

theorem rn_edge_measurable {Ω : Type} [MeasurableSpace Ω] (X : Site d → Ω → Bool)
    (hX : ∀ x, Measurable (X x)) :
    Measurable (fun (ω : Ω) (e : RnBond d) => X e.1 ω && X (e.1 + unit e.2) ω) := by
  refine measurable_pi_lambda _ fun e => ?_
  exact (measurable_of_countable (fun p : Bool × Bool => p.1 && p.2)).comp
    ((hX e.1).prodMk (hX (e.1 + unit e.2)))

theorem rn_bondCritical_le {d : ℕ} {qP : ℝ} (hqP0 : 0 ≤ qP)
    (hPE : ∀ q : ℝ, qP ≤ q → q ≤ 1 → bondTheta d q ≠ 0) : bondCritical d ≤ qP := by
  unfold bondCritical
  refine Real.sSup_le (fun q hq => ?_) hqP0
  obtain ⟨_, hq1, hθ⟩ := hq
  by_contra hlt
  exact hPE q (not_le.mp hlt).le hq1 hθ

/-- **The percolation content of Proposition 2.2.**  Given the cited theorems and the positivity of
the percolation probability of bond percolation at high density, there are `q < 1` and `C` such that
for every field of independent bits of density at least `q` on `ℤ^d`, almost surely the open sites
contain an infinite connected set with small holes and linear chemical distance. -/
theorem rn_core (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) (d : ℕ) (hd : 2 ≤ d)
    (hPE : ∃ qP : ℝ, 0 ≤ qP ∧ qP < 1 ∧ ∀ q : ℝ, qP ≤ q → q ≤ 1 → bondTheta d q ≠ 0) :
    ∃ q : ℝ, q < 1 ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Site d → Ω → Bool), (∀ x, Measurable (X x)) → iIndepFun X P →
        (∀ x, ENNReal.ofReal q ≤ P {ω | X x ω = true}) →
        ∀ᵐ ω ∂P, ∃ S : Set (Site d), S.Infinite ∧ (∀ x ∈ S, X x ω = true) ∧
          (∀ x ∈ S, ∀ y ∈ S, y ∈ componentIn S x) ∧ RnHoleProp d S ∧ RnChemClause d C S := by
  obtain ⟨qP, hqP0, hqP1, hPE'⟩ := hPE
  have hθ : bondTheta d qP ≠ 0 := hPE' qP le_rfl hqP1.le
  have hcrit : bondCritical d ≤ qP := rn_bondCritical_le hqP0 hPE'
  obtain ⟨r, hr1, hhole⟩ := rn_siteField_ae hLSSB hHole d hd qP hqP0 hqP1 hθ
  set m : ℝ := max (max r qP) 0 with hm
  have hm1 : m < 1 := max_lt (max_lt hr1 hqP1) zero_lt_one
  set ρ₁ : ℝ := (1 + m) / 2 with hρ₁
  have hρ₁0 : 0 ≤ ρ₁ := by rw [hρ₁]; linarith [le_max_right (max r qP) 0]
  have hρ₁1 : ρ₁ < 1 := by rw [hρ₁]; linarith
  have hrρ : r ≤ ρ₁ := by
    rw [hρ₁]; linarith [le_max_left r qP, le_max_left (max r qP) 0]
  have hqρ : bondCritical d < ρ₁ := by
    have : qP ≤ m := (le_max_right r qP).trans (le_max_left _ _)
    rw [hρ₁]; linarith
  obtain ⟨C, hC1, hchem⟩ := rn_chem_ae hChem d hd hqρ hρ₁0 hρ₁1.le
  obtain ⟨q, hq1, hdom⟩ := rn_edge_dom hLSSB d ρ₁ hρ₁0 hρ₁1
  refine ⟨q, hq1, C, hC1, ?_⟩
  intro Ω _ P _ X hX hind hmarg
  haveI : IsProbabilityMeasure (bondPercolation d ρ₁) := rn_infinitePi_isProb hρ₁0 hρ₁1.le
  set ν : Measure (RnBond d → Bool) := bondPercolation d ρ₁ with hν
  have hholeρ := hhole ρ₁ hrρ hρ₁1.le
  -- the good set of bond configurations
  set Bad : Set (RnBond d → Bool) := {ζ | ¬ ((∃ i, {y | (openBondGraph ζ).Reachable i y}.Infinite ∧
        RnHoleProp d {y | (openBondGraph ζ).Reachable i y}) ∧ RnChemProp d C ζ)} with hBad
  have hBad0 : ν Bad = 0 := by
    refine measure_mono_null (fun ζ hζ => ?_) (measure_union_null hholeρ (ae_iff.mp hchem))
    by_contra hcon
    simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hcon
    exact hζ ⟨hcon.1, hcon.2⟩
  set Z : Set (RnBond d → Bool) := (toMeasurable ν Bad)ᶜ with hZ
  have hZm : MeasurableSet Z := (measurableSet_toMeasurable ν Bad).compl
  have hZν : ν Zᶜ = 0 := by
    rw [hZ, compl_compl, measure_toMeasurable]; exact hBad0
  have hZgood : ∀ ζ ∈ Z, (∃ i, {y | (openBondGraph ζ).Reachable i y}.Infinite ∧
        RnHoleProp d {y | (openBondGraph ζ).Reachable i y}) ∧ RnChemProp d C ζ := by
    intro ζ hζ
    by_contra hcon
    exact hζ (subset_toMeasurable ν Bad hcon)
  -- the coupling
  set F : Ω → RnBond d → Bool := fun ω e => X e.1 ω && X (e.1 + unit e.2) ω with hF
  have hFm : Measurable F := rn_edge_measurable X hX
  haveI : IsProbabilityMeasure (P.map F) := Measure.isProbabilityMeasure_map hFm.aemeasurable
  have hdomB : ∀ A : Set (RnBond d → Bool), MeasurableSet A → IsIncreasingSet A → ν A ≤ (P.map F) A := by
    intro A hA hinc
    rw [Measure.map_apply hFm hA]
    exact hdom P X hX hind hmarg A hA hinc
  obtain ⟨B, hBm, hBμ, hBex⟩ := rn_strassen_bool ν (P.map F) hdomB Z hZm hZν
  have hae : ∀ᵐ ω ∂P, F ω ∈ B := by
    rw [ae_iff]
    have := hBμ
    rw [Measure.map_apply hFm hBm.compl] at this
    exact this
  refine hae.mono fun ω hω => ?_
  obtain ⟨ζ, hζZ, hζle⟩ := hBex _ hω
  obtain ⟨⟨i, hinf, hhol⟩, hch⟩ := hZgood ζ hζZ
  refine rn_conclude (g := fun x => X x ω) ?_ hinf hhol hch
  intro b hb
  have := hζle b hb
  simp only [hF, Bool.and_eq_true] at this
  exact this

end Exploding
