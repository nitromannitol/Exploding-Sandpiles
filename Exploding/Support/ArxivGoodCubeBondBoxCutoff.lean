import Exploding.Support.RNProofGood
import Exploding.Support.ArxivActualBondBoxCutoffAE

/-!
# Good cubes coupled to an actual bond cluster

The good-cube indicator field dominates a high-density Bernoulli bond field under the existing
coupling.  The coupling keeps the actual bond root together with its hole cutoff and chemical
estimate, so all geometric conclusions concern one and the same cluster.
-/

open MeasureTheory ProbabilityTheory Exploding LatticeProb Filter

namespace Exploding

variable {d : ℕ}

/-- The actual open-bond cluster inherits a chemical estimate inside its induced lattice graph. -/
private theorem rn_actual_bond_chemical_clause {ζ : RnBond d → Bool} {g : Site d → Bool}
    {i : Site d} {C : ℝ}
    (hζ : ∀ b, ζ b = true → g b.1 = true ∧ g (b.1 + unit b.2) = true)
    (hinf : {y : Site d | (openBondGraph ζ).Reachable i y}.Infinite)
    (hchem : RnChemProp d C ζ) :
    (∀ x ∈ {y : Site d | (openBondGraph ζ).Reachable i y}, g x = true) ∧
      (∀ x ∈ {y : Site d | (openBondGraph ζ).Reachable i y}, ∀ y ∈
        {z : Site d | (openBondGraph ζ).Reachable i z},
          y ∈ componentIn {z : Site d | (openBondGraph ζ).Reachable i z} x) ∧
      RnChemClause d C {y : Site d | (openBondGraph ζ).Reachable i y} := by
  let I : Set (Site d) := {y | (openBondGraph ζ).Reachable i y}
  have hgood : ∀ x ∈ I, g x = true := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := (hinf.sdiff (Set.finite_singleton x)).nonempty
    have hreach : (openBondGraph ζ).Reachable x y := hx.symm.trans hy
    obtain ⟨p⟩ := hreach
    cases p with
    | nil => exact absurd rfl hyx
    | cons h _ => exact rn_nonIso_le_of_le hζ x (rn_openBond_adj h).2.1
  have hconn : ∀ x ∈ I, ∀ y ∈ I, y ∈ componentIn I x := by
    intro x hx y hy
    obtain ⟨p⟩ : (openBondGraph ζ).Reachable x y := hx.symm.trans hy
    obtain ⟨w, _⟩ := rn_lift_walk (i := i) p hx hy
    exact ⟨hx, hy, ⟨w⟩⟩
  obtain ⟨n0, hn0⟩ := hchem
  have hchemical : RnChemClause d C I := by
    refine ⟨n0, fun n hn x hx y hy hxn hlog => ?_⟩
    have hreach : (openBondGraph ζ).Reachable x y := hx.symm.trans hy
    obtain ⟨m, hm, hmC⟩ := hn0 n hn x y hxn hlog hreach
    obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_eq_coe hm
    obtain ⟨w, hw⟩ := rn_lift_walk (i := i) p hx hy
    have hle : chemDist I x y ≤ (m : ℕ∞) := by
      have := rn_chemDist_le_walk I hx hy w
      rwa [hw, hp] at this
    have hge := rn_chemDist_ge I x y
    have hne : chemDist I x y ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top m) hle
    obtain ⟨m', hm'⟩ := ENat.ne_top_iff_exists.mp hne
    have h1 : m' ≤ m := by
      rw [← hm'] at hle
      exact_mod_cast hle
    have h2 : (mnorm (x - y)).toNat ≤ m' := by
      rw [← hm'] at hge
      exact_mod_cast hge
    refine ⟨m', hm'.symm, ?_, ?_⟩
    · have hnorm : 0 ≤ mnorm (x - y) :=
        Finset.sum_nonneg fun j _ => abs_nonneg ((x - y) j)
      have hnat : mnorm (x - y) ≤ (m' : ℤ) := by omega
      have hreal : (mnorm (x - y) : ℝ) ≤ (m' : ℝ) := by exact_mod_cast hnat
      linarith
    · exact (by exact_mod_cast h1 : (m' : ℝ) ≤ (m : ℝ)).trans hmC
  exact ⟨hgood, hconn, hchemical⟩

/-- A joint full-measure event for an actual bond root carries the hole cutoff and chemistry
through the same Strassen witness. -/
private theorem rn_good_field_bond_box_cutoff
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) (d : ℕ) (hd : 2 ≤ d)
    (hPE : ∃ qP : ℝ, 0 ≤ qP ∧ qP < 1 ∧
      ∀ q : ℝ, qP ≤ q → q ≤ 1 → bondTheta d q ≠ 0) :
    ∃ q : ℝ, q < 1 ∧ ∃ C B : ℝ, 1 ≤ C ∧ 1 ≤ B ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Site d → Ω → Bool), (∀ x, Measurable (X x)) → iIndepFun X P →
        (∀ x, ENNReal.ofReal q ≤ P {ω | X x ω = true}) →
        ∀ᵐ ω ∂P, ∃ ζ : RnBond d → Bool, ∃ i : Site d,
          let I : Set (Site d) := {y | (openBondGraph ζ).Reachable i y}
          I.Infinite ∧ (∀ x ∈ I, X x ω = true) ∧
            (∀ x ∈ I, ∀ y ∈ I, y ∈ componentIn I x) ∧ RnHoleProp d I ∧
            (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ z : Site d,
              z ∈ cent d (4 * n) → z ∉ I →
              (componentIn Iᶜ z).Finite ∧
                ((componentIn Iᶜ z).ncard : ℝ) ≤
                  B * (Real.log ((n : ℝ) + 2)) ^ (2 : ℕ)) ∧
            RnChemClause d C I := by
  obtain ⟨qBox, B, hqBox0, hqBox1, hB, hbox⟩ :=
    arxiv_actual_bond_box_cutoff_ae d hd
  obtain ⟨qP, hqP0, hqP1, hPE'⟩ := hPE
  have hcrit : bondCritical d ≤ qP := rn_bondCritical_le hqP0 hPE'
  let m : ℝ := max (max qBox qP) 0
  have hm1 : m < 1 := by
    dsimp [m]
    exact max_lt (max_lt hqBox1 hqP1) zero_lt_one
  let ρ : ℝ := (1 + m) / 2
  have hm0 : 0 ≤ m := le_max_right _ _
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; linarith
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith
  have hmρ : m < ρ := by dsimp [ρ]; linarith
  have hqBoxρ : qBox ≤ ρ := by
    dsimp [m] at hmρ
    exact (le_trans (le_max_left _ _) (le_max_left _ _)).trans hmρ.le
  have hqPρ : qP ≤ ρ := by
    dsimp [m] at hmρ
    exact (le_trans (le_max_right _ _) (le_max_left _ _)).trans hmρ.le
  have hqP_m : qP ≤ m := by
    dsimp [m]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hcritρ : bondCritical d < ρ :=
    lt_of_le_of_lt (hcrit.trans hqP_m) hmρ
  obtain ⟨C, hC, hchem⟩ := rn_chem_ae hChem d hd hcritρ hρ0 hρ1.le
  obtain ⟨q, hq, hdom⟩ := rn_edge_dom hLSSB d ρ hρ0 hρ1
  refine ⟨q, hq, C, B, hC, hB, ?_⟩
  intro Ω _ P _ X hX hind hmarg
  haveI : IsProbabilityMeasure (bondPercolation d ρ) := rn_infinitePi_isProb hρ0 hρ1.le
  let ν : Measure (RnBond d → Bool) := bondPercolation d ρ
  have hboxAE := hbox ρ hqBoxρ hρ1.le
  let Joint : Set (RnBond d → Bool) := {ζ | ∃ i : Site d,
    let I : Set (Site d) := {y | (openBondGraph ζ).Reachable i y}
    I.Infinite ∧ RnHoleProp d I ∧
      (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ z : Site d,
        z ∈ cent d (4 * n) → z ∉ I →
          (componentIn Iᶜ z).Finite ∧
            ((componentIn Iᶜ z).ncard : ℝ) ≤ B * (Real.log ((n : ℝ) + 2)) ^ (2 : ℕ)) ∧
      RnChemProp d C ζ}
  have hJointAE : ∀ᵐ ζ ∂ν, ζ ∈ Joint := by
    filter_upwards [hboxAE, hchem] with ζ hboxζ hchemζ
    rcases hboxζ with ⟨i, hi, hholes, hcutoff⟩
    exact ⟨i, hi, hholes, hcutoff, hchemζ⟩
  let Bad : Set (RnBond d → Bool) := {ζ | ζ ∉ Joint}
  have hBad0 : ν Bad = 0 := by
    have h := ae_iff.mp hJointAE
    simpa [Bad] using h
  let Z : Set (RnBond d → Bool) := (toMeasurable ν Bad)ᶜ
  have hZm : MeasurableSet Z := (measurableSet_toMeasurable ν Bad).compl
  have hZν : ν Zᶜ = 0 := by
    rw [show Zᶜ = toMeasurable ν Bad by simp [Z], measure_toMeasurable]
    exact hBad0
  have hZgood : ∀ ζ ∈ Z, ζ ∈ Joint := by
    intro ζ hζ
    by_contra hnot
    exact hζ (subset_toMeasurable ν Bad hnot)
  set F : Ω → RnBond d → Bool := fun ω e =>
    X e.1 ω && X (e.1 + unit e.2) ω with hF
  have hFm : Measurable F := rn_edge_measurable X hX
  haveI : IsProbabilityMeasure (P.map F) := Measure.isProbabilityMeasure_map hFm.aemeasurable
  have hdomB : ∀ A : Set (RnBond d → Bool), MeasurableSet A → IsIncreasingSet A →
      ν A ≤ (P.map F) A := by
    intro A hA hinc
    rw [Measure.map_apply hFm hA]
    exact hdom P X hX hind hmarg A hA hinc
  obtain ⟨D, hDm, hDμ, hDle⟩ := rn_strassen_bool ν (P.map F) hdomB Z hZm hZν
  have hAE : ∀ᵐ ω ∂P, F ω ∈ D := by
    rw [ae_iff]
    have h := hDμ
    rw [Measure.map_apply hFm hDm.compl] at h
    exact h
  filter_upwards [hAE] with ω hω
  obtain ⟨ζ, hζZ, hζle⟩ := hDle (F ω) hω
  obtain ⟨i, hIinf, hIholes, hIbox, hIchem⟩ := hZgood ζ hζZ
  have hζ : ∀ b, ζ b = true → X b.1 ω = true ∧ X (b.1 + unit b.2) ω = true := by
    intro b hb
    have h := hζle b hb
    simp only [hF, Bool.and_eq_true] at h
    exact h
  obtain ⟨hgood, hconn, hchemI⟩ :=
    rn_actual_bond_chemical_clause (g := fun x => X x ω) hζ hIinf hIchem
  exact ⟨ζ, i, hIinf, hgood, hconn, hIholes, hIbox, hchemI⟩

/-- For strict `p`, sufficiently large good-cube scales contain an infinite connected good set
that is one actual open-bond cluster and retains that cluster's uniform finite-hole cutoff. -/
theorem arxiv_good_cube_bond_box_cutoff
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance)
    (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ k0 : ℕ, 1 ≤ k0 ∧ ∀ k : ℕ, k0 ≤ k → ∃ C B : ℝ, 1 ≤ C ∧ 1 ≤ B ∧
      ∀ᵐ η ∂(toyLaw d p), ∃ ζ : RnBond d → Bool, ∃ i : Site d,
        let I : Set (Site d) := {y | (openBondGraph ζ).Reachable i y}
        IsInfiniteConnectedGoodSet η k I ∧ RnHoleProp d I ∧
          (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ z : Site d,
            z ∈ cent d (4 * n) → z ∉ I →
              (componentIn Iᶜ z).Finite ∧
                ((componentIn Iᶜ z).ncard : ℝ) ≤
                  B * (Real.log ((n : ℝ) + 2)) ^ (2 : ℕ)) ∧
          RnChemClause d C I := by
  classical
  have hPE : ∃ qP : ℝ, 0 ≤ qP ∧ qP < 1 ∧
      ∀ q : ℝ, qP ≤ q → q ≤ 1 → bondTheta d q ≠ 0 := by
    refine ⟨255 / 256, by norm_num, by norm_num, ?_⟩
    intro q hq hq1
    exact pe_theta_ne_zero hd hq hq1
  obtain ⟨q, hq, C, B, hC, hB, hcore⟩ :=
    rn_good_field_bond_box_cutoff hLSSB hChem d hd hPE
  let q' : ℝ := max q 0
  have hq' : q' < 1 := max_lt hq zero_lt_one
  obtain ⟨k0, hk01, hk0⟩ := rn_goodCube_tail d hd p hp hp1 (1 - q') (by linarith)
  refine ⟨k0, hk01, fun k hk => ⟨C, B, hC, hB, ?_⟩⟩
  have hk1 : 1 ≤ k := le_trans hk01 hk
  haveI : IsProbabilityMeasure (toyLaw d p) := rn_toyLaw_prob d hp.le hp1.le
  have hmarg : ∀ x : Site d, ENNReal.ofReal q ≤
      toyLaw d p {η | decide (GoodAt η k x) = true} := by
    intro x
    rw [show {η : Site d → ℤ | decide (GoodAt η k x) = true} = {η | GoodAt η k x} by
      ext η; simp]
    rw [rn_goodAt_marginal hp.le hp1.le k x]
    have htail := hk0 k hk
    rw [show 1 - (1 - q') = q' by ring] at htail
    exact (ENNReal.ofReal_le_ofReal (le_max_left q 0)).trans htail
  have hfield : ∀ x : Site d, Measurable (fun η : Site d → ℤ => decide (GoodAt η k x)) := by
    intro x
    exact measurable_to_bool (by
      have hpre : (fun η : Site d → ℤ => decide (GoodAt η k x)) ⁻¹' {true} =
          {η | GoodAt η k x} := by
        ext η
        simp
      rw [hpre]
      exact rn_goodAt_measurable k x)
  have hae := hcore (toyLaw d p)
    (fun (x : Site d) (η : Site d → ℤ) => decide (GoodAt η k x)) hfield
    (rn_iIndep_good p hp hp1 k hk1) hmarg
  filter_upwards [hae] with η hη
  obtain ⟨ζ, i, hIinf, hXgood, hconn, hIholes, hIbox, hIchem⟩ := hη
  let I : Set (Site d) := {y | (openBondGraph ζ).Reachable i y}
  have hIgood : I ⊆ goodSites η k := by
    intro x hx
    have hx' : decide (GoodAt η k x) = true := hXgood x hx
    simpa [goodSites] using (of_decide_eq_true hx')
  have hCgood : IsInfiniteConnectedGoodSet η k I := ⟨hIinf, hIgood, hconn⟩
  exact ⟨ζ, i, hCgood, hIholes, hIbox, hIchem⟩

end Exploding
