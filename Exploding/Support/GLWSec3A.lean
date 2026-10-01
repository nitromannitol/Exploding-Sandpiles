/-
Proposition 5.1 of the paper (generalized last wave), the Section-3 assembly, part A:
the almost sure good event, the two-sided Lipschitz bound for the penultimate-cluster
arrival times from the origin, and the subadditive cocycle along a lattice vector.

Every declaration is prefixed `glws_`.  Nothing here uses the infinite-cluster machinery:
the inputs are the local bound of `glw2_LipschitzLocal`, the shift covariance of the wave
objects (`LWCProof`) and the approximate subadditivity of `GLWProofAux`.
-/
import Exploding.Support.GLWProof2
import Exploding.Support.LWCProof
import Exploding.Support.LWCProof2
import Exploding.Support.LWCProof3

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

/-- The body of the conclusion of `glw2_LipschitzLocal`, for fixed constants. -/
def glws_Loc (d : ℕ) (γ C : ℝ) (η : Site d → ℤ) : Prop :=
  (∀ y : Site d, ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n y) ∧
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ cent d n, ∃ a : ℕ,
      clusterArrival η (0 : Site d) x = (a : ℕ∞) ∧
      ∀ x' ∈ cent d n, ∃ c : ℕ, clusterArrival η x x' = (c : ℕ∞) ∧
        (c : ℝ) ≤ C * (mnorm (x - x') : ℝ) + Real.log n ^ γ

/-- The penultimate-cluster arrival time from the origin, read in `ℝ` (with `⊤ ↦ 0`). -/
noncomputable def glws_f (η : Site d → ℤ) (x : Site d) : ℝ :=
  ((clusterArrival η (0 : Site d) x).toNat : ℝ)

/-- The coordinates of a site are bounded by its Manhattan norm. -/
theorem glws_abs_le_mnorm (x : Site d) (i : Fin d) : |x i| ≤ mnorm x :=
  abs_coord_le_mnorm x i

/-- Every site lies in `cent d n` for `n` large. -/
theorem glws_mem_cent (x : Site d) {n : ℕ} (hn : (mnorm x).toNat ≤ n) : x ∈ cent d n := by
  intro i
  have h1 := glws_abs_le_mnorm x i
  have h2 : mnorm x ≤ (n : ℤ) := by omega
  exact le_trans h1 h2

/-- Finiteness of every penultimate-cluster arrival time on the local good event. -/
theorem glws_loc_finite {γ C : ℝ} {η : Site d → ℤ} (h : glws_Loc d γ C η) (a b : Site d) :
    clusterArrival η a b ≠ ⊤ := by
  obtain ⟨_, n0, hn0⟩ := h
  have hn : n0 ≤ max n0 (max (mnorm a).toNat (mnorm b).toNat) := le_max_left _ _
  have ha : a ∈ cent d (max n0 (max (mnorm a).toNat (mnorm b).toNat)) :=
    glws_mem_cent a (le_trans (le_max_left _ _) (le_max_right _ _))
  have hb : b ∈ cent d (max n0 (max (mnorm a).toNat (mnorm b).toNat)) :=
    glws_mem_cent b (le_trans (le_max_right _ _) (le_max_right _ _))
  obtain ⟨_, _, hloc⟩ := hn0 _ hn a ha
  obtain ⟨c, hc', _⟩ := hloc b hb
  rw [hc']
  exact ENat.coe_ne_top c

/-- **Two-sided Lipschitz bound.**  On the local good event, with the standing bounds
`0 ≤ η ≤ 2d - 1`, `f = T̃(0, ·)` is Lipschitz up to a polylogarithmic error on `cent d n`. -/
theorem glws_two_sided (hd : 2 ≤ d) {γ C : ℝ} {η : Site d → ℤ}
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (h : glws_Loc d γ C η) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x x' : Site d, x ∈ cent d n → x' ∈ cent d n →
      |glws_f η x - glws_f η x'| ≤ C * (mnorm (x - x') : ℝ) + Real.log n ^ γ := by
  have hlast := h.1
  obtain ⟨_, n0, hn0⟩ := h
  refine ⟨n0, fun n hn x x' hx hx' => ?_⟩
  -- the bound from `x` to `x'`, in both directions
  have key : ∀ u w : Site d, u ∈ cent d n → w ∈ cent d n →
      glws_f η w ≤ glws_f η u + C * (mnorm (u - w) : ℝ) + Real.log n ^ γ := by
    intro u w hu hw
    obtain ⟨a, ha, hloc⟩ := hn0 n hn u hu
    obtain ⟨c, hc, hcb⟩ := hloc w hw
    obtain ⟨a', ha', _⟩ := hn0 n hn w hw
    have htri := glw_approx_subadditivity d hd η hlow hhigh hlast (0 : Site d) u w
    rw [ha, ha', hc, ← Nat.cast_add] at htri
    have htri' : a' ≤ a + c := by exact_mod_cast htri
    have hcast : (a' : ℝ) ≤ (a : ℝ) + (c : ℝ) := by exact_mod_cast htri'
    have e1 : glws_f η w = (a' : ℝ) := by simp [glws_f, ha']
    have e2 : glws_f η u = (a : ℝ) := by simp [glws_f, ha]
    rw [e1, e2]
    linarith
  rw [abs_le]
  have h1 := key x x' hx hx'
  have h2 := key x' x hx' hx
  have hsym : mnorm (x' - x) = mnorm (x - x') := by
    unfold mnorm
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply]
    exact abs_sub_comm _ _
  rw [hsym] at h2
  constructor <;> linarith

/-! ### The good event -/

/-- The deterministic good event: in `Ω`, every site has a last wave and every
penultimate-cluster arrival time is finite. -/
def glws_G (d : ℕ) (ηmin : ℤ) : Set (Site d → ℤ) :=
  {η | InOmega d ηmin η ∧ (∀ y : Site d, ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n y) ∧
    ∀ a b : Site d, clusterArrival η a b ≠ ⊤}

theorem glws_G_measurable (d : ℕ) (ηmin : ℤ) : MeasurableSet (glws_G d ηmin) := by
  have h1 : MeasurableSet {η : Site d → ℤ | InOmega d ηmin η} := by
    have : {η : Site d → ℤ | InOmega d ηmin η} =
        ⋂ x : Site d, ({η | ηmin ≤ η x} ∩ {η | η x ≤ 2 * (d : ℤ) - 1}) := by
      ext η; simp [InOmega]
    rw [this]
    refine MeasurableSet.iInter fun x => ?_
    exact (measurableSet_le measurable_const (measurable_pi_apply x)).inter
      (measurableSet_le (measurable_pi_apply x) measurable_const)
  have h2 : MeasurableSet {η : Site d → ℤ | ∀ y : Site d, ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n y} := by
    have : {η : Site d → ℤ | ∀ y : Site d, ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n y} =
        ⋂ y : Site d, ⋃ n : ℕ, {η | 1 ≤ n ∧ ¬ WaveStabilizable η n y} := by
      ext η; simp
    rw [this]
    refine MeasurableSet.iInter fun y => MeasurableSet.iUnion fun n => ?_
    by_cases hn : 1 ≤ n
    · have : {η : Site d → ℤ | 1 ≤ n ∧ ¬ WaveStabilizable η n y} =
          {η | WaveStabilizable η n y}ᶜ := by
        ext η; simp [hn]
      rw [this]
      exact (lwc_waveStabilizable_measurableSet n y).compl
    · have : {η : Site d → ℤ | 1 ≤ n ∧ ¬ WaveStabilizable η n y} = ∅ := by
        ext η; simp [hn]
      rw [this]; exact MeasurableSet.empty
  have h3 : MeasurableSet {η : Site d → ℤ | ∀ a b : Site d, clusterArrival η a b ≠ ⊤} := by
    have : {η : Site d → ℤ | ∀ a b : Site d, clusterArrival η a b ≠ ⊤} =
        ⋂ a : Site d, ⋂ b : Site d, (fun η => clusterArrival η a b) ⁻¹' {⊤}ᶜ := by
      ext η; simp
    rw [this]
    exact MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
      (lwc_clusterArrival_measurable a b) (measurableSet_singleton _).compl
  exact h1.inter (h2.inter h3)

/-- The good event is invariant under every translation. -/
theorem glws_G_shift {ηmin : ℤ} {η : Site d → ℤ} (hη : η ∈ glws_G d ηmin) (v : Site d) :
    (fun z => η (v + z)) ∈ glws_G d ηmin := by
  obtain ⟨hΩ, hlast, hfin⟩ := hη
  refine ⟨fun x => hΩ (v + x), fun y => ?_, fun a b => ?_⟩
  · obtain ⟨n, hn1, hn⟩ := hlast (v + y)
    refine ⟨n, hn1, fun hcon => hn ?_⟩
    exact (lwc_waveStabilizable_shift η v n y).mp hcon
  · rw [lwc_cluster_shift]
    exact hfin _ _

/-- The iterate of the translation by `y` is the translation by `m • y`. -/
theorem glws_iterate_mem {ηmin : ℤ} {η : Site d → ℤ} (hη : η ∈ glws_G d ηmin) (y : Site d)
    (m : ℕ) : ((fun η : Site d → ℤ => fun z => η (y + z))^[m]) η ∈ glws_G d ηmin := by
  rw [glw_shift_ergodic_iterate]
  exact glws_G_shift hη _

/-- On the good event the local bound makes `glws_f` finite-valued, so that `toNat` reads no
junk: the `ℝ`-valued cluster arrival is subadditive along a base point. -/
theorem glws_f_subadd (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin) {η : Site d → ℤ}
    (hη : η ∈ glws_G d ηmin) (a b z : Site d) :
    ((clusterArrival η a z).toNat : ℝ) ≤
      ((clusterArrival η a b).toNat : ℝ) + ((clusterArrival η b z).toNat : ℝ) := by
  obtain ⟨hΩ, hlast, hfin⟩ := hη
  have hlow : ∀ x, 0 ≤ η x := fun x => le_trans hηmin (hΩ x).1
  have hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1 := fun x => (hΩ x).2
  have h := glw_approx_subadditivity d hd η hlow hhigh hlast a b z
  obtain ⟨p, hp⟩ := ENat.ne_top_iff_exists.mp (hfin a z)
  obtain ⟨q, hq⟩ := ENat.ne_top_iff_exists.mp (hfin a b)
  obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp (hfin b z)
  rw [← hp, ← hq, ← hr, ← Nat.cast_add] at h
  have h' : p ≤ q + r := by exact_mod_cast h
  rw [← hp, ← hq, ← hr]
  simp only [ENat.toNat_coe]
  exact_mod_cast h'

end Exploding
