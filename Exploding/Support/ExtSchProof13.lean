/-
The base scale of the Schonmann renormalization.

Together with the recursion `xsch8_Recursion` (`a (2n) ≤ 2^{2d} a n ^ 2`, proved
in `ExtSchProof12`) the remaining claim of the renormalization scheme is the
existence of one scale at which the failure probability drops below `2^{-2d}`:

`xsch8_Base d p := ∃ n0, 2^{2d} * a n0 < 1`.

This is *Schonmann's theorem at a single scale*: for the `d`-neighbour bootstrap
with threshold `d` and any `p > 0` the cube is internally spanned with
probability tending to `1` as its side grows, because the process percolates for
every positive density.  We isolate the exact finite-size input:

`xsch13_Percolates d p := a n → 0`, i.e. `P(Q_n internally spanned) → 1`.

This is the sharpest form in which the remaining probabilistic content can be
stated: it is the standard finite-volume form of Schonmann's theorem, it implies
the base immediately, and everything deterministic (the L-shape growth, the
corner seed, the recursion) has already been discharged.  We also record the
monotonicity of toppling in the occupied set, the complement identity relating
`xsch8_a` to the spanning probability, the unconditional one-dimensional
instance, and the observation that the base alone already produces the doubly
fast decay along the dyadic tower.
-/
import Exploding.Support.ExtSchProof12
import Exploding.Support.ExtSchProof7

namespace Exploding

open LatticeProb MeasureTheory Filter Topology

variable {d : ℕ}

/-- Toppling is monotone in the occupied set: enlarging the set of sites with
`2d` chips can only add topplings (the `nbr` rule does not read the background). -/
theorem xsch13_Top_mono_occ {J : Finset (Fin d)} {B : Set (Site d)} {η η' : Site d → ℤ}
    (h : ∀ x ∈ B, η x = 2 * (d : ℤ) → η' x = 2 * (d : ℤ)) :
    ∀ x, xsch_Top J B η x → xsch_Top J B η' x := by
  intro x hx
  induction hx with
  | occ hB h2 => exact xsch_Top.occ hB (h _ hB h2)
  | nbr S hB hSJ hcard _ ih => exact xsch_Top.nbr S hB hSJ hcard ih

/-- Spanning is monotone in the occupied set. -/
theorem xsch13_Sp_mono_occ {J : Finset (Fin d)} {R : Set (Site d)} {η η' : Site d → ℤ}
    (h : ∀ x ∈ R, η x = 2 * (d : ℤ) → η' x = 2 * (d : ℤ))
    (hsp : xsch_Sp J R η) : xsch_Sp J R η' :=
  fun x hx => xsch13_Top_mono_occ h x (hsp x hx)

/-- The spanning probability is the complement of the failure probability. -/
theorem xsch13_sp_compl {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)] (n : ℕ) :
    (xsch_mu d p).real {η | xsch_Sp (Finset.univ : Finset (Fin d)) (cube d n) η}
      = 1 - xsch8_a d p n := by
  haveI : IsProbabilityMeasure (xsch_mu d p) := inferInstance
  have hmeas2 : MeasurableSet {η : Site d → ℤ |
      ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (cube d n) η} :=
    ((xsch_det_Sp (Finset.univ : Finset (Fin d)) (cube d n)).measurableSet
      (xsch10_cube_finite n)).compl
  have hdisj : Disjoint {η | xsch_Sp (Finset.univ : Finset (Fin d)) (cube d n) η}
      {η | ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (cube d n) η} := by
    rw [Set.disjoint_left]
    exact fun η h1 h2 => h2 h1
  have hunion : {η | xsch_Sp (Finset.univ : Finset (Fin d)) (cube d n) η}
      ∪ {η | ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (cube d n) η} = Set.univ := by
    ext η
    by_cases h : xsch_Sp (Finset.univ : Finset (Fin d)) (cube d n) η <;> simp [h]
  have h1 : (xsch_mu d p).real {η | xsch_Sp (Finset.univ : Finset (Fin d)) (cube d n) η}
      + (xsch_mu d p).real {η | ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (cube d n) η} = 1 := by
    rw [← measureReal_union hdisj hmeas2, hunion, measureReal_def, measure_univ,
      ENNReal.toReal_one]
  rw [xsch8_a]
  linarith

/-- **The sharpest remaining claim.**  The failure probability at scale `n` tends
to zero: equivalently, `Q_n` is internally spanned with probability tending to
one.  This is the finite-volume form of Schonmann's theorem and the exact
probabilistic input the renormalization still needs. -/
def xsch13_Percolates (d : ℕ) (p : ℝ) : Prop :=
  Tendsto (xsch8_a d p) atTop (𝓝 0)

/-- The base scale follows from the finite-volume percolation statement. -/
theorem xsch13_base_of_Percolates {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)]
    (h : xsch13_Percolates d p) : xsch8_Base d p := by
  rw [xsch13_Percolates] at h
  have htarget : (0 : ℝ) < 1 / (2 : ℝ) ^ (2 * d) := by positivity
  have hev : ∀ᶠ n in atTop, xsch8_a d p n < 1 / (2 : ℝ) ^ (2 * d) :=
    h.eventually (eventually_lt_nhds htarget)
  rw [eventually_atTop] at hev
  obtain ⟨n0, hn0⟩ := hev
  rw [xsch8_Base]
  refine ⟨n0, ?_⟩
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (2 * d) := by positivity
  calc (2 : ℝ) ^ (2 * d) * xsch8_a d p n0
      < (2 : ℝ) ^ (2 * d) * (1 / (2 : ℝ) ^ (2 * d)) :=
        mul_lt_mul_of_pos_left (hn0 n0 le_rfl) hpos
    _ = 1 := by field_simp

/-- The full exponential percolation estimate is stronger than the base scale:
an exponentially small failure probability dips below `2^{-2d}` at a large
enough scale. -/
theorem xsch13_base_of_percolationBound {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)]
    (h : xsch3_PercolationBound d p) : xsch8_Base d p := by
  obtain ⟨c, C, _hc, hC, hbound⟩ := h
  have hlim : Tendsto (fun n : ℕ => c * Real.exp (-(C * (n : ℝ)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => Real.exp (-(C * (n : ℝ)))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop hC)
    simpa using h1.const_mul c
  have htarget : (0 : ℝ) < 1 / (2 : ℝ) ^ (2 * d) := by positivity
  have hev : ∀ᶠ n : ℕ in atTop, c * Real.exp (-(C * (n : ℝ))) < 1 / (2 : ℝ) ^ (2 * d) :=
    hlim.eventually (eventually_lt_nhds htarget)
  rw [eventually_atTop] at hev
  obtain ⟨n0, hn0⟩ := hev
  rw [xsch8_Base]
  refine ⟨n0, ?_⟩
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (2 * d) := by positivity
  calc (2 : ℝ) ^ (2 * d) * xsch8_a d p n0
      ≤ (2 : ℝ) ^ (2 * d) * (c * Real.exp (-(C * (n0 : ℝ)))) :=
        mul_le_mul_of_nonneg_left (hbound n0) hpos.le
    _ < (2 : ℝ) ^ (2 * d) * (1 / (2 : ℝ) ^ (2 * d)) :=
        mul_lt_mul_of_pos_left (hn0 n0 le_rfl) hpos
    _ = 1 := by field_simp

/-- The base scale follows from the coarse block-percolation estimate
`xsch7_BlockPercolation`, since the latter gives `xsch3_PercolationBound`. -/
theorem xsch13_base_of_blockPercolation {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (h : xsch7_BlockPercolation d p) : xsch8_Base d p := by
  haveI : Fact (0 ≤ p ∧ p ≤ 1) := ⟨⟨hp.le, hp1.le⟩⟩
  obtain ⟨c, C, hc, hC, hbound⟩ := h
  refine xsch13_base_of_percolationBound ⟨c, C, hc, hC, fun n => ?_⟩
  have hsub : {η : Site d → ℤ | ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (cube d n) η}
      ⊆ {η : Site d → ℤ | η ∉ xsch7_BlockCover d n} := by
    intro η hη hcov
    exact hη (xsch7_sp_of_blockCover hcov)
  exact le_trans (measureReal_mono hsub (measure_ne_top _ _)) (hbound n)

/-- **One dimension.**  In one dimension the base scale holds unconditionally,
since a single occupied site topples the whole interval and hence `a n = (1-p)^n`. -/
theorem xsch13_base_one {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)] (hp : 0 < p) :
    xsch8_Base 1 p :=
  xsch13_base_of_percolationBound (xsch5_percolation_one hp)

/-- The base scale alone produces the doubly fast decay along every dyadic tower
above `n0`, via the recursion. -/
theorem xsch13_dyadic_decay_of_base {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)]
    (hrec : xsch8_Recursion d p) (hbase : xsch8_Base d p) :
    ∃ n0 : ℕ, ∀ k : ℕ,
      xsch8_a d p (2 ^ k * n0)
        ≤ (1 / (2 : ℝ) ^ (2 * d)) * ((2 : ℝ) ^ (2 * d) * xsch8_a d p n0) ^ (2 ^ k) := by
  obtain ⟨n0, _hn0⟩ := hbase
  exact ⟨n0, xsch8_dyadic_bound (by positivity) (fun n => measureReal_nonneg) hrec⟩

end Exploding
