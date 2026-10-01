/-
Proposition 5.1 of the paper (generalized last wave): from a lit tile of the infinite cluster, the
penultimate-cluster arrival time of a site.

The data of the cluster are bundled in `glws_Cl`; its fields are the standing facts used by
Lemmas 3.5 and 3.6 in the generalized setting.
-/
import Exploding.Support.GLWSec3Y

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

/-- The data of the cluster of strongly box-crossing tiles at a background: the standing bounds,
the infinite connected set of strongly box-crossing tiles, the hole estimate, the chemical-distance
upper bound and path-filling. -/
structure glws_Cl (d : ℕ) (η : Site d → ℤ) (k : Fin d → ℕ) (Cinf : Set (Site d)) (γp Cch : ℝ) :
    Prop where
  hd : 2 ≤ d
  hlow : ∀ x, 0 ≤ η x
  hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1
  hk : ∀ i, 0 < k i
  hinf : Cinf.Infinite
  hgood : ∀ j ∈ Cinf, StronglyBoxCrossed η k j
  hconn : ∀ x ∈ Cinf, ∀ y ∈ Cinf, y ∈ componentIn Cinf x
  hole : ∃ n0h : ℕ, ∀ n : ℕ, n0h ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ Cinf →
    (componentIn Cinfᶜ x).Finite ∧ ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2)
  hchem : ∃ n0c : ℕ, ∀ n : ℕ, n0c ≤ n → ∀ x ∈ Cinf, ∀ y ∈ Cinf, mnorm x ≤ (n : ℤ) →
    Real.log n ^ (2 : ℕ) ≤ (mnorm (x - y) : ℝ) →
    ∃ m : ℕ, chemDist Cinf x y = (m : ℕ∞) ∧ (m : ℝ) ≤ Cch * (mnorm (x - y) : ℝ)
  hγp : 0 < γp
  hCch : 0 ≤ Cch
  hpf : glws_PF d γp η

/-- **The penultimate-cluster arrival time from a lit tile.**  If a tile `j` of the cluster is lit
by the last wave from the origin at time `τ`, then for `n` large and `x ∈ [-n,n]^d` the arrival time
`T̃(0,x)` is finite and at most `τ + A |j - ν(x)| + B Z^d + 1`, where `Z` is the macroscopic radius at
any scale `n'' ≥ n` large enough to contain `j` and `ν(x)`. -/
theorem glws_cluster_lit {η : Site d → ℤ} {k : Fin d → ℕ} {Cinf : Set (Site d)} {γp Cch : ℝ}
    (S : glws_Cl d η k Cinf γp Cch) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ n'' : ℕ, n ≤ n'' → n0 ≤ n'' → ∀ x ∈ (cent d n : Set (Site d)),
      ∀ j ∈ Cinf, mnorm j ≤ (n'' : ℤ) → mnorm (glws_nu k x) ≤ (n'' : ℤ) → ∀ τ : ℕ,
      glws_Fired η (waveThreshold η (0 : Site d)) k 0 τ j →
      ∃ a : ℕ, clusterArrival η (0 : Site d) x = (a : ℕ∞) ∧
        a ≤ τ + glws_LA Cch k * (mnorm (j - glws_nu k x)).toNat +
          glws_LB Cch k * (glws_Zn γp n'') ^ d + 1 := by
  classical
  obtain ⟨n0h, hole⟩ := S.hole
  obtain ⟨n0c, hchem⟩ := S.hchem
  have hγp : 0 < γp := S.hγp
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast S.hd
    linarith
  obtain ⟨n0s, hsmall⟩ := glws_penultimate_small S.hd η S.hlow S.hhigh k S.hk Cinf S.hinf
    S.hgood S.hconn n0h hole γp S.hγp S.hpf
  obtain ⟨n0l, hln⟩ := glws_light_near S.hd η S.hlow S.hhigh k S.hk Cinf S.hgood n0h hole Cch
    S.hCch n0c hchem γp S.hγp S.hpf
  have hlast := glws_finite_exploding S.hd η S.hlow S.hhigh k S.hk Cinf S.hinf S.hgood S.hconn
    (0 : Site d)
  have hne : {n : ℕ | 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d)}.Nonempty := hlast
  have hN1 : 1 ≤ waveThreshold η (0 : Site d) := (Nat.sInf_mem hne).1
  refine ⟨max (max n0s n0l) 3, fun n hn n'' hnn'' hn'' x hx j hj hjn hνn τ hfired => ?_⟩
  have hn0s : n0s ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hn0l : n0l ≤ n'' := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn''
  set N : ℕ := waveThreshold η (0 : Site d) with hN
  set Z : ℕ := glws_Zn γp n'' with hZ
  set T : ℕ := τ + glws_LA Cch k * (mnorm (j - glws_nu k x)).toNat + glws_LB Cch k * Z ^ d
    with hT
  -- the penultimate cluster lies in the box of radius `Z` about `x`
  have hL1 : (1 : ℝ) ≤ Real.log n := by
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    have : Real.exp 1 ≤ 3 := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log n := Real.log_le_log (Real.exp_pos 1) (le_trans this h3)
  have hZge : Real.log n ^ (γp + 4) ≤ (Z : ℝ) := by
    have h1 : Real.log (n : ℝ) ≤ Real.log (n'' : ℝ) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast hnn''
    have h2 : Real.log n ^ (γp + 4) ≤ Real.log n ^ (γp + 5) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have h3 : Real.log n ^ (γp + 5) ≤ Real.log (n'' : ℝ) ^ (γp + 5) :=
      Real.rpow_le_rpow (by linarith) h1 (by linarith)
    have h4 : Real.log (n'' : ℝ) ^ (γp + 5) ≤ (Z : ℝ) := Nat.le_ceil _
    linarith
  have hball : ∀ w ∈ penultimateCluster η x, ∀ m, (k m : ℤ) * (glws_nu k x m - (Z : ℤ)) + 1 ≤ w m ∧
      w m ≤ (k m : ℤ) * (glws_nu k x m + (Z : ℤ) + 1) := by
    intro w hw m
    have h1 := hsmall n hn0s x hx w hw m
    have h2 : |w m - x m| ≤ (Z : ℤ) := by
      have : ((|w m - x m| : ℤ) : ℝ) ≤ (Z : ℝ) := le_trans h1 hZge
      exact_mod_cast this
    rw [abs_le] at h2
    have hxt := glws_mem_tile_nu k S.hk x m
    have hk1 : (1 : ℤ) ≤ (k m : ℤ) := by exact_mod_cast S.hk m
    have hZ0 : (0 : ℤ) ≤ (Z : ℤ) := Int.natCast_nonneg Z
    have e1 : (k m : ℤ) * (glws_nu k x m - Z) = (k m : ℤ) * glws_nu k x m - (k m : ℤ) * Z := by ring
    have e2 : (k m : ℤ) * (glws_nu k x m + Z + 1) =
        (k m : ℤ) * glws_nu k x m + (k m : ℤ) * Z + k m := by ring
    have e3 : (Z : ℤ) ≤ (k m : ℤ) * Z := by nlinarith
    rw [e1, e2]
    constructor <;> linarith [hxt.1, hxt.2, h2.1, h2.2]
  -- the lighting
  have hlit : ∀ w ∈ penultimateCluster η x, 0 < wave η N 0 T w := fun w hw =>
    hln n'' hn0l N hN1 0 τ j hj hjn hfired (glws_nu k x) hνn w (hball w hw)
  have hlit' : ∀ w ∈ penultimateCluster η x, 0 < lastWave η (0 : Site d) (T + 1) w := by
    intro w hw
    exact pclose_pos_mono hd0 η S.hlow N 0 (Nat.le_succ T) (hlit w hw)
  have hle := clusterArrival_le η (0 : Site d) x (T + 1) (by omega) hlit'
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (ENat.coe_ne_top _) hle)
  refine ⟨a, ha.symm, ?_⟩
  have : (a : ℕ∞) ≤ ((T + 1 : ℕ) : ℕ∞) := by rw [ha]; exact hle
  exact_mod_cast this

end Exploding
