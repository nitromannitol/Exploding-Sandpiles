/-
The renormalization step of the chemical-distance estimate.

A block scheme at scale `N` and window radius `r` is a local predicate `good` on blocks with
cores satisfying `BlockLinks` for every bond configuration.  If every block is bad with
probability at most a threshold depending only on `d` and `r`, the chemical distance between
the origin and `y` exceeds a constant multiple of `|y|₁` only with probability exponentially
small in `|y|₁`.  The proof bounds the chemical distance by the number of sites of the blocks
near the halo of bad blocks around a shortest reference path of blocks (block surgery,
`open_reach_in_coarseEnlargement_of_closed`), and the size of that halo by the Peierls estimate
`predHalo_tail`.  Compare Antal and Pisztora, *On the chemical distance for supercritical
Bernoulli percolation*, Ann. Probab. 24 (1996), Section 4; the tail of the halo is obtained here
by a Peierls bound on the block events instead of by stochastic domination and a large-deviation
estimate for sums of cluster sizes.
-/
import Exploding.Support.APBlockSurgery
import Exploding.Support.APBlockPeierls

open LatticeProb MeasureTheory
open scoped ENNReal

namespace Exploding

variable {d : ℕ}

/-- A block scheme at scale `N` with windows of radius `r`: whether a block is good depends only
on the bonds inside its window, and the good blocks and their cores satisfy `BlockLinks` in
every configuration. -/
structure IsBlockScheme (N r : ℕ) (good : (Site d × Fin d → Bool) → Site d → Prop)
    (core : (Site d × Fin d → Bool) → Site d → Set (Site d)) : Prop where
  pos : 0 < N
  isLocal : IsLocalBlockPredicate N r good
  links : ∀ ω, BlockLinks N r ω (good ω) (core ω)

/-! ### Comparing a site with its block -/

theorem abs_coarseSite_le {N : ℕ} (hN : 0 < N) (y : Site d) (i : Fin d) :
    |coarseSite N y i| ≤ |y i| := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  obtain ⟨h1, h2⟩ := int_ediv_bounds hN' (y i)
  change |y i / (N : ℤ)| ≤ |y i|
  rcases le_or_gt 0 (y i) with hy | hy
  · have hq : 0 ≤ y i / (N : ℤ) := Int.ediv_nonneg hy hN'.le
    rw [abs_of_nonneg hq, abs_of_nonneg hy]
    nlinarith
  · have hq : y i / (N : ℤ) < 0 := Int.ediv_neg_of_neg_of_pos hy hN'
    rw [abs_of_neg hq, abs_of_neg hy]
    by_contra hcon
    have : y i / (N : ℤ) + 1 ≤ y i := by linarith
    nlinarith

theorem abs_le_coarseSite {N : ℕ} (hN : 0 < N) (y : Site d) (i : Fin d) :
    |y i| ≤ (N : ℤ) * |coarseSite N y i| + N := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  obtain ⟨h1, h2⟩ := int_ediv_bounds hN' (y i)
  change |y i| ≤ (N : ℤ) * |y i / (N : ℤ)| + N
  rcases le_or_gt 0 (y i) with hy | hy
  · have hq : 0 ≤ y i / (N : ℤ) := Int.ediv_nonneg hy hN'.le
    rw [abs_of_nonneg hq, abs_of_nonneg hy]
    linarith
  · have hq : y i / (N : ℤ) < 0 := Int.ediv_neg_of_neg_of_pos hy hN'
    rw [abs_of_neg hq, abs_of_neg hy]
    linarith

theorem mnorm_coarseSite_le {N : ℕ} (hN : 0 < N) (y : Site d) :
    mnorm (coarseSite N y) ≤ mnorm y :=
  Finset.sum_le_sum fun i _ => abs_coarseSite_le hN y i

theorem mnorm_le_coarseSite {N : ℕ} (hN : 0 < N) (y : Site d) :
    mnorm y ≤ (N : ℤ) * mnorm (coarseSite N y) + d * N := by
  calc
    mnorm y ≤ ∑ i, ((N : ℤ) * |coarseSite N y i| + N) :=
      Finset.sum_le_sum fun i _ => abs_le_coarseSite hN y i
    _ = (N : ℤ) * mnorm (coarseSite N y) + d * N := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rfl

theorem exists_far_coordinate {N r : ℕ} (hN : 0 < N) (hd : 1 ≤ d) {y : Site d}
    (hy : ((d * N * (2 * r + 2) : ℕ) : ℤ) ≤ mnorm y) :
    ∃ i, 2 * (r : ℤ) + 1 ≤ |coarseSite N y i| := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have hi : ∃ i, (N : ℤ) * (2 * r + 2) ≤ |y i| := by
    by_contra hcon
    push Not at hcon
    have hlt : mnorm y < ∑ _i : Fin d, (N : ℤ) * (2 * r + 2) := by
      have : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
      exact Finset.sum_lt_sum_of_nonempty this fun i _ => hcon i
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
    push_cast at hy
    nlinarith
  obtain ⟨i, hi⟩ := hi
  refine ⟨i, ?_⟩
  have h := abs_le_coarseSite hN y i
  have h2 : (N : ℤ) * (2 * r + 1) ≤ (N : ℤ) * |coarseSite N y i| := by linarith
  exact le_of_mul_le_mul_left h2 hN'

/-! ### The reduction -/

/-- **The renormalization step.**  For `d ≥ 2` and every window radius `r` there is a threshold
`ε₀ > 0` such that, at every density `q`, a block scheme whose blocks are bad with probability at
most `ε₀` gives the Antal–Pisztora chemical-distance bound at density `q`. -/
theorem chemicalDistance_of_blockScheme (d : ℕ) (hd : 2 ≤ d) (r : ℕ) :
    ∃ ε₀ : ℝ≥0∞, 0 < ε₀ ∧ ∀ {q : ℝ}, 0 ≤ q → q ≤ 1 →
      ∀ {N : ℕ} {good : (Site d × Fin d → Bool) → Site d → Prop}
        {core : (Site d × Fin d → Bool) → Site d → Set (Site d)},
      IsBlockScheme N r good core →
      (∀ b, bondPercolation d q {ω | ¬ good ω b} ≤ ε₀) →
      ∃ ρ c : ℝ, 1 ≤ ρ ∧ 0 < c ∧ ∃ R : ℕ, ∀ y : Site d, (R : ℤ) ≤ mnorm y →
        bondPercolation d q
            {ω | ∃ m : ℕ, (openBondGraph ω).edist 0 y = (m : ℕ∞) ∧
              ρ * (mnorm y : ℝ) < (m : ℝ)} ≤
          ENNReal.ofReal (Real.exp (-(c * (mnorm y : ℝ)))) := by
  classical
  obtain ⟨ε₀, hε₀, htail⟩ := predHalo_tail d (by omega) r
  refine ⟨ε₀, hε₀, fun {q} hq0 hq1 {N good core} hS hbad => ?_⟩
  have hN := hS.pos
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set A : ℕ := 1 + (2 * r + 1) ^ d with hA
  set B : ℕ := (2 * (r + 1) + 1) ^ d with hB
  have hApos : 1 ≤ A := by omega
  have hBpos : 1 ≤ B := Nat.one_le_pow _ _ (by omega)
  have hNd : 1 ≤ N ^ d := Nat.one_le_pow _ _ hN
  set ρn : ℕ := 2 * A * B * N ^ d with hρn
  have hρn1 : 1 ≤ ρn := by
    have : 1 ≤ A * B := Nat.mul_le_mul hApos hBpos
    have : 1 ≤ A * B * N ^ d := Nat.mul_le_mul this hNd
    rw [hρn]
    nlinarith
  refine ⟨ρn, Real.log 2 / (2 * N), by exact_mod_cast hρn1, by positivity,
    d * N * (2 * r + 2), fun y hy => ?_⟩
  set Y : Site d := coarseSite N y with hYdef
  obtain ⟨P, hP0, hPY, hPconn, hprob⟩ := htail hN hq0 hq1 hS.isLocal hbad 0 Y
  have hmY : mnorm (0 - Y) = mnorm Y := by
    simp only [zero_sub, mnorm, Pi.neg_apply, abs_neg]
  rw [hmY] at hprob
  have hYnn : 0 ≤ mnorm Y := Finset.sum_nonneg fun i _ => abs_nonneg _
  set t : ℕ := (mnorm Y).toNat + 1 with ht
  have htY : (t : ℤ) = mnorm Y + 1 := by
    rw [ht]
    push_cast
    rw [Int.toNat_of_nonneg hYnn]
  have hle1 : mnorm Y ≤ mnorm y := mnorm_coarseSite_le hN y
  have hle2 : mnorm y ≤ (N : ℤ) * mnorm Y + d * N := mnorm_le_coarseSite hN y
  have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hRpos : (1 : ℤ) ≤ ((d * N * (2 * r + 2) : ℕ) : ℤ) := by
    have : 1 ≤ d * N * (2 * r + 2) := by
      have h1 : 0 < d * N := Nat.mul_pos (by omega) hN
      nlinarith
    exact_mod_cast this
  have hfarY := exists_far_coordinate (r := r) hN (by omega) hy
  have hsub : {ω : Site d × Fin d → Bool | ∃ m : ℕ, (openBondGraph ω).edist 0 y = (m : ℕ∞) ∧
      (ρn : ℝ) * (mnorm y : ℝ) < (m : ℝ)} ⊆
      {ω | ((A * t : ℕ) : ℕ∞) ≤ (predHalo (good ω) P).encard} := by
    intro ω hω
    obtain ⟨m, hm, hlt⟩ := hω
    by_contra hsize
    have hsize' : (predHalo (good ω) P).encard < ((A * t : ℕ) : ℕ∞) := lt_of_not_ge hsize
    have hfin : (predHalo (good ω) P).Finite := by
      rw [← Set.encard_lt_top_iff]
      exact lt_of_lt_of_le hsize' le_top
    let F : Finset (Site d) := hfin.toFinset
    have hFcard : F.card < A * t := by
      have h : (F.card : ℕ∞) < ((A * t : ℕ) : ℕ∞) := by
        rw [← hfin.encard_eq_coe_toFinset_card]
        exact hsize'
      exact_mod_cast h
    have hreach : (openBondGraph ω).Reachable 0 y := by
      apply SimpleGraph.reachable_of_edist_ne_top
      rw [hm]
      exact ENat.natCast_ne_top m
    have hx : coarseSite N (0 : Site d) ∈ F := by
      rw [coarseSite_zero]
      exact hfin.mem_toFinset.mpr (subset_predHalo _ P hP0)
    have hF : xmh_SConn (F : Set (Site d)) := by
      simpa only [F, Set.Finite.coe_toFinset] using predHalo_star_connected (G := good ω) hPconn
    have hclosed : ∀ c ∈ F, ∀ z, ¬ good ω z → xmh_star c z → z ∈ F := by
      intro c hc z hz hcz
      exact hfin.mem_toFinset.mpr (mem_predHalo_of_star (hfin.mem_toFinset.mp hc) hz hcz)
    have hyF : coarseSite N y ∈ unitCubeEnlargement F :=
      subset_unit_cube_enlargement F (hfin.mem_toFinset.mpr (subset_predHalo _ P hPY))
    have hfar : ∀ b, (0 : Site d) ∉ coarseWindow N r b ∨ y ∉ coarseWindow N r b := by
      intro b
      by_contra hcon
      push Not at hcon
      obtain ⟨h0, hyb⟩ := hcon
      obtain ⟨i, hi⟩ := hfarY
      have h1 := h0 i
      have h2 := hyb i
      rw [coarseSite_zero] at h1
      simp only [Pi.zero_apply, zero_sub, abs_neg] at h1
      rw [← hYdef] at h2
      have h3 : |Y i| ≤ |Y i - b i| + |b i| := by
        calc |Y i| = |(Y i - b i) + b i| := by ring_nf
          _ ≤ |Y i - b i| + |b i| := abs_add_le _ _
      linarith
    have hconf := open_reach_in_coarseEnlargement_of_closed (by omega) hN (hS.links ω) hx hF
      hclosed hyF hfar hreach
    have hdist := open_bond_edist_lt_of_reach_coarseRegion hN hconf
    rw [hm] at hdist
    have hmnat : m < (coarseEnlargement (r + 1) F).card * N ^ d := by exact_mod_cast hdist
    have hcard := card_coarseEnlargement_le (r + 1) F
    have hm2 : m < A * t * B * N ^ d := by
      calc m < (coarseEnlargement (r + 1) F).card * N ^ d := hmnat
        _ ≤ (F.card * B) * N ^ d := Nat.mul_le_mul_right _ hcard
        _ ≤ (A * t * B) * N ^ d := by
          apply Nat.mul_le_mul_right
          exact Nat.mul_le_mul_right _ hFcard.le
    have ht2 : (t : ℤ) ≤ 2 * mnorm y := by linarith
    have hm3 : (m : ℤ) < (ρn : ℤ) * mnorm y := by
      have h1 : ((A * t * B * N ^ d : ℕ) : ℤ) ≤ (ρn : ℤ) * mnorm y := by
        rw [hρn]
        push_cast
        have hABN : (0 : ℤ) ≤ (A : ℤ) * B * N ^ d := by positivity
        nlinarith
      have h2 : (m : ℤ) < ((A * t * B * N ^ d : ℕ) : ℤ) := by exact_mod_cast hm2
      linarith
    have hm4 : (m : ℝ) < (ρn : ℝ) * (mnorm y : ℝ) := by exact_mod_cast hm3
    linarith
  refine (measure_mono hsub).trans (hprob.trans ?_)
  · -- `2^{-t} ≤ exp (-(log 2 / (2N)) |y|₁)`
    have hyt : (mnorm y : ℝ) ≤ 2 * N * t := by
      have h1 : mnorm y ≤ 2 * (N : ℤ) * t := by
        rw [htY]
        have hdN : (d : ℤ) * N ≤ (N : ℤ) * mnorm Y + 2 * N := by
          have : (d : ℤ) * N * (2 * r + 2) ≤ mnorm y := by exact_mod_cast hy
          nlinarith
        nlinarith
      exact_mod_cast h1
    have hhalf : (1 / 2 : ℝ≥0∞) ^ t = ENNReal.ofReal ((1 / 2 : ℝ) ^ t) := by
      rw [ENNReal.ofReal_pow (by norm_num)]
      congr 1
      rw [one_div, one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
    rw [hhalf]
    apply ENNReal.ofReal_le_ofReal
    have hexp : (1 / 2 : ℝ) ^ t = Real.exp (-(Real.log 2 * t)) := by
      rw [show -(Real.log 2 * (t : ℝ)) = (t : ℝ) * (-Real.log 2) by ring, Real.exp_nat_mul,
        Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div]
    rw [hexp]
    apply Real.exp_le_exp.mpr
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hkey : Real.log 2 / (2 * N) * (mnorm y : ℝ) ≤ Real.log 2 * t := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith

end Exploding
