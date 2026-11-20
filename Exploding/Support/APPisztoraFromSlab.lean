/-
The box estimate of the coarse graining from uniform slab connectivity.

Under uniform two-point connectivity in the slabs of cubes, Percolation-Rigidity proves that an
integer cube of side `s` has a crossing component to which every open path inside the cube that
leaves every `ℓ¹`-ball of radius `r / 10` connects, outside an event of probability at most a
polynomial in `s` times `exp (-c (r / (10 d w) - 1))`
(`Rigidity.Percolation.IntegerCube.measureReal_no_crossing_connecting_radius_le_scaled_exp`, after
Pisztora, *Surface order large deviations for Ising, Potts and percolation models*, Probab.
Theory Related Fields 104 (1996), Section 3).  Applied to the cube `[0, N)^d` it gives
`CubeCrossing N`, and applied to the box `[-N, 2N)^d` with `r = 5N - 6` it gives
`BoxUniqueness N`, since an open path between two sites at sup-distance at least `N - 1` leaves
every `ℓ¹`-ball of radius `(N - 1) / 2`.  Hence uniform slab connectivity above the critical
probability, the slab form of the theorem of Grimmett and Marstrand, gives
`PisztoraBoxEstimate d` (`pisztoraBoxEstimate_of_slabConnectivity`), and with the planar case
the full Antal–Pisztora statement (`antalPisztoraChemicalDistance_of_slabConnectivity`).
-/
import Exploding.Rigidity.Percolation.SlabRadiusCrossing
import Exploding.Support.APSlabConnectivity
import Exploding.Support.APBoxChemical

open LatticeProb MeasureTheory Filter Topology
open scoped ENNReal

namespace Exploding

variable {d : ℕ}

/-! ### Integer cubes -/

/-- The slab of an integer cube of Percolation-Rigidity is the slab `cubeSlab` of its corner and
size. -/
theorem integerCube_slab_eq_cubeSlab (Q : Rigidity.Percolation.IntegerCube d) (a : Fin d)
    (w k : ℕ) : Q.slab a w k = cubeSlab Q.corner Q.size a w k := by
  ext x
  simp only [Rigidity.Percolation.IntegerCube.slab, cubeSlab, Set.mem_ofPred_eq,
    Rigidity.Percolation.IntegerCube.mem_vertices]

theorem integerCube_card_vertices (Q : Rigidity.Percolation.IntegerCube d) :
    Q.vertices.card = Q.size ^ d := by
  rw [Rigidity.Percolation.IntegerCube.vertices, Fintype.card_piFinset]
  simp only [Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem integerCube_card_lowerFace_le (Q : Rigidity.Percolation.IntegerCube d) (j : Fin d) :
    (Q.lowerFace j).card ≤ Q.size ^ d :=
  (Finset.card_filter_le _ _).trans (integerCube_card_vertices Q).le

/-! ### The crossing bound in the form used here -/

theorem exists_slab_parameters (d : ℕ) {p ρ : ℝ} (hp : 0 < p) (hρ : 0 < ρ) :
    ∃ ρ' c : ℝ, 0 ≤ ρ' ∧ ρ' ≤ 1 ∧ ρ' ≤ ρ ∧ 0 < c ∧ c ≤ ρ' ∧ c ≤ p * ρ' ^ (2 * d) ∧
      c ≤ p * (p * ρ') := by
  set ρ' := min ρ 1 with hρ'
  have hρ'0 : 0 < ρ' := lt_min hρ one_pos
  refine ⟨ρ', min ρ' (min (p * ρ' ^ (2 * d)) (p * (p * ρ'))), hρ'0.le, min_le_right _ _,
    min_le_left _ _, lt_min hρ'0 (lt_min (by positivity) (by positivity)), min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩

/-- Under uniform slab connectivity, the probability that an integer cube has no crossing
component connecting all open paths that leave every `ℓ¹`-ball of radius `r / 10` is at most a
polynomial in the side times an exponential in `r`. -/
theorem latticeBond_no_crossing_le (hd : 2 ≤ d) {p : unitInterval} (hp : 0 < (p : ℝ))
    {width : ℕ} (hwidth : 0 < width) {ρ : ℝ} (hρ : 0 < ρ)
    (hslab : ∀ (c : Site d) (n : ℕ) (a : Fin d) (k : ℕ), (k + 1) * width ≤ n →
      ∀ x ∈ cubeSlab c n a width k, ∀ y ∈ cubeSlab c n a width k,
        ρ ≤ (LatticeBond.latticeBondLaw d p).real
          {ω | (Rigidity.External.openIn ω (cubeSlab c n a width k)).Reachable x y}) :
    ∃ c : ℝ, 0 < c ∧ ∀ (Q : Rigidity.Percolation.IntegerCube d) (radius : ℕ),
      10 * d * width ≤ radius → radius < 10 * d * Q.size →
      (LatticeBond.latticeBondLaw d p).real
          {ω | ¬ Rigidity.Percolation.HasCrossingComponentConnectingPaths ω ↑Q.vertices
            (fun t => ↑(Q.lowerFace t)) (fun t => ↑(Q.upperFace t))
            (fun n γ => ∀ z : Site d, ∃ a : Fin (n + 1),
              (radius : ℤ) < 10 * ∑ k, |γ a k - z k|)} ≤
        (1 + ((Q.size : ℝ) ^ d) + ((d * Q.size : ℕ) : ℝ) * ((Q.size : ℝ) ^ d) ^ 2) *
          Real.exp (-(c * ((radius / (10 * d * width) - 1 : ℕ) : ℝ))) := by
  obtain ⟨ρ', c, hρ'0, hρ'1, hρ'ρ, hc, hcρ, hcroot, hctwo⟩ := exists_slab_parameters d hp hρ
  refine ⟨c, hc, fun Q radius hradius hfit => ?_⟩
  have hd0 : 0 < d := by omega
  have hij : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by simp
  have h := Rigidity.Percolation.IntegerCube.measureReal_no_crossing_connecting_radius_le_scaled_exp
    hd0 Q ⟨1, by omega⟩ ⟨0, by omega⟩ hij width radius hwidth hradius hfit p ρ' c hρ'0 hρ'1 hc
    hcρ hcroot hctwo (fun t k hk x hx y hy => by
      rw [integerCube_slab_eq_cubeSlab] at hx hy ⊢
      exact hρ'ρ.trans (hslab Q.corner Q.size t k hk x hx y hy))
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  have h1 : (((Q.lowerFace ⟨1, by omega⟩).card : ℕ) : ℝ) ≤ (Q.size : ℝ) ^ d := by
    exact_mod_cast integerCube_card_lowerFace_le Q _
  have h2 : ((Q.vertices.card : ℕ) : ℝ) = (Q.size : ℝ) ^ d := by
    exact_mod_cast integerCube_card_vertices Q
  rw [h2]
  linarith

/-! ### Open paths as sequences of sites -/

theorem exists_fin_path_of_xap_reach {ω : Site d × Fin d → Bool} {S : Set (Site d)}
    {x y : Site d} (h : xap_Reach ω S x y) :
    ∃ (n : ℕ) (γ : Fin (n + 1) → Site d), γ 0 = x ∧ γ (Fin.last n) = y ∧ (∀ a, γ a ∈ S) ∧
      ∀ i : Fin n, (openBondGraph ω).Adj (γ i.castSucc) (γ i.succ) := by
  obtain ⟨p, hp⟩ := open_walk_of_reach_in_set h
  refine ⟨p.length, fun a => p.getVert a, by simp, by simp, fun a => hp _
    (p.getVert_mem_support a), fun i => ?_⟩
  have := p.adj_getVert_succ i.isLt
  simpa using this

theorem openIn_toLatticeConfig_adj {ω : Site d × Fin d → Bool} {S : Set (Site d)} {u v : Site d}
    (hu : u ∈ S) (hv : v ∈ S) (h : (openBondGraph ω).Adj u v) :
    (Rigidity.External.openIn (toLatticeConfig ω) S).Adj u v := by
  refine ⟨?_, hu, hv⟩
  rw [openGraph_toLatticeConfig]
  exact h

/-! ### The two events -/

/-- The integer cube `[0, N)^d`. -/
def lowerIntegerCube (d N : ℕ) : Rigidity.Percolation.IntegerCube d := ⟨0, N⟩

/-- The integer cube `[-N, 2N)^d`. -/
def tripleIntegerCube (d N : ℕ) : Rigidity.Percolation.IntegerCube d := ⟨fun _ => -(N : ℤ), 3 * N⟩

theorem lowerIntegerCube_vertices (N : ℕ) :
    (↑(lowerIntegerCube d N).vertices : Set (Site d)) = lowerCube d N := by
  ext x
  simp only [Finset.mem_coe, Rigidity.Percolation.IntegerCube.mem_vertices, lowerIntegerCube,
    lowerCube, Set.mem_ofPred_eq, Pi.zero_apply, zero_add]

theorem tripleIntegerCube_vertices (N : ℕ) :
    (↑(tripleIntegerCube d N).vertices : Set (Site d)) = tripleBox d N := by
  ext x
  simp only [Finset.mem_coe, Rigidity.Percolation.IntegerCube.mem_vertices, tripleIntegerCube,
    tripleBox, Set.mem_ofPred_eq]
  push_cast
  exact forall_congr' fun i => and_congr_right fun _ => by constructor <;> intro h <;> linarith

/-- A crossing component of `[0, N)^d` gives an open path between two sites at sup-distance
`N - 1`. -/
theorem cubeCrossing_of_crossingComponent (hd : 1 ≤ d) {N : ℕ} {ω : Site d × Fin d → Bool}
    {large : (n : ℕ) → (Fin (n + 1) → Site d) → Prop}
    (h : Rigidity.Percolation.HasCrossingComponentConnectingPaths (toLatticeConfig ω)
      ↑(lowerIntegerCube d N).vertices (fun t => ↑((lowerIntegerCube d N).lowerFace t))
      (fun t => ↑((lowerIntegerCube d N).upperFace t)) large) : CubeCrossing N ω := by
  obtain ⟨root, ⟨_, hroot⟩, _⟩ := h
  obtain ⟨⟨yl, hyl, hylf, hryl⟩, ⟨yu, hyu, hyuf, hryu⟩⟩ := hroot ⟨0, by omega⟩
  have hreach := (hryl.symm.trans hryu)
  have hxap := openIn_toLatticeConfig_reachable hyl hreach
  rw [lowerIntegerCube_vertices] at hxap
  refine ⟨yl, yu, hxap, ⟨0, by omega⟩, ?_⟩
  rw [Finset.mem_coe, Rigidity.Percolation.IntegerCube.mem_lowerFace] at hylf
  rw [Finset.mem_coe, Rigidity.Percolation.IntegerCube.mem_upperFace] at hyuf
  have h1 := hylf.2
  have h2 := hyuf.2
  simp only [lowerIntegerCube, Pi.zero_apply, zero_add] at h1 h2
  have heq : (N : ℤ) - 1 = yu ⟨0, by omega⟩ - yl ⟨0, by omega⟩ := by omega
  rw [heq, abs_sub_comm]
  exact le_abs_self _

/-- A large pair inside `[-N, 2N)^d` is the start of an open path that leaves every `ℓ¹`-ball
of radius `(N - 1) / 2`. -/
theorem exists_large_fin_path {N radius : ℕ} (hr : 2 * (radius : ℤ) < 10 * ((N : ℤ) - 1))
    {ω : Site d × Fin d → Bool} {x y : Site d} (hxy : LargePair N ω (tripleBox d N) x y) :
    ∃ (n : ℕ) (γ : Fin (n + 1) → Site d), γ 0 = x ∧ γ 0 ∈ tripleBox d N ∧
      (∀ i : Fin n, (Rigidity.External.openIn (toLatticeConfig ω) (tripleBox d N)).Adj
        (γ i.castSucc) (γ i.succ)) ∧
      ∀ z : Site d, ∃ a : Fin (n + 1), (radius : ℤ) < 10 * ∑ k, |γ a k - z k| := by
  obtain ⟨hreach, i, hi⟩ := hxy
  obtain ⟨n, γ, h0, hlast, hmem, hadj⟩ := exists_fin_path_of_xap_reach hreach
  refine ⟨n, γ, h0, hmem 0, fun j => openIn_toLatticeConfig_adj (hmem _) (hmem _) (hadj j),
    fun z => ?_⟩
  by_contra hcon
  push Not at hcon
  have ha := hcon 0
  have hb := hcon (Fin.last n)
  rw [h0] at ha
  rw [hlast] at hb
  have hxi : |x i - z i| ≤ ∑ k, |x k - z k| :=
    Finset.single_le_sum (f := fun k => |x k - z k|) (fun k _ => abs_nonneg _) (Finset.mem_univ i)
  have hyi : |y i - z i| ≤ ∑ k, |y k - z k| :=
    Finset.single_le_sum (f := fun k => |y k - z k|) (fun k _ => abs_nonneg _) (Finset.mem_univ i)
  have htri : |x i - y i| ≤ |x i - z i| + |y i - z i| := by
    calc |x i - y i| = |(x i - z i) - (y i - z i)| := by ring_nf
      _ ≤ |x i - z i| + |y i - z i| := abs_sub _ _
  linarith

/-- A crossing component of `[-N, 2N)^d` connecting the paths that leave every `ℓ¹`-ball of
radius `radius / 10`, with `radius < 5 (N - 1)`, joins any two large pairs inside the box. -/
theorem boxUniqueness_of_crossingComponent {N radius : ℕ}
    (hr : 2 * (radius : ℤ) < 10 * ((N : ℤ) - 1)) {ω : Site d × Fin d → Bool}
    (h : Rigidity.Percolation.HasCrossingComponentConnectingPaths (toLatticeConfig ω)
      ↑(tripleIntegerCube d N).vertices (fun t => ↑((tripleIntegerCube d N).lowerFace t))
      (fun t => ↑((tripleIntegerCube d N).upperFace t))
      (fun n γ => ∀ z : Site d, ∃ a : Fin (n + 1), (radius : ℤ) < 10 * ∑ k, |γ a k - z k|)) :
    BoxUniqueness N ω := by
  obtain ⟨root, _, hconn⟩ := h
  rw [tripleIntegerCube_vertices] at hconn
  have hroot : ∀ x y, LargePair N ω (tripleBox d N) x y →
      (Rigidity.External.openIn (toLatticeConfig ω) (tripleBox d N)).Reachable root x := by
    intro x y hxy
    obtain ⟨n, γ, h0, hmem, hadj, hlarge⟩ := exists_large_fin_path hr hxy
    obtain ⟨z, _, hγz, hrz⟩ := hconn n γ hlarge hmem hadj
    rw [h0] at hγz
    exact hrz.trans hγz.symm
  intro x y z w hxy hzw
  have hx := hroot x y hxy
  have hz := hroot z w hzw
  exact openIn_toLatticeConfig_reachable hxy.1.1 (hx.symm.trans hz)

/-! ### Decay of the bound -/

theorem eventually_pow_mul_exp_neg_le {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, ((N : ℝ) ^ k * Real.exp (-(a * N))) ≤ δ := by
  have hlim : Tendsto (fun N : ℕ => (a * N) ^ k * Real.exp (-(a * N))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
      ((tendsto_natCast_atTop_atTop).const_mul_atTop ha)
  have hδ' : 0 < δ * a ^ k := by positivity
  filter_upwards [hlim.eventually (gt_mem_nhds hδ')] with N hN
  have hak : 0 < a ^ k := by positivity
  rw [mul_pow] at hN
  have : a ^ k * ((N : ℝ) ^ k * Real.exp (-(a * N))) < a ^ k * δ := by
    rw [← mul_assoc]
    linarith
  exact (lt_of_mul_lt_mul_left this hak.le).le

/-- **The box estimate from uniform slab connectivity.**  If uniform slab connectivity holds in
the Lattice-Probability model above its critical probability, then `PisztoraBoxEstimate d`
holds. -/
theorem pisztoraBoxEstimate_of_slabConnectivity [NeZero d] (hd : 2 ≤ d)
    (h : ∀ p : unitInterval, LatticeBond.criticalProbability d < (p : ℝ) →
      LatticeBond.UniformCubeSlabConnectivity d p) :
    PisztoraBoxEstimate d := by
  intro q hq hq1 ε hε
  have hq0 : 0 ≤ q := (xap14_bondCritical_nonneg d).trans hq.le
  have hqpos : 0 < q := lt_of_le_of_lt (xap14_bondCritical_nonneg d) hq
  obtain ⟨width, hwidth, ρ, hρ, hslab⟩ :=
    h ⟨q, hq0, hq1⟩ (criticalProbability_lt_of_bondCritical_lt hq hq1)
  obtain ⟨c, hc, hbound⟩ := latticeBond_no_crossing_le (p := ⟨q, hq0, hq1⟩) hd hqpos hwidth hρ
    hslab
  have : IsProbabilityMeasure (bondPercolation d q) := rn_infinitePi_isProb hq0 hq1
  -- the real bound `g N`
  set M : ℝ := ((10 * d * width : ℕ) : ℝ) with hM
  have hMpos : 0 < M := by rw [hM]; exact_mod_cast (show 0 < 10 * d * width by positivity)
  set a : ℝ := c * 5 / M with ha
  have hapos : 0 < a := by positivity
  set A : ℝ := (2 + d) * 3 ^ (2 * d + 1) * Real.exp (c * (6 / M + 2)) with hA
  have hApos : 0 < A := by positivity
  -- choose a tolerance in `ℝ`
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ ε := by
    by_cases htop : ε = ⊤
    · exact ⟨1, one_pos, htop ▸ le_top⟩
    · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' htop, (ENNReal.ofReal_toReal htop).le⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((eventually_ge_atTop (2 * d * width + 2)).and
    (eventually_pow_mul_exp_neg_le hapos (show 0 < δ / A by positivity) (2 * d + 1)))
  obtain ⟨hNbig, hNsmall⟩ := hN N le_rfl
  set r : ℕ := 5 * N - 6 with hr
  have hN2 : 2 ≤ N := by
    have : 1 ≤ d * width := Nat.mul_pos (by omega) hwidth
    nlinarith
  have hr10 : 10 * d * width ≤ r := by
    have e1 : 10 * d * width = 10 * (d * width) := by ring
    have e2 : 2 * d * width = 2 * (d * width) := by ring
    rw [e1]
    rw [e2] at hNbig
    omega
  have hr5 : r < 5 * N := by omega
  have hrfit1 : r < 10 * d * (lowerIntegerCube d N).size := by
    simp only [lowerIntegerCube]
    have : 1 ≤ d := by omega
    nlinarith
  have hrfit3 : r < 10 * d * (tripleIntegerCube d N).size := by
    simp only [tripleIntegerCube]
    have : 1 ≤ d := by omega
    nlinarith
  have hr2 : 2 * (r : ℤ) < 10 * ((N : ℤ) - 1) := by
    rw [hr]
    push_cast [show 6 ≤ 5 * N by omega]
    omega
  -- the common real bound
  have hexp : Real.exp (-(c * ((r / (10 * d * width) - 1 : ℕ) : ℝ))) ≤
      Real.exp (c * (6 / M + 2)) * Real.exp (-(a * N)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hfloor : ((r : ℝ) / M) - 2 ≤ ((r / (10 * d * width) - 1 : ℕ) : ℝ) := by
      have h1 : ((r : ℝ) / M) - 1 ≤ ((r / (10 * d * width) : ℕ) : ℝ) := by
        have hdiv := Nat.lt_div_mul_add (a := r) (show 0 < 10 * d * width by positivity)
        have h' : (r : ℝ) < ((r / (10 * d * width) : ℕ) : ℝ) * M + M := by
          rw [hM]
          exact_mod_cast hdiv
        rw [div_sub_one hMpos.ne', div_le_iff₀ hMpos]
        linarith
      have h2 : ((r / (10 * d * width) : ℕ) : ℝ) - 1 ≤ ((r / (10 * d * width) - 1 : ℕ) : ℝ) := by
        rcases Nat.eq_zero_or_pos (r / (10 * d * width)) with h0 | hpos
        · rw [h0]; simp
        · rw [Nat.cast_sub hpos]; simp
      linarith
    have hrN : (r : ℝ) = 5 * N - 6 := by
      rw [hr]
      push_cast [show 6 ≤ 5 * N by omega]
      ring
    rw [hrN] at hfloor
    have : -(c * ((r / (10 * d * width) - 1 : ℕ) : ℝ)) ≤ -(c * ((5 * (N : ℝ) - 6) / M - 2)) := by
      have := mul_le_mul_of_nonneg_left hfloor hc.le
      linarith
    refine this.trans (le_of_eq ?_)
    rw [ha]
    field_simp
    ring
  have hpoly : ∀ s : ℕ, 1 ≤ s → s ≤ 3 * N →
      (1 + ((s : ℝ) ^ d) + ((d * s : ℕ) : ℝ) * ((s : ℝ) ^ d) ^ 2) ≤
        (2 + d) * 3 ^ (2 * d + 1) * (N : ℝ) ^ (2 * d + 1) := by
    intro s hs1 hs3
    have hs : (1 : ℝ) ≤ s := by exact_mod_cast hs1
    have hs3' : (s : ℝ) ≤ 3 * N := by exact_mod_cast hs3
    have hpow1 : (s : ℝ) ^ d ≤ (s : ℝ) ^ (2 * d + 1) := pow_le_pow_right₀ hs (by omega)
    have hpow0 : (1 : ℝ) ≤ (s : ℝ) ^ (2 * d + 1) := one_le_pow₀ hs
    have hpow2 : ((d * s : ℕ) : ℝ) * ((s : ℝ) ^ d) ^ 2 = d * (s : ℝ) ^ (2 * d + 1) := by
      push_cast
      ring
    have hsN : (s : ℝ) ^ (2 * d + 1) ≤ 3 ^ (2 * d + 1) * (N : ℝ) ^ (2 * d + 1) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hs3' _
    rw [hpow2]
    have hd' : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith
  have hfinal : ∀ s : ℕ, 1 ≤ s → s ≤ 3 * N →
      (1 + ((s : ℝ) ^ d) + ((d * s : ℕ) : ℝ) * ((s : ℝ) ^ d) ^ 2) *
          Real.exp (-(c * ((r / (10 * d * width) - 1 : ℕ) : ℝ))) ≤ δ := by
    intro s hs1 hs3
    calc
      _ ≤ ((2 + d) * 3 ^ (2 * d + 1) * (N : ℝ) ^ (2 * d + 1)) *
            (Real.exp (c * (6 / M + 2)) * Real.exp (-(a * N))) :=
        mul_le_mul (hpoly s hs1 hs3) hexp (Real.exp_pos _).le (by positivity)
      _ = A * ((N : ℝ) ^ (2 * d + 1) * Real.exp (-(a * N))) := by rw [hA]; ring
      _ ≤ A * (δ / A) := mul_le_mul_of_nonneg_left hNsmall hApos.le
      _ = δ := by field_simp
  refine ⟨N, by omega, ?_, ?_⟩
  · -- the crossing of `[0, N)^d`
    have hsub : {ω : Site d × Fin d → Bool | ¬ CubeCrossing N ω} ⊆
        toLatticeConfig ⁻¹' {ω | ¬ Rigidity.Percolation.HasCrossingComponentConnectingPaths ω
          ↑(lowerIntegerCube d N).vertices (fun t => ↑((lowerIntegerCube d N).lowerFace t))
          (fun t => ↑((lowerIntegerCube d N).upperFace t))
          (fun n γ => ∀ z : Site d, ∃ a : Fin (n + 1), (r : ℤ) < 10 * ∑ k, |γ a k - z k|)} :=
      fun ω hω hcross => hω (cubeCrossing_of_crossingComponent (by omega) hcross)
    calc
      bondPercolation d q {ω | ¬ CubeCrossing N ω}
          ≤ (bondPercolation d q).map toLatticeConfig {ω |
              ¬ Rigidity.Percolation.HasCrossingComponentConnectingPaths ω
              ↑(lowerIntegerCube d N).vertices (fun t => ↑((lowerIntegerCube d N).lowerFace t))
              (fun t => ↑((lowerIntegerCube d N).upperFace t))
              (fun n γ => ∀ z : Site d, ∃ a : Fin (n + 1),
                (r : ℤ) < 10 * ∑ k, |γ a k - z k|)} :=
        (measure_mono hsub).trans
          (Measure.le_map_apply measurable_toLatticeConfig.aemeasurable _)
      _ ≤ ENNReal.ofReal δ := by
        rw [map_toLatticeConfig_bondPercolation hq0 hq1, ← ofReal_measureReal]
        exact ENNReal.ofReal_le_ofReal ((hbound _ r hr10 hrfit1).trans
          (hfinal N (by omega) (by omega)))
      _ ≤ ε := hδε
  · -- uniqueness in `[-N, 2N)^d`
    have hsub : {ω : Site d × Fin d → Bool | ¬ BoxUniqueness N ω} ⊆
        toLatticeConfig ⁻¹' {ω | ¬ Rigidity.Percolation.HasCrossingComponentConnectingPaths ω
          ↑(tripleIntegerCube d N).vertices (fun t => ↑((tripleIntegerCube d N).lowerFace t))
          (fun t => ↑((tripleIntegerCube d N).upperFace t))
          (fun n γ => ∀ z : Site d, ∃ a : Fin (n + 1), (r : ℤ) < 10 * ∑ k, |γ a k - z k|)} :=
      fun ω hω hcross => hω (boxUniqueness_of_crossingComponent hr2 hcross)
    calc
      bondPercolation d q {ω | ¬ BoxUniqueness N ω}
          ≤ (bondPercolation d q).map toLatticeConfig {ω |
              ¬ Rigidity.Percolation.HasCrossingComponentConnectingPaths ω
              ↑(tripleIntegerCube d N).vertices (fun t => ↑((tripleIntegerCube d N).lowerFace t))
              (fun t => ↑((tripleIntegerCube d N).upperFace t))
              (fun n γ => ∀ z : Site d, ∃ a : Fin (n + 1),
                (r : ℤ) < 10 * ∑ k, |γ a k - z k|)} :=
        (measure_mono hsub).trans
          (Measure.le_map_apply measurable_toLatticeConfig.aemeasurable _)
      _ ≤ ENNReal.ofReal δ := by
        rw [map_toLatticeConfig_bondPercolation hq0 hq1, ← ofReal_measureReal]
        exact ENNReal.ofReal_le_ofReal ((hbound _ r hr10 hrfit3).trans
          (hfinal (3 * N) (by omega) le_rfl))
      _ ≤ ε := hδε

/-- **The Antal–Pisztora theorem from uniform slab connectivity.**  The planar case is
`antalPisztora_dim_two`; in dimensions `d ≥ 3`, uniform slab connectivity in the
Lattice-Probability model above its critical probability gives the box estimate and hence the
bound. -/
theorem antalPisztoraChemicalDistance_of_slabConnectivity
    (h : ∀ d : ℕ, ∀ [NeZero d], 3 ≤ d → ∀ p : unitInterval,
      LatticeBond.criticalProbability d < (p : ℝ) → LatticeBond.UniformCubeSlabConnectivity d p) :
    Exploding.External.AntalPisztoraChemicalDistance :=
  antalPisztoraChemicalDistance_of_boxEstimate fun d hd => by
    have : NeZero d := ⟨by omega⟩
    exact pisztoraBoxEstimate_of_slabConnectivity (by omega) (h d hd)

end Exploding
