/-
Follow-up to `Exploding/Support/LWCProof2.lean` (packet LWC-3).

Conjunct (2) of the last-wave reduction: the lattice-direction convergence, the continuity and
homogeneity of the limit shape `N` and the Lipschitz bound on `f` upgrade to locally uniform
convergence on every compact.  The rational-direction half is `lwc2_rational_convergence`; this
file covers the compact set by finitely many balls on which `N` barely moves, replaces each
centre by its rational direction and uses the Lipschitz bound for the rest.  All declarations are
`lwc3_`-prefixed.
-/
import Exploding.Support.LWCProof2
import Exploding.Support.Gen

open Exploding LatticeProb MeasureTheory Filter

variable {d : ℕ}

/-- One coordinate is bounded by the sup norm. -/
theorem lwc3_abs_coord_sub_le_dist (y z : Fin d → ℝ) (i : Fin d) :
    |y i - z i| ≤ dist y z := by
  rw [dist_eq_norm]
  calc |y i - z i| = ‖(y - z) i‖ := by simp [Real.norm_eq_abs]
    _ ≤ ‖y - z‖ := norm_le_pi_norm _ i

/-- `cent d ·` is monotone in the side length. -/
theorem lwc3_cent_mono {N N' : ℕ} (h : N ≤ N') : cent d N ⊆ cent d N' := by
  intro x hx i
  exact le_trans (hx i) (by exact_mod_cast h)

/-- A lattice difference of nearest sites is `O(1)` plus `O(n)` times a coordinatewise bound. -/
theorem lwc3_nearest_sub_mnorm_le (y z : Fin d → ℝ) (n : ℕ) (δ : ℝ)
    (hyz : ∀ i, |y i - z i| ≤ δ) :
    (mnorm (nearestSite ((n : ℝ) • y) - nearestSite ((n : ℝ) • z)) : ℝ) ≤
      (d : ℝ) * (2 + (n : ℝ) * δ) := by
  have hcoord : ∀ i, |(nearestSite ((n : ℝ) • y) i : ℝ) - (nearestSite ((n : ℝ) • z) i : ℝ)|
      ≤ 2 + (n : ℝ) * δ := by
    intro i
    have h2 := lwc2_nearestSite_sub_le ((n : ℝ) • y) i
    have h3 := lwc2_nearestSite_sub_le ((n : ℝ) • z) i
    have h5 : |(((n : ℝ) • y) i) - (((n : ℝ) • z) i)| ≤ (n : ℝ) * δ := by
      rw [show ((n : ℝ) • y) i = (n : ℝ) * y i by rfl,
        show ((n : ℝ) • z) i = (n : ℝ) * z i by rfl, ← mul_sub, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg n)]
      exact mul_le_mul_of_nonneg_left (hyz i) (Nat.cast_nonneg n)
    have htri : |(nearestSite ((n : ℝ) • y) i : ℝ) - (nearestSite ((n : ℝ) • z) i : ℝ)|
        ≤ |(nearestSite ((n : ℝ) • y) i : ℝ) - (((n : ℝ) • y) i)|
          + |(((n : ℝ) • y) i) - (nearestSite ((n : ℝ) • z) i : ℝ)| := abs_sub_le _ _ _
    have htri2 : |(((n : ℝ) • y) i) - (nearestSite ((n : ℝ) • z) i : ℝ)|
        ≤ |(((n : ℝ) • y) i) - (((n : ℝ) • z) i)|
          + |(((n : ℝ) • z) i) - (nearestSite ((n : ℝ) • z) i : ℝ)| := abs_sub_le _ _ _
    have h3' : |(((n : ℝ) • z) i) - (nearestSite ((n : ℝ) • z) i : ℝ)| ≤ 1 := by
      rw [abs_sub_comm]; exact h3
    linarith [htri, htri2, h2, h3', h5]
  calc (mnorm (nearestSite ((n : ℝ) • y) - nearestSite ((n : ℝ) • z)) : ℝ)
      = ∑ i : Fin d,
          |(nearestSite ((n : ℝ) • y) i : ℝ) - (nearestSite ((n : ℝ) • z) i : ℝ)| := by
        simp only [mnorm, Pi.sub_apply, Int.cast_sum, Int.cast_abs, Int.cast_sub]
    _ ≤ ∑ _i : Fin d, (2 + (n : ℝ) * δ) := Finset.sum_le_sum fun i _ => hcoord i
    _ = (d : ℝ) * (2 + (n : ℝ) * δ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Conjunct (2).**  Lattice-direction convergence with a continuous homogeneous limit shape
plus the Lipschitz bound upgrade to locally uniform convergence on compacts. -/
theorem lwc3_lattice_upgrade (f : Site d → ℝ) (N : (Fin d → ℝ) → ℝ) (hd : 0 < d)
    (hNcont : Continuous N)
    (hNhom : ∀ (c : ℝ), 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y)
    (hlat : ∀ v : Site d, Tendsto (fun n : ℕ => f ((n : ℤ) • v) / (n : ℝ)) atTop
        (nhds (N (lwc2_toReal v))))
    (C γ : ℝ) (hC : 0 < C) (hγ : 0 < γ)
    (hlip : ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x x' : Site d,
        x ∈ cent d n → x' ∈ cent d n →
        |f x - f x'| ≤ C * (mnorm (x - x') : ℝ) + Real.log n ^ γ)
    (K : Set (Fin d → ℝ)) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
      |f (nearestSite ((n : ℝ) • y)) / (n : ℝ) - N y| ≤ ε := by
  have hlipkeep := hlip
  obtain ⟨n0, hn0⟩ := hlip
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set δ1 : ℝ := ε / (16 * C * (d : ℝ)) with hδ1
  have hδ1pos : 0 < δ1 := by rw [hδ1]; positivity
  -- continuity radii
  have hrad : ∀ c : K, ∃ δ : ℝ, 0 < δ ∧
      ∀ z : Fin d → ℝ, dist z (c : Fin d → ℝ) < δ → |N z - N (c : Fin d → ℝ)| < ε / 8 := by
    intro c
    have hc := hNcont.continuousAt (x := (c : Fin d → ℝ))
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨δ, hδpos, hδ⟩ := hc (ε / 8) (by linarith)
    exact ⟨δ, hδpos, fun z hz => by
      have := hδ hz
      rwa [Real.dist_eq] at this⟩
  choose δc hδcpos hδc using hrad
  have hcover : K ⊆ ⋃ c : K, Metric.ball (c : Fin d → ℝ) (min (δc c) δ1) := by
    intro y hy
    refine Set.mem_iUnion.mpr ⟨⟨y, hy⟩, ?_⟩
    rw [Metric.mem_ball, dist_self]
    exact lt_min (hδcpos ⟨y, hy⟩) hδ1pos
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun c : K => Metric.ball (c : Fin d → ℝ) (min (δc c) δ1))
    (fun _ => Metric.isOpen_ball) hcover
  -- rational directions attached to the centres
  let q : K → ℕ := fun c => ⌈(1 : ℝ) / min (δc c) δ1⌉₊ + 1
  let r : K → Fin d → ℝ := fun c => ((q c : ℝ)⁻¹) • lwc2_toReal
    (nearestSite ((q c : ℝ) • (c : Fin d → ℝ)))
  have hqpos : ∀ c : K, 1 ≤ q c := fun c => Nat.le_add_left 1 _
  have hrdist : ∀ c : K, dist (r c) (c : Fin d → ℝ) < min (δc c) δ1 := by
    intro c
    have hminpos : 0 < min (δc c) δ1 := lt_min (hδcpos c) hδ1pos
    have hqposR : (0 : ℝ) < (q c : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hqpos c))
    have hq_gt : (1 : ℝ) / min (δc c) δ1 < (q c : ℝ) := by
      have h1 : (1 : ℝ) / min (δc c) δ1 ≤ (⌈(1 : ℝ) / min (δc c) δ1⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (⌈(1 : ℝ) / min (δc c) δ1⌉₊ : ℝ) < (q c : ℝ) := by
        simp only [q]; push_cast; linarith
      linarith
    have hq_gt' : (min (δc c) δ1)⁻¹ < (q c : ℝ) := by rw [one_div] at hq_gt; exact hq_gt
    have hinv_lt : (q c : ℝ)⁻¹ < min (δc c) δ1 :=
      (inv_lt_comm₀ hminpos hqposR).mp hq_gt'
    rw [dist_eq_norm, pi_norm_lt_iff hminpos]
    intro i
    have hcoord : (r c - (c : Fin d → ℝ)) i =
        (q c : ℝ)⁻¹ * ((nearestSite ((q c : ℝ) • (c : Fin d → ℝ)) i : ℝ) -
          (q c : ℝ) * ((c : Fin d → ℝ) i)) := by
      simp only [r, Pi.sub_apply, Pi.smul_apply, lwc2_toReal, smul_eq_mul]
      have hqne : (q c : ℝ) ≠ 0 := by positivity
      field_simp [hqne]
    rw [hcoord, Real.norm_eq_abs, abs_mul]
    have hnear := lwc2_nearestSite_sub_le ((q c : ℝ) • (c : Fin d → ℝ)) i
    have h1 : |(nearestSite ((q c : ℝ) • (c : Fin d → ℝ)) i : ℝ) -
        (q c : ℝ) * ((c : Fin d → ℝ) i)| ≤ 1 := by
      rw [show ((q c : ℝ) • (c : Fin d → ℝ)) i = (q c : ℝ) * ((c : Fin d → ℝ) i) by rfl]
        at hnear
      exact hnear
    rw [abs_of_pos (inv_pos.mpr hqposR)]
    calc (q c : ℝ)⁻¹ * |(nearestSite ((q c : ℝ) • (c : Fin d → ℝ)) i : ℝ) -
          (q c : ℝ) * ((c : Fin d → ℝ) i)|
        ≤ (q c : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ < min (δc c) δ1 := by rw [mul_one]; exact hinv_lt
  -- the finite family of directions converges
  have hconv_t : ∀ᶠ n : ℕ in atTop, ∀ c ∈ t,
      |f (nearestSite ((n : ℝ) • r c)) / (n : ℝ) - N (r c)| < ε / 4 := by
    rw [Finset.eventually_all]
    intro c _
    have hconv_c := lwc2_rational_convergence f N hNhom hlat C γ hC hγ hlipkeep
      (nearestSite ((q c : ℝ) • (c : Fin d → ℝ))) (q c) (hqpos c)
    have hε4 : 0 < ε / 4 := by linarith
    have := hconv_c.eventually (Metric.ball_mem_nhds _ hε4)
    filter_upwards [this] with n hn
    simpa only [Real.dist_eq, r] using hn
  -- the Lipschitz budget
  obtain ⟨MK, hMK⟩ := lwc_transfer_1 d K hK
  have hbig : ∀ᶠ n : ℕ in atTop, (2 * C * (d : ℝ)) / (n : ℝ) < ε / 8 := by
    have h0 : Tendsto (fun n : ℕ => (2 * C * (d : ℝ)) / (n : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    exact h0.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < ε / 8))
  -- the logarithmic error
  have hlogev : ∀ᶠ n : ℕ in atTop,
      Real.log ((n * (MK + 3) + 1 : ℕ) : ℝ) ^ γ / (n : ℝ) < ε / 4 := by
    have h0 : Tendsto (fun n : ℕ => Real.log (((MK + 4 : ℕ) : ℝ) * (n : ℝ)) ^ γ / (n : ℝ))
        atTop (nhds 0) := lwc_transfer_4 γ (MK + 4) (by omega)
    have hlt : ∀ᶠ n : ℕ in atTop,
        Real.log (((MK + 4 : ℕ) : ℝ) * (n : ℝ)) ^ γ / (n : ℝ) < ε / 4 :=
      h0.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < ε / 4))
    filter_upwards [hlt, eventually_ge_atTop 1] with n hn hn1
    refine lt_of_le_of_lt ?_ hn
    apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ n)
    have harg : ((n * (MK + 3) + 1 : ℕ) : ℝ) ≤ (((MK + 4 : ℕ) : ℝ)) * (n : ℝ) := by
      have hnat : n * (MK + 3) + 1 ≤ (MK + 4) * n := by
        calc n * (MK + 3) + 1 ≤ n * (MK + 3) + n := Nat.add_le_add_left hn1 _
          _ = n * (MK + 4) := by ring
          _ = (MK + 4) * n := by ring
      exact_mod_cast hnat
    have hlog : Real.log ((n * (MK + 3) + 1 : ℕ) : ℝ) ≤
        Real.log ((((MK + 4 : ℕ) : ℝ)) * (n : ℝ)) :=
      Real.log_le_log (by positivity) harg
    exact Real.rpow_le_rpow (Real.log_natCast_nonneg (n * (MK + 3) + 1)) hlog hγ.le
  filter_upwards [hconv_t, hbig, hlogev, eventually_ge_atTop (max n0 1),
    eventually_ge_atTop 1] with n hconvn hbn hlogn hnn hn1
  intro y hy
  have hmemK' := ht hy
  simp only [Set.mem_iUnion, exists_prop] at hmemK'
  obtain ⟨c, hc, hyc⟩ := hmemK'
  have hyc' : dist y (c : Fin d → ℝ) < min (δc c) δ1 := by rwa [Metric.mem_ball] at hyc
  have hrc' : dist (r c) (c : Fin d → ℝ) < min (δc c) δ1 := hrdist c
  have hNn : n0 ≤ n * (MK + 3) + 1 := by
    have h1 : n0 ≤ n := le_trans (le_max_left _ _) hnn
    exact le_trans h1 (le_trans (Nat.le_mul_of_pos_right n (by omega)) (Nat.le_succ _))
  -- memberships in the common box
  have hmemK : nearestSite ((n : ℝ) • y) ∈ cent d (n * (MK + 3) + 1) :=
    lwc3_cent_mono (by nlinarith) (Gen.nearestSite_smul_mem_cent y MK n (hMK y hy))
  have hri : ∀ i, |(r c) i| ≤ (((MK + 2 : ℕ)) : ℝ) := by
    intro i
    have hci : ∀ j, |(c : Fin d → ℝ) j| ≤ (MK : ℝ) := hMK c c.2
    have hz := Gen.nearestSite_smul_mem_cent (c : Fin d → ℝ) MK (q c) hci
    have hzi : |(nearestSite ((q c : ℝ) • (c : Fin d → ℝ)) i : ℤ)| ≤
        ((q c) * (MK + 1) + 1 : ℕ) := hz i
    have hcoord : (r c) i =
        (q c : ℝ)⁻¹ * (nearestSite ((q c : ℝ) • (c : Fin d → ℝ)) i : ℝ) := by
      simp only [r, Pi.smul_apply, lwc2_toReal, smul_eq_mul]
    rw [hcoord, abs_mul, abs_of_pos (inv_pos.mpr (by exact_mod_cast
      (lt_of_lt_of_le Nat.zero_lt_one (hqpos c))))]
    have hziR : |(nearestSite ((q c : ℝ) • (c : Fin d → ℝ)) i : ℝ)| ≤
        ((q c) * (MK + 1) + 1 : ℕ) := by exact_mod_cast hzi
    have hqinv1 : (q c : ℝ)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity)]; exact_mod_cast hqpos c
    calc (q c : ℝ)⁻¹ * |(nearestSite ((q c : ℝ) • (c : Fin d → ℝ)) i : ℝ)|
        ≤ (q c : ℝ)⁻¹ * (((q c) * (MK + 1) + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hziR (by positivity)
      _ = ((q c : ℝ)⁻¹ * (q c : ℝ)) * ((MK : ℝ) + 1) + (q c : ℝ)⁻¹ := by push_cast; ring
      _ = 1 * ((MK : ℝ) + 1) + (q c : ℝ)⁻¹ := by
          rw [inv_mul_cancel₀ (by positivity : (q c : ℝ) ≠ 0)]
      _ ≤ 1 * ((MK : ℝ) + 1) + 1 := by linarith
      _ = (((MK + 2 : ℕ)) : ℝ) := by push_cast; ring
  have hmemR : nearestSite ((n : ℝ) • (r c)) ∈ cent d (n * (MK + 3) + 1) :=
    Gen.nearestSite_smul_mem_cent (r c) (MK + 2) n hri
  -- the three estimates
  have hN1 : |N y - N (c : Fin d → ℝ)| < ε / 8 :=
    hδc c y (lt_of_lt_of_le hyc' (min_le_left _ _))
  have hN2 : |N (r c) - N (c : Fin d → ℝ)| < ε / 8 :=
    hδc c (r c) (lt_of_lt_of_le hrc' (min_le_left _ _))
  have hN3 : |N y - N (r c)| < ε / 4 := by
    have h := abs_sub_le (N y) (N (c : Fin d → ℝ)) (N (r c))
    have h' : |N (r c) - N (c : Fin d → ℝ)| = |N (c : Fin d → ℝ) - N (r c)| :=
      abs_sub_comm _ _
    linarith
  have hmid := hconvn c hc
  -- the Lipschitz comparison
  have hcoord : ∀ i, |y i - (r c) i| ≤ 2 * δ1 := by
    intro i
    have h1 := lwc3_abs_coord_sub_le_dist y (c : Fin d → ℝ) i
    have h2 := lwc3_abs_coord_sub_le_dist (r c) (c : Fin d → ℝ) i
    have h3 : |(c : Fin d → ℝ) i - (r c) i| = |(r c) i - (c : Fin d → ℝ) i| := abs_sub_comm _ _
    have h4 : |y i - (r c) i| ≤ |y i - (c : Fin d → ℝ) i| + |(c : Fin d → ℝ) i - (r c) i| :=
      abs_sub_le _ _ _
    rw [h3] at h4
    have h5 : min (δc c) δ1 ≤ δ1 := min_le_right _ _
    linarith [le_of_lt hyc', le_of_lt hrc']
  have hmnorm := lwc3_nearest_sub_mnorm_le y (r c) n (2 * δ1) hcoord
  have hlip_n := hn0 (n * (MK + 3) + 1) hNn (nearestSite ((n : ℝ) • y))
    (nearestSite ((n : ℝ) • (r c))) hmemK hmemR
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hL : |f (nearestSite ((n : ℝ) • y)) / (n : ℝ) -
      f (nearestSite ((n : ℝ) • (r c))) / (n : ℝ)| < ε / 2 := by
    rw [div_sub_div_same, abs_div, abs_of_pos hnpos]
    have hmm : C * (mnorm (nearestSite ((n : ℝ) • y) -
        nearestSite ((n : ℝ) • (r c))) : ℝ)
        ≤ C * ((d : ℝ) * (2 + (n : ℝ) * (2 * δ1))) :=
      mul_le_mul_of_nonneg_left hmnorm hC.le
    have hbup : |f (nearestSite ((n : ℝ) • y)) - f (nearestSite ((n : ℝ) • (r c)))|
        ≤ C * ((d : ℝ) * (2 + (n : ℝ) * (2 * δ1))) +
          Real.log ((n * (MK + 3) + 1 : ℕ) : ℝ) ^ γ := by linarith
    have hCd : C * ((d : ℝ) * (2 * δ1)) = ε / 8 := by
      rw [hδ1]; field_simp; ring
    have hdiv : (C * ((d : ℝ) * (2 + (n : ℝ) * (2 * δ1))) +
        Real.log ((n * (MK + 3) + 1 : ℕ) : ℝ) ^ γ) / (n : ℝ)
        = (2 * C * (d : ℝ)) / (n : ℝ) + C * ((d : ℝ) * (2 * δ1)) +
          Real.log ((n * (MK + 3) + 1 : ℕ) : ℝ) ^ γ / (n : ℝ) := by
      field_simp
    have hstep : |f (nearestSite ((n : ℝ) • y)) - f (nearestSite ((n : ℝ) • (r c)))|
        / (n : ℝ) ≤ (2 * C * (d : ℝ)) / (n : ℝ) + C * ((d : ℝ) * (2 * δ1)) +
          Real.log ((n * (MK + 3) + 1 : ℕ) : ℝ) ^ γ / (n : ℝ) := by
      rw [← hdiv]; exact div_le_div_of_nonneg_right hbup hnpos.le
    rw [hCd] at hstep
    linarith
  have htri : |f (nearestSite ((n : ℝ) • y)) / (n : ℝ) - N y|
      ≤ |f (nearestSite ((n : ℝ) • y)) / (n : ℝ) -
            f (nearestSite ((n : ℝ) • (r c))) / (n : ℝ)|
          + |f (nearestSite ((n : ℝ) • (r c))) / (n : ℝ) - N (r c)|
          + |N y - N (r c)| := by
    have h := abs_sub_le (f (nearestSite ((n : ℝ) • y)) / (n : ℝ))
      (f (nearestSite ((n : ℝ) • (r c))) / (n : ℝ)) (N y)
    have h2 : |N y - N (r c)| = |N (r c) - N y| := abs_sub_comm _ _
    rw [h2]
    linarith [abs_sub_le (f (nearestSite ((n : ℝ) • (r c))) / (n : ℝ)) (N (r c)) (N y)]
  linarith
