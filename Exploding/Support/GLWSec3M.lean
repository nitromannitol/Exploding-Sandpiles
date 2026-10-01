/-
Proposition 5.1 of the paper (generalized last wave): the penultimate cluster is polylogarithmically
small (Lemma 3.5 in the generalized setting), from path-filling and the cluster of strongly
box-crossing tiles.

If the support of the penultimate wave `ũ^{(x)}` left the box of radius `(log n)^γ` around `x`, it
would contain a long path from `x` (it is connected to `x`), whose bounding rectangle would be
lit by Hypothesis 5.3 and would contain a line of a tile of `C_∞` (the tiles of a long row cannot all
lie in a hole); by Hypothesis 5.4 the tile would be lit, and then all of `C_∞`, which a stabilizable
wave, having finite support, cannot do.
-/
import Exploding.Support.GLWSec3L

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

/-- The size estimates of the scales used in the proof of Lemma 3.5 hold for `n` large. -/
theorem glws_asymp35 (γp : ℝ) (hγp : 0 < γp) (kmax : ℕ) :
    ∃ n1 : ℕ, ∀ n : ℕ, n1 ≤ n →
      2 ≤ n ∧ 1 ≤ Real.log n ∧ 1 ≤ ⌊Real.log n ^ (γp + 4)⌋₊ ∧
      ⌊Real.log n ^ (γp + 4)⌋₊ + 1 ≤ n ∧
      (2 * Real.log n) ^ γp ≤ Real.log n ^ (γp + 4) ∧
      (kmax : ℝ) * ((2 * Real.log n) ^ ((5 : ℝ) / 2) + 3) ≤ Real.log n ^ (γp + 4) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- `log n ≥ 1`, `log n ^ 4 ≥ 2 ^ γp`, and the big constant
  have hev1 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n := hlog.eventually_ge_atTop 1
  have hev2 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ γp ≤ Real.log n ^ 4 := by
    have h4 : Tendsto (fun n : ℕ => Real.log n ^ 4) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp hlog
    exact h4.eventually_ge_atTop _
  have hev3 : ∀ᶠ n : ℕ in atTop,
      (kmax : ℝ) * (2 ^ ((5 : ℝ) / 2) + 3) ≤ Real.log n ^ (γp + 3 / 2) := by
    have h : Tendsto (fun n : ℕ => Real.log n ^ (γp + 3 / 2)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp hlog
    exact h.eventually_ge_atTop _
  have hev4 : ∀ᶠ n : ℕ in atTop, Real.log n ^ (γp + 4) ≤ (n : ℝ) / 2 := by
    have h := lwc_transfer_4 (γp + 4) 1 one_pos
    simp only [Nat.cast_one, one_mul] at h
    have := h.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)
    filter_upwards [this, eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [div_le_iff₀ hnpos] at hn
    linarith
  obtain ⟨n1, hn1⟩ := eventually_atTop.mp (hev1.and (hev2.and (hev3.and (hev4.and
    (eventually_ge_atTop 2)))))
  refine ⟨n1, fun n hn => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hn1 n hn
  set L := Real.log n with hL
  have hL0 : 0 < L := by linarith
  have hLpow : (1 : ℝ) ≤ L ^ (γp + 4) := Real.one_le_rpow h1 (by linarith)
  refine ⟨h5, h1, ?_, ?_, ?_, ?_⟩
  · exact Nat.le_floor (by simpa using hLpow)
  · have hfl : (⌊L ^ (γp + 4)⌋₊ : ℝ) ≤ L ^ (γp + 4) := Nat.floor_le (by positivity)
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h5
    have : ((⌊L ^ (γp + 4)⌋₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  · have e1 : (2 * L) ^ γp = 2 ^ γp * L ^ γp := Real.mul_rpow (by norm_num) hL0.le
    have e2 : L ^ (γp + 4) = L ^ γp * L ^ (4 : ℕ) := by
      rw [Real.rpow_add hL0]
      congr 1
      exact_mod_cast Real.rpow_natCast L 4
    rw [e1, e2]
    have : (0 : ℝ) ≤ L ^ γp := by positivity
    nlinarith
  · have e1 : (2 * L) ^ ((5 : ℝ) / 2) = 2 ^ ((5 : ℝ) / 2) * L ^ ((5 : ℝ) / 2) :=
      Real.mul_rpow (by norm_num) hL0.le
    have e2 : L ^ (γp + 4) = L ^ ((5 : ℝ) / 2) * L ^ (γp + 3 / 2) := by
      rw [← Real.rpow_add hL0]; ring_nf
    have hLp : (1 : ℝ) ≤ L ^ ((5 : ℝ) / 2) := Real.one_le_rpow h1 (by norm_num)
    rw [e1, e2]
    have hk0 : (0 : ℝ) ≤ (kmax : ℝ) := Nat.cast_nonneg _
    calc (kmax : ℝ) * (2 ^ ((5 : ℝ) / 2) * L ^ ((5 : ℝ) / 2) + 3)
        ≤ (kmax : ℝ) * ((2 ^ ((5 : ℝ) / 2) + 3) * L ^ ((5 : ℝ) / 2)) := by
          apply mul_le_mul_of_nonneg_left _ hk0
          nlinarith
      _ = ((kmax : ℝ) * (2 ^ ((5 : ℝ) / 2) + 3)) * L ^ ((5 : ℝ) / 2) := by ring
      _ ≤ L ^ (γp + 3 / 2) * L ^ ((5 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = L ^ ((5 : ℝ) / 2) * L ^ (γp + 3 / 2) := by ring

/-- **Lemma 3.5 in the generalized setting.**  On a background with `0 ≤ η ≤ 2d - 1` satisfying
path-filling and carrying the cluster `C_∞` of strongly box-crossing tiles with the hole
estimate, for `n` large every site `x ∈ [-n,n]^d` has a penultimate cluster inside the box of radius
`(log n)^{γ_p + 4}` around `x`. -/
theorem glws_penultimate_small (hd : 2 ≤ d) (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (k : Fin d → ℕ) (hk : ∀ i, 0 < k i)
    (Cinf : Set (Site d)) (hinf : Cinf.Infinite)
    (hgood : ∀ j ∈ Cinf, StronglyBoxCrossed η k j)
    (hconn : ∀ x ∈ Cinf, ∀ y ∈ Cinf, y ∈ componentIn Cinf x)
    (n0h : ℕ) (hole : ∀ n : ℕ, n0h ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ Cinf →
      (componentIn Cinfᶜ x).Finite ∧ ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2))
    (γp : ℝ) (hγp : 0 < γp) (hpf : glws_PF d γp η) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)),
      ∀ y ∈ penultimateCluster η x, ∀ i,
        ((|y i - x i| : ℤ) : ℝ) ≤ Real.log n ^ (γp + 4) := by
  classical
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  set kmax : ℕ := ∑ i, k i with hkmax
  obtain ⟨n1, hn1⟩ := glws_asymp35 γp hγp kmax
  obtain ⟨n0pf, hpfill⟩ := glws_pf_fill d γp η hd0 hlow hhigh hpf
  refine ⟨max n1 (max n0h n0pf), fun n hn x hx y hy i => ?_⟩
  have hn1' : n1 ≤ n := le_trans (le_max_left _ _) hn
  have hn0h : n0h ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn0pf : n0pf ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  obtain ⟨hn2, hL1, hD1, hDn, hA3, hA4⟩ := hn1 n hn1'
  set L : ℝ := Real.log n with hL
  set D : ℕ := ⌊L ^ (γp + 4)⌋₊ with hD
  have hL0 : 0 < L := by linarith
  have hfloor_le : (D : ℝ) ≤ L ^ (γp + 4) := Nat.floor_le (by positivity)
  have hfloor_lt : L ^ (γp + 4) < (D : ℝ) + 1 := Nat.lt_floor_add_one _
  -- the main claim: the support of a stabilizable wave stays in the box of radius `D`
  have hmain : ∀ y' : Site d, ∀ N : ℕ, 1 ≤ N → WaveStabilizable η N x →
      ∀ t : ℕ, 0 < wave η N x t y' → ∀ l, |y' l - x l| < (D : ℤ) := by
    intro y' N hN hstab t hty'
    by_contra hcon
    push Not at hcon
    obtain ⟨l, hl⟩ := hcon
    obtain ⟨m, z, hz0, hzm, hadj, hinj, hposz⟩ := glws_path_extract η hlow hhigh hd0 N x t y' hty'
    have hex : ∃ q : ℕ, ∃ l' : Fin d, (D : ℤ) ≤ |z q l' - x l'| := ⟨m, l, by rw [hzm]; exact hl⟩
    set p : ℕ := Nat.find hex with hp
    have hp1 : ∃ l' : Fin d, (D : ℤ) ≤ |z p l' - x l'| := Nat.find_spec hex
    have hpmin : ∀ q, q < p → ∀ l' : Fin d, |z q l' - x l'| < (D : ℤ) := by
      intro q hq l'
      have := Nat.find_min hex hq
      push Not at this
      exact this l'
    have hpm : p ≤ m := Nat.find_min' hex ⟨l, by rw [hzm]; exact hl⟩
    have hp0 : p ≠ 0 := by
      intro h0
      obtain ⟨l', hl'⟩ := hp1
      rw [h0, hz0] at hl'
      simp at hl'
      omega
    obtain ⟨p', hp'⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    have hdev : ∀ q, q ≤ p → ∀ l' : Fin d, |z q l' - x l'| ≤ (D : ℤ) := by
      intro q hq l'
      rcases Nat.lt_or_ge q p with hlt | hge
      · exact (hpmin q hlt l').le
      · have hqp : q = p := le_antisymm hq hge
        subst hqp
        have h1 := hpmin p' (by omega) l'
        have h2 := glws_adj_coord (hadj p' (by omega)) l'
        have h3 : |z (p' + 1) l' - x l'| ≤ |z (p' + 1) l' - z p' l'| + |z p' l' - x l'| := by
          have := abs_add_le (z (p' + 1) l' - z p' l') (z p' l' - x l')
          simpa using this
        rw [hp']
        linarith
    obtain ⟨l₁, hl₁⟩ := hp1
    have hdev1 : |z p l₁ - x l₁| = (D : ℤ) := le_antisymm (hdev p le_rfl l₁) hl₁
    have hpD : D ≤ p := by
      have h1 := glws_path_coord z hadj l₁ p hpm
      rw [hz0] at h1
      have : (D : ℤ) ≤ (p : ℤ) := by rw [← hdev1]; exact h1
      exact_mod_cast this
    -- the scales
    have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hDn' : (D : ℝ) + 1 ≤ n := by exact_mod_cast hDn
    have hlogn'' : Real.log ((n + D + 1 : ℕ) : ℝ) ≤ 2 * L := by
      have h1 : ((n + D + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by push_cast; linarith
      calc Real.log ((n + D + 1 : ℕ) : ℝ) ≤ Real.log (2 * (n : ℝ)) :=
            Real.log_le_log (by positivity) h1
        _ = Real.log 2 + L := Real.log_mul (by norm_num) (by positivity)
        _ ≤ 2 * L := by linarith
    have hlogn' : Real.log ((n + D : ℕ) : ℝ) ≤ 2 * L :=
      le_trans (Real.log_le_log (by positivity) (by push_cast; linarith)) hlogn''
    set n' : ℕ := n + D with hn'
    have hcent : ∀ i, i < p + 1 → z i ∈ cent d n' := by
      intro i hi l'
      have h1 := hdev i (by omega) l'
      have h2 := hx l'
      calc |z i l'| = |(z i l' - x l') + x l'| := by ring_nf
        _ ≤ |z i l' - x l'| + |x l'| := abs_add_le _ _
        _ ≤ (D : ℤ) + n := add_le_add h1 h2
        _ = ((n' : ℕ) : ℤ) := by rw [hn']; push_cast; ring
    have hlenR : Real.log (n' : ℝ) ^ γp ≤ ((p + 1 : ℕ) : ℝ) := by
      have h1 : Real.log (n' : ℝ) ^ γp ≤ (2 * L) ^ γp :=
        Real.rpow_le_rpow (Real.log_natCast_nonneg _) hlogn' hγp.le
      have h3 : (D : ℝ) + 1 ≤ ((p + 1 : ℕ) : ℝ) := by
        push_cast
        have : (D : ℝ) ≤ p := by exact_mod_cast hpD
        linarith
      linarith
    have hfill := hpfill N hN x n' (by omega) (p + 1) z hlenR hcent
      (fun i j hi hj hij => hinj i j (by omega) (by omega) hij)
      (fun i hi => hadj i (by omega)) t (fun i hi => hposz i (by omega))
    -- the rectangle
    set lo : Site d := fun m' => if m' = l₁ then min (x l₁) (z p l₁) else x m' with hlo_def
    set hi : Site d := fun m' => if m' = l₁ then max (x l₁) (z p l₁) else x m' with hhi_def
    have h0mem : z 0 ∈ z '' {i : ℕ | i < p + 1} := ⟨0, Nat.succ_pos p, rfl⟩
    have hpmem : z p ∈ z '' {i : ℕ | i < p + 1} := ⟨p, Nat.lt_succ_self p, rfl⟩
    have hbr : ∀ w : Site d, (∀ m', lo m' ≤ w m' ∧ w m' ≤ hi m') →
        w ∈ br (z '' {i : ℕ | i < p + 1}) := by
      intro w hw m'
      by_cases hm : m' = l₁
      · have := hw m'
        simp only [hlo_def, hhi_def, hm, if_true] at this
        rcases le_total (x l₁) (z p l₁) with hle | hle
        · rw [min_eq_left hle, max_eq_right hle] at this
          exact ⟨⟨z 0, h0mem, by rw [hz0, hm]; exact this.1⟩, ⟨z p, hpmem, by rw [hm]; exact this.2⟩⟩
        · rw [min_eq_right hle, max_eq_left hle] at this
          exact ⟨⟨z p, hpmem, by rw [hm]; exact this.1⟩, ⟨z 0, h0mem, by rw [hz0, hm]; exact this.2⟩⟩
      · have := hw m'
        simp only [hlo_def, hhi_def, hm, if_false] at this
        have hwx : w m' = x m' := le_antisymm this.2 this.1
        exact ⟨⟨z 0, h0mem, by rw [hz0, hwx]⟩, ⟨z 0, h0mem, by rw [hz0, hwx]⟩⟩
    have hbox : ∀ m', lo m' ≤ hi m' := by
      intro m'
      by_cases hm : m' = l₁
      · simp only [hlo_def, hhi_def, hm, if_true]
        exact le_trans (min_le_left _ _) (le_max_left _ _)
      · simp [hlo_def, hhi_def, hm]
    have hxn : ∀ m', |x m'| ≤ (n' : ℤ) := by
      intro m'
      have := hx m'
      rw [hn']; push_cast; have : (0 : ℤ) ≤ D := Int.natCast_nonneg D; linarith
    have hzp : |z p l₁| ≤ (n' : ℤ) := hcent p (by omega) l₁
    have hlo_abs : ∀ m', |lo m'| ≤ (n' : ℤ) := by
      intro m'
      by_cases hm : m' = l₁
      · simp only [hlo_def, hm, if_true]
        rcases min_choice (x l₁) (z p l₁) with h | h <;> rw [h]
        · exact hxn l₁
        · exact hzp
      · simp only [hlo_def, hm, if_false]; exact hxn m'
    have hhi_abs : ∀ m', |hi m'| ≤ (n' : ℤ) := by
      intro m'
      by_cases hm : m' = l₁
      · simp only [hhi_def, hm, if_true]
        rcases max_choice (x l₁) (z p l₁) with h | h <;> rw [h]
        · exact hxn l₁
        · exact hzp
      · simp only [hhi_def, hm, if_false]; exact hxn m'
    have hdiff : hi l₁ - lo l₁ = (D : ℤ) := by
      simp only [hlo_def, hhi_def, if_true]
      rw [max_sub_min_eq_abs]
      exact hdev1
    -- the row of macroscopic sites
    set r : ℕ := ⌈Real.log ((n' + 1 : ℕ) : ℝ) ^ ((5 : ℝ) / 2)⌉₊ with hr
    have hlenk : (k l₁ : ℤ) * ((r : ℤ) + 2) ≤ hi l₁ - lo l₁ + 1 := by
      rw [hdiff]
      have h1 : (r : ℝ) ≤ Real.log ((n' + 1 : ℕ) : ℝ) ^ ((5 : ℝ) / 2) + 1 :=
        (Nat.ceil_lt_add_one (by positivity)).le
      have h2 : Real.log ((n' + 1 : ℕ) : ℝ) ^ ((5 : ℝ) / 2) ≤ (2 * L) ^ ((5 : ℝ) / 2) :=
        Real.rpow_le_rpow (Real.log_natCast_nonneg _) hlogn'' (by norm_num)
      have h3 : (k l₁ : ℝ) ≤ (kmax : ℝ) := by
        have : k l₁ ≤ kmax := Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ l₁)
        exact_mod_cast this
      have h4 : (0 : ℝ) ≤ (k l₁ : ℝ) := Nat.cast_nonneg _
      have h5 : (r : ℝ) + 2 ≤ (2 * L) ^ ((5 : ℝ) / 2) + 3 := by linarith
      have h6 : (k l₁ : ℝ) * ((r : ℝ) + 2) ≤ (kmax : ℝ) * ((2 * L) ^ ((5 : ℝ) / 2) + 3) :=
        mul_le_mul h3 h5 (by positivity) (Nat.cast_nonneg _)
      have h7 : (k l₁ : ℝ) * ((r : ℝ) + 2) ≤ (D : ℝ) + 1 := by linarith
      have h8 : (k l₁ : ℤ) * ((r : ℤ) + 2) ≤ (D : ℤ) + 1 := by exact_mod_cast h7
      exact h8
    obtain ⟨μ, hrowc, hline⟩ := glws_row_geom k hk l₁ lo hi hbox n' hlo_abs hhi_abs r hlenk
    obtain ⟨t', ht', hj⟩ := glws_row_hole Cinf (n' + 1) (hole (n' + 1) (by omega)) l₁ μ r
      (Nat.le_ceil _) hrowc
    obtain ⟨zz, hzz, hlinezz⟩ := hline t' ht'
    have hpos : ∀ w ∈ rline k (μ + (t' : ℤ) • unit l₁) l₁ zz,
        0 < wave η N x (t + (p + 1) ^ d) w := fun w hw => hfill w (hbr w (hlinezz w hw))
    have hfired := glws_tile_of_line hd0 η hlow hhigh N hN x k (μ + (t' : ℤ) • unit l₁)
      (hgood _ hj) l₁ zz hzz (t + (p + 1) ^ d) hpos
    exact glws_not_stab_of_fired hd η hlow hhigh k hk Cinf hinf hgood hconn N hN x hj hfired hstab
  have hlast := glws_finite_exploding hd η hlow hhigh k hk Cinf hinf hgood hconn x
  have hne : {n : ℕ | 1 ≤ n ∧ ¬ WaveStabilizable η n x}.Nonempty := hlast
  have hmem : 1 ≤ waveThreshold η x ∧ ¬ WaveStabilizable η (waveThreshold η x) x :=
    Nat.sInf_mem hne
  rcases hy with hyx | ⟨y', hadj, hpos⟩
  · rw [hyx]
    simp only [sub_self, abs_zero, Int.cast_zero]
    exact Real.rpow_nonneg hL0.le _
  · by_cases hM1 : waveThreshold η x = 1
    · exfalso
      simp [penultimateWave, hM1] at hpos
    · have hstab := glw_penultimate_stabilizable η x hlast hM1
      have hN : 1 ≤ waveThreshold η x - 1 := by omega
      have hpen : penultimateWave η x = waveTerminal η (waveThreshold η x - 1) x := by
        simp [penultimateWave, hM1]
      rw [hpen] at hpos
      unfold waveTerminal at hpos
      have hdev := hmain y' (waveThreshold η x - 1) hN hstab _ hpos i
      have hadjc := glws_adj_coord hadj i
      have h3 : |y i - x i| ≤ |y i - y' i| + |y' i - x i| := by
        have := abs_add_le (y i - y' i) (y' i - x i)
        simpa using this
      have h4 : |y i - x i| ≤ (D : ℤ) := by linarith
      have h5 : ((|y i - x i| : ℤ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast h4
      linarith

end Exploding
