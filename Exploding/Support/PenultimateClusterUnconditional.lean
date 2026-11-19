import Exploding.Support.FiniteExplodingAllSitesUnconditional

/-!
# Polylogarithmic bounds on penultimate clusters

Almost surely, penultimate clusters inside a large box have polylogarithmic
diameter.
-/

open Exploding LatticeProb MeasureTheory

/-- Penultimate clusters are almost surely contained in polylogarithmic boxes. -/
theorem Exploding.last_penultimate_cluster_unconditional (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
        ∀ y ∈ penultimateCluster η x, ∀ i, ((|y i - x i| : ℤ) : ℝ) ≤ Real.log n ^ γ
:= by
  rcases hp1.lt_or_eq with hp1 | heq
  ·
    refine ⟨(5 : ℝ) / 2 + 1, by norm_num, ?_⟩
    obtain ⟨k0, hk0⟩ :=
      Exploding.renormalization_properties_unconditional d hd p hp hp1.le
    obtain ⟨c, C, hc, hC, hren⟩ := hk0 (max k0 1) (le_max_left _ _)
    have hk : 1 ≤ max k0 1 := le_max_right _ _
    obtain ⟨Nk, hNk8, hNkk, hNk1, hNk2⟩ := pcl_thresh_spec (max k0 1)
    filter_upwards [aux_penultimate_bounds d p hp hp1, hren,
      Exploding.finite_exploding_at_unconditional d hd p hp hp1] with η hb hren' hlast_all
    obtain ⟨Cinf, hCinf, hcomp, hchem, -, -⟩ := hren'
    obtain ⟨n0c, hn0c⟩ := hcomp
    refine ⟨max n0c (max Nk (max 1 (Nat.ceil (Real.exp 2)))), ?_⟩
    intro n hn x hx y hy i
    simp only [max_le_iff] at hn
    obtain ⟨hn0c', hnNk, hn1, hne⟩ := hn
    have hlog2 : 2 ≤ Real.log n := by
      have h1 : Real.exp 2 ≤ (n : ℝ) := by
        have := Nat.le_ceil (Real.exp 2)
        exact le_trans this (by exact_mod_cast hne)
      have h2 : Real.log (Real.exp 2) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (Real.exp_pos 2) h1
      rwa [Real.log_exp] at h2
    have hlog0 : 0 ≤ Real.log n := by linarith
    have hlogpow : 0 ≤ Real.log n ^ ((5 : ℝ) / 2) := Real.rpow_nonneg hlog0 _
    rcases hy with hxy | ⟨y', hy'adj, hy'pos⟩
    · rw [hxy]
      have h1 : ((|x i - x i| : ℤ) : ℝ) = 0 := by simp
      rw [h1]
      exact Real.rpow_nonneg hlog0 _
    ·
      obtain ⟨m, path, h0, hm, hadj, hfin, hpos⟩ :=
        pen_box_pos hd η (fun z => (hb z).1) (fun z => (hb z).2) x y' hy'pos
      have hpathfin : (path '' {j : ℕ | j ≤ m}).Finite :=
        Set.Finite.image _ (Set.finite_Iic m)
      obtain ⟨m0, M0, hm0, hM0, hbox⟩ :=
        br_eq_box (path '' {j : ℕ | j ≤ m}) hpathfin ⟨x, ⟨0, Nat.zero_le m, h0⟩⟩
      have hy'R : y' ∈ br (path '' {j : ℕ | j ≤ m}) := by
        apply mem_br_of_mem
        exact ⟨m, le_refl m, hm⟩
      have hcoord : ∀ j : Fin d, |y j - x j| ≤ (M0 j - m0 j) + 1 := by
        intro j
        have hxmem : x ∈ br (path '' {j : ℕ | j ≤ m}) := by
          apply mem_br_of_mem
          exact ⟨0, Nat.zero_le m, h0⟩
        have hxbox : m0 j ≤ x j ∧ x j ≤ M0 j := by
          rw [hbox] at hxmem
          exact hxmem j
        have hy'box : m0 j ≤ y' j ∧ y' j ≤ M0 j := by
          rw [hbox] at hy'R
          exact hy'R j
        obtain ⟨hx1, hx2⟩ := hxbox
        obtain ⟨hy1, hy2⟩ := hy'box
        obtain ⟨j', hj' | hj'⟩ := hy'adj
        · have h1 : y j = y' j + (unit j') j := by
            have := congrFun hj' j
            simp only [Pi.add_apply] at this
            linarith
          have h2 : (unit j') j ≤ 1 := by
            by_cases h : j' = j
            · subst h; simp [LatticeProb.unit]
            · simp [LatticeProb.unit, h]
          have h3 : (unit j') j ≥ -1 := by
            by_cases h : j' = j
            · subst h; simp [LatticeProb.unit]
            · simp [LatticeProb.unit, h]
          rw [h1, abs_le]
          constructor <;> omega
        · have h1 : y j = y' j - (unit j') j := by
            have := congrFun hj' j
            simp only [Pi.add_apply] at this
            linarith
          have h2 : (unit j') j ≤ 1 := by
            by_cases h : j' = j
            · subst h; simp [LatticeProb.unit]
            · simp [LatticeProb.unit, h]
          have h3 : (unit j') j ≥ -1 := by
            by_cases h : j' = j
            · subst h; simp [LatticeProb.unit]
            · simp [LatticeProb.unit, h]
          rw [h1, abs_le]
          constructor <;> omega
      have hxcent : ∀ j, |x j| ≤ (n : ℤ) := fun j => le_trans (abs_coord_le_mnorm x j) hx
      have hxbox : m0 i ≤ x i ∧ x i ≤ M0 i := by
        have hxmem : x ∈ br (path '' {j : ℕ | j ≤ m}) := by
          apply mem_br_of_mem
          exact ⟨0, Nat.zero_le m, h0⟩
        rw [hbox] at hxmem
        exact hxmem i
      have hseg : ∀ v : ℤ, m0 i ≤ v → v ≤ M0 i →
          0 < penultimateWave η x (fun j => if j = i then v else x j) := by
        intro v hv0 hv1
        have hmem : (fun j => if j = i then v else x j) ∈ br (path '' {j : ℕ | j ≤ m}) := by
          have h1 : ∀ j, m0 j ≤ (fun j => if j = i then v else x j) j ∧
              (fun j => if j = i then v else x j) j ≤ M0 j := by
            intro j
            by_cases hj : j = i
            · subst hj
              simpa using ⟨hv0, hv1⟩
            · simp only [ite_eq_right hj]
              have h2 : |x j| ≤ (n : ℤ) := hxcent j
              rw [abs_le] at h2
              have h3 : m0 j ≤ x j ∧ x j ≤ M0 j := by
                have h5 : x ∈ br (path '' {j : ℕ | j ≤ m}) := by
                  apply mem_br_of_mem
                  exact ⟨0, Nat.zero_le m, h0⟩
                rw [hbox] at h5
                exact h5 j
              exact ⟨h3.1, h3.2⟩
          rw [hbox]
          exact h1
        exact hpos _ hmem
      set L : ℤ := M0 i - m0 i with hL
      have hLnonneg : 0 ≤ L := by omega
      set n' : ℕ := n + L.toNat + (max k0 1) + 4 with hn'
      have hn'_ge : n ≤ n' := by simp only [hn']; omega
      have hn'_eq : ((n' : ℕ) : ℤ) = (n : ℤ) + (L.toNat : ℤ) + (max k0 1 : ℤ) + 4 := by
        simp only [hn']; push_cast; ring
      have hLtoNat : (L.toNat : ℤ) = L := Int.toNat_of_nonneg hLnonneg
      have hLle : L ≤ (n' : ℤ) - (n : ℤ) := by rw [hn'_eq, hLtoNat]; omega
      have hlog' : 0 ≤ Real.log n' ^ ((5 : ℝ) / 2) := by
        apply Real.rpow_nonneg
        apply Real.log_nonneg
        have : (1 : ℕ) ≤ n' := le_trans (by omega : 1 ≤ n) hn'_ge
        exact_mod_cast this
      have hboxle := box_end_le (m0 i) (M0 i) (x i) hxbox.1 hxbox.2
      have h3 : |m0 i| ≤ |x i| + L := by
        have h1 : |x i| + (M0 i - m0 i) = |x i| + L := by rw [hL]
        rw [← h1]
        exact hboxle.1
      have h4 : |M0 i| ≤ |x i| + L := by
        have h1 : |x i| + (M0 i - m0 i) = |x i| + L := by rw [hL]
        rw [← h1]
        exact hboxle.2
      have hxle : |x i| ≤ (n : ℤ) := hxcent i
      have h3' : |m0 i| + 2 ≤ (n' : ℤ) := by
        have h1 : (n : ℤ) + L + 2 ≤ (n' : ℤ) := by
          have h8 : ((n' : ℕ) : ℤ) = (n : ℤ) + L + (max k0 1 : ℤ) + 4 := by
            rw [hn'_eq, hLtoNat]
          have h9 : (1 : ℤ) ≤ (max k0 1 : ℤ) := by exact_mod_cast hk
          rw [h8]; omega
        have h6 : |m0 i| ≤ (n : ℤ) + L := le_trans h3 (by linarith [hxle])
        have h7 : |m0 i| + 2 ≤ (n : ℤ) + L + 2 := by linarith
        linarith [h1, h7]
      have h4' : |M0 i| + (max k0 1 : ℤ) ≤ (n' : ℤ) := by
        have h1 : (n : ℤ) + L + (max k0 1 : ℤ) ≤ (n' : ℤ) := by
          have h8 : ((n' : ℕ) : ℤ) = (n : ℤ) + L + (max k0 1 : ℤ) + 4 := by
            rw [hn'_eq, hLtoNat]
          rw [h8]; omega
        have h6 : |M0 i| ≤ (n : ℤ) + L := le_trans h4 (by linarith [hxle])
        have h7 : |M0 i| + (max k0 1 : ℤ) ≤ (n : ℤ) + L + (max k0 1 : ℤ) := by linarith
        linarith [h1, h7]
      have hbase' : ∀ j, |x j| + 2 ≤ (n' : ℤ) := by
        intro j
        have h1 : |x j| ≤ (n : ℤ) := hxcent j
        have h2 : (n : ℤ) + 2 ≤ (n' : ℤ) := by
          have h3 : ((n' : ℕ) : ℤ) = (n : ℤ) + L + (max k0 1 : ℤ) + 4 := by
            rw [hn'_eq, hLtoNat]
          have h4 : (0 : ℤ) ≤ L := hLnonneg
          have h5 : (1 : ℤ) ≤ (max k0 1 : ℤ) := by exact_mod_cast hk
          rw [h3]; omega
        omega
      have hrun' : ∀ v : ℤ, (m0 i - 1) / (max k0 1 : ℤ) + 1 ≤ v →
          v ≤ (M0 i - (max k0 1 : ℤ)) / (max k0 1 : ℤ) → |v| ≤ (n' : ℤ) := by
        intro v hv0 hv1
        have hk1 : (1 : ℤ) ≤ (max k0 1 : ℤ) := by exact_mod_cast hk
        have h1 : |(m0 i - 1) / (max k0 1 : ℤ) + 1| ≤ |m0 i| + 2 :=
          (div_run_abs_le _ hk1 (m0 i)).1
        have h2 : |(M0 i - (max k0 1 : ℤ)) / (max k0 1 : ℤ)| ≤ |M0 i| + (max k0 1 : ℤ) :=
          (div_run_abs_le _ hk1 (M0 i)).2
        rw [abs_le] at h1 h2
        rw [abs_le]
        constructor
        · have h6 : -(n' : ℤ) ≤ (m0 i - 1) / (max k0 1 : ℤ) + 1 := by
            have h8 : -(|m0 i| + 2) ≤ (m0 i - 1) / (max k0 1 : ℤ) + 1 := h1.1
            have h11 : -(n' : ℤ) ≤ -(|m0 i| + 2) := by linarith [h3']
            omega
          have h7 : -(n' : ℤ) ≤ (M0 i - (max k0 1 : ℤ)) / (max k0 1 : ℤ) := by
            have h8 : -(|M0 i| + (max k0 1 : ℤ)) ≤ (M0 i - (max k0 1 : ℤ)) / (max k0 1 : ℤ) := h2.1
            have h11 : -(n' : ℤ) ≤ -(|M0 i| + (max k0 1 : ℤ)) := by linarith [h4']
            omega
          omega
        · have h6 : (m0 i - 1) / (max k0 1 : ℤ) + 1 ≤ (n' : ℤ) := by
            have h8 : (m0 i - 1) / (max k0 1 : ℤ) + 1 ≤ |m0 i| + 2 := h1.2
            have h11 : |m0 i| + 2 ≤ (n' : ℤ) := h3'
            linarith
          have h7 : (M0 i - (max k0 1 : ℤ)) / (max k0 1 : ℤ) ≤ (n' : ℤ) := by
            have h8 : (M0 i - (max k0 1 : ℤ)) / (max k0 1 : ℤ) ≤ |M0 i| + (max k0 1 : ℤ) := h2.2
            have h11 : |M0 i| + (max k0 1 : ℤ) ≤ (n' : ℤ) := h4'
            linarith
          omega
      have hin' : ∀ v : ℤ, (m0 i - 1) / (max k0 1 : ℤ) + 1 ≤ v →
          v ≤ (M0 i - (max k0 1 : ℤ)) / (max k0 1 : ℤ) →
          (fun j => if j = i then v else (x j - 1) / (max k0 1 : ℤ)) ∈ (cent d n' : Set (Site d)) := by
        intro v hv0 hv1 j
        have hk1 : (1 : ℤ) ≤ (max k0 1 : ℤ) := by exact_mod_cast hk
        have hv : |v| ≤ (n' : ℤ) := hrun' v hv0 hv1
        have hc : |x j| + 2 ≤ (n' : ℤ) := hbase' j
        have hc' : |x j| ≤ (n' : ℤ) := by linarith
        rw [abs_le] at hv hc'
        obtain ⟨hv1', hv2'⟩ := hv
        obtain ⟨hc1, hc2⟩ := hc'
        by_cases hj : j = i
        · simp only [ite_eq_left hj]
          rw [abs_le]
          exact ⟨hv1', hv2'⟩
        · simp only [ite_eq_right hj]
          have h1 : |(x j - 1) / (max k0 1 : ℤ)| ≤ |x j - 1| := div_abs_le _ hk1 _
          have h2 : |x j - 1| ≤ |x j| + 1 := by
            rw [abs_sub_le_iff]
            constructor
            · have h5 : x j ≤ |x j| := le_abs_self _
              omega
            · have h5 : -(x j) ≤ |x j| := neg_le_abs _
              omega
          have h3 : |(x j - 1) / (max k0 1 : ℤ)| ≤ |x j| + 1 := le_trans h1 h2
          rw [abs_le] at h3
          rw [abs_le]
          constructor
          · have h5 : -(|x j| + 1) ≤ (x j - 1) / (max k0 1 : ℤ) := h3.1
            have h6 : -(|x j| + 1) ≥ -(n' : ℤ) := by linarith [hbase' j]
            linarith
          · have h5 : (x j - 1) / (max k0 1 : ℤ) ≤ |x j| + 1 := h3.2
            have h6 : |x j| + 1 ≤ (n' : ℤ) := by linarith [hbase' j]
            linarith
      have hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n x := hlast_all x
      have hcastk : ((max k0 1 : ℕ) : ℤ) = (max k0 1 : ℤ) := by push_cast; rfl
      have hin'' : ∀ v : ℤ, (m0 i - 1) / ((max k0 1 : ℕ) : ℤ) + 1 ≤ v →
          v ≤ (M0 i - ((max k0 1 : ℕ) : ℤ)) / ((max k0 1 : ℕ) : ℤ) →
          (fun j => if j = i then v else (x j - 1) / ((max k0 1 : ℕ) : ℤ)) ∈
            (cent d (n + (M0 i - m0 i).toNat + (max k0 1 : ℕ) + 4) : Set (Site d)) := by
        rw [hcastk]
        exact hin'
      have hfin := pcl_length_final hd η (fun z => (hb z).1) (fun z => (hb z).2) (max k0 1) hk
        Cinf hCinf x hlast n0c hn0c Nk hNk8 hNkk hNk1 hNk2 n hn0c' hnNk i x (m0 i) (M0 i)
        (by omega) hin'' hseg
      have hc := hcoord i
      have hcR : ((|y i - x i| : ℤ) : ℝ) ≤ ((M0 i - m0 i : ℤ) : ℝ) + 1 := by
        have : ((|y i - x i| : ℤ) : ℝ) ≤ (((M0 i - m0 i) + 1 : ℤ) : ℝ) := by exact_mod_cast hc
        simpa using this
      linarith
  · subst heq
    exact Exploding.last_penultimate_cluster_p1 d hd
