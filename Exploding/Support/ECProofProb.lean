/-
The probability estimates of Proposition 7.1: box-crossing events of tiles depend only on
the tile, tiles far apart are independent under finite range of dependence, and the
chance that a long `*`-path of tiles fails to be box-crossing is exponentially small.
-/
import Exploding.Support.ECProofTile
import Exploding.Support.ECProofCount

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

/-! ### Locality of the crossing events -/

/-- **The frozen odometer is congruent in the background off the frozen set.** -/
theorem ec_fodo_congr (S : Set (Site d)) (s0 s0' w0 : Site d → ℤ)
    (h : ∀ x, x ∉ S → s0 x = s0' x) (t : ℕ) (x : Site d) :
    fodo S s0 w0 t x = fodo S s0' w0 t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    have hfun : fodo S s0 w0 t = fodo S s0' w0 t := funext ih
    rw [fodo_succ, fodo_succ]
    by_cases hx : x ∈ S
    · rw [if_pos hx, if_pos hx]
    · have hf : fconf S s0 w0 t x = fconf S s0' w0 t x := by
        simp only [fconf, lap, hfun, h x hx]
      rw [if_neg hx, if_neg hx, hfun, hf]

/-- Box-crossing of a tile reads the background only on the tile. -/
theorem ec_boxCrossed_congr (k : Fin d → ℕ) (j : Site d) {η η' : Site d → ℤ}
    (h : ∀ x ∈ rboxShift k j, η x = η' x) : BoxCrossed η k j ↔ BoxCrossed η' k j := by
  unfold BoxCrossed CrossedInDirection
  have hf : ∀ i hi t x, fodo (rboxShift k j)ᶜ η (Set.indicator (faceOut k j i hi) 1) t x =
      fodo (rboxShift k j)ᶜ η' (Set.indicator (faceOut k j i hi) 1) t x := fun i hi t x =>
    ec_fodo_congr _ _ _ _ (fun y hy => h y (by simpa using hy)) t x
  simp only [hf]

theorem ec_rbox_finite (k : Fin d → ℕ) (j : Site d) : (rboxShift k j).Finite :=
  (Set.Finite.pi (t := fun i : Fin d => Set.Icc (1 + (k i : ℤ) * j i) ((k i : ℤ) * j i + k i))
    (fun _ => Set.finite_Icc _ _)).subset (fun _ hx i _ => hx i)

/-- The tile as a finite set of sites. -/
noncomputable def ec_tileFin (k : Fin d → ℕ) (j : Site d) : Finset (Site d) :=
  (ec_rbox_finite k j).toFinset

theorem ec_mem_tileFin (k : Fin d → ℕ) (j : Site d) (x : Site d) :
    x ∈ ec_tileFin k j ↔ x ∈ rboxShift k j := by
  unfold ec_tileFin
  simp

/-! ### Events depending on finitely many sites -/

theorem ec_dep_eq (I : Finset (Site d)) (E : Set (Site d → ℤ))
    (hdep : ∀ η η' : Site d → ℤ, (∀ x ∈ I, η x = η' x) → (η ∈ E ↔ η' ∈ E)) :
    E = (fun η : Site d → ℤ => fun i : I => η i) ⁻¹'
      ((fun η : Site d → ℤ => fun i : I => η i) '' E) := by
  ext η
  constructor
  · intro h; exact ⟨η, h, rfl⟩
  · rintro ⟨η', hη', hff⟩
    exact (hdep η' η (fun x hx => congrFun hff ⟨x, hx⟩)).1 hη'

theorem ec_measurableSet_of_dep (I : Finset (Site d)) (E : Set (Site d → ℤ))
    (hdep : ∀ η η' : Site d → ℤ, (∀ x ∈ I, η x = η' x) → (η ∈ E ↔ η' ∈ E)) :
    MeasurableSet E := by
  rw [ec_dep_eq I E hdep]
  refine MeasurableSet.preimage ((Set.to_countable _).measurableSet) ?_
  exact measurable_pi_lambda _ (fun i => measurable_pi_apply (i : Site d))

/-! ### Independence of far-apart events -/

/-- **Product formula.**  Events that depend only on finite sets of sites, any two of which
are more than `K` apart, are independent under a measure of finite range of dependence. -/
theorem ec_indep_prod (P : Measure (Site d → ℤ)) [IsProbabilityMeasure P] (K : ℕ)
    (h1 : ∀ I J : Finset (Site d), (∀ a ∈ I, ∀ b ∈ J, (K : ℤ) < mnorm (a - b)) →
      ProbabilityTheory.IndepFun (fun η : Site d → ℤ => fun i : I => η i)
        (fun η : Site d → ℤ => fun j : J => η j) P)
    {ι : Type*} [DecidableEq ι] (E : ι → Set (Site d → ℤ)) (I : ι → Finset (Site d))
    (hdep : ∀ t, ∀ η η' : Site d → ℤ, (∀ x ∈ I t, η x = η' x) → (η ∈ E t ↔ η' ∈ E t)) :
    ∀ T : Finset ι, (∀ s ∈ T, ∀ t ∈ T, s ≠ t → ∀ a ∈ I s, ∀ b ∈ I t, (K : ℤ) < mnorm (a - b)) →
      P (⋂ t ∈ T, E t) = ∏ t ∈ T, P (E t) := by
  intro T
  induction T using Finset.induction_on with
  | empty => intro _; simp
  | insert s T hs ih =>
    intro hfar
    rw [Finset.set_biInter_insert, Finset.prod_insert hs]
    have ihT := ih (fun a ha b hb hab => hfar a (Finset.mem_insert_of_mem ha) b
      (Finset.mem_insert_of_mem hb) hab)
    set J : Finset (Site d) := T.biUnion I with hJ
    have hIJ : ∀ a ∈ I s, ∀ b ∈ J, (K : ℤ) < mnorm (a - b) := by
      intro a ha b hb
      obtain ⟨t, ht, hbt⟩ := Finset.mem_biUnion.1 hb
      have hne : s ≠ t := fun h => hs (h ▸ ht)
      exact hfar s (Finset.mem_insert_self _ _) t (Finset.mem_insert_of_mem ht) hne a ha b hbt
    have hind := h1 (I s) J hIJ
    have hEs := ec_dep_eq (I s) (E s) (hdep s)
    have hGdep : ∀ η η' : Site d → ℤ, (∀ x ∈ J, η x = η' x) →
        (η ∈ (⋂ t ∈ T, E t) ↔ η' ∈ (⋂ t ∈ T, E t)) := by
      intro η η' hη
      simp only [Set.mem_iInter]
      refine forall₂_congr (fun t ht => hdep t η η' (fun x hx => hη x ?_))
      exact Finset.mem_biUnion.2 ⟨t, ht, hx⟩
    have hG := ec_dep_eq J (⋂ t ∈ T, E t) hGdep
    have hmA : MeasurableSet ((fun η : Site d → ℤ => fun i : I s => η i) '' E s) :=
      (Set.to_countable _).measurableSet
    have hmB : MeasurableSet ((fun η : Site d → ℤ => fun i : J => η i) '' (⋂ t ∈ T, E t)) :=
      (Set.to_countable _).measurableSet
    calc P (E s ∩ ⋂ t ∈ T, E t)
        = P ((fun η : Site d → ℤ => fun i : I s => η i) ⁻¹'
            ((fun η : Site d → ℤ => fun i : I s => η i) '' E s) ∩
            (fun η : Site d → ℤ => fun i : J => η i) ⁻¹'
            ((fun η : Site d → ℤ => fun i : J => η i) '' (⋂ t ∈ T, E t))) := by
          rw [← hEs, ← hG]
      _ = P ((fun η : Site d → ℤ => fun i : I s => η i) ⁻¹'
            ((fun η : Site d → ℤ => fun i : I s => η i) '' E s)) *
          P ((fun η : Site d → ℤ => fun i : J => η i) ⁻¹'
            ((fun η : Site d → ℤ => fun i : J => η i) '' (⋂ t ∈ T, E t))) :=
          hind.measure_inter_preimage_eq_mul _ _ hmA hmB
      _ = P (E s) * ∏ t ∈ T, P (E t) := by rw [← hEs, ← hG, ihT]

/-! ### One tile, and a path of tiles -/

theorem ec_boxCrossed_measurable (k : Fin d → ℕ) (j : Site d) :
    MeasurableSet {η : Site d → ℤ | BoxCrossed η k j} :=
  ec_measurableSet_of_dep (ec_tileFin k j) _ (fun _ _ h =>
    ec_boxCrossed_congr k j (fun x hx => h x ((ec_mem_tileFin k j x).2 hx)))

/-- A tile fails to be box-crossing with probability at most `δ`. -/
theorem ec_bad_prob_le (P : Measure (Site d → ℤ)) [IsProbabilityMeasure P] (k : Fin d → ℕ)
    (j : Site d) (δ : ℝ) (hδ1 : δ ≤ 1)
    (hP : ENNReal.ofReal (1 - δ) < P {η | BoxCrossed η k j}) :
    P {η | ¬ BoxCrossed η k j} ≤ ENNReal.ofReal δ := by
  have hc : {η : Site d → ℤ | ¬ BoxCrossed η k j} = {η | BoxCrossed η k j}ᶜ := rfl
  rw [hc, prob_compl_eq_one_sub (ec_boxCrossed_measurable k j)]
  calc 1 - P {η | BoxCrossed η k j} ≤ 1 - ENNReal.ofReal (1 - δ) := tsub_le_tsub_left hP.le 1
    _ = ENNReal.ofReal δ := by
        have := ENNReal.ofReal_sub 1 (show (0 : ℝ) ≤ 1 - δ by linarith)
        rw [ENNReal.ofReal_one] at this
        rw [← this]
        congr 1
        ring

/-- Two boxes in the `i`-th coordinate separated by more than `K` tiles are more than `K`
apart. -/
theorem ec_sep_coord (K : ℕ) (kk : ℤ) (hkk : 1 ≤ kk) (x y s t : ℤ)
    (hx : 1 + kk * s ≤ x ∧ x ≤ kk * s + kk) (hy : 1 + kk * t ≤ y ∧ y ≤ kk * t + kk)
    (h : (K : ℤ) < |s - t|) : (K : ℤ) < |x - y| := by
  have hK : (0 : ℤ) ≤ K := by positivity
  rcases lt_or_gt_of_ne (show s ≠ t by intro e; rw [e, sub_self, abs_zero] at h; omega) with hst | hst
  · rw [abs_of_neg (by omega)] at h
    have h1 : 0 ≤ (kk - 1) * (t - s - 1) := mul_nonneg (by omega) (by omega)
    rw [abs_of_nonpos (by nlinarith)]
    nlinarith
  · rw [abs_of_pos (by omega)] at h
    have h1 : 0 ≤ (kk - 1) * (s - t - 1) := mul_nonneg (by omega) (by omega)
    rw [abs_of_nonneg (by nlinarith)]
    nlinarith

/-- Far-apart planar tiles occupy far-apart sites. -/
theorem ec_tiles_far (hd : 2 ≤ d) (K : ℕ) (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {s t : ℤ × ℤ}
    (hfar : ec_far K s t) :
    ∀ a ∈ ec_tileFin k (ec_emb d s), ∀ b ∈ ec_tileFin k (ec_emb d t),
      (K : ℤ) < mnorm (a - b) := by
  intro a ha b hb
  rw [ec_mem_tileFin] at ha hb
  rcases hfar with h | h
  · have := ec_sep_coord K (k ⟨0, by omega⟩ : ℤ) (by have := hk ⟨0, by omega⟩; omega)
      (a ⟨0, by omega⟩) (b ⟨0, by omega⟩) s.1 t.1
      (by simpa [ec_emb] using ha ⟨0, by omega⟩) (by simpa [ec_emb] using hb ⟨0, by omega⟩) h
    have h2 := ec_abs_le_mnorm (a - b) ⟨0, by omega⟩
    simp only [Pi.sub_apply] at h2
    omega
  · have := ec_sep_coord K (k ⟨1, by omega⟩ : ℤ) (by have := hk ⟨1, by omega⟩; omega)
      (a ⟨1, by omega⟩) (b ⟨1, by omega⟩) s.2 t.2
      (by simpa [ec_emb] using ha ⟨1, by omega⟩) (by simpa [ec_emb] using hb ⟨1, by omega⟩) h
    have h2 := ec_abs_le_mnorm (a - b) ⟨1, by omega⟩
    simp only [Pi.sub_apply] at h2
    omega

/-- **A path of non-crossing tiles is unlikely.** -/
theorem ec_path_prob (hd : 2 ≤ d) (P : Measure (Site d → ℤ)) [IsProbabilityMeasure P] (K : ℕ)
    (h1 : ∀ I J : Finset (Site d), (∀ a ∈ I, ∀ b ∈ J, (K : ℤ) < mnorm (a - b)) →
      ProbabilityTheory.IndepFun (fun η : Site d → ℤ => fun i : I => η i)
        (fun η : Site d → ℤ => fun j : J => η j) P)
    (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hbad : ∀ j, P {η | ¬ BoxCrossed η k j} ≤ ENNReal.ofReal (r ^ ((2 * K + 1) ^ 2)))
    (l : List (ℤ × ℤ)) (hl : l.Nodup) :
    P {η | ∀ z ∈ l, ¬ BoxCrossed η k (ec_emb d z)} ≤ ENNReal.ofReal r ^ l.length := by
  classical
  obtain ⟨T, hTl, hTfar, hTcard⟩ := ec_greedy K l.toFinset
  have hlen : l.toFinset.card = l.length := List.toFinset_card_of_nodup hl
  have hprod := ec_indep_prod P K h1
    (fun z : ℤ × ℤ => {η : Site d → ℤ | ¬ BoxCrossed η k (ec_emb d z)})
    (fun z => ec_tileFin k (ec_emb d z))
    (fun z η η' h => by
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, not_iff_not]
      exact ec_boxCrossed_congr k _ (fun x hx => h x ((ec_mem_tileFin _ _ x).2 hx))) T
    (fun s hs t ht hst => ec_tiles_far hd K k hk (hTfar s hs t ht hst))
  have hsub : {η : Site d → ℤ | ∀ z ∈ l, ¬ BoxCrossed η k (ec_emb d z)} ⊆
      ⋂ t ∈ T, {η : Site d → ℤ | ¬ BoxCrossed η k (ec_emb d t)} := by
    intro η hη
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact fun t ht => hη t (List.mem_toFinset.1 (hTl ht))
  calc P {η : Site d → ℤ | ∀ z ∈ l, ¬ BoxCrossed η k (ec_emb d z)}
      ≤ P (⋂ t ∈ T, {η : Site d → ℤ | ¬ BoxCrossed η k (ec_emb d t)}) := measure_mono hsub
    _ = ∏ t ∈ T, P {η : Site d → ℤ | ¬ BoxCrossed η k (ec_emb d t)} := hprod
    _ ≤ ENNReal.ofReal (r ^ ((2 * K + 1) ^ 2)) ^ T.card :=
        Finset.prod_le_pow_card _ _ _ (fun t _ => hbad _)
    _ = ENNReal.ofReal (r ^ ((2 * K + 1) ^ 2 * T.card)) := by
        rw [← ENNReal.ofReal_pow (pow_nonneg hr0 _), ← pow_mul]
    _ ≤ ENNReal.ofReal (r ^ l.length) := by
        refine ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hr0 hr1 ?_)
        rw [← hlen]; exact hTcard
    _ = ENNReal.ofReal r ^ l.length := ENNReal.ofReal_pow hr0 _

end Exploding
