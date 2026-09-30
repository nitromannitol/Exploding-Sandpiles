/-
`eq:induction_specialcase2` of `paper/exploding.tex` (lines 918-1063), the first conjunct of
Step 1's three simultaneous inductions, in the form used by Step 2 of Proposition 4.1: for the
constructed background `s` (equal to `2d` at the origin, to `2d - 1` on the rest of the frozen
set `P̃`, and to `η ∈ [2d-2, 2d-1]` off `P̃`), positivity of the parallel toppling odometer `w_t`
of `s` implies positivity of the `P̃`-frozen odometer `w̃_t`.

The proof is the paper's simultaneous induction on `t`, in two layers.

* `assp_podo_inv` carries `eq:induction3` (`w_t(0) = max w_t`) and `eq:induction2`
  (`w_t` changes by at most one along every unit step and every two-coordinate diagonal step;
  `assp_Lip`) for the odometer of any background `s` with `2d - 2 ≤ s`, `s ≤ 2d - 1` off the
  origin and `s(0) ≤ 2d`.  The heart of it is `assp_unstable_propagate`: a site `x` with
  `w_t(x) = w_t(y) + 1` that is unstable forces its unit or diagonal neighbour `y` unstable.
* `assp_incl` carries `eq:induction1` (`R_t ⊆ R̃_t`), using only the one-step Lipschitz bound of
  the first layer at the previous time.
-/
import Exploding.Support.ASProof

open Exploding LatticeProb

variable {d : ℕ}

/-- `y` is a unit or a two-coordinate diagonal neighbour of `x` (the pairs of `eq:induction2`). -/
def assp_Close (x y : Site d) : Prop :=
  (∃ (i : Fin d) (a : ℤ), (a = 1 ∨ a = -1) ∧ y = x + a • unit i) ∨
  (∃ (i j : Fin d) (a b : ℤ), i ≠ j ∧ (a = 1 ∨ a = -1) ∧ (b = 1 ∨ b = -1) ∧
      y = x + a • unit i + b • unit j)

theorem assp_Close_symm {x y : Site d} (h : assp_Close x y) : assp_Close y x := by
  rcases h with ⟨i, a, ha, rfl⟩ | ⟨i, j, a, b, hij, ha, hb, rfl⟩
  · exact Or.inl ⟨i, -a, by omega, by module⟩
  · exact Or.inr ⟨i, j, -a, -b, hij, by omega, by omega, by module⟩

theorem assp_Close_of_adj {x y : Site d} (h : (lattice d).Adj y x) : assp_Close y x := by
  obtain ⟨i, h | h⟩ := h
  · exact Or.inl ⟨i, 1, Or.inl rfl, by rw [h]; module⟩
  · exact Or.inl ⟨i, -1, Or.inr rfl, by rw [h]; module⟩

/-- `eq:induction2`: `w` changes by at most `1` between close sites. -/
def assp_Lip (w : Site d → ℤ) : Prop := ∀ x y, assp_Close x y → w x ≤ w y + 1

theorem assp_Lip_adj {w : Site d → ℤ} (hw : assp_Lip w) (x : Site d) (i : Fin d) {a : ℤ}
    (ha : a = 1 ∨ a = -1) : w (x + a • unit i) ≤ w x + 1 ∧ w x ≤ w (x + a • unit i) + 1 :=
  ⟨hw _ _ (assp_Close_symm (Or.inl ⟨i, a, ha, rfl⟩)), hw _ _ (Or.inl ⟨i, a, ha, rfl⟩)⟩

/-! ### Sums over the `2d` neighbours -/

theorem assp_lap_eq_sum (w : Site d → ℤ) (x : Site d) :
    lap w x = ∑ k : Fin d,
      ((w (x + (1 : ℤ) • unit k) - w x) + (w (x + (-1 : ℤ) • unit k) - w x)) := by
  have h : ∀ k : Fin d, ((w (x + (1 : ℤ) • unit k) - w x) + (w (x + (-1 : ℤ) • unit k) - w x))
      = (w (x + unit k) + w (x - unit k)) - 2 * w x := by
    intro k
    have h1 : x + (1 : ℤ) • unit k = x + unit k := by rw [one_smul]
    have h2 : x + (-1 : ℤ) • unit k = x - unit k := by rw [neg_one_smul, sub_eq_add_neg]
    rw [h1, h2]; ring
  simp only [h]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [lap, nbrSumZ, nsmul_eq_mul]
  ring

theorem assp_sum_nonpos {f : Fin d → ℤ} (h : ∀ k, f k ≤ 0) : ∑ k, f k ≤ 0 :=
  Finset.sum_nonpos (fun k _ => h k)

theorem assp_sum_le_neg_one {f : Fin d → ℤ} (h : ∀ k, f k ≤ 0) (j : Fin d) (hj : f j ≤ -1) :
    ∑ k, f k ≤ -1 := by
  rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ j)]
  have : ∑ k ∈ Finset.univ.erase j, f k ≤ 0 := Finset.sum_nonpos (fun k _ => h k)
  omega

theorem assp_sum_ge_two {f : Fin d → ℤ} (h : ∀ k, 0 ≤ f k) {i j : Fin d} (hij : i ≠ j)
    (hi : 1 ≤ f i) (hj : 1 ≤ f j) : 2 ≤ ∑ k, f k := by
  calc (2 : ℤ) ≤ f i + f j := by omega
    _ = ∑ k ∈ ({i, j} : Finset (Fin d)), f k := (Finset.sum_pair hij).symm
    _ ≤ ∑ k, f k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => h k)

/-! ### The unstable-site propagation (`eq:induction2`, inductive step) -/

/-- A site with a unit neighbour one lower than itself is stable (the first displayed
case of the paper's inductive step for `eq:induction2`, origin and non-origin together). -/
theorem assp_stable_of_low_nbr {s w : Site d → ℤ}
    (hs_high : ∀ x, x ≠ 0 → s x ≤ 2 * (d : ℤ) - 1) (hs0 : s 0 ≤ 2 * (d : ℤ))
    (hmax : ∀ x, w x ≤ w 0) (hlip : assp_Lip w)
    (x : Site d) (j : Fin d) {a : ℤ} (ha : a = 1 ∨ a = -1)
    (hlow : w (x + a • unit j) + 1 ≤ w x) :
    s x + lap w x ≤ 2 * (d : ℤ) - 1 := by
  have hA : ∀ k : Fin d, k ≠ j → ∀ c : ℤ, (c = 1 ∨ c = -1) → w (x + c • unit k) ≤ w x := by
    intro k hk c hc
    have h1 : w (x + c • unit k) ≤ w (x + a • unit j) + 1 :=
      hlip _ _ (Or.inr ⟨k, j, -c, a, hk, by omega, ha, by module⟩)
    omega
  have hfj : ((w (x + (1 : ℤ) • unit j) - w x) + (w (x + (-1 : ℤ) • unit j) - w x)) ≤ 0 := by
    have h1 := assp_Lip_adj hlip x j (Or.inl rfl : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1)
    have h2 := assp_Lip_adj hlip x j (Or.inr rfl : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1)
    rcases ha with rfl | rfl <;> omega
  by_cases hx0 : x = 0
  · subst hx0
    have hfk : ∀ k : Fin d,
        ((w (0 + (1 : ℤ) • unit k) - w 0) + (w (0 + (-1 : ℤ) • unit k) - w 0)) ≤ 0 := by
      intro k
      have h1 := hmax (0 + (1 : ℤ) • unit k)
      have h2 := hmax (0 + (-1 : ℤ) • unit k)
      omega
    have hfj' : ((w (0 + (1 : ℤ) • unit j) - w 0) + (w (0 + (-1 : ℤ) • unit j) - w 0)) ≤ -1 := by
      have h1 := hmax (0 + (1 : ℤ) • unit j)
      have h2 := hmax (0 + (-1 : ℤ) • unit j)
      rcases ha with rfl | rfl <;> omega
    have := assp_sum_le_neg_one hfk j hfj'
    rw [assp_lap_eq_sum]
    omega
  · have hfk : ∀ k : Fin d,
        ((w (x + (1 : ℤ) • unit k) - w x) + (w (x + (-1 : ℤ) • unit k) - w x)) ≤ 0 := by
      intro k
      by_cases hk : k = j
      · subst hk; exact hfj
      · have h1 := hA k hk 1 (Or.inl rfl)
        have h2 := hA k hk (-1) (Or.inr rfl)
        omega
    have := assp_sum_nonpos hfk
    have hs := hs_high x hx0
    rw [assp_lap_eq_sum]
    omega

/-- A diagonal neighbour one lower than an unstable site is unstable (the diagonal case of the
paper's inductive step for `eq:induction2`). -/
theorem assp_unstable_diag {s w : Site d → ℤ}
    (hs_low : ∀ x, 2 * (d : ℤ) - 2 ≤ s x)
    (hs_high : ∀ x, x ≠ 0 → s x ≤ 2 * (d : ℤ) - 1) (hs0 : s 0 ≤ 2 * (d : ℤ))
    (hmax : ∀ x, w x ≤ w 0) (hlip : assp_Lip w)
    (x : Site d) (i j : Fin d) (hij : i ≠ j) {a b : ℤ} (ha : a = 1 ∨ a = -1)
    (hb : b = 1 ∨ b = -1)
    (hw : w x = w (x + a • unit i + b • unit j) + 1)
    (hun : 2 * (d : ℤ) ≤ s x + lap w x) :
    2 * (d : ℤ) ≤ s (x + a • unit i + b • unit j) + lap w (x + a • unit i + b • unit j) := by
  obtain ⟨y, hy⟩ : ∃ y, y = x + a • unit i + b • unit j := ⟨_, rfl⟩
  rw [← hy] at hw ⊢
  have hst := assp_stable_of_low_nbr hs_high hs0 hmax hlip x
  have h_ai : w x ≤ w (x + a • unit i) := by
    by_contra hcon
    have := hst i ha (by omega)
    omega
  have h_bj : w x ≤ w (x + b • unit j) := by
    by_contra hcon
    have := hst j hb (by omega)
    omega
  have h_ai' : w (x + a • unit i) ≤ w y + 1 := hlip _ _ (Or.inl ⟨j, b, hb, hy⟩)
  have h_bj' : w (x + b • unit j) ≤ w y + 1 :=
    hlip _ _ (Or.inl ⟨i, a, ha, by rw [hy]; module⟩)
  have hnb : ∀ (k : Fin d) (c : ℤ), (c = 1 ∨ c = -1) → w y ≤ w (y + c • unit k) := by
    intro k c hc
    by_cases hki : k = i
    · subst hki
      have hca : c = a ∨ c = -a := by omega
      rcases hca with hca | hca
      · rw [hca]
        have h1 : w (x + a • unit k) ≤ w (y + a • unit k) + 1 :=
          hlip _ _ (Or.inr ⟨k, j, a, b, hij, ha, hb, by rw [hy]; module⟩)
        omega
      · have hyc : y + c • unit k = x + b • unit j := by rw [hca, hy]; module
        rw [hyc]
        omega
    · by_cases hkj : k = j
      · subst hkj
        have hcb : c = b ∨ c = -b := by omega
        rcases hcb with hcb | hcb
        · rw [hcb]
          have h1 : w (x + b • unit k) ≤ w (y + b • unit k) + 1 :=
            hlip _ _ (Or.inr ⟨i, k, a, b, hij, ha, hb, by rw [hy]; module⟩)
          omega
        · have hyc : y + c • unit k = x + a • unit i := by rw [hcb, hy]; module
          rw [hyc]
          omega
      · have h1 : w (x + a • unit i) ≤ w (y + c • unit k) + 1 :=
          hlip _ _ (Or.inr ⟨j, k, b, c, Ne.symm hkj, hb, hc, by rw [hy]⟩)
        omega
  have hfk : ∀ k : Fin d,
      0 ≤ ((w (y + (1 : ℤ) • unit k) - w y) + (w (y + (-1 : ℤ) • unit k) - w y)) := by
    intro k
    have h1 := hnb k 1 (Or.inl rfl)
    have h2 := hnb k (-1) (Or.inr rfl)
    omega
  have hfi : 1 ≤ ((w (y + (1 : ℤ) • unit i) - w y) + (w (y + (-1 : ℤ) • unit i) - w y)) := by
    have h1 := hnb i 1 (Or.inl rfl)
    have h2 := hnb i (-1) (Or.inr rfl)
    rcases ha with rfl | rfl
    · have hyc : y + (-1 : ℤ) • unit i = x + b • unit j := by rw [hy]; module
      rw [hyc] at h2 ⊢
      omega
    · have hyc : y + (1 : ℤ) • unit i = x + b • unit j := by rw [hy]; module
      rw [hyc] at h1 ⊢
      omega
  have hfj : 1 ≤ ((w (y + (1 : ℤ) • unit j) - w y) + (w (y + (-1 : ℤ) • unit j) - w y)) := by
    have h1 := hnb j 1 (Or.inl rfl)
    have h2 := hnb j (-1) (Or.inr rfl)
    rcases hb with rfl | rfl
    · have hyc : y + (-1 : ℤ) • unit j = x + a • unit i := by rw [hy]; module
      rw [hyc] at h2 ⊢
      omega
    · have hyc : y + (1 : ℤ) • unit j = x + a • unit i := by rw [hy]; module
      rw [hyc] at h1 ⊢
      omega
  have h2 := assp_sum_ge_two hfk hij hfi hfj
  rw [← assp_lap_eq_sum] at h2
  have := hs_low y
  omega

theorem assp_unstable_propagate {s w : Site d → ℤ}
    (hs_low : ∀ x, 2 * (d : ℤ) - 2 ≤ s x)
    (hs_high : ∀ x, x ≠ 0 → s x ≤ 2 * (d : ℤ) - 1) (hs0 : s 0 ≤ 2 * (d : ℤ))
    (hmax : ∀ x, w x ≤ w 0) (hlip : assp_Lip w)
    (x y : Site d) (hxy : assp_Close x y) (heq : w x = w y + 1)
    (hun : 2 * (d : ℤ) ≤ s x + lap w x) :
    2 * (d : ℤ) ≤ s y + lap w y := by
  rcases hxy with ⟨i, a, ha, rfl⟩ | ⟨i, j, a, b, hij, ha, hb, rfl⟩
  · exfalso
    have := assp_stable_of_low_nbr hs_high hs0 hmax hlip x i ha (by omega)
    omega
  · exact assp_unstable_diag hs_low hs_high hs0 hmax hlip x i j hij ha hb heq hun

/-! ### `eq:induction3` and `eq:induction2` -/

/-- `eq:induction3` and `eq:induction2` of the paper, by induction on `t`, for the odometer of
any background `s` with `2d - 2 ≤ s`, `s ≤ 2d - 1` off the origin and `s 0 ≤ 2d`. -/
theorem assp_podo_inv {s : Site d → ℤ}
    (hs_low : ∀ x, 2 * (d : ℤ) - 2 ≤ s x)
    (hs_high : ∀ x, x ≠ 0 → s x ≤ 2 * (d : ℤ) - 1) (hs0 : s 0 ≤ 2 * (d : ℤ)) (t : ℕ) :
    (∀ x, podo s t x ≤ podo s t 0) ∧ assp_Lip (podo s t) := by
  induction t with
  | zero =>
    refine ⟨fun x => le_rfl, fun x y _ => ?_⟩
    simp [podo_zero]
  | succ t ih =>
    obtain ⟨hmax, hlip⟩ := ih
    refine ⟨fun x => ?_, fun x y hxy => ?_⟩
    · by_cases hx0 : x = 0
      · rw [hx0]
      · rw [podo_succ s t x, podo_succ s t 0]
        by_cases hlt : podo s t x < podo s t 0
        · split_ifs <;> omega
        · have heq : podo s t x = podo s t 0 := le_antisymm (hmax x) (not_lt.mp hlt)
          have hlap : lap (podo s t) x ≤ 0 := by
            rw [assp_lap_eq_sum]
            refine assp_sum_nonpos (fun k => ?_)
            have h1 := hmax (x + (1 : ℤ) • unit k)
            have h2 := hmax (x + (-1 : ℤ) • unit k)
            omega
          have hs := hs_high x hx0
          have hst : ¬ 2 * (d : ℤ) ≤ pconf s t x := by
            simp only [pconf]; omega
          rw [if_neg hst]
          split_ifs <;> omega
    · rw [podo_succ s t x, podo_succ s t y]
      by_cases hle : podo s t x ≤ podo s t y
      · split_ifs <;> omega
      · have heq : podo s t x = podo s t y + 1 := by
          have := hlip x y hxy
          omega
        by_cases hux : 2 * (d : ℤ) ≤ pconf s t x
        · have huy : 2 * (d : ℤ) ≤ pconf s t y :=
            assp_unstable_propagate hs_low hs_high hs0 hmax hlip x y hxy heq hux
          rw [if_pos hux, if_pos huy]
          omega
        · rw [if_neg hux]
          split_ifs <;> omega

/-! ### `eq:induction1` -/

/-- `eq:induction1`: the reachable set of the odometer of `s` is inside that of the `S`-frozen
odometer started at `w0`, when `s = η` off `S`, `w0 ≥ 1` on `S`, and the odometer of `s` is
Lipschitz at every time. -/
theorem assp_incl {s η w0 : Site d → ℤ} (S : Set (Site d))
    (hmatch : ∀ x, x ∉ S → s x = η x) (hw0nn : ∀ x, 0 ≤ w0 x) (hw0S : ∀ x ∈ S, 1 ≤ w0 x)
    (hlip : ∀ t, assp_Lip (podo s t)) (t : ℕ) :
    ∀ x, 0 < podo s t x → 0 < fodo S η w0 t x := by
  induction t with
  | zero => intro x hx; simp [podo_zero] at hx
  | succ t ih =>
    intro x hx
    by_cases hxS : x ∈ S
    · rw [fodo_of_mem S η w0 (t + 1) hxS]
      have := hw0S x hxS
      omega
    · rw [fodo_succ_of_notMem S η w0 t hxS]
      have hnn := fodo_nonneg S η w0 hw0nn t x
      by_cases hpos : 0 < fodo S η w0 t x
      · split_ifs <;> omega
      · have hf0 : fodo S η w0 t x = 0 := by omega
        have hp0 : podo s t x = 0 := by
          by_contra hne
          have := as_podo_nonneg s t x
          exact hpos (ih x (by omega))
        rw [podo_succ s t x, hp0] at hx
        have hun : 2 * (d : ℤ) ≤ pconf s t x := by
          by_contra hc
          rw [if_neg hc] at hx
          omega
        have hnb : ∀ y, (lattice d).Adj y x → podo s t y ≤ fodo S η w0 t y := by
          intro y hy
          have h1 : podo s t y ≤ podo s t x + 1 := hlip t y x (assp_Close_of_adj hy)
          have h2 := as_podo_nonneg s t y
          have h3 := fodo_nonneg S η w0 hw0nn t y
          by_cases hy0 : 0 < podo s t y
          · have := ih y hy0
            omega
          · omega
        have hsum := nbrSumZ_le_of_adj (podo s t) (fodo S η w0 t) x hnb
        have hc : 2 * (d : ℤ) ≤ fconf S η w0 t x := by
          simp only [pconf, lap, hp0, mul_zero, sub_zero, hmatch x hxS] at hun
          simp only [fconf, lap, hf0, mul_zero, sub_zero]
          omega
        rw [if_pos hc]
        omega

/-! ### The statement used by the proof of Proposition 4.1 -/

/-- `eq:induction_specialcase2` of the paper (`exploding.tex:1061-1063`): the reachable set of
`w_t` is inside that of `w̃_t`. -/
theorem assp_special (d : ℕ) (hd : 2 ≤ d) : ∀ η : Site d → ℤ, (∀ x, 2 * (d : ℤ) - 2 ≤ η x) →
    (∀ x, η x ≤ 2 * (d : ℤ) - 1) →
      ∀ t : ℕ, ∀ x : Site d, 0 < as_wOdo η t x → 0 < as_tildeW η t x := by
  intro η hlow hhigh
  have _ := hd
  classical
  have hz : (0 : Site d) ∈ as_tildeP η := Or.inl rfl
  have hs_low : ∀ x, 2 * (d : ℤ) - 2 ≤ as_sBackground η x := by
    intro x
    simp only [as_sBackground]
    split_ifs with hx
    · by_cases hx0 : x = 0
      · subst hx0; simp
      · rw [dirac_of_ne hx0]; omega
    · exact hlow x
  have hs_high : ∀ x, x ≠ 0 → as_sBackground η x ≤ 2 * (d : ℤ) - 1 := by
    intro x hx0
    simp only [as_sBackground]
    split_ifs with hx
    · rw [dirac_of_ne hx0]; omega
    · exact hhigh x
  have hs0 : as_sBackground η 0 ≤ 2 * (d : ℤ) := by
    simp [as_sBackground, hz]
  have hmatch : ∀ x, x ∉ as_tildeP η → as_sBackground η x = η x := by
    intro x hx
    simp [as_sBackground, hx]
  intro t x hx
  have hinv := fun t => (assp_podo_inv hs_low hs_high hs0 t).2
  exact assp_incl (as_tildeP η) hmatch
    (w0 := fun x => if x ∈ as_tildeP η then (1 : ℤ) else 0)
    (fun x => by split_ifs <;> omega) (fun x hx => by simp [hx]) hinv t x hx
