/-
The parts of the proof of `theorem:counterexample` of `paper/exploding.tex`
Section 6 that reduce to the Step 1 relay / Step 3'-stacking machinery already
proved in `Exploding/Support/SubRelay.lean`, together with the real-analysis
assembly of `T(n)/n`.  The genuinely new Step 3-4 material (the reflected
cylinder front) enters only through the explicit hypotheses `hSlow2D`,
`hLow` and `hBdd`; the frozen statement discharges those with `sorry`.
-/
import Exploding.Support.SubRelay

namespace Exploding

open LatticeProb Filter

/-- The background fails `η ≥ 2d - 2` at the origin, where it is `2d - 3`. -/
theorem ce_not_ge (d : ℕ) (_hd : 2 ≤ d) :
    ¬ ∀ x : Site d, 2 * (d : ℤ) - 2 ≤ ceEta d x := by
  intro h
  have h0 := h 0
  have h0d : 0 < d := by omega
  have h1d : 1 < d := by omega
  have hce : ceEta d (0 : Site d) = 2 * ((d : ℤ) - 2) + zeta1 0 0 := by
    simp [ceEta, h0d, h1d]
  have hz : zeta1 0 0 = 1 := by unfold zeta1; norm_num
  rw [hce, hz] at h0
  linarith

/-- Step 3' of `exploding.tex:1767-1790`: the `d`-dimensional odometer is
dominated by the 2D odometer of the projection. -/
theorem ce_stack_le_2D (d : ℕ) (hd : 2 ≤ d) (t : ℕ) (x : Site d) :
    podo (explodingPile (ceEta d)) t x ≤
      podo (explodingPile (ceEta 2)) t
        (fun i : Fin 2 => if (i : ℕ) = 0 then x ⟨0, by omega⟩ else x ⟨1, by omega⟩) := by
  induction t generalizing x with
  | zero => simp
  | succ t ih => exact aux_ce_stack_le_2D_step d hd t ih x

/-- Steps 3-4, lifted from the 2D bound: the slow bound `12n` at `(3+8n)e₁`.
The 2D bound is the explicit hypothesis `hSlow2D`; `hFin` supplies the value
of the (finite) `d`-dimensional arrival time. -/
theorem ce_slow (d : ℕ) (hd : 2 ≤ d)
    (hSlow2D : ∀ n : ℕ, ∃ m : ℕ,
      arrival (ceEta 2) (((3 + 8 * n : ℕ) : ℤ) • e1 2) = (m : ℕ∞) ∧ 12 * n ≤ m)
    (hFin : ∀ n : ℕ, arrival (ceEta d) ((n : ℤ) • e1 d) ≠ ⊤) (n : ℕ) :
    ∃ m : ℕ, arrival (ceEta d) (((3 + 8 * n : ℕ) : ℤ) • e1 d) = (m : ℕ∞) ∧ 12 * n ≤ m := by
  have h0 : 0 < d := (by omega)
  have h1 : 1 < d := (by omega)
  obtain ⟨m2, hm2, h12⟩ := hSlow2D n
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (hFin (3 + 8 * n))
  refine ⟨m, hm.symm, ?_⟩
  have hproj : (fun i : Fin 2 => if (i : ℕ) = 0 then (((3 + 8 * n : ℕ) : ℤ) • e1 d) ⟨0, h0⟩ else (((3 + 8 * n : ℕ) : ℤ) • e1 d) ⟨1, h1⟩) = ((3 + 8 * n : ℕ) : ℤ) • e1 2 := funext (fun i => (by fin_cases i <;> simp [e1]))
  have hsub : arrival (ceEta 2) (((3 + 8 * n : ℕ) : ℤ) • e1 2) ≤ arrival (ceEta d) (((3 + 8 * n : ℕ) : ℤ) • e1 d) := (by
    simp only [arrival]
    refine sInf_le_sInf ?_
    rintro t ⟨k, rfl, hk, hpos⟩
    have hle := ce_stack_le_2D d hd k (((3 + 8 * n : ℕ) : ℤ) • e1 d)
    rw [hproj] at hle
    exact ⟨k, rfl, hk, lt_of_lt_of_le hpos hle⟩)
  rw [hm2, ← hm] at hsub
  have hle : m2 ≤ m := WithTop.coe_le_coe.mp hsub
  omega

/-- The high-type points `n ≡ 1, 2 (mod 4)` are reached directly by the relay
row; the low-type points `n ≡ 0, 3 (mod 4)` are the explicit hypothesis
`hLow`.  Together they give finiteness of every arrival time. -/
theorem ce_arrival_finite_of_low (d : ℕ) (hd : 2 ≤ d)
    (hLow : ∀ n : ℕ, n % 4 = 0 ∨ n % 4 = 3 →
      arrival (ceEta d) ((n : ℤ) • e1 d) ≠ ⊤)
    (n : ℕ) : arrival (ceEta d) ((n : ℤ) • e1 d) ≠ ⊤ := by
  have htoNat : ((n : ℤ)).toNat = n := by simp
  rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with h0 | h1 | h2 | h3
  · exact hLow n (Or.inl h0)
  · have hpos := aux_ce_row0_lands d hd (n : ℤ) (Or.inl (by exact_mod_cast h1)) (Nat.cast_nonneg n)
    rw [htoNat] at hpos
    exact aux_ce_arrival_finite_of_pos d hd n (n + 3) (by omega) hpos
  · have hpos := aux_ce_row0_lands d hd (n : ℤ) (Or.inr (by exact_mod_cast h2)) (Nat.cast_nonneg n)
    rw [htoNat] at hpos
    exact aux_ce_arrival_finite_of_pos d hd n (n + 3) (by omega) hpos
  · exact hLow n (Or.inr h3)

/-- `T(n)/n → 1` along the fast subsequence, giving `liminf = 1`. -/
theorem ce_liminf (d : ℕ) (hd : 2 ≤ d)
    (hFin : ∀ n : ℕ, arrival (ceEta d) ((n : ℤ) • e1 d) ≠ ⊤) :
    liminf (fun n : ℕ => ((arrival (ceEta d) ((n : ℤ) • e1 d)).toNat : ℝ) / (n : ℝ)) atTop = 1 := by
  have hbase : ∀ n : ℕ, 1 ≤ n →
      (1:ℝ) ≤ ((arrival (ceEta d) ((n : ℤ) • e1 d)).toNat : ℝ) / (n : ℝ) :=
    fun n hn => (by
      rw [one_le_div (by exact_mod_cast (by omega : (0 : ℕ) < n))]
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (hFin n)
      have hnm : n ≤ m := aux_ce_speed d hd n m hm.symm
      rw [← hm, ENat.toNat_coe]
      exact_mod_cast hnm)
  have hup : ∀ k : ℕ,
      ((arrival (ceEta d) (((4 * k + 1 : ℕ) : ℤ) • e1 d)).toNat : ℝ) / (((4 * k + 1 : ℕ)) : ℝ)
        ≤ (((4 * k + 4 : ℕ)) : ℝ) / (((4 * k + 1 : ℕ)) : ℝ) :=
    fun k => (by
      obtain ⟨m, hm, hml⟩ := aux_ce_fast d hd k
      rw [hm, ENat.toNat_coe]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hml) (by positivity))
  have hSbd : BddAbove {a : ℝ | ∀ᶠ n : ℕ in atTop,
      a ≤ ((arrival (ceEta d) ((n : ℤ) • e1 d)).toNat : ℝ) / (n : ℝ)} := (by
    refine ⟨4, fun a ha => ?_⟩
    simp only [Set.mem_setOf_eq] at ha
    rw [Filter.eventually_atTop] at ha
    obtain ⟨N, hN⟩ := ha
    have hA := hN (4 * N + 1) (by omega)
    have hB := hup N
    have hC : (((4 * N + 4 : ℕ)) : ℝ) / (((4 * N + 1 : ℕ)) : ℝ) ≤ 4 := (by
      rw [div_le_iff₀ (by positivity)]
      push_cast
      linarith)
    linarith)
  have hSne : ({a : ℝ | ∀ᶠ n : ℕ in atTop,
      a ≤ ((arrival (ceEta d) ((n : ℤ) • e1 d)).toNat : ℝ) / (n : ℝ)}).Nonempty :=
    ⟨0, (by
      simp only [Set.mem_setOf_eq]
      exact Filter.Eventually.of_forall (fun n => by positivity))⟩
  have hub : sSup {a : ℝ | ∀ᶠ n : ℕ in atTop,
      a ≤ ((arrival (ceEta d) ((n : ℤ) • e1 d)).toNat : ℝ) / (n : ℝ)} ≤ 1 := (by
    refine csSup_le hSne fun a ha => ?_
    simp only [Set.mem_setOf_eq] at ha
    by_contra hcon
    push Not at hcon
    rw [Filter.eventually_atTop] at ha
    obtain ⟨N, hN⟩ := ha
    obtain ⟨k, hk⟩ : ∃ k : ℕ, max ((4 - a) / (4 * (a - 1))) (N : ℝ) < (k : ℝ) := exists_nat_gt _
    have hNk : N ≤ 4 * k + 1 := (by
      have h1 : (N : ℝ) < (k : ℝ) := lt_of_le_of_lt (le_max_right _ _) hk
      have h2 : N < k := (by exact_mod_cast h1)
      omega)
    have hky : (4 - a) / (4 * (a - 1)) < (k : ℝ) := lt_of_le_of_lt (le_max_left _ _) hk
    have h4 : (0 : ℝ) < 4 * (a - 1) := (by linarith)
    have hkey : 4 - a < (k : ℝ) * (4 * (a - 1)) := (div_lt_iff₀ h4).mp hky
    have hratio : (((4 * k + 4 : ℕ)) : ℝ) / (((4 * k + 1 : ℕ)) : ℝ) < a := (by
      rw [div_lt_iff₀ (by positivity)]
      push_cast
      nlinarith [hkey])
    have h1' := hN (4 * k + 1) hNk
    have h2' := hup k
    linarith)
  have hlb : (1:ℝ) ≤ sSup {a : ℝ | ∀ᶠ n : ℕ in atTop,
      a ≤ ((arrival (ceEta d) ((n : ℤ) • e1 d)).toNat : ℝ) / (n : ℝ)} := (by
    refine le_csSup hSbd ?_
    simp only [Set.mem_setOf_eq]
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hbase n hn)
  rw [Filter.liminf_eq]
  exact le_antisymm hub hlb

/-- `T(3+8n)/(3+8n) ≥ 12n/(3+8n) → 3/2` gives `limsup ≥ 3/2`.  `hSlow` is the
slow bound (conditional on the cylinder front) and `hBdd` makes the defining
`sInf` of `Filter.limsup_eq` nonempty. -/
theorem ce_limsup (d : ℕ) (_hd : 2 ≤ d)
    (hSlow : ∀ n : ℕ, ∃ m : ℕ,
      arrival (ceEta d) (((3 + 8 * n : ℕ) : ℤ) • e1 d) = (m : ℕ∞) ∧ 12 * n ≤ m)
    (hBdd : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      ((arrival (ceEta d) ((n : ℤ) • e1 d)).toNat : ℝ) / (n : ℝ) ≤ C) :
    3 / 2 ≤ limsup (fun n : ℕ => ((arrival (ceEta d) ((n : ℤ) • e1 d)).toNat : ℝ) / (n : ℝ)) atTop := by
  obtain ⟨C, hC⟩ := hBdd
  rw [Filter.limsup_eq]
  refine le_csInf ⟨C, hC⟩ ?_
  intro a ha
  by_contra hcon
  push Not at hcon
  simp only [Set.mem_setOf_eq] at ha
  rw [Filter.eventually_atTop] at ha
  obtain ⟨N, hN⟩ := ha
  obtain ⟨k, hk⟩ : ∃ k : ℕ, max ((3 * a) / (12 - 8 * a)) (N : ℝ) < (k : ℝ) := exists_nat_gt _
  have hNk : N ≤ 3 + 8 * k := by
    have h1 : (N : ℝ) < (k : ℝ) := lt_of_le_of_lt (le_max_right _ _) hk
    have h2 : N < k := by exact_mod_cast h1
    omega
  have hky : (3 * a) / (12 - 8 * a) < (k : ℝ) := lt_of_le_of_lt (le_max_left _ _) hk
  have h4 : (0 : ℝ) < 12 - 8 * a := by linarith
  have hkey : 3 * a < (k : ℝ) * (12 - 8 * a) := (div_lt_iff₀ h4).mp hky
  obtain ⟨m, hm, hml⟩ := hSlow k
  have hmlr : (12 * k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hml
  have hratio : a < (m : ℝ) / (((3 + 8 * k : ℕ)) : ℝ) := by
    rw [lt_div_iff₀ (by positivity)]
    push_cast
    nlinarith [hkey, hmlr]
  have h1' := hN (3 + 8 * k) hNk
  rw [hm, ENat.toNat_coe] at h1'
  linarith [hratio]

/-- The background is explosive: `η + 3δ₀` is not stabilizable, so it is not
robust. -/
theorem ce_explosive (d : ℕ) (hd : 2 ≤ d) : Explosive (ceEta d) := by
  intro hrob
  exact aux_ce_not_stab3_direct d hd (by simpa using hrob 3 (by norm_num))

/-- The cylinder neighbour sum is additive. -/
theorem cylNbrSum_add (u v : ℤ × Fin 4 → ℤ) (x : ℤ × Fin 4) :
    cylNbrSum (fun y => u y + v y) x = cylNbrSum u x + cylNbrSum v x := by
  unfold cylNbrSum
  split <;> ring

/-- The cylinder neighbour sum is monotone. -/
theorem cylNbrSum_mono {u v : ℤ × Fin 4 → ℤ} (h : ∀ y, u y ≤ v y) (x : ℤ × Fin 4) :
    cylNbrSum u x ≤ cylNbrSum v x := by
  unfold cylNbrSum
  have h1 : (if x.1 = 0 then u (1, x.2) + u x else u (x.1 - 1, x.2) + u (x.1 + 1, x.2))
      ≤ (if x.1 = 0 then v (1, x.2) + v x else v (x.1 - 1, x.2) + v (x.1 + 1, x.2)) := by
    split <;> linarith [h (1, x.2), h x, h (x.1 - 1, x.2), h (x.1 + 1, x.2)]
  exact add_le_add h1 (add_le_add (h _) (h _))

/-- The paper's elementary comparison `Σ v_t ≤ Σ(w_t + ũ)` in Laplacian form. -/
theorem cylLap_le_of_le_add {v w u : ℤ × Fin 4 → ℤ} (h : ∀ y, v y ≤ w y + u y)
    (x : ℤ × Fin 4) :
    cylLap v x ≤ cylLap w x + cylLap u x + 4 * (w x + u x - v x) := by
  have hsum := cylNbrSum_mono h x
  rw [cylNbrSum_add w u x] at hsum
  unfold cylLap
  linarith

/-- **Step 3b of `exploding.tex:1506-1513`** (`eq:topple_compare_induc`), in the
corrected general form needed here: for an arbitrary cylinder background
`ζ` and `ũ ≥ 0`, with `ζ' := ζ + Δũ`, the odometer for `ζ` is dominated by the
odometer for `ζ'` plus `ũ`.  The displayed tables of `exploding.tex` are used only
in Step 4. -/
theorem ce_step3b (ζ u : ℤ × Fin 4 → ℤ) (hu : ∀ x, 0 ≤ u x) :
    ∀ t : ℕ, ∀ x : ℤ × Fin 4,
      cylOdo ζ t x ≤ cylOdo (fun y => ζ y + cylLap u y) t x + u x := by
  intro t
  induction t with
  | zero => intro x; simp [cylOdo]; exact hu x
  | succ t ih =>
    intro x
    rw [cylOdo_succ ζ t x, cylOdo_succ (fun y => ζ y + cylLap u y) t x]
    by_cases hlt : cylOdo ζ t x + 1 ≤ cylOdo (fun y => ζ y + cylLap u y) t x + u x
    · have h1 : cylOdo ζ t x + (if 4 ≤ ζ x + cylLap (cylOdo ζ t) x then 1 else 0)
          ≤ cylOdo ζ t x + 1 := by split <;> omega
      have h2 : cylOdo (fun y => ζ y + cylLap u y) t x + u x
          ≤ cylOdo (fun y => ζ y + cylLap u y) t x
            + (if 4 ≤ (fun y => ζ y + cylLap u y) x
                + cylLap (cylOdo (fun y => ζ y + cylLap u y) t) x then 1 else 0)
            + u x := by split <;> omega
      linarith
    · have heq : cylOdo ζ t x = cylOdo (fun y => ζ y + cylLap u y) t x + u x := by
        have := ih x; omega
      by_cases hf : 4 ≤ ζ x + cylLap (cylOdo ζ t) x
      · have hlap := cylLap_le_of_le_add ih x
        have hf' : 4 ≤ (fun y => ζ y + cylLap u y) x
            + cylLap (cylOdo (fun y => ζ y + cylLap u y) t) x := by
          show 4 ≤ (ζ x + cylLap u x) + cylLap (cylOdo (fun y => ζ y + cylLap u y) t) x
          linarith
        rw [if_pos hf, if_pos hf']
        omega
      · rw [if_neg hf]
        have hge : 0 ≤ (if 4 ≤ (fun y => ζ y + cylLap u y) x
            + cylLap (cylOdo (fun y => ζ y + cylLap u y) t) x then (1 : ℤ) else 0) := by
          split <;> norm_num
        omega

/-! ### Corrected cylinder projection (fixes the `SubRelay.cylProj` bug)

`SubRelay.cylProj` folds `x₂` through `Int.toNat`, so `x₂ = -1` lands in
column `0` instead of `3`; `cylNbrSum_cylProj` is then false for a
non-constant 4-periodic `v` (e.g. `a = 1`, `b = 0`).  The copies below fold
`x₂` through `Int.emod · 4`, and `ce_cylNbrSum_cylProj` is the corrected
identity.
-/

/-- `Int.toNat ((n+1) % 4) = (Int.toNat (n % 4) + 1) % 4`. -/
theorem ce_emod_succ (n : ℤ) :
    Int.toNat ((n + 1) % 4) = (Int.toNat (n % 4) + 1) % 4 := by
  have h1 : 0 ≤ n % 4 := Int.emod_nonneg n (by norm_num)
  have hmod : (n + 1) % 4 = (n % 4 + 1) % 4 := by rw [Int.add_emod]; norm_num
  rw [hmod]
  have hnat : ((n % 4).toNat : ℤ) = n % 4 := Int.toNat_of_nonneg h1
  have hcase : (n % 4).toNat = 0 ∨ (n % 4).toNat = 1 ∨
      (n % 4).toNat = 2 ∨ (n % 4).toNat = 3 := by
    have h2 : n % 4 < 4 := Int.emod_lt_of_pos n (by norm_num); omega
  rcases hcase with h | h | h | h
  · have : n % 4 = 0 := by rw [← hnat]; norm_num [h]
    rw [this]; decide
  · have : n % 4 = 1 := by rw [← hnat]; norm_num [h]
    rw [this]; decide
  · have : n % 4 = 2 := by rw [← hnat]; norm_num [h]
    rw [this]; decide
  · have : n % 4 = 3 := by rw [← hnat]; norm_num [h]
    rw [this]; decide

/-- `Int.toNat ((n-1) % 4) = (Int.toNat (n % 4) + 3) % 4`. -/
theorem ce_emod_pred (n : ℤ) :
    Int.toNat ((n - 1) % 4) = (Int.toNat (n % 4) + 3) % 4 := by
  have h1 : 0 ≤ n % 4 := Int.emod_nonneg n (by norm_num)
  have hmod : (n - 1) % 4 = (n % 4 - 1) % 4 := by rw [Int.sub_emod]; norm_num
  rw [hmod]
  have hnat : ((n % 4).toNat : ℤ) = n % 4 := Int.toNat_of_nonneg h1
  have hcase : (n % 4).toNat = 0 ∨ (n % 4).toNat = 1 ∨
      (n % 4).toNat = 2 ∨ (n % 4).toNat = 3 := by
    have h2 : n % 4 < 4 := Int.emod_lt_of_pos n (by norm_num); omega
  rcases hcase with h | h | h | h
  · have : n % 4 = 0 := by rw [← hnat]; norm_num [h]
    rw [this]; decide
  · have : n % 4 = 1 := by rw [← hnat]; norm_num [h]
    rw [this]; decide
  · have : n % 4 = 2 := by rw [← hnat]; norm_num [h]
    rw [this]; decide
  · have : n % 4 = 3 := by rw [← hnat]; norm_num [h]
    rw [this]; decide

/-- The corrected fold `Site 2 → ℤ × Fin 4`, using `Int.emod 4` so that
negative `x₂` fold to the right torus column. -/
def ce_cylProj (x : Site 2) : ℤ × Fin 4 :=
  (x ⟨0, by norm_num⟩, Fin.ofNat 4 (Int.toNat (x ⟨1, by norm_num⟩ % 4)))

/-- `Fin 4` successor commutes with the `emod`-fold. -/
theorem ce_fin4_emod_succ (n : ℤ) :
    Fin.ofNat 4 (Int.toNat ((n + 1) % 4))
      = Fin.ofNat 4 (Int.toNat (n % 4)) + 1 := by
  apply Fin.ext
  rw [Fin.val_add, Fin.val_one, Fin.val_ofNat, Fin.val_ofNat]
  have hlt : Int.toNat ((n + 1) % 4) < 4 := by
    have := Int.emod_lt_of_pos (n + 1) (by norm_num : (0:ℤ) < 4); omega
  have hlt2 : Int.toNat (n % 4) < 4 := by
    have := Int.emod_lt_of_pos n (by norm_num : (0:ℤ) < 4); omega
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt2]
  exact ce_emod_succ n

/-- `Fin 4` predecessor commutes with the `emod`-fold. -/
theorem ce_fin4_emod_pred (n : ℤ) :
    Fin.ofNat 4 (Int.toNat ((n - 1) % 4))
      = Fin.ofNat 4 (Int.toNat (n % 4)) - 1 := by
  apply Fin.ext
  rw [Fin.val_sub, Fin.val_one, Fin.val_ofNat, Fin.val_ofNat]
  have hlt : Int.toNat ((n - 1) % 4) < 4 := by
    have := Int.emod_lt_of_pos (n - 1) (by norm_num : (0:ℤ) < 4); omega
  rw [Nat.mod_eq_of_lt hlt]
  have hval : Int.toNat ((n - 1) % 4)
      = (Int.toNat (n % 4) + 3) % 4 := ce_emod_pred n
  rw [hval]
  omega

theorem ce_cylProj_add_one (x : Site 2) :
    ce_cylProj (x + unit (⟨1, by norm_num⟩ : Fin 2))
      = ((ce_cylProj x).1, (ce_cylProj x).2 + 1) := by
  refine Prod.ext ?_ ?_
  · simp [ce_cylProj, Pi.add_apply, unit]
  · show (ce_cylProj (x + unit (⟨1, by norm_num⟩ : Fin 2))).2
        = (ce_cylProj x).2 + 1
    unfold ce_cylProj
    rw [show (x + unit (⟨1, by norm_num⟩ : Fin 2)) ⟨1, by norm_num⟩
        = x ⟨1, by norm_num⟩ + 1 by simp [Pi.add_apply, unit]]
    exact ce_fin4_emod_succ (x ⟨1, by norm_num⟩)

theorem ce_cylProj_sub_one (x : Site 2) :
    ce_cylProj (x - unit (⟨1, by norm_num⟩ : Fin 2))
      = ((ce_cylProj x).1, (ce_cylProj x).2 - 1) := by
  refine Prod.ext ?_ ?_
  · simp [ce_cylProj, Pi.sub_apply, unit]
  · show (ce_cylProj (x - unit (⟨1, by norm_num⟩ : Fin 2))).2
        = (ce_cylProj x).2 - 1
    unfold ce_cylProj
    rw [show (x - unit (⟨1, by norm_num⟩ : Fin 2)) ⟨1, by norm_num⟩
        = x ⟨1, by norm_num⟩ - 1 by simp [Pi.sub_apply, unit]]
    exact ce_fin4_emod_pred (x ⟨1, by norm_num⟩)

theorem ce_cylProj_add_zero (x : Site 2) :
    ce_cylProj (x + unit (⟨0, by norm_num⟩ : Fin 2))
      = ((ce_cylProj x).1 + 1, (ce_cylProj x).2) := by
  refine Prod.ext ?_ ?_ <;> simp [ce_cylProj, Pi.add_apply, unit]

theorem ce_cylProj_sub_zero (x : Site 2) :
    ce_cylProj (x - unit (⟨0, by norm_num⟩ : Fin 2))
      = ((ce_cylProj x).1 - 1, (ce_cylProj x).2) := by
  refine Prod.ext ?_ ?_ <;> simp [ce_cylProj, Pi.sub_apply, unit]

/-- **Corrected `cylNbrSum_cylProj`.**  For the `Int.emod`-fold `ce_cylProj`,
the cylinder neighbour sum at the projection of `x` equals the 2D neighbour
sum, for `x₁ ≥ 1` (away from the reflecting boundary) and `v` agreeing with
the fold `u` on the half-plane. -/
theorem ce_cylNbrSum_cylProj (u : ℤ × Fin 4 → ℤ) (v : Site 2 → ℤ)
    (hfold : ∀ y : Site 2, 0 ≤ y ⟨0, by norm_num⟩ → u (ce_cylProj y) = v y)
    (x : Site 2) (hx : 1 ≤ x ⟨0, by norm_num⟩) :
    cylNbrSum u (ce_cylProj x) = nbrSumZ v x := by
  unfold cylNbrSum nbrSumZ
  rw [Fin.sum_univ_two]
  have hx0 : ¬ (ce_cylProj x).1 = 0 := by
    unfold ce_cylProj
    omega
  rw [if_neg hx0]
  have hs0 : 0 ≤ (x - unit (⟨0, by norm_num⟩ : Fin 2)) ⟨0, by norm_num⟩ := by
    simp only [Pi.sub_apply, LatticeProb.unit, Pi.single_eq_same]
    omega
  have h1 : u ((ce_cylProj x).1 - 1, (ce_cylProj x).2)
      = v (x - unit (⟨0, by norm_num⟩ : Fin 2)) := by
    rw [← hfold (x - unit (⟨0, by norm_num⟩ : Fin 2)) hs0]
    congr 1
    exact (ce_cylProj_sub_zero x).symm
  have ha0 : 0 ≤ (x + unit (⟨0, by norm_num⟩ : Fin 2)) ⟨0, by norm_num⟩ := by
    simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_same]
    omega
  have h2 : u ((ce_cylProj x).1 + 1, (ce_cylProj x).2)
      = v (x + unit (⟨0, by norm_num⟩ : Fin 2)) := by
    rw [← hfold (x + unit (⟨0, by norm_num⟩ : Fin 2)) ha0]
    congr 1
    exact (ce_cylProj_add_zero x).symm
  have ha1 : 0 ≤ (x + unit (⟨1, by norm_num⟩ : Fin 2)) ⟨0, by norm_num⟩ := by
    simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_of_ne
      (show (⟨0, by norm_num⟩ : Fin 2) ≠ ⟨1, by norm_num⟩ from
        fun hc => absurd (congrArg Fin.val hc) (by decide))]
    omega
  have h3 : u ((ce_cylProj x).1, (ce_cylProj x).2 + 1)
      = v (x + unit (⟨1, by norm_num⟩ : Fin 2)) := by
    rw [← hfold (x + unit (⟨1, by norm_num⟩ : Fin 2)) ha1]
    congr 1
    exact (ce_cylProj_add_one x).symm
  have hs1 : 0 ≤ (x - unit (⟨1, by norm_num⟩ : Fin 2)) ⟨0, by norm_num⟩ := by
    simp only [Pi.sub_apply, LatticeProb.unit, Pi.single_eq_of_ne
      (show (⟨0, by norm_num⟩ : Fin 2) ≠ ⟨1, by norm_num⟩ from
        fun hc => absurd (congrArg Fin.val hc) (by decide))]
    omega
  have h4 : u ((ce_cylProj x).1, (ce_cylProj x).2 - 1)
      = v (x - unit (⟨1, by norm_num⟩ : Fin 2)) := by
    rw [← hfold (x - unit (⟨1, by norm_num⟩ : Fin 2)) hs1]
    congr 1
    exact (ce_cylProj_sub_one x).symm
  rw [h1, h2, h3, h4]
  abel

end Exploding
