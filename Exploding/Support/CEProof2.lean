/-
Step 3-4 of `theorem:counterexample` (`exploding.tex:1443-1747`): the reflected
cylinder process and the pulsating front.

The paper starts from the all-`ζ₁` tiling, increments the background to the
cylinder tiling `ζ` (a `4` at the first block's `(0,3)`), and reflects it
across `x₁ = -1/2`.  This file builds the corrected cylinder objects
(`ce2_…`, prefix `ce2_`) that the reduction rests on.
-/
import Exploding.Support.CEProof

namespace Exploding

open LatticeProb Filter

/-! ### The reflection and the period-four translation on `Site 2` -/

/-- Reflection of `Site 2` about `x₁ = -1/2`: `x₁ ↦ -1 - x₁`. -/
def ce2_reflect (x : Site 2) : Site 2 :=
  fun i => if (i : ℕ) = 0 then -1 - x ⟨0, by norm_num⟩ else x ⟨1, by norm_num⟩

/-- Translation by `4` in the `x₂` direction. -/
def ce2_shift (x : Site 2) : Site 2 := x + 4 • e2 2

theorem ce2_reflect_invol (x : Site 2) : ce2_reflect (ce2_reflect x) = x := by
  funext i
  fin_cases i <;> simp [ce2_reflect]

theorem ce2_reflect_add_zero (x : Site 2) :
    ce2_reflect (x + unit (⟨0, by norm_num⟩ : Fin 2))
      = ce2_reflect x - unit (⟨0, by norm_num⟩ : Fin 2) := by
  funext i
  fin_cases i
  · simp [ce2_reflect, unit, Pi.add_apply, Pi.sub_apply]; ring
  · simp [ce2_reflect, unit, Pi.add_apply, Pi.sub_apply]

theorem ce2_reflect_sub_zero (x : Site 2) :
    ce2_reflect (x - unit (⟨0, by norm_num⟩ : Fin 2))
      = ce2_reflect x + unit (⟨0, by norm_num⟩ : Fin 2) := by
  funext i
  fin_cases i
  · simp [ce2_reflect, unit, Pi.add_apply, Pi.sub_apply]; ring
  · simp [ce2_reflect, unit, Pi.add_apply, Pi.sub_apply]

theorem ce2_reflect_add_one (x : Site 2) :
    ce2_reflect (x + unit (⟨1, by norm_num⟩ : Fin 2))
      = ce2_reflect x + unit (⟨1, by norm_num⟩ : Fin 2) := by
  funext i
  fin_cases i
  · simp [ce2_reflect, unit, Pi.add_apply]
  · simp [ce2_reflect, unit, Pi.add_apply]

theorem ce2_reflect_sub_one (x : Site 2) :
    ce2_reflect (x - unit (⟨1, by norm_num⟩ : Fin 2))
      = ce2_reflect x - unit (⟨1, by norm_num⟩ : Fin 2) := by
  funext i
  fin_cases i
  · simp [ce2_reflect, unit, Pi.sub_apply]
  · simp [ce2_reflect, unit, Pi.sub_apply]

/-- The neighbour sum is invariant under the reflection. -/
theorem ce2_nbrSumZ_reflect (v : Site 2 → ℤ) (x : Site 2) :
    nbrSumZ (fun y => v (ce2_reflect y)) x = nbrSumZ v (ce2_reflect x) := by
  rw [nbrSumZ, nbrSumZ]
  apply Finset.sum_congr rfl
  intro i _
  fin_cases i
  · rw [ce2_reflect_add_zero, ce2_reflect_sub_zero]; ring
  · rw [ce2_reflect_add_one, ce2_reflect_sub_one]

theorem ce2_shift_add (x : Site 2) (i : Fin 2) :
    ce2_shift (x + unit i) = ce2_shift x + unit i := by
  funext j
  simp only [ce2_shift, Pi.add_apply, Pi.smul_apply]
  ring

theorem ce2_shift_sub (x : Site 2) (i : Fin 2) :
    ce2_shift (x - unit i) = ce2_shift x - unit i := by
  funext j
  simp only [ce2_shift, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring

/-- The neighbour sum is invariant under the period-four translation. -/
theorem ce2_nbrSumZ_shift (v : Site 2 → ℤ) (x : Site 2) :
    nbrSumZ (fun y => v (ce2_shift y)) x = nbrSumZ v (ce2_shift x) := by
  rw [nbrSumZ, nbrSumZ]
  apply Finset.sum_congr rfl
  intro i _
  rw [ce2_shift_add, ce2_shift_sub]

/-! ### Symmetry and periodicity of the odometer -/

/-- The parallel odometer inherits the reflection symmetry of the background. -/
theorem ce2_podo_reflect (s0 : Site 2 → ℤ) (hs : ∀ x, s0 (ce2_reflect x) = s0 x) :
    ∀ t x, podo s0 t (ce2_reflect x) = podo s0 t x := by
  intro t
  induction t with
  | zero => intro x; simp
  | succ t ih =>
    intro x
    have hlap : lap (podo s0 t) (ce2_reflect x) = lap (podo s0 t) x := by
      rw [lap_eq, lap_eq]
      have h1 := ce2_nbrSumZ_reflect (podo s0 t) x
      have hfun : (fun y => podo s0 t (ce2_reflect y)) = podo s0 t := funext ih
      rw [hfun] at h1
      rw [h1, ih x]
    have hconf : pconf s0 t (ce2_reflect x) = pconf s0 t x := by
      simp only [pconf]
      rw [hs x, hlap]
    rw [podo_succ, podo_succ, ih x, hconf]

/-- The parallel odometer inherits the period-four translation symmetry of the
background. -/
theorem ce2_podo_period (s0 : Site 2 → ℤ) (hper : ∀ x, s0 (ce2_shift x) = s0 x) :
    ∀ t x, podo s0 t (ce2_shift x) = podo s0 t x := by
  intro t
  induction t with
  | zero => intro x; simp
  | succ t ih =>
    intro x
    have hlap : lap (podo s0 t) (ce2_shift x) = lap (podo s0 t) x := by
      rw [lap_eq, lap_eq]
      have h1 := ce2_nbrSumZ_shift (podo s0 t) x
      have hfun : (fun y => podo s0 t (ce2_shift y)) = podo s0 t := funext ih
      rw [hfun] at h1
      rw [h1, ih x]
    have hconf : pconf s0 t (ce2_shift x) = pconf s0 t x := by
      simp only [pconf]
      rw [hper x, hlap]
    rw [podo_succ, podo_succ, ih x, hconf]

/-! ### The folded cylinder background and the reflected process

`ce2_cyl s0` is the cylinder background obtained by folding a 2D background along
the `x₂ mod 4` classes.  `ce2_cylOdo_eq_podo` identifies the cylinder odometer
of the folded background with the true 2D odometer on the half-plane `x₁ ≥ 0`,
which is the paper's reduction ("Lemma 2.3 in [bou2020dynamic]"). -/

/-- The point `(a,b)` of `Site 2`, with `b` a natural representative. -/
def ce2_pt (a : ℤ) (b : ℕ) : Site 2 := fun i => if (i : ℕ) = 0 then a else (b : ℤ)

/-- The representative of `x` with `x₂` reduced mod `4`. -/
def ce2_mod (x : Site 2) : Site 2 :=
  ce2_pt (x ⟨0, by norm_num⟩) (Int.toNat (x ⟨1, by norm_num⟩ % 4))

theorem ce2_mod_add_zsmul (x : Site 2) :
    ce2_mod x + (x ⟨1, by norm_num⟩ / 4) • (4 • e2 2) = x := by
  funext i
  fin_cases i
  · simp [ce2_mod, ce2_pt, e2]
  · simp only [ce2_mod, ce2_pt, Pi.add_apply, Pi.smul_apply, e2, smul_eq_mul]
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num : (4:ℤ) ≠ 0))]
    have h := Int.emod_add_mul_ediv (x ⟨1, by norm_num⟩) 4
    rw [mul_comm] at h
    exact h

/-- A `4`-periodic function depends only on the `mod 4` representative. -/
theorem ce2_periodic_reduce {α : Type*} (f : Site 2 → α)
    (hf : ∀ x, f (ce2_shift x) = f x) (x : Site 2) :
    f x = f (ce2_mod x) := by
  have hper : Function.Periodic f (4 • e2 2) := hf
  have h := (hper.zsmul (x ⟨1, by norm_num⟩ / 4)) (ce2_mod x)
  rw [ce2_mod_add_zsmul x] at h
  exact h

/-- The folded cylinder background. -/
def ce2_cyl (s0 : Site 2 → ℤ) : ℤ × Fin 4 → ℤ := fun p => s0 (ce2_pt p.1 (p.2 : ℕ))

/-- At a boundary point `x₁ = 0`, reflection about `x₁ = -1/2` is the same as the
left shift. -/
theorem ce2_reflect_eq_sub_zero (x : Site 2) (hx0 : x ⟨0, by norm_num⟩ = 0) :
    ce2_reflect x = x - unit (⟨0, by norm_num⟩ : Fin 2) := by
  funext i
  fin_cases i
  · show -1 - x ⟨0, by norm_num⟩ = x ⟨0, by norm_num⟩ - 1
    rw [hx0]; ring
  · simp [ce2_reflect, unit, Pi.sub_apply]

/-- The fold of a periodic background agrees with the background after projection. -/
theorem ce2_cyl_cylProj (s0 : Site 2 → ℤ)
    (hper : ∀ x, s0 (ce2_shift x) = s0 x) (x : Site 2) :
    ce2_cyl s0 (ce_cylProj x) = s0 x := by
  have hpt : ce2_pt (ce_cylProj x).1 ((ce_cylProj x).2 : ℕ) = ce2_mod x := by
    funext i
    fin_cases i
    · rfl
    · have hlt : (x ⟨1, by norm_num⟩ % 4).toNat < 4 := by
        have h := Int.emod_lt_of_pos (x ⟨1, by norm_num⟩) (by norm_num : (0:ℤ) < 4)
        omega
      simp only [ce2_pt, ce2_mod, ce_cylProj, Fin.val_ofNat,
        if_neg (by decide : ¬ (1 : ℕ) = 0)]
      rw [Nat.mod_eq_of_lt hlt]
  change s0 (ce2_pt (ce_cylProj x).1 ((ce_cylProj x).2 : ℕ)) = s0 x
  rw [hpt]
  exact (ce2_periodic_reduce s0 hper x).symm

/-- The cylinder neighbour sum of the folded background equals the 2D neighbour
sum, including at the reflecting boundary `x₁ = 0` where the missing left
neighbour is supplied by the reflection symmetry. -/
theorem ce2_cylNbrSum_fold (u : ℤ × Fin 4 → ℤ) (v : Site 2 → ℤ)
    (hfold : ∀ y : Site 2, 0 ≤ y ⟨0, by norm_num⟩ → u (ce_cylProj y) = v y)
    (hsym : ∀ y : Site 2, v (ce2_reflect y) = v y)
    (x : Site 2) (hx : 0 ≤ x ⟨0, by norm_num⟩) :
    cylNbrSum u (ce_cylProj x) = nbrSumZ v x := by
  rcases lt_or_ge (x ⟨0, by norm_num⟩) 1 with hlt | hge
  · have hx0 : x ⟨0, by norm_num⟩ = 0 := by omega
    have hp0 : (ce_cylProj x).1 = 0 := hx0
    have hself : u (ce_cylProj x) = v (x - unit (⟨0, by norm_num⟩ : Fin 2)) := by
      rw [← ce2_reflect_eq_sub_zero x hx0]
      exact (hfold x hx).trans (hsym x).symm
    have hadd0 : u (1, (ce_cylProj x).2)
        = v (x + unit (⟨0, by norm_num⟩ : Fin 2)) := by
      have hone : ce_cylProj (x + unit (⟨0, by norm_num⟩ : Fin 2))
          = (1, (ce_cylProj x).2) := by
        rw [ce_cylProj_add_zero]
        refine Prod.ext ?_ ?_
        · rw [hp0]; norm_num
        · rfl
      rw [← hone, hfold (x + unit (⟨0, by norm_num⟩ : Fin 2)) (by
        simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_same]; omega)]
    have ha1 : 0 ≤ (x + unit (⟨1, by norm_num⟩ : Fin 2)) ⟨0, by norm_num⟩ := by
      simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_of_ne
        (show (⟨0, by norm_num⟩ : Fin 2) ≠ ⟨1, by norm_num⟩ from
          fun hc => absurd (congrArg Fin.val hc) (by decide))]
      omega
    have hadd1 : u ((ce_cylProj x).1, (ce_cylProj x).2 + 1)
        = v (x + unit (⟨1, by norm_num⟩ : Fin 2)) := by
      rw [← hfold (x + unit (⟨1, by norm_num⟩ : Fin 2)) ha1]
      congr 1
      exact (ce_cylProj_add_one x).symm
    have hs1 : 0 ≤ (x - unit (⟨1, by norm_num⟩ : Fin 2)) ⟨0, by norm_num⟩ := by
      simp only [Pi.sub_apply, LatticeProb.unit, Pi.single_eq_of_ne
        (show (⟨0, by norm_num⟩ : Fin 2) ≠ ⟨1, by norm_num⟩ from
          fun hc => absurd (congrArg Fin.val hc) (by decide))]
      omega
    have hsub1 : u ((ce_cylProj x).1, (ce_cylProj x).2 - 1)
        = v (x - unit (⟨1, by norm_num⟩ : Fin 2)) := by
      rw [← hfold (x - unit (⟨1, by norm_num⟩ : Fin 2)) hs1]
      congr 1
      exact (ce_cylProj_sub_one x).symm
    unfold cylNbrSum nbrSumZ
    rw [Fin.sum_univ_two, if_pos hp0]
    rw [hadd0, hself, hadd1, hsub1]
    abel
  · exact ce_cylNbrSum_cylProj u v hfold x hge

/-- **The reflected-cylinder identification** (paper `exploding.tex:1490-1518`,
Step 3a): for a background `s0` symmetric about `x₁ = -1/2` and `4`-periodic in
`x₂`, the cylinder odometer of the folded background equals the true 2D odometer
on the half-plane `x₁ ≥ 0`. -/
theorem ce2_cylOdo_eq_podo (s0 : Site 2 → ℤ)
    (hsym : ∀ x, s0 (ce2_reflect x) = s0 x)
    (hper : ∀ x, s0 (ce2_shift x) = s0 x) :
    ∀ t x, 0 ≤ x ⟨0, by norm_num⟩ →
      cylOdo (ce2_cyl s0) t (ce_cylProj x) = podo s0 t x := by
  intro t
  induction t with
  | zero => intro x _; simp
  | succ t ih =>
    intro x hx
    rw [cylOdo_succ, podo_succ]
    have hlap : cylLap (cylOdo (ce2_cyl s0) t) (ce_cylProj x)
        = lap (podo s0 t) x := by
      rw [cylLap, lap_eq]
      have hnbr := ce2_cylNbrSum_fold (cylOdo (ce2_cyl s0) t) (podo s0 t)
        (fun y hy => ih y hy) (ce2_podo_reflect s0 hsym t) x hx
      rw [hnbr, ih x hx]
      norm_num
    have hs0 : ce2_cyl s0 (ce_cylProj x) = s0 x := ce2_cyl_cylProj s0 hper x
    have hconf : ce2_cyl s0 (ce_cylProj x) + cylLap (cylOdo (ce2_cyl s0) t) (ce_cylProj x)
        = s0 x + lap (podo s0 t) x := by rw [hs0, hlap]
    rw [ih x hx]
    congr 1
    rw [hconf]
    rfl

end Exploding
