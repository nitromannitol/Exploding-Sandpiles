/-
The relay induction of the counterexample of `paper/exploding.tex` Section 6
(`exploding.tex:1386-1389`): on the stacked checkerboard background the front on
the relay row `x₁ = 1` advances at unit speed, reaching position `k` by time
`k + 2`.  This is Step 1's upper bound in the proof of `theorem:counterexample`.
-/
import Exploding.Support.Vocab

namespace Exploding

open LatticeProb Filter

variable {d : ℕ}

/-- The checkerboard block `ζ₁` of `exploding.tex:1370-1376`. -/
def zeta1 (a b : ℤ) : ℤ :=
  if (a % 4 = 0 ∨ a % 4 = 3) ∧ (b % 4 = 0 ∨ b % 4 = 3) then 1 else 3

/-- The stacked counterexample background `(6.4)`: `2(d-2) + ζ₁(x₀, x₁)`. -/
def ceEta (d : ℕ) (x : Site d) : ℤ :=
  2 * ((d : ℤ) - 2) +
    zeta1 (if h : 0 < d then x ⟨0, h⟩ else 0) (if h : 1 < d then x ⟨1, h⟩ else 0)

/-- The unit vector in the paper's `x₂`-direction (`x 1` in this file's
indexing).  Names the relay row `x₁ = 1`. -/
def e2 (d : ℕ) : Site d := fun i => if (i : ℕ) = 1 then 1 else 0

theorem aux_podo_nonneg {d : ℕ} (s0 : Site d → ℤ) (t : ℕ) (x : Site d) :
    0 ≤ podo s0 t x := by
  induction t with
  | zero => simp
  | succ t ih => rw [podo_succ]; split <;> omega

/-- The relay row `x₁ = 1` carries the constant value `2d - 1`. -/
theorem aux_ce_row1_const (d : ℕ) (hd : 2 ≤ d) (k : ℤ) :
    ceEta d ((k • e1 d : Site d) + e2 d) = 2 * (d : ℤ) - 1 := by
  have h0 : 0 < d := by omega
  have h1 : 1 < d := by omega
  have hce : ceEta d ((k • e1 d : Site d) + e2 d)
      = 2 * ((d : ℤ) - 2)
        + zeta1 (((k • e1 d : Site d) + e2 d) ⟨0, h0⟩)
            (((k • e1 d : Site d) + e2 d) ⟨1, h1⟩) := by
    simp [ceEta, h0, h1]
  have hx1 : ((k • e1 d : Site d) + e2 d) ⟨1, h1⟩ = 1 := by
    simp [e1, e2, Pi.add_apply]
  have hz1 : ∀ A : ℤ, zeta1 A 1 = 3 := by
    intro A
    unfold zeta1
    norm_num
  rw [hce, hx1, hz1]
  ring

theorem aux_ce_relay_fires (d : ℕ) (hd : 2 ≤ d) :
    ∀ k : ℕ, 0 < podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k + 2)
      ((k : ℤ) • e1 d + e2 d) := by
  intro k
  have h0 : 0 < d := by omega
  have h1 : 1 < d := by omega
  have h01 : (⟨0, h0⟩ : Fin d) ≠ ⟨1, h1⟩ := by
    intro hcon
    have := congrArg Fin.val hcon
    norm_num at this
  have hdirac0 : dirac (0 : Site d) (0 : Site d) = 1 := dirac_self _
  have hce0 : ceEta d (0 : Site d) = 2 * (d : ℤ) - 3 := by
    have hce : ceEta d (0 : Site d) = 2 * ((d : ℤ) - 2) + zeta1 0 0 := by
      simp [ceEta, h0, h1]
    have hz : zeta1 0 0 = 1 := by unfold zeta1; norm_num
    rw [hce, hz]; ring
  -- the origin fires at time 1
  have hfire0 : 0 < podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) 1 (0 : Site d) := by
    rw [podo_succ]
    have hc : 2 * (d : ℤ) ≤ pconf (fun x => ceEta d x + 3 * dirac (0 : Site d) x) 0 (0 : Site d) := by
      simp only [pconf, podo_zero, lap, nbrSumZ, mul_zero, sub_zero]
      rw [hce0, hdirac0]
      push_cast
      ring_nf
      simp
    rw [if_pos hc]
    norm_num
  -- the relay row point at `k` fires by time `k + 2`
  induction k with
  | zero =>
    -- e₂ is fed by the origin
    have hrow : ceEta d (e2 d) = 2 * (d : ℤ) - 1 := by
      have h := aux_ce_row1_const d hd 0
      simpa using h
    have hsum : (1 : ℤ) ≤ nbrSumZ (podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) 1) (e2 d) := by
      have hterm := Finset.single_le_sum
        (f := fun j : Fin d => podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) 1
            ((e2 d) + unit j) + podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) 1
            ((e2 d) - unit j))
        (fun j _ => by
          have ha := aux_podo_nonneg (fun x => ceEta d x + 3 * dirac (0 : Site d) x) 1 ((e2 d) + unit j)
          have hb := aux_podo_nonneg (fun x => ceEta d x + 3 * dirac (0 : Site d) x) 1 ((e2 d) - unit j)
          linarith)
        (Finset.mem_univ ⟨1, h1⟩)
      have hoff : (e2 d) - unit ⟨1, h1⟩ = (0 : Site d) := by
        funext i
        simp only [Pi.sub_apply, e2, LatticeProb.unit, Pi.single_apply, Pi.zero_apply]
        by_cases hi : i = ⟨1, h1⟩
        · subst hi
          norm_num
        · have hi' : ¬ (i : ℕ) = 1 := fun hcon => hi (Fin.ext hcon)
          simp only [if_neg hi', if_neg hi]
          norm_num
      rw [hoff] at hterm
      have hpos : (1 : ℤ) ≤ podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) 1 0 := hfire0
      have hnn : (0 : ℤ) ≤ podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) 1
          (e2 d + unit ⟨1, h1⟩) := aux_podo_nonneg _ 1 _
      simp only [nbrSumZ] at hterm ⊢
      linarith
    have hdirac0' : dirac (0 : Site d) (e2 d) = 0 := by
      apply dirac_of_ne
      intro hcon
      have h1' := congrFun hcon ⟨1, h1⟩
      simp only [e2, Pi.zero_apply] at h1'
      norm_num at h1'
    have hle1 : podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) 1 (e2 d) ≤ 1 := by
      rw [podo_succ]
      have h0' : podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) 0 (e2 d) = 0 := rfl
      rw [h0']
      split
      · omega
      · omega
    by_cases h1f : podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) 1 (e2 d) = 1
    · have hmono := podo_mono_step (fun x => ceEta d x + 3 * dirac (0 : Site d) x) 1 (e2 d)
      rw [h1f] at hmono
      have he : ((0 : ℕ) : ℤ) • e1 d + e2 d = e2 d := by
        rw [Nat.cast_zero, zero_smul, zero_add]
      rw [he]
      show (0 : ℤ) < podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (1 + 1) (e2 d)
      omega
    · have h0f : podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) 1 (e2 d) = 0 := by
        have hnn := aux_podo_nonneg (fun x => ceEta d x + 3 * dirac (0 : Site d) x) 1 (e2 d)
        omega
      have he : ((0 : ℕ) : ℤ) • e1 d + e2 d = e2 d := by
        rw [Nat.cast_zero, zero_smul, zero_add]
      rw [he]
      rw [podo_succ]
      have hc : 2 * (d : ℤ) ≤ pconf (fun x => ceEta d x + 3 * dirac (0 : Site d) x) 1 (e2 d) := by
        have hnn1 : 0 ≤ podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) 1 (e2 d) :=
          aux_podo_nonneg _ 1 _
        simp only [pconf, lap, hrow, hdirac0', mul_zero, add_zero, h0f]
        nlinarith [hsum, hle1, hnn1]
      rw [if_pos hc]
      show (0 : ℤ) < podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) 1 (e2 d) + 1
      omega
  | succ k ih =>
    by_cases hpos : 0 < podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k + 1 + 2)
        (((k + 1 : ℕ) : ℤ) • e1 d + e2 d)
    · exact hpos
    · have h0f : podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k + 1 + 2)
          (((k + 1 : ℕ) : ℤ) • e1 d + e2 d) = 0 := by
        have hnn := aux_podo_nonneg (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k + 1 + 2)
          (((k + 1 : ℕ) : ℤ) • e1 d + e2 d)
        omega
      have he2 : k + 1 + 2 = k + 2 + 1 := by omega
      rw [he2]
      rw [podo_succ]
      have hc : 2 * (d : ℤ) ≤ pconf (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k + 2)
          (((k + 1 : ℕ) : ℤ) • e1 d + e2 d) := by
        have hrow : ceEta d (((k + 1 : ℕ) : ℤ) • e1 d + e2 d) = 2 * (d : ℤ) - 1 :=
          aux_ce_row1_const d hd ((k + 1 : ℕ) : ℤ)
        have hsum : (1 : ℤ) ≤ nbrSumZ (podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x)
            (k + 2)) (((k + 1 : ℕ) : ℤ) • e1 d + e2 d) := by
          have hterm := Finset.single_le_sum
            (f := fun j : Fin d => podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x)
                (k + 2) ((((k + 1 : ℕ) : ℤ) • e1 d + e2 d) + unit j) +
              podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k + 2)
                ((((k + 1 : ℕ) : ℤ) • e1 d + e2 d) - unit j))
            (fun j _ => by
              have ha := aux_podo_nonneg (fun x => ceEta d x + 3 * dirac (0 : Site d) x)
                (k + 2) ((((k + 1 : ℕ) : ℤ) • e1 d + e2 d) + unit j)
              have hb := aux_podo_nonneg (fun x => ceEta d x + 3 * dirac (0 : Site d) x)
                (k + 2) ((((k + 1 : ℕ) : ℤ) • e1 d + e2 d) - unit j)
              linarith)
            (Finset.mem_univ ⟨0, h0⟩)
          have hoff : (((k + 1 : ℕ) : ℤ) • e1 d + e2 d) - unit ⟨0, h0⟩
              = ((k : ℕ) : ℤ) • e1 d + e2 d := by
            funext i
            simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, e1, e2,
              LatticeProb.unit, Pi.single_apply]
            by_cases hi0 : i = ⟨0, h0⟩
            · subst hi0
              norm_num
            · by_cases hi1 : i = ⟨1, h1⟩
              · subst hi1
                norm_num
              · have hi0' : ¬ (i : ℕ) = 0 := fun hcon => hi0 (Fin.ext hcon)
                have hi1' : ¬ (i : ℕ) = 1 := fun hcon => hi1 (Fin.ext hcon)
                simp only [if_neg hi0', if_neg hi1', if_neg hi0]
                ring
          rw [hoff] at hterm
          have hpos' : (1 : ℤ) ≤ podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x)
              (k + 2) (((k : ℕ) : ℤ) • e1 d + e2 d) := ih
          have hnn : (0 : ℤ) ≤ podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x)
              (k + 2) ((((k + 1 : ℕ) : ℤ) • e1 d + e2 d) + unit ⟨0, h0⟩) :=
            aux_podo_nonneg _ _ _
          simp only [nbrSumZ] at hterm ⊢
          linarith
        have hdirac0'' : dirac (0 : Site d) (((k + 1 : ℕ) : ℤ) • e1 d + e2 d) = 0 := by
          apply dirac_of_ne
          intro hcon
          have h1' := congrFun hcon ⟨1, h1⟩
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e1, e2, Pi.zero_apply] at h1'
          rw [if_neg (by norm_num : ¬ ((⟨1, h1⟩ : Fin d) : ℕ) = 0)] at h1'
          norm_num at h1'
        have h0'' : podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k + 2)
            (((k + 1 : ℕ) : ℤ) • e1 d + e2 d) = 0 := by
          have hmono := podo_mono_step (fun x => ceEta d x + 3 * dirac (0 : Site d) x)
            (k + 2) (((k + 1 : ℕ) : ℤ) • e1 d + e2 d)
          have he : k + 2 + 1 = k + 1 + 2 := by omega
          have h0f' : podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k + 2 + 1)
              (((k + 1 : ℕ) : ℤ) • e1 d + e2 d) = 0 := by
            rw [he]; exact h0f
          have hnn : (0 : ℤ) ≤ podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k + 2)
              (((k + 1 : ℕ) : ℤ) • e1 d + e2 d) :=
            aux_podo_nonneg _ _ _
          linarith [hmono, h0f', hnn]
        simp only [pconf, lap, hrow, hdirac0'', mul_zero, add_zero, h0'']
        linarith
      rw [if_pos hc]
      show (0 : ℤ) < podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k + 2)
          (((k + 1 : ℕ) : ℤ) • e1 d + e2 d) + 1
      have h0''' : podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k + 2)
          (((k + 1 : ℕ) : ℤ) • e1 d + e2 d) = 0 := by
        have hmono := podo_mono_step (fun x => ceEta d x + 3 * dirac (0 : Site d) x)
          (k + 2) (((k + 1 : ℕ) : ℤ) • e1 d + e2 d)
        have he : k + 2 + 1 = k + 1 + 2 := by omega
        have h0f' : podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k + 2 + 1)
            (((k + 1 : ℕ) : ℤ) • e1 d + e2 d) = 0 := by
          rw [he]; exact h0f
        have hnn : (0 : ℤ) ≤ podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k + 2)
            (((k + 1 : ℕ) : ℤ) • e1 d + e2 d) := aux_podo_nonneg _ _ _
        linarith [hmono, h0f', hnn]
      rw [h0''']
      norm_num

/-- The row-`0` point `k • e₁` is "high" type (`ceEta = 2d-1`, needs only one
extra chip) exactly when `k ≢ 0, 3 (mod 4)`. -/
theorem aux_ce_row0_high (d : ℕ) (hd : 2 ≤ d) (k : ℤ) (hk : k % 4 = 1 ∨ k % 4 = 2) :
    ceEta d ((k • e1 d : Site d)) = 2 * (d : ℤ) - 1 := by
  have h0 : 0 < d := by omega
  have h1 : 1 < d := by omega
  have hce : ceEta d ((k • e1 d : Site d))
      = 2 * ((d : ℤ) - 2)
        + zeta1 ((k • e1 d : Site d) ⟨0, h0⟩) ((k • e1 d : Site d) ⟨1, h1⟩) := by
    simp [ceEta, h0, h1]
  have hx0 : (k • e1 d : Site d) ⟨0, h0⟩ = k := by
    simp [e1]
  have hx1 : (k • e1 d : Site d) ⟨1, h1⟩ = 0 := by
    simp [e1]
  have hz : zeta1 k 0 = 3 := by
    rcases hk with hk | hk <;> unfold zeta1 <;> norm_num [hk]
  rw [hce, hx0, hx1, hz]
  ring

/-- One further step beyond the relay (`exploding.tex:1389`): a row-`0` point of
"high" type gets fed by its own relay-row point above it. -/
theorem aux_ce_row0_lands (d : ℕ) (hd : 2 ≤ d) (k : ℤ) (hk : k % 4 = 1 ∨ k % 4 = 2)
    (hk0 : 0 ≤ k) :
    0 < podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k.toNat + 3)
      ((k • e1 d : Site d)) := by
  have h0 : 0 < d := by omega
  have h1 : 1 < d := by omega
  have hrow : ceEta d ((k • e1 d : Site d)) = 2 * (d : ℤ) - 1 := aux_ce_row0_high d hd k hk
  have hrelay : 0 < podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k.toNat + 2)
      ((k.toNat : ℤ) • e1 d + e2 d) := aux_ce_relay_fires d hd k.toNat
  have hcast : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk0
  rw [hcast] at hrelay
  by_cases hpos : 0 < podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k.toNat + 3)
      ((k • e1 d : Site d))
  · exact hpos
  · have h0f : podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k.toNat + 3)
        ((k • e1 d : Site d)) = 0 := by
      have hnn := aux_podo_nonneg (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k.toNat + 3)
        ((k • e1 d : Site d))
      omega
    rw [podo_succ]
    have hc : 2 * (d : ℤ) ≤ pconf (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k.toNat + 2)
        ((k • e1 d : Site d)) := by
      have hsum : (1 : ℤ) ≤ nbrSumZ (podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x)
          (k.toNat + 2)) ((k • e1 d : Site d)) := by
        have hterm := Finset.single_le_sum
          (f := fun j : Fin d => podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x)
              (k.toNat + 2) (((k • e1 d : Site d)) + unit j) +
            podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k.toNat + 2)
              (((k • e1 d : Site d)) - unit j))
          (fun j _ => by
            have ha := aux_podo_nonneg (fun x => ceEta d x + 3 * dirac (0 : Site d) x)
              (k.toNat + 2) (((k • e1 d : Site d)) + unit j)
            have hb := aux_podo_nonneg (fun x => ceEta d x + 3 * dirac (0 : Site d) x)
              (k.toNat + 2) (((k • e1 d : Site d)) - unit j)
            linarith)
          (Finset.mem_univ ⟨1, h1⟩)
        have hoff : ((k • e1 d : Site d)) + unit ⟨1, h1⟩ = (k : ℤ) • e1 d + e2 d := by
          have he : e2 d = unit ⟨1, h1⟩ := by
            funext i
            simp only [e2, LatticeProb.unit, Pi.single_apply]
            by_cases hi : (i : ℕ) = 1
            · have hii : i = ⟨1, h1⟩ := Fin.ext hi
              rw [hii, if_pos rfl, if_pos rfl]
            · have hne : i ≠ ⟨1, h1⟩ := fun hcon => hi (by rw [hcon])
              rw [if_neg hi, if_neg hne]
          rw [he]
        rw [hoff] at hterm
        have hnn : (0 : ℤ) ≤ podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x)
            (k.toNat + 2) (((k • e1 d : Site d)) - unit ⟨1, h1⟩) := aux_podo_nonneg _ _ _
        have hpos' : (1 : ℤ) ≤ podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x)
            (k.toNat + 2) ((k : ℤ) • e1 d + e2 d) := hrelay
        simp only [nbrSumZ] at hterm ⊢
        linarith
      have hdirac0 : dirac (0 : Site d) ((k • e1 d : Site d)) = 0 := by
        apply dirac_of_ne
        intro hcon
        have h1' := congrFun hcon ⟨0, h0⟩
        simp only [Pi.smul_apply, smul_eq_mul, e1, Pi.zero_apply] at h1'
        norm_num at h1'
        have hkpos : k ≠ 0 := by
          intro hkz
          rw [hkz] at hk
          norm_num at hk
        exact hkpos h1'
      have hle1 : podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k.toNat + 2)
          ((k • e1 d : Site d)) ≤ 1 := by
        rw [podo_succ]
        have h0' : podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k.toNat + 1)
            ((k • e1 d : Site d)) = 0 := by
          have hmono := podo_mono_step (fun x => ceEta d x + 3 * dirac (0 : Site d) x)
            (k.toNat + 1) ((k • e1 d : Site d))
          have he : k.toNat + 1 + 1 = k.toNat + 2 := by omega
          rw [he] at hmono
          have hmono2 := podo_mono_step (fun x => ceEta d x + 3 * dirac (0 : Site d) x)
            (k.toNat + 2) ((k • e1 d : Site d))
          have he2 : k.toNat + 2 + 1 = k.toNat + 3 := by omega
          rw [he2] at hmono2
          have hnn := aux_podo_nonneg (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k.toNat + 1)
            ((k • e1 d : Site d))
          omega
        rw [h0']
        split <;> omega
      have hnn1 : 0 ≤ podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k.toNat + 2)
          ((k • e1 d : Site d)) := aux_podo_nonneg _ _ _
      have h0mid : podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k.toNat + 2)
          ((k • e1 d : Site d)) = 0 := by
        have hmono := podo_mono_step (fun x => ceEta d x + 3 * dirac (0 : Site d) x)
          (k.toNat + 2) ((k • e1 d : Site d))
        have he : k.toNat + 2 + 1 = k.toNat + 3 := by omega
        rw [he] at hmono
        omega
      simp only [pconf, lap, hrow, hdirac0, mul_zero, add_zero, h0mid]
      linarith
    rw [if_pos hc]
    show (0 : ℤ) < podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k.toNat + 2)
        ((k • e1 d : Site d)) + 1
    have h0mid : podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k.toNat + 2)
        ((k • e1 d : Site d)) = 0 := by
      have hmono := podo_mono_step (fun x => ceEta d x + 3 * dirac (0 : Site d) x)
        (k.toNat + 2) ((k • e1 d : Site d))
      have he : k.toNat + 2 + 1 = k.toNat + 3 := by omega
      rw [he] at hmono
      have hnn := aux_podo_nonneg (fun x => ceEta d x + 3 * dirac (0 : Site d) x) (k.toNat + 2)
        ((k • e1 d : Site d))
      omega
    rw [h0mid]
    norm_num

/-- The row-`0` point `k • e₁` is "low" type (`ceEta = 2d-3`) exactly when
`k ≡ 0, 3 (mod 4)`. -/
theorem aux_ce_row0_low (d : ℕ) (hd : 2 ≤ d) (k : ℤ) (hk : k % 4 = 0 ∨ k % 4 = 3) :
    ceEta d ((k • e1 d : Site d)) = 2 * (d : ℤ) - 3 := by
  have h0 : 0 < d := by omega
  have h1 : 1 < d := by omega
  have hce : ceEta d ((k • e1 d : Site d))
      = 2 * ((d : ℤ) - 2)
        + zeta1 ((k • e1 d : Site d) ⟨0, h0⟩) ((k • e1 d : Site d) ⟨1, h1⟩) := by
    simp [ceEta, h0, h1]
  have hx0 : (k • e1 d : Site d) ⟨0, h0⟩ = k := by simp [e1]
  have hx1 : (k • e1 d : Site d) ⟨1, h1⟩ = 0 := by simp [e1]
  have hz : zeta1 k 0 = 1 := by
    rcases hk with hk | hk <;> unfold zeta1 <;> norm_num [hk]
  rw [hce, hx0, hx1, hz]
  ring

theorem aux_ceEta_bounds (d : ℕ) (x : Site d) :
    2 * (d : ℤ) - 3 ≤ ceEta d x ∧ ceEta d x ≤ 2 * (d : ℤ) - 1 := by
  have hval : ∀ (a b : ℤ), zeta1 a b = 1 ∨ zeta1 a b = 3 := by
    intro a b
    unfold zeta1
    split <;> simp
  unfold ceEta
  rcases hval _ _ with h | h <;> rw [h] <;> constructor <;> omega

theorem aux_unit_apply {d : ℕ} (i j : Fin d) : unit i j = if j = i then (1 : ℤ) else 0 := by
  simp [unit, Pi.single_apply]

theorem aux_mnorm_le_add_unit (d : ℕ) (x : Site d) (i : Fin d) :
    mnorm x ≤ mnorm (x + unit i) + 1 := by
  have hterm : ∀ j : Fin d,
      |x j| ≤ |(x + unit i) j| + (if j = i then (1 : ℤ) else 0) := by
    intro j
    by_cases hj : j = i
    · have hxj : (x + unit i) j = x j + 1 := by
        rw [Pi.add_apply, aux_unit_apply, if_pos hj]
      rw [hxj, if_pos hj]
      have h1 := abs_add_le (x j + 1) (-1 : ℤ)
      rw [show x j + 1 + (-1) = x j from by ring, abs_neg, abs_one] at h1
      exact h1
    · have hxj : (x + unit i) j = x j := by
        rw [Pi.add_apply, aux_unit_apply, if_neg hj, add_zero]
      rw [hxj, if_neg hj]
      simp
  have hsum : (∑ j : Fin d, (if j = i then (1 : ℤ) else 0)) = 1 := by
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb])
      (fun hi => absurd (Finset.mem_univ i) hi), if_pos rfl]
  calc mnorm x = ∑ j : Fin d, |x j| := rfl
    _ ≤ ∑ j : Fin d, (|(x + unit i) j| + (if j = i then (1 : ℤ) else 0)) :=
        Finset.sum_le_sum (fun j _ => hterm j)
    _ = mnorm (x + unit i) + 1 := by
        rw [Finset.sum_add_distrib, hsum]
        rfl

theorem aux_mnorm_le_sub_unit (d : ℕ) (x : Site d) (i : Fin d) :
    mnorm x ≤ mnorm (x - unit i) + 1 := by
  have hterm : ∀ j : Fin d,
      |x j| ≤ |(x - unit i) j| + (if j = i then (1 : ℤ) else 0) := by
    intro j
    by_cases hj : j = i
    · have hxj : (x - unit i) j = x j - 1 := by
        rw [Pi.sub_apply, aux_unit_apply, if_pos hj]
      rw [hxj, if_pos hj]
      have h1 := abs_add_le (x j - 1) (1 : ℤ)
      rw [show x j - 1 + 1 = x j from by ring, abs_one] at h1
      exact h1
    · have hxj : (x - unit i) j = x j := by
        rw [Pi.sub_apply, aux_unit_apply, if_neg hj, sub_zero]
      rw [hxj, if_neg hj]
      simp
  have hsum : (∑ j : Fin d, (if j = i then (1 : ℤ) else 0)) = 1 := by
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb])
      (fun hi => absurd (Finset.mem_univ i) hi), if_pos rfl]
  calc mnorm x = ∑ j : Fin d, |x j| := rfl
    _ ≤ ∑ j : Fin d, (|(x - unit i) j| + (if j = i then (1 : ℤ) else 0)) :=
        Finset.sum_le_sum (fun j _ => hterm j)
    _ = mnorm (x - unit i) + 1 := by
        rw [Finset.sum_add_distrib, hsum]
        rfl

theorem aux_nbrSumZ_pos_neighbour (d : ℕ) (u : Site d → ℤ) (x : Site d)
    (h : 0 < nbrSumZ u x) :
    (∃ i : Fin d, 0 < u (x + unit i)) ∨ (∃ i : Fin d, 0 < u (x - unit i)) := by
  by_contra hc
  simp only [not_or, not_exists, not_lt] at hc
  obtain ⟨h1, h2⟩ := hc
  have hle : nbrSumZ u x ≤ 0 := by
    simp only [nbrSumZ]
    exact Finset.sum_nonpos fun i _ => add_nonpos (h1 i) (h2 i)
  omega

theorem aux_zeta1_mem (a b : ℤ) : 1 ≤ zeta1 a b ∧ zeta1 a b ≤ 3 := by
  unfold zeta1
  split <;> norm_num

theorem aux_lap_zero (d : ℕ) (x : Site d) : lap (fun _ : Site d => (0 : ℤ)) x = 0 := by
  simp [lap, nbrSumZ]

theorem aux_podo_zero_of_bound (d : ℕ) (s0 : Site d → ℤ) (h : ∀ x, s0 x ≤ 2 * (d : ℤ) - 1) :
    ∀ t : ℕ, podo s0 t = fun _ => 0 := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
      funext x
      rw [podo_succ]
      have hp : pconf s0 t x = s0 x := by
        rw [pconf, ih]
        simp [lap, nbrSumZ]
      rw [hp, if_neg (by intro hc; have hx := h x; linarith)]
      rw [ih]
      simp

theorem aux_ce_s0_bound (d : ℕ) (hd : 2 ≤ d) (n : ℕ) (hn : n ≤ 2) (x : Site d) :
    ceEta d x + n * dirac (0 : Site d) x ≤ 2 * (d : ℤ) - 1 := by
  have h0 : 0 < d := by omega
  have h1 : 1 < d := by omega
  have hce : ceEta d x = 2 * ((d : ℤ) - 2) + zeta1 (x ⟨0, h0⟩) (x ⟨1, h1⟩) := by
    simp [ceEta, h0, h1]
  by_cases hx : x = 0
  · subst hx
    have hz : zeta1 ((0 : Site d) ⟨0, h0⟩) ((0 : Site d) ⟨1, h1⟩) = 1 := by
      simp only [Pi.zero_apply]
      norm_num [zeta1]
    rw [hce, hz, dirac_self]
    have hnz : (n : ℤ) ≤ 2 := by exact_mod_cast hn
    nlinarith
  · rw [hce, dirac_of_ne (z := (0 : Site d)) hx]
    have hz := (aux_zeta1_mem (x ⟨0, h0⟩) (x ⟨1, h1⟩)).2
    nlinarith

theorem aux_ce_stab_small (d : ℕ) (hd : 2 ≤ d) (n : ℕ) (hn : n ≤ 2) :
    Stabilizable (fun x => ceEta d x + n * dirac (0 : Site d) x) := by
  refine ⟨0, ?_⟩
  intro t ht
  have hb : ∀ x : Site d, ceEta d x + n * dirac (0 : Site d) x ≤ 2 * (d : ℤ) - 1 :=
    fun x => aux_ce_s0_bound d hd n hn x
  have h := aux_podo_zero_of_bound d (fun x => ceEta d x + n * dirac (0 : Site d) x) hb t
  have h0 := aux_podo_zero_of_bound d (fun x => ceEta d x + n * dirac (0 : Site d) x) hb 0
  rw [h, h0]

/-- General form of `aux_podo_mnorm_le` for an arbitrary extra charge `c` at
the origin, instead of `explosionThreshold (ceEta d)`.  Needed because this
is proven BEFORE `explosionThreshold (ceEta d) = 3` is available (that fact,
`aux_ce_threshold`/`aux_ce_threshold'` below, itself rests on
`aux_ce_not_stab3`).  Identical proof to `aux_podo_mnorm_le`, with
`explodingPile (ceEta d)` replaced by `fun y => ceEta d y + c * dirac 0 y`
throughout (the proof never used the specific value of the origin charge). -/
theorem aux_ce_s0_mnorm_le (d : ℕ) (_hd : 2 ≤ d) (c : ℤ) :
    ∀ t : ℕ, ∀ x : Site d,
      0 < podo (fun y => ceEta d y + c * dirac (0 : Site d) y) t x → mnorm x + 1 ≤ t := by
  intro t
  induction t with
  | zero => intro x h; simp at h
  | succ t ih =>
    intro x hx
    rw [podo_succ] at hx
    by_cases h0 : 0 < podo (fun y => ceEta d y + c * dirac (0 : Site d) y) t x
    · have := ih x h0
      omega
    · have hge : 2 * d ≤ pconf (fun y => ceEta d y + c * dirac (0 : Site d) y) t x := by
        by_cases hc : 2 * d ≤ pconf (fun y => ceEta d y + c * dirac (0 : Site d) y) t x
        · exact hc
        · simp [hc] at hx
          omega
      have hnng : 0 ≤ podo (fun y => ceEta d y + c * dirac (0 : Site d) y) t x :=
        aux_podo_nonneg _ t x
      have hz : podo (fun y => ceEta d y + c * dirac (0 : Site d) y) t x = 0 := by omega
      have hpe : pconf (fun y => ceEta d y + c * dirac (0 : Site d) y) t x =
          (fun y => ceEta d y + c * dirac (0 : Site d) y) x
            + nbrSumZ (podo (fun y => ceEta d y + c * dirac (0 : Site d) y) t) x := by
        simp only [pconf, lap_eq]
        rw [hz]
        ring
      by_cases hx0 : x = 0
      · subst hx0
        have hm0 : mnorm (0 : Site d) = 0 := by simp [mnorm]
        omega
      · have hSx : (fun y => ceEta d y + c * dirac (0 : Site d) y) x = ceEta d x := by
          show ceEta d x + c * dirac (0 : Site d) x = ceEta d x
          rw [dirac_of_ne hx0, mul_zero, add_zero]
        have hbd := aux_ceEta_bounds d x
        have hnbr : 0 < nbrSumZ (podo (fun y => ceEta d y + c * dirac (0 : Site d) y) t) x := by
          have h2 : 2 * d ≤ ceEta d x
              + nbrSumZ (podo (fun y => ceEta d y + c * dirac (0 : Site d) y) t) x := by
            calc 2 * d ≤ pconf (fun y => ceEta d y + c * dirac (0 : Site d) y) t x := hge
              _ = (fun y => ceEta d y + c * dirac (0 : Site d) y) x
                    + nbrSumZ (podo (fun y => ceEta d y + c * dirac (0 : Site d) y) t) x := hpe
              _ = ceEta d x
                    + nbrSumZ (podo (fun y => ceEta d y + c * dirac (0 : Site d) y) t) x := by
                  rw [hSx]
          omega
        rcases aux_nbrSumZ_pos_neighbour d
            (podo (fun y => ceEta d y + c * dirac (0 : Site d) y) t) x hnbr with
          ⟨i, hi⟩ | ⟨i, hi⟩
        · have hrec := ih (x + unit i) hi
          have hmm := aux_mnorm_le_add_unit d x i
          omega
        · have hrec := ih (x - unit i) hi
          have hmm := aux_mnorm_le_sub_unit d x i
          omega

/-- The relay row point at `k` is at Manhattan distance at least `k` from the
origin. -/
theorem aux_ce_relay_mnorm_ge (d : ℕ) (_hd : 2 ≤ d) (k : ℕ) :
    (k : ℤ) ≤ mnorm (((k : ℤ) • e1 d + e2 d : Site d)) := by
  have h0 : 0 < d := by omega
  have hterm := Finset.single_le_sum
    (f := fun j : Fin d => |(((k : ℤ) • e1 d + e2 d : Site d)) j|)
    (fun j _ => abs_nonneg _) (Finset.mem_univ ⟨0, h0⟩)
  have hval : (((k : ℤ) • e1 d + e2 d : Site d)) ⟨0, h0⟩ = (k : ℤ) := by
    simp [e1, e2, Pi.add_apply]
  rw [hval, abs_of_nonneg (Nat.cast_nonneg k)] at hterm
  exact hterm

/-- The relay row point at `k` has not fired by time `k` (it first fires at
`k + 2`, by `aux_ce_relay_fires`). -/
theorem aux_ce_relay_not_yet (d : ℕ) (hd : 2 ≤ d) (k : ℕ) :
    podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) k ((k : ℤ) • e1 d + e2 d) = 0 := by
  by_contra hne
  have hnn := aux_podo_nonneg (fun x => ceEta d x + 3 * dirac (0 : Site d) x) k
    ((k : ℤ) • e1 d + e2 d)
  have hpos : 0 < podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) k
      ((k : ℤ) • e1 d + e2 d) := by omega
  have hb := aux_ce_s0_mnorm_le d hd 3 k ((k : ℤ) • e1 d + e2 d) hpos
  have hge := aux_ce_relay_mnorm_ge d hd k
  omega


theorem aux_ce_not_stab3_direct (d : ℕ) (hd : 2 ≤ d) :
    ¬ Stabilizable (fun x => ceEta d x + 3 * dirac (0 : Site d) x) := by
  rintro ⟨T, hT⟩
  have hfire := aux_ce_relay_fires d hd T
  have hnotyet := aux_ce_relay_not_yet d hd T
  have heq := hT (T + 2) (by omega)
  rw [heq, hnotyet] at hfire
  exact absurd hfire (lt_irrefl 0)

/-- `aux_ce_threshold` without `hFMR`, by the same bookkeeping as
`aux_ce_sInf_eq`/`aux_ce_threshold`, using `aux_ce_not_stab3_direct` in place
of `aux_ce_not_stab3 d hd hFMR`. -/
theorem aux_ce_sInf_eq' (d : ℕ) (hd : 2 ≤ d) :
    sInf {n : ℕ | 1 ≤ n ∧ ¬ Stabilizable (fun x => ceEta d x + n * dirac (0 : Site d) x)} = 3 := by
  have h3 : ¬ Stabilizable (fun x => ceEta d x + 3 * dirac (0 : Site d) x) :=
    aux_ce_not_stab3_direct d hd
  have h1 : Stabilizable (fun x => ceEta d x + 1 * dirac (0 : Site d) x) :=
    aux_ce_stab_small d hd 1 (by norm_num)
  have h2 : Stabilizable (fun x => ceEta d x + 2 * dirac (0 : Site d) x) :=
    aux_ce_stab_small d hd 2 (by norm_num)
  have hmem3 : (3 : ℕ) ∈ {n : ℕ | 1 ≤ n ∧ ¬ Stabilizable (fun x => ceEta d x + n * dirac (0 : Site d) x)} :=
    ⟨by norm_num, h3⟩
  have hmem : sInf {n : ℕ | 1 ≤ n ∧ ¬ Stabilizable (fun x => ceEta d x + n * dirac (0 : Site d) x)} ∈
      {n : ℕ | 1 ≤ n ∧ ¬ Stabilizable (fun x => ceEta d x + n * dirac (0 : Site d) x)} :=
    Nat.sInf_mem ⟨3, hmem3⟩
  have hge : (1 : ℕ) ≤ sInf {n : ℕ | 1 ≤ n ∧ ¬ Stabilizable (fun x => ceEta d x + n * dirac (0 : Site d) x)} :=
    hmem.1
  refine le_antisymm (Nat.sInf_le hmem3) ?_
  by_contra hc
  have hclt : sInf {n : ℕ | 1 ≤ n ∧ ¬ Stabilizable (fun x => ceEta d x + n * dirac (0 : Site d) x)} < 3 :=
    not_le.mp hc
  have hcase : sInf {n : ℕ | 1 ≤ n ∧ ¬ Stabilizable (fun x => ceEta d x + n * dirac (0 : Site d) x)} = 1 ∨
      sInf {n : ℕ | 1 ≤ n ∧ ¬ Stabilizable (fun x => ceEta d x + n * dirac (0 : Site d) x)} = 2 := by
    omega
  rcases hcase with hc1 | hc2
  · rw [hc1] at hmem
    exact hmem.2 h1
  · rw [hc2] at hmem
    exact hmem.2 h2

theorem aux_ce_threshold' (d : ℕ) (hd : 2 ≤ d) :
    explosionThreshold (ceEta d) = 3 := by
  show sInf {n : ℕ | 1 ≤ n ∧ ¬ Stabilizable (fun x => ceEta d x + n * dirac (0 : Site d) x)} = 3
  exact aux_ce_sInf_eq' d hd


/-- **The counterexample's low-type case, first step.**  A low-type point
`n•e₁` (`n ≡ 0, 3 mod 4`) has `ceEta = 2d-3`.  Its two row-0 neighbours are
`(n-1)•e₁` and `(n+1)•e₁`; the latter is high type when `n ≡ 0 mod 4`.  So the
low point receives one chip from the relay row and one from its high neighbour,
giving `2d-1` — one short.  The paper's front supplies the missing chip. -/
theorem low_neighbour_high (n : ℤ) (hn : n % 4 = 0) :
    (n + 1) % 4 = 1 := by omega

theorem low_neighbour_high' (n : ℤ) (hn : n % 4 = 3) :
    (n + 1) % 4 = 0 := by omega

/-- The low point's total after both contributions is `2d-1`, one short of the
threshold `2d`. -/
theorem low_short (d : ℕ) : (2 * (d : ℤ) - 3) + 1 + 1 = 2 * (d : ℤ) - 1 := by ring

/-- Bookkeeping for `aux_ce_stack_le_2D_step`: the two extra `ζ₁`-stacking
coordinates cancel between `ceEta d x` and `ceEta 2 (proj x) + 2*(d-2)`. -/
theorem aux_ce_stack_eta_eq (d : ℕ) (hd : 2 ≤ d) (x : Site d) :
    ceEta d x = ceEta 2 (fun i : Fin 2 => if (i : ℕ) = 0 then x ⟨0, by omega⟩ else x ⟨1, by omega⟩)
      + 2 * ((d : ℤ) - 2) := by
  have h0 : 0 < d := by omega
  have h1 : 1 < d := by omega
  unfold ceEta
  simp [h0, h1]
  ring

/-- The inductive step of Step 3' (exploding.tex:1797-1811), the hard core:
if the `d`-dim odometer at time `t` is dominated pointwise by the projected
2D odometer (`ih`), it still is at `t+1`.  PROOF PLAN (paper's own case
split).  Fix `x`, write `x̄` for its projection.  If `podo d t x < podo 2D t
x̄` (strict): `podo d (t+1) x ≤ podo d t x + 1 ≤ podo 2D t x̄ ≤ podo 2D (t+1)
x̄` via `podo_mono_step`, done.  Otherwise `podo d t x = podo 2D t x̄ =: v`
(equality, from `ih`).  Unfold `pconf d t x = ceEta d x + nbrSumZ (podo d t)
x - 2d*v` (`pconf`, `lap_eq`) and split the `2d`-term sum `∑_{i:Fin d}` at
`i = ⟨0,h₀⟩, ⟨1,h₁⟩` versus the remaining `d - 2` indices: for `i ≥ 2` (in the
`(i:ℕ)` sense), `x ± unit i` projects to `x̄` again (`unit i`'s first two
coordinates vanish, `aux_unit_apply`), so those `2(d-2)` neighbour terms are
each `≤ v` by `ih`; for `i = ⟨0,h₀⟩` or `⟨1,h₁⟩`, `x ± unit i` projects to
`x̄ ± unit (matching Fin 2 index)`, so those `4` terms are bounded by the
corresponding `podo 2D t` neighbour values via `ih`.  Summing, `nbrSumZ (podo
d t) x ≤ nbrSumZ (podo 2D t) x̄ + 2*(d-2)*v`.  With `aux_ce_stack_eta_eq`,
`pconf d t x ≤ ceEta 2 x̄ + 2*(d-2) + nbrSumZ (podo 2D t) x̄ + 2*(d-2)*v -
2d*v = pconf 2D t x̄ + 2*(d-2) - 2*(d-2)*v ... ` reduces (using `v` common to
both sides, exactly the paper's algebra at exploding.tex:1801-1811) to
`pconf d t x ≥ 2d ↔ pconf 2D t x̄ ≥ 4`, so `d`'s firing at `x` forces `2D`'s
firing at `x̄`, giving `podo d (t+1) x = v + 1 = podo 2D (t+1) x̄` (or `≤` if
`2D` alone fires without `d` needing to). -/
theorem aux_ce_stack_le_2D_step (d : ℕ) (hd : 2 ≤ d) (t : ℕ)
    (ih : ∀ x : Site d, podo (explodingPile (ceEta d)) t x ≤
      podo (explodingPile (ceEta 2)) t
        (fun i : Fin 2 => if (i : ℕ) = 0 then x ⟨0, by omega⟩ else x ⟨1, by omega⟩)) :
    ∀ x : Site d, podo (explodingPile (ceEta d)) (t + 1) x ≤
      podo (explodingPile (ceEta 2)) (t + 1)
        (fun i : Fin 2 => if (i : ℕ) = 0 then x ⟨0, by omega⟩ else x ⟨1, by omega⟩) := by
  have h0 : 0 < d := by omega
  have h1 : 1 < d := by omega
  set proj := fun (x : Site d) (i : Fin 2) => if (i : ℕ) = 0 then x ⟨0, h0⟩ else x ⟨1, h1⟩ with hproj
  have h_proj_add_zero : ∀ x : Site d, proj (x + unit ⟨0, h0⟩) = proj x + unit 0 := by
    intro x; ext i; fin_cases i <;> simp [proj, unit, Pi.add_apply]
  have h_proj_sub_zero : ∀ x : Site d, proj (x - unit ⟨0, h0⟩) = proj x - unit 0 := by
    intro x; ext i; fin_cases i <;> simp [proj, unit, Pi.sub_apply]
  have h_proj_add_one : ∀ x : Site d, proj (x + unit ⟨1, h1⟩) = proj x + unit 1 := by
    intro x; ext i; fin_cases i <;> simp [proj, unit, Pi.add_apply]
  have h_proj_sub_one : ∀ x : Site d, proj (x - unit ⟨1, h1⟩) = proj x - unit 1 := by
    intro x; ext i; fin_cases i <;> simp [proj, unit, Pi.sub_apply]
  have h_proj_add_ge2 : ∀ (x : Site d) (i : Fin d), 2 ≤ (i : ℕ) → proj (x + unit i) = proj x := by
    intro x i hi
    ext j
    fin_cases j
    · simp [proj, unit, Pi.add_apply]
      by_cases h_eq : (⟨0, h0⟩ : Fin d) = i
      · exfalso; have h_val : (⟨0, h0⟩ : Fin d).val = i.val := congrArg Fin.val h_eq; simp at h_val; omega
      · simp [h_eq]
    · simp [proj, unit, Pi.add_apply]
      by_cases h_eq : (⟨1, h1⟩ : Fin d) = i
      · exfalso; have h_val : (⟨1, h1⟩ : Fin d).val = i.val := congrArg Fin.val h_eq; simp at h_val; omega
      · simp [h_eq]
  have h_proj_sub_ge2 : ∀ (x : Site d) (i : Fin d), 2 ≤ (i : ℕ) → proj (x - unit i) = proj x := by
    intro x i hi
    ext j
    fin_cases j
    · simp [proj, unit, Pi.sub_apply]
      by_cases h_eq : (⟨0, h0⟩ : Fin d) = i
      · exfalso; have h_val : (⟨0, h0⟩ : Fin d).val = i.val := congrArg Fin.val h_eq; simp at h_val; omega
      · simp [h_eq]
    · simp [proj, unit, Pi.sub_apply]
      by_cases h_eq : (⟨1, h1⟩ : Fin d) = i
      · exfalso; have h_val : (⟨1, h1⟩ : Fin d).val = i.val := congrArg Fin.val h_eq; simp at h_val; omega
      · simp [h_eq]
  have h_dirac_le : ∀ x : Site d, dirac (0 : Site d) x ≤ dirac (0 : Site 2) (proj x) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      have h_proj0 : proj (0 : Site d) = (0 : Site 2) := by
        ext i; fin_cases i <;> simp [proj]
      simp [dirac, h_proj0]
    · rw [dirac_of_ne hx]
      by_cases hproj0 : proj x = (0 : Site 2)
      · rw [hproj0]; simp [dirac]
      · simp [dirac_of_ne hproj0]
  have h_eta_eq : ∀ x : Site d, ceEta d x = ceEta 2 (proj x) + 2 * ((d : ℤ) - 2) := by
    intro x
    unfold ceEta zeta1 proj
    simp [h0, h1]
    ring
  intro x
  set s0_d := explodingPile (ceEta d) with hs0_d
  set s0_2 := explodingPile (ceEta 2) with hs0_2
  set v := podo s0_d t with hv
  set v2 := podo s0_2 t with hv2
  have h_ih : v x ≤ v2 (proj x) := ih x
  -- Key combinatorial inequality for nbrSumZ
  have h_nbrSumZ : nbrSumZ v x ≤ nbrSumZ v2 (proj x) + 2 * ((d : ℤ) - 2) * v2 (proj x) := by
    unfold nbrSumZ
    have h_bound : ∀ i : Fin d, v (x + unit i) + v (x - unit i) ≤
        v2 (proj (x + unit i)) + v2 (proj (x - unit i)) := by
      intro i
      have h1 := ih (x + unit i)
      have h2 := ih (x - unit i)
      linarith
    have h_sum_le : (∑ i : Fin d, (v (x + unit i) + v (x - unit i))) ≤
        (∑ i : Fin d, (v2 (proj (x + unit i)) + v2 (proj (x - unit i)))) :=
      Finset.sum_le_sum fun i _ => h_bound i
    have h_rhs_eq : (∑ i : Fin d, (v2 (proj (x + unit i)) + v2 (proj (x - unit i)))) =
        (∑ j : Fin 2, (v2 (proj x + unit j) + v2 (proj x - unit j))) + 2 * ((d : ℤ) - 2) * v2 (proj x) := by
      let f (i : Fin d) : ℤ := v2 (proj (x + unit i)) + v2 (proj (x - unit i))
      let A : Finset (Fin d) := {⟨0, h0⟩, ⟨1, h1⟩}
      have h_split : (∑ i : Fin d, f i) = (∑ i ∈ A, f i) + (∑ i ∈ Aᶜ, f i) :=
        (Finset.sum_add_sum_compl (s := A) (f := f)).symm
      have h_A_compl_eq : Aᶜ = (Finset.univ : Finset (Fin d)) \ A := by
        ext i; simp [A]
      rw [h_split, h_A_compl_eq]
      have h_sum_A : (∑ i ∈ A, f i) = (∑ j : Fin 2, (v2 (proj x + unit j) + v2 (proj x - unit j))) := by
        unfold A
        have h0sum : f ⟨0, h0⟩ = v2 (proj x + unit 0) + v2 (proj x - unit 0) := by
          unfold f; simp [h_proj_add_zero x, h_proj_sub_zero x]
        have h1sum : f ⟨1, h1⟩ = v2 (proj x + unit 1) + v2 (proj x - unit 1) := by
          unfold f; simp [h_proj_add_one x, h_proj_sub_one x]
        simp [Finset.sum_insert, Finset.sum_singleton, h0sum, h1sum, Fin.sum_univ_two]
      rw [h_sum_A]
      have h_sum_compl : (∑ i ∈ ((Finset.univ : Finset (Fin d)) \ A), f i) =
          2 * ((d : ℤ) - 2) * v2 (proj x) := by
        have h_term : ∀ i, i ∈ ((Finset.univ : Finset (Fin d)) \ A) → f i = 2 * v2 (proj x) := by
          intro i hi
          have hi_not_A : i ∉ A := (Finset.mem_sdiff.mp hi).2
          unfold A at hi_not_A
          have hi_val_ge2 : 2 ≤ i.val := by
            by_contra h_lt2
            have h_val_lt2 : i.val < 2 := by omega
            have h_val_cases : i.val = 0 ∨ i.val = 1 := by omega
            rcases h_val_cases with h0val | h1val
            · have heq : i = ⟨0, h0⟩ := Fin.ext h0val
              subst heq; exact hi_not_A (by simp)
            · have heq : i = ⟨1, h1⟩ := Fin.ext h1val
              subst heq; exact hi_not_A (by simp)
          unfold f
          rw [h_proj_add_ge2 x i hi_val_ge2, h_proj_sub_ge2 x i hi_val_ge2]
          rw [two_mul]
        rw [Finset.sum_congr rfl h_term]
        simp [Finset.sum_const]
        have h_card : ((Finset.univ : Finset (Fin d)) \ A).card = d - 2 := by
          have hA_sub_univ : A ⊆ Finset.univ := by simp [A]
          have h_card_eq := Finset.card_sdiff_add_card_eq_card hA_sub_univ
          have h_card_univ : (Finset.univ : Finset (Fin d)).card = d := by simp
          have h_card_A : A.card = 2 := by simp [A]
          rw [h_card_univ, h_card_A] at h_card_eq
          omega
        rw [h_card]
        have hd2 : 2 ≤ d := hd
        simp [Nat.cast_sub hd2, Nat.cast_ofNat]
        ring
      rw [h_sum_compl]
    rw [← h_rhs_eq]
    exact h_sum_le
  have h_s0 : s0_d x ≤ s0_2 (proj x) + 2 * ((d : ℤ) - 2) := by
    rw [hs0_d, hs0_2]
    simp only [explodingPile]
    have h_eta := h_eta_eq x
    have h_dirac := h_dirac_le x
    have h_thresh_d : (explosionThreshold (ceEta d) : ℤ) = 3 := by
      exact mod_cast aux_ce_threshold' d hd
    have h_thresh_2 : (explosionThreshold (ceEta 2) : ℤ) = 3 := by
      have h2d : 2 ≤ 2 := by omega
      exact mod_cast aux_ce_threshold' 2 h2d
    rw [h_thresh_d, h_thresh_2]
    linarith
  rw [podo_succ s0_d t x, podo_succ s0_2 t (proj x)]
  rw [← hv, ← hv2]
  -- Goal: v x + (if 2*d ≤ pconf s0_d t x then 1 else 0) ≤ v2 (proj x) + (if 2*2 ≤ pconf s0_2 t (proj x) then 1 else 0)
  by_cases h_eq : v x = v2 (proj x)
  · have h_pconf : pconf s0_d t x ≤ pconf s0_2 t (proj x) + 2 * ((d : ℤ) - 2) := by
      rw [pconf, pconf]
      simp only [lap_eq]
      rw [← hv, ← hv2]
      have h_nbr := h_nbrSumZ
      have h_s0' := h_s0
      rw [← h_eq] at h_nbr
      -- h_nbr: nbrSumZ v x ≤ nbrSumZ v2 (proj x) + 2*(d-2)*v x
      -- h_s0': s0_d x ≤ s0_2 (proj x) + 2*(d-2)
      rw [← h_eq]
      -- Goal: s0_d x + (nbrSumZ v x - 2*d*v x) ≤ s0_2 (proj x) + (nbrSumZ v2 (proj x) - 4*v x) + 2*(d-2)
      have h_sum : s0_d x + nbrSumZ v x ≤ s0_2 (proj x) + nbrSumZ v2 (proj x) + 2 * ((d : ℤ) - 2) + 2 * ((d : ℤ) - 2) * v x := by
        linarith
      calc
        s0_d x + (nbrSumZ v x - 2 * (d : ℤ) * v x) = (s0_d x + nbrSumZ v x) - 2 * (d : ℤ) * v x := by ring
        _ ≤ (s0_2 (proj x) + nbrSumZ v2 (proj x) + 2 * ((d : ℤ) - 2) + 2 * ((d : ℤ) - 2) * v x) - 2 * (d : ℤ) * v x :=
          sub_le_sub_right h_sum (2 * (d : ℤ) * v x)
        _ = s0_2 (proj x) + (nbrSumZ v2 (proj x) - 4 * v x) + 2 * ((d : ℤ) - 2) := by ring
    rw [h_eq]
    by_cases h_fire : 2 * d ≤ pconf s0_d t x
    · have h_fire_2d : 4 ≤ pconf s0_2 t (proj x) := by
        omega
      simp [h_fire, h_fire_2d]
    · have hpos : 0 ≤ (if 4 ≤ pconf s0_2 t (proj x) then (1 : ℤ) else 0) := by
        split <;> norm_num
      rw [if_neg h_fire]
      have htemp := add_le_add_right hpos (v2 (proj x))
      simpa [add_comm, show (2 : ℤ) * 2 = (4 : ℤ) by norm_num] using htemp
  · have h_lt : v x < v2 (proj x) := lt_of_le_of_ne h_ih h_eq
    have h_bound : v x + 1 ≤ v2 (proj x) := by omega
    have h2c : (2 : ℤ) * 2 = 2 * ((2 : ℕ) : ℤ) := by norm_num
    by_cases h_fire_2d : 2 * ((2 : ℕ) : ℤ) ≤ pconf s0_2 t (proj x)
    · rw [if_pos h_fire_2d]
      by_cases h_fire_d : 2 * d ≤ pconf s0_d t x
      · rw [if_pos h_fire_d]; omega
      · rw [if_neg h_fire_d]
        omega
    · rw [if_neg h_fire_2d]
      by_cases h_fire_d : 2 * d ≤ pconf s0_d t x
      · rw [if_pos h_fire_d]; omega
      · rw [if_neg h_fire_d]
        omega

/-- Steps 3-4 (exploding.tex:1443-1726), hard, `T((3+8n)e₁) ≥ 12n` in 2D.
CONFIRMED (this pass) genuinely NOT a mechanical further split of the current
toolkit: the paper's own four sub-steps split into two that need brand-new
Lean INFRASTRUCTURE (not new mathematics -- the paper supplies the full
argument) rather than a restatement from existing pieces, and two that are
routine given that infrastructure:
(3a) `-- GAP`, NEEDS-PROOF-DESIGN: replace `ζ₁` by the cylinder background
     `ζ`, reflect across `x₁ = -1/2` (`v_t(-1,x₂) := v_t(0,x₂)`, an extra
     SELF-LOOP at the boundary, not a frozen exterior) and fold `x₂` mod `4`
     onto a symmetrised Laplacian on `{x₁ ≥ 0} × ℤ/4`.  Checked: no cylinder,
     reflection, or folded-Laplacian object exists anywhere in this
     repository (`grep`-confirmed empty in `Exploding/`), and
     `Exploding.fodo`'s `S`-frozen odometer only supports a FROZEN exterior
     held at a fixed `w₀`, not this reflected/coupled one, so it cannot
     stand in for it.  The paper cites "Lemma 2.3 in [bou2020dynamic]" for
     identifying the resulting folded process with the honest `Site 2`
     odometer's restriction to `{x₁ ≥ 0}`; formalizing it needs a NEW
     recursive definition (a `cylOdo` on, e.g., `ℤ × Fin 4` with a
     hand-written reflected/toroidal neighbour-sum) plus the symmetry lemma
     identifying it with `podo (explodingPile (ceEta 2))` restricted to the
     half-plane -- a genuine, self-contained but substantial design task for
     a future pass, not attempted here.
(3b) TRACTABLE once (3a)'s objects exist: the comparison `v_t ≤ w_t + ũ`, a
     clean induction written out in full at exploding.tex:1506-1513, in
     exactly the same style as `aux_te_podo_mono`/`aux_ce_stack_le_2D_step`
     above (compare two odometers on the SAME domain via a fixed pointwise
     offset function).
(4a) TRACTABLE once (3a)'s objects exist: reduce `w_t` to its last wave with
     the displayed `{0,1}` initial data, "identical to Step 1 of Proposition
     4.1" (`prop-approximate-subadditive`'s own already-present machinery,
     just not yet wired to a cylinder domain).
(4b) `-- GAP`, NEEDS-PROOF-DESIGN: the pulsating front, 12 steps of the last
     wave on the cylinder translate the front configuration by 8 columns,
     which the paper itself verifies "by manual computation" on an explicit
     `4x13` window.  Recommended route (unchanged from the prior pass):
     define the front recursion on a fixed finite window as a computable
     `Fin 13 → Fin 4 → ℤ` iteration and discharge "12 steps shift the front
     by 8" via `decide`/`native_decide`, then a NEW locality lemma (the front
     only interacts with columns within distance `1` per step) transfers the
     window computation to the infinite cylinder.  This needs (3a)'s cylinder
     object to even state, and is a genuinely separate, self-contained
     finite-computation task once that object exists.
Both GAPs need the SAME missing object ((3a)'s cylinder/reflected process);
until it is designed, (3b)/(4a)/(4b) cannot be stated as separate Lean
lemmas either (they are all ABOUT that object).  This is why the file's own
prior "needs further split" note could not, in this pass, be turned into
additional standalone `sorry` declarations without guessing at that object's
definition -- which risks a silently wrong formalization more than it helps
a later prover. -/

theorem aux_arrival_unfold (d : ℕ) (η : Site d → ℤ) (x : Site d) :
    arrival η x = sInf {t : ℕ∞ | ∃ k : ℕ, t = (k : ℕ∞) ∧ 1 ≤ k ∧
      0 < podo (explodingPile η) k x} := rfl

theorem aux_ce_explodingPile_eq (d : ℕ) (hd : 2 ≤ d) :
    explodingPile (ceEta d) = (fun x => ceEta d x + 3 * dirac (0 : Site d) x) := by
  funext x
  simp only [explodingPile, aux_ce_threshold' d hd]
  norm_num

/-- Packages a single witness time `m` at which `(n•e₁)` has fired into the
bound `arrival (ceEta d) (n•e₁) ≤ m`. -/
theorem aux_ce_arrival_le (d : ℕ) (hd : 2 ≤ d) (n : ℕ) (m : ℕ) (hm1 : 1 ≤ m)
    (hpos : 0 < podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) m ((n : ℤ) • e1 d)) :
    arrival (ceEta d) ((n : ℤ) • e1 d) ≤ (m : ℕ∞) := by
  rw [aux_arrival_unfold]
  apply sInf_le
  refine ⟨m, rfl, hm1, ?_⟩
  rw [aux_ce_explodingPile_eq d hd]
  exact hpos

/-- Corollary of `aux_ce_arrival_le`: such a witness proves finiteness. -/
theorem aux_ce_arrival_finite_of_pos (d : ℕ) (hd : 2 ≤ d) (n : ℕ) (m : ℕ) (hm1 : 1 ≤ m)
    (hpos : 0 < podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) m ((n : ℤ) • e1 d)) :
    arrival (ceEta d) ((n : ℤ) • e1 d) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENat.coe_ne_top m) (aux_ce_arrival_le d hd n m hm1 hpos)

theorem aux_mnorm_nsmul_e1_ge (d : ℕ) (hd : 1 ≤ d) (n : ℕ) :
    (n : ℤ) ≤ mnorm (((n : ℤ) • e1 d : Site d)) := by
  have hterm := Finset.single_le_sum
    (f := fun j : Fin d => |(((n : ℤ) • e1 d : Site d) j)|)
    (fun j _ => abs_nonneg _) (Finset.mem_univ ⟨0, hd⟩)
  have hval : (((n : ℤ) • e1 d : Site d) ⟨0, hd⟩) = (n : ℤ) := by
    simp [e1, Pi.smul_apply]
  rw [hval, abs_of_nonneg (Nat.cast_nonneg n)] at hterm
  exact hterm

theorem aux_podo_mnorm_le (d : ℕ) (_hd : 2 ≤ d) :
    ∀ t : ℕ, ∀ x : Site d,
      0 < podo (explodingPile (ceEta d)) t x → mnorm x + 1 ≤ t := by
  intro t
  induction t with
  | zero => intro x h; simp at h
  | succ t ih =>
    intro x hx
    rw [podo_succ] at hx
    by_cases h0 : 0 < podo (explodingPile (ceEta d)) t x
    · have := ih x h0
      omega
    · have hge : 2 * d ≤ pconf (explodingPile (ceEta d)) t x := by
        by_cases hc : 2 * d ≤ pconf (explodingPile (ceEta d)) t x
        · exact hc
        · simp [hc] at hx
          omega
      have hnng : 0 ≤ podo (explodingPile (ceEta d)) t x := aux_podo_nonneg _ t x
      have hz : podo (explodingPile (ceEta d)) t x = 0 := by omega
      have hpe : pconf (explodingPile (ceEta d)) t x =
          explodingPile (ceEta d) x + nbrSumZ (podo (explodingPile (ceEta d)) t) x := by
        simp only [pconf, lap_eq]
        rw [hz]
        ring
      by_cases hx0 : x = 0
      · subst hx0
        have hm0 : mnorm (0 : Site d) = 0 := by simp [mnorm]
        omega
      · have hSx : explodingPile (ceEta d) x = ceEta d x := by
          simp only [explodingPile]
          rw [dirac_of_ne hx0, mul_zero, add_zero]
        have hbd := aux_ceEta_bounds d x
        have hnbr : 0 < nbrSumZ (podo (explodingPile (ceEta d)) t) x := by
          have h2 : 2 * d ≤ ceEta d x + nbrSumZ (podo (explodingPile (ceEta d)) t) x := by
            calc 2 * d ≤ pconf (explodingPile (ceEta d)) t x := hge
              _ = explodingPile (ceEta d) x
                    + nbrSumZ (podo (explodingPile (ceEta d)) t) x := hpe
              _ = ceEta d x + nbrSumZ (podo (explodingPile (ceEta d)) t) x := by rw [hSx]
          omega
        rcases aux_nbrSumZ_pos_neighbour d (podo (explodingPile (ceEta d)) t) x hnbr with
          ⟨i, hi⟩ | ⟨i, hi⟩
        · have hrec := ih (x + unit i) hi
          have hmm := aux_mnorm_le_add_unit d x i
          omega
        · have hrec := ih (x - unit i) hi
          have hmm := aux_mnorm_le_sub_unit d x i
          omega

theorem aux_arrival_lower (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    ((n + 1 : ℕ) : ℕ∞) ≤ arrival (ceEta d) ((n : ℤ) • e1 d) := by
  rw [aux_arrival_unfold]
  refine le_sInf ?_
  rintro t ⟨k, rfl, hk1, hk⟩
  have hm : mnorm (((n : ℤ) • e1 d : Site d)) + 1 ≤ k :=
    aux_podo_mnorm_le d hd k ((n : ℤ) • e1 d) hk
  have hmn : (n : ℤ) ≤ mnorm (((n : ℤ) • e1 d : Site d)) :=
    aux_mnorm_nsmul_e1_ge d (by omega) n
  refine ENat.coe_le_coe.mpr ?_
  omega

theorem aux_ce_speed (d : ℕ) (hd : 2 ≤ d) (n m : ℕ)
    (h : arrival (ceEta d) ((n : ℤ) • e1 d) = (m : ℕ∞)) : n ≤ m := by
  have key := aux_arrival_lower d hd n
  rw [h] at key
  have hm := ENat.coe_le_coe.mp key
  omega

/-- Step 1 upper bound (exploding.tex:1386-1389), medium: `T((4n+1)e₁) ≤ 4n+4`.
The row `x₁ = 1` is all `2d-1`; the origin fires at `t=1`, `e₂` at `t=2`, the
row carries the firing one step per unit time, reaching `e₂+(4n+1)e₁` at
`4n+3`, then `(4n+1)e₁` at `4n+4`.  Explicit induction on `n` along the row.
For `d ≥ 3` the extra coordinates are held at `0`; the argument is identical. -/
theorem aux_ce_fast (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    ∃ m : ℕ, arrival (ceEta d) (((4 * n + 1 : ℕ) : ℤ) • e1 d) = (m : ℕ∞) ∧ m ≤ 4 * n + 4 := by
  have hmod : ((4 * n + 1 : ℕ) : ℤ) % 4 = 1 := by omega
  have hpos := aux_ce_row0_lands d hd ((4 * n + 1 : ℕ) : ℤ) (Or.inl hmod) (by positivity)
  have htoNat : (((4 * n + 1 : ℕ) : ℤ)).toNat = 4 * n + 1 := by omega
  rw [htoNat] at hpos
  have harg : 4 * n + 1 + 3 = 4 * n + 4 := by omega
  rw [harg] at hpos
  have hle := aux_ce_arrival_le d hd (4 * n + 1) (4 * n + 4) (by omega) hpos
  have hne := aux_ce_arrival_finite_of_pos d hd (4 * n + 1) (4 * n + 4) (by omega) hpos
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
  refine ⟨m, hm.symm, ?_⟩
  rw [← hm] at hle
  exact ENat.coe_le_coe.mp hle



def cylNbrSum (u : ℤ × Fin 4 → ℤ) (x : ℤ × Fin 4) : ℤ :=
  (if x.1 = 0 then 2 * u x else u (x.1 - 1, x.2) + u (x.1 + 1, x.2)) +
    (u (x.1, x.2 + 1) + u (x.1, x.2 - 1))

def cylLap (u : ℤ × Fin 4 → ℤ) (x : ℤ × Fin 4) : ℤ :=
  cylNbrSum u x - 4 * u x

def cylOdo (s0 : ℤ × Fin 4 → ℤ) : ℕ → ℤ × Fin 4 → ℤ
  | 0 => fun _ => 0
  | t + 1 => fun x =>
      cylOdo s0 t x + (if 8 ≤ s0 x + cylLap (cylOdo s0 t) x then 1 else 0)

@[simp] theorem cylOdo_zero (s0 : ℤ × Fin 4 → ℤ) : cylOdo s0 0 = fun _ => 0 := rfl

theorem cylOdo_succ (s0 : ℤ × Fin 4 → ℤ) (t : ℕ) (x : ℤ × Fin 4) :
    cylOdo s0 (t + 1) x = cylOdo s0 t x +
      (if 8 ≤ s0 x + cylLap (cylOdo s0 t) x then 1 else 0) := rfl

/-- The cylinder odometer is nondecreasing in time. -/
theorem cylOdo_mono (s0 : ℤ × Fin 4 → ℤ) (t : ℕ) (x : ℤ × Fin 4) :
    cylOdo s0 t x ≤ cylOdo s0 (t + 1) x := by
  rw [cylOdo_succ]
  split <;> omega

/-- The cylinder odometer is monotone in time. -/
theorem cylOdo_mono_time (s0 : ℤ × Fin 4 → ℤ) {s t : ℕ} (h : s ≤ t) (x : ℤ × Fin 4) :
    cylOdo s0 s x ≤ cylOdo s0 t x := by
  induction t with
  | zero => simp at h; subst h; exact le_refl _
  | succ t ih =>
    rcases Nat.lt_or_ge s (t + 1) with hlt | hge
    · exact le_trans (ih (Nat.lt_succ_iff.mp hlt)) (cylOdo_mono s0 t x)
    · have hs : s = t + 1 := le_antisymm (by omega) hge
      rw [hs]


/-- `ζ₁` is 4-periodic in its second coordinate. -/
theorem zeta1_periodic_4 (a b : ℤ) : zeta1 a (b + 4) = zeta1 a b := by
  have h : (b + 4) % 4 = b % 4 := by omega
  simp only [zeta1, h]



/-- `ζ₁` depends only on its second coordinate mod 4. -/
theorem zeta1_mod_4 (a b : ℤ) : zeta1 a (b % 4) = zeta1 a b := by
  have h : (b % 4) % 4 = b % 4 := by omega
  simp only [zeta1, h]




def cylProj (x : Site 2) : ℤ × Fin 4 :=
  (x ⟨0, by norm_num⟩, Fin.ofNat 4 (x ⟨1, by norm_num⟩).toNat)

def cylEta (x : ℤ × Fin 4) : ℤ :=
  zeta1 x.1 (x.2 : ℕ)

/-- **The cylinder background is the folded `ζ₁`.** -/
theorem cylEta_cylProj (x : Site 2) (hx2 : 0 ≤ x ⟨1, by norm_num⟩) :
    cylEta (cylProj x) = zeta1 (x ⟨0, by norm_num⟩) (x ⟨1, by norm_num⟩ % 4) := by
  unfold cylEta cylProj
  congr 1
  -- `(Fin.ofNat 4 n : ℕ) = n % 4`, and `ζ₁` depends only on `% 4`
  rw [show ((Fin.ofNat 4 (x ⟨1, by norm_num⟩).toNat : Fin 4) : ℕ)
      = (x ⟨1, by norm_num⟩).toNat % 4 from Fin.val_ofNat 4 _]
  have h1 : ((x ⟨1, by norm_num⟩).toNat % 4 : ℤ) = x ⟨1, by norm_num⟩ % 4 := by
    have h2 : ((x ⟨1, by norm_num⟩).toNat : ℤ) = x ⟨1, by norm_num⟩ :=
      Int.toNat_of_nonneg hx2
    have h3 : ((x ⟨1, by norm_num⟩).toNat % 4 : ℤ)
        = ((x ⟨1, by norm_num⟩).toNat : ℤ) % 4 := by push_cast; ring
    rw [h3, h2]
  exact h1


end Exploding
