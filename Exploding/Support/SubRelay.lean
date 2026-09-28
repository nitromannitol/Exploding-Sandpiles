/-
The relay induction of the counterexample of `paper/exploding.tex` Section 6
(`exploding.tex:1386-1389`): on the stacked checkerboard background the front on
the relay row `x₁ = 1` advances at unit speed, reaching position `k` by time
`k + 2`.  This is Step 1's upper bound in the proof of `theorem:counterexample`.
-/
import Exploding.Support.Vocab

namespace Exploding

open LatticeProb

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

end Exploding

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
