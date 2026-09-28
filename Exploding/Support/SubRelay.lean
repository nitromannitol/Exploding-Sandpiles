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

end Exploding
