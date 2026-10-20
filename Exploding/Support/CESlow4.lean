/-
The slow bound of `theorem:counterexample` in dimension two:
`T((3 + 8n) e₁) ≥ 12 n` (Step 4 of the proof of `exploding-corrected-arxiv.tex`, Section 6), and
finiteness of the arrival time.
-/
import Exploding.Support.CESlow3

namespace Exploding

open LatticeProb

theorem cels_tau_axis (n : ℕ) : cels_tau ((3 + 8 * n : ℕ) : ℤ) 0 = 12 * (n : ℤ) + 8 := by
  have hcol : cels_col ((3 + 8 * n : ℕ) : ℤ) = 3 := by
    unfold cels_col
    rw [if_neg (by omega)]
    omega
  have hsh : cels_sh ((3 + 8 * n : ℕ) : ℤ) = 12 * (n : ℤ) := by
    unfold cels_sh
    rw [if_neg (by omega)]
    omega
  have hlk : cels_lk 3 0 = 8 := by decide
  unfold cels_tau
  rw [hcol, hsh, hlk]
  ring

/-- The odometer vanishes at `(3 + 8n) e₁` before time `12 n + 8`. -/
theorem cels_podo_axis (n k : ℕ) (hk : k < 12 * n + 8) :
    podo (fun y => ceEta 2 y + 3 * dirac (0 : Site 2) y) k ((((3 + 8 * n : ℕ) : ℤ)) • e1 2) = 0 := by
  have hle := cels_podo_le k ((((3 + 8 * n : ℕ) : ℤ)) • e1 2)
  have hnn := aux_podo_nonneg (fun y => ceEta 2 y + 3 * dirac (0 : Site 2) y) k
    ((((3 + 8 * n : ℕ) : ℤ)) • e1 2)
  have hx0 : ((((3 + 8 * n : ℕ) : ℤ)) • e1 2 : Site 2) 0 = ((3 + 8 * n : ℕ) : ℤ) := by
    simp [e1]
  have hx1 : ((((3 + 8 * n : ℕ) : ℤ)) • e1 2 : Site 2) 1 = 0 := by
    simp [e1]
  have hW : cels_wP k ((((3 + 8 * n : ℕ) : ℤ)) • e1 2) = 0 := by
    unfold cels_wP cels_w
    rw [hx0, hx1]
    have hf : cels_fold ((3 + 8 * n : ℕ) : ℤ) = ((3 + 8 * n : ℕ) : ℤ) := by
      unfold cels_fold
      rw [if_pos (by omega)]
    rw [hf]
    have hu : cels_u ((3 + 8 * n : ℕ) : ℤ) (0 % 4) = 0 := by
      unfold cels_u zeta1
      have h4 : ((3 + 8 * n : ℕ) : ℤ) % 4 = 3 := by omega
      rw [h4]
      norm_num
    have hW0 : cels_W (k : ℤ) ((3 + 8 * n : ℕ) : ℤ) (0 % 4) = 0 := by
      unfold cels_W
      have h0 : (0 : ℤ) % 4 = 0 := by norm_num
      have hne : ¬ (((3 + 8 * n : ℕ) : ℤ) = 0 ∧ (0 : ℤ) % 4 = 0) := by omega
      rw [if_neg hne, h0, if_pos]
      rw [cels_tau_axis]
      omega
    unfold cels_cw
    rw [hu, hW0]
    norm_num
  omega

/-- **The slow bound of Theorem 6.1, Step 4.**  The arrival time at `(3 + 8n) e₁` of the
explosion of `ceEta 2` is finite and at least `12 n`. -/
theorem cels_slow2D : ∀ n : ℕ, ∃ m : ℕ,
    arrival (ceEta 2) (((3 + 8 * n : ℕ) : ℤ) • e1 2) = (m : ℕ∞) ∧ 12 * n ≤ m := by
  intro n
  obtain ⟨T, hT, _⟩ := cel_upper 2 le_rfl (3 + 8 * n)
  refine ⟨T, hT, ?_⟩
  have hlow : ((12 * n : ℕ) : ℕ∞) ≤ arrival (ceEta 2) (((3 + 8 * n : ℕ) : ℤ) • e1 2) := by
    rw [aux_arrival_unfold]
    refine le_sInf ?_
    rintro t ⟨k, rfl, hk1, hk⟩
    rw [aux_ce_explodingPile_eq 2 le_rfl] at hk
    refine ENat.coe_le_coe.mpr ?_
    by_contra hcon
    have h0 := cels_podo_axis n k (by omega)
    rw [h0] at hk
    exact absurd hk (lt_irrefl 0)
  rw [hT] at hlow
  exact ENat.coe_le_coe.mp hlow

end Exploding
