/-
Least action principle of Fey, Meester and Redig for legal toppling procedures
on `ℤ^d`, in the form of `Exploding.External.FeyMeesterRedigLeastAction`.

A legal toppling procedure never exceeds a stabilizing odometer: the first time
a site could exceed `w`, it would be unstable although all its neighbours have
been toppled at most as often as under `w`, which makes its Laplacian at most
that of `w`, a stable configuration.
-/
import Exploding.External.FeyMeesterRedig

namespace Exploding

open LatticeProb

/-- A legal toppling procedure is nonnegative: it starts at `0` and only increases. -/
theorem xfmr_legal_nonneg {d : ℕ} {s0 : Site d → ℤ} {v : ℕ → Site d → ℤ}
    (hv : Exploding.External.IsLegalToppling s0 v) (k : ℕ) (x : Site d) : 0 ≤ v k x := by
  induction k with
  | zero => simp [hv.1]
  | succ k ih =>
    rcases hv.2 k x with h | ⟨h, _⟩
    · rw [h]; exact ih
    · rw [h]; omega

/-- A site that is unstable in `s0 + Δ z`, with `z ≤ w` and `w` stable, has `z x < w x`. -/
theorem xfmr_unstable_lt {d : ℕ} {s0 w z : Site d → ℤ}
    (hw : ∀ x, s0 x + lap w x < 2 * (d : ℤ)) (hz : ∀ y, z y ≤ w y) {x : Site d}
    (hx : 2 * (d : ℤ) ≤ s0 x + lap z x) : z x < w x := by
  by_contra h
  have hzx : z x = w x := le_antisymm (hz x) (not_lt.mp h)
  have hle : lap z x ≤ lap w x := by
    simp only [lap, hzx]
    have := nbrSumZ_mono hz x
    linarith
  have := hw x
  linarith

/-- A legal toppling procedure is dominated by every stable nonnegative `w`. -/
theorem xfmr_legal_le {d : ℕ} {s0 w : Site d → ℤ} {u : ℕ → Site d → ℤ}
    (hu : Exploding.External.IsLegalToppling s0 u) (hw0 : ∀ x, 0 ≤ w x)
    (hw : ∀ x, s0 x + lap w x < 2 * (d : ℤ)) (k : ℕ) (x : Site d) : u k x ≤ w x := by
  induction k generalizing x with
  | zero => simp [hu.1, hw0 x]
  | succ k ih =>
    rcases hu.2 k x with h | ⟨h, hx⟩
    · rw [h]; exact ih x
    · rw [h]
      have := xfmr_unstable_lt hw ih hx
      omega

/-- The least action principle of Fey, Meester and Redig. -/
theorem xfmr_proved : Exploding.External.FeyMeesterRedigLeastAction := by
  intro d _ s0 _ u v hu hv w hvw hw k x
  have hw0 : ∀ y, 0 ≤ w y := by
    intro y
    obtain ⟨K, hK⟩ := hvw y
    rw [← hK K le_rfl]
    exact xfmr_legal_nonneg hv K y
  exact xfmr_legal_le hu hw0 hw k x

end Exploding
