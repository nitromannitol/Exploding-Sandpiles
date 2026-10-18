import Exploding.Support.Toppling
import LatticeProb.Sandpile.Toppling
import LatticeProb.Sandpile.Nonnegative

/-!
# The parallel toppling process of `Exploding` and the library sandpile

`Exploding.podo`, `Exploding.pconf` and `Exploding.Stabilizable` (`Exploding/Support/Toppling.lean`)
and `LatticeProb.Sandpile.podo`, `LatticeProb.Sandpile.pconf` and `LatticeProb.Sandpile.Stabilizable`
(`LatticeProb/Sandpile/Toppling.lean`) are two independent recursions with the same recurrence:
`podo s0 0 = 0`, `podo s0 (t + 1) = podo s0 t + 1{2d ≤ pconf s0 t}` and
`pconf s0 t = s0 + lap (podo s0 t)`. The two odometers are not definitionally equal at a variable
time, so the identification is proved by induction on the time, along the recurrence.

The results are the pointwise and whole-function equalities of the odometer, the equality of the
sandpile, the equivalence of stabilizability, the transfer of positive support, and the transfer of
nonnegativity from `LatticeProb.Sandpile.pconf_nonneg`.
-/

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The Laplacian of this file and of the library agree at every site. -/
theorem lap_eq_sandpile (u : Site d → ℤ) (x : Site d) :
    lap u x = LatticeProb.Sandpile.lap u x := rfl

/-- The sandpile agrees with the library sandpile once the odometers agree at that time. -/
theorem pconf_of_podo_eq (s0 : Site d → ℤ) (t : ℕ)
    (h : podo s0 t = LatticeProb.Sandpile.podo s0 t) (x : Site d) :
    pconf s0 t x = LatticeProb.Sandpile.pconf s0 t x := by
  rw [pconf, LatticeProb.Sandpile.pconf, lap_eq_sandpile, h]

/-- The parallel toppling odometer is the library odometer, for every initial sandpile and
every time. -/
theorem podo_eq_sandpile (s0 : Site d → ℤ) (t : ℕ) :
    podo s0 t = LatticeProb.Sandpile.podo s0 t := by
  induction t with
  | zero => rw [podo_zero, LatticeProb.Sandpile.podo_zero]
  | succ t ih =>
    funext x
    rw [podo_succ, LatticeProb.Sandpile.podo_succ, ih, pconf_of_podo_eq s0 t ih x]

/-- Pointwise form of the odometer identity. -/
theorem podo_apply_eq_sandpile (s0 : Site d → ℤ) (t : ℕ) (x : Site d) :
    podo s0 t x = LatticeProb.Sandpile.podo s0 t x :=
  congrFun (podo_eq_sandpile s0 t) x

/-- The parallel toppling sandpile is the library sandpile, at every site and every time. -/
theorem pconf_eq_sandpile (s0 : Site d → ℤ) (t : ℕ) (x : Site d) :
    pconf s0 t x = LatticeProb.Sandpile.pconf s0 t x :=
  pconf_of_podo_eq s0 t (podo_eq_sandpile s0 t) x

/-- An initial sandpile is stabilizable in this file exactly when it is in the library. -/
theorem stabilizable_iff_sandpile (s0 : Site d → ℤ) :
    Exploding.Stabilizable s0 ↔ LatticeProb.Sandpile.Stabilizable s0 := by
  simp only [Exploding.Stabilizable, LatticeProb.Sandpile.Stabilizable, podo_eq_sandpile]

/-- A site fires at some time in this process exactly when it does in the library process. -/
theorem exists_pos_podo_iff_sandpile (s0 : Site d → ℤ) (x : Site d) :
    (∃ t : ℕ, 0 < podo s0 t x) ↔ ∃ t : ℕ, 0 < LatticeProb.Sandpile.podo s0 t x := by
  simp only [podo_apply_eq_sandpile]

/-- The positive odometer support at each fixed time is the library's. -/
theorem pos_podo_set_eq_sandpile (s0 : Site d → ℤ) (t : ℕ) :
    {x : Site d | 0 < podo s0 t x} = {x : Site d | 0 < LatticeProb.Sandpile.podo s0 t x} := by
  ext x
  simp only [Set.mem_setOf_eq, podo_apply_eq_sandpile]

/-- For a stabilizable initial sandpile, after its stabilization time the positive support of
the odometer is the library's positive support at that stabilization time. -/
theorem stabilizable_terminal_support (s0 : Site d → ℤ) (hs : Exploding.Stabilizable s0) :
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t → ∀ x : Site d,
      (0 < podo s0 t x ↔ 0 < LatticeProb.Sandpile.podo s0 T x) := by
  obtain ⟨T, hT⟩ := hs
  refine ⟨T, fun t ht x => ?_⟩
  rw [hT t ht, podo_apply_eq_sandpile]

/-- A nonnegative initial sandpile stays nonnegative: the library theorem, transported through
the identification of the two sandpiles. -/
theorem pconf_nonneg (s0 : Site d → ℤ) (hs0 : ∀ x, 0 ≤ s0 x) (t : ℕ) (x : Site d) :
    0 ≤ pconf s0 t x := by
  rw [pconf_eq_sandpile]
  exact LatticeProb.Sandpile.pconf_nonneg s0 hs0 t x

/-- Checked control: on `Site 2` with background height `2` and `2` extra chips at the origin,
the origin topples once by time one in this process. -/
theorem origin_topples_once :
    podo (d := 2) (fun x : Site 2 => 2 + 2 * dirac (0 : Site 2) x) 1 0 = 1 := by
  have h0 : pconf (d := 2) (fun x : Site 2 => 2 + 2 * dirac (0 : Site 2) x) 0 0 = 4 := by
    simp [pconf, lap, nbrSumZ, dirac_self]
  show podo (d := 2) (fun x : Site 2 => 2 + 2 * dirac (0 : Site 2) x) (0 + 1) 0 = 1
  rw [podo_succ, h0]
  simp

/-- The same control in the library process. -/
theorem origin_topples_once_sandpile :
    LatticeProb.Sandpile.podo (d := 2) (fun x : Site 2 => 2 + 2 * dirac (0 : Site 2) x) 1 0 = 1 := by
  rw [← podo_apply_eq_sandpile]
  exact origin_topples_once

end Exploding
