/-
The ordinary-to-frozen-wave comparison used in the proof of the corrected square
lemma, `paper/corrected-arxiv/exploding-corrected-arxiv.tex`, lines 758–777.

Let `h ≥ 0` be a constant background, let `N` extra chips sit at the origin, and let
`η ≥ h` pointwise.  If the ordinary origin odometer of the pile `h + N δ₀` never
exceeds `m`, then the ordinary parallel odometer is dominated by the `m`-wave
`u^{(m,0)}` for `η`, at every time and site.

This is a CONDITIONAL internal comparison.  The origin bound is a hypothesis.  In the
corrected proof it is an obligation of the Green-function and radius estimate, and it
is not established in this file.  The file is not the square lemma and uses no
external radius theorem.
-/
import Exploding.Support.Toppling
import Exploding.Support.LatticeSandpileBridge
import LatticeProb.Sandpile.Parallel

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-! ### Nonnegativity of the ordinary sandpile -/

/-- The unit mass is nonnegative. -/
theorem sqw_dirac_nonneg (z x : Site d) : 0 ≤ dirac z x :=
  LatticeProb.Sandpile.dirac_nonneg z x

/-- A nonnegative initial pile keeps every site nonnegative at every time.  A site loses
`2d` chips only when it holds at least `2d`, and its neighbour contribution never
decreases in time. -/
theorem sqw_pconf_nonneg (s0 : Site d → ℤ) (hs0 : ∀ x, 0 ≤ s0 x) :
    ∀ t : ℕ, ∀ x : Site d, 0 ≤ pconf s0 t x :=
  fun t x => pconf_nonneg s0 hs0 t x

/-! ### The min/floor update away from the origin -/

/-- Wherever the ordinary sandpile is nonnegative, the parallel odometer's one-step update
is the minimum of "one more toppling" and the floor of
`(∑_{y∼x} v_t(y) + s₀(x)) / 2d`.  This is the recurrence used in the paper's comparison. -/
theorem sqw_podo_succ_eq_min_floor (s0 : Site d → ℤ) (hdz : (0 : ℤ) < 2 * (d : ℤ))
    (t : ℕ) (x : Site d) (hp : 0 ≤ pconf s0 t x) :
    podo s0 (t + 1) x =
      min (podo s0 t x + 1) ((nbrSumZ (podo s0 t) x + s0 x) / (2 * (d : ℤ))) := by
  rw [podo_eq_sandpile s0 t, podo_eq_sandpile s0 (t + 1)]
  rw [pconf_eq_sandpile] at hp
  exact LatticeProb.Sandpile.podo_succ_eq_min_floor s0 hdz t x hp

/-- The floor bound: the next odometer value is at most `(∑_{y∼x} v_t(y) + s₀(x)) / 2d`. -/
theorem sqw_podo_succ_le_floor (s0 : Site d → ℤ) (hdz : (0 : ℤ) < 2 * (d : ℤ))
    (t : ℕ) (x : Site d) (hp : 0 ≤ pconf s0 t x) :
    podo s0 (t + 1) x ≤ (nbrSumZ (podo s0 t) x + s0 x) / (2 * (d : ℤ)) := by
  rw [podo_eq_sandpile s0 t, podo_eq_sandpile s0 (t + 1)]
  rw [pconf_eq_sandpile] at hp
  exact LatticeProb.Sandpile.podo_succ_le_floor s0 hdz t x hp

/-! ### Time monotonicity of the ordinary odometer -/

/-- The ordinary parallel odometer is nondecreasing in time across any gap. -/
theorem sqw_podo_mono (s0 : Site d → ℤ) {s t : ℕ} (hst : s ≤ t) (x : Site d) :
    podo s0 s x ≤ podo s0 t x := by
  rw [podo_apply_eq_sandpile, podo_apply_eq_sandpile]
  exact LatticeProb.Sandpile.podo_mono s0 hst x

/-! ### The conditional comparison -/

/-- **Conditional comparison, abstract pile.**  Assume `s₀ ≥ 0`, `s₀ = h` off the origin,
`η ≥ h ≥ 0`, and that the ordinary origin odometer never exceeds `m`.  Then
`v_t ≤ u_t^{(m,0)}` for every `t` and `x`. -/
theorem sqw_podo_le_wave_core (s0 : Site d → ℤ) (h : ℤ) (m : ℕ) (hd : 0 < d)
    (η : Site d → ℤ) (hη : ∀ x, h ≤ η x) (hh : 0 ≤ h) (hs0 : ∀ x, 0 ≤ s0 x)
    (hoff : ∀ x, x ≠ 0 → s0 x = h) (horig : ∀ t : ℕ, podo s0 t 0 ≤ (m : ℤ)) :
    ∀ t : ℕ, ∀ x : Site d, podo s0 t x ≤ wave η m (0 : Site d) t x := by
  have hdz : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
    linarith
  have hη0 : ∀ x, 0 ≤ η x := fun x => le_trans hh (hη x)
  have hpc := sqw_pconf_nonneg s0 hs0
  intro t
  induction t with
  | zero =>
    intro x
    exact le_trans (le_of_eq (rfl : podo s0 0 x = 0)) (wave_nonneg η hη0 m 0 0 x)
  | succ t ih =>
    intro x
    by_cases hx : x = 0
    · subst hx
      rw [wave_at_centre]
      exact horig (t + 1)
    · have hstep := sqw_podo_succ_le_floor s0 hdz t x (hpc t x)
      rw [hoff x hx] at hstep
      rw [wave_of_ne _ _ _ _ _ hx]
      refine le_trans hstep (Int.ediv_le_ediv hdz ?_)
      linarith [nbrSumZ_mono (fun y => ih y) x, hη x]

/-- **Conditional comparison, finite stabilization.**  As `sqw_podo_le_wave_core`, but the
all-time origin bound is replaced by a stabilization time `T` (the body of `Stabilizable`
at `T`) and the single value `podo s0 T 0 ≤ m`.  Time monotonicity transfers the bound to
every earlier time, and stabilization to every later one. -/
theorem sqw_podo_le_wave_of_stabilized_origin (s0 : Site d → ℤ) (h : ℤ) (m : ℕ) (hd : 0 < d)
    (η : Site d → ℤ) (hη : ∀ x, h ≤ η x) (hh : 0 ≤ h) (hs0 : ∀ x, 0 ≤ s0 x)
    (hoff : ∀ x, x ≠ 0 → s0 x = h)
    (T : ℕ) (hT : ∀ t : ℕ, T ≤ t → podo s0 t = podo s0 T) (hTm : podo s0 T 0 ≤ (m : ℤ)) :
    ∀ t : ℕ, ∀ x : Site d, podo s0 t x ≤ wave η m (0 : Site d) t x := by
  refine sqw_podo_le_wave_core s0 h m hd η hη hh hs0 hoff ?_
  intro t
  rcases le_total t T with htT | hTt
  · exact le_trans (sqw_podo_mono s0 htT 0) hTm
  · rw [hT t hTt]
    exact hTm

/-- **Conditional comparison for the ordinary pile `h + N δ₀`.**  For a constant background
`h ≥ 0`, `N` extra chips at the origin, `η ≥ h` pointwise, and `d > 0`, if the ordinary
origin odometer of `h + N δ₀` never exceeds `m`, then its parallel odometer is dominated by
the `m`-wave for `η` started at the origin, at every time and site.  The origin bound is a
hypothesis here, not a conclusion. -/
theorem sqw_podo_le_wave_of_origin_bound (h : ℤ) (hh : 0 ≤ h) (N m : ℕ) (hd : 0 < d)
    (η : Site d → ℤ) (hη : ∀ x, h ≤ η x)
    (horig : ∀ t : ℕ, podo (fun x => h + (N : ℤ) * dirac (0 : Site d) x) t 0 ≤ (m : ℤ)) :
    ∀ t : ℕ, ∀ x : Site d,
      podo (fun x => h + (N : ℤ) * dirac (0 : Site d) x) t x ≤ wave η m (0 : Site d) t x :=
  sqw_podo_le_wave_core (fun x => h + (N : ℤ) * dirac (0 : Site d) x) h m hd η hη hh
    (fun x => add_nonneg hh (mul_nonneg (Nat.cast_nonneg N) (sqw_dirac_nonneg _ x)))
    (fun x hx => by simp [dirac_of_ne hx])
    horig

/-! ### Zero-pile check -/

/-- A zero initial pile has zero odometer at every time: no site ever holds `2d` chips,
since the Laplacian of the zero odometer vanishes. -/
theorem sqw_podo_eq_zero (s0 : Site d → ℤ) (hd : 0 < d) (hs : ∀ x, s0 x = 0) :
    ∀ t : ℕ, ∀ x : Site d, podo s0 t x = 0 :=
  fun t x =>
    (podo_apply_eq_sandpile s0 t x).trans (LatticeProb.Sandpile.podo_eq_zero s0 hd hs t x)

/-- Check with `h = 0`, `N = 0`, `m = 0`, `η = 0` in dimension one.  The same pile
`0 + 0 · δ₀` satisfies the stabilization body at `T = 0`, every premise of
`sqw_podo_le_wave_of_origin_bound`, and the conclusion holds for it. -/
theorem sqw_check_zero_pile :
    Stabilizable (fun x : Site 1 => (0 : ℤ) + ((0 : ℕ) : ℤ) * dirac (0 : Site 1) x) ∧
    ∀ t : ℕ, ∀ x : Site 1,
      podo (fun x : Site 1 => (0 : ℤ) + ((0 : ℕ) : ℤ) * dirac (0 : Site 1) x) t x ≤
        wave (fun _ : Site 1 => (0 : ℤ)) 0 (0 : Site 1) t x := by
  have hs : ∀ x : Site 1, (fun x : Site 1 => (0 : ℤ) + ((0 : ℕ) : ℤ) * dirac (0 : Site 1) x) x
      = 0 := fun x => by simp
  have hz := sqw_podo_eq_zero (fun x : Site 1 => (0 : ℤ) + ((0 : ℕ) : ℤ) * dirac (0 : Site 1) x)
    one_pos hs
  refine ⟨?_, ?_⟩
  · unfold Stabilizable
    exact ⟨0, fun t _ => funext fun x => by rw [hz t x, hz 0 x]⟩
  · exact sqw_podo_le_wave_of_origin_bound (d := 1) 0 le_rfl 0 0 one_pos (fun _ => (0 : ℤ))
      (fun _ => le_rfl) (fun t => (hz t 0).trans_le (Nat.cast_nonneg 0))

end Exploding
