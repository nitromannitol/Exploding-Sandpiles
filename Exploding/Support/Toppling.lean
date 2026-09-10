/-
The Abelian sandpile under parallel toppling on `ℤ^d`, in the vocabulary of
`paper/exploding.tex`.

A *background* is a function `η : Site d → ℤ`; a *sandpile* is a function
`s : Site d → ℤ` counting chips.  A site *fires* when it holds at least `2d`
chips: firing removes `2d` chips from it and adds one chip to each neighbour.
Parallel toppling fires every unstable site at once.

The objects defined here, with the display of the paper they transcribe:

* `lap`         the lattice Laplacian `Δ u (x) = ∑_{y ∼ x} (u y - u x)`;
* `podo`, `pconf`   the parallel toppling odometer `v_t` and sandpile `s_t`
  of `(1.1)`, for the initial sandpile `s_0`;
* `Stabilizable`, `Robust`, `Explosive`  the notions of the Overview;
* `explosionThreshold`  the threshold `M_η` of `(1.3)`;
* `fodo`, `fconf`   the `S`-frozen odometer `w_t` and sandpile `s_t'` of `(2.3)`;
* `wave`  the `n`-wave `u_t^{(n,z)}` of `(3.1)`.

Integer division `/` on `ℤ` rounds towards `-∞`, so it is the floor `⌊·⌋` of
the paper: `(-7 : ℤ) / 2 = -4`.
-/
import LatticeProb.Site

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The unit mass at `z`. -/
def dirac (z : Site d) : Site d → ℤ := fun x => if x = z then 1 else 0

@[simp] theorem dirac_self (z : Site d) : dirac z z = 1 := by simp [dirac]

theorem dirac_of_ne {x z : Site d} (h : x ≠ z) : dirac z x = 0 := by simp [dirac, h]

/-- The sum of `u` over the `2d` neighbours of `x`, direction by direction, so
that `d = 0` is not special-cased. -/
def nbrSumZ (u : Site d → ℤ) (x : Site d) : ℤ :=
  ∑ i : Fin d, (u (x + unit i) + u (x - unit i))

theorem nbrSumZ_mono {u v : Site d → ℤ} (h : ∀ y, u y ≤ v y) (x : Site d) :
    nbrSumZ u x ≤ nbrSumZ v x :=
  Finset.sum_le_sum fun _ _ => add_le_add (h _) (h _)

theorem nbrSumZ_add_const (u : Site d → ℤ) (c : ℤ) (x : Site d) :
    nbrSumZ (fun y => c + u y) x = 2 * (d : ℤ) * c + nbrSumZ u x := by
  simp only [nbrSumZ]
  rw [show (fun i : Fin d => (c + u (x + unit i)) + (c + u (x - unit i)))
        = (fun i : Fin d => 2 * c + (u (x + unit i) + u (x - unit i))) from
      funext fun i => by ring]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp
  ring

theorem nbrSumZ_congr {u v : Site d → ℤ} (h : ∀ y, u y = v y) (x : Site d) :
    nbrSumZ u x = nbrSumZ v x := by
  simp only [nbrSumZ, h]

/-- The lattice Laplacian `Δ u (x) = ∑_{y ∼ x} (u y - u x)` of the Overview. -/
def lap (u : Site d → ℤ) (x : Site d) : ℤ := nbrSumZ u x - 2 * d * u x

theorem lap_eq (u : Site d → ℤ) (x : Site d) :
    lap u x = nbrSumZ u x - 2 * d * u x := rfl

/-- The parallel toppling odometer `v_t` for the initial sandpile `s₀`:
`v_0 = 0` and `v_{t+1} = v_t + 1{s_t ≥ 2d}`, where `s_t = s₀ + Δ v_t`. -/
def podo (s0 : Site d → ℤ) : ℕ → Site d → ℤ
  | 0 => fun _ => 0
  | t + 1 => fun x =>
      podo s0 t x + (if 2 * d ≤ s0 x + lap (podo s0 t) x then 1 else 0)

/-- The parallel toppling sandpile `s_t = s₀ + Δ v_t`. -/
def pconf (s0 : Site d → ℤ) (t : ℕ) (x : Site d) : ℤ := s0 x + lap (podo s0 t) x

@[simp] theorem podo_zero (s0 : Site d → ℤ) : podo s0 0 = fun _ => 0 := rfl

theorem podo_succ (s0 : Site d → ℤ) (t : ℕ) (x : Site d) :
    podo s0 (t + 1) x = podo s0 t x + (if 2 * d ≤ pconf s0 t x then 1 else 0) := rfl

/-- The parallel toppling odometer is nondecreasing in time. -/
theorem podo_mono_step (s0 : Site d → ℤ) (t : ℕ) (x : Site d) :
    podo s0 t x ≤ podo s0 (t + 1) x := by
  rw [podo_succ]
  exact le_add_of_nonneg_right (by positivity)

/-- `s₀` is *stabilizable*: the parallel toppling odometer is eventually
constant. -/
def Stabilizable (s0 : Site d → ℤ) : Prop :=
  ∃ T : ℕ, ∀ t : ℕ, T ≤ t → podo s0 t = podo s0 T

/-- A background is *robust* if `η + n δ₀` is stabilizable for every `n ≥ 1`. -/
def Robust (η : Site d → ℤ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → Stabilizable (fun x => η x + n * dirac (0 : Site d) x)

/-- A background is *explosive* if it is not robust. -/
def Explosive (η : Site d → ℤ) : Prop := ¬ Robust η

/-- The explosion threshold `M_η = min {n ≥ 1 : η + n δ₀ is not stabilizable}`
of `(1.3)`.  Carry `Explosive η` to know the set is nonempty. -/
noncomputable def explosionThreshold (η : Site d → ℤ) : ℕ :=
  sInf {n : ℕ | 1 ≤ n ∧ ¬ Stabilizable (fun x => η x + n * dirac (0 : Site d) x)}

open scoped Classical in
/-- The `S`-frozen parallel toppling odometer `w_t` of `(2.3)`: the odometer is
held at `w₀` on `S`, and `s_t' = s₀ + Δ w_t`. -/
noncomputable def fodo (S : Set (Site d)) (s0 w0 : Site d → ℤ) : ℕ → Site d → ℤ
  | 0 => w0
  | t + 1 => fun x =>
      if x ∈ S then w0 x
      else fodo S s0 w0 t x + (if 2 * d ≤ s0 x + lap (fodo S s0 w0 t) x then 1 else 0)

/-- The `S`-frozen parallel toppling sandpile `s_t' = s₀ + Δ w_t`. -/
noncomputable def fconf (S : Set (Site d)) (s0 w0 : Site d → ℤ) (t : ℕ) (x : Site d) : ℤ :=
  s0 x + lap (fodo S s0 w0 t) x

@[simp] theorem fodo_zero (S : Set (Site d)) (s0 w0 : Site d → ℤ) : fodo S s0 w0 0 = w0 := rfl

open scoped Classical in
theorem fodo_succ (S : Set (Site d)) (s0 w0 : Site d → ℤ) (t : ℕ) (x : Site d) :
    fodo S s0 w0 (t + 1) x =
      if x ∈ S then w0 x
      else fodo S s0 w0 t x + (if 2 * d ≤ fconf S s0 w0 t x then 1 else 0) := rfl

/-- On the frozen set the frozen odometer never moves. -/
theorem fodo_of_mem (S : Set (Site d)) (s0 w0 : Site d → ℤ) (t : ℕ) {x : Site d} (hx : x ∈ S) :
    fodo S s0 w0 t x = w0 x := by
  cases t with
  | zero => rfl
  | succ t => rw [fodo_succ]; exact if_pos hx

open scoped Classical in
/-- The `n`-wave `u_t^{(n,z)}` for the background `η` starting at `z`, of
`(3.1)`: `u_0 = n δ_z` and, away from `z`,
`u_{t+1}(x) = ⌊(∑_{y ∼ x} u_t(y) + η(x)) / 2d⌋`, with no `u_t(x) + 1` cap. -/
noncomputable def wave (η : Site d → ℤ) (n : ℕ) (z : Site d) : ℕ → Site d → ℤ
  | 0 => fun x => if x = z then (n : ℤ) else 0
  | t + 1 => fun x =>
      if x = z then (n : ℤ)
      else (nbrSumZ (wave η n z t) x + η x) / (2 * d)

theorem wave_zero (η : Site d → ℤ) (n : ℕ) (z : Site d) (x : Site d) :
    wave η n z 0 x = if x = z then (n : ℤ) else 0 := rfl

theorem wave_succ (η : Site d → ℤ) (n : ℕ) (z x : Site d) (t : ℕ) :
    wave η n z (t + 1) x =
      if x = z then (n : ℤ)
      else (nbrSumZ (wave η n z t) x + η x) / (2 * d) := rfl

@[simp] theorem wave_at_centre (η : Site d → ℤ) (n : ℕ) (z : Site d) (t : ℕ) :
    wave η n z t z = (n : ℤ) := by
  cases t with
  | zero => simp [wave_zero]
  | succ t => simp [wave_succ]

theorem wave_of_ne (η : Site d → ℤ) (n : ℕ) (z x : Site d) (t : ℕ) (h : x ≠ z) :
    wave η n z (t + 1) x = (nbrSumZ (wave η n z t) x + η x) / (2 * d) := by
  simp [wave_succ, h]

/-- The `n`-wave is monotone in `n`. -/
theorem wave_mono_n (η : Site d → ℤ) (hd : (0 : ℤ) < 2 * (d : ℤ)) (z : Site d) {n m : ℕ}
    (hnm : n ≤ m) (t : ℕ) (x : Site d) : wave η n z t x ≤ wave η m z t x := by
  induction t generalizing x with
  | zero =>
    by_cases h : x = z <;> simp [wave_zero, h, Nat.cast_le.mpr hnm]
  | succ t ih =>
    by_cases h : x = z
    · simp [h]; exact_mod_cast hnm
    · simp only [wave_succ, if_neg h]
      refine Int.ediv_le_ediv hd ?_
      have h1 := nbrSumZ_mono (fun y => ih y) x
      linarith

/-- On a nonnegative background the `n`-wave is nonnegative. -/
theorem wave_nonneg (η : Site d → ℤ) (hη : ∀ y, 0 ≤ η y) (n : ℕ) (z : Site d)
    (t : ℕ) (x : Site d) : 0 ≤ wave η n z t x := by
  induction t generalizing x with
  | zero =>
    by_cases h : x = z <;> simp [wave_zero, h]
  | succ t ih =>
    by_cases h : x = z
    · simp [h]
    · rw [wave_of_ne _ _ _ _ _ h]
      apply Int.ediv_nonneg _ (by positivity)
      have : 0 ≤ nbrSumZ (wave η n z t) x := by
        refine Finset.sum_nonneg ?_
        intro i _
        exact add_nonneg (ih _) (ih _)
      linarith [hη x]

/-- On a nonnegative background the `n`-wave is nondecreasing in time. -/
theorem wave_mono_t (η : Site d → ℤ) (hη : ∀ y, 0 ≤ η y) (hd : (0 : ℤ) < 2 * (d : ℤ))
    (n : ℕ) (z : Site d) (t : ℕ) (x : Site d) :
    wave η n z t x ≤ wave η n z (t + 1) x := by
  induction t generalizing x with
  | zero =>
    by_cases h : x = z
    · simp [h]
    · rw [wave_zero]
      simp only [if_neg h]
      exact wave_nonneg η hη n z 1 x
  | succ t ih =>
    by_cases h : x = z
    · simp [h]
    · rw [wave_of_ne _ _ _ _ _ h, wave_of_ne _ _ _ _ _ h]
      exact Int.ediv_le_ediv hd (by linarith [nbrSumZ_mono (fun y => ih y) x])

/-- A site at which the wave equation holds is stable there. -/
theorem lap_le_of_fixed (η : Site d → ℤ) (hd : (0 : ℤ) < 2 * (d : ℤ)) (u : Site d → ℤ)
    (x : Site d) (h : u x = (nbrSumZ u x + η x) / (2 * (d : ℤ))) :
    lap u x + η x ≤ 2 * (d : ℤ) - 1 := by
  have key := Int.lt_ediv_add_one_mul_self (nbrSumZ u x + η x) hd
  rw [← h] at key
  simp only [lap]
  nlinarith [key]

/-- The `n`-wave is *stabilizable* if it is eventually constant. -/
def WaveStabilizable (η : Site d → ℤ) (n : ℕ) (z : Site d) : Prop :=
  ∃ T : ℕ, ∀ t : ℕ, T ≤ t → wave η n z t = wave η n z T

/-- `M̂_η(z) = min {n ≥ 1 : the n-wave for η starting at z is not
stabilizable}`, the index of the last-wave. -/
noncomputable def waveThreshold (η : Site d → ℤ) (z : Site d) : ℕ :=
  sInf {n : ℕ | 1 ≤ n ∧ ¬ WaveStabilizable η n z}

end Exploding
