/-
Elementary geometry of the lattice used by the penultimate-cluster and
local-convexity arguments of `paper/exploding.tex`: the centred box `cent d m`
is connected, a segment between two of its points that differ in one coordinate
stays inside it, and the frozen odometer is dominated by the wave once the wave
dominates its seed.
-/
import Exploding.Support.Vocab
import Exploding.Support.Wave
import Exploding.Support.SubFodo

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- Coordinate formula for a step in direction `i`. -/
theorem coord_add_smul (x : Site d) (c : ℤ) (i j : Fin d) :
    (x + c • unit i) j = x j + c * (if j = i then 1 else 0) := by
  simp [unit, Pi.single_apply]

/-- A point of the segment between two points of `cent d m` that differ only in
coordinate `i` lies in `cent d m`. -/
theorem cent_seg (m : ℕ) (i : Fin d) (x y : Site d)
    (hx : x ∈ (cent d m : Set (Site d))) (hy : y ∈ (cent d m : Set (Site d)))
    (hxy : ∀ j, j ≠ i → y j = x j) (t : ℤ)
    (hlo : min (x i) (y i) ≤ t) (hhi : t ≤ max (x i) (y i)) :
    x + (t - x i) • unit i ∈ (cent d m : Set (Site d)) := by
  intro j
  have h2 : -(m : ℤ) ≤ x j ∧ x j ≤ (m : ℤ) := by
    have h := hx j; rwa [abs_le] at h
  have h3 : -(m : ℤ) ≤ y j ∧ y j ≤ (m : ℤ) := by
    have h := hy j; rwa [abs_le] at h
  have hcoord := coord_add_smul x (t - x i) i j
  rw [hcoord]
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl, mul_one]
    have hti : x j + (t - x j) = t := by ring
    rw [hti, abs_le]
    constructor <;> omega
  · rw [if_neg hji, mul_zero, add_zero]
    rw [abs_le]
    rw [hxy j hji] at h3
    exact h2

/-- The segment from `z` to `y` along direction `i` stays in `cent d m`, and the
induced graph reaches `y` from `z` along it. -/
theorem reachable_induce_seg (S : Set (Site d)) (m : ℕ) (hsub : (cent d m : Set (Site d)) ⊆ S)
    (z y : Site d) (hz : z ∈ (cent d m : Set (Site d))) (hy : y ∈ (cent d m : Set (Site d)))
    (i : Fin d) (hzy : ∀ j, j ≠ i → y j = z j) :
    ∃ (hz' : z + (y i - z i) • unit i ∈ S),
      ((lattice d).induce S).Reachable ⟨z, hsub hz⟩ ⟨z + (y i - z i) • unit i, hz'⟩ := by
  have hzbd : -(m : ℤ) ≤ z i ∧ z i ≤ (m : ℤ) := by
    have h := hz i; rwa [abs_le] at h
  have hybd : -(m : ℤ) ≤ y i ∧ y i ≤ (m : ℤ) := by
    have h := hy i; rwa [abs_le] at h
  have key : ∀ n : ℕ, (n : ℤ) ≤ y i - z i →
      ∃ (h : z + (n : ℤ) • unit i ∈ S),
        ((lattice d).induce S).Reachable ⟨z, hsub hz⟩ ⟨z + (n : ℤ) • unit i, h⟩ := by
    intro n
    induction n with
    | zero =>
      intro _
      have hz0 : z + ((0 : ℕ) : ℤ) • unit i = z := by simp
      rw [hz0]
      exact ⟨hsub hz, SimpleGraph.Reachable.refl (G := (lattice d).induce S) ⟨z, hsub hz⟩⟩
    | succ n ih =>
      intro hn
      push_cast at hn
      obtain ⟨h', hreach⟩ := ih (by linarith)
      have hmem : z + (((n : ℤ) + 1)) • unit i ∈ (cent d m : Set (Site d)) := by
        have h1 : z + (((n : ℤ) + 1)) • unit i = z + (((z i + ((n : ℤ) + 1)) - z i)) • unit i := by
          congr 1
          ring
        rw [h1]
        refine cent_seg m i z y hz hy hzy (z i + ((n : ℤ) + 1)) ?_ ?_
        · exact le_trans (min_le_left _ _) (by linarith)
        · exact le_trans (by linarith) (le_max_right _ _)
      have hadj : (lattice d).Adj (z + (n : ℤ) • unit i) (z + (((n : ℤ) + 1)) • unit i) := by
        refine ⟨i, Or.inl ?_⟩
        rw [add_smul, one_smul]
        abel
      exact ⟨hsub hmem, hreach.trans ((SimpleGraph.induce_adj).mpr hadj).reachable⟩
  have keyneg : ∀ n : ℕ, (n : ℤ) ≤ z i - y i →
      ∃ (h : z + (-(n : ℤ)) • unit i ∈ S),
        ((lattice d).induce S).Reachable ⟨z, hsub hz⟩ ⟨z + (-(n : ℤ)) • unit i, h⟩ := by
    intro n
    induction n with
    | zero =>
      intro _
      have hz0 : z + (-((0 : ℕ) : ℤ)) • unit i = z := by simp
      rw [hz0]
      exact ⟨hsub hz, SimpleGraph.Reachable.refl (G := (lattice d).induce S) ⟨z, hsub hz⟩⟩
    | succ n ih =>
      intro hn
      push_cast at hn
      obtain ⟨h', hreach⟩ := ih (by linarith)
      have hmem : z + (-((n : ℤ) + 1)) • unit i ∈ (cent d m : Set (Site d)) := by
        have h1 : z + (-((n : ℤ) + 1)) • unit i = z + (((z i - ((n : ℤ) + 1)) - z i)) • unit i := by
          congr 1
          ring
        rw [h1]
        refine cent_seg m i z y hz hy hzy (z i - ((n : ℤ) + 1)) ?_ ?_
        · exact le_trans (min_le_right _ _) (by linarith)
        · exact le_trans (by linarith) (le_max_left _ _)
      have hadj : (lattice d).Adj (z + (-(n : ℤ)) • unit i) (z + (-((n : ℤ) + 1)) • unit i) := by
        refine ⟨i, Or.inr ?_⟩
        rw [show -((n : ℤ) + 1) = -(n : ℤ) - 1 by ring, sub_smul, one_smul]
        abel
      exact ⟨hsub hmem, hreach.trans ((SimpleGraph.induce_adj).mpr hadj).reachable⟩
  rcases le_total (0 : ℤ) (y i - z i) with hpos | hneg
  · have h1 : y i - z i = (((y i - z i).toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hpos).symm
    rw [h1]
    exact key (y i - z i).toNat (by rw [Int.toNat_of_nonneg hpos])
  · have h1 : y i - z i = -(((-(y i - z i)).toNat : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg (by linarith)]
      ring
    rw [h1]
    exact keyneg (-(y i - z i)).toNat (by
      rw [Int.toNat_of_nonneg (by linarith)]
      linarith)

/-- `cent d m` is connected under the lattice graph of any `S ⊇ cent d m`. -/
theorem cent_connected_in (S : Set (Site d)) (m : ℕ)
    (hsub : (cent d m : Set (Site d)) ⊆ S) (x y : Site d)
    (hx : x ∈ (cent d m : Set (Site d))) (hy : y ∈ (cent d m : Set (Site d))) :
    y ∈ componentIn S x := by
  classical
  refine ⟨hsub hx, hsub hy, ?_⟩
  have hmem : ∀ s : Finset (Fin d),
      (fun j => if j ∈ s then y j else x j) ∈ (cent d m : Set (Site d)) := by
    intro s j
    show |(if j ∈ s then y j else x j)| ≤ (m : ℤ)
    by_cases hjs : j ∈ s
    · rw [if_pos hjs]
      have h := hy j; rwa [abs_le] at h ⊢
    · rw [if_neg hjs]
      have h := hx j; rwa [abs_le] at h ⊢
  have key : ∀ (s : Finset (Fin d)), ∃ (hz : (fun j => if j ∈ s then y j else x j) ∈ S),
      ((lattice d).induce S).Reachable ⟨x, hsub hx⟩
        ⟨(fun j => if j ∈ s then y j else x j), hz⟩ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have hpt : (fun j => if j ∈ (∅ : Finset (Fin d)) then y j else x j) = x := by
        funext j; simp
      rw [hpt]
      exact ⟨hsub hx, SimpleGraph.Reachable.refl _⟩
    | insert i s hi ih =>
      obtain ⟨hz, hreach⟩ := ih
      have hdiff : ∀ j, j ≠ i →
          (fun j => if j ∈ insert i s then y j else x j) j =
            (fun j => if j ∈ s then y j else x j) j := by
        intro j hji
        show (if j ∈ insert i s then y j else x j) = (if j ∈ s then y j else x j)
        by_cases hjs : j ∈ s
        · rw [if_pos (Finset.mem_insert_of_mem hjs), if_pos hjs]
        · rw [if_neg (fun h => hjs ((Finset.mem_insert.mp h).resolve_left hji)), if_neg hjs]
      obtain ⟨hz', hstep⟩ := reachable_induce_seg S m hsub
        (fun j => if j ∈ s then y j else x j)
        (fun j => if j ∈ insert i s then y j else x j) (hmem s) (hmem _) i hdiff
      have hpt_step : (fun j => if j ∈ s then y j else x j) +
          ((fun j => if j ∈ insert i s then y j else x j) i -
            (fun j => if j ∈ s then y j else x j) i) • unit i =
          (fun j => if j ∈ insert i s then y j else x j) := by
        funext j
        rw [coord_add_smul]
        show (if j ∈ s then y j else x j) +
            ((if i ∈ insert i s then y i else x i) - (if i ∈ s then y i else x i)) *
              (if j = i then 1 else 0) = (if j ∈ insert i s then y j else x j)
        by_cases hji : j = i
        · subst hji
          rw [if_pos rfl, mul_one, if_pos (Finset.mem_insert_self j s)]
          ring
        · rw [if_neg hji, mul_zero, add_zero]
          exact (hdiff j hji).symm
      have heq : (⟨(fun j => if j ∈ s then y j else x j) +
            ((fun j => if j ∈ insert i s then y j else x j) i -
              (fun j => if j ∈ s then y j else x j) i) • unit i, hz'⟩ : S) =
          ⟨(fun j => if j ∈ insert i s then y j else x j), hsub (hmem _)⟩ :=
        Subtype.ext hpt_step
      exact ⟨hsub (hmem _), hreach.trans (heq ▸ hstep)⟩
  obtain ⟨hz, hreach⟩ := key Finset.univ
  have hpt : (fun j => if j ∈ (Finset.univ : Finset (Fin d)) then y j else x j) = y := by
    funext j; simp
  have heq : (⟨(fun j => if j ∈ (Finset.univ : Finset (Fin d)) then y j else x j), hz⟩ : S) =
      ⟨y, hsub hy⟩ := Subtype.ext hpt
  exact heq ▸ hreach

/-- The frozen odometer started from a nonnegative seed is nonnegative. -/
theorem fodo_nonneg_of_seed (S : Set (Site d)) (s0 w0 : Site d → ℤ) (hw0 : ∀ x, 0 ≤ w0 x)
    (t : ℕ) (x : Site d) : 0 ≤ fodo S s0 w0 t x := by
  induction t generalizing x with
  | zero => exact hw0 x
  | succ t ih =>
    rw [fodo_succ]
    by_cases hx : x ∈ S
    · rw [if_pos hx]; exact hw0 x
    · rw [if_neg hx]; split_ifs <;> linarith [ih x]

/-- The wave dominates the frozen odometer started from a seed that the wave
already dominates, at every later time. -/
theorem wave_dom_fodo {d : ℕ} (hd0 : (0 : ℤ) < 2 * (d : ℤ))
    (S : Set (Site d)) (η : Site d → ℤ) (hη : ∀ y, 0 ≤ η y) (N : ℕ) (z : Site d)
    (t0 : ℕ) (w0 : Site d → ℤ) (_hw0nn : ∀ x, 0 ≤ w0 x)
    (hz : z ∈ S)
    (hw0 : ∀ x, w0 x ≤ wave η N z t0 x)
    (hSdom : ∀ s : ℕ, ∀ x ∈ S, w0 x ≤ wave η N z (t0 + s) x) :
    ∀ s x, fodo S η w0 s x ≤ wave η N z (t0 + s) x := by
  intro s
  induction s with
  | zero =>
    intro x
    rw [fodo_zero]
    simpa using hw0 x
  | succ s ih =>
    intro x
    rw [fodo_succ]
    by_cases hx : x ∈ S
    · rw [if_pos hx]
      have h := hSdom (s + 1) x hx
      rwa [show t0 + (s + 1) = t0 + s + 1 from by omega] at h
    · rw [if_neg hx]
      have hxz : x ≠ z := fun h => hx (h ▸ hz)
      rw [show t0 + (s + 1) = t0 + s + 1 from by omega,
        wave_of_ne η N z x (t0 + s) hxz]
      split_ifs with hc
      · rw [Int.le_ediv_iff_mul_le (by positivity)]
        have hc' : 2 * (d : ℤ) ≤ η x + lap (fodo S η w0 s) x := hc
        rw [lap] at hc'
        have hmono := nbrSumZ_mono (fun y => ih y) x
        linarith
      · rw [add_zero, ← wave_of_ne η N z x (t0 + s) hxz]
        exact le_trans (ih x) (wave_mono_t η hη hd0 N z (t0 + s) x)

/-- The `n`-wave never exceeds `n` on a background of at most `2d - 1` chips. -/
theorem wave_le_n (η : Site d → ℤ) (hhigh : ∀ y, η y ≤ 2 * (d : ℤ) - 1)
    (hd0 : (0 : ℤ) < 2 * (d : ℤ)) (N : ℕ) (z : Site d) (t : ℕ) (x : Site d) :
    wave η N z t x ≤ (N : ℤ) := by
  induction t generalizing x with
  | zero =>
    by_cases h : x = z <;> simp [wave_zero, h]
  | succ t ih =>
    by_cases h : x = z
    · rw [h, wave_at_centre]
    · rw [wave_of_ne η N z x t h]
      have hsum : nbrSumZ (wave η N z t) x ≤ 2 * (d : ℤ) * (N : ℤ) := by
        simp only [nbrSumZ]
        calc ∑ i : Fin d, (wave η N z t (x + unit i) + wave η N z t (x - unit i))
            ≤ ∑ _i : Fin d, ((N : ℤ) + (N : ℤ)) :=
              Finset.sum_le_sum fun i _ => by linarith [ih (x + unit i), ih (x - unit i)]
          _ = 2 * (d : ℤ) * (N : ℤ) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
      have hlt : nbrSumZ (wave η N z t) x + η x < ((N : ℤ) + 1) * (2 * (d : ℤ)) := by
        linarith [hhigh x]
      by_contra hcon
      have hcon' : (N : ℤ) < (nbrSumZ (wave η N z t) x + η x) / (2 * (d : ℤ)) :=
        lt_of_not_ge hcon
      have h1 : (N : ℤ) + 1 ≤ (nbrSumZ (wave η N z t) x + η x) / (2 * (d : ℤ)) := by
        omega
      rw [Int.le_ediv_iff_mul_le (by positivity)] at h1
      linarith

/-- The wave dominates the frozen odometer started from a seed that the wave
already dominates, at every later time.  At the centre the wave is `N ≥ 1`
while the frozen odometer is at most `1`. -/
theorem wave_dom_fodo' {d : ℕ} (hd0 : (0 : ℤ) < 2 * (d : ℤ))
    (S : Set (Site d)) (η : Site d → ℤ) (hη : ∀ y, 0 ≤ η y)
    (hηhigh : ∀ y, η y ≤ 2 * (d : ℤ) - 1)
    (N : ℕ) (hN : 1 ≤ N) (z : Site d)
    (t0 : ℕ) (w0 : Site d → ℤ) (hw0nn : ∀ x, 0 ≤ w0 x) (hw0one : ∀ x, w0 x ≤ 1)
    (hw0 : ∀ x, w0 x ≤ wave η N z t0 x)
    (hSdom : ∀ s : ℕ, ∀ x ∈ S, w0 x ≤ wave η N z (t0 + s) x) :
    ∀ s x, fodo S η w0 s x ≤ wave η N z (t0 + s) x := by
  intro s
  induction s with
  | zero =>
    intro x
    rw [fodo_zero]
    simpa using hw0 x
  | succ s ih =>
    intro x
    rw [fodo_succ]
    by_cases hx : x ∈ S
    · rw [if_pos hx]
      have h := hSdom (s + 1) x hx
      rwa [show t0 + (s + 1) = t0 + s + 1 from by omega] at h
    · rw [if_neg hx]
      by_cases hxz : x = z
      · subst hxz
        rw [wave_at_centre]
        have hle1 := fodo_le_one S η w0 hηhigh hw0one hw0nn (s + 1) x
        have hN' : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
        rw [fodo_succ] at hle1
        rw [if_neg hx] at hle1
        linarith
      · rw [show t0 + (s + 1) = t0 + s + 1 from by omega,
          wave_of_ne η N z x (t0 + s) hxz]
        split_ifs with hc
        · rw [Int.le_ediv_iff_mul_le (by positivity)]
          have hc' : 2 * (d : ℤ) ≤ η x + lap (fodo S η w0 s) x := hc
          rw [lap] at hc'
          have hmono := nbrSumZ_mono (fun y => ih y) x
          linarith
        · rw [add_zero, ← wave_of_ne η N z x (t0 + s) hxz]
          exact le_trans (ih x) (wave_mono_t η hη hd0 N z (t0 + s) x)

/-- The neighbour sum is translation invariant. -/
theorem nbrSumZ_shift (u : Site d → ℤ) (c x : Site d) :
    nbrSumZ (fun y => u (y + c)) x = nbrSumZ u (x + c) := by
  simp only [nbrSumZ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show x + unit i + c = (x + c) + unit i from by abel,
    show x - unit i + c = (x + c) - unit i from by abel]

/-- The Laplacian is translation invariant. -/
theorem lap_shift (u : Site d → ℤ) (c x : Site d) :
    lap (fun y => u (y + c)) x = lap u (x + c) := by
  simp only [lap, nbrSumZ_shift]

/-- The frozen odometer is equivariant under translation of the lattice. -/
theorem fodo_shift (S : Set (Site d)) (s0 w0 : Site d → ℤ) (c : Site d) :
    ∀ t x, fodo {y | y + c ∈ S} (fun y => s0 (y + c)) (fun y => w0 (y + c)) t x
      = fodo S s0 w0 t (x + c) := by
  intro t
  induction t with
  | zero => intro x; rfl
  | succ t ih =>
    intro x
    rw [fodo_succ, fodo_succ]
    by_cases hx : x + c ∈ S
    · rw [if_pos hx, if_pos (show x ∈ {y | y + c ∈ S} from hx)]
    · rw [if_neg hx, if_neg (show ¬ (x ∈ {y | y + c ∈ S}) from hx)]
      have hfun : fodo {y | y + c ∈ S} (fun y => s0 (y + c)) (fun y => w0 (y + c)) t
          = fun y => fodo S s0 w0 t (y + c) := funext fun y => ih y
      have hconf : fconf {y | y + c ∈ S} (fun y => s0 (y + c)) (fun y => w0 (y + c)) t x
          = fconf S s0 w0 t (x + c) := by
        simp only [fconf]
        rw [hfun, lap_shift]
      rw [hconf, ih]

/-- The frozen odometer is nondecreasing in time, for any seed and background:
the increment is `0` or `1`. -/
theorem fodo_mono_time (S : Set (Site d)) (η : Site d → ℤ) (w0 : Site d → ℤ)
    (t : ℕ) (x : Site d) : fodo S η w0 t x ≤ fodo S η w0 (t + 1) x := by
  rw [fodo_succ]
  by_cases hx : x ∈ S
  · rw [if_pos hx, fodo_of_mem S η w0 t hx]
  · rw [if_neg hx]
    exact le_add_of_nonneg_right (by positivity)

end Exploding
