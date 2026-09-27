import Exploding.Support.Vocab
import Exploding.Support.Wave
import Exploding.Support.SubFodo

/-!
# Lattice geometry for the filling argument

Elementary geometry of the lattice used by the penultimate-cluster and
local-convexity arguments of `paper/exploding.tex`: the centred box `cent d m`
is connected, a segment between two of its points that differ in one coordinate
stays inside it, the frozen odometer is monotone in time and in its background
for a zero-one seed, and a site with two toppled neighbours topples next on the
extremal background.
-/
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

/-- The frozen odometer is monotone in time, and its value at a site is `1` from
the first time it topples on. -/
theorem fodo_mono_time' (S : Set (Site d)) (η : Site d → ℤ) (w0 : Site d → ℤ)
    {s t : ℕ} (hst : s ≤ t) (x : Site d) : fodo S η w0 s x ≤ fodo S η w0 t x := by
  induction t, hst using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih => exact le_trans ih (fodo_mono_time S η w0 t x)

/-- On the extremal background `η ≡ 2d-2`, a site with two toppled neighbours
topples at the next step. -/
theorem fodo_two_nbrs_topple (S : Set (Site d)) (w0 : Site d → ℤ)
    (_hw0 : ∀ x, w0 x ≤ 1) (_hw0nn : ∀ x, 0 ≤ w0 x)
    (t : ℕ) (x : Site d) (hx : x ∉ S) (h0 : fodo S (fun _ => 2 * (d : ℤ) - 2) w0 t x = 0)
    (h2 : 2 ≤ nbrSumZ (fodo S (fun _ => 2 * (d : ℤ) - 2) w0 t) x) :
    fodo S (fun _ => 2 * (d : ℤ) - 2) w0 (t + 1) x = 1 := by
  rw [fodo_succ, if_neg hx]
  have hc : 2 * (d : ℤ) ≤ fconf S (fun _ => 2 * (d : ℤ) - 2) w0 t x := by
    simp only [fconf, lap, h0, mul_zero, sub_zero]
    linarith
  rw [if_pos hc]
  omega

/-- The increment `1{2d ≤ c}` is monotone in `c`. -/
theorem incr_mono {c c' : ℤ} (h : c ≤ c') :
    (if 2 * (d : ℤ) ≤ c then (1 : ℤ) else 0) ≤ (if 2 * (d : ℤ) ≤ c' then 1 else 0) := by
  split_ifs with h1 h2
  · exact le_refl 1
  · exact absurd (le_trans h1 h) h2
  · omega
  · exact le_refl 0

/-- With a `{0,1}`-valued seed and a background of at most `2d-1` chips, the
frozen odometer is `{0,1}`-valued, so the toppling rule reads
`s0 x + nbrSumZ (fodo …) x ≥ 2d` and is monotone in the background. -/
theorem fodo_mono_background_01 (S : Set (Site d)) (s0 s0' w0 : Site d → ℤ)
    (h : ∀ x, s0 x ≤ s0' x)
    (hhigh : ∀ x, s0' x ≤ 2 * (d : ℤ) - 1)
    (hw0 : ∀ x, w0 x ≤ 1) (hw0nn : ∀ x, 0 ≤ w0 x)
    (t : ℕ) (x : Site d) :
    fodo S s0 w0 t x ≤ fodo S s0' w0 t x := by
  induction t generalizing x with
  | zero => exact le_refl _
  | succ t ih =>
    rw [fodo_succ S s0 w0 t x, fodo_succ S s0' w0 t x]
    by_cases hx : x ∈ S
    · rw [if_pos hx, if_pos hx]
    · rw [if_neg hx, if_neg hx]
      have hle := fodo_le_one S s0' w0 hhigh hw0 hw0nn t x
      have hnn := fodo_nonneg_of_seed S s0' w0 hw0nn t x
      have hle0 := fodo_le_one S s0 w0 (fun y => le_trans (h y) (hhigh y)) hw0 hw0nn t x
      have hnn0 := fodo_nonneg_of_seed S s0 w0 hw0nn t x
      by_cases h1 : fodo S s0' w0 t x = 1
      · by_cases h5 : fodo S s0 w0 t x = 1
        · have hconf : fconf S s0 w0 t x ≤ fconf S s0' w0 t x := by
            simp only [fconf, lap, h5, h1, mul_one]
            have := nbrSumZ_mono (fun y => ih y) x
            linarith [h x]
          rw [h5, h1]
          exact add_le_add_right (incr_mono (d := d) hconf) 1
        · have h6 : fodo S s0 w0 t x = 0 := by omega
          rw [h6]
          have h7 : (if 2 * (d : ℤ) ≤ fconf S s0 w0 t x then (1 : ℤ) else 0) ≤ 1 := by
            split_ifs <;> omega
          have h8 : (if 2 * (d : ℤ) ≤ fconf S s0' w0 t x then (1 : ℤ) else 0) = 0 := by
            split_ifs with hh
            · exfalso
              have h9 : nbrSumZ (fodo S s0' w0 t) x ≤ 2 * (d : ℤ) := by
                simp only [nbrSumZ]
                calc ∑ i : Fin d, (fodo S s0' w0 t (x + unit i) + fodo S s0' w0 t (x - unit i))
                    ≤ ∑ _i : Fin d, ((1 : ℤ) + 1) :=
                      Finset.sum_le_sum fun i _ => by
                        have ha := fodo_le_one S s0' w0 hhigh hw0 hw0nn t (x + unit i)
                        have hb := fodo_le_one S s0' w0 hhigh hw0 hw0nn t (x - unit i)
                        linarith
                  _ = 2 * (d : ℤ) := by
                      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
              simp only [fconf, lap, h1, mul_one] at hh
              linarith [hhigh x]
            · rfl
          rw [h8]
          linarith
      · have h0 : fodo S s0' w0 t x = 0 := by omega
        have h0' : fodo S s0 w0 t x = 0 := by
          have h4 : 0 ≤ fodo S s0 w0 t x := fodo_nonneg_of_seed S s0 w0 hw0nn t x
          have h7 : fodo S s0 w0 t x ≤ fodo S s0' w0 t x := ih x
          omega
        rw [h0, h0']
        have hconf : fconf S s0 w0 t x ≤ fconf S s0' w0 t x := by
          simp only [fconf, lap, h0, h0', mul_zero, sub_zero]
          have := nbrSumZ_mono (fun y => ih y) x
          linarith [h x]
        simpa using incr_mono (d := d) hconf

/-- **"By monotonicity of parallel toppling, we may take `η = 2d-2`"**
(`exploding.tex:539-540`).  A result proved on the extremal background
transports to any background in `[2d-2, 2d-1]`: the frozen odometer is monotone
in the background (`fodo_mono_background_01`) and is at most `1`
(`fodo_le_one`). -/
theorem local_convexity_wlog_eta (A : Set (Site d)) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (t : ℕ) (x : Site d)
    (hmin : fodo A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1) t x = 1) :
    fodo A η (Set.indicator A 1) t x = 1 := by
  have hle : fodo A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1) t x ≤
      fodo A η (Set.indicator A 1) t x :=
    fodo_mono_background_01 A (fun _ => 2 * (d : ℤ) - 2) η (Set.indicator A 1)
      hlow hhigh (fun y => by
        by_cases hy : y ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy])
      (fun y => by
        by_cases hy : y ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]) t x
  have hcap : fodo A η (Set.indicator A 1) t x ≤ 1 :=
    fodo_le_one A η (Set.indicator A 1) hhigh
      (fun y => by
        by_cases hy : y ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy])
      (fun y => by
        by_cases hy : y ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]) t x
  linarith

/-- A nonnegative function is bounded by the neighbour sum at a site adjacent
to it. -/
theorem le_nbrSumZ_of_adj {u : Site d → ℤ} (hu : ∀ y, 0 ≤ u y) {x y : Site d}
    (h : (lattice d).Adj x y) : u y ≤ nbrSumZ u x := by
  obtain ⟨i, hi | hi⟩ := h
  · rw [hi]
    have h1 : u (x + unit i) ≤ ∑ k : Fin d, u (x + unit k) :=
      Finset.single_le_sum (f := fun k : Fin d => u (x + unit k))
        (fun k _ => hu _) (Finset.mem_univ i)
    have h2 : 0 ≤ ∑ k : Fin d, u (x - unit k) := Finset.sum_nonneg (fun k _ => hu _)
    simp only [nbrSumZ, Finset.sum_add_distrib]
    linarith
  · have hy : y = x - unit i := by rw [hi]; abel
    rw [hy]
    have h1 : u (x - unit i) ≤ ∑ k : Fin d, u (x - unit k) :=
      Finset.single_le_sum (f := fun k : Fin d => u (x - unit k))
        (fun k _ => hu _) (Finset.mem_univ i)
    have h2 : 0 ≤ ∑ k : Fin d, u (x + unit k) := Finset.sum_nonneg (fun k _ => hu _)
    simp only [nbrSumZ, Finset.sum_add_distrib]
    linarith

/-- Two distinct neighbours of a site contribute their values to the neighbour
sum. -/
theorem add_le_nbrSumZ_of_adj {u : Site d → ℤ} (hu : ∀ y, 0 ≤ u y) {x y z : Site d}
    (hxy : (lattice d).Adj x y) (hxz : (lattice d).Adj x z) (hyz : y ≠ z) :
    u y + u z ≤ nbrSumZ u x := by
  obtain ⟨i, hi | hi⟩ := hxy
  · obtain ⟨j, hj | hj⟩ := hxz
    · have hij : i ≠ j := by
        intro h
        exact hyz (by rw [hi, hj, h])
      have h1 : u (x + unit i) + u (x + unit j) ≤ ∑ k : Fin d, u (x + unit k) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        have h2 : u (x + unit j) ≤ ∑ k ∈ Finset.univ.erase i, u (x + unit k) :=
          Finset.single_le_sum (f := fun k : Fin d => u (x + unit k))
            (fun k _ => hu _) (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)
        linarith
      have h3 : 0 ≤ ∑ k : Fin d, u (x - unit k) := Finset.sum_nonneg (fun k _ => hu _)
      simp only [nbrSumZ, Finset.sum_add_distrib]
      rw [hi, hj]
      linarith
    · have hz : z = x - unit j := by rw [hj]; abel
      have h1 : u (x + unit i) ≤ ∑ k : Fin d, u (x + unit k) :=
        Finset.single_le_sum (f := fun k : Fin d => u (x + unit k))
          (fun k _ => hu _) (Finset.mem_univ i)
      have h2 : u (x - unit j) ≤ ∑ k : Fin d, u (x - unit k) :=
        Finset.single_le_sum (f := fun k : Fin d => u (x - unit k))
          (fun k _ => hu _) (Finset.mem_univ j)
      simp only [nbrSumZ, Finset.sum_add_distrib]
      rw [hi, hz]
      linarith
  · obtain ⟨j, hj | hj⟩ := hxz
    · have hy : y = x - unit i := by rw [hi]; abel
      have h1 : u (x - unit i) ≤ ∑ k : Fin d, u (x - unit k) :=
        Finset.single_le_sum (f := fun k : Fin d => u (x - unit k))
          (fun k _ => hu _) (Finset.mem_univ i)
      have h2 : u (x + unit j) ≤ ∑ k : Fin d, u (x + unit k) :=
        Finset.single_le_sum (f := fun k : Fin d => u (x + unit k))
          (fun k _ => hu _) (Finset.mem_univ j)
      simp only [nbrSumZ, Finset.sum_add_distrib]
      rw [hy, hj]
      linarith
    · have hy : y = x - unit i := by rw [hi]; abel
      have hz : z = x - unit j := by rw [hj]; abel
      have hij : i ≠ j := by
        intro h
        exact hyz (by rw [hy, hz, h])
      have h1 : u (x - unit i) + u (x - unit j) ≤ ∑ k : Fin d, u (x - unit k) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        have h2 : u (x - unit j) ≤ ∑ k ∈ Finset.univ.erase i, u (x - unit k) :=
          Finset.single_le_sum (f := fun k : Fin d => u (x - unit k))
            (fun k _ => hu _) (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)
        linarith
      have h3 : 0 ≤ ∑ k : Fin d, u (x + unit k) := Finset.sum_nonneg (fun k _ => hu _)
      simp only [nbrSumZ, Finset.sum_add_distrib]
      rw [hy, hz]
      linarith

/-- The frozen odometer on the extremal background, started from the indicator
of `A`, is `1` on `A` at every time. -/
theorem fodo_indicator_mem (A : Set (Site d)) (t : ℕ) {x : Site d} (hx : x ∈ A) :
    fodo A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1) t x = 1 := by
  rw [fodo_of_mem A _ _ t hx, Set.indicator_of_mem hx]
  rfl

/-- The frozen odometer on the extremal background, started from the indicator
of `A`, is `{0,1}`-valued. -/
theorem fodo_indicator_le_one (A : Set (Site d)) (t : ℕ) (x : Site d) :
    fodo A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1) t x ≤ 1 :=
  fodo_le_one A _ _ (fun y => by omega)
    (fun y => by by_cases hy : y ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy])
    (fun y => by by_cases hy : y ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]) t x

/-- The frozen odometer on the extremal background, started from the indicator
of `A`, is nonnegative. -/
theorem fodo_indicator_nonneg (A : Set (Site d)) (t : ℕ) (x : Site d) :
    0 ≤ fodo A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1) t x :=
  fodo_nonneg_of_seed A _ _
    (fun y => by by_cases hy : y ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]) t x

/-- A site of the bounding box of a path that is not yet toppled and has two
toppled neighbours topples at the next step. -/
theorem fodo_fill_step (A : Set (Site d)) (t : ℕ) (x y z : Site d)
    (hx : x ∉ A) (hxy : (lattice d).Adj y x) (hy : fodo A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1) t y = 1)
    (hxz : (lattice d).Adj z x) (hz : fodo A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1) t z = 1)
    (hyz : y ≠ z) :
    fodo A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1) (t + 1) x = 1 := by
  have hle := fodo_indicator_le_one A t x
  have hnn := fodo_indicator_nonneg A t x
  by_cases h1 : fodo A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1) t x = 1
  · have hmono := fodo_mono_time A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1) t x
    have hle' := fodo_indicator_le_one A (t + 1) x
    omega
  · have h0 : fodo A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1) t x = 0 := by omega
    refine Exploding.fodo_two_nbrs_topple A (Set.indicator A 1)
      (fun y => by by_cases hy : y ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy])
      (fun y => by by_cases hy : y ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy])
      t x hx h0 ?_
    have hsum := add_le_nbrSumZ_of_adj (u := fodo A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1) t)
      (fun y => fodo_indicator_nonneg A t y) hxy.symm hxz.symm hyz
    rw [hy, hz] at hsum
    simp only [nbrSumZ] at hsum
    have h2 : (2 : ℤ) ≤ nbrSumZ (fodo A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1) t) x := by
      simp only [nbrSumZ]
      linarith
    exact h2

/-- The terminal support of the frozen odometer on the extremal background: the
sites that topple at some time. -/
def fillSet (A : Set (Site d)) : Set (Site d) :=
  {x | ∃ t, fodo A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1) t x = 1}

/-- The seed is in the terminal support. -/
theorem mem_fillSet_of_mem (A : Set (Site d)) {x : Site d} (hx : x ∈ A) :
    x ∈ fillSet A :=
  ⟨0, fodo_indicator_mem A 0 hx⟩

/-- The terminal support is closed under the toppling rule: a site off `A` with
two distinct neighbours in the support is in the support. -/
theorem fillSet_two_nbrs (A : Set (Site d)) {x y z : Site d}
    (hy : y ∈ fillSet A) (hz : z ∈ fillSet A) (hyz : y ≠ z)
    (hxy : (lattice d).Adj y x) (hxz : (lattice d).Adj z x) :
    x ∈ fillSet A := by
  by_cases hx : x ∈ A
  · exact mem_fillSet_of_mem A hx
  · obtain ⟨ty, hty⟩ := hy
    obtain ⟨tz, htz⟩ := hz
    refine ⟨max ty tz + 1, ?_⟩
    refine fodo_fill_step A (max ty tz) x y z hx hxy ?_ hxz ?_ hyz
    · have h := fodo_mono_time' A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1)
        (le_max_left ty tz) y
      rw [hty] at h
      exact le_antisymm (fodo_indicator_le_one A (max ty tz) y) h
    · have h := fodo_mono_time' A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1)
        (le_max_right ty tz) z
      rw [htz] at h
      exact le_antisymm (fodo_indicator_le_one A (max ty tz) z) h

/-- A box in the coordinates other than `i`, as a set. -/
def slab (a b : Site d) (i : Fin d) (c : ℤ) : Set (Site d) :=
  {y | y i = c ∧ ∀ j, j ≠ i → a j ≤ y j ∧ y j ≤ b j}

/-- The `i`-th coordinate of a point of the slab below the cap. -/
theorem slab_sub_unit_mem (a b : Site d) (i : Fin d) (hab : a i ≤ b i) {y : Site d}
    (hy : y ∈ slab a b i (b i + 1)) :
    ∀ j, a j ≤ (y - unit i) j ∧ (y - unit i) j ≤ b j := by
  intro j
  by_cases hji : j = i
  · rw [hji]
    have h1 : (y - unit i) i = y i - 1 := by
      simp only [Pi.sub_apply, LatticeProb.unit, Pi.single_eq_same]
    rw [h1, hy.1]
    exact ⟨by linarith, by linarith⟩
  · have h1 : (y - unit i) j = y j := by
      simp only [Pi.sub_apply, LatticeProb.unit, Pi.single_eq_of_ne hji, sub_zero]
    rw [h1]
    exact hy.2 j hji

/-- Moving one coordinate of a point of the slab by one step, staying in the
slab. -/
theorem slab_move (a b : Site d) (i : Fin d) (c : ℤ) {p : Site d}
    (hp : p ∈ slab a b i c) (j : Fin d) (hj : j ≠ i) {d' : ℤ}
    (hlo : a j ≤ p j + d') (hhi : p j + d' ≤ b j) :
    p + d' • unit j ∈ slab a b i c := by
  refine ⟨?_, ?_⟩
  · have h1 : (p + d' • unit j) i = p i := by
      rw [coord_add_smul]
      simp only [if_neg (Ne.symm hj), mul_zero, add_zero]
    rw [h1]; exact hp.1
  · intro k hki
    rw [coord_add_smul]
    have h2 := hp.2 k hki
    by_cases hkj : k = j
    · rw [if_pos hkj]
      constructor
      · have h3 : p k + d' * 1 = p k + d' := by ring
        rw [h3]
        subst hkj
        exact hlo
      · have h3 : p k + d' * 1 = p k + d' := by ring
        rw [h3]
        subst hkj
        exact hhi
    · rw [if_neg hkj, mul_zero, add_zero]
      exact h2

/-- **The cap spread** (`exploding.tex:545-553`, the mechanism of the one-turn
case): if a box `B` is in the terminal support of the frozen odometer on the
extremal background, and one point of the cap `S` one step above `B` in
direction `i` is in the terminal support, then the whole cap is.

The proof: `S` is a box in the coordinates `≠ i`, hence connected; along a path
in `S` each step is in a direction `j ≠ i`, and a point of `S` whose predecessor
is in the support has the two distinct neighbours `predecessor` (in the support)
and `point - e_i` (in `B`, hence in the support). -/
theorem fillSet_slab (A : Set (Site d)) (a b : Site d) (i : Fin d) (hab : a i ≤ b i)
    (hbox : ∀ x, (∀ j, a j ≤ x j ∧ x j ≤ b j) → x ∈ fillSet A)
    {y : Site d} (hy : y ∈ slab a b i (b i + 1)) (hyF : y ∈ fillSet A) :
    slab a b i (b i + 1) ⊆ fillSet A := by
  -- a single step of the slab in a direction `j ≠ i` preserves membership in `fillSet`
  have hstep : ∀ {p : Site d}, p ∈ slab a b i (b i + 1) → p ∈ fillSet A →
      ∀ j : Fin d, j ≠ i → ∀ c : ℤ, (c = 1 ∨ c = -1) →
      p + c • unit j ∈ slab a b i (b i + 1) →
      p + c • unit j ∈ fillSet A := by
    intro p hp hpF j hj c hc hpj
    refine fillSet_two_nbrs A (x := p + c • unit j) (y := p)
      (z := p + c • unit j - unit i)
      hpF (hbox (p + c • unit j - unit i) (slab_sub_unit_mem a b i hab hpj)) ?_ ?_ ?_
    · -- the two neighbours differ in coordinate `i`
      intro hcon
      have h1 := congrFun hcon i
      have h2 : (p + c • unit j - unit i) i = p i - 1 := by
        rw [Pi.sub_apply, coord_add_smul]
        simp only [if_neg (Ne.symm hj), mul_zero, add_zero, LatticeProb.unit,
          Pi.single_eq_same]
      rw [h2] at h1
      omega
    · rcases hc with hc | hc
      · refine ⟨j, Or.inl ?_⟩
        rw [hc, one_smul]
      · refine ⟨j, Or.inr ?_⟩
        rw [hc, neg_smul, one_smul]
        abel
    · refine ⟨i, Or.inl ?_⟩
      abel
  -- move one coordinate of `p` to that of `q`, one step at a time
  have hmove : ∀ {p q : Site d} (j : Fin d), j ≠ i →
      p ∈ slab a b i (b i + 1) → p ∈ fillSet A →
      (∀ k, k ≠ j → p k = q k) → q ∈ slab a b i (b i + 1) →
      q ∈ fillSet A := by
    intro p q j hj hp hpF hagree hq
    set N : ℕ := (if p j ≤ q j then (q j - p j).toNat else (p j - q j).toNat) with hN
    have hNle : p j + (N : ℤ) * (if p j ≤ q j then 1 else -1) = q j := by
      rw [hN]
      by_cases hle : p j ≤ q j
      · rw [if_pos hle, if_pos hle]
        have h0 : (0 : ℤ) ≤ q j - p j := by linarith
        rw [Int.toNat_of_nonneg h0]
        ring
      · rw [if_neg hle, if_neg hle]
        have h0 : (0 : ℤ) ≤ p j - q j := by linarith
        rw [Int.toNat_of_nonneg h0]
        ring
    have hbetween : ∀ (n : ℕ), n ≤ N →
        min (p j) (q j) ≤ p j + (n : ℤ) * (if p j ≤ q j then 1 else -1) ∧
        p j + (n : ℤ) * (if p j ≤ q j then 1 else -1) ≤ max (p j) (q j) := by
      intro n hn
      have hnN : (n : ℤ) ≤ (N : ℤ) := by exact_mod_cast hn
      by_cases hle : p j ≤ q j
      · rw [if_pos hle]
        have hN' : p j + (N : ℤ) = q j := by
          have h := hNle; rw [if_pos hle] at h; simpa using h
        constructor
        · rw [min_eq_left hle]; linarith
        · rw [max_eq_right hle]; linarith
      · rw [if_neg hle]
        have hN' : p j - (N : ℤ) = q j := by
          have h := hNle; rw [if_neg hle] at h; linarith
        constructor
        · rw [min_eq_right (le_of_lt (not_le.mp hle))]; linarith
        · rw [max_eq_left (le_of_lt (not_le.mp hle))]; linarith
    have hstep' : ∀ (n : ℕ), n ≤ N →
        (fun l => if l = j then p j + (n : ℤ) * (if p j ≤ q j then 1 else -1) else p l) ∈
          slab a b i (b i + 1) := by
      intro n hn
      refine ⟨?_, ?_⟩
      · simp only [if_neg (Ne.symm hj)]; exact hp.1
      · intro k hki
        show a k ≤ (if k = j then p j + (n : ℤ) * (if p j ≤ q j then 1 else -1) else p k) ∧
          (if k = j then p j + (n : ℤ) * (if p j ≤ q j then 1 else -1) else p k) ≤ b k
        by_cases hkj : k = j
        · subst hkj
          rw [if_pos rfl]
          have hb := hbetween n hn
          have hpj := hp.2 k hki
          have hqj := hq.2 k hki
          exact ⟨le_trans (le_min hpj.1 hqj.1) hb.1,
            le_trans hb.2 (max_le hpj.2 hqj.2)⟩
        · rw [if_neg hkj]
          exact hp.2 k hki
    have hwalk : ∀ (n : ℕ), n ≤ N →
        (fun l => if l = j then p j + (n : ℤ) * (if p j ≤ q j then 1 else -1) else p l) ∈
          fillSet A := by
      intro n
      induction n with
      | zero =>
        intro _
        have h0 : (fun l => if l = j then p j + ((0 : ℕ) : ℤ) * (if p j ≤ q j then 1 else -1)
            else p l) = p := by
          funext l
          by_cases hlj : l = j
          · subst hlj; simp
          · rw [if_neg hlj]
        rw [h0]; exact hpF
      | succ n ih =>
        intro hn
        have hn' : n ≤ N := le_trans (Nat.le_succ n) hn
        have hprev := ih hn'
        have hcur := hstep' (n + 1) hn
        have hsucc : (fun l => if l = j then p j + ((n : ℕ) : ℤ) * (if p j ≤ q j then 1 else -1)
              else p l) + (if p j ≤ q j then (1 : ℤ) else -1) • unit j =
            (fun l => if l = j then p j + ((n + 1 : ℕ) : ℤ) * (if p j ≤ q j then 1 else -1)
              else p l) := by
          funext l
          by_cases hlj : l = j
          · subst hlj
            rw [coord_add_smul]
            ring_nf
            push_cast
            ring
          · rw [coord_add_smul]
            simp only [if_neg hlj, mul_zero, add_zero]
        rw [← hsucc]
        refine hstep (hstep' n hn') hprev j hj _ ?_ ?_
        · by_cases hle : p j ≤ q j
          · exact Or.inl (by rw [if_pos hle])
          · exact Or.inr (by rw [if_neg hle])
        · rw [hsucc]; exact hcur
    have hfin := hwalk N le_rfl
    have hqeq : (fun l => if l = j then p j + (N : ℤ) * (if p j ≤ q j then 1 else -1)
        else p l) = q := by
      funext l
      by_cases hlj : l = j
      · subst hlj; rw [if_pos rfl]; exact hNle
      · rw [if_neg hlj]; exact hagree l hlj
    rwa [hqeq] at hfin
  -- walk from `y` to the target, one coordinate at a time
  have key : ∀ (s : Finset (Fin d)), i ∉ s →
      ∀ {p q : Site d}, p ∈ slab a b i (b i + 1) → p ∈ fillSet A →
      (∀ j, j ∉ s → p j = q j) → q ∈ slab a b i (b i + 1) →
      q ∈ fillSet A := by
    intro s
    refine Finset.induction (motive := fun s => i ∉ s →
      ∀ {p q : Site d}, p ∈ slab a b i (b i + 1) → p ∈ fillSet A →
      (∀ j, j ∉ s → p j = q j) → q ∈ slab a b i (b i + 1) → q ∈ fillSet A) ?_ ?_ s
    case refine_1 =>
      intro _ p q hp hpF hagree hq
      have hpq : p = q := by
        funext j
        exact hagree j (Finset.notMem_empty j)
      rwa [← hpq]
    case refine_2 =>
      intro j s hjs ih hi p q hp hpF hagree hq
      have hji : j ≠ i := fun h => hi (h ▸ Finset.mem_insert_self j s)
      have hmid : (fun k => if k = j then q j else p k) ∈ slab a b i (b i + 1) := by
        refine ⟨?_, ?_⟩
        · simp only [if_neg (Ne.symm hji)]; exact hp.1
        · intro k hki
          show a k ≤ (if k = j then q j else p k) ∧ (if k = j then q j else p k) ≤ b k
          by_cases hkj : k = j
          · subst hkj
            rw [if_pos rfl]
            exact hq.2 k hki
          · rw [if_neg hkj]
            exact hp.2 k hki
      have hmidF : (fun k => if k = j then q j else p k) ∈ fillSet A :=
        hmove j hji hp hpF (fun k hkj => by rw [if_neg hkj]) hmid
      refine ih (fun h => hi (Finset.mem_insert_of_mem h)) hmid hmidF ?_ hq
      intro k hk
      by_cases hkj : k = j
      · subst hkj
        simp
      · rw [if_neg hkj]
        exact hagree k (by simp [hkj, hk])
  intro q hq
  refine key (Finset.univ.erase i) (Finset.notMem_erase i Finset.univ)
    (p := y) (q := q) hy hyF ?_ hq
  intro j hj
  have hji : j = i := by
    by_contra hne
    exact hj (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ j⟩)
  rw [hji, hy.1, hq.1]
/-- **The cap spread for an arbitrary closed set**: if `F` contains a box and is
closed under the two-neighbour rule, and one point of the cap above the box is
in `F`, then the whole cap is.

This is the combinatorial content of the paper's one-turn case
(`exploding.tex:545-553`), stated without any odometer. -/
theorem closed_slab (F : Set (Site d)) (a b : Site d) (i : Fin d) (hab : a i ≤ b i)
    (hbox : ∀ x, (∀ j, a j ≤ x j ∧ x j ≤ b j) → x ∈ F)
    (hclosed : ∀ x y z' : Site d, y ∈ F → z' ∈ F → y ≠ z' →
      (lattice d).Adj y x → (lattice d).Adj z' x → x ∈ F)
    {y : Site d} (hy : y ∈ slab a b i (b i + 1)) (hyF : y ∈ F) :
    slab a b i (b i + 1) ⊆ F := by
  have hstep : ∀ {p : Site d}, p ∈ slab a b i (b i + 1) → p ∈ F →
      ∀ j : Fin d, j ≠ i → ∀ c : ℤ, (c = 1 ∨ c = -1) →
      p + c • unit j ∈ slab a b i (b i + 1) →
      p + c • unit j ∈ F := by
    intro p hp hpF j hj c hc hpj
    refine hclosed (p + c • unit j) p (p + c • unit j - unit i) hpF
      (hbox (p + c • unit j - unit i) (slab_sub_unit_mem a b i hab hpj)) ?_ ?_ ?_
    · intro hcon
      have h1 := congrFun hcon i
      have h2 : (p + c • unit j - unit i) i = p i - 1 := by
        rw [Pi.sub_apply, coord_add_smul]
        simp only [if_neg (Ne.symm hj), mul_zero, add_zero, LatticeProb.unit,
          Pi.single_eq_same]
      rw [h2] at h1
      omega
    · rcases hc with hc | hc
      · refine ⟨j, Or.inl ?_⟩
        rw [hc, one_smul]
      · refine ⟨j, Or.inr ?_⟩
        rw [hc, neg_smul, one_smul]
        abel
    · refine ⟨i, Or.inl ?_⟩
      abel
  have hmove : ∀ {p q : Site d} (j : Fin d), j ≠ i →
      p ∈ slab a b i (b i + 1) → p ∈ F →
      (∀ k, k ≠ j → p k = q k) → q ∈ slab a b i (b i + 1) →
      q ∈ F := by
    intro p q j hj hp hpF hagree hq
    set N : ℕ := (if p j ≤ q j then (q j - p j).toNat else (p j - q j).toNat) with hN
    have hNle : p j + (N : ℤ) * (if p j ≤ q j then 1 else -1) = q j := by
      rw [hN]
      by_cases hle : p j ≤ q j
      · rw [if_pos hle, if_pos hle]
        have h0 : (0 : ℤ) ≤ q j - p j := by linarith
        rw [Int.toNat_of_nonneg h0]
        ring
      · rw [if_neg hle, if_neg hle]
        have h0 : (0 : ℤ) ≤ p j - q j := by linarith
        rw [Int.toNat_of_nonneg h0]
        ring
    have hbetween : ∀ (n : ℕ), n ≤ N →
        min (p j) (q j) ≤ p j + (n : ℤ) * (if p j ≤ q j then 1 else -1) ∧
        p j + (n : ℤ) * (if p j ≤ q j then 1 else -1) ≤ max (p j) (q j) := by
      intro n hn
      have hnN : (n : ℤ) ≤ (N : ℤ) := by exact_mod_cast hn
      by_cases hle : p j ≤ q j
      · rw [if_pos hle]
        have hN' : p j + (N : ℤ) = q j := by
          have h := hNle; rw [if_pos hle] at h; simpa using h
        constructor
        · rw [min_eq_left hle]; linarith
        · rw [max_eq_right hle]; linarith
      · rw [if_neg hle]
        have hN' : p j - (N : ℤ) = q j := by
          have h := hNle; rw [if_neg hle] at h; linarith
        constructor
        · rw [min_eq_right (le_of_lt (not_le.mp hle))]; linarith
        · rw [max_eq_left (le_of_lt (not_le.mp hle))]; linarith
    have hstep' : ∀ (n : ℕ), n ≤ N →
        (fun l => if l = j then p j + (n : ℤ) * (if p j ≤ q j then 1 else -1) else p l) ∈
          slab a b i (b i + 1) := by
      intro n hn
      refine ⟨?_, ?_⟩
      · simp only [if_neg (Ne.symm hj)]; exact hp.1
      · intro k hki
        show a k ≤ (if k = j then p j + (n : ℤ) * (if p j ≤ q j then 1 else -1) else p k) ∧
          (if k = j then p j + (n : ℤ) * (if p j ≤ q j then 1 else -1) else p k) ≤ b k
        by_cases hkj : k = j
        · subst hkj
          rw [if_pos rfl]
          have hb := hbetween n hn
          have hpj := hp.2 k hki
          have hqj := hq.2 k hki
          refine ⟨le_trans (le_min hpj.1 hqj.1) hb.1, ?_⟩
          exact le_trans hb.2 (max_le hpj.2 hqj.2)
        · rw [if_neg hkj]
          exact hp.2 k hki
    have hwalk : ∀ (n : ℕ), n ≤ N →
        (fun l => if l = j then p j + (n : ℤ) * (if p j ≤ q j then 1 else -1) else p l) ∈
          F := by
      intro n
      induction n with
      | zero =>
        intro _
        have h0 : (fun l => if l = j then p j + ((0 : ℕ) : ℤ) * (if p j ≤ q j then 1 else -1)
            else p l) = p := by
          funext l
          by_cases hlj : l = j
          · subst hlj; simp
          · rw [if_neg hlj]
        rw [h0]; exact hpF
      | succ n ih =>
        intro hn
        have hn' : n ≤ N := le_trans (Nat.le_succ n) hn
        have hprev := ih hn'
        have hcur := hstep' (n + 1) hn
        have hsucc : (fun l => if l = j then p j + ((n : ℕ) : ℤ) * (if p j ≤ q j then 1 else -1)
              else p l) + (if p j ≤ q j then (1 : ℤ) else -1) • unit j =
            (fun l => if l = j then p j + ((n + 1 : ℕ) : ℤ) * (if p j ≤ q j then 1 else -1)
              else p l) := by
          funext l
          by_cases hlj : l = j
          · subst hlj
            rw [coord_add_smul]
            ring_nf
            push_cast
            ring
          · rw [coord_add_smul]
            simp only [if_neg hlj, mul_zero, add_zero]
        rw [← hsucc]
        refine hstep (hstep' n hn') hprev j hj _ ?_ ?_
        · by_cases hle : p j ≤ q j
          · exact Or.inl (by rw [if_pos hle])
          · exact Or.inr (by rw [if_neg hle])
        · rw [hsucc]; exact hcur
    have hfin := hwalk N le_rfl
    have hqeq : (fun l => if l = j then p j + (N : ℤ) * (if p j ≤ q j then 1 else -1)
        else p l) = q := by
      funext l
      by_cases hlj : l = j
      · subst hlj; rw [if_pos rfl]; exact hNle
      · rw [if_neg hlj]; exact hagree l hlj
    rwa [hqeq] at hfin
  have key : ∀ (s : Finset (Fin d)), i ∉ s →
      ∀ {p q : Site d}, p ∈ slab a b i (b i + 1) → p ∈ F →
      (∀ j, j ∉ s → p j = q j) → q ∈ slab a b i (b i + 1) →
      q ∈ F := by
    intro s
    refine Finset.induction (motive := fun s => i ∉ s →
      ∀ {p q : Site d}, p ∈ slab a b i (b i + 1) → p ∈ F →
      (∀ j, j ∉ s → p j = q j) → q ∈ slab a b i (b i + 1) → q ∈ F) ?_ ?_ s
    case refine_1 =>
      intro _ p q hp hpF hagree hq
      have hpq : p = q := by
        funext j
        exact hagree j (Finset.notMem_empty j)
      rwa [← hpq]
    case refine_2 =>
      intro j s hjs ih hi p q hp hpF hagree hq
      have hji : j ≠ i := fun h => hi (h ▸ Finset.mem_insert_self j s)
      have hmid : (fun k => if k = j then q j else p k) ∈ slab a b i (b i + 1) := by
        refine ⟨?_, ?_⟩
        · simp only [if_neg (Ne.symm hji)]; exact hp.1
        · intro k hki
          show a k ≤ (if k = j then q j else p k) ∧ (if k = j then q j else p k) ≤ b k
          by_cases hkj : k = j
          · subst hkj
            rw [if_pos rfl]
            exact hq.2 k hki
          · rw [if_neg hkj]
            exact hp.2 k hki
      have hmidF : (fun k => if k = j then q j else p k) ∈ F :=
        hmove j hji hp hpF (fun k hkj => by rw [if_neg hkj]) hmid
      refine ih (fun h => hi (Finset.mem_insert_of_mem h)) hmid hmidF ?_ hq
      intro k hk
      by_cases hkj : k = j
      · subst hkj
        rw [if_pos rfl]
      · rw [if_neg hkj]
        exact hagree k (by simp [hkj, hk])
  intro q hq
  refine key (Finset.univ.erase i) (Finset.notMem_erase i Finset.univ)
    (p := y) (q := q) hy hyF ?_ hq
  intro j hj
  have hji : j = i := by
    by_contra hne
    exact hj (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ j⟩)
  rw [hji, hy.1, hq.1]


end Exploding
