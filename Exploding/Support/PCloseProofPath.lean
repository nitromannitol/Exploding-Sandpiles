/-
The first deterministic steps of the second inequality of Lemma 3.7
(`exploding.tex:828-835`): a site reached by the last wave is reached along a
path of distinct sites that are all positive, and a path of positive sites
carries positivity to its bounding rectangle within the size of that rectangle.
-/
import Exploding.Support.Vocab
import Exploding.Support.Wave
import Exploding.Support.SubGeom
import Exploding.Support.SubBox
import Exploding.Frozen.LocalConvexity

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- Positivity of the wave persists in time on a nonnegative background. -/
theorem pclose_pos_mono (hd0 : (0 : ℤ) < 2 * (d : ℤ)) (η : Site d → ℤ)
    (hlow : ∀ y, 0 ≤ η y) (N : ℕ) (z : Site d) {s t : ℕ} (hst : s ≤ t) {x : Site d}
    (h : 0 < wave η N z s x) : 0 < wave η N z t x :=
  lt_of_lt_of_le h (wave_mono_time η hlow hd0 N z hst x)

/-- A site positive for the wave at time `s` is joined to the centre by a path of
pairwise distinct sites, all positive at time `s`: a site outside the support
at time `s - 1` has a positive neighbour there, because `η ≤ 2d - 1`. -/
theorem pclose_path_extract (η : Site d → ℤ) (hlow : ∀ y, 0 ≤ η y)
    (hhigh : ∀ y, η y ≤ 2 * (d : ℤ) - 1) (hd0 : (0 : ℤ) < 2 * (d : ℤ))
    (N : ℕ) :
    ∀ s : ℕ, ∀ y : Site d, 0 < wave η N 0 s y →
      ∃ (m : ℕ) (z : ℕ → Site d), z 0 = 0 ∧ z m = y ∧
        (∀ i, i < m → (lattice d).Adj (z i) (z (i + 1))) ∧
        (∀ i j, i ≤ m → j ≤ m → z i = z j → i = j) ∧
        ∀ i, i ≤ m → 0 < wave η N 0 s (z i) := by
  intro s
  induction s with
  | zero =>
    intro y hy
    have hy0 : y = 0 := by
      by_contra hne
      rw [wave_zero, if_neg hne] at hy
      exact lt_irrefl _ hy
    subst hy0
    refine ⟨0, fun _ => 0, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i), ?_, ?_⟩
    · intro i j hi hj _
      omega
    · intro i _
      exact hy
  | succ s ih =>
    intro y hy
    by_cases hps : 0 < wave η N 0 s y
    · obtain ⟨m, z, h0, hm, hadj, hinj, hpos⟩ := ih y hps
      exact ⟨m, z, h0, hm, hadj, hinj, fun i hi =>
        pclose_pos_mono hd0 η hlow N 0 (Nat.le_succ s) (hpos i hi)⟩
    · have hy0 : y ≠ 0 := by
        intro h0
        subst h0
        rw [wave_at_centre] at hy hps
        exact hps hy
      rw [wave_of_ne η N 0 y s hy0] at hy
      have h1 : (1 : ℤ) ≤ (nbrSumZ (wave η N 0 s) y + η y) / (2 * (d : ℤ)) := hy
      rw [Int.le_ediv_iff_mul_le hd0] at h1
      have hS : 0 < nbrSumZ (wave η N 0 s) y := by linarith [hhigh y]
      obtain ⟨y', hadj', hy'pos⟩ :=
        exists_adj_pos_of_nbrSumZ_pos _ (wave_nonneg η hlow N 0 s) y hS
      obtain ⟨m, z, h0, hm, hadj, hinj, hpos⟩ := ih y' hy'pos
      refine ⟨m + 1, fun i => if i ≤ m then z i else y, ?_, ?_, ?_, ?_, ?_⟩
      · simpa using h0
      · simp
      · intro i hi
        by_cases him : i < m
        · have h1 : i ≤ m := le_of_lt him
          have h2 : i + 1 ≤ m := him
          simpa [h1, h2] using hadj i him
        · have him' : i = m := by omega
          subst him'
          simp only [le_refl, if_true, Nat.lt_irrefl, Nat.succ_le_iff]
          simp only [if_false]
          rw [hm]
          exact hadj'
      · intro i j hi hj hij
        by_cases hi' : i ≤ m <;> by_cases hj' : j ≤ m
        · simp only [hi', hj', if_true] at hij
          exact hinj i j hi' hj' hij
        · simp only [hi', hj', if_true, if_false] at hij
          exfalso
          have := hpos i hi'
          rw [hij] at this
          exact hps this
        · simp only [hi', hj', if_true, if_false] at hij
          exfalso
          have := hpos j hj'
          rw [← hij] at this
          exact hps this
        · omega
      · intro i hi
        by_cases hi' : i ≤ m
        · simp only [hi', if_true]
          exact pclose_pos_mono hd0 η hlow N 0 (Nat.le_succ s) (hpos i hi')
        · simp only [hi', if_false]
          rw [wave_of_ne η N 0 y s hy0]
          exact (Int.le_ediv_iff_mul_le hd0).mpr (by linarith [hhigh y] : (1 : ℤ) * (2 * (d : ℤ)) ≤ _)

/-- The Manhattan norm of a unit vector. -/
theorem pclose_mnorm_unit (l : Fin d) : mnorm (unit l : Site d) = 1 := by
  unfold mnorm
  have h : ∀ j : Fin d, |(unit l : Site d) j| = if j = l then 1 else 0 := by
    intro j
    by_cases hj : j = l <;> simp [unit, hj]
  simp [h]

/-- The triangle inequality for the Manhattan norm. -/
theorem pclose_mnorm_add_le (a b : Site d) : mnorm (a + b) ≤ mnorm a + mnorm b := by
  unfold mnorm
  calc ∑ j, |(a + b) j| ≤ ∑ j, (|a j| + |b j|) := Finset.sum_le_sum fun j _ => abs_add_le _ _
    _ = ∑ j, |a j| + ∑ j, |b j| := Finset.sum_add_distrib

/-- The Manhattan norm is invariant under negation. -/
theorem pclose_mnorm_neg (a : Site d) : mnorm (-a) = mnorm a := by
  unfold mnorm
  simp

/-- The Manhattan norm of a difference. -/
theorem pclose_mnorm_sub_le (a b : Site d) : mnorm (a - b) ≤ mnorm a + mnorm b := by
  rw [sub_eq_add_neg]
  have := pclose_mnorm_add_le a (-b)
  rwa [pclose_mnorm_neg] at this

/-- The Manhattan norm is nonnegative. -/
theorem pclose_mnorm_nonneg (a : Site d) : 0 ≤ mnorm a :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- A coordinate is bounded by the Manhattan norm. -/
theorem pclose_abs_coord_le (a : Site d) (l : Fin d) : |a l| ≤ mnorm a :=
  Finset.single_le_sum (f := fun j => |a j|) (fun j _ => abs_nonneg (a j)) (Finset.mem_univ l)

/-- The path of `pclose_path_extract` is long: it has at least `mnorm x` steps, since
each step changes the Manhattan norm by at most one. -/
theorem pclose_mnorm_le_of_path (m : ℕ) (z : ℕ → Site d) (h0 : z 0 = 0)
    (hadj : ∀ i, i < m → (lattice d).Adj (z i) (z (i + 1))) :
    mnorm (z m) ≤ (m : ℤ) := by
  have key : ∀ i, i ≤ m → mnorm (z i) ≤ (i : ℤ) := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [h0]
      simp [mnorm]
    | succ i ih =>
      intro hi
      have hih := ih (by omega)
      obtain ⟨l, hl⟩ := hadj i (by omega)
      have hstep : mnorm (z (i + 1)) ≤ mnorm (z i) + 1 := by
        rcases hl with hl | hl
        · rw [hl]
          have := pclose_mnorm_add_le (z i) (unit l)
          rwa [pclose_mnorm_unit] at this
        · have hz : z i = z (i + 1) + unit l := hl
          have h2 : z (i + 1) = z i - unit l := by rw [hz]; abel
          rw [h2]
          have := pclose_mnorm_sub_le (z i) (unit l)
          rwa [pclose_mnorm_unit] at this
      push_cast
      linarith
  exact key m le_rfl

/-- A path of sites that are positive at time `t` fills its bounding rectangle with
positive sites by time `t + s`, once `s` is at least the size of the rectangle.
This is local convexity (Lemma 2.1) read through the domination of the frozen
odometer by the wave. -/
theorem pclose_fill (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (N : ℕ) (hN : 1 ≤ N) (zc : Site d) (m : ℕ) (z : ℕ → Site d)
    (hpath : ∀ i : ℕ, i < m → (lattice d).Adj (z i) (z (i + 1))) (t : ℕ)
    (hpos : ∀ i, i ≤ m → 0 < wave η N zc t (z i))
    (hfin : (br (z '' {i : ℕ | i ≤ m})).Finite) (s : ℕ)
    (hs : hfin.toFinset.card ≤ s) :
    ∀ y ∈ br (z '' {i : ℕ | i ≤ m}), 0 < wave η N zc (t + s) y := by
  have hd2 : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by linarith
  have hη0 : ∀ y, 0 ≤ η y := fun y => by linarith [hlow y]
  intro y hy
  have hconv := Exploding.Frozen.local_convexity d hd η hlow hhigh m z hpath
    (z '' {i : ℕ | i ≤ m}) rfl hfin s hs y hy
  have hdom := wave_dom_fodo' hd0 (z '' {i : ℕ | i ≤ m}) η hη0 hhigh N hN zc t
    (Set.indicator (z '' {i : ℕ | i ≤ m}) 1)
    (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x)
    (fun x => by by_cases hx : x ∈ z '' {i : ℕ | i ≤ m} <;> simp [Set.indicator, hx])
    (fun x => by
      by_cases hx : x ∈ z '' {i : ℕ | i ≤ m}
      · obtain ⟨i, hi, rfl⟩ := hx
        rw [Set.indicator_of_mem (show z i ∈ z '' {i : ℕ | i ≤ m} from ⟨i, hi, rfl⟩)]
        exact hpos i hi
      · rw [Set.indicator_of_notMem hx]
        exact wave_nonneg η hη0 N zc t x)
    (fun s' x hx => by
      obtain ⟨i, hi, rfl⟩ := hx
      rw [Set.indicator_of_mem (show z i ∈ z '' {i : ℕ | i ≤ m} from ⟨i, hi, rfl⟩)]
      exact pclose_pos_mono hd0 η hη0 N zc (Nat.le_add_right t s') (hpos i hi))
    s y
  rw [hconv] at hdom
  exact lt_of_lt_of_le zero_lt_one hdom

end Exploding
