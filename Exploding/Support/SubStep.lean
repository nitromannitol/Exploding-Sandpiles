/-
The propagation step of Lemma 3.2 of `paper/exploding.tex`: once the wave covers
a good cube `Q_k(i)`, it covers an adjacent good cube `Q_k(j)`.

The paper's mechanism (`exploding.tex:499-501`): a good cube is crossed by a
fired line within `k^d` steps.  The line used here is a line of `Q_k(j)` through
a point of the outer boundary of `Q_k(j)` that the coverage of `Q_k(i)` has
already fired; the crossing property of the good cube `Q_k(j)` fills `Q_k(j)`
from it, and the wave dominates that frozen process.
-/
import Exploding.Support.Vocab
import Exploding.Support.Wave
import Exploding.Support.SubGeom

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The wave is equivariant under translation: shifting the background back by
`c` and the centre forward by `c` shifts the wave forward by `c`. -/
theorem wave_shift (η : Site d → ℤ) (N : ℕ) (z c : Site d) :
    ∀ t x, wave (fun y => η (y - c)) N (z + c) t (x + c) = wave η N z t x := by
  intro t
  induction t with
  | zero =>
    intro x
    by_cases h : x = z
    · subst h; simp
    · have h' : x + c ≠ z + c := fun hcon => h (add_right_cancel hcon)
      simp [wave_zero, h, h']
  | succ t ih =>
    intro x
    by_cases h : x = z
    · subst h; simp [wave_at_centre]
    · have h' : x + c ≠ z + c := fun hcon => h (add_right_cancel hcon)
      rw [wave_of_ne _ _ _ _ _ h', wave_of_ne _ _ _ _ _ h]
      have hsum : nbrSumZ (wave (fun y => η (y - c)) N (z + c) t) (x + c) =
          nbrSumZ (wave η N z t) x := by
        simp only [nbrSumZ]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show x + c + unit i = (x + unit i) + c from by abel,
          show x + c - unit i = (x - unit i) + c from by abel]
        rw [ih (x + unit i), ih (x - unit i)]
      rw [hsum]
      congr 1
      congr 1
      abel

/-- The wave dominates the frozen odometer of a good cube once the frozen line
is already fired. -/
theorem crossOdo_le_wave {d : ℕ} (hd0 : (0 : ℤ) < 2 * (d : ℤ))
    (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (N k : ℕ) (hN : 2 ≤ N) (j : Site d) (dir' : Fin d) (z : Site d) (t : ℕ)
    (hseed : ∀ y ∈ line d k dir' z, 0 < wave η N (0 : Site d) t (y + (k : ℤ) • j)) :
    ∀ s y, crossOdo (fun x => η (x + (k : ℤ) • j)) k dir' z s y ≤
      wave η N (0 : Site d) (t + s) (y + (k : ℤ) • j) := by
  classical
  have hseed1 : ∀ y ∈ line d k dir' z, (1 : ℤ) ≤ wave η N (0 : Site d) t (y + (k : ℤ) • j) :=
    fun y hy => hseed y hy
  have hseed0 : ∀ y, (if y ∈ line d k dir' z then (1 : ℤ) else 0) ≤
      wave η N (0 : Site d) t (y + (k : ℤ) • j) := by
    intro y
    by_cases hy : y ∈ line d k dir' z
    · rw [if_pos hy]; exact hseed1 y hy
    · rw [if_neg hy]; exact wave_nonneg η hlow N (0 : Site d) t _
  have hseed0' : ∀ y, (0 : ℤ) ≤ (if y ∈ line d k dir' z then (1 : ℤ) else 0) := by
    intro y
    by_cases hy : y ∈ line d k dir' z <;> simp [hy]
  have hseed1' : ∀ y, (if y ∈ line d k dir' z then (1 : ℤ) else 0) ≤ 1 := by
    intro y
    by_cases hy : y ∈ line d k dir' z <;> simp [hy]
  have hmono : ∀ s y, wave η N (0 : Site d) t (y + (k : ℤ) • j) ≤
      wave η N (0 : Site d) (t + s) (y + (k : ℤ) • j) :=
    fun s y => wave_mono_time η hlow hd0 N (0 : Site d) (Nat.le_add_right t s) _
  have hcap : ∀ s y, crossOdo (fun x => η (x + (k : ℤ) • j)) k dir' z s y ≤ 1 :=
    fun s y => fodo_le_one _ _ _ (fun x => hhigh _) hseed1' hseed0' s y
  intro s
  induction s with
  | zero =>
    intro y
    rw [crossOdo, fodo_zero]
    exact hseed0 y
  | succ s ih =>
    intro y
    rw [crossOdo, fodo_succ]
    by_cases hy : y ∈ (cube d k)ᶜ ∪ line d k dir' z
    · rw [if_pos hy]
      exact le_trans (hseed0 y) (hmono (s + 1) y)
    · rw [if_neg hy]
      have hyc : y ∈ cube d k := by
        by_contra h
        exact hy (Or.inl h)
      have hmono' : wave η N (0 : Site d) (t + s) (y + (k : ℤ) • j) ≤
          wave η N (0 : Site d) (t + s + 1) (y + (k : ℤ) • j) :=
        wave_mono_t η hlow hd0 N (0 : Site d) (t + s) (y + (k : ℤ) • j)
      by_cases hc : 2 * (d : ℤ) ≤ fconf ((cube d k)ᶜ ∪ line d k dir' z)
          (fun x => η (x + (k : ℤ) • j)) (fun x => if x ∈ line d k dir' z then 1 else 0) s y
      · rw [if_pos hc]
        have hsum : nbrSumZ (crossOdo (fun x => η (x + (k : ℤ) • j)) k dir' z s) y ≤
            nbrSumZ (wave η N (0 : Site d) (t + s)) (y + (k : ℤ) • j) := by
          have h1 := nbrSumZ_mono (fun w => ih w) y
          rwa [nbrSumZ_shift] at h1
        have hc' : 2 * (d : ℤ) ≤ η (y + (k : ℤ) • j) +
            lap (crossOdo (fun x => η (x + (k : ℤ) • j)) k dir' z s) y := hc
        rw [lap] at hc'
        have hle1 : crossOdo (fun x => η (x + (k : ℤ) • j)) k dir' z s y ≤
            wave η N (0 : Site d) (t + s) (y + (k : ℤ) • j) := ih y
        rw [show t + (s + 1) = t + s + 1 from by omega]
        by_cases hz : y + (k : ℤ) • j = 0
        · have hN2 : (2 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
          have hc1 := hcap s y
          simp only [crossOdo] at hc1 ⊢
          rw [hz, wave_at_centre]
          linarith
        · rw [wave_of_ne η N (0 : Site d) (y + (k : ℤ) • j) (t + s) hz]
          rw [Int.le_ediv_iff_mul_le (by positivity)]
          simp only [crossOdo] at hsum hc' hle1 ⊢
          nlinarith [hsum, hc', hle1]
      · rw [if_neg hc]
        simp only [crossOdo] at ih ⊢
        have h1 := ih y
        rw [show t + (s + 1) = t + s + 1 from by omega]
        linarith [h1, hmono']

end Exploding
