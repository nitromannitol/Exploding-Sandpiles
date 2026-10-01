/-
The critical case `r = d`: finite seeds do not grow.

For threshold `d` bootstrap percolation with `d ≥ 2`, the toppling closure of any
configuration that is occupied only inside the cube `Q_K^d` stays inside `Q_K^d`.
A site outside `Q_K` has at most one neighbour in `Q_K` (moving parallel to the
nearest face keeps the out-of-range coordinate out of range), and `d ≥ 2`
topplings are required, so nothing outside can ever topple.

Consequently no finite "critical droplet" has unbounded closure in the critical
case `r = d`; in particular a fully occupied box is a fixed point.  This is why a
supercritical Bernoulli block coarse graining, which would need a growing local
seed, cannot prove `xsch13_Percolates`; the percolation for `r = d` is carried by a
global diagonal structure (Schonmann 1992) rather than by a block droplet.

The file records this obstruction; it does not claim `xsch13_Percolates`.
-/
import Exploding.Support.ExtSchProof16

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- A step displacement changes its own coordinate by `±1`. -/
theorem xsch17_coord_dir_self (x : Site d) (s : Fin d × Bool) :
    (x + xsch_dir s) s.1 = x s.1 + (if s.2 then 1 else -1) := by
  rw [Pi.add_apply]
  unfold xsch_dir
  by_cases h : s.2 <;> simp [h, unit, Pi.single_eq_same]

/-- A step displacement leaves the other coordinates unchanged. -/
theorem xsch17_coord_dir_ne (x : Site d) (s : Fin d × Bool) {j : Fin d} (h : j ≠ s.1) :
    (x + xsch_dir s) j = x j := by
  rw [Pi.add_apply]
  unfold xsch_dir
  by_cases hb : s.2 <;> simp [hb, unit, Pi.single_eq_of_ne h]

/-- A site outside `Q_K^d` has at most one neighbour inside it, for `d ≥ 2`. -/
theorem xsch17_nbr_card_le_one (K : ℕ) {x : Site d}
    (hbad : ∃ j, x j < 1 ∨ (K : ℤ) < x j) (S : Finset (Fin d × Bool))
    (hS : ∀ s ∈ S, (x + xsch_dir s) ∈ cube d K) : S.card ≤ 1 := by
  obtain ⟨j0, hj0⟩ := hbad
  have hcoord : ∀ s ∈ S, s.1 = j0 := by
    intro s hs
    by_contra hne
    have h1 := (hS s hs) j0
    rw [xsch17_coord_dir_ne x s (Ne.symm hne)] at h1
    rcases hj0 with h | h <;> omega
  have key : ∀ s ∈ S, (s.2 = true → x j0 + 1 ≤ (K : ℤ)) ∧
      (s.2 = false → 1 ≤ x j0 - 1) := by
    intro s hs
    have hsj : s.1 = j0 := hcoord s hs
    have h1 := (hS s hs) j0
    have hval : (x + xsch_dir s) j0 = x j0 + (if s.2 then (1 : ℤ) else -1) := by
      rw [← hsj]; exact xsch17_coord_dir_self x s
    constructor
    · intro hs2
      have hthis : (x + xsch_dir s) j0 = x j0 + 1 := by
        rw [hval, hs2]
        simp only [if_true]
      rw [hthis] at h1
      exact h1.2
    · intro hs2
      have hthis : (x + xsch_dir s) j0 = x j0 - 1 := by
        rw [hval, hs2]
        simp only [Bool.false_eq_true, if_false]
        ring
      rw [hthis] at h1
      exact h1.1
  rw [Finset.card_le_one]
  intro a ha b hb
  have ha1 : a.1 = j0 := hcoord a ha
  have hb1 : b.1 = j0 := hcoord b hb
  have h2 : a.2 = b.2 := by
    by_contra hne
    have ka := key a ha
    have kb := key b hb
    cases haa : a.2
    · have hb2 : b.2 = true := by cases hbb : b.2 <;> simp_all
      have h3 := ka.2 haa
      have h4 := kb.1 hb2
      rcases hj0 with h | h <;> omega
    · have hb2 : b.2 = false := by cases hbb : b.2 <;> simp_all
      have h3 := ka.1 haa
      have h4 := kb.2 hb2
      rcases hj0 with h | h <;> omega
  ext
  · rw [ha1, hb1]
  · exact h2

/-- **Finite seeds do not grow.**  If every occupied site lies in `Q_K^d`, then so
does every site that topples, for `d ≥ 2`. -/
theorem xsch17_Top_subset_cube (hd : 2 ≤ d) (K : ℕ) (B : Set (Site d)) (η : Site d → ℤ)
    (hη : ∀ x, η x = 2 * (d : ℤ) → x ∈ cube d K)
    (x : Site d) (hx : xsch_Top (Finset.univ : Finset (Fin d)) B η x) : x ∈ cube d K := by
  refine xsch_Top.rec (motive := fun y _ => y ∈ cube d K) ?_ ?_ hx
  · intro y _ h2
    exact hη y h2
  · intro y S _ hSJ hcard hnbr ih j
    by_cases hgood : 1 ≤ y j ∧ y j ≤ (K : ℤ)
    · exact hgood
    · have hbad : ∃ j, y j < 1 ∨ (K : ℤ) < y j := by
        refine ⟨j, ?_⟩
        by_cases h : 1 ≤ y j
        · right; omega
        · left; omega
      have h1 : S.card ≤ 1 := xsch17_nbr_card_le_one K hbad S (fun s hs => ih s hs)
      have h2 : d ≤ S.card := by simpa using hcard
      omega

end Exploding
