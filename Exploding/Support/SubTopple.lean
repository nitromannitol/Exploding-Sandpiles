/-
One step of the recurrence argument of Proposition 7.3 of `paper/exploding.tex`:
a site of `V` that has not yet toppled and whose `+e_i` neighbours have all
toppled, topples at the next step.
-/
import Exploding.Support.SubRec
import Exploding.Support.Wave

namespace Exploding

open LatticeProb
open scoped Classical

variable {d : ℕ}

/-- A site of `V` with no toppling yet and all `+e_i` neighbours toppled topples
at the next step. -/
theorem recOdo_topple (d : ℕ) (hd : 1 ≤ d) (V : Finset (Site d)) (t : ℕ) {x : Site d}
    (hx : x ∈ V) (h0 : recOdo d V t x = 0)
    (hup : ∀ i : Fin d, 1 ≤ recOdo d V t (x + unit i)) :
    recOdo d V (t + 1) x = 1 := by
  rw [Exploding.recOdo_succ, if_neg (by simpa using hx), h0, zero_add]
  rw [if_pos]
  rw [Exploding.lap, Exploding.nbrSumZ, h0, mul_zero, sub_zero]
  have hsum : (d : ℤ) ≤ ∑ i : Fin d, (Exploding.recOdo d V t (x + LatticeProb.unit i) + Exploding.recOdo d V t (x - LatticeProb.unit i)) := by
    have hle : (∑ _ : Fin d, (1 : ℤ)) ≤ ∑ i : Fin d, (Exploding.recOdo d V t (x + LatticeProb.unit i) + Exploding.recOdo d V t (x - LatticeProb.unit i)) := by
      apply Finset.sum_le_sum
      intro i _
      have h1 := hup i
      have h2 := Exploding.recOdo_nonneg d V t (x - LatticeProb.unit i)
      linarith
    simpa using hle
  have hd1 : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  linarith [hd1]
