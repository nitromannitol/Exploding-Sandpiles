/-
The recurrence odometer of Proposition 7.3 of `paper/exploding.tex`.
-/
import Exploding.Support.SubMax
import Exploding.Support.SubTopple

namespace Exploding

open LatticeProb
open scoped Classical

variable {d : ℕ}

/-- The recurrence odometer is at most `1` on `V`. -/
theorem recOdo_le_one (d : ℕ) (hd : 1 ≤ d) (V : Finset (Site d)) (t : ℕ) {x : Site d}
    (hx : x ∈ V) : recOdo d V t x ≤ 1 := by
  have key : ∀ t : ℕ, ∀ x ∈ V, recOdo d V t x ≤ 1 := by
    intro t
    induction t with
    | zero => intro x hx; rw [recOdo_zero_of_mem d V hx]; omega
    | succ t ih =>
      intro x hx
      rw [recOdo_succ, if_neg (by simpa using hx)]
      have hnb : nbrSumZ (recOdo d V t) x ≤ 2 * (d : ℤ) := by
        rw [nbrSumZ]
        have h2 : ∀ i : Fin d, recOdo d V t (x + unit i) + recOdo d V t (x - unit i) ≤ 2 := by
          intro i
          have h1 : recOdo d V t (x + unit i) ≤ 1 := by
            by_cases h : x + unit i ∈ V
            · exact ih _ h
            · rw [recOdo_of_notMem d V t h]; split_ifs <;> omega
          have h3 : recOdo d V t (x - unit i) ≤ 1 := by
            by_cases h : x - unit i ∈ V
            · exact ih _ h
            · rw [recOdo_of_notMem d V t h]; split_ifs <;> omega
          linarith
        calc ∑ i : Fin d, (recOdo d V t (x + unit i) + recOdo d V t (x - unit i))
            ≤ ∑ _ : Fin d, (2 : ℤ) := Finset.sum_le_sum (fun i _ => h2 i)
          _ = 2 * (d : ℤ) := by simp; ring
      split_ifs with hc
      · have hz : recOdo d V t x = 0 := by
          by_contra hne
          have hge : 1 ≤ recOdo d V t x := by
            have := recOdo_nonneg d V t x; omega
          rw [lap] at hc
          nlinarith [hc, hnb, hge]
        omega
      · simpa using ih x hx
  exact key t x hx

end Exploding
