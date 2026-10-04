/-
The percolation estimate for the cube, and with it Schonmann's bootstrap bound.

The failure probability of the near-cubes along all `d` directions decays faster than any
polynomial in the size (the induction on the number of directions), so the base scale of the
doubling recursion `F(s) ≤ 4^d F(s / 2)^2` is reached with `4^d F(s) ≤ 1 / 2`; from there the
recursion squares the bound at each halving and gives an exponential rate.  The cube `[1, n]^d`
is the box with corners `1` and `n`, a near-cube of size `n` along all directions.
-/
import Exploding.Support.ExtSchDouble
import Exploding.Support.ExtSchExp
import Exploding.Support.ExtSchProof3

open Exploding

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

section Final
variable {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)]

/-- **The percolation estimate.**  The cube is internally spanned with probability
`1 - c exp(-C n)`. -/
theorem xsr_percolation (hd : 1 ≤ d) (hp : 0 < p) : xsch3_PercolationBound d p := by
  set a : ℕ → ℝ := xsr_gbound d p d with ha
  have ha0 : ∀ s, 0 ≤ a s := fun s => xsr_gbound_nonneg _ _
  obtain ⟨c₀, hc₀, hc₀s⟩ := xsr_gbound_decay (xsr_decay_all hp hd) 1
  set C : ℝ := (4 : ℝ) ^ d with hCdef
  have hC : 1 ≤ C := one_le_pow₀ (by norm_num)
  have hrec : ∀ s, 2 ≤ s → a s ≤ C * a (s / 2) ^ 2 := fun s hs => xsr_double_rec hd hs
  have hbase : ∀ s, ⌈2 * C * c₀⌉₊ + 1 ≤ s → C * a s ≤ 1 / 2 := by
    intro s hs
    have hs1 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
    have hsr : 2 * C * c₀ ≤ (s : ℝ) := by
      have h1 : (⌈2 * C * c₀⌉₊ : ℝ) + 1 ≤ (s : ℝ) := by exact_mod_cast hs
      linarith [Nat.le_ceil (2 * C * c₀)]
    have h1 := hc₀s s (by omega)
    rw [pow_one] at h1
    calc C * a s ≤ C * (c₀ / (s : ℝ)) := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = C * c₀ / (s : ℝ) := by ring
      _ ≤ 1 / 2 := by
          rw [div_le_div_iff₀ hs1 (by norm_num)]
          linarith
  obtain ⟨c, c', hc, hc', hexp⟩ := xse_exp_of_recursion a C hC ha0 hrec (⌈2 * C * c₀⌉₊ + 1)
    (Nat.succ_pos _) hbase
  refine ⟨c, c', hc, hc', fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hemp : {η : Site d → ℤ | ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (cube d 0) η} = ∅ := by
      ext η
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      intro x hx
      have h := hx ⟨0, hd⟩
      omega
    rw [hemp, measureReal_empty]
    positivity
  · have hnear : xsb_Near (Finset.univ : Finset (Fin d)) n (fun _ => (1 : ℤ))
        (fun _ => (n : ℤ)) :=
      ⟨fun i _ => Or.inl (by ring), fun i hi => absurd (Finset.mem_univ i) hi⟩
    have hge := xsr_gbound_ge (p := p) (k := d) (J' := (Finset.univ : Finset (Fin d)))
      (by simp) hnear
    exact hge.trans (hexp n hn)

end Final

end Exploding

/-- **Schonmann's bootstrap bound.** -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.xsr_schonmann : Exploding.External.SchonmannBootstrap
-- FROZEN-STATEMENT-END
  :=
  xsch3_schonmann_of_percolation fun _ hd p hp hp1 => by
    haveI : Fact (0 ≤ p ∧ p ≤ 1) := ⟨⟨hp.le, hp1.le⟩⟩
    exact xsr_percolation hd hp
