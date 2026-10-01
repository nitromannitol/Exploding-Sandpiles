/-
Theorem 6.1 of the paper: explosive backgrounds without a limit shape.
-/
import Exploding.Support.Vocab
import Exploding.Support.CEProof
import Exploding.Support.CEProof2
import Exploding.External.FeyMeesterRedig
import Exploding.Support.CELow4

open Exploding LatticeProb Filter

/-- **Theorem 6.1** (`exploding.tex:1351-1361`, label
`theorem:counterexample`).

"For each dimension `d ≥ 2`, there are explosive backgrounds `η ≱ (2d-2)` on
`ℤ^d` which fail to have a limit shape; the first arrival times
`T(n) := min{t > 0 : v_t(n e_1) > 0}` do not converge,
`limsup_n n^{-1} T(n) ≥ 3/2` and `liminf_n n^{-1} T(n) = 1`."

`T(n)` is the arrival time of the exploding sandpile at `n e_1`; its finiteness
at every `n` is asserted, so that reading it as a natural number is not a junk
value.  The `limsup` and `liminf` are of a bounded sequence of reals, so the
two clauses are the paper's.

Theorem 2.8 of Fey, Meester and Redig, which the paper cites in Step 2, enters
as the explicit hypothesis `hFMR`. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.counterexample (d : ℕ) (hd : 2 ≤ d)
    (hFMR : Exploding.External.FeyMeesterRedigLeastAction) :
    ∃ η : Site d → ℤ,
      Explosive η ∧
      (¬ ∀ x : Site d, 2 * (d : ℤ) - 2 ≤ η x) ∧
      (∀ n : ℕ, arrival η ((n : ℤ) • e1 d) ≠ ⊤) ∧
      3 / 2 ≤ limsup (fun n : ℕ => ((arrival η ((n : ℤ) • e1 d)).toNat : ℝ) / (n : ℝ)) atTop ∧
      liminf (fun n : ℕ => ((arrival η ((n : ℤ) • e1 d)).toNat : ℝ) / (n : ℝ)) atTop = 1
-- FROZEN-STATEMENT-END
:= by
  -- The three front estimates of Steps 3-4 on the reflected cylinder: the slow
  -- bound `12n` at `(3+8n)e₁` (reduced to 2D by `ce_stack_le_2D`), finiteness at
  -- the low-type row-0 points `n ≡ 0, 3 (mod 4)` (the high-type points are
  -- reached by `aux_ce_row0_lands`), and an eventual linear upper bound on `T(n)`,
  -- which makes the `sInf` defining `Filter.limsup` nonempty.
  obtain ⟨hSlow2D, hLow, hBdd⟩ :
      (∀ n : ℕ, ∃ m : ℕ,
        arrival (ceEta 2) (((3 + 8 * n : ℕ) : ℤ) • e1 2) = (m : ℕ∞) ∧ 12 * n ≤ m) ∧
      (∀ n : ℕ, n % 4 = 0 ∨ n % 4 = 3 →
        arrival (ceEta d) ((n : ℤ) • e1 d) ≠ ⊤) ∧
      (∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
        ((arrival (ceEta d) ((n : ℤ) • e1 d)).toNat : ℝ) / (n : ℝ) ≤ C) :=
    ⟨by sorry, Exploding.cel_low d hd, Exploding.cel_bdd d hd⟩
  have hFin : ∀ n : ℕ, arrival (ceEta d) ((n : ℤ) • e1 d) ≠ ⊤ :=
    ce_arrival_finite_of_low d hd hLow
  refine ⟨ceEta d, ce_explosive d hd, ce_not_ge d hd, hFin, ?_, ?_⟩
  · exact ce_limsup d hd (ce_slow d hd hSlow2D hFin) hBdd
  · exact ce_liminf d hd hFin
