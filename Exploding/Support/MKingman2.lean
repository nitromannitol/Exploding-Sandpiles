/-
Follow-up to `MKingman.lean`: the first-return (induced) map used by the
paper's repair of the moment-free Kingman theorem (Proposition 5.1 and
Proposition 3.1).  Mathlib has conservativity and Poincaré recurrence
(`MeasureTheory.Conservative`) but no induced transformation or Kac lemma, so
this file builds the parts of the induced system that are needed.

The general statement `mk_kingman_linear` of `MKingman.lean` is too strong as
written: the a.s. linear bound `g n ≤ C n + K(ω)` bounds `g` at a point, but the
paper's transfer from convergence along the return times `r_j` to convergence
along every `n` additionally uses the second bound of `eq:generalized_lipschitz`
(a Lipschitz transfer).  This file supplies the induced-map
infrastructure on which that route rests, including the induced cocycle.
-/
import Exploding.Support.MKingman
import Mathlib.Dynamics.Ergodic.Conservative

open Exploding LatticeProb MeasureTheory Filter ProbabilityTheory

namespace Exploding

variable {Ω : Type}

/-- The first return time of `x` to `A` under `T`, `0` if it never returns. -/
noncomputable def mk2_returnTime (T : Ω → Ω) (A : Set Ω) (x : Ω) : ℕ :=
  sInf {n : ℕ | 1 ≤ n ∧ T^[n] x ∈ A}

/-- The induced (first-return) map on `A`. -/
noncomputable def mk2_inducedMap (T : Ω → Ω) (A : Set Ω) (x : Ω) : Ω :=
  T^[mk2_returnTime T A x] x

/-- If `x` returns to `A`, the defined return time is at least `1`. -/
theorem mk2_returnTime_pos (T : Ω → Ω) (A : Set Ω) (x : Ω)
    (h : ∃ n : ℕ, 1 ≤ n ∧ T^[n] x ∈ A) : 1 ≤ mk2_returnTime T A x :=
  (Nat.sInf_mem h).1

/-- If `x` returns to `A`, the induced map lands in `A`. -/
theorem mk2_inducedMap_mem (T : Ω → Ω) (A : Set Ω) (x : Ω)
    (h : ∃ n : ℕ, 1 ≤ n ∧ T^[n] x ∈ A) : mk2_inducedMap T A x ∈ A :=
  (Nat.sInf_mem h).2

/-- **Poincaré recurrence** for the return time: almost every point of a
measurable set `A` returns to `A` after a positive number of steps. -/
theorem mk2_ae_return [MeasurableSpace Ω] (μ : Measure Ω) (T : Ω → Ω)
    (hf : Conservative T μ) (A : Set Ω) (hA : NullMeasurableSet A μ) :
    ∀ᵐ x ∂μ, x ∈ A → ∃ n : ℕ, 1 ≤ n ∧ T^[n] x ∈ A := by
  filter_upwards [hf.ae_mem_imp_frequently_image_mem hA] with x hx hxA
  obtain ⟨n, hAn, hn1⟩ := ((hx hxA).and_eventually (eventually_ge_atTop 1)).exists
  exact ⟨n, hn1, hAn⟩

/-- The two orders of iterating `T` agree. -/
theorem mk2_iterate_comm (T : Ω → Ω) (m n : ℕ) (x : Ω) :
    T^[m] (T^[n] x) = T^[n] (T^[m] x) := by
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.add_comm]

/-- The cumulative return time: the position along the `T`-orbit after `k`
returns to `A`. -/
noncomputable def mk2_returnSeq (T : Ω → Ω) (A : Set Ω) (x : Ω) : ℕ → ℕ
  | 0 => 0
  | k + 1 => mk2_returnSeq T A x k + mk2_returnTime T A ((mk2_inducedMap T A)^[k] x)

/-- The `k`-fold induced iterate is the `T`-iterate by the cumulative return
time, so the cumulative return sequence really counts orbit positions. -/
theorem mk2_inducedMap_iterate (T : Ω → Ω) (A : Set Ω) (x : Ω) (k : ℕ) :
    (mk2_inducedMap T A)^[k] x = T^[mk2_returnSeq T A x k] x := by
  induction k with
  | zero => simp [mk2_returnSeq]
  | succ k ih =>
    calc (mk2_inducedMap T A)^[k + 1] x
        = mk2_inducedMap T A ((mk2_inducedMap T A)^[k] x) :=
          Function.iterate_succ_apply' _ _ _
      _ = mk2_inducedMap T A (T^[mk2_returnSeq T A x k] x) := by rw [ih]
      _ = T^[mk2_returnTime T A (T^[mk2_returnSeq T A x k] x)]
            (T^[mk2_returnSeq T A x k] x) := rfl
      _ = T^[mk2_returnSeq T A x k
              + mk2_returnTime T A (T^[mk2_returnSeq T A x k] x)] x := by
          rw [← Function.iterate_add_apply, Nat.add_comm]
      _ = T^[mk2_returnSeq T A x (k + 1)] x := by
          rw [mk2_returnSeq, ih]

/-- The cumulative return sequence is additive along the induced orbit. -/
theorem mk2_returnSeq_add (T : Ω → Ω) (A : Set Ω) (x : Ω) (j k : ℕ) :
    mk2_returnSeq T A x (j + k)
      = mk2_returnSeq T A x j + mk2_returnSeq T A ((mk2_inducedMap T A)^[j] x) k := by
  induction k with
  | zero => simp [mk2_returnSeq]
  | succ k ih =>
    calc mk2_returnSeq T A x (j + (k + 1))
        = mk2_returnSeq T A x (j + k)
            + mk2_returnTime T A ((mk2_inducedMap T A)^[j + k] x) := by
          rw [Nat.add_succ, mk2_returnSeq]
      _ = (mk2_returnSeq T A x j + mk2_returnSeq T A ((mk2_inducedMap T A)^[j] x) k)
            + mk2_returnTime T A ((mk2_inducedMap T A)^[j + k] x) := by rw [ih]
      _ = mk2_returnSeq T A x j
            + (mk2_returnSeq T A ((mk2_inducedMap T A)^[j] x) k
                + mk2_returnTime T A ((mk2_inducedMap T A)^[j + k] x)) := by
          exact Nat.add_assoc _ _ _
      _ = mk2_returnSeq T A x j
            + (mk2_returnSeq T A ((mk2_inducedMap T A)^[j] x) k
                + mk2_returnTime T A ((mk2_inducedMap T A)^[k]
                    ((mk2_inducedMap T A)^[j] x))) := by
          rw [Function.iterate_add_apply, mk2_iterate_comm]
      _ = mk2_returnSeq T A x j
            + mk2_returnSeq T A ((mk2_inducedMap T A)^[j] x) (k + 1) := by
          rw [mk2_returnSeq]

/-- The induced cocycle `G k y = g (r_k y) y` is subadditive along the induced
map whenever `g` is subadditive along `T`. -/
theorem mk2_return_cocycle_subadditive (T : Ω → Ω) (A : Set Ω) (g : ℕ → Ω → ℝ)
    (hsub : ∀ m n x, g (m + n) x ≤ g m x + g n (T^[m] x)) (x : Ω) (j k : ℕ) :
    g (mk2_returnSeq T A x (j + k)) x
      ≤ g (mk2_returnSeq T A x j) x
        + g (mk2_returnSeq T A ((mk2_inducedMap T A)^[j] x) k)
            ((mk2_inducedMap T A)^[j] x) := by
  rw [mk2_returnSeq_add, mk2_inducedMap_iterate]
  exact hsub _ _ _

end Exploding
