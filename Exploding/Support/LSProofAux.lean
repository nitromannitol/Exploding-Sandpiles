/-
Theorem 1.2 of the paper: the support of the exploding sandpile, rescaled by
time, converges in measure to a convex domain.

The paper gives NO proof of this theorem.  It is stated at exploding.tex:246-254,
immediately followed (255-257) by "In fact, we prove something stronger. Not
only does the support of the explosion converge, but the rate at which the
explosion spreads also converges" -- i.e. Theorem 1.3
(`theorem:convergence_of_time_constant`) is presented as the stronger statement
from which Theorem 1.2 should follow, but the derivation ("locally uniform
convergence of rescaled arrival times to a homogeneous convex gauge implies
convergence in measure of the corresponding super-level sets") is never written
down.  This file reconstructs that standard real-analysis argument and proves it,
culminating in `ls_assemble`.

The key geometric fact needed to make sense of `|{v̄_t > 0} △ B(p)| → 0` at all
(a symmetric-difference measure tending to a REAL number `0`, so in
particular eventually finite) is that `B(p) := {y | N y < 1}` is BOUNDED.
Boundedness is not asserted by the paper but is true and provable: arrival
times can only grow at Manhattan speed 1 (firing moves chips one step per
unit time), so `T_η(x) ≥ |x|_1` always, hence `N(y) ≥ ‖y‖₁` for the limit `N`,
which forces `{N < 1}` into the Manhattan unit ball.
-/
import Exploding.Support.Vocab
import Exploding.Frozen.TimeConstant
import Exploding.Frozen.Explosive
import Exploding.External.FeyLevinePeres
import Exploding.External.LiggettSchonmannStaceyBoundedDegree
import Exploding.External.MathieuHoles
import Exploding.External.AntalPisztora
import Exploding.External.Schonmann

open Exploding LatticeProb MeasureTheory Filter
open scoped symmDiff

namespace Exploding.LSProof

variable {d : ℕ}

/-- Step 1 (elementary; a short induction on `t`): the
parallel-toppling odometer for any initial sandpile `s₀` can only become
positive at `x` after at least `|x|₁` (Manhattan distance from the origin of
firing; here the origin of firing is `0` since `s₀ - η` is supported at `0`)
time steps, because each step of `(1.1)` only lets a site fire using
information from its immediate neighbours.  Stated for `podo (explodingPile
η)`, the object `arrival` is built from.

The statement needs a hypothesis on `η`: without one it is FALSE.
Counterexample: `d = 1`, `η ≡ 2`; then `explodingPile η x = η x = 2` at every
`x ≠ 0` (since `dirac 0 x = 0` there), and `2 * 1 - 1 = 1 < 2 = η x`, so `η`
already meets the firing threshold `2d` on its own, so `podo (explodingPile η) 1 x > 0`
at `x` with `mnorm x = 2 > 1 = t`.  The hypothesis, as in every other use of this
speed bound in the repository (e.g. `ceEta`'s `aux_ceEta_bounds` in
`Exploding/Support/SubRelay.lean`), is the standing assumption that `η` alone is
stable off the origin: `η ≤ 2d - 1` everywhere, so firing can only ever be
triggered by a chain of neighbours ultimately traced back to the extra chips
`explodingPile η - η` at `0`. -/
theorem ls_speed_bound_tri_add (a b : ℤ) : |a + b| ≤ |a| + |b| := by
  calc
    |a + b| = |a - (-b)| := by ring
    _ ≤ |a| + |-b| := abs_sub _ _
    _ = |a| + |b| := by simp

theorem ls_speed_bound_add (x : Site d) (i : Fin d) : mnorm x ≤ mnorm (x + unit i) + 1 := by
  simp only [mnorm]
  calc
    (∑ j : Fin d, |x j|) = (∑ j : Fin d, |(x + unit i) j - (unit i) j|) := by simp
    _ ≤ (∑ j : Fin d, (|(x + unit i) j| + |(unit i) j|)) :=
      Finset.sum_le_sum fun j _ => abs_sub _ _
    _ = (∑ j : Fin d, |(x + unit i) j|) + (∑ j : Fin d, |(unit i) j|) :=
      Finset.sum_add_distrib
    _ = (∑ j : Fin d, |(x + unit i) j|) + 1 := by
      have h_unit_sum : (∑ j : Fin d, |(unit i : Site d) j|) = 1 := by
        simp only [unit, Pi.single_apply]
        calc
          (∑ j : Fin d, |(if j = i then (1 : ℤ) else 0)|) = (∑ j : Fin d, if j = i then (1 : ℤ) else 0) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            split_ifs with h
            · simp
            · simp
          _ = 1 := by simp
      simp [h_unit_sum]

theorem ls_speed_bound_sub (x : Site d) (i : Fin d) : mnorm x ≤ mnorm (x - unit i) + 1 := by
  simp only [mnorm]
  calc
    (∑ j : Fin d, |x j|) = (∑ j : Fin d, |(x - unit i) j + (unit i) j|) := by simp
    _ ≤ (∑ j : Fin d, (|(x - unit i) j| + |(unit i) j|)) :=
      Finset.sum_le_sum fun j _ => ls_speed_bound_tri_add _ _
    _ = (∑ j : Fin d, |(x - unit i) j|) + (∑ j : Fin d, |(unit i) j|) :=
      Finset.sum_add_distrib
    _ = (∑ j : Fin d, |(x - unit i) j|) + 1 := by
      have h_unit_sum : (∑ j : Fin d, |(unit i : Site d) j|) = 1 := by
        simp only [unit, Pi.single_apply]
        calc
          (∑ j : Fin d, |(if j = i then (1 : ℤ) else 0)|) = (∑ j : Fin d, if j = i then (1 : ℤ) else 0) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            split_ifs with h
            · simp
            · simp
          _ = 1 := by simp
      simp [h_unit_sum]

theorem ls_speed_bound (η : Site d → ℤ) (hη : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (t : ℕ) (x : Site d) :
    0 < podo (explodingPile η) t x → mnorm x ≤ (t : ℤ) := by
  induction' t with t ih generalizing x
  · intro h
    simp [podo_zero] at h
  · intro h
    rw [podo_succ, pconf] at h
    split_ifs at h with hfire
    · by_cases hpt : 0 < podo (explodingPile η) t x
      · have hm := ih x hpt
        omega
      · have hzero : podo (explodingPile η) t x = 0 := by omega
        by_cases hx0 : x = 0
        · subst hx0; simp [mnorm]; omega
        · have hx_ne_0 : x ≠ 0 := hx0
          have h_exploding_val : (explodingPile η) x = η x := by
            simp [explodingPile, hx_ne_0, dirac]
          rw [h_exploding_val] at hfire
          have h_eta_le : η x ≤ 2 * (d : ℤ) - 1 := hη x
          have h_lap_eq : lap (podo (explodingPile η) t) x =
              nbrSumZ (podo (explodingPile η) t) x := by
            dsimp [lap]
            rw [hzero, mul_zero, sub_zero]
          have h_lap_pos : 0 < lap (podo (explodingPile η) t) x := by
            rw [h_lap_eq]
            have : 2 * (d : ℤ) ≤ η x + nbrSumZ (podo (explodingPile η) t) x := by
              rw [← h_lap_eq]; exact hfire
            have h_eta_le : η x ≤ 2 * (d : ℤ) - 1 := hη x
            omega
          have h_nbr_pos : 0 < nbrSumZ (podo (explodingPile η) t) x := by
            rw [← h_lap_eq]; exact h_lap_pos
          have h_exists_nbr : ∃ (y : Site d), (lattice d).Adj x y ∧
              0 < podo (explodingPile η) t y := by
            dsimp [nbrSumZ] at h_nbr_pos
            have hpos_sum : ∃ i, 0 < podo (explodingPile η) t (x + unit i) +
                podo (explodingPile η) t (x - unit i) := by
              by_contra! h_all
              have h_sum_nonpos : nbrSumZ (podo (explodingPile η) t) x ≤ 0 := by
                dsimp [nbrSumZ]
                refine Finset.sum_nonpos fun i _ => ?_
                have hi := h_all i
                omega
              omega
            rcases hpos_sum with ⟨i, hpos_sum'⟩
            by_cases hpos : 0 < podo (explodingPile η) t (x + unit i)
            · have hadj : (lattice d).Adj x (x + unit i) := by
                refine ⟨i, Or.inl ?_⟩
                rfl
              exact ⟨x + unit i, hadj, hpos⟩
            · have hpos' : 0 < podo (explodingPile η) t (x - unit i) := by omega
              have hadj : (lattice d).Adj x (x - unit i) := by
                refine ⟨i, Or.inr ?_⟩
                abel
              exact ⟨x - unit i, hadj, hpos'⟩
          rcases h_exists_nbr with ⟨y, hadj, hpos_y⟩
          have hm_y := ih y hpos_y
          rcases hadj with ⟨i, hy | hy⟩
          · rw [hy] at hm_y
            have h_bound := ls_speed_bound_add x i
            omega
          · -- hy : x = y + unit i, so y = x - unit i
            have hy_eq : y = x - unit i := by
              calc
                y = (y + unit i) - unit i := by abel
                _ = x - unit i := by rw [← hy]
            rw [hy_eq] at hm_y
            have h_bound := ls_speed_bound_sub x i
            omega
    · have hpos : 0 < podo (explodingPile η) t x := by omega
      have hm := ih x hpos
      omega

/-- Step 2 (assembly of Step 1 into a bound on `arrival`, immediate once
Step 1 is granted: the least `t` with `podo (explodingPile η) t x > 0` is at
least `mnorm x`). -/
theorem ls_arrival_attained (η : Site d → ℤ) (x : Site d) (m : ℕ)
    (heq : arrival η x = (m : ℕ∞)) : 0 < podo (explodingPile η) m x := by
  classical
  have hS : arrival η x = sInf {t : ℕ∞ | ∃ n : ℕ, t = (n : ℕ∞) ∧ 1 ≤ n ∧ 0 < podo (explodingPile η) n x} := rfl
  have hne : ∃ n : ℕ, 1 ≤ n ∧ 0 < podo (explodingPile η) n x := by
    by_contra h
    have hset : {t : ℕ∞ | ∃ n : ℕ, t = (n : ℕ∞) ∧ 1 ≤ n ∧ 0 < podo (explodingPile η) n x} = ∅ := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨n, -, hn1, hpos⟩
      exact h ⟨n, hn1, hpos⟩
    have htop : arrival η x = ⊤ := by rw [hS, hset, sInf_empty]
    rw [htop] at heq
    exact ENat.coe_ne_top m heq.symm
  have harr : arrival η x = (Nat.find hne : ℕ∞) := by
    rw [hS]
    refine le_antisymm (sInf_le ⟨Nat.find hne, rfl, (Nat.find_spec hne).1, (Nat.find_spec hne).2⟩) ?_
    refine le_sInf ?_
    rintro t ⟨n, rfl, hn1, hnP⟩
    exact_mod_cast Nat.find_min' hne ⟨hn1, hnP⟩
  have hm : m = Nat.find hne := ENat.coe_inj.mp (heq.symm.trans harr)
  rw [hm]
  exact (Nat.find_spec hne).2

theorem ls_arrival_speed_bound (η : Site d → ℤ) (hη : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (x : Site d) (m : ℕ)
    (heq : arrival η x = (m : ℕ∞)) : mnorm x ≤ (m : ℤ) := by
  exact ls_speed_bound η hη m x (ls_arrival_attained η x m heq)


theorem ls_podo_nonneg (s0 : Site d → ℤ) (t : ℕ) (x : Site d) : 0 ≤ podo s0 t x := by
  induction t with
  | zero => simp
  | succ t ih => rw [podo_succ]; split <;> omega

theorem ls_podo_mono (s0 : Site d → ℤ) (x : Site d) : Monotone (fun t => podo s0 t x) :=
  monotone_nat_of_le_succ fun t => podo_mono_step s0 t x

theorem ls_arrival_le (η : Site d → ℤ) (x : Site d) (n : ℕ) (hn : 1 ≤ n)
    (h : 0 < podo (explodingPile η) n x) : arrival η x ≤ (n : ℕ∞) := by
  rw [show arrival η x = sInf {t : ℕ∞ | ∃ k : ℕ, t = (k : ℕ∞) ∧ 1 ≤ k ∧
      0 < podo (explodingPile η) k x} from rfl]
  exact sInf_le ⟨n, rfl, hn, h⟩

theorem ls_toNat_le_of_podo_pos (η : Site d → ℤ) (x : Site d) (n : ℕ) (hn : 1 ≤ n)
    (h : 0 < podo (explodingPile η) n x) : (arrival η x).toNat ≤ n :=
  ENat.toNat_le_of_le_coe (ls_arrival_le η x n hn h)

theorem ls_toNat_lt_of_podo_zero (η : Site d → ℤ) (x : Site d) (n : ℕ)
    (hexp : arrival η x ≠ ⊤) (h : podo (explodingPile η) n x = 0) :
    n < (arrival η x).toNat := by
  by_contra hlt
  push Not at hlt
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hexp
  have hpos := ls_arrival_attained η x m hm.symm
  have hmt : (arrival η x).toNat = m := by rw [← hm]; exact ENat.toNat_coe m
  rw [hmt] at hlt
  have hmono := ls_podo_mono (explodingPile η) x hlt
  change podo (explodingPile η) m x ≤ podo (explodingPile η) n x at hmono
  rw [h] at hmono
  omega

theorem ls_toNat_div_le_one_of_podo_pos (η : Site d → ℤ) (x : Site d) (t : ℕ) (ht : 1 ≤ t)
    (h : 0 < podo (explodingPile η) t x) :
    ((arrival η x).toNat : ℝ) / (t : ℝ) ≤ 1 := by
  have htR : (0 : ℝ) < t := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ht)
  rw [div_le_one htR]
  exact_mod_cast ls_toNat_le_of_podo_pos η x t ht h

theorem ls_one_lt_toNat_div_of_podo_zero (η : Site d → ℤ) (x : Site d) (t : ℕ) (ht : 1 ≤ t)
    (hexp : arrival η x ≠ ⊤) (h : podo (explodingPile η) t x = 0) :
    1 < ((arrival η x).toNat : ℝ) / (t : ℝ) := by
  have htR : (0 : ℝ) < t := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ht)
  rw [one_lt_div htR]
  exact_mod_cast ls_toNat_lt_of_podo_zero η x t hexp h

/-- The geometric half of the finite-speed bound: `t · ‖y‖₁` exceeds the
Manhattan norm of the nearest lattice point by at most `d` (each coordinate
rounds off by at most `1`). -/
theorem ls_smul_mnorm_sum_le (y : Fin d → ℝ) (t : ℕ) :
    (t : ℝ) * (∑ i, |y i|) ≤ (mnorm (nearestSite ((t : ℝ) • y)) : ℝ) + (d : ℝ) := by
  set x : Site d := nearestSite ((t : ℝ) • y) with hx
  have hterm : ∀ i : Fin d, (t : ℝ) * |y i| ≤ (|(x i : ℤ)| : ℝ) + 1 := by
    intro i
    have h := Gen.nearestSite_sub_le ((t : ℝ) • y) i
    have h3 : |(t : ℝ) * y i - ((nearestSite ((t : ℝ) • y)) i : ℝ)| ≤ 1 := by
      rw [abs_sub_comm]
      simpa [Pi.smul_apply, smul_eq_mul] using h
    have hx_eq : ((nearestSite ((t : ℝ) • y)) i : ℝ) = (x i : ℝ) := by rw [← hx]
    rw [hx_eq] at h3
    have ht_abs : |(t : ℝ)| = (t : ℝ) := abs_of_nonneg (Nat.cast_nonneg t)
    calc (t : ℝ) * |y i| = |(t : ℝ)| * |y i| := by rw [ht_abs]
      _ = |(t : ℝ) * y i| := by rw [abs_mul]
      _ = |((t : ℝ) * y i - (x i : ℝ)) + (x i : ℝ)| := by ring_nf
      _ ≤ |(t : ℝ) * y i - (x i : ℝ)| + |(x i : ℝ)| := abs_add_le _ _
      _ ≤ 1 + |(x i : ℝ)| := by linarith
      _ = (|(x i : ℤ)| : ℝ) + 1 := by ring
  calc (t : ℝ) * (∑ i, |y i|) = ∑ i, (t : ℝ) * |y i| := by rw [Finset.mul_sum]
    _ ≤ ∑ i, ((|(x i : ℤ)| : ℝ) + 1) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = (∑ i, (|(x i : ℤ)| : ℝ)) + (d : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp
    _ = (mnorm x : ℝ) + (d : ℝ) := by
        congr 1
        simp only [mnorm, Int.cast_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Int.cast_abs]

/-- Step 3: passing Step 2's bound to the limit `n → ∞` along `nearestSite
(n • y)` gives the homogeneous limit function `N` of `thm-time-constant` a
linear-growth lower bound `‖y‖₁ ≤ N y`.  (The statement carries the standing
stability bound on `η` and finiteness of all arrival times, both available at
the call site from `thm-time-constant`.) -/
theorem ls_N_lower_bound (η : Site d → ℤ) (N : (Fin d → ℝ) → ℝ)
    (hη : ∀ x : Site d, η x ≤ 2 * (d : ℤ) - 1)
    (hexp : ∀ x : Site d, arrival η x ≠ ⊤)
    (hloc : ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
        |((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
          - N y| ≤ ε)
    (y : Fin d → ℝ) : ∑ i, |y i| ≤ N y := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (hloc {y} isCompact_singleton (ε / 2) (by linarith))
  obtain ⟨n, hn_big⟩ := exists_nat_gt (max (N0 : ℝ) (2 * (d : ℝ) / ε) + 1)
  have hn_ge : N0 ≤ n := by
    have h1 : (N0 : ℝ) < n :=
      lt_of_le_of_lt (le_trans (le_max_left _ _) (le_add_of_nonneg_right zero_le_one)) hn_big
    exact_mod_cast le_of_lt h1
  have hn_big' : (d : ℝ) < (ε / 2) * (n : ℝ) := by
    have h1 : 2 * (d : ℝ) / ε < (n : ℝ) :=
      lt_of_le_of_lt (le_trans (le_max_right _ _) (le_add_of_nonneg_right zero_le_one)) hn_big
    rw [div_lt_iff₀ hε] at h1
    nlinarith
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    rw [hn0] at hn_big'
    simp at hn_big'
    exact not_lt_of_ge (Nat.cast_nonneg d) hn_big'
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hf := hN0 n hn_ge y (Set.mem_singleton y)
  have hf_le : ((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ) ≤ N y + ε / 2 := by
    have := (abs_le.mp hf).2; linarith
  have hspeed : (mnorm (nearestSite ((n : ℝ) • y)) : ℝ)
      ≤ ((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ) := by
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (hexp _)
    have h := ls_arrival_speed_bound η hη (nearestSite ((n : ℝ) • y)) m hm.symm
    have hmt : ((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ) = (m : ℝ) := by
      rw [← hm]; simp
    rw [hmt]
    exact_mod_cast h
  have hchain : (n : ℝ) * (∑ i, |y i|)
      ≤ ((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ) + (d : ℝ) := by
    have hg := ls_smul_mnorm_sum_le y n
    linarith
  have hdiv : (∑ i, |y i|)
      ≤ (((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ) + (d : ℝ)) / (n : ℝ) := by
    rw [le_div_iff₀ hnR]
    linarith
  have hdn : (d : ℝ) / (n : ℝ) < ε / 2 := by
    rw [div_lt_iff₀ hnR]
    nlinarith
  have hfin : (((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ) + (d : ℝ)) / (n : ℝ)
      ≤ N y + ε := by
    rw [add_div]
    linarith
  linarith

/-- Step 4 (`Convex.addHaar_frontier` in Mathlib, `Mathlib/Analysis/Convex/
Measure.lean` -- NOT a gap, directly applicable): a bounded convex set has a
Lebesgue-null frontier.  Combined with Step 3 (`{y | N y < 1}` is contained
in the Manhattan unit ball, hence bounded) and convexity/continuity of `N`
(from `thm-time-constant`), `B := {y | N y < 1}` is a bounded, open, convex,
nonempty (since `N 0 = 0 < 1` by `0`-homogeneity) set with `volume (frontier
B) = 0`. -/
theorem ls_N_zero (d : ℕ) (N : (Fin d → ℝ) → ℝ)
    (hhom : ∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) : N 0 = 0 := by
  simpa [zero_smul, zero_mul] using hhom 0 le_rfl (0 : Fin d → ℝ)

theorem ls_B_domain (N : (Fin d → ℝ) → ℝ) (hcont : Continuous N)
    (hconv : ConvexOn ℝ Set.univ N)
    (hhom : ∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y)
    (_hlb : ∀ y : Fin d → ℝ, ∑ i, |y i| ≤ N y) :
    Convex ℝ {y : Fin d → ℝ | N y < 1} ∧ IsOpen {y : Fin d → ℝ | N y < 1} ∧
      {y : Fin d → ℝ | N y < 1}.Nonempty ∧
      volume (frontier {y : Fin d → ℝ | N y < 1}) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Set.sep_univ] using hconv.convex_lt (1 : ℝ)
  · exact isOpen_lt hcont continuous_const
  · exact ⟨0, by
      show N 0 < 1
      rw [ls_N_zero d N hhom]
      norm_num⟩
  · exact Convex.addHaar_frontier volume (by simpa only [Set.sep_univ] using hconv.convex_lt (1 : ℝ))


/-- Step 5 (the core convergence-in-measure argument, real analysis, "needs
further split" -- this is genuinely the paper's missing proof, broken into
its two halves).  Half A: for `y` with `N y < 1 - ε`, locally uniform
convergence of the rescaled arrival time to `N` eventually puts `y` in
`{v̄_t > 0}` (i.e. `arrival η (nearestSite (t•y))` is reached by time `t`).
Half B (symmetric): for `y` with `N y > 1 + ε`, eventually `y ∉ {v̄_t > 0}`.
Together, for every `ε > 0`, eventually `{v̄_t > 0} △ B ⊆ {y | 1 - ε ≤ N y ≤
1 + ε}` (a shell around the boundary), on any fixed bounded region (the
convergence is only LOCALLY uniform, so this needs restricting to a compact
set first and handling the exterior separately using Step 3's growth bound
to show the exterior symmetric difference is controlled too). -/
theorem ls_shell_inclusion (η : Site d → ℤ) (N : (Fin d → ℝ) → ℝ)
    (hexp : ∀ x : Site d, arrival η x ≠ ⊤)
    (hloc : ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℕ in atTop, ∀ y ∈ K,
        |((arrival η (nearestSite ((t : ℝ) • y))).toNat : ℝ) / (t : ℝ) - N y| ≤ ε)
    (K : Set (Fin d → ℝ)) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop,
      symmDiff ({y : Fin d → ℝ | 0 < podo (explodingPile η) t (nearestSite ((t : ℝ) • y))} ∩ K)
        ({y : Fin d → ℝ | N y < 1} ∩ K)
        ⊆ {y : Fin d → ℝ | 1 - ε ≤ N y ∧ N y ≤ 1 + ε} := by
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (hloc K hK (ε / 2) (by linarith))
  rw [eventually_atTop]
  refine ⟨max N0 1, ?_⟩
  intro t ht y hy
  have htN0 : N0 ≤ t := le_trans (le_max_left _ _) ht
  have ht1 : 1 ≤ t := le_trans (le_max_right _ _) ht
  rw [Set.mem_symmDiff] at hy
  rcases hy with ⟨hyA, hyB⟩ | ⟨hyB, hyA⟩
  · have hyK : y ∈ K := hyA.2
    have hyAnb : y ∈ {y : Fin d → ℝ | 0 < podo (explodingPile η) t (nearestSite ((t : ℝ) • y))} :=
      hyA.1
    have hnotB : y ∉ {y : Fin d → ℝ | N y < 1} := fun hB => hyB ⟨hB, hyK⟩
    have hNy_ge : 1 ≤ N y := by
      simp only [Set.mem_setOf_eq] at hnotB
      linarith
    have hf := hN0 t htN0 y hyK
    have hle1 := ls_toNat_div_le_one_of_podo_pos η _ t ht1 hyAnb
    have hfge : N y - ε / 2
        ≤ ((arrival η (nearestSite ((t : ℝ) • y))).toNat : ℝ) / (t : ℝ) := by
      have := (abs_le.mp hf).1; linarith
    exact ⟨by linarith, by linarith⟩
  · have hyK : y ∈ K := hyB.2
    have hBy : y ∈ {y : Fin d → ℝ | N y < 1} := hyB.1
    have hnotA : y ∉ {y : Fin d → ℝ | 0 < podo (explodingPile η) t (nearestSite ((t : ℝ) • y))} :=
      fun hA => hyA ⟨hA, hyK⟩
    have hNz : N y < 1 := hBy
    have hpodo0 : podo (explodingPile η) t (nearestSite ((t : ℝ) • y)) = 0 := by
      have hnn := ls_podo_nonneg (explodingPile η) t (nearestSite ((t : ℝ) • y))
      simp only [Set.mem_setOf_eq] at hnotA
      omega
    have hf := hN0 t htN0 y hyK
    have hgt1 := ls_one_lt_toNat_div_of_podo_zero η _ t ht1 (hexp _) hpodo0
    have hfle : ((arrival η (nearestSite ((t : ℝ) • y))).toNat : ℝ) / (t : ℝ)
        ≤ N y + ε / 2 := by
      have := (abs_le.mp hf).2; linarith
    exact ⟨by linarith, by linarith⟩

/-- Step 6, piece (a) (TRUE, general topology, no gap): the level set `{N=1}`
sits in the frontier of `B := {N<1}`.  Proof: `{N=1} ⊆ closure B` because
`y` with `N y = 1` is the limit as `c ↑ 1` of `c • y ∈ B` (`N (c•y) = c*N y =
c < 1` by `hhom`, and `c•y → y` by continuity of scalar multiplication); and
`{N=1} ∩ interior B = ∅` because `interior B = B` (`hBopen`) and `N y = 1`
already contradicts `N y < 1`. -/
theorem ls_levelset_subset_frontier (N : (Fin d → ℝ) → ℝ)
    (hBopen : IsOpen {y : Fin d → ℝ | N y < 1})
    (hhom : ∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) :
    {y : Fin d → ℝ | N y = 1} ⊆ frontier {y : Fin d → ℝ | N y < 1} := by
  intro y hy
  have hyN : N y = 1 := hy
  have h_not_mem : y ∉ {y | N y < 1} := by
    rw [Set.mem_setOf_eq]
    linarith
  have h_mem_closure : y ∈ closure {y | N y < 1} := by
    rw [mem_closure_iff]
    intro U hU_open hyU
    have h_cont : ContinuousAt (λ c : ℝ => c • y) 1 := by
      refine ContinuousAt.smul (f := id) (g := λ (_ : ℝ) => y) ?_ ?_
      · exact continuousAt_id
      · exact continuousAt_const
    have h_preimage_mem : (λ c : ℝ => c • y) ⁻¹' U ∈ nhds 1 :=
      h_cont.tendsto (by
        simpa [one_smul] using hU_open.mem_nhds hyU)
    rcases Metric.mem_nhds_iff.mp h_preimage_mem with ⟨ε, hε_pos, hε⟩
    set c := max 0 (1 - ε / 2) with hc_def
    have hc_nonneg : 0 ≤ c := by
      dsimp [c]
      exact le_max_left _ _
    have hc_lt_one : c < 1 := by
      dsimp [c]
      refine max_lt (by norm_num) ?_
      nlinarith
    have hc_mem_ball : c ∈ Metric.ball (1 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have hc_le_one : c ≤ 1 := by
        dsimp [c]
        refine max_le (by norm_num) ?_
        nlinarith
      have hc_ge : 1 - ε / 2 ≤ c := by
        dsimp [c]
        exact le_max_right _ _
      rw [abs_of_nonpos (sub_nonpos.mpr hc_le_one)]
      nlinarith
    have hc_smul_mem_U : c • y ∈ U := hε hc_mem_ball
    have hN_c_smul : N (c • y) = c := by
      calc
        N (c • y) = c * N y := hhom c hc_nonneg y
        _ = c * 1 := by rw [hyN]
        _ = c := by ring
    have hc_smul_mem_B : c • y ∈ {y | N y < 1} := by
      rw [Set.mem_setOf_eq, hN_c_smul]
      exact hc_lt_one
    exact ⟨c • y, hc_smul_mem_U, hc_smul_mem_B⟩
  have h_frontier : y ∈ frontier {y | N y < 1} := by
    rw [hBopen.frontier_eq, Set.mem_sdiff]
    exact ⟨h_mem_closure, h_not_mem⟩
  exact h_frontier

/-- Step 6, piece (b) (real analysis, from (a)): the shells `{1 - 1/(n+1) ≤ N
≤ 1 + 1/(n+1)}` shrink in volume to `0`.  Proof: the shells are an
antitone (in `n`) sequence of sets with `⋂ n, shell n = {N = 1}` (pure set
algebra: `y` is in every shell iff `N y = 1`, since `1/(n+1) → 0`); by
`ls_levelset_subset_frontier` and `hfrontier`, `{N=1}` is `volume`-null;
`hlb` bounds `shell 0 ⊆ {∑|y_i| ≤ 2}` (`N y ≤ 2` there), a finite-volume set,
so `MeasureTheory.tendsto_measure_iInter_atTop` (or the `Antitone` variant)
applies to conclude `volume (shell n) → volume {N=1} = 0`. -/
theorem ls_shell_volume_tendsto (N : (Fin d → ℝ) → ℝ)
    (hlb : ∀ y : Fin d → ℝ, ∑ i, |y i| ≤ N y)
    (hfrontier : volume (frontier {y : Fin d → ℝ | N y < 1}) = 0)
    (hBopen : IsOpen {y : Fin d → ℝ | N y < 1})
    (hhom : ∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) :
    Tendsto (fun n : ℕ =>
        volume {y : Fin d → ℝ | 1 - (1 / (n + 1 : ℝ)) ≤ N y ∧ N y ≤ 1 + (1 / (n + 1 : ℝ))})
      atTop (nhds 0) := by
  set shell := fun (n : ℕ) => {y : Fin d → ℝ | 1 - (1 / ((n : ℝ) + 1)) ≤ N y ∧ N y ≤ 1 + (1 / ((n : ℝ) + 1))} with hshell_def
  have hN_nonneg : ∀ y, 0 ≤ N y := by
    intro y
    have hsum_nonneg : 0 ≤ ∑ i, |y i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    have h := hlb y
    linarith
  -- For t > 0, {N < t} is open (image of {N < 1} under scaling)
  have h_open_lt : ∀ t : ℝ, 0 < t → IsOpen {y | N y < t} := by
    intro t ht
    have ht' : 0 ≤ t := le_of_lt ht
    have h_eq : {y | N y < t} = (fun y : Fin d → ℝ => t • y) '' {y | N y < 1} := by
      ext y; constructor
      · intro hy
        refine ⟨t⁻¹ • y, ?_, ?_⟩
        · rw [Set.mem_setOf_eq]
          have h := hhom t⁻¹ (by positivity) y
          -- h : N (t⁻¹ • y) = t⁻¹ * N y
          rw [h]
          -- Need: t⁻¹ * N y < 1
          have h_mul : t⁻¹ * N y < t⁻¹ * t := mul_lt_mul_of_pos_left hy (by positivity)
          have h_one : t⁻¹ * t = 1 := by field_simp [ne_of_gt ht]
          rwa [h_one] at h_mul
        · -- (t • (t⁻¹ • y)) = y
          calc
            t • (t⁻¹ • y) = (t * t⁻¹) • y := by rw [smul_smul]
            _ = 1 • y := by
              have h_mul : t * t⁻¹ = 1 := by field_simp [ne_of_gt ht]
              simp [h_mul]
            _ = y := by simp
      · rintro ⟨z, hz, rfl⟩
        have hz' : N z < 1 := hz
        have h := hhom t ht' z
        -- h : N (t • z) = t * N z
        have h_lt : N (t • z) < t := by
          rw [h]
          nlinarith
        exact h_lt
    rw [h_eq]
    exact (isOpenMap_smul₀ (ne_of_gt ht)) _ hBopen
  -- For t ≤ 0, {N < t} is empty (since N ≥ 0)
  have h_empty_lt : ∀ t : ℝ, t ≤ 0 → {y | N y < t} = ∅ := by
    intro t ht
    ext y; simpa [Set.mem_setOf_eq, Set.mem_empty_iff_false] using not_lt.mpr (le_trans ht (hN_nonneg y))
  -- Each shell is NullMeasurableSet: it's the intersection of {N ≤ b} and {a ≤ N}
  -- {a ≤ N} = {N < a}ᶜ (open or empty)
  -- {N ≤ b} = ⋂_k {N < b + 1/(k+1)} (countable intersection of open sets)
  have hmeas : ∀ n : ℕ, NullMeasurableSet (shell n) volume := by
    intro n
    set a := 1 - (1 / ((n : ℝ) + 1)) with ha_def
    set b := 1 + (1 / ((n : ℝ) + 1)) with hb_def
    have ha_nonneg : 0 ≤ a := by
      rw [ha_def]
      have : 0 < (n : ℝ) + 1 := by positivity
      have hdiv : 1 / ((n : ℝ) + 1) ≤ 1 := by
        refine (div_le_one ?_).mpr ?_
        · positivity
        · have : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
          linarith
      linarith
    have hb_pos : 0 < b := by
      rw [hb_def]
      have : 0 < 1 / ((n : ℝ) + 1) := div_pos (by norm_num) (by exact_mod_cast (Nat.zero_lt_succ n))
      linarith
    -- shell n = {N ≤ b} ∩ {a ≤ N}
    have h_shell_eq : shell n = {y | N y ≤ b} ∩ {y | a ≤ N y} := by
      rw [hshell_def, ha_def, hb_def]
      ext y; simp; tauto
    rw [h_shell_eq]
    -- {a ≤ N} = {N < a}ᶜ
    have h_left : NullMeasurableSet {y | a ≤ N y} volume := by
      have h_eq : {y | a ≤ N y} = {y | N y < a}ᶜ := by
        ext y; simp
      rw [h_eq]
      by_cases ha_zero : a ≤ 0
      · have h_empty : {y | N y < a} = ∅ := h_empty_lt _ ha_zero
        rw [h_empty, Set.compl_empty]
        exact MeasurableSet.univ.nullMeasurableSet
      · have ha_pos' : 0 < a := by linarith
        exact (h_open_lt a ha_pos').isClosed_compl.nullMeasurableSet
    -- {N ≤ b} = ⋂_k {N < b + 1/(k+1)}
    have h_right : NullMeasurableSet {y | N y ≤ b} volume := by
      have h_eq : {y | N y ≤ b} = ⋂ i : ℕ, {y | N y < b + (1 / ((i : ℝ) + 1))} := by
        ext y; simp only [Set.mem_iInter, Set.mem_setOf_eq]
        constructor
        · intro hy i
          have hy' : N y ≤ b := hy
          have hpos : 0 < 1 / ((i : ℝ) + 1) :=
            div_pos (by norm_num) (by exact_mod_cast (Nat.zero_lt_succ i))
          have hlt : b < b + (1 / ((i : ℝ) + 1)) := by linarith
          linarith
        · intro hy
          have hy' : ∀ i : ℕ, N y < b + (1 / ((i : ℝ) + 1)) := hy
          by_contra! hgt
          have hgt' : b < N y := by simpa [Set.mem_setOf_eq] using hgt
          have hpos_diff : 0 < N y - b := sub_pos.mpr hgt'
          rcases exists_nat_one_div_lt hpos_diff with ⟨i, hi⟩
          have hi' : N y < b + (1 / ((i : ℝ) + 1)) := hy' i
          linarith
      rw [h_eq]
      refine NullMeasurableSet.iInter (fun i => ?_)
      have hi_pos : 0 < b + (1 / ((i : ℝ) + 1)) := by
        have : 0 < 1 / ((i : ℝ) + 1) := div_pos (by norm_num) (by exact_mod_cast (Nat.zero_lt_succ i))
        positivity
      exact (h_open_lt _ hi_pos).nullMeasurableSet
    exact h_right.inter h_left
  -- The shells form an antitone sequence
  have h_anti : Antitone shell := by
    intro m n hmn y hy
    rcases hy with ⟨hlo, hhi⟩
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have h_div : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      refine (one_div_le_one_div (by positivity) (by positivity)).mpr ?_
      linarith
    have h_lo : 1 - (1 / ((m : ℝ) + 1)) ≤ 1 - (1 / ((n : ℝ) + 1)) := by linarith
    have h_hi : 1 + (1 / ((n : ℝ) + 1)) ≤ 1 + (1 / ((m : ℝ) + 1)) := by linarith
    exact ⟨le_trans h_lo hlo, le_trans hhi h_hi⟩
  -- The intersection of all shells is {N = 1}
  have h_inter : ⋂ n : ℕ, shell n = {y | N y = 1} := by
    ext y; constructor
    · intro h
      have hmem : ∀ n : ℕ, y ∈ shell n := fun n => Set.mem_iInter.1 h n
      have hle : ∀ n : ℕ, 1 - (1 / ((n : ℝ) + 1)) ≤ N y := fun n => (hmem n).1
      have hge : ∀ n : ℕ, N y ≤ 1 + (1 / ((n : ℝ) + 1)) := fun n => (hmem n).2
      have hNle1 : N y ≤ 1 := by
        by_contra! hgt
        have : N y - 1 > 0 := sub_pos.mpr hgt
        rcases exists_nat_one_div_lt this with ⟨n, hn⟩
        have h := hge n
        linarith
      have hNge1 : 1 ≤ N y := by
        by_contra! hlt
        have : 1 - N y > 0 := sub_pos.mpr hlt
        rcases exists_nat_one_div_lt this with ⟨n, hn⟩
        have h := hle n
        linarith
      exact le_antisymm hNle1 hNge1
    · intro hy
      have hyN : N y = 1 := hy
      refine Set.mem_iInter.mpr ?_
      intro n
      rw [hshell_def, Set.mem_setOf_eq]
      have hpos_div : 0 ≤ 1 / ((n : ℝ) + 1) := div_nonneg (by norm_num) (by positivity)
      constructor
      · rw [hyN]; linarith
      · rw [hyN]; linarith
  -- shell 0 has finite measure: shell 0 ⊆ Metric.closedBall 0 2
  -- With the product norm on Fin d → ℝ, Metric.closedBall 0 2 = {y | ∀ i, |y i| ≤ 2}
  have h_fin : ∃ n : ℕ, volume (shell n) ≠ (⊤ : ENNReal) := by
    refine ⟨0, ?_⟩
    have h_sub : shell 0 ⊆ Metric.closedBall (0 : Fin d → ℝ) 2 := by
      intro y hy
      rw [hshell_def, Set.mem_setOf_eq] at hy
      rcases hy with ⟨hlo, hhi⟩
      have hsum : ∑ i, |y i| ≤ N y := hlb y
      have hsum2 : ∑ i, |y i| ≤ 2 := by linarith
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      have h_each : ∀ i, |y i| ≤ 2 := by
        intro i
        have h := Finset.single_le_sum (fun j _ => abs_nonneg (y j)) (Finset.mem_univ i)
        linarith
      have h_norm_le : ‖y‖ ≤ 2 := by
        have h2 : 0 ≤ (2 : ℝ) := by norm_num
        rw [pi_norm_le_iff_of_nonneg h2]
        intro i
        simpa [Real.norm_eq_abs] using h_each i
      exact h_norm_le
    have h_fin_ball : volume (Metric.closedBall (0 : Fin d → ℝ) 2) < (⊤ : ENNReal) :=
      measure_closedBall_lt_top (x := (0 : Fin d → ℝ)) (r := 2)
    refine ne_of_lt (lt_of_le_of_lt (measure_mono h_sub) h_fin_ball)
  -- volume {N = 1} = 0
  have h_vol_zero : volume {y | N y = 1} = 0 := by
    have h_sub : {y | N y = 1} ⊆ frontier {y | N y < 1} := ls_levelset_subset_frontier N hBopen hhom
    have h_vol_frontier : volume (frontier {y | N y < 1}) = 0 := hfrontier
    have h_le : volume {y | N y = 1} ≤ 0 := by
      calc
        volume {y | N y = 1} ≤ volume (frontier {y | N y < 1}) := measure_mono (μ := volume) h_sub
        _ = 0 := h_vol_frontier
    have h_ge : 0 ≤ volume {y | N y = 1} := by
      apply zero_le
    exact le_antisymm h_le h_ge
  -- Apply tendsto_measure_iInter_atTop
  have h_tendsto := tendsto_measure_iInter_atTop hmeas h_anti h_fin
  rw [h_inter, h_vol_zero] at h_tendsto
  convert h_tendsto using 1
  ext n
  simp [hshell_def]

/-- Step 6, piece (c) (finite propagation speed, from `ls_speed_bound`):
for any fixed `R > 1`, eventually (in `t`) the rescaled support `{v̄_t > 0}` is
confined to the `ℓ¹` ball of radius `R`.  (`R = 1` is not claimed: the speed
bound only gives `∑|y_i| ≤ 1 + d/t`.)  Proof: `ls_speed_bound hη t
(nearestSite (t•y))` gives `mnorm (nearestSite (t•y)) ≤ t` whenever `v̄_t(y) >
0`; `ls_smul_mnorm_sum_le` gives `t * ∑|y_i| ≤ mnorm (nearestSite (t•y)) + d`;
combining, `t * ∑|y_i| ≤ t + d`, i.e. `∑|y_i| ≤ 1 + d/t ≤ R` once
`t ≥ d/(R-1)`. -/
theorem ls_A_ball_eventually (η : Site d → ℤ) (hη : ∀ x : Site d, η x ≤ 2 * (d : ℤ) - 1) :
    ∀ R : ℝ, 1 < R → ∀ᶠ t : ℕ in atTop,
      {y : Fin d → ℝ | 0 < podo (explodingPile η) t (nearestSite ((t : ℝ) • y))}
        ⊆ {y : Fin d → ℝ | ∑ i, |y i| ≤ R} := by
  intro R hR
  have hR1 : 0 < R - 1 := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (max ((d : ℝ) / (R - 1)) 0)
  rw [eventually_atTop]
  refine ⟨max N 1, ?_⟩
  intro t ht y hy
  have htN : N ≤ t := le_trans (le_max_left _ _) ht
  have ht1 : 1 ≤ t := le_trans (le_max_right _ _) ht
  have htR : (0 : ℝ) < t := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ht1)
  have hbig : (d : ℝ) / (R - 1) < (t : ℝ) := by
    have h1 : (d : ℝ) / (R - 1) < (N : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) hN
    exact lt_of_lt_of_le h1 (by exact_mod_cast htN)
  have hspeed : (mnorm (nearestSite ((t : ℝ) • y)) : ℝ) ≤ (t : ℝ) := by
    have h := ls_speed_bound η hη t (nearestSite ((t : ℝ) • y)) hy
    exact_mod_cast h
  have hgeom := ls_smul_mnorm_sum_le y t
  have hchain : (t : ℝ) * (∑ i, |y i|) ≤ (t : ℝ) + (d : ℝ) := by linarith
  have hS : (∑ i, |y i|) ≤ 1 + (d : ℝ) / (t : ℝ) := by
    have h1 : (∑ i, |y i|) ≤ ((t : ℝ) + (d : ℝ)) / (t : ℝ) := by
      rw [le_div_iff₀ htR]
      calc (∑ i, |y i|) * (t : ℝ) = (t : ℝ) * (∑ i, |y i|) := by ring
        _ ≤ (t : ℝ) + (d : ℝ) := hchain
    calc (∑ i, |y i|) ≤ ((t : ℝ) + (d : ℝ)) / (t : ℝ) := h1
      _ = 1 + (d : ℝ) / (t : ℝ) := by rw [add_div, div_self (ne_of_gt htR)]
  have hdt : (d : ℝ) / (t : ℝ) ≤ R - 1 := by
    rw [div_le_iff₀ htR]
    have h1 : (d : ℝ) / (R - 1) * (R - 1) < (t : ℝ) * (R - 1) :=
      mul_lt_mul_of_pos_right hbig hR1
    rw [div_mul_cancel₀ _ (ne_of_gt hR1)] at h1
    nlinarith
  show (∑ i, |y i|) ≤ R
  linarith

/-- Step 6, piece (d) (the hard real-analysis core that the paper skips;
it is the content of Step 6, not a further mechanical reduction).
Proof: fix `δ > 0`.  By (b) pick `n` with the shell volume `<
ENNReal.ofReal (δ/2)`, set `ε := 1/(n+1)`.  By `hBR` and (c) with `R := 2`,
`B ⊆ {∑|y_i|≤2}` and eventually `A_t ⊆ {∑|y_i|≤2}`, so `symmDiff A_t B ⊆
{∑|y_i|≤2} =: K'` eventually; take `K := Metric.closedBall 0 2` (compact,
containing `K'` in the sup norm comparison, or work directly with `K'` via
`Gen.exists...`-style compactness of an `ℓ¹` ball) so `symmDiff A_t B =
symmDiff (A_t∩K) (B∩K)` eventually.  By `hshell K ε`, eventually this is `⊆`
the shell, so `volume (symmDiff A_t B) ≤ volume (shell n) < ENNReal.ofReal
(δ/2) < ENNReal.ofReal δ` eventually; conclude via `ENNReal.tendsto_nhds_zero`
(or the order characterisation of `Tendsto _ _ (𝓝 (0 : ℝ≥0∞))`). -/
theorem ls_shell_sandwich_tendsto (η : Site d → ℤ) (N : (Fin d → ℝ) → ℝ)
    (hshell : ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℕ in atTop,
        symmDiff ({y : Fin d → ℝ | 0 < podo (explodingPile η) t (nearestSite ((t : ℝ) • y))} ∩ K)
          ({y : Fin d → ℝ | N y < 1} ∩ K)
          ⊆ {y : Fin d → ℝ | 1 - ε ≤ N y ∧ N y ≤ 1 + ε})
    (hshellvol : Tendsto (fun n : ℕ =>
        volume {y : Fin d → ℝ | 1 - (1 / (n + 1 : ℝ)) ≤ N y ∧ N y ≤ 1 + (1 / (n + 1 : ℝ))})
      atTop (nhds 0))
    (hBR : {y : Fin d → ℝ | N y < 1} ⊆ {y : Fin d → ℝ | ∑ i, |y i| ≤ 1})
    (hAR : ∀ R : ℝ, 1 < R → ∀ᶠ t : ℕ in atTop,
        {y : Fin d → ℝ | 0 < podo (explodingPile η) t (nearestSite ((t : ℝ) • y))}
          ⊆ {y : Fin d → ℝ | ∑ i, |y i| ≤ R}) :
    Tendsto (fun t : ℕ =>
        volume (symmDiff {y : Fin d → ℝ | 0 < podo (explodingPile η) t (nearestSite ((t : ℝ) • y))}
          {y : Fin d → ℝ | N y < 1}))
      atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  by_cases htop : δ = ⊤
  · exact Eventually.of_forall (fun _ => by rw [htop]; exact le_top)
  · have hδ2pos : 0 < δ / 2 := ENNReal.div_pos (ne_of_gt hδ) (by norm_num)
    have hev := (ENNReal.tendsto_nhds_zero.mp hshellvol) (δ / 2) hδ2pos
    rw [eventually_atTop] at hev
    obtain ⟨n, hn⟩ := hev
    have hεr : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    set K : Set (Fin d → ℝ) := Metric.closedBall (0 : Fin d → ℝ) 2 with hK_def
    have hK : IsCompact K := by
      rw [hK_def]
      exact isCompact_closedBall 0 2
    have hshell_ev := hshell K hK (1 / ((n : ℝ) + 1)) hεr
    have hAR_ev := hAR 2 (by norm_num)
    filter_upwards [hshell_ev, hAR_ev] with t hst hAt
    have hAtK : ({y : Fin d → ℝ | 0 < podo (explodingPile η) t (nearestSite ((t : ℝ) • y))})
        ⊆ K := by
      intro z hz
      have hSz : (∑ i, |z i|) ≤ 2 := hAt hz
      rw [hK_def, Metric.mem_closedBall, dist_eq_norm, sub_zero]
      rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      intro i
      rw [Real.norm_eq_abs]
      have := Finset.single_le_sum (fun j _ => abs_nonneg (z j)) (Finset.mem_univ i)
      linarith
    have hBK : ({y : Fin d → ℝ | N y < 1}) ⊆ K := by
      intro z hz
      have hSz : (∑ i, |z i|) ≤ 1 := hBR hz
      rw [hK_def, Metric.mem_closedBall, dist_eq_norm, sub_zero]
      rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      intro i
      rw [Real.norm_eq_abs]
      have := Finset.single_le_sum (fun j _ => abs_nonneg (z j)) (Finset.mem_univ i)
      linarith
    have hAi : ({y : Fin d → ℝ | 0 < podo (explodingPile η) t (nearestSite ((t : ℝ) • y))}) ∩ K
        = {y : Fin d → ℝ | 0 < podo (explodingPile η) t (nearestSite ((t : ℝ) • y))} :=
      Set.inter_eq_left.mpr hAtK
    have hBi : ({y : Fin d → ℝ | N y < 1}) ∩ K = {y : Fin d → ℝ | N y < 1} :=
      Set.inter_eq_left.mpr hBK
    rw [hAi, hBi] at hst
    have hle_shell : volume (symmDiff
        {y : Fin d → ℝ | 0 < podo (explodingPile η) t (nearestSite ((t : ℝ) • y))}
        {y : Fin d → ℝ | N y < 1})
        ≤ volume {y : Fin d → ℝ | 1 - (1 / ((n : ℝ) + 1)) ≤ N y ∧ N y ≤ 1 + (1 / ((n : ℝ) + 1))} :=
      measure_mono hst
    have hn' : volume {y : Fin d → ℝ | 1 - (1 / ((n : ℝ) + 1)) ≤ N y ∧ N y ≤ 1 + (1 / ((n : ℝ) + 1))}
        ≤ δ / 2 :=
      by simpa only [Nat.cast_add, Nat.cast_one] using hn n le_rfl
    calc volume (symmDiff
          {y : Fin d → ℝ | 0 < podo (explodingPile η) t (nearestSite ((t : ℝ) • y))}
          {y : Fin d → ℝ | N y < 1})
        ≤ volume {y : Fin d → ℝ | 1 - (1 / ((n : ℝ) + 1)) ≤ N y ∧ N y ≤ 1 + (1 / ((n : ℝ) + 1))} := hle_shell
      _ ≤ δ / 2 := hn'
      _ ≤ δ := ENNReal.half_le_self

theorem ls_measure_convergence (η : Site d → ℤ) (N : (Fin d → ℝ) → ℝ)
    (_hexp : ∀ x : Site d, arrival η x ≠ ⊤)
    (hlb : ∀ y : Fin d → ℝ, ∑ i, |y i| ≤ N y)
    (hshell : ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℕ in atTop,
        symmDiff ({y : Fin d → ℝ | 0 < podo (explodingPile η) t (nearestSite ((t : ℝ) • y))} ∩ K)
          ({y : Fin d → ℝ | N y < 1} ∩ K)
          ⊆ {y : Fin d → ℝ | 1 - ε ≤ N y ∧ N y ≤ 1 + ε})
    (hfrontier : volume (frontier {y : Fin d → ℝ | N y < 1}) = 0)
    -- The next three hypotheses are needed for Step 6 (see
    -- `ls_levelset_subset_frontier`'s need for openness/homogeneity of `N`, and
    -- `ls_A_ball_eventually`'s need for `η`'s standing bound).  All of them are
    -- available at this lemma's only call site (`ls_assemble`).
    (hBopen : IsOpen {y : Fin d → ℝ | N y < 1})
    (hhom : ∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y)
    (hη : ∀ x : Site d, η x ≤ 2 * (d : ℤ) - 1) :
    Tendsto (fun t : ℕ =>
        volume (symmDiff {y : Fin d → ℝ | 0 < podo (explodingPile η) t (nearestSite ((t : ℝ) • y))}
          {y : Fin d → ℝ | N y < 1}))
      atTop (nhds 0) := by
  refine ls_shell_sandwich_tendsto η N hshell
    (ls_shell_volume_tendsto N hlb hfrontier hBopen hhom) ?_
    (ls_A_ball_eventually η hη)
  intro y hy
  have hyN := hlb y
  simp only [Set.mem_setOf_eq] at hy ⊢
  linarith


/-- Mirror of `ls_chipLaw_low` for an upper bound instead of a lower one
(same proof, `Measure.dirac_apply_of_mem` applied to the other-facing
membership facts `ha'`/`hb'`).  Placed here (ahead of `ls_chipLaw_low`'s
own home in "Step 8" below) because `ls_toyLaw_upper_ae`, needed by
`ls_assemble`'s call into `ls_measure_convergence`, needs it first. -/
theorem ls_chipLaw_up (a b c : ℤ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (ha : a ≤ c) (hb : b ≤ c) : (chipLaw a b p) {m : ℤ | m ≤ c} = 1 := by
  have ha' : a ∈ ({m : ℤ | m ≤ c} : Set ℤ) := ha
  have hb' : b ∈ ({m : ℤ | m ≤ c} : Set ℤ) := hb
  rw [chipLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem ha', Measure.dirac_apply_of_mem hb',
    smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← ENNReal.ofReal_add hp (by linarith)]
  have h : p + (1 - p) = 1 := by ring
  rw [h, ENNReal.ofReal_one]

/-- The product-measure lift of `ls_chipLaw_up`: since EVERY coordinate is
`≤ 2d-1` with probability `1` under the one-site law (`ls_chipLaw_up`
with `a := 2d-1, b := 2d-2, c := 2d-1`), and `Site d = Fin d → ℤ` is
countable, the countable intersection of these full-measure per-coordinate
events is again full measure.  Proof: `toyLaw d p = Measure.infinitePi
(fun _ => chipLaw (2d-1) (2d-2) p)`; the pushforward of `Measure.infinitePi`
under evaluation at a fixed coordinate `x` is that coordinate's own law
(the marginal fact used identically, for a lower bound instead of an upper
one, in `aux_finite_exploding_bounds` of `Exploding/Support/SubFinite.lean`); combine
`∀ x, ∀ᵐ η, η x ≤ 2d-1` (one instance of `ls_chipLaw_up` per `x`, read
through the marginal) into `∀ᵐ η, ∀ x, η x ≤ 2d-1` via
`MeasureTheory.ae_all_iff` (valid since `Site d` is countable). -/
theorem ls_toyLaw_upper_ae (d : ℕ) (_hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    ∀ᵐ η ∂(toyLaw d p), ∀ x : Site d, η x ≤ 2 * (d : ℤ) - 1 := by
  have hp0 : 0 ≤ p := by linarith
  have hp1' : p ≤ 1 := by linarith
  haveI : IsProbabilityMeasure (chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p) := by
    refine ⟨?h⟩
    rw [chipLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.dirac_apply, Measure.dirac_apply]
    simp
    rw [← ENNReal.ofReal_add hp0 (by linarith)]
    simp
  have h_chip : ∀ x : Site d, (chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p) {m : ℤ | m ≤ 2 * (d : ℤ) - 1} = 1 := by
    intro x
    apply ls_chipLaw_up (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) (2 * (d : ℤ) - 1) p hp0 hp1'
    · rfl
    · omega
  have h_per_x : ∀ x : Site d, ∀ᵐ η ∂(toyLaw d p), η x ≤ 2 * (d : ℤ) - 1 := by
    intro x
    have h_map : (toyLaw d p).map (fun η : Site d → ℤ => η x) = chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p := by
      simpa [toyLaw, productLaw] using MeasureTheory.Measure.infinitePi_map_eval (μ := fun _ : Site d => chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p) (i := x)
    have h_ae_chip : ∀ᵐ v ∂(chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p), v ≤ 2 * (d : ℤ) - 1 := by
      rw [MeasureTheory.ae_iff]
      simp [chipLaw]
    have h_aemeas : AEMeasurable (fun (η : Site d → ℤ) => η x) (toyLaw d p) :=
      (measurable_pi_apply x).aemeasurable
    have h_meas : MeasurableSet {v : ℤ | v ≤ 2 * (d : ℤ) - 1} := measurableSet_Iic
    rw [← MeasureTheory.ae_map_iff h_aemeas h_meas, h_map]
    exact h_ae_chip
  rw [ae_all_iff]
  exact h_per_x

/-- Step 7 (assembly).  Apply `thm-time-constant`
(`Exploding.Frozen.convergence_of_time_constant`) to get `N`, its
regularity, and the a.s. locally-uniform convergence; feed the `N`,
`hcont`, `hconv`, `hhom` into Steps 3-4 to get `B := {N < 1}` is a domain
with null frontier; feed `hloc`/`hexp` into Steps 5-6 to get the measure
convergence; assemble into the target's `∃ B, ...`.  Pure bookkeeping given
Steps 1-6. -/
theorem ls_assemble (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hFLP : Exploding.External.FeyLevinePeresExplosive)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree) (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ B : Set (Fin d → ℝ),
      Convex ℝ B ∧ IsOpen B ∧ B.Nonempty ∧
      ∀ᵐ η ∂(toyLaw d p),
        Tendsto
          (fun t : ℕ =>
            volume (symmDiff
              {y : Fin d → ℝ | 0 < podo (explodingPile η) t (nearestSite ((t : ℝ) • y))} B))
          atTop (nhds 0) := by
  obtain ⟨N, hcont, hconv, hhom, hae⟩ :=
    Exploding.Frozen.convergence_of_time_constant d hd p hp hp1 hFLP hLSSB hHole hChem
  by_cases hμ : toyLaw d p = 0
  · exact ⟨Set.univ, convex_univ, isOpen_univ, Set.univ_nonempty, by simp [hμ]⟩
  · haveI : NeBot (ae (toyLaw d p)) := ae_neBot.mpr hμ
    obtain ⟨η₀, hη₀, hη₀ub⟩ := (hae.and (ls_toyLaw_upper_ae d hd p hp hp1)).exists
    have hlb : ∀ y : Fin d → ℝ, ∑ i, |y i| ≤ N y :=
      fun y => ls_N_lower_bound η₀ N hη₀ub hη₀.2.1 hη₀.2.2 y
    obtain ⟨hBconv, hBopen, hBne, hBfront⟩ := ls_B_domain N hcont hconv hhom hlb
    refine ⟨{y : Fin d → ℝ | N y < 1}, hBconv, hBopen, hBne, ?_⟩
    filter_upwards [hae, ls_toyLaw_upper_ae d hd p hp hp1] with η hη hηub
    exact ls_measure_convergence η N hη.2.1 hlb
      (fun K hK ε hε => ls_shell_inclusion η N hη.2.1 hη.2.2 K hK ε hε) hBfront
      hBopen hhom hηub


/-- Step 8 (the hypothesis `hFLP` is not
actually a free assumption). `Exploding.Frozen.explosive` (Theorem 1.4, node
`thm-explosive`) applied to `η ∼ Bernoulli(2d-1, 2d-2, p) =
Measure.infinitePi (chipLaw (2d-1) (2d-2) p)` proves exactly
`Exploding.External.FeyLevinePeresExplosive`: the hypothesis `β ≥ d` holds
since `2d - 2 ≥ d` when `d ≥ 2`, and `P(β(0) = 2d-1) = p > 0`. This is
literally the relationship the paper itself describes ("we use this ... to
extend Theorem 1.1", `exploding.tex:264`), so `hFLP` is discharged by it. -/
theorem ls_chipLaw_isProb (a b : ℤ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (chipLaw a b p) := by
  refine ⟨?_⟩
  rw [chipLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ a), Measure.dirac_apply_of_mem (Set.mem_univ b),
    smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← ENNReal.ofReal_add hp (by linarith)]
  have h : p + (1 - p) = 1 := by ring
  rw [h, ENNReal.ofReal_one]

theorem ls_chipLaw_low (a b c : ℤ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (ha : c ≤ a) (hb : c ≤ b) : (chipLaw a b p) {m : ℤ | c ≤ m} = 1 := by
  have ha' : a ∈ ({m : ℤ | c ≤ m} : Set ℤ) := ha
  have hb' : b ∈ ({m : ℤ | c ≤ m} : Set ℤ) := hb
  rw [chipLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem ha', Measure.dirac_apply_of_mem hb',
    smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← ENNReal.ofReal_add hp (by linarith)]
  have h : p + (1 - p) = 1 := by ring
  rw [h, ENNReal.ofReal_one]

theorem ls_chipLaw_hit (a b : ℤ) (p : ℝ) (hp : 0 < p) :
    0 < (chipLaw a b p) {a} := by
  have hle : (ENNReal.ofReal p • Measure.dirac a) {a} ≤ (chipLaw a b p) {a} := by
    rw [chipLaw, Measure.add_apply]
    exact le_add_of_nonneg_right bot_le
  rw [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_singleton a), smul_eq_mul,
    mul_one] at hle
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hp) hle

theorem ls_flp_from_explosive (hSch : Exploding.External.SchonmannBootstrap) :
    Exploding.External.FeyLevinePeresExplosive := by
  intro d hd p hp hp1
  have hν : IsProbabilityMeasure (chipLaw (2 * d - 1) (2 * d - 2) p) :=
    ls_chipLaw_isProb (2 * d - 1) (2 * d - 2) p hp.le hp1
  have hlow : (chipLaw (2 * d - 1) (2 * d - 2) p) {m : ℤ | (d : ℤ) ≤ m} = 1 :=
    ls_chipLaw_low (2 * d - 1) (2 * d - 2) (d : ℤ) p hp.le hp1 (by omega) (by omega)
  have hhit : 0 < (chipLaw (2 * d - 1) (2 * d - 2) p) {2 * (d : ℤ) - 1} :=
    ls_chipLaw_hit (2 * d - 1) (2 * d - 2) p hp
  simpa only [toyLaw, productLaw] using
    Exploding.Frozen.explosive d hd (chipLaw (2 * d - 1) (2 * d - 2) p) hν hlow hhit hSch


end Exploding.LSProof

open Exploding LatticeProb MeasureTheory Filter
