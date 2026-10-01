/-
Packet AS-7: the last claim `hpodo` of
`Exploding.Frozen.approximate_subadditive`.  Sorry-free support file.

## What is added

* `as7_podo_origin_max`: for an arbitrary pile whose background is at most
  `2d - 1` off the origin, the odometer of the origin is the pointwise maximum
  at every time.  This is the `eq:induction3` half of the paper's Step 1
  (`assp_podo_inv` in `ASSpecial.lean`), but with the hypothesis `s 0 ≤ 2d`
  dropped: the origin-maximum argument never uses it.  This is what makes the
  argument available for `explodingPile η = η + M_η δ_0`, whose origin value
  `η 0 + M_η` can exceed `2d`.

* `as7_hpodo_of_infTopple`: if some site topples infinitely often, then `hpodo`
  holds.  `as2_infTopple_all` (in `ASProof2.lean`) spreads unbounded toppling to
  every site, and the penultimate cluster is finite, so one can take the maximum
  of the individual first-toppling times.

* `as7_hpodo_of_double`: the reduction of `ASProof6.lean` assembled with the
  origin toppling `as5_origin_topples_of_not_stabilizable`.  Thus `hpodo`
  follows from the sharper claim that the pile topples every
  positive-penultimate-wave site at least twice.
-/
import Exploding.Support.ASProof6

open Exploding LatticeProb MeasureTheory

set_option linter.unusedVariables false

/-- **New.**  For an arbitrary pile `σ` with `σ x ≤ 2d - 1` off the origin, the
origin's odometer is the maximum at every time.  Induction on `t`: if at time
`t` the origin is the maximum and a site `x ≠ 0` ties the maximum, then
`lap (podo σ t) x ≤ 0` (all neighbours are at most the tied value), so
`pconf σ t x ≤ σ x ≤ 2d - 1` and `x` is stable; hence only the origin can
increase, and the maximum is preserved.  Unlike `assp_podo_inv`, no upper bound
on `σ 0` is used. -/
theorem as7_podo_origin_max {d : ℕ} (σ : Site d → ℤ)
    (hhigh : ∀ x, x ≠ (0 : Site d) → σ x ≤ 2 * (d : ℤ) - 1) :
    ∀ t : ℕ, ∀ x : Site d, podo σ t x ≤ podo σ t (0 : Site d) := by
  intro t
  induction t with
  | zero => intro x; simp [podo_zero]
  | succ t ih =>
    intro x
    by_cases hx0 : x = (0 : Site d)
    · rw [hx0]
    · rw [podo_succ σ t x, podo_succ σ t (0 : Site d)]
      by_cases hlt : podo σ t x < podo σ t (0 : Site d)
      · have h3 : podo σ t x + 1 ≤ podo σ t (0 : Site d) := by omega
        split_ifs <;> omega
      · have heq : podo σ t x = podo σ t (0 : Site d) := le_antisymm (ih x) (not_lt.mp hlt)
        have hlap : lap (podo σ t) x ≤ 0 := by
          have hnb : nbrSumZ (podo σ t) x ≤ 2 * (d : ℤ) * podo σ t x := by
            simp only [nbrSumZ]
            have hterm : ∀ i : Fin d, podo σ t (x + unit i) + podo σ t (x - unit i)
                ≤ podo σ t x + podo σ t x := by
              intro i
              have h1 := ih (x + unit i)
              have h2 := ih (x - unit i)
              rw [← heq] at h1 h2
              linarith
            calc ∑ i : Fin d, (podo σ t (x + unit i) + podo σ t (x - unit i))
                ≤ ∑ _i : Fin d, (podo σ t x + podo σ t x) :=
                  Finset.sum_le_sum fun i _ => hterm i
              _ = 2 * (d : ℤ) * podo σ t x := by
                  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
                  simp only [nsmul_eq_mul]
                  ring
          simp only [lap]
          linarith
        have hstable : ¬ 2 * (d : ℤ) ≤ pconf σ t x := by
          simp only [pconf]
          have := hhigh x hx0
          linarith
        rw [if_neg hstable, heq]
        split_ifs <;> omega

/-- **New.**  If some site of a pile `σ` topples infinitely often, then every
site topples at least once, and since any finite set is covered by taking the
maximum of the individual first-toppling times, the whole finite set topples at
one common time.  This is `as2_infTopple_all` (unbounded toppling spreads to
every site) plus monotonicity. -/
theorem as7_topples_finite_set_of_infTopple {d : ℕ} (hd : 1 ≤ d) (σ : Site d → ℤ)
    (hinf : ∃ x : Site d, as2_InfTopple σ x) (S : Set (Site d)) (hS : S.Finite) :
    ∃ t0 : ℕ, ∀ x ∈ S, 1 ≤ podo σ t0 x := by
  classical
  have hall : ∀ y : Site d, as2_InfTopple σ y := as2_infTopple_all hd hinf
  choose tt htt using fun y : Site d => hall y 0
  refine ⟨hS.toFinset.sup tt, fun x hx => ?_⟩
  have hxmem : x ∈ hS.toFinset := hS.mem_toFinset.mpr hx
  have hle : tt x ≤ hS.toFinset.sup tt := Finset.le_sup (f := tt) hxmem
  have hpos : 0 < podo σ (tt x) x := htt x
  exact le_trans (by omega : 1 ≤ podo σ (tt x) x) (as_podo_mono σ hle x)

/-- **`hpodo` in the unbounded-toppling case.**  If `explodingPile η` topples
some site infinitely often, then it topples the finite penultimate cluster at a
common time. -/
theorem as7_hpodo_of_infTopple {d : ℕ} (hd : 1 ≤ d) (η : Site d → ℤ)
    (hfin : (penultimateCluster η (0 : Site d)).Finite)
    (hinf : ∃ x : Site d, as2_InfTopple (explodingPile η) x) :
    ∃ t0 : ℕ, ∀ x ∈ penultimateCluster η (0 : Site d),
      1 ≤ podo (explodingPile η) t0 x :=
  as7_topples_finite_set_of_infTopple hd (explodingPile η) hinf _ hfin

/-- **`hpodo` from the sharper double-toppling claim.**  Combine the reduction
of `ASProof6.lean` (`as6_cluster_lit_of_double_support`, which lights every
non-origin point of `penultimateCluster η 0` from two topplings of its
positive-penultimate-wave neighbour) with the origin toppling
`as5_origin_topples_of_not_stabilizable` (a non-stabilizable pile whose
background is at most `2d - 1` off the origin topples the origin).  The common
time is the maximum of `T + 1` and the origin's toppling time. -/
theorem as7_hpodo_of_double {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (hnr : ¬ Robust η)
    (hdouble : ∃ T : ℕ, ∀ y : Site d, 0 < penultimateWave η (0 : Site d) y →
      2 ≤ podo (explodingPile η) T y) :
    ∃ t0 : ℕ, ∀ x ∈ penultimateCluster η (0 : Site d),
      1 ≤ podo (explodingPile η) t0 x := by
  obtain ⟨T, hT⟩ := hdouble
  obtain ⟨s, hs⟩ := as5_origin_topples_of_not_stabilizable (by omega : 1 ≤ d) (explodingPile η)
    (fun x hx => by
      simp only [explodingPile]
      rw [dirac_of_ne hx, mul_zero, add_zero]
      exact hhigh x)
    (as_explosionThreshold_spec η hnr).2
  refine ⟨max (T + 1) s, fun x hx => ?_⟩
  by_cases hx0 : x = (0 : Site d)
  · subst hx0
    exact le_trans hs (as_podo_mono (explodingPile η) (le_max_right (T + 1) s) (0 : Site d))
  · have h1 := as6_cluster_lit_of_double_support η hlow T hT x hx hx0
    exact le_trans h1 (as_podo_mono (explodingPile η) (le_max_left (T + 1) s) x)
