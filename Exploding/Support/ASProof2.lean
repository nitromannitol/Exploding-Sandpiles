/-
Follow-up AS-2 support file for `Exploding.Frozen.approximate_subadditive`: the
restated `|P̃| < ∞` claim and the final a.e. assembly taking the smaller set of
open claims.  Sorry-free.

## Why the unrestricted `|P̃| < ∞` is false

The previous reduction carried

  `htildePfin : ∀ η : Site d → ℤ, (as_tildeP η).Finite`

with no hypothesis on `η`.  This is refuted as follows.  Take `d = 2` and let
`S = {(5n, 0) : n ≥ 1}` be a sparse ray; set `η x = 4` for `x ∈ S` and
`η x = 0` otherwise.  The sites of `S` are pairwise at distance at least `5`,
so their unit neighbourhoods are disjoint.  Each `x ∈ S` holds exactly `2d = 4`
chips, hence topples exactly once; each neighbour of `S` receives the single
chip from the adjacent site of `S` and holds at most `1 < 4`, so it never
topples.  Thus `η` stabilizes with terminal odometer `1_S`, supported on the
infinite set `S`.  Adding any finite mass `n δ_0` at the origin produces a
finite avalanche (finite mass on a threshold-`2d` lattice always stabilizes)
which reaches only finitely many sites of `S`; those topple at most once and
their sparks die out.  Hence `η + n δ_0` stabilizes for every `n ≥ 1`, i.e.
`η` is `Robust`, and `explosionThreshold η = sInf ∅ = 0`.  Therefore

  `as_tildeV η = as_podoTerminal (η + ((0 : ℤ) - 1) δ_0) = as_podoTerminal (η - δ_0)`,

which is `≥ 1` on the infinite set `S` because removing the chip at the origin
`0 ∉ S` does not affect the `S`-topplings (and the stabilization time is `≥ 1`
since `podo (η - δ_0) 0 = 0 ≠ podo (η - δ_0) 1`).  Hence `as_tildeP η`
contains the infinite neighbourhood set `N(S)`.

The counterexample violates both standing assumptions of the use site: the
bound `2d - 2 ≤ η ≤ 2d - 1` and non-robustness.  The restatement below keeps
exactly the hypotheses available where `htildePfin` is consumed.
-/
import Exploding.Support.ASProof

open Exploding LatticeProb MeasureTheory

set_option linter.unusedVariables false

/-- The final a.e. assembly, with `htildePfin` restated under the bounds that
hold at the use site: the finiteness of `as_tildeP` is only needed for the
almost-every `η` satisfying `2d - 2 ≤ η ≤ 2d - 1`.  The other open claims
`hrobust`, `hpodo`, `hlastreach`, `hspecial` are unchanged. -/
theorem as2_approximate_subadditive_of_gaps
    (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance)
    (hrobust : ∀ η : Site d → ℤ, (∀ x, 2 * (d : ℤ) - 2 ≤ η x) →
      (∀ x, η x ≤ 2 * (d : ℤ) - 1) → Robust η →
        ∀ n : ℕ, 1 ≤ n → WaveStabilizable η n (0 : Site d))
    (hpodo : ∀ η : Site d → ℤ, (∀ x, 2 * (d : ℤ) - 2 ≤ η x) →
      (∀ x, η x ≤ 2 * (d : ℤ) - 1) → ¬ Robust η →
        (penultimateCluster η (0 : Site d)).Finite →
          ∃ t0 : ℕ, ∀ x ∈ penultimateCluster η (0 : Site d),
            1 ≤ podo (explodingPile η) t0 x)
    (hlastreach : ∀ η : Site d → ℤ, (∀ x, 2 * (d : ℤ) - 2 ≤ η x) →
      (∀ x, η x ≤ 2 * (d : ℤ) - 1) →
        (∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d)) →
          ∃ c : ℕ, ∀ x ∈ as_tildeP η, 1 ≤ lastWave η (0 : Site d) c x)
    (htildePfin : ∀ η : Site d → ℤ, (∀ x, 2 * (d : ℤ) - 2 ≤ η x) →
      (∀ x, η x ≤ 2 * (d : ℤ) - 1) → (as_tildeP η).Finite)
    (hspecial : ∀ η : Site d → ℤ, (∀ x, 2 * (d : ℤ) - 2 ≤ η x) →
      (∀ x, η x ≤ 2 * (d : ℤ) - 1) →
        ∀ t : ℕ, ∀ x : Site d, 0 < as_wOdo η t x → 0 < as_tildeW η t x) :
    ∀ᵐ η ∂(toyLaw d p), ∃ C1 C2 : ℕ, ∀ x : Site d,
      arrival η x ≤ lastArrival η (0 : Site d) x + (C1 : ℕ∞) ∧
        lastArrival η (0 : Site d) x ≤ arrival η x + (C2 : ℕ∞) := by
  filter_upwards [as_eta_bounds d hd p hp hp1,
    Exploding.Frozen.finite_exploding d hd p hp hp1.le hLSSB hHole hChem,
    as_penultimateCluster_finite d hd p hp hp1 hLSSB hHole hChem] with η hbounds hlast hPfin
  have hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x := fun x => (hbounds x).1
  have hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1 := fun x => (hbounds x).2
  have hnotrobust : ¬ Robust η := by
    intro hrob
    obtain ⟨n, hn1, hnstab⟩ := hlast
    exact hnstab (hrobust η hlow hhigh hrob n hn1)
  have hexp1 : 1 ≤ explosionThreshold η := (as_explosionThreshold_spec η hnotrobust).1
  obtain ⟨C1, hC1⟩ := as_ineq1 hd η hlow hhigh hlast (hpodo η hlow hhigh hnotrobust hPfin)
  obtain ⟨C2, hC2⟩ := as_ineq2 hd η hlow hhigh hlast hexp1
    (hlastreach η hlow hhigh hlast) (htildePfin η hlow hhigh) (hspecial η hlow hhigh)
  exact ⟨C1, C2, fun x => ⟨hC1 x, hC2 x⟩⟩

/-! ### Finite-sink stabilization -/

/-- A site whose parallel-toppling odometer is unbounded (`x` topples infinitely
often). -/
def as2_InfTopple {d : ℕ} (σ : Site d → ℤ) (x : Site d) : Prop :=
  ∀ N : ℕ, ∃ t : ℕ, (N : ℤ) < podo σ t x

/-- Unbounded toppling spreads to a neighbour: the neighbour receives one chip
per toppling, so if it stopped toppling its (stable) pile would eventually
exceed `2d`. -/
theorem as2_infTopple_propagate {d : ℕ} {σ : Site d → ℤ} {x y : Site d}
    (hd : 1 ≤ d) (hyx : (lattice d).Adj y x) (hx : as2_InfTopple σ x) :
    as2_InfTopple σ y := by
  intro N
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  set B : ℕ := (2 * (d : ℤ) * (N : ℤ) + |σ y| + 2 * (d : ℤ) + 1).toNat with hB
  obtain ⟨t, ht⟩ := hx B
  have hBcast : (B : ℤ) = 2 * (d : ℤ) * (N : ℤ) + |σ y| + 2 * (d : ℤ) + 1 := by
    rw [hB, Int.toNat_of_nonneg]
    have h := neg_abs_le (σ y)
    positivity
  have hpc : ∀ s : ℕ, 2 * (d : ℤ) ≤ pconf σ (t + s) y := by
    intro s
    have hxle : podo σ t x ≤ podo σ (t + s) x := as_podo_mono σ (Nat.le_add_right t s) x
    have hyle : podo σ (t + s) y ≤ (N : ℤ) := hcon (t + s)
    have hnr : podo σ (t + s) x ≤ nbrSumZ (podo σ (t + s)) y := by
      obtain ⟨i, hi | hi⟩ := hyx
      · have h2 : podo σ (t + s) (y + unit i) + podo σ (t + s) (y - unit i)
            ≤ nbrSumZ (podo σ (t + s)) y := by
          rw [nbrSumZ]
          exact Finset.single_le_sum
            (f := fun j : Fin d => podo σ (t + s) (y + unit j) + podo σ (t + s) (y - unit j))
            (fun j _ => by
              have h3 := as_podo_nonneg σ (t + s) (y + unit j)
              have h4 := as_podo_nonneg σ (t + s) (y - unit j)
              linarith) (Finset.mem_univ i)
        have h1 : podo σ (t + s) (y + unit i)
            ≤ podo σ (t + s) (y + unit i) + podo σ (t + s) (y - unit i) := by
          have h := as_podo_nonneg σ (t + s) (y - unit i); linarith
        rw [hi]; linarith
      · have h2 : podo σ (t + s) (y + unit i) + podo σ (t + s) (y - unit i)
            ≤ nbrSumZ (podo σ (t + s)) y := by
          rw [nbrSumZ]
          exact Finset.single_le_sum
            (f := fun j : Fin d => podo σ (t + s) (y + unit j) + podo σ (t + s) (y - unit j))
            (fun j _ => by
              have h3 := as_podo_nonneg σ (t + s) (y + unit j)
              have h4 := as_podo_nonneg σ (t + s) (y - unit j)
              linarith) (Finset.mem_univ i)
        have h1 : podo σ (t + s) (y - unit i)
            ≤ podo σ (t + s) (y + unit i) + podo σ (t + s) (y - unit i) := by
          have h := as_podo_nonneg σ (t + s) (y + unit i); linarith
        have hxeq : x = y - unit i := by rw [hi]; abel
        rw [hxeq]; linarith
    have hsy : -(0 : ℤ) ≤ σ y + |σ y| := by
      have h := neg_abs_le (σ y); linarith
    simp only [pconf, lap]
    have hdpos : (0 : ℤ) < 2 * (d : ℤ) := by
      have : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
      linarith
    nlinarith [hxle, ht, hBcast, hyle, hnr, hsy, hdpos]
  have hind : ∀ s : ℕ, podo σ (t + s) y = podo σ t y + (s : ℤ) := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      have hstep : podo σ (t + (s + 1)) y = podo σ (t + s) y + 1 := by
        have heq : t + (s + 1) = (t + s) + 1 := by omega
        rw [heq, podo_succ, if_pos (hpc s)]
      rw [hstep, ih]
      push_cast
      ring
  have hcontr := hcon (t + (N + 1))
  rw [hind (N + 1)] at hcontr
  have hnn := as_podo_nonneg σ t y
  push_cast at hcontr
  omega

/-- Unbounded toppling at one site forces unbounded toppling at every site,
by connectedness of the lattice. -/
theorem as2_infTopple_all {d : ℕ} (hd : 1 ≤ d) {σ : Site d → ℤ}
    (h : ∃ x, as2_InfTopple σ x) : ∀ y, as2_InfTopple σ y := by
  obtain ⟨x, hx⟩ := h
  intro y
  -- propagation along a walk of the induced graph on `univ`
  have hwalk : ∀ (u v : (Set.univ : Set (Site d)))
      (p : ((lattice d).induce (Set.univ : Set (Site d))).Walk u v),
      as2_InfTopple σ (u : Site d) → as2_InfTopple σ (v : Site d) := by
    intro u v p
    induction p with
    | nil => intro hu; exact hu
    | cons h q ih =>
        intro hu
        exact ih (as2_infTopple_propagate hd (SimpleGraph.induce_adj.mp h).symm hu)
  -- get a walk from `x` to `y` inside a large centred box
  have hxn : 0 ≤ mnorm x := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hyn : 0 ≤ mnorm y := Finset.sum_nonneg fun i _ => abs_nonneg _
  set m : ℕ := (mnorm x + mnorm y).toNat with hm
  have hmcast : ((m : ℕ) : ℤ) = mnorm x + mnorm y := Int.toNat_of_nonneg (by linarith)
  have hxcent : x ∈ (cent d m : Set (Site d)) := by
    intro i
    have h1 : |x i| ≤ mnorm x := abs_coord_le_mnorm x i
    have h2 : mnorm x ≤ (m : ℤ) := by rw [hmcast]; linarith
    linarith
  have hycent : y ∈ (cent d m : Set (Site d)) := by
    intro i
    have h1 : |y i| ≤ mnorm y := abs_coord_le_mnorm y i
    have h2 : mnorm y ≤ (m : ℤ) := by rw [hmcast]; linarith
    linarith
  obtain ⟨_, _, hreach⟩ := cent_connected_in (Set.univ : Set (Site d)) m
    (by intro z _; exact trivial) x y hxcent hycent
  obtain ⟨p⟩ := hreach
  exact hwalk ⟨x, trivial⟩ ⟨y, trivial⟩ p hx

/-- **Finite-sink stabilization.** If only finitely many sites ever topple, the
process is stabilizable: an unbounded toppler spreads to every site, and a
bounded monotone odometer stabilizes. -/
theorem as2_finite_toppling_set_stabilizable {d : ℕ} (hd : 1 ≤ d) (σ : Site d → ℤ)
    (hfin : {x : Site d | ∃ t : ℕ, 0 < podo σ t x}.Finite) : Stabilizable σ := by
  classical
  -- every site has a bounded odometer
  have hbounded : ∀ x : Site d, ∃ N : ℕ, ∀ t : ℕ, podo σ t x ≤ (N : ℤ) := by
    intro x
    by_contra hx
    have hinf : as2_InfTopple σ x := by
      intro N
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      exact hx ⟨N, hcon⟩
    have hall := as2_infTopple_all hd ⟨x, hinf⟩
    have huniv : (Set.univ : Set (Site d)) ⊆ {x | ∃ t : ℕ, 0 < podo σ t x} := by
      intro z _
      obtain ⟨t, ht⟩ := hall z 0
      exact ⟨t, by omega⟩
    haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    haveI : Infinite (Site d) := inferInstance
    exact Set.infinite_univ (hfin.subset huniv)
  -- each site stabilizes
  have hstab : ∀ x : Site d, ∃ T : ℕ, ∀ t : ℕ, T ≤ t → podo σ t x = podo σ T x := by
    intro x
    obtain ⟨N, hN⟩ := hbounded x
    obtain ⟨ub, hub, hmax⟩ := Int.exists_greatest_of_bdd
      (P := fun k : ℤ => ∃ t : ℕ, podo σ t x = k)
      ⟨(N : ℤ), fun k hk => by obtain ⟨t, ht⟩ := hk; rw [← ht]; exact hN t⟩
      ⟨podo σ 0 x, 0, rfl⟩
    obtain ⟨Ts, hsT⟩ := hub
    refine ⟨Ts, fun t ht => le_antisymm ?_ ?_⟩
    · calc podo σ t x ≤ ub := hmax _ ⟨t, rfl⟩
        _ = podo σ Ts x := hsT.symm
    · exact as_podo_mono σ ht x
  choose T hT using hstab
  refine ⟨hfin.toFinset.sup T, fun t ht => ?_⟩
  funext x
  by_cases hx : x ∈ hfin.toFinset
  · have h1 : T x ≤ t := le_trans (Finset.le_sup (f := T) hx) ht
    have h2 : T x ≤ hfin.toFinset.sup T := Finset.le_sup (f := T) hx
    rw [hT x t h1, hT x (hfin.toFinset.sup T) h2]
  · have hxR : ¬ (∃ t : ℕ, 0 < podo σ t x) := fun h => hx (hfin.mem_toFinset.mpr h)
    have hz : ∀ s : ℕ, podo σ s x = 0 := by
      intro s
      have hnn := as_podo_nonneg σ s x
      by_contra hne
      exact hxR ⟨s, by omega⟩
    rw [hz t, hz (hfin.toFinset.sup T)]
