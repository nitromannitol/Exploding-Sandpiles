import Exploding.Support.Hypotheses
import Exploding.Support.CrossingTimeAux
import Exploding.Support.SubGeom
import Exploding.Support.AllHighGoodCubes
import Exploding.Support.AllHighLastArrival
import Exploding.Support.ApproximateSubadditiveP1
import Exploding.Support.ExplosiveVacuity
import LatticeProb.Lattice.Translation

/-!
# The all-high background satisfies the generalized hypotheses H4 and H5

At `d ≥ 2` the Dirac mass `Q` at the all-high background `η ≡ 2d - 1` satisfies
the strongly box-crossing hypothesis `StronglyBoxCrossingHyp` with singleton boxes
`k ≡ 1`, and the wave-approximation hypothesis `WaveApproximationHyp`.

The strong box-crossing statement is obtained from the cube-level good-cube result
`all_high_good_cube` by translating the cube `Q_K` onto the tile `rboxShift`, which
is the translated closure and line bookkeeping of `Hypotheses.lean`. The wave
approximation uses the exact all-high formulas for the last-wave and ordinary
arrival times.
-/

namespace Exploding

open LatticeProb MeasureTheory Filter
open scoped Classical

/-- The outer closure commutes with translation of the underlying set. -/
theorem ahg_closureN_shift {d : ℕ} (B : Set (Site d)) (c x : Site d) :
    x ∈ closureN {y | y + c ∈ B} ↔ x + c ∈ closureN B := by
  simp only [closureN, outerBoundary, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (h | ⟨hx, y, hy, hadj⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hx, y + c, hy, (lattice_adj_add_right_iff c x y).2 hadj⟩
  · rintro (h | ⟨hx, w, hw, hadj⟩)
    · exact Or.inl h
    · refine Or.inr ⟨hx, w - c, by rwa [sub_add_cancel], ?_⟩
      exact (lattice_adj_add_right_iff c x (w - c)).1 (by rwa [sub_add_cancel])

/-- A crossing time bounded by the deadline `k^d` is witnessed by some time
`n ≤ k^d` at which the odometer covers the cube. -/
theorem ahg_exists_time_le {d : ℕ} {η : Site d → ℤ} {K : ℕ} {i : Fin d} {z : Site d}
    (h : crossingTime η K i z ≤ ((K ^ d : ℕ) : ℕ∞)) :
    ∃ n : ℕ, n ≤ K ^ d ∧ 1 ≤ n ∧ ∀ x ∈ cube d K, crossOdo η K i z n x = 1 := by
  have hlt : crossingTime η K i z < ((K ^ d + 1 : ℕ) : ℕ∞) :=
    lt_of_le_of_lt h (by exact_mod_cast Nat.lt_succ_self (K ^ d))
  unfold crossingTime at hlt
  obtain ⟨t, ⟨n, rfl, hn1, hcov⟩, hlt'⟩ := sInf_lt_iff.1 hlt
  have hnK : n < K ^ d + 1 := by exact_mod_cast hlt'
  exact ⟨n, by omega, hn1, hcov⟩

/-- A good cube for a constant background gives the strong box-crossing of its
translate `rboxShift (K, …, K) j`, at the deadline `∏ l, K = K ^ d`. -/
theorem ahg_strongly_box_of_good_cube {d : ℕ} (K : ℕ) (a : ℤ)
    (hG : GoodCube (fun _ : Site d => a) K) (j : Site d) :
    StronglyBoxCrossed (fun _ : Site d => a) (fun _ : Fin d => K) j := by
  unfold StronglyBoxCrossed
  intro i z hz x hx
  -- the translation vector: the tile `rboxShift` is the cube moved by `c`
  set c : Site d := fun l => -((K : ℤ) * j l) with hc
  have hrb : ∀ y : Site d, y ∈ rboxShift (fun _ : Fin d => K) j ↔ y + c ∈ cube d K := by
    intro y
    simp only [rboxShift, cube, hc, Set.mem_setOf_eq, Pi.add_apply]
    constructor
    · intro h l
      constructor <;> linarith [(h l).1, (h l).2]
    · intro h l
      constructor <;> linarith [(h l).1, (h l).2]
  have hline : ∀ y : Site d, y + c ∈ line d K i (z + c) ↔
      y ∈ rline (fun _ : Fin d => K) j i z := by
    intro y
    simp only [line, rline, hc, Set.mem_setOf_eq, Pi.add_apply]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by linarith, by linarith⟩, fun l hl => by linarith [h3 l hl]⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by linarith, by linarith⟩, fun l hl => by linarith [h3 l hl]⟩
  have hset : rboxShift (fun _ : Fin d => K) j = {y | y + c ∈ cube d K} := Set.ext hrb
  have hz' : z + c ∈ closureN (cube d K) := by
    rw [hset] at hz
    exact (ahg_closureN_shift (cube d K) c z).1 hz
  obtain ⟨n, hnK, _hn1, hcov⟩ := ahg_exists_time_le (hG i (z + c) hz')
  have hx' : x + c ∈ cube d K := (hrb x).1 hx
  -- the frozen odometer of the tile is the translate of the cube odometer
  have hfodo : ∀ (t : ℕ) (y : Site d),
      fodo ((rboxShift (fun _ : Fin d => K) j)ᶜ ∪ rline (fun _ : Fin d => K) j i z)
        (fun _ => a) (Set.indicator (rline (fun _ : Fin d => K) j i z) 1) t y
      = fodo ((cube d K)ᶜ ∪ line d K i (z + c)) (fun _ => a)
        (fun w => if w ∈ line d K i (z + c) then (1 : ℤ) else 0) t (y + c) := by
    intro t y
    have hS : {w : Site d | w + c ∈ (cube d K)ᶜ ∪ line d K i (z + c)} =
        (rboxShift (fun _ : Fin d => K) j)ᶜ ∪ rline (fun _ : Fin d => K) j i z := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff]
      rw [hrb w, ← hline w]
    have hw : (fun w : Site d => if w + c ∈ line d K i (z + c) then (1 : ℤ) else 0)
        = Set.indicator (rline (fun _ : Fin d => K) j i z) 1 := by
      funext w
      by_cases h : w ∈ rline (fun _ : Fin d => K) j i z
      · have h' := (hline w).2 h
        simp [h, h']
      · have h' : w + c ∉ line d K i (z + c) := fun h'' => h ((hline w).1 h'')
        simp [h, h']
    have hmain := fodo_shift ((cube d K)ᶜ ∪ line d K i (z + c)) (fun _ => a)
      (fun w => if w ∈ line d K i (z + c) then (1 : ℤ) else 0) c t y
    rw [hS, hw] at hmain
    exact hmain
  have hcross : (1 : ℤ) ≤ fodo ((cube d K)ᶜ ∪ line d K i (z + c)) (fun _ => a)
      (fun w => if w ∈ line d K i (z + c) then (1 : ℤ) else 0) (K ^ d) (x + c) := by
    have h1 : crossOdo (fun _ : Site d => a) K i (z + c) n (x + c) = 1 := hcov (x + c) hx'
    have hmono := aux_ct_propagate_fodo_mono_time ((cube d K)ᶜ ∪ line d K i (z + c))
      (fun _ => a) (fun w => if w ∈ line d K i (z + c) then (1 : ℤ) else 0) hnK (x + c)
    exact le_trans (le_of_eq h1.symm) hmono
  have hprod : (∏ l : Fin d, (fun _ : Fin d => K) l) = K ^ d := by simp
  rw [hprod, hfodo (K ^ d) x]
  exact hcross

/-- **H4 at the all-high Dirac law.** With singleton boxes `k ≡ 1`, every tile is
strongly box-crossed by the all-high background, uniformly in the translation `j`. -/
theorem all_high_strongly_box_crossing (d : ℕ) (hd : 2 ≤ d) :
    StronglyBoxCrossingHyp d (Measure.dirac (fun _ : Site d => 2 * (d : ℤ) - 1)) := by
  intro δ hδ
  refine ⟨fun _ : Fin d => 1, fun _ => Nat.one_pos, fun j => ?_⟩
  have hmem : (fun _ : Site d => 2 * (d : ℤ) - 1) ∈
      {η : Site d → ℤ | StronglyBoxCrossed η (fun _ : Fin d => 1) j} :=
    ahg_strongly_box_of_good_cube 1 _ (all_high_good_cube d hd 1) j
  rw [Measure.dirac_apply_of_mem hmem]
  exact ENNReal.ofReal_lt_one.2 (by linarith)

/-- **H5 at the all-high Dirac law.** The last-wave and ordinary arrival times are
finite everywhere and differ by at most one, so the `ε n` bound holds eventually. -/
theorem all_high_wave_approximation (d : ℕ) (hd : 2 ≤ d) :
    WaveApproximationHyp d (Measure.dirac (fun _ : Site d => 2 * (d : ℤ) - 1)) := by
  unfold WaveApproximationHyp
  rw [MeasureTheory.ae_dirac_eq]
  simp only [Filter.Eventually, Filter.mem_pure, Set.mem_setOf_eq]
  intro _hexp
  refine ⟨fun x => ?_, fun x => ?_, fun ε hε => ?_⟩
  · rw [all_high_last_arrival_eq d hd 0 x]
    exact ENat.coe_ne_top _
  · rw [all_high_arrival d hd x]
    exact ENat.coe_ne_top _
  · refine Filter.eventually_atTop.2 ⟨⌈1 / ε⌉₊, fun n hn x _ => ?_⟩
    rw [all_high_last_arrival_eq d hd 0 x, all_high_arrival d hd x, sub_zero,
      ENat.toNat_coe, ENat.toNat_coe]
    have hA : |((max 1 (mnorm x).toNat : ℕ) : ℝ) - (((mnorm x).toNat + 1 : ℕ) : ℝ)| ≤ 1 := by
      have h1 : max 1 (mnorm x).toNat ≤ (mnorm x).toNat + 1 :=
        max_le (by omega) (by omega)
      have h2 : (mnorm x).toNat + 1 ≤ max 1 (mnorm x).toNat + 1 :=
        Nat.succ_le_succ (Nat.le_max_right 1 _)
      have h1' : ((max 1 (mnorm x).toNat : ℕ) : ℝ) ≤ (((mnorm x).toNat + 1 : ℕ) : ℝ) := by
        exact_mod_cast h1
      have h2' : (((mnorm x).toNat + 1 : ℕ) : ℝ) ≤ ((max 1 (mnorm x).toNat : ℕ) : ℝ) + 1 := by
        exact_mod_cast h2
      rw [abs_le]
      constructor <;> linarith
    have hn' : 1 / ε ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    have hεn : 1 ≤ ε * n := by
      have := (div_le_iff₀ hε).1 hn'
      linarith [mul_comm ε (n : ℝ)]
    exact le_trans hA hεn

/-- **Common law at the all-high Dirac mass.** The same Dirac law `Q` is explosive
almost surely (`explosive_all_high_nonvacuity`), satisfies H4, and satisfies H5. -/
theorem all_high_common_law (d : ℕ) (hd : 2 ≤ d) :
    ExplosiveLaw d (Measure.dirac (fun _ : Site d => 2 * (d : ℤ) - 1)) ∧
      StronglyBoxCrossingHyp d (Measure.dirac (fun _ : Site d => 2 * (d : ℤ) - 1)) ∧
      WaveApproximationHyp d (Measure.dirac (fun _ : Site d => 2 * (d : ℤ) - 1)) := by
  refine ⟨?_, all_high_strongly_box_crossing d hd, all_high_wave_approximation d hd⟩
  obtain ⟨hpi, hexp, _⟩ := explosive_all_high_nonvacuity d hd
  unfold ExplosiveLaw
  rw [← hpi]
  exact hexp

end Exploding
