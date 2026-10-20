/-
The path-filling hypothesis (Hypothesis 3 of `paper/corrected-arxiv/exploding-corrected-arxiv.tex`) holds on the
all-high background in dimension two.

On the background `η ≡ 3 = 2d - 1`, a site outside the seed `A` topples as soon as one
neighbour carries a frozen-odometer chip: the threshold `2d = 4` is reached from the
background `3` plus the single unit contributed by that neighbour.  Hence the frozen
odometer started from the indicator of `A` is at least one at every site whose
Manhattan distance to `A` is at most the time, by induction on the time.

A path of `m` distinct points with consecutive points adjacent has coordinate spread at
most `m - 1` in each direction, so every point of its bounding rectangle lies within
Manhattan distance `2(m - 1)` of its first point.  Since `2(m - 1) ≤ m²`, the bound holds
at every time `t ≥ m²`.
-/
import Exploding.Support.Hypotheses
import Exploding.Support.SubGeom
import Exploding.Support.AllHighPodoFront
import LatticeProb.Lattice.PathBoundingRectangle

namespace Exploding

open LatticeProb MeasureTheory Filter

/-! ### Bounding rectangle of a path -/

/-- Every point of the bounding rectangle of a path of `m` consecutive adjacent sites is
within Manhattan distance `2(m - 1)` of the first site of the path. -/
theorem allHighPath_br_mnorm_le (z : ℕ → Site 2) (m : ℕ)
    (hadj : ∀ i, i + 1 < m → (lattice 2).Adj (z i) (z (i + 1))) {x : Site 2}
    (hx : x ∈ br (z '' {i : ℕ | i < m})) :
    ∃ a ∈ z '' {i : ℕ | i < m}, mnorm (x - a) ≤ 2 * ((m : ℤ) - 1) := by
  have hbox : ∀ c : Fin 2, (∃ i, i < m ∧ z i c ≤ x c) ∧ (∃ i, i < m ∧ x c ≤ z i c) := by
    intro c
    obtain ⟨⟨_, ⟨i, hi, rfl⟩, hyx⟩, ⟨_, ⟨i', hi', rfl⟩, hxy⟩⟩ := hx c
    exact ⟨⟨i, hi, hyx⟩, ⟨i', hi', hxy⟩⟩
  have hm : 0 < m := by
    obtain ⟨⟨i, hi, _⟩, _⟩ := hbox 0
    omega
  refine ⟨z 0, ⟨0, hm, rfl⟩, ?_⟩
  have hsum := LatticeProb.sum_abs_sub_le_of_walk_box z m hadj x hbox
  unfold mnorm
  rw [Fin.sum_univ_two] at hsum ⊢
  simp only [Pi.sub_apply]
  push_cast at hsum
  linarith

/-! ### Propagation of the frozen odometer on the all-high background -/

/-- A site off the seed that differs from a seed site has a neighbour one step nearer to
that seed site in Manhattan distance. -/
theorem allHighPath_neighbor_of_ne {x a : Site 2} (hxa : x ≠ a) :
    ∃ y : Site 2, (lattice 2).Adj x y ∧ mnorm (y - a) + 1 ≤ mnorm (x - a) := by
  obtain ⟨i, hi | hi⟩ := exists_mnorm_pred (sub_ne_zero.mpr hxa)
  · refine ⟨x - unit i, (adj_sub_unit x i).symm, ?_⟩
    have e : x - unit i - a = x - a - unit i := by abel
    rw [e]
    exact hi.2
  · refine ⟨x + unit i, (adj_add_unit x i).symm, ?_⟩
    have e : x + unit i - a = x - a + unit i := by abel
    rw [e]
    exact hi.2

/-- One step of the frozen odometer on the all-high background: a site off the seed with
a covered neighbour is covered at the next time. -/
theorem allHighPath_covered_of_adj (A : Set (Site 2)) (t : ℕ) {x y : Site 2}
    (hxA : x ∉ A) (hadj : (lattice 2).Adj x y)
    (hy : 1 ≤ fodo A (fun _ : Site 2 => (3 : ℤ)) (Set.indicator A 1) t y) :
    1 ≤ fodo A (fun _ : Site 2 => (3 : ℤ)) (Set.indicator A 1) (t + 1) x := by
  have hnn : ∀ z, 0 ≤ fodo A (fun _ : Site 2 => (3 : ℤ)) (Set.indicator A 1) t z :=
    fodo_nonneg_of_seed A _ _
      (fun z => by by_cases hz : z ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]) t
  have hsum := le_nbrSumZ_of_adj hnn hadj
  rw [fodo_succ, if_neg hxA]
  by_cases hw : 1 ≤ fodo A (fun _ : Site 2 => (3 : ℤ)) (Set.indicator A 1) t x
  · split_ifs <;> linarith [hnn x]
  · have h0 : fodo A (fun _ : Site 2 => (3 : ℤ)) (Set.indicator A 1) t x = 0 := by
      have := hnn x
      omega
    have hc : 2 * ((2 : ℕ) : ℤ) ≤ fconf A (fun _ : Site 2 => (3 : ℤ)) (Set.indicator A 1) t x := by
      show 2 * ((2 : ℕ) : ℤ) ≤
        (3 : ℤ) + lap (fodo A (fun _ : Site 2 => (3 : ℤ)) (Set.indicator A 1) t) x
      rw [lap, h0]
      push_cast
      linarith
    rw [if_pos hc]
    omega

/-- On the all-high background, the frozen odometer started from the indicator of `A` is
at least one at every site whose Manhattan distance to a seed site is at most the time. -/
theorem allHighPath_fodo_ge_one_of_mnorm_le (A : Set (Site 2)) (t : ℕ) :
    ∀ x a : Site 2, a ∈ A → mnorm (x - a) ≤ (t : ℤ) →
      1 ≤ fodo A (fun _ : Site 2 => (3 : ℤ)) (Set.indicator A 1) t x := by
  induction t with
  | zero =>
    intro x a ha hd
    by_cases hxA : x ∈ A
    · rw [fodo_of_mem A _ _ 0 hxA, Set.indicator_of_mem hxA]
      norm_num
    · exfalso
      obtain ⟨y, _, hy⟩ := allHighPath_neighbor_of_ne (x := x) (a := a)
        (fun h => hxA (by rw [h]; exact ha))
      have := mnorm_nonneg (y - a)
      push_cast at hd
      linarith
  | succ t ih =>
    intro x a ha hd
    by_cases hxA : x ∈ A
    · rw [fodo_of_mem A _ _ (t + 1) hxA, Set.indicator_of_mem hxA]
      norm_num
    · obtain ⟨y, hadj, hy⟩ := allHighPath_neighbor_of_ne (x := x) (a := a)
        (fun h => hxA (by rw [h]; exact ha))
      have hyd : mnorm (y - a) ≤ (t : ℤ) := by
        push_cast at hd
        linarith
      exact allHighPath_covered_of_adj A t hxA hadj (ih y a ha hyd)

/-! ### The path-filling hypothesis in dimension two -/

/-- On the all-high background `η ≡ 3` in dimension two, the path-filling hypothesis
holds: the frozen odometer started from the indicator of a path's point set is at least
one on its bounding rectangle at every time `t ≥ m²`, for every path of `m` consecutive
adjacent sites, with the constant `γ = 1` and `n₀ = 0`. -/
theorem all_high_path_filling_dim_two :
    PathFillingHyp 2 (Measure.dirac (fun _ : Site 2 => (3 : ℤ))) := by
  unfold PathFillingHyp
  refine ⟨1, one_pos, ?_⟩
  rw [ae_dirac_eq]
  refine Filter.eventually_pure.mpr ⟨0, fun n _ m z _ _ _ hadj t ht x hx => ?_⟩
  obtain ⟨a, ha, hd⟩ := allHighPath_br_mnorm_le z m hadj hx
  have h1 : 2 * ((m : ℤ) - 1) ≤ (m : ℤ) ^ 2 := by nlinarith [sq_nonneg ((m : ℤ) - 1)]
  have h2 : (m : ℤ) ^ 2 ≤ (t : ℤ) := by exact_mod_cast ht
  exact allHighPath_fodo_ge_one_of_mnorm_le _ t x a ha (le_trans hd (by linarith))

end Exploding
