/-
Proposition 5.1 of the paper (generalized last wave): the lighting of strongly box-crossing tiles
by the `N`-wave, and the finiteness of the last wave at every site.

Hypothesis 4 replaces the crossing time of good cubes: a lit line of a strongly box-crossing tile,
or of its outer boundary, lights the whole tile within `∏ k` steps.  Along a connected set of
strongly box-crossing tiles the lighting travels at `∏ k` steps per tile, and an infinite such set
makes every `N`-wave with `N` large non-stabilizable, since a wave has finite support at each time.
-/
import Exploding.Support.SquareLowerBoundExponential
import Exploding.Support.GLWSec3A
import Exploding.Support.LWCProof4
import Exploding.Support.PCloseProofPath
import Exploding.Support.ASProof

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

/-- **A lit line lights a strongly box-crossing tile.**  If the `N`-wave is positive at time `t`
on a line across the tile `B_k + j k`, or across its outer boundary, then it is positive on the
whole tile at time `t + ∏ k`. -/
theorem glws_tile_of_line (hd0 : (0 : ℤ) < 2 * (d : ℤ)) (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (N : ℕ) (hN : 1 ≤ N) (zc : Site d) (k : Fin d → ℕ) (j : Site d)
    (hgood : StronglyBoxCrossed η k j) (i : Fin d) (z : Site d)
    (hz : z ∈ closureN (rboxShift k j)) (t : ℕ)
    (hline : ∀ w ∈ rline k j i z, 0 < wave η N zc t w) :
    ∀ x ∈ rboxShift k j, 0 < wave η N zc (t + ∏ l, k l) x := by
  classical
  intro x hx
  set S : Set (Site d) := (rboxShift k j)ᶜ ∪ rline k j i z with hS
  set w0 : Site d → ℤ := Set.indicator (rline k j i z) 1 with hw0
  have hw0nn : ∀ x, 0 ≤ w0 x := by
    intro x
    by_cases h : x ∈ rline k j i z <;> simp [hw0, h]
  have hw0one : ∀ x, w0 x ≤ 1 := by
    intro x
    by_cases h : x ∈ rline k j i z <;> simp [hw0, h]
  have hw0le : ∀ x, w0 x ≤ wave η N zc t x := by
    intro x
    by_cases h : x ∈ rline k j i z
    · have h1 := hline x h
      simp only [hw0, Set.indicator_of_mem h, Pi.one_apply]
      omega
    · simp only [hw0, Set.indicator_of_notMem h]
      exact wave_nonneg η hlow N zc t x
  have hSdom : ∀ s : ℕ, ∀ x ∈ S, w0 x ≤ wave η N zc (t + s) x := fun s x _ =>
    le_trans (hw0le x) (wave_mono_time η hlow hd0 N zc (Nat.le_add_right t s) x)
  have hdom := wave_dom_fodo' hd0 S η hlow hhigh N hN zc t w0 hw0nn hw0one hw0le hSdom
    (∏ l, k l) x
  have h1 := hgood i z hz x hx
  exact lt_of_lt_of_le zero_lt_one (le_trans h1 hdom)

theorem glws_unit_apply (l m : Fin d) : (unit l : Site d) m = if m = l then 1 else 0 := by
  simp [unit, Pi.single_apply]

/-- **A line of a tile through the outer boundary lies in an adjacent tile.**  For adjacent
macroscopic sites `i, j` there are a direction and a point `z` of the closure of the tile of `j`
such that the line of the tile of `j` through `z` lies in the tile of `i`. -/
theorem glws_adj_line (hd : 2 ≤ d) (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (i j : Site d)
    (hij : (lattice d).Adj j i) :
    ∃ (dir' : Fin d) (z : Site d), z ∈ closureN (rboxShift k j) ∧
      ∀ w ∈ rline k j dir' z, w ∈ rboxShift k i := by
  obtain ⟨l, hl⟩ := hij
  obtain ⟨dir', hne⟩ := pub_exists_ne hd l
  have hk1 : ∀ m, (1 : ℤ) ≤ (k m : ℤ) := fun m => by exact_mod_cast hk m
  rcases hl with hl | hl
  · -- `i = j + unit l`: the tile of `i` lies above the tile of `j` in direction `l`
    refine ⟨dir', fun m => if m = l then (k l : ℤ) * j l + k l + 1 else 1 + (k m : ℤ) * j m,
      ?_, ?_⟩
    · refine Or.inr ⟨?_, fun m => if m = l then (k l : ℤ) * j l + k l else 1 + (k m : ℤ) * j m,
        ?_, ?_⟩
      · intro hcon
        have h := (hcon l).2
        simp only [if_true] at h
        linarith
      · intro m
        by_cases hm : m = l
        · simp only [hm, if_true]
          have := hk1 l
          constructor <;> linarith
        · simp only [hm, if_false]
          have := hk1 m
          constructor <;> linarith
      · refine ⟨l, Or.inr ?_⟩
        funext m
        by_cases hm : m = l
        · subst hm
          simp [glws_unit_apply]
        · simp [glws_unit_apply, hm]
    · intro w hw m
      have hi : i m = j m + (if m = l then 1 else 0) := by
        have := congrFun hl m
        simpa [glws_unit_apply] using this
      by_cases hmd : m = dir'
      · subst hmd
        have hml : m ≠ l := hne
        rw [hi, if_neg hml, add_zero]
        exact hw.1
      · have hwm : w m = if m = l then (k l : ℤ) * j l + k l + 1 else 1 + (k m : ℤ) * j m :=
          hw.2 m hmd
        have hkm := hk1 m
        by_cases hm : m = l
        · subst hm
          rw [hwm, hi]
          simp only [if_true]
          have : (k m : ℤ) * (j m + 1) = (k m : ℤ) * j m + k m := by ring
          rw [this]
          constructor <;> linarith
        · rw [hwm, hi]
          simp only [hm, if_false, add_zero]
          constructor <;> linarith
  · -- `j = i + unit l`: the tile of `i` lies below the tile of `j` in direction `l`
    refine ⟨dir', fun m => if m = l then (k l : ℤ) * j l else 1 + (k m : ℤ) * j m, ?_, ?_⟩
    · refine Or.inr ⟨?_, fun m => if m = l then (k l : ℤ) * j l + 1 else 1 + (k m : ℤ) * j m,
        ?_, ?_⟩
      · intro hcon
        have h := (hcon l).1
        simp only [if_true] at h
        linarith
      · intro m
        by_cases hm : m = l
        · simp only [hm, if_true]
          have := hk1 l
          constructor <;> linarith
        · simp only [hm, if_false]
          have := hk1 m
          constructor <;> linarith
      · refine ⟨l, Or.inl ?_⟩
        funext m
        by_cases hm : m = l
        · subst hm
          simp [glws_unit_apply]
        · simp [glws_unit_apply, hm]
    · intro w hw m
      have hj : j m = i m + (if m = l then 1 else 0) := by
        have := congrFun hl m
        simpa [glws_unit_apply] using this
      by_cases hmd : m = dir'
      · subst hmd
        have hml : m ≠ l := hne
        have hjm : j m = i m := by rw [hj, if_neg hml, add_zero]
        rw [← hjm]
        exact hw.1
      · have hwm : w m = if m = l then (k l : ℤ) * j l else 1 + (k m : ℤ) * j m :=
          hw.2 m hmd
        have hkm := hk1 m
        by_cases hm : m = l
        · subst hm
          rw [hwm]
          simp only [if_true]
          have hjm : j m = i m + 1 := by rw [hj]; simp
          rw [hjm]
          have : (k m : ℤ) * (i m + 1) = (k m : ℤ) * i m + k m := by ring
          rw [this]
          constructor <;> linarith
        · rw [hwm]
          simp only [hm, if_false]
          have hjm : j m = i m := by rw [hj, if_neg hm, add_zero]
          rw [hjm]
          constructor <;> linarith

/-- The tile of `j` is fully lit at time `T`: the `N`-wave from `zc` is positive on it. -/
def glws_Fired (η : Site d → ℤ) (N : ℕ) (k : Fin d → ℕ) (zc : Site d) (T : ℕ) (j : Site d) :
    Prop :=
  ∀ y ∈ rboxShift k j, 0 < wave η N zc T y

/-- A strongly box-crossing tile adjacent to a lit tile is lit within `∏ k` further steps. -/
theorem glws_tile_step (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (N : ℕ) (hN : 1 ≤ N) (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (zc i j : Site d)
    (hgood : StronglyBoxCrossed η k j) (hij : (lattice d).Adj j i) (T : ℕ)
    (hfired : glws_Fired η N k zc T i) : glws_Fired η N k zc (T + ∏ l, k l) j := by
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  obtain ⟨dir', z, hz, hline⟩ := glws_adj_line hd k hk i j hij
  exact glws_tile_of_line hd0 η hlow hhigh N hN zc k j hgood dir' z hz T
    (fun w hw => hfired w (hline w hw))

/-- Along a walk of strongly box-crossing tiles each step costs at most `∏ k`. -/
theorem glws_walk_fires (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (N : ℕ) (hN : 1 ≤ N) (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (zc : Site d) (m : ℕ)
    (c : ℕ → Site d) (hgood : ∀ s, s ≤ m → StronglyBoxCrossed η k (c s))
    (hadj : ∀ s, s < m → (lattice d).Adj (c s) (c (s + 1))) (T : ℕ)
    (h0 : glws_Fired η N k zc T (c 0)) :
    ∀ s, s ≤ m → glws_Fired η N k zc (T + s * ∏ l, k l) (c s) := by
  intro s
  induction s with
  | zero => intro _; simpa using h0
  | succ s ih =>
    intro hs
    have h1 := ih (by omega)
    have h2 := glws_tile_step hd η hlow hhigh N hN k hk zc (c s) (c (s + 1))
      (hgood (s + 1) hs) (hadj s (by omega)).symm _ h1
    have : T + s * ∏ l, k l + ∏ l, k l = T + (s + 1) * ∏ l, k l := by ring
    rwa [this] at h2

/-- A walk in the induced graph on `S` from `x` to `y` gives a sequence of adjacent points of
`S`. -/
theorem glws_walk_of_component {S : Set (Site d)} {x y : Site d} (h : y ∈ componentIn S x) :
    ∃ (m : ℕ) (c : ℕ → Site d), c 0 = x ∧ c m = y ∧ (∀ s, s ≤ m → c s ∈ S) ∧
      ∀ s, s < m → (lattice d).Adj (c s) (c (s + 1)) := by
  obtain ⟨hx, hy, hreach⟩ := h
  obtain ⟨w⟩ := hreach
  refine ⟨w.length, fun s => (w.getVert s).1, ?_, ?_, ?_, ?_⟩
  · simp
  · simp only
    rw [SimpleGraph.Walk.getVert_length]
  · intro s _
    exact (w.getVert s).2
  · intro s hs
    have := w.adj_getVert_succ hs
    simpa [SimpleGraph.induce_adj] using this

end Exploding

namespace Exploding

variable {d : ℕ}

/-- A tile is a finite set. -/
theorem glws_tile_finite (k : Fin d → ℕ) (j : Site d) : (rboxShift k j).Finite := by
  rw [show rboxShift k j = Set.univ.pi
      (fun i : Fin d => Set.Icc (1 + (k i : ℤ) * j i) ((k i : ℤ) * j i + (k i : ℤ))) from by
    ext x
    simp only [rboxShift, Set.mem_setOf_eq, Set.mem_univ_pi, Set.mem_Icc]]
  exact Set.Finite.pi (fun i => Set.finite_Icc _ _)

/-- The corner of a tile. -/
def glws_corner (k : Fin d → ℕ) (j : Site d) : Site d := fun l => 1 + (k l : ℤ) * j l

theorem glws_corner_mem (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (j : Site d) :
    glws_corner k j ∈ rboxShift k j := by
  intro l
  have : (1 : ℤ) ≤ (k l : ℤ) := by exact_mod_cast hk l
  simp only [glws_corner]
  constructor <;> linarith

theorem glws_corner_injective (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) :
    Function.Injective (glws_corner k) := by
  intro j j' h
  funext l
  have := congrFun h l
  simp only [glws_corner] at this
  have hkl : (k l : ℤ) ≠ 0 := by exact_mod_cast (hk l).ne'
  have h2 : (k l : ℤ) * j l = (k l : ℤ) * j' l := by linarith
  exact mul_left_cancel₀ hkl h2

/-- **The `N`-wave from any site lights a given tile**, for `N` large. -/
theorem glws_light_tile (hd : 2 ≤ d) (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (k : Fin d → ℕ) (y j : Site d) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ T : ℕ, glws_Fired η N k y T j := by
  classical
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  set R : ℕ := (∑ l : Fin d, ((k l) * ((j l).natAbs + 1) + (y l).natAbs)) + 1 with hR
  have hR1 : 1 ≤ R := by omega
  set N : ℕ := (2 * d) ^ (d * R) with hN
  have hN1 : 1 ≤ N := Nat.one_le_pow _ _ (by omega)
  refine ⟨N, hN1, ?_⟩
  set η' : Site d → ℤ := fun w => η (y + w) with hη'
  have hη'low : ∀ w, 0 ≤ η' w := fun w => hlow _
  have hcent : ∀ x ∈ rboxShift k j, x - y ∈ cent d R := by
    intro x hx l
    have hxl := hx l
    have hsum : (k l) * ((j l).natAbs + 1) + (y l).natAbs ≤
        ∑ l : Fin d, ((k l) * ((j l).natAbs + 1) + (y l).natAbs) :=
      Finset.single_le_sum (f := fun l : Fin d => (k l) * ((j l).natAbs + 1) + (y l).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
    have hkl : (0 : ℤ) ≤ (k l : ℤ) := Int.natCast_nonneg _
    have hjabs1 : j l ≤ |j l| := le_abs_self _
    have hjabs2 : -|j l| ≤ j l := neg_abs_le _
    have h1 : (k l : ℤ) * j l ≤ (k l : ℤ) * |j l| :=
      mul_le_mul_of_nonneg_left hjabs1 hkl
    have h2 : (k l : ℤ) * (-|j l|) ≤ (k l : ℤ) * j l :=
      mul_le_mul_of_nonneg_left hjabs2 hkl
    have hsum' : ((k l : ℤ)) * (|j l| + 1) + |y l| ≤ (R : ℤ) := by
      have : ((k l * ((j l).natAbs + 1) + (y l).natAbs : ℕ) : ℤ) ≤ (R : ℤ) := by
        exact_mod_cast (by omega : k l * ((j l).natAbs + 1) + (y l).natAbs ≤ R)
      push_cast at this
      exact this
    have hyabs : -|y l| ≤ y l ∧ y l ≤ |y l| := ⟨neg_abs_le _, le_abs_self _⟩
    rw [abs_le]
    simp only [Pi.sub_apply]
    constructor <;> nlinarith [hxl.1, hxl.2, hyabs.1, hyabs.2]
  have hfin := glws_tile_finite k j
  have hex : ∀ x ∈ rboxShift k j, ∃ t : ℕ, 0 < wave η N y t x := by
    intro x hx
    obtain ⟨t, ht⟩ := Exploding.square_lower_bound_exponential d hd η' hη'low R hR1 N le_rfl _
      (hcent x hx)
    refine ⟨t, ?_⟩
    have := lwc_wave_shift η y N 0 t (x - y)
    rw [add_zero, add_sub_cancel] at this
    rw [← this]
    exact ht
  choose! t ht using hex
  refine ⟨hfin.toFinset.sup t, fun x hx => ?_⟩
  have hle : t x ≤ hfin.toFinset.sup t := Finset.le_sup (f := t) (hfin.mem_toFinset.mpr hx)
  exact pclose_pos_mono hd0 η hlow N y hle (ht x hx)

/-- **Lemma 3.2 in the generalized setting.**  An infinite connected set of strongly box-crossing
tiles makes the last wave well defined at every site: some `N`-wave is not stabilizable. -/
theorem glws_finite_exploding (hd : 2 ≤ d) (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (k : Fin d → ℕ) (hk : ∀ i, 0 < k i)
    (Cinf : Set (Site d)) (hinf : Cinf.Infinite)
    (hgood : ∀ j ∈ Cinf, StronglyBoxCrossed η k j)
    (hconn : ∀ x ∈ Cinf, ∀ y ∈ Cinf, y ∈ componentIn Cinf x) (y : Site d) :
    ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n y := by
  classical
  obtain ⟨j0, hj0⟩ := hinf.nonempty
  obtain ⟨N, hN1, T0, h0⟩ := glws_light_tile hd η hlow k y j0
  refine ⟨N, hN1, ?_⟩
  rintro ⟨T, hT⟩
  -- every tile of `Cinf` is eventually lit
  have hlit : ∀ j' ∈ Cinf, ∃ T' : ℕ, glws_Fired η N k y T' j' := by
    intro j' hj'
    obtain ⟨m, c, hc0, hcm, hcS, hcadj⟩ := glws_walk_of_component (hconn j0 hj0 j' hj')
    have := glws_walk_fires hd η hlow hhigh N hN1 k hk y m c
      (fun s hs => hgood _ (hcS s hs)) hcadj T0 (by rw [hc0]; exact h0) m le_rfl
    rw [hcm] at this
    exact ⟨_, this⟩
  -- the support of the wave at time `T` is finite
  have hd0 : 0 < d := by omega
  set B : Set (Site d) := {x | mnorm (x - y) ≤ (T : ℤ)} with hB
  have hBfin : B.Finite := by
    refine as_coord_bdd_finite y (T : ℝ) B ?_
    intro x hx i
    have h1 : |x i - y i| ≤ mnorm (x - y) := by
      have := abs_coord_le_mnorm (x - y) i
      simpa using this
    have h2 : |x i - y i| ≤ (T : ℤ) := le_trans h1 hx
    exact_mod_cast h2
  have himg : (glws_corner k '' Cinf).Infinite := hinf.image (glws_corner_injective k hk).injOn
  obtain ⟨x, ⟨j', hj', rfl⟩, hxB⟩ := himg.exists_notMem_finite hBfin
  obtain ⟨T', hT'⟩ := hlit j' hj'
  have hpos : 0 < wave η N y T' (glws_corner k j') := hT' _ (glws_corner_mem k hk j')
  have hd0' : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  have hposmax : 0 < wave η N y (max T T') (glws_corner k j') :=
    pclose_pos_mono hd0' η hlow N y (le_max_right T T') hpos
  have heq : wave η N y (max T T') = wave η N y T := hT _ (le_max_left T T')
  rw [heq] at hposmax
  exact hxB (lwc4_wave_pos_mnorm_le hd0 η hlow hhigh N y T _ hposmax)

end Exploding
