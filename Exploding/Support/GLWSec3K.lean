/-
Proposition 5.1 of the paper (generalized last wave): the tools of the estimates of Section 3
run with Hypotheses 3 and 4 in place of the good cubes and local convexity.

* the support of the wave is connected to its centre by a path of distinct sites;
* a path of `m ≥ (log n)^γ` distinct sites lit by the wave lights its bounding rectangle `m^d`
  steps later (Hypothesis 3);
* a row of more than `(log n)^{5/2}` consecutive macroscopic sites meets `C_∞`;
* a lit bounding rectangle with a long side contains a line of a tile of `C_∞`, which lights the
  tile (Hypothesis 4); a lit tile of `C_∞` lights all of `C_∞`, so the wave cannot stabilize.
-/
import Exploding.Support.GLWSec3J

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

/-! ### Paths in the support of the wave -/

/-- **A site in the support of the wave is joined to its centre by a path of distinct sites in the
support** (the version of `pclose_path_extract` with an arbitrary centre). -/
theorem glws_path_extract (η : Site d → ℤ) (hlow : ∀ y, 0 ≤ η y)
    (hhigh : ∀ y, η y ≤ 2 * (d : ℤ) - 1) (hd0 : (0 : ℤ) < 2 * (d : ℤ))
    (N : ℕ) (zc : Site d) :
    ∀ s : ℕ, ∀ y : Site d, 0 < wave η N zc s y →
      ∃ (m : ℕ) (z : ℕ → Site d), z 0 = zc ∧ z m = y ∧
        (∀ i, i < m → (lattice d).Adj (z i) (z (i + 1))) ∧
        (∀ i j, i ≤ m → j ≤ m → z i = z j → i = j) ∧
        ∀ i, i ≤ m → 0 < wave η N zc s (z i) := by
  intro s
  induction s with
  | zero =>
    intro y hy
    have hy0 : y = zc := by
      by_contra hne
      rw [wave_zero, if_neg hne] at hy
      exact lt_irrefl _ hy
    subst hy0
    refine ⟨0, fun _ => y, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i), ?_, ?_⟩
    · intro i j hi hj _
      omega
    · intro i _
      exact hy
  | succ s ih =>
    intro y hy
    by_cases hps : 0 < wave η N zc s y
    · obtain ⟨m, z, h0, hm, hadj, hinj, hpos⟩ := ih y hps
      exact ⟨m, z, h0, hm, hadj, hinj, fun i hi =>
        pclose_pos_mono hd0 η hlow N zc (Nat.le_succ s) (hpos i hi)⟩
    · have hy0 : y ≠ zc := by
        intro h0
        subst h0
        rw [wave_at_centre] at hy hps
        exact hps hy
      rw [wave_of_ne η N zc y s hy0] at hy
      have h1 : (1 : ℤ) ≤ (nbrSumZ (wave η N zc s) y + η y) / (2 * (d : ℤ)) := hy
      rw [Int.le_ediv_iff_mul_le hd0] at h1
      have hS : 0 < nbrSumZ (wave η N zc s) y := by linarith [hhigh y]
      obtain ⟨y', hadj', hy'pos⟩ :=
        exists_adj_pos_of_nbrSumZ_pos _ (wave_nonneg η hlow N zc s) y hS
      obtain ⟨m, z, h0, hm, hadj, hinj, hpos⟩ := ih y' hy'pos
      refine ⟨m + 1, fun i => if i ≤ m then z i else y, ?_, ?_, ?_, ?_, ?_⟩
      · simpa using h0
      · simp
      · intro i hi
        by_cases him : i < m
        · have h1 : i ≤ m := le_of_lt him
          have h2 : i + 1 ≤ m := him
          simpa [h1, h2] using hadj i him
        · have him' : i = m := by omega
          subst him'
          simp only [le_refl, if_true, Nat.lt_irrefl, Nat.succ_le_iff]
          simp only [if_false]
          rw [hm]
          exact hadj'
      · intro i j hi hj hij
        by_cases hi' : i ≤ m <;> by_cases hj' : j ≤ m
        · simp only [hi', hj', if_true] at hij
          exact hinj i j hi' hj' hij
        · simp only [hi', hj', if_true, if_false] at hij
          exfalso
          have := hpos i hi'
          rw [hij] at this
          exact hps this
        · simp only [hi', hj', if_true, if_false] at hij
          exfalso
          have := hpos j hj'
          rw [← hij] at this
          exact hps this
        · omega
      · intro i hi
        by_cases hi' : i ≤ m
        · simp only [hi', if_true]
          exact pclose_pos_mono hd0 η hlow N zc (Nat.le_succ s) (hpos i hi')
        · simp only [hi', if_false]
          rw [wave_of_ne η N zc y s hy0]
          exact (Int.le_ediv_iff_mul_le hd0).mpr (by linarith [hhigh y] : (1 : ℤ) * (2 * (d : ℤ)) ≤ _)

/-- Adjacent sites differ by at most one in every coordinate. -/
theorem glws_adj_coord {a b : Site d} (h : (lattice d).Adj a b) (l : Fin d) :
    |b l - a l| ≤ 1 := by
  obtain ⟨i, hi | hi⟩ := h
  · have := congrFun hi l
    simp only [Pi.add_apply, glws_unit_apply] at this
    by_cases hl : l = i
    · subst hl
      simp only [if_true] at this
      rw [this]; simp
    · simp only [hl, if_false, add_zero] at this
      rw [this]; simp
  · have := congrFun hi l
    simp only [Pi.add_apply, glws_unit_apply] at this
    by_cases hl : l = i
    · subst hl
      simp only [if_true] at this
      rw [this]; simp
    · simp only [hl, if_false, add_zero] at this
      rw [this]; simp

/-- Along a path of adjacent sites the coordinates move by at most one per step. -/
theorem glws_path_coord {m : ℕ} (z : ℕ → Site d) (hadj : ∀ i, i < m → (lattice d).Adj (z i) (z (i + 1)))
    (l : Fin d) : ∀ q, q ≤ m → |z q l - z 0 l| ≤ q := by
  intro q
  induction q with
  | zero => intro _; simp
  | succ q ih =>
    intro hq
    have h1 := ih (by omega)
    have h2 := glws_adj_coord (hadj q (by omega)) l
    have h3 : |z (q + 1) l - z 0 l| ≤ |z (q + 1) l - z q l| + |z q l - z 0 l| := by
      have := abs_add_le (z (q + 1) l - z q l) (z q l - z 0 l)
      simpa using this
    push_cast
    linarith

/-! ### Filling the bounding rectangle of a lit path (Hypothesis 3) -/

/-- **A lit path of distinct sites lights its bounding rectangle.**  If the `N`-wave is positive
at time `t` on `m ≥ (log n)^γ` distinct sites of a path in `[-n,n]^d`, it is positive on the
bounding rectangle of the path at time `t + m^d`.  The threshold in `n` does not depend on the
wave. -/
theorem glws_pf_fill (d : ℕ) (γp : ℝ) (η : Site d → ℤ) (hd0 : (0 : ℤ) < 2 * (d : ℤ))
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (hpf : glws_PF d γp η) :
    ∃ n0 : ℕ, ∀ (N : ℕ), 1 ≤ N → ∀ (zc : Site d) (n : ℕ), n0 ≤ n → ∀ (m : ℕ) (z : ℕ → Site d),
      Real.log n ^ γp ≤ (m : ℝ) → (∀ i, i < m → z i ∈ cent d n) →
      (∀ i j, i < m → j < m → z i = z j → i = j) →
      (∀ i, i + 1 < m → (lattice d).Adj (z i) (z (i + 1))) →
      ∀ t : ℕ, (∀ i, i < m → 0 < wave η N zc t (z i)) →
        ∀ x ∈ br (z '' {i : ℕ | i < m}), 0 < wave η N zc (t + m ^ d) x := by
  classical
  obtain ⟨n0, hn0⟩ := hpf
  refine ⟨n0, fun N hN zc n hn m z hm hz hinj hadj t hlit x hx => ?_⟩
  set S : Set (Site d) := z '' {i : ℕ | i < m} with hS
  have hPF := hn0 n hn m z hm hz hinj hadj (m ^ d) le_rfl x hx
  have hw0nn : ∀ x, 0 ≤ Set.indicator S (1 : Site d → ℤ) x := by
    intro x
    by_cases h : x ∈ S <;> simp [h]
  have hw0one : ∀ x, Set.indicator S (1 : Site d → ℤ) x ≤ 1 := by
    intro x
    by_cases h : x ∈ S <;> simp [h]
  have hw0le : ∀ x, Set.indicator S (1 : Site d → ℤ) x ≤ wave η N zc t x := by
    intro x
    by_cases h : x ∈ S
    · obtain ⟨i, hi, rfl⟩ := h
      have h1 := hlit i hi
      simp only [Set.indicator_of_mem (show z i ∈ S from ⟨i, hi, rfl⟩), Pi.one_apply]
      omega
    · simp only [Set.indicator_of_notMem h]
      exact wave_nonneg η hlow N zc t x
  have hSdom : ∀ s : ℕ, ∀ x ∈ S, Set.indicator S (1 : Site d → ℤ) x ≤ wave η N zc (t + s) x :=
    fun s x _ => le_trans (hw0le x) (wave_mono_time η hlow hd0 N zc (Nat.le_add_right t s) x)
  have hdom := wave_dom_fodo' hd0 S η hlow hhigh N hN zc t _ hw0nn hw0one hw0le hSdom (m ^ d) x
  exact lt_of_lt_of_le zero_lt_one (le_trans hPF hdom)

/-! ### A lit tile of `C_∞` makes the wave non-stabilizable -/

/-- If some tile of the infinite connected set `C_∞` is lit by the `N`-wave, the wave is not
stabilizable: all of `C_∞` is lit eventually, and a wave has finite support at every time. -/
theorem glws_not_stab_of_fired (hd : 2 ≤ d) (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (k : Fin d → ℕ) (hk : ∀ i, 0 < k i)
    (Cinf : Set (Site d)) (hinf : Cinf.Infinite)
    (hgood : ∀ j ∈ Cinf, StronglyBoxCrossed η k j)
    (hconn : ∀ x ∈ Cinf, ∀ y ∈ Cinf, y ∈ componentIn Cinf x)
    (N : ℕ) (hN1 : 1 ≤ N) (zc : Site d) {j0 : Site d} (hj0 : j0 ∈ Cinf) {T0 : ℕ}
    (h0 : glws_Fired η N k zc T0 j0) : ¬ WaveStabilizable η N zc := by
  classical
  rintro ⟨T, hT⟩
  have hlit : ∀ j' ∈ Cinf, ∃ T' : ℕ, glws_Fired η N k zc T' j' := by
    intro j' hj'
    obtain ⟨m, c, hc0, hcm, hcS, hcadj⟩ := glws_walk_of_component (hconn j0 hj0 j' hj')
    have := glws_walk_fires hd η hlow hhigh N hN1 k hk zc m c
      (fun s hs => hgood _ (hcS s hs)) hcadj T0 (by rw [hc0]; exact h0) m le_rfl
    rw [hcm] at this
    exact ⟨_, this⟩
  have hd0 : 0 < d := by omega
  set B : Set (Site d) := {x | mnorm (x - zc) ≤ (T : ℤ)} with hB
  have hBfin : B.Finite := by
    refine as_coord_bdd_finite zc (T : ℝ) B ?_
    intro x hx i
    have h1 : |x i - zc i| ≤ mnorm (x - zc) := by
      have := abs_coord_le_mnorm (x - zc) i
      simpa using this
    have h2 : |x i - zc i| ≤ (T : ℤ) := le_trans h1 hx
    exact_mod_cast h2
  have himg : (glws_corner k '' Cinf).Infinite := hinf.image (glws_corner_injective k hk).injOn
  obtain ⟨x, ⟨j', hj', rfl⟩, hxB⟩ := himg.exists_notMem_finite hBfin
  obtain ⟨T', hT'⟩ := hlit j' hj'
  have hpos : 0 < wave η N zc T' (glws_corner k j') := hT' _ (glws_corner_mem k hk j')
  have hd0' : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  have hposmax : 0 < wave η N zc (max T T') (glws_corner k j') :=
    pclose_pos_mono hd0' η hlow N zc (le_max_right T T') hpos
  have heq : wave η N zc (max T T') = wave η N zc T := hT _ (le_max_left T T')
  rw [heq] at hposmax
  exact hxB (lwc4_wave_pos_mnorm_le hd0 η hlow hhigh N zc T _ hposmax)

end Exploding
