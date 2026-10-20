/-
Support for Lemma 3.6 of `paper/corrected-arxiv/exploding-corrected-arxiv.tex`: the last wave is a connected,
monotone, bounded process; a good cube converts a lit line, or a lit adjacent cube, into a lit
cube within `k^d` steps, for every wave mass `N ≥ 1`; a walk of good cubes carries a lit cube
along it at `k^d` steps per edge; and a finite region whose outer boundary is lit is lit.
-/
import Exploding.Support.Vocab
import Exploding.Support.Wave
import Exploding.Support.SubGeom
import Exploding.Support.SubFodo
import Exploding.Support.SubStep
import Exploding.Support.SubCross
import Exploding.Support.SubFinite
import Exploding.Support.SubPen
import Exploding.Support.SubPub
import Exploding.Support.ReductionShift
import Exploding.Frozen.LocalConvexity

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-! ### The support of the wave is connected to the centre -/

/-- A site on which the `N`-wave is positive at time `t` is joined to the centre by a path of
sites on which the wave is positive at time `t`. -/
theorem pub_wave_path (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (N : ℕ) :
    ∀ (t : ℕ) (x : Site d), 0 < wave η N (0 : Site d) t x →
      ∃ (m : ℕ) (z : ℕ → Site d), z 0 = 0 ∧ z m = x ∧
        (∀ i, i < m → (lattice d).Adj (z i) (z (i + 1))) ∧
        ∀ i, i ≤ m → 0 < wave η N (0 : Site d) t (z i) := by
  intro t
  induction t with
  | zero =>
    intro x hx
    have hx0 : x = 0 := by
      by_contra hne
      rw [wave_zero] at hx
      simp [hne] at hx
    subst hx0
    exact ⟨0, fun _ => 0, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i),
      fun i _ => hx⟩
  | succ t ih =>
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      exact ⟨0, fun _ => 0, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i), fun i _ => hx⟩
    · have hx' := hx
      rw [wave_of_ne η N 0 x t hx0] at hx'
      have h1 : 1 ≤ (nbrSumZ (wave η N (0 : Site d) t) x + η x) / (2 * (d : ℤ)) := by omega
      have hdpos : (0 : ℤ) < 2 * (d : ℤ) := by
        rcases Nat.eq_zero_or_pos d with h0 | hpos
        · exfalso
          apply hx0
          subst h0
          exact funext fun i => i.elim0
        · have : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hpos
          linarith
      rw [Int.le_ediv_iff_mul_le hdpos] at h1
      have hsum : 0 < nbrSumZ (wave η N (0 : Site d) t) x := by
        linarith [hhigh x]
      obtain ⟨y, hyadj, hypos⟩ :=
        exists_adj_pos_of_nbrSumZ_pos _ (fun y => wave_nonneg η hlow N 0 t y) x hsum
      obtain ⟨m, z, h0, hm, hadj, hpos⟩ := ih y hypos
      have hmono : ∀ w : Site d, 0 < wave η N (0 : Site d) t w →
          0 < wave η N (0 : Site d) (t + 1) w := fun w hw =>
        lt_of_lt_of_le hw (wave_mono_t η hlow (by linarith) N 0 t w)
      refine ⟨m + 1, fun i => if i = m + 1 then x else z i, ?_, ?_, ?_, ?_⟩
      · have : (0 : ℕ) ≠ m + 1 := by omega
        simp [h0]
      · simp
      · intro i hi
        by_cases him : i = m
        · subst him
          have h3 : i ≠ i + 1 := by omega
          simp only [hm, if_true, h3, if_false]
          exact hyadj
        · have h1 : i ≠ m + 1 := by omega
          have h2 : i + 1 ≠ m + 1 := by omega
          simp only [h1, h2, if_false]
          exact hadj i (by omega)
      · intro i hi
        by_cases him : i = m + 1
        · simp [him, hx]
        · simp only [him, if_false]
          exact hmono _ (hpos i (by omega))

/-! ### The crossing odometer of a good cube, dominated by the wave for every mass `N ≥ 1` -/

/-- The wave dominates the frozen odometer of a good cube once the frozen line is lit, for
every mass `N ≥ 1`, including the case where the wave's centre lies in the cube. -/
theorem pub_crossOdo_le_wave (hd0 : (0 : ℤ) < 2 * (d : ℤ))
    (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (N k : ℕ) (hN : 1 ≤ N) (zc j : Site d) (dir' : Fin d) (z : Site d) (t : ℕ)
    (hseed : ∀ y ∈ line d k dir' z, 0 < wave η N zc t (y + (k : ℤ) • j)) :
    ∀ s y, crossOdo (fun x => η (x + (k : ℤ) • j)) k dir' z s y ≤
      wave η N zc (t + s) (y + (k : ℤ) • j) := by
  classical
  intro s y
  set c : Site d := (k : ℤ) • j with hc
  unfold crossOdo
  have hshift := fodo_shift {u : Site d | u - c ∈ (cube d k)ᶜ ∪ line d k dir' z} η
    (fun u => if u - c ∈ line d k dir' z then (1 : ℤ) else 0) c s y
  have e1 : {u : Site d | u + c ∈ {u : Site d | u - c ∈ (cube d k)ᶜ ∪ line d k dir' z}} =
      (cube d k)ᶜ ∪ line d k dir' z := by
    ext u
    simp
  have e2 : (fun u : Site d => (fun u : Site d => if u - c ∈ line d k dir' z then (1 : ℤ) else 0)
      (u + c)) = fun x => if x ∈ line d k dir' z then 1 else 0 := by
    funext u
    simp
  rw [e1, e2] at hshift
  rw [hshift]
  refine wave_dom_fodo' hd0 _ η hlow hhigh N hN zc t
    (fun u => if u - c ∈ line d k dir' z then (1 : ℤ) else 0) ?_ ?_ ?_ ?_ s (y + c)
  · intro x; split_ifs <;> norm_num
  · intro x; split_ifs <;> norm_num
  · intro x
    by_cases hx : x - c ∈ line d k dir' z
    · simp only [if_pos hx]
      have := hseed (x - c) hx
      rw [sub_add_cancel] at this
      exact this
    · simp only [if_neg hx]
      exact wave_nonneg η hlow N zc t x
  · intro s' x _
    by_cases hx : x - c ∈ line d k dir' z
    · simp only [if_pos hx]
      have := hseed (x - c) hx
      rw [sub_add_cancel] at this
      have h1 : 1 ≤ wave η N zc t x := by omega
      exact le_trans h1 (wave_mono_time η hlow hd0 N zc (Nat.le_add_right t s') x)
    · simp only [if_neg hx]
      exact wave_nonneg η hlow N zc (t + s') x

/-- A lit line of a good cube lights the cube within `k^d` steps. -/
theorem pub_cover_of_line (hd0 : (0 : ℤ) < 2 * (d : ℤ))
    (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (N k : ℕ) (hN : 1 ≤ N) (zc j : Site d) (hgood : GoodAt η k j) (dir' : Fin d) (z : Site d)
    (hz : z ∈ closureN (cube d k)) (t : ℕ)
    (hline : ∀ w ∈ line d k dir' z, 0 < wave η N zc t (w + (k : ℤ) • j)) :
    ∀ x ∈ cube d k, 0 < wave η N zc (t + k ^ d) (x + (k : ℤ) • j) := by
  obtain ⟨n, hn, hcross⟩ := exists_crossOdo_eq_one_of_goodCube
    (fun x => η (x + (k : ℤ) • j)) k hgood dir' hz
  intro x hx
  have hdom := pub_crossOdo_le_wave hd0 η hlow hhigh N k hN zc j dir' z t hline n x
  have h1 := hcross x hx
  rw [h1] at hdom
  exact lt_of_lt_of_le (by norm_num) (le_trans hdom
    (wave_mono_time η hlow hd0 N zc (by omega : t + n ≤ t + k ^ d) _))


/-- The cube lit from a line of it lying in a cube already lit: the abstract form of the step
between adjacent cubes.  The line is read in `Q_k(j)`'s coordinates, and `v` carries it into
`Q_k(i)`'s. -/
theorem pub_cover_step_gen (hd0 : (0 : ℤ) < 2 * (d : ℤ))
    (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (N k : ℕ) (hN : 1 ≤ N) (zc i j : Site d) (hgood : GoodAt η k j) (dir' : Fin d)
    (z v : Site d) (hz : z ∈ closureN (cube d k)) (hv : (k : ℤ) • j = (k : ℤ) • i + v)
    (hmem : ∀ w ∈ line d k dir' z, w + v ∈ cube d k) (t : ℕ)
    (hcover : ∀ x ∈ cube d k, 0 < wave η N zc t (x + (k : ℤ) • i)) :
    ∀ x ∈ cube d k, 0 < wave η N zc (t + k ^ d) (x + (k : ℤ) • j) := by
  refine pub_cover_of_line hd0 η hlow hhigh N k hN zc j hgood dir' z hz t ?_
  intro w hw
  have h1 := hcover (w + v) (hmem w hw)
  have h2 : w + v + (k : ℤ) • i = w + (k : ℤ) • j := by rw [hv]; abel
  rw [h2] at h1
  exact h1

theorem pub_exists_ne (hd : 2 ≤ d) (dir : Fin d) : ∃ dir' : Fin d, dir' ≠ dir := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have hcard : Fintype.card (Fin d) = 1 := Fintype.card_eq_one_iff.mpr ⟨dir, hcon⟩
  rw [Fintype.card_fin] at hcard
  omega

/-- **One edge of a walk of good cubes.**  If `Q_k(i)` is lit at time `t` and `Q_k(j)` is a good
neighbouring cube, then `Q_k(j)` is lit at time `t + k^d`. -/
theorem pub_cover_step (hd : 2 ≤ d)
    (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (N k : ℕ) (hk : 1 ≤ k) (hN : 1 ≤ N) (zc i j : Site d) (hgood : GoodAt η k j)
    (hadj : (lattice d).Adj i j) (t : ℕ)
    (hcover : ∀ x ∈ cube d k, 0 < wave η N zc t (x + (k : ℤ) • i)) :
    ∀ x ∈ cube d k, 0 < wave η N zc (t + k ^ d) (x + (k : ℤ) • j) := by
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  obtain ⟨dir, hdir⟩ := hadj
  obtain ⟨dir', hne⟩ := pub_exists_ne hd dir
  have hu1 : (unit dir : Site d) dir = 1 := by simp [unit]
  have hu0 : ∀ l : Fin d, l ≠ dir → (unit dir : Site d) l = 0 := fun l hl => by
    simp [unit, Pi.single_eq_of_ne hl]
  rcases hdir with hj | hi
  · -- `j = i + e_dir`
    have hz : (fun l : Fin d => if l = dir then (0 : ℤ) else 1) ∈ closureN (cube d k) := by
      refine Or.inr ⟨?_, (fun l : Fin d => if l = dir then (0 : ℤ) else 1) + unit dir, ?_, ?_⟩
      · intro h
        have := (h dir).1
        simp at this
      · intro l
        by_cases hl : l = dir
        · subst hl
          simp [hu1]
          first | exact hk1 | exact hk
        · simp [hl, hu0 l hl]
          first | exact hk1 | exact hk
      · exact ⟨dir, Or.inl rfl⟩
    refine pub_cover_step_gen hd0 η hlow hhigh N k hN zc i j hgood dir'
      (fun l : Fin d => if l = dir then (0 : ℤ) else 1) ((k : ℤ) • unit dir) hz ?_ ?_ t hcover
    · rw [hj, smul_add]
    · intro w hw l
      by_cases hl : l = dir'
      · subst hl
        have := hw.1
        simp [hu0 l hne]
        exact this
      · have h2 := hw.2 l hl
        by_cases hld : l = dir
        · subst hld
          simp at h2
          simp [h2, hu1]
          first | exact hk1 | exact hk
        · simp [hld] at h2
          simp [h2, hu0 l hld]
          first | exact hk1 | exact hk
  · -- `i = j + e_dir`
    have hz : (fun l : Fin d => if l = dir then (k : ℤ) + 1 else 1) ∈ closureN (cube d k) := by
      refine Or.inr ⟨?_, (fun l : Fin d => if l = dir then (k : ℤ) + 1 else 1) - unit dir, ?_, ?_⟩
      · intro h
        have := (h dir).2
        simp at this
      · intro l
        by_cases hl : l = dir
        · subst hl
          simp [hu1]
          first | exact hk1 | exact hk
        · simp [hl, hu0 l hl]
          first | exact hk1 | exact hk
      · exact ⟨dir, Or.inr (by abel)⟩
    refine pub_cover_step_gen hd0 η hlow hhigh N k hN zc i j hgood dir'
      (fun l : Fin d => if l = dir then (k : ℤ) + 1 else 1) (-((k : ℤ) • unit dir)) hz ?_ ?_ t hcover
    · rw [hi, smul_add]; abel
    · intro w hw l
      by_cases hl : l = dir'
      · subst hl
        have := hw.1
        simp [hu0 l hne]
        exact this
      · have h2 := hw.2 l hl
        by_cases hld : l = dir
        · subst hld
          simp at h2
          simp [h2, hu1]
          first | exact hk1 | exact hk
        · simp [hld] at h2
          simp [h2, hu0 l hld]
          first | exact hk1 | exact hk

/-- Lit cubes stay lit. -/
theorem pub_cover_mono (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hd0 : (0 : ℤ) < 2 * (d : ℤ)) (N k : ℕ) (zc i : Site d) {s t : ℕ} (hst : s ≤ t)
    (h : ∀ x ∈ cube d k, 0 < wave η N zc s (x + (k : ℤ) • i)) :
    ∀ x ∈ cube d k, 0 < wave η N zc t (x + (k : ℤ) • i) := fun x hx =>
  lt_of_lt_of_le (h x hx) (wave_mono_time η hlow hd0 N zc hst _)

/-- **A walk of good cubes carries a lit cube along it**, at `k^d` steps per edge. -/
theorem pub_cover_walk (hd : 2 ≤ d)
    (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (N k : ℕ) (hk : 1 ≤ k) (hN : 1 ≤ N) (zc : Site d) (C : Set (Site d))
    (hC : C ⊆ goodSites η k) {a b : C} (p : ((lattice d).induce C).Walk a b) :
    ∀ t : ℕ, (∀ x ∈ cube d k, 0 < wave η N zc t (x + (k : ℤ) • (a : Site d))) →
      ∀ x ∈ cube d k, 0 < wave η N zc (t + p.length * k ^ d) (x + (k : ℤ) • (b : Site d)) := by
  induction p with
  | nil =>
    intro t h
    simpa using h
  | @cons u v w h p ih =>
    intro t ht
    have hstep := pub_cover_step hd η hlow hhigh N k hk hN zc (u : Site d) (v : Site d)
      (hC v.2) (SimpleGraph.induce_adj.mp h) t ht
    have := ih (t + k ^ d) hstep
    rw [SimpleGraph.Walk.length_cons]
    have e : t + (p.length + 1) * k ^ d = t + k ^ d + p.length * k ^ d := by ring
    rw [e]
    exact this

/-! ### A path of lit sites lights its bounding rectangle -/

/-- **A lit path lights its bounding rectangle** (`Exploding.Frozen.local_convexity`, read through
the domination of the frozen odometer by the wave). -/
theorem pub_rect_lit (hd : 2 ≤ d) (η : Site d → ℤ) (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (N : ℕ) (hN : 1 ≤ N) (t : ℕ) (m : ℕ) (z : ℕ → Site d)
    (hpath : ∀ i : ℕ, i < m → (lattice d).Adj (z i) (z (i + 1)))
    (hpos : ∀ i : ℕ, i ≤ m → 0 < wave η N (0 : Site d) t (z i)) :
    ∃ τ : ℕ, ∀ x ∈ br (z '' {i : ℕ | i ≤ m}), 0 < wave η N (0 : Site d) τ x := by
  classical
  have hd2 : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by linarith
  have hlow0 : ∀ x, 0 ≤ η x := fun x => by linarith [hlow x]
  set A : Set (Site d) := z '' {i : ℕ | i ≤ m} with hA
  have hAfin : A.Finite := Set.Finite.image _ (Set.finite_Iic m)
  have hfin : (br A).Finite := br_finite A hAfin
  refine ⟨t + hfin.toFinset.card, fun x hx => ?_⟩
  have hAlit : ∀ y ∈ A, 0 < wave η N (0 : Site d) t y := by
    rintro y ⟨i, hi, rfl⟩
    exact hpos i hi
  have hdom := wave_dom_fodo' hd0 A η hlow0 hhigh N hN 0 t (Set.indicator A 1)
    (fun x => by by_cases hx : x ∈ A <;> simp [hx])
    (fun x => by by_cases hx : x ∈ A <;> simp [hx])
    (fun x => by
      by_cases hx : x ∈ A
      · simp only [Set.indicator_of_mem hx, Pi.one_apply]
        have := hAlit x hx
        omega
      · simp only [Set.indicator_of_notMem hx]
        exact wave_nonneg η hlow0 N 0 t x)
    (fun s' x hx => by
      simp only [Set.indicator_of_mem hx, Pi.one_apply]
      have := hAlit x hx
      have h1 : 1 ≤ wave η N (0 : Site d) t x := by omega
      exact le_trans h1 (wave_mono_time η hlow0 hd0 N 0 (Nat.le_add_right t s') x))
    hfin.toFinset.card x
  have hconv := Exploding.Frozen.local_convexity d hd η hlow hhigh m z hpath A hA hfin
    hfin.toFinset.card le_rfl x hx
  rw [hconv] at hdom
  omega

/-! ### A finite region whose outer boundary is lit is lit -/

/-- The coordinate sum. -/
def pub_sigma (x : Site d) : ℤ := ∑ l, x l

theorem pub_sigma_add_unit (x : Site d) (l : Fin d) : pub_sigma (x + unit l) = pub_sigma x + 1 := by
  simp only [pub_sigma, Pi.add_apply, Finset.sum_add_distrib]
  congr 1
  simp [unit]

/-- If the `d ≥ 2` upper neighbours of a site are lit then the site is lit at the next step. -/
theorem pub_lit_of_up (hd : 2 ≤ d) (η : Site d → ℤ) (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x)
    (N : ℕ) (hN : 1 ≤ N) (zc : Site d) (t : ℕ) (y : Site d)
    (hup : ∀ l : Fin d, 0 < wave η N zc t (y + unit l)) :
    0 < wave η N zc (t + 1) y := by
  have hd2 : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by linarith
  have hlow0 : ∀ x, 0 ≤ η x := fun x => by linarith [hlow x]
  by_cases hy : y = zc
  · subst hy
    rw [wave_at_centre]
    exact_mod_cast hN
  · rw [wave_of_ne η N zc y t hy]
    have hsum : (d : ℤ) ≤ nbrSumZ (wave η N zc t) y := by
      have h1 : ∑ _l : Fin d, (1 : ℤ) ≤ ∑ l : Fin d, (wave η N zc t (y + unit l) +
          wave η N zc t (y - unit l)) := by
        refine Finset.sum_le_sum fun l _ => ?_
        have := hup l
        have h2 := wave_nonneg η hlow0 N zc t (y - unit l)
        omega
      simpa [nbrSumZ] using h1
    have : 1 ≤ (nbrSumZ (wave η N zc t) y + η y) / (2 * (d : ℤ)) := by
      rw [Int.le_ediv_iff_mul_le hd0]
      linarith [hlow y]
    omega

/-- **Filling a finite region from its lit outer boundary.**  If every site of the outer boundary
of `V` is lit at time `t0`, then every site of `V` whose coordinate sum exceeds `B - j` is lit at
time `t0 + j`, where `B` bounds the coordinate sum on `V`.  A site of `V` with all its upper
neighbours lit is lit at the next step, because `d ≥ 2` and `η ≥ 2d - 2`. -/
theorem pub_fill (hd : 2 ≤ d) (η : Site d → ℤ) (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x)
    (N : ℕ) (hN : 1 ≤ N) (zc : Site d) (V : Set (Site d)) (B : ℤ)
    (hB : ∀ v ∈ V, pub_sigma v ≤ B) (t0 : ℕ)
    (hbd : ∀ y ∈ outerBoundary V, 0 < wave η N zc t0 y) :
    ∀ (j : ℕ) (y : Site d), B - (j : ℤ) < pub_sigma y → (y ∈ V ∨ y ∈ outerBoundary V) →
      0 < wave η N zc (t0 + j) y := by
  have hd2 : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by linarith
  have hlow0 : ∀ x, 0 ≤ η x := fun x => by linarith [hlow x]
  intro j
  induction j with
  | zero =>
    intro y hy hmem
    rcases hmem with hV | hb
    · exact absurd (hB y hV) (by push_cast at hy; omega)
    · simpa using hbd y hb
  | succ j ih =>
    intro y hy hmem
    by_cases hc : B - (j : ℤ) < pub_sigma y
    · exact lt_of_lt_of_le (ih y hc hmem) (wave_mono_time η hlow0 hd0 N zc (by omega) y)
    · have hsy : pub_sigma y = B - (j : ℤ) := by push_cast at hy; omega
      rcases hmem with hV | hb
      · have hup : ∀ l : Fin d, 0 < wave η N zc (t0 + j) (y + unit l) := by
          intro l
          refine ih _ ?_ ?_
          · rw [pub_sigma_add_unit]; omega
          · by_cases hyl : y + unit l ∈ V
            · exact Or.inl hyl
            · exact Or.inr ⟨hyl, y, hV, adj_add_unit y l⟩
        exact pub_lit_of_up hd η hlow N hN zc (t0 + j) y hup
      · exact lt_of_lt_of_le (hbd y hb) (wave_mono_time η hlow0 hd0 N zc (by omega) y)

end Exploding
