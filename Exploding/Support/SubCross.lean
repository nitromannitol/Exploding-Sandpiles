/-
The crossing property of a good cube, in the form the propagation step of
Lemma 3.2 uses it: if a line of `Q_k` through a point of its outer boundary has
already fired, then the whole cube has fired within `k^d` steps.

This is the paper's `exploding-corrected-arxiv.tex:369-371`: a good cube is one whose crossing
time is at most `k^d`, and the crossing time is exactly the first time the
`{Q_k^c ∪ L}`-frozen odometer is `1` on all of `Q_k`.
-/
import Exploding.Support.Vocab
import Exploding.Support.Wave
import Exploding.Support.SubGeom
import Exploding.Support.SubStep

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The crossing time of a good cube is attained at a natural number at most
`k^d`. -/
theorem exists_crossOdo_of_good {d : ℕ} (η : Site d → ℤ) (k : ℕ) (i : Fin d) (z : Site d)
    (hz : z ∈ closureN (cube d k)) (hgood : GoodCube η k) :
    ∃ n : ℕ, n ≤ k ^ d ∧ ∀ x ∈ cube d k, crossOdo η k i z n x = 1 := by
  have h1 : crossingTime η k i z ≤ ((k ^ d : ℕ) : ℕ∞) := hgood i z hz
  have hex : ∃ n : ℕ, 1 ≤ n ∧ ∀ x ∈ cube d k, crossOdo η k i z n x = 1 := by
    by_contra hcon
    have h2 : crossingTime η k i z = ⊤ := sInf_coe_top hcon
    rw [h2] at h1
    exact absurd h1 (by simp)
  obtain ⟨n, hn1, hn2⟩ := sInf_coe_attained (P := fun n => 1 ≤ n ∧
    ∀ x ∈ cube d k, crossOdo η k i z n x = 1) hex
  refine ⟨n, ?_, hn1.2⟩
  have h3 : ((n : ℕ∞)) = crossingTime η k i z := hn2.symm
  rw [← h3] at h1
  exact_mod_cast h1

/-- **The paper's propagation mechanism** (`exploding-corrected-arxiv.tex:369-371`): once the
support of the wave contains a line of a good cube `Q_k(j)`, the wave covers the
whole cube at a later time.  This is the crossing property of a good cube
(`exists_crossOdo_of_good`) combined with the domination of the frozen odometer
by the wave (`crossOdo_le_wave`). -/
theorem wave_covers_of_line {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (N k : ℕ) (hN : 2 ≤ N)
    (zc j : Site d) (hgoodj : GoodAt η k j) (dir' : Fin d) (z : Site d)
    (hz : z ∈ closureN (cube d k)) (t : ℕ)
    (hline : ∀ w ∈ line d k dir' z, 0 < wave η N zc t (w + (k : ℤ) • j)) :
    ∃ t' : ℕ, t ≤ t' ∧ ∀ x ∈ cube d k, 0 < wave η N zc t' (x + (k : ℤ) • j) := by
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  obtain ⟨n, hn, hcross⟩ := exists_crossOdo_of_good (fun x => η (x + (k : ℤ) • j)) k dir' z
    hz hgoodj
  refine ⟨t + n, Nat.le_add_right t n, fun x hx => ?_⟩
  have hdom := crossOdo_le_wave hd0 η hlow hhigh N k hN zc j dir' z t hline n x
  have h1 : crossOdo (fun x => η (x + (k : ℤ) • j)) k dir' z n x = 1 := hcross x hx
  rw [h1] at hdom
  omega

/-- **The line producer.**  A line of `Q_k(j)` whose base point lies in the cube is
contained in the cube, so the cover hypothesis gives the wave on it. -/
theorem line_of_cover {d : ℕ} (η : Site d → ℤ) (N k : ℕ) (zc i : Site d) (t : ℕ)
    (dir : Fin d) (z : Site d)
    (hcover : ∀ x ∈ cube d k, 0 < wave η N zc t (x + (k : ℤ) • i))
    (hz : z ∈ cube d k) :
    ∀ y ∈ line d k dir z, 0 < wave η N zc t (y + (k : ℤ) • i) := by
  intro y hy
  exact hcover y (fun l => by
    by_cases hl : l = dir
    · rw [hl]; exact hy.1
    · rw [hy.2 l hl]; exact hz l)



/-- **The `N = 1` case of `wave_covers_of_line`, with the exceptional site
handled.**  Same proof as `wave_covers_of_line`, with `crossOdo_le_wave_one'` in
place of `crossOdo_le_wave`; the extra hypothesis is that the wave's centre `zc`
does not lie in the cube's image, which is exactly what makes the `2 ≤ N`
hypothesis of `crossOdo_le_wave` unnecessary. -/
theorem wave_covers_of_line_one' {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (k : ℕ)
    (zc j : Site d) (hgoodj : GoodAt η k j) (dir' : Fin d) (z : Site d)
    (hz : z ∈ closureN (cube d k)) (t : ℕ)
    (hline : ∀ w ∈ line d k dir' z, 0 < wave η 1 zc t (w + (k : ℤ) • j))
    (hfar : ∀ y ∈ cube d k, y + (k : ℤ) • j ≠ zc) :
    ∃ t' : ℕ, t ≤ t' ∧ ∀ x ∈ cube d k, 0 < wave η 1 zc t' (x + (k : ℤ) • j) := by
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  obtain ⟨n, hn, hcross⟩ := exists_crossOdo_of_good (fun x => η (x + (k : ℤ) • j)) k dir' z
    hz hgoodj
  refine ⟨t + n, Nat.le_add_right t n, fun x hx => ?_⟩
  have hdom := crossOdo_le_wave_one' hd0 η hlow hhigh k zc j dir' z t hline hfar n x
  have h1 : crossOdo (fun x => η (x + (k : ℤ) • j)) k dir' z n x = 1 := hcross x hx
  rw [h1] at hdom
  omega

/-- **The `N = 1` propagation step.**  Same proof as `finite_exploding_step`,
with `wave_covers_of_line_one'` in place of `wave_covers_of_line` and the extra
hypothesis that the wave's centre `zc` is not in `Q_k(j)`'s image. -/
theorem finite_exploding_step {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (N k : ℕ) (hN : 2 ≤ N) (hk : 1 ≤ k) (zc i j : Site d)
    (hgoodj : GoodAt η k j) (dir : Fin d)
    (hdir : j = i + LatticeProb.unit dir ∨ i = j + LatticeProb.unit dir)
    (dir' : Fin d) (hne : dir' ≠ dir)
    (t : ℕ) (hcover : ∀ x ∈ cube d k, 0 < wave η N zc t (x + (k : ℤ) • i)) :
    ∃ t' : ℕ, t ≤ t' ∧ ∀ x ∈ cube d k, 0 < wave η N zc t' (x + (k : ℤ) • j) := by
  rcases hdir with hdir | hdir
  swap
  · -- i = j + unit dir: the same argument with the bottom face of Q_k(i)
    have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    have hz : (fun l : Fin d => if l = dir then (1 : ℤ) else 1) ∈ cube d k := fun l => by
      show 1 ≤ (if l = dir then (1 : ℤ) else 1) ∧ (if l = dir then (1 : ℤ) else 1) ≤ (k : ℤ)
      by_cases hl : l = dir
      · rw [if_pos hl]; exact ⟨le_refl 1, hk1⟩
      · rw [if_neg hl]; exact ⟨le_refl 1, hk1⟩
    have hline : ∀ y ∈ line d k dir' (fun l : Fin d => if l = dir then (1 : ℤ) else 1),
        0 < wave η N zc t (y + (k : ℤ) • i) :=
      line_of_cover η N k zc i t dir' (fun l : Fin d => if l = dir then (1 : ℤ) else 1) hcover hz
    have hz' : (fun l : Fin d => if l = dir then (k : ℤ) + 1 else 1) ∈ closureN (cube d k) := by
      refine Or.inr ⟨?_, (fun l : Fin d => if l = dir then (k : ℤ) else 1), ?_, ?_⟩
      · intro hcon
        have h := (hcon dir).2
        have h0 : (fun l : Fin d => if l = dir then (k : ℤ) + 1 else 1) dir = (k : ℤ) + 1 := by
          simp
        omega
      · intro l
        show 1 ≤ (if l = dir then (k : ℤ) else 1) ∧ (if l = dir then (k : ℤ) else 1) ≤ (k : ℤ)
        by_cases hl : l = dir
        · rw [if_pos hl]; exact ⟨hk1, le_refl _⟩
        · rw [if_neg hl]; exact ⟨le_refl 1, hk1⟩
      · refine ⟨dir, Or.inr ?_⟩
        funext l
        by_cases hl : l = dir
        · show (if l = dir then (k : ℤ) + 1 else 1) = (if l = dir then (k : ℤ) else 1) +
            (LatticeProb.unit dir : Site d) l
          simp only [hl, LatticeProb.unit, Pi.single_eq_same]
          norm_num
        · show (if l = dir then (k : ℤ) + 1 else 1) = (if l = dir then (k : ℤ) else 1) +
            (LatticeProb.unit dir : Site d) l
          simp only [if_neg hl, LatticeProb.unit, Pi.single_eq_of_ne hl, add_zero]
    have hline' : ∀ w ∈ line d k dir' (fun l : Fin d => if l = dir then (k : ℤ) + 1 else 1),
        0 < wave η N zc t (w + (k : ℤ) • j) := by
      intro w hw
      have hmem : w - (k : ℤ) • LatticeProb.unit dir ∈
          line d k dir' (fun l : Fin d => if l = dir then (1 : ℤ) else 1) := by
        refine ⟨?_, ?_⟩
        · have hwl := hw.1
          show 1 ≤ (w - (k : ℤ) • LatticeProb.unit dir) dir' ∧
            (w - (k : ℤ) • LatticeProb.unit dir) dir' ≤ (k : ℤ)
          have hne' : dir' ≠ dir := hne
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, LatticeProb.unit,
            Pi.single_eq_of_ne hne', mul_zero, sub_zero]
          exact hwl
        · intro l hl
          have h2 := hw.2 l hl
          show (w - (k : ℤ) • LatticeProb.unit dir) l = (if l = dir then (1 : ℤ) else 1)
          by_cases hld : l = dir
          · show (w - (k : ℤ) • LatticeProb.unit dir) l = (if l = dir then (1 : ℤ) else 1)
            have hwv : w l = (k : ℤ) + 1 := by
              have h3 := hw.2 l (by rw [hld]; exact Ne.symm hne)
              simpa [hld] using h3
            simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, LatticeProb.unit,
              hld, Pi.single_eq_same]
            rw [hld] at hwv
            rw [hwv]
            norm_num
          · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, LatticeProb.unit,
              Pi.single_eq_of_ne hld, mul_zero, sub_zero, if_neg hld] at h2 ⊢
            exact h2
      have h := hline _ hmem
      have he : w - (k : ℤ) • LatticeProb.unit dir + (k : ℤ) • i = w + (k : ℤ) • j := by
        rw [hdir]
        simp only [smul_add]
        abel
      rwa [he] at h
    exact wave_covers_of_line hd η hlow hhigh N k hN zc j hgoodj dir'
      (fun l : Fin d => if l = dir then (k : ℤ) + 1 else 1) hz' t hline'
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  -- the top face of Q_k(i), in Q_k(i) coordinates
  have hz : (fun l : Fin d => if l = dir then (k : ℤ) else 1) ∈ cube d k := fun l => by
    show 1 ≤ (if l = dir then (k : ℤ) else 1) ∧ (if l = dir then (k : ℤ) else 1) ≤ (k : ℤ)
    by_cases hl : l = dir
    · rw [if_pos hl]; exact ⟨hk1, le_refl _⟩
    · rw [if_neg hl]; exact ⟨le_refl 1, hk1⟩
  -- the wave on the top face of Q_k(i), shifted by k•i
  have hline : ∀ y ∈ line d k dir' (fun l : Fin d => if l = dir then (k : ℤ) else 1),
      0 < wave η N zc t (y + (k : ℤ) • i) :=
    line_of_cover η N k zc i t dir' (fun l : Fin d => if l = dir then (k : ℤ) else 1) hcover hz
  -- the same line, read in Q_k(j) coordinates: one step below Q_k(j)
  have hz' : (fun l : Fin d => if l = dir then (0 : ℤ) else 1) ∈ closureN (cube d k) := by
    refine Or.inr ⟨?_, (fun l : Fin d => if l = dir then (1 : ℤ) else 1), ?_, ?_⟩
    · intro hcon
      have h := (hcon dir).1
      have h0 : (fun l : Fin d => if l = dir then (0 : ℤ) else 1) dir = 0 := by simp
      omega
    · intro l
      show 1 ≤ (if l = dir then (1 : ℤ) else 1) ∧ (if l = dir then (1 : ℤ) else 1) ≤ (k : ℤ)
      by_cases hl : l = dir
      · simp only [hl]; exact ⟨le_refl 1, hk1⟩
      · simp only [if_neg hl]; exact ⟨le_refl 1, hk1⟩
    · refine ⟨dir, Or.inl ?_⟩
      funext l
      by_cases hl : l = dir
      · show (if l = dir then (1 : ℤ) else 1) =
          (if l = dir then (0 : ℤ) else 1) + (LatticeProb.unit dir : Site d) l
        simp only [hl, LatticeProb.unit, Pi.single_eq_same]
        norm_num
      · show (if l = dir then (1 : ℤ) else 1) =
          (if l = dir then (0 : ℤ) else 1) + (LatticeProb.unit dir : Site d) l
        simp only [if_neg hl, LatticeProb.unit, Pi.single_eq_of_ne hl, add_zero]
  have hline' : ∀ w ∈ line d k dir' (fun l : Fin d => if l = dir then (0 : ℤ) else 1),
      0 < wave η N zc t (w + (k : ℤ) • j) := by
    intro w hw
    -- w + k•j = (w + k•unit dir) + k•i
    have hmem : w + (k : ℤ) • LatticeProb.unit dir ∈
        line d k dir' (fun l : Fin d => if l = dir then (k : ℤ) else 1) := by
      refine ⟨?_, ?_⟩
      · have hwl := hw.1
        show 1 ≤ (w + (k : ℤ) • LatticeProb.unit dir) dir' ∧
          (w + (k : ℤ) • LatticeProb.unit dir) dir' ≤ (k : ℤ)
        have hne' : dir' ≠ dir := hne
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, LatticeProb.unit,
          Pi.single_eq_of_ne hne', mul_zero, add_zero]
        exact hwl
      · intro l hl
        have h2 := hw.2 l hl
        show (w + (k : ℤ) • LatticeProb.unit dir) l = (if l = dir then (k : ℤ) else 1)
        by_cases hld : l = dir
        · rw [hld]
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, LatticeProb.unit,
            Pi.single_eq_same]
          have hw0 : w dir = 0 := by
            have h3 := hw.2 dir (Ne.symm hne)
            simpa using h3
          rw [hw0]
          norm_num
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, LatticeProb.unit,
            Pi.single_eq_of_ne hld, mul_zero, add_zero, if_neg hld] at h2 ⊢
          exact h2
    have h := hline _ hmem
    have he : w + (k : ℤ) • LatticeProb.unit dir + (k : ℤ) • i = w + (k : ℤ) • j := by
      rw [hdir]
      simp only [smul_add]
      abel
    rwa [he] at h
  exact wave_covers_of_line hd η hlow hhigh N k hN zc j hgoodj dir'
    (fun l : Fin d => if l = dir then (0 : ℤ) else 1) hz' t hline'

theorem finite_exploding_step_one {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (k : ℕ) (hk : 1 ≤ k) (zc i j : Site d)
    (hgoodj : GoodAt η k j) (dir : Fin d)
    (hdir : j = i + LatticeProb.unit dir ∨ i = j + LatticeProb.unit dir)
    (dir' : Fin d) (hne : dir' ≠ dir)
    (t : ℕ) (hcover : ∀ x ∈ cube d k, 0 < wave η 1 zc t (x + (k : ℤ) • i))
    (hfar : ∀ y ∈ cube d k, y + (k : ℤ) • j ≠ zc) :
    ∃ t' : ℕ, t ≤ t' ∧ ∀ x ∈ cube d k, 0 < wave η 1 zc t' (x + (k : ℤ) • j) := by
  rcases hdir with hdir | hdir
  swap
  · -- i = j + unit dir: the same argument with the bottom face of Q_k(i)
    have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    have hz : (fun l : Fin d => if l = dir then (1 : ℤ) else 1) ∈ cube d k := fun l => by
      show 1 ≤ (if l = dir then (1 : ℤ) else 1) ∧ (if l = dir then (1 : ℤ) else 1) ≤ (k : ℤ)
      by_cases hl : l = dir
      · rw [if_pos hl]; exact ⟨le_refl 1, hk1⟩
      · rw [if_neg hl]; exact ⟨le_refl 1, hk1⟩
    have hline : ∀ y ∈ line d k dir' (fun l : Fin d => if l = dir then (1 : ℤ) else 1),
        0 < wave η 1 zc t (y + (k : ℤ) • i) :=
      line_of_cover η 1 k zc i t dir' (fun l : Fin d => if l = dir then (1 : ℤ) else 1) hcover hz
    have hz' : (fun l : Fin d => if l = dir then (k : ℤ) + 1 else 1) ∈ closureN (cube d k) := by
      refine Or.inr ⟨?_, (fun l : Fin d => if l = dir then (k : ℤ) else 1), ?_, ?_⟩
      · intro hcon
        have h := (hcon dir).2
        have h0 : (fun l : Fin d => if l = dir then (k : ℤ) + 1 else 1) dir = (k : ℤ) + 1 := by
          simp
        omega
      · intro l
        show 1 ≤ (if l = dir then (k : ℤ) else 1) ∧ (if l = dir then (k : ℤ) else 1) ≤ (k : ℤ)
        by_cases hl : l = dir
        · rw [if_pos hl]; exact ⟨hk1, le_refl _⟩
        · rw [if_neg hl]; exact ⟨le_refl 1, hk1⟩
      · refine ⟨dir, Or.inr ?_⟩
        funext l
        by_cases hl : l = dir
        · show (if l = dir then (k : ℤ) + 1 else 1) = (if l = dir then (k : ℤ) else 1) +
            (LatticeProb.unit dir : Site d) l
          simp only [hl, LatticeProb.unit, Pi.single_eq_same]
          norm_num
        · show (if l = dir then (k : ℤ) + 1 else 1) = (if l = dir then (k : ℤ) else 1) +
            (LatticeProb.unit dir : Site d) l
          simp only [if_neg hl, LatticeProb.unit, Pi.single_eq_of_ne hl, add_zero]
    have hline' : ∀ w ∈ line d k dir' (fun l : Fin d => if l = dir then (k : ℤ) + 1 else 1),
        0 < wave η 1 zc t (w + (k : ℤ) • j) := by
      intro w hw
      have hmem : w - (k : ℤ) • LatticeProb.unit dir ∈
          line d k dir' (fun l : Fin d => if l = dir then (1 : ℤ) else 1) := by
        refine ⟨?_, ?_⟩
        · have hwl := hw.1
          show 1 ≤ (w - (k : ℤ) • LatticeProb.unit dir) dir' ∧
            (w - (k : ℤ) • LatticeProb.unit dir) dir' ≤ (k : ℤ)
          have hne' : dir' ≠ dir := hne
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, LatticeProb.unit,
            Pi.single_eq_of_ne hne', mul_zero, sub_zero]
          exact hwl
        · intro l hl
          have h2 := hw.2 l hl
          show (w - (k : ℤ) • LatticeProb.unit dir) l = (if l = dir then (1 : ℤ) else 1)
          by_cases hld : l = dir
          · show (w - (k : ℤ) • LatticeProb.unit dir) l = (if l = dir then (1 : ℤ) else 1)
            have hwv : w l = (k : ℤ) + 1 := by
              have h3 := hw.2 l (by rw [hld]; exact Ne.symm hne)
              simpa [hld] using h3
            simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, LatticeProb.unit,
              hld, Pi.single_eq_same]
            rw [hld] at hwv
            rw [hwv]
            norm_num
          · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, LatticeProb.unit,
              Pi.single_eq_of_ne hld, mul_zero, sub_zero, if_neg hld] at h2 ⊢
            exact h2
      have h := hline _ hmem
      have he : w - (k : ℤ) • LatticeProb.unit dir + (k : ℤ) • i = w + (k : ℤ) • j := by
        rw [hdir]
        simp only [smul_add]
        abel
      rwa [he] at h
    exact wave_covers_of_line_one' hd η hlow hhigh k zc j hgoodj dir'
      (fun l : Fin d => if l = dir then (k : ℤ) + 1 else 1) hz' t hline' hfar
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  -- the top face of Q_k(i), in Q_k(i) coordinates
  have hz : (fun l : Fin d => if l = dir then (k : ℤ) else 1) ∈ cube d k := fun l => by
    show 1 ≤ (if l = dir then (k : ℤ) else 1) ∧ (if l = dir then (k : ℤ) else 1) ≤ (k : ℤ)
    by_cases hl : l = dir
    · rw [if_pos hl]; exact ⟨hk1, le_refl _⟩
    · rw [if_neg hl]; exact ⟨le_refl 1, hk1⟩
  -- the wave on the top face of Q_k(i), shifted by k•i
  have hline : ∀ y ∈ line d k dir' (fun l : Fin d => if l = dir then (k : ℤ) else 1),
      0 < wave η 1 zc t (y + (k : ℤ) • i) :=
    line_of_cover η 1 k zc i t dir' (fun l : Fin d => if l = dir then (k : ℤ) else 1) hcover hz
  -- the same line, read in Q_k(j) coordinates: one step below Q_k(j)
  have hz' : (fun l : Fin d => if l = dir then (0 : ℤ) else 1) ∈ closureN (cube d k) := by
    refine Or.inr ⟨?_, (fun l : Fin d => if l = dir then (1 : ℤ) else 1), ?_, ?_⟩
    · intro hcon
      have h := (hcon dir).1
      have h0 : (fun l : Fin d => if l = dir then (0 : ℤ) else 1) dir = 0 := by simp
      omega
    · intro l
      show 1 ≤ (if l = dir then (1 : ℤ) else 1) ∧ (if l = dir then (1 : ℤ) else 1) ≤ (k : ℤ)
      by_cases hl : l = dir
      · simp only [hl]; exact ⟨le_refl 1, hk1⟩
      · simp only [if_neg hl]; exact ⟨le_refl 1, hk1⟩
    · refine ⟨dir, Or.inl ?_⟩
      funext l
      by_cases hl : l = dir
      · show (if l = dir then (1 : ℤ) else 1) =
          (if l = dir then (0 : ℤ) else 1) + (LatticeProb.unit dir : Site d) l
        simp only [hl, LatticeProb.unit, Pi.single_eq_same]
        norm_num
      · show (if l = dir then (1 : ℤ) else 1) =
          (if l = dir then (0 : ℤ) else 1) + (LatticeProb.unit dir : Site d) l
        simp only [if_neg hl, LatticeProb.unit, Pi.single_eq_of_ne hl, add_zero]
  have hline' : ∀ w ∈ line d k dir' (fun l : Fin d => if l = dir then (0 : ℤ) else 1),
      0 < wave η 1 zc t (w + (k : ℤ) • j) := by
    intro w hw
    -- w + k•j = (w + k•unit dir) + k•i
    have hmem : w + (k : ℤ) • LatticeProb.unit dir ∈
        line d k dir' (fun l : Fin d => if l = dir then (k : ℤ) else 1) := by
      refine ⟨?_, ?_⟩
      · have hwl := hw.1
        show 1 ≤ (w + (k : ℤ) • LatticeProb.unit dir) dir' ∧
          (w + (k : ℤ) • LatticeProb.unit dir) dir' ≤ (k : ℤ)
        have hne' : dir' ≠ dir := hne
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, LatticeProb.unit,
          Pi.single_eq_of_ne hne', mul_zero, add_zero]
        exact hwl
      · intro l hl
        have h2 := hw.2 l hl
        show (w + (k : ℤ) • LatticeProb.unit dir) l = (if l = dir then (k : ℤ) else 1)
        by_cases hld : l = dir
        · rw [hld]
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, LatticeProb.unit,
            Pi.single_eq_same]
          have hw0 : w dir = 0 := by
            have h3 := hw.2 dir (Ne.symm hne)
            simpa using h3
          rw [hw0]
          norm_num
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, LatticeProb.unit,
            Pi.single_eq_of_ne hld, mul_zero, add_zero, if_neg hld] at h2 ⊢
          exact h2
    have h := hline _ hmem
    have he : w + (k : ℤ) • LatticeProb.unit dir + (k : ℤ) • i = w + (k : ℤ) • j := by
      rw [hdir]
      simp only [smul_add]
      abel
    rwa [he] at h
  exact wave_covers_of_line_one' hd η hlow hhigh k zc j hgoodj dir'
    (fun l : Fin d => if l = dir then (0 : ℤ) else 1) hz' t hline' hfar

theorem finite_exploding_step_centre {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (N k : ℕ) (hN : 2 ≤ N) (hk : 1 ≤ k) (zc i j : Site d)
    (hgoodj : GoodAt η k j) (dir : Fin d)
    (hdir : j = i + LatticeProb.unit dir ∨ i = j + LatticeProb.unit dir)
    (dir' : Fin d) (hne : dir' ≠ dir)
    (t : ℕ) (hcover : ∀ x ∈ cube d k, 0 < wave η N zc t (x + (k : ℤ) • i)) :
    ∃ t' : ℕ, t ≤ t' ∧ ∀ x ∈ cube d k, 0 < wave η N zc t' (x + (k : ℤ) • j) := by
  rcases hdir with hdir | hdir
  swap
  · -- i = j + unit dir: the same argument with the bottom face of Q_k(i)
    have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    have hz : (fun l : Fin d => if l = dir then (1 : ℤ) else 1) ∈ cube d k := fun l => by
      show 1 ≤ (if l = dir then (1 : ℤ) else 1) ∧ (if l = dir then (1 : ℤ) else 1) ≤ (k : ℤ)
      by_cases hl : l = dir
      · rw [if_pos hl]; exact ⟨le_refl 1, hk1⟩
      · rw [if_neg hl]; exact ⟨le_refl 1, hk1⟩
    have hline : ∀ y ∈ line d k dir' (fun l : Fin d => if l = dir then (1 : ℤ) else 1),
        0 < wave η N zc t (y + (k : ℤ) • i) :=
      line_of_cover η N k zc i t dir' (fun l : Fin d => if l = dir then (1 : ℤ) else 1) hcover hz
    have hz' : (fun l : Fin d => if l = dir then (k : ℤ) + 1 else 1) ∈ closureN (cube d k) := by
      refine Or.inr ⟨?_, (fun l : Fin d => if l = dir then (k : ℤ) else 1), ?_, ?_⟩
      · intro hcon
        have h := (hcon dir).2
        have h0 : (fun l : Fin d => if l = dir then (k : ℤ) + 1 else 1) dir = (k : ℤ) + 1 := by
          simp
        omega
      · intro l
        show 1 ≤ (if l = dir then (k : ℤ) else 1) ∧ (if l = dir then (k : ℤ) else 1) ≤ (k : ℤ)
        by_cases hl : l = dir
        · rw [if_pos hl]; exact ⟨hk1, le_refl _⟩
        · rw [if_neg hl]; exact ⟨le_refl 1, hk1⟩
      · refine ⟨dir, Or.inr ?_⟩
        funext l
        by_cases hl : l = dir
        · show (if l = dir then (k : ℤ) + 1 else 1) = (if l = dir then (k : ℤ) else 1) +
            (LatticeProb.unit dir : Site d) l
          simp only [hl, LatticeProb.unit, Pi.single_eq_same]
          norm_num
        · show (if l = dir then (k : ℤ) + 1 else 1) = (if l = dir then (k : ℤ) else 1) +
            (LatticeProb.unit dir : Site d) l
          simp only [if_neg hl, LatticeProb.unit, Pi.single_eq_of_ne hl, add_zero]
    have hline' : ∀ w ∈ line d k dir' (fun l : Fin d => if l = dir then (k : ℤ) + 1 else 1),
        0 < wave η N zc t (w + (k : ℤ) • j) := by
      intro w hw
      have hmem : w - (k : ℤ) • LatticeProb.unit dir ∈
          line d k dir' (fun l : Fin d => if l = dir then (1 : ℤ) else 1) := by
        refine ⟨?_, ?_⟩
        · have hwl := hw.1
          show 1 ≤ (w - (k : ℤ) • LatticeProb.unit dir) dir' ∧
            (w - (k : ℤ) • LatticeProb.unit dir) dir' ≤ (k : ℤ)
          have hne' : dir' ≠ dir := hne
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, LatticeProb.unit,
            Pi.single_eq_of_ne hne', mul_zero, sub_zero]
          exact hwl
        · intro l hl
          have h2 := hw.2 l hl
          show (w - (k : ℤ) • LatticeProb.unit dir) l = (if l = dir then (1 : ℤ) else 1)
          by_cases hld : l = dir
          · show (w - (k : ℤ) • LatticeProb.unit dir) l = (if l = dir then (1 : ℤ) else 1)
            have hwv : w l = (k : ℤ) + 1 := by
              have h3 := hw.2 l (by rw [hld]; exact Ne.symm hne)
              simpa [hld] using h3
            simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, LatticeProb.unit,
              hld, Pi.single_eq_same]
            rw [hld] at hwv
            rw [hwv]
            norm_num
          · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, LatticeProb.unit,
              Pi.single_eq_of_ne hld, mul_zero, sub_zero, if_neg hld] at h2 ⊢
            exact h2
      have h := hline _ hmem
      have he : w - (k : ℤ) • LatticeProb.unit dir + (k : ℤ) • i = w + (k : ℤ) • j := by
        rw [hdir]
        simp only [smul_add]
        abel
      rwa [he] at h
    exact wave_covers_of_line hd η hlow hhigh N k hN zc j hgoodj dir'
      (fun l : Fin d => if l = dir then (k : ℤ) + 1 else 1) hz' t hline'
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  -- the top face of Q_k(i), in Q_k(i) coordinates
  have hz : (fun l : Fin d => if l = dir then (k : ℤ) else 1) ∈ cube d k := fun l => by
    show 1 ≤ (if l = dir then (k : ℤ) else 1) ∧ (if l = dir then (k : ℤ) else 1) ≤ (k : ℤ)
    by_cases hl : l = dir
    · rw [if_pos hl]; exact ⟨hk1, le_refl _⟩
    · rw [if_neg hl]; exact ⟨le_refl 1, hk1⟩
  -- the wave on the top face of Q_k(i), shifted by k•i
  have hline : ∀ y ∈ line d k dir' (fun l : Fin d => if l = dir then (k : ℤ) else 1),
      0 < wave η N zc t (y + (k : ℤ) • i) :=
    line_of_cover η N k zc i t dir' (fun l : Fin d => if l = dir then (k : ℤ) else 1) hcover hz
  -- the same line, read in Q_k(j) coordinates: one step below Q_k(j)
  have hz' : (fun l : Fin d => if l = dir then (0 : ℤ) else 1) ∈ closureN (cube d k) := by
    refine Or.inr ⟨?_, (fun l : Fin d => if l = dir then (1 : ℤ) else 1), ?_, ?_⟩
    · intro hcon
      have h := (hcon dir).1
      have h0 : (fun l : Fin d => if l = dir then (0 : ℤ) else 1) dir = 0 := by simp
      omega
    · intro l
      show 1 ≤ (if l = dir then (1 : ℤ) else 1) ∧ (if l = dir then (1 : ℤ) else 1) ≤ (k : ℤ)
      by_cases hl : l = dir
      · simp only [hl]; exact ⟨le_refl 1, hk1⟩
      · simp only [if_neg hl]; exact ⟨le_refl 1, hk1⟩
    · refine ⟨dir, Or.inl ?_⟩
      funext l
      by_cases hl : l = dir
      · show (if l = dir then (1 : ℤ) else 1) =
          (if l = dir then (0 : ℤ) else 1) + (LatticeProb.unit dir : Site d) l
        simp only [hl, LatticeProb.unit, Pi.single_eq_same]
        norm_num
      · show (if l = dir then (1 : ℤ) else 1) =
          (if l = dir then (0 : ℤ) else 1) + (LatticeProb.unit dir : Site d) l
        simp only [if_neg hl, LatticeProb.unit, Pi.single_eq_of_ne hl, add_zero]
  have hline' : ∀ w ∈ line d k dir' (fun l : Fin d => if l = dir then (0 : ℤ) else 1),
      0 < wave η N zc t (w + (k : ℤ) • j) := by
    intro w hw
    -- w + k•j = (w + k•unit dir) + k•i
    have hmem : w + (k : ℤ) • LatticeProb.unit dir ∈
        line d k dir' (fun l : Fin d => if l = dir then (k : ℤ) else 1) := by
      refine ⟨?_, ?_⟩
      · have hwl := hw.1
        show 1 ≤ (w + (k : ℤ) • LatticeProb.unit dir) dir' ∧
          (w + (k : ℤ) • LatticeProb.unit dir) dir' ≤ (k : ℤ)
        have hne' : dir' ≠ dir := hne
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, LatticeProb.unit,
          Pi.single_eq_of_ne hne', mul_zero, add_zero]
        exact hwl
      · intro l hl
        have h2 := hw.2 l hl
        show (w + (k : ℤ) • LatticeProb.unit dir) l = (if l = dir then (k : ℤ) else 1)
        by_cases hld : l = dir
        · rw [hld]
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, LatticeProb.unit,
            Pi.single_eq_same]
          have hw0 : w dir = 0 := by
            have h3 := hw.2 dir (Ne.symm hne)
            simpa using h3
          rw [hw0]
          norm_num
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, LatticeProb.unit,
            Pi.single_eq_of_ne hld, mul_zero, add_zero, if_neg hld] at h2 ⊢
          exact h2
    have h := hline _ hmem
    have he : w + (k : ℤ) • LatticeProb.unit dir + (k : ℤ) • i = w + (k : ℤ) • j := by
      rw [hdir]
      simp only [smul_add]
      abel
    rwa [he] at h
  exact wave_covers_of_line hd η hlow hhigh N k hN zc j hgoodj dir'
    (fun l : Fin d => if l = dir then (0 : ℤ) else 1) hz' t hline'


/-- **The `N = 1` case of `wave_covers_of_line`.**  Same proof as
`wave_covers_of_line`, with `crossOdo_le_wave_one` in place of
`crossOdo_le_wave`; the extra hypothesis is that the wave's centre `zc` does not
lie in the cube's image, which is exactly what makes the `2 ≤ N` hypothesis of
`crossOdo_le_wave` unnecessary. -/
theorem wave_covers_of_line_one {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (k : ℕ)
    (zc j : Site d) (hgoodj : GoodAt η k j) (dir' : Fin d) (z : Site d)
    (hz : z ∈ closureN (cube d k)) (t : ℕ)
    (hline : ∀ w ∈ line d k dir' z, 0 < wave η 1 zc t (w + (k : ℤ) • j))
    (hfar : ∀ y ∈ cube d k, y + (k : ℤ) • j ≠ zc) :
    ∃ t' : ℕ, t ≤ t' ∧ ∀ x ∈ cube d k, 0 < wave η 1 zc t' (x + (k : ℤ) • j) := by
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  obtain ⟨n, hn, hcross⟩ := exists_crossOdo_of_good (fun x => η (x + (k : ℤ) • j)) k dir' z
    hz hgoodj
  refine ⟨t + n, Nat.le_add_right t n, fun x hx => ?_⟩
  have hdom := crossOdo_le_wave_one hd0 η hlow hhigh k zc j dir' z t hline hfar n x
  have h1 : crossOdo (fun x => η (x + (k : ℤ) • j)) k dir' z n x = 1 := hcross x hx
  rw [h1] at hdom
  omega

end Exploding