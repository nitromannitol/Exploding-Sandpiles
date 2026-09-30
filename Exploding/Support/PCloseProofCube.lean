/-
The propagation mechanism of a good cube in the form the second inequality of
Lemma 3.7 uses it: once a line of a good cube has fired, the whole cube has
fired within `k^d` further steps, and the same holds for a good cube adjacent
to a fired cube.  The wave is an arbitrary `N`-wave with `N ≥ 1`, and the time
needed is tracked.
-/
import Exploding.Support.Vocab
import Exploding.Support.Wave
import Exploding.Support.SubGeom
import Exploding.Support.SubStep
import Exploding.Support.SubCross
import Exploding.Support.PCloseProofPath

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- **Domination of the frozen crossing odometer by the `N`-wave, for every `N ≥ 1`.**
This is `crossOdo_le_wave` without the restriction `2 ≤ N`: at the wave's centre the
wave equals `N ≥ 1` and the frozen odometer is at most `1`. -/
theorem pclose_crossOdo_le_wave {d : ℕ} (hd0 : (0 : ℤ) < 2 * (d : ℤ))
    (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (N k : ℕ) (hN : 1 ≤ N) (zc j : Site d) (dir' : Fin d) (z : Site d) (t : ℕ)
    (hseed : ∀ y ∈ line d k dir' z, 0 < wave η N zc t (y + (k : ℤ) • j)) :
    ∀ s y, crossOdo (fun x => η (x + (k : ℤ) • j)) k dir' z s y ≤
      wave η N zc (t + s) (y + (k : ℤ) • j) := by
  classical
  have hseed1 : ∀ y ∈ line d k dir' z, (1 : ℤ) ≤ wave η N zc t (y + (k : ℤ) • j) :=
    fun y hy => hseed y hy
  have hseed0 : ∀ y, (if y ∈ line d k dir' z then (1 : ℤ) else 0) ≤
      wave η N zc t (y + (k : ℤ) • j) := by
    intro y
    by_cases hy : y ∈ line d k dir' z
    · rw [if_pos hy]; exact hseed1 y hy
    · rw [if_neg hy]; exact wave_nonneg η hlow N zc t _
  have hseed0' : ∀ y, (0 : ℤ) ≤ (if y ∈ line d k dir' z then (1 : ℤ) else 0) := by
    intro y
    by_cases hy : y ∈ line d k dir' z <;> simp [hy]
  have hseed1' : ∀ y, (if y ∈ line d k dir' z then (1 : ℤ) else 0) ≤ 1 := by
    intro y
    by_cases hy : y ∈ line d k dir' z <;> simp [hy]
  have hmono : ∀ s y, wave η N zc t (y + (k : ℤ) • j) ≤
      wave η N zc (t + s) (y + (k : ℤ) • j) :=
    fun s y => wave_mono_time η hlow hd0 N zc (Nat.le_add_right t s) _
  have hcap : ∀ s y, crossOdo (fun x => η (x + (k : ℤ) • j)) k dir' z s y ≤ 1 :=
    fun s y => fodo_le_one _ _ _ (fun x => hhigh _) hseed1' hseed0' s y
  have hN1 : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  intro s
  induction s with
  | zero =>
    intro y
    rw [crossOdo, fodo_zero]
    exact hseed0 y
  | succ s ih =>
    intro y
    by_cases hzc : y + (k : ℤ) • j = zc
    · rw [hzc, wave_at_centre]
      exact le_trans (hcap (s + 1) y) hN1
    rw [crossOdo, fodo_succ]
    by_cases hy : y ∈ (cube d k)ᶜ ∪ line d k dir' z
    · rw [if_pos hy]
      exact le_trans (hseed0 y) (hmono (s + 1) y)
    · rw [if_neg hy]
      have hmono' : wave η N zc (t + s) (y + (k : ℤ) • j) ≤
          wave η N zc (t + s + 1) (y + (k : ℤ) • j) :=
        wave_mono_t η hlow hd0 N zc (t + s) (y + (k : ℤ) • j)
      by_cases hc : 2 * (d : ℤ) ≤ fconf ((cube d k)ᶜ ∪ line d k dir' z)
          (fun x => η (x + (k : ℤ) • j)) (fun x => if x ∈ line d k dir' z then 1 else 0) s y
      · rw [if_pos hc]
        have hsum : nbrSumZ (crossOdo (fun x => η (x + (k : ℤ) • j)) k dir' z s) y ≤
            nbrSumZ (wave η N zc (t + s)) (y + (k : ℤ) • j) := by
          have h1 := nbrSumZ_mono (fun w => ih w) y
          rwa [nbrSumZ_shift] at h1
        have hc' : 2 * (d : ℤ) ≤ η (y + (k : ℤ) • j) +
            lap (crossOdo (fun x => η (x + (k : ℤ) • j)) k dir' z s) y := hc
        rw [lap] at hc'
        have hle1 : crossOdo (fun x => η (x + (k : ℤ) • j)) k dir' z s y ≤
            wave η N zc (t + s) (y + (k : ℤ) • j) := ih y
        rw [show t + (s + 1) = t + s + 1 from by omega]
        rw [wave_of_ne η N zc (y + (k : ℤ) • j) (t + s) hzc]
        rw [Int.le_ediv_iff_mul_le (by positivity)]
        simp only [crossOdo] at hsum hc' hle1 ⊢
        nlinarith [hsum, hc', hle1]
      · rw [if_neg hc]
        simp only [crossOdo] at ih ⊢
        have h1 := ih y
        rw [show t + (s + 1) = t + s + 1 from by omega]
        linarith [h1, hmono']

/-- The cube `Q_k(j)` has fired at time `T`: the wave is positive on all of it. -/
def PCloseFired (η : Site d → ℤ) (N k : ℕ) (zc : Site d) (T : ℕ) (j : Site d) : Prop :=
  ∀ y ∈ cube d k, 0 < wave η N zc T (y + (k : ℤ) • j)

theorem pclose_fired_mono (hd0 : (0 : ℤ) < 2 * (d : ℤ)) (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (N k : ℕ) (zc : Site d) {T T' : ℕ} (hT : T ≤ T') {j : Site d}
    (h : PCloseFired η N k zc T j) : PCloseFired η N k zc T' j :=
  fun y hy => pclose_pos_mono hd0 η hlow N zc hT (h y hy)

/-- A good cube one of whose lines is positive at time `t` has fired by time `t + k^d`. -/
theorem pclose_cube_of_line (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (N k : ℕ) (hN : 1 ≤ N) (zc j : Site d) (hgood : GoodAt η k j) (dir' : Fin d) (z : Site d)
    (hz : z ∈ closureN (cube d k)) (t : ℕ)
    (hline : ∀ w ∈ line d k dir' z, 0 < wave η N zc t (w + (k : ℤ) • j)) :
    PCloseFired η N k zc (t + k ^ d) j := by
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  obtain ⟨n, hn, hcross⟩ := exists_crossOdo_of_good (fun x => η (x + (k : ℤ) • j)) k dir' z
    hz hgood
  intro x hx
  have hdom := pclose_crossOdo_le_wave hd0 η hlow hhigh N k hN zc j dir' z t hline n x
  have h1 : crossOdo (fun x => η (x + (k : ℤ) • j)) k dir' z n x = 1 := hcross x hx
  rw [h1] at hdom
  exact pclose_pos_mono hd0 η hlow N zc (by omega : t + n ≤ t + k ^ d)
    (lt_of_lt_of_le zero_lt_one hdom)

/-- Two adjacent cubes: a line of `Q_k(j)` through a point of its outer boundary lies in
`Q_k(i)`. -/
theorem pclose_adj_line (hd : 2 ≤ d) (k : ℕ) (hk : 1 ≤ k) (i j : Site d)
    (hij : (lattice d).Adj j i) :
    ∃ (dir' : Fin d) (z : Site d), z ∈ closureN (cube d k) ∧
      ∀ w ∈ line d k dir' z, w + (k : ℤ) • j - (k : ℤ) • i ∈ cube d k := by
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  obtain ⟨dir, hdir⟩ := hij
  -- a direction different from `dir`
  have hex : ∃ dir' : Fin d, dir' ≠ dir := by
    by_cases h0 : dir = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, by
        intro h; rw [h0] at h
        have := congrArg Fin.val h
        simp at this⟩
    · exact ⟨⟨0, by omega⟩, fun h => h0 h.symm⟩
  obtain ⟨dir', hne⟩ := hex
  rcases hdir with hdir | hdir
  · -- `i = j + unit dir`: the cube `Q_k(i)` lies above `Q_k(j)`, at coordinate `k + 1`
    refine ⟨dir', fun l => if l = dir then (k : ℤ) + 1 else 1, ?_, ?_⟩
    · refine Or.inr ⟨?_, fun l => if l = dir then (k : ℤ) else 1, ?_, ?_⟩
      · intro hcon
        have h := (hcon dir).2
        simp at h
      · intro l
        by_cases hl : l = dir
        · simp only [hl, if_true]; exact ⟨hk1, le_rfl⟩
        · simp only [hl, if_false]; exact ⟨le_rfl, hk1⟩
      · refine ⟨dir, Or.inr ?_⟩
        funext l
        by_cases hl : l = dir
        · subst hl; simp [unit]
        · simp [unit, hl]
    · intro w hw l
      have hwl : w l = if l = dir' then w l else (if l = dir then (k : ℤ) + 1 else 1) := by
        by_cases hl : l = dir'
        · simp [hl]
        · simp only [if_neg hl]; exact hw.2 l hl
      have hcoord : (w + (k : ℤ) • j - (k : ℤ) • i) l = w l + (k : ℤ) * (j l - i l) := by
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [hcoord]
      have hji : j l - i l = if l = dir then -1 else 0 := by
        have := congrFun hdir l
        by_cases hl : l = dir
        · subst hl; simp [unit] at this ⊢; linarith
        · simp [unit, hl] at this ⊢; linarith
      rw [hji]
      by_cases hl : l = dir'
      · have hld : l ≠ dir := by rw [hl]; exact hne
        simp only [hld, if_false, mul_zero, add_zero]
        rw [hl]; exact hw.1
      · by_cases hld : l = dir
        · have hwv : w l = (k : ℤ) + 1 := by
            have := hw.2 l hl
            simpa [hld] using this
          simp only [hld, if_true]
          rw [hld] at hwv
          rw [hwv]
          constructor <;> nlinarith
        · have hwv : w l = 1 := by
            have := hw.2 l hl
            simpa [hld] using this
          simp only [hld, if_false, mul_zero, add_zero]
          rw [hwv]; exact ⟨le_rfl, hk1⟩
  · -- `j = i + unit dir`: the cube `Q_k(i)` lies below `Q_k(j)`, at coordinate `0`
    refine ⟨dir', fun l => if l = dir then (0 : ℤ) else 1, ?_, ?_⟩
    · refine Or.inr ⟨?_, fun l => 1, ?_, ?_⟩
      · intro hcon
        have h := (hcon dir).1
        simp at h
      · intro l
        exact ⟨le_rfl, hk1⟩
      · refine ⟨dir, Or.inl ?_⟩
        funext l
        by_cases hl : l = dir
        · subst hl; simp [unit]
        · simp [unit, hl]
    · intro w hw l
      have hcoord : (w + (k : ℤ) • j - (k : ℤ) • i) l = w l + (k : ℤ) * (j l - i l) := by
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [hcoord]
      have hji : j l - i l = if l = dir then 1 else 0 := by
        have := congrFun hdir l
        by_cases hl : l = dir
        · subst hl; simp [unit] at this ⊢; linarith
        · simp [unit, hl] at this ⊢; linarith
      rw [hji]
      by_cases hl : l = dir'
      · have hld : l ≠ dir := by rw [hl]; exact hne
        simp only [hld, if_false, mul_zero, add_zero]
        rw [hl]; exact hw.1
      · by_cases hld : l = dir
        · have hwv : w dir = 0 := by
            have := hw.2 dir (by rw [← hld]; exact hl)
            simpa using this
          simp only [hld, if_true]
          rw [hwv]
          constructor <;> nlinarith
        · have hwv : w l = 1 := by
            have := hw.2 l hl
            simpa [hld] using this
          simp only [hld, if_false, mul_zero, add_zero]
          rw [hwv]; exact ⟨le_rfl, hk1⟩

/-- A good cube adjacent to a fired cube fires within `k^d` further steps. -/
theorem pclose_cube_step (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (N k : ℕ) (hN : 1 ≤ N) (hk : 1 ≤ k) (zc i j : Site d) (hgood : GoodAt η k j)
    (hij : (lattice d).Adj j i) (T : ℕ) (hfired : PCloseFired η N k zc T i) :
    PCloseFired η N k zc (T + k ^ d) j := by
  obtain ⟨dir', z, hz, hline⟩ := pclose_adj_line hd k hk i j hij
  refine pclose_cube_of_line hd η hlow hhigh N k hN zc j hgood dir' z hz T ?_
  intro w hw
  have h := hfired _ (hline w hw)
  have he : w + (k : ℤ) • j - (k : ℤ) • i + (k : ℤ) • i = w + (k : ℤ) • j := by abel
  rwa [he] at h

/-- Along a walk of good cubes, each step costs at most `k^d`. -/
theorem pclose_walk_fires (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (N k : ℕ) (hN : 1 ≤ N) (hk : 1 ≤ k) (zc : Site d) (m : ℕ) (c : ℕ → Site d)
    (hgood : ∀ s, s ≤ m → GoodAt η k (c s))
    (hadj : ∀ s, s < m → (lattice d).Adj (c s) (c (s + 1))) (T : ℕ)
    (h0 : PCloseFired η N k zc T (c 0)) :
    ∀ s, s ≤ m → PCloseFired η N k zc (T + s * k ^ d) (c s) := by
  intro s
  induction s with
  | zero => intro _; simpa using h0
  | succ s ih =>
    intro hs
    have h1 := ih (by omega)
    have h2 := pclose_cube_step hd η hlow hhigh N k hN hk zc (c s) (c (s + 1))
      (hgood (s + 1) hs) (hadj s (by omega)).symm _ h1
    have : T + s * k ^ d + k ^ d = T + (s + 1) * k ^ d := by ring
    rwa [this] at h2

end Exploding
