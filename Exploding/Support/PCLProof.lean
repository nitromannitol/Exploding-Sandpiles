/-
Support for Lemma 3.5 (`Exploding.Frozen.last_penultimate_cluster`): the crossing
comparison, the cube cover, the propagation step and the side bound for the
`N`-wave with `N ≥ 1`, without any hypothesis that the wave's centre lies outside
the cube being crossed.

The comparison `crossOdo ≤ wave` holds for `N = 1` at the centre too: at the
preimage of the centre the crossing odometer is at most `1` after the toppling
(`fodo_le_one` at the next time), and the wave is `N = 1` there.
-/
import Exploding.Support.Vocab
import Exploding.Support.Wave
import Exploding.Support.SubGeom
import Exploding.Support.SubStep
import Exploding.Support.SubCross
import Exploding.Support.SubFodo
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Exploding.Support.SubPen
import Exploding.Support.SubFinite

namespace Exploding

open LatticeProb Filter Asymptotics

variable {d : ℕ}

/-- The wave dominates the frozen odometer of a good cube once the frozen line is
already fired, for every `N ≥ 1`. -/
theorem pcl_crossOdo_le_wave {d : ℕ} (hd0 : (0 : ℤ) < 2 * (d : ℤ))
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
  intro s
  induction s with
  | zero =>
    intro y
    rw [crossOdo, fodo_zero]
    exact hseed0 y
  | succ s ih =>
    intro y
    rw [crossOdo, fodo_succ]
    by_cases hy : y ∈ (cube d k)ᶜ ∪ line d k dir' z
    · rw [if_pos hy]
      exact le_trans (hseed0 y) (hmono (s + 1) y)
    · rw [if_neg hy]
      have hyc : y ∈ cube d k := by
        by_contra h
        exact hy (Or.inl h)
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
        by_cases hz : y + (k : ℤ) • j = zc
        · -- at the centre the odometer after the toppling is at most `1 ≤ N`
          have hN1 : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
          have hc1 := hcap (s + 1) y
          rw [crossOdo, fodo_succ, if_neg hy, if_pos hc] at hc1
          rw [← hz, wave_at_centre]
          linarith
        · rw [wave_of_ne η N zc (y + (k : ℤ) • j) (t + s) hz]
          rw [Int.le_ediv_iff_mul_le (by positivity)]
          simp only [crossOdo] at hsum hc' hle1 ⊢
          nlinarith [hsum, hc', hle1]
      · rw [if_neg hc]
        simp only [crossOdo] at ih ⊢
        have h1 := ih y
        rw [show t + (s + 1) = t + s + 1 from by omega]
        linarith [h1, hmono']

/-- The cube cover from a line, for every `N ≥ 1`. -/
theorem pcl_wave_covers_of_line {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (N k : ℕ) (hN : 1 ≤ N)
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
  have hdom := pcl_crossOdo_le_wave hd0 η hlow hhigh N k hN zc j dir' z t hline n x
  have h1 : crossOdo (fun x => η (x + (k : ℤ) • j)) k dir' z n x = 1 := hcross x hx
  rw [h1] at hdom
  omega

/-- The propagation step from a covered cube to an adjacent good cube, for every
`N ≥ 1`, with no hypothesis on the position of the wave's centre. -/
theorem pcl_finite_exploding_step {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (N k : ℕ) (hN : 1 ≤ N) (hk : 1 ≤ k) (zc i j : Site d)
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
    exact pcl_wave_covers_of_line hd η hlow hhigh N k hN zc j hgoodj dir'
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
  exact pcl_wave_covers_of_line hd η hlow hhigh N k hN zc j hgoodj dir'
    (fun l : Fin d => if l = dir then (0 : ℤ) else 1) hz' t hline'

/-- **The propagation half of the side bound, for every `N = M̂ - 1 ≥ 1`.**  If the
penultimate wave from `zc` is positive on a line of a good cube `Q_k(i)` with
`i ∈ Cinf`, then the penultimate wave is positive on the cubes of the whole infinite
cluster, contradicting that its support is finite.  No hypothesis is placed on the
position of the wave's centre relative to the cubes. -/
theorem pcl_overlap_propagate_line {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (k : ℕ) (hk : 1 ≤ k) (Cinf : Set (Site d)) (hCinf : IsInfiniteConnectedGoodSet η k Cinf)
    (zc : Site d) (i : Site d) (hiCinf : i ∈ Cinf)
    (dir : Fin d) (z : Site d) (hz : z ∈ cube d k)
    (hline : ∀ w ∈ line d k dir z, 0 < penultimateWave η zc (w + (k : ℤ) • i))
    (hN : 1 ≤ waveThreshold η zc - 1)
    (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n zc) : False := by
  have hlow0 : ∀ x, 0 ≤ η x := fun x => by have := hlow x; linarith
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  -- the penultimate wave is positive at the line's base point
  have hzpos : 0 < penultimateWave η zc (z + (k : ℤ) • i) := hline z (by
    exact ⟨hz dir, fun l hl => rfl⟩)
  have h1 : waveThreshold η zc ≠ 1 := by
    intro h
    have hp : penultimateWave η zc = 0 := by simp [penultimateWave, h]
    rw [hp] at hzpos
    simp at hzpos
  have hN' : 1 ≤ waveThreshold η zc - 1 := hN
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  -- the penultimate wave is stabilizable, so its support is finite
  have hpenstab : WaveStabilizable η (waveThreshold η zc - 1) zc :=
    penultimate_stabilizable η zc hlast h1
  have hpenstab' := hpenstab
  obtain ⟨T, hT⟩ := hpenstab
  have hpen_eq : ∀ x : Site d,
      penultimateWave η zc x = wave η (waveThreshold η zc - 1) zc T x := by
    intro x
    simp only [penultimateWave, if_neg h1, waveTerminal]
    exact (congrFun (waveTerminal_spec η (waveThreshold η zc - 1) zc hpenstab' T
      (Nat.sInf_le hT)) x).symm
  have hpenfin : {x : Site d | 0 < penultimateWave η zc x}.Finite := by
    refine Set.Finite.subset (Set.finite_Icc (zc - fun _ => (T : ℤ)) (zc + fun _ => (T : ℤ))) ?_
    intro x hx
    have hx' : 0 < penultimateWave η zc x := hx
    rw [hpen_eq x] at hx'
    constructor
    · intro i
      by_contra hcon
      have hcon' : zc i - (T : ℤ) > x i := not_le.mp hcon
      have hsp := aux_finite_exploding_speed η hlow0 hhigh (waveThreshold η zc - 1) zc T x
      have hm : (T : ℤ) < mnorm (x - zc) := by
        have h1' : (T : ℤ) < zc i - x i := by linarith
        have h2' : zc i - x i ≤ mnorm (x - zc) := by
          have := abs_coord_le_mnorm (x - zc) i
          rw [show (x - zc) i = x i - zc i from rfl] at this
          rw [abs_of_neg (by linarith : x i - zc i < 0)] at this
          linarith
        linarith
      rw [hsp hm] at hx'
      exact lt_irrefl 0 hx'
    · intro i
      by_contra hcon
      have hcon' : x i > zc i + (T : ℤ) := not_le.mp hcon
      have hsp := aux_finite_exploding_speed η hlow0 hhigh (waveThreshold η zc - 1) zc T x
      have hm : (T : ℤ) < mnorm (x - zc) := by
        have h1' : (T : ℤ) < x i - zc i := by linarith
        have h2' : x i - zc i ≤ mnorm (x - zc) := by
          have := abs_coord_le_mnorm (x - zc) i
          rw [show (x - zc) i = x i - zc i from rfl] at this
          rw [abs_of_pos (by linarith : 0 < x i - zc i)] at this
          exact this
        linarith
      rw [hsp hm] at hx'
      exact lt_irrefl 0 hx'
  -- the (M̂-1)-wave is positive on the line at time T
  have hline' : ∀ w ∈ line d k dir z,
      0 < wave η (waveThreshold η zc - 1) zc T (w + (k : ℤ) • i) := by
    intro w hw
    rw [← hpen_eq]
    exact hline w hw
  obtain ⟨t', ht'⟩ := pcl_wave_covers_of_line hd η hlow0 hhigh (waveThreshold η zc - 1) k hN' zc i
    (hCinf.2.1 hiCinf) dir z (Or.inl hz) T hline'
  -- the penultimate wave is positive on Q_k(i)
  have hcov : ∀ x ∈ cube d k, 0 < penultimateWave η zc (x + (k : ℤ) • i) := by
    intro x hx
    rw [hpen_eq]
    have hpos := ht'.2 x hx
    have hmono := wave_mono_time η hlow0 hd0 (waveThreshold η zc - 1) zc (le_max_right T t')
      (x + (k : ℤ) • i)
    have hmax : 0 < wave η (waveThreshold η zc - 1) zc (max T t') (x + (k : ℤ) • i) := by linarith
    rw [← hT (max T t') (le_max_left T t')]
    exact hmax
  -- propagate to every cube of the cluster
  have hreach' : ∀ y ∈ Cinf, ∃ t, ∀ x ∈ cube d k,
      0 < wave η (waveThreshold η zc - 1) zc t (x + (k : ℤ) • y) := by
    intro y hy
    have hstep : ∀ (a b : Site d), GoodAt η k b → (lattice d).Adj a b → ∀ s : ℕ,
        (∀ x ∈ cube d k, 0 < wave η (waveThreshold η zc - 1) zc s (x + (k : ℤ) • a)) →
        ∃ s' : ℕ, s ≤ s' ∧
          ∀ x ∈ cube d k, 0 < wave η (waveThreshold η zc - 1) zc s' (x + (k : ℤ) • b) := by
      intro a b hgood hadj s hs
      obtain ⟨dir', hdir'⟩ := hadj
      obtain ⟨dir'', hne⟩ : ∃ dir'' : Fin d, dir'' ≠ dir' := by
        by_contra hcon
        simp only [not_exists, not_not] at hcon
        have hcard : Fintype.card (Fin d) = 1 := Fintype.card_eq_one_iff.mpr ⟨dir', hcon⟩
        rw [Fintype.card_fin] at hcard
        omega
      exact pcl_finite_exploding_step hd η hlow0 hhigh (waveThreshold η zc - 1) k hN' hk zc a b
        hgood dir' hdir' dir'' hne s hs
    obtain ⟨t'', ht''⟩ := aux_finite_exploding_propagate_walk η hlow0 hhigh
      (waveThreshold η zc - 1) k zc Cinf hCinf.2.1 hstep i y (hCinf.2.2 i hiCinf y hy) t' ht'.2
    exact ⟨t'', ht''⟩
  -- so the penultimate wave is positive on Q_k(y) for every y in the cluster
  have hpeninf : {x : Site d | 0 < penultimateWave η zc x}.Infinite := by
    have hinj : Function.Injective (fun y : Site d => (fun _ => (1 : ℤ)) + (k : ℤ) • y) := by
      intro y1 y2 h
      have h1 := congrFun h
      ext i
      have h2 := h1 i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h2
      have hk0 : (k : ℤ) ≠ 0 := by
        intro hkz
        have : k = 0 := by exact_mod_cast hkz
        omega
      have : (k : ℤ) * y1 i = (k : ℤ) * y2 i := by linarith
      exact mul_left_cancel₀ hk0 this
    have himg : (fun y : Site d => (fun _ => (1 : ℤ)) + (k : ℤ) • y) '' Cinf ⊆
        {x : Site d | 0 < penultimateWave η zc x} := by
      rintro x ⟨y, hy, rfl⟩
      obtain ⟨t, ht⟩ := hreach' y hy
      have hpos := ht _ (fun l => ⟨le_refl 1, hk1⟩)
      have hmono := wave_mono_time η hlow0 hd0 (waveThreshold η zc - 1) zc (le_max_right T t)
        ((fun _ => (1 : ℤ)) + (k : ℤ) • y)
      have hmax : 0 < wave η (waveThreshold η zc - 1) zc (max T t)
          ((fun _ => (1 : ℤ)) + (k : ℤ) • y) := by linarith
      show 0 < penultimateWave η zc ((fun _ => (1 : ℤ)) + (k : ℤ) • y)
      rw [hpen_eq, ← hT (max T t) (le_max_left T t)]
      exact hmax
    exact (hCinf.1.image hinj.injOn).mono himg
  exact hpeninf hpenfin

/-- **The side bound for every `M̂`.**  If the penultimate wave from `zc` is positive
on a segment of length `(2 (log n)^(5/2) + 6) k` in a coordinate direction whose
cube-base points lie in `cent d n`, then `zc` is not a counterexample to
`hlast`.  This is `aux_penultimate_segment_bound'` with the `M̂ = 2` input `hcov_zc`
removed: the cover comparison `pcl_crossOdo_le_wave` holds at the wave's centre. -/
theorem pcl_segment_bound {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (k : ℕ) (hk : 1 ≤ k) (Cinf : Set (Site d)) (hCinf : IsInfiniteConnectedGoodSet η k Cinf)
    (zc : Site d)
    (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n zc)
    (n0 : ℕ)
    (hcomp : ∀ n, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ Cinf →
      (componentIn Cinfᶜ x).Finite ∧
        ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2))
    (n : ℕ) (hn : n0 ≤ n) (l : Fin d) (c : Site d) (a b : ℤ)
    (hlog : 0 ≤ Real.log n ^ ((5 : ℝ) / 2))
    (hab : ((2 * Real.log n ^ ((5 : ℝ) / 2) + 6) * (k : ℝ)) ≤ ((b - a : ℤ) : ℝ))
    (hin' : ∀ v : ℤ, (a - 1) / (k : ℤ) + 1 ≤ v → v ≤ (b - (k : ℤ)) / (k : ℤ) →
      (fun j => if j = l then v else (c j - 1) / (k : ℤ)) ∈ (cent d n : Set (Site d)))
    (hpos : ∀ v : ℤ, a ≤ v → v ≤ b →
      0 < penultimateWave η zc (fun j => if j = l then v else c j)) :
    False := by
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hk0 : (0 : ℤ) < (k : ℤ) := by linarith
  obtain ⟨i, hiC, hline⟩ :=
    aux_segment_meets_cinf_line' k hk Cinf n0 hcomp n hn l c a b hlog hab hin'
  have hz : (fun j => if j = l then 1 else 1 + (c j - 1) % (k : ℤ)) ∈ cube d k := by
    intro j
    have hval : (fun j' => if j' = l then (1 : ℤ) else 1 + (c j' - 1) % (k : ℤ)) j =
        (if j = l then (1 : ℤ) else 1 + (c j - 1) % (k : ℤ)) := rfl
    rw [hval]
    split_ifs with hj
    · exact ⟨le_refl 1, hk1⟩
    · have h2 : 0 ≤ (c j - 1) % (k : ℤ) := Int.emod_nonneg _ (by linarith)
      have h3 : (c j - 1) % (k : ℤ) < (k : ℤ) := Int.emod_lt_of_pos _ hk0
      constructor <;> linarith
  have hline' : ∀ w ∈ line d k l (fun j => if j = l then 1 else 1 + (c j - 1) % (k : ℤ)),
      0 < penultimateWave η zc (w + (k : ℤ) • i) := by
    intro w hw
    obtain ⟨hlo, hhi, hoth⟩ := hline w hw
    have hfun : (fun j => if j = l then (w + (k : ℤ) • i) l else c j) = (w + (k : ℤ) • i) := by
      ext j
      by_cases hj : j = l
      · subst hj; simp only [if_true]
      · simp only [if_neg hj]
        exact (hoth j hj).symm
    rw [← hfun]
    exact hpos _ hlo hhi
  have hlow0 : ∀ x, 0 ≤ η x := fun x => by linarith [hlow x]
  have hzpos : 0 < penultimateWave η zc
      ((fun j => if j = l then 1 else 1 + (c j - 1) % (k : ℤ)) + (k : ℤ) • i) :=
    hline' _ (by
      refine ⟨⟨?_, ?_⟩, fun j hj => rfl⟩
      · show (1 : ℤ) ≤ (if l = l then (1 : ℤ) else 1 + (c l - 1) % (k : ℤ))
        rw [if_pos rfl]
      · show (if l = l then (1 : ℤ) else 1 + (c l - 1) % (k : ℤ)) ≤ (k : ℤ)
        rw [if_pos rfl]; exact hk1)
  obtain ⟨h2, _⟩ := aux_penultimate_hlast η hlow0 hhigh zc _ hzpos
  exact pcl_overlap_propagate_line hd η hlow hhigh k hk Cinf hCinf zc i hiC
    l (fun j => if j = l then 1 else 1 + (c j - 1) % (k : ℤ)) hz hline' (by omega) hlast

/-- The polylogarithmic function `(2 (log 3x)^(5/2) + 6) k` is eventually below `x`. -/
theorem pcl_eventually_small (k : ℕ) :
    ∃ A : ℝ, ∀ x : ℝ, A ≤ x → (2 * Real.log (3 * x) ^ ((5:ℝ)/2) + 6) * (k:ℝ) ≤ x := by
  have h1 := isLittleO_log_rpow_rpow_atTop (5/2 : ℝ) (one_pos : (0:ℝ) < 1)
  have h2 := h1.comp_tendsto (Filter.tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 3))
  have hc : (0:ℝ) < 1 / (12 * ((k:ℝ) + 1)) := by positivity
  have h3 := h2.def hc
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.1 (h3.and (Filter.eventually_ge_atTop (12 * (k:ℝ) + 1)))
  refine ⟨max A 1, fun x hx => ?_⟩
  have hxA : A ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : (1:ℝ) ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hh, hxk⟩ := hA x hxA
  simp only [Function.comp, id] at hh
  have hlog : 0 ≤ Real.log (3 * x) := Real.log_nonneg (by linarith)
  have hL : 0 ≤ Real.log (3 * x) ^ ((5:ℝ)/2) := Real.rpow_nonneg hlog _
  rw [Real.norm_of_nonneg hL, Real.rpow_one, Real.norm_of_nonneg (by linarith)] at hh
  have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  have hkpos : (0:ℝ) < (k:ℝ) + 1 := by linarith
  have h4 : 12 * ((k:ℝ) + 1) * Real.log (3 * x) ^ ((5:ℝ)/2) ≤ 3 * x := by
    have := mul_le_mul_of_nonneg_left hh (by positivity : (0:ℝ) ≤ 12 * ((k:ℝ) + 1))
    have h5 : 12 * ((k:ℝ) + 1) * (1 / (12 * ((k:ℝ) + 1)) * (3 * x)) = 3 * x := by
      field_simp
    linarith
  -- `2 k L ≤ x / 2`
  have h6 : 2 * (k:ℝ) * Real.log (3 * x) ^ ((5:ℝ)/2) ≤ x / 2 := by
    nlinarith [h4, hL, hk0]
  nlinarith [h6, hxk, hk0]

/-- The shifted length bound is below the exponent `5/2 + 1` of the statement once
`log n` is large in terms of `k`. -/
theorem pcl_log_shift (k : ℕ) (n : ℕ) (hn : Nat.ceil (Real.exp (22 * (k:ℝ) + 23)) ≤ n) :
    (2 * (Real.log n + Real.log 8) ^ ((5:ℝ)/2) + 6) * (k:ℝ) + 1 ≤
      Real.log n ^ ((5:ℝ)/2 + 1) := by
  have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  have h1 : Real.exp (22 * (k:ℝ) + 23) ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have hlam : 22 * (k:ℝ) + 23 ≤ Real.log n := by
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at h2
  set lam := Real.log n with hlamdef
  have hlam0 : 0 < lam := by linarith
  have hlam1 : 1 ≤ lam := by linarith
  have h8 : Real.log 8 ≤ 7 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 8)
    linarith
  have h2 : lam + Real.log 8 ≤ 2 * lam := by linarith
  have h3 : (lam + Real.log 8) ^ ((5:ℝ)/2) ≤ (2 * lam) ^ ((5:ℝ)/2) :=
    Real.rpow_le_rpow (by linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 8)]) h2 (by norm_num)
  have h4 : (2 * lam) ^ ((5:ℝ)/2) = 2 ^ ((5:ℝ)/2) * lam ^ ((5:ℝ)/2) :=
    Real.mul_rpow (by norm_num) hlam0.le
  have h5 : (2:ℝ) ^ ((5:ℝ)/2) ≤ 8 := by
    have : (2:ℝ) ^ ((5:ℝ)/2) ≤ (2:ℝ) ^ ((3:ℕ):ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    rw [Real.rpow_natCast] at this
    linarith
  have hp1 : 1 ≤ lam ^ ((5:ℝ)/2) := Real.one_le_rpow hlam1 (by norm_num)
  have hp0 : 0 ≤ lam ^ ((5:ℝ)/2) := by linarith
  have h6 : (lam + Real.log 8) ^ ((5:ℝ)/2) ≤ 8 * lam ^ ((5:ℝ)/2) := by
    calc (lam + Real.log 8) ^ ((5:ℝ)/2) ≤ (2 * lam) ^ ((5:ℝ)/2) := h3
      _ = 2 ^ ((5:ℝ)/2) * lam ^ ((5:ℝ)/2) := h4
      _ ≤ 8 * lam ^ ((5:ℝ)/2) := by nlinarith
  have h7 : lam ^ ((5:ℝ)/2 + 1) = lam ^ ((5:ℝ)/2) * lam := by
    rw [Real.rpow_add hlam0, Real.rpow_one]
  rw [h7]
  have h9 : (2 * (lam + Real.log 8) ^ ((5:ℝ)/2) + 6) * (k:ℝ) ≤ 22 * (k:ℝ) * lam ^ ((5:ℝ)/2) := by
    nlinarith [h6, hp1, hk0]
  nlinarith [h9, hp1, hlam, hk0]

/-- The threshold on `n` that the length bound of Lemma 3.5 needs, depending only on
the cube size `k`. -/
theorem pcl_thresh_spec (k : ℕ) :
    ∃ N : ℕ, 8 ≤ N ∧ k ≤ N ∧
      (∀ n : ℕ, N ≤ n → (2 * (Real.log n + Real.log 8) ^ ((5:ℝ)/2) + 6) * (k:ℝ) + 1 ≤
        Real.log n ^ ((5:ℝ)/2 + 1)) ∧
      (∀ L : ℝ, (N : ℝ) ≤ L → (2 * Real.log (3 * L) ^ ((5:ℝ)/2) + 6) * (k:ℝ) ≤ L) := by
  obtain ⟨A, hA⟩ := pcl_eventually_small k
  set N : ℕ := max (max 8 k) (max (Nat.ceil (Real.exp (22 * (k:ℝ) + 23))) (Nat.ceil A)) with hN
  have h8 : 8 ≤ N := by
    have : 8 ≤ max 8 k := le_max_left _ _
    exact le_trans this (le_max_left _ _)
  have hk : k ≤ N := by
    have : k ≤ max 8 k := le_max_right _ _
    exact le_trans this (le_max_left _ _)
  have hexp : Nat.ceil (Real.exp (22 * (k:ℝ) + 23)) ≤ N := by
    have : Nat.ceil (Real.exp (22 * (k:ℝ) + 23)) ≤ max (Nat.ceil (Real.exp (22 * (k:ℝ) + 23)))
        (Nat.ceil A) := le_max_left _ _
    exact le_trans this (le_max_right _ _)
  have hceil : Nat.ceil A ≤ N := by
    have : Nat.ceil A ≤ max (Nat.ceil (Real.exp (22 * (k:ℝ) + 23))) (Nat.ceil A) := le_max_right _ _
    exact le_trans this (le_max_right _ _)
  refine ⟨N, h8, hk, ?_, ?_⟩
  · intro n hn
    exact pcl_log_shift k n (le_trans hexp hn)
  · intro L hL
    apply hA
    have h1 : (Nat.ceil A : ℝ) ≤ (N : ℝ) := by exact_mod_cast hceil
    exact le_trans (Nat.le_ceil A) (le_trans h1 hL)

/-- **The side length bound of Lemma 3.5.**  If the penultimate wave from `zc` is
positive on the segment `[a, b]` through `c` in direction `l`, and its cube-base points lie
in `cent d n'` for `n' = n + (b - a) + k + 4`, then `b - a + 1 ≤ (log n)^(5/2 + 1)` for
`n` beyond a threshold depending on `k` only. -/
theorem pcl_length_final {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (k : ℕ) (hk : 1 ≤ k) (Cinf : Set (Site d)) (hCinf : IsInfiniteConnectedGoodSet η k Cinf)
    (zc : Site d) (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n zc)
    (n0 : ℕ)
    (hcomp : ∀ n, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ Cinf →
      (componentIn Cinfᶜ x).Finite ∧
        ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2))
    (N : ℕ) (hN8 : 8 ≤ N) (hNk : k ≤ N)
    (hN1 : ∀ n : ℕ, N ≤ n → (2 * (Real.log n + Real.log 8) ^ ((5:ℝ)/2) + 6) * (k:ℝ) + 1 ≤
        Real.log n ^ ((5:ℝ)/2 + 1))
    (hN2 : ∀ L : ℝ, (N : ℝ) ≤ L → (2 * Real.log (3 * L) ^ ((5:ℝ)/2) + 6) * (k:ℝ) ≤ L)
    (n : ℕ) (hn0 : n0 ≤ n) (hnN : N ≤ n) (l : Fin d) (c : Site d) (a b : ℤ) (hab : a ≤ b)
    (hin' : ∀ v : ℤ, (a - 1) / (k : ℤ) + 1 ≤ v → v ≤ (b - (k : ℤ)) / (k : ℤ) →
      (fun j => if j = l then v else (c j - 1) / (k : ℤ)) ∈
        (cent d (n + (b - a).toNat + k + 4) : Set (Site d)))
    (hpos : ∀ v : ℤ, a ≤ v → v ≤ b →
      0 < penultimateWave η zc (fun j => if j = l then v else c j)) :
    ((b - a : ℤ) : ℝ) + 1 ≤ Real.log n ^ ((5:ℝ)/2 + 1) := by
  set L : ℤ := b - a with hL
  have hL0 : 0 ≤ L := by omega
  set n' : ℕ := n + L.toNat + k + 4 with hn'
  have hn'1 : 1 ≤ n' := by omega
  have hlog : 0 ≤ Real.log n' ^ ((5:ℝ)/2) :=
    Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hn'1)) _
  -- the side bound: the segment is shorter than the threshold at radius `n'`
  have hlt : (L : ℝ) < (2 * Real.log n' ^ ((5:ℝ)/2) + 6) * (k:ℝ) := by
    by_contra hcon
    rw [not_lt] at hcon
    exact pcl_segment_bound hd η hlow hhigh k hk Cinf hCinf zc hlast n0 hcomp n'
      (by omega) l c a b hlog hcon hin' hpos
  by_cases hL2 : L ≤ 2 * (n : ℤ) + 1
  · -- the self-referential length bound
    have htoNat : (((n : ℤ) + L + (k : ℤ) + 4).toNat) = n' := by omega
    have hbig : (L : ℝ) < (2 * Real.log ((((n : ℤ) + L + (k : ℤ) + 4).toNat : ℕ) : ℝ) ^
        ((5:ℝ)/2) + 6) * (k : ℝ) := by
      rw [htoNat]; exact hlt
    have h1 := aux_length_bound k k hk (n : ℤ) L (by omega) (by omega) hL0 hL2 hbig
    have h2 := hN1 n hnN
    simp only [Int.cast_natCast] at h1
    linarith
  · -- `L > 2n + 1`: then `n' ≤ 3 L` and the threshold `hN2` contradicts `hlt`
    exfalso
    rw [not_le] at hL2
    have hn'le : (n' : ℤ) ≤ 3 * L := by rw [hn']; push_cast; omega
    have hn'leR : (n' : ℝ) ≤ 3 * (L : ℝ) := by exact_mod_cast hn'le
    have hNL : (N : ℝ) ≤ (L : ℝ) := by
      have : (N : ℤ) ≤ L := by omega
      exact_mod_cast this
    have hlogle : Real.log (n' : ℝ) ≤ Real.log (3 * (L : ℝ)) :=
      Real.log_le_log (by exact_mod_cast hn'1) hn'leR
    have hpow : Real.log (n' : ℝ) ^ ((5:ℝ)/2) ≤ Real.log (3 * (L : ℝ)) ^ ((5:ℝ)/2) :=
      Real.rpow_le_rpow (Real.log_nonneg (by exact_mod_cast hn'1)) hlogle (by norm_num)
    have hk0 : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h3 := hN2 (L : ℝ) hNL
    nlinarith [hpow, hk0, h3, hlt]

end Exploding
