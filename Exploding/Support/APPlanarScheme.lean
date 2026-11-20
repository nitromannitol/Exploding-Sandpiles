/-
The frame block scheme of the square lattice and the chemical-distance bound in two dimensions.

At scale `2m + 1` with windows of radius one, the predicate `frameGood m` with cores
`frameCore m` is a block scheme: it is local, a site of a good block that leaves its window
reaches the core (`frame_enclosure`), the core is connected, and the cores of star-adjacent good
blocks are joined because the core of one block runs from inside the other block to outside its
window.  Each of the four rectangles of a frame is a translate of the `3N × N` rectangle or of its
transpose, so a block is bad with probability at most four times the probability that the
`3N × N` rectangle has no open long-way crossing.  Above `bondCritical 2 ≥ 1/2` this tends to
zero (Bollobás–Riordan, *Percolation* (2006), Ch. 3, Lemma 9, proved in Lattice-Probability),
and the renormalization step gives the Antal–Pisztora bound for every supercritical density in
two dimensions.
-/
import Exploding.Support.APPlanarFrame
import Exploding.Support.APPlanarCritical
import Exploding.Support.APBlockReduction

open LatticeProb Relation LQGMetric MeasureTheory Filter Topology
open scoped ENNReal

namespace Exploding

/-! ### Locality -/

theorem xap_reach_congr_of_window {N r : ℕ} {b : Site 2} {ω ω' : Site 2 × Fin 2 → Bool}
    (h : ∀ e ∈ windowBonds N r b, ω e = ω' e) {S : Set (Site 2)}
    (hS : S ⊆ coarseWindow N r b) {a z : Site 2} (hω : xap_Reach ω S a z) : xap_Reach ω' S a z := by
  refine ⟨hω.1, xap_rtg_mono (fun x y hxy => ⟨hxy.1, hxy.2.1, ?_⟩) hω.2⟩
  obtain ⟨hx, hy, hadj⟩ := hxy
  rw [openBondGraph, SimpleGraph.fromRel_adj] at hadj ⊢
  obtain ⟨hne, ⟨i, rfl, hi⟩ | ⟨i, rfl, hi⟩⟩ := hadj
  · exact ⟨hne, Or.inl ⟨i, rfl, by rw [← h (x, i) ⟨hS hx, hS hy⟩]; exact hi⟩⟩
  · exact ⟨hne, Or.inr ⟨i, rfl, by rw [← h (y, i) ⟨hS hy, hS hx⟩]; exact hi⟩⟩

theorem frameGood_isLocal (m : ℕ) : IsLocalBlockPredicate (2 * m + 1) 1 (frameGood m) := by
  have key : ∀ b (ω ω' : Site 2 × Fin 2 → Bool), (∀ e ∈ windowBonds (2 * m + 1) 1 b, ω e = ω' e) →
      frameGood m ω b → frameGood m ω' b := by
    intro b ω ω' h hg dir
    obtain ⟨a, e, ha, he, hae⟩ := hg dir
    exact ⟨a, e, ha, he, xap_reach_congr_of_window h (frameRect_subset_window m b dir) hae⟩
  intro b ω ω' h
  exact ⟨key b ω ω' h, key b ω' ω fun e he => (h e he).symm⟩

/-! ### Points of the core of a neighbouring block -/

theorem annLong_adj4 (d : PercDir) {x y : ℤ × ℤ} (h : PercAdj4 x y) :
    -annLong d y ≤ -annLong d x + 1 ∧ -annLong d x ≤ -annLong d y + 1 := by
  cases d <;> simp only [annLong, PercAdj4] at h ⊢ <;> omega

/-- A long-way crossing passes through every level along its rectangle. -/
theorem frameCross_hits {m : ℕ} {ω : Site 2 × Fin 2 → Bool} {b : Site 2} {d : PercDir}
    {a e : Site 2} (h : FrameCross m ω b d a e) {t : ℤ} (ht0 : -(3 * (m : ℤ) + 1) ≤ t)
    (ht1 : t ≤ 3 * m + 1) :
    ∃ z, xap_Reach ω (frameRect m b d) a z ∧ annLong d (framePlane m b z) = t := by
  obtain ⟨ha, he, hae⟩ := h
  have hP := frame_lift_reach (T := annRect ((m : ℤ) + 1) (3 * m + 1) d) (fun z hz => hz) hae
  obtain ⟨c, hc, hac⟩ := perc_first_reach (fun p => -annLong d p)
    (fun x y h => annLong_adj4 d h) (-t) hP
    (by show -t ≤ -annLong d (framePlane m b a); rw [ha]; omega)
    (by show -annLong d (framePlane m b e) ≤ -t; rw [he]; omega)
  have hcS := PercAnn.rtg_end_mem hac ⟨⟨hae.1, ⟨a, xap_reach_refl hae.1, rfl⟩⟩,
    by show -t ≤ -annLong d (framePlane m b a); rw [ha]; omega⟩
  obtain ⟨z, hz, rfl⟩ := hcS.1.2
  exact ⟨z, hz, neg_injective hc⟩

theorem framePlane_shift (m : ℕ) (b b' z : Site 2) :
    framePlane m b z = ((framePlane m b' z).1 + (2 * m + 1) * (b' 0 - b 0),
      (framePlane m b' z).2 + (2 * m + 1) * (b' 1 - b 1)) := by
  simp only [framePlane, Prod.mk.injEq]
  constructor <;> ring

/-- If `b'` is a good star-neighbour of `b`, the core of `b'` has a site in the block `b` and a
site outside the window of `b`. -/
theorem frameCore_link_points {m : ℕ} {ω : Site 2 × Fin 2 → Bool} {b b' : Site 2}
    (hgood : frameGood m ω b') (hbb : xmh_star b b') :
    (∃ u ∈ frameCore m ω b', coarseSite (2 * m + 1) u = b) ∧
      ∃ e ∈ frameCore m ω b', e ∉ coarseWindow (2 * m + 1) 1 b := by
  obtain ⟨hne, hclose⟩ := hbb
  have h0 := hclose 0
  have h1 := hclose 1
  rw [abs_le] at h0 h1
  have hne' : b 0 ≠ b' 0 ∨ b 1 ≠ b' 1 := by
    by_contra hcon
    push Not at hcon
    exact hne (funext fun i => by fin_cases i <;> simp [hcon.1, hcon.2])
  have hblock : ∀ u, coarseSite (2 * m + 1) u = b ↔
      (-((m : ℤ) + 1) < (framePlane m b' u).1 + (2 * m + 1) * (b' 0 - b 0) ∧
        (framePlane m b' u).1 + (2 * m + 1) * (b' 0 - b 0) < (m : ℤ) + 1 ∧
        -((m : ℤ) + 1) < (framePlane m b' u).2 + (2 * m + 1) * (b' 1 - b 1) ∧
        (framePlane m b' u).2 + (2 * m + 1) * (b' 1 - b 1) < (m : ℤ) + 1) := by
    intro u
    rw [coarseSite_eq_iff_framePlane, framePlane_shift m b b' u]
  have hwin : ∀ e, e ∈ coarseWindow (2 * m + 1) 1 b ↔
      annBox (3 * m + 1) ((framePlane m b' e).1 + (2 * m + 1) * (b' 0 - b 0),
        (framePlane m b' e).2 + (2 * m + 1) * (b' 1 - b 1)) := by
    intro e
    rw [mem_coarseWindow_iff_annBox, framePlane_shift m b b' e]
  have hcore : ∀ d a e, FrameCross m ω b' d a e → ∀ z,
      xap_Reach ω (frameRect m b' d) a z → z ∈ frameCore m ω b' ∧ z ∈ frameRect m b' d :=
    fun d a e h z hz => ⟨⟨d, a, e, h, hz⟩, xap_reach_mem_right hz⟩
  -- the side of `b'` facing `b` and the opposite side
  have hside : ∃ d d' : PercDir, (∃ t : ℤ, -(3 * (m : ℤ) + 1) ≤ t ∧ t ≤ 3 * m + 1 ∧
      ∀ z, framePlane m b' z ∈ annRect ((m : ℤ) + 1) (3 * m + 1) d →
        annLong d (framePlane m b' z) = t → coarseSite (2 * m + 1) z = b) ∧
      ∀ z, framePlane m b' z ∈ annRect ((m : ℤ) + 1) (3 * m + 1) d' →
        z ∉ coarseWindow (2 * m + 1) 1 b := by
    rcases lt_trichotomy (b' 0 - b 0) 0 with hδ | hδ | hδ
    · refine ⟨.R, .L, ⟨-(2 * m + 1) * (b' 1 - b 1), by nlinarith, by nlinarith, ?_⟩, ?_⟩
      · intro z hz hzt
        obtain ⟨⟨_, _, _, _⟩, hdir⟩ := hz
        simp only [annLong, annDir] at hzt hdir
        rw [hblock]
        have : b' 0 - b 0 = -1 := by omega
        rw [this]
        refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
      · intro z hz hzW
        obtain ⟨⟨_, _, _, _⟩, hdir⟩ := hz
        simp only [annDir] at hdir
        rw [hwin] at hzW
        obtain ⟨hw1, -, -, -⟩ := hzW
        have : b' 0 - b 0 = -1 := by omega
        rw [this] at hw1
        nlinarith
    · have hδ1 : b' 1 - b 1 ≠ 0 := by
        rcases hne' with h | h
        · omega
        · omega
      rcases lt_or_gt_of_ne hδ1 with hδ1 | hδ1
      · refine ⟨.T, .B, ⟨0, by omega, by omega, ?_⟩, ?_⟩
        · intro z hz hzt
          obtain ⟨⟨_, _, _, _⟩, hdir⟩ := hz
          simp only [annLong, annDir] at hzt hdir
          rw [hblock, hδ]
          have : b' 1 - b 1 = -1 := by omega
          rw [this]
          refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
        · intro z hz hzW
          obtain ⟨⟨_, _, _, _⟩, hdir⟩ := hz
          simp only [annDir] at hdir
          rw [hwin] at hzW
          obtain ⟨-, -, hw3, -⟩ := hzW
          have : b' 1 - b 1 = -1 := by omega
          rw [this] at hw3
          nlinarith
      · refine ⟨.B, .T, ⟨0, by omega, by omega, ?_⟩, ?_⟩
        · intro z hz hzt
          obtain ⟨⟨_, _, _, _⟩, hdir⟩ := hz
          simp only [annLong, annDir] at hzt hdir
          rw [hblock, hδ]
          have : b' 1 - b 1 = 1 := by omega
          rw [this]
          refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
        · intro z hz hzW
          obtain ⟨⟨_, _, _, _⟩, hdir⟩ := hz
          simp only [annDir] at hdir
          rw [hwin] at hzW
          obtain ⟨-, -, -, hw4⟩ := hzW
          have : b' 1 - b 1 = 1 := by omega
          rw [this] at hw4
          nlinarith
    · refine ⟨.L, .R, ⟨-(2 * m + 1) * (b' 1 - b 1), by nlinarith, by nlinarith, ?_⟩, ?_⟩
      · intro z hz hzt
        obtain ⟨⟨_, _, _, _⟩, hdir⟩ := hz
        simp only [annLong, annDir] at hzt hdir
        rw [hblock]
        have : b' 0 - b 0 = 1 := by omega
        rw [this]
        refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
      · intro z hz hzW
        obtain ⟨⟨_, _, _, _⟩, hdir⟩ := hz
        simp only [annDir] at hdir
        rw [hwin] at hzW
        obtain ⟨-, hw2, -, -⟩ := hzW
        have : b' 0 - b 0 = 1 := by omega
        rw [this] at hw2
        nlinarith
  obtain ⟨d, d', ⟨t, ht0, ht1, hblk⟩, hout⟩ := hside
  obtain ⟨a, e, hcross⟩ := hgood d
  obtain ⟨z, hz, hzt⟩ := frameCross_hits hcross ht0 ht1
  obtain ⟨a', e', hcross'⟩ := hgood d'
  obtain ⟨hzc, hzR⟩ := hcore d a e hcross z hz
  obtain ⟨ha'c, ha'R⟩ := hcore d' a' e' hcross' a' (xap_reach_refl hcross'.2.2.1)
  exact ⟨⟨z, hzc, hblk z hzR hzt⟩, ⟨a', ha'c, hout a' ha'R⟩⟩

/-! ### The frame is a block scheme -/

theorem frame_blockLinks (m : ℕ) (ω : Site 2 × Fin 2 → Bool) :
    BlockLinks (2 * m + 1) 1 ω (frameGood m ω) (frameCore m ω) where
  nonempty b hb := by
    obtain ⟨a, e, h⟩ := hb .T
    exact ⟨a, .T, a, e, h, xap_reach_refl h.2.2.1⟩
  attach u hu hleave := by
    obtain ⟨e, he, hue⟩ := hleave
    obtain ⟨z, hz, huz⟩ := frame_enclosure (S := Set.univ) hu rfl he
      ⟨Set.mem_univ u, xap_rtg_mono (fun x y hxy => ⟨Set.mem_univ x, Set.mem_univ y, hxy⟩)
        ((SimpleGraph.reachable_iff_reflTransGen _ _).mp hue)⟩
    exact ⟨z, hz, xap_reach_mono Set.inter_subset_right huz⟩
  inner b hb c hc c' hc' :=
    xap_reach_mono (frameAnnulus_subset_window m b) (frameCore_connected hb hc hc')
  link b b' hb hb' hbb c hc c' hc' := by
    obtain ⟨⟨u, hu, hub⟩, ⟨e, he, heb⟩⟩ := frameCore_link_points hb' hbb
    have hue : xap_Reach ω (coarseWindow (2 * m + 1) 1 b') u e :=
      xap_reach_mono (frameAnnulus_subset_window m b') (frameCore_connected hb' hu he)
    obtain ⟨z, hz, huz⟩ := frame_enclosure hb hub heb hue
    have h1 : xap_Reach ω (coarseWindow (2 * m + 1) 1 b ∪ coarseWindow (2 * m + 1) 1 b') c z :=
      xap_reach_mono (frameAnnulus_subset_window m b |>.trans Set.subset_union_left)
        (frameCore_connected hb hc hz)
    have h2 : xap_Reach ω (coarseWindow (2 * m + 1) 1 b ∪ coarseWindow (2 * m + 1) 1 b') z u :=
      xap_reach_symm (xap_reach_mono (Set.inter_subset_left.trans Set.subset_union_right) huz)
    have h3 : xap_Reach ω (coarseWindow (2 * m + 1) 1 b ∪ coarseWindow (2 * m + 1) 1 b') u c' :=
      xap_reach_mono (frameAnnulus_subset_window m b' |>.trans Set.subset_union_right)
        (frameCore_connected hb' hu hc')
    exact xap_reach_trans h1 (xap_reach_trans h2 h3)

theorem frame_isBlockScheme (m : ℕ) :
    IsBlockScheme (2 * m + 1) 1 (frameGood m) (frameCore m) :=
  ⟨by omega, frameGood_isLocal m, frame_blockLinks m⟩

end Exploding
