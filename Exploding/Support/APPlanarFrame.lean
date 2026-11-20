/-
The frame of a block of the square lattice.

At scale `N = 2m + 1` the window of radius one of a block `b` is the box of side `3N` around it,
and in planar coordinates centred at the block it is the box `‖z‖_∞ ≤ 3m + 1`, while the block
is the hole `‖z‖_∞ ≤ m`.  The annulus between them is the union of the four rectangles
`LQGMetric.annRect (m + 1) (3m + 1) d` of side lengths `3N` and `N`.  A block is good for the
frame when each of the four rectangles has an open crossing the long way; its core is the set of
sites joined, inside a rectangle, to the start of such a crossing.  Long-way crossings of
adjacent rectangles meet (`frame_meet`), so the core is connected inside the annulus, and every
open path from the block to the outside of its window meets the core (`frame_enclosure`).  The
planar topology is that of `LQGMetric.annRect_meet` and `LQGMetric.PercAnn.ann_exit` in
Lattice-Probability.
-/
import Exploding.Support.APCoarseGeometry
import LatticeProb.Bonanno.LQGMetric.Perc.AnnulusMain

open LatticeProb Relation LQGMetric

namespace Exploding

/-! ### Planar coordinates of a block -/

/-- Planar coordinates of a site of `ℤ²` relative to the centre of the block `b` at scale
`2m + 1`. -/
def framePlane (m : ℕ) (b z : Site 2) : ℤ × ℤ :=
  (z 0 - ((2 * m + 1) * b 0 + m), z 1 - ((2 * m + 1) * b 1 + m))

theorem framePlane_injective (m : ℕ) (b : Site 2) : Function.Injective (framePlane m b) := by
  intro z z' h
  simp only [framePlane, Prod.mk.injEq] at h
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]
    omega
  · simp only [Fin.mk_one, Fin.isValue]
    omega

/-- The rectangle of the frame of `b` on the side `dir`. -/
def frameRect (m : ℕ) (b : Site 2) (dir : PercDir) : Set (Site 2) :=
  {z | framePlane m b z ∈ annRect ((m : ℤ) + 1) (3 * m + 1) dir}

/-- The annulus of the frame of `b`: the union of its four rectangles. -/
def frameAnnulus (m : ℕ) (b : Site 2) : Set (Site 2) := {z | ∃ dir, z ∈ frameRect m b dir}

/-- `a` and `e` are the ends of an open long-way crossing of the rectangle of `b` on side `dir`. -/
def FrameCross (m : ℕ) (ω : Site 2 × Fin 2 → Bool) (b : Site 2) (dir : PercDir) (a e : Site 2) :
    Prop :=
  annLong dir (framePlane m b a) = -(3 * m + 1) ∧ annLong dir (framePlane m b e) = 3 * m + 1 ∧
    xap_Reach ω (frameRect m b dir) a e

/-- The block `b` is good for the frame: each of its four rectangles has an open long-way
crossing. -/
def frameGood (m : ℕ) (ω : Site 2 × Fin 2 → Bool) (b : Site 2) : Prop :=
  ∀ dir, ∃ a e, FrameCross m ω b dir a e

/-- The core of the frame: the sites joined inside a rectangle to the start of a long-way
crossing of that rectangle. -/
def frameCore (m : ℕ) (ω : Site 2 × Fin 2 → Bool) (b : Site 2) : Set (Site 2) :=
  {z | ∃ dir a e, FrameCross m ω b dir a e ∧ xap_Reach ω (frameRect m b dir) a z}

theorem frameRect_subset_annulus (m : ℕ) (b : Site 2) (dir : PercDir) :
    frameRect m b dir ⊆ frameAnnulus m b := fun _ hz => ⟨dir, hz⟩

/-! ### Blocks and windows in planar coordinates -/

theorem int_ediv_abs_sub_le_one_iff {N a c : ℤ} (hN : 0 < N) :
    |a / N - c| ≤ 1 ↔ N * (c - 1) ≤ a ∧ a < N * (c + 2) := by
  obtain ⟨h1, h2⟩ := int_ediv_bounds hN a
  rw [abs_le]
  constructor
  · rintro ⟨h3, h4⟩
    constructor <;> nlinarith
  · rintro ⟨h3, h4⟩
    constructor
    · by_contra h
      have : a / N ≤ c - 2 := by linarith
      nlinarith
    · by_contra h
      have : c + 2 ≤ a / N := by linarith
      nlinarith

theorem mem_coarseWindow_iff_annBox {m : ℕ} {b z : Site 2} :
    z ∈ coarseWindow (2 * m + 1) 1 b ↔ annBox (3 * m + 1) (framePlane m b z) := by
  have hN : (0 : ℤ) < ((2 * m + 1 : ℕ) : ℤ) := by positivity
  rw [mem_coarseWindow_iff]
  simp only [coarseSite, Nat.cast_one, Fin.forall_fin_two, annBox, framePlane]
  rw [int_ediv_abs_sub_le_one_iff hN, int_ediv_abs_sub_le_one_iff hN]
  push_cast
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

theorem coarseSite_eq_iff_framePlane {m : ℕ} {b z : Site 2} :
    coarseSite (2 * m + 1) z = b ↔
      (-((m : ℤ) + 1) < (framePlane m b z).1 ∧ (framePlane m b z).1 < (m : ℤ) + 1 ∧
        -((m : ℤ) + 1) < (framePlane m b z).2 ∧ (framePlane m b z).2 < (m : ℤ) + 1) := by
  have hN : (0 : ℤ) < ((2 * m + 1 : ℕ) : ℤ) := by positivity
  have key : ∀ a c : ℤ, a / ((2 * m + 1 : ℕ) : ℤ) = c ↔
      ((2 * m + 1 : ℕ) : ℤ) * c ≤ a ∧ a < ((2 * m + 1 : ℕ) : ℤ) * c + ((2 * m + 1 : ℕ) : ℤ) := by
    intro a c
    constructor
    · rintro rfl
      exact int_ediv_bounds hN a
    · rintro ⟨h1, h2⟩
      exact int_ediv_eq_of_bounds hN h1 h2
  constructor
  · intro h
    have h0 := (key (z 0) (b 0)).1 (congrFun h 0)
    have h1 := (key (z 1) (b 1)).1 (congrFun h 1)
    simp only [framePlane]
    push_cast at h0 h1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨h1, h2, h3, h4⟩
    simp only [framePlane] at h1 h2 h3 h4
    funext i
    fin_cases i
    · exact (key (z 0) (b 0)).2 (by push_cast; constructor <;> linarith)
    · exact (key (z 1) (b 1)).2 (by push_cast; constructor <;> linarith)

theorem frameRect_subset_window (m : ℕ) (b : Site 2) (dir : PercDir) :
    frameRect m b dir ⊆ coarseWindow (2 * m + 1) 1 b := fun _ hz =>
  mem_coarseWindow_iff_annBox.mpr hz.1

theorem frameAnnulus_subset_window (m : ℕ) (b : Site 2) :
    frameAnnulus m b ⊆ coarseWindow (2 * m + 1) 1 b := by
  rintro z ⟨dir, hz⟩
  exact frameRect_subset_window m b dir hz

/-! ### Open paths in planar coordinates -/

theorem framePlane_adj4 {m : ℕ} {b : Site 2} {ω : Site 2 × Fin 2 → Bool} {x y : Site 2}
    (h : (openBondGraph ω).Adj x y) : PercAdj4 (framePlane m b x) (framePlane m b y) := by
  obtain ⟨i, hi | hi⟩ := xap_lattice_of_open h <;>
  · subst hi
    fin_cases i <;> simp [framePlane, PercAdj4, unit] <;> omega

theorem percAdjK_symm' : ∀ x y : ℤ × ℤ, PercAdjK x y → PercAdjK y x := by
  intro x y h
  simp only [PercAdjK] at h ⊢
  omega

/-- An open path inside `S` is a nearest-neighbour path of planar sites, each joined to its start
inside `S`. -/
theorem frame_lift_reach {m : ℕ} {b : Site 2} {ω : Site 2 × Fin 2 → Bool} {S : Set (Site 2)}
    {T : Set (ℤ × ℤ)} (hST : ∀ z ∈ S, framePlane m b z ∈ T) {a e : Site 2}
    (h : xap_Reach ω S a e) :
    ReflTransGen (PercStepIn {p | p ∈ T ∧ p ∈ framePlane m b '' {z | xap_Reach ω S a z}} PercAdj4)
      (framePlane m b a) (framePlane m b e) := by
  obtain ⟨ha, h⟩ := h
  have key : ∀ w, ReflTransGen (xap_RS ω S) a w →
      ReflTransGen (PercStepIn {p | p ∈ T ∧ p ∈ framePlane m b '' {z | xap_Reach ω S a z}}
        PercAdj4) (framePlane m b a) (framePlane m b w) := by
    intro w hw
    induction hw with
    | refl => exact ReflTransGen.refl
    | @tail u v hu huv ih =>
      exact ih.tail ⟨⟨hST u huv.1, u, ⟨ha, hu⟩, rfl⟩, ⟨hST v huv.2.1, v, ⟨ha, hu.tail huv⟩, rfl⟩,
        framePlane_adj4 huv.2.2⟩
  exact key e h

/-! ### Crossings of adjacent rectangles meet -/

/-- A long-way crossing of the rectangle on side `d` meets an open path inside the rectangle on
side `d'` that starts on the outer side of `d` and reaches the inner level of `d`. -/
theorem frame_meet {m : ℕ} {ω : Site 2 × Fin 2 → Bool} {b : Site 2} {d d' : PercDir}
    {a e s t : Site 2} (hcross : FrameCross m ω b d a e)
    (hside : xap_Reach ω (frameRect m b d') s t)
    (hs : annDir d (framePlane m b s) = 3 * m + 1)
    (ht : annDir d (framePlane m b t) ≤ (m : ℤ) + 1) :
    ∃ z, xap_Reach ω (frameRect m b d) a z ∧ xap_Reach ω (frameRect m b d') s z := by
  obtain ⟨ha, he, hae⟩ := hcross
  have hP := frame_lift_reach (T := annRect ((m : ℤ) + 1) (3 * m + 1) d') (fun z hz => hz) hside
  obtain ⟨c, hc, hsc⟩ := perc_first_reach (annDir d)
    (fun x y h => annDir_adjK d (percAdjK_of_adj4 h)) ((m : ℤ) + 1) hP (by rw [hs]; omega) ht
  have hsX : framePlane m b s ∈ annRect ((m : ℤ) + 1) (3 * m + 1) d :=
    ⟨hside.1.1, by rw [hs]; omega⟩
  have hC' : ReflTransGen (PercStepIn {p | p ∈ annRect ((m : ℤ) + 1) (3 * m + 1) d ∧
      p ∈ framePlane m b '' {z | xap_Reach ω (frameRect m b d') s z}} PercAdjK)
      (framePlane m b s) c :=
    by
      refine percStepIn_mono ?_ (fun _ _ h => percAdjK_of_adj4 h) hsc
      intro p hp
      exact ⟨⟨hp.1.1.1, hp.2⟩, hp.1.2⟩
  obtain ⟨p, -, ⟨z1, hz1, rfl⟩, ⟨z2, hz2, hz12⟩⟩ := annRect_meet ((m : ℤ) + 1) (3 * m + 1) d
    (framePlane m b '' {z | xap_Reach ω (frameRect m b d) a z})
    (framePlane m b '' {z | xap_Reach ω (frameRect m b d') s z})
    ⟨framePlane m b a, framePlane m b e, ha, he, hae.1, ⟨a, xap_reach_refl hae.1, rfl⟩,
      frame_lift_reach (fun z hz => hz) hae⟩
    ⟨framePlane m b s, c, hs, hc, hsX, ⟨s, xap_reach_refl hside.1, rfl⟩, hC'⟩
  have : z2 = z1 := framePlane_injective m b hz12
  subst this
  exact ⟨z2, hz1, hz2⟩

/-- A crossing of a side rectangle (left or right) is joined inside the annulus to every
crossing of the top rectangle. -/
theorem frame_side_connected {m : ℕ} {ω : Site 2 × Fin 2 → Bool} {b : Site 2} {d : PercDir}
    (hd : d = .L ∨ d = .R) {a e aT eT : Site 2} (h : FrameCross m ω b d a e)
    (hT : FrameCross m ω b .T aT eT) : xap_Reach ω (frameAnnulus m b) a aT := by
  have h1 := h.1
  have h2 := h.2.1
  obtain ⟨z, hTz, hdz⟩ := frame_meet (d := .T) (d' := d) hT (xap_reach_symm h.2.2)
    (by rcases hd with rfl | rfl <;> simp only [annDir, annLong] at h2 ⊢ <;> omega)
    (by rcases hd with rfl | rfl <;> simp only [annDir, annLong] at h1 ⊢ <;> omega)
  have h1 : xap_Reach ω (frameAnnulus m b) a e :=
    xap_reach_mono (frameRect_subset_annulus m b d) h.2.2
  have h2 : xap_Reach ω (frameAnnulus m b) e z :=
    xap_reach_mono (frameRect_subset_annulus m b d) hdz
  have h3 : xap_Reach ω (frameAnnulus m b) aT z :=
    xap_reach_mono (frameRect_subset_annulus m b .T) hTz
  exact xap_reach_trans h1 (xap_reach_trans h2 (xap_reach_symm h3))

/-- In a good frame, every long-way crossing is joined inside the annulus to every crossing of
the top rectangle. -/
theorem frame_cross_connected {m : ℕ} {ω : Site 2 × Fin 2 → Bool} {b : Site 2}
    (hgood : frameGood m ω b) {d : PercDir} {a e aT eT : Site 2} (h : FrameCross m ω b d a e)
    (hT : FrameCross m ω b .T aT eT) : xap_Reach ω (frameAnnulus m b) a aT := by
  obtain ⟨aL, eL, hL⟩ := hgood .L
  have hLT := frame_side_connected (Or.inl rfl) hL hT
  cases d with
  | L => exact frame_side_connected (Or.inl rfl) h hT
  | R => exact frame_side_connected (Or.inr rfl) h hT
  | T => exact xap_reach_trans (xap_reach_symm (frame_side_connected (Or.inl rfl) hL h)) hLT
  | B =>
    have hL1 := hL.1
    have hL2 := hL.2.1
    obtain ⟨z, hBz, hLz⟩ := frame_meet (d := .B) (d' := .L) h hL.2.2
      (by simp only [annDir, annLong] at hL1 ⊢; omega)
      (by simp only [annDir, annLong] at hL2 ⊢; omega)
    have h1 : xap_Reach ω (frameAnnulus m b) a z :=
      xap_reach_mono (frameRect_subset_annulus m b .B) hBz
    have h2 : xap_Reach ω (frameAnnulus m b) aL z :=
      xap_reach_mono (frameRect_subset_annulus m b .L) hLz
    exact xap_reach_trans h1 (xap_reach_trans (xap_reach_symm h2) hLT)

/-- The core of a good frame is connected inside the annulus. -/
theorem frameCore_connected {m : ℕ} {ω : Site 2 × Fin 2 → Bool} {b : Site 2}
    (hgood : frameGood m ω b) {c c' : Site 2} (hc : c ∈ frameCore m ω b)
    (hc' : c' ∈ frameCore m ω b) : xap_Reach ω (frameAnnulus m b) c c' := by
  obtain ⟨d, a, e, h, hac⟩ := hc
  obtain ⟨d', a', e', h', hac'⟩ := hc'
  obtain ⟨aT, eT, hT⟩ := hgood .T
  have h1 := frame_cross_connected hgood h hT
  have h2 := frame_cross_connected hgood h' hT
  exact xap_reach_trans (xap_reach_symm (xap_reach_mono (frameRect_subset_annulus m b d) hac))
    (xap_reach_trans h1 (xap_reach_trans (xap_reach_symm h2)
      (xap_reach_mono (frameRect_subset_annulus m b d') hac')))

/-! ### Every path leaving the window meets the core -/

/-- **Enclosure.**  In a good frame, an open path inside `S` from a site of the block to a site
outside the window meets the core, at a site joined to its start inside `S` and the window. -/
theorem frame_enclosure {m : ℕ} {ω : Site 2 × Fin 2 → Bool} {b : Site 2}
    (hgood : frameGood m ω b) {S : Set (Site 2)} {u e : Site 2}
    (hu : coarseSite (2 * m + 1) u = b) (he : e ∉ coarseWindow (2 * m + 1) 1 b)
    (hue : xap_Reach ω S u e) :
    ∃ z ∈ frameCore m ω b, xap_Reach ω (S ∩ coarseWindow (2 * m + 1) 1 b) u z := by
  set W := coarseWindow (2 * m + 1) 1 b
  have huW : u ∈ W := by
    have := mem_coarseWindow_self (2 * m + 1) 1 u
    rwa [hu] at this
  have hhole := coarseSite_eq_iff_framePlane.mp hu
  have key : ∀ w, ReflTransGen (xap_RS ω S) u w →
      (w ∈ W ∧ xap_Reach ω (S ∩ W) u w) ∨
        ∃ z ∈ frameCore m ω b, xap_Reach ω (S ∩ W) u z := by
    intro w hw
    induction hw with
    | refl => exact Or.inl ⟨huW, xap_reach_refl ⟨hue.1, huW⟩⟩
    | @tail w w' _ hww' ih =>
      rcases ih with ⟨hwW, huw⟩ | hdone
      · by_cases hw'W : w' ∈ W
        · exact Or.inl ⟨hw'W, xap_reach_trans huw
            (xap_reach_step ⟨hww'.1, hwW⟩ ⟨hww'.2.1, hw'W⟩ hww'.2.2)⟩
        · right
          set Γ : Set (ℤ × ℤ) := framePlane m b '' {z | xap_Reach ω (S ∩ W) u z} ∪
            {p | ¬ annBox (3 * m + 1) p}
          have hpath : ReflTransGen (PercStepIn Γ PercAdjK) (framePlane m b u)
              (framePlane m b w') := by
            have hlift := frame_lift_reach (m := m) (b := b) (T := Set.univ) (fun _ _ => trivial) huw
            refine (percStepIn_mono (fun p hp => Or.inl hp.2)
              (fun _ _ h => percAdjK_of_adj4 h) hlift).tail ⟨Or.inl ⟨w, huw, rfl⟩, Or.inr ?_,
                percAdjK_of_adj4 (framePlane_adj4 hww'.2.2)⟩
            exact fun h => hw'W (mem_coarseWindow_iff_annBox.mpr h)
          obtain ⟨d, c, e', hc, he', hcX, hcΓ, hce⟩ := PercAnn.ann_exit ((m : ℤ) + 1)
            (3 * m + 1) (by omega) Γ (by omega) (fun h => hw'W (mem_coarseWindow_iff_annBox.mpr h))
            hpath
          obtain ⟨a, a', hcross⟩ := hgood d
          have he'X := PercAnn.rtg_end_mem hce ⟨hcX, hcΓ⟩
          obtain ⟨p, hpX, ⟨z1, hz1, rfl⟩, hpΓ⟩ := annRect_meet ((m : ℤ) + 1) (3 * m + 1) d
            (framePlane m b '' {z | xap_Reach ω (frameRect m b d) a z}) Γ
            ⟨framePlane m b a, framePlane m b a', hcross.1, hcross.2.1, hcross.2.2.1,
              ⟨a, xap_reach_refl hcross.2.2.1, rfl⟩, frame_lift_reach (fun z hz => hz) hcross.2.2⟩
            ⟨e', c, he', hc, he'X.1, he'X.2, percStepIn_rev percAdjK_symm' hce⟩
          rcases hpΓ with ⟨z2, hz2, hz12⟩ | hout
          · have : z2 = z1 := framePlane_injective m b hz12
            subst this
            exact ⟨z2, ⟨d, a, a', hcross, hz1⟩, hz2⟩
          · exact (hout hpX.1).elim
      · exact Or.inr hdone
  rcases key e hue.2 with ⟨heW, _⟩ | hdone
  · exact (he heW).elim
  · exact hdone

end Exploding
