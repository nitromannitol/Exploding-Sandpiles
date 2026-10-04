/-
The star-connectedness of a minimal box cut, assembled from the augmented box
boundary-star theorem.

Fix a minimal vertex cut `S` of the two opposite `i`-faces of the box `cent d n`.  Let
`C = xmg_C d n i S` be the negative-face side, the set of sites reachable from the negative
face along paths that avoid `S`, and let `B` be its complement in the box.  Every site of
`S` lies in `B`.  The inner boundary of `C` inside `B`, i.e. the sites of `B` adjacent to
`C` or lying on the negative face, is exactly `S`: a site of `S` is reached by a minimising
crossing path, so its predecessor lies in `C` (or it is itself on the negative face), while
a site of `B` adjacent to `C` would otherwise belong to `C`.  The augmented box
boundary-star theorem `xmb_boundaryStar` then makes this boundary `*`-connected, once `B`
is known to be connected.  Converting through `xmk_induce_connected_iff` gives the
connectedness of the king graph induced on `S`.  The box-crossing star duality follows.

The connectedness of `B` is the substance of the assembly.  The positive-face side
`P = xmh_P d n i S` lies in `B`, and the positive face, being a coordinate face of the box,
is connected inside `B`.  A site of `S` reaches the positive face inside `B`: minimising
crossing paths supply a successor outside `S` (`xmh_avoid_erase_last`), which lies on the
positive-face side.  A site of `B` reaches `S` inside `B`: along a box path from the
negative face, which must meet `S` because the site is off the negative-face side, the last
meeting point with `S` leaves a suffix that stays in `B`.  Hence every site of `B` reaches
the connected positive face, so `B` is connected (`xmh_B_connected`).
-/
import Exploding.Support.ExtAPMinCutStar
import Exploding.Support.ExtAPKingConnected
import Exploding.Support.ExtAPMinCutDuality

open Exploding LatticeProb Relation
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-! ### The complement of the negative-face side -/

/-- The complement of the negative-face side of a cut inside the box. -/
def xmh_B (d n : ℕ) (i : Fin d) (S : Finset (Site d)) : Set (Site d) :=
  {z | z ∈ cent d n ∧ z ∉ xmg_C d n i S}

/-- The inner boundary of the negative-face side, read inside its complement: the sites of
`xmh_B` that are adjacent to the negative-face side or lie on the negative face. -/
def xmh_D (d n : ℕ) (i : Fin d) (S : Finset (Site d)) : Set (Site d) :=
  {z | z ∈ xmh_B d n i S ∧ xmb_Bdry (xmc_Fneg d n i) (xmg_C d n i S) z}

/-- The geometric input that completes the assembly: for a minimal cut `S`, the complement
of the negative-face side inside the box is connected. -/
def xmh_ComplementConnected (d : ℕ) : Prop :=
  ∀ (n : ℕ) (i : Fin d) (S : Finset (Site d)), xmc_Minimal d n i S →
    ∀ u ∈ xmh_B d n i S, ∀ v ∈ xmh_B d n i S,
      ReflTransGen (fun a b => a ∈ xmh_B d n i S ∧ b ∈ xmh_B d n i S ∧
        (lattice d).Adj a b) u v

/-! ### Elementary consequences of avoidance -/

/-- A path avoiding `S` cannot end in `S` when it starts outside `S`. -/
theorem xmh_Avoid_notMem_right (d n : ℕ) {S : Finset (Site d)} {a b : Site d}
    (h : xmc_Avoid d n S a b) (ha : a ∉ (S : Set (Site d))) :
    b ∉ (S : Set (Site d)) := by
  rw [xmc_Avoid] at h
  induction h with
  | refl => exact ha
  | tail _ hstep _ => exact hstep.2.2.2.2

/-- A path that avoids `S \ {s}` and starts outside `S` either meets `s` for the first time
after a prefix avoiding `S`, or avoids `S` outright. -/
theorem xmh_avoid_erase_split (d n : ℕ) {S : Finset (Site d)} {s a b : Site d}
    (haS : a ∉ (S : Set (Site d))) (h : xmc_Avoid d n (S.erase s) a b) :
    (∃ p, xmc_Avoid d n S a p ∧ (lattice d).Adj p s) ∨ xmc_Avoid d n S a b := by
  rw [xmc_Avoid] at h
  induction h with
  | refl => exact Or.inr (xmc_Avoid_refl d n S a)
  | @tail mid b hpref hstep ih =>
    rcases ih with ⟨p, hp, hps⟩ | havoid
    · exact Or.inl ⟨p, hp, hps⟩
    · rcases hstep with ⟨hadj, hmidc, hbc, hmidSe, hbSe⟩
      by_cases hbs : b = s
      · exact Or.inl ⟨mid, havoid, hbs ▸ hadj⟩
      · have hbS : b ∉ (S : Set (Site d)) := by
          intro hbS
          exact hbSe (Finset.mem_erase.mpr ⟨hbs, hbS⟩)
        have hmidS : mid ∉ (S : Set (Site d)) :=
          xmh_Avoid_notMem_right d n havoid haS
        exact Or.inr (havoid.tail ⟨hadj, hmidc, hbc, hmidS, hbS⟩)

/-! ### The boundary of the negative-face side is the cut -/

/-- A site of the inner boundary of the negative-face side belongs to the cut. -/
theorem xmh_D_subset_S (d n : ℕ) (i : Fin d) (S : Finset (Site d)) :
    xmh_D d n i S ⊆ (S : Set (Site d)) := by
  intro z hz
  rcases hz with ⟨⟨hzc, hzC⟩, hbdry⟩
  rcases hbdry with ⟨c, hcC, hcz⟩ | hzF
  · by_contra hzS
    have hcS : c ∉ (S : Set (Site d)) := hcC.1
    obtain ⟨x, hxF, havoid⟩ := hcC.2
    have hc_cent : c ∈ cent d n := xmg_C_subset d n i S hcC
    exact hzC ⟨hzS, x, hxF,
      havoid.tail ⟨hcz, hc_cent, hzc, hcS, hzS⟩⟩
  · by_contra hzS
    exact hzC ⟨hzS, z, hzF, xmc_Avoid_refl d n S z⟩

/-- Every site of a minimal cut is on the inner boundary of the negative-face side: a
minimising crossing path reaches the cut at that site either directly from the negative
face or from a site of the negative-face side. -/
theorem xmh_S_subset_D (d n : ℕ) (i : Fin d) {S : Finset (Site d)}
    (hmin : xmc_Minimal d n i S) (hn : 1 ≤ n) :
    (S : Set (Site d)) ⊆ xmh_D d n i S := by
  intro s hs
  have hScent : s ∈ cent d n := xbc_mem_ball.mp (hmin.1.1 hs)
  have hsC : s ∉ xmg_C d n i S := fun hc => hc.1 hs
  refine ⟨⟨hScent, hsC⟩, ?_⟩
  obtain ⟨x, y, hxF, hyF, havoid⟩ := xmc_Minimal_exists_avoid d n i hmin hs
  have hxy : x ≠ y := by
    intro hxy
    have hxi : x i = -(n : ℤ) := hxF.2
    have hyi : y i = (n : ℤ) := hyF.2
    rw [hxy] at hxi
    omega
  have hxSe : x ∉ (S.erase s : Set (Site d)) := by
    rcases ReflTransGen.cases_head havoid with h | ⟨v, hv, _⟩
    · exact absurd h hxy
    · exact hv.2.2.2.1
  by_cases hxs : x = s
  · exact Or.inr (hxs ▸ hxF)
  · have hxS : x ∉ (S : Set (Site d)) := by
      intro hxS
      exact hxSe (Finset.mem_erase.mpr ⟨hxs, hxS⟩)
    rcases xmh_avoid_erase_split d n hxS havoid with ⟨p, hp, hps⟩ | hfull
    · exact Or.inl ⟨p, ⟨xmh_Avoid_notMem_right d n hp hxS, x, hxF, hp⟩, hps⟩
    · exact absurd hfull (hmin.1.2 x y hxF hyF)

/-- The inner boundary of the negative-face side of a minimal cut is the cut itself. -/
theorem xmh_D_eq_S (d n : ℕ) (i : Fin d) {S : Finset (Site d)}
    (hmin : xmc_Minimal d n i S) (hn : 1 ≤ n) :
    xmh_D d n i S = (S : Set (Site d)) :=
  Set.Subset.antisymm (xmh_D_subset_S d n i S) (xmh_S_subset_D d n i hmin hn)

/-- A minimal cut cannot live in the degenerate box of radius zero. -/
theorem xmh_minimal_ne_zero (d : ℕ) (i : Fin d) {S : Finset (Site d)}
    (hmin : xmc_Minimal d 0 i S) : False := by
  refine hmin.1.2 (0 : Site d) (0 : Site d) ?_ ?_ (xmc_Avoid_refl d 0 S 0)
  · refine ⟨fun j => ?_, ?_⟩
    · simp
    · simp
  · refine ⟨fun j => ?_, ?_⟩
    · simp
    · simp

/-! ### Connectivity of the box -/

theorem xmh_cent_update_mem {n : ℕ} {z : Site d} (hz : z ∈ cent d n) {j : Fin d} {s : ℤ}
    (hs : |s| ≤ (n : ℤ)) : Function.update z j s ∈ cent d n := by
  intro k
  by_cases hk : k = j
  · subst hk; rw [Function.update_self]; exact hs
  · rw [Function.update_of_ne hk]; exact hz k

theorem xmh_cent_path {n : ℕ} {z : Site d} (hz : z ∈ cent d n) {j : Fin d} {b : ℤ}
    (hb : |b| ≤ (n : ℤ)) :
    ReflTransGen (fun a b => a ∈ cent d n ∧ b ∈ cent d n ∧ (lattice d).Adj a b) z
      (Function.update z j b) := by
  have hzj : |z j| ≤ (n : ℤ) := hz j
  have hzj_lo : -(n : ℤ) ≤ z j := (abs_le.mp hzj).1
  have hzj_hi : z j ≤ (n : ℤ) := (abs_le.mp hzj).2
  have hb_lo : -(n : ℤ) ≤ b := (abs_le.mp hb).1
  have hb_hi : b ≤ (n : ℤ) := (abs_le.mp hb).2
  rcases le_total (z j) b with hab | hba
  · have key : ∀ k : ℕ, (z j) + (k : ℤ) ≤ b →
        ReflTransGen (fun a b => a ∈ cent d n ∧ b ∈ cent d n ∧ (lattice d).Adj a b) z
          (Function.update z j ((z j) + (k : ℤ))) := by
      intro k
      induction k with
      | zero => intro _; simpa using ReflTransGen.refl
      | succ k ih =>
        intro hk
        have hk' : (z j) + (k : ℤ) ≤ b := by omega
        have hb1 : |(z j) + (k : ℤ)| ≤ (n : ℤ) := by rw [abs_le]; constructor <;> omega
        have hb2 : |(z j) + (k : ℤ) + 1| ≤ (n : ℤ) := by rw [abs_le]; constructor <;> omega
        have hstep : (fun a b => a ∈ cent d n ∧ b ∈ cent d n ∧ (lattice d).Adj a b)
            (Function.update z j ((z j) + (k : ℤ)))
            (Function.update z j ((z j) + ((k + 1 : ℕ) : ℤ))) := by
          rw [show (z j) + ((k + 1 : ℕ) : ℤ) = (z j) + (k : ℤ) + 1 by push_cast; ring]
          exact ⟨xmh_cent_update_mem hz hb1, xmh_cent_update_mem hz hb2,
            xmb_adj_update_succ z j ((z j) + (k : ℤ))⟩
        exact (ih hk').tail hstep
    have hb' : b = (z j) + ((b - z j).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (by omega)]; ring
    rw [hb']
    exact key ((b - z j).toNat) (by rw [Int.toNat_of_nonneg (by omega)]; omega)
  · have key : ∀ k : ℕ, b ≤ (z j) - (k : ℤ) →
        ReflTransGen (fun a b => a ∈ cent d n ∧ b ∈ cent d n ∧ (lattice d).Adj a b) z
          (Function.update z j ((z j) - (k : ℤ))) := by
      intro k
      induction k with
      | zero => intro _; simpa using ReflTransGen.refl
      | succ k ih =>
        intro hk
        have hk' : b ≤ (z j) - (k : ℤ) := by omega
        have hb1 : |(z j) - (k : ℤ)| ≤ (n : ℤ) := by rw [abs_le]; constructor <;> omega
        have hb2 : |(z j) - (k : ℤ) - 1| ≤ (n : ℤ) := by rw [abs_le]; constructor <;> omega
        have hstep : (fun a b => a ∈ cent d n ∧ b ∈ cent d n ∧ (lattice d).Adj a b)
            (Function.update z j ((z j) - (k : ℤ)))
            (Function.update z j ((z j) - ((k + 1 : ℕ) : ℤ))) := by
          rw [show (z j) - ((k + 1 : ℕ) : ℤ) = (z j) - (k : ℤ) - 1 by push_cast; ring]
          have hadj := xmb_adj_update_succ z j ((z j) - (k : ℤ) - 1)
          rw [show (z j) - (k : ℤ) - 1 + 1 = (z j) - (k : ℤ) by ring] at hadj
          exact ⟨xmh_cent_update_mem hz hb1, xmh_cent_update_mem hz hb2, hadj.symm⟩
        exact (ih hk').tail hstep
    have hb' : b = (z j) - ((z j - b).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (by omega)]; ring
    rw [hb']
    exact key ((z j - b).toNat) (by rw [Int.toNat_of_nonneg (by omega)]; omega)

theorem xmh_update_mem_Fneg {n : ℕ} {i : Fin d} {z : Site d} (hz : z ∈ cent d n) :
    Function.update z i (-(n : ℤ)) ∈ xmc_Fneg d n i := by
  refine ⟨?_, ?_⟩
  · intro k
    by_cases hk : k = i
    · subst hk; rw [Function.update_self]; simp
    · rw [Function.update_of_ne hk]; exact hz k
  · rw [Function.update_self]

theorem xmh_cent_connected (d n : ℕ) (i : Fin d) {u v : Site d}
    (hu : u ∈ cent d n) (hv : v ∈ cent d n) :
    ReflTransGen (fun a b => a ∈ cent d n ∧ b ∈ cent d n ∧ (lattice d).Adj a b) u v := by
  have h1 := xmh_cent_path (d := d) (n := n) hu (j := i) (b := -(n : ℤ)) (by simp)
  have h2 := xmh_cent_path (d := d) (n := n) hv (j := i) (b := -(n : ℤ)) (by simp)
  have huF : Function.update u i (-(n : ℤ)) ∈ xmc_Fneg d n i := xmh_update_mem_Fneg hu
  have hvF : Function.update v i (-(n : ℤ)) ∈ xmc_Fneg d n i := xmh_update_mem_Fneg hv
  have h3 := xmb_Fneg_connected n i huF hvF
  have h3' : ReflTransGen (fun a b => a ∈ cent d n ∧ b ∈ cent d n ∧ (lattice d).Adj a b)
      (Function.update u i (-(n : ℤ))) (Function.update v i (-(n : ℤ))) :=
    ReflTransGen.mono (fun a b hab => ⟨hab.1.1, hab.2.1.1, hab.2.2⟩) _ _ h3
  have h2rev : ReflTransGen (fun a b => a ∈ cent d n ∧ b ∈ cent d n ∧ (lattice d).Adj a b)
      (Function.update v i (-(n : ℤ))) v :=
    xmh_rtg_symm (fun a b h => ⟨h.2.1, h.1, h.2.2.symm⟩) h2
  exact h1.trans (h3'.trans h2rev)

/-! ### A site of the negative face -/

/-- The negative-face site with coordinate `-n` in direction `i` and `0` elsewhere. -/
def xmh_negpt (n : ℕ) (i : Fin d) : Site d :=
  fun j => if j = i then -(n : ℤ) else 0

theorem xmh_negpt_mem (n : ℕ) (i : Fin d) :
    xmh_negpt (d := d) n i ∈ xmc_Fneg d n i := by
  refine ⟨?_, ?_⟩
  · intro j
    simp only [xmh_negpt]
    by_cases hj : j = i
    · rw [if_pos hj]; simp
    · rw [if_neg hj]; simp
  · simp [xmh_negpt]

/-! ### The positive-face side -/

/-- The `Fpos`-side of a cut: the sites reachable from the positive face without meeting
the cut, and not in the cut. -/
def xmh_P (d n : ℕ) (i : Fin d) (S : Finset (Site d)) : Set (Site d) :=
  {z | z ∉ (S : Set (Site d)) ∧ ∃ y ∈ xmc_Fpos d n i, xmc_Avoid d n S y z}

/-- A path avoiding `S` ends inside the box when it starts inside the box. -/
theorem xmh_Avoid_endpoint_cent (d n : ℕ) {S : Finset (Site d)} {a b : Site d}
    (h : xmc_Avoid d n S a b) (ha : a ∈ cent d n) : b ∈ cent d n := by
  rw [xmc_Avoid] at h
  induction h with
  | refl => exact ha
  | tail _ hstep _ => exact hstep.2.2.1

/-- Splitting a path that avoids `S \ {s}`: either it meets `s` for the last time before a
successor that stays outside `S` all the way to the endpoint, or it avoids `S` outright. -/
theorem xmh_avoid_erase_last (d n : ℕ) {S : Finset (Site d)} {s x y : Site d}
    (h : xmc_Avoid d n (S.erase s) x y) :
    y = s ∨ (∃ q, q ∉ (S : Set (Site d)) ∧ (lattice d).Adj s q ∧ xmc_Avoid d n S q y) ∨
      xmc_Avoid d n S x y := by
  rw [xmc_Avoid] at h
  induction h with
  | refl =>
    by_cases hxs : x = s
    · exact Or.inl hxs
    · exact Or.inr (Or.inr (xmc_Avoid_refl d n S x))
  | @tail mid b hpref hstep ih =>
    rcases hstep with ⟨hadj, hmidc, hbc, hmidSe, hbSe⟩
    by_cases hms : mid = s
    · by_cases hbs : b = s
      · exact Or.inl hbs
      · have hbS : b ∉ (S : Set (Site d)) := by
          intro hbS; exact hbSe (Finset.mem_erase.mpr ⟨hbs, hbS⟩)
        exact Or.inr (Or.inl ⟨b, hbS, hms ▸ hadj, xmc_Avoid_refl d n S b⟩)
    · have hmidS : mid ∉ (S : Set (Site d)) := by
        intro hmidS; exact hmidSe (Finset.mem_erase.mpr ⟨hms, hmidS⟩)
      rcases ih with hmid | ⟨q, hqS, hsq, hq⟩ | hx
      · exact absurd hmid hms
      · by_cases hbs : b = s
        · exact Or.inl hbs
        · have hbS : b ∉ (S : Set (Site d)) := by
            intro hbS; exact hbSe (Finset.mem_erase.mpr ⟨hbs, hbS⟩)
          exact Or.inr (Or.inl ⟨q, hqS, hsq,
            hq.tail ⟨hadj, hmidc, hbc, hmidS, hbS⟩⟩)
      · by_cases hbs : b = s
        · exact Or.inl hbs
        · have hbS : b ∉ (S : Set (Site d)) := by
            intro hbS; exact hbSe (Finset.mem_erase.mpr ⟨hbs, hbS⟩)
          exact Or.inr (Or.inr (hx.tail ⟨hadj, hmidc, hbc, hmidS, hbS⟩))

/-- A path that avoids the cut and starts outside the negative-face side stays in the
complement of that side. -/
theorem xmh_avoid_path_in_B (d n : ℕ) (i : Fin d) {S : Finset (Site d)} {q y : Site d}
    (hqcent : q ∈ cent d n) (hqS : q ∉ (S : Set (Site d)))
    (hqC : q ∉ xmg_C d n i S) (h : xmc_Avoid d n S q y) :
    ReflTransGen (fun a b => a ∈ xmh_B d n i S ∧ b ∈ xmh_B d n i S ∧
      (lattice d).Adj a b) q y := by
  have hkey : ∀ w, xmc_Avoid d n S q w → w ∈ xmh_B d n i S := by
    intro w hw
    refine ⟨xmh_Avoid_endpoint_cent d n hw hqcent, fun hwC => ?_⟩
    obtain ⟨_, x, hxF, havoid⟩ := hwC
    exact hqC ⟨hqS, x, hxF, xmc_Avoid_trans d n S havoid (xmc_Avoid_symm d n S hw)⟩
  rw [xmc_Avoid] at h
  induction h with
  | refl => exact ReflTransGen.refl
  | @tail mid b hpref hstep ih =>
    rcases hstep with ⟨hadj, hmidc, hbc, hmidSe, hbSe⟩
    have hmidB : mid ∈ xmh_B d n i S := hkey mid hpref
    have hbB : b ∈ xmh_B d n i S :=
      hkey b (hpref.tail ⟨hadj, hmidc, hbc, hmidSe, hbSe⟩)
    exact ih.tail ⟨hmidB, hbB, hadj⟩

/-- Every site of the cut lies in the complement of the negative-face side. -/
theorem xmh_S_subset_B (d n : ℕ) (i : Fin d) {S : Finset (Site d)}
    (hmin : xmc_Minimal d n i S) : (S : Set (Site d)) ⊆ xmh_B d n i S :=
  fun _ hs => ⟨xbc_mem_ball.mp (hmin.1.1 hs), fun hc => hc.1 hs⟩

/-- The positive face lies in the complement of the negative-face side. -/
theorem xmh_Fpos_subset_B (d n : ℕ) (i : Fin d) {S : Finset (Site d)}
    (hmin : xmc_Minimal d n i S) : xmc_Fpos d n i ⊆ xmh_B d n i S := by
  intro z hz
  refine ⟨hz.1, fun hzC => ?_⟩
  obtain ⟨_, x, hxF, havoid⟩ := hzC
  exact hmin.1.2 x z hxF hz havoid

/-- The positive-face side lies in the complement of the negative-face side. -/
theorem xmh_P_subset_B (d n : ℕ) (i : Fin d) {S : Finset (Site d)}
    (hmin : xmc_Minimal d n i S) : xmh_P d n i S ⊆ xmh_B d n i S := by
  intro z hz
  obtain ⟨hzS, y, hyF, havoid⟩ := hz
  refine ⟨xmh_Avoid_endpoint_cent d n havoid hyF.1, fun hzC => ?_⟩
  obtain ⟨_, x, hxF, hxavoid⟩ := hzC
  exact hmin.1.2 x y hxF hyF
    (xmc_Avoid_trans d n S hxavoid (xmc_Avoid_symm d n S havoid))

/-- A site of the cut reaches the positive face inside the complement of the negative-face
side. -/
theorem xmh_S_reaches_Fpos (d n : ℕ) (i : Fin d) {S : Finset (Site d)}
    (hmin : xmc_Minimal d n i S) :
    ∀ s ∈ (S : Set (Site d)), ∃ y ∈ xmc_Fpos d n i,
      ReflTransGen (fun a b => a ∈ xmh_B d n i S ∧ b ∈ xmh_B d n i S ∧
        (lattice d).Adj a b) s y := by
  intro s hs
  by_cases hsF : s ∈ xmc_Fpos d n i
  · exact ⟨s, hsF, ReflTransGen.refl⟩
  · obtain ⟨x, y, hxF, hyF, havoid⟩ := xmc_Minimal_exists_avoid d n i hmin hs
    have hys : y ≠ s := fun h => hsF (h ▸ hyF)
    rcases xmh_avoid_erase_last d n havoid with hys' | ⟨q, hqS, hsq, hqavoid⟩ | hfull
    · exact absurd hys' hys
    · have hqB : q ∈ xmh_B d n i S :=
        xmh_P_subset_B d n i hmin ⟨hqS, y, hyF, xmc_Avoid_symm d n S hqavoid⟩
      have hpathB : ReflTransGen (fun a b => a ∈ xmh_B d n i S ∧ b ∈ xmh_B d n i S ∧
          (lattice d).Adj a b) q y :=
        xmh_avoid_path_in_B d n i hqB.1 hqS hqB.2 hqavoid
      have hsB : s ∈ xmh_B d n i S := xmh_S_subset_B d n i hmin hs
      exact ⟨y, hyF, (ReflTransGen.single ⟨hsB, hqB, hsq⟩).trans hpathB⟩
    · exact absurd hfull (hmin.1.2 x y hxF hyF)

/-- Any site reachable from the negative face inside the box is either on the negative-face
side or reaches the cut inside the complement of that side. -/
theorem xmh_reach_S (d n : ℕ) (i : Fin d) {S : Finset (Site d)} {f z : Site d}
    (hf : f ∈ xmc_Fneg d n i)
    (h : ReflTransGen (fun a b => a ∈ cent d n ∧ b ∈ cent d n ∧ (lattice d).Adj a b) f z) :
    z ∈ xmg_C d n i S ∨
      (∃ s ∈ (S : Set (Site d)), z ∈ xmh_B d n i S ∧
        ReflTransGen (fun a b => a ∈ xmh_B d n i S ∧
          b ∈ xmh_B d n i S ∧ (lattice d).Adj a b) z s) := by
  induction h with
  | refl =>
    by_cases hfS : f ∈ (S : Set (Site d))
    · exact Or.inr ⟨f, hfS, ⟨hf.1, fun hc => hc.1 hfS⟩, ReflTransGen.refl⟩
    · exact Or.inl ⟨hfS, f, hf, xmc_Avoid_refl d n S f⟩
  | @tail w z hpref hstep ih =>
    rcases hstep with ⟨hwc, hzc, hwz⟩
    by_cases hzS : z ∈ (S : Set (Site d))
    · exact Or.inr ⟨z, hzS, ⟨hzc, fun hc => hc.1 hzS⟩, ReflTransGen.refl⟩
    · rcases ih with hwC | ⟨s, hsS, hwB, hpath⟩
      · obtain ⟨hwS, x, hxF, havoid⟩ := hwC
        exact Or.inl ⟨hzS, x, hxF, havoid.tail ⟨hwz, hwc, hzc, hwS, hzS⟩⟩
      · by_cases hzC : z ∈ xmg_C d n i S
        · exact Or.inl hzC
        · have hzB : z ∈ xmh_B d n i S := ⟨hzc, hzC⟩
          exact Or.inr ⟨s, hsS, hzB, ReflTransGen.head ⟨hzB, hwB, hwz.symm⟩ hpath⟩

/-- Every site of the complement of the negative-face side reaches the cut inside that
complement. -/
theorem xmh_B_reaches_S (d n : ℕ) (i : Fin d) (S : Finset (Site d)) :
    ∀ z ∈ xmh_B d n i S, ∃ s ∈ (S : Set (Site d)),
      ReflTransGen (fun a b => a ∈ xmh_B d n i S ∧ b ∈ xmh_B d n i S ∧
        (lattice d).Adj a b) z s := by
  intro z hz
  by_cases hzS : z ∈ (S : Set (Site d))
  · exact ⟨z, hzS, ReflTransGen.refl⟩
  · have hf := xmh_negpt_mem (d := d) n i
    have hpath := xmh_cent_connected d n i hf.1 hz.1
    rcases xmh_reach_S d n i hf hpath with hzC | ⟨s, hsS, _, hpathS⟩
    · exact absurd hzC hz.2
    · exact ⟨s, hsS, hpathS⟩

/-- The complement of the negative-face side of a minimal cut is connected. -/
theorem xmh_B_connected (d n : ℕ) (i : Fin d) {S : Finset (Site d)}
    (hmin : xmc_Minimal d n i S) :
    ∀ u ∈ xmh_B d n i S, ∀ v ∈ xmh_B d n i S,
      ReflTransGen (fun a b => a ∈ xmh_B d n i S ∧ b ∈ xmh_B d n i S ∧
        (lattice d).Adj a b) u v := by
  intro u hu v hv
  obtain ⟨su, hsuS, hupath⟩ := xmh_B_reaches_S d n i S u hu
  obtain ⟨sv, hsvS, hvpath⟩ := xmh_B_reaches_S d n i S v hv
  obtain ⟨yu, hyuF, hupath2⟩ := xmh_S_reaches_Fpos d n i hmin su hsuS
  obtain ⟨yv, hyvF, hvpath2⟩ := xmh_S_reaches_Fpos d n i hmin sv hsvS
  have hfpos : ReflTransGen (fun a b => a ∈ xmb_face d n i ((n : ℤ)) ∧
      b ∈ xmb_face d n i ((n : ℤ)) ∧ (lattice d).Adj a b) yu yv :=
    xmb_face_connected n i (by rw [abs_of_nonneg (Int.natCast_nonneg n)]) hyuF hyvF
  have hfposB : ReflTransGen (fun a b => a ∈ xmh_B d n i S ∧ b ∈ xmh_B d n i S ∧
      (lattice d).Adj a b) yu yv :=
    ReflTransGen.mono (fun _ _ hab => ⟨xmh_Fpos_subset_B d n i hmin hab.1,
      xmh_Fpos_subset_B d n i hmin hab.2.1, hab.2.2⟩) _ _ hfpos
  have hyvsv : ReflTransGen (fun a b => a ∈ xmh_B d n i S ∧ b ∈ xmh_B d n i S ∧
      (lattice d).Adj a b) yv sv :=
    xmh_rtg_symm (fun a b h => ⟨h.2.1, h.1, h.2.2.symm⟩) hvpath2
  have hsvv : ReflTransGen (fun a b => a ∈ xmh_B d n i S ∧ b ∈ xmh_B d n i S ∧
      (lattice d).Adj a b) sv v :=
    xmh_rtg_symm (fun a b h => ⟨h.2.1, h.1, h.2.2.symm⟩) hvpath
  exact hupath.trans (hupath2.trans (hfposB.trans (hyvsv.trans hsvv)))

/-- The complement of the negative-face side of a minimal cut is connected, for every box. -/
theorem xmh_complementConnected (d : ℕ) : xmh_ComplementConnected d :=
  fun _ _ _ hmin => xmh_B_connected d _ _ hmin

/-! ### Assembling the minimal-cut star-connectedness -/

/-- **A minimal cut of the two opposite faces of a box is `*`-connected.** -/
theorem xmh_minCutStarConnected (d : ℕ) (hd : 2 ≤ d) : xmc_MinCutStarConnected d := by
  intro n i S hmin
  rw [xmk_induce_connected_iff]
  refine ⟨?_, ?_⟩
  · have hcard := xml_cut_card_ge hd hmin.1
    exact Finset.card_pos.mp (by omega)
  · intro x hx y hy
    have hn : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        exact (xmh_minimal_ne_zero d i hmin).elim
      · exact hpos
    have hD := xmh_D_eq_S d n i hmin hn
    have hx' : x ∈ xmh_D d n i S := by rw [hD]; exact hx
    have hy' : y ∈ xmh_D d n i S := by rw [hD]; exact hy
    have hbd := xmb_boundaryStar n i
      (A := xmg_C d n i S) (B := xmh_B d n i S)
      (xmg_C_subset d n i S)
      (fun z => Iff.rfl)
      (xmh_B_connected d n i hmin)
      (xmg_C_meets d n i S)
      (xmh_negpt_mem (d := d) n i) x y hx' hy'
    refine ReflTransGen.mono (fun _ _ hab => ?_) x y hbd
    exact ⟨by rw [← hD]; exact hab.1, by rw [← hD]; exact hab.2.1, hab.2.2⟩

/-- **The box-crossing star duality holds in every dimension at least two.** -/
theorem xmh_starDuality (d : ℕ) (hd : 2 ≤ d) : xbc_StarDuality d :=
  xml_starDuality_of_minCut hd (xmh_minCutStarConnected d hd)

end Exploding
