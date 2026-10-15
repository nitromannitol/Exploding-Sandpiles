import Exploding.Support.ArxivVolumeSlow

/-!
# Fast sites paired with the signed slow sites

This module proves the matching fast-site firing bound for the stacked checkerboard.
The path begins at the relay site `(1,1,0)`, traverses signed transverse coordinates,
and then moves along coordinate one. Every update after the relay uses a site whose
background has height `2d - 1`.
-/

namespace Exploding

open LatticeProb

/-- A coordinate walk takes one signed unit step at each natural time. -/
def ceVolumeFastWalk {d : ℕ} (x : Site d) (i : Fin d) (dir : ℤ) : ℕ → Site d
  | 0 => x
  | n + 1 => ceVolumeFastWalk x i dir n + dir • unit i

/-- The coordinate walk preserves every coordinate other than its direction. -/
theorem ceVolumeFastWalk_apply_of_ne {d : ℕ} (x : Site d) (i j : Fin d)
    (dir : ℤ) (n : ℕ) (hji : j ≠ i) :
    ceVolumeFastWalk x i dir n j = x j := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [ceVolumeFastWalk, ih, unit, Pi.add_apply, hji]

/-- The coordinate walk is the initial site plus its signed displacement. -/
theorem ceVolumeFastWalk_eq_add {d : ℕ} (x : Site d) (i : Fin d) (dir : ℤ)
    (n : ℕ) :
    ceVolumeFastWalk x i dir n = x + (n : ℤ) • (dir • unit i) := by
  induction n with
  | zero => simp [ceVolumeFastWalk]
  | succ n ih =>
      rw [ceVolumeFastWalk, ih, Nat.cast_succ]
      simp only [add_smul, one_smul]
      abel

/-- The endpoint of a coordinate walk is a function update. -/
theorem ceVolumeFastWalk_eq_update {d : ℕ} (x : Site d) (i : Fin d)
    (dir : ℤ) (m : ℕ) (v : ℤ)
    (hdisp : x i + (m : ℤ) * dir = v) :
    ceVolumeFastWalk x i dir m = Function.update x i v := by
  funext j
  by_cases hji : j = i
  · subst j
    rw [ceVolumeFastWalk_eq_add]
    simp [unit, hdisp]
  · rw [ceVolumeFastWalk_apply_of_ne x i j dir m hji]
    simp [Function.update, hji]

/-- If a neighbor has fired, a high site fires on the next parallel update. -/
theorem ceVolumeFastStep (d : ℕ) (x y : Site d) (i : Fin d)
    (t : ℕ)
    (hneighbor : x = y + unit i ∨ x = y - unit i)
    (hheight : ceEta d y = 2 * (d : ℤ) - 1)
    (hfire : 0 < podo (fun w => ceEta d w + 3 * dirac (0 : Site d) w) t x) :
    0 < podo (fun w => ceEta d w + 3 * dirac (0 : Site d) w) (t + 1) y := by
  let σ : Site d → ℤ := fun w => ceEta d w + 3 * dirac (0 : Site d) w
  let u : Site d → ℤ := podo σ t
  have hy_nonneg : 0 ≤ u y := aux_podo_nonneg σ t y
  by_cases hy_pos : 0 < u y
  · exact lt_of_lt_of_le hy_pos (podo_mono_step σ t y)
  · have hy_zero : u y = 0 := by omega
    have hdirac_nonneg : 0 ≤ dirac (0 : Site d) y := by
      unfold dirac
      split <;> norm_num
    have hsource : 2 * (d : ℤ) - 1 ≤ σ y := by
      dsimp [σ]
      rw [hheight]
      nlinarith [hdirac_nonneg]
    have hterm :
        1 ≤ u (y + unit i) + u (y - unit i) := by
      have hfire' : 0 < u x := by simpa [u, σ] using hfire
      rcases hneighbor with hxy | hxy
      · rw [hxy] at hfire'
        have hxpos : 1 ≤ u (y + unit i) := by omega
        have hxnonneg : 0 ≤ u (y - unit i) := aux_podo_nonneg σ t (y - unit i)
        omega
      · rw [hxy] at hfire'
        have hxpos : 1 ≤ u (y - unit i) := by omega
        have hxnonneg : 0 ≤ u (y + unit i) := aux_podo_nonneg σ t (y + unit i)
        omega
    have hsum_le : u (y + unit i) + u (y - unit i) ≤ nbrSumZ u y := by
      have hs := Finset.single_le_sum
        (f := fun j : Fin d => u (y + unit j) + u (y - unit j))
        (fun j hj => add_nonneg (aux_podo_nonneg σ t (y + unit j))
          (aux_podo_nonneg σ t (y - unit j)))
        (Finset.mem_univ i)
      simpa [nbrSumZ] using hs
    have hsum : 1 ≤ nbrSumZ u y := le_trans hterm hsum_le
    have hconf : 2 * (d : ℤ) ≤ pconf σ t y := by
      change 2 * (d : ℤ) ≤ σ y + (nbrSumZ u y - 2 * (d : ℤ) * u y)
      rw [hy_zero]
      omega
    rw [podo_succ, if_pos hconf]
    change 0 < u y + 1
    omega

/-- The checkerboard has height `2d - 1` whenever coordinate zero is `1 mod 4`. -/
theorem ceVolumeFast_high_of_first_mod_one (d : ℕ) (hd : 2 ≤ d) (x : Site d)
    (hmod : x ⟨0, by omega⟩ % 4 = 1) :
    ceEta d x = 2 * (d : ℤ) - 1 := by
  have h0 : 0 < d := by omega
  have h1 : 1 < d := by omega
  have hce : ceEta d x = 2 * ((d : ℤ) - 2) +
      zeta1 (x ⟨0, h0⟩) (x ⟨1, h1⟩) := by
    simp [ceEta, h0, h1]
  rw [hce]
  have hz : zeta1 (x ⟨0, h0⟩) (x ⟨1, h1⟩) = 3 := by
    simp [zeta1, hmod]
  rw [hz]
  ring

/-- The checkerboard has height `2d - 1` whenever coordinate one is `1 mod 4`. -/
theorem ceVolumeFast_high_of_second_mod_one (d : ℕ) (hd : 2 ≤ d) (x : Site d)
    (hmod : x ⟨1, by omega⟩ % 4 = 1) :
    ceEta d x = 2 * (d : ℤ) - 1 := by
  have h0 : 0 < d := by omega
  have h1 : 1 < d := by omega
  have hce : ceEta d x = 2 * ((d : ℤ) - 2) +
      zeta1 (x ⟨0, h0⟩) (x ⟨1, h1⟩) := by
    simp [ceEta, h0, h1]
  rw [hce]
  have hz : zeta1 (x ⟨0, h0⟩) (x ⟨1, h1⟩) = 3 := by
    simp [zeta1, hmod]
  rw [hz]
  ring

/-- A segment of high sites transports a firing along a signed coordinate walk. -/
theorem ceVolumeFastSegment (d : ℕ) (_hd : 2 ≤ d) (x : Site d) (i : Fin d)
    (dir : ℤ) (m t : ℕ) (hdir : dir = 1 ∨ dir = -1)
    (hstart : 0 < podo (fun w => ceEta d w + 3 * dirac (0 : Site d) w) t x)
    (hhigh : ∀ j, j < m →
      ceEta d (ceVolumeFastWalk x i dir (j + 1)) = 2 * (d : ℤ) - 1) :
    0 < podo (fun w => ceEta d w + 3 * dirac (0 : Site d) w)
      (t + m) (ceVolumeFastWalk x i dir m) := by
  induction m generalizing t with
  | zero => simpa [ceVolumeFastWalk] using hstart
  | succ m ih =>
      have hprevhigh : ∀ j, j < m →
          ceEta d (ceVolumeFastWalk x i dir (j + 1)) = 2 * (d : ℤ) - 1 := by
        intro j hj
        exact hhigh j (by omega)
      have hprev := ih t hstart hprevhigh
      have hlast := hhigh m (by omega)
      have hneighbor :
          ceVolumeFastWalk x i dir m =
              ceVolumeFastWalk x i dir (m + 1) + unit i ∨
          ceVolumeFastWalk x i dir m =
              ceVolumeFastWalk x i dir (m + 1) - unit i := by
        let w : Site d := ceVolumeFastWalk x i dir m
        change w = (w + dir • unit i) + unit i ∨
          w = (w + dir • unit i) - unit i
        rcases hdir with hdir | hdir
        · right
          simp [hdir]
        · left
          simp [hdir]
      have hstep := ceVolumeFastStep d _ _ i (t + m) hneighbor hlast hprev
      have htime : t + m + 1 = t + (m + 1) := by omega
      rw [← htime]
      exact hstep

/-- A signed coordinate segment uses exactly the absolute displacement many steps. -/
theorem ceVolumeFastSignedSegment (d : ℕ) (hd : 2 ≤ d) (x : Site d)
    (i : Fin d) (delta : ℤ) (t : ℕ)
    (hstart : 0 < podo (fun w => ceEta d w + 3 * dirac (0 : Site d) w) t x)
    (hhigh : ∀ j, j < Int.natAbs delta →
      ceEta d
        (ceVolumeFastWalk x i (if 0 ≤ delta then 1 else -1) (j + 1)) =
        2 * (d : ℤ) - 1) :
    0 < podo (fun w => ceEta d w + 3 * dirac (0 : Site d) w)
      (t + Int.natAbs delta)
      (ceVolumeFastWalk x i (if 0 ≤ delta then 1 else -1) (Int.natAbs delta)) := by
  let dir : ℤ := if 0 ≤ delta then 1 else -1
  have hdir : dir = 1 ∨ dir = -1 := by
    dsimp [dir]
    split <;> simp_all
  exact ceVolumeFastSegment d hd x i dir (Int.natAbs delta) t hdir hstart hhigh

/-- The extra-coordinate part of the path, with coordinates in `S` already set. -/
def ceVolumeFastPartialSite (d : ℕ) (hd : 2 ≤ d) (b : ℤ)
    (z : Fin (d - 2) → ℤ) (S : Finset (Fin (d - 2))) : Site d :=
  ceVolumeSlowSite d hd 1 b (fun i => if i ∈ S then z i else 0)

/-- Inserting one fiber coordinate updates exactly its corresponding lattice site. -/
theorem ceVolumeFastPartialSite_insert (d : ℕ) (hd : 2 ≤ d) (b : ℤ)
    (z : Fin (d - 2) → ℤ) (S : Finset (Fin (d - 2))) (i : Fin (d - 2))
    (hi : i ∉ S) :
    ceVolumeFastPartialSite d hd b z (insert i S) =
      Function.update (ceVolumeFastPartialSite d hd b z S)
        ⟨(i : ℕ) + 2, by omega⟩ (z i) := by
  let ifull : Fin d := ⟨(i : ℕ) + 2, by omega⟩
  funext j
  by_cases hji : j = ifull
  · subst j
    simp [ceVolumeFastPartialSite, ceVolumeSlowSite, Function.update,
      ifull, hi]
  · by_cases hj0 : (j : ℕ) = 0
    · simp [ceVolumeFastPartialSite, ceVolumeSlowSite, Function.update,
        ifull, hj0, hji]
    · by_cases hj1 : (j : ℕ) = 1
      · simp [ceVolumeFastPartialSite, ceVolumeSlowSite, Function.update,
          ifull, hj1, hji]
      · let q : Fin (d - 2) := ⟨(j : ℕ) - 2, by omega⟩
        have hqi : q ≠ i := by
          intro heq
          have hval := congrArg Fin.val heq
          simp [q] at hval
          have hjfull : j = ifull := Fin.ext (by
            simp [ifull]
            omega)
          exact hji hjfull
        simp [ceVolumeFastPartialSite, ceVolumeSlowSite, Function.update,
          ifull, hj0, hj1, q, hqi, hji]

/-- A signed transverse fiber fires by its exact `ℓ¹` path length. -/
theorem ceVolumeFastAllExtras (d : ℕ) (hd : 2 ≤ d) (b : ℤ)
    (z : Fin (d - 2) → ℤ) (t : ℕ)
    (hstart : 0 < podo (fun y => ceEta d y + 3 * dirac (0 : Site d) y) t
      (ceVolumeFastPartialSite d hd b (fun _ => 0) ∅)) :
    ∀ S : Finset (Fin (d - 2)),
      0 < podo (fun y => ceEta d y + 3 * dirac (0 : Site d) y)
        (t + ∑ i ∈ S, Int.natAbs (z i))
        (ceVolumeFastPartialSite d hd b z S) := by
  intro S
  induction S using Finset.induction with
  | empty => simpa [ceVolumeFastPartialSite] using hstart
  | @insert i S hi ih =>
      let xstart := ceVolumeFastPartialSite d hd b z S
      let ifull : Fin d := ⟨(i : ℕ) + 2, by omega⟩
      let mi : ℕ := Int.natAbs (z i)
      have hdirDisp :
          xstart ifull + (mi : ℤ) * (if 0 ≤ z i then 1 else -1) = z i := by
        have hx : xstart ifull = 0 := by
          simp [xstart, ceVolumeFastPartialSite, ceVolumeSlowSite, ifull, hi]
        rw [hx]
        by_cases hzi : 0 ≤ z i
        · simp [mi, hzi, abs_of_nonneg hzi]
        · have hneg : z i < 0 := lt_of_not_ge hzi
          simp [mi, hzi, abs_of_neg hneg]
      have hfirst : ∀ r,
          ceVolumeFastWalk xstart ifull (if 0 ≤ z i then 1 else -1) r ⟨0, by omega⟩ = 1 := by
        intro r
        have hne : (⟨0, by omega⟩ : Fin d) ≠ ifull := by
          intro h
          have := congrArg Fin.val h
          norm_num [ifull] at this
        have hcoord := ceVolumeFastWalk_apply_of_ne xstart ifull ⟨0, by omega⟩
          (if 0 ≤ z i then 1 else -1) r hne
        have hx : xstart ⟨0, by omega⟩ = 1 := by
          simp [xstart, ceVolumeFastPartialSite, ceVolumeSlowSite]
        simpa [hx] using hcoord
      have hhigh : ∀ j, j < mi →
          ceEta d (ceVolumeFastWalk xstart ifull
            (if 0 ≤ z i then 1 else -1) (j + 1)) = 2 * (d : ℤ) - 1 := by
        intro j hj
        apply ceVolumeFast_high_of_first_mod_one d hd
        rw [hfirst]
        norm_num
      have hstart' :
          0 < podo (fun y => ceEta d y + 3 * dirac (0 : Site d) y)
            (t + ∑ j ∈ S, Int.natAbs (z j)) xstart := by
        exact ih
      have hsegment := ceVolumeFastSignedSegment d hd xstart ifull (z i)
        (t + ∑ j ∈ S, Int.natAbs (z j)) hstart' hhigh
      have hend :
          ceVolumeFastWalk xstart ifull (if 0 ≤ z i then 1 else -1) mi =
            ceVolumeFastPartialSite d hd b z (insert i S) := by
        rw [ceVolumeFastWalk_eq_update]
        · rw [ceVolumeFastPartialSite_insert d hd b z S i hi]
        · exact hdirDisp
      have hresult :
          0 < podo (fun y => ceEta d y + 3 * dirac (0 : Site d) y)
            (t + (∑ j ∈ S, Int.natAbs (z j)) + mi)
            (ceVolumeFastPartialSite d hd b z (insert i S)) := by
        simpa [hend, mi] using hsegment
      simpa [Finset.sum_insert hi, mi, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using hresult

/-- The actual threshold-three odometer fires at `(a_n,4k+1,z)` by
`a_n + |4k| + ‖z‖₁ + 2`, for signed `k` and every signed fiber. -/
theorem ce_podo_pos_signed_fast_site (d : ℕ) (hd : 2 ≤ d) (n : ℕ)
    (_hn : 1 ≤ n) (k : ℤ) (z : Fin (d - 2) → ℤ) :
    0 < podo (fun y => ceEta d y + 3 * dirac (0 : Site d) y)
      ((3 + 8 * n) + Int.natAbs (4 * k) +
        (∑ i : Fin (d - 2), Int.natAbs (z i)) + 2)
      (ceVolumeSlowSite d hd ((3 + 8 * n : ℕ) : ℤ) (4 * k + 1) z) := by
  let σ : Site d → ℤ := fun y => ceEta d y + 3 * dirac (0 : Site d) y
  let zeroExtra : Fin (d - 2) → ℤ := fun _ => 0
  let seed : Site d := ceVolumeFastPartialSite d hd 1 zeroExtra ∅
  have hseed : 0 < podo σ 3 seed := by
    have hrelay := aux_ce_relay_fires d hd 1
    have hsite : seed = (1 : ℤ) • e1 d + e2 d := by
      funext j
      by_cases hj0 : (j : ℕ) = 0
      · simp [seed, ceVolumeFastPartialSite, ceVolumeSlowSite, zeroExtra,
          e1, e2, hj0]
      · by_cases hj1 : (j : ℕ) = 1
        · simp [seed, ceVolumeFastPartialSite, ceVolumeSlowSite, zeroExtra,
            e1, e2, hj1]
        ·
          simp [seed, ceVolumeFastPartialSite, ceVolumeSlowSite, zeroExtra,
            e1, e2, hj0, hj1]
    simpa [σ, hsite] using hrelay
  let i2 : Fin d := ⟨1, by omega⟩
  let i0 : Fin d := ⟨0, by omega⟩
  let x2start : Site d := seed
  have hfirst : ∀ r, ceVolumeFastWalk x2start i2
      (if 0 ≤ 4 * k then 1 else -1) r i0 = 1 := by
    intro r
    have hne : i0 ≠ i2 := by
      intro h
      have := congrArg Fin.val h
      norm_num [i0, i2] at this
    have hcoord := ceVolumeFastWalk_apply_of_ne x2start i2 i0
      (if 0 ≤ 4 * k then 1 else -1) r hne
    have hx : x2start i0 = 1 := by
      simp [x2start, seed, ceVolumeFastPartialSite, ceVolumeSlowSite, zeroExtra, i0]
    simpa [hx] using hcoord
  have hhigh2 : ∀ j, j < Int.natAbs (4 * k) →
      ceEta d (ceVolumeFastWalk x2start i2
        (if 0 ≤ 4 * k then 1 else -1) (j + 1)) = 2 * (d : ℤ) - 1 := by
    intro j hj
    apply ceVolumeFast_high_of_first_mod_one d hd
    rw [hfirst]
    norm_num
  have hfire2 := ceVolumeFastSignedSegment d hd x2start i2 (4 * k) 3 hseed hhigh2
  have hdisp2 : x2start i2 +
      (Int.natAbs (4 * k) : ℤ) * (if 0 ≤ 4 * k then 1 else -1) = 4 * k + 1 := by
    have hx : x2start i2 = 1 := by
      simp [x2start, seed, ceVolumeFastPartialSite, ceVolumeSlowSite, zeroExtra, i2]
    rw [hx]
    by_cases hk : 0 ≤ 4 * k
    · simp [hk, abs_of_nonneg hk]
      ring
    · have hneg : 4 * k < 0 := lt_of_not_ge hk
      simp [hk, abs_of_neg hneg]
      ring
  have hx2walk : ceVolumeFastWalk x2start i2
      (if 0 ≤ 4 * k then 1 else -1) (Int.natAbs (4 * k)) =
      Function.update x2start i2 (4 * k + 1) :=
    ceVolumeFastWalk_eq_update x2start i2 (if 0 ≤ 4 * k then 1 else -1)
      (Int.natAbs (4 * k)) (4 * k + 1) hdisp2
  let zeroExtra' : Fin (d - 2) → ℤ := fun _ => 0
  have hx2end : Function.update x2start i2 (4 * k + 1) =
      ceVolumeSlowSite d hd 1 (4 * k + 1) zeroExtra' := by
    funext j
    by_cases hj0 : (j : ℕ) = 0
    · have hji : j ≠ i2 := by
        intro h
        have hv := congrArg Fin.val h
        simp [i2] at hv
        omega
      simp [x2start, seed, ceVolumeFastPartialSite, ceVolumeSlowSite,
        zeroExtra, i2, Function.update, hj0, hji]
    · by_cases hj1 : (j : ℕ) = 1
      · have hji : j = i2 := Fin.ext (by simpa [i2] using hj1)
        subst j
        simp [ceVolumeSlowSite, i2, Function.update]
      · have hji : j ≠ i2 := by
          intro h
          have hv := congrArg Fin.val h
          simp [i2] at hv
          omega
        simp [x2start, seed, ceVolumeFastPartialSite, ceVolumeSlowSite,
          zeroExtra, zeroExtra', i2, Function.update, hj0, hj1, hji]
  have hfire2' : 0 < podo σ (3 + Int.natAbs (4 * k))
      (ceVolumeSlowSite d hd 1 (4 * k + 1) zeroExtra') := by
    rw [hx2walk, hx2end] at hfire2
    simpa [σ] using hfire2
  have hfireExtra := ceVolumeFastAllExtras d hd (4 * k + 1) z
    (3 + Int.natAbs (4 * k)) (by
      simpa [σ, ceVolumeFastPartialSite, zeroExtra', Nat.add_assoc] using hfire2')
  let a : ℕ := 3 + 8 * n
  let xaxis : Site d := ceVolumeFastPartialSite d hd (4 * k + 1) z Finset.univ
  let iaxis : Fin d := ⟨0, by omega⟩
  let maxis : ℕ := a - 1
  have hmaxis : (maxis : ℤ) = (a : ℤ) - 1 := by
    dsimp [maxis, a]
    omega
  have hsecond : ∀ r, ceVolumeFastWalk xaxis iaxis 1 r ⟨1, by omega⟩ = 4 * k + 1 := by
    intro r
    have hne : (⟨1, by omega⟩ : Fin d) ≠ iaxis := by
      intro h
      have := congrArg Fin.val h
      norm_num [iaxis] at this
    have hcoord := ceVolumeFastWalk_apply_of_ne xaxis iaxis ⟨1, by omega⟩ 1 r hne
    have hx : xaxis ⟨1, by omega⟩ = 4 * k + 1 := by
      simp [xaxis, ceVolumeFastPartialSite, ceVolumeSlowSite]
    simpa [hx] using hcoord
  have hhighAxis : ∀ j, j < maxis →
      ceEta d (ceVolumeFastWalk xaxis iaxis 1 (j + 1)) = 2 * (d : ℤ) - 1 := by
    intro j hj
    apply ceVolumeFast_high_of_second_mod_one d hd
    rw [hsecond]
    omega
  have haxisStart : 0 < podo σ
      (3 + Int.natAbs (4 * k) + ∑ i : Fin (d - 2), Int.natAbs (z i)) xaxis := by
    simpa [σ, xaxis, ceVolumeFastPartialSite] using
      hfireExtra Finset.univ
  have haxis := ceVolumeFastSegment d hd xaxis iaxis 1 maxis
    (3 + Int.natAbs (4 * k) + ∑ i : Fin (d - 2), Int.natAbs (z i))
    (Or.inl rfl) haxisStart hhighAxis
  have hendAxis : ceVolumeFastWalk xaxis iaxis 1 maxis =
      ceVolumeSlowSite d hd (a : ℤ) (4 * k + 1) z := by
    have hx : xaxis iaxis = 1 := by
      simp [xaxis, ceVolumeFastPartialSite, ceVolumeSlowSite, iaxis]
    have hdisp : xaxis iaxis + (maxis : ℤ) * 1 = (a : ℤ) := by
      rw [hx, hmaxis]
      ring
    have hwalk := ceVolumeFastWalk_eq_update xaxis iaxis 1 maxis (a : ℤ) hdisp
    have hupdate : Function.update xaxis iaxis (a : ℤ) =
        ceVolumeSlowSite d hd (a : ℤ) (4 * k + 1) z := by
      funext j
      by_cases hj : j = iaxis
      · subst j
        simp [Function.update, ceVolumeSlowSite, iaxis]
      · have hj0 : (j : ℕ) ≠ 0 := by
          intro h
          exact hj (Fin.ext (by simpa [iaxis] using h))
        simp [Function.update, xaxis, ceVolumeFastPartialSite,
          ceVolumeSlowSite, iaxis, hj, hj0]
    exact hwalk.trans hupdate
  have hfinal : 0 < podo σ
      (3 + Int.natAbs (4 * k) + (∑ i : Fin (d - 2), Int.natAbs (z i)) + maxis)
      (ceVolumeSlowSite d hd (a : ℤ) (4 * k + 1) z) := by
    simpa [hendAxis, Nat.add_assoc] using haxis
  have hdeadline :
      3 + Int.natAbs (4 * k) + (∑ i : Fin (d - 2), Int.natAbs (z i)) + maxis =
        (3 + 8 * n) + Int.natAbs (4 * k) +
          (∑ i : Fin (d - 2), Int.natAbs (z i)) + 2 := by
    dsimp [a, maxis]
    omega
  rw [hdeadline] at hfinal
  simpa [σ, a] using hfinal

end Exploding
