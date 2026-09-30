/-
The first step of the second inequality of Lemma 3.7: a site reached by the last wave
has, near it, a good cube of the infinite cluster that fires shortly afterwards.  The
wave reaches `x` along a path of distinct sites; the bounding rectangle of the last
stretch of that path fills by local convexity and has a long side; a long row of
macroscopic cubes along that side meets the infinite cluster; and the good cube so
found is crossed by a positive line.
-/
import Exploding.Support.Vocab
import Exploding.Support.SubPub
import Exploding.Support.PCloseProofPath
import Exploding.Support.PCloseProofGeom
import Exploding.Support.PCloseProofCube
import Exploding.Support.PCloseProofWalk
import Exploding.Support.PCloseProofMacro

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The floor quotient `(a - 1) / k` is at most `|a| + 1` in absolute value. -/
theorem pclose_ediv_abs (a : ℤ) (k : ℕ) (hk : 1 ≤ k) : |(a - 1) / (k : ℤ)| ≤ |a| + 1 := by
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hk0 : (0 : ℤ) < (k : ℤ) := by linarith
  have h1 := Int.emod_add_mul_ediv (a - 1) (k : ℤ)
  have h2 := Int.emod_nonneg (a - 1) (ne_of_gt hk0)
  have h3 := Int.emod_lt_of_pos (a - 1) hk0
  set u := (a - 1) / (k : ℤ) with hu
  set r := (a - 1) % (k : ℤ) with hr
  rcases le_or_gt 0 u with hu0 | hu0
  · rw [abs_of_nonneg hu0]
    have : u ≤ (k : ℤ) * u := by nlinarith
    have : a ≤ |a| := le_abs_self a
    linarith
  · rw [abs_of_neg hu0]
    have h4 : (k : ℤ) * (u + 1) ≤ u + 1 := by nlinarith
    have : -a ≤ |a| := neg_le_abs a
    nlinarith

theorem pclose_update_add_smul (x : Site d) (i : Fin d) (u r : ℤ) :
    Function.update x i u + r • unit i = Function.update x i (u + r) := by
  funext l
  rw [Pi.add_apply]
  by_cases hl : l = i
  · subst hl; simp [unit]
  · simp [unit, hl]

set_option maxHeartbeats 1000000 in
/-- **The first fired good cube.**  If the wave is positive at `x` at time `t`, and `x`
is far from the centre, then some good cube `Q_k(Q)` of the infinite cluster, at
macroscopic distance at most `L` from the macroscopic index of `x`, has fired by time
`t + (2L+1)^d + k^d`. -/
theorem pclose_first_cube (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (N : ℕ) (hN : 1 ≤ N) (k : ℕ) (hk : 1 ≤ k) (Cinf : Set (Site d))
    (hgood : ∀ j ∈ Cinf, GoodAt η k j) (Z n1 : ℕ)
    (hhole : ∀ y ∈ (cent d n1 : Set (Site d)), y ∉ Cinf →
      (componentIn Cinfᶜ y).Finite ∧ (componentIn Cinfᶜ y).ncard < Z)
    (x : Site d) (t : ℕ) (hx : 0 < wave η N 0 t x)
    (L : ℕ) (hL : L = (k * (Z + 2)) ^ d) (hxL : (L : ℤ) ≤ mnorm x)
    (hn1 : mnorm x + ((L + 3 : ℕ) : ℤ) ≤ (n1 : ℤ)) :
    ∃ Q : Site d, Q ∈ Cinf ∧ PCloseFired η N k 0 (t + (2 * L + 1) ^ d + k ^ d) Q ∧
      mnorm (Q - macroIdx k x) ≤ (L : ℤ) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by linarith
  have hη0 : ∀ y, 0 ≤ η y := fun y => by linarith [hlow y]
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hk0 : (0 : ℤ) < (k : ℤ) := by linarith
  have hS1 : 1 ≤ k * (Z + 2) := Nat.mul_pos (by omega) (by omega)
  -- the path from the centre to `x`
  obtain ⟨m, z, hz0, hzm, hadj, hinj, hpos⟩ :=
    pclose_path_extract η hη0 hhigh hd0 N t x hx
  have hmx : mnorm x ≤ (m : ℤ) := by
    have := pclose_mnorm_le_of_path m z hz0 hadj
    rwa [hzm] at this
  have hLm : L ≤ m := by
    have : (L : ℤ) ≤ (m : ℤ) := le_trans hxL hmx
    exact_mod_cast this
  -- its last stretch
  set z' : ℕ → Site d := fun j => z (m - L + j) with hz'
  have hadj' : ∀ j, j < L → (lattice d).Adj (z' j) (z' (j + 1)) := by
    intro j hj
    have := hadj (m - L + j) (by omega)
    simpa [hz', show m - L + (j + 1) = m - L + j + 1 from by omega] using this
  have hpos' : ∀ j, j ≤ L → 0 < wave η N 0 t (z' j) := fun j hj => hpos _ (by omega)
  set A' : Set (Site d) := z' '' {j : ℕ | j ≤ L} with hA'
  have hA'fin : A'.Finite := Set.Finite.image _ (Set.finite_Iic L)
  have hxA' : x ∈ A' := ⟨L, show L ≤ L from le_rfl, by simp [hz', hzm, show m - L + L = m from by omega]⟩
  have hball : A' ⊆ pcloseBall x L := by
    have := pclose_path_tail_ball m z hadj L hLm
    rw [hzm] at this
    exact this
  have hncard : A'.ncard = L + 1 := pclose_path_tail_ncard m z hinj L hLm
  have hfin : (br A').Finite := br_finite A' hA'fin
  have hbrball : br A' ⊆ pcloseBall x L := pclose_br_subset_ball A' x L hball
  have hcardbr : hfin.toFinset.card ≤ (2 * L + 1) ^ d := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    obtain ⟨hbf, hbc⟩ := pclose_ball_ncard_le x L
    exact le_trans (Set.ncard_le_ncard hbrball hbf) hbc
  have hfill := pclose_fill hd η hlow hhigh N hN 0 L z' hadj' t hpos' hfin _ hcardbr
  -- a long side of the filled rectangle
  obtain ⟨i, a, b, hab, hseg⟩ := pclose_long_side hd1 A' hA'fin ⟨x, hxA'⟩ (k * (Z + 2)) hS1
    (by rw [hncard, ← hL]; omega)
  have hxbr : x ∈ br A' := mem_br_of_mem A' hxA'
  have hS1' : (1 : ℤ) ≤ ((k * (Z + 2) : ℕ) : ℤ) := by exact_mod_cast hS1
  have hab' : a ≤ b := by linarith
  have hseg_ball : ∀ v, a ≤ v → v ≤ b → |v - x i| ≤ (L : ℤ) := by
    intro v hv1 hv2
    have := hbrball (hseg x hxbr v hv1 hv2) i
    simpa using this
  have ha_low : x i - L ≤ a := by
    have := hseg_ball a le_rfl hab'
    rw [abs_le] at this; linarith [this.1]
  have hb_up : b ≤ x i + L := by
    have := hseg_ball b hab' le_rfl
    rw [abs_le] at this; linarith [this.2]
  -- the row of macroscopic cubes along the side
  set mac := macroIdx k x with hmac
  set q : ℤ := (a - 1) / (k : ℤ) + 1 with hq
  have hkq : (k : ℤ) * q = (k : ℤ) * ((a - 1) / (k : ℤ)) + k := by rw [hq]; ring
  have hq1 : a ≤ (k : ℤ) * q := by
    have h1 := Int.emod_add_mul_ediv (a - 1) (k : ℤ)
    have h3 := Int.emod_lt_of_pos (a - 1) hk0
    linarith
  have hq2 : (k : ℤ) * q ≤ a - 1 + k := by
    have h1 := Int.emod_add_mul_ediv (a - 1) (k : ℤ)
    have h2 := Int.emod_nonneg (a - 1) (ne_of_gt hk0)
    linarith
  have hJ0 : Function.update mac i q ∈ (cent d n1 : Set (Site d)) := by
    intro l
    by_cases hl : l = i
    · subst hl
      simp only [Function.update_self]
      have h1 : |(a - 1) / (k : ℤ)| ≤ |a| + 1 := pclose_ediv_abs a k hk
      have h2 : |q| ≤ |(a - 1) / (k : ℤ)| + 1 := by
        rw [hq]; exact abs_add_le _ _ |>.trans (by simp)
      have h5 := pclose_abs_coord_le x l
      push_cast at hn1
      have h6 : |a| ≤ |x l| + L := by
        rcases le_or_gt 0 a with h | h
        · rw [abs_of_nonneg h]
          have := le_abs_self (x l)
          linarith
        · rw [abs_of_neg h]
          have := neg_le_abs (x l)
          linarith
      linarith
    · simp only [Function.update_of_ne hl]
      have h1 := pclose_macro_abs k hk x l
      have h2 := pclose_abs_coord_le x l
      push_cast at hn1
      linarith
  obtain ⟨r, hrZ, hrmem⟩ := pclose_ray_hit Cinf Z n1 hhole _ hJ0 i
  set Q := Function.update mac i q + (r : ℤ) • unit i with hQ
  have hQe : Q = Function.update mac i (q + r) := by
    rw [hQ]; exact pclose_update_add_smul mac i q r
  have hQC : Q ∈ Cinf := hrmem
  have hr0 : (0 : ℤ) ≤ r := Int.natCast_nonneg r
  have hr1 : (r : ℤ) ≤ Z := by exact_mod_cast hrZ
  refine ⟨Q, hQC, ?_, ?_⟩
  · -- the cube is crossed by a positive line
    have hzl : (fun l => if l = i then (1 : ℤ) else x l - (k : ℤ) * mac l) ∈ cube d k := by
      intro l
      by_cases hl : l = i
      · simp only [hl, if_true]; exact ⟨le_rfl, hk1⟩
      · simp only [hl, if_false]
        have := pclose_macro_bounds k hk x l
        constructor <;> linarith [this.1, this.2]
    refine pclose_cube_of_line hd η hη0 hhigh N k hN 0 Q (hgood Q hQC) i _
      (Or.inl hzl) (t + (2 * L + 1) ^ d) ?_
    intro w hw
    have hwQ : w + (k : ℤ) • Q = Function.update x i (w i + (k : ℤ) * (q + r)) := by
      funext l
      rw [hQe]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hl : l = i
      · subst hl; simp
      · have hwl := hw.2 l hl
        simp only [hl, if_false] at hwl
        simp only [Function.update_of_ne hl, hwl]
        rw [hmac]; ring
    rw [hwQ]
    have hwi := hw.1
    have hkr : (k : ℤ) * r ≤ (k : ℤ) * Z := mul_le_mul_of_nonneg_left hr1 hk0.le
    have hkr0 : (0 : ℤ) ≤ (k : ℤ) * r := mul_nonneg hk0.le hr0
    have hexp : (k : ℤ) * (q + r) = (k : ℤ) * q + (k : ℤ) * r := by ring
    have h2 : ((k * (Z + 2) : ℕ) : ℤ) = (k : ℤ) * Z + 2 * k := by push_cast; ring
    have hv1 : a ≤ w i + (k : ℤ) * (q + r) := by
      linarith [hwi.1]
    have hv2 : w i + (k : ℤ) * (q + r) ≤ b := by
      linarith [hwi.2]
    exact hfill _ (hseg x hxbr _ hv1 hv2)
  · -- the distance from the macroscopic index of `x`
    have hxi := pclose_macro_bounds k hk x i
    have hu : |q + r - mac i| ≤ (L : ℤ) := by
      have hkr : (k : ℤ) * r ≤ (k : ℤ) * Z := mul_le_mul_of_nonneg_left hr1 hk0.le
      have hkr0 : (0 : ℤ) ≤ (k : ℤ) * r := mul_nonneg hk0.le hr0
      have hexp : (k : ℤ) * (q + r) = (k : ℤ) * q + (k : ℤ) * r := by ring
      have hkq1 : a ≤ (k : ℤ) * (q + r) := by linarith
      have h2 : ((k * (Z + 2) : ℕ) : ℤ) = (k : ℤ) * Z + 2 * k := by push_cast; ring
      have hkq2 : (k : ℤ) * (q + r) + k ≤ b := by linarith
      have hexp2 : (k : ℤ) * (q + r - mac i) = (k : ℤ) * (q + r) - (k : ℤ) * mac i := by ring
      have hlo : 1 - (L : ℤ) ≤ (k : ℤ) * (q + r - mac i) := by
        linarith [hxi.1, hxi.2]
      have hhi : (k : ℤ) * (q + r - mac i) ≤ L := by
        linarith [hxi.1, hxi.2]
      set u := q + r - mac i with hu
      have hk1u : (k : ℤ) * u - u = ((k : ℤ) - 1) * u := by ring
      rw [abs_le]
      constructor
      · by_contra hcon
        push Not at hcon
        have hneg : u < 0 := by
          have : (0 : ℤ) ≤ L := Int.natCast_nonneg L
          linarith
        have h6 := mul_nonneg (sub_nonneg.mpr hk1) (neg_nonneg.mpr hneg.le)
        have h5 : ((k : ℤ) - 1) * (-u) = -((k : ℤ) * u) + u := by ring
        linarith
      · by_contra hcon
        push Not at hcon
        have hpos : 0 < u := by
          have : (0 : ℤ) ≤ L := Int.natCast_nonneg L
          linarith
        have h6 := mul_nonneg (sub_nonneg.mpr hk1) hpos.le
        have h5 : ((k : ℤ) - 1) * u = (k : ℤ) * u - u := by ring
        linarith
    have hnorm : mnorm (Q - mac) = |q + r - mac i| := by
      unfold mnorm
      rw [Finset.sum_eq_single i]
      · rw [hQe]; simp
      · intro l _ hl
        rw [hQe]; simp [Function.update_of_ne hl]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hnorm]
    exact hu

end Exploding
