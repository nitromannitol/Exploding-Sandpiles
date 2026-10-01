/-
Proposition 5.1 of the paper (generalized last wave): a long lit path lights a tile of `C_∞` near it.

A path of `p + 1` distinct adjacent sites lit by the `N`-wave at time `t`, with
`p + 1 ≥ (log n')^{γ_p}` and `p + 1 ≥ (∑ k (r + 2))^d`, has a bounding rectangle with a side of length
at least `∑ k (r + 2)` and is entirely lit at time `t + (p+1)^d` (Hypothesis 5.3); a row of more than
`(log n')^{5/2}` macroscopic sites inside that side meets `C_∞`, and the line of the tile in the lit
rectangle lights the tile `∏ k` steps later (Hypothesis 5.4).
-/
import Exploding.Support.GLWSec3S

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

/-- **A long lit path lights a tile of the cluster near it.** -/
theorem glws_path_to_tile (hd : 2 ≤ d) (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (k : Fin d → ℕ) (hk : ∀ i, 0 < k i)
    (Cinf : Set (Site d)) (hgood : ∀ j ∈ Cinf, StronglyBoxCrossed η k j)
    (n0h : ℕ) (hole : ∀ n : ℕ, n0h ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ Cinf →
      (componentIn Cinfᶜ x).Finite ∧ ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2))
    (γp : ℝ) (hpf : glws_PF d γp η) :
    ∃ n0 : ℕ, ∀ n' : ℕ, n0 ≤ n' → ∀ r : ℕ,
      Real.log ((n' + 1 : ℕ) : ℝ) ^ ((5 : ℝ) / 2) ≤ (r : ℝ) →
      ∀ (N : ℕ), 1 ≤ N → ∀ (zc : Site d) (t p : ℕ) (z : ℕ → Site d),
      (∀ i, i ≤ p → z i ∈ cent d n') →
      (∀ i j, i ≤ p → j ≤ p → z i = z j → i = j) →
      (∀ i, i < p → (lattice d).Adj (z i) (z (i + 1))) →
      (∀ i, i ≤ p → 0 < wave η N zc t (z i)) →
      Real.log n' ^ γp ≤ ((p + 1 : ℕ) : ℝ) →
      ((∑ i, k i) * (r + 2)) ^ d ≤ p + 1 →
      ∃ j ∈ Cinf, glws_Fired η N k zc (t + (p + 1) ^ d + ∏ l, k l) j ∧
        ∀ y ∈ rboxShift k j, ∀ m, |y m - z 0 m| ≤ (p : ℤ) + ((∑ i, k i : ℕ) : ℤ) := by
  classical
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  have hdpos : 0 < d := by omega
  obtain ⟨n0pf, hfill⟩ := glws_pf_fill d γp η hd0 hlow hhigh hpf
  refine ⟨max n0pf n0h, fun n' hn' r hr N hN zc t p z hcent hinj hadj hlit hlenR hS => ?_⟩
  have hn0pf : n0pf ≤ n' := le_trans (le_max_left _ _) hn'
  have hn0h : n0h ≤ n' + 1 := by have := le_trans (le_max_right _ _) hn'; omega
  set kmax : ℕ := ∑ i, k i with hkmax
  have hkmax1 : 1 ≤ kmax := by
    have h0 : 0 < d := hdpos
    exact le_trans (hk ⟨0, h0⟩)
      (Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))
  set A : Set (Site d) := z '' {i : ℕ | i < p + 1} with hA
  have hinj' : Set.InjOn z {i : ℕ | i < p + 1} := by
    intro i hi j hj hij
    exact hinj i j (by simpa using Nat.lt_succ_iff.mp hi) (by simpa using Nat.lt_succ_iff.mp hj) hij
  have hAfin : A.Finite := (Set.finite_lt_nat (p + 1)).image z
  have h0mem : z 0 ∈ A := ⟨0, Nat.succ_pos p, rfl⟩
  have hAcard : A.ncard = p + 1 := by
    rw [hA, hinj'.ncard_image]
    have : ({i : ℕ | i < p + 1} : Set ℕ) = ↑(Finset.range (p + 1)) := by ext i; simp
    rw [this, Set.ncard_coe_finset, Finset.card_range]
  set S : ℕ := kmax * (r + 2) with hSdef
  have hS1 : 1 ≤ S := Nat.mul_pos (by omega) (by omega)
  obtain ⟨i, a, b, hab, hupd⟩ := pclose_long_side hdpos A hAfin ⟨z 0, h0mem⟩ S hS1
    (by rw [hAcard]; exact hS)
  have hx0 : z 0 ∈ br A := mem_br_of_mem A h0mem
  have hab' : a ≤ b := by
    have : (1 : ℤ) ≤ (S : ℤ) := by exact_mod_cast hS1
    linarith
  set lo : Site d := Function.update (z 0) i a with hlo
  set hi : Site d := Function.update (z 0) i b with hhi
  have hlobr : lo ∈ br A := hupd _ hx0 a le_rfl hab'
  have hhibr : hi ∈ br A := hupd _ hx0 b hab' le_rfl
  -- the bounding rectangle lies in the box of radius `n'`
  have hAbox : A ⊆ pcloseBox (fun _ => -(n' : ℤ)) (fun _ => (n' : ℤ)) := by
    rintro y ⟨q, hq, rfl⟩ m
    have := hcent q (by simpa using Nat.lt_succ_iff.mp hq) m
    rw [abs_le] at this
    exact this
  have hbrbox := pclose_br_subset_box A _ _ hAbox
  have hbound : ∀ w ∈ br A, ∀ m, |w m| ≤ (n' : ℤ) := by
    intro w hw m
    have := hbrbox hw m
    rw [abs_le]
    exact this
  have hbox : ∀ m, lo m ≤ hi m := by
    intro m
    by_cases hm : m = i
    · subst hm; simp [hlo, hhi, hab']
    · simp [hlo, hhi, hm]
  have hlo_abs : ∀ m, |lo m| ≤ (n' : ℤ) := fun m => hbound lo hlobr m
  have hhi_abs : ∀ m, |hi m| ≤ (n' : ℤ) := fun m => hbound hi hhibr m
  have hlen : (k i : ℤ) * ((r : ℤ) + 2) ≤ hi i - lo i + 1 := by
    have h1 : hi i - lo i + 1 = b - a + 1 := by simp [hlo, hhi]
    have h2 : (k i : ℤ) * ((r : ℤ) + 2) ≤ (S : ℤ) := by
      have : k i ≤ kmax := Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
      have : k i * (r + 2) ≤ kmax * (r + 2) := Nat.mul_le_mul_right _ this
      exact_mod_cast this
    rw [h1]
    linarith
  obtain ⟨μ, hrowc, hline⟩ := glws_row_geom k hk i lo hi hbox n' hlo_abs hhi_abs r hlen
  obtain ⟨t0, ht0, hj⟩ := glws_row_hole Cinf (n' + 1) (hole (n' + 1) hn0h) i μ r hr hrowc
  obtain ⟨zz, hzz, hlinezz, htile⟩ := hline t0 ht0
  -- the line lies in the bounding rectangle, which is lit
  have hbrline : ∀ w ∈ rline k (μ + (t0 : ℤ) • unit i) i zz, w ∈ br A := by
    intro w hw
    have h := hlinezz w hw
    have hw' : w = Function.update (z 0) i (w i) := by
      funext m
      by_cases hm : m = i
      · subst hm; simp
      · simp only [Function.update_of_ne hm]
        have := h m
        have hl : lo m = z 0 m := by simp [hlo, hm]
        have hh : hi m = z 0 m := by simp [hhi, hm]
        rw [hl] at this
        rw [hh] at this
        exact le_antisymm this.2 this.1
    have hwi := h i
    have hli : lo i = a := by simp [hlo]
    have hhi' : hi i = b := by simp [hhi]
    rw [hli] at hwi
    rw [hhi'] at hwi
    rw [hw']
    exact hupd _ hx0 (w i) hwi.1 hwi.2
  have hfilled := hfill N hN zc n' hn0pf (p + 1) z hlenR
    (fun q hq => hcent q (by omega))
    (fun q q' hq hq' h => hinj q q' (by omega) (by omega) h)
    (fun q hq => hadj q (by omega)) t (fun q hq => hlit q (by omega))
  have hpos : ∀ w ∈ rline k (μ + (t0 : ℤ) • unit i) i zz, 0 < wave η N zc (t + (p + 1) ^ d) w :=
    fun w hw => hfilled w (hbrline w hw)
  have hfired := glws_tile_of_line hd0 η hlow hhigh N hN zc k (μ + (t0 : ℤ) • unit i)
    (hgood _ hj) i zz hzz (t + (p + 1) ^ d) hpos
  refine ⟨μ + (t0 : ℤ) • unit i, hj, hfired, fun y hy m => ?_⟩
  -- the tile is within `p + kmax` of the start of the path
  have hpath : ∀ q, q ≤ p → ∀ m, |z q m - z 0 m| ≤ (p : ℤ) := by
    intro q hq m
    have := glws_path_coord z hadj m q hq
    have hqp : (q : ℤ) ≤ p := by exact_mod_cast hq
    linarith
  have hrange : ∀ w ∈ br A, ∀ m, z 0 m - (p : ℤ) ≤ w m ∧ w m ≤ z 0 m + (p : ℤ) := by
    intro w hw m
    obtain ⟨⟨y1, ⟨q1, hq1, rfl⟩, h1⟩, ⟨y2, ⟨q2, hq2, rfl⟩, h2⟩⟩ := hw m
    have e1 := hpath q1 (by simpa using Nat.lt_succ_iff.mp hq1) m
    have e2 := hpath q2 (by simpa using Nat.lt_succ_iff.mp hq2) m
    rw [abs_le] at e1 e2
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
  obtain ⟨hyl, hym⟩ := htile y hy
  by_cases hm : m = i
  · subst hm
    have h1 := hrange lo hlobr m
    have h2 := hrange hi hhibr m
    have hli : lo m = a := by simp [hlo]
    have hhi' : hi m = b := by simp [hhi]
    rw [hli] at h1 hyl
    rw [hhi'] at h2 hyl
    rw [abs_le]
    have hkm : (0 : ℤ) ≤ ((∑ i, k i : ℕ) : ℤ) := Int.natCast_nonneg _
    constructor <;> linarith [hyl.1, hyl.2, h1.1, h1.2, h2.1, h2.2]
  · have := hym m hm
    have hl : lo m = z 0 m := by simp [hlo, hm]
    rw [hl] at this
    have hkk : (k m : ℤ) ≤ ((∑ i, k i : ℕ) : ℤ) := by
      have : k m ≤ ∑ i, k i := Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ m)
      exact_mod_cast this
    have hp0 : (0 : ℤ) ≤ (p : ℤ) := Int.natCast_nonneg p
    have hk1 : (1 : ℤ) ≤ (k m : ℤ) := by exact_mod_cast hk m
    rw [abs_le]
    constructor <;> linarith [this.1, this.2]

end Exploding
