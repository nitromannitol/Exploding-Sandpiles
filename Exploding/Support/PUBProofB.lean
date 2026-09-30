/-
Support for Lemma 3.6 of `paper/exploding.tex` (packet PUB): the norm bookkeeping, a walk of a
finite chemical distance, the unboundedness of the support of a non-stabilizing wave, and the
first lit good cube: a long lit path lights a rectangle containing a whole line of a good cube
of the infinite cluster.
-/
import Exploding.Support.PUBProofA

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-! ### Norms -/

theorem pub_mnorm_nonneg (x : Site d) : 0 ≤ mnorm x :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem pub_mnorm_add_le (a b : Site d) : mnorm (a + b) ≤ mnorm a + mnorm b :=
  aux_finite_exploding_mnorm_add_le a b

theorem pub_mnorm_neg (a : Site d) : mnorm (-a) = mnorm a :=
  aux_finite_exploding_mnorm_neg a

theorem pub_mnorm_sub_comm (a b : Site d) : mnorm (a - b) = mnorm (b - a) := by
  rw [← pub_mnorm_neg (a - b)]
  congr 1
  abel

theorem pub_mnorm_sub_le (a b c : Site d) : mnorm (a - c) ≤ mnorm (a - b) + mnorm (b - c) := by
  have := pub_mnorm_add_le (a - b) (b - c)
  rwa [show a - b + (b - c) = a - c by abel] at this

theorem pub_abs_le_mnorm (x : Site d) (i : Fin d) : |x i| ≤ mnorm x :=
  abs_coord_le_mnorm x i

/-- The norm of a multiple of a unit vector. -/
theorem pub_mnorm_smul_unit (i : Fin d) (a : ℤ) : mnorm (a • (unit i : Site d)) = |a| := by
  simp only [mnorm, Pi.smul_apply, smul_eq_mul, unit]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

/-- The norm of a point moved along one coordinate. -/
theorem pub_mnorm_update_sub (z : Site d) (i : Fin d) (v : ℤ) :
    mnorm ((fun j => if j = i then v else z j) - z) = |v - z i| := by
  have : ((fun j => if j = i then v else z j) - z) = (v - z i) • (unit i : Site d) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [unit]
    · simp [hj, unit]
  rw [this, pub_mnorm_smul_unit]

/-- Floor division by `k ≥ 2` keeps a coordinate in the box. -/
theorem pub_macro_coord_le (k : ℕ) (hk : 2 ≤ k) (n : ℕ) (hn : 1 ≤ n) (a : ℤ)
    (ha : |a| ≤ (n : ℤ)) : |(a - 1) / (k : ℤ)| ≤ (n : ℤ) := by
  have hk0 : (0 : ℤ) < (k : ℤ) := by exact_mod_cast (by omega : 0 < k)
  have hk2 : (2 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hn1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  rw [abs_le] at ha ⊢
  constructor
  · rw [Int.le_ediv_iff_mul_le hk0]
    nlinarith [ha.1]
  · rw [← Int.lt_add_one_iff, Int.ediv_lt_iff_lt_mul hk0]
    nlinarith [ha.2]

/-- The coordinates of the macroscopic index are bounded by those of the site, up to one. -/
theorem pub_macro_abs_le (k : ℕ) (hk : 1 ≤ k) (a : ℤ) :
    |(a - 1) / (k : ℤ)| ≤ |a| + 1 := by
  have hk0 : (0 : ℤ) < (k : ℤ) := by exact_mod_cast (by omega : 0 < k)
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hprod : 0 ≤ (|a| + 1) * ((k : ℤ) - 1) :=
    mul_nonneg (by positivity) (by linarith)
  have h1 : (a - 1) / (k : ℤ) ≤ |a| + 1 := by
    rw [← Int.lt_add_one_iff, Int.ediv_lt_iff_lt_mul hk0]
    nlinarith [le_abs_self a, abs_nonneg a]
  have h2 : -(|a| + 1) ≤ (a - 1) / (k : ℤ) := by
    rw [Int.le_ediv_iff_mul_le hk0]
    nlinarith [neg_abs_le a, abs_nonneg a]
  exact abs_le.mpr ⟨h2, h1⟩

/-! ### Walks of finite chemical distance -/

/-- A finite chemical distance is the length of a walk. -/
theorem pub_walk_of_chemDist (C : Set (Site d)) (x y : Site d) (m : ℕ)
    (h : chemDist C x y = (m : ℕ∞)) :
    ∃ (hx : x ∈ C) (hy : y ∈ C) (p : ((lattice d).induce C).Walk ⟨x, hx⟩ ⟨y, hy⟩),
      p.length = m := by
  have hex : ∃ n : ℕ, ∃ (hx : x ∈ C) (hy : y ∈ C)
      (p : ((lattice d).induce C).Walk ⟨x, hx⟩ ⟨y, hy⟩), p.length = n := by
    by_contra hcon
    have := sInf_coe_top (P := fun n : ℕ => ∃ (hx : x ∈ C) (hy : y ∈ C)
      (p : ((lattice d).induce C).Walk ⟨x, hx⟩ ⟨y, hy⟩), p.length = n) hcon
    rw [chemDist] at h
    rw [this] at h
    exact absurd h (by simp)
  obtain ⟨n, hn, heq⟩ := sInf_coe_attained (P := fun n : ℕ => ∃ (hx : x ∈ C) (hy : y ∈ C)
      (p : ((lattice d).induce C).Walk ⟨x, hx⟩ ⟨y, hy⟩), p.length = n) hex
  rw [chemDist] at h
  rw [heq] at h
  have : n = m := by exact_mod_cast h
  subst this
  exact hn

/-! ### The support of a non-stabilizing wave is unbounded -/

theorem pub_support_unbounded (hd : 2 ≤ d) (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (N : ℕ) (hns : ¬ WaveStabilizable η N (0 : Site d)) :
    ∀ R : ℕ, ∃ (t : ℕ) (x : Site d), 0 < wave η N (0 : Site d) t x ∧ (R : ℤ) < mnorm x := by
  intro R
  by_contra hcon
  push Not at hcon
  have hd2 : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by linarith
  apply hns
  refine aux_pub_reach_confined_stabilizable η hlow hhigh hd0 N 0 (cent d R)
    (aux_finite_exploding_cent_card d R).1 ?_
  intro t x hx
  by_contra hne
  have hpos : 0 < wave η N (0 : Site d) t x :=
    lt_of_le_of_ne (wave_nonneg η hlow N 0 t x) (Ne.symm hne)
  apply hx
  intro l
  exact le_trans (pub_abs_le_mnorm x l) (hcon t x hpos)

/-! ### The first lit good cube -/

theorem pub_mem_br_seg (A : Set (Site d)) (w : Site d) (hw : w ∈ A) (h0 : (0 : Site d) ∈ A)
    (i : Fin d) (p : Site d) (hp : ∀ l, l ≠ i → p l = 0)
    (hpi : (0 ≤ p i ∧ p i ≤ w i) ∨ (w i ≤ p i ∧ p i ≤ 0)) : p ∈ br A := by
  intro l
  by_cases hl : l = i
  · subst hl
    rcases hpi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨⟨0, h0, h1⟩, ⟨w, hw, h2⟩⟩
    · exact ⟨⟨w, hw, h1⟩, ⟨0, h0, h2⟩⟩
  · have := hp l hl
    exact ⟨⟨0, h0, by simp [this]⟩, ⟨0, h0, by simp [this]⟩⟩

/-- **The first lit good cube of the infinite cluster.**  A non-stabilizing wave has a lit path
from the centre to a site far out along some coordinate; the path's bounding rectangle is lit, and
it contains a whole line of a good cube of the infinite cluster, found on the ray from the
centre's cube by the hole bound. -/
theorem pub_initial_cube (hd : 2 ≤ d) (η : Site d → ℤ) (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (N : ℕ) (hN : 1 ≤ N)
    (hns : ¬ WaveStabilizable η N (0 : Site d)) (k : ℕ) (hk : 1 ≤ k) (Cinf : Set (Site d))
    (hCinf : IsInfiniteConnectedGoodSet η k Cinf) (n0h : ℕ)
    (hhole : ∀ n : ℕ, n0h ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ Cinf →
      (componentIn Cinfᶜ x).Finite ∧
        ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2))
    (n1 : ℕ) (hn1 : n0h ≤ n1)
    (hρ : ((Nat.ceil (Real.log n1 ^ ((5 : ℝ) / 2)) : ℕ) : ℤ) + 2 ≤ (n1 : ℤ)) :
    ∃ z0 ∈ Cinf, ∃ T1 : ℕ, ∀ x ∈ cube d k, 0 < wave η N (0 : Site d) T1 (x + (k : ℤ) • z0) := by
  have hd2 : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by linarith
  have hlow0 : ∀ x, 0 ≤ η x := fun x => by linarith [hlow x]
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  set ρ : ℕ := Nat.ceil (Real.log n1 ^ ((5 : ℝ) / 2)) with hρdef
  have hρle : Real.log n1 ^ ((5 : ℝ) / 2) ≤ (ρ : ℝ) := Nat.le_ceil _
  set W : ℕ := k * (ρ + 2) with hW
  obtain ⟨t, w, hwpos, hwbig⟩ := pub_support_unbounded hd η hlow0 hhigh N hns (d * W)
  obtain ⟨i, hi⟩ : ∃ i : Fin d, (W : ℤ) ≤ |w i| := by
    by_contra hcon
    push Not at hcon
    have h1 : mnorm w ≤ (d : ℤ) * W := by
      calc mnorm w = ∑ l, |w l| := rfl
        _ ≤ ∑ _l : Fin d, (W : ℤ) := Finset.sum_le_sum fun l _ => (hcon l).le
        _ = (d : ℤ) * W := by simp
    have h2 : ((d * W : ℕ) : ℤ) < mnorm w := hwbig
    push_cast at h2
    linarith
  obtain ⟨m, zp, hz0, hzm, hadj, hpos⟩ := pub_wave_path η hlow0 hhigh N t w hwpos
  obtain ⟨τ, hτ⟩ := pub_rect_lit hd η hlow hhigh N hN t m zp hadj hpos
  set A : Set (Site d) := zp '' {j : ℕ | j ≤ m} with hA
  have h0A : (0 : Site d) ∈ A := ⟨0, by simp, hz0⟩
  have hwA : w ∈ A := ⟨m, by simp, hzm⟩
  set zl : Site d := fun l => if l = i then 1 else (k : ℤ) with hzl
  have hzlc : zl ∈ closureN (cube d k) := Or.inl (fun l => by
    by_cases hl : l = i
    · simp [hzl, hl]; exact hk
    · simp [hzl, hl]; exact hk)
  have hρn : (ρ : ℤ) + 2 ≤ (n1 : ℤ) := hρ
  have hn1pos : (1 : ℤ) ≤ (n1 : ℤ) := by linarith [(Int.natCast_nonneg ρ)]
  -- the ray lemma
  have ray : ∀ a b : ℤ, b - a = (ρ : ℤ) → (∀ v : ℤ, a ≤ v → v ≤ b → |v| ≤ (n1 : ℤ)) →
      ∃ v : ℤ, a ≤ v ∧ v ≤ b ∧ (fun j : Fin d => if j = i then v else (-1 : ℤ)) ∈ Cinf := by
    intro a b hab hin
    have hreal : Real.log n1 ^ ((5 : ℝ) / 2) ≤ ((b - a : ℤ) : ℝ) := by
      rw [hab]; exact_mod_cast hρle
    exact aux_penultimate_overlap_line_meets_cinf Cinf n0h hhole n1 hn1 (fun _ => (-1 : ℤ)) i a b
      hreal (fun v hv hv' l => by
        by_cases hl : l = i
        · subst hl; simpa using hin v hv hv'
        · simpa [hl] using hn1pos)
  -- the conclusion, from a cube on the ray
  have fin : ∀ v : ℤ, (fun j : Fin d => if j = i then v else (-1 : ℤ)) ∈ Cinf →
      ((1 ≤ v ∧ v ≤ 1 + (ρ : ℤ) ∧ (W : ℤ) ≤ w i) ∨
        (-(ρ : ℤ) - 2 ≤ v ∧ v ≤ -2 ∧ w i ≤ -(W : ℤ))) →
      ∃ z0 ∈ Cinf, ∃ T1 : ℕ, ∀ x ∈ cube d k,
        0 < wave η N (0 : Site d) T1 (x + (k : ℤ) • z0) := by
    intro v hvC hv
    set y : Site d := fun j : Fin d => if j = i then v else (-1 : ℤ) with hy
    refine ⟨y, hvC, τ + k ^ d, ?_⟩
    refine pub_cover_of_line hd0 η hlow0 hhigh N k hN 0 y (hCinf.2.1 hvC) i zl hzlc τ ?_
    intro u hu
    apply hτ
    have hul : ∀ l, l ≠ i → u l = k := fun l hl => by
      have := hu.2 l hl
      simpa [hzl, hl] using this
    have hyl : ∀ l, l ≠ i → y l = -1 := fun l hl => by simp [hy, hl]
    have hyi : y i = v := by simp [hy]
    have hu1 : 1 ≤ u i := hu.1.1
    have hu2 : u i ≤ (k : ℤ) := hu.1.2
    refine pub_mem_br_seg A w hwA h0A i _ ?_ ?_
    · intro l hl
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hul l hl, hyl l hl]
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hyi]
      have hkv : (W : ℤ) = (k : ℤ) * ((ρ : ℤ) + 2) := by rw [hW]; push_cast; ring
      rcases hv with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · left
        constructor
        · nlinarith
        · nlinarith
      · right
        constructor
        · nlinarith
        · nlinarith
  rcases le_abs'.mp hi with hneg | hpos'
  · -- `w i ≤ -W`: the ray runs down
    obtain ⟨v, hva, hvb, hvC⟩ := ray (-(ρ : ℤ) - 2) (-2) (by ring) (fun v hv hv' => by
      rw [abs_of_neg (by omega)]
      omega)
    exact fin v hvC (Or.inr ⟨hva, hvb, hneg⟩)
  · obtain ⟨v, hva, hvb, hvC⟩ := ray 1 (1 + (ρ : ℤ)) (by ring) (fun v hv hv' => by
      rw [abs_of_pos (by omega)]
      omega)
    exact fin v hvC (Or.inl ⟨hva, hvb, hpos'⟩)

end Exploding
