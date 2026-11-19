import Exploding.Support.RenormalizationUnconditional

/-!
# Finiteness of the last wave

The last wave is well-defined almost surely for the toy background law.
-/

open Exploding LatticeProb MeasureTheory

/-- A sufficiently large wave covers a good cube of the infinite cluster. -/
theorem aux_finite_exploding_covers_unconditional (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    :
    ∀ᵐ η ∂(toyLaw d p), ∃ N t k : ℕ, 2 ≤ N ∧ 1 ≤ k ∧ ∃ (Cinf : Set (Site d)) (i : Site d),
      IsInfiniteConnectedGoodSet η k Cinf ∧ i ∈ Cinf ∧
        ∀ x ∈ cube d k, 0 < wave η N (0 : Site d) t (x + (k : ℤ) • i) := by
  obtain ⟨kb, hkb⟩ := Exploding.renormalization_properties_unconditional d hd p hp hp1.le
  set k0 : ℕ := max kb 1 with hk0def
  obtain ⟨c, Cr, hc, hCr, hae⟩ := hkb k0 (le_max_left kb 1)
  obtain ⟨m0, hm0⟩ := aux_finite_exploding_growth d hd
  filter_upwards [hae, aux_finite_exploding_bounds d p hp hp1] with η hη hηbd
  obtain ⟨Cinf, hCinf, ⟨n0, hn0⟩, -, -, -⟩ := hη
  set m := max n0 m0 with hmdef
  obtain ⟨i, hicent, hiCinf⟩ := aux_finite_exploding_meets_cluster d Cinf m
    (fun x hx hnotin => hn0 m (le_max_left _ _) x hx hnotin) (hm0 m (le_max_right _ _))
  set n1 : ℕ := k0 * (m + 2) + 1 with hn1def
  set N : ℕ := (2 * d) ^ (d * n1) with hNdef
  have hd2 : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hηnn : ∀ y : Site d, 0 ≤ η y := fun y => by linarith [(hηbd y).1]
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by linarith
  have hxcent : ∀ x ∈ cube d k0, x + (k0 : ℤ) • i ∈ (cent d n1 : Set (Site d)) := by
    intro x hx j
    have h1 := hx j
    have h2 := hicent j
    simp only [Pi.add_apply]
    have hxj : |x j| ≤ (k0 : ℤ) := by
      rw [abs_of_pos (by linarith [h1.1] : (0 : ℤ) < x j)]; linarith [h1.2]
    have hprod : |(k0 : ℤ) * i j| ≤ (k0 : ℤ) * (m : ℤ) := by
      rw [abs_mul, abs_of_nonneg (by exact_mod_cast Nat.zero_le k0 : (0 : ℤ) ≤ (k0 : ℤ))]
      exact mul_le_mul_of_nonneg_left h2 (by exact_mod_cast Nat.zero_le k0)
    calc |x j + (k0 : ℤ) * i j| ≤ |x j| + |(k0 : ℤ) * i j| := abs_add_le _ _
      _ ≤ (k0 : ℤ) + (k0 : ℤ) * (m : ℤ) := by linarith
      _ ≤ (n1 : ℤ) := by rw [hn1def]; push_cast; nlinarith [Nat.zero_le k0, Nat.zero_le m]
  have hpt : ∀ x ∈ cube d k0, ∃ t : ℕ, 0 < wave η N (0 : Site d) t (x + (k0 : ℤ) • i) :=
    fun x hx => Exploding.square_lower_bound_exponential d hd η hηnn n1 (by omega) N (le_refl N)
      (x + (k0 : ℤ) • i) (hxcent x hx)
  obtain ⟨t, ht⟩ := aux_finite_exploding_uniform_time η hηnn hd0
    N (0 : Site d) (cube d k0) (aux_finite_exploding_cube_finite d k0)
    (fun x => x + (k0 : ℤ) • i) hpt
  refine ⟨N, t, k0, ?_, le_max_right kb 1, Cinf, i, hCinf, hiCinf, ht⟩
  rw [hNdef]
  have hbase : 2 ≤ 2 * d := by omega
  have hexp : 1 ≤ d * n1 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hpos : 0 < 2 * d := by omega
  have h2d : 2 ≤ 2 * d := by omega
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ (2 * d) ^ 1 := by
        rw [pow_one, pow_one]
        exact h2d
    _ ≤ (2 * d) ^ (d * n1) := Nat.pow_le_pow_right hpos hexp

/-- The last wave is well-defined almost surely. -/
theorem Exploding.finite_exploding_unconditional (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    :
    ∀ᵐ η ∂(toyLaw d p), ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d)
:= by
  rcases lt_or_eq_of_le hp1 with hp1 | heq
  ·
    filter_upwards [aux_finite_exploding_covers_unconditional d hd p hp hp1,
      aux_finite_exploding_bounds d p hp hp1] with η hη hbounds
    obtain ⟨N, t0, k, hN, hk, Cinf, i, hCinf, hi, hcover⟩ := hη
    refine ⟨N, Nat.one_le_of_lt hN, ?_⟩
    refine aux_finite_exploding_propagate d hd η
      (fun x => by have := (hbounds x).1; linarith) (fun x => (hbounds x).2) N t0 k hk
      (fun a b hgood hadj s hs => ?_) Cinf i hCinf hi hcover
    obtain ⟨dir, hdir⟩ := hadj
    obtain ⟨dir', hne⟩ : ∃ dir' : Fin d, dir' ≠ dir := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      have hcard : Fintype.card (Fin d) = 1 := Fintype.card_eq_one_iff.mpr ⟨dir, hcon⟩
      rw [Fintype.card_fin] at hcard
      omega
    exact finite_exploding_step hd η (fun x => by have := (hbounds x).1; linarith)
      (fun x => (hbounds x).2) N k hN hk (0 : Site d) a b hgood dir hdir dir' hne s hs
  · subst p
    exact finite_exploding_p1 d hd
