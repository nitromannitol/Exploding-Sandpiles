import Exploding.Support.PlanarWaveOrder
import Exploding.Support.PlanarWaveBarrier
import Exploding.Support.SquareGreenOriginLower
import Exploding.Support.SquareLowerBoundSharp
import Exploding.External.FeyDenBoerRedigCubicalCluster
import Exploding.External.FeyLevinePeresRadius
import LatticeProb.Walk.KilledGreenPlanarLower
import LatticeProb.Walk.KilledGreenDiagonal
import LatticeProb.Sandpile.RadiusConsequences

/-!
# Logarithmic order of the least covering planar wave

On the homogeneous height-two background in dimension two, let `M(n)` be the least positive order
whose wave from the origin reaches every site of the cube `cent 2 n` at some time. The remark after
the sharp square lower bound states that `M(n)` is of order `n² log (n + 1)`.

The upper bound is the sharp square lower bound with `m = ⌈C₀ n² log (n + 1)⌉ + 1`.

For the lower bound, fix an integer `a ≥ A`, where `A` is the Fey-Levine-Peres radius constant,
and put `k = ⌊n / (a + 1)⌋`. The parallel toppling of the pile `2 + k² δ₀` stabilizes (Fey-den Boer
and Redig) and its terminal odometer `v` vanishes off the box of radius `a k` (Fey, Levine and
Peres). The lower origin estimate, the planar logarithmic Green bound and the row-sum bound give
`v(0) ≥ (c₀ / 2) k² log (k + 2)` for large `k`. The site `(n, 0)` of the cube lies outside that box,
so `v` vanishes there, and the covering comparison gives `v(0) < m` for every covering order `m`.
Finitely many small `n` are handled by `M(n) ≥ 1`.

The only hypotheses are the two cited propositions.
-/

open Exploding LatticeProb

namespace Exploding

/-- **Covering orders at large scales.** Assume the two cited propositions. There are `c > 0` and
`n₀ ≥ 1` such that for every `n ≥ n₀`, every order `m` whose wave on the background `2` reaches
each site of `cent 2 n` at some time satisfies `c n² log (n + 1) ≤ m`. -/
theorem planar_wave_cover_order_lower_eventually
    (hFDR : Exploding.External.FeyDenBoerRedigCubicalCluster)
    (hFLP : Exploding.External.FeyLevinePeresRadius) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∀ m : ℕ,
      (∀ x ∈ cent 2 n, ∃ t : ℕ,
        0 < wave (fun _ : Site 2 => (2 : ℤ)) m (0 : Site 2) t x) →
      c * (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1) ≤ (m : ℝ) := by
  have hFDR' : LatticeProb.External.FeyDenBoerRedigCubicalCluster :=
    Exploding.External.FeyDenBoerRedigCubicalCluster_iff.mp hFDR
  have hFLP' : LatticeProb.External.FeyLevinePeresRadius :=
    Exploding.External.FeyLevinePeresRadius_iff.mp hFLP
  -- Constants, all chosen before `n`.
  obtain ⟨A, _, N0, hN0, hFLPspec⟩ := LatticeProb.Sandpile.flp_specialization hFLP' 2 le_rfl
  obtain ⟨c0, hc0, L0, hGL, hgreen⟩ := LatticeProb.planar_killedGreen_zero_zero_log_lower
  obtain ⟨E, hE, hrow⟩ := LatticeProb.GreenTwoSided.killedGreen_row_sum_le_sq (d := 2) le_rfl
  obtain ⟨a, ha1, hAa⟩ : ∃ a : ℕ, 1 ≤ a ∧ A ≤ (a : ℝ) :=
    ⟨Nat.ceil A + 1, Nat.le_add_left 1 _, by push_cast; linarith [Nat.le_ceil A]⟩
  obtain ⟨K0, hK0⟩ := exists_nat_gt (Real.exp (2 * E * ((a : ℝ) + 1) ^ 2 / c0))
  obtain ⟨K, hN0K, hGLK, haK, hK0K⟩ :
      ∃ K : ℕ, N0 ≤ K ∧ L0 ≤ K ∧ a + 1 ≤ K ∧ K0 ≤ K :=
    ⟨N0 + L0 + (a + 1) + K0, by omega, by omega, by omega, by omega⟩
  have hK1 : 1 ≤ K := le_trans hGL hGLK
  refine ⟨c0 / (16 * ((a : ℝ) + 1) ^ 2), div_pos hc0 (by positivity), (a + 1) * K,
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.succ_ne_zero a) (by omega)), ?_⟩
  intro n hn m hcover
  -- The scale `k = ⌊n / (a + 1)⌋` and the remainder `r`.
  have hab : 0 < a + 1 := Nat.succ_pos a
  have hKk : K ≤ n / (a + 1) :=
    (Nat.le_div_iff_mul_le hab).mpr (by rw [Nat.mul_comm]; exact hn)
  have hdm := Nat.div_add_mod n (a + 1)
  have hmod := Nat.mod_lt n hab
  generalize n / (a + 1) = k at hKk hdm
  generalize n % (a + 1) = r at hdm hmod
  have hk1 : 1 ≤ k := le_trans hK1 hKk
  have hN0k : N0 ≤ k ^ 2 := le_trans (le_trans hN0K hKk) (Nat.le_self_pow (by norm_num) k)
  have hN2 : 2 ≤ k ^ 2 := le_trans hN0 hN0k
  have hGLk : L0 ≤ a * k := le_trans (le_trans hGLK hKk) (Nat.le_mul_of_pos_left k ha1)
  have hakn : a * k < n := by linarith
  -- The parallel process of `2 + k² δ₀` stabilizes at a common time `T`.
  obtain ⟨⟨T, hT⟩, -⟩ := LatticeProb.Sandpile.fdbr_parallel_terminal hFDR' 2 le_rfl (k ^ 2) hN2
    (squareOrigin_pile (d := 2) (2 * ((2 : ℕ) : ℤ) - 2) (k ^ 2)) (fun x => rfl)
  have hTe : ∀ t : ℕ, T ≤ t →
      Exploding.podo (squareOrigin_pile (d := 2) (2 * ((2 : ℕ) : ℤ) - 2) (k ^ 2)) t =
        Exploding.podo (squareOrigin_pile (d := 2) (2 * ((2 : ℕ) : ℤ) - 2) (k ^ 2)) T := by
    intro t ht
    simp only [Exploding.podo_eq_sandpile]
    exact hT t ht
  -- Its odometer vanishes off the box of radius `a k`.
  have hroot : ((k ^ 2 : ℕ) : ℝ) ^ (1 / ((2 : ℕ) : ℝ)) = (k : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.sqrt_eq_rpow, Real.sqrt_sq (Nat.cast_nonneg k)]
  have hsupp : ∀ x : Site 2, x ∉ LatticeProb.originBox 2 (a * k) →
      Exploding.podo (squareOrigin_pile (d := 2) (2 * ((2 : ℕ) : ℤ) - 2) (k ^ 2)) T x = 0 := by
    intro x hx
    have hnn :
        0 ≤ Exploding.podo (squareOrigin_pile (d := 2) (2 * ((2 : ℕ) : ℤ) - 2) (k ^ 2)) T x := by
      rw [Exploding.podo_apply_eq_sandpile]
      exact (LatticeProb.Sandpile.podo_isLegal _).nonneg T x
    refine le_antisymm (not_lt.mp fun hpos => ?_) hnn
    rw [Exploding.podo_apply_eq_sandpile] at hpos
    have hbd := hFLPspec (k ^ 2) hN0k x ⟨T, hpos⟩
    obtain ⟨i, hi⟩ := LatticeProb.exists_of_notMem_box hx
    have h1 : |((x i : ℤ) : ℝ)| ≤ ((a * k : ℕ) : ℝ) :=
      calc |((x i : ℤ) : ℝ)| ≤ A * ((k ^ 2 : ℕ) : ℝ) ^ (1 / ((2 : ℕ) : ℝ)) := hbd i
        _ = A * (k : ℝ) := by rw [hroot]
        _ ≤ (a : ℝ) * (k : ℝ) := mul_le_mul_of_nonneg_right hAa (Nat.cast_nonneg k)
        _ = ((a * k : ℕ) : ℝ) := (Nat.cast_mul a k).symm
    have h2 : |x i| ≤ ((a * k : ℕ) : ℤ) := by
      rw [← Int.cast_abs] at h1
      exact_mod_cast h1
    exact absurd hi (not_lt.mpr h2)
  -- Lower origin estimate on the box of radius `a k`.
  have hDbox : ∀ z ∈ LatticeProb.originBox 2 (a * k), z ∈ LatticeProb.box 2 (a * k) := by
    intro z hz
    unfold LatticeProb.originBox at hz
    have hz' := Fintype.mem_piFinset.mp hz
    simp only [LatticeProb.box, Set.mem_setOf_eq]
    intro i
    exact abs_le.mpr (Finset.mem_Icc.mp (hz' i))
  have hG := Exploding.squareOrigin_odometer_ge_green (d := 2) le_rfl (k ^ 2) T
    (LatticeProb.originBox 2 (a * k)) (LatticeProb.zero_mem_originBox (a * k)) hTe hsupp
  have hgr := hgreen (a * k) hGLk
  have hrw := hrow (a * k) (LatticeProb.originBox 2 (a * k)) hDbox 0
  have hNR : ((k ^ 2 : ℕ) : ℝ) = (k : ℝ) ^ 2 := Nat.cast_pow k 2
  have hakR : ((a * k : ℕ) : ℝ) = (a : ℝ) * (k : ℝ) := Nat.cast_mul a k
  rw [hNR] at hG
  rw [hakR] at hgr hrw
  -- Real forms of the scale relations.
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have haKR : (a : ℝ) + 1 ≤ k := by exact_mod_cast le_trans haK hKk
  have hdmR : ((a : ℝ) + 1) * k + r = n := by exact_mod_cast hdm
  have hra : r ≤ a := by omega
  have hrR : (r : ℝ) ≤ a := by exact_mod_cast hra
  -- `log (k + 2) ≤ log (a k + 2)` and `(a k + 1)² ≤ (a + 1)² k²`.
  have hlogak : Real.log ((k : ℝ) + 2) ≤ Real.log ((a : ℝ) * k + 2) := by
    apply Real.log_le_log (by positivity)
    have := mul_le_mul_of_nonneg_right haR (Nat.cast_nonneg (α := ℝ) k)
    linarith
  have hak1 : (a : ℝ) * k + 1 ≤ ((a : ℝ) + 1) * k := by linarith
  have hsq : ((a : ℝ) * k + 1) ^ 2 ≤ ((a : ℝ) + 1) ^ 2 * (k : ℝ) ^ 2 := by
    have := mul_self_le_mul_self (by positivity) hak1
    linarith [this]
  -- The deterministic logarithmic cutoff.
  have hexp : Real.exp (2 * E * ((a : ℝ) + 1) ^ 2 / c0) < (k : ℝ) + 2 := by
    have : (K0 : ℝ) ≤ k := by exact_mod_cast le_trans hK0K hKk
    linarith
  have hcut : 2 * E * ((a : ℝ) + 1) ^ 2 / c0 < Real.log ((k : ℝ) + 2) :=
    (Real.lt_log_iff_exp_lt (by positivity)).mpr hexp
  have hcut' : 2 * E * ((a : ℝ) + 1) ^ 2 < c0 * Real.log ((k : ℝ) + 2) := by
    rw [div_lt_iff₀ hc0] at hcut
    linarith
  -- The terminal origin value is at least `(c₀ / 2) k² log (k + 2)`.
  have hV : c0 / 2 * (k : ℝ) ^ 2 * Real.log ((k : ℝ) + 2) ≤
      ((Exploding.podo (squareOrigin_pile (d := 2) (2 * ((2 : ℕ) : ℤ) - 2) (k ^ 2)) T 0 : ℤ)
        : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left hlogak hc0.le).trans hgr) (sq_nonneg (k : ℝ))
    have h2 := mul_le_mul_of_nonneg_left hcut'.le (sq_nonneg (k : ℝ))
    have h3 := hrw.trans (mul_le_mul_of_nonneg_left hsq hE.le)
    have h5 := le_trans (sub_le_sub_right h1 _) hG
    have h6 := le_trans h3 (show E * (((a : ℝ) + 1) ^ 2 * (k : ℝ) ^ 2) ≤
      c0 / 2 * (k : ℝ) ^ 2 * Real.log ((k : ℝ) + 2) by linarith [h2])
    calc c0 / 2 * (k : ℝ) ^ 2 * Real.log ((k : ℝ) + 2)
        = (k : ℝ) ^ 2 * (c0 * Real.log ((k : ℝ) + 2)) -
            c0 / 2 * (k : ℝ) ^ 2 * Real.log ((k : ℝ) + 2) := by ring
      _ ≤ (k : ℝ) ^ 2 * (c0 * Real.log ((k : ℝ) + 2)) - _ := sub_le_sub_left h6 _
      _ ≤ _ := h5
  -- The covering comparison: the site `(n, 0)` of the cube lies outside the box.
  have hpile : squareOrigin_pile (d := 2) (2 * ((2 : ℕ) : ℤ) - 2) (k ^ 2) =
      squareOrigin_pile (d := 2) 2 (k ^ 2) := by
    rw [show (2 * ((2 : ℕ) : ℤ) - 2) = 2 by norm_num]
  have hlt : Exploding.podo (squareOrigin_pile (d := 2) (2 * ((2 : ℕ) : ℤ) - 2) (k ^ 2)) T 0
      < (m : ℤ) := by
    rw [hpile]
    refine Exploding.planar_wave_covering_order_gt_parallel_origin (k ^ 2) T n m ?_ hcover ?_
    · rw [← hpile]
      exact hTe
    · refine ⟨![(n : ℤ), 0], ?_, ?_⟩
      · show ∀ i, |(![(n : ℤ), 0] : Site 2) i| ≤ (n : ℤ)
        intro i
        fin_cases i <;> simp
      · rw [← hpile]
        apply hsupp
        apply LatticeProb.notMem_originBox_of_lt (i := 0)
        show ((a * k : ℕ) : ℤ) < (n : ℤ)
        exact_mod_cast hakn
  have hltR :
      ((Exploding.podo (squareOrigin_pile (d := 2) (2 * ((2 : ℕ) : ℤ) - 2) (k ^ 2)) T 0 : ℤ)
        : ℝ) < (m : ℝ) := by
    exact_mod_cast hlt
  -- From `k` back to `n`.
  have hn2 : (n : ℝ) ≤ 2 * ((a : ℝ) + 1) * k := by
    have := mul_le_mul_of_nonneg_left hkR (by positivity : (0 : ℝ) ≤ (a : ℝ) + 1)
    linarith
  have hn1 : (n : ℝ) + 1 ≤ ((k : ℝ) + 2) ^ 2 := by
    have := mul_le_mul_of_nonneg_right haKR (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)
    linarith
  have hlogn : Real.log ((n : ℝ) + 1) ≤ 2 * Real.log ((k : ℝ) + 2) := by
    calc Real.log ((n : ℝ) + 1) ≤ Real.log (((k : ℝ) + 2) ^ 2) :=
          Real.log_le_log (by positivity) hn1
      _ = 2 * Real.log ((k : ℝ) + 2) := by rw [Real.log_pow]; norm_num
  have hlogn0 : 0 ≤ Real.log ((n : ℝ) + 1) := by
    apply Real.log_nonneg
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hnsq : (n : ℝ) ^ 2 ≤ 4 * ((a : ℝ) + 1) ^ 2 * (k : ℝ) ^ 2 := by
    have := mul_self_le_mul_self (Nat.cast_nonneg (α := ℝ) n) hn2
    linarith [this]
  have hprod : (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1) ≤
      (4 * ((a : ℝ) + 1) ^ 2 * (k : ℝ) ^ 2) * (2 * Real.log ((k : ℝ) + 2)) :=
    mul_le_mul hnsq hlogn hlogn0 (by positivity)
  have hc16 : c0 / (16 * ((a : ℝ) + 1) ^ 2) * (16 * ((a : ℝ) + 1) ^ 2) = c0 :=
    div_mul_cancel₀ c0 (by positivity)
  calc c0 / (16 * ((a : ℝ) + 1) ^ 2) * (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1)
      = c0 / (16 * ((a : ℝ) + 1) ^ 2) * ((n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1)) := by ring
    _ ≤ c0 / (16 * ((a : ℝ) + 1) ^ 2) *
          ((4 * ((a : ℝ) + 1) ^ 2 * (k : ℝ) ^ 2) * (2 * Real.log ((k : ℝ) + 2))) :=
        mul_le_mul_of_nonneg_left hprod (div_pos hc0 (by positivity)).le
    _ = (c0 / (16 * ((a : ℝ) + 1) ^ 2) * (16 * ((a : ℝ) + 1) ^ 2)) *
          ((k : ℝ) ^ 2 * Real.log ((k : ℝ) + 2) / 2) := by ring
    _ = c0 / 2 * (k : ℝ) ^ 2 * Real.log ((k : ℝ) + 2) := by rw [hc16]; ring
    _ ≤ _ := hV
    _ ≤ (m : ℝ) := hltR.le

/-- **Covering orders from above.** Assume the two cited propositions. There is `C > 0` such that
for every `n ≥ 1` some positive order `m ≤ C n² log (n + 1)` has a wave on the background `2`
reaching each site of `cent 2 n` at some time. -/
theorem planar_wave_cover_order_upper
    (hFDR : Exploding.External.FeyDenBoerRedigCubicalCluster)
    (hFLP : Exploding.External.FeyLevinePeresRadius) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 1 ≤ m ∧
      (∀ x ∈ cent 2 n, ∃ t : ℕ,
        0 < wave (fun _ : Site 2 => (2 : ℤ)) m (0 : Site 2) t x) ∧
      (m : ℝ) ≤ C * (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1) := by
  obtain ⟨C0, hC0, hsharp⟩ := Exploding.square_lower_bound_sharp 2 le_rfl
    (Exploding.External.FeyDenBoerRedigCubicalCluster_iff.mp hFDR)
    (Exploding.External.FeyLevinePeresRadius_iff.mp hFLP)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C0 + 2 / Real.log 2, by positivity, fun n hn => ?_⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : Real.log 2 ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by norm_num) (by linarith)
  have hF : Real.log 2 ≤ (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1) := by
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hnR
    calc Real.log 2 = 1 * Real.log 2 := (one_mul _).symm
      _ ≤ (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1) := mul_le_mul h2 hlogn hlog2.le (by positivity)
  have hF0 : 0 ≤ C0 * (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1) := by
    have : 0 ≤ Real.log ((n : ℝ) + 1) := le_trans hlog2.le hlogn
    positivity
  refine ⟨Nat.ceil (C0 * (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1)) + 1, Nat.le_add_left 1 _, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := hsharp (fun _ : Site 2 => (2 : ℤ)) (fun _ => ⟨by norm_num, by norm_num⟩)
      n hn (Nat.ceil (C0 * (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1)) + 1) (Nat.le_add_left 1 _)
      (by rw [if_pos rfl]; exact Nat.le_succ _)
    exact fun x hx => ⟨T, hT T le_rfl x hx⟩
  · have hceil := Nat.ceil_lt_add_one hF0
    have h2 : 2 ≤ 2 / Real.log 2 * ((n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      linarith
    push_cast
    linarith [hceil, h2]

/-- **Order of the least covering planar wave.** Assume the two cited propositions. There are
constants `c, C > 0` such that for every `n ≥ 1` the least positive order `M` whose wave from the
origin on the background `2` reaches each site of `cent 2 n` at some time satisfies
`c n² log (n + 1) ≤ M ≤ C n² log (n + 1)`. -/
theorem planar_wave_order_bounds
    (hFDR : Exploding.External.FeyDenBoerRedigCubicalCluster)
    (hFLP : Exploding.External.FeyLevinePeresRadius) :
    ∃ c C : Real, 0 < c ∧ 0 < C ∧
      ∀ n : Nat, 1 ≤ n → ∃ M : Nat,
        1 ≤ M ∧
        (∀ x ∈ cent 2 n, ∃ t : Nat,
          0 < wave (fun _ : Site 2 => (2 : Int)) M (0 : Site 2) t x) ∧
        (∀ m : Nat, 1 ≤ m →
          (∀ x ∈ cent 2 n, ∃ t : Nat,
            0 < wave (fun _ : Site 2 => (2 : Int)) m (0 : Site 2) t x) → M ≤ m) ∧
        c * (n : Real)^2 * Real.log ((n : Real) + 1) ≤ (M : Real) ∧
        (M : Real) ≤ C * (n : Real)^2 * Real.log ((n : Real) + 1) := by
  obtain ⟨c1, hc1, n0, hn0, hlow⟩ := planar_wave_cover_order_lower_eventually hFDR hFLP
  obtain ⟨C, hC, hup⟩ := planar_wave_cover_order_upper hFDR hFLP
  -- Small scales `n < n₀`: there `n² log (n + 1) ≤ n₀² log (n₀ + 1)` and `M ≥ 1`.
  have hn0R : (1 : ℝ) ≤ n0 := by exact_mod_cast hn0
  have hF0 : 0 < (n0 : ℝ) ^ 2 * Real.log ((n0 : ℝ) + 1) := by
    have : 0 < Real.log ((n0 : ℝ) + 1) := Real.log_pos (by linarith)
    positivity
  obtain ⟨c2, hc2, hc2F⟩ : ∃ c2 : ℝ, 0 < c2 ∧
      c2 * ((n0 : ℝ) ^ 2 * Real.log ((n0 : ℝ) + 1)) = 1 :=
    ⟨1 / ((n0 : ℝ) ^ 2 * Real.log ((n0 : ℝ) + 1)), by positivity, one_div_mul_cancel hF0.ne'⟩
  refine ⟨min c1 c2, C, lt_min hc1 hc2, hC, fun n hn => ?_⟩
  obtain ⟨M, ⟨hM1, hMcov, hMmin⟩, -⟩ := planar_wave_least_order_exists_unique n hn
  obtain ⟨m, hm1, hmcov, hmC⟩ := hup n hn
  have hMm : (M : ℝ) ≤ m := by exact_mod_cast hMmin m hm1 hmcov
  refine ⟨M, hM1, hMcov, hMmin, ?_, hMm.trans hmC⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn0 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hFn : 0 ≤ (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1) := by positivity
  rcases le_or_gt n0 n with h | h
  · calc min c1 c2 * (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1)
        = min c1 c2 * ((n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1)) := by ring
      _ ≤ c1 * ((n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right (min_le_left c1 c2) hFn
      _ = c1 * (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1) := by ring
      _ ≤ (M : ℝ) := hlow n h M hMcov
  · have hnn0 : (n : ℝ) ≤ n0 := by exact_mod_cast h.le
    have hmono : (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1) ≤
        (n0 : ℝ) ^ 2 * Real.log ((n0 : ℝ) + 1) :=
      mul_le_mul (pow_le_pow_left₀ (by linarith) hnn0 2)
        (Real.log_le_log (by linarith) (by linarith)) hlogn0 (by positivity)
    have hM1R : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    calc min c1 c2 * (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1)
        = min c1 c2 * ((n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1)) := by ring
      _ ≤ c2 * ((n0 : ℝ) ^ 2 * Real.log ((n0 : ℝ) + 1)) :=
          mul_le_mul (min_le_right c1 c2) hmono hFn hc2.le
      _ = 1 := hc2F
      _ ≤ (M : ℝ) := hM1R

end Exploding
