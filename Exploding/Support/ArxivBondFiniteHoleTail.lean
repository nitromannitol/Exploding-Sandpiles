import Exploding.Support.ArxivBondFiniteHoleSeries
import Exploding.Support.ArxivBondHoleGeometricTerm

/-!
# Exponential tail of the finite-hole event

For `d ≥ 2` the installed finite-hole series bound and the geometric term bound combine into
a tail `C · exp(-c √s)`, uniform over a density window `[q0, 1]` with `q0 < 1`. The constants
`K`, `q0`, `C`, `c` are fixed before the root `z`, the threshold `s`, and the density `q`. The
event is the actual open-bond finite-hole event with an existential cluster root `i`.

The proof sets `L = ⌈√s⌉₊`. Then `s ≤ m²` implies `L ≤ m`, the series is dominated by a
geometric series with ratio `1/2`, and `(1/2)^L ≤ exp(-log 2 · √s)`. The natural floor `m / 3^d`
and the case `m < 3^d` are handled inside the geometric term bound. The case `b = 0`, that is
`q = 1`, needs no separate argument.

This is a support estimate for the finite-hole event. It does not identify the infinite
cluster, transfer the event to a paper's cluster, or take a union over a box.
-/

open LatticeProb MeasureTheory

namespace Exploding

/-- The ceiling of `√s` is at most `m` whenever `s ≤ m²`. -/
private theorem ceil_sqrt_le_of_sq_le (s m : ℕ) (h : s ≤ m ^ 2) :
    ⌈Real.sqrt (s : ℝ)⌉₊ ≤ m := by
  rw [Nat.ceil_le, Real.sqrt_le_left (Nat.cast_nonneg m)]
  exact_mod_cast h

/-- The window `1 / (2 d N^(3^d))` is positive when `N ≥ 1`. -/
private theorem density_window_pos (d N : ℕ) (hd : 2 ≤ d) (hN : 0 < N) :
    0 < 1 / (2 * (d : ℝ) * (N : ℝ) ^ (3 ^ d)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  exact div_pos one_pos (mul_pos (mul_pos two_pos hd0) (pow_pos hN0 _))

/-- The window `1 / (2 d N^(3^d))` is at most `1` when `d ≥ 2` and `N ≥ 1`. -/
private theorem density_window_le_one (d N : ℕ) (hd : 2 ≤ d) (hN : 0 < N) :
    1 / (2 * (d : ℝ) * (N : ℝ) ^ (3 ^ d)) ≤ 1 := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hpow : (1 : ℝ) ≤ (N : ℝ) ^ (3 ^ d) := one_le_pow₀ hN1
  have h2 : (1 : ℝ) ≤ 2 * (d : ℝ) * (N : ℝ) ^ (3 ^ d) := by nlinarith
  have hpos : (0 : ℝ) < 2 * (d : ℝ) * (N : ℝ) ^ (3 ^ d) := by linarith
  exact (div_le_one hpos).mpr h2

/-- On the window `q ≥ 1 - 1 / (2 d N^(3^d))`, the density condition `N^(3^d) · b ≤ 1` holds
for `b = ofReal (2 d (1 - q))`. -/
private theorem density_condition (d N : ℕ) (hd : 2 ≤ d) (hN : 0 < N) (q : ℝ)
    (hq : 1 - 1 / (2 * (d : ℝ) * (N : ℝ) ^ (3 ^ d)) ≤ q) :
    (N : ENNReal) ^ (3 ^ d) * ENNReal.ofReal (2 * (d : ℝ) * (1 - q)) ≤ 1 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hAD : (0 : ℝ) < (N : ℝ) ^ (3 ^ d) := pow_pos hN0 _
  have hX : (0 : ℝ) < 2 * (d : ℝ) * (N : ℝ) ^ (3 ^ d) := mul_pos (mul_pos two_pos hd0) hAD
  have hreal : (N : ℝ) ^ (3 ^ d) * (2 * (d : ℝ) * (1 - q)) ≤ 1 := by
    have h1 : 1 - q ≤ 1 / (2 * (d : ℝ) * (N : ℝ) ^ (3 ^ d)) := by linarith
    calc (N : ℝ) ^ (3 ^ d) * (2 * (d : ℝ) * (1 - q))
        ≤ (N : ℝ) ^ (3 ^ d) * (2 * (d : ℝ) * (1 / (2 * (d : ℝ) * (N : ℝ) ^ (3 ^ d)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by positivity)) hAD.le
      _ = 2 * (d : ℝ) * (N : ℝ) ^ (3 ^ d) * (1 / (2 * (d : ℝ) * (N : ℝ) ^ (3 ^ d))) := by
          ring
      _ = 1 := mul_one_div_cancel hX.ne'
  have heq : (N : ENNReal) ^ (3 ^ d) * ENNReal.ofReal (2 * (d : ℝ) * (1 - q)) =
      ENNReal.ofReal ((N : ℝ) ^ (3 ^ d) * (2 * (d : ℝ) * (1 - q))) := by
    rw [ENNReal.ofReal_mul (pow_nonneg hN0.le (3 ^ d)), ENNReal.ofReal_pow hN0.le,
      ENNReal.ofReal_natCast]
  rw [heq]
  exact ENNReal.ofReal_le_one.mpr hreal

/-- Summing `a · (1/2)^m` over the indices `m ≥ L` gives `a · ((1/2)^L · 2)` in `ℝ≥0∞`. -/
private theorem tsum_ite_geometric_half (L : ℕ) (a : ENNReal) :
    ∑' m : ℕ, (if L ≤ m then a * (1 / 2 : ENNReal) ^ m else 0) =
      a * ((1 / 2 : ENNReal) ^ L * 2) := by
  have hfac : ∀ m : ℕ, (if L ≤ m then a * (1 / 2 : ENNReal) ^ m else 0) =
      a * (if L ≤ m then (1 / 2 : ENNReal) ^ m else 0) := by
    intro m
    by_cases h : L ≤ m <;> simp [h]
  have hsupp : Function.support (fun m : ℕ => if L ≤ m then (1 / 2 : ENNReal) ^ m else 0) ⊆
      Set.range (fun c : ℕ => c + L) := by
    intro m hm
    rw [Function.mem_support] at hm
    by_cases h : L ≤ m
    · exact ⟨m - L, Nat.sub_add_cancel h⟩
    · exact absurd (if_neg h) hm
  have hshift : ∑' m : ℕ, (if L ≤ m then (1 / 2 : ENNReal) ^ m else 0) =
      (1 / 2 : ENNReal) ^ L * 2 := by
    rw [← (add_left_injective L).tsum_eq hsupp]
    calc ∑' c : ℕ, (if L ≤ c + L then (1 / 2 : ENNReal) ^ (c + L) else 0)
        = ∑' c : ℕ, (1 / 2 : ENNReal) ^ c * (1 / 2 : ENNReal) ^ L :=
          tsum_congr fun c => by
            rw [if_pos (Nat.le_add_left L c), pow_add]
      _ = (∑' c : ℕ, (1 / 2 : ENNReal) ^ c) * (1 / 2 : ENNReal) ^ L :=
          ENNReal.tsum_mul_right
      _ = (1 / 2 : ENNReal) ^ L * 2 := by
          rw [ENNReal.tsum_geometric, one_div, ENNReal.one_sub_inv_two, inv_inv, mul_comm]
  rw [tsum_congr hfac, ENNReal.tsum_mul_left, hshift]

/-- `ofReal (1/2) = 1/2` in `ℝ≥0∞`. -/
private theorem ennreal_ofReal_half : ENNReal.ofReal (1 / 2 : ℝ) = 1 / 2 := by
  rw [one_div, one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]

/-- Bridge from the ENNReal geometric factor to a real exponential bound: if `(1/2)^L ≤ x`,
then `N^k · (1/2)^L · 2 ≤ ofReal (2 N^k x)`. -/
private theorem ennreal_geometric_le_ofReal (N k L : ℕ) (x : ℝ)
    (hx : (1 / 2 : ℝ) ^ L ≤ x) :
    (N : ENNReal) ^ k * ((1 / 2 : ENNReal) ^ L * 2) ≤
      ENNReal.ofReal (2 * (N : ℝ) ^ k * x) := by
  have hhalf0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ L := pow_nonneg (by norm_num) L
  have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ k := pow_nonneg (Nat.cast_nonneg N) k
  have hpow : (1 / 2 : ENNReal) ^ L = ENNReal.ofReal ((1 / 2 : ℝ) ^ L) := by
    rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2), ennreal_ofReal_half]
  calc (N : ENNReal) ^ k * ((1 / 2 : ENNReal) ^ L * 2)
      = ENNReal.ofReal ((N : ℝ) ^ k) * (ENNReal.ofReal ((1 / 2 : ℝ) ^ L) * ENNReal.ofReal 2) := by
        rw [hpow, ENNReal.ofReal_ofNat, ENNReal.ofReal_pow (Nat.cast_nonneg N),
          ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal ((N : ℝ) ^ k * ((1 / 2 : ℝ) ^ L * 2)) := by
        rw [ENNReal.ofReal_mul hN0, ENNReal.ofReal_mul hhalf0]
    _ ≤ ENNReal.ofReal (2 * (N : ℝ) ^ k * x) := by
        apply ENNReal.ofReal_le_ofReal
        calc (N : ℝ) ^ k * ((1 / 2 : ℝ) ^ L * 2) = 2 * (N : ℝ) ^ k * (1 / 2 : ℝ) ^ L := by
              ring
          _ ≤ 2 * (N : ℝ) ^ k * x := mul_le_mul_of_nonneg_left hx (by positivity)

/-- With `L = ⌈√s⌉₊`, the real factor `(1/2)^L` is at most `exp(-log 2 · √s)`, since
`√s ≤ L` and `log 2 > 0`. -/
private theorem half_pow_ceil_sqrt_le_exp (s : ℕ) :
    (1 / 2 : ℝ) ^ ⌈Real.sqrt (s : ℝ)⌉₊ ≤ Real.exp (-Real.log 2 * Real.sqrt (s : ℝ)) := by
  have hexp2 : Real.exp (-Real.log 2) = 2⁻¹ := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hpow : (1 / 2 : ℝ) ^ ⌈Real.sqrt (s : ℝ)⌉₊ =
      Real.exp (-Real.log 2 * (⌈Real.sqrt (s : ℝ)⌉₊ : ℝ)) := by
    rw [one_div, ← hexp2, ← Real.exp_nat_mul]
    congr 1
    ring
  have hL : Real.sqrt (s : ℝ) ≤ (⌈Real.sqrt (s : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmul : Real.log 2 * Real.sqrt (s : ℝ) ≤ Real.log 2 * (⌈Real.sqrt (s : ℝ)⌉₊ : ℝ) :=
    mul_le_mul_of_nonneg_left hL hlog.le
  rw [hpow]
  apply Real.exp_le_exp.mpr
  linarith

/-- For `d ≥ 2` there are fixed constants `K ≥ 1`, `q0 < 1`, `C > 0`, `c > 0` such that, for
every root `z`, threshold `s`, and density `q ∈ [q0, 1]`, the finite-hole event with an
existential cluster root `i` has probability at most `C · exp(-c √s)`. -/
theorem arxiv_bond_finite_hole_tail_exp (d : ℕ) (hd : 2 ≤ d) :
    ∃ (K : ℕ) (q0 C c : ℝ), 1 ≤ K ∧ 0 ≤ q0 ∧ q0 < 1 ∧ 0 < C ∧ 0 < c ∧
      ∀ (z : Site d) (s : ℕ) {q : ℝ}, q0 ≤ q → q ≤ 1 →
        bondPercolation d q
          {ζ | ∃ i : Site d,
            z ∉ {y : Site d | (openBondGraph ζ).Reachable i y} ∧
            (componentIn
              ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z).Finite ∧
            s ≤ (componentIn
              ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z).ncard} ≤
        ENNReal.ofReal (C * Real.exp (-c * Real.sqrt (s : ℝ))) := by
  obtain ⟨K, hK, hfin⟩ := arxiv_bond_finite_hole_volume_prob_le_tsum d hd
  have hN : 0 < 2 * 3 ^ d * K := Nat.mul_pos (by positivity) (by omega)
  have hNR : (0 : ℝ) < ((2 * 3 ^ d * K : ℕ) : ℝ) := Nat.cast_pos.mpr hN
  have hq0 : 0 ≤ 1 - 1 / (2 * (d : ℝ) * ((2 * 3 ^ d * K : ℕ) : ℝ) ^ (3 ^ d)) :=
    sub_nonneg.mpr (density_window_le_one d _ hd hN)
  refine ⟨K, 1 - 1 / (2 * (d : ℝ) * ((2 * 3 ^ d * K : ℕ) : ℝ) ^ (3 ^ d)),
    2 * ((2 * 3 ^ d * K : ℕ) : ℝ) ^ (3 ^ d - 1), Real.log 2, hK, hq0, ?_, ?_, ?_, ?_⟩
  · linarith [density_window_pos d _ hd hN]
  · exact mul_pos two_pos (pow_pos hNR _)
  · exact Real.log_pos (by norm_num)
  · intro z s q hq0' hq1
    have hq : 0 ≤ q := hq0.trans hq0'
    have hterm : ∀ m : ℕ,
        (if s ≤ m ^ 2 then (((2 * m + 1) ^ d : ℕ) : ENNReal) * (K : ENNReal) ^ m *
          (ENNReal.ofReal (2 * (d : ℝ) * (1 - q))) ^ (m / 3 ^ d) else 0) ≤
        (if ⌈Real.sqrt (s : ℝ)⌉₊ ≤ m then
          ((2 * 3 ^ d * K : ℕ) : ENNReal) ^ (3 ^ d - 1) * (1 / 2 : ENNReal) ^ m else 0) := by
      intro m
      by_cases hm : s ≤ m ^ 2
      · rw [if_pos hm, if_pos (ceil_sqrt_le_of_sq_le s m hm)]
        exact arxiv_bond_hole_term_le_geometric d K hK _
          (density_condition d _ hd hN q hq0') m
      · rw [if_neg hm]
        exact zero_le
    refine (hfin z s hq hq1).trans ((ENNReal.tsum_le_tsum hterm).trans ?_)
    rw [tsum_ite_geometric_half]
    exact ennreal_geometric_le_ofReal _ _ _ _ (half_pow_ceil_sqrt_le_exp s)

end Exploding
