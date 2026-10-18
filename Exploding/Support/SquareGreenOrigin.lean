/-
Finite-domain origin estimate for the ordinary parallel odometer of the pile `h + N δ₀`.

For a finite domain `D ∋ 0` containing the support of the odometer at time `T`, the origin
value obeys
  `u_T(0) ≤ N g_D(0,0) + h ∑_{y∈D} g_D(0,y)`,
where `g_D = LatticeProb.Graph.killedGreenReal (lattice d) D` is the killed Green function
of `ℤ^d` in the library normalization (expected visits divided by `2d`).

The argument is chip conservation for the ordinary pile, the library characterization of the
killed Green function (`LatticeProb.Network.laplacian_killedGreenReal`), and summation by parts
on the finite set `D`, the unit-conductance case `LatticeProb.Network.sum_mul_laplacian_comm`.
Nonnegativity of the ordinary sandpile is `Exploding.sqw_pconf_nonneg`, imported from
`Exploding.Support.SquareWaveComparison`.  The support of the odometer on `D` is a premise of the
estimate; no radius theorem is used.
-/
import Exploding.Support.SquareWaveComparison
import Exploding.Support.Toppling
import LatticeProb.Graph.Zd
import LatticeProb.Network.KilledGreen
import LatticeProb.Network.LaplacianSymmetry

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-! ### The pile `h + N δ₀` and its nonnegativity -/

/-- The ordinary pile `h + N δ₀`: a constant background `h` with `N` extra chips at the origin. -/
def squareOrigin_pile (h : ℤ) (N : ℕ) : Site d → ℤ :=
  fun y => h + (N : ℤ) * dirac (0 : Site d) y

/-- The pile is nonnegative when the background is. -/
theorem squareOrigin_pile_nonneg (h : ℤ) (hh : 0 ≤ h) (N : ℕ) (x : Site d) :
    0 ≤ squareOrigin_pile h N x := by
  have hdir : 0 ≤ dirac (0 : Site d) x := by
    unfold dirac
    split_ifs <;> norm_num
  have hN : (0 : ℤ) ≤ (N : ℤ) := by positivity
  have := mul_nonneg hN hdir
  simp only [squareOrigin_pile]
  linarith

/-- The pile in `ℝ`: the background plus `N` at the origin. -/
theorem squareOrigin_pile_real (h : ℤ) (N : ℕ) (v : Site d) :
    ((squareOrigin_pile h N v : ℤ) : ℝ) = (h : ℝ) + (N : ℝ) * (if v = 0 then 1 else 0) := by
  simp only [squareOrigin_pile, dirac]
  split_ifs <;> simp

/-! ### The integer lattice Laplacian is the library Laplacian -/

/-- The integer lattice Laplacian `lap u`, cast to `ℝ`, is the library graph Laplacian of
`lattice d` applied to the cast function. -/
theorem squareOrigin_lap_cast (hd : 0 < d) (u : Site d → ℤ) (x : Site d) :
    ((lap u x : ℤ) : ℝ) = LatticeProb.Graph.laplacian (lattice d) (fun y => (u y : ℝ)) x := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hne : (2 * (d : ℝ)) ≠ 0 := mul_ne_zero two_ne_zero hdR.ne'
  have hw := LatticeProb.Graph.Zd.walkOp_eq (fun y => (u y : ℝ)) x
  unfold LatticeProb.Graph.walkOp LatticeProb.walkOp at hw
  rw [LatticeProb.Graph.Zd.degree_eq] at hw
  push_cast at hw
  have hsum : ∑ y ∈ (lattice d).neighborFinset x, (u y : ℝ)
      = LatticeProb.nbrSum (fun y => (u y : ℝ)) x :=
    (div_left_inj' hne).mp hw
  simp only [LatticeProb.Graph.laplacian]
  rw [Finset.sum_sub_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
    LatticeProb.Graph.Zd.degree_eq, nsmul_eq_mul, hsum]
  simp only [lap, nbrSumZ, LatticeProb.nbrSum]
  push_cast
  ring

/-! ### Chip conservation with the killed Green function -/

/-- Chip conservation for any pile `s₀` whose odometer at time `T` vanishes off a finite
`D ∋ 0`: the origin value is `u_T(0) = ∑_{v∈D} g_D(0,v) (s₀(v) - s_T(v))`. -/
theorem squareOrigin_origin_identity (hd : 0 < d) (D : Finset (Site d)) (hO : (0 : Site d) ∈ D)
    (s0 : Site d → ℤ) (T : ℕ) (hsupp : ∀ x, x ∉ D → podo s0 T x = 0) :
    ((podo s0 T 0 : ℤ) : ℝ)
      = ∑ v ∈ D, LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0 v
          * (((s0 v : ℤ) : ℝ) - ((pconf s0 T v : ℤ) : ℝ)) := by
  haveI : NeZero d := ⟨hd.ne'⟩
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset D
  have hG : (lattice d).Connected := LatticeProb.Graph.Zd.latticeConnected d
  -- the killed Green function vanishes off `D`, and its Laplacian is `-δ₀` on `D`
  have hgoff : ∀ v, v ∉ D →
      LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0 v = 0 :=
    fun v hv => LatticeProb.Network.killedGreenReal_eq_zero_of_not_mem hG D hq hv 0
  have hgcomp : ∀ v, v ∈ D → LatticeProb.Graph.laplacian (lattice d)
      (LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0) v
        = -(if v = 0 then (1 : ℝ) else 0) :=
    fun v hv => by
      convert LatticeProb.Network.laplacian_killedGreenReal hG D hO hq (Finset.mem_coe.mpr hv)
  have hu_off : ∀ v, v ∉ D → ((podo s0 T v : ℤ) : ℝ) = 0 := fun v hv => by
    simp [hsupp v hv]
  -- the odometer's graph Laplacian is the sandpile defect `s_T - s₀`
  have hlapR : ∀ v, LatticeProb.Graph.laplacian (lattice d)
      (fun y => ((podo s0 T y : ℤ) : ℝ)) v
        = ((pconf s0 T v : ℤ) : ℝ) - ((s0 v : ℤ) : ℝ) := by
    intro v
    rw [← squareOrigin_lap_cast hd (podo s0 T) v]
    have hdef : pconf s0 T v = s0 v + lap (podo s0 T) v := rfl
    rw [hdef]
    push_cast
    ring
  have hsbp : ∑ v ∈ D, ((podo s0 T v : ℤ) : ℝ) * LatticeProb.Graph.laplacian (lattice d)
        (LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0) v
      = ∑ v ∈ D, LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0 v
          * LatticeProb.Graph.laplacian (lattice d) (fun y => ((podo s0 T y : ℤ) : ℝ)) v :=
    LatticeProb.Network.sum_mul_laplacian_comm (lattice d) D (fun y => ((podo s0 T y : ℤ) : ℝ))
      (LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0) hu_off hgoff
  have hLHS1 : ∑ v ∈ D, ((podo s0 T v : ℤ) : ℝ) * LatticeProb.Graph.laplacian (lattice d)
        (LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0) v
      = ∑ v ∈ D, ((podo s0 T v : ℤ) : ℝ) * (-(if v = 0 then (1 : ℝ) else 0)) :=
    Finset.sum_congr rfl fun v hv => by rw [hgcomp v hv]
  have hLHS2 : ∑ v ∈ D, ((podo s0 T v : ℤ) : ℝ) * (-(if v = 0 then (1 : ℝ) else 0))
      = -((podo s0 T 0 : ℤ) : ℝ) := by
    simp [mul_neg, mul_ite, Finset.sum_neg_distrib, Finset.sum_ite_eq', hO]
  have hRHS : ∑ v ∈ D, LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0 v
          * LatticeProb.Graph.laplacian (lattice d) (fun y => ((podo s0 T y : ℤ) : ℝ)) v
      = ∑ v ∈ D, LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0 v
          * (((pconf s0 T v : ℤ) : ℝ) - ((s0 v : ℤ) : ℝ)) :=
    Finset.sum_congr rfl fun v _ => by rw [hlapR v]
  have hfin : ∑ v ∈ D, LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0 v
          * (((s0 v : ℤ) : ℝ) - ((pconf s0 T v : ℤ) : ℝ))
      = -∑ v ∈ D, LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0 v
          * (((pconf s0 T v : ℤ) : ℝ) - ((s0 v : ℤ) : ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  linarith

/-! ### The origin bound for the ordinary pile `h + N δ₀` -/

/-- **Origin bound.**  Let `h ≥ 0`, let `D ∋ 0` be finite and contain the support of the
ordinary odometer of `h + N δ₀` at time `T`.  Then the origin value satisfies
`u_T(0) ≤ N g_D(0,0) + h ∑_{y∈D} g_D(0,y)`, with `g_D` the killed Green function of
`lattice d`. -/
theorem squareOrigin_odometer_le_green (hd : 0 < d) (h : ℤ) (hh : 0 ≤ h) (N T : ℕ)
    (D : Finset (Site d)) (hO : (0 : Site d) ∈ D)
    (hsupp : ∀ x, x ∉ D → podo (squareOrigin_pile h N) T x = 0) :
    ((podo (squareOrigin_pile (d := d) h N) T 0 : ℤ) : ℝ)
      ≤ (N : ℝ) * LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0 0
        + (h : ℝ) * ∑ y ∈ D, LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0 y := by
  haveI : NeZero d := ⟨hd.ne'⟩
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset D
  have hG : (lattice d).Connected := LatticeProb.Graph.Zd.latticeConnected d
  have hid := squareOrigin_origin_identity hd D hO (squareOrigin_pile h N) T hsupp
  have hgnn : ∀ v, 0 ≤ LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0 v :=
    fun v => LatticeProb.Network.killedGreenReal_nonneg hG D hq 0 v
  have hpc := sqw_pconf_nonneg (squareOrigin_pile (d := d) h N)
    (fun x => squareOrigin_pile_nonneg h hh N x) T
  -- pointwise: `g(v)(s₀(v) - s_T(v)) ≤ h g(v) + N g(0)·1{v=0}`, using `s_T(v) ≥ 0`
  have hpt : ∀ v ∈ D,
      LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0 v
        * (((squareOrigin_pile h N v : ℤ) : ℝ) - ((pconf (squareOrigin_pile h N) T v : ℤ) : ℝ))
      ≤ (h : ℝ) * LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0 v
        + (N : ℝ) * (if v = 0 then
            LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0 v else 0) := by
    intro v _
    have hp : 0 ≤ LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0 v
        * ((pconf (squareOrigin_pile h N) T v : ℤ) : ℝ) :=
      mul_nonneg (hgnn v) (by exact_mod_cast hpc v)
    rw [squareOrigin_pile_real h N v]
    by_cases hv : v = 0
    · rw [if_pos hv, if_pos hv]
      nlinarith [hp]
    · rw [if_neg hv, if_neg hv]
      nlinarith [hp]
  have hsum_le := Finset.sum_le_sum hpt
  have hR : ∑ v ∈ D, ((h : ℝ) * LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0 v
        + (N : ℝ) * (if v = 0 then
            LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0 v else 0))
      = (h : ℝ) * ∑ y ∈ D, LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0 y
        + (N : ℝ) * LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0 0 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_ite_eq', if_pos hO]
  rw [hid]
  linarith [hsum_le, hR]
