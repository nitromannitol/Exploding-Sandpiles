/-
Block geometry for the renormalization of the chemical-distance estimate: the block of a site at
scale `N`, the sites of a set of blocks, sup-norm cubes of blocks, the window of a block, the
bonds inside a window, and the cardinality bounds used to compare chemical distances with
numbers of blocks.
-/
import Exploding.Support.ArxivBondConfinedDistance
import Exploding.Support.ArxivBondReachWalk

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-! ### Integer division -/

/-- Bounds characterizing integer division by a positive integer. -/
theorem int_ediv_eq_of_bounds {N a q : ℤ} (hN : 0 < N) (h1 : N * q ≤ a) (h2 : a < N * q + N) :
    a / N = q := by
  have h0 := Int.mul_ediv_add_emod a N
  have h3 := Int.emod_nonneg a hN.ne'
  have h4 := Int.emod_lt_of_pos a hN
  have h5 : N * (a / N - q) < N * 1 := by nlinarith
  have h6 : N * (q - a / N) < N * 1 := by nlinarith
  have h7 := lt_of_mul_lt_mul_left h5 hN.le
  have h8 := lt_of_mul_lt_mul_left h6 hN.le
  omega

/-- The quotient of integer division by a positive integer brackets the dividend. -/
theorem int_ediv_bounds {N : ℤ} (hN : 0 < N) (a : ℤ) : N * (a / N) ≤ a ∧ a < N * (a / N) + N := by
  have h0 := Int.mul_ediv_add_emod a N
  have h3 := Int.emod_nonneg a hN.ne'
  have h4 := Int.emod_lt_of_pos a hN
  constructor <;> linarith

/-! ### Blocks -/

/-- The block of a site at scale `N`: the coordinatewise quotient by `N`, rounded down. -/
def coarseSite (N : ℕ) (u : Site d) : Site d := fun i => u i / (N : ℤ)

/-- The sites whose block lies in a given set of blocks. -/
def coarseRegion (N : ℕ) (S : Set (Site d)) : Set (Site d) := {u | coarseSite N u ∈ S}

/-- The blocks at sup-norm distance at most `r` from `b`. -/
def coarseCube (r : ℕ) (b : Site d) : Set (Site d) := {c | ∀ i, |c i - b i| ≤ r}

/-- The window of the block `b`: the sites of the blocks at sup-norm distance at most `r`. -/
def coarseWindow (N r : ℕ) (b : Site d) : Set (Site d) := coarseRegion N (coarseCube r b)

/-- The bonds with both endpoints in the window of `b`. -/
def windowBonds (N r : ℕ) (b : Site d) : Set (Site d × Fin d) :=
  {e | e.1 ∈ coarseWindow N r b ∧ e.1 + unit e.2 ∈ coarseWindow N r b}

theorem coarseSite_zero (N : ℕ) : coarseSite N (0 : Site d) = 0 := by
  funext i
  simp [coarseSite]

theorem mem_coarseCube_self (r : ℕ) (b : Site d) : b ∈ coarseCube r b := fun i => by simp

theorem coarseCube_symm {r : ℕ} {b c : Site d} (h : c ∈ coarseCube r b) : b ∈ coarseCube r c :=
  fun i => by rw [abs_sub_comm]; exact h i

/-- A block and its window: the block of a site of the window lies in the cube of blocks. -/
theorem mem_coarseWindow_iff {N r : ℕ} {b u : Site d} :
    u ∈ coarseWindow N r b ↔ ∀ i, |coarseSite N u i - b i| ≤ r := Iff.rfl

theorem mem_coarseWindow_self (N r : ℕ) (u : Site d) : u ∈ coarseWindow N r (coarseSite N u) :=
  mem_coarseCube_self r _

/-- Nearest-neighbour sites lie in the same block or in nearest-neighbour blocks. -/
theorem coarseSite_eq_or_adj {N : ℕ} (hN : 0 < N) {u v : Site d} (h : (lattice d).Adj u v) :
    coarseSite N u = coarseSite N v ∨ (lattice d).Adj (coarseSite N u) (coarseSite N v) := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have key : ∀ a b : Site d, ∀ i : Fin d, b = a + unit i →
      coarseSite N a = coarseSite N b ∨ coarseSite N b = coarseSite N a + unit i := by
    intro a b i hb
    subst hb
    obtain ⟨h1, h2⟩ := int_ediv_bounds hN' (a i)
    by_cases hlt : a i + 1 < (N : ℤ) * (a i / N) + N
    · left
      funext j
      by_cases hj : j = i
      · subst hj
        simp only [coarseSite, Pi.add_apply, unit, Pi.single_eq_same]
        exact (int_ediv_eq_of_bounds hN' (by linarith) hlt).symm
      · simp [coarseSite, unit, Pi.single_eq_of_ne hj]
    · right
      funext j
      by_cases hj : j = i
      · subst hj
        simp only [coarseSite, Pi.add_apply, unit, Pi.single_eq_same]
        exact int_ediv_eq_of_bounds hN' (by nlinarith) (by nlinarith)
      · simp [coarseSite, unit, Pi.single_eq_of_ne hj]
  obtain ⟨i, hi | hi⟩ := h
  · rcases key u v i hi with h | h
    · exact Or.inl h
    · exact Or.inr ⟨i, Or.inl h⟩
  · rcases key v u i hi with h | h
    · exact Or.inl h.symm
    · exact Or.inr ⟨i, Or.inr h⟩

/-! ### Finite versions -/

/-- The sites of the block `c`, as a finset. -/
noncomputable def coarseBoxFinset (N : ℕ) (c : Site d) : Finset (Site d) :=
  Finset.univ.image fun v : Fin d → Fin N => fun i => (N : ℤ) * c i + ((v i : ℕ) : ℤ)

theorem mem_coarseBoxFinset {N : ℕ} (hN : 0 < N) {c u : Site d} :
    u ∈ coarseBoxFinset N c ↔ coarseSite N u = c := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  constructor
  · intro hu
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hu
    funext i
    have hv : ((v i : ℕ) : ℤ) < N := by exact_mod_cast (v i).isLt
    exact int_ediv_eq_of_bounds hN' (by simp) (by simp only; omega)
  · intro hu
    refine Finset.mem_image.mpr ⟨fun i => ⟨(u i % N).toNat, ?_⟩, Finset.mem_univ _, ?_⟩
    · have h3 := Int.emod_nonneg (u i) hN'.ne'
      have h4 := Int.emod_lt_of_pos (u i) hN'
      omega
    · funext i
      have h0 := Int.mul_ediv_add_emod (u i) N
      have h3 := Int.emod_nonneg (u i) hN'.ne'
      have hc : c i = u i / N := (congrFun hu i).symm
      simp only [Int.toNat_of_nonneg h3, hc]
      omega

theorem card_coarseBoxFinset_le (N : ℕ) (c : Site d) : (coarseBoxFinset N c).card ≤ N ^ d := by
  classical
  refine Finset.card_image_le.trans ?_
  simp

/-- The blocks at sup-norm distance at most `r` from `b`, as a finset. -/
def coarseCubeFinset (r : ℕ) (b : Site d) : Finset (Site d) :=
  Finset.Icc (fun i => b i - r) (fun i => b i + r)

theorem mem_coarseCubeFinset {r : ℕ} {b c : Site d} :
    c ∈ coarseCubeFinset r b ↔ c ∈ coarseCube r b := by
  simp only [coarseCubeFinset, Finset.mem_Icc, coarseCube, Set.mem_ofPred_eq, Pi.le_def, abs_le]
  constructor
  · rintro ⟨h1, h2⟩ i
    have := h1 i
    have := h2 i
    constructor <;> linarith
  · intro h
    exact ⟨fun i => by linarith [(h i).1], fun i => by linarith [(h i).2]⟩

theorem card_coarseCubeFinset (r : ℕ) (b : Site d) :
    (coarseCubeFinset r b).card = (2 * r + 1) ^ d := by
  rw [coarseCubeFinset, Pi.card_Icc]
  simp only [Int.card_Icc]
  have h : ∀ x : Fin d, (b x + (r : ℤ) + 1 - (b x - r)).toNat = 2 * r + 1 := fun x => by omega
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The sites of a finite set of blocks, as a finset. -/
noncomputable def coarseRegionFinset (N : ℕ) (E : Finset (Site d)) : Finset (Site d) :=
  E.biUnion (coarseBoxFinset N)

theorem mem_coarseRegionFinset {N : ℕ} (hN : 0 < N) {E : Finset (Site d)} {u : Site d} :
    u ∈ coarseRegionFinset N E ↔ u ∈ coarseRegion N (E : Set (Site d)) := by
  simp only [coarseRegionFinset, Finset.mem_biUnion, mem_coarseBoxFinset hN, coarseRegion,
    Set.mem_ofPred_eq, Finset.mem_coe]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact hc
  · intro h
    exact ⟨_, h, rfl⟩

theorem card_coarseRegionFinset_le (N : ℕ) (E : Finset (Site d)) :
    (coarseRegionFinset N E).card ≤ E.card * N ^ d := by
  refine Finset.card_biUnion_le.trans ?_
  calc
    ∑ c ∈ E, (coarseBoxFinset N c).card ≤ ∑ _c ∈ E, N ^ d :=
      Finset.sum_le_sum fun c _ => card_coarseBoxFinset_le N c
    _ = E.card * N ^ d := by rw [Finset.sum_const, smul_eq_mul]

/-- The enlargement of a finite set of blocks by sup-norm cubes of radius `r`. -/
noncomputable def coarseEnlargement (r : ℕ) (F : Finset (Site d)) : Finset (Site d) :=
  F.biUnion (coarseCubeFinset r)

theorem mem_coarseEnlargement {r : ℕ} {F : Finset (Site d)} {b : Site d} :
    b ∈ coarseEnlargement r F ↔ ∃ c ∈ F, b ∈ coarseCube r c := by
  simp only [coarseEnlargement, Finset.mem_biUnion, mem_coarseCubeFinset]

theorem card_coarseEnlargement_le (r : ℕ) (F : Finset (Site d)) :
    (coarseEnlargement r F).card ≤ F.card * (2 * r + 1) ^ d := by
  refine Finset.card_biUnion_le.trans ?_
  simp only [card_coarseCubeFinset, Finset.sum_const, smul_eq_mul, le_refl]

theorem coarseWindow_finite {N : ℕ} (hN : 0 < N) (r : ℕ) (b : Site d) :
    (coarseWindow N r b).Finite := by
  refine (coarseRegionFinset N (coarseCubeFinset r b)).finite_toSet.subset ?_
  intro u hu
  rw [Finset.mem_coe, mem_coarseRegionFinset hN]
  exact mem_coarseCubeFinset.mpr hu

theorem windowBonds_finite {N : ℕ} (hN : 0 < N) (r : ℕ) (b : Site d) :
    (windowBonds N r b).Finite := by
  refine ((coarseWindow_finite hN r b).prod (Set.finite_univ (α := Fin d))).subset ?_
  intro e he
  exact ⟨he.1, Set.mem_univ _⟩

/-- Windows of blocks at sup-norm distance more than `2r` are disjoint. -/
theorem coarseWindow_disjoint {N r : ℕ} {b b' : Site d} (h : ∃ i, 2 * (r : ℤ) + 1 ≤ |b i - b' i|) :
    Disjoint (coarseWindow N r b) (coarseWindow N r b') := by
  rw [Set.disjoint_left]
  intro u hu hu'
  obtain ⟨i, hi⟩ := h
  have h1 := hu i
  have h2 := hu' i
  rw [abs_le] at h1 h2
  rw [le_abs] at hi
  omega

/-- Bonds of windows of blocks at sup-norm distance more than `2r` are disjoint. -/
theorem windowBonds_disjoint {N r : ℕ} {b b' : Site d} (h : ∃ i, 2 * (r : ℤ) + 1 ≤ |b i - b' i|) :
    Disjoint (windowBonds N r b) (windowBonds N r b') := by
  rw [Set.disjoint_left]
  intro e he he'
  exact Set.disjoint_left.mp (coarseWindow_disjoint h) he.1 he'.1

/-- An open path inside the sites of a finite set of blocks bounds the chemical distance by the
number of sites of these blocks. -/
theorem open_bond_edist_lt_of_reach_coarseRegion {N : ℕ} (hN : 0 < N)
    {ω : Site d × Fin d → Bool} {E : Finset (Site d)} {x y : Site d}
    (h : xap_Reach ω (coarseRegion N (E : Set (Site d))) x y) :
    (openBondGraph ω).edist x y < ((E.card * N ^ d : ℕ) : ℕ∞) := by
  obtain ⟨p, hp⟩ := open_walk_of_reach_in_set h
  have hlt := open_bond_edist_lt_card_of_walk_support_subset (coarseRegionFinset N E) p
    (fun z hz => (mem_coarseRegionFinset hN).mpr (hp z hz))
  exact lt_of_lt_of_le hlt (by exact_mod_cast card_coarseRegionFinset_le N E)

/-- Open paths inside a subset of a window depend only on the bonds of the window. -/
theorem xap_reach_congr_of_window {N r : ℕ} {b : Site d} {ω ω' : Site d × Fin d → Bool}
    (h : ∀ e ∈ windowBonds N r b, ω e = ω' e) {S : Set (Site d)}
    (hS : S ⊆ coarseWindow N r b) {a z : Site d} (hω : xap_Reach ω S a z) : xap_Reach ω' S a z := by
  refine ⟨hω.1, xap_rtg_mono (fun x y hxy => ⟨hxy.1, hxy.2.1, ?_⟩) hω.2⟩
  obtain ⟨hx, hy, hadj⟩ := hxy
  rw [openBondGraph, SimpleGraph.fromRel_adj] at hadj ⊢
  obtain ⟨hne, ⟨i, rfl, hi⟩ | ⟨i, rfl, hi⟩⟩ := hadj
  · exact ⟨hne, Or.inl ⟨i, rfl, by rw [← h (x, i) ⟨hS hx, hS hy⟩]; exact hi⟩⟩
  · exact ⟨hne, Or.inr ⟨i, rfl, by rw [← h (y, i) ⟨hS hy, hS hx⟩]; exact hi⟩⟩

theorem int_ediv_abs_sub_le_iff {N a c r : ℤ} (hN : 0 < N) :
    |a / N - c| ≤ r ↔ N * (c - r) ≤ a ∧ a < N * (c + r + 1) := by
  obtain ⟨h1, h2⟩ := int_ediv_bounds hN a
  rw [abs_le]
  constructor
  · rintro ⟨h3, h4⟩
    constructor <;> nlinarith
  · rintro ⟨h3, h4⟩
    constructor
    · by_contra h
      have : a / N ≤ c - r - 1 := by linarith
      nlinarith
    · by_contra h
      have : c + r + 1 ≤ a / N := by linarith
      nlinarith

/-- The window of `b` is a box of `(2r+1)N` sites in each direction. -/
theorem mem_coarseWindow_iff_bounds {N r : ℕ} (hN : 0 < N) {b u : Site d} :
    u ∈ coarseWindow N r b ↔
      ∀ i, (N : ℤ) * (b i - r) ≤ u i ∧ u i < (N : ℤ) * (b i + r + 1) := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  rw [mem_coarseWindow_iff]
  exact forall_congr' fun i => int_ediv_abs_sub_le_iff hN'

/-- The block of `u` is `b` exactly when `u` lies in the box of side `N` at `N b`. -/
theorem coarseSite_eq_iff_bounds {N : ℕ} (hN : 0 < N) {b u : Site d} :
    coarseSite N u = b ↔ ∀ i, (N : ℤ) * b i ≤ u i ∧ u i < (N : ℤ) * b i + N := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  constructor
  · rintro rfl i
    exact int_ediv_bounds hN' (u i)
  · intro h
    funext i
    exact int_ediv_eq_of_bounds hN' (h i).1 (h i).2

theorem coarseSite_sub_smul {N : ℕ} (hN : 0 < N) (u b : Site d) :
    coarseSite N (u - fun i => (N : ℤ) * b i) = coarseSite N u - b := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  funext i
  obtain ⟨h1, h2⟩ := int_ediv_bounds hN' (u i)
  simp only [coarseSite, Pi.sub_apply]
  exact int_ediv_eq_of_bounds hN' (by rw [mul_sub]; linarith) (by rw [mul_sub]; linarith)

end Exploding
