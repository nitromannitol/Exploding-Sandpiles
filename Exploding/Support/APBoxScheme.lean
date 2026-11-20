/-
The box block scheme in every dimension, from a crossing estimate for cubes and a uniqueness
estimate for large open paths in boxes.

For `N ≥ 1`, a block `b` is box-good when each of the `3^d` blocks of its window contains an open
path between two of its sites at sup-distance at least `N - 1`, and any two open paths inside the
window, each between two sites at sup-distance at least `N - 1`, are joined inside the window.
The core of a box-good block is the set of sites joined inside the window to the start of such
a path.  This is a block scheme with windows of radius one (`box_isBlockScheme`), and a block is
bad with probability at most `3^d` times the probability that the cube `[0, N)^d` has no such
path plus the probability that uniqueness fails in the box `[-N, 2N)^d`.  Both probabilities tend
to zero at every density above `bondCritical d` by the coarse-graining estimate of Pisztora
(*Surface order large deviations for Ising, Potts and percolation models*, Probab. Theory
Related Fields 104 (1996), Theorem 3.1, for `d ≥ 3`; it rests on the slab theorem of Grimmett
and Marstrand); `PisztoraBoxEstimate d` is that statement, and under it the Antal–Pisztora bound
holds in dimension `d` (`chemicalDistance_of_boxEstimate`).
-/
import Exploding.Support.APBlockReduction
import Exploding.Support.RNProofChem

open LatticeProb Relation MeasureTheory Filter Topology
open scoped ENNReal

namespace Exploding

variable {d : ℕ}

/-! ### Large open paths -/

/-- `x` and `y` are joined by an open path inside `S` and are at sup-distance at least
`N - 1`. -/
def LargePair (N : ℕ) (ω : Site d × Fin d → Bool) (S : Set (Site d)) (x y : Site d) : Prop :=
  xap_Reach ω S x y ∧ ∃ i, (N : ℤ) - 1 ≤ |x i - y i|

/-- The cube `[0, N)^d`. -/
def lowerCube (d N : ℕ) : Set (Site d) := {x | ∀ i, 0 ≤ x i ∧ x i < N}

/-- The box `[-N, 2N)^d`. -/
def tripleBox (d N : ℕ) : Set (Site d) := {x | ∀ i, -(N : ℤ) ≤ x i ∧ x i < 2 * N}

/-- The cube `[0, N)^d` contains an open path between two of its sites at sup-distance at least
`N - 1`. -/
def CubeCrossing (N : ℕ) (ω : Site d × Fin d → Bool) : Prop :=
  ∃ x y, LargePair N ω (lowerCube d N) x y

/-- Any two open paths inside the box `[-N, 2N)^d`, each between two sites at sup-distance at
least `N - 1`, are joined inside the box. -/
def BoxUniqueness (N : ℕ) (ω : Site d × Fin d → Bool) : Prop :=
  ∀ x y z w, LargePair N ω (tripleBox d N) x y → LargePair N ω (tripleBox d N) z w →
    xap_Reach ω (tripleBox d N) x z

/-- **The box estimate of the renormalization** in dimension `d`: at every density above
`bondCritical d`, the cube `[0, N)^d` contains an open path between two of its sites at
sup-distance at least `N - 1`, and all such paths inside `[-N, 2N)^d` are joined inside it, with
probabilities tending to one as `N → ∞`.  For `d ≥ 3` this is a consequence of Pisztora's
coarse-graining theorem (Pisztora 1996, Theorem 3.1). -/
def PisztoraBoxEstimate (d : ℕ) : Prop :=
  ∀ q : ℝ, bondCritical d < q → q ≤ 1 →
    Tendsto (fun N : ℕ => bondPercolation d q {ω | ¬ CubeCrossing N ω}) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => bondPercolation d q {ω | ¬ BoxUniqueness N ω}) atTop (𝓝 0)

theorem lowerCube_eq {N : ℕ} (hN : 0 < N) :
    lowerCube d N = coarseRegion N ({0} : Set (Site d)) := by
  ext u
  simp only [coarseRegion, Set.mem_singleton_iff, Set.mem_ofPred_eq, lowerCube,
    coarseSite_eq_iff_bounds hN, Pi.zero_apply, mul_zero, zero_add]

theorem tripleBox_eq {N : ℕ} (hN : 0 < N) : tripleBox d N = coarseWindow N 1 0 := by
  ext u
  rw [mem_coarseWindow_iff_bounds hN]
  simp only [tripleBox, Set.mem_ofPred_eq, Pi.zero_apply, zero_sub, Nat.cast_one, zero_add]
  exact forall_congr' fun i => by constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-! ### Translation -/

theorem xap_reach_shift_iff {x : Site d} {ω : Site d × Fin d → Bool} {S : Set (Site d)}
    {a e : Site d} :
    xap_Reach (rn_shiftBond x ω) S a e ↔ xap_Reach ω {z | z - x ∈ S} (a + x) (e + x) := by
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨by simpa using ha, ?_⟩
    exact ReflTransGen.lift (fun z => z + x) (fun u v huv => ⟨by simpa using huv.1,
      by simpa using huv.2.1, (rn_openBond_shift_adj x ω u v).mp huv.2.2⟩) _ _ h
  · rintro ⟨ha, h⟩
    refine ⟨by simpa using ha, ?_⟩
    have h2 : ReflTransGen (xap_RS (rn_shiftBond x ω) S) (a + x - x) (e + x - x) :=
      ReflTransGen.lift (fun z => z - x) (p := xap_RS (rn_shiftBond x ω) S)
        (fun u v huv => ⟨huv.1, huv.2.1, (rn_openBond_shift_adj x ω (u - x) (v - x)).mpr
          (by simpa using huv.2.2)⟩) _ _ h
    simpa using h2

theorem largePair_shift_iff {N : ℕ} {x : Site d} {ω : Site d × Fin d → Bool} {S : Set (Site d)}
    {a e : Site d} :
    LargePair N (rn_shiftBond x ω) S a e ↔ LargePair N ω {z | z - x ∈ S} (a + x) (e + x) := by
  rw [LargePair, LargePair, xap_reach_shift_iff]
  simp only [Pi.add_apply, add_sub_add_right_eq_sub]

/-- An event determined by the bonds of a finite set is measurable. -/
theorem measurableSet_of_local {A : Set (Site d × Fin d)} (hA : A.Finite)
    {E : Set (Site d × Fin d → Bool)}
    (hdet : ∀ ω ω' : Site d × Fin d → Bool, (∀ e ∈ A, ω e = ω' e) → (ω ∈ E ↔ ω' ∈ E)) :
    MeasurableSet E :=
  Measurable.comap_le (Measurable.of_eval fun _ => measurable_pi_apply _) _
    (measurableSet_comap_domRestrict_of_local hA hdet)

/-! ### The box scheme -/

/-- A block is box-good: every block of its window contains a large open path, and large open
paths inside the window are joined inside it. -/
def boxGood (N : ℕ) (ω : Site d × Fin d → Bool) (b : Site d) : Prop :=
  (∀ b' ∈ coarseCube 1 b, ∃ x y, LargePair N ω (coarseRegion N {b'}) x y) ∧
    ∀ x y z w, LargePair N ω (coarseWindow N 1 b) x y → LargePair N ω (coarseWindow N 1 b) z w →
      xap_Reach ω (coarseWindow N 1 b) x z

/-- The core of a block: the sites joined inside its window to the start of a large open path
inside the window. -/
def boxCore (N : ℕ) (ω : Site d × Fin d → Bool) (b : Site d) : Set (Site d) :=
  {v | ∃ x y, LargePair N ω (coarseWindow N 1 b) x y ∧ xap_Reach ω (coarseWindow N 1 b) x v}

theorem coarseRegion_singleton_subset_window {N : ℕ} {b b' : Site d} (h : b' ∈ coarseCube 1 b) :
    coarseRegion N ({b'} : Set (Site d)) ⊆ coarseWindow N 1 b := by
  intro u hu
  rw [coarseRegion, Set.mem_ofPred_eq, Set.mem_singleton_iff] at hu
  show coarseSite N u ∈ coarseCube 1 b
  rw [hu]
  exact h

theorem largePair_mono {N : ℕ} {ω : Site d × Fin d → Bool} {S S' : Set (Site d)} (h : S ⊆ S')
    {x y : Site d} (hp : LargePair N ω S x y) : LargePair N ω S' x y :=
  ⟨xap_reach_mono h hp.1, hp.2⟩

theorem boxCore_connected {N : ℕ} {ω : Site d × Fin d → Bool} {b : Site d}
    (hgood : boxGood N ω b) {c c' : Site d} (hc : c ∈ boxCore N ω b) (hc' : c' ∈ boxCore N ω b) :
    xap_Reach ω (coarseWindow N 1 b) c c' := by
  obtain ⟨x, y, hxy, hxc⟩ := hc
  obtain ⟨z, w, hzw, hzc⟩ := hc'
  exact xap_reach_trans (xap_reach_symm hxc) (xap_reach_trans (hgood.2 x y z w hxy hzw) hzc)

/-- The last site inside the window before an open path leaves it. -/
theorem exists_exit_of_reachable {N r : ℕ} {ω : Site d × Fin d → Bool} {b u e : Site d}
    (hu : u ∈ coarseWindow N r b) (he : e ∉ coarseWindow N r b)
    (hue : (openBondGraph ω).Reachable u e) :
    ∃ w w', xap_Reach ω (coarseWindow N r b) u w ∧ w' ∉ coarseWindow N r b ∧
      (openBondGraph ω).Adj w w' := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hue
  have key : ∀ z, ReflTransGen (openBondGraph ω).Adj u z →
      (z ∈ coarseWindow N r b ∧ xap_Reach ω (coarseWindow N r b) u z) ∨
        ∃ w w', xap_Reach ω (coarseWindow N r b) u w ∧ w' ∉ coarseWindow N r b ∧
          (openBondGraph ω).Adj w w' := by
    intro z hz
    induction hz with
    | refl => exact Or.inl ⟨hu, xap_reach_refl hu⟩
    | @tail z z' _ hzz' ih =>
      rcases ih with ⟨hzW, huz⟩ | hdone
      · by_cases hz'W : z' ∈ coarseWindow N r b
        · exact Or.inl ⟨hz'W, xap_reach_trans huz (xap_reach_step hzW hz'W hzz')⟩
        · exact Or.inr ⟨z, z', huz, hz'W, hzz'⟩
      · exact Or.inr hdone
  rcases key e hue with ⟨heW, _⟩ | hdone
  · exact (he heW).elim
  · exact hdone

theorem box_blockLinks {N : ℕ} (hN : 0 < N) (ω : Site d × Fin d → Bool) :
    BlockLinks N 1 ω (boxGood N ω) (boxCore N ω) where
  nonempty b hb := by
    obtain ⟨x, y, hxy⟩ := hb.1 b (mem_coarseCube_self 1 b)
    exact ⟨x, x, y, largePair_mono (coarseRegion_singleton_subset_window
      (mem_coarseCube_self 1 b)) hxy, xap_reach_refl (coarseRegion_singleton_subset_window
        (mem_coarseCube_self 1 b) hxy.1.1)⟩
  attach u hu hleave := by
    obtain ⟨e, he, hue⟩ := hleave
    set b := coarseSite N u
    have huW : u ∈ coarseWindow N 1 b := mem_coarseWindow_self N 1 u
    obtain ⟨w, w', huw, hw'W, hww'⟩ := exists_exit_of_reachable huW he hue
    have hwW := xap_reach_mem_right huw
    refine ⟨u, ⟨u, w, ⟨huw, ?_⟩, xap_reach_refl huW⟩, xap_reach_refl huW⟩
    have hub := (coarseSite_eq_iff_bounds hN (b := b) (u := u)).mp rfl
    have hwb := (mem_coarseWindow_iff_bounds hN).mp hwW
    have hw'b : ¬ ∀ i, (N : ℤ) * (b i - (1 : ℕ)) ≤ w' i ∧ w' i < (N : ℤ) * (b i + (1 : ℕ) + 1) :=
      fun h => hw'W ((mem_coarseWindow_iff_bounds hN).mpr h)
    push Not at hw'b
    obtain ⟨i, hi⟩ := hw'b
    refine ⟨i, ?_⟩
    obtain ⟨j, hj | hj⟩ := xap_lattice_of_open hww'
    · subst hj
      by_cases hij : i = j
      · subst hij
        have h1 := hwb i
        have h2 := hub i
        simp only [Pi.add_apply, unit, Pi.single_eq_same] at hi
        push_cast at h1 hi
        have h3 := hi (by linarith [h1.1])
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith
      · have := hwb i
        simp only [Pi.add_apply, unit, Pi.single_eq_of_ne hij, add_zero] at hi
        exact absurd (hi this.1) (not_le.mpr this.2)
    · subst hj
      by_cases hij : i = j
      · subst hij
        have h1 := hwb i
        have h2 := hub i
        simp only [Pi.add_apply, unit, Pi.single_eq_same] at h1 ⊢
        push_cast at h1 hi
        have h3 : w' i < (N : ℤ) * (b i - 1) := by
          by_contra hcon
          have := hi (not_lt.mp hcon)
          linarith [h1.2]
        rw [abs_of_nonneg (by linarith)]
        linarith
      · have := hwb i
        simp only [Pi.add_apply, unit, Pi.single_eq_of_ne hij, add_zero] at this
        exact absurd (hi this.1) (not_le.mpr this.2)
  inner b hb c hc c' hc' := boxCore_connected hb hc hc'
  link b b' hb hb' hbb c hc c' hc' := by
    have hb'cube : b' ∈ coarseCube 1 b := fun i => by
      rw [abs_sub_comm]
      exact_mod_cast hbb.2 i
    obtain ⟨x, y, hxy⟩ := hb.1 b' hb'cube
    have hxyb : LargePair N ω (coarseWindow N 1 b) x y :=
      largePair_mono (coarseRegion_singleton_subset_window hb'cube) hxy
    have hxyb' : LargePair N ω (coarseWindow N 1 b') x y :=
      largePair_mono (coarseRegion_singleton_subset_window (mem_coarseCube_self 1 b')) hxy
    have hxW : x ∈ coarseWindow N 1 b := hxyb.1.1
    have hxW' : x ∈ coarseWindow N 1 b' := hxyb'.1.1
    have h1 := boxCore_connected hb hc ⟨x, y, hxyb, xap_reach_refl hxW⟩
    have h2 := boxCore_connected hb' ⟨x, y, hxyb', xap_reach_refl hxW'⟩ hc'
    exact xap_reach_trans (xap_reach_mono Set.subset_union_left h1)
      (xap_reach_mono Set.subset_union_right h2)

theorem boxGood_isLocal (N : ℕ) : IsLocalBlockPredicate N 1 (boxGood (d := d) N) := by
  have hreach : ∀ b (ω ω' : Site d × Fin d → Bool), (∀ e ∈ windowBonds N 1 b, ω e = ω' e) →
      ∀ {S : Set (Site d)}, S ⊆ coarseWindow N 1 b → ∀ {x y}, LargePair N ω S x y →
        LargePair N ω' S x y :=
    fun b ω ω' h S hS x y hp => ⟨xap_reach_congr_of_window h hS hp.1, hp.2⟩
  have key : ∀ b (ω ω' : Site d × Fin d → Bool), (∀ e ∈ windowBonds N 1 b, ω e = ω' e) →
      boxGood N ω b → boxGood N ω' b := by
    intro b ω ω' h hg
    have h' : ∀ e ∈ windowBonds N 1 b, ω' e = ω e := fun e he => (h e he).symm
    refine ⟨fun b' hb' => ?_, fun x y z w hxy hzw => ?_⟩
    · obtain ⟨x, y, hxy⟩ := hg.1 b' hb'
      exact ⟨x, y, hreach b ω ω' h (coarseRegion_singleton_subset_window hb') hxy⟩
    · exact xap_reach_congr_of_window h le_rfl
        (hg.2 x y z w (hreach b ω' ω h' le_rfl hxy) (hreach b ω' ω h' le_rfl hzw))
  intro b ω ω' h
  exact ⟨key b ω ω' h, key b ω' ω fun e he => (h e he).symm⟩

theorem box_isBlockScheme {N : ℕ} (hN : 0 < N) :
    IsBlockScheme N 1 (boxGood (d := d) N) (boxCore N) :=
  ⟨hN, boxGood_isLocal N, box_blockLinks hN⟩

end Exploding
