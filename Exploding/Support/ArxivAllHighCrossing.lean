/-
The deterministic all-high endpoint of the arXiv-v2 crossing construction.

At scale one the cube has a single site.  An internal seed fixes that site;
an external face seed delivers one chip to it, so it topples at the first step.
-/
import Exploding.Support.SubCrossTime
import Exploding.Support.SubFodoStep
import Exploding.Support.SubGeom

namespace Exploding

open LatticeProb
open scoped Classical

private def arxivAllHigh_oneSite (d : ℕ) : Site d := fun _ => 1

private theorem arxivAllHigh_mem_cube_one_eq {d : ℕ} {x : Site d}
    (hx : x ∈ cube d 1) : x = arxivAllHigh_oneSite d := by
  funext i
  exact le_antisymm (hx i).2 (hx i).1

private theorem arxivAllHigh_oneSite_mem_cube (d : ℕ) :
    arxivAllHigh_oneSite d ∈ cube d 1 := by
  intro i
  simp [arxivAllHigh_oneSite]

private theorem arxivAllHigh_crossOne_of_internalSeed (d : ℕ) (i : Fin d)
    (z : Site d) (hqline : arxivAllHigh_oneSite d ∈ line d 1 i z) :
    crossOdo (fun _ : Site d => 2 * (d : ℤ) - 1) 1 i z 1
      (arxivAllHigh_oneSite d) = 1 := by
  let S : Set (Site d) := (cube d 1)ᶜ ∪ line d 1 i z
  let w : Site d → ℤ := fun x => if x ∈ line d 1 i z then 1 else 0
  have hqS : arxivAllHigh_oneSite d ∈ S := by
    exact Or.inr hqline
  change fodo S (fun _ : Site d => 2 * (d : ℤ) - 1) w 1 (arxivAllHigh_oneSite d) = 1
  rw [fodo_of_mem S _ _ 1 hqS]
  simp [w, hqline]

private theorem arxivAllHigh_crossOne_of_externalSeed (d : ℕ) (i : Fin d)
    (z : Site d) (hzline : z ∈ line d 1 i z)
    (hqnotline : arxivAllHigh_oneSite d ∉ line d 1 i z)
    (hadj : (lattice d).Adj z (arxivAllHigh_oneSite d)) :
    crossOdo (fun _ : Site d => 2 * (d : ℤ) - 1) 1 i z 1
      (arxivAllHigh_oneSite d) = 1 := by
  let q := arxivAllHigh_oneSite d
  let η : Site d → ℤ := fun _ => 2 * (d : ℤ) - 1
  let S : Set (Site d) := (cube d 1)ᶜ ∪ line d 1 i z
  let w : Site d → ℤ := fun x => if x ∈ line d 1 i z then 1 else 0
  have hqcube : q ∈ cube d 1 := arxivAllHigh_oneSite_mem_cube d
  have hqnotS : q ∉ S := by
    intro h
    rcases h with h | h
    · exact h hqcube
    · exact hqnotline h
  have hw_nonneg : ∀ x, 0 ≤ w x := by
    intro x
    dsimp [w]
    split_ifs <;> norm_num
  have hsum : 1 ≤ nbrSumZ w q := by
    obtain ⟨j, hj | hj⟩ := hadj
    · have hq : q = z + unit j := hj
      have hz : z = q - unit j := by
        calc
          z = (z + unit j) - unit j := by abel
          _ = q - unit j := by rw [hq]
      have hterm : w (q - unit j) = 1 := by
        rw [← hz]
        exact if_pos hzline
      unfold nbrSumZ
      calc
        1 = w (q - unit j) := hterm.symm
        _ ≤ w (q + unit j) + w (q - unit j) :=
          le_add_of_nonneg_left (hw_nonneg _)
        _ ≤ ∑ l : Fin d, (w (q + unit l) + w (q - unit l)) :=
          Finset.single_le_sum
            (fun l _ => add_nonneg (hw_nonneg _) (hw_nonneg _)) (Finset.mem_univ j)
    · have hz : z = q + unit j := hj
      have hterm : w (q + unit j) = 1 := by
        rw [← hz]
        exact if_pos hzline
      unfold nbrSumZ
      calc
        1 = w (q + unit j) := hterm.symm
        _ ≤ w (q + unit j) + w (q - unit j) :=
          le_add_of_nonneg_right (hw_nonneg _)
        _ ≤ ∑ l : Fin d, (w (q + unit l) + w (q - unit l)) :=
          Finset.single_le_sum
            (fun l _ => add_nonneg (hw_nonneg _) (hw_nonneg _)) (Finset.mem_univ j)
  have hqw : w q = 0 := by
    dsimp [w]
    exact if_neg hqnotline
  have hconf : 2 * (d : ℤ) ≤ fconf S η w 0 q := by
    change 2 * (d : ℤ) ≤ η q + lap w q
    rw [lap, hqw]
    dsimp [η]
    omega
  change fodo S η w 1 q = 1
  rw [fodo_succ_of_notMem S η w 0 hqnotS, fodo_zero, if_pos hconf, hqw]
  norm_num

/-- At scale one, the all-high background crosses from every internal or
external-face seed at time one.  The external case uses the delivered-seed
configuration `η + Δw₀`: its adjacent cube site has exactly the extra chip
needed to topple. -/
theorem arxivAllHigh_crossOne (d : ℕ) (i : Fin d) (z : Site d)
    (hz : z ∈ closureN (cube d 1)) :
    ∀ x ∈ cube d 1,
      crossOdo (fun _ : Site d => 2 * (d : ℤ) - 1) 1 i z 1 x = 1 := by
  intro x hx
  have hxq : x = arxivAllHigh_oneSite d := arxivAllHigh_mem_cube_one_eq hx
  subst x
  change z ∈ cube d 1 ∨
    (z ∉ cube d 1 ∧ ∃ y, y ∈ cube d 1 ∧ (lattice d).Adj z y) at hz
  rcases hz with hzin | ⟨hzout, y, hy, hadj⟩
  · have hzq := arxivAllHigh_mem_cube_one_eq hzin
    subst z
    apply arxivAllHigh_crossOne_of_internalSeed d i (arxivAllHigh_oneSite d)
    change (1 ≤ (arxivAllHigh_oneSite d) i ∧ (arxivAllHigh_oneSite d) i ≤ 1) ∧
      ∀ l, l ≠ i → (arxivAllHigh_oneSite d) l = (arxivAllHigh_oneSite d) l
    simp [arxivAllHigh_oneSite]
  · have hyq : y = arxivAllHigh_oneSite d := arxivAllHigh_mem_cube_one_eq hy
    subst y
    obtain ⟨l, hplus | hminus⟩ := hadj
    · have hzEq : z = arxivAllHigh_oneSite d - unit l := by
        calc
          z = (z + unit l) - unit l := by abel
          _ = arxivAllHigh_oneSite d - unit l := by rw [hplus]
      by_cases hil : l = i
      · have hqline : arxivAllHigh_oneSite d ∈ line d 1 i z := by
          change (1 ≤ (arxivAllHigh_oneSite d) i ∧
              (arxivAllHigh_oneSite d) i ≤ 1) ∧
            ∀ m, m ≠ i → (arxivAllHigh_oneSite d) m = z m
          constructor
          · simp [arxivAllHigh_oneSite]
          · intro m hmi
            rw [hzEq]
            simp [arxivAllHigh_oneSite, unit, hmi, hil]
        exact arxivAllHigh_crossOne_of_internalSeed d i z hqline
      · have hline : z ∈ line d 1 i z := by
          change (1 ≤ z i ∧ z i ≤ 1) ∧ ∀ m, m ≠ i → z m = z m
          constructor
          · have hzCoord : z i = 1 := by
              rw [hzEq]
              simp [arxivAllHigh_oneSite, unit, hil]
            rw [hzCoord]
            omega
          · intro m hm
            rfl
        have hqnotline : arxivAllHigh_oneSite d ∉ line d 1 i z := by
          intro h
          have hcoord := h.2 l hil
          have hzl : z l = 0 := by
            rw [hzEq]
            simp [arxivAllHigh_oneSite, unit]
          rw [arxivAllHigh_oneSite, hzl] at hcoord
          norm_num at hcoord
        exact arxivAllHigh_crossOne_of_externalSeed d i z hline hqnotline
          ⟨l, Or.inl (by rw [hzEq]; abel)⟩
    · have hzEq : z = arxivAllHigh_oneSite d + unit l := hminus
      by_cases hil : l = i
      · have hqline : arxivAllHigh_oneSite d ∈ line d 1 i z := by
          change (1 ≤ (arxivAllHigh_oneSite d) i ∧
              (arxivAllHigh_oneSite d) i ≤ 1) ∧
            ∀ m, m ≠ i → (arxivAllHigh_oneSite d) m = z m
          constructor
          · simp [arxivAllHigh_oneSite]
          · intro m hmi
            rw [hzEq]
            simp [arxivAllHigh_oneSite, unit, hmi, hil]
        exact arxivAllHigh_crossOne_of_internalSeed d i z hqline
      · have hline : z ∈ line d 1 i z := by
          change (1 ≤ z i ∧ z i ≤ 1) ∧ ∀ m, m ≠ i → z m = z m
          constructor
          · have hzCoord : z i = 1 := by
              rw [hzEq]
              simp [arxivAllHigh_oneSite, unit, hil]
            rw [hzCoord]
            omega
          · intro m hm
            rfl
        have hqnotline : arxivAllHigh_oneSite d ∉ line d 1 i z := by
          intro h
          have hcoord := h.2 l hil
          have hzl : z l = 2 := by
            rw [hzEq]
            simp [arxivAllHigh_oneSite, unit]
          rw [arxivAllHigh_oneSite, hzl] at hcoord
          norm_num at hcoord
        exact arxivAllHigh_crossOne_of_externalSeed d i z hline hqnotline
          ⟨l, Or.inr hzEq⟩

/-- The all-high background is a good cube at scale one in every dimension
`d ≥ 2`, with the delivered-seed frozen dynamics and the source `GoodCube`
predicate. -/
theorem arxivAllHigh_goodOne (d : ℕ) (_hd : 2 ≤ d) :
    GoodCube (fun _ : Site d => 2 * (d : ℤ) - 1) 1 := by
  intro i z hz
  have hcross := arxivAllHigh_crossOne d i z hz
  have hle := (crossingTime_le_iff (fun _ : Site d => 2 * (d : ℤ) - 1) 1 i z 1).2
    ⟨1, by omega, le_rfl, hcross⟩
  simpa using hle

/-- Every translated scale-one cube is good in the all-high background. -/
theorem arxivAllHigh_goodAtOne (d : ℕ) (hd : 2 ≤ d) (j : Site d) :
    GoodAt (fun _ : Site d => 2 * (d : ℤ) - 1) 1 j := by
  unfold GoodAt
  simpa using arxivAllHigh_goodOne d hd

/-- The all-high good-site cluster is the whole macroscopic lattice. -/
theorem arxivAllHigh_goodSitesOne (d : ℕ) (hd : 2 ≤ d) :
    goodSites (fun _ : Site d => 2 * (d : ℤ) - 1) 1 = Set.univ := by
  ext j
  simp [goodSites, arxivAllHigh_goodAtOne d hd j]

/-- The whole all-high good-site set is infinite in the source dimensions. -/
theorem arxivAllHigh_goodSitesOne_infinite (d : ℕ) (hd : 2 ≤ d) :
    (goodSites (fun _ : Site d => 2 * (d : ℤ) - 1) 1).Infinite := by
  rw [arxivAllHigh_goodSitesOne d hd]
  let i₀ : Fin d := ⟨0, by omega⟩
  let embed : ℕ → Site d := fun n i => if i = i₀ then (n : ℤ) else 0
  have hinj : Function.Injective embed := by
    intro m n hmn
    have hcoord := congrFun hmn i₀
    change (if i₀ = i₀ then (m : ℤ) else 0) =
      (if i₀ = i₀ then (n : ℤ) else 0) at hcoord
    simpa using hcoord
  exact Set.infinite_univ_iff.mpr (Infinite.of_injective embed hinj)

/-- Consequently the all-high macroscopic lattice has no bad sites (hence no
holes in the good-site set). -/
theorem arxivAllHigh_noHolesOne (d : ℕ) (hd : 2 ≤ d) :
    (goodSites (fun _ : Site d => 2 * (d : ℤ) - 1) 1)ᶜ = ∅ := by
  rw [arxivAllHigh_goodSitesOne d hd]
  simp

private def arxivAllHigh_toInducedHom (d : ℕ) :
    lattice d →g (lattice d).induce (Set.univ : Set (Site d)) where
  toFun := fun x => ⟨x, Set.mem_univ x⟩
  map_rel' := fun h => SimpleGraph.induce_adj.mpr h

private def arxivAllHigh_fromInducedHom (d : ℕ) :
    (lattice d).induce (Set.univ : Set (Site d)) →g lattice d where
  toFun := fun x => x.val
  map_rel' := fun h => SimpleGraph.induce_adj.mp h

/-- On the whole lattice, chemical distance is exactly the ordinary
lattice-graph distance. -/
theorem arxivAllHigh_chemDist_eq_graphEdist (d : ℕ) (x y : Site d) :
    chemDist (Set.univ : Set (Site d)) x y = (lattice d).edist x y := by
  unfold chemDist
  rw [SimpleGraph.edist_eq_sInf]
  congr 1
  ext t
  constructor
  · rintro ⟨n, rfl, hx, hy, w, hw⟩
    let w' : (lattice d).Walk x y :=
      (SimpleGraph.Walk.map (arxivAllHigh_fromInducedHom d) w).copy (by rfl) (by rfl)
    refine ⟨w', ?_⟩
    have hlen : w'.length = w.length := by
      simp [w', SimpleGraph.Walk.length_copy]
    change (w'.length : ℕ∞) = (n : ℕ∞)
    exact_mod_cast hlen.trans hw
  · rintro ⟨w, rfl⟩
    let W : ((lattice d).induce (Set.univ : Set (Site d))).Walk
        ⟨x, Set.mem_univ x⟩ ⟨y, Set.mem_univ y⟩ :=
      (SimpleGraph.Walk.map (arxivAllHigh_toInducedHom d) w).copy (by rfl) (by rfl)
    refine ⟨W.length, ?_, Set.mem_univ _, Set.mem_univ _, W, rfl⟩
    change (w.length : ℕ∞) = (W.length : ℕ∞)
    have hlen : W.length = w.length := by
      simp [W, SimpleGraph.Walk.length_copy]
    exact_mod_cast hlen.symm

/-- Every good-site component in the all-high configuration is the whole
macroscopic lattice, so its infinite component is unique and has no holes. -/
theorem arxivAllHigh_goodComponentOne (d : ℕ) (hd : 2 ≤ d) (x : Site d) :
    componentIn (goodSites (fun _ : Site d => 2 * (d : ℤ) - 1) 1) x = Set.univ := by
  rw [arxivAllHigh_goodSitesOne d hd]
  apply Set.eq_univ_iff_forall.mpr
  intro y
  let m : ℕ := max (mnorm x).toNat (mnorm y).toNat
  have hxnonneg : 0 ≤ mnorm x := by
    unfold mnorm
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hynonneg : 0 ≤ mnorm y := by
    unfold mnorm
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hxm : mnorm x ≤ (m : ℤ) := by
    rw [(Int.toNat_of_nonneg hxnonneg).symm]
    exact_mod_cast (Nat.le_max_left (mnorm x).toNat (mnorm y).toNat)
  have hym : mnorm y ≤ (m : ℤ) := by
    rw [(Int.toNat_of_nonneg hynonneg).symm]
    exact_mod_cast (Nat.le_max_right (mnorm x).toNat (mnorm y).toNat)
  have hxcent : x ∈ cent d m := by
    intro i
    have hcoord : |x i| ≤ mnorm x := by
      unfold mnorm
      exact Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)
    exact le_trans hcoord hxm
  have hycent : y ∈ cent d m := by
    intro i
    have hcoord : |y i| ≤ mnorm y := by
      unfold mnorm
      exact Finset.single_le_sum (fun j _ => abs_nonneg (y j)) (Finset.mem_univ i)
    exact le_trans hcoord hym
  exact cent_connected_in Set.univ m (Set.subset_univ _) x y hxcent hycent

end Exploding
