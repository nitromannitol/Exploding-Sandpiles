/-
The maximalization step for the infinite cluster of good sites: the source
finite-hole property makes an infinite connected good set intersect every
infinite connected good set.
-/
import Exploding.Support.RNProofPercolation

open Exploding LatticeProb

namespace Exploding

private theorem arxiv_component_finite_of_holeProp {d : ℕ} {C : Set (Site d)}
    (hholes : RnHoleProp d C) (x : Site d) (hx : x ∉ C) :
    (componentIn Cᶜ x).Finite := by
  obtain ⟨n₀, hn₀⟩ := hholes
  let n : ℕ := max n₀ (mnorm x).toNat
  have hn₀n : n₀ ≤ n := Nat.le_max_left _ _
  have hxcent : x ∈ (cent d n : Set (Site d)) := by
    intro i
    have hcoord : |x i| ≤ mnorm x := by
      unfold mnorm
      exact Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)
    have hnorm : 0 ≤ mnorm x := by
      unfold mnorm
      exact Finset.sum_nonneg fun j _ => abs_nonneg (x j)
    have hcast : ((mnorm x).toNat : ℤ) = mnorm x := Int.toNat_of_nonneg hnorm
    have hncoord : (mnorm x).toNat ≤ n := Nat.le_max_right _ _
    omega
  exact (hn₀ n hn₀n x hxcent hx).1

private theorem arxiv_infinite_connected_intersects {d : ℕ} {C D : Set (Site d)}
    (hholes : RnHoleProp d C) (hDinf : D.Infinite)
    (hDconn : ∀ x ∈ D, ∀ y ∈ D, y ∈ componentIn D x) :
    ∃ x, x ∈ D ∧ x ∈ C := by
  classical
  by_contra hdisj
  have hDcompl : D ⊆ Cᶜ := by
    intro x hxD
    change x ∉ C
    intro hxC
    exact hdisj ⟨x, hxD, hxC⟩
  obtain ⟨x, hxD⟩ := hDinf.nonempty
  have hDhole : D ⊆ componentIn Cᶜ x := by
    intro y hyD
    exact rn_componentIn_mono hDcompl x (hDconn x hxD y hyD)
  have hfin : (componentIn Cᶜ x).Finite :=
    arxiv_component_finite_of_holeProp hholes x (hDcompl hxD)
  exact hDinf (hfin.subset hDhole)

private theorem arxiv_componentIn_eq_of_mem {d : ℕ} {S : Set (Site d)} {x y : Site d}
    (hy : y ∈ componentIn S x) : componentIn S x = componentIn S y := by
  rcases hy with ⟨hxS, hyS, hxy⟩
  ext z
  constructor
  · rintro ⟨_, hzS, hxz⟩
    exact ⟨hyS, hzS, hxy.symm.trans hxz⟩
  · rintro ⟨_, hzS, hyz⟩
    exact ⟨hxS, hzS, hxy.trans hyz⟩

private theorem arxiv_walk_lift_to_component {d : ℕ} {S : Set (Site d)} {z : Site d}
    {u v : S} (p : ((lattice d).induce S).Walk u v)
    (hu : (u : Site d) ∈ componentIn S z) (hv : (v : Site d) ∈ componentIn S z) :
    Nonempty (((lattice d).induce (componentIn S z)).Walk ⟨u, hu⟩ ⟨v, hv⟩) := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil⟩
  | @cons a b c hadj p ih =>
    have hbComp : (b : Site d) ∈ componentIn S z := by
      rcases hu with ⟨hzS, haS, hza⟩
      have hab : ((lattice d).induce S).Reachable a b := SimpleGraph.Adj.reachable hadj
      exact ⟨hzS, b.property, hza.trans hab⟩
    obtain ⟨wp⟩ := ih hbComp hv
    have habComp : ((lattice d).induce (componentIn S z)).Adj ⟨a, hu⟩ ⟨b, hbComp⟩ := by
      simpa using hadj
    exact ⟨SimpleGraph.Walk.cons habComp wp⟩

/-- The source finite-hole property promotes an infinite connected set of good sites
to the unique infinite good-site component containing it. The maximal component
inherits the same hole bound by inclusion of complementary components. -/
theorem arxivUniqueMaximalGoodCluster {d : ℕ} (η : Site d → ℤ) (k : ℕ)
    {C : Set (Site d)} (hC : IsInfiniteConnectedGoodSet η k C)
    (hholes : RnHoleProp d C) (z : Site d) (hz : z ∈ C) :
    ∃ Cstar : Set (Site d),
      Cstar = componentIn (goodSites η k) z ∧
      IsInfiniteConnectedGoodSet η k Cstar ∧
      C ⊆ Cstar ∧
      (∀ D, IsInfiniteConnectedGoodSet η k D → D ⊆ Cstar) ∧
      (∀ D, D.Infinite → (∃ w ∈ goodSites η k, D = componentIn (goodSites η k) w) →
        D = Cstar) ∧
      RnHoleProp d Cstar ∧
      (∀ x, x ∉ Cstar →
        componentIn Cstarᶜ x ⊆ componentIn Cᶜ x) := by
  classical
  rcases hC with ⟨hCinf, hCgood, hCconn⟩
  let G : Set (Site d) := goodSites η k
  let Cstar : Set (Site d) := componentIn G z
  have hCstarG : Cstar ⊆ G := by
    intro y hy
    exact hy.2.1
  have hCsub : C ⊆ Cstar := by
    intro y hy
    exact rn_componentIn_mono hCgood z (hCconn z hz y hy)
  have hCstarInf : Cstar.Infinite := hCinf.mono hCsub
  have hCstarConn : ∀ x ∈ Cstar, ∀ y ∈ Cstar, y ∈ componentIn Cstar x := by
    intro x hx y hy
    have hxCstar : x ∈ Cstar := hx
    have hyCstar : y ∈ Cstar := hy
    rcases hx with ⟨hzG, hxG, hzx⟩
    rcases hy with ⟨_, hyG, hzy⟩
    have hxy : ((lattice d).induce G).Reachable ⟨x, hxG⟩ ⟨y, hyG⟩ := hzx.symm.trans hzy
    obtain ⟨p⟩ := hxy
    obtain ⟨q⟩ := arxiv_walk_lift_to_component p hxCstar hyCstar
    exact ⟨hxCstar, hyCstar, ⟨q⟩⟩
  have hCstarGood : IsInfiniteConnectedGoodSet η k Cstar :=
    ⟨hCstarInf, hCstarG, hCstarConn⟩
  have hmax : ∀ D, IsInfiniteConnectedGoodSet η k D → D ⊆ Cstar := by
    intro D hD
    rcases hD with ⟨hDinf, hDgood, hDconn⟩
    obtain ⟨a, haD, haC⟩ := arxiv_infinite_connected_intersects hholes hDinf hDconn
    intro y hyD
    have hay : a ∈ Cstar := hCsub haC
    have hya : y ∈ componentIn (goodSites η k) a :=
      rn_componentIn_mono hDgood a (hDconn a haD y hyD)
    rcases hay with ⟨hzG, haG, hza⟩
    rcases hya with ⟨_, hyG, hayReach⟩
    exact ⟨hzG, hyG, hza.trans hayReach⟩
  have huniq : ∀ D, D.Infinite →
      (∃ w ∈ G, D = componentIn G w) → D = Cstar := by
    intro D hDinf hDcomp
    obtain ⟨w, hwG, hDeq⟩ := hDcomp
    have hDinf' : (componentIn G w).Infinite := by
      rw [← hDeq]
      exact hDinf
    have hDgood : componentIn G w ⊆ G := by
      intro y hy
      exact hy.2.1
    have hDconn : ∀ x ∈ componentIn G w, ∀ y ∈ componentIn G w,
        y ∈ componentIn (componentIn G w) x := by
      intro x hx y hy
      have hxComp : x ∈ componentIn G w := hx
      have hyComp : y ∈ componentIn G w := hy
      rcases hx with ⟨_, hxG, hwx⟩
      rcases hy with ⟨_, hyG, hwy⟩
      have hxy : ((lattice d).induce G).Reachable ⟨x, hxG⟩ ⟨y, hyG⟩ :=
        hwx.symm.trans hwy
      obtain ⟨p⟩ := hxy
      obtain ⟨q⟩ := arxiv_walk_lift_to_component p hxComp hyComp
      exact ⟨hxComp, hyComp, ⟨q⟩⟩
    obtain ⟨a, haD, haC⟩ :=
      arxiv_infinite_connected_intersects hholes hDinf' hDconn
    have haStar : a ∈ Cstar := hCsub haC
    have hDa : componentIn G w = componentIn G a := arxiv_componentIn_eq_of_mem haD
    have hStarA : Cstar = componentIn G a := arxiv_componentIn_eq_of_mem haStar
    calc
      D = componentIn G w := hDeq
      _ = componentIn G a := hDa
      _ = Cstar := hStarA.symm
  refine ⟨Cstar, rfl, hCstarGood, hCsub, hmax, huniq, ?_, ?_⟩
  · exact rn_holeProp_mono hCsub hholes
  · intro x hx
    exact rn_componentIn_mono (Set.compl_subset_compl.mpr hCsub) x

end Exploding
