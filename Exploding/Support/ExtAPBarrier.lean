/-
The closed barrier around the open cluster of the negative face of a box.

Fix a dimension `d`, a box radius `n` and a direction `i`.  In the Bernoulli site
configuration `ω : Site d → Bool` a site is open when `ω` is `true`.  Let `xba_cluster`
be the open cluster inside the box `cent d n` grown from the site `xba_seed` of the
negative `i`-face, and let `xba_barrier` be the outer boundary of that cluster inside
the box.  The barrier is all closed; whenever the seed is open and the box has no open
crossing in direction `i`, the barrier is nonempty; and every nearest-neighbour path in
the box from the cluster to the positive `i`-face meets the barrier.
-/
import Exploding.Support.ExtBCBernoulli2

open Exploding LatticeProb MeasureTheory Filter
open scoped Classical Topology ENNReal

namespace Exploding

variable {d : ℕ}

/-- The site of the negative `i`-face of the box used as the seed of the open cluster:
coordinate `i` is `-n` and all other coordinates vanish. -/
def xba_seed (d n : ℕ) (i : Fin d) : Site d := fun j => if j = i then -(n : ℤ) else 0

theorem xba_seed_mem_cent (d n : ℕ) (i : Fin d) : xba_seed d n i ∈ cent d n := by
  intro j
  by_cases hj : j = i
  · subst hj
    simp [xba_seed]
  · simp [xba_seed, hj]

theorem xba_seed_neg (d n : ℕ) (i : Fin d) : xba_seed d n i i = -(n : ℤ) := by
  simp [xba_seed]

/-- A nearest-neighbour edge of the box whose two endpoints are open. -/
def xba_step (d n : ℕ) (ω : Site d → Bool) (a b : Site d) : Prop :=
  (lattice d).Adj a b ∧ a ∈ cent d n ∧ b ∈ cent d n ∧ ω a = true ∧ ω b = true

theorem xba_step_symm (d n : ℕ) (ω : Site d → Bool) {a b : Site d}
    (h : xba_step d n ω a b) : xba_step d n ω b a :=
  ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.2, h.2.2.2.1⟩

/-- The open cluster of the negative `i`-face seed inside the box: the sites of `cent d n`
that are open and joined to the seed by nearest-neighbour edges of the box between open
sites. -/
def xba_cluster (d n : ℕ) (i : Fin d) (ω : Site d → Bool) : Set (Site d) :=
  {x | x ∈ cent d n ∧ ω x = true ∧
    Relation.ReflTransGen (xba_step d n ω) (xba_seed d n i) x}

/-- The inner boundary of the open cluster inside the box: the sites of `cent d n` outside
the cluster that are nearest neighbours of a cluster site. -/
def xba_barrier (d n : ℕ) (i : Fin d) (ω : Site d → Bool) : Set (Site d) :=
  {z | z ∈ cent d n ∧ z ∉ xba_cluster d n i ω ∧
    ∃ y ∈ xba_cluster d n i ω, (lattice d).Adj z y}

theorem xba_cluster_subset_cent (d n : ℕ) (i : Fin d) (ω : Site d → Bool) :
    xba_cluster d n i ω ⊆ cent d n := fun _ hx => hx.1

theorem xba_cluster_open (d n : ℕ) (i : Fin d) (ω : Site d → Bool) :
    ∀ x ∈ xba_cluster d n i ω, ω x = true := fun _ hx => hx.2.1

theorem xba_cluster_conn (d n : ℕ) (i : Fin d) (ω : Site d → Bool) :
    ∀ x ∈ xba_cluster d n i ω, ∀ y ∈ xba_cluster d n i ω,
      Relation.ReflTransGen (xba_step d n ω) x y := by
  intro x hx y hy
  exact (xap_rtg_symm (fun a b hab => xba_step_symm d n ω hab) hx.2.2).trans hy.2.2

theorem xba_barrier_closed (d n : ℕ) (i : Fin d) (ω : Site d → Bool) :
    ∀ z ∈ xba_barrier d n i ω, ω z = false := by
  intro z hz
  obtain ⟨hzc, hznc, y, hy, hzy⟩ := hz
  cases hzval : ω z with
  | false => rfl
  | true =>
      exfalso
      have hstep : xba_step d n ω y z :=
        ⟨hzy.symm, xba_cluster_subset_cent d n i ω hy, hzc,
          xba_cluster_open d n i ω y hy, hzval⟩
      exact hznc ⟨hzc, hzval, hy.2.2.tail hstep⟩

theorem xba_seed_mem_cluster (d n : ℕ) (i : Fin d) (ω : Site d → Bool)
    (h : ω (xba_seed d n i) = true) : xba_seed d n i ∈ xba_cluster d n i ω :=
  ⟨xba_seed_mem_cent d n i, h, Relation.ReflTransGen.refl⟩

theorem xba_no_crossing_plus_disjoint (d n : ℕ) (i : Fin d) (ω : Site d → Bool)
    (hnc : ¬ xbc_Crosses d n i ω) :
    Disjoint (xba_cluster d n i ω) {y : Site d | y i = (n : ℤ)} := by
  rw [Set.disjoint_left]
  intro y hy hyface
  exact hnc ⟨xba_seed d n i, y, xba_seed_neg d n i, hyface, xba_seed_mem_cent d n i,
    xba_cluster_subset_cent d n i ω hy, hy.2.2⟩

/-- The straight path through the box along direction `i`, from the seed at coordinate
`-n` to coordinate `-n + k`. -/
def xba_axis (d n : ℕ) (i : Fin d) (k : ℕ) : Site d :=
  fun j => if j = i then -(n : ℤ) + (k : ℤ) else 0

theorem xba_axis_zero (d n : ℕ) (i : Fin d) : xba_axis d n i 0 = xba_seed d n i := by
  funext j
  by_cases hj : j = i <;> simp [xba_axis, xba_seed, hj]

theorem xba_axis_mem_cent (d n : ℕ) (i : Fin d) {k : ℕ} (hk : k ≤ 2 * n) :
    xba_axis d n i k ∈ cent d n := by
  intro j
  by_cases hj : j = i
  · subst hj
    simp only [xba_axis, if_true]
    rw [abs_le]
    constructor <;> omega
  · simp [xba_axis, hj]

theorem xba_axis_succ (d n : ℕ) (i : Fin d) (k : ℕ) :
    xba_axis d n i (k + 1) = xba_axis d n i k + unit i := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp only [xba_axis, if_true, Pi.add_apply, unit, Pi.single_eq_same]
    push_cast
    ring
  · simp [xba_axis, unit, hj]

theorem xba_axis_adj (d n : ℕ) (i : Fin d) (k : ℕ) :
    (lattice d).Adj (xba_axis d n i k) (xba_axis d n i (k + 1)) :=
  ⟨i, Or.inl (xba_axis_succ d n i k)⟩

theorem xba_axis_end (d n : ℕ) (i : Fin d) : xba_axis d n i (2 * n) i = (n : ℤ) := by
  simp only [xba_axis, if_true]
  push_cast
  ring

theorem xba_path_cluster_or_barrier (d n : ℕ) (i : Fin d) (ω : Site d → Bool)
    {γ : ℕ → Site d} {m : ℕ} (hstart : γ 0 ∈ xba_cluster d n i ω)
    (hcent : ∀ k ≤ m, γ k ∈ cent d n)
    (hadj : ∀ k < m, (lattice d).Adj (γ k) (γ (k + 1))) :
    ∀ k ≤ m, γ k ∈ xba_cluster d n i ω ∨
      ∃ j ≤ k, γ j ∈ xba_barrier d n i ω := by
  intro k
  induction k with
  | zero =>
      intro _
      exact Or.inl hstart
  | succ k ih =>
      intro hk
      have hk' : k ≤ m := by omega
      rcases ih hk' with hmem | ⟨j, hjle, hbar⟩
      · by_cases hnext : γ (k + 1) ∈ xba_cluster d n i ω
        · exact Or.inl hnext
        · refine Or.inr ⟨k + 1, le_refl _, ?_⟩
          exact ⟨hcent (k + 1) hk, hnext, γ k, hmem, (hadj k (by omega)).symm⟩
      · exact Or.inr ⟨j, by omega, hbar⟩

theorem xba_barrier_nonempty (d n : ℕ) (i : Fin d) (ω : Site d → Bool)
    (hseed : xba_seed d n i ∈ xba_cluster d n i ω)
    (hnc : ¬ xbc_Crosses d n i ω) : (xba_barrier d n i ω).Nonempty := by
  have hpath := xba_path_cluster_or_barrier d n i ω (γ := xba_axis d n i) (m := 2 * n)
    (by rw [xba_axis_zero]; exact hseed)
    (fun k hk => xba_axis_mem_cent d n i hk) (fun k _ => xba_axis_adj d n i k)
    (2 * n) le_rfl
  rcases hpath with hmem | hbar
  · exact absurd (xba_axis_end d n i)
      (Set.disjoint_left.mp (xba_no_crossing_plus_disjoint d n i ω hnc) hmem)
  · exact ⟨xba_axis d n i hbar.choose, hbar.choose_spec.2⟩

theorem xba_barrier_separates (d n : ℕ) (i : Fin d) (ω : Site d → Bool)
    (hnc : ¬ xbc_Crosses d n i ω) {γ : ℕ → Site d} {m : ℕ}
    (hstart : γ 0 ∈ xba_cluster d n i ω)
    (hcent : ∀ k ≤ m, γ k ∈ cent d n)
    (hadj : ∀ k < m, (lattice d).Adj (γ k) (γ (k + 1)))
    (hend : γ m i = (n : ℤ)) :
    ∃ k ≤ m, γ k ∈ xba_barrier d n i ω := by
  rcases xba_path_cluster_or_barrier d n i ω hstart hcent hadj m le_rfl with hmem | hbar
  · exact absurd hend
      (Set.disjoint_left.mp (xba_no_crossing_plus_disjoint d n i ω hnc) hmem)
  · exact hbar

end Exploding
