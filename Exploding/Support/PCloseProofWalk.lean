/-
Walks in the infinite cluster for the second inequality of Lemma 3.7: a ray
meets the infinite cluster within the hole volume, a finite chemical distance is
realised by a walk, and a walk of macroscopic cubes carries a microscopic path
through the corners of its cubes.
-/
import Exploding.Support.Vocab
import Exploding.Support.SubPub
import Exploding.Support.PCloseProofGeom

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- A ray of macroscopic sites starting inside `cent d n1` meets the infinite cluster
within `Z` steps, when every component of its complement meeting `cent d n1` has
fewer than `Z` points. -/
theorem pclose_ray_hit (Cinf : Set (Site d)) (Z n1 : ℕ)
    (hhole : ∀ y ∈ (cent d n1 : Set (Site d)), y ∉ Cinf →
      (componentIn Cinfᶜ y).Finite ∧ (componentIn Cinfᶜ y).ncard < Z)
    (s0 : Site d) (hs0 : s0 ∈ (cent d n1 : Set (Site d))) (i0 : Fin d) :
    ∃ r : ℕ, r ≤ Z ∧ s0 + (r : ℤ) • unit i0 ∈ Cinf := by
  by_contra hcon
  push Not at hcon
  have hray : ∀ j : ℕ, j ≤ Z → s0 + (j : ℤ) • unit i0 ∈ Cinfᶜ := fun j hj hmem =>
    hcon j hj hmem
  have hs0C : s0 ∉ Cinf := by
    have := hray 0 (Nat.zero_le Z)
    simpa using this
  obtain ⟨hfin, hcard⟩ := hhole s0 hs0 hs0C
  have hraycomp := aux_pub_nearest_ray Cinfᶜ s0 i0 Z hray
  have hpig := aux_pub_nearest_pigeonhole Cinfᶜ s0 i0 hfin Z hraycomp
  rw [← Set.ncard_eq_toFinset_card (componentIn Cinfᶜ s0) hfin] at hpig
  omega

/-- A finite chemical distance is realised by a walk. -/
theorem pclose_chem_walk (S : Set (Site d)) (x y : Site d) (m : ℕ)
    (h : chemDist S x y = (m : ℕ∞)) :
    ∃ c : ℕ → Site d, c 0 = x ∧ c m = y ∧ (∀ s, s ≤ m → c s ∈ S) ∧
      ∀ s, s < m → (lattice d).Adj (c s) (c (s + 1)) := by
  have hex : ∃ n : ℕ, ∃ (hx : x ∈ S) (hy : y ∈ S)
      (w : ((lattice d).induce S).Walk ⟨x, hx⟩ ⟨y, hy⟩), w.length = n := by
    by_contra hne
    have htop := sInf_coe_top
      (P := fun n : ℕ => ∃ (hx : x ∈ S) (hy : y ∈ S)
        (w : ((lattice d).induce S).Walk ⟨x, hx⟩ ⟨y, hy⟩), w.length = n) hne
    have : chemDist S x y = ⊤ := htop
    rw [this] at h
    exact absurd h (by simp)
  obtain ⟨n0, hP, hn0⟩ := sInf_coe_attained
    (P := fun n : ℕ => ∃ (hx : x ∈ S) (hy : y ∈ S)
      (w : ((lattice d).induce S).Walk ⟨x, hx⟩ ⟨y, hy⟩), w.length = n) hex
  have hmn : n0 = m := by
    have : chemDist S x y = (n0 : ℕ∞) := hn0
    rw [this] at h
    exact_mod_cast h
  subst hmn
  obtain ⟨hx, hy, w, hw⟩ := hP
  refine ⟨fun s => (w.getVert s).1, ?_, ?_, ?_, ?_⟩
  · simp
  · simp only
    rw [← hw, SimpleGraph.Walk.getVert_length]
  · intro s _
    exact (w.getVert s).2
  · intro s hs
    have := w.adj_getVert_succ (by rw [hw]; exact hs)
    simpa [SimpleGraph.induce_adj] using this

/-- The corner of the macroscopic cube `Q_k(c)`. -/
def pcloseCorner (k : ℕ) (c : Site d) : Site d := fun l => (k : ℤ) * c l + 1

theorem pclose_corner_mem (k : ℕ) (hk : 1 ≤ k) (c : Site d) :
    pcloseCorner k c - (k : ℤ) • c ∈ cube d k := by
  intro l
  simp only [pcloseCorner, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  constructor <;> linarith

/-- A macroscopic walk carries a microscopic path through the corners of its cubes,
of length at most `k` times the length of the walk, all of whose sites lie in the
cubes of the walk. -/
theorem pclose_corner_path (k : ℕ) (hk : 1 ≤ k) (c : ℕ → Site d) :
    ∀ m : ℕ, (∀ s, s < m → (lattice d).Adj (c s) (c (s + 1))) →
    ∃ (L : ℕ) (z : ℕ → Site d), L ≤ m * k ∧ z 0 = pcloseCorner k (c 0) ∧
      z L = pcloseCorner k (c m) ∧
      (∀ q, q < L → (lattice d).Adj (z q) (z (q + 1))) ∧
      ∀ q, q ≤ L → ∃ s, s ≤ m ∧ z q - (k : ℤ) • c s ∈ cube d k := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨0, fun _ => pcloseCorner k (c 0), by simp, rfl, rfl,
      fun q hq => absurd hq (Nat.not_lt_zero q), ?_⟩
    intro q hq
    refine ⟨0, le_rfl, ?_⟩
    have : q = 0 := by omega
    subst this
    exact pclose_corner_mem k hk (c 0)
  | succ m ih =>
    intro hadj
    obtain ⟨L, z, hL, hz0, hzL, hzadj, hzmem⟩ := ih (fun s hs => hadj s (by omega))
    obtain ⟨dir, hdir⟩ := hadj m (by omega)
    -- the segment from the corner of `c m` to the corner of `c (m + 1)`
    have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    -- `δ` is the unit step and `σ r` the point `r` steps along the segment
    obtain ⟨δ, hδ, hcδ⟩ : ∃ δ : Site d, (δ = unit dir ∨ δ = -unit dir) ∧
        pcloseCorner k (c (m + 1)) = pcloseCorner k (c m) + (k : ℤ) • δ := by
      rcases hdir with hdir | hdir
      · refine ⟨unit dir, Or.inl rfl, ?_⟩
        funext l
        simp only [pcloseCorner, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [hdir]
        simp only [Pi.add_apply]
        ring
      · refine ⟨-unit dir, Or.inr rfl, ?_⟩
        funext l
        simp only [pcloseCorner, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
        rw [hdir]
        simp only [Pi.add_apply]
        ring
    let σ : ℕ → Site d := fun r => pcloseCorner k (c m) + (r : ℤ) • δ
    have hσadj : ∀ r, (lattice d).Adj (σ r) (σ (r + 1)) := by
      intro r
      refine ⟨dir, ?_⟩
      rcases hδ with hδ | hδ
      · left
        simp only [σ, hδ]
        rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
        abel
      · right
        simp only [σ, hδ]
        rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
        abel
    refine ⟨L + k, fun q => if q ≤ L then z q else σ (q - L), by nlinarith, ?_, ?_, ?_, ?_⟩
    · simpa using hz0
    · have h1 : ¬ (L + k ≤ L) := by omega
      simp only [h1, if_false]
      simp only [σ, Nat.add_sub_cancel_left]
      exact hcδ.symm
    · intro q hq
      by_cases hqL : q < L
      · have h1 : q ≤ L := le_of_lt hqL
        have h2 : q + 1 ≤ L := hqL
        simpa [h1, h2] using hzadj q hqL
      · have hqL' : L ≤ q := not_lt.mp hqL
        by_cases hq0 : q = L
        · subst hq0
          simp only [le_refl, if_true, show ¬ (q + 1 ≤ q) from by omega, if_false]
          simp only [Nat.add_sub_cancel_left]
          have := hσadj 0
          have hσ0 : σ 0 = z q := by
            simp only [σ, Nat.cast_zero, zero_smul, add_zero]
            rw [← hzL]
          rw [hσ0] at this
          simpa using this
        · have h1 : ¬ q ≤ L := by omega
          have h2 : ¬ q + 1 ≤ L := by omega
          simp only [h1, h2, if_false]
          have h3 : q + 1 - L = (q - L) + 1 := by omega
          rw [h3]
          exact hσadj (q - L)
    · intro q hq
      by_cases hqL : q ≤ L
      · simp only [hqL, if_true]
        obtain ⟨s, hs, hmem⟩ := hzmem q hqL
        exact ⟨s, by omega, hmem⟩
      · simp only [hqL, if_false]
        set r := q - L with hr
        have hr1 : 1 ≤ r := by omega
        have hrk : r ≤ k := by omega
        rcases hδ with hδ | hδ
        · -- stepping up: the segment lies in `c m` until its last point
          by_cases hrk' : r < k
          · refine ⟨m, by omega, ?_⟩
            intro l
            have hc : (σ r - (k : ℤ) • c m) l = 1 + (r : ℤ) * (if l = dir then 1 else 0) := by
              simp only [σ, hδ, pcloseCorner, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
                smul_eq_mul, unit, Pi.single_apply]
              ring
            rw [hc]
            by_cases hl : l = dir
            · simp only [hl, if_true]
              have : (r : ℤ) + 1 ≤ (k : ℤ) := by exact_mod_cast hrk'
              constructor <;> nlinarith
            · simp only [hl, if_false, mul_zero, add_zero]
              exact ⟨le_rfl, hk1⟩
          · have hrk2 : r = k := by omega
            refine ⟨m + 1, le_rfl, ?_⟩
            have : σ r = pcloseCorner k (c (m + 1)) := by
              simp only [σ, hrk2]
              rw [hcδ, hδ]
            rw [this]
            exact pclose_corner_mem k hk (c (m + 1))
        · -- stepping down: the segment lies in `c (m + 1)`
          refine ⟨m + 1, le_rfl, ?_⟩
          intro l
          have hc : (σ r - (k : ℤ) • c (m + 1)) l =
              1 + ((k : ℤ) - r) * (if l = dir then 1 else 0) := by
            have hc1 : c m = c (m + 1) + unit dir := by
              rcases hdir with hdir | hdir
              · exfalso
                -- `c (m+1) = c m + unit dir` and `δ = -unit dir` are incompatible with `k ≥ 1`
                have h1 := congrFun hcδ dir
                simp only [pcloseCorner, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hδ,
                  Pi.neg_apply, unit, Pi.single_eq_same] at h1
                rw [hdir] at h1
                simp only [Pi.add_apply, unit, Pi.single_eq_same] at h1
                nlinarith
              · exact hdir
            simp only [σ, hδ, pcloseCorner, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
              smul_eq_mul, Pi.neg_apply, unit, Pi.single_apply, hc1]
            by_cases hl : l = dir <;> simp [hl] <;> ring
          rw [hc]
          by_cases hl : l = dir
          · simp only [hl, if_true]
            have h1 : (r : ℤ) ≤ (k : ℤ) := by exact_mod_cast hrk
            have h2 : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr1
            constructor <;> nlinarith
          · simp only [hl, if_false, mul_zero, add_zero]
            exact ⟨le_rfl, hk1⟩

end Exploding
