/-
Support for Lemma 3.6 of `paper/exploding.tex`: the hole step.  A finite component
of the complement of the infinite cluster is surrounded by cubes of the cluster; once those are
lit, the region inside is lit within its own diameter.
-/
import Exploding.Support.PUBProofB

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-! ### Distance inside a finite component -/

theorem pub_adj_mnorm {a b : Site d} (h : (lattice d).Adj a b) : mnorm (b - a) = 1 := by
  obtain ⟨i, hi | hi⟩ := h
  · have : b - a = unit i := by rw [hi]; abel
    rw [this]
    exact aux_finite_exploding_mnorm_unit i
  · have : b - a = -(unit i) := by rw [hi]; abel
    rw [this, pub_mnorm_neg]
    exact aux_finite_exploding_mnorm_unit i

theorem pub_walk_mnorm_le {S : Set (Site d)} {u v : S} (p : ((lattice d).induce S).Walk u v) :
    mnorm ((v : Site d) - (u : Site d)) ≤ p.length := by
  induction p with
  | nil => simp [mnorm]
  | @cons a b c h p ih =>
    rw [SimpleGraph.Walk.length_cons]
    have hadj : (lattice d).Adj (a : Site d) (b : Site d) := SimpleGraph.induce_adj.mp h
    have h1 := pub_adj_mnorm hadj
    have := pub_mnorm_add_le ((c : Site d) - (b : Site d)) ((b : Site d) - (a : Site d))
    rw [show (c : Site d) - (b : Site d) + ((b : Site d) - (a : Site d)) = (c : Site d) - (a : Site d)
      by abel] at this
    push_cast
    linarith

/-- A point of a finite component is, in the Manhattan norm, closer to the base point than the
cardinality of the component. -/
theorem pub_dist_lt_ncard (S : Set (Site d)) (a : Site d) (hfin : (componentIn S a).Finite)
    {h : Site d} (hh : h ∈ componentIn S a) :
    mnorm (h - a) < ((componentIn S a).ncard : ℤ) := by
  classical
  obtain ⟨ha', hh', ⟨p⟩⟩ := hh
  set q := p.bypass with hqdef
  have hq : q.IsPath := p.bypass_isPath
  have hreach : ∀ v ∈ q.support, (v : Site d) ∈ componentIn S a := by
    intro v hv
    obtain ⟨q1, _, _⟩ := (SimpleGraph.Walk.mem_support_iff_exists_append).mp hv
    exact ⟨ha', v.2, ⟨q1⟩⟩
  have hnodup : (q.support.map Subtype.val).Nodup := hq.support_nodup.map Subtype.val_injective
  have hcard : (q.support.map Subtype.val).toFinset.card = q.length + 1 := by
    rw [List.toFinset_card_of_nodup hnodup]
    simp [SimpleGraph.Walk.length_support]
  have hsub : (q.support.map Subtype.val).toFinset ⊆ hfin.toFinset := by
    intro y hy
    simp only [List.mem_toFinset, List.mem_map] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    exact hfin.mem_toFinset.mpr (hreach v hv)
  have hle := Finset.card_le_card hsub
  rw [hcard, ← Set.ncard_eq_toFinset_card _ hfin] at hle
  have hm := pub_walk_mnorm_le q
  have : (q.length : ℤ) + 1 ≤ ((componentIn S a).ncard : ℤ) := by exact_mod_cast hle
  simp only at hm
  linarith

/-! ### The coordinate sum -/

theorem pub_sigma_sub (a b : Site d) : pub_sigma (a - b) = pub_sigma a - pub_sigma b := by
  simp [pub_sigma, Finset.sum_sub_distrib]

theorem pub_sigma_add (a b : Site d) : pub_sigma (a + b) = pub_sigma a + pub_sigma b := by
  simp [pub_sigma, Finset.sum_add_distrib]

theorem pub_sigma_smul (c : ℤ) (a : Site d) : pub_sigma (c • a) = c * pub_sigma a := by
  simp [pub_sigma, Finset.mul_sum]

theorem pub_sigma_le_mnorm (a : Site d) : pub_sigma a ≤ mnorm a :=
  Finset.sum_le_sum fun _ _ => le_abs_self _

theorem pub_sigma_cube {k : ℕ} {u : Site d} (hu : u ∈ cube d k) :
    (d : ℤ) ≤ pub_sigma u ∧ pub_sigma u ≤ (d : ℤ) * k := by
  constructor
  · calc (d : ℤ) = ∑ _l : Fin d, (1 : ℤ) := by simp
      _ ≤ pub_sigma u := Finset.sum_le_sum fun l _ => (hu l).1
  · calc pub_sigma u ≤ ∑ _l : Fin d, (k : ℤ) := Finset.sum_le_sum fun l _ => (hu l).2
      _ = (d : ℤ) * k := by simp

/-! ### The hole step -/

theorem pub_macro_adj (k : ℕ) (hk : 1 ≤ k) {y u : Site d} (hadj : (lattice d).Adj y u) :
    Exploding.macroIdx k y = Exploding.macroIdx k u ∨
      (lattice d).Adj (Exploding.macroIdx k y) (Exploding.macroIdx k u) := by
  obtain ⟨l, hu | hy⟩ := hadj
  · have h1 : Exploding.macroIdx k (y + unit l) = Exploding.macroIdx k y ∨
        (lattice d).Adj (Exploding.macroIdx k (y + unit l)) (Exploding.macroIdx k y) :=
      (macroIdx_adj k hk y l).1
    rw [← hu] at h1
    rcases h1 with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · have h1 : Exploding.macroIdx k (u + unit l) = Exploding.macroIdx k u ∨
        (lattice d).Adj (Exploding.macroIdx k (u + unit l)) (Exploding.macroIdx k u) :=
      (macroIdx_adj k hk u l).1
    rw [← hy] at h1
    exact h1

/-- **The hole step.**  If the cubes of the infinite cluster within reach of a finite hole are lit
at time `τ`, then every site of the hole is lit by time `τ + k (d + r) + 1`, where `r` bounds the
hole's size: the sites of the hole have their outer boundary lit, and a site whose upper
neighbours are lit is lit. -/
theorem pub_hole_lit (hd : 2 ≤ d) (η : Site d → ℤ) (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x)
    (N : ℕ) (hN : 1 ≤ N) (k : ℕ) (hk : 1 ≤ k) (Cinf : Set (Site d)) (x : Site d)
    (hx : Exploding.macroIdx k x ∉ Cinf)
    (hfin : (componentIn Cinfᶜ (Exploding.macroIdx k x)).Finite) (r : ℕ)
    (hr : (componentIn Cinfᶜ (Exploding.macroIdx k x)).ncard ≤ r) (τ : ℕ)
    (hcov : ∀ b ∈ Cinf, mnorm (b - Exploding.macroIdx k x) ≤ (r : ℤ) →
      ∀ u ∈ cube d k, 0 < wave η N (0 : Site d) τ (u + (k : ℤ) • b)) :
    0 < wave η N (0 : Site d) (τ + k * (d + r) + 1) x := by
  classical
  have hd2 : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by linarith
  have hlow0 : ∀ x, 0 ≤ η x := fun x => by linarith [hlow x]
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  set i := Exploding.macroIdx k x with hi
  set H := componentIn Cinfᶜ i with hH
  set V : Set (Site d) := {u | Exploding.macroIdx k u ∈ H} with hV
  have hiH : i ∈ H := ⟨hx, hx, SimpleGraph.Reachable.refl _⟩
  have hxV : x ∈ V := hiH
  have hcube : ∀ u, u - (k : ℤ) • Exploding.macroIdx k u ∈ cube d k :=
    fun u => mem_cube_of_macroIdx k hk u
  have hdist : ∀ h ∈ H, mnorm (h - i) + 1 ≤ (r : ℤ) := by
    intro h hh
    have := pub_dist_lt_ncard Cinfᶜ i hfin hh
    change mnorm (h - i) < ((H.ncard : ℕ) : ℤ) at this
    have hr' : ((H.ncard : ℕ) : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
    omega
  have hsig : ∀ u : Site d, pub_sigma u = pub_sigma (u - (k : ℤ) • Exploding.macroIdx k u) +
      (k : ℤ) * pub_sigma (Exploding.macroIdx k u) := by
    intro u
    have e : u = (u - (k : ℤ) • Exploding.macroIdx k u) + (k : ℤ) • Exploding.macroIdx k u := by
      abel
    have := congrArg pub_sigma e
    rw [pub_sigma_add, pub_sigma_smul] at this
    exact this
  set B : ℤ := (d : ℤ) * k + k * (pub_sigma i + r) with hB
  have hBV : ∀ v ∈ V, pub_sigma v ≤ B := by
    intro v hv
    have hh : Exploding.macroIdx k v ∈ H := hv
    have h1 := (pub_sigma_cube (hcube v)).2
    have h2 : pub_sigma (Exploding.macroIdx k v) ≤ pub_sigma i + r := by
      have h3 := pub_sigma_le_mnorm (Exploding.macroIdx k v - i)
      rw [pub_sigma_sub] at h3
      have h4 := hdist _ hh
      linarith
    have h5 := hsig v
    nlinarith
  have hbd : ∀ y ∈ outerBoundary V, 0 < wave η N (0 : Site d) τ y := by
    intro y hy
    obtain ⟨hyV, u, huV, hadj⟩ := hy
    have hhH : Exploding.macroIdx k u ∈ H := huV
    have hbH : Exploding.macroIdx k y ∉ H := hyV
    have hmadj : (lattice d).Adj (Exploding.macroIdx k y) (Exploding.macroIdx k u) := by
      rcases pub_macro_adj k hk hadj with h | h
      · exact absurd (h ▸ hhH) hbH
      · exact h
    have hbC : Exploding.macroIdx k y ∈ Cinf := by
      by_contra hb
      apply hbH
      obtain ⟨hiC, hhC, hreach⟩ := hhH
      exact ⟨hiC, hb, hreach.trans
        (SimpleGraph.Adj.reachable (SimpleGraph.induce_adj.mpr hmadj.symm))⟩
    have hn1 : mnorm (Exploding.macroIdx k y - Exploding.macroIdx k u) = 1 :=
      pub_adj_mnorm hmadj.symm
    have hn2 := hdist _ hhH
    have hn3 := pub_mnorm_sub_le (Exploding.macroIdx k y) (Exploding.macroIdx k u) i
    have := hcov _ hbC (by linarith) _ (hcube y)
    rwa [sub_add_cancel] at this
  have hfill := pub_fill hd η hlow N hN 0 V B hBV τ hbd (B - pub_sigma x + 1).toNat x
    (by
      have := Int.self_le_toNat (B - pub_sigma x + 1)
      omega) (Or.inl hxV)
  have hxs : (d : ℤ) + k * pub_sigma i ≤ pub_sigma x := by
    have h1 := (pub_sigma_cube (hcube x)).1
    have h2 := hsig x
    have h3 : Exploding.macroIdx k x = i := rfl
    rw [h3] at h2
    linarith
  have hj : (B - pub_sigma x + 1).toNat ≤ k * (d + r) + 1 := by
    rw [Int.toNat_le]
    push_cast
    have : (d : ℤ) ≥ 0 := by positivity
    nlinarith
  exact lt_of_lt_of_le hfill (wave_mono_time η hlow0 hd0 N 0 (by omega) x)

end Exploding
