/-
The planar bonds of `ℤ^d` used in the Peierls estimate for bond percolation: the bond joining
two adjacent sites of the plane spanned by the first two coordinates, the open cluster of the
origin in the plane, and the fact that a closed bond lies across the boundary of that cluster.
-/
import Exploding.Support.ECProofMain
import Exploding.Support.Percolation

namespace Exploding

open LatticeProb MeasureTheory Relation

variable {d : ℕ}

/-! ### The bond between two adjacent planar sites -/

/-- The bond of `ℤ^d` between two adjacent sites `a`, `z` of the plane: it is indexed by its
lower endpoint and its direction. -/
def pe_bnd (hd : 2 ≤ d) (a z : ℤ × ℤ) : Site d × Fin d :=
  (ec_emb d (min a.1 z.1, min a.2 z.2), if a.1 = z.1 then ⟨1, by omega⟩ else ⟨0, by omega⟩)

theorem pe_bnd_comm (hd : 2 ≤ d) (a z : ℤ × ℤ) : pe_bnd hd a z = pe_bnd hd z a := by
  unfold pe_bnd
  rw [min_comm a.1 z.1, min_comm a.2 z.2]
  by_cases h : a.1 = z.1
  · simp [h]
  · simp [h, Ne.symm h]

theorem pe_emb_inj (hd : 2 ≤ d) : Function.Injective (ec_emb d) := by
  intro z z' h
  have h0 := congrFun h ⟨0, by omega⟩
  have h1 := congrFun h ⟨1, by omega⟩
  simp only [ec_emb] at h0 h1
  simp at h0 h1
  exact Prod.ext h0 h1

/-- Two adjacent pairs of planar sites with the same bond are equal or reversed. -/
theorem pe_bnd_inj (hd : 2 ≤ d) {a z a' z' : ℤ × ℤ} (h : ec_adj4 a z) (h' : ec_adj4 a' z')
    (hb : pe_bnd hd a z = pe_bnd hd a' z') : (a = a' ∧ z = z') ∨ (a = z' ∧ z = a') := by
  unfold pe_bnd at hb
  obtain ⟨hb1, hb2⟩ := Prod.mk.inj hb
  have h1 := pe_emb_inj hd hb1
  simp only [Prod.mk.injEq] at h1
  obtain ⟨a1, a2⟩ := a
  obtain ⟨z1, z2⟩ := z
  obtain ⟨a1', a2'⟩ := a'
  obtain ⟨z1', z2'⟩ := z'
  rw [ec_adj4_iff] at h h'
  simp only [Prod.mk_add_mk, Prod.mk.injEq] at h h'
  simp only at h1 hb2
  simp only [Prod.mk.injEq]
  rcases h with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;>
    rcases h' with ⟨h3', h4'⟩ | ⟨h3', h4'⟩ | ⟨h3', h4'⟩ | ⟨h3', h4'⟩ <;>
    subst h1' h2' h3' h4' <;> simp at hb2 h1 <;> omega

/-! ### The open cluster of the origin in the plane -/

/-- The bond between adjacent planar sites `a`, `z` is open in `ω`. -/
def pe_open (hd : 2 ≤ d) (ω : Site d × Fin d → Bool) (a z : ℤ × ℤ) : Prop :=
  ec_adj4 a z ∧ ω (pe_bnd hd a z) = true

/-- The open cluster of the origin in the plane spanned by the first two coordinates. -/
def pe_cluster (hd : 2 ≤ d) (ω : Site d × Fin d → Bool) : Set (ℤ × ℤ) :=
  {z | ReflTransGen (pe_open hd ω) (0, 0) z}

theorem pe_bnd_east (hd : 2 ≤ d) (a : ℤ × ℤ) :
    pe_bnd hd a (a + (1, 0)) = (ec_emb d a, ⟨0, by omega⟩) := by
  simp [pe_bnd]

theorem pe_bnd_north (hd : 2 ≤ d) (a : ℤ × ℤ) :
    pe_bnd hd a (a + (0, 1)) = (ec_emb d a, ⟨1, by omega⟩) := by
  simp [pe_bnd]

theorem pe_adj_east (hd : 2 ≤ d) {ω : Site d × Fin d → Bool} {a : ℤ × ℤ}
    (hω : ω (pe_bnd hd a (a + (1, 0))) = true) :
    (openBondGraph ω).Adj (ec_emb d a) (ec_emb d (a + (1, 0))) := by
  rw [pe_bnd_east] at hω
  rw [openBondGraph, SimpleGraph.fromRel_adj]
  refine ⟨fun e => ?_, Or.inl ⟨⟨0, by omega⟩, by rw [ec_emb_add, ec_emb_e0 hd], hω⟩⟩
  have := pe_emb_inj hd e
  simp [Prod.ext_iff] at this

theorem pe_adj_north (hd : 2 ≤ d) {ω : Site d × Fin d → Bool} {a : ℤ × ℤ}
    (hω : ω (pe_bnd hd a (a + (0, 1))) = true) :
    (openBondGraph ω).Adj (ec_emb d a) (ec_emb d (a + (0, 1))) := by
  rw [pe_bnd_north] at hω
  rw [openBondGraph, SimpleGraph.fromRel_adj]
  refine ⟨fun e => ?_, Or.inl ⟨⟨1, by omega⟩, by rw [ec_emb_add, ec_emb_e1 hd], hω⟩⟩
  have := pe_emb_inj hd e
  simp [Prod.ext_iff] at this

theorem pe_adj (hd : 2 ≤ d) {ω : Site d × Fin d → Bool} {a z : ℤ × ℤ} (h : pe_open hd ω a z) :
    (openBondGraph ω).Adj (ec_emb d a) (ec_emb d z) := by
  obtain ⟨hadj, hω⟩ := h
  rcases (ec_adj4_iff a z).1 hadj with h | h | h | h
  · subst h
    exact pe_adj_east hd hω
  · have e : z + (1, 0) = a := by rw [h]; ext <;> simp
    have h2 := pe_adj_east hd (ω := ω) (a := z) (by rw [e, pe_bnd_comm]; exact hω)
    rw [e] at h2
    exact h2.symm
  · subst h
    exact pe_adj_north hd hω
  · have e : z + (0, 1) = a := by rw [h]; ext <;> simp
    have h2 := pe_adj_north hd (ω := ω) (a := z) (by rw [e, pe_bnd_comm]; exact hω)
    rw [e] at h2
    exact h2.symm

theorem pe_reach (hd : 2 ≤ d) (ω : Site d × Fin d → Bool) {z : ℤ × ℤ} (hz : z ∈ pe_cluster hd ω) :
    (openBondGraph ω).Reachable 0 (ec_emb d z) := by
  induction hz with
  | refl => rw [ec_emb_zero]
  | tail _ hbc ih => exact ih.trans (pe_adj hd hbc).reachable

theorem pe_cluster_finite (hd : 2 ≤ d) (ω : Site d × Fin d → Bool)
    (h : {x : Site d | (openBondGraph ω).Reachable 0 x}.Finite) : (pe_cluster hd ω).Finite :=
  (h.preimage (pe_emb_inj hd).injOn).subset (fun _ hz => pe_reach hd ω hz)

/-- A bond between a site of the cluster and a site off it is closed. -/
theorem pe_closed (hd : 2 ≤ d) (ω : Site d × Fin d → Bool) {a z : ℤ × ℤ}
    (ha : a ∈ pe_cluster hd ω) (hz : z ∉ pe_cluster hd ω) (hadj : ec_adj4 a z) :
    ω (pe_bnd hd a z) = false := by
  by_contra h
  exact hz (ReflTransGen.tail ha ⟨hadj, by simpa using h⟩)

/-! ### Bonds along a chain -/

/-- The four nearest-neighbour offsets of the plane. -/
def pe_offs : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1)}

open Classical in
/-- The four planar bonds at a site. -/
noncomputable def pe_bondsAt (hd : 2 ≤ d) (z : ℤ × ℤ) : Finset (Site d × Fin d) :=
  pe_offs.image (fun o => pe_bnd hd z (z + o))

theorem pe_bondsAt_card (hd : 2 ≤ d) (z : ℤ × ℤ) : (pe_bondsAt hd z).card ≤ 4 := by
  classical
  unfold pe_bondsAt
  refine Finset.card_image_le.trans ?_
  decide

theorem pe_mem_bondsAt (hd : 2 ≤ d) {a z : ℤ × ℤ} (h : ec_adj4 a z) :
    pe_bnd hd a z ∈ pe_bondsAt hd z := by
  classical
  unfold pe_bondsAt
  rw [Finset.mem_image, pe_bnd_comm]
  have h' := (ec_adj4_iff z a).1 (ec_adj4_symm h)
  refine ⟨a - z, ?_, by rw [add_sub_cancel]⟩
  simp only [pe_offs, Finset.mem_insert, Finset.mem_singleton]
  rcases h' with h' | h' | h' | h' <;> subst h' <;> simp

open Classical in
/-- The planar bonds at the sites of a list. -/
noncomputable def pe_lam (hd : 2 ≤ d) (l : List (ℤ × ℤ)) : Finset (Site d × Fin d) :=
  l.toFinset.biUnion (pe_bondsAt hd)

theorem pe_lam_card (hd : 2 ≤ d) (l : List (ℤ × ℤ)) : (pe_lam hd l).card ≤ 4 * l.length := by
  classical
  unfold pe_lam
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ z ∈ l.toFinset, (pe_bondsAt hd z).card ≤ ∑ _z ∈ l.toFinset, 4 :=
        Finset.sum_le_sum (fun z _ => pe_bondsAt_card hd z)
    _ = l.toFinset.card * 4 := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ l.length * 4 := Nat.mul_le_mul_right _ (List.toFinset_card_le l)
    _ = 4 * l.length := by ring

open Classical in
/-- The event that at least `l.length` of the planar bonds at the sites of `l` are closed. -/
def pe_E (hd : 2 ≤ d) (l : List (ℤ × ℤ)) : Set (Site d × Fin d → Bool) :=
  {ω | l.length ≤ ((pe_lam hd l).filter (fun b => ω b = false)).card}

/-- The boundary of the cluster carries one closed bond per vertex of a chain of distinct
boundary vertices. -/
theorem pe_E_of_boundary (hd : 2 ≤ d) (ω : Site d × Fin d → Bool) (l : List (ℤ × ℤ))
    (hl : l.Nodup)
    (hz : ∀ z ∈ l, z ∉ pe_cluster hd ω ∧ ∃ a ∈ pe_cluster hd ω, ec_adj4 a z) :
    ω ∈ pe_E hd l := by
  classical
  have hz' : ∀ z ∈ l, ∃ a, a ∈ pe_cluster hd ω ∧ ec_adj4 a z := fun z hzl => by
    obtain ⟨_, a, ha, hadj⟩ := hz z hzl
    exact ⟨a, ha, hadj⟩
  choose! a ha using hz'
  have hcard : l.toFinset.card ≤ ((pe_lam hd l).filter (fun b => ω b = false)).card := by
    refine Finset.card_le_card_of_injOn (fun z => pe_bnd hd (a z) z) ?_ ?_
    · intro z hzl
      have hzl' : z ∈ l := List.mem_toFinset.1 hzl
      simp only [Finset.coe_filter, Set.mem_setOf_eq]
      refine ⟨?_, pe_closed hd ω (ha z hzl').1 (hz z hzl').1 (ha z hzl').2⟩
      unfold pe_lam
      exact Finset.mem_biUnion.2 ⟨z, hzl, pe_mem_bondsAt hd (ha z hzl').2⟩
    · intro z hzl z' hzl' hbb
      have hzl1 : z ∈ l := List.mem_toFinset.1 hzl
      have hzl2 : z' ∈ l := List.mem_toFinset.1 hzl'
      rcases pe_bnd_inj hd (ha z hzl1).2 (ha z' hzl2).2 hbb with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact h2
      · exact absurd (h1 ▸ (ha z hzl1).1) (hz z' hzl2).1
  rw [List.toFinset_card_of_nodup hl] at hcard
  exact hcard

/-! ### Closed bonds -/

theorem pe_bitLaw_univ {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : bitLaw q Set.univ = 1 := by
  simp only [bitLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  simp

theorem pe_bitLaw_false (q : ℝ) : bitLaw q {false} = ENNReal.ofReal (1 - q) := by
  simp [bitLaw]

/-- Distinct bonds are closed independently, each with probability `1 - q`. -/
theorem pe_closed_prob {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (S : Finset (Site d × Fin d)) :
    bondPercolation d q {ω | ∀ b ∈ S, ω b = false} = ENNReal.ofReal (1 - q) ^ S.card := by
  haveI : IsProbabilityMeasure (bitLaw q) := ⟨pe_bitLaw_univ h0 h1⟩
  have hset : {ω : Site d × Fin d → Bool | ∀ b ∈ S, ω b = false} =
      Set.pi (↑S : Set (Site d × Fin d)) (fun _ => ({false} : Set Bool)) := by
    ext ω
    simp
  unfold bondPercolation
  rw [hset, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  simp [pe_bitLaw_false]

/-- The chance of `l.length` closed bonds among the planar bonds at the sites of `l`. -/
theorem pe_E_prob (hd : 2 ≤ d) {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (l : List (ℤ × ℤ)) :
    bondPercolation d q (pe_E hd l) ≤ ENNReal.ofReal (16 * (1 - q)) ^ l.length := by
  classical
  set Λ := pe_lam hd l with hΛ
  set 𝒮 := Λ.powerset.filter (fun S => S.card = l.length) with h𝒮
  have hsub : pe_E hd l ⊆ ⋃ S ∈ 𝒮, {ω : Site d × Fin d → Bool | ∀ b ∈ S, ω b = false} := by
    intro ω hω
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨S, Finset.mem_filter.2 ⟨Finset.mem_powerset.2
      (hSsub.trans (Finset.filter_subset _ _)), hScard⟩, fun b hb => ?_⟩
    exact (Finset.mem_filter.1 (hSsub hb)).2
  have h𝒮card : 𝒮.card ≤ 16 ^ l.length := by
    calc 𝒮.card ≤ Λ.powerset.card := Finset.card_filter_le _ _
      _ = 2 ^ Λ.card := Finset.card_powerset _
      _ ≤ 2 ^ (4 * l.length) := Nat.pow_le_pow_right (by norm_num) (pe_lam_card hd l)
      _ = 16 ^ l.length := by rw [pow_mul]; norm_num
  calc bondPercolation d q (pe_E hd l)
      ≤ bondPercolation d q (⋃ S ∈ 𝒮, {ω : Site d × Fin d → Bool | ∀ b ∈ S, ω b = false}) :=
        measure_mono hsub
    _ ≤ ∑ S ∈ 𝒮, bondPercolation d q {ω : Site d × Fin d → Bool | ∀ b ∈ S, ω b = false} :=
        measure_biUnion_finset_le _ _
    _ = ∑ _S ∈ 𝒮, ENNReal.ofReal (1 - q) ^ l.length := by
        refine Finset.sum_congr rfl (fun S hS => ?_)
        rw [pe_closed_prob h0 h1, (Finset.mem_filter.1 hS).2]
    _ = (𝒮.card : ENNReal) * ENNReal.ofReal (1 - q) ^ l.length := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (16 : ENNReal) ^ l.length * ENNReal.ofReal (1 - q) ^ l.length := by
        gcongr
        calc (𝒮.card : ENNReal) ≤ ((16 ^ l.length : ℕ) : ENNReal) := by exact_mod_cast h𝒮card
          _ = 16 ^ l.length := by push_cast; rfl
    _ = ENNReal.ofReal (16 * (1 - q)) ^ l.length := by
        rw [← mul_pow, ENNReal.ofReal_mul (by norm_num)]
        simp

/-! ### The Peierls sum -/

open Classical in
/-- The event that, for some nodup king-move chain of `j + 3 + i` sites from `(j + 1, 0)`,
at least one closed planar bond per site lies at the chain. -/
noncomputable def pe_badSet (hd : 2 ≤ d) (j i : ℕ) : Set (Site d × Fin d → Bool) :=
  ⋃ l ∈ (ec_paths (j + 2 + i) ((j : ℤ) + 1, 0)).filter List.Nodup, pe_E hd l

theorem pe_badSet_prob (hd : 2 ≤ d) {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (j i : ℕ) :
    bondPercolation d q (pe_badSet hd j i) ≤
      (8 : ENNReal) ^ (j + 2 + i) * ENNReal.ofReal (16 * (1 - q)) ^ (j + 2 + i + 1) := by
  classical
  set F := (ec_paths (j + 2 + i) ((j : ℤ) + 1, 0)).filter List.Nodup with hF
  unfold pe_badSet
  calc bondPercolation d q (⋃ l ∈ F, pe_E hd l)
      ≤ ∑ l ∈ F, bondPercolation d q (pe_E hd l) := measure_biUnion_finset_le _ _
    _ ≤ ∑ l ∈ F, ENNReal.ofReal (16 * (1 - q)) ^ (j + 2 + i + 1) := by
        refine Finset.sum_le_sum (fun l hl => ?_)
        obtain ⟨hlp, _⟩ := Finset.mem_filter.1 hl
        have := pe_E_prob hd h0 h1 l
        rwa [ec_paths_length _ _ l hlp] at this
    _ = (F.card : ENNReal) * ENNReal.ofReal (16 * (1 - q)) ^ (j + 2 + i + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (8 : ENNReal) ^ (j + 2 + i) * ENNReal.ofReal (16 * (1 - q)) ^ (j + 2 + i + 1) := by
        gcongr
        have h1 : F.card ≤ 8 ^ (j + 2 + i) :=
          (Finset.card_filter_le _ _).trans (ec_paths_card _ _)
        calc (F.card : ENNReal) ≤ ((8 ^ (j + 2 + i) : ℕ) : ENNReal) := by exact_mod_cast h1
          _ = 8 ^ (j + 2 + i) := by push_cast; rfl

/-- If the origin has a finite open cluster in the plane, some chain event occurs. -/
theorem pe_cover (hd : 2 ≤ d) (ω : Site d × Fin d → Bool)
    (h : {x : Site d | (openBondGraph ω).Reachable 0 x}.Finite) :
    ω ∈ ⋃ j : ℕ, ⋃ i : ℕ, pe_badSet hd j i := by
  classical
  obtain ⟨j, l, hnd, hch, hhd, hlen, hz⟩ :=
    ec_top (pe_cluster hd ω) (pe_cluster_finite hd ω h) ReflTransGen.refl
  obtain ⟨i, hi⟩ : ∃ i, l.length = j + 2 + i + 1 := ⟨l.length - (j + 3), by omega⟩
  refine Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨i, ?_⟩⟩
  unfold pe_badSet
  simp only [Set.mem_iUnion]
  exact ⟨l, Finset.mem_filter.2 ⟨ec_mem_paths _ _ l hi hhd hch, hnd⟩,
    pe_E_of_boundary hd ω l hnd hz⟩

/-- **The percolation probability of bond percolation on `ℤ^d`, `d ≥ 2`, is positive for `q`
close to one.**  The Peierls argument: a finite open cluster of the origin in a plane is
surrounded by a `*`-connected chain of boundary sites, each carrying a closed bond. -/
theorem pe_theta_ne_zero (hd : 2 ≤ d) {q : ℝ} (hq0 : 255 / 256 ≤ q) (hq1 : q ≤ 1) :
    bondTheta d q ≠ 0 := by
  classical
  have h0 : 0 ≤ q := by linarith
  haveI : IsProbabilityMeasure (bitLaw q) := ⟨pe_bitLaw_univ h0 hq1⟩
  haveI : IsProbabilityMeasure (bondPercolation d q) := by
    unfold bondPercolation; infer_instance
  set B : Set (Site d × Fin d → Bool) := ⋃ j : ℕ, ⋃ i : ℕ, pe_badSet hd j i with hB
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = 16 * (1 - q) := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hr1 : r ≤ 1 / 16 := by rw [hr]; linarith
  have hρ8 : 8 * ENNReal.ofReal r ≤ 2⁻¹ := by
    have e1 : (8 : ENNReal) * ENNReal.ofReal r = ENNReal.ofReal (8 * r) := by
      rw [ENNReal.ofReal_mul (by norm_num)]; simp
    have e2 : (2 : ENNReal)⁻¹ = ENNReal.ofReal (1 / 2) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
    rw [e1, e2]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hPB : bondPercolation d q B ≤ ENNReal.ofReal (1 / 16) :=
    calc bondPercolation d q B
        ≤ ∑' j : ℕ, ∑' i : ℕ, bondPercolation d q (pe_badSet hd j i) :=
          (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun j => measure_iUnion_le _)
      _ ≤ ∑' j : ℕ, ∑' i : ℕ,
            (8 : ENNReal) ^ (j + 2 + i) * ENNReal.ofReal r ^ (j + 2 + i + 1) :=
          ENNReal.tsum_le_tsum fun j => ENNReal.tsum_le_tsum fun i => by
            have := pe_badSet_prob hd h0 hq1 j i
            rwa [← hr] at this
      _ ≤ 256 * ENNReal.ofReal r ^ 3 := ec_series_bound _ hρ8
      _ ≤ ENNReal.ofReal (1 / 16) := by
          have e3 : (256 : ENNReal) * ENNReal.ofReal r ^ 3 = ENNReal.ofReal (256 * r ^ 3) := by
            rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow hr0]; simp
          rw [e3]
          refine ENNReal.ofReal_le_ofReal ?_
          have : r ^ 3 ≤ (1 / 16) ^ 3 := pow_le_pow_left₀ hr0 hr1 3
          nlinarith
  have hsub : Bᶜ ⊆ {ω | {x : Site d | (openBondGraph ω).Reachable 0 x}.Infinite} := by
    intro ω hω
    by_contra hinf
    exact hω (pe_cover hd ω (Set.not_infinite.1 hinf))
  intro hθ
  unfold bondTheta at hθ
  have hc : bondPercolation d q Bᶜ = 0 := le_antisymm (hθ ▸ measure_mono hsub) bot_le
  have h1 : (1 : ENNReal) ≤ bondPercolation d q B + bondPercolation d q Bᶜ := by
    calc (1 : ENNReal) = bondPercolation d q Set.univ := measure_univ.symm
      _ = bondPercolation d q (B ∪ Bᶜ) := by rw [Set.union_compl_self]
      _ ≤ _ := measure_union_le _ _
  rw [hc, add_zero] at h1
  have h2 : ENNReal.ofReal (1 / 16) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)
  exact absurd (hPB.trans_lt h2) (not_lt.2 h1)

end Exploding
