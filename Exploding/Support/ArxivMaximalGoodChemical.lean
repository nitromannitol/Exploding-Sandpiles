import Exploding.Support.ArxivCoreAttachment
import Exploding.Support.ArxivMaximalGoodCluster
import Exploding.Support.RNProofCore
import Exploding.Support.SubPoly

/-!
# Chemical distance transfer to the maximal good-site component

An infinite connected good core with linear chemical distance and a uniform finite-hole
box cutoff transfers its chemical bound to the full maximal good-site component.
-/

open Exploding LatticeProb Filter

namespace Exploding

variable {d : ℕ}

private theorem arxiv_maxchem_mnorm_nonneg (x : Site d) : 0 ≤ mnorm x := by
  unfold mnorm
  exact Finset.sum_nonneg fun i _ => abs_nonneg (x i)

private theorem arxiv_maxchem_mnorm_sub_symm (x y : Site d) :
    mnorm (x - y) = mnorm (y - x) := by
  unfold mnorm
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply]
  exact abs_sub_comm _ _

private theorem arxiv_maxchem_mnorm_sub_triangle (x y z : Site d) :
    mnorm (x - z) ≤ mnorm (x - y) + mnorm (y - z) := by
  have h : x - z = (x - y) + (y - z) := by ext i; simp
  rw [h]
  exact rn_mnorm_add_le _ _

private theorem arxiv_maxchem_abs_coord_le (x : Site d) (i : Fin d) :
    |x i| ≤ mnorm x := by
  unfold mnorm
  exact Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)

private theorem arxiv_maxchem_mem_cent {x : Site d} {r : ℕ}
    (hx : mnorm x ≤ (r : ℤ)) : x ∈ (cent d r : Set (Site d)) := by
  intro i
  exact (arxiv_maxchem_abs_coord_le x i).trans hx

private theorem arxiv_maxchem_chemDist_eq_edist (S : Set (Site d)) (x y : Site d)
    (hx : x ∈ S) (hy : y ∈ S) :
    chemDist S x y = ((lattice d).induce S).edist ⟨x, hx⟩ ⟨y, hy⟩ := by
  unfold chemDist
  rw [SimpleGraph.edist_eq_sInf]
  congr 1
  ext t
  constructor
  · rintro ⟨n, rfl, hx', hy', w, hw⟩
    refine ⟨w, ?_⟩
    exact congrArg (fun k : ℕ => (k : ℕ∞)) hw
  · rintro ⟨w, rfl⟩
    exact ⟨w.length, rfl, hx, hy, w, rfl⟩

private theorem arxiv_maxchem_map_core_walk {S K : Set (Site d)} (hSK : S ⊆ K)
    {x y : Site d} (hx : x ∈ S) (hy : y ∈ S)
    (w : ((lattice d).induce S).Walk ⟨x, hx⟩ ⟨y, hy⟩) :
    ∃ w' : ((lattice d).induce K).Walk ⟨x, hSK hx⟩ ⟨y, hSK hy⟩,
      w'.length = w.length := by
  let f := (lattice d).induceHomOfLE hSK
  let w' := (SimpleGraph.Walk.map f.toHom w).copy (by rfl) (by rfl)
  refine ⟨w', ?_⟩
  change (SimpleGraph.Walk.map f.toHom w).length = w.length
  exact SimpleGraph.Walk.length_map _ _

private theorem arxiv_maxchem_map_walk_to_K {S K : Set (Site d)} (hSK : S ⊆ K)
    {x y : Site d} (hx : x ∈ S) (hy : y ∈ S) (hxK : x ∈ K) (hyK : y ∈ K)
    (w : ((lattice d).induce S).Walk ⟨x, hx⟩ ⟨y, hy⟩) :
    ∃ w' : ((lattice d).induce K).Walk ⟨x, hxK⟩ ⟨y, hyK⟩,
      w'.length = w.length := by
  obtain ⟨w', hw'⟩ := arxiv_maxchem_map_core_walk hSK hx hy w
  have hxEq : (⟨x, hSK hx⟩ : K) = ⟨x, hxK⟩ := by
    apply Subtype.ext
    rfl
  have hyEq : (⟨y, hSK hy⟩ : K) = ⟨y, hyK⟩ := by
    apply Subtype.ext
    rfl
  refine ⟨w'.copy hxEq hyEq, ?_⟩
  simpa only [SimpleGraph.Walk.length_copy] using hw'

private theorem arxiv_maxchem_eventually_log_room (B : ℝ) (hB : 1 ≤ B) :
    ∃ N₀ : ℕ, 512 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      B * Real.log ((N : ℝ) + 2) ^ (2 : ℕ) + 1 ≤ (N : ℝ) / 64 ∧
      Real.log (4 * (N : ℝ)) ^ (2 : ℕ) ≤ (N : ℝ) / 64 := by
  have hlittle := (Real.isLittleO_pow_log_id_atTop (n := 2)).def
    (c := 1 / (512 * (B + 1))) (by positivity)
  rw [Filter.eventually_atTop] at hlittle
  obtain ⟨X, hX⟩ := hlittle
  refine ⟨max (Nat.ceil X) 512, Nat.le_max_right _ _, fun N hN => ?_⟩
  have hNceil : Nat.ceil X ≤ N := le_trans (Nat.le_max_left _ _) hN
  have hN512 : 512 ≤ N := le_trans (Nat.le_max_right _ _) hN
  have hXN : X ≤ (N : ℝ) := le_trans (Nat.le_ceil X) (by exact_mod_cast hNceil)
  have hXn2 : X ≤ (N : ℝ) + 2 := by linarith
  have hX4n : X ≤ 4 * (N : ℝ) := by nlinarith
  have hlogN2 := hX ((N : ℝ) + 2) hXn2
  have hlog4N := hX (4 * (N : ℝ)) hX4n
  simp only [id, Real.norm_eq_abs] at hlogN2 hlog4N
  have hN2nonneg : (0 : ℝ) ≤ (N : ℝ) + 2 := by positivity
  have h4Nnonneg : (0 : ℝ) ≤ 4 * (N : ℝ) := by positivity
  rw [abs_of_nonneg hN2nonneg] at hlogN2
  rw [abs_of_nonneg h4Nnonneg] at hlog4N
  have hlogN2' : Real.log ((N : ℝ) + 2) ^ 2 ≤
      (1 / (512 * (B + 1))) * ((N : ℝ) + 2) := by
    calc
      Real.log ((N : ℝ) + 2) ^ 2 =
          |Real.log ((N : ℝ) + 2) ^ 2| :=
        (abs_of_nonneg (sq_nonneg _)).symm
      _ ≤ (1 / (512 * (B + 1))) * ((N : ℝ) + 2) := hlogN2
  have hlog4N' : Real.log (4 * (N : ℝ)) ^ 2 ≤
      (1 / (512 * (B + 1))) * (4 * (N : ℝ)) := by
    calc
      Real.log (4 * (N : ℝ)) ^ 2 = |Real.log (4 * (N : ℝ)) ^ 2| :=
        (abs_of_nonneg (sq_nonneg _)).symm
      _ ≤ (1 / (512 * (B + 1))) * (4 * (N : ℝ)) := hlog4N
  constructor
  · have hNpos : (0 : ℝ) ≤ N := by positivity
    have hNadd : (N : ℝ) + 2 ≤ 2 * N := by
      have h128 : 128 ≤ N := by omega
      have : (128 : ℝ) ≤ N := by exact_mod_cast h128
      linarith
    have hBpos : 0 ≤ B := le_trans (by norm_num) hB
    have hcoef : B / (512 * (B + 1)) ≤ 1 / 512 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hlogbound := mul_le_mul_of_nonneg_left hlogN2' hBpos
    have hscale : B * ((1 / (512 * (B + 1))) * ((N : ℝ) + 2)) ≤
        (N : ℝ) / 256 := by
      calc
        B * ((1 / (512 * (B + 1))) * ((N : ℝ) + 2)) =
            (B / (512 * (B + 1))) * ((N : ℝ) + 2) := by ring
        _ ≤ (1 / 512) * ((N : ℝ) + 2) :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
        _ ≤ (N : ℝ) / 256 := by nlinarith
    have hconst : (1 : ℝ) ≤ (N : ℝ) / 256 := by
      have : (256 : ℝ) ≤ N := by exact_mod_cast (by omega : 256 ≤ N)
      nlinarith
    nlinarith
  · have hNpos : (0 : ℝ) ≤ N := by positivity
    have hcoef : 4 / (512 * (B + 1)) ≤ 1 / 128 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc
      Real.log (4 * (N : ℝ)) ^ 2 ≤
          (1 / (512 * (B + 1))) * (4 * (N : ℝ)) := hlog4N'
      _ = (4 / (512 * (B + 1))) * (N : ℝ) := by ring
      _ ≤ (1 / 128) * (N : ℝ) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ ≤ (N : ℝ) / 64 := by linarith

private theorem arxiv_maxchem_log_sq_le {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxy : x ≤ y ^ (2 : ℕ)) : Real.log x ^ (2 : ℕ) ≤ 4 * Real.log y ^ (2 : ℕ) := by
  have hlog := Real.log_le_log (by linarith : 0 < x) hxy
  rw [Real.log_pow] at hlog
  norm_num at hlog
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
  have hprod : 0 ≤ (2 * Real.log y - Real.log x) * (2 * Real.log y + Real.log x) :=
    mul_nonneg (by linarith [hlog]) (by positivity)
  nlinarith [hprod]

private theorem arxiv_maxchem_log_cutoff_le (N : ℕ) (hN : 512 ≤ N) :
    Real.log (4 * (N : ℝ)) ^ (2 : ℕ) ≤
      4 * Real.log ((N : ℝ) + 2) ^ (2 : ℕ) := by
  apply arxiv_maxchem_log_sq_le
  · have : 1 ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
    nlinarith
  · nlinarith [show (0 : ℝ) ≤ N by positivity]
  · nlinarith [sq_nonneg (N : ℝ)]

private theorem arxiv_maxchem_log_box_le (n N : ℕ) (hn : 512 ≤ n)
    (hN : N ≤ 2 * n) :
    Real.log ((N : ℝ) + 2) ^ (2 : ℕ) ≤ 4 * Real.log (n : ℝ) ^ (2 : ℕ) := by
  apply arxiv_maxchem_log_sq_le
  · nlinarith [show (0 : ℝ) ≤ N by positivity]
  · have : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    exact this
  · have hnR : (N : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hN
    have hn' : (N : ℝ) + 2 ≤ 2 * (n : ℝ) + 2 := by linarith
    have hnR512 : (512 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnsq : 2 * (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((n : ℝ) - 2)]
    exact hn'.trans hnsq

private theorem arxiv_maxchem_walk_crosses_radius {S : Set (Site d)}
    {a : Site d} (R : ℕ) {u v : S}
    (p : ((lattice d).induce S).Walk u v)
    (hstart : mnorm ((u : Site d) - a) ≤ (R : ℤ))
    (hend : (R : ℤ) ≤ mnorm ((v : Site d) - a)) :
    ∃ w ∈ p.support, mnorm ((w : Site d) - a) = (R : ℤ) := by
  induction p generalizing R with
  | @nil u =>
      refine ⟨u, by simp, ?_⟩
      exact le_antisymm hstart hend
  | @cons u v w hadj p ih =>
      let du : ℤ := mnorm ((u : Site d) - a)
      let dv : ℤ := mnorm ((v : Site d) - a)
      by_cases hdu : du = (R : ℤ)
      · exact ⟨u, by simp, by simpa [du] using hdu⟩
      · by_cases hRdv : (R : ℤ) ≤ dv
        · have hduLt : du < (R : ℤ) := by omega
          have hadj' : (lattice d).Adj (u : Site d) (v : Site d) := by
            simpa using hadj
          have hdvLe : dv ≤ du + 1 := by
            dsimp [dv, du]
            exact rn_mnorm_sub_le_of_adj a hadj'.symm
          have hdvEq : dv = (R : ℤ) := by omega
          exact ⟨v, by simp [SimpleGraph.Walk.support_cons], by simpa [dv] using hdvEq⟩
        · have hdvLt : dv < (R : ℤ) := by omega
          obtain ⟨x, hx, hxdist⟩ := ih R (by simpa [dv] using hdvLt.le) hend
          exact ⟨x, by simp [SimpleGraph.Walk.support_cons, hx], hxdist⟩

private theorem arxiv_maxchem_core_point_at_radius {S : Set (Site d)}
    (hSinf : S.Infinite)
    (hSconn : ∀ x ∈ S, ∀ y ∈ S, y ∈ componentIn S x)
    {a : Site d} (ha : a ∈ S) (R : ℕ) :
    ∃ w ∈ S, mnorm (w - a) = (R : ℤ) := by
  classical
  have hboxFin := (cent_finite_ncard d ((mnorm a).toNat + R)).1
  have hexists : ∃ v ∈ S, v ∉ cent d ((mnorm a).toNat + R) := by
    by_contra hnone
    have hsub : S ⊆ cent d ((mnorm a).toNat + R) := by
      intro v hv
      by_contra hvbox
      exact hnone ⟨v, hv, hvbox⟩
    exact hSinf (hboxFin.subset hsub)
  obtain ⟨v, hvS, hvbox⟩ := hexists
  have hnormA : ((mnorm a).toNat : ℤ) = mnorm a :=
    Int.toNat_of_nonneg (arxiv_maxchem_mnorm_nonneg a)
  have hvbigCoord : ∃ i : Fin d, ((mnorm a).toNat + R : ℤ) < |v i| := by
    have hvnot : ¬ ∀ i : Fin d, |v i| ≤ ((mnorm a).toNat + R : ℤ) := by
      simpa [cent] using hvbox
    obtain ⟨i, hi⟩ := not_forall.mp hvnot
    exact ⟨i, not_le.mp hi⟩
  obtain ⟨i, hcoord⟩ := hvbigCoord
  have hnormV : |v i| ≤ mnorm v := arxiv_maxchem_abs_coord_le v i
  have htri := arxiv_maxchem_mnorm_sub_triangle v a 0
  have hfar : (R : ℤ) < mnorm (v - a) := by
    have hcoord' : (mnorm a + R : ℤ) < mnorm v := by
      have hcast : ((mnorm a).toNat + R : ℤ) = mnorm a + R := by
        rw [hnormA]
      rw [hcast] at hcoord
      exact lt_of_lt_of_le hcoord hnormV
    have htri' : mnorm v ≤ mnorm (v - a) + mnorm a := by
      simpa using htri
    omega
  obtain ⟨huG, hvG, hreach⟩ := hSconn a ha v hvS
  have hreach' : ((lattice d).induce S).Reachable ⟨a, ha⟩ ⟨v, hvS⟩ := by
    simpa using hreach
  obtain ⟨p⟩ := hreach'
  have hstart : mnorm (a - a) ≤ (R : ℤ) := by
    simp [mnorm]
  obtain ⟨w, hwSupport, hwdist⟩ :=
    arxiv_maxchem_walk_crosses_radius (S := S) R p hstart hfar.le
  exact ⟨w, w.property, hwdist⟩

private theorem arxiv_maxchem_attachment {η : Site d → ℤ} {k N : ℕ}
    {S : Set (Site d)} {z u : Site d} {B : ℝ}
    (hB : 1 ≤ B) (hS : IsInfiniteConnectedGoodSet η k S)
    (hholes : RnHoleProp d S) (hz : z ∈ S)
    (huK : u ∈ componentIn (goodSites η k) z)
    (huCent : u ∈ cent d (4 * N))
    (hcut : ∀ v ∈ cent d (4 * N), v ∉ S →
      (componentIn Sᶜ v).Finite ∧
        ((componentIn Sᶜ v).ncard : ℝ) ≤ B * Real.log ((N : ℝ) + 2) ^ (2 : ℕ)) :
    ∃ a, ∃ _ha : a ∈ S, ∃ haK : a ∈ componentIn (goodSites η k) z,
      ∃ p : ((lattice d).induce (componentIn (goodSites η k) z)).Walk
        ⟨u, huK⟩ ⟨a, haK⟩,
        (p.length : ℝ) ≤ B * Real.log ((N : ℝ) + 2) ^ (2 : ℕ) + 1 := by
  classical
  by_cases huS : u ∈ S
  · refine ⟨u, huS, huK, SimpleGraph.Walk.nil, ?_⟩
    have hlogsq : 0 ≤ Real.log ((N : ℝ) + 2) ^ (2 : ℕ) := sq_nonneg _
    have hBpos : 0 ≤ B := le_trans (by norm_num) hB
    have hprod : 0 ≤ B * Real.log ((N : ℝ) + 2) ^ (2 : ℕ) := mul_nonneg hBpos hlogsq
    simp only [SimpleGraph.Walk.length_nil, Nat.cast_zero]
    exact add_nonneg hprod (by norm_num)
  · obtain ⟨hfinite, hvol⟩ := hcut u huCent huS
    let H : Set (Site d) := componentIn Sᶜ u
    have hcardEq : H.ncard = hfinite.toFinset.card :=
      Set.ncard_eq_toFinset_card H hfinite
    have hvol' : (H.ncard : ℝ) ≤ B * Real.log ((N : ℝ) + 2) ^ (2 : ℕ) := by
      rw [hcardEq] at hvol ⊢
      exact hvol
    obtain ⟨a, ha, haK, p, hp⟩ :=
      arxiv_core_attachment η k hS hholes z hz u huK
    have hpR : (p.length : ℝ) ≤ (H.ncard : ℝ) + 1 := by
      exact_mod_cast hp
    refine ⟨a, ha, haK, p, ?_⟩
    calc
      (p.length : ℝ) ≤ (H.ncard : ℝ) + 1 := hpR
      _ ≤ B * Real.log ((N : ℝ) + 2) ^ (2 : ℕ) + 1 := by linarith

private theorem arxiv_maxchem_core_path {S : Set (Site d)} {C : ℝ}
    (n : ℕ)
    (hchemAt : ∀ x ∈ S, ∀ y ∈ S, mnorm x ≤ (n : ℤ) →
      Real.log n ^ (2 : ℕ) ≤ (mnorm (x - y) : ℝ) →
      ∃ m : ℕ, chemDist S x y = (m : ℕ∞) ∧
        (1 : ℝ) * (mnorm (x - y) : ℝ) ≤ (m : ℝ) ∧
        (m : ℝ) ≤ C * (mnorm (x - y) : ℝ))
    {a b : Site d} (ha : a ∈ S) (hb : b ∈ S)
    (haNorm : mnorm a ≤ (n : ℤ))
    (hsep : Real.log n ^ (2 : ℕ) ≤ (mnorm (a - b) : ℝ)) :
    ∃ p : ((lattice d).induce S).Walk ⟨a, ha⟩ ⟨b, hb⟩,
      (p.length : ℝ) ≤ C * (mnorm (a - b) : ℝ) := by
  obtain ⟨m, hm, _, hmC⟩ := hchemAt a ha b hb haNorm hsep
  have hed : ((lattice d).induce S).edist ⟨a, ha⟩ ⟨b, hb⟩ = (m : ℕ∞) := by
    rw [← arxiv_maxchem_chemDist_eq_edist S a b ha hb]
    exact hm
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_eq_coe hed
  refine ⟨p, ?_⟩
  rw [hp]
  exact hmC

private theorem arxiv_maxchem_conclude_walk {K : Set (Site d)} {A : ℝ}
    {x y : Site d} (hx : x ∈ K) (hy : y ∈ K)
    (p : ((lattice d).induce K).Walk ⟨x, hx⟩ ⟨y, hy⟩)
    (hwalk : (p.length : ℝ) ≤ A * (mnorm (x - y) : ℝ)) :
    ∃ m : ℕ, chemDist K x y = (m : ℕ∞) ∧
      (1 : ℝ) * (mnorm (x - y) : ℝ) ≤ (m : ℝ) ∧
      (m : ℝ) ≤ A * (mnorm (x - y) : ℝ) := by
  have hle : chemDist K x y ≤ (p.length : ℕ∞) := rn_chemDist_le_walk K hx hy p
  have hne : chemDist K x y ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top p.length) hle
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
  have hlen : m ≤ p.length := by
    rw [← hm] at hle
    exact_mod_cast hle
  have hge := rn_chemDist_ge K x y
  have hdist : (mnorm (x - y)).toNat ≤ m := by
    rw [← hm] at hge
    exact_mod_cast hge
  have hnorm0 : 0 ≤ mnorm (x - y) := arxiv_maxchem_mnorm_nonneg _
  have hdistInt : mnorm (x - y) ≤ (m : ℤ) := by omega
  have hdistReal : (mnorm (x - y) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hdistInt
  refine ⟨m, hm.symm, ?_, ?_⟩
  · simpa using hdistReal
  · exact (by exact_mod_cast hlen : (m : ℝ) ≤ (p.length : ℝ)).trans hwalk

private theorem arxiv_maxchem_box_walk {η : Site d → ℤ} {k N : ℕ}
    {S K : Set (Site d)} {z : Site d} {B C : ℝ}
    (hB : 1 ≤ B) (hC : 1 ≤ C) (hS : IsInfiniteConnectedGoodSet η k S)
    (hholes : RnHoleProp d S) (hz : z ∈ S)
    (hK : K = componentIn (goodSites η k) z) (hSK : S ⊆ K)
    (hchemAt : ∀ a ∈ S, ∀ b ∈ S, mnorm a ≤ ((4 * N : ℕ) : ℤ) →
      Real.log (4 * (N : ℝ)) ^ (2 : ℕ) ≤ (mnorm (a - b) : ℝ) →
      ∃ m : ℕ, chemDist S a b = (m : ℕ∞) ∧
        (1 : ℝ) * (mnorm (a - b) : ℝ) ≤ (m : ℝ) ∧
        (m : ℝ) ≤ C * (mnorm (a - b) : ℝ))
    (hcut : ∀ v ∈ (cent d (4 * N) : Set (Site d)), v ∉ S →
      (componentIn Sᶜ v).Finite ∧
        ((componentIn Sᶜ v).ncard : ℝ) ≤ B * Real.log ((N : ℝ) + 2) ^ (2 : ℕ))
    (hroomT : B * Real.log ((N : ℝ) + 2) ^ (2 : ℕ) + 1 ≤ (N : ℝ) / 64)
    (hroomL : Real.log (4 * (N : ℝ)) ^ (2 : ℕ) ≤ (N : ℝ) / 64)
    {x y : Site d} (hxK : x ∈ K) (hyK : y ∈ K)
    (hxCent : x ∈ (cent d (4 * N) : Set (Site d)))
    (hyCent : y ∈ (cent d (4 * N) : Set (Site d)))
    (hxNorm : mnorm x ≤ (N : ℤ)) :
    ∃ p : ((lattice d).induce K).Walk ⟨x, hxK⟩ ⟨y, hyK⟩,
      (p.length : ℝ) ≤ C * (mnorm (x - y) : ℝ) +
        2 * (C + 1) * (B * Real.log ((N : ℝ) + 2) ^ (2 : ℕ) + 1) +
        C * (5 * Real.log (4 * (N : ℝ)) ^ (2 : ℕ) + 8) := by
  classical
  subst K
  let T : ℝ := B * Real.log ((N : ℝ) + 2) ^ (2 : ℕ) + 1
  let L : ℝ := Real.log (4 * (N : ℝ)) ^ (2 : ℕ)
  let D : ℝ := (mnorm (x - y) : ℝ)
  have hTnonneg : 0 ≤ T := by
    dsimp [T]
    have hlog : 0 ≤ Real.log ((N : ℝ) + 2) ^ (2 : ℕ) := sq_nonneg _
    have hBpos : 0 ≤ B := le_trans (by norm_num) hB
    positivity
  have hLnonneg : 0 ≤ L := by dsimp [L]; exact sq_nonneg _
  have hCpos : 0 ≤ C := le_trans (by norm_num) hC
  have hroomT' : T ≤ (N : ℝ) / 64 := by simpa [T] using hroomT
  have hroomL' : L ≤ (N : ℝ) / 64 := by simpa [L] using hroomL
  have hchemAtCore : ∀ a ∈ S, ∀ b ∈ S,
      mnorm a ≤ ((4 * N : ℕ) : ℤ) →
      Real.log ((4 * N : ℕ) : ℝ) ^ (2 : ℕ) ≤ (mnorm (a - b) : ℝ) →
      ∃ m : ℕ, chemDist S a b = (m : ℕ∞) ∧
        (1 : ℝ) * (mnorm (a - b) : ℝ) ≤ (m : ℝ) ∧
        (m : ℝ) ≤ C * (mnorm (a - b) : ℝ) := by
    intro a ha b hb haNorm hsep
    have hsep' : Real.log (4 * (N : ℝ)) ^ (2 : ℕ) ≤
        (mnorm (a - b) : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hsep
    exact hchemAt a ha b hb haNorm hsep'
  obtain ⟨a, ha, haK, pX, hpX⟩ :=
    arxiv_maxchem_attachment hB hS hholes hz hxK hxCent hcut
  obtain ⟨b, hb, hbK, pY, hpY⟩ :=
    arxiv_maxchem_attachment hB hS hholes hz hyK hyCent hcut
  have hpX' : (pX.length : ℝ) ≤ T := by simpa [T] using hpX
  have hpY' : (pY.length : ℝ) ≤ T := by simpa [T] using hpY
  have hattachSum : (pX.length : ℝ) + (pY.length : ℝ) ≤ 2 * T := by
    linarith
  have hattachOrd : (pX.length : ℝ) + (pY.length : ℝ) ≤ 2 * (C + 1) * T := by
    have hprod : 0 ≤ (C - 1) * T :=
      mul_nonneg (sub_nonneg.mpr hC) hTnonneg
    nlinarith [hattachSum, hprod]
  have hattachFactor : (C + 1) * ((pX.length : ℝ) + (pY.length : ℝ)) ≤
      2 * (C + 1) * T := by
    calc
      (C + 1) * ((pX.length : ℝ) + (pY.length : ℝ)) ≤
          (C + 1) * (2 * T) :=
        mul_le_mul_of_nonneg_left hattachSum (by positivity)
      _ = 2 * (C + 1) * T := by ring
  have hdistXa : mnorm (a - x) ≤ (pX.length : ℤ) := by
    have h := rn_walk_length_ge ⟨x, hxK⟩ ⟨a, haK⟩ pX
    rwa [arxiv_maxchem_mnorm_sub_symm] at h
  have haNormReal : (mnorm a : ℝ) ≤ (N : ℝ) + T := by
    have haEq : a = (a - x) + x := by abel
    have hsum := calc
      mnorm a = mnorm ((a - x) + x) := congrArg mnorm haEq
      _ ≤ mnorm (a - x) + mnorm x := rn_mnorm_add_le _ _
    have hsum' : mnorm a ≤ (pX.length : ℤ) + (N : ℤ) := by
      exact hsum.trans (add_le_add hdistXa hxNorm)
    have hsumR : (mnorm a : ℝ) ≤ (pX.length : ℝ) + N := by exact_mod_cast hsum'
    exact hsumR.trans (by
      calc
        (pX.length : ℝ) + N ≤ T + N := add_le_add hpX' le_rfl
        _ = N + T := by ring)
  have haNorm : mnorm a ≤ ((4 * N : ℕ) : ℤ) := by
    have hreal : (mnorm a : ℝ) ≤ (4 * (N : ℝ)) := by
      calc
        (mnorm a : ℝ) ≤ (N : ℝ) + T := haNormReal
        _ ≤ (N : ℝ) + (N : ℝ) / 64 := add_le_add le_rfl hroomT'
        _ ≤ 4 * (N : ℝ) := by nlinarith
    exact_mod_cast hreal
  have hdistYb : mnorm (y - b) ≤ (pY.length : ℤ) := by
    have h := rn_walk_length_ge ⟨y, hyK⟩ ⟨b, hbK⟩ pY
    simpa using h
  have hDcore : (mnorm (a - b) : ℝ) ≤ D + (pX.length : ℝ) + (pY.length : ℝ) := by
    have htri : mnorm (a - b) ≤ mnorm (a - x) + mnorm (x - y) + mnorm (y - b) := by
      calc
        mnorm (a - b) ≤ mnorm (a - x) + mnorm (x - b) :=
          arxiv_maxchem_mnorm_sub_triangle a x b
        _ ≤ mnorm (a - x) + (mnorm (x - y) + mnorm (y - b)) :=
          add_le_add le_rfl (arxiv_maxchem_mnorm_sub_triangle x y b)
        _ = mnorm (a - x) + mnorm (x - y) + mnorm (y - b) := by ring
    have htriR : (mnorm (a - b) : ℝ) ≤
        (mnorm (a - x) : ℝ) + D + (mnorm (y - b) : ℝ) := by
      dsimp [D]
      exact_mod_cast htri
    have hXa : (mnorm (a - x) : ℝ) ≤ (pX.length : ℝ) := by exact_mod_cast hdistXa
    have hYb : (mnorm (y - b) : ℝ) ≤ (pY.length : ℝ) := by exact_mod_cast hdistYb
    linarith
  by_cases hsep : L ≤ (mnorm (a - b) : ℝ)
  · obtain ⟨pAB, hpAB⟩ := arxiv_maxchem_core_path (C := C) (n := 4 * N)
      hchemAtCore ha hb haNorm (by
        simpa [L, Nat.cast_mul, Nat.cast_ofNat] using hsep)
    obtain ⟨pABK, hpABK⟩ := arxiv_maxchem_map_walk_to_K hSK ha hb haK hbK pAB
    let p := (pX.append pABK).append pY.reverse
    refine ⟨p, ?_⟩
    have hlen : p.length = pX.length + pABK.length + pY.length := by
      simp [p, SimpleGraph.Walk.length_append]
    have hpABK' : (pABK.length : ℝ) ≤ C * (mnorm (a - b) : ℝ) := by
      have hpAB' : (pAB.length : ℝ) ≤ C * (mnorm (a - b) : ℝ) := hpAB
      simpa [hpABK] using hpAB'
    have hcore : C * (mnorm (a - b) : ℝ) ≤ C * (D + (pX.length : ℝ) + (pY.length : ℝ)) :=
      mul_le_mul_of_nonneg_left hDcore hCpos
    rw [hlen]
    push_cast
    nlinarith [hpX', hpY', hpABK', hcore, hattachFactor, hTnonneg, hCpos]
  · have hclose : (mnorm (a - b) : ℝ) < L := lt_of_not_ge hsep
    let R : ℕ := Nat.ceil (2 * L)
    have hRlo : 2 * L ≤ (R : ℝ) := by
      exact Nat.le_ceil _
    have hRhi : (R : ℝ) < 2 * L + 1 := by
      change (Nat.ceil (2 * L) : ℝ) < 2 * L + 1
      exact Nat.ceil_lt_add_one (mul_nonneg (by norm_num) hLnonneg)
    obtain ⟨w, hw, hwa⟩ :=
      arxiv_maxchem_core_point_at_radius hS.1 hS.2.2 ha R
    have hwaReal : (mnorm (a - w) : ℝ) = (R : ℝ) := by
      have hwa' : mnorm (w - a) = (R : ℤ) := hwa
      have : mnorm (a - w) = (R : ℤ) := by
        rw [arxiv_maxchem_mnorm_sub_symm]
        exact hwa'
      exact_mod_cast this
    have hdistBW : (mnorm (w - b) : ℝ) ≤ (R : ℝ) + (mnorm (a - b) : ℝ) := by
      have htri := arxiv_maxchem_mnorm_sub_triangle w a b
      have htriR : (mnorm (w - b) : ℝ) ≤
          (mnorm (w - a) : ℝ) + (mnorm (a - b) : ℝ) := by exact_mod_cast htri
      rw [arxiv_maxchem_mnorm_sub_symm w a] at htriR
      rwa [hwaReal] at htriR
    have hdistWBge : L ≤ (mnorm (w - b) : ℝ) := by
      have htriangle := arxiv_maxchem_mnorm_sub_triangle a b w
      have htriangleR : (mnorm (a - w) : ℝ) ≤
          (mnorm (a - b) : ℝ) + (mnorm (b - w) : ℝ) := by exact_mod_cast htriangle
      rw [arxiv_maxchem_mnorm_sub_symm b w] at htriangleR
      rw [hwaReal] at htriangleR
      linarith
    have hwNormReal : (mnorm w : ℝ) ≤ (N : ℝ) + T + (R : ℝ) := by
      have hweq : w = (w - a) + a := by abel
      have htri := calc
        mnorm w = mnorm ((w - a) + a) := congrArg mnorm hweq
        _ ≤ mnorm (w - a) + mnorm a := rn_mnorm_add_le _ _
      have htriR : (mnorm w : ℝ) ≤ (mnorm (w - a) : ℝ) + (mnorm a : ℝ) := by
        exact_mod_cast htri
      rw [arxiv_maxchem_mnorm_sub_symm w a, hwaReal] at htriR
      linarith
    have hwNorm : mnorm w ≤ ((4 * N : ℕ) : ℤ) := by
      have hreal : (mnorm w : ℝ) ≤ 4 * (N : ℝ) := by
        calc
          (mnorm w : ℝ) ≤ (N : ℝ) + T + (R : ℝ) := hwNormReal
          _ ≤ N + N / 64 + (2 * L + 1) := by linarith [hroomT', hRhi.le]
          _ ≤ 4 * N := by nlinarith [hroomL']
      exact_mod_cast hreal
    have hsepAW : L ≤ (mnorm (a - w) : ℝ) := by
      rw [hwaReal]
      linarith [hRlo]
    obtain ⟨pAW, hpAW⟩ := arxiv_maxchem_core_path (C := C) (n := 4 * N)
      hchemAtCore ha hw haNorm (by
        simpa [L, Nat.cast_mul, Nat.cast_ofNat] using hsepAW)
    obtain ⟨pWB, hpWB⟩ := arxiv_maxchem_core_path (C := C) (n := 4 * N)
      hchemAtCore hw hb hwNorm (by
        simpa [L, Nat.cast_mul, Nat.cast_ofNat] using hdistWBge)
    obtain ⟨pAWK, hpAWK⟩ := arxiv_maxchem_map_walk_to_K hSK ha hw haK (hSK hw) pAW
    obtain ⟨pWBK, hpWBK⟩ := arxiv_maxchem_map_walk_to_K hSK hw hb (hSK hw) hbK pWB
    let p := ((pX.append pAWK).append pWBK).append pY.reverse
    refine ⟨p, ?_⟩
    have hlen : p.length = pX.length + pAWK.length + pWBK.length + pY.length := by
      simp [p, SimpleGraph.Walk.length_append]
    have hpAWK' : (pAWK.length : ℝ) ≤ C * (mnorm (a - w) : ℝ) := by
      have hp' : (pAW.length : ℝ) ≤ C * (mnorm (a - w) : ℝ) := hpAW
      simpa [hpAWK] using hp'
    have hpWBK' : (pWBK.length : ℝ) ≤ C * (mnorm (w - b) : ℝ) := by
      have hp' : (pWB.length : ℝ) ≤ C * (mnorm (w - b) : ℝ) := hpWB
      simpa [hpWBK] using hp'
    have hcore : C * (mnorm (a - w) : ℝ) + C * (mnorm (w - b) : ℝ) ≤
        C * (5 * L + 2) := by
      rw [hwaReal]
      have hsum : (R : ℝ) + (mnorm (w - b) : ℝ) ≤ 2 * (R : ℝ) +
          (mnorm (a - b) : ℝ) := by linarith [hdistBW]
      have hsum' : 2 * (R : ℝ) + (mnorm (a - b) : ℝ) ≤ 5 * L + 2 := by
        linarith [hRhi, hclose]
      calc
        C * (R : ℝ) + C * (mnorm (w - b) : ℝ) =
            C * ((R : ℝ) + (mnorm (w - b) : ℝ)) := by ring
        _ ≤ C * (2 * (R : ℝ) + (mnorm (a - b) : ℝ)) :=
          mul_le_mul_of_nonneg_left hsum hCpos
        _ ≤ C * (5 * L + 2) := mul_le_mul_of_nonneg_left hsum' hCpos
    rw [hlen]
    push_cast
    nlinarith [hpX', hpY', hpAWK', hpWBK', hcore, hattachOrd, hTnonneg, hCpos,
      hLnonneg]

private theorem arxiv_maxchem_small_absorb {B C D T L : ℝ}
    (hB : 1 ≤ B) (hC : 1 ≤ C) (hD : 1 ≤ D)
    (hT : T ≤ (4 * B + 1) * D) (hL : L ≤ 16 * D) :
    C * D + 2 * (C + 1) * T + C * (5 * L + 8) ≤
      1000 * (B + 1) * (C + 1) * D := by
  have hT' := mul_le_mul_of_nonneg_left hT (by positivity : 0 ≤ 2 * (C + 1))
  have hLsum : 5 * L + 8 ≤ 88 * D := by nlinarith
  have hL' := mul_le_mul_of_nonneg_left hLsum (by positivity : 0 ≤ C)
  have hcoeff : C + 2 * (C + 1) * (4 * B + 1) + 88 * C ≤
      1000 * (B + 1) * (C + 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr hC)]
  calc
    C * D + 2 * (C + 1) * T + C * (5 * L + 8) =
        C * D + (2 * (C + 1) * T + C * (5 * L + 8)) := by ring
    _ ≤ C * D + (2 * (C + 1) * ((4 * B + 1) * D) + C * (88 * D)) :=
      by linarith [hT', hL']
    _ = (C + 2 * (C + 1) * (4 * B + 1) + 88 * C) * D := by ring
    _ ≤ 1000 * (B + 1) * (C + 1) * D :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)

private theorem arxiv_maxchem_large_absorb {B C D T L : ℝ}
    (hB : 1 ≤ B) (hC : 1 ≤ C) (hT : T ≤ D) (hL : L ≤ D)
    (h8 : 8 ≤ D) :
    C * D + 2 * (C + 1) * T + C * (5 * L + 8) ≤
      1000 * (B + 1) * (C + 1) * D := by
  have hT' := mul_le_mul_of_nonneg_left hT (by positivity : 0 ≤ 2 * (C + 1))
  have hLsum : 5 * L + 8 ≤ 6 * D := by nlinarith
  have hL' := mul_le_mul_of_nonneg_left hLsum (by positivity : 0 ≤ C)
  have hcoeff : 9 * C + 2 ≤ 1000 * (B + 1) * (C + 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr hC)]
  calc
    C * D + 2 * (C + 1) * T + C * (5 * L + 8) =
        C * D + (2 * (C + 1) * T + C * (5 * L + 8)) := by ring
    _ ≤ C * D + (2 * (C + 1) * D + C * (6 * D)) :=
      by linarith [hT', hL']
    _ = (9 * C + 2) * D := by ring
    _ ≤ 1000 * (B + 1) * (C + 1) * D :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)

/-- Transfer the chemical-distance clause from an infinite connected good core to its
maximal good-site component under a uniform finite-hole box cutoff. -/
theorem arxiv_maximal_good_component_chemical_transfer (hd : 2 ≤ d)
    (B C : ℝ) (hB : 1 ≤ B) (hC : 1 ≤ C) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (η : Site d → ℤ) (k : ℕ) (S : Set (Site d)) (z : Site d),
      IsInfiniteConnectedGoodSet η k S → z ∈ S → RnHoleProp d S →
      RnChemClause d C S →
      (∃ ncut : ℕ, ∀ N : ℕ, ncut ≤ N → ∀ u ∈ (cent d (4 * N) : Set (Site d)),
        u ∉ S → (componentIn Sᶜ u).Finite ∧
          ((componentIn Sᶜ u).ncard : ℝ) ≤ B * Real.log ((N : ℝ) + 2) ^ (2 : ℕ)) →
      RnChemClause d A (componentIn (goodSites η k) z) := by
  let A : ℝ := 1000 * (B + 1) * (C + 1)
  have hA : 1 ≤ A := by
    dsimp [A]
    nlinarith
  refine ⟨A, hA, ?_⟩
  intro η k S z hS hz hholes hchem hcutoff
  have _hd_pos : 0 < d := by omega
  obtain ⟨nchem, hchemAt⟩ := hchem
  obtain ⟨ncut, hcut⟩ := hcutoff
  obtain ⟨nroom, hnroom512, hroom⟩ := arxiv_maxchem_eventually_log_room B hB
  let n0 := max nchem (max ncut nroom)
  obtain ⟨K0, hK0eq, _hK0, hSK0, _hmax, _huniq, _hholesK, _hmonotone⟩ :=
    arxivUniqueMaximalGoodCluster η k hS hholes z hz
  let K : Set (Site d) := componentIn (goodSites η k) z
  have hSK : S ⊆ K := by simpa [K, hK0eq] using hSK0
  refine ⟨n0, fun n hn x hx y hy hxNorm hsep => ?_⟩
  have hnchem : nchem ≤ n := le_trans (le_max_left _ _) hn
  have hncut : ncut ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnroom : nroom ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  let Y : ℕ := (mnorm y).toNat
  have hnormY : (Y : ℤ) = mnorm y := by
    dsimp [Y]
    exact Int.toNat_of_nonneg (arxiv_maxchem_mnorm_nonneg y)
  let N : ℕ := max n Y
  have hNn : n ≤ N := Nat.le_max_left _ _
  have hNY : Y ≤ N := Nat.le_max_right _ _
  have hNroom : nroom ≤ N := hnroom.trans hNn
  have hNcut : ncut ≤ N := hncut.trans hNn
  have hN512 : 512 ≤ N := (hnroom512.trans hNroom)
  have hYNorm : mnorm y ≤ (N : ℤ) := by
    rw [← hnormY]
    exact_mod_cast hNY
  have hxNormN : mnorm x ≤ (N : ℤ) := hxNorm.trans (by exact_mod_cast hNn)
  have hxCent : x ∈ (cent d (4 * N) : Set (Site d)) :=
    arxiv_maxchem_mem_cent (hxNormN.trans (by omega))
  have hyCent : y ∈ (cent d (4 * N) : Set (Site d)) :=
    arxiv_maxchem_mem_cent (hYNorm.trans (by omega))
  have hroomN := hroom N hNroom
  have hcutN : ∀ u ∈ (cent d (4 * N) : Set (Site d)), u ∉ S →
      (componentIn Sᶜ u).Finite ∧
        ((componentIn Sᶜ u).ncard : ℝ) ≤ B * Real.log ((N : ℝ) + 2) ^ (2 : ℕ) :=
    fun u hu hnot => hcut N hNcut u hu hnot
  have hchemAtN : ∀ a ∈ S, ∀ b ∈ S, mnorm a ≤ ((4 * N : ℕ) : ℤ) →
      Real.log (4 * (N : ℝ)) ^ (2 : ℕ) ≤ (mnorm (a - b) : ℝ) →
      ∃ m : ℕ, chemDist S a b = (m : ℕ∞) ∧
        (1 : ℝ) * (mnorm (a - b) : ℝ) ≤ (m : ℝ) ∧
        (m : ℝ) ≤ C * (mnorm (a - b) : ℝ) := by
    intro a ha b hb haNorm hcoreSep
    have hraw := hchemAt (4 * N) (by omega) a ha b hb haNorm
    have hcoreSep' : Real.log ((4 * N : ℕ) : ℝ) ^ (2 : ℕ) ≤
        (mnorm (a - b) : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcoreSep
    exact hraw hcoreSep'
  obtain ⟨p, hpBox⟩ := arxiv_maxchem_box_walk hB hC hS hholes hz rfl hSK
    hchemAtN hcutN hroomN.1 hroomN.2 hx hy hxCent hyCent hxNormN
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hDpos : 0 < (mnorm (x - y) : ℝ) :=
    lt_of_lt_of_le (sq_pos_of_pos hlogn) hsep
  have hDposInt : 0 < mnorm (x - y) := by exact_mod_cast hDpos
  have hDlarge : 1 ≤ (mnorm (x - y) : ℝ) := by
    have hDint : 1 ≤ mnorm (x - y) := by omega
    exact_mod_cast hDint
  by_cases hYsmall : Y ≤ 2 * n
  · have hNsmall : N ≤ 2 * n := max_le (by omega) hYsmall
    have hlogNsmall := arxiv_maxchem_log_box_le n N (hnroom512.trans hnroom) hNsmall
    have hLsmall := arxiv_maxchem_log_cutoff_le N hN512
    have hTsmall : B * Real.log ((N : ℝ) + 2) ^ (2 : ℕ) + 1 ≤
        (4 * B + 1) * (mnorm (x - y) : ℝ) := by
      have hBpos : 0 ≤ B := le_trans (by norm_num) hB
      have hmul := mul_le_mul_of_nonneg_left hlogNsmall hBpos
      have hlogNleD : Real.log (n : ℝ) ^ (2 : ℕ) ≤
          (mnorm (x - y) : ℝ) := hsep
      have hscaled : B * (4 * Real.log (n : ℝ) ^ (2 : ℕ)) ≤
          B * (4 * (mnorm (x - y) : ℝ)) :=
        mul_le_mul_of_nonneg_left (by nlinarith [hlogNleD]) hBpos
      nlinarith [hDlarge, hmul, hscaled]
    have hfinalbound : (p.length : ℝ) ≤ A * (mnorm (x - y) : ℝ) := by
      have hLbound : Real.log (4 * (N : ℝ)) ^ (2 : ℕ) ≤
          16 * (mnorm (x - y) : ℝ) := by
        calc
          Real.log (4 * (N : ℝ)) ^ (2 : ℕ) ≤
              4 * Real.log ((N : ℝ) + 2) ^ (2 : ℕ) := hLsmall
          _ ≤ 16 * Real.log (n : ℝ) ^ (2 : ℕ) := by nlinarith [hlogNsmall]
          _ ≤ 16 * (mnorm (x - y) : ℝ) := by nlinarith [hsep]
      have hboxBound := arxiv_maxchem_small_absorb hB hC hDlarge hTsmall hLbound
      have hboxBoundA : C * (mnorm (x - y) : ℝ) +
          2 * (C + 1) * (B * Real.log ((N : ℝ) + 2) ^ (2 : ℕ) + 1) +
          C * (5 * Real.log (4 * (N : ℝ)) ^ (2 : ℕ) + 8) ≤
          A * (mnorm (x - y) : ℝ) := by simpa [A] using hboxBound
      exact hpBox.trans hboxBoundA
    exact arxiv_maxchem_conclude_walk hx hy p hfinalbound
  · have hYlarge : 2 * n < Y := Nat.lt_of_not_ge hYsmall
    have hNeq : N = Y := max_eq_right (by omega)
    have hYtri : mnorm y ≤ mnorm (x - y) + mnorm x := by
      have heq : y = (y - x) + x := by abel
      calc
        mnorm y = mnorm ((y - x) + x) := congrArg mnorm heq
        _ ≤ mnorm (y - x) + mnorm x := rn_mnorm_add_le _ _
        _ = mnorm (x - y) + mnorm x := by rw [arxiv_maxchem_mnorm_sub_symm]
    have hYtriR : (Y : ℝ) ≤ (mnorm (x - y) : ℝ) + (n : ℝ) := by
      have h := hYtri
      rw [← hnormY] at h
      have hxNormR : (mnorm x : ℝ) ≤ (n : ℝ) := by exact_mod_cast hxNorm
      have hYtriR' : (Y : ℝ) ≤ (mnorm (x - y) : ℝ) + (mnorm x : ℝ) := by
        exact_mod_cast h
      exact hYtriR'.trans (by
        calc
          (mnorm (x - y) : ℝ) + (mnorm x : ℝ) =
              (mnorm x : ℝ) + (mnorm (x - y) : ℝ) := by ring
          _ ≤ (n : ℝ) + (mnorm (x - y) : ℝ) := add_le_add hxNormR le_rfl
          _ = (mnorm (x - y) : ℝ) + (n : ℝ) := by ring)
    have hDlargeN : (N : ℝ) / 2 < (mnorm (x - y) : ℝ) := by
      rw [hNeq]
      have hYlargeR : 2 * (n : ℝ) < (Y : ℝ) := by exact_mod_cast hYlarge
      nlinarith [hYtriR]
    have hTleD : B * Real.log ((N : ℝ) + 2) ^ (2 : ℕ) + 1 ≤
        (mnorm (x - y) : ℝ) := by
      have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := by positivity
      have hN64 : (N : ℝ) / 64 ≤ (N : ℝ) / 2 := by linarith
      have hstrict : B * Real.log ((N : ℝ) + 2) ^ (2 : ℕ) + 1 <
          (mnorm (x - y) : ℝ) := calc
        B * Real.log ((N : ℝ) + 2) ^ (2 : ℕ) + 1 ≤ (N : ℝ) / 64 := hroomN.1
        _ ≤ (N : ℝ) / 2 := hN64
        _ < (mnorm (x - y) : ℝ) := hDlargeN
      exact le_of_lt hstrict
    have hLleD : Real.log (4 * (N : ℝ)) ^ (2 : ℕ) ≤
        (mnorm (x - y) : ℝ) := by
      have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := by positivity
      have hstrict : Real.log (4 * (N : ℝ)) ^ (2 : ℕ) <
          (mnorm (x - y) : ℝ) := calc
        Real.log (4 * (N : ℝ)) ^ (2 : ℕ) ≤ (N : ℝ) / 64 := hroomN.2
        _ ≤ (N : ℝ) / 2 := by linarith
        _ < (mnorm (x - y) : ℝ) := hDlargeN
      exact le_of_lt hstrict
    have h8leD : 8 ≤ (mnorm (x - y) : ℝ) := by
      have hN512R : (512 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN512
      have h8N : 8 ≤ (N : ℝ) / 2 := by linarith
      exact h8N.trans (le_of_lt hDlargeN)
    have hfinalbound : (p.length : ℝ) ≤ A * (mnorm (x - y) : ℝ) := by
      have hboxBound := arxiv_maxchem_large_absorb hB hC hTleD hLleD h8leD
      have hboxBoundA : C * (mnorm (x - y) : ℝ) +
          2 * (C + 1) * (B * Real.log ((N : ℝ) + 2) ^ (2 : ℕ) + 1) +
          C * (5 * Real.log (4 * (N : ℝ)) ^ (2 : ℕ) + 8) ≤
          A * (mnorm (x - y) : ℝ) := by simpa [A] using hboxBound
      exact hpBox.trans hboxBoundA
    exact arxiv_maxchem_conclude_walk hx hy p hfinalbound

end Exploding
