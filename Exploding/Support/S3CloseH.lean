/-
Proposition 5.1 (generalized last wave), closeness of the arrival times, part H:
the closeness `T̂(x) ≤ T̃(x) ≤ T̂(x) + (log n)^γ` on a background carrying the data of `S3kData`,
with an exponent depending only on `d` and the path-filling exponent.
-/
import Exploding.Support.S3CloseG

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

/-- **Closeness on a background.**  The exponent is `s3k_Etop d γp + 1`. -/
theorem s3k_close_of_data {k : Fin d → ℕ} {Cinf : Set (Site d)} {γp Cch : ℝ} {η : Site d → ℤ}
    (D : S3kData d η k Cinf γp Cch) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
      lastArrival η (0 : Site d) x ≤ clusterArrival η (0 : Site d) x ∧
        ∃ a b : ℕ, lastArrival η (0 : Site d) x = (a : ℕ∞) ∧
          clusterArrival η (0 : Site d) x = (b : ℕ∞) ∧
            (b : ℝ) ≤ (a : ℝ) + Real.log n ^ (s3k_Etop d γp + 1) := by
  classical
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast D.hd
    linarith
  have hd1 : 1 ≤ d := by have := D.hd; omega
  set kmax : ℕ := ∑ i, k i with hkmax
  set K : ℕ := ∏ l, k l with hK
  obtain ⟨τ0, J, An, Bn, n0n, hnear⟩ := s3k_near D
  obtain ⟨Af, Bf, n0f, hfar⟩ := s3k_far D
  -- every penultimate-cluster arrival time is finite
  have hfin : ∀ x : Site d, clusterArrival η (0 : Site d) x ≠ ⊤ := by
    intro x
    set R : ℕ := (mnorm x).toNat with hR
    have hxR : mnorm x ≤ (R : ℤ) := Int.self_le_toNat _
    have hlit := hnear (max n0n (R + d)) (le_max_left _ _) x R hxR (le_max_right _ _)
    have hcl := clusterArrival_le η (0 : Site d) x
      (τ0 + An * (J + R + d) + Bn * glws_Zn γp (max n0n (R + d)) ^ d + 1) (by omega)
      (fun w hw => pclose_pos_mono hd0 η D.hlow _ (0 : Site d) (Nat.le_succ _) (hlit w hw))
    exact ne_top_of_le_ne_top (WithTop.coe_ne_top) hcl
  have hPL := s3k_PL_Pn γp D.hγp kmax d
  obtain ⟨n0e, he⟩ := eventually_atTop.mp
    ((s3k_PL_le (s3k_PL_Tnear γp D.hγp kmax d hd1 τ0 J An Bn)).and
      ((s3k_PL_le (s3k_PL_Tfar γp D.hγp kmax d hd1 K Af Bf)).and
        ((s3k_PL_le_n hPL (2 * (d : ℝ)) (by positivity)).and (eventually_ge_atTop (2 * d)))))
  refine ⟨max (max n0n n0f) n0e, ?_⟩
  intro n hn x hxn
  have hn0n : n0n ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn0f : n0f ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn0e : n0e ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨hTn, hTf, hbig1, hbig2⟩ := he n hn0e
  have hle := lastArrival_le_clusterArrival η (0 : Site d) x
  have hTne : lastArrival η (0 : Site d) x ≠ ⊤ := ne_top_of_le_ne_top (hfin x) hle
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hTne
  have ha' : lastArrival η (0 : Site d) x = (a : ℕ∞) := ha.symm
  obtain ⟨ha1, hapos⟩ := pclose_attained η x a ha'
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp (hfin x)
  have hb' : clusterArrival η (0 : Site d) x = (b : ℕ∞) := hb.symm
  refine ⟨hle, a, b, ha', hb', ?_⟩
  -- a time `T`, polylogarithmic, with the cluster lit at `a + T`
  have key : ∃ T : ℕ, (T : ℝ) ≤ Real.log n ^ (s3k_Etop d γp + 1) ∧
      ∀ w ∈ penultimateCluster η x, 0 < lastWave η (0 : Site d) (a + T) w := by
    by_cases hfarc : ∃ l, ((glws_Pn γp kmax d n : ℕ) : ℤ) ≤ |x l|
    · exact ⟨s3k_Tfar γp kmax d K Af Bf n, hTf,
        hfar n hn0f x a hxn hfarc hapos⟩
    · push Not at hfarc
      set Pn : ℕ := glws_Pn γp kmax d n with hPn
      have hxR : mnorm x ≤ ((d * Pn : ℕ) : ℤ) := by
        have := glws_mnorm_le_coord x (Pn : ℤ) (fun l => (hfarc l).le)
        push_cast
        exact this
      have hRn : d * Pn + d ≤ n := by
        have h1 : (2 * (d : ℝ)) * (Pn : ℝ) ≤ (n : ℝ) := hbig1
        have h2 : (2 * d * Pn : ℕ) ≤ n := by exact_mod_cast h1
        nlinarith
      have hlit := hnear n hn0n x (d * Pn) hxR hRn
      refine ⟨s3k_Tnear γp kmax d τ0 J An Bn n, hTn, fun w hw => ?_⟩
      refine pclose_pos_mono hd0 η D.hlow _ (0 : Site d) (Nat.le_add_left _ _) ?_
      have := hlit w hw
      unfold s3k_Tnear
      exact this
  obtain ⟨T, hT, hlitT⟩ := key
  have hcl := clusterArrival_le η (0 : Site d) x (a + T) (by omega) hlitT
  have hbT : b ≤ a + T := by
    rw [hb'] at hcl
    exact_mod_cast hcl
  have hbT' : (b : ℝ) ≤ (a : ℝ) + (T : ℝ) := by exact_mod_cast hbT
  linarith

end Exploding
