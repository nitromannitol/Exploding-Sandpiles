/-
A reusable supercritical Bernoulli site box-crossing lemma.

The nearest-neighbour open crossing of a box is an increasing finite-coordinate
event.  Its complement forces a `*`-connected closed barrier of at least the side
length of the box, and the number of `*`-connected `s`-sets in the box is
`≤ |box| * (3^d)^{2s}` (`xap11_starSets_card_le`).  Hence at high density the
crossing fails with exponentially small probability, uniformly in the box.  The
domination theorems of Liggett, Schonmann and Stacey
(`Exploding.xlse_lss_general`) then transfer the product estimate to any field of
bits with a bounded-range dependence graph and high one-site marginals, which is
the form the Schonmann base scale and the Antal-Pisztora box crossing consume.
-/
import Exploding.Support.ExtAPProof11
import Exploding.Support.ExtLSSCountable

open Exploding LatticeProb MeasureTheory Filter
open scoped Classical Topology ENNReal

namespace Exploding

variable {d : ℕ}

/-- The nearest-neighbour open left-right crossing of the box `cent d n` in direction `i`:
an open lattice path inside the box joining the two `i`-faces. -/
def xbc_Crosses (d n : ℕ) (i : Fin d) (ω : Site d → Bool) : Prop :=
  ∃ x y : Site d, x i = -(n : ℤ) ∧ y i = (n : ℤ) ∧ x ∈ cent d n ∧ y ∈ cent d n ∧
    Relation.ReflTransGen
      (fun a b => (lattice d).Adj a b ∧ a ∈ cent d n ∧ b ∈ cent d n ∧
        ω a = true ∧ ω b = true) x y

/-- The crossing event is monotone in the configuration. -/
theorem xbc_Crosses_mono {n : ℕ} {i : Fin d} {ω ω' : Site d → Bool}
    (h : ∀ z, ω z = true → ω' z = true) (hc : xbc_Crosses d n i ω) :
    xbc_Crosses d n i ω' := by
  obtain ⟨x, y, hx, hy, hxb, hyb, hpath⟩ := hc
  refine ⟨x, y, hx, hy, hxb, hyb, ?_⟩
  refine xap_rtg_mono (fun a b hab => ?_) hpath
  exact ⟨hab.1, hab.2.1, hab.2.2.1, h a hab.2.2.2.1, h b hab.2.2.2.2⟩

/-- The event that a fixed finite set of sites is closed. -/
def xbc_allClosed (Γ : Finset (Site d)) : Set (Site d → Bool) := {ω | ∀ z ∈ Γ, ω z = false}

theorem xbc_measurableSet_allClosed (Γ : Finset (Site d)) : MeasurableSet (xbc_allClosed Γ) := by
  classical
  rw [xbc_allClosed]
  measurability

/-- The product measure of a cylinder in which a finite set is closed. -/
theorem xbc_sitePercolation_allClosed {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (Γ : Finset (Site d)) :
    sitePercolation d q (xbc_allClosed Γ) = ENNReal.ofReal ((1 - q) ^ Γ.card) := by
  classical
  haveI : IsProbabilityMeasure (bitLaw q) := xlss6_bitLaw_isProb h0 h1
  have hq : (0 : ℝ) ≤ 1 - q := by linarith
  have hbit : bitLaw q {false} = ENNReal.ofReal (1 - q) := by
    unfold bitLaw
    simp [Measure.dirac_apply']
  have hset : xbc_allClosed Γ =
      Set.pi (Γ : Set (Site d)) (fun _ => ({false} : Set Bool)) := by
    ext ω
    simp [xbc_allClosed, Set.mem_pi]
  rw [hset, sitePercolation, Measure.infinitePi_pi]
  · rw [Finset.prod_congr rfl fun z _ => hbit, Finset.prod_const, ← ENNReal.ofReal_pow hq]
  · intro z _
    exact measurableSet_singleton false

/-- **The bad-set bound.**  At density `q` the probability that the box `X` contains a
`*`-connected closed set of size `s` is at most the number of `*`-connected `s`-sets times
`(1 - q)^s`. -/
theorem xbc_bad_starSets_prob_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (X : Finset (Site d)) (s : ℕ) :
    sitePercolation d q {ω | ∃ Γ ∈ xap11_starSets X s, ∀ z ∈ Γ, ω z = false} ≤
      ((X.card * (3 ^ d) ^ (2 * s) : ℕ) : ENNReal) * ENNReal.ofReal ((1 - q) ^ s) := by
  classical
  have hcard : ∀ Γ ∈ xap11_starSets X s, Γ.card = s := by
    intro Γ hΓ
    rw [xap11_starSets, Finset.mem_filter] at hΓ
    exact hΓ.2.1
  have hEq : {ω : Site d → Bool | ∃ Γ ∈ xap11_starSets X s, ∀ z ∈ Γ, ω z = false} =
      ⋃ Γ ∈ xap11_starSets X s, xbc_allClosed Γ := by
    ext ω
    simp [xbc_allClosed]
  rw [hEq]
  calc sitePercolation d q (⋃ Γ ∈ xap11_starSets X s, xbc_allClosed Γ)
      ≤ ∑ Γ ∈ xap11_starSets X s, sitePercolation d q (xbc_allClosed Γ) :=
        measure_biUnion_finset_le _ _
    _ = ∑ Γ ∈ xap11_starSets X s, ENNReal.ofReal ((1 - q) ^ s) := by
        refine Finset.sum_congr rfl fun Γ hΓ => ?_
        rw [xbc_sitePercolation_allClosed h0 h1 Γ, hcard Γ hΓ]
    _ = ((xap11_starSets X s).card : ENNReal) * ENNReal.ofReal ((1 - q) ^ s) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((X.card * (3 ^ d) ^ (2 * s) : ℕ) : ENNReal) * ENNReal.ofReal ((1 - q) ^ s) := by
        gcongr
        exact_mod_cast xap11_starSets_card_le X s

/-- **The Liggett–Schonmann–Stacey transfer.**  Any `k`-dependent field of bits on `ℤ^d`
with one-site marginals above a high enough `p` is dominated from below by the Bernoulli
product of density `ρ` on every increasing event. -/
theorem xbc_lss_transfer {d k : ℕ} (hd : 1 ≤ d) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∃ p : ℝ, p < 1 ∧ ∀ (μ : Measure (Site d → Bool)) [IsProbabilityMeasure μ],
      KDependent k μ → (∀ s : Site d, ENNReal.ofReal p ≤ μ {ω | ω s = true}) →
      ∀ A : Set (Site d → Bool), MeasurableSet A → IsIncreasingEvent A →
        sitePercolation d ρ A ≤ μ A :=
  xlse_lss_general d k hd ρ hρ0 hρ1

end Exploding
