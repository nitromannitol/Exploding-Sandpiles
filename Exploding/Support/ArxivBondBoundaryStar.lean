import Exploding.Support.RNProofCore
import Exploding.Support.ExtMHProof11

/-!
# Star-connected inner boundary of a bond-cluster complement component

For any bond configuration, the inner boundary of any lattice component of the
complement of the root's actual open-bond component is star-connected. The proof
uses the lattice walk lift for the bond component and the deterministic boundary
interface theorem; it assumes no probabilistic or finiteness properties.
-/

namespace Exploding

open LatticeProb Relation

/-- The inner boundary of a lattice component outside an actual open-bond
component is star-connected. -/
theorem arxiv_innerBoundary_bond_star_connected {d : ℕ}
    (ζ : RnBond d → Bool) (i x : Site d) :
    xmh_SConn (innerBoundary
      (componentIn
        ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) x)) := by
  let I : Set (Site d) := {y | (openBondGraph ζ).Reachable i y}
  let H : Set (Site d) := componentIn Iᶜ x
  change xmh_SConn (innerBoundary H)
  have hi : i ∈ I := by
    change (openBondGraph ζ).Reachable i i
    exact SimpleGraph.Reachable.refl _
  have hIeq : componentIn I i = I := by
    ext y
    constructor
    · exact fun hy => hy.2.1
    · intro hy
      have hreach : (openBondGraph ζ).Reachable i y := hy
      obtain ⟨p⟩ := hreach
      obtain ⟨w, _⟩ := rn_lift_walk (i := i) p hi hy
      exact ⟨hi, hy, ⟨w⟩⟩
  have hIconn : ∀ u ∈ I, ∀ v ∈ I,
      ReflTransGen (fun a b => a ∈ I ∧ b ∈ I ∧ (lattice d).Adj a b) u v := by
    intro u hu v hv
    have h := xmh7_componentIn_conn (S := I) (x := i)
      (hIeq ▸ hu) (hIeq ▸ hv)
    simpa [hIeq] using h
  have hHconn : ∀ u ∈ H, ∀ v ∈ H,
      ReflTransGen (fun a b => a ∈ H ∧ b ∈ H ∧ (lattice d).Adj a b) u v := by
    intro u hu v hv
    exact xmh7_componentIn_conn hu hv
  have hdisj : ∀ z, z ∈ I → z ∈ H → False := by
    intro z hzI hzH
    exact hzH.2.1 hzI
  have hclose : ∀ b ∈ H, ∀ z, (lattice d).Adj b z → z ∉ I → z ∈ H :=
    fun b hb z hbz hzI => xmh7_componentIn_close hb (by simpa using hzI) hbz
  have hconnD : xmh_SConn {z | z ∈ H ∧ ∃ c ∈ I, (lattice d).Adj c z} := by
    intro u hu v hv
    exact xmh3_boundaryStar d I H hIconn hHconn hdisj hclose u v hu hv
  have hDeq : {z | z ∈ H ∧ ∃ c ∈ I, (lattice d).Adj c z} = innerBoundary H := by
    ext z
    constructor
    · rintro ⟨hzH, c, hcI, hcz⟩
      exact ⟨hzH, c, fun hcH => hdisj c hcI hcH, hcz.symm⟩
    · rintro ⟨hzH, y, hyH, hzy⟩
      refine ⟨hzH, y, ?_, hzy.symm⟩
      by_contra hyI
      exact hyH (hclose z hzH y hzy hyI)
  exact hDeq ▸ hconnD

end Exploding
