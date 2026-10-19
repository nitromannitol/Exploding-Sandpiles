/-
Proposition 5.1 (generalized last wave), closeness of the arrival times, part I:
the closeness of the penultimate-cluster and last-wave arrival times, the general-law Lemma 3.7.

Almost surely the infinite cluster of strongly box-crossing tiles exists (`s3k_renorm`, from the cited
percolation results) and path-filling holds (Hypothesis 3); on such a background the closeness
holds with an exponent depending only on `d` and the path-filling exponent (`s3k_close_of_data`).
-/
import Exploding.Support.S3CloseH

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

/-- **The closeness of the two arrival times** (the general-law Lemma 3.7). -/
theorem s3k_close (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (P : Measure (Site d → ℤ)) : glws_Close d ηmin P := by
  intro hP hsupp h1 h3 h4 hLSS hLSSB hHole hChem
  obtain ⟨k, hk, c, C, hc, hC, hclu⟩ := s3k_renorm d P hd hP h1 h4 hLSS hLSSB hHole hChem
  obtain ⟨γp, hγp, hpf⟩ := h3
  have hd1 : 1 ≤ d := by omega
  refine ⟨s3k_Etop d γp + 1, by linarith [(s3k_E_ge d hd1 γp hγp).2.2.2], ?_⟩
  filter_upwards [hclu, hpf, hsupp] with η hη1 hη2 hη3
  have hlow : ∀ x, 0 ≤ η x := fun x => le_trans hηmin (hη3 x).1
  have hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1 := fun x => (hη3 x).2
  obtain ⟨Cinf, hinf, hgood, hconn, ⟨n0h, hhole⟩, ⟨n0c, hchem⟩⟩ := hη1
  let D : S3kData d η k Cinf γp C :=
    { hd := hd
      hlow := hlow
      hhigh := hhigh
      hk := hk
      hinf := hinf
      hgood := hgood
      hconn := hconn
      n0h := n0h
      hole := hhole
      hCch := hC.le
      n0c := n0c
      hchem := fun n hn x hx y hy hxn hlog => by
        obtain ⟨m, hm, _, hmC⟩ := hchem n hn x hx y hy hxn hlog
        exact ⟨m, hm, hmC⟩
      hγp := hγp
      hpf := hη2 }
  obtain ⟨n0, hn0⟩ := s3k_close_of_data D
  exact ⟨n0, fun n hn x hx => hn0 n hn x hx⟩

end Exploding
