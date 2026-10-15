import Exploding.Frozen.CounterexampleArrival
import Exploding.Frozen.CounterexampleSupport
import Exploding.Support.ArxivCounterexampleSameWitness

open Exploding LatticeProb MeasureTheory Filter
open scoped Topology

/-- The exact corrected-source counterexample, assembled on one background from the
reviewed same-witness Support theorem. -/
theorem Exploding.ce_counterexample_complete (d : ℕ) (hd : 2 ≤ d) :
    ∃ η : Site d → ℤ, ∃ hη : Explosive η,
      (¬ ∀ x : Site d, 2 * (d : ℤ) - 2 ≤ η x) ∧
      (∀ n : ℕ, counterexampleArrival η hη ((n : ℤ) • e1 d) ≠ ⊤) ∧
      3 / 2 ≤ limsup
        (fun n : ℕ =>
          ((counterexampleArrival η hη ((n : ℤ) • e1 d)).toNat : ℝ) / (n : ℝ))
        atTop ∧
      liminf
        (fun n : ℕ =>
          ((counterexampleArrival η hη ((n : ℤ) • e1 d)).toNat : ℝ) / (n : ℝ))
        atTop = 1 ∧
      ¬ ∃ B : Set (Fin d → ℝ),
        MeasurableSet B ∧
        Tendsto
          (fun t : ℕ => volume (symmDiff (counterexampleSupport η hη t) B))
          atTop (nhds 0) := by
  classical
  obtain ⟨hη, hbelow, hFinite, hLimsup, hLiminf, hVolume⟩ :=
    ce_arxiv_counterexample_same_witness d hd
  refine ⟨ceEta d, hη, ?_⟩
  have hThresholdSet :
      {n : ℕ | 1 ≤ n ∧
        ¬ Stabilizable (fun x => ceEta d x + n * dirac (0 : Site d) x)}.Nonempty := by
    by_contra hEmpty
    apply hη
    intro n hn
    by_contra hstab
    exact hEmpty ⟨n, hn, hstab⟩
  have hThresholdMember :
      sInf {n : ℕ | 1 ≤ n ∧
        ¬ Stabilizable (fun x => ceEta d x + n * dirac (0 : Site d) x)} ∈
      {n : ℕ | 1 ≤ n ∧
        ¬ Stabilizable (fun x => ceEta d x + n * dirac (0 : Site d) x)} :=
    Nat.sInf_mem hThresholdSet
  have hThresholdPositive :
      1 ≤ counterexampleThreshold (ceEta d) hη := by
    change 1 ≤ sInf {n : ℕ | 1 ≤ n ∧
      ¬ Stabilizable (fun x => ceEta d x + n * dirac (0 : Site d) x)}
    exact hThresholdMember.1
  have hThresholdNew3 : counterexampleThreshold (ceEta d) hη = 3 := by
    change sInf {n : ℕ | 1 ≤ n ∧
      ¬ Stabilizable (fun x => ceEta d x + n * dirac (0 : Site d) x)} = 3
    exact aux_ce_sInf_eq' d hd
  have hThresholdOld3 : explosionThreshold (ceEta d) = 3 :=
    aux_ce_threshold' d hd
  have hThresholdCompatibility :
      counterexampleThreshold (ceEta d) hη = explosionThreshold (ceEta d) := by
    rw [hThresholdNew3, hThresholdOld3]
  have hPileCompatibility :
      counterexamplePile (ceEta d) hη = explodingPile (ceEta d) := by
    change (fun x => ceEta d x +
      (counterexampleThreshold (ceEta d) hη : ℤ) * dirac (0 : Site d) x) =
      (fun x => ceEta d x +
        (explosionThreshold (ceEta d) : ℤ) * dirac (0 : Site d) x)
    rw [hThresholdCompatibility]
  have hPileAtThree :
      counterexamplePile (ceEta d) hη =
        (fun x => ceEta d x + 3 * dirac (0 : Site d) x) := by
    calc
      counterexamplePile (ceEta d) hη = explodingPile (ceEta d) :=
        hPileCompatibility
      _ = (fun x => ceEta d x + 3 * dirac (0 : Site d) x) :=
        aux_ce_explodingPile_eq d hd
  have hArrivalCompatibility (x : Site d) :
      counterexampleArrival (ceEta d) hη x = arrival (ceEta d) x := by
    unfold counterexampleArrival
    rw [hPileCompatibility]
    symm
    exact aux_arrival_unfold d (ceEta d) x
  have hSupportCompatibility (t : ℕ) :
      counterexampleSupport (ceEta d) hη t =
        {y : Fin d → ℝ | 0 < podo (explodingPile (ceEta d)) t
          (nearestSite ((t : ℝ) • y))} := by
    change {y : Fin d → ℝ | 0 < podo (counterexamplePile (ceEta d) hη) t
      (nearestSite ((t : ℝ) • y))} = _
    rw [hPileCompatibility]
  refine ⟨hbelow, ?_⟩
  constructor
  · intro n
    simpa only [hArrivalCompatibility] using hFinite n
  constructor
  · simpa only [hArrivalCompatibility] using hLimsup
  constructor
  · simpa only [hArrivalCompatibility] using hLiminf
  · simpa only [hSupportCompatibility] using hVolume
