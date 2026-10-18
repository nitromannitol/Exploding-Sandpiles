# Source and declaration rulings

The source-facing declarations below select the corrected arXiv-format draft.
The official arXiv extraction and abstract remain unchanged. Marker changes
have explicit successors; historical declarations are retained in Git history.
These rulings record mathematical meaning and do not replace proof or source audits.

The corrected delivered-seed convention is `s0prime = eta + Delta w0`.
Measurable ergodicity replaces the stronger all-set predicate, and nonnegativity
is derived from the printed hypotheses. The source theorem constant/witness
order, full Boolean boundary data, separate dimension-one law, and complete
last-wave exterior clause are retained. The two added radius inputs are actual
cited propositions, not paper-owned proof steps. Their explicit-name version2
headers preserve their global names, literal bodies and definitional iff proofs.

## lem-square-lower-bound — version 4 to 5

Source: exploding-corrected-arxiv.tex:586-603 (label lemma:square_lower_bound). Frozen SHA-256 `19f817d7ff3eb7c2f9a112ea3fe3c0070bb13f4e9e9ca3a6c31ad2f0265dcf1b`.

```lean
theorem Exploding.Frozen.square_lower_bound (d : ℕ) (hd : 2 ≤ d)
    (hFdBR : Exploding.External.FeyDenBoerRedigCubicalCluster)
    (hFLP : Exploding.External.FeyLevinePeresRadius) :
    ∃ C : ℝ, 0 < C ∧
      ∀ η : Site d → ℤ,
        (∀ x, 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1) →
        ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, 1 ≤ m →
          Nat.ceil (C * (n : ℝ) ^ d *
            (if d = 2 then Real.log ((n : ℝ) + 1) else 1)) ≤ m →
          ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
            ∀ x ∈ cent d n, 0 < wave η m (0 : Site d) t x
```

## prop-generalized-last-wave — version 4 to 5

Source: exploding-corrected-arxiv.tex:1325-1329 (label prop:convergence_of_the_generalized_last_wave). Frozen SHA-256 `aa81aa6cdc69939e486fb145c1d7b7b7643e47511b4dbe84d71ad588ea823eaf`.

```lean
theorem Exploding.Frozen.convergence_of_the_generalized_last_wave (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0)
    (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η)
    (hstat : StationaryOn d L P) (herg : MeasurableErgodicOn d L P)
    (h1 : FiniteRangeOfDependence d P) (h3 : PathFillingHyp d P)
    (h4 : StronglyBoxCrossingHyp d P)
    (hLSS : Exploding.External.LiggettSchonmannStacey)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ N : (Fin d → ℝ) → ℝ,
      Continuous N ∧
      ConvexOn ℝ Set.univ N ∧
      (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
      ∀ᵐ η ∂P,
        Explosive η ∧ (∀ x : Site d, lastArrival η (0 : Site d) x ≠ ⊤) ∧
          ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
            ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
              |((lastArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
                - N y| ≤ ε
```

## thm-generalized-convergence — version 5 to 6

Source: exploding-corrected-arxiv.tex:1755-1759. Frozen SHA-256 `d32daec0ed262bf93997fd6bf958d784c860b5024f292c5a782cf8b0f332c546`.

```lean
theorem Exploding.Frozen.generalized_convergence (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0)
    (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η)
    (hstat : StationaryOn d L P) (herg : MeasurableErgodicOn d L P)
    (h1 : FiniteRangeOfDependence d P) (h3 : PathFillingHyp d P)
    (h4 : StronglyBoxCrossingHyp d P) (h5 : WaveApproximationHyp d P)
    (hLSS : Exploding.External.LiggettSchonmannStacey)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ N : (Fin d → ℝ) → ℝ,
      Continuous N ∧
      ConvexOn ℝ Set.univ N ∧
      (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
      ∀ᵐ η ∂P,
        Explosive η ∧ (∀ x : Site d, arrival η x ≠ ⊤) ∧
          ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
            ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
              |((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ) - N y| ≤ ε
```

## prop-explosion-criteria — version 3 to 4

Source: exploding-corrected-arxiv.tex:2388-2392 (label prop:explosion_criteria). Frozen SHA-256 `72c7f767456a36130729aa032ed6da22a650bd11c0d87266b9a785b73dab827f`.

```lean
theorem Exploding.Frozen.explosion_criteria (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0) (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η)
    (hstat : StationaryOn d L P) (herg : MeasurableErgodicOn d L P)
    (h1 : FiniteRangeOfDependence d P) (h2 : BoxCrossingHyp d P)
    (hrec : RecurrentLaw d P) :
    ExplosiveLaw d P
```

## prop-box-crossing — version 3 to 4

Source: exploding-corrected-arxiv.tex:2657-2659. Frozen SHA-256 `967eea86ece9bb02ada55289f36b6bb98ab9f02b4099f9067c43565191c91144`.

```lean
theorem Exploding.Frozen.box_crossing :
    (∀ (d : ℕ) (_hd : 2 ≤ d) (ν : Measure ℤ) (_hν : IsProbabilityMeasure ν)
      (_hlow : ν {m : ℤ | (d : ℤ) ≤ m} = 1) (_hhit : 0 < ν {(2 * (d : ℤ) - 1)})
      (_hSch : Exploding.External.SchonmannBootstrap),
      BoxCrossingHyp d (Measure.infinitePi fun _ : Site d => ν)) ∧
    (∀ (P : Measure (Site 1 → ℤ)) (_hP : IsProbabilityMeasure P)
      (_hsupp : P {η : Site 1 → ℤ | ∀ x, (1 : ℤ) ≤ η x} = 1),
      BoxCrossingHyp 1 P)
```

## lem-last-wave-bound — version 3 to 4

Source: exploding-corrected-arxiv.tex:858-863 (label lemma:last_wave_bound). Frozen SHA-256 `3760843f3135cb089b2282167e54ccfa110776cff8af977a314b73c7f3179774`.

```lean
theorem Exploding.Frozen.last_wave_bound (d : ℕ) (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (z : Site d) (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n z) (t : ℕ) (x : Site d) :
    lastWave η z t x ≤ 1 + penultimateWave η z x ∧
      (x ∉ penultimateCluster η z \ innerBoundary (penultimateCluster η z) →
        lastWave η z t x ≤ 1)
```

## prop-dimensional-reduction — version 3 to 4

Source: exploding-corrected-arxiv.tex:2526-2535 (label prop:dimensional_reduction). Frozen SHA-256 `678347f088aa6399bee44eabb178981923e8fa91f3fa119fb1550a2f5b25d7a1`.

```lean
theorem Exploding.Frozen.dimensional_reduction (d n : ℕ) (hd : 1 ≤ d) (beta : Site d → Bool)
    (η : Site (d + 1) → ℤ) (t : ℕ) (y : Site d) (hy : cons 1 y ∈ faceLow (d + 1) n 0) :
    bUpOdo beta n η t (cons 1 y) = bLowOdo beta n η t y ∧
      (bUpOdo beta n η t (cons 1 y) = 0 →
        bUpConf beta n η t (cons 1 y) = bLowConf beta n η t y + 2)
```

The six unchanged last-wave/arrival conclusions retain the same law and exact approved Antal-Pisztora input. Actual consumers supply the LSS and Mathieu proof companions. Garet-Marchand adds no unregistered premise. The separate planar minimum-order bound remains unclaimed until its own proof and registration.

## rem-sharp-planar-obstruction — new, version 1

Source: exploding-corrected-arxiv.tex:785-823 (remark Sharp planar obstruction, printed as Remark 1). Frozen SHA-256 `a086ab6a2d98e5e193a5bf73c82335824ffa3b2628bf1f418859acbf9777a03d`.

```lean
theorem Exploding.Frozen.sharp_planar_obstruction
    (hFDR : Exploding.External.FeyDenBoerRedigCubicalCluster)
    (hFLP : Exploding.External.FeyLevinePeresRadius) :
    ∃ c C : Real, 0 < c ∧ 0 < C ∧
      ∀ n : Nat, 1 ≤ n → ∃ M : Nat,
        1 ≤ M ∧
        (∀ x ∈ cent 2 n, ∃ t : Nat,
          0 < wave (fun _ : Site 2 => (2 : Int)) M (0 : Site 2) t x) ∧
        (∀ m : Nat, 1 ≤ m →
          (∀ x ∈ cent 2 n, ∃ t : Nat,
            0 < wave (fun _ : Site 2 => (2 : Int)) m (0 : Site 2) t x) → M ≤ m) ∧
        c * (n : Real)^2 * Real.log ((n : Real) + 1) ≤ (M : Real) ∧
        (M : Real) ≤ C * (n : Real)^2 * Real.log ((n : Real) + 1)
```

The least positive covering order is characterized inside the statement, and both bounds concern that same order with constants chosen before `n`. The only hypotheses are the two cited radius inputs already used by the sharp square lower bound; no new cited input or paper-owned premise is introduced. The lower bound uses the planar killed-Green logarithmic lower bound of Lattice-Probability in place of the printed early-return calculation; the source text is unchanged. See ledger/audits/2026-10-18-sharp-planar-obstruction.md.
