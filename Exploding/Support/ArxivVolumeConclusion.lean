import Exploding.Support.ArxivVolumeLower

/-!
# Local translation continuity and the volume obstruction

Translations of arbitrary measurable sets are continuous in measure on a fixed bounded
window, even when the set has infinite global volume. The lower bound for the
threshold-three support then rules out convergence in global symmetric-difference volume.
-/

namespace Exploding

open Filter LatticeProb MeasureTheory Set
open scoped ENNReal symmDiff Topology

private def ceVolumeLocalBox (d : ℕ) : Set (Fin d → ℝ) :=
  Set.pi Set.univ fun _ : Fin d => Set.Icc (-4 : ℝ) 4

private theorem ceVolumeGridOmega_coord_bound (d : ℕ) (hd : 2 ≤ d)
    (y : Fin d → ℝ) (hy : y ∈ ceVolumeGridOmega d hd) (i : Fin d) :
    -1 ≤ y i ∧ y i ≤ 1 := by
  simp only [ceVolumeGridOmega, Set.mem_setOf_eq] at hy
  by_cases hi : i = ⟨0, by omega⟩
  · subst i
    exact ⟨by linarith [hy.1], by linarith [hy.2.1]⟩
  · have hsmall := (hy.2.2 i hi)
    have hdR : 2 ≤ (d : ℝ) := by exact_mod_cast hd
    have hden : 1 < 100 * (d : ℝ) := by nlinarith
    have hfrac : (1 / (100 * (d : ℝ)) : ℝ) < 1 := by
      apply (div_lt_iff₀ (by positivity : 0 < 100 * (d : ℝ))).2
      nlinarith
    have habs : |y i| < 1 := lt_trans hsmall hfrac
    exact ⟨(abs_lt.mp habs).1.le, (abs_lt.mp habs).2.le⟩

private theorem ceVolumeGridOmega_subset_localBox (d : ℕ) (hd : 2 ≤ d) :
    ceVolumeGridOmega d hd ⊆ ceVolumeLocalBox d := by
  intro y hy
  simp only [ceVolumeLocalBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  intro i
  have h := ceVolumeGridOmega_coord_bound d hd y hy i
  constructor <;> linarith

private theorem ceVolumeShift_coord_bound (d t : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    -1 ≤ ceVolumeShift d t hd i ∧ ceVolumeShift d t hd i ≤ 1 := by
  by_cases hi : i = ⟨1, by omega⟩
  · subst i
    have hnum : (ceVolumeE₂ d hd ⟨1, by omega⟩ : ℝ) = 1 := by
      change ((LatticeProb.unit (⟨1, by omega⟩ : Fin d) ⟨1, by omega⟩ : ℤ) : ℝ) = 1
      simp [LatticeProb.unit]
    by_cases ht : t = 0
    · subst t
      simp [ceVolumeShift, hnum]
    · have htpos : (0 : ℝ) < (t : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero ht
      have htge : (1 : ℝ) ≤ (t : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr ht)
      have hquot : 0 ≤ (1 : ℝ) / (t : ℝ) ∧ (1 : ℝ) / (t : ℝ) ≤ 1 := by
        constructor
        · exact div_nonneg (by norm_num) htpos.le
        · apply (div_le_iff₀ htpos).2
          nlinarith
      change -1 ≤ (ceVolumeE₂ d hd ⟨1, by omega⟩ : ℝ) / (t : ℝ) ∧
        (ceVolumeE₂ d hd ⟨1, by omega⟩ : ℝ) / (t : ℝ) ≤ 1
      rw [hnum]
      constructor
      · exact le_trans (by norm_num) hquot.1
      · exact hquot.2
  · have hcoord : ceVolumeE₂ d hd i = 0 := by
      change LatticeProb.unit (⟨1, by omega⟩ : Fin d) i = 0
      simp [LatticeProb.unit, hi]
    simp [ceVolumeShift, hcoord]

private theorem ceVolumeGridOmega_add_shift_mem_localBox (d t : ℕ) (hd : 2 ≤ d)
    (y : Fin d → ℝ) (hy : y ∈ ceVolumeGridOmega d hd) :
    y + ceVolumeShift d t hd ∈ ceVolumeLocalBox d := by
  simp only [ceVolumeLocalBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  intro i
  have hyi := ceVolumeGridOmega_coord_bound d hd y hy i
  have hsi := ceVolumeShift_coord_bound d t hd i
  simp only [Pi.add_apply]
  constructor <;> linarith

private theorem ceVolumeShift_tendsto (d : ℕ) (hd : 2 ≤ d) :
    Tendsto (fun t : ℕ => ceVolumeShift d t hd) atTop (𝓝 0) := by
  rw [tendsto_pi_nhds]
  intro i
  by_cases hi : i = ⟨1, by omega⟩
  · subst i
    have hnum : (ceVolumeE₂ d hd ⟨1, by omega⟩ : ℝ) = 1 := by
      change ((LatticeProb.unit (⟨1, by omega⟩ : Fin d) ⟨1, by omega⟩ : ℤ) : ℝ) = 1
      simp [LatticeProb.unit]
    simpa only [ceVolumeShift, hnum, Pi.zero_apply] using
      (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (1 : ℝ))
  · have hcoord : ceVolumeE₂ d hd i = 0 := by
      change LatticeProb.unit (⟨1, by omega⟩ : Fin d) i = 0
      simp [LatticeProb.unit, hi]
    simpa only [ceVolumeShift, hcoord, Int.cast_zero, zero_div, Pi.zero_apply] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

private def ceVolumeTranslateKernel (d : ℕ) :
    ContinuousMap ((Fin d → ℝ) × (Fin d → ℝ)) (Fin d → ℝ) :=
  ⟨fun p => p.2 + p.1, continuous_snd.add continuous_fst⟩

/-- The actual positive support is measurable at every scale, including scale zero. -/
private theorem measurableSet_ceVolumeAtTime (d t : ℕ) : MeasurableSet (ceVolumeAtTime d t) := by
  classical
  let σ : Site d → ℤ := fun x => ceEta d x + 3 * dirac (0 : Site d) x
  change MeasurableSet {y : Fin d → ℝ | 0 < podo σ t (nearestSite ((t : ℝ) • y))}
  by_cases ht : 1 ≤ t
  · have hunion :
        {y : Fin d → ℝ | 0 < podo σ t (nearestSite ((t : ℝ) • y))} =
          ⋃ x : {x : Site d // 0 < podo σ t x}, ceVolumeCell d t x.1 := by
      ext y
      constructor
      · intro hy
        exact Set.mem_iUnion.mpr
          ⟨⟨nearestSite ((t : ℝ) • y), hy⟩, by
            change nearestSite ((t : ℝ) • y) = nearestSite ((t : ℝ) • y)
            rfl⟩
      · intro hy
        rcases Set.mem_iUnion.mp hy with ⟨x, hx⟩
        have hsite : nearestSite ((t : ℝ) • y) = x.1 := by
          exact Set.mem_setOf_eq.mp hx
        change 0 < podo σ t (nearestSite ((t : ℝ) • y))
        rw [hsite]
        exact x.2
    rw [hunion]
    exact MeasurableSet.iUnion fun x => measurableSet_ceVolumeCell d t x.1 ht
  · have ht0 : t = 0 := by omega
    subst t
    change MeasurableSet
      {y : Fin d → ℝ | 0 < podo σ 0 (nearestSite ((0 : ℝ) • y))}
    have hconst :
        {y : Fin d → ℝ | 0 < podo σ 0 (nearestSite ((0 : ℝ) • y))} =
          if 0 < podo σ 0 (0 : Site d) then Set.univ else ∅ := by
      ext y
      simp
    rw [hconst]
    split_ifs <;> simp

/-- Every measurable set has vanishing translated symmetric difference inside the fixed
grid window. Only the restriction to a finite-volume box is used. -/
theorem ce_volume_local_translation_tendsto (d : ℕ) (hd : 2 ≤ d)
    (B : Set (Fin d → ℝ)) (hB : MeasurableSet B) :
    Tendsto
      (fun t : ℕ => volume
        ((symmDiff B {y | y + ceVolumeShift d t hd ∈ B}) ∩ ceVolumeGridOmega d hd))
      atTop (𝓝 0) := by
  classical
  let K := ceVolumeLocalBox d
  let C := B ∩ K
  have hKcompact : IsCompact K := by
    dsimp [K, ceVolumeLocalBox]
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hKmeas : MeasurableSet K := by
    dsimp [K, ceVolumeLocalBox]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hCmeas : MeasurableSet C := hB.inter hKmeas
  have hCfinite : volume C ≠ ∞ :=
    ((measure_mono Set.inter_subset_right).trans_lt hKcompact.measure_lt_top).ne
  let family : ContinuousMap (Fin d → ℝ) (ContinuousMap (Fin d → ℝ) (Fin d → ℝ)) :=
    (ceVolumeTranslateKernel d).curry
  let f : ℕ → ContinuousMap (Fin d → ℝ) (Fin d → ℝ) :=
    fun t => family (ceVolumeShift d t hd)
  have hfamily_zero : family 0 = ContinuousMap.id (Fin d → ℝ) := by
    ext y
    simp [family, ceVolumeTranslateKernel]
  have hf : Tendsto f atTop (𝓝 (ContinuousMap.id (Fin d → ℝ))) := by
    rw [← hfamily_zero]
    exact family.continuous.continuousAt.tendsto.comp (ceVolumeShift_tendsto d hd)
  have hpres (t : ℕ) : MeasurePreserving (f t) volume volume := by
    change MeasurePreserving (fun y : Fin d → ℝ => y + ceVolumeShift d t hd) volume volume
    exact MeasureTheory.measurePreserving_add_right volume (ceVolumeShift d t hd)
  have hpre := MeasureTheory.tendsto_measure_symmDiff_preimage_nhds_zero hf
    (Eventually.of_forall hpres) (MeasurePreserving.id volume)
    hCmeas.nullMeasurableSet hCfinite
  have hglobal : Tendsto (fun t => volume (C ∆ (f t ⁻¹' C))) atTop (𝓝 0) := by
    simpa [symmDiff_comm] using hpre
  have hlocal_le (t : ℕ) :
      volume ((symmDiff B {y | y + ceVolumeShift d t hd ∈ B}) ∩ ceVolumeGridOmega d hd) ≤
        volume (C ∆ (f t ⁻¹' C)) := by
    apply measure_mono
    intro y hy
    rcases hy with ⟨hyDiff, hyOmega⟩
    have hyK : y ∈ K := ceVolumeGridOmega_subset_localBox d hd hyOmega
    have hyhK : y + ceVolumeShift d t hd ∈ K :=
      ceVolumeGridOmega_add_shift_mem_localBox d t hd y hyOmega
    have hCmem : y ∈ C ↔ y ∈ B := by simp [C, hyK]
    have hCshift : y + ceVolumeShift d t hd ∈ C ↔
        y + ceVolumeShift d t hd ∈ B := by simp [C, hyhK]
    have hfapply : f t y = y + ceVolumeShift d t hd := by
      rfl
    have hpre : y ∈ f t ⁻¹' C ↔ y + ceVolumeShift d t hd ∈ C := by
      change f t y ∈ C ↔ _
      rw [hfapply]
    have hshiftSet : y ∈ f t ⁻¹' C ↔
        y ∈ {z | z + ceVolumeShift d t hd ∈ B} := by
      constructor
      · intro hyPre
        exact Set.mem_setOf_eq.mpr (hCshift.mp (hpre.mp hyPre))
      · intro hyPre
        exact hpre.mpr (hCshift.mpr (Set.mem_setOf_eq.mp hyPre))
    have hmem : y ∈ symmDiff B {z | z + ceVolumeShift d t hd ∈ B} ↔
        y ∈ symmDiff C (f t ⁻¹' C) := by
      rw [Set.mem_symmDiff, Set.mem_symmDiff]
      simp [hCmem, hshiftSet]
    exact hmem.mp hyDiff
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hglobal
    (fun _ => bot_le) hlocal_le

/-- The actual threshold-three support cannot converge to any measurable set in global
symmetric-difference volume. -/
theorem ce_volume_no_global_limit (d : ℕ) (hd : 2 ≤ d) :
    ¬ ∃ B : Set (Fin d → ℝ), MeasurableSet B ∧
      Tendsto (fun t : ℕ => volume (symmDiff (ceVolumeAtTime d t) B)) atTop (𝓝 0) := by
  rintro ⟨B, hB, herror⟩
  let err : ℕ → ℝ≥0∞ := fun t => volume (symmDiff (ceVolumeAtTime d t) B)
  let localErr : ℕ → ℝ≥0∞ := fun t =>
    volume ((symmDiff (ceVolumeAtTime d t)
      {y | y + ceVolumeShift d t hd ∈ ceVolumeAtTime d t}) ∩ ceVolumeGridOmega d hd)
  let bshift : ℕ → ℝ≥0∞ := fun t =>
    volume ((symmDiff B {y | y + ceVolumeShift d t hd ∈ B}) ∩ ceVolumeGridOmega d hd)
  have hBshift : Tendsto bshift atTop (𝓝 0) := by
    simpa [bshift] using ce_volume_local_translation_tendsto d hd B hB
  have herr : Tendsto err atTop (𝓝 0) := by simpa [err] using herror
  have hupper (t : ℕ) : localErr t ≤ err t + bshift t + err t := by
    have hA : MeasurableSet (ceVolumeAtTime d t) := measurableSet_ceVolumeAtTime d t
    have hpres : MeasurePreserving
        (fun y : Fin d → ℝ => y + ceVolumeShift d t hd) volume volume := by
      exact MeasureTheory.measurePreserving_add_right volume (ceVolumeShift d t hd)
    let τ : (Fin d → ℝ) → (Fin d → ℝ) := fun y => y + ceVolumeShift d t hd
    have htriangle :
        (symmDiff (ceVolumeAtTime d t)
          {y | y + ceVolumeShift d t hd ∈ ceVolumeAtTime d t}) ∩ ceVolumeGridOmega d hd ⊆
          symmDiff (ceVolumeAtTime d t) B ∪
            ((symmDiff B {y | y + ceVolumeShift d t hd ∈ B}) ∩ ceVolumeGridOmega d hd ∪
              symmDiff {y | y + ceVolumeShift d t hd ∈ B}
                {y | y + ceVolumeShift d t hd ∈ ceVolumeAtTime d t}) := by
      intro y hy
      rcases hy with ⟨hyDiff, hyOmega⟩
      have hfirst := (symmDiff_triangle (ceVolumeAtTime d t) B
        {y | y + ceVolumeShift d t hd ∈ ceVolumeAtTime d t}) hyDiff
      rcases hfirst with h | h
      · exact Or.inl h
      · have hsecond := (symmDiff_triangle B
          {y | y + ceVolumeShift d t hd ∈ B}
          {y | y + ceVolumeShift d t hd ∈ ceVolumeAtTime d t}) h
        rcases hsecond with h | h
        · exact Or.inr (Or.inl ⟨h, hyOmega⟩)
        · exact Or.inr (Or.inr h)
    have htranslated :
        volume (symmDiff {y | y + ceVolumeShift d t hd ∈ B}
          {y | y + ceVolumeShift d t hd ∈ ceVolumeAtTime d t}) =
          volume (symmDiff (ceVolumeAtTime d t) B) := by
      change volume ((τ ⁻¹' B) ∆ (τ ⁻¹' ceVolumeAtTime d t)) = _
      rw [← preimage_symmDiff]
      calc
        volume (τ ⁻¹' (B ∆ ceVolumeAtTime d t)) = volume (B ∆ ceVolumeAtTime d t) :=
          hpres.measure_preimage (hB.symmDiff hA).nullMeasurableSet
        _ = volume (symmDiff (ceVolumeAtTime d t) B) := by rw [symmDiff_comm]
    have hmeasure :
        volume ((symmDiff (ceVolumeAtTime d t)
          {y | y + ceVolumeShift d t hd ∈ ceVolumeAtTime d t}) ∩ ceVolumeGridOmega d hd) ≤
          volume (symmDiff (ceVolumeAtTime d t) B) +
            (volume ((symmDiff B {y | y + ceVolumeShift d t hd ∈ B}) ∩
              ceVolumeGridOmega d hd) +
              volume (symmDiff {y | y + ceVolumeShift d t hd ∈ B}
                {y | y + ceVolumeShift d t hd ∈ ceVolumeAtTime d t})) := by
      calc
        _ ≤ volume (symmDiff (ceVolumeAtTime d t) B ∪
            ((symmDiff B {y | y + ceVolumeShift d t hd ∈ B}) ∩
              ceVolumeGridOmega d hd ∪
              symmDiff {y | y + ceVolumeShift d t hd ∈ B}
                {y | y + ceVolumeShift d t hd ∈ ceVolumeAtTime d t})) :=
              measure_mono htriangle
        _ ≤ volume (symmDiff (ceVolumeAtTime d t) B) +
            volume ((symmDiff B {y | y + ceVolumeShift d t hd ∈ B}) ∩
              ceVolumeGridOmega d hd ∪
              symmDiff {y | y + ceVolumeShift d t hd ∈ B}
                {y | y + ceVolumeShift d t hd ∈ ceVolumeAtTime d t}) :=
              measure_union_le _ _
        _ ≤ _ := by
          rw [measure_symmDiff_eq hA.nullMeasurableSet hB.nullMeasurableSet]
          have hFG :
              volume ((symmDiff B {y | y + ceVolumeShift d t hd ∈ B}) ∩
                ceVolumeGridOmega d hd ∪
                symmDiff {y | y + ceVolumeShift d t hd ∈ B}
                  {y | y + ceVolumeShift d t hd ∈ ceVolumeAtTime d t}) ≤
              volume ((symmDiff B {y | y + ceVolumeShift d t hd ∈ B}) ∩
                ceVolumeGridOmega d hd) +
                volume (symmDiff {y | y + ceVolumeShift d t hd ∈ B}
                  {y | y + ceVolumeShift d t hd ∈ ceVolumeAtTime d t}) := by
            exact measure_union_le _ _
          calc
            (volume (ceVolumeAtTime d t \ B) + volume (B \ ceVolumeAtTime d t)) +
                volume ((symmDiff B {y | y + ceVolumeShift d t hd ∈ B}) ∩
                  ceVolumeGridOmega d hd ∪
                  symmDiff {y | y + ceVolumeShift d t hd ∈ B}
                    {y | y + ceVolumeShift d t hd ∈ ceVolumeAtTime d t}) =
                volume ((symmDiff B {y | y + ceVolumeShift d t hd ∈ B}) ∩
                    ceVolumeGridOmega d hd ∪
                    symmDiff {y | y + ceVolumeShift d t hd ∈ B}
                      {y | y + ceVolumeShift d t hd ∈ ceVolumeAtTime d t}) +
                  (volume (ceVolumeAtTime d t \ B) + volume (B \ ceVolumeAtTime d t)) := by
              ac_rfl
            _ = (volume (ceVolumeAtTime d t \ B) + volume (B \ ceVolumeAtTime d t)) +
                volume ((symmDiff B {y | y + ceVolumeShift d t hd ∈ B}) ∩
                  ceVolumeGridOmega d hd ∪
                  symmDiff {y | y + ceVolumeShift d t hd ∈ B}
                    {y | y + ceVolumeShift d t hd ∈ ceVolumeAtTime d t}) := by
              ac_rfl
            _ ≤ (volume ((symmDiff B {y | y + ceVolumeShift d t hd ∈ B}) ∩
                  ceVolumeGridOmega d hd) +
                  volume (symmDiff {y | y + ceVolumeShift d t hd ∈ B}
                    {y | y + ceVolumeShift d t hd ∈ ceVolumeAtTime d t})) +
                (volume (ceVolumeAtTime d t \ B) + volume (B \ ceVolumeAtTime d t)) :=
              by
                calc
                  _ ≤ (volume (ceVolumeAtTime d t \ B) + volume (B \ ceVolumeAtTime d t)) +
                      (volume ((symmDiff B {y | y + ceVolumeShift d t hd ∈ B}) ∩
                        ceVolumeGridOmega d hd) +
                        volume (symmDiff {y | y + ceVolumeShift d t hd ∈ B}
                          {y | y + ceVolumeShift d t hd ∈ ceVolumeAtTime d t})) :=
                    add_le_add_right hFG
                      (volume (ceVolumeAtTime d t \ B) + volume (B \ ceVolumeAtTime d t))
                  _ = _ := by ac_rfl
            _ = (volume (ceVolumeAtTime d t \ B) + volume (B \ ceVolumeAtTime d t)) +
                (volume ((symmDiff B {y | y + ceVolumeShift d t hd ∈ B}) ∩
                  ceVolumeGridOmega d hd) +
                  volume (symmDiff {y | y + ceVolumeShift d t hd ∈ B}
                    {y | y + ceVolumeShift d t hd ∈ ceVolumeAtTime d t})) := by
              ac_rfl
    simpa [err, bshift, localErr, htranslated, add_assoc] using hmeasure
  have hbound : Tendsto (fun t => err t + bshift t + err t) atTop (𝓝 0) := by
    simpa using (herr.add hBshift).add herr
  have hlocal : Tendsto localErr atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
      (fun _ => bot_le) hupper
  have hcpos : 0 < ENNReal.ofReal (ceVolumeLowerConstant d) :=
    ENNReal.ofReal_pos.mpr (ceVolumeLowerConstant_pos d hd)
  have hcne : ENNReal.ofReal (ceVolumeLowerConstant d) ≠ 0 := hcpos.ne'
  have hctop : ENNReal.ofReal (ceVolumeLowerConstant d) ≠ ∞ := ENNReal.ofReal_ne_top
  have hchalf : ENNReal.ofReal (ceVolumeLowerConstant d) / 2 <
      ENNReal.ofReal (ceVolumeLowerConstant d) := ENNReal.half_lt_self hcne hctop
  have hhalfpos : 0 < ENNReal.ofReal (ceVolumeLowerConstant d) / 2 :=
    ENNReal.half_pos hcne
  have hlarge : ∀ᶠ t : ℕ in atTop, 1000000 * d ≤ t :=
    eventually_atTop.2 ⟨1000000 * d, fun _ ht => ht⟩
  have hlower : ∀ᶠ t : ℕ in atTop,
      ENNReal.ofReal (ceVolumeLowerConstant d) ≤ localErr t :=
    hlarge.mono fun t ht => by
      simpa [localErr] using ce_volume_translation_lower d hd t ht
  have hsmall : ∀ᶠ t : ℕ in atTop,
      localErr t ≤ ENNReal.ofReal (ceVolumeLowerConstant d) / 2 :=
    (ENNReal.tendsto_nhds_zero.mp hlocal)
      (ENNReal.ofReal (ceVolumeLowerConstant d) / 2) hhalfpos
  have hfalse : ∀ᶠ t : ℕ in atTop, False :=
    (hlower.and hsmall).mono fun _ h => (not_le_of_gt hchalf) (le_trans h.1 h.2)
  rcases hfalse.exists with ⟨_, hfalse⟩
  exact hfalse

end Exploding
