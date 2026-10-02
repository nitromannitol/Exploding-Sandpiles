/-
Boundary geometry of finite subsets of `ℤ^d`.  A ray from a point of a finite set leaves it,
and the last site inside is an inner-boundary site.  Hence the coordinate values and the
lines meeting the set are each at most as many as its inner-boundary sites, so the set has
at most `|∂B|^2` sites when `d ≥ 2`, and every point of the set is within sup-distance `|∂B|`
of an inner-boundary site.
-/
import Mathlib
import Exploding.Support.Percolation

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The coordinates of a point of the ray `x + k e_i`. -/
theorem xmg_ray_apply (x : Site d) (i : Fin d) (k : ℤ) (j : Fin d) :
    (x + k • unit i) j = x j + (if j = i then k else 0) := by
  by_cases h : j = i
  · subst h
    simp [unit]
  · simp [unit, h]

/-- The `i`-th coordinate of a point of the ray `x + k e_i`. -/
theorem xmg_ray_self (x : Site d) (i : Fin d) (k : ℤ) : (x + k • unit i) i = x i + k := by
  simp [unit]

/-- The other coordinates of a point of the ray `x + k e_i` are those of `x`. -/
theorem xmg_ray_ne (x : Site d) {i j : Fin d} (k : ℤ) (h : j ≠ i) :
    (x + k • unit i) j = x j := by
  simp [unit, h]

/-- The first exit of the ray `x + k e_i` from a finite set: the initial segment up to `k`
lies in the set and the next site does not. -/
theorem xmg_first_exit (B : Finset (Site d)) (i : Fin d) {x : Site d} (hx : x ∈ B) :
    ∃ k : ℕ, (∀ j : ℕ, j ≤ k → x + (j : ℤ) • unit i ∈ B) ∧
      x + ((k : ℤ) + 1) • unit i ∉ B := by
  classical
  have hex : ∃ k : ℕ, x + ((k : ℤ) + 1) • unit i ∉ B := by
    by_contra hcon
    push Not at hcon
    have hmaps : Set.MapsTo (fun k : ℕ => x + ((k : ℤ) + 1) • unit i)
        ↑(Finset.range (B.card + 1)) ↑B := fun k _ => hcon k
    have hinj : Set.InjOn (fun k : ℕ => x + ((k : ℤ) + 1) • unit i)
        ↑(Finset.range (B.card + 1)) := by
      intro a _ b _ hab
      have h : x i + ((a : ℤ) + 1) = x i + ((b : ℤ) + 1) := by
        simpa only [xmg_ray_self] using congrFun hab i
      exact_mod_cast (by linarith : (a : ℤ) = b)
    have h := Finset.card_le_card_of_injOn _ hmaps hinj
    rw [Finset.card_range] at h
    omega
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · simpa using hx
  · have hlt : j - 1 < Nat.find hex := by omega
    have h := Nat.find_min hex hlt
    have hcast : (((j - 1 : ℕ) : ℤ) + 1) = (j : ℤ) := by omega
    rw [hcast] at h
    exact not_not.mp h

/-- The last site of a ray inside the set is an inner-boundary site. -/
theorem xmg_mem_innerBoundary_of_exit (B : Finset (Site d)) (i : Fin d) (x : Site d) (k : ℕ)
    (hin : x + (k : ℤ) • unit i ∈ B) (hout : x + ((k : ℤ) + 1) • unit i ∉ B) :
    x + (k : ℤ) • unit i ∈ innerBoundary (B : Set (Site d)) := by
  refine ⟨by simpa using hin, x + ((k : ℤ) + 1) • unit i, by simpa using hout, ?_⟩
  refine ⟨i, Or.inl ?_⟩
  simp only [add_smul, one_smul, add_assoc]

/-- The inner boundary of a finite set is finite. -/
theorem xmg_innerBoundary_finite (B : Finset (Site d)) :
    (innerBoundary (B : Set (Site d))).Finite :=
  B.finite_toSet.subset fun _ hz => hz.1

/-- The `i`-th coordinate takes at most `|∂B|` values on `B`, given a second direction. -/
theorem xmg_card_proj_le (B : Finset (Site d)) {i j : Fin d} (hij : i ≠ j) :
    (B.image (fun x => x i)).card ≤ (innerBoundary (B : Set (Site d))).ncard := by
  classical
  have hfin := xmg_innerBoundary_finite B
  rw [Set.ncard_eq_toFinset_card _ hfin]
  have key : ∀ t ∈ B.image (fun x => x i), ∃ p ∈ hfin.toFinset, p i = t := by
    intro t ht
    obtain ⟨x, hxB, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨k, hseg, hout⟩ := xmg_first_exit B j hxB
    refine ⟨x + (k : ℤ) • unit j, ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset]
      exact xmg_mem_innerBoundary_of_exit B j x k (hseg k le_rfl) hout
    · rw [xmg_ray_apply, if_neg hij, add_zero]
  choose p hpT hpi using key
  let f : ℤ → Site d := fun t =>
    if h : t ∈ B.image (fun x => x i) then p t h else 0
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro t ht
    rw [Finset.mem_coe] at ht ⊢
    simp only [f, dif_pos ht]
    exact hpT t ht
  · intro t₁ ht₁ t₂ ht₂ heq
    rw [Finset.mem_coe] at ht₁ ht₂
    simp only [f, dif_pos ht₁, dif_pos ht₂] at heq
    rw [← hpi t₁ ht₁, ← hpi t₂ ht₂, heq]

/-- The lines parallel to `e_i` meeting `B` are at most `|∂B|` in number. -/
theorem xmg_card_lines_le (B : Finset (Site d)) (i : Fin d) :
    (B.image (fun x => Function.update x i 0)).card ≤
      (innerBoundary (B : Set (Site d))).ncard := by
  classical
  have hfin := xmg_innerBoundary_finite B
  rw [Set.ncard_eq_toFinset_card _ hfin]
  have key : ∀ l ∈ B.image (fun x => Function.update x i 0),
      ∃ p ∈ hfin.toFinset, Function.update p i 0 = l := by
    intro l hl
    obtain ⟨x, hxB, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨k, hseg, hout⟩ := xmg_first_exit B i hxB
    refine ⟨x + (k : ℤ) • unit i, ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset]
      exact xmg_mem_innerBoundary_of_exit B i x k (hseg k le_rfl) hout
    · funext j
      by_cases hj : j = i
      · subst hj
        simp
      · rw [Function.update_of_ne hj, Function.update_of_ne hj, xmg_ray_apply, if_neg hj,
          add_zero]
  choose p hpT hpl using key
  let f : Site d → Site d := fun l =>
    if h : l ∈ B.image (fun x => Function.update x i 0) then p l h else 0
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro l hl
    rw [Finset.mem_coe] at hl ⊢
    simp only [f, dif_pos hl]
    exact hpT l hl
  · intro l₁ hl₁ l₂ hl₂ heq
    rw [Finset.mem_coe] at hl₁ hl₂
    simp only [f, dif_pos hl₁, dif_pos hl₂] at heq
    rw [← hpl l₁ hl₁, ← hpl l₂ hl₂, heq]

/-- `B` injects into (its lines parallel to `e_i`) × (its `i`-th coordinate values). -/
theorem xmg_card_le_mul (B : Finset (Site d)) (i : Fin d) :
    B.card ≤ (B.image (fun x => Function.update x i 0)).card * (B.image (fun x => x i)).card := by
  classical
  rw [← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun x => (Function.update x i 0, x i)) ?_ ?_
  · intro x hx
    rw [Finset.mem_coe] at hx ⊢
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hx⟩
  · intro x _ y _ hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    funext j
    by_cases hj : j = i
    · subst hj
      exact h2
    · have h := congrFun h1 j
      rwa [Function.update_of_ne hj, Function.update_of_ne hj] at h

/-- **`|B| ≤ |∂B|^2`** for a finite subset of `ℤ^d`, `d ≥ 2`. -/
theorem xmg_card_le_sq (hd : 2 ≤ d) (B : Finset (Site d)) :
    B.card ≤ (innerBoundary (B : Set (Site d))).ncard ^ 2 := by
  obtain ⟨i₀, j₀, hij⟩ : ∃ i₀ j₀ : Fin d, i₀ ≠ j₀ :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  have h1 := xmg_card_le_mul B i₀
  have h2 := xmg_card_lines_le B i₀
  have h3 := xmg_card_proj_le B hij
  calc B.card
      ≤ (B.image (fun x => Function.update x i₀ 0)).card *
          (B.image (fun x => x i₀)).card := h1
    _ ≤ (innerBoundary (B : Set (Site d))).ncard * (innerBoundary (B : Set (Site d))).ncard :=
        Nat.mul_le_mul h2 h3
    _ = (innerBoundary (B : Set (Site d))).ncard ^ 2 := (sq _).symm

/-- A finite nonempty set in `ℤ^d`, `d ≥ 1`, has an inner-boundary site. -/
theorem xmg_innerBoundary_nonempty (hd : 1 ≤ d) (B : Finset (Site d)) (hB : B.Nonempty) :
    (innerBoundary (B : Set (Site d))).Nonempty := by
  obtain ⟨x, hx⟩ := hB
  obtain ⟨k, hseg, hout⟩ := xmg_first_exit B ⟨0, by omega⟩ hx
  exact ⟨_, xmg_mem_innerBoundary_of_exit B _ x k (hseg k le_rfl) hout⟩

/-- Every point of a finite set in `ℤ^d`, `d ≥ 2`, is within sup-distance `|∂B|` of an
inner-boundary site. -/
theorem xmg_exists_near (hd : 2 ≤ d) (B : Finset (Site d)) {x : Site d} (hx : x ∈ B) :
    ∃ p ∈ innerBoundary (B : Set (Site d)),
      ∀ i, |p i - x i| ≤ ((innerBoundary (B : Set (Site d))).ncard : ℤ) := by
  classical
  set i₀ : Fin d := ⟨0, by omega⟩ with hi₀
  have hij : i₀ ≠ ⟨1, by omega⟩ := by
    simp [hi₀, Fin.ext_iff]
  obtain ⟨k, hseg, hout⟩ := xmg_first_exit B i₀ hx
  refine ⟨x + (k : ℤ) • unit i₀,
    xmg_mem_innerBoundary_of_exit B i₀ x k (hseg k le_rfl) hout, ?_⟩
  have hk : k + 1 ≤ (B.image (fun y => y i₀)).card := by
    have hmaps : Set.MapsTo (fun j : ℕ => x i₀ + (j : ℤ)) ↑(Finset.range (k + 1))
        ↑(B.image (fun y => y i₀)) := by
      intro j hj
      rw [Finset.mem_coe, Finset.mem_range] at hj
      rw [Finset.mem_coe, Finset.mem_image]
      refine ⟨x + (j : ℤ) • unit i₀, hseg j (by omega), ?_⟩
      rw [xmg_ray_apply, if_pos rfl]
    have hinj : Set.InjOn (fun j : ℕ => x i₀ + (j : ℤ)) ↑(Finset.range (k + 1)) := by
      intro a _ b _ hab
      exact_mod_cast (by simpa using hab : (a : ℤ) = b)
    have h := Finset.card_le_card_of_injOn _ hmaps hinj
    rwa [Finset.card_range] at h
  have hkn : k + 1 ≤ (innerBoundary (B : Set (Site d))).ncard :=
    hk.trans (xmg_card_proj_le B hij)
  intro i
  rw [xmg_ray_apply]
  by_cases hi : i = i₀
  · rw [if_pos hi, add_sub_cancel_left, abs_of_nonneg (by positivity)]
    exact_mod_cast (by omega : k ≤ (innerBoundary (B : Set (Site d))).ncard)
  · rw [if_neg hi]
    simp

end Exploding
