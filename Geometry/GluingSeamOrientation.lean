module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingSmoothAtlas
public import Geometry.GluingSeamMetric
public import Geometry.GluingPolarOrientation

@[expose] public section

/-!
# Orientation signs of the native seam transitions

The actual inverse differential preserves the negative mixed-transition
sign. Same-seam transitions have identity differential even at radius zero.
Distinct seam overlaps factor through a genuine original interior chart,
so their two negative mixed determinants multiply to a positive determinant.
-/

open Set Filter
open scoped Topology

namespace SystolicGrowth

private theorem gluingChartTransition_fderiv_of_middle_orientation
    {M : Type*} [TopologicalSpace M] (e₁ e₂ e : OpenPartialHomeomorph M ℂ)
    {x : ℂ} (hx : x ∈ e₁.target) (he : e₁.symm x ∈ e.source)
    (h₁ : DifferentiableAt ℝ (e₁.symm.trans e) x)
    (h₂ : DifferentiableAt ℝ (e.symm.trans e₂) (e (e₁.symm x))) :
    fderiv ℝ (e₁.symm.trans e₂) x =
      (fderiv ℝ (e.symm.trans e₂) (e (e₁.symm x))).comp
        (fderiv ℝ (e₁.symm.trans e) x) := by
  have hnear : ∀ᶠ y in 𝓝 x, e₁.symm y ∈ e.source :=
    (e₁.symm.continuousAt hx).eventually (e.open_source.mem_nhds he)
  have hlocal : (e₁.symm.trans e₂ : ℂ → ℂ) =ᶠ[𝓝 x]
      ((e.symm.trans e₂ : ℂ → ℂ) ∘ (e₁.symm.trans e : ℂ → ℂ)) := by
    filter_upwards [hnear] with y hy
    change e₂ (e₁.symm y) = e₂ (e.symm (e (e₁.symm y)))
    rw [e.left_inv hy]
  exact hlocal.fderiv_eq.trans (fderiv_comp x h₂ h₁)

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The native reverse mixed transition has negative real Jacobian
determinant by the actual forward differential and its genuine inverse. -/
theorem interiorSeam_transition_fderiv_det_neg
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    (k : Fin (n - 1)) (θ : ℝ) {x : ℂ}
    (hx : x ∈ (e.symm.trans (P.seamAngularComplexChart k θ)).source) :
    LinearMap.det (fderiv ℝ (e.symm.trans (P.seamAngularComplexChart k θ)) x).toLinearMap < 0 := by
  let F := (P.seamAngularComplexChart k θ).symm.trans e
  have ht : x ∈ F.target := hx
  have hs : F.symm x ∈ F.source := F.symm.map_source ht
  obtain ⟨D, hD⟩ := P.seamInterior_transition_hasFDerivAt_equiv k θ e he hs
  have hInv := F.hasFDerivAt_symm ht hD
  have hneg := P.seamInterior_transition_fderiv_det_neg k θ e he hs
  change LinearMap.det (fderiv ℝ F (F.symm x)).toLinearMap < 0 at hneg
  rw [hD.fderiv] at hneg
  change LinearMap.det (fderiv ℝ F.symm x).toLinearMap < 0
  rw [hInv.fderiv]
  change (D.symm : ℂ →L[ℝ] ℂ).det < 0
  rw [ContinuousLinearEquiv.det_coe_symm]
  exact inv_lt_zero.mpr hneg

/-- Same-seam transitions have positive determinant on the entire actual
overlap, including points lying exactly on the glued seam. -/
theorem seamAngularComplexChart_transition_fderiv_det_pos
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ ψ : ℝ)
    {x : ℂ} (hx : x ∈ ((P.seamAngularComplexChart k θ).symm.trans
      (P.seamAngularComplexChart k ψ)).source) :
    0 < LinearMap.det (fderiv ℝ ((P.seamAngularComplexChart k θ).symm.trans
      (P.seamAngularComplexChart k ψ)) x).toLinearMap := by
  rw [(P.seamAngularComplexChart_transition_hasFDerivAt k θ ψ hx).fderiv]
  simp

/-- The actual transition between distinct seam charts has positive
determinant: its two genuine mixed transitions both have negative sign. -/
theorem seamAngularComplexChart_distinct_transition_fderiv_det_pos
    (P : ExerciseGluingPreparation C g n genera X) (k l : Fin (n - 1))
    (hkl : k ≠ l) (θ ψ : ℝ) {x : ℂ}
    (hx : x ∈ ((P.seamAngularComplexChart k θ).symm.trans
      (P.seamAngularComplexChart l ψ)).source) :
    0 < LinearMap.det (fderiv ℝ ((P.seamAngularComplexChart k θ).symm.trans
      (P.seamAngularComplexChart l ψ)) x).toLinearMap := by
  obtain ⟨e, he, hsource⟩ :=
    P.seamAngularComplexChart_distinct_overlap_exists_interior_chart k l hkl θ ψ hx
  have hfirst : x ∈ ((P.seamAngularComplexChart k θ).symm.trans e).source :=
    ⟨hx.1, hsource⟩
  have hsecond : e ((P.seamAngularComplexChart k θ).symm x) ∈
      (e.symm.trans (P.seamAngularComplexChart l ψ)).source := by
    refine ⟨e.map_source hsource, ?_⟩
    change e.symm (e ((P.seamAngularComplexChart k θ).symm x)) ∈
      (P.seamAngularComplexChart l ψ).source
    rw [e.left_inv hsource]
    exact hx.2
  have hchain := gluingChartTransition_fderiv_of_middle_orientation
    (P.seamAngularComplexChart k θ) (P.seamAngularComplexChart l ψ) e hx.1 hsource
    ((P.seamInterior_transition_contDiffAt k θ e he hfirst).differentiableAt (by simp))
    ((P.interiorSeam_transition_contDiffAt e he l ψ hsecond).differentiableAt (by simp))
  rw [hchain]
  change 0 < LinearMap.det
    ((fderiv ℝ (e.symm.trans (P.seamAngularComplexChart l ψ))
      (e ((P.seamAngularComplexChart k θ).symm x))).toLinearMap.comp
        (fderiv ℝ ((P.seamAngularComplexChart k θ).symm.trans e) x).toLinearMap)
  rw [LinearMap.det_comp]
  exact mul_pos_of_neg_of_neg (P.interiorSeam_transition_fderiv_det_neg e he l ψ hsecond)
    (P.seamInterior_transition_fderiv_det_neg k θ e he hfirst)

/-- Every native seam-to-seam transition preserves orientation on its
literal overlap, whether the two chart entries use the same seam or not. -/
theorem seamAngularComplexChart_seam_transition_fderiv_det_pos
    (P : ExerciseGluingPreparation C g n genera X) (k l : Fin (n - 1)) (θ ψ : ℝ)
    {x : ℂ} (hx : x ∈ ((P.seamAngularComplexChart k θ).symm.trans
      (P.seamAngularComplexChart l ψ)).source) :
    0 < LinearMap.det (fderiv ℝ ((P.seamAngularComplexChart k θ).symm.trans
      (P.seamAngularComplexChart l ψ)) x).toLinearMap := by
  by_cases hkl : k = l
  · subst l
    exact P.seamAngularComplexChart_transition_fderiv_det_pos k θ ψ hx
  · exact P.seamAngularComplexChart_distinct_transition_fderiv_det_pos k l hkl θ ψ hx

end ExerciseGluingPreparation

#print axioms ExerciseGluingPreparation.interiorSeam_transition_fderiv_det_neg
#print axioms ExerciseGluingPreparation.seamAngularComplexChart_transition_fderiv_det_pos
#print axioms ExerciseGluingPreparation.seamAngularComplexChart_distinct_transition_fderiv_det_pos
#print axioms ExerciseGluingPreparation.seamAngularComplexChart_seam_transition_fderiv_det_pos

end SystolicGrowth
