module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChartMetric
public import Geometry.GluingInteriorMetric
public import Geometry.GluingSeamMetric
public import Geometry.GluingMixedMetric

@[expose] public section

/-!
# Tangent-form compatibility of the actual glued atlas

The actual interior, same-seam and mixed pullbacks imply compatibility on
every literal atlas overlap. Reverse mixed pullbacks use the constructed
forward derivative equivalence and the native inverse differential. Distinct
seam overlaps factor through an actual original interior chart, using its
true inverse law and the real derivative chain rule. No coordinate tensor
compatibility or inverse differential is supplied as an assumption.
-/

open Set Filter UpperHalfPlane
open scoped Topology ComplexConjugate

namespace SystolicGrowth

private theorem gluingChartTransition_fderiv_of_middle
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

private theorem gluingChartTangentForm_seamInterior_transition
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    {x : ℂ} (hx : x ∈ ((P.seamAngularComplexChart k θ).symm.trans e).source)
    (v u : ℂ) :
    P.gluingChartTangentForm e (((P.seamAngularComplexChart k θ).symm.trans e) x)
      (fderiv ℝ ((P.seamAngularComplexChart k θ).symm.trans e) x v)
      (fderiv ℝ ((P.seamAngularComplexChart k θ).symm.trans e) x u) =
        P.gluingChartTangentForm (P.seamAngularComplexChart k θ) x v u := by
  have hy : 0 < (((P.seamAngularComplexChart k θ).symm.trans e) x).im :=
    P.gluedInteriorComplexChart_target_im_pos e he (e.map_source hx.2)
  rw [P.gluingChartTangentForm_interior e he, P.gluingChartTangentForm_seam,
    gluingComplexHalfPlaneTangentForm_apply, gluingComplexCollarTangentForm_apply]
  simpa only [gluingHalfPlaneTangentForm,
    UpperHalfPlane.ofComplex_apply_of_im_pos hy, UpperHalfPlane.mk_im] using
    P.seamInterior_transition_tangentForm_pullback k θ e he hx v u

private theorem gluingChartTangentForm_interiorSeam_transition
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    (k : Fin (n - 1)) (θ : ℝ) {x : ℂ}
    (hx : x ∈ (e.symm.trans (P.seamAngularComplexChart k θ)).source) (v u : ℂ) :
    P.gluingChartTangentForm (P.seamAngularComplexChart k θ)
      ((e.symm.trans (P.seamAngularComplexChart k θ)) x)
      (fderiv ℝ (e.symm.trans (P.seamAngularComplexChart k θ)) x v)
      (fderiv ℝ (e.symm.trans (P.seamAngularComplexChart k θ)) x u) =
        P.gluingChartTangentForm e x v u := by
  let f := (P.seamAngularComplexChart k θ).symm.trans e
  have ht : x ∈ f.target := hx
  have hs : f.symm x ∈ f.source := f.symm.map_source ht
  obtain ⟨D, hD⟩ := P.seamInterior_transition_hasFDerivAt_equiv k θ e he hs
  have hInv := f.hasFDerivAt_symm ht hD
  have hPull := P.gluingChartTangentForm_seamInterior_transition k θ e he hs
    (D.symm v) (D.symm u)
  change P.gluingChartTangentForm e (f (f.symm x))
    (fderiv ℝ f (f.symm x) (D.symm v)) (fderiv ℝ f (f.symm x) (D.symm u)) =
      P.gluingChartTangentForm (P.seamAngularComplexChart k θ) (f.symm x)
        (D.symm v) (D.symm u) at hPull
  rw [hD.fderiv] at hPull
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
    f.right_inv ht] at hPull
  change P.gluingChartTangentForm (P.seamAngularComplexChart k θ) (f.symm x)
    (fderiv ℝ f.symm x v) (fderiv ℝ f.symm x u) = P.gluingChartTangentForm e x v u
  rw [hInv.fderiv]
  exact hPull.symm

private theorem gluingChartTangentForm_distinctSeam_transition
    (P : ExerciseGluingPreparation C g n genera X) (k l : Fin (n - 1))
    (hkl : k ≠ l) (θ ψ : ℝ) {x : ℂ}
    (hx : x ∈ ((P.seamAngularComplexChart k θ).symm.trans
      (P.seamAngularComplexChart l ψ)).source) (v u : ℂ) :
    P.gluingChartTangentForm (P.seamAngularComplexChart l ψ)
      (((P.seamAngularComplexChart k θ).symm.trans (P.seamAngularComplexChart l ψ)) x)
      (fderiv ℝ ((P.seamAngularComplexChart k θ).symm.trans
        (P.seamAngularComplexChart l ψ)) x v)
      (fderiv ℝ ((P.seamAngularComplexChart k θ).symm.trans
        (P.seamAngularComplexChart l ψ)) x u) =
        P.gluingChartTangentForm (P.seamAngularComplexChart k θ) x v u := by
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
  have hD := gluingChartTransition_fderiv_of_middle
    (P.seamAngularComplexChart k θ) (P.seamAngularComplexChart l ψ) e hx.1 hsource
    ((P.seamInterior_transition_contDiffAt k θ e he hfirst).differentiableAt (by simp))
    ((P.interiorSeam_transition_contDiffAt e he l ψ hsecond).differentiableAt (by simp))
  have hvalue : (e.symm.trans (P.seamAngularComplexChart l ψ))
      (((P.seamAngularComplexChart k θ).symm.trans e) x) =
      ((P.seamAngularComplexChart k θ).symm.trans (P.seamAngularComplexChart l ψ)) x := by
    change P.seamAngularComplexChart l ψ (e.symm (e ((P.seamAngularComplexChart k θ).symm x))) =
      P.seamAngularComplexChart l ψ ((P.seamAngularComplexChart k θ).symm x)
    rw [e.left_inv hsource]
  rw [hD]
  simp only [ContinuousLinearMap.comp_apply]
  rw [← hvalue]
  exact (P.gluingChartTangentForm_interiorSeam_transition e he l ψ hsecond
    (fderiv ℝ ((P.seamAngularComplexChart k θ).symm.trans e) x v)
    (fderiv ℝ ((P.seamAngularComplexChart k θ).symm.trans e) x u)).trans
      (P.gluingChartTangentForm_seamInterior_transition k θ e he hfirst v u)

/-- Every actual atlas transition preserves the concrete coordinate tangent
forms on its exact native source and arbitrary tangent vectors. -/
theorem gluingChartTangentForm_transition_pullback
    (P : ExerciseGluingPreparation C g n genera X)
    (e e' : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : e ∈ P.gluedComplexAtlas) (he' : e' ∈ P.gluedComplexAtlas)
    {x : ℂ} (hx : x ∈ (e.symm.trans e').source) (v u : ℂ) :
    P.gluingChartTangentForm e' ((e.symm.trans e') x)
      (fderiv ℝ (e.symm.trans e') x v) (fderiv ℝ (e.symm.trans e') x u) =
        P.gluingChartTangentForm e x v u := by
  rcases he with he | ⟨k, θ, rfl⟩
  · rcases he' with he' | ⟨l, ψ, rfl⟩
    · rw [P.gluingChartTangentForm_interior e he, P.gluingChartTangentForm_interior e' he']
      simpa only [gluingComplexHalfPlaneTangentForm_apply] using
        P.gluedInteriorComplexAtlas_transition_poincare_pullback e e' he he' x hx v u
    · exact P.gluingChartTangentForm_interiorSeam_transition e he l ψ hx v u
  · rcases he' with he' | ⟨l, ψ, rfl⟩
    · exact P.gluingChartTangentForm_seamInterior_transition k θ e' he' hx v u
    · by_cases hkl : k = l
      · subst l
        rw [P.gluingChartTangentForm_seam, P.gluingChartTangentForm_seam]
        simpa only [gluingComplexCollarTangentForm_apply] using
          P.seamAngularComplexChart_transition_tangentForm k θ ψ hx v u
      · exact P.gluingChartTangentForm_distinctSeam_transition k l hkl θ ψ hx v u

#print axioms gluingChartTangentForm_interiorSeam_transition
#print axioms gluingChartTangentForm_distinctSeam_transition
#print axioms gluingChartTangentForm_transition_pullback

end ExerciseGluingPreparation

end SystolicGrowth
