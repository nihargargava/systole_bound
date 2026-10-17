module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingInteriorTransitions
public import Geometry.GluingSeamTransitions
public import Geometry.GluingReverseTransitions
public import Geometry.GluingSeamOverlap

@[expose] public section

/-!
# Smoothness of the actual glued atlas

Coordinate changes are checked on their native open overlap domains.
Distinct seam neighborhoods may overlap in component interiors; their
changes of coordinates must factor through a genuine interior chart.
-/

open Set Filter
open scoped Topology Manifold

namespace SystolicGrowth

/-- Smooth coordinate changes through a genuine intermediate chart compose
locally. The inverse identity is used only in that chart's actual source. -/
theorem gluingChartTransition_contDiffAt_of_middle
    {M : Type*} [TopologicalSpace M] (e₁ e₂ e : OpenPartialHomeomorph M ℂ)
    {x : ℂ} (hx : x ∈ e₁.target) (he : e₁.symm x ∈ e.source)
    (h₁ : ContDiffAt ℝ ⊤ (e₁.symm.trans e) x)
    (h₂ : ContDiffAt ℝ ⊤ (e.symm.trans e₂) (e (e₁.symm x))) :
    ContDiffAt ℝ ⊤ (e₁.symm.trans e₂) x := by
  have hcomp := h₂.comp x h₁
  have hnear : ∀ᶠ y in 𝓝 x, e₁.symm y ∈ e.source :=
    (e₁.symm.continuousAt hx).eventually (e.open_source.mem_nhds he)
  have hlocal : (fun y => e₂ (e₁.symm y)) =ᶠ[𝓝 x]
      (fun y => e₂ (e.symm (e (e₁.symm y)))) := by
    filter_upwards [hnear] with y hy
    rw [e.left_inv hy]
  exact hcomp.congr_of_eventuallyEq hlocal

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Distinct seam charts overlap only at actual original interior points.
Their coordinate change factors locally through a constructed interior chart. -/
theorem seamAngularComplexChart_distinct_trans_contDiffOn
    (P : ExerciseGluingPreparation C g n genera X) (k l : Fin (n - 1))
    (hkl : k ≠ l) (θ ψ : ℝ) :
    ContDiffOn ℝ ⊤
      ((P.seamAngularComplexChart k θ).symm.trans (P.seamAngularComplexChart l ψ))
      ((P.seamAngularComplexChart k θ).symm.trans (P.seamAngularComplexChart l ψ)).source := by
  intro x hx
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
  exact (gluingChartTransition_contDiffAt_of_middle
    (P.seamAngularComplexChart k θ) (P.seamAngularComplexChart l ψ) e hx.1 hsource
    (P.seamInterior_transition_contDiffAt k θ e he hfirst)
    (P.interiorSeam_transition_contDiffAt e he l ψ hsecond)).contDiffWithinAt

/-- All coordinate changes in the original concrete atlas are real analytic
on their exact native sources, including seam points and distinct-collar overlaps. -/
theorem gluedComplexAtlas_transition_contDiffOn
    (P : ExerciseGluingPreparation C g n genera X)
    (e e' : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : e ∈ P.gluedComplexAtlas) (he' : e' ∈ P.gluedComplexAtlas) :
    ContDiffOn ℝ ⊤ (e.symm.trans e') (e.symm.trans e').source := by
  rcases he with he | ⟨k, θ, rfl⟩
  · rcases he' with he' | ⟨l, ψ, rfl⟩
    · exact P.gluedInteriorComplexAtlas_transition_contDiffOn e e' he he'
    · exact P.interiorSeam_transition_contDiffOn e he l ψ
  · rcases he' with he' | ⟨l, ψ, rfl⟩
    · exact P.seamInterior_transition_contDiffOn k θ e' he'
    · by_cases hkl : k = l
      · subst l
        exact P.seamAngularComplexChart_trans_contDiffOn k θ ψ
      · exact P.seamAngularComplexChart_distinct_trans_contDiffOn k l hkl θ ψ

/-- The actual quotient, with its original topology and concrete charts,
is a native real-analytic manifold. This does not yet construct a global metric. -/
noncomputable instance gluedCarrierIsManifold
    (P : ExerciseGluingPreparation C g n genera X) :
    IsManifold (modelWithCornersSelf ℝ ℂ) ⊤ P.GluedCarrier := by
  apply isManifold_of_contDiffOn (modelWithCornersSelf ℝ ℂ) ⊤ P.GluedCarrier
  intro e e' he he'
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, preimage_id, Set.range_id, inter_univ] using
    P.gluedComplexAtlas_transition_contDiffOn e e' he he'

/-- In particular the unchanged concrete charted space has the C¹ structure
required by native tangent bundles and continuous Riemannian metrics. -/
theorem gluedCarrier_isManifold_one
    (P : ExerciseGluingPreparation C g n genera X) :
    IsManifold (modelWithCornersSelf ℝ ℂ) 1 P.GluedCarrier := inferInstance

end ExerciseGluingPreparation

#print axioms gluingChartTransition_contDiffAt_of_middle
#print axioms ExerciseGluingPreparation.seamAngularComplexChart_distinct_trans_contDiffOn
#print axioms ExerciseGluingPreparation.gluedComplexAtlas_transition_contDiffOn
#print axioms ExerciseGluingPreparation.gluedCarrierIsManifold
#print axioms ExerciseGluingPreparation.gluedCarrier_isManifold_one

end SystolicGrowth
