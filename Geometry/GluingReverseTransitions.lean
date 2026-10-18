module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingPolarTransitions
public import Geometry.GluingChartEvaluations

@[expose] public section

/-!
# Actual reverse interior-to-seam transitions

On the exact native overlap, the inverse of the actual smooth seam-to-interior
transition is smooth by its proved invertible differential. The inverse is
the existing native interior-to-seam transition, not a separately selected
local inverse. No derivative or smoothness hypothesis is added to the
original interior-chart predicate.
-/

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The actual native interior-to-seam transition is smooth at every point
of its exact overlap, using the constructed forward derivative equivalence. -/
theorem interiorSeam_transition_contDiffAt
    (P : ExerciseGluingPreparation C g n genera X) (e : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : P.IsGluedInteriorComplexChart e) (k : Fin (n - 1)) (θ : ℝ) {z : ℂ}
    (hz : z ∈ (e.symm.trans (P.seamAngularComplexChart k θ)).source) :
    ContDiffAt ℝ ⊤ (e.symm.trans (P.seamAngularComplexChart k θ)) z := by
  let f := (P.seamAngularComplexChart k θ).symm.trans e
  have ht : z ∈ f.target := hz
  have hs : f.symm z ∈ f.source := f.symm.map_source ht
  obtain ⟨D, hD⟩ := P.seamInterior_transition_hasFDerivAt_equiv k θ e he hs
  have hf : ContDiffAt ℝ ⊤ f (f.symm z) :=
    P.seamInterior_transition_contDiffAt k θ e he hs
  exact f.contDiffAt_symm ht hD hf

/-- Smoothness holds on the literal native interior-to-seam transition source. -/
theorem interiorSeam_transition_contDiffOn
    (P : ExerciseGluingPreparation C g n genera X) (e : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : P.IsGluedInteriorComplexChart e) (k : Fin (n - 1)) (θ : ℝ) :
    ContDiffOn ℝ ⊤ (e.symm.trans (P.seamAngularComplexChart k θ))
      (e.symm.trans (P.seamAngularComplexChart k θ)).source := by
  intro z hz
  exact (P.interiorSeam_transition_contDiffAt e he k θ hz).contDiffWithinAt

/-- The explicit actual chart composition has the same smoothness on the
native overlap; no auxiliary transition function or domain is substituted. -/
theorem interiorSeam_transition_composition_contDiffOn
    (P : ExerciseGluingPreparation C g n genera X) (e : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : P.IsGluedInteriorComplexChart e) (k : Fin (n - 1)) (θ : ℝ) :
    ContDiffOn ℝ ⊤ (fun z : ℂ => P.seamAngularComplexChart k θ (e.symm z))
      (e.symm.trans (P.seamAngularComplexChart k θ)).source :=
  P.interiorSeam_transition_contDiffOn e he k θ

#print axioms interiorSeam_transition_contDiffAt
#print axioms interiorSeam_transition_contDiffOn
#print axioms interiorSeam_transition_composition_contDiffOn

end SystolicGrowth.ExerciseGluingPreparation
