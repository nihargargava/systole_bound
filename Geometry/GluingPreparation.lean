module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingOrbitCenters

@[expose] public section

/-!
# Concrete parameters for the gluing construction

This is the existing preparation contract, moved out of the unfinished
exercise module so that the actual chain construction can consume it
without a circular import. All radii use the global genus.
-/

open UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth

/-- Concrete preparation for chain gluing. Radii use the GLOBAL genus g,
even on a component of genus `genera i`; outer balls may overlap. -/
structure ExerciseGluingPreparation (C : ℝ) (g n : ℕ)
    (genera : Fin n → ℕ) (X : ∀ i, ClosedHyperbolicSurface (genera i)) where
  target_pos : 0 < targetSystole C g
  component_genus : ∀ i, 2 ≤ genera i
  component_systole : ∀ i, targetSystole C g ≤ (X i).systole
  twice_outer_lt_systole : ∀ i, 2 * gluingEmbeddedRadius C g < (X i).systole
  centers : Fin n → ℍ × ℍ
  separated : ∀ i (γ : (X i).deckGroup),
    gluingSeparationRadius C g ≤ dist (centers i).1 (γ • (centers i).2)

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The actual removed disks have strictly positive radius. -/
theorem radius_pos (P : ExerciseGluingPreparation C g n genera X) :
    0 < gluingRadius C g := by
  rw [gluingRadius, Real.arsinh_pos_iff]
  exact div_pos P.target_pos (by positivity)

/-- The actual collar has strictly positive width. -/
theorem depth_pos (P : ExerciseGluingPreparation C g n genera X) :
    0 < gluingDepth C g := by
  exact div_pos P.target_pos (by norm_num)

/-- The inner boundary circle lies strictly inside its embedded chart. -/
theorem radius_lt_embeddedRadius (P : ExerciseGluingPreparation C g n genera X) :
    gluingRadius C g < gluingEmbeddedRadius C g := by
  dsimp only [gluingEmbeddedRadius]
  linarith [P.depth_pos]

/-- Each actual radius-R ball is injectively mapped to its component. -/
theorem quotient_injOn_outer_ball (P : ExerciseGluingPreparation C g n genera X)
    (i : Fin n) (o : ℍ) :
    Set.InjOn (fun z : ℍ => (Quotient.mk'' z : (X i).Carrier))
      (Metric.ball o (gluingEmbeddedRadius C g)) :=
  quotientMk_injOn_ball (X i) o _ (P.twice_outer_lt_systole i)

end ExerciseGluingPreparation

#print axioms ExerciseGluingPreparation.quotient_injOn_outer_ball

end SystolicGrowth
