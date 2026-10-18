module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCurvatureBoundedCoverBalls

@[expose] public section

/-!
# Systole as actual smooth universal-cover fiber displacement

The infimum ranges over distinct points in one genuine projection fiber.
It is initially extended-real, so finiteness is not silently assumed.
The native essential-loop theorem supplies its positive lower bound.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** The actual smooth-cover fiber displacement infimum, with
no assumed existence of a nontrivial fiber or shortest essential loop. -/
def gluedCurvatureBoundedFiberSystole
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) : ℝ≥0∞ :=
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  ⨅ a : P.basedTopologicalUniversalCover x,
    ⨅ b : P.basedTopologicalUniversalCover x,
      ⨅ (_ : P.gluedUniversalCoverProjection x a = P.gluedUniversalCoverProjection x b),
        ⨅ (_ : a ≠ b), edist a b

/-- **Math.** Every genuine nontrivial same-fiber displacement bounds the
actual systolic infimum from above. -/
theorem gluedCurvatureBoundedFiberSystole_le_edist
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (a b : P.basedTopologicalUniversalCover x)
    (hproj : P.gluedUniversalCoverProjection x a = P.gluedUniversalCoverProjection x b)
    (hne : a ≠ b) :
    letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
    P.gluedCurvatureBoundedFiberSystole x ≤ edist a b := by
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  exact iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le hproj (iInf_le _ hne)))

/-- **Math.** A real number bounds the actual systole exactly when it
bounds every distinct same-fiber distance. This supplies ball embedding
with its actual systolic radius, rather than only the prescribed target. -/
theorem le_gluedCurvatureBoundedFiberSystole_iff
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) (L : ℝ) :
    (ENNReal.ofReal L ≤ P.gluedCurvatureBoundedFiberSystole x) ↔
      (letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
        ∀ a b : P.basedTopologicalUniversalCover x,
          P.gluedUniversalCoverProjection x a = P.gluedUniversalCoverProjection x b →
            a ≠ b → L ≤ dist a b) := by
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  constructor
  · intro h a b hproj hne
    have hle := h.trans (P.gluedCurvatureBoundedFiberSystole_le_edist x a b hproj hne)
    rw [edist_dist] at hle
    exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hle
  · intro h
    apply le_iInf
    intro a
    apply le_iInf
    intro b
    apply le_iInf
    intro hproj
    apply le_iInf
    intro hne
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (h a b hproj hne)

/-- **Math.** The unchanged target is a lower bound for the actual smooth
systolic infimum, derived from the native essential-loop bound. -/
theorem target_le_gluedCurvatureBoundedFiberSystole
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    ENNReal.ofReal (targetSystole C g) ≤ P.gluedCurvatureBoundedFiberSystole x := by
  apply (P.le_gluedCurvatureBoundedFiberSystole_iff x (targetSystole C g)).mpr
  intro a b hproj hne
  exact P.targetSystole_le_gluedCurvatureBoundedUniversalCover_dist_of_same_fiber_ne
    x a b hproj hne

#print axioms gluedCurvatureBoundedFiberSystole_le_edist
#print axioms le_gluedCurvatureBoundedFiberSystole_iff
#print axioms target_le_gluedCurvatureBoundedFiberSystole

end
end SystolicGrowth.ExerciseGluingPreparation
