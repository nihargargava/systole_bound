module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.MetricHomotopySystole
public import Geometry.GluingCurvatureBoundedSystolicLoop

@[expose] public section

/-!
# Continuous-loop and cover-displacement systoles agree

For the actual smooth glued metric, every essential continuous loop has
variation at least the fiber displacement infimum. The already constructed
attaining geodesic loop gives the reverse inequality. Thus the two genuine
definitions agree, independently of the chosen cover basepoint.
-/

open Set
open scoped ENNReal unitInterval

noncomputable section

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** The actual smooth metric's continuous homotopy systole equals
its literal infimum over distinct points of one universal-cover fiber. -/
theorem metricHomotopySystole_eq_gluedCurvatureBoundedFiberSystole
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) :
    letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
    metricHomotopySystole P.GluedCarrier = P.gluedCurvatureBoundedFiberSystole x := by
  letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
  apply le_antisymm
  · obtain ⟨y, β, ℓ, _, _, _, _, _, hess, _, hvar⟩ :=
      P.exists_gluedCurvatureBounded_systolic_loop_variation x hn hsum
    exact (metricHomotopySystole_le_eVariationOn ℓ hess).trans_eq hvar
  · apply le_metricHomotopySystole_iff.mpr
    intro y ℓ hess
    exact P.gluedCurvatureBoundedFiberSystole_le_eVariationOn_of_essential x y ℓ hess

/-- **Math.** Changing the pointed universal cover does not change the
actual smooth systole. This follows from the common continuous-loop infimum,
without a chosen isometry between the two pointed covers. -/
theorem gluedCurvatureBoundedFiberSystole_basepoint_eq
    (P : ExerciseGluingPreparation C g n genera X) (x y : P.GluedCarrier)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) :
    P.gluedCurvatureBoundedFiberSystole x = P.gluedCurvatureBoundedFiberSystole y := by
  exact (P.metricHomotopySystole_eq_gluedCurvatureBoundedFiberSystole x hn hsum).symm.trans
    (P.metricHomotopySystole_eq_gluedCurvatureBoundedFiberSystole y hn hsum)

#print axioms metricHomotopySystole_eq_gluedCurvatureBoundedFiberSystole
#print axioms gluedCurvatureBoundedFiberSystole_basepoint_eq

end SystolicGrowth.ExerciseGluingPreparation
