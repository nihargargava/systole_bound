module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingConformalCurvaturePDE
public import Geometry.ConformalMetricSystole
public import Geometry.GluingCurvatureBoundedHomotopySystole
public import Geometry.GluingConstantCurvatureLiftedOutput

@[expose] public section

/-!
# Actual lifted-chain output from the classical conformal solution

The old smooth metric's target systole bound is already constructed.
Nonnegative conformal scaling preserves it through actual path and metric
comparison. The proved PDE-curvature theorem supplies the actual intrinsic
constant-curvature metric, hence the marked half-plane model, holonomy and
coherent lift are constructed by the existing consumer.

Constructing the smooth nonnegative scalar solution remains the analytic
prerequisite; no systole, curvature, representation or lift is assumed here.
-/

open Manifold Riemannian
open scoped Manifold ContDiff Topology ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

set_option backward.isDefEq.respectTransparency false

local instance gluedConformalOutputComplexFinrankNonzero : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by simp [Complex.finrank_real_complex]⟩

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** The old smooth metric has the actual continuous-loop target
systole bound, obtained from its genuine universal-cover displacement. -/
theorem target_le_gluedCurvatureBounded_metricHomotopySystole
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) :
    ENNReal.ofReal (targetSystole C g) ≤
      @metricHomotopySystole P.GluedCarrier
        (LeeLib.Ch02.RiemannianMetric.toMetricSpace
          P.gluedCurvatureBoundedSmoothRiemannianMetric).toPseudoMetricSpace := by
  exact (P.target_le_gluedCurvatureBoundedFiberSystole x).trans_eq
    (P.metricHomotopySystole_eq_gluedCurvatureBoundedFiberSystole x hn hsum).symm

/-- **Math.** The actual conformal metric retains the target homotopy
systole through the proved one-Lipschitz identity homeomorphism. -/
theorem target_le_gluedConformal_metricHomotopySystole
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g)
    (u : P.GluedCarrier → ℝ)
    (hu : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞ u)
    (hupos : ∀ b, 0 ≤ u b) :
    ENNReal.ofReal (targetSystole C g) ≤
      @metricHomotopySystole P.GluedCarrier
        (LeeLib.Ch02.RiemannianMetric.toMetricSpace
          (conformalRiemannianMetric P.gluedCurvatureBoundedSmoothRiemannianMetric u hu)).toPseudoMetricSpace :=
  (P.target_le_gluedCurvatureBounded_metricHomotopySystole x hn hsum).trans
    (conformalRiemannianMetric_homotopySystole_ge P.gluedCurvatureBoundedSmoothRiemannianMetric u hu hupos)

/-- **Math.** Construct the marked hyperbolic surface from the SAME
original smooth carrier and a genuine smooth nonnegative classical PDE
solution. The actual curvature and systole inputs are proved above. -/
def gluedConformalLiftedSurface
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g)
    (u : P.GluedCarrier → ℝ)
    (hu : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞ u)
    (hpde : P.GluedConformalClassicalPDE u) (hupos : ∀ b, 0 ≤ u b) : ClosedHyperbolicSurface g :=
  P.gluedConstantCurvatureLiftedSurface hn hsum x
    (conformalRiemannianMetric P.gluedCurvatureBoundedSmoothRiemannianMetric u hu)
    (P.gluedConformalMetric_curvature_eq u hu hpde)
    (targetSystole C g) P.target_pos
    (P.target_le_gluedConformal_metricHomotopySystole x hn hsum u hu hupos)

/-- **Math.** The constructed marked hyperbolic surface retains the
unchanged target lower bound on its genuine geometric systole. -/
theorem target_le_gluedConformalLiftedSurface_systole
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g)
    (u : P.GluedCarrier → ℝ)
    (hu : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞ u)
    (hpde : P.GluedConformalClassicalPDE u) (hupos : ∀ b, 0 ≤ u b) :
    targetSystole C g ≤ (P.gluedConformalLiftedSurface x hn hsum u hu hpde hupos).systole :=
  P.le_gluedConstantCurvatureLiftedSurface_systole hn hsum x
    (conformalRiemannianMetric P.gluedCurvatureBoundedSmoothRiemannianMetric u hu)
    (P.gluedConformalMetric_curvature_eq u hu hpde)
    (targetSystole C g) P.target_pos
    (P.target_le_gluedConformal_metricHomotopySystole x hn hsum u hu hupos)

/-- **Math.** Produce all six remaining geometric source fields together
from the actual classical conformal solution. No new metric, representation,
faithfulness, compactness, orbit or systole conclusion is an input. -/
def gluedConformalLiftedOutput
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g)
    (u : P.GluedCarrier → ℝ)
    (hu : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞ u)
    (hpde : P.GluedConformalClassicalPDE u) (hupos : ∀ b, 0 ≤ u b) :
    ExerciseLiftedChainOutput g (targetSystole C g) :=
  P.gluedConstantCurvatureLiftedOutput hn hsum x
    (conformalRiemannianMetric P.gluedCurvatureBoundedSmoothRiemannianMetric u hu)
    (P.gluedConformalMetric_curvature_eq u hu hpde)
    (targetSystole C g) P.target_pos
    (P.target_le_gluedConformal_metricHomotopySystole x hn hsum u hu hupos)

#print axioms target_le_gluedCurvatureBounded_metricHomotopySystole
#print axioms target_le_gluedConformal_metricHomotopySystole
#print axioms gluedConformalLiftedSurface
#print axioms target_le_gluedConformalLiftedSurface_systole
#print axioms gluedConformalLiftedOutput

end

end SystolicGrowth.ExerciseGluingPreparation
