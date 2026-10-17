module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ConstantCurvatureNormalCoordinates
public import Geometry.UpperHalfPlaneHadamard

@[expose] public section

/-!
# The genuine upper-half-plane model of a constant-curvature surface

The source's actual tangent tensor determines an initial metric equivalence.
Normal coordinates then produce a smooth diffeomorphism to mathlib's original
upper half-plane, preserving its original hyperbolic distance. No frame,
initial isometry, model-curvature conclusion or distance formula is assumed.
-/

open Bundle Manifold Riemannian UpperHalfPlane
open scoped ContDiff Manifold Topology

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SystolicGrowth

local instance : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by rw [Complex.finrank_real_complex]; norm_num⟩

variable {M : Type*} [MetricSpace M] [ChartedSpace ℂ M]
  [IsManifold (modelWithCornersSelf ℝ ℂ) ∞ M]
  [SigmaCompactSpace M] [CompleteSpace M] [ConnectedSpace M]
  [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]

/-- **Math.** The genuine normal-coordinate diffeomorphism to the original
Poincaré upper half-plane, with its initial metric equivalence constructed
from the source tensor rather than supplied as an extra premise. -/
def constantCurvatureHalfPlaneDiffeomorph
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M)
    (hg : g.IsRiemannianDist) (p : M)
    (hK : ∀ (a : M) (u v : TangentSpace (modelWithCornersSelf ℝ ℂ) a),
      g.metricInner a u u * g.metricInner a v v -
        g.metricInner a u v * g.metricInner a u v =
      g.metricInner a (g.leviCivitaConnection.curvatureOperatorAt a u v v) u) :
    Diffeomorph (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) M ℍ ∞ :=
  constantCurvatureNormalDiffeomorph g upperHalfPlanePoincareMetric hg
    upperHalfPlanePoincareMetric_isRiemannianDist p UpperHalfPlane.I hK
    upperHalfPlanePoincareMetric_curvatureOperatorAt_eq
    (Classical.choose (exists_upperHalfPlanePoincare_initialMetricEquiv g p))

/-- **Math.** The constructed smooth model map preserves the actual full
Riemannian tensor. The model curvature and initial metric isometry are both
proved inputs, not assumptions on the source. -/
theorem constantCurvatureHalfPlaneDiffeomorph_isIsometry
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M)
    (hg : g.IsRiemannianDist) (p : M)
    (hK : ∀ (a : M) (u v : TangentSpace (modelWithCornersSelf ℝ ℂ) a),
      g.metricInner a u u * g.metricInner a v v -
        g.metricInner a u v * g.metricInner a u v =
      g.metricInner a (g.leviCivitaConnection.curvatureOperatorAt a u v v) u) :
    LeeLib.Ch02.IsIsometry g upperHalfPlanePoincareMetric
      (constantCurvatureHalfPlaneDiffeomorph g hg p hK) :=
  constantCurvatureNormalDiffeomorph_isIsometry g upperHalfPlanePoincareMetric hg
    upperHalfPlanePoincareMetric_isRiemannianDist p UpperHalfPlane.I hK
    upperHalfPlanePoincareMetric_curvatureOperatorAt_eq
    (Classical.choose (exists_upperHalfPlanePoincare_initialMetricEquiv g p))
    (Classical.choose_spec (exists_upperHalfPlanePoincare_initialMetricEquiv g p))

/-- **Math.** Every complete simply-connected smooth surface with actual
constant curvature `-1` is isometric to mathlib's genuine hyperbolic plane.
The distance conclusion is obtained from the proved tensor equality. -/
def constantCurvatureHalfPlaneIsometryEquiv
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M)
    (hg : g.IsRiemannianDist) (p : M)
    (hK : ∀ (a : M) (u v : TangentSpace (modelWithCornersSelf ℝ ℂ) a),
      g.metricInner a u u * g.metricInner a v v -
        g.metricInner a u v * g.metricInner a u v =
      g.metricInner a (g.leviCivitaConnection.curvatureOperatorAt a u v v) u) :
    M ≃ᵢ ℍ :=
  constantCurvatureNormalIsometryEquiv g upperHalfPlanePoincareMetric hg
    upperHalfPlanePoincareMetric_isRiemannianDist p UpperHalfPlane.I hK
    upperHalfPlanePoincareMetric_curvatureOperatorAt_eq
    (Classical.choose (exists_upperHalfPlanePoincare_initialMetricEquiv g p))
    (Classical.choose_spec (exists_upperHalfPlanePoincare_initialMetricEquiv g p))

/-- **Math.** The metric and smooth model equivalences are literally the
same map; smoothness is not asserted for a separately chosen isometry. -/
@[simp] theorem constantCurvatureHalfPlaneIsometryEquiv_apply
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M)
    (hg : g.IsRiemannianDist) (p : M)
    (hK : ∀ (a : M) (u v : TangentSpace (modelWithCornersSelf ℝ ℂ) a),
      g.metricInner a u u * g.metricInner a v v -
        g.metricInner a u v * g.metricInner a u v =
      g.metricInner a (g.leviCivitaConnection.curvatureOperatorAt a u v v) u)
    (x : M) :
    constantCurvatureHalfPlaneIsometryEquiv g hg p hK x =
      constantCurvatureHalfPlaneDiffeomorph g hg p hK x := rfl

/-- **Math.** The genuine model map is normalized at the chosen basepoint. -/
@[simp] theorem constantCurvatureHalfPlaneDiffeomorph_basepoint
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M)
    (hg : g.IsRiemannianDist) (p : M)
    (hK : ∀ (a : M) (u v : TangentSpace (modelWithCornersSelf ℝ ℂ) a),
      g.metricInner a u u * g.metricInner a v v -
        g.metricInner a u v * g.metricInner a u v =
      g.metricInner a (g.leviCivitaConnection.curvatureOperatorAt a u v v) u) :
    constantCurvatureHalfPlaneDiffeomorph g hg p hK p = UpperHalfPlane.I := by
  let dM := constantCurvatureExpDiffeomorph g hg p hK
  let dN := constantCurvatureExpDiffeomorph upperHalfPlanePoincareMetric
    upperHalfPlanePoincareMetric_isRiemannianDist UpperHalfPlane.I
    upperHalfPlanePoincareMetric_curvatureOperatorAt_eq
  let A := Classical.choose (exists_upperHalfPlanePoincare_initialMetricEquiv g p)
  have hz : dM (0 : ℂ) = p := by
    have hmap := congrFun (Jacobi.hadamardDiffeomorphOfNonpos_complete_coe g hg p
      (Internal.ConstantCurvatureNormalCoordinatesHelpers.constantCurvature_curvatureOperator_pair_nonneg g hK))
      (0 : HadamardModel ℂ)
    exact hmap.trans (Exponential.expMapGlobal_zero g hg p)
  have hinv : dM.symm p = 0 := by
    apply dM.injective
    change dM (dM.symm p) = dM (0 : ℂ)
    rw [dM.apply_symm_apply, hz]
  change dN (A (dM.symm p)) = UpperHalfPlane.I
  rw [hinv, map_zero]
  have hmap := congrFun (Jacobi.hadamardDiffeomorphOfNonpos_complete_coe
    upperHalfPlanePoincareMetric upperHalfPlanePoincareMetric_isRiemannianDist UpperHalfPlane.I
    (Internal.ConstantCurvatureNormalCoordinatesHelpers.constantCurvature_curvatureOperator_pair_nonneg
      upperHalfPlanePoincareMetric upperHalfPlanePoincareMetric_curvatureOperatorAt_eq))
    (0 : HadamardModel ℂ)
  exact hmap.trans (Exponential.expMapGlobal_zero upperHalfPlanePoincareMetric
    upperHalfPlanePoincareMetric_isRiemannianDist UpperHalfPlane.I)

@[simp] theorem constantCurvatureHalfPlaneIsometryEquiv_basepoint
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M)
    (hg : g.IsRiemannianDist) (p : M)
    (hK : ∀ (a : M) (u v : TangentSpace (modelWithCornersSelf ℝ ℂ) a),
      g.metricInner a u u * g.metricInner a v v -
        g.metricInner a u v * g.metricInner a u v =
      g.metricInner a (g.leviCivitaConnection.curvatureOperatorAt a u v v) u) :
    constantCurvatureHalfPlaneIsometryEquiv g hg p hK p = UpperHalfPlane.I := by
  rw [constantCurvatureHalfPlaneIsometryEquiv_apply,
    constantCurvatureHalfPlaneDiffeomorph_basepoint]

#print axioms constantCurvatureHalfPlaneDiffeomorph
#print axioms constantCurvatureHalfPlaneDiffeomorph_isIsometry
#print axioms constantCurvatureHalfPlaneIsometryEquiv
#print axioms constantCurvatureHalfPlaneIsometryEquiv_basepoint

end SystolicGrowth

end
