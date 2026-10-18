module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Metric.RiemannianMetric
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

@[expose] public section

/-!
# Positive conformal rescaling on the unchanged smooth manifold

The tensor is constructed on the same tangent bundle and charted space.
Its unit ball is a continuous linear image of the original metric unit
ball, so positive scaling preserves the genuine boundedness obligation.
For a nonnegative logarithmic factor, the tensor and its length integrand
dominate the original ones. Curvature transformation is a separate step.
-/

open Bundle Manifold Riemannian
open scoped ContDiff Manifold Topology

namespace SystolicGrowth

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** Scale an actual smooth metric by an actual smooth positive scalar.
The source manifold structure is unchanged. -/
def positiveConformalRiemannianMetric (g : RiemannianMetric I M) (φ : M → ℝ)
    (hφ : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ φ) (hpos : ∀ p, 0 < φ p) :
    RiemannianMetric I M where
  inner p := φ p • g.inner p
  symm p v w := by
    simp only [smul_apply, smul_eq_mul]
    rw [g.symm p v w]
  pos p v hv := by
    simp only [smul_apply, smul_eq_mul]
    exact mul_pos (hpos p) (g.pos p v hv)
  isVonNBounded p := by
    let r := Real.sqrt (φ p)
    have hr : 0 < r := Real.sqrt_pos.mpr (hpos p)
    have hrsq : r * r = φ p := by
      simpa only [r, pow_two] using Real.sq_sqrt (hpos p).le
    let L : TangentSpace I p →L[ℝ] TangentSpace I p :=
      r⁻¹ • ContinuousLinearMap.id ℝ (TangentSpace I p)
    apply ((g.isVonNBounded p).image L).subset
    intro v hv
    refine ⟨r • v, ?_, ?_⟩
    · change g.metricInner p (r • v) (r • v) < 1
      rw [g.metricInner_smul_left, g.metricInner_smul_right]
      simp only [Set.mem_setOf_eq, smul_apply, smul_eq_mul] at hv
      change φ p * g.metricInner p v v < 1 at hv
      simpa only [← mul_assoc, hrsq] using hv
    · simp [L, smul_smul, hr.ne']
  contMDiff := ContMDiff.smul_section hφ g.contMDiff

@[simp] theorem positiveConformalRiemannianMetric_inner
    (g : RiemannianMetric I M) (φ : M → ℝ)
    (hφ : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ φ) (hpos : ∀ p, 0 < φ p)
    (p : M) (v w : TangentSpace I p) :
    (positiveConformalRiemannianMetric g φ hφ hpos).metricInner p v w =
      φ p * g.metricInner p v w := by
  rfl

/-- **Math.** The exact positive conformal metric `exp (2 * u) * g`, constructed
on the original smooth atlas, for every actual smooth function `u`. -/
def conformalRiemannianMetric (g : RiemannianMetric I M) (u : M → ℝ)
    (hu : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ u) : RiemannianMetric I M :=
  positiveConformalRiemannianMetric g (fun p => Real.exp (2 * u p))
    (Real.contDiff_exp.comp_contMDiff
      ((show ContDiff ℝ ∞ (fun t : ℝ => 2 * t) from
        contDiff_const.mul contDiff_id).comp_contMDiff hu))
    (fun p => Real.exp_pos (2 * u p))

@[simp] theorem conformalRiemannianMetric_inner
    (g : RiemannianMetric I M) (u : M → ℝ)
    (hu : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ u)
    (p : M) (v w : TangentSpace I p) :
    (conformalRiemannianMetric g u hu).metricInner p v w =
      Real.exp (2 * u p) * g.metricInner p v w := by
  rfl

/-- **Math.** Nonnegativity of the actual logarithmic factor gives pointwise
domination of the original tangent metric, including zero vectors. -/
theorem conformalRiemannianMetric_self_ge
    (g : RiemannianMetric I M) (u : M → ℝ)
    (hu : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ u)
    (p : M) (hp : 0 ≤ u p) (v : TangentSpace I p) :
    g.metricInner p v v ≤ (conformalRiemannianMetric g u hu).metricInner p v v := by
  rw [conformalRiemannianMetric_inner]
  have hfactor : 1 ≤ Real.exp (2 * u p) := by
    simpa only [Real.exp_zero] using
      Real.exp_le_exp.mpr (show 0 ≤ 2 * u p by linarith)
  have hnonneg := g.metricInner_self_nonneg p v
  nlinarith

/-- **Math.** The literal square-root integrand of every smooth path is dominated. -/
theorem conformalRiemannianMetric_sqrt_self_ge
    (g : RiemannianMetric I M) (u : M → ℝ)
    (hu : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ u)
    (p : M) (hp : 0 ≤ u p) (v : TangentSpace I p) :
    Real.sqrt (g.metricInner p v v) ≤
      Real.sqrt ((conformalRiemannianMetric g u hu).metricInner p v v) :=
  Real.sqrt_le_sqrt (conformalRiemannianMetric_self_ge g u hu p hp v)

#print axioms positiveConformalRiemannianMetric
#print axioms conformalRiemannianMetric
#print axioms conformalRiemannianMetric_self_ge
#print axioms conformalRiemannianMetric_sqrt_self_ge

end

end SystolicGrowth
