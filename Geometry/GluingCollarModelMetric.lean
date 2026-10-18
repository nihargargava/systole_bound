module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChartMetric
public import Mathlib.Geometry.Manifold.Riemannian.Basic

@[expose] public section

/-!
# Native intrinsic distance of the signed collar model

The full complex coordinate plane carries the actual continuous tangent form
`dt² + sinh(r+|t|)² dθ²`. Its native C¹-path infimum defines a finite metric
with the original model topology. Bundle and distance instances are explicit
local choices, not global replacements for the usual complex metric.
-/

open Set Filter Bundle Manifold ContinuousLinearMap
open scoped Manifold Topology Bundle ENNReal

namespace SystolicGrowth

set_option backward.isDefEq.respectTransparency false in
/-- The collar form on the actual native tangent fibers. -/
noncomputable def gluingCollarModelTangentInner (r : ℝ) (z : ℂ) :
    TangentSpace (modelWithCornersSelf ℝ ℂ) z →L[ℝ]
      TangentSpace (modelWithCornersSelf ℝ ℂ) z →L[ℝ] ℝ :=
  gluingComplexCollarTangentForm r z

set_option backward.isDefEq.respectTransparency false in
/-- Continuity in the native tangent bilinear-form bundle, not a replacement
trivial-bundle topology. -/
theorem gluingCollarModelTangentForm_continuous_section (r : ℝ) :
    Continuous (fun z : ℂ =>
      TotalSpace.mk' (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) z (gluingCollarModelTangentInner r z)) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  rw [FiberBundle.continuousAt_section]
  convert (gluingComplexCollarTangentForm_continuous r).continuousAt (x := z₀) using 1
  funext z
  rw [hom_trivializationAt_apply]
  ext v u
  rw [inCoordinates_apply_eq₂ (by simp) (by simp) (mem_univ _)]
  have hs (w : ℂ) :
      (trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ)) z₀).symm z w = w := by
    exact ((trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ)) z₀).symmL_apply
      (by simp) w).symm.trans (by rw [TangentBundle.symmL_model_space]; rfl)
  have hl (a : ℝ) :
      (trivializationAt ℝ (fun _ : ℂ => ℝ) z₀).linearMapAt ℝ z a = a := by
    change (Bundle.Trivial.trivialization ℂ ℝ).linearMapAt ℝ z a = a
    rw [Bundle.Trivial.linearMapAt_trivialization]
    rfl
  change (trivializationAt ℝ (fun _ : ℂ => ℝ) z₀).linearMapAt ℝ z
    (gluingCollarModelTangentInner r z
    ((trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ)) z₀).symm z v)
    ((trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ)) z₀).symm z u)) = _
  rw [hs, hs, hl]
  rfl

/-- The actual native continuous tangent metric of the signed collar plane. -/
noncomputable def gluingCollarModelContinuousRiemannianMetric {r : ℝ} (hr : 0 < r) :
    Bundle.ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : ℂ → Type) where
  inner := gluingCollarModelTangentInner r
  symm := gluingComplexCollarTangentForm_symm r
  pos := gluingComplexCollarTangentForm_pos hr
  isVonNBounded z := by
    change Bornology.IsVonNBounded ℝ {v : ℂ | gluingComplexCollarTangentForm r z v v < 1}
    apply (NormedSpace.isVonNBounded_iff' ℝ).mpr
    exact ⟨2 * (1 + ((gluingCollarWarp r z.re) ^ 2)⁻¹),
      fun v hv => gluingComplexCollarTangentForm_unit_norm_le hr z v hv⟩
  continuous := gluingCollarModelTangentForm_continuous_section r

/-- Explicit local bundle data for the model metric; no instance is registered. -/
@[instance_reducible]
noncomputable def gluingCollarModelRiemannianBundle {r : ℝ} (hr : 0 < r) :
    RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : ℂ → Type) :=
  ⟨(gluingCollarModelContinuousRiemannianMetric hr).toRiemannianMetric⟩

/-- Literal native C¹-path-length infimum in the signed collar plane. -/
noncomputable def gluingCollarModelEDist {r : ℝ} (hr : 0 < r) (z w : ℂ) : ℝ≥0∞ := by
  letI := gluingCollarModelRiemannianBundle hr
  exact riemannianEDist (modelWithCornersSelf ℝ ℂ) z w

/-- Length using the model tangent norm, fixed independently of a consumer's
other local bundle instances. -/
noncomputable def gluingCollarModelPathELength {r : ℝ} (hr : 0 < r)
    (α : ℝ → ℂ) (a b : ℝ) : ℝ≥0∞ := by
  letI := gluingCollarModelRiemannianBundle hr
  exact pathELength (modelWithCornersSelf ℝ ℂ) α a b

/-- Native extended metric, retaining the original complex topology. -/
@[instance_reducible]
noncomputable def gluingCollarModelEMetricSpace {r : ℝ} (hr : 0 < r) : EMetricSpace ℂ := by
  letI := gluingCollarModelRiemannianBundle hr
  exact EMetricSpace.ofRiemannianMetric (modelWithCornersSelf ℝ ℂ) ℂ

theorem gluingCollarModelEMetricSpace_edist {r : ℝ} (hr : 0 < r) (z w : ℂ) :
    letI := gluingCollarModelEMetricSpace hr
    edist z w = gluingCollarModelEDist hr z w := rfl

theorem gluingCollarModelEMetricSpace_topology {r : ℝ} (hr : 0 < r) :
    (gluingCollarModelEMetricSpace hr).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace ℂ) := rfl

/-- Original model connectivity makes the intrinsic path distance finite. -/
theorem gluingCollarModelEDist_lt_top {r : ℝ} (hr : 0 < r) (z w : ℂ) :
    gluingCollarModelEDist hr z w < ⊤ := by
  letI := gluingCollarModelEMetricSpace hr
  have hc : IsClopen (Metric.eball z (⊤ : ℝ≥0∞)) :=
    ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩
  have heq : Metric.eball z (⊤ : ℝ≥0∞) = univ := hc.eq_univ ⟨z, by simp⟩
  have hw : w ∈ Metric.eball z (⊤ : ℝ≥0∞) := heq.symm ▸ mem_univ w
  have hzw : edist z w < ⊤ := by
    simpa only [Metric.mem_eball, edist_comm] using hw
  rw [gluingCollarModelEMetricSpace_edist] at hzw
  exact hzw

/-- Genuine finite collar path metric with definitionally the model topology. -/
@[instance_reducible]
noncomputable def gluingCollarModelMetricSpace {r : ℝ} (hr : 0 < r) : MetricSpace ℂ := by
  letI := gluingCollarModelEMetricSpace hr
  exact EMetricSpace.toMetricSpace (fun z w => (gluingCollarModelEDist_lt_top hr z w).ne)

theorem gluingCollarModelMetricSpace_edist {r : ℝ} (hr : 0 < r) (z w : ℂ) :
    letI := gluingCollarModelMetricSpace hr
    edist z w = gluingCollarModelEDist hr z w := rfl

theorem gluingCollarModelMetricSpace_topology {r : ℝ} (hr : 0 < r) :
    (gluingCollarModelMetricSpace hr).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace ℂ) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual model length is exactly the signed collar speed integral;
this identity does not require regularity of the curve. -/
theorem gluingCollarModelPathELength_eq_lintegral {r : ℝ} (hr : 0 < r)
    (α : ℝ → ℂ) (a b : ℝ) :
    gluingCollarModelPathELength hr α a b =
      ∫⁻ t in Icc a b, ENNReal.ofReal
        (Real.sqrt (gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t))) := by
  letI := gluingCollarModelRiemannianBundle hr
  unfold gluingCollarModelPathELength
  rw [pathELength_eq_lintegral_mfderiv_Icc]
  apply MeasureTheory.setLIntegral_congr_fun measurableSet_Icc
  intro t _ht
  dsimp only
  have hsq : ‖mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) α t 1‖ ^ 2 =
      gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t) := by
    calc
      _ = inner ℝ
          (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) α t 1)
          (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) α t 1) :=
        (real_inner_self_eq_norm_sq _).symm
      _ = _ := by rw [mfderiv_eq_fderiv]; rfl
  rw [← hsq, Real.sqrt_sq (norm_nonneg _), ofReal_norm]

/-- Native within-C¹ curves bound the true collar intrinsic distance. -/
theorem gluingCollarModelEDist_le_pathELength {r : ℝ} (hr : 0 < r)
    {α : ℝ → ℂ} {a b : ℝ}
    (hα : ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1 α (Icc a b))
    (hab : a ≤ b) :
    gluingCollarModelEDist hr (α a) (α b) ≤ gluingCollarModelPathELength hr α a b := by
  letI := gluingCollarModelRiemannianBundle hr
  exact riemannianEDist_le_pathELength hα rfl rfl hab

#print axioms gluingCollarModelTangentForm_continuous_section
#print axioms gluingCollarModelContinuousRiemannianMetric
#print axioms gluingCollarModelEDist_lt_top
#print axioms gluingCollarModelMetricSpace
#print axioms gluingCollarModelMetricSpace_edist
#print axioms gluingCollarModelMetricSpace_topology
#print axioms gluingCollarModelPathELength_eq_lintegral
#print axioms gluingCollarModelEDist_le_pathELength

end SystolicGrowth
