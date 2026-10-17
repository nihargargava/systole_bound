module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarConformalCurvatureMeasure
public import Mathlib.MeasureTheory.Group.Measure

@[expose] public section

/-!
# Genuine collar-curvature compatibility under the native chart changes

The actual conformal radial coordinate is odd and its native log metric
factor is even on the genuine chart target. Exact Lebesgue invariance then
transports the constructed negative density-plus-seam curvature measures
under angular shifts and simultaneous radial/angular reflection. Compact
rectangle containment is transported within the actual coordinate target.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SystolicGrowth

/-- The reciprocal native warp is even, so its actual seam-based primitive
is odd, without any assumption about the coordinate inverse. -/
theorem gluingCollarConformalRadius_neg (r t : ℝ) :
    gluingCollarConformalRadius r (-t) = -gluingCollarConformalRadius r t := by
  have h := intervalIntegral.integral_comp_neg
    (fun s : ℝ => (gluingCollarWarp r s)⁻¹) (a := 0) (b := t)
  have heven : (fun s : ℝ => (gluingCollarWarp r (-s))⁻¹) =
      (fun s : ℝ => (gluingCollarWarp r s)⁻¹) := by
    funext s
    simp only [gluingCollarWarp, abs_neg]
  rw [heven] at h
  simp only [neg_zero] at h
  unfold gluingCollarConformalRadius
  rw [intervalIntegral.integral_symm, ← h]

/-- The true target of the constructed conformal radial chart is closed
under reflection about the original seam. -/
theorem gluingCollarConformalRadialChart_target_neg {r : ℝ} (hr : 0 < r)
    {u : ℝ} (hu : u ∈ (gluingCollarConformalRadialChart hr).target) :
    -u ∈ (gluingCollarConformalRadialChart hr).target := by
  have hm := (gluingCollarConformalRadialChart hr).map_source
    (show -(gluingCollarConformalRadialChart hr).symm u ∈
      (gluingCollarConformalRadialChart hr).source by simp)
  rw [gluingCollarConformalRadialChart_apply, gluingCollarConformalRadius_neg,
    ← gluingCollarConformalRadialChart_apply hr,
    (gluingCollarConformalRadialChart hr).right_inv hu] at hm
  exact hm

/-- Oddness of the genuine native inverse is proved on its actual target. -/
theorem gluingCollarConformalRadialChart_symm_neg_eq {r : ℝ} (hr : 0 < r)
    {u : ℝ} (hu : u ∈ (gluingCollarConformalRadialChart hr).target) :
    (gluingCollarConformalRadialChart hr).symm (-u) =
      -(gluingCollarConformalRadialChart hr).symm u := by
  have h := gluingCollarConformalRadialChart_left_inv hr
    (-(gluingCollarConformalRadialChart hr).symm u)
  rw [gluingCollarConformalRadius_neg,
    ← gluingCollarConformalRadialChart_apply hr,
    (gluingCollarConformalRadialChart hr).right_inv hu] at h
  exact h

/-- The actual logarithmic conformal factor is even on the native chart
target, retaining the original absolute-value warp at the seam. -/
theorem gluingCollarConformalLogFactor_neg {r : ℝ} (hr : 0 < r)
    {u : ℝ} (hu : u ∈ (gluingCollarConformalRadialChart hr).target) :
    gluingCollarConformalLogFactor hr (-u) = gluingCollarConformalLogFactor hr u := by
  unfold gluingCollarConformalLogFactor
  rw [gluingCollarConformalRadialChart_symm_neg_eq hr hu]
  simp only [gluingCollarWarp, abs_neg]

/-- Every reflected compact radial window remains in the genuine chart
target; this constructs the domain condition needed by the transported measure. -/
theorem gluingCollarConformalRadialChart_reflected_window {r a b : ℝ} (hr : 0 < r)
    (hwindow : Icc a b ⊆ (gluingCollarConformalRadialChart hr).target) :
    Icc (-b) (-a) ⊆ (gluingCollarConformalRadialChart hr).target := by
  intro u hu
  have hneg : -u ∈ Icc a b := by
    constructor <;> linarith [hu.1, hu.2]
  simpa only [neg_neg] using gluingCollarConformalRadialChart_target_neg hr (hwindow hneg)

/-- Actual angular-origin change in circular collar coordinates. -/
def gluingCollarAngularChartShift (c : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1, p.2 + c)

/-- Actual side exchange, reversing radial and angular orientation together. -/
def gluingCollarAngularChartReflection (c : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (-p.1, -p.2 + c)

theorem gluingCollarAngularChartShift_continuous (c : ℝ) :
    Continuous (gluingCollarAngularChartShift c) := by
  unfold gluingCollarAngularChartShift
  fun_prop

theorem gluingCollarAngularChartReflection_continuous (c : ℝ) :
    Continuous (gluingCollarAngularChartReflection c) := by
  unfold gluingCollarAngularChartReflection
  fun_prop

/-- The actual conformal coordinate commutes with the native angular shift. -/
theorem gluingCollarConformalChart_angularShift {r : ℝ} (hr : 0 < r) (c : ℝ) (p : ℝ × ℝ) :
    gluingCollarConformalChart hr (gluingCollarAngularChartShift c p) =
      gluingCollarAngularChartShift c (gluingCollarConformalChart hr p) := rfl

/-- The actual conformal coordinate commutes with simultaneous side reflection. -/
theorem gluingCollarConformalChart_angularReflection {r : ℝ} (hr : 0 < r)
    (c : ℝ) (p : ℝ × ℝ) :
    gluingCollarConformalChart hr (gluingCollarAngularChartReflection c p) =
      gluingCollarAngularChartReflection c (gluingCollarConformalChart hr p) := by
  simp only [gluingCollarConformalChart_apply, gluingCollarAngularChartReflection,
    gluingCollarConformalRadius_neg]

private theorem map_neg_restrict_volume_Icc (a b : ℝ) :
    Measure.map (fun u : ℝ => -u) (volume.restrict (Icc a b)) =
      volume.restrict (Icc (-b) (-a)) := by
  have hpre : (fun u : ℝ => -u) ⁻¹' Icc (-b) (-a) = Icc a b := by
    ext u
    simp only [mem_preimage, mem_Icc, neg_le_neg_iff]
    exact and_comm
  rw [← hpre, ← Measure.restrict_map measurable_neg measurableSet_Icc,
    Measure.map_neg_eq_self (volume : Measure ℝ)]

private theorem map_add_restrict_volume_Icc (u v c : ℝ) :
    Measure.map (fun θ : ℝ => θ + c) (volume.restrict (Icc u v)) =
      volume.restrict (Icc (u + c) (v + c)) := by
  have hpre : (fun θ : ℝ => θ + c) ⁻¹' Icc (u + c) (v + c) = Icc u v := by
    ext θ
    simp only [mem_preimage, mem_Icc, add_le_add_iff_right]
  have hmeas : Measurable (fun θ : ℝ => θ + c) := by fun_prop
  rw [← hpre, ← Measure.restrict_map hmeas measurableSet_Icc,
    map_add_right_eq_self (volume : Measure ℝ) c]

private theorem map_neg_add_restrict_volume_Icc (u v c : ℝ) :
    Measure.map (fun θ : ℝ => -θ + c) (volume.restrict (Icc u v)) =
      volume.restrict (Icc (c - v) (c - u)) := by
  have heq : (fun θ : ℝ => -θ + c) = (fun θ : ℝ => θ + c) ∘ (fun θ : ℝ => -θ) := rfl
  have hmeas : Measurable (fun θ : ℝ => θ + c) := by fun_prop
  rw [heq, ← Measure.map_map hmeas measurable_neg,
    map_neg_restrict_volume_Icc, map_add_restrict_volume_Icc]
  simp only [neg_add_eq_sub]

/-- Density reflection needs only genuine equality on the restricted
window, not unproved measurability or symmetry of the inverse outside its target. -/
private theorem map_neg_restrict_withDensity (f : ℝ → ℝ≥0∞) (a b : ℝ)
    (heven : ∀ u ∈ Icc a b, f (-u) = f u) :
    Measure.map (fun u : ℝ => -u) ((volume.withDensity f).restrict (Icc a b)) =
      (volume.withDensity f).restrict (Icc (-b) (-a)) := by
  rw [restrict_withDensity measurableSet_Icc, restrict_withDensity measurableSet_Icc]
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply measurable_neg hs, withDensity_apply _ (measurable_neg hs),
    withDensity_apply _ hs, ← map_neg_restrict_volume_Icc a b,
    Measure.restrict_map measurable_neg hs, measurableEmbedding_neg.lintegral_map]
  symm
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae (ae_restrict_mem measurableSet_Icc)] with u hu
  exact heven u hu

/-- Exact reflection transport of the actual conformal area density on a
genuine compact window. The outside-target inverse plays no role. -/
theorem gluingCollarConformalRadialAreaMeasure_map_neg {r a b : ℝ} (hr : 0 < r)
    (hwindow : Icc a b ⊆ (gluingCollarConformalRadialChart hr).target) :
    Measure.map (fun u : ℝ => -u) ((gluingCollarConformalRadialAreaMeasure hr).restrict (Icc a b)) =
      (gluingCollarConformalRadialAreaMeasure hr).restrict (Icc (-b) (-a)) := by
  unfold gluingCollarConformalRadialAreaMeasure
  apply map_neg_restrict_withDensity
  intro u hu
  rw [gluingCollarConformalLogFactor_neg hr (hwindow hu)]

/-- Reflection fixes the original seam atom and transports the actual
conformal curvature magnitude to the reflected genuine window. -/
theorem gluingCollarConformalRadialCurvatureMagnitude_map_neg {r a b : ℝ} (hr : 0 < r)
    (hwindow : Icc a b ⊆ (gluingCollarConformalRadialChart hr).target) :
    Measure.map (fun u : ℝ => -u)
      ((gluingCollarConformalRadialCurvatureMagnitude hr).restrict (Icc a b)) =
      (gluingCollarConformalRadialCurvatureMagnitude hr).restrict (Icc (-b) (-a)) := by
  rw [gluingCollarConformalRadialCurvatureMagnitude, Measure.restrict_add,
    Measure.map_add _ _ measurable_neg, gluingCollarConformalRadialAreaMeasure_map_neg hr hwindow,
    Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul,
    Measure.map_smul _ measurable_neg.aemeasurable, restrict_dirac, restrict_dirac]
  have hzero : (0 : ℝ) ∈ Icc a b ↔ (0 : ℝ) ∈ Icc (-b) (-a) := by
    constructor <;> rintro ⟨ha, hb⟩ <;> constructor <;> linarith
  by_cases h : (0 : ℝ) ∈ Icc a b
  · rw [ite_eq_left h, ite_eq_left (hzero.mp h), Measure.map_dirac' measurable_neg, neg_zero]
  · rw [ite_eq_right h, ite_eq_right (mt hzero.mpr h), Measure.map_zero, smul_zero]

/-- Genuine positive conformal curvature magnitude transports under any
native angular-origin shift, with the actual rectangle shifted accordingly. -/
theorem gluingCollarConformalCurvatureMagnitudeOnRectangle_map_angularShift
    {r a b : ℝ} (hr : 0 < r)
    (hwindow : Icc a b ⊆ (gluingCollarConformalRadialChart hr).target) (u v c : ℝ) :
    Measure.map (gluingCollarAngularChartShift c)
      (gluingCollarConformalCurvatureMagnitudeOnRectangle hr a b u v) =
      gluingCollarConformalCurvatureMagnitudeOnRectangle hr a b (u + c) (v + c) := by
  let := gluingCollarConformalRadialCurvatureMagnitude_restrict_isFinite hr hwindow
  unfold gluingCollarConformalCurvatureMagnitudeOnRectangle
  change Measure.map (Prod.map id (fun θ : ℝ => θ + c))
    (((gluingCollarConformalRadialCurvatureMagnitude hr).restrict (Icc a b)).prod
      (volume.restrict (Icc u v))) = _
  have hmeas : Measurable (fun θ : ℝ => θ + c) := by fun_prop
  rw [← Measure.map_prod_map _ _ measurable_id hmeas,
    Measure.map_id, map_add_restrict_volume_Icc]

/-- The genuine density and seam atom transport under simultaneous side
reflection and angular shift, within the constructed reflected chart window. -/
theorem gluingCollarConformalCurvatureMagnitudeOnRectangle_map_reflection
    {r a b : ℝ} (hr : 0 < r)
    (hwindow : Icc a b ⊆ (gluingCollarConformalRadialChart hr).target) (u v c : ℝ) :
    Measure.map (gluingCollarAngularChartReflection c)
      (gluingCollarConformalCurvatureMagnitudeOnRectangle hr a b u v) =
      gluingCollarConformalCurvatureMagnitudeOnRectangle hr (-b) (-a) (c - v) (c - u) := by
  let := gluingCollarConformalRadialCurvatureMagnitude_restrict_isFinite hr hwindow
  unfold gluingCollarConformalCurvatureMagnitudeOnRectangle
  change Measure.map (Prod.map (fun s : ℝ => -s) (fun θ : ℝ => -θ + c))
    (((gluingCollarConformalRadialCurvatureMagnitude hr).restrict (Icc a b)).prod
      (volume.restrict (Icc u v))) = _
  have hmeas : Measurable (fun θ : ℝ => -θ + c) := by fun_prop
  rw [← Measure.map_prod_map _ _ measurable_neg hmeas,
    gluingCollarConformalRadialCurvatureMagnitude_map_neg hr hwindow,
    map_neg_add_restrict_volume_Icc]

/-- Genuine finite positive-measure transport induces exact transport of
its signed measure; the native curvature transport consumer supplies `hmap`. -/
theorem toSignedMeasure_map_of_map_eq
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : α → β} (hf : Measurable f) (hmap : Measure.map f μ = ν) :
    μ.toSignedMeasure.map f = ν.toSignedMeasure := by
  apply VectorMeasure.ext
  intro s hs
  rw [VectorMeasure.map_apply _ hf hs,
    Measure.toSignedMeasure_apply_measurable (hf hs),
    Measure.toSignedMeasure_apply_measurable hs, measureReal_def, measureReal_def]
  have h := congrArg (fun m : Measure β => m s) hmap
  rw [Measure.map_apply hf hs] at h
  exact congrArg ENNReal.toReal h

set_option backward.isDefEq.respectTransparency false in
/-- The same exact transport respects the genuine negative curvature sign.
Both finite measures are supplied by the proved compact native restrictions. -/
theorem negative_toSignedMeasure_map_of_map_eq
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : α → β} (hf : Measurable f) (hmap : Measure.map f μ = ν) :
    (-μ.toSignedMeasure).map f = -ν.toSignedMeasure := by
  calc
    _ = -μ.toSignedMeasure.map f := (VectorMeasure.mapGm f).map_neg μ.toSignedMeasure
    _ = _ := congrArg Neg.neg (toSignedMeasure_map_of_map_eq hf hmap)

/-- The actual finite negative conformal curvature measure is compatible
with native angular chart shifts, not only its positive magnitude. -/
theorem gluingCollarConformalCurvatureOnRectangle_map_angularShift
    {r a b : ℝ} (hr : 0 < r)
    (hwindow : Icc a b ⊆ (gluingCollarConformalRadialChart hr).target) (u v c : ℝ) :
    (gluingCollarConformalCurvatureOnRectangle hr a b hwindow u v).map
      (gluingCollarAngularChartShift c) =
      gluingCollarConformalCurvatureOnRectangle hr a b hwindow (u + c) (v + c) := by
  let := gluingCollarConformalCurvatureMagnitudeOnRectangle_isFinite hr hwindow u v
  let := gluingCollarConformalCurvatureMagnitudeOnRectangle_isFinite hr hwindow (u + c) (v + c)
  unfold gluingCollarConformalCurvatureOnRectangle
  exact negative_toSignedMeasure_map_of_map_eq
    (gluingCollarAngularChartShift_continuous c).measurable
    (gluingCollarConformalCurvatureMagnitudeOnRectangle_map_angularShift hr hwindow u v c)

/-- The actual finite negative conformal curvature measure is compatible
with simultaneous radial/angular reflection, including the fixed seam atom.
The reflected compact rectangle's target containment is constructed internally. -/
theorem gluingCollarConformalCurvatureOnRectangle_map_reflection
    {r a b : ℝ} (hr : 0 < r)
    (hwindow : Icc a b ⊆ (gluingCollarConformalRadialChart hr).target) (u v c : ℝ) :
    (gluingCollarConformalCurvatureOnRectangle hr a b hwindow u v).map
      (gluingCollarAngularChartReflection c) =
      gluingCollarConformalCurvatureOnRectangle hr (-b) (-a)
        (gluingCollarConformalRadialChart_reflected_window hr hwindow) (c - v) (c - u) := by
  let := gluingCollarConformalCurvatureMagnitudeOnRectangle_isFinite hr hwindow u v
  let := gluingCollarConformalCurvatureMagnitudeOnRectangle_isFinite hr
    (gluingCollarConformalRadialChart_reflected_window hr hwindow) (c - v) (c - u)
  unfold gluingCollarConformalCurvatureOnRectangle
  exact negative_toSignedMeasure_map_of_map_eq
    (gluingCollarAngularChartReflection_continuous c).measurable
    (gluingCollarConformalCurvatureMagnitudeOnRectangle_map_reflection hr hwindow u v c)

#print axioms gluingCollarConformalRadius_neg
#print axioms gluingCollarConformalRadialChart_symm_neg_eq
#print axioms gluingCollarConformalLogFactor_neg
#print axioms gluingCollarConformalRadialCurvatureMagnitude_map_neg
#print axioms toSignedMeasure_map_of_map_eq
#print axioms negative_toSignedMeasure_map_of_map_eq
#print axioms gluingCollarConformalCurvatureOnRectangle_map_angularShift
#print axioms gluingCollarConformalCurvatureOnRectangle_map_reflection

end SystolicGrowth
