module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarModelBounds
public import Mathlib.Topology.MetricSpace.ProperSpace

@[expose] public section

/-!
# Properness of the genuine signed collar length metric

The global radial and positive seam-weighted angular distance bounds contain
every native closed ball in a compact coordinate rectangle. Compactness is
taken in the original complex topology, which the constructed model metric
preserves. No Euclidean properness or completeness instance is used for the
new metric, and no global replacement metric instance is registered.
-/

open Set Metric
open scoped Topology

namespace SystolicGrowth

/-- Actual collar-metric balls are bounded in both original real coordinates. -/
theorem gluingCollarModelMetric_closedBall_subset_rectangle {r : ℝ} (hr : 0 < r)
    (z : ℂ) (R : ℝ) :
    letI := gluingCollarModelMetricSpace hr
    letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
    closedBall z R ⊆
      Icc (z.re - R) (z.re + R) ×ℂ
        Icc (z.im - R / Real.sinh r) (z.im + R / Real.sinh r) := by
  letI := gluingCollarModelMetricSpace hr
  letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
  intro w hw
  have hdist : dist w z ≤ R := hw
  obtain ⟨hrad, hang⟩ := gluingCollarModelMetric_coordinates_le_dist hr w z
  have hradR : |w.re - z.re| ≤ R := hrad.trans hdist
  have hs : 0 < Real.sinh r := Real.sinh_pos_iff.mpr hr
  have hangR : |w.im - z.im| ≤ R / Real.sinh r := by
    apply (le_div_iff₀ hs).2
    simpa only [mul_comm] using hang.trans hdist
  obtain ⟨hradlo, hradhi⟩ := abs_sub_le_iff.mp hradR
  obtain ⟨hanglo, hanghi⟩ := abs_sub_le_iff.mp hangR
  simp only [Complex.mem_reProdIm, mem_Icc]
  constructor
  · constructor <;> linarith
  · constructor <;> linarith

/-- Native closed balls are compact in the preserved original model topology. -/
theorem gluingCollarModelMetric_isCompact_closedBall {r : ℝ} (hr : 0 < r)
    (z : ℂ) (R : ℝ) :
    letI := gluingCollarModelMetricSpace hr
    letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
    IsCompact (closedBall z R) := by
  letI := gluingCollarModelMetricSpace hr
  letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
  have hrectangle : IsCompact
      (Icc (z.re - R) (z.re + R) ×ℂ
        Icc (z.im - R / Real.sinh r) (z.im + R / Real.sinh r)) :=
    isCompact_Icc.reProdIm isCompact_Icc
  exact hrectangle.of_isClosed_subset isClosed_closedBall
    (gluingCollarModelMetric_closedBall_subset_rectangle hr z R)

/-- Properness refers to the true native collar length metric, not the usual
complex metric. Consumers install this proved instance locally. -/
theorem gluingCollarModelMetric_properSpace {r : ℝ} (hr : 0 < r) :
    letI := gluingCollarModelMetricSpace hr
    letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
    ProperSpace ℂ := by
  letI := gluingCollarModelMetricSpace hr
  letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
  exact ⟨gluingCollarModelMetric_isCompact_closedBall hr⟩

/-- Completeness is derived from the actual model closed-ball compactness. -/
theorem gluingCollarModelMetric_completeSpace {r : ℝ} (hr : 0 < r) :
    @CompleteSpace ℂ (gluingCollarModelMetricSpace hr).toUniformSpace := by
  letI := gluingCollarModelMetricSpace hr
  letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
  exact @complete_of_proper ℂ (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
    (gluingCollarModelMetric_properSpace hr)

/-- The fixed radial window is proper for the restricted native metric.
This is the target space for retracting finite-fin comparison midpoints;
the ordinary complex metric is not used. -/
theorem gluingCollarModelMetric_window_properSpace {r : ℝ} (hr : 0 < r) (R : ℝ) :
    letI := gluingCollarModelMetricSpace hr
    letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
    ProperSpace {z : ℂ | z.re ∈ Icc (-R) R} := by
  letI := gluingCollarModelMetricSpace hr
  letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
  letI := gluingCollarModelMetric_properSpace hr
  exact ProperSpace.of_isClosed (isClosed_Icc.preimage Complex.continuous_re)

#print axioms gluingCollarModelMetric_closedBall_subset_rectangle
#print axioms gluingCollarModelMetric_isCompact_closedBall
#print axioms gluingCollarModelMetric_properSpace
#print axioms gluingCollarModelMetric_completeSpace
#print axioms gluingCollarModelMetric_window_properSpace

end SystolicGrowth
