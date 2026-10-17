module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarModelMetric
public import Geometry.GluingCurveLength

@[expose] public section

/-!
# Coordinate bounds and escape barriers for the actual collar model

The distance here is the infimum of native C¹ path lengths for
`dt² + sinh(r + |t|)² dθ²`, not the ambient complex distance. The radial
and seam-weighted angular bounds are obtained from actual near-minimizers.
Preservation of the original complex topology then supplies short-path
barriers in arbitrary open collar-coordinate neighborhoods.

The distance contracts explicitly select the model's pseudo-metric as well
as its metric: the complex normed-field instance must not supply the usual
Euclidean distance. Ordinary coordinate derivatives retain their usual norm.
-/

open Set Metric Bundle Manifold
open scoped Manifold Topology Bundle ENNReal

namespace SystolicGrowth

/-- Every C¹ model path pays for its signed radial displacement. -/
theorem gluingCollarModel_radial_enorm_sub_le_pathELength {r : ℝ} (hr : 0 < r)
    {α : ℝ → ℂ} {a b : ℝ} (hα : ContDiffOn ℝ 1 α (Icc a b)) (hab : a ≤ b) :
    ‖(α b).re - (α a).re‖ₑ ≤ gluingCollarModelPathELength hr α a b := by
  rw [gluingCollarModelPathELength_eq_lintegral]
  exact collar_radial_enorm_sub_le_lintegral r hα hab

/-- Every C¹ model path pays for its lifted angular displacement at the
seam's own positive coefficient, including paths crossing signed radius zero. -/
theorem gluingCollarModel_angular_enorm_sub_le_pathELength {r : ℝ} (hr : 0 < r)
    {α : ℝ → ℂ} {a b : ℝ} (hα : ContDiffOn ℝ 1 α (Icc a b)) (hab : a ≤ b) :
    ‖Real.sinh r * ((α b).im - (α a).im)‖ₑ ≤
      gluingCollarModelPathELength hr α a b := by
  rw [gluingCollarModelPathELength_eq_lintegral]
  exact collar_angular_enorm_sub_le_lintegral hr hα hab

/-- Global coordinate displacement lower bounds for the constructed collar
length metric. No containment or minimizing-path regularity is assumed. -/
theorem gluingCollarModelMetric_coordinates_le_dist {r : ℝ} (hr : 0 < r) (z w : ℂ) :
    letI := gluingCollarModelMetricSpace hr
    letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
    |z.re - w.re| ≤ dist z w ∧ Real.sinh r * |z.im - w.im| ≤ dist z w := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : ℂ → Type) :=
    ⟨(gluingCollarModelContinuousRiemannianMetric hr).toRiemannianMetric⟩
  letI collarMetric : MetricSpace ℂ := gluingCollarModelMetricSpace hr
  letI : PseudoMetricSpace ℂ := collarMetric.toPseudoMetricSpace
  have hbound (ε : ℝ) (hε : 0 < ε) :
      |z.re - w.re| ≤ dist z w + ε ∧
      Real.sinh r * |z.im - w.im| ≤ dist z w + ε := by
    have hdist : 0 ≤ dist z w := @dist_nonneg ℂ collarMetric.toPseudoMetricSpace z w
    have hnear : riemannianEDist (modelWithCornersSelf ℝ ℂ) z w <
        ENNReal.ofReal (dist z w + ε) := by
      change edist z w < ENNReal.ofReal (dist z w + ε)
      rw [@edist_dist ℂ collarMetric.toPseudoMetricSpace z w,
        ENNReal.ofReal_lt_ofReal_iff (by linarith)]
      linarith
    obtain ⟨α, hα0, hα1, hα, hlen, _, _⟩ :=
      exists_lt_locally_constant_of_riemannianEDist_lt hnear
        (show (0 : ℝ) < 1 by norm_num)
    have hαC : ContDiffOn ℝ 1 α (Icc 0 1) := hα.contMDiffOn.contDiffOn
    have hrad := (gluingCollarModel_radial_enorm_sub_le_pathELength hr hαC
      zero_le_one).trans hlen.le
    rw [hα0, hα1, ← ofReal_norm, Real.norm_eq_abs, abs_sub_comm] at hrad
    have hradReal := (ENNReal.ofReal_le_ofReal_iff
      (by linarith : 0 ≤ dist z w + ε)).1 hrad
    have hang := (gluingCollarModel_angular_enorm_sub_le_pathELength hr hαC
      zero_le_one).trans hlen.le
    rw [hα0, hα1, ← ofReal_norm, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.sinh_pos_iff.mpr hr), abs_sub_comm] at hang
    have hangReal := (ENNReal.ofReal_le_ofReal_iff
      (by linarith : 0 ≤ dist z w + ε)).1 hang
    exact ⟨hradReal, hangReal⟩
  exact ⟨le_of_forall_pos_le_add (fun ε hε => (hbound ε hε).1),
    le_of_forall_pos_le_add (fun ε hε => (hbound ε hε).2)⟩

/-- Every original open coordinate neighborhood contains a model ball and
every sufficiently short native C¹ model path starting in a smaller ball.
This barrier uses the length metric's original complex topology. -/
theorem gluingCollarModel_exists_short_path_barrier {r : ℝ} (hr : 0 < r)
    {U : Set ℂ} (hU : IsOpen U) (x : ℂ) (hx : x ∈ U) :
    letI := gluingCollarModelMetricSpace hr
    letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
    ∃ R > 0, ball x R ⊆ U ∧
      ∀ α : ℝ → ℂ, ContDiffOn ℝ 1 α (Icc 0 1) →
        dist x (α 0) < R / 4 →
        gluingCollarModelPathELength hr α 0 1 < ENNReal.ofReal (3 * R / 4) →
        MapsTo α (Icc 0 1) U := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : ℂ → Type) :=
    ⟨(gluingCollarModelContinuousRiemannianMetric hr).toRiemannianMetric⟩
  letI collarMetric : MetricSpace ℂ := gluingCollarModelMetricSpace hr
  letI : PseudoMetricSpace ℂ := collarMetric.toPseudoMetricSpace
  obtain ⟨R, hR, hball⟩ :=
    (@Metric.mem_nhds_iff ℂ collarMetric.toPseudoMetricSpace x U).1 (hU.mem_nhds hx)
  refine ⟨R, hR, hball, ?_⟩
  intro α hα hstart hlen t ht
  have hp := gluingCollarModelEDist_le_pathELength hr
    ((hα.mono (Icc_subset_Icc le_rfl ht.2)).contMDiffOn) ht.1
  change edist (α 0) (α t) ≤ pathELength (modelWithCornersSelf ℝ ℂ) α 0 t at hp
  have hsub : edist (α 0) (α t) < ENNReal.ofReal (3 * R / 4) :=
    hp.trans_lt ((pathELength_mono le_rfl ht.2).trans_lt hlen)
  rw [@edist_dist ℂ collarMetric.toPseudoMetricSpace (α 0) (α t),
    ENNReal.ofReal_lt_ofReal_iff (by linarith)] at hsub
  have htR : dist x (α t) < R := by
    have := @dist_triangle ℂ collarMetric.toPseudoMetricSpace x (α 0) (α t)
    linarith
  apply hball
  simpa only [@Metric.mem_ball ℂ collarMetric.toPseudoMetricSpace,
    @dist_comm ℂ collarMetric.toPseudoMetricSpace] using htR

#print axioms gluingCollarModel_radial_enorm_sub_le_pathELength
#print axioms gluingCollarModel_angular_enorm_sub_le_pathELength
#print axioms gluingCollarModelMetric_coordinates_le_dist
#print axioms gluingCollarModel_exists_short_path_barrier

end SystolicGrowth
