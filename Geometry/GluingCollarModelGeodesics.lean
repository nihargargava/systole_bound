module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarModelProper
public import Geometry.GluingGeodesics
public import Geometry.ProperMidpoints

@[expose] public section

/-!
# Actual metric segments in the signed collar model

Native C¹ near-minimizers split at half the endpoint distance give
approximate midpoints. Actual properness gives exact midpoint attainment,
and the coherent dyadic construction extends to true metric segments using
the collar length metric's proved completeness. No C¹ regularity is claimed
for the limiting metric path, and no curvature assumption is supplied.

Every distance contract explicitly installs the native pseudo-metric and
uniform space as well as the metric, avoiding the ambient complex metric.
-/

open Set Bundle Manifold
open scoped Manifold Topology Bundle ENNReal

namespace SystolicGrowth

/-- Actual native C¹ collar near-minimizers give approximate midpoints,
including paths crossing signed radius zero. -/
theorem gluingCollarModelMetric_approximate_midpoint {r : ℝ} (hr : 0 < r)
    (x y : ℂ) {ε : ℝ} (hε : 0 < ε) :
    letI := gluingCollarModelMetricSpace hr
    letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
    letI := (gluingCollarModelMetricSpace hr).toUniformSpace
    ∃ z : ℂ, dist x z ≤ dist x y / 2 + ε ∧ dist z y ≤ dist x y / 2 + ε := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : ℂ → Type) :=
    gluingCollarModelRiemannianBundle hr
  letI collarMetric : MetricSpace ℂ := gluingCollarModelMetricSpace hr
  letI : PseudoMetricSpace ℂ := collarMetric.toPseudoMetricSpace
  letI : UniformSpace ℂ := collarMetric.toUniformSpace
  have hd : 0 ≤ dist x y := @dist_nonneg ℂ collarMetric.toPseudoMetricSpace x y
  have hnear : riemannianEDist (modelWithCornersSelf ℝ ℂ) x y <
      ENNReal.ofReal (dist x y + ε) := by
    change edist x y < ENNReal.ofReal (dist x y + ε)
    rw [@edist_dist ℂ collarMetric.toPseudoMetricSpace x y,
      ENNReal.ofReal_lt_ofReal_iff (by linarith)]
    linarith
  obtain ⟨α, hα0, hα1, hα, hlen, _, _⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hnear
      (show (0 : ℝ) < 1 by norm_num)
  have hhalf : dist x y / 2 ∈ Icc (dist x (α 0)) (dist x (α 1)) := by
    rw [hα0, hα1, dist_self]
    constructor <;> linarith
  obtain ⟨t, ht, htd⟩ := intermediate_value_Icc zero_le_one
    ((continuous_const.dist hα.continuous).continuousOn) hhalf
  change dist x (α t) = dist x y / 2 at htd
  have htot : pathELength (modelWithCornersSelf ℝ ℂ) α 0 1 < ⊤ :=
    hlen.trans ENNReal.ofReal_lt_top
  have hleft : pathELength (modelWithCornersSelf ℝ ℂ) α 0 t < ⊤ :=
    (pathELength_mono le_rfl ht.2).trans_lt htot
  have hright : pathELength (modelWithCornersSelf ℝ ℂ) α t 1 < ⊤ :=
    (pathELength_mono ht.1 le_rfl).trans_lt htot
  have hsplit := congrArg ENNReal.toReal
    (pathELength_add (I := modelWithCornersSelf ℝ ℂ) (γ := α) ht.1 ht.2)
  rw [ENNReal.toReal_add hleft.ne hright.ne] at hsplit
  have htotalReal : (pathELength (modelWithCornersSelf ℝ ℂ) α 0 1).toReal <
      dist x y + ε := by
    have h := (ENNReal.toReal_lt_toReal htot.ne ENNReal.ofReal_ne_top).2 hlen
    simpa only [ENNReal.toReal_ofReal (by linarith : 0 ≤ dist x y + ε)] using h
  have hleftDist := gluingCollarModelEDist_le_pathELength hr
    (hα.contMDiffOn.mono (Icc_subset_Icc le_rfl ht.2)) ht.1
  change edist (α 0) (α t) ≤ pathELength (modelWithCornersSelf ℝ ℂ) α 0 t at hleftDist
  have hleftReal := ENNReal.toReal_mono hleft.ne hleftDist
  rw [← @dist_edist ℂ collarMetric.toPseudoMetricSpace, hα0, htd] at hleftReal
  have hrightDist := gluingCollarModelEDist_le_pathELength hr
    (hα.contMDiffOn.mono (Icc_subset_Icc ht.1 le_rfl)) ht.2
  change edist (α t) (α 1) ≤ pathELength (modelWithCornersSelf ℝ ℂ) α t 1 at hrightDist
  have hrightReal := ENNReal.toReal_mono hright.ne hrightDist
  rw [← @dist_edist ℂ collarMetric.toPseudoMetricSpace, hα1] at hrightReal
  refine ⟨α t, ?_, ?_⟩
  · rw [htd]
    linarith
  · linarith

/-- Actual compact closed balls attain the half-distance midpoint in the
signed collar length metric. Global compactness is not required. -/
theorem gluingCollarModelMetric_midpoint {r : ℝ} (hr : 0 < r) (x y : ℂ) :
    letI := gluingCollarModelMetricSpace hr
    letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
    letI := (gluingCollarModelMetricSpace hr).toUniformSpace
    ∃ z : ℂ, dist x z = dist x y / 2 ∧ dist z y = dist x y / 2 := by
  letI collarMetric : MetricSpace ℂ := gluingCollarModelMetricSpace hr
  letI : PseudoMetricSpace ℂ := collarMetric.toPseudoMetricSpace
  letI : UniformSpace ℂ := collarMetric.toUniformSpace
  letI : ProperSpace ℂ := gluingCollarModelMetric_properSpace hr
  exact exists_midpoint_of_proper_approximate_midpoints x y
    (fun ε hε => gluingCollarModelMetric_approximate_midpoint hr x y hε)

/-- True collar length-metric segments are constructed from the actual
midpoint grid and native completeness, including coincident endpoints. -/
theorem gluingCollarModelMetric_exists_metric_path {r : ℝ} (hr : 0 < r) (x y : ℂ) :
    letI := gluingCollarModelMetricSpace hr
    letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
    letI := (gluingCollarModelMetricSpace hr).toUniformSpace
    ∃ α : Path x y, ∀ s t : unitInterval,
      dist (α s) (α t) = dist x y * |(s : ℝ) - (t : ℝ)| := by
  letI collarMetric : MetricSpace ℂ := gluingCollarModelMetricSpace hr
  letI : PseudoMetricSpace ℂ := collarMetric.toPseudoMetricSpace
  letI : UniformSpace ℂ := collarMetric.toUniformSpace
  letI : CompleteSpace ℂ := gluingCollarModelMetric_completeSpace hr
  let m : ℂ → ℂ → ℂ := fun a b => (gluingCollarModelMetric_midpoint hr a b).choose
  have hm : ∀ a b, dist a (m a b) = dist a b / 2 ∧ dist (m a b) b = dist a b / 2 :=
    fun a b => (gluingCollarModelMetric_midpoint hr a b).choose_spec
  exact exists_midpoint_metric_path m hm x y

/-- Every genuine collar distance interval embeds isometrically in the
signed collar length metric, with both prescribed endpoints. -/
theorem gluingCollarModelMetric_exists_isometric_segment {r : ℝ} (hr : 0 < r)
    (x y : ℂ) :
    letI := gluingCollarModelMetricSpace hr
    letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
    letI := (gluingCollarModelMetricSpace hr).toUniformSpace
    ∃ σ : Icc (0 : ℝ) (dist x y) → ℂ, Isometry σ ∧
      σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
      σ ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y := by
  letI collarMetric : MetricSpace ℂ := gluingCollarModelMetricSpace hr
  letI : PseudoMetricSpace ℂ := collarMetric.toPseudoMetricSpace
  letI : UniformSpace ℂ := collarMetric.toUniformSpace
  obtain ⟨α, hα⟩ := gluingCollarModelMetric_exists_metric_path hr x y
  exact metric_path_exists_isometric_interval α hα

/-- Actual metric segments have Lipschitz ordinary coordinates, so their
coordinate curves are admissible for warped-product length comparison.
The Lipschitz conclusion uses the original Euclidean complex metric, while
every distance in the segment law is the explicitly applied native metric.
No equality of the two path-length infima is asserted. -/
theorem gluingCollarModelMetric_exists_coordinate_lipschitz_path {r : ℝ}
    (hr : 0 < r) (x y : ℂ) :
    ∃ α : Path x y,
      (∀ s t : unitInterval,
        @dist ℂ (gluingCollarModelMetricSpace hr).toDist (α s) (α t) =
          @dist ℂ (gluingCollarModelMetricSpace hr).toDist x y *
            |(s : ℝ) - (t : ℝ)|) ∧
      LipschitzWith
        ⟨(1 + (Real.sinh r)⁻¹) * @dist ℂ (gluingCollarModelMetricSpace hr).toDist x y,
          mul_nonneg (add_nonneg zero_le_one
            (inv_nonneg.mpr (Real.sinh_pos_iff.mpr hr).le))
            (@dist_nonneg ℂ (gluingCollarModelMetricSpace hr).toPseudoMetricSpace x y)⟩ α := by
  obtain ⟨α, hα⟩ := gluingCollarModelMetric_exists_metric_path hr x y
  refine ⟨α, hα, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro s t
  have hcoord := gluingCollarModelMetric_coordinates_le_dist hr (α s) (α t)
  have him : |(α s).im - (α t).im| ≤
      @dist ℂ (gluingCollarModelMetricSpace hr).toDist (α s) (α t) / Real.sinh r := by
    apply (le_div_iff₀ (Real.sinh_pos_iff.mpr hr)).2
    simpa only [mul_comm] using hcoord.2
  have hnorm : ‖α s - α t‖ ≤ (1 + (Real.sinh r)⁻¹) *
      @dist ℂ (gluingCollarModelMetricSpace hr).toDist (α s) (α t) := by
    calc
      _ ≤ |(α s).re - (α t).re| + |(α s).im - (α t).im| := by
        simpa only [Complex.sub_re, Complex.sub_im] using
          Complex.norm_le_abs_re_add_abs_im (α s - α t)
      _ ≤ @dist ℂ (gluingCollarModelMetricSpace hr).toDist (α s) (α t) +
          @dist ℂ (gluingCollarModelMetricSpace hr).toDist (α s) (α t) / Real.sinh r :=
        add_le_add hcoord.1 him
      _ = _ := by rw [div_eq_mul_inv]; ring
  rw [dist_eq_norm, Subtype.dist_eq, Real.dist_eq]
  change ‖α s - α t‖ ≤
    ((1 + (Real.sinh r)⁻¹) * @dist ℂ (gluingCollarModelMetricSpace hr).toDist x y) *
      |(s : ℝ) - (t : ℝ)|
  convert hnorm using 1
  rw [hα s t]
  ring

#print axioms gluingCollarModelMetric_approximate_midpoint
#print axioms gluingCollarModelMetric_midpoint
#print axioms gluingCollarModelMetric_exists_metric_path
#print axioms gluingCollarModelMetric_exists_isometric_segment
#print axioms gluingCollarModelMetric_exists_coordinate_lipschitz_path

end SystolicGrowth
