module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainBoundedCurvatureMetric
public import Geometry.GluingChainSmoothAreaCharts
public import Geometry.GluingChainSmoothExteriorArea
public import Geometry.GluingChainSmoothGaussBonnet
public import Geometry.GluingChainSmoothCurvature
public import Geometry.HyperbolicGaussianCurvature

@[expose] public section

/-!
# Local Gaussian curvature of the ODE-patched glued metric

Mathlib currently supplies no intrinsic Levi-Civita/Gaussian-curvature
operation for `ContMDiffRiemannianMetric`.  This file proves the strongest
available intrinsic substitute without adding assumptions: every point of
the actual smooth patched metric has an atlas neighborhood on which its
coordinate tensor is exactly one of two explicitly computed metrics.  Their
genuine coordinate Gaussian curvatures are respectively at most `-1` (ODE
seam chart) and equal to `-1` (native hyperbolic chart).
-/

open Set Filter Bundle ContinuousLinearMap MeasureTheory
open scoped Manifold Topology ContDiff

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** The explicit Gaussian scalar of the ODE metric in a seam chart.  Its
definition is the scalar computed from the literal Christoffel and Riemann
coordinates in `GluingWarpedGaussianCurvature`. -/
def gluedCurvatureBoundedSeamGaussian
    (P : ExerciseGluingPreparation C g n genera X) (z : ℂ) : ℝ :=
  gluingWarpedGaussianCurvature
    (gluingCurvatureBoundedWarp (gluingRadius C g) (gluingThinSeamWidth C g)
      P.thinSeamWidth_pos) (z.re, z.im)

theorem gluedCurvatureBoundedSeamGaussian_le_neg_one
    (P : ExerciseGluingPreparation C g n genera X) (z : ℂ) :
    gluedCurvatureBoundedSeamGaussian P z ≤ -1 := by
  exact gluingCurvatureBoundedWarp_gaussianCurvature_le_neg_one
    P.radius_pos P.thinSeamWidth_pos (z.re, z.im)

/-- **Math.** The signed curvature density of the explicit ODE collar, expressed in
the genuine one-turn circle and open radial-strip coordinates. -/
def gluedCurvatureBoundedThinCylinderCurvatureDensity
    (r δ : ℝ) (hδ : 0 < δ) (p : Circle × Ioo (-δ) δ) : ℝ :=
  -deriv (deriv (gluingCurvatureBoundedWarp r δ hδ)) p.2.1

set_option maxHeartbeats 400000 in
/-- **Math.** The ODE cylinder density is the genuine Gaussian curvature multiplied
by the determinant area density of its constructed warped metric. -/
theorem gluedCurvatureBoundedThinCylinderCurvatureDensity_eq_gaussian_mul_area
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (p : Circle × Ioo (-δ) δ) :
    gluedCurvatureBoundedThinCylinderCurvatureDensity r δ hδ p =
      gluingWarpedGaussianCurvature
          (gluingCurvatureBoundedWarp r δ hδ) (p.2.1, 0) *
        gluingCurvatureBoundedWarp r δ hδ p.2.1 := by
  have hindex : (2 : ℕ∞ω) ≤ ∞ := by
    exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
  have hW : ContDiff ℝ 2 (gluingCurvatureBoundedWarp r δ hδ) :=
    (gluingCurvatureBoundedWarp_contDiff r δ hδ).of_le hindex
  have hpos : 0 < gluingCurvatureBoundedWarp r δ hδ p.2.1 :=
    gluingCurvatureBoundedWarp_pos hr hδ p.2.1
  have hmass := gluingWarpedGaussianCurvature_mul_areaDensity
    (x := (p.2.1, 0)) hW hpos
  rw [gluingWarpedMetric_areaDensity (x := (p.2.1, 0)) hpos] at hmass
  change -deriv (deriv (gluingCurvatureBoundedWarp r δ hδ)) p.2.1 = _
  exact hmass.symm

theorem gluedCurvatureBoundedThinCylinderCurvatureDensity_integrable
    (r δ : ℝ) (hδ : 0 < δ) :
    Integrable (gluedCurvatureBoundedThinCylinderCurvatureDensity r δ hδ)
      (gluingThinCylinderCoordinateMeasure δ) := by
  have hi : IntegrableOn
      (fun t : ℝ => -deriv (deriv (gluingCurvatureBoundedWarp r δ hδ)) t)
      (Icc (-δ) δ) :=
    ((gluingCurvatureBoundedWarp_contDiff r δ hδ).of_le (by
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))).deriv'.continuous_deriv_one.neg
      |>.continuousOn.integrableOn_compact isCompact_Icc
  have hs := (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mp
    (hi.mono_set Ioo_subset_Icc_self)
  change Integrable (fun t : Ioo (-δ) δ =>
    -deriv (deriv (gluingCurvatureBoundedWarp r δ hδ)) t.1)
    (gluingThinRadialMeasure δ) at hs
  exact hs.comp_snd gluingCircleAngularLengthMeasure

/-- **Math.** The genuine signed ODE-collar curvature measure in circle/radial
coordinates. -/
def gluedCurvatureBoundedThinCylinderCurvature
    (r δ : ℝ) (hδ : 0 < δ) : SignedMeasure (Circle × Ioo (-δ) δ) :=
  (gluingThinCylinderCoordinateMeasure δ).withDensityᵥ
    (gluedCurvatureBoundedThinCylinderCurvatureDensity r δ hδ)

/-- **Math.** The actual ODE-collar area measure, using the square root of
the warped metric determinant as its density. -/
def gluedCurvatureBoundedThinCylinderArea
    (r δ : ℝ) (hδ : 0 < δ) : Measure (Circle × Ioo (-δ) δ) :=
  (gluingThinCylinderCoordinateMeasure δ).withDensity
    (fun p => ENNReal.ofReal (gluingCurvatureBoundedWarp r δ hδ p.2.1))

instance gluedCurvatureBoundedThinCylinderArea_isFinite
    (r δ : ℝ) (hδ : 0 < δ) :
    IsFiniteMeasure (gluedCurvatureBoundedThinCylinderArea r δ hδ) := by
  unfold gluedCurvatureBoundedThinCylinderArea
  exact isFiniteMeasure_withDensity_ofReal
    (gluingThinCylinder_radial_integrable
      (gluingCurvatureBoundedWarp_contDiff r δ hδ).continuous δ).2

/-- **Math.** The ODE cylinder area pulls back to the exact warped density
in every literal real angular chart. -/
theorem gluedCurvatureBoundedThinCylinderArea_comap_angular
    (r δ : ℝ) (hδ : 0 < δ) (θ : ℝ) :
    (gluedCurvatureBoundedThinCylinderArea r δ hδ).comap
        (gluingThinAngularCylinderMap δ θ) =
      ((((volume : Measure ℝ).comap (Subtype.val : Ioo (-δ) δ → ℝ)).prod
        ((volume : Measure ℝ).comap (Subtype.val : GluingAngularInterval θ → ℝ))).withDensity
        (fun p => ENNReal.ofReal (gluingCurvatureBoundedWarp r δ hδ p.1.1))) := by
  rw [gluedCurvatureBoundedThinCylinderArea,
    gluingMeasure_comap_withDensity
      (gluingThinAngularCylinderMap_measurableEmbedding δ θ),
    gluingThinCylinderCoordinateMeasure_comap_angular]
  rfl

/-- **Math.** Gaussian curvature of the actual ODE cylinder at the point's
radial coordinate. -/
def gluedCurvatureBoundedThinCylinderGaussian
    (r δ : ℝ) (hδ : 0 < δ) (p : Circle × Ioo (-δ) δ) : ℝ :=
  gluingWarpedGaussianCurvature (gluingCurvatureBoundedWarp r δ hδ) (p.2.1, 0)

theorem gluedCurvatureBoundedThinCylinderGaussian_continuous
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) :
    Continuous (gluedCurvatureBoundedThinCylinderGaussian r δ hδ) := by
  have hindex : (2 : ℕ∞ω) ≤ ∞ := by
    exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
  have hW : ContDiff ℝ 2 (gluingCurvatureBoundedWarp r δ hδ) :=
    (gluingCurvatureBoundedWarp_contDiff r δ hδ).of_le hindex
  have hnum : Continuous (fun p : Circle × Ioo (-δ) δ =>
      -deriv (deriv (gluingCurvatureBoundedWarp r δ hδ)) p.2.1) :=
    (hW.deriv'.continuous_deriv_one.neg).comp
      (continuous_subtype_val.comp continuous_snd)
  have hden : Continuous (fun p : Circle × Ioo (-δ) δ =>
      gluingCurvatureBoundedWarp r δ hδ p.2.1) :=
    (gluingCurvatureBoundedWarp_contDiff r δ hδ).continuous.comp
      (continuous_subtype_val.comp continuous_snd)
  have hformula : gluedCurvatureBoundedThinCylinderGaussian r δ hδ = fun p =>
      -deriv (deriv (gluingCurvatureBoundedWarp r δ hδ)) p.2.1 /
        gluingCurvatureBoundedWarp r δ hδ p.2.1 := by
    funext p
    exact gluingWarpedGaussianCurvature_eq hW
      (gluingCurvatureBoundedWarp_pos hr hδ p.2.1)
  rw [hformula]
  exact hnum.div hden (fun p =>
    (gluingCurvatureBoundedWarp_pos hr hδ p.2.1).ne')

theorem gluedCurvatureBoundedThinCylinderGaussian_mul_warp
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (p : Circle × Ioo (-δ) δ) :
    gluingCurvatureBoundedWarp r δ hδ p.2.1 *
      gluedCurvatureBoundedThinCylinderGaussian r δ hδ p =
        gluedCurvatureBoundedThinCylinderCurvatureDensity r δ hδ p := by
  rw [gluedCurvatureBoundedThinCylinderCurvatureDensity_eq_gaussian_mul_area hr hδ p]
  simp only [gluedCurvatureBoundedThinCylinderGaussian]
  ring

theorem gluedCurvatureBoundedThinCylinderGaussian_integrable_area
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) :
    Integrable (gluedCurvatureBoundedThinCylinderGaussian r δ hδ)
      (gluedCurvatureBoundedThinCylinderArea r δ hδ) := by
  rw [gluedCurvatureBoundedThinCylinderArea]
  apply (integrable_withDensity_iff_integrable_smul'
    (((gluingCurvatureBoundedWarp_contDiff r δ hδ).continuous.comp
      (continuous_subtype_val.comp continuous_snd)).measurable.ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
  have heq : (fun p : Circle × Ioo (-δ) δ =>
      (ENNReal.ofReal (gluingCurvatureBoundedWarp r δ hδ p.2.1)).toReal •
        gluedCurvatureBoundedThinCylinderGaussian r δ hδ p) =
      gluedCurvatureBoundedThinCylinderCurvatureDensity r δ hδ := by
    funext p
    rw [ENNReal.toReal_ofReal
      (gluingCurvatureBoundedWarp_pos hr hδ p.2.1).le,
      smul_eq_mul, gluedCurvatureBoundedThinCylinderGaussian_mul_warp hr hδ]
  change Integrable (fun p : Circle × Ioo (-δ) δ =>
    (ENNReal.ofReal (gluingCurvatureBoundedWarp r δ hδ p.2.1)).toReal •
      gluedCurvatureBoundedThinCylinderGaussian r δ hδ p)
    (gluingThinCylinderCoordinateMeasure δ)
  rw [heq]
  exact gluedCurvatureBoundedThinCylinderCurvatureDensity_integrable r δ hδ

theorem gluedCurvatureBoundedThinCylinderCurvature_eq_area_withDensity_gaussian
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) :
    gluedCurvatureBoundedThinCylinderCurvature r δ hδ =
      (gluedCurvatureBoundedThinCylinderArea r δ hδ).withDensityᵥ
        (gluedCurvatureBoundedThinCylinderGaussian r δ hδ) := by
  have heq : (fun p : Circle × Ioo (-δ) δ =>
      (ENNReal.ofReal (gluingCurvatureBoundedWarp r δ hδ p.2.1)).toReal •
        gluedCurvatureBoundedThinCylinderGaussian r δ hδ p) =
      gluedCurvatureBoundedThinCylinderCurvatureDensity r δ hδ := by
    funext p
    rw [ENNReal.toReal_ofReal
      (gluingCurvatureBoundedWarp_pos hr hδ p.2.1).le,
      smul_eq_mul, gluedCurvatureBoundedThinCylinderGaussian_mul_warp hr hδ]
  have hfg : Integrable (fun p : Circle × Ioo (-δ) δ =>
      (ENNReal.ofReal (gluingCurvatureBoundedWarp r δ hδ p.2.1)).toReal •
        gluedCurvatureBoundedThinCylinderGaussian r δ hδ p)
      (gluingThinCylinderCoordinateMeasure δ) := by
    rw [heq]
    exact gluedCurvatureBoundedThinCylinderCurvatureDensity_integrable r δ hδ
  have h := withDensityᵥ_smul_eq_withDensityᵥ_withDensity'
    (μ := gluingThinCylinderCoordinateMeasure δ)
    (f := fun p => ENNReal.ofReal (gluingCurvatureBoundedWarp r δ hδ p.2.1))
    (g := gluedCurvatureBoundedThinCylinderGaussian r δ hδ)
    (((gluingCurvatureBoundedWarp_contDiff r δ hδ).continuous.comp
      (continuous_subtype_val.comp continuous_snd)).measurable.ennreal_ofReal.aemeasurable)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) hfg
  simpa only [heq, gluedCurvatureBoundedThinCylinderCurvature,
    gluedCurvatureBoundedThinCylinderArea] using h

/-- **Math.** The ODE collar has exactly the same signed curvature mass as the
localized smoothing; this is the full angular mass of the radial endpoint
identity proved for the normalized warp. -/
theorem gluedCurvatureBoundedThinCylinderCurvature_univ
    (r δ : ℝ) (hδ : 0 < δ) :
    gluedCurvatureBoundedThinCylinderCurvature r δ hδ univ =
      -4 * Real.pi * Real.cosh (r + δ) := by
  have hI := gluedCurvatureBoundedThinCylinderCurvatureDensity_integrable r δ hδ
  rw [gluedCurvatureBoundedThinCylinderCurvature,
    withDensityᵥ_apply hI MeasurableSet.univ,
    Measure.restrict_univ, gluingThinCylinderCoordinateMeasure,
    integral_prod _ hI]
  simp only [gluedCurvatureBoundedThinCylinderCurvatureDensity,
    integral_const, smul_eq_mul]
  rw [measureReal_def, gluingCircleAngularLengthMeasure_univ,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi),
    gluingThinRadialMeasure, integral_subtype_comap measurableSet_Ioo
      (fun t : ℝ => -deriv (deriv (gluingCurvatureBoundedWarp r δ hδ)) t),
    gluingCurvatureBoundedWarp_signed_radial_curvature_mass_Ioo]
  ring

/-- **Math.** Push the actual ODE collar curvature measure into the corresponding
thin seam of the glued carrier. -/
def gluedCurvatureBoundedSeamCurvature
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    SignedMeasure P.GluedCarrier :=
  (gluedCurvatureBoundedThinCylinderCurvature (gluingRadius C g)
    (gluingThinSeamWidth C g) P.thinSeamWidth_pos).map
      (P.thinSeamCylinderMap k)

theorem gluedCurvatureBoundedSeamCurvature_univ
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedCurvatureBoundedSeamCurvature k univ =
      -4 * Real.pi * Real.cosh
        (gluingRadius C g + gluingThinSeamWidth C g) := by
  rw [gluedCurvatureBoundedSeamCurvature,
    VectorMeasure.map_apply _
      (P.thinSeamCylinderMap_measurableEmbedding k).measurable
      MeasurableSet.univ, preimage_univ]
  exact gluedCurvatureBoundedThinCylinderCurvature_univ _ _ _

/-- **Math.** The ODE collar pieces together with unchanged exterior area form a global
signed curvature measure on the actual glued carrier. -/
def gluedCurvatureBoundedCurvature
    (P : ExerciseGluingPreparation C g n genera X) : SignedMeasure P.GluedCarrier :=
  -P.gluedChainSmoothOutsideArea.toSignedMeasure +
    ∑ k : Fin (n - 1), P.gluedCurvatureBoundedSeamCurvature k

/-- **Math.** ODE-collar area transported through the actual seam embedding. -/
def gluedCurvatureBoundedSeamArea
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Measure P.GluedCarrier :=
  Measure.map (P.thinSeamCylinderMap k)
    (gluedCurvatureBoundedThinCylinderArea (gluingRadius C g)
      (gluingThinSeamWidth C g) P.thinSeamWidth_pos)

instance gluedCurvatureBoundedSeamArea_isFinite
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    IsFiniteMeasure (P.gluedCurvatureBoundedSeamArea k) := by
  unfold gluedCurvatureBoundedSeamArea
  infer_instance

/-- **Math.** Global area measure of the ODE-patched metric: native area on
the exterior and its determinant density in each disjoint seam cylinder. -/
def gluedCurvatureBoundedAreaMeasure
    (P : ExerciseGluingPreparation C g n genera X) : Measure P.GluedCarrier :=
  P.gluedChainSmoothOutsideArea +
    ∑ k : Fin (n - 1), P.gluedCurvatureBoundedSeamArea k

instance gluedCurvatureBoundedAreaMeasure_isFinite
    (P : ExerciseGluingPreparation C g n genera X) :
    IsFiniteMeasure P.gluedCurvatureBoundedAreaMeasure := by
  unfold gluedCurvatureBoundedAreaMeasure
  infer_instance

theorem gluedCurvatureBoundedSeamArea_restrict_own_thinCollar
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    (P.gluedCurvatureBoundedSeamArea k).restrict (P.thinSeamCollar k) =
      P.gluedCurvatureBoundedSeamArea k := by
  rw [gluedCurvatureBoundedSeamArea,
    Measure.restrict_map (P.thinSeamCylinderMap_measurableEmbedding k).measurable
      (P.thinSeamCollar_isOpen k).measurableSet]
  have hpre : P.thinSeamCylinderMap k ⁻¹' P.thinSeamCollar k = univ := by
    rw [← P.range_thinSeamCylinderMap k, preimage_range]
  rw [hpre, Measure.restrict_univ]

theorem gluedCurvatureBoundedSeamArea_restrict_distinct_thinCollar
    (P : ExerciseGluingPreparation C g n genera X)
    {k l : Fin (n - 1)} (hkl : k ≠ l) :
    (P.gluedCurvatureBoundedSeamArea k).restrict (P.thinSeamCollar l) = 0 := by
  rw [gluedCurvatureBoundedSeamArea,
    Measure.restrict_map (P.thinSeamCylinderMap_measurableEmbedding k).measurable
      (P.thinSeamCollar_isOpen l).measurableSet]
  have hpre : P.thinSeamCylinderMap k ⁻¹' P.thinSeamCollar l = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hk : P.thinSeamCylinderMap k p ∈ P.thinSeamCollar k := by
      rw [← P.range_thinSeamCylinderMap k]
      exact ⟨p, rfl⟩
    exact disjoint_left.mp (P.closedThinSeamCollar_disjoint hkl)
      (P.thinSeamCollar_subset_closedThinSeamCollar k hk)
      (P.thinSeamCollar_subset_closedThinSeamCollar l hp)
  simp [hpre]

theorem gluedCurvatureBoundedAreaMeasure_restrict_thinCollar
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedCurvatureBoundedAreaMeasure.restrict (P.thinSeamCollar k) =
      P.gluedCurvatureBoundedSeamArea k := by
  classical
  rw [gluedCurvatureBoundedAreaMeasure, Measure.restrict_add,
    P.gluedChainSmoothOutsideArea_restrict_thinCollar k, zero_add]
  have hsum := map_sum (Measure.restrictₗ (P.thinSeamCollar k))
    (fun l : Fin (n - 1) => P.gluedCurvatureBoundedSeamArea l) Finset.univ
  simp only [Measure.restrictₗ_apply] at hsum
  rw [hsum, Finset.sum_eq_single k]
  · exact P.gluedCurvatureBoundedSeamArea_restrict_own_thinCollar k
  · intro l _ hlk
    exact P.gluedCurvatureBoundedSeamArea_restrict_distinct_thinCollar hlk
  · simp

theorem gluedCurvatureBoundedAreaMeasure_comap_thinSeamCylinderMap
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedCurvatureBoundedAreaMeasure.comap (P.thinSeamCylinderMap k) =
      gluedCurvatureBoundedThinCylinderArea (gluingRadius C g)
        (gluingThinSeamWidth C g) P.thinSeamWidth_pos := by
  have hf := P.thinSeamCylinderMap_measurableEmbedding k
  have h := congrArg
    (fun μ : Measure P.GluedCarrier => μ.comap (P.thinSeamCylinderMap k))
    (P.gluedCurvatureBoundedAreaMeasure_restrict_thinCollar k)
  rw [hf.comap_restrict, ← P.range_thinSeamCylinderMap k, preimage_range,
    Measure.restrict_univ, gluedCurvatureBoundedSeamArea, hf.comap_map] at h
  exact h

/-- **Math.** Outside the disjoint ODE strips, the global candidate area is exactly the
unchanged native area measure. -/
theorem gluedCurvatureBoundedAreaMeasure_restrict_outside_thinCollars
    (P : ExerciseGluingPreparation C g n genera X) :
    P.gluedCurvatureBoundedAreaMeasure.restrict
        (⋃ k : Fin (n - 1), P.thinSeamCollar k)ᶜ =
      P.gluedChainSmoothOutsideArea := by
  classical
  let U : Set P.GluedCarrier := ⋃ k : Fin (n - 1), P.thinSeamCollar k
  have hU : MeasurableSet U :=
    MeasurableSet.iUnion (fun k => (P.thinSeamCollar_isOpen k).measurableSet)
  have hseam (k : Fin (n - 1)) :
      (P.gluedCurvatureBoundedSeamArea k).restrict Uᶜ = 0 := by
    rw [gluedCurvatureBoundedSeamArea,
      (P.thinSeamCylinderMap_measurableEmbedding k).restrict_map]
    have hpre : P.thinSeamCylinderMap k ⁻¹' Uᶜ = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      apply hp
      apply mem_iUnion.mpr
      refine ⟨k, ?_⟩
      rw [← P.range_thinSeamCylinderMap k]
      exact mem_range_self p
    simp [hpre]
  apply Measure.ext
  intro s hs
  have hseamval (k : Fin (n - 1)) :
      P.gluedCurvatureBoundedSeamArea k (s ∩ Uᶜ) = 0 := by
    have h := congrArg (fun μ : Measure P.GluedCarrier => μ s) (hseam k)
    simpa [Measure.restrict_apply hs] using h
  rw [Measure.restrict_apply hs, gluedChainSmoothOutsideArea,
    Measure.restrict_apply hs]
  change P.gluedCurvatureBoundedAreaMeasure (s ∩ Uᶜ) =
    P.gluedChainAreaMeasure (s ∩ Uᶜ)
  rw [gluedCurvatureBoundedAreaMeasure, Measure.add_apply,
    Measure.finsetSum_apply, Finset.sum_eq_zero (fun k _ => hseamval k), add_zero]
  rw [gluedChainSmoothOutsideArea,
    Measure.restrict_apply (hs.inter hU.compl)]
  have hcomplUnion : Uᶜ ⊆ (⋃ i : Fin (n - 1), P.thinSeamCollar i)ᶜ := by
    change Uᶜ ⊆ Uᶜ
    exact subset_rfl
  rw [inter_assoc, inter_eq_left.mpr hcomplUnion]

/-- **Math.** Measurable global Gaussian curvature field of the ODE-patched
metric, defined by the local cylinder fields and the unchanged exterior value. -/
def gluedCurvatureBoundedGaussian
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedCarrier) : ℝ :=
  -1 + ∑ k : Fin (n - 1), Function.extend (P.thinSeamCylinderMap k)
    (fun p => gluedCurvatureBoundedThinCylinderGaussian (gluingRadius C g)
      (gluingThinSeamWidth C g) P.thinSeamWidth_pos p + 1)
    (fun _ => 0) q

theorem gluedCurvatureBoundedGaussian_measurable
    (P : ExerciseGluingPreparation C g n genera X) :
    Measurable P.gluedCurvatureBoundedGaussian := by
  apply Measurable.add measurable_const
  apply Finset.measurable_sum
  intro k _
  exact (P.thinSeamCylinderMap_measurableEmbedding k).measurable_extend
    ((gluedCurvatureBoundedThinCylinderGaussian_continuous
      P.radius_pos P.thinSeamWidth_pos).measurable.add_const 1) measurable_const

theorem gluedCurvatureBoundedGaussian_eq_neg_one_of_outside
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedCarrier)
    (hq : ∀ k : Fin (n - 1), q ∉ P.thinSeamCollar k) :
    P.gluedCurvatureBoundedGaussian q = -1 := by
  unfold gluedCurvatureBoundedGaussian
  have hz : (∑ k : Fin (n - 1), Function.extend (P.thinSeamCylinderMap k)
      (fun p => gluedCurvatureBoundedThinCylinderGaussian (gluingRadius C g)
        (gluingThinSeamWidth C g) P.thinSeamWidth_pos p + 1)
      (fun _ => 0) q) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    apply Function.extend_apply'
    rintro ⟨p, hp⟩
    apply hq k
    rw [← P.range_thinSeamCylinderMap k, ← hp]
    exact ⟨p, rfl⟩
  rw [hz, add_zero]

theorem gluedCurvatureBoundedGaussian_thinSeamCylinderMap
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (p : Circle × Ioo (-gluingThinSeamWidth C g) (gluingThinSeamWidth C g)) :
    P.gluedCurvatureBoundedGaussian (P.thinSeamCylinderMap k p) =
      gluedCurvatureBoundedThinCylinderGaussian (gluingRadius C g)
        (gluingThinSeamWidth C g) P.thinSeamWidth_pos p := by
  classical
  unfold gluedCurvatureBoundedGaussian
  rw [Finset.sum_eq_single k]
  · rw [(P.thinSeamCylinderMap_measurableEmbedding k).injective.extend_apply]
    ring
  · intro l _ hlk
    apply Function.extend_apply'
    rintro ⟨q, hq⟩
    have hk : P.thinSeamCylinderMap k p ∈ P.thinSeamCollar k := by
      rw [← P.range_thinSeamCylinderMap k]
      exact ⟨p, rfl⟩
    have hl : P.thinSeamCylinderMap k p ∈ P.thinSeamCollar l := by
      rw [← P.range_thinSeamCylinderMap l, ← hq]
      exact ⟨q, rfl⟩
    exact disjoint_left.mp (P.closedThinSeamCollar_disjoint hlk)
      (P.thinSeamCollar_subset_closedThinSeamCollar l hl)
      (P.thinSeamCollar_subset_closedThinSeamCollar k hk)
  · simp

theorem gluedCurvatureBoundedGaussian_le_neg_one
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedCarrier) :
    P.gluedCurvatureBoundedGaussian q ≤ -1 := by
  by_cases hq : ∃ k : Fin (n - 1), q ∈ P.thinSeamCollar k
  · obtain ⟨k, hk⟩ := hq
    have hrange : q ∈ Set.range (P.thinSeamCylinderMap k) := by
      rw [P.range_thinSeamCylinderMap k]
      exact hk
    obtain ⟨p, rfl⟩ := hrange
    rw [P.gluedCurvatureBoundedGaussian_thinSeamCylinderMap]
    exact gluingCurvatureBoundedWarp_gaussianCurvature_le_neg_one
      P.radius_pos P.thinSeamWidth_pos (p.2.1, 0)
  · rw [P.gluedCurvatureBoundedGaussian_eq_neg_one_of_outside q (by
      intro k hk
      exact hq ⟨k, hk⟩)]

theorem gluedCurvatureBoundedGaussian_integrable_outsideArea
    (P : ExerciseGluingPreparation C g n genera X) :
    Integrable P.gluedCurvatureBoundedGaussian P.gluedChainSmoothOutsideArea := by
  have hU : MeasurableSet (⋃ k : Fin (n - 1), P.thinSeamCollar k) :=
    (isOpen_iUnion fun k => P.thinSeamCollar_isOpen k).measurableSet
  have hEq : P.gluedCurvatureBoundedGaussian =ᵐ[P.gluedChainSmoothOutsideArea]
      fun _ => -1 := by
    filter_upwards [ae_restrict_mem hU.compl] with q hq
    exact P.gluedCurvatureBoundedGaussian_eq_neg_one_of_outside q
      (fun k hk => hq (mem_iUnion.mpr ⟨k, hk⟩))
  exact (integrable_const (-1 : ℝ)).congr hEq.symm

theorem gluedCurvatureBoundedGaussian_integrable_seamArea
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Integrable P.gluedCurvatureBoundedGaussian (P.gluedCurvatureBoundedSeamArea k) := by
  rw [gluedCurvatureBoundedSeamArea,
    (P.thinSeamCylinderMap_measurableEmbedding k).integrable_map_iff]
  have heq : (P.gluedCurvatureBoundedGaussian ∘ P.thinSeamCylinderMap k) =
      gluedCurvatureBoundedThinCylinderGaussian (gluingRadius C g)
        (gluingThinSeamWidth C g) P.thinSeamWidth_pos :=
    funext (P.gluedCurvatureBoundedGaussian_thinSeamCylinderMap k)
  rw [heq]
  exact gluedCurvatureBoundedThinCylinderGaussian_integrable_area
    P.radius_pos P.thinSeamWidth_pos

theorem gluedCurvatureBoundedGaussian_integrable_area
    (P : ExerciseGluingPreparation C g n genera X) :
    Integrable P.gluedCurvatureBoundedGaussian P.gluedCurvatureBoundedAreaMeasure := by
  apply (P.gluedCurvatureBoundedGaussian_integrable_outsideArea).add_measure
  exact integrable_finsetSum_measure.mpr fun k _ =>
    P.gluedCurvatureBoundedGaussian_integrable_seamArea k

theorem gluedCurvatureBoundedOutsideArea_withDensity_gaussian
    (P : ExerciseGluingPreparation C g n genera X) :
    P.gluedChainSmoothOutsideArea.withDensityᵥ P.gluedCurvatureBoundedGaussian =
      -P.gluedChainSmoothOutsideArea.toSignedMeasure := by
  have hU : MeasurableSet (⋃ k : Fin (n - 1), P.thinSeamCollar k) :=
    (isOpen_iUnion fun k => P.thinSeamCollar_isOpen k).measurableSet
  have hEq : P.gluedCurvatureBoundedGaussian =ᵐ[P.gluedChainSmoothOutsideArea]
      fun _ => -1 := by
    filter_upwards [ae_restrict_mem hU.compl] with q hq
    exact P.gluedCurvatureBoundedGaussian_eq_neg_one_of_outside q
      (fun k hk => hq (mem_iUnion.mpr ⟨k, hk⟩))
  rw [WithDensityᵥEq.congr_ae hEq]
  ext s hs
  rw [withDensityᵥ_apply (integrable_const _) hs, _root_.neg_apply,
    Measure.toSignedMeasure_apply_measurable hs, integral_const]
  simp [smul_eq_mul]

theorem gluedCurvatureBoundedSeamArea_withDensity_gaussian
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    (P.gluedCurvatureBoundedSeamArea k).withDensityᵥ
      P.gluedCurvatureBoundedGaussian = P.gluedCurvatureBoundedSeamCurvature k := by
  have heq : (P.gluedCurvatureBoundedGaussian ∘ P.thinSeamCylinderMap k) =
      gluedCurvatureBoundedThinCylinderGaussian (gluingRadius C g)
        (gluingThinSeamWidth C g) P.thinSeamWidth_pos :=
    funext (P.gluedCurvatureBoundedGaussian_thinSeamCylinderMap k)
  rw [gluedCurvatureBoundedSeamArea,
    ← signedMeasure_map_withDensity_of_embedding
      (P.thinSeamCylinderMap_measurableEmbedding k) _
      (by
        rw [heq]
        exact gluedCurvatureBoundedThinCylinderGaussian_integrable_area
          P.radius_pos P.thinSeamWidth_pos),
    heq, ← gluedCurvatureBoundedThinCylinderCurvature_eq_area_withDensity_gaussian
      P.radius_pos P.thinSeamWidth_pos]
  rfl

theorem gluedCurvatureBoundedCurvature_eq_area_withDensity_gaussian
    (P : ExerciseGluingPreparation C g n genera X) :
    P.gluedCurvatureBoundedCurvature =
      P.gluedCurvatureBoundedAreaMeasure.withDensityᵥ
        P.gluedCurvatureBoundedGaussian := by
  rw [gluedCurvatureBoundedAreaMeasure,
    signedMeasure_withDensity_add_measure _ _
      P.gluedCurvatureBoundedGaussian_integrable_outsideArea
      (integrable_finsetSum_measure.mpr fun k _ =>
        P.gluedCurvatureBoundedGaussian_integrable_seamArea k),
    signedMeasure_withDensity_finsetSum_measure _ Finset.univ
      (fun k _ => P.gluedCurvatureBoundedGaussian_integrable_seamArea k),
    P.gluedCurvatureBoundedOutsideArea_withDensity_gaussian]
  simp only [P.gluedCurvatureBoundedSeamArea_withDensity_gaussian]
  rfl

/-- **Math.** The assembled ODE-curvature measure has the exact original-genus total.
The collar contribution is the verified ODE mass; the exterior is unchanged. -/
theorem gluedCurvatureBoundedCurvature_univ
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (hsum : (∑ i, genera i) = g) :
    P.gluedCurvatureBoundedCurvature univ = -4 * Real.pi * ((g : ℝ) - 1) := by
  rw [gluedCurvatureBoundedCurvature, add_apply, neg_apply,
    Measure.toSignedMeasure_apply_measurable MeasurableSet.univ]
  simp only [FunLike.coe_sum, Finset.sum_apply]
  simp_rw [P.gluedCurvatureBoundedSeamCurvature_univ]
  rw [P.gluedChainSmoothOutsideArea_real_univ,
    P.gluedChainAreaMeasure_real_univ hn hsum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem gluedCurvatureBoundedGaussian_integral
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (hsum : (∑ i, genera i) = g) :
    (∫ q, P.gluedCurvatureBoundedGaussian q
      ∂P.gluedCurvatureBoundedAreaMeasure) = -4 * Real.pi * ((g : ℝ) - 1) := by
  have hmass := P.gluedCurvatureBoundedCurvature_univ hn hsum
  rw [P.gluedCurvatureBoundedCurvature_eq_area_withDensity_gaussian,
    withDensityᵥ_apply P.gluedCurvatureBoundedGaussian_integrable_area
      MeasurableSet.univ,
    Measure.restrict_univ] at hmass
  exact hmass

/-- **Math.** The ODE-patched metric's global Gaussian-area measure is at most
the Gauss--Bonnet area `4π(g - 1)`. -/
theorem gluedCurvatureBoundedAreaMeasure_real_univ_le
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (hsum : (∑ i, genera i) = g) :
    P.gluedCurvatureBoundedAreaMeasure.real univ ≤
      4 * Real.pi * ((g : ℝ) - 1) := by
  have hmono :
      (∫ q, P.gluedCurvatureBoundedGaussian q
        ∂P.gluedCurvatureBoundedAreaMeasure) ≤
        -(P.gluedCurvatureBoundedAreaMeasure.real univ) := by
    calc
      (∫ q, P.gluedCurvatureBoundedGaussian q
          ∂P.gluedCurvatureBoundedAreaMeasure) ≤
          ∫ q, (-1 : ℝ) ∂P.gluedCurvatureBoundedAreaMeasure :=
        integral_mono_ae P.gluedCurvatureBoundedGaussian_integrable_area
          (integrable_const (-1 : ℝ))
          (ae_of_all _ fun q => P.gluedCurvatureBoundedGaussian_le_neg_one q)
      _ = -(P.gluedCurvatureBoundedAreaMeasure.real univ) := by
        simp [integral_const, measureReal_def, smul_eq_mul]
  rw [P.gluedCurvatureBoundedGaussian_integral hn hsum] at hmono
  linarith

/-- **Math.** In the seam chart the patched metric coefficient is the literal
`dt² + f(t)² dθ²` coefficient used to compute the seam Gaussian scalar. -/
theorem gluingComplexCurvatureBoundedTangentForm_eq_warpedMetricForm
    (P : ExerciseGluingPreparation C g n genera X) (z v u : ℂ) :
    gluingComplexCurvatureBoundedTangentForm (gluingRadius C g)
        (gluingThinSeamWidth C g) P.thinSeamWidth_pos z v u =
      gluingWarpedMetricForm
        (gluingCurvatureBoundedWarp (gluingRadius C g) (gluingThinSeamWidth C g)
          P.thinSeamWidth_pos) (z.re, z.im)
        ![v.re, v.im] ![u.re, u.im] := by
  rw [gluingComplexCurvatureBoundedTangentForm_apply,
    gluingWarpedMetricForm_apply]
  simp

/-- **Math.** Pointwise local metric identity plus its exact coordinate Gaussian
bound. The `hother` premise says the selected seam chart is isolated from
the other disjoint seam collars; it is proved automatically in the global
chart-cover theorem below. -/
theorem gluedCurvatureBoundedSmoothMetric_seam_chart
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (b : P.GluedCarrier) (hb : b ∈ (P.seamAngularComplexChart k θ).source)
    (hother : ∀ l : Fin (n - 1), l ≠ k → b ∉ P.thinSeamCollar l) :
    gluedCurvatureBoundedSeamGaussian P (P.seamAngularComplexChart k θ b) ≤ -1 ∧
      ∀ v u : ℂ,
        (P.gluedCurvatureBoundedSmoothRiemannianMetric).inner b
          (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
            (⟨P.seamAngularComplexChart k θ,
              Or.inr ⟨k, θ, rfl⟩⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ b v)
          (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
            (⟨P.seamAngularComplexChart k θ,
              Or.inr ⟨k, θ, rfl⟩⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ b u) =
        gluingComplexCurvatureBoundedTangentForm (gluingRadius C g)
          (gluingThinSeamWidth C g) P.thinSeamWidth_pos
          (P.seamAngularComplexChart k θ b) v u := by
  constructor
  · exact gluedCurvatureBoundedSeamGaussian_le_neg_one P _
  · intro v u
    rw [gluedCurvatureBoundedSmoothRiemannianMetric_inner]
    calc
      P.gluedCurvatureTangentInner b
          (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
            (⟨P.seamAngularComplexChart k θ,
              Or.inr ⟨k, θ, rfl⟩⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ b v)
          (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
            (⟨P.seamAngularComplexChart k θ,
              Or.inr ⟨k, θ, rfl⟩⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ b u) =
        v.re * u.re +
          gluingCurvatureBoundedWarp (gluingRadius C g) (gluingThinSeamWidth C g)
            P.thinSeamWidth_pos (P.seamAngularComplexChart k θ b).re ^ 2 * v.im * u.im :=
        P.gluedCurvatureTangentInner_in_isolated_seam_chart k θ b hb hother v u
      _ = gluingComplexCurvatureBoundedTangentForm (gluingRadius C g)
          (gluingThinSeamWidth C g) P.thinSeamWidth_pos
          (P.seamAngularComplexChart k θ b) v u := by
        rw [gluingComplexCurvatureBoundedTangentForm_apply]

/-- **Math.** On a native interior chart the patched metric is unchanged and its
literal coordinate Gaussian curvature is the original hyperbolic value. -/
theorem gluedCurvatureBoundedSmoothMetric_interior_chart
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : P.IsGluedInteriorComplexChart e) (b : P.GluedCarrier)
    (hb : b ∈ e.source)
    (hother : ∀ k : Fin (n - 1), b ∉ P.thinSeamCollar k) :
    hyperbolicGaussianCurvature ((e b).re, (e b).im) = -1 ∧
      ∀ v u : ℂ,
        (P.gluedCurvatureBoundedSmoothRiemannianMetric).inner b
          (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
            (⟨e, Or.inl he⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ b v)
          (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
            (⟨e, Or.inl he⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ b u) =
        gluingComplexHalfPlaneTangentForm (e b) v u := by
  constructor
  · exact hyperbolicGaussianCurvature_eq_neg_one
      (P.gluedInteriorComplexChart_target_im_pos e he (e.map_source hb))
  · intro v u
    rw [gluedCurvatureBoundedSmoothRiemannianMetric_inner,
      P.gluedCurvatureTangentInner_eq_native_of_outside_thinCollars b hother]
    rw [P.gluedTangentInner_in_chart e (Or.inl he) b hb v u,
      P.gluingChartTangentForm_interior e he]

/-- **Math.** Global chartwise curvature bound for the actual smooth patched metric.
Every point admits an atlas chart in which the genuine coordinate tensor
and its computed Gaussian curvature are given by one of the two explicit
models. In the seam case the model curvature is `≤ -1`; in the interior it
is exactly `-1`. -/
theorem gluedCurvatureBoundedSmoothRiemannianMetric_has_local_gaussian_le_neg_one
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier) :
    ∃ (e : OpenPartialHomeomorph P.GluedCarrier ℂ)
      (he : e ∈ P.gluedComplexAtlas), b ∈ e.source ∧
      ((∃ k : Fin (n - 1), ∃ θ : ℝ,
          e = P.seamAngularComplexChart k θ ∧
          gluedCurvatureBoundedSeamGaussian P (e b) ≤ -1 ∧
          (∀ v u : ℂ,
            (P.gluedCurvatureBoundedSmoothRiemannianMetric).inner b
              (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
                (⟨e, he⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ b v)
              (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
                (⟨e, he⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ b u) =
            gluingComplexCurvatureBoundedTangentForm (gluingRadius C g)
              (gluingThinSeamWidth C g) P.thinSeamWidth_pos (e b) v u) ∧
          ∀ᶠ c in 𝓝 b, c ∈ e.source ∧ ∀ v u : ℂ,
            (P.gluedCurvatureBoundedSmoothRiemannianMetric).inner c
              (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
                (⟨e, he⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ c v)
              (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
                (⟨e, he⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ c u) =
            gluingComplexCurvatureBoundedTangentForm (gluingRadius C g)
              (gluingThinSeamWidth C g) P.thinSeamWidth_pos (e c) v u) ∨
        (P.IsGluedInteriorComplexChart e ∧
          hyperbolicGaussianCurvature ((e b).re, (e b).im) = -1 ∧
          (∀ v u : ℂ,
            (P.gluedCurvatureBoundedSmoothRiemannianMetric).inner b
              (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
                (⟨e, he⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ b v)
              (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
                (⟨e, he⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ b u) =
            gluingComplexHalfPlaneTangentForm (e b) v u) ∧
          ∀ᶠ c in 𝓝 b, c ∈ e.source ∧ ∀ v u : ℂ,
            (P.gluedCurvatureBoundedSmoothRiemannianMetric).inner c
              (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
                (⟨e, he⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ c v)
              (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
                (⟨e, he⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ c u) =
            gluingComplexHalfPlaneTangentForm (e c) v u)) := by
  classical
  by_cases hc : ∃ k : Fin (n - 1), b ∈ P.closedThinSeamCollar k
  · obtain ⟨k, hk⟩ := hc
    have hnb := P.closedThinSeamCollar_subset_original_collar k hk
    let θ := P.seamSmoothingAngle k ⟨b, hnb⟩
    let e := P.seamAngularComplexChart k θ
    have hs : b ∈ e.source := P.mem_seamSmoothingAngle_chart k ⟨b, hnb⟩
    have he : e ∈ P.gluedComplexAtlas := Or.inr ⟨k, θ, rfl⟩
    have hother : ∀ l : Fin (n - 1), l ≠ k → b ∉ P.thinSeamCollar l := by
      intro l hl hthin
      exact (Set.disjoint_left.mp (P.closedThinSeamCollar_disjoint hl)
        (P.thinSeamCollar_subset_closedThinSeamCollar l hthin)) hk
    refine ⟨e, he, hs, Or.inl ⟨k, θ, rfl, ?_, ?_, ?_⟩⟩
    · exact (P.gluedCurvatureBoundedSmoothMetric_seam_chart k θ b hs hother).1
    · intro v u
      exact (P.gluedCurvatureBoundedSmoothMetric_seam_chart k θ b hs hother).2 v u
    · have hotherNear : ∀ᶠ c in 𝓝 b, ∀ l : Fin (n - 1),
          l ≠ k → c ∉ P.thinSeamCollar l := by
        rw [Filter.eventually_all]
        intro l
        by_cases hl : l = k
        · exact Filter.Eventually.of_forall (fun _ h => (h hl).elim)
        · have hn : b ∉ P.closedThinSeamCollar l := fun h =>
            Set.disjoint_left.mp (P.closedThinSeamCollar_disjoint hl) h hk
          filter_upwards
            [(P.closedThinSeamCollar_isCompact l).isClosed.isOpen_compl.mem_nhds hn]
            with c hc _ hthin
          exact hc (P.thinSeamCollar_subset_closedThinSeamCollar l hthin)
      filter_upwards [e.open_source.mem_nhds hs, hotherNear] with c hcs hco
      refine ⟨hcs, ?_⟩
      intro v u
      exact (P.gluedCurvatureBoundedSmoothMetric_seam_chart k θ c hcs hco).2 v u
  · have hn : ∀ k : Fin (n - 1), b ∉ P.closedThinSeamCollar k := by
      simpa only [not_exists] using hc
    obtain ⟨e, he, hs⟩ := P.exists_interior_chart_of_outside_closedThinSeamCollars b hn
    have hi : P.IsGluedInteriorComplexChart e := he
    have he' : e ∈ P.gluedComplexAtlas := Or.inl hi
    have hother : ∀ k : Fin (n - 1), b ∉ P.thinSeamCollar k := fun k hthin =>
      hn k (P.thinSeamCollar_subset_closedThinSeamCollar k hthin)
    refine ⟨e, he', hs, Or.inr ⟨hi, ?_, ?_, ?_⟩⟩
    · exact (P.gluedCurvatureBoundedSmoothMetric_interior_chart e hi b hs hother).1
    · intro v u
      exact (P.gluedCurvatureBoundedSmoothMetric_interior_chart e hi b hs hother).2 v u
    · have hotherNear : ∀ᶠ c in 𝓝 b, ∀ k : Fin (n - 1),
          c ∉ P.thinSeamCollar k := by
        rw [Filter.eventually_all]
        intro k
        filter_upwards
          [(P.closedThinSeamCollar_isCompact k).isClosed.isOpen_compl.mem_nhds (hn k)]
          with c hc hthin
        exact hc (P.thinSeamCollar_subset_closedThinSeamCollar k hthin)
      filter_upwards [e.open_source.mem_nhds hs, hotherNear] with c hcs hco
      refine ⟨hcs, ?_⟩
      intro v u
      exact (P.gluedCurvatureBoundedSmoothMetric_interior_chart e hi c hcs hco).2 v u

/-- **Math.** The chart actually selected by the glued carrier's `ChartedSpace`
structure is one of the concrete interior or seam charts. This classifies the
chart used by the intrinsic Levi-Civita curvature API. It does not itself
transfer the explicit seam-coordinate curvature formula: an interior chart
may overlap a smoothing collar, so that coordinate transfer remains to prove. -/
theorem gluedCurvatureBounded_chartAt_is_seam_or_interior
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier) :
    P.IsGluedInteriorComplexChart (chartAt ℂ b) ∨
      ∃ k : Fin (n - 1), ∃ θ : ℝ, chartAt ℂ b = P.seamAngularComplexChart k θ := by
  have h := chart_mem_atlas ℂ b
  change chartAt ℂ b ∈ P.gluedComplexAtlas at h
  simpa only [gluedComplexAtlas, Set.mem_setOf_eq] using h

/-- **Math.** On the closed smoothing strip, the canonical chart selected by
the actual glued-carrier `ChartedSpace` structure is the real-angular chart
of that same seam. The selector is arranged to prefer seam charts there;
disjointness of the closed strips identifies the chosen seam index. -/
theorem gluedCurvatureBounded_chartAt_eq_seam_of_mem_closedThinSeamCollar
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier)
    (k : Fin (n - 1)) (hb : b ∈ P.closedThinSeamCollar k) :
    ∃ θ : ℝ, chartAt ℂ b = P.seamAngularComplexChart k θ := by
  have hbranch := (P.exists_gluedComplexAtlas_chart_for_curvature b).choose_spec.2.2
  change
    (∃ l : Fin (n - 1), ∃ θ : ℝ,
      b ∈ P.closedThinSeamCollar l ∧
        chartAt ℂ b = P.seamAngularComplexChart l θ) ∨
      ∀ l : Fin (n - 1), b ∉ P.closedThinSeamCollar l at hbranch
  rcases hbranch with ⟨l, θ, hl, he⟩ | hnone
  · have hkl : l = k := by
      by_contra hne
      exact Set.disjoint_left.mp (P.closedThinSeamCollar_disjoint hne) hl hb
    subst l
    exact ⟨θ, he⟩
  · exact (hnone k hb).elim

/-- **Math.** Literal coordinate matrix of the ODE-patched metric in a real
radial/angular seam chart. -/
def gluedCurvatureBoundedSeamCoordinateMetric
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (θ : ℝ) (p : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let q := (P.seamAngularComplexChart k θ).symm (Complex.equivRealProdCLM.symm p)
  let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
  let i : atlas ℂ P.GluedCarrier :=
    ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩
  fun a b => (P.gluedCurvatureBoundedSmoothRiemannianMetric).inner q
    ((Z.localTriv i).symmL ℝ q (if a = 0 then 1 else Complex.I))
    ((Z.localTriv i).symmL ℝ q (if b = 0 then 1 else Complex.I))

/-- **Math.** On the ODE seam strip, the actual patched coordinate matrix is
the warped metric matrix used in the curvature calculation. -/
theorem gluedCurvatureBoundedSeamCoordinateMetric_eq_warped
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {p : ℝ × ℝ}
    (hp : Complex.equivRealProdCLM.symm p ∈ (P.seamAngularComplexChart k θ).target)
    (hthin : (P.seamAngularComplexChart k θ).symm
      (Complex.equivRealProdCLM.symm p) ∈ P.thinSeamCollar k) :
    P.gluedCurvatureBoundedSeamCoordinateMetric k θ p =
      gluingWarpedMetric
        (gluingCurvatureBoundedWarp (gluingRadius C g) (gluingThinSeamWidth C g)
          P.thinSeamWidth_pos) p := by
  ext a b
  dsimp only [gluedCurvatureBoundedSeamCoordinateMetric]
  let q := (P.seamAngularComplexChart k θ).symm (Complex.equivRealProdCLM.symm p)
  have hother : ∀ l : Fin (n - 1), l ≠ k → q ∉ P.thinSeamCollar l := by
    intro l hl hq
    exact disjoint_left.mp (P.closedThinSeamCollar_disjoint hl)
      (P.thinSeamCollar_subset_closedThinSeamCollar l hq)
      (P.thinSeamCollar_subset_closedThinSeamCollar k hthin)
  have hb : q ∈ (P.seamAngularComplexChart k θ).source :=
    (P.seamAngularComplexChart k θ).map_target hp
  rw [gluedCurvatureBoundedSmoothRiemannianMetric_inner,
    P.gluedCurvatureTangentInner_in_isolated_seam_chart k θ q hb hother,
    (P.seamAngularComplexChart k θ).right_inv hp]
  fin_cases a <;> fin_cases b <;> simp [gluingWarpedMetric]

/-- **Math.** The seam-coordinate matrix has the same ODE warp throughout
any part of the seam chart isolated from other thin strips. -/
theorem gluedCurvatureBoundedSeamCoordinateMetric_eq_warped_of_other
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {p : ℝ × ℝ}
    (hp : Complex.equivRealProdCLM.symm p ∈ (P.seamAngularComplexChart k θ).target)
    (hother : ∀ l : Fin (n - 1), l ≠ k →
      (P.seamAngularComplexChart k θ).symm
        (Complex.equivRealProdCLM.symm p) ∉ P.thinSeamCollar l) :
    P.gluedCurvatureBoundedSeamCoordinateMetric k θ p =
      gluingWarpedMetric
        (gluingCurvatureBoundedWarp (gluingRadius C g) (gluingThinSeamWidth C g)
          P.thinSeamWidth_pos) p := by
  ext a b
  dsimp only [gluedCurvatureBoundedSeamCoordinateMetric]
  let q := (P.seamAngularComplexChart k θ).symm (Complex.equivRealProdCLM.symm p)
  have hb : q ∈ (P.seamAngularComplexChart k θ).source :=
    (P.seamAngularComplexChart k θ).map_target hp
  rw [gluedCurvatureBoundedSmoothRiemannianMetric_inner,
    P.gluedCurvatureTangentInner_in_isolated_seam_chart k θ q hb hother,
    (P.seamAngularComplexChart k θ).right_inv hp]
  fin_cases a <;> fin_cases b <;> simp [gluingWarpedMetric]

/-- **Math.** Actual coordinates of the ODE-patched metric in a native
interior chart. -/
def gluedCurvatureBoundedInteriorCoordinateMetric
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : P.IsGluedInteriorComplexChart e) (p : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let q := e.symm (Complex.equivRealProdCLM.symm p)
  let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
  let i : atlas ℂ P.GluedCarrier := ⟨e, Or.inl he⟩
  fun a b => (P.gluedCurvatureBoundedSmoothRiemannianMetric).inner q
    ((Z.localTriv i).symmL ℝ q (if a = 0 then 1 else Complex.I))
    ((Z.localTriv i).symmL ℝ q (if b = 0 then 1 else Complex.I))

/-- **Math.** Wherever a native interior chart avoids the ODE strips, the
actual coordinate metric is precisely the original Poincaré metric. -/
theorem gluedCurvatureBoundedInteriorCoordinateMetric_eq_hyperbolic
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : P.IsGluedInteriorComplexChart e) {p : ℝ × ℝ}
    (hp : Complex.equivRealProdCLM.symm p ∈ e.target)
    (houtside : ∀ k : Fin (n - 1),
      e.symm (Complex.equivRealProdCLM.symm p) ∉ P.thinSeamCollar k) :
    P.gluedCurvatureBoundedInteriorCoordinateMetric e he p =
      hyperbolicGaussianMetric p := by
  ext a b
  dsimp only [gluedCurvatureBoundedInteriorCoordinateMetric]
  rw [gluedCurvatureBoundedSmoothRiemannianMetric_inner,
    P.gluedCurvatureTangentInner_eq_native_of_outside_thinCollars _ houtside,
    P.gluedTangentInner_in_chart e (Or.inl he) _ (e.map_target hp),
    P.gluingChartTangentForm_interior e he, e.right_inv hp]
  fin_cases a <;> fin_cases b <;>
    simp [hyperbolicGaussianMetric, gluingComplexHalfPlaneTangentForm_apply, div_eq_mul_inv]

/-- **Math.** The determinant of the actual ODE-patched metric on every thin
seam chart is the ODE warp, hence its square root is the area density. -/
theorem gluedCurvatureBoundedSeamCoordinateMetric_areaDensity
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {p : ℝ × ℝ}
    (hp : Complex.equivRealProdCLM.symm p ∈ (P.seamAngularComplexChart k θ).target)
    (hthin : (P.seamAngularComplexChart k θ).symm
      (Complex.equivRealProdCLM.symm p) ∈ P.thinSeamCollar k) :
    Real.sqrt (P.gluedCurvatureBoundedSeamCoordinateMetric k θ p).det =
      gluingCurvatureBoundedWarp (gluingRadius C g) (gluingThinSeamWidth C g)
        P.thinSeamWidth_pos p.1 := by
  rw [P.gluedCurvatureBoundedSeamCoordinateMetric_eq_warped k θ hp hthin]
  exact gluingWarpedMetric_areaDensity
    (gluingCurvatureBoundedWarp_pos P.radius_pos P.thinSeamWidth_pos p.1)

/-- **Math.** The global ODE area measure pulls back through every literal
thin-seam angular chart to the radial/angular warped determinant density. -/
theorem gluedCurvatureBoundedAreaMeasure_comap_thinSeamAngularPoint
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) :
    P.gluedCurvatureBoundedAreaMeasure.comap (P.thinSeamAngularPoint k θ) =
      ((volume : Measure ℂ).withDensity (fun z => ENNReal.ofReal
        (gluingCurvatureBoundedWarp (gluingRadius C g) (gluingThinSeamWidth C g)
          P.thinSeamWidth_pos z.re))).comap
        (gluingThinSeamAngularModel (gluingThinSeamWidth C g) θ) := by
  have hangular := gluingThinAngularCylinderMap_measurableEmbedding
    (gluingThinSeamWidth C g) θ
  have hcylinder := P.thinSeamCylinderMap_measurableEmbedding k
  have hcomp : P.thinSeamAngularPoint k θ =
      P.thinSeamCylinderMap k ∘
        gluingThinAngularCylinderMap (gluingThinSeamWidth C g) θ := rfl
  rw [hcomp, ← Measure.comap_comap hangular.measurableSet_image' hcylinder.injective
    hcylinder.measurableSet_image',
    P.gluedCurvatureBoundedAreaMeasure_comap_thinSeamCylinderMap k,
    gluedCurvatureBoundedThinCylinderArea_comap_angular,
    gluingMeasure_comap_withDensity
      (gluingThinSeamAngularModel_measurableEmbedding
        (gluingThinSeamWidth C g) θ),
    gluingThinSeamAngularModel_comap_volume]
  rfl

/-- **Math.** On each genuine thin angular chart the transported ODE area is
exactly the determinant area of the actual patched metric tensor. -/
theorem gluedCurvatureBoundedAreaMeasure_comap_thinSeamAngularPoint_eq_metricArea
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) :
    P.gluedCurvatureBoundedAreaMeasure.comap (P.thinSeamAngularPoint k θ) =
      ((volume : Measure ℂ).withDensity (fun z => ENNReal.ofReal
        (Real.sqrt (P.gluedCurvatureBoundedSeamCoordinateMetric k θ
          (z.re, z.im)).det))).comap
        (gluingThinSeamAngularModel (gluingThinSeamWidth C g) θ) := by
  rw [P.gluedCurvatureBoundedAreaMeasure_comap_thinSeamAngularPoint k θ,
    gluingMeasure_comap_withDensity
      (gluingThinSeamAngularModel_measurableEmbedding
        (gluingThinSeamWidth C g) θ),
    gluingMeasure_comap_withDensity
      (gluingThinSeamAngularModel_measurableEmbedding
        (gluingThinSeamWidth C g) θ)]
  congr 1
  funext p
  dsimp only [Function.comp_apply, gluingThinSeamAngularModel]
  change ENNReal.ofReal
      (gluingCurvatureBoundedWarp (gluingRadius C g) (gluingThinSeamWidth C g)
        P.thinSeamWidth_pos p.1.1) =
    ENNReal.ofReal (Real.sqrt
      (P.gluedCurvatureBoundedSeamCoordinateMetric k θ
        (p.1.1, p.2.1)).det)
  have hp := P.gluingThinSeamAngularModel_mem_chart_target k θ p
  have hthin : (P.seamAngularComplexChart k θ).symm
      (Complex.equivRealProdCLM.symm (p.1.1, p.2.1)) ∈ P.thinSeamCollar k := by
    change (P.seamAngularComplexChart k θ).symm
      (gluingThinSeamAngularModel (gluingThinSeamWidth C g) θ p) ∈
        P.thinSeamCollar k
    rw [← P.thinSeamAngularPoint_eq_chart_symm k θ p]
    exact P.thinSeamAngularPoint_mem_thinCollar k θ p
  rw [← P.gluedCurvatureBoundedSeamCoordinateMetric_areaDensity k θ hp hthin]

/-- **Math.** Any measurable set contained in the thin angular chart has the
integral of the actual ODE-patched metric's determinant density. -/
theorem gluedCurvatureBoundedAreaMeasure_thin_seam_chart_image
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {s : Set ℂ} (hs : MeasurableSet s)
    (hsub : s ⊆ range (gluingThinSeamAngularModel
      (gluingThinSeamWidth C g) θ)) :
    P.gluedCurvatureBoundedAreaMeasure ((P.seamAngularComplexChart k θ).symm '' s) =
      ∫⁻ z : ℂ in s, ENNReal.ofReal
        (Real.sqrt (P.gluedCurvatureBoundedSeamCoordinateMetric k θ
          (z.re, z.im)).det) := by
  let f := gluingThinSeamAngularModel (gluingThinSeamWidth C g) θ
  let t := f ⁻¹' s
  have himage : f '' t = s := image_preimage_eq_of_subset hsub
  have hpoint : P.thinSeamAngularPoint k θ '' t =
      (P.seamAngularComplexChart k θ).symm '' s := by
    rw [← himage, ← image_comp]
    congr 1
    funext p
    exact P.thinSeamAngularPoint_eq_chart_symm k θ p
  have h := congrArg (fun μ : Measure
      (Ioo (-gluingThinSeamWidth C g) (gluingThinSeamWidth C g) ×
        GluingAngularInterval θ) => μ t)
    (P.gluedCurvatureBoundedAreaMeasure_comap_thinSeamAngularPoint_eq_metricArea k θ)
  rw [(P.thinSeamAngularPoint_measurableEmbedding k θ).comap_apply,
    (gluingThinSeamAngularModel_measurableEmbedding
      (gluingThinSeamWidth C g) θ).comap_apply, hpoint, himage,
    withDensity_apply _ hs] at h
  exact h

/-- **Math.** In an isolated seam-chart subset outside every thin ODE strip,
the global area measure is the determinant area of the actual metric. -/
theorem gluedCurvatureBoundedAreaMeasure_isolated_seam_chart_exterior_image
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {s : Set ℂ} (hs : MeasurableSet s)
    (ht : s ⊆ (P.seamAngularComplexChart k θ).target)
    (houtside : ∀ z ∈ s, ∀ l : Fin (n - 1),
      (P.seamAngularComplexChart k θ).symm z ∉ P.thinSeamCollar l) :
    P.gluedCurvatureBoundedAreaMeasure
        ((P.seamAngularComplexChart k θ).symm '' s) =
      ∫⁻ z : ℂ in s, ENNReal.ofReal
        (Real.sqrt (P.gluedCurvatureBoundedSeamCoordinateMetric k θ
          (z.re, z.im)).det) := by
  let e := P.seamAngularComplexChart k θ
  have hmeas : MeasurableSet (e.symm '' s) :=
    hs.image_of_continuousOn_injOn (e.symm.continuousOn.mono ht)
      (e.symm.injOn.mono ht)
  have hsub : e.symm '' s ⊆ (⋃ l : Fin (n - 1), P.thinSeamCollar l)ᶜ := by
    rintro q ⟨z, hz, rfl⟩ hq
    rcases mem_iUnion.mp hq with ⟨l, hl⟩
    exact houtside z hz l hl
  have h := congrArg (fun μ : Measure P.GluedCarrier => μ (e.symm '' s))
    (P.gluedCurvatureBoundedAreaMeasure_restrict_outside_thinCollars)
  rw [Measure.restrict_apply hmeas, inter_eq_left.mpr hsub] at h
  have hbase : P.gluedChainSmoothOutsideArea (e.symm '' s) =
      P.gluedChainAreaMeasure (e.symm '' s) := by
    rw [gluedChainSmoothOutsideArea, Measure.restrict_apply hmeas,
      inter_eq_left.mpr hsub]
  have hmeasure : P.gluedCurvatureBoundedAreaMeasure (e.symm '' s) =
      P.gluedChainAreaMeasure (e.symm '' s) := by
    exact h.trans hbase
  rw [hmeasure, P.gluedChainAreaMeasure_seamAngularComplexChart_image k θ hs ht,
    withDensity_apply _ hs]
  apply setLIntegral_congr_fun hs
  intro z hz
  change ENNReal.ofReal (gluingCollarWarp (gluingRadius C g) z.re) =
    ENNReal.ofReal (Real.sqrt
      (P.gluedCurvatureBoundedSeamCoordinateMetric k θ (z.re, z.im)).det)
  have hcoord : Complex.equivRealProdCLM.symm (z.re, z.im) = z :=
    Complex.ext rfl rfl
  have hp : Complex.equivRealProdCLM.symm (z.re, z.im) ∈ e.target := by
    simpa only [hcoord] using ht hz
  have hother : ∀ l : Fin (n - 1), l ≠ k →
      e.symm (Complex.equivRealProdCLM.symm (z.re, z.im)) ∉ P.thinSeamCollar l := by
    intro l hl
    simpa only [hcoord] using houtside z hz l
  have hrad : gluingThinSeamWidth C g ≤ |z.re| := by
    have hnot :=
      (P.seamAngularComplexChart_symm_mem_thinSeamCollar_iff k θ (ht hz)).not.mp
        (houtside z hz k)
    exact le_of_not_gt hnot
  rw [P.gluedCurvatureBoundedSeamCoordinateMetric_eq_warped_of_other k θ hp
      (by simpa only [hcoord] using hother),
    gluingWarpedMetric_areaDensity
      (gluingCurvatureBoundedWarp_pos P.radius_pos P.thinSeamWidth_pos z.re),
    gluingCurvatureBoundedWarp_eq_native_of_abs_ge_strip (gluingRadius C g)
      (gluingThinSeamWidth C g) P.thinSeamWidth_pos hrad]

/-- **Math.** On every native interior-chart subset outside the ODE strips,
global area is the determinant area of the actual patched metric. -/
theorem gluedCurvatureBoundedAreaMeasure_exteriorInteriorComplexChart_image
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : P.IsGluedInteriorComplexChart e)
    {s : Set ℂ} (hs : MeasurableSet s) (ht : s ⊆ e.target)
    (houtside : ∀ z ∈ s, ∀ k : Fin (n - 1), e.symm z ∉ P.thinSeamCollar k) :
    P.gluedCurvatureBoundedAreaMeasure (e.symm '' s) =
      ∫⁻ z : ℂ in s, ENNReal.ofReal
        (Real.sqrt (P.gluedCurvatureBoundedInteriorCoordinateMetric e he
          (z.re, z.im)).det) := by
  have hmeas : MeasurableSet (e.symm '' s) :=
    hs.image_of_continuousOn_injOn (e.symm.continuousOn.mono ht)
      (e.symm.injOn.mono ht)
  have hsub : e.symm '' s ⊆ (⋃ k : Fin (n - 1), P.thinSeamCollar k)ᶜ := by
    rintro q ⟨z, hz, rfl⟩ hq
    rcases mem_iUnion.mp hq with ⟨k, hk⟩
    exact houtside z hz k hk
  have h := congrArg (fun μ : Measure P.GluedCarrier => μ (e.symm '' s))
    (P.gluedCurvatureBoundedAreaMeasure_restrict_outside_thinCollars)
  rw [Measure.restrict_apply hmeas, inter_eq_left.mpr hsub] at h
  have hbase : P.gluedChainSmoothOutsideArea (e.symm '' s) =
      P.gluedChainAreaMeasure (e.symm '' s) := by
    rw [gluedChainSmoothOutsideArea, Measure.restrict_apply hmeas,
      inter_eq_left.mpr hsub]
  rw [h.trans hbase, P.gluedChainAreaMeasure_interiorComplexChart_image e he hs ht]
  apply setLIntegral_congr_fun hs
  intro z hz
  change ENNReal.ofReal ((z.im ^ 2)⁻¹) = ENNReal.ofReal
    (Real.sqrt (P.gluedCurvatureBoundedInteriorCoordinateMetric e he
      (z.re, z.im)).det)
  have hcoord : Complex.equivRealProdCLM.symm (z.re, z.im) = z :=
    Complex.ext rfl rfl
  have hp : Complex.equivRealProdCLM.symm (z.re, z.im) ∈ e.target := by
    simpa only [hcoord] using ht hz
  have houtside' : ∀ k : Fin (n - 1),
      e.symm (Complex.equivRealProdCLM.symm (z.re, z.im)) ∉ P.thinSeamCollar k := by
    intro k
    simpa only [hcoord] using houtside z hz k
  rw [P.gluedCurvatureBoundedInteriorCoordinateMetric_eq_hyperbolic e he hp
      houtside', hyperbolicGaussianMetric_areaDensity]

/-- **Math.** Every measurable subset of a seam angular chart isolated from
other strips has the determinant area of the actual patched metric. -/
theorem gluedCurvatureBoundedAreaMeasure_isolated_seam_chart_image
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {s : Set ℂ} (hs : MeasurableSet s)
    (ht : s ⊆ (P.seamAngularComplexChart k θ).target)
    (hother : ∀ z ∈ s, ∀ l : Fin (n - 1), l ≠ k →
      (P.seamAngularComplexChart k θ).symm z ∉ P.thinSeamCollar l) :
    P.gluedCurvatureBoundedAreaMeasure
        ((P.seamAngularComplexChart k θ).symm '' s) =
      ∫⁻ z : ℂ in s, ENNReal.ofReal
        (Real.sqrt (P.gluedCurvatureBoundedSeamCoordinateMetric k θ
          (z.re, z.im)).det) := by
  let e := P.seamAngularComplexChart k θ
  let A : Set ℂ := {z | |z.re| < gluingThinSeamWidth C g}
  let si := s ∩ A
  let so := s \ A
  have hA : MeasurableSet A :=
    (isOpen_lt Complex.continuous_re.abs continuous_const).measurableSet
  have hi : MeasurableSet si := hs.inter hA
  have ho : MeasurableSet so := hs.diff hA
  have his : si ⊆ s := inter_subset_left
  have hos : so ⊆ s := sdiff_subset
  have hdisj : Disjoint si so := by
    exact disjoint_left.mpr fun z hz hw => hw.2 hz.2
  have hunion : si ∪ so = s := inter_union_sdiff s A
  have himagedisj : Disjoint (e.symm '' si) (e.symm '' so) := by
    apply Set.disjoint_image_image
    intro z hz w hw heq
    have hzw := e.symm.injOn (ht (his hz)) (ht (hos hw)) heq
    exact disjoint_left.mp hdisj hz (hzw ▸ hw)
  have hmeaso : MeasurableSet (e.symm '' so) :=
    P.seamAngularComplexChart_symm_image_measurable k θ ho (hos.trans ht)
  have hinsub : si ⊆ range (gluingThinSeamAngularModel
      (gluingThinSeamWidth C g) θ) := by
    intro z hz
    rw [gluingThinSeamAngularModel_range]
    exact ⟨abs_lt.mp hz.2,
      ((P.mem_seamAngularComplexChart_target k θ z).mp (ht hz.1)).2⟩
  have hin := P.gluedCurvatureBoundedAreaMeasure_thin_seam_chart_image
    k θ hi hinsub
  have hout := P.gluedCurvatureBoundedAreaMeasure_isolated_seam_chart_exterior_image
    k θ ho (hos.trans ht) (by
      intro z hz l
      by_cases hl : l = k
      · subst l
        exact (P.seamAngularComplexChart_symm_mem_thinSeamCollar_iff k θ
          (ht hz.1)).not.mpr hz.2
      · exact hother z hz.1 l hl)
  rw [← hunion, image_union, measure_union himagedisj hmeaso,
    lintegral_union ho hdisj, hin, hout]

/-- **Math.** Every point has a neighborhood in a genuine atlas chart on
which one of the proved area-density chart formulas applies: an isolated seam
chart near a closed seam strip, or an unchanged interior chart elsewhere. -/
theorem exists_local_gluedCurvatureBoundedArea_chart
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedCarrier) :
    ∃ (e : OpenPartialHomeomorph P.GluedCarrier ℂ)
      (_he : e ∈ P.gluedComplexAtlas) (W : Set P.GluedCarrier),
      q ∈ W ∧ IsOpen W ∧ W ⊆ e.source ∧
        ((∃ k : Fin (n - 1), ∃ θ : ℝ,
          e = P.seamAngularComplexChart k θ ∧
          ∀ c ∈ W, ∀ l : Fin (n - 1), l ≠ k → c ∉ P.thinSeamCollar l) ∨
        (P.IsGluedInteriorComplexChart e ∧
          ∀ c ∈ W, ∀ k : Fin (n - 1), c ∉ P.thinSeamCollar k)) := by
  classical
  by_cases hclosed : ∃ k : Fin (n - 1), q ∈ P.closedThinSeamCollar k
  · obtain ⟨k, hq⟩ := hclosed
    have hnotother : ∀ l : Fin (n - 1), l ≠ k →
        q ∉ P.closedThinSeamCollar l := by
      intro l hl hlq
      exact disjoint_left.mp (P.closedThinSeamCollar_disjoint hl) hlq hq
    have hqcollar := P.closedThinSeamCollar_subset_original_collar k hq
    let θ := P.seamSmoothingAngle k ⟨q, hqcollar⟩
    let e := P.seamAngularComplexChart k θ
    have hsource : q ∈ e.source := P.mem_seamSmoothingAngle_chart k ⟨q, hqcollar⟩
    have he : e ∈ P.gluedComplexAtlas := Or.inr ⟨k, θ, rfl⟩
    let V : Set P.GluedCarrier := ⋃ l : Fin (n - 1),
      if l = k then ∅ else P.closedThinSeamCollar l
    have hV : IsClosed V := by
      apply isClosed_iUnion_of_finite
      intro l
      by_cases hl : l = k
      · subst l
        simp
      · simpa only [if_neg hl] using
          (P.closedThinSeamCollar_isCompact l).isClosed
    have hqV : q ∉ V := by
      intro hqV
      rcases mem_iUnion.mp hqV with ⟨l, hlV⟩
      by_cases hl : l = k
      · simp [hl] at hlV
      · exact hnotother l hl (by simpa only [if_neg hl] using hlV)
    let W : Set P.GluedCarrier := e.source ∩ Vᶜ
    have hqW : q ∈ W := ⟨hsource, hqV⟩
    have hWopen : IsOpen W := e.open_source.inter hV.isOpen_compl
    refine ⟨e, he, W, hqW, hWopen, inter_subset_left,
      Or.inl ⟨k, θ, rfl, ?_⟩⟩
    intro c hc l hl hthin
    apply hc.2
    apply mem_iUnion.mpr
    refine ⟨l, ?_⟩
    simp only [if_neg hl]
    exact P.thinSeamCollar_subset_closedThinSeamCollar l hthin
  · have hnotclosed : ∀ k : Fin (n - 1), q ∉ P.closedThinSeamCollar k := by
      simpa only [not_exists] using hclosed
    obtain ⟨e, he, hsource⟩ :=
      P.exists_interior_chart_of_outside_closedThinSeamCollars q hnotclosed
    have he' : e ∈ P.gluedComplexAtlas := Or.inl he
    let V : Set P.GluedCarrier := ⋃ k : Fin (n - 1), P.closedThinSeamCollar k
    have hV : IsClosed V := by
      apply isClosed_iUnion_of_finite
      intro k
      exact (P.closedThinSeamCollar_isCompact k).isClosed
    have hqV : q ∉ V := by
      intro hqV
      rcases mem_iUnion.mp hqV with ⟨k, hk⟩
      exact hnotclosed k hk
    let W : Set P.GluedCarrier := e.source ∩ Vᶜ
    have hqW : q ∈ W := ⟨hsource, hqV⟩
    have hWopen : IsOpen W := e.open_source.inter hV.isOpen_compl
    refine ⟨e, he', W, hqW, hWopen, inter_subset_left, Or.inr ⟨he, ?_⟩⟩
    intro c hc k hthin
    apply hc.2
    exact mem_iUnion.mpr ⟨k, P.thinSeamCollar_subset_closedThinSeamCollar k hthin⟩

#print axioms gluedCurvatureBoundedSeamGaussian_le_neg_one
#print axioms gluedCurvatureBoundedThinCylinderCurvatureDensity_integrable
#print axioms gluedCurvatureBoundedThinCylinderCurvatureDensity_eq_gaussian_mul_area
#print axioms gluedCurvatureBoundedThinCylinderGaussian_continuous
#print axioms gluedCurvatureBoundedThinCylinderGaussian_integrable_area
#print axioms gluedCurvatureBoundedThinCylinderCurvature_eq_area_withDensity_gaussian
#print axioms gluedCurvatureBoundedThinCylinderCurvature_univ
#print axioms gluedCurvatureBoundedSeamCurvature_univ
#print axioms gluedCurvatureBoundedGaussian_le_neg_one
#print axioms gluedCurvatureBoundedCurvature_eq_area_withDensity_gaussian
#print axioms gluedCurvatureBoundedCurvature_univ
#print axioms gluedCurvatureBoundedGaussian_integral
#print axioms gluedCurvatureBoundedAreaMeasure_real_univ_le
#print axioms gluingComplexCurvatureBoundedTangentForm_eq_warpedMetricForm
#print axioms gluedCurvatureBoundedSmoothMetric_seam_chart
#print axioms gluedCurvatureBoundedSmoothMetric_interior_chart
#print axioms gluedCurvatureBoundedSmoothRiemannianMetric_has_local_gaussian_le_neg_one
#print axioms gluedCurvatureBounded_chartAt_is_seam_or_interior
#print axioms gluedCurvatureBounded_chartAt_eq_seam_of_mem_closedThinSeamCollar
#print axioms gluedCurvatureBoundedAreaMeasure_restrict_outside_thinCollars
#print axioms gluedCurvatureBoundedAreaMeasure_comap_thinSeamAngularPoint_eq_metricArea
#print axioms gluedCurvatureBoundedAreaMeasure_thin_seam_chart_image
#print axioms gluedCurvatureBoundedAreaMeasure_isolated_seam_chart_exterior_image
#print axioms gluedCurvatureBoundedAreaMeasure_isolated_seam_chart_image
#print axioms gluedCurvatureBoundedInteriorCoordinateMetric_eq_hyperbolic
#print axioms gluedCurvatureBoundedAreaMeasure_exteriorInteriorComplexChart_image
#print axioms gluedCurvatureBoundedSeamCoordinateMetric_eq_warped_of_other
#print axioms exists_local_gluedCurvatureBoundedArea_chart

end
end SystolicGrowth.ExerciseGluingPreparation
