module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainCurvatureRadon
public import Geometry.GluingDisjointThinSeamCollars
public import Geometry.GluingCollarLocalizedCurvatureProduct
public import Geometry.GluingWarpedGaussianCurvature
public import Geometry.GluingChainSmoothMetric
public import Geometry.HyperbolicGaussianCurvature
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

@[expose] public section

/-!
# Genuine global curvature measures of localized native smooth metrics

The signed localized curvature density is transported from genuine native
thin cylinders. Their angular measure is the actual one-turn Lebesgue
arclength on `Circle`, and their radial measure is original Lebesgue measure.
Outside the disjoint thin strips the curvature remains negative native area.
-/

open Set Filter MeasureTheory
open scoped ENNReal BigOperators Manifold

namespace SystolicGrowth

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

/-- Jordan total variation agrees with the actual norm-partition variation.
This permits genuine map and finite-sum estimates for signed curvature. -/
theorem signedMeasure_totalVariation_eq_variation {α : Type*} [MeasurableSpace α]
    (s : SignedMeasure α) : s.totalVariation = s.variation := by
  let j := s.toJordanDecomposition
  have hsj : j.toSignedMeasure = s := SignedMeasure.toSignedMeasure_toJordanDecomposition s
  apply le_antisymm
  · obtain ⟨A, hA, _, _, hp, hn⟩ := j.exists_compl_positive_negative
    apply Measure.le_iff.mpr
    intro E hE
    have hpos : ‖s (E ∩ Aᶜ)‖ₑ = j.posPart (E ∩ Aᶜ) := by
      rw [← hsj, JordanDecomposition.toSignedMeasure,
        Measure.toSignedMeasure_sub_apply (hE.inter hA.compl)]
      have hz : j.negPart (E ∩ Aᶜ) = 0 := measure_mono_null inter_subset_right hn
      simp [measureReal_def, hz, Real.enorm_eq_ofReal]
    have hneg : ‖s (E ∩ A)‖ₑ = j.negPart (E ∩ A) := by
      rw [← hsj, JordanDecomposition.toSignedMeasure,
        Measure.toSignedMeasure_sub_apply (hE.inter hA)]
      have hz : j.posPart (E ∩ A) = 0 := measure_mono_null inter_subset_right hp
      simp [measureReal_def, hz, Real.enorm_eq_ofReal]
    have hposE : j.posPart E = j.posPart (E ∩ Aᶜ) := by
      rw [← inter_union_compl E A, measure_union]
      · simp [measure_mono_null (inter_subset_right : E ∩ A ⊆ A) hp]
      · exact disjoint_left.mpr fun _ h₁ h₂ => h₂.2 h₁.2
      · exact hE.inter hA.compl
    have hnegE : j.negPart E = j.negPart (E ∩ A) := by
      rw [← inter_union_compl E A, measure_union]
      · simp [measure_mono_null (inter_subset_right : E ∩ Aᶜ ⊆ Aᶜ) hn]
      · exact disjoint_left.mpr fun _ h₁ h₂ => h₂.2 h₁.2
      · exact hE.inter hA.compl
    change j.posPart E + j.negPart E ≤ _
    rw [hposE, hnegE, ← hpos, ← hneg]
    calc
      _ ≤ s.variation (E ∩ Aᶜ) + s.variation (E ∩ A) :=
        add_le_add (VectorMeasure.enorm_measure_le_variation _ _)
          (VectorMeasure.enorm_measure_le_variation _ _)
      _ = s.variation E := by
        rw [← measure_union]
        · congr 1
          simpa using inter_union_compl E Aᶜ
        · exact disjoint_left.mpr fun _ h₁ h₂ => h₁.2 h₂.2
        · exact hE.inter hA
  · change s.variation ≤ j.posPart + j.negPart
    rw [← hsj, JordanDecomposition.toSignedMeasure, sub_eq_add_neg]
    simpa [VectorMeasure.variation_neg,
      Measure.variation_toSignedMeasure] using
      (VectorMeasure.variation_add_le (μ := j.posPart.toSignedMeasure)
        (ν := -j.negPart.toSignedMeasure))

/-- Actual angular arclength: original real Lebesgue measure on one
positive turn, pushed through the genuine circle exponential. -/
def gluingCircleAngularLengthMeasure : Measure Circle :=
  Measure.map Circle.exp (volume.restrict (Ioc 0 (2 * Real.pi)))

instance gluingCircleAngularLengthMeasure_isFinite :
    IsFiniteMeasure gluingCircleAngularLengthMeasure := by
  unfold gluingCircleAngularLengthMeasure
  infer_instance

theorem gluingCircleAngularLengthMeasure_univ :
    gluingCircleAngularLengthMeasure univ = ENNReal.ofReal (2 * Real.pi) := by
  rw [gluingCircleAngularLengthMeasure, Measure.map_apply Circle.exp.continuous.measurable
    MeasurableSet.univ]
  simp

/-- Original radial Lebesgue measure on a genuine open thin interval. -/
def gluingThinRadialMeasure (δ : ℝ) : Measure (Ioo (-δ) δ) :=
  (volume : Measure ℝ).comap Subtype.val

instance gluingThinRadialMeasure_isFinite (δ : ℝ) :
    IsFiniteMeasure (gluingThinRadialMeasure δ) where
  measure_univ_lt_top := by
    rw [gluingThinRadialMeasure, comap_subtype_coe_apply measurableSet_Ioo]
    rw [Set.image_univ, Subtype.range_val]
    rw [Real.volume_Ioo]
    finiteness

/-- Genuine product of circle arclength and original radial Lebesgue measure. -/
def gluingThinCylinderCoordinateMeasure (δ : ℝ) : Measure (Circle × Ioo (-δ) δ) :=
  gluingCircleAngularLengthMeasure.prod (gluingThinRadialMeasure δ)

instance gluingThinCylinderCoordinateMeasure_isFinite (δ : ℝ) :
    IsFiniteMeasure (gluingThinCylinderCoordinateMeasure δ) := by
  unfold gluingThinCylinderCoordinateMeasure
  infer_instance

def gluingThinCylinderCurvatureDensity (r ε : ℝ) (b : ContDiffBump (0 : ℝ))
    {δ : ℝ} (p : Circle × Ioo (-δ) δ) : ℝ :=
  -deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) p.2.1

theorem gluingThinCylinderCurvatureDensity_continuous (r : ℝ)
    {ε : ℝ} (hε : 0 < ε) (b : ContDiffBump (0 : ℝ)) (δ : ℝ) :
    Continuous (gluingThinCylinderCurvatureDensity r ε b (δ := δ)) :=
  ((gluingCollarLocalizedSmoothWarp_contDiff r hε b 2).deriv'.continuous_deriv_one.comp
    (continuous_subtype_val.comp continuous_snd)).neg

theorem gluingThinCylinderCurvatureDensity_integrable (r : ℝ)
    {ε : ℝ} (hε : 0 < ε) (b : ContDiffBump (0 : ℝ)) (δ : ℝ) :
    Integrable (gluingThinCylinderCurvatureDensity r ε b)
      (gluingThinCylinderCoordinateMeasure δ) := by
  have hi : IntegrableOn
      (fun t : ℝ => -deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) t)
      (Icc (-δ) δ) :=
    ((gluingCollarLocalizedSmoothWarp_contDiff r hε b 2).deriv'.continuous_deriv_one.neg).continuousOn.integrableOn_compact
      isCompact_Icc
  have hs := (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mp
    (hi.mono_set Ioo_subset_Icc_self)
  change Integrable (fun t : Ioo (-δ) δ =>
    -deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) t.1) (gluingThinRadialMeasure δ) at hs
  exact hs.comp_snd gluingCircleAngularLengthMeasure

/-- The actual smooth signed curvature on a thin cylinder; neither sign
is imposed on the genuine localized second derivative. -/
def gluingThinCylinderCurvature (r ε : ℝ) (b : ContDiffBump (0 : ℝ)) (δ : ℝ) :
    SignedMeasure (Circle × Ioo (-δ) δ) :=
  (gluingThinCylinderCoordinateMeasure δ).withDensityᵥ
    (gluingThinCylinderCurvatureDensity r ε b)

theorem gluingThinCylinderCurvature_totalVariation (r : ℝ)
    {ε : ℝ} (hε : 0 < ε) (b : ContDiffBump (0 : ℝ)) (δ : ℝ) :
    (gluingThinCylinderCurvature r ε b δ).totalVariation =
      (gluingThinCylinderCoordinateMeasure δ).withDensity
        (fun p => ENNReal.ofReal
          |deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) p.2.1|) := by
  rw [gluingThinCylinderCurvature,
    signedMeasure_withDensity_totalVariation_of_integrable _
      (gluingThinCylinderCurvatureDensity_continuous r hε b δ).measurable
      (gluingThinCylinderCurvatureDensity_integrable r hε b δ)]
  congr 1
  funext p
  simp [gluingThinCylinderCurvatureDensity]

/-- Exact actual cylinder variation: radial absolute Gaussian density
times the actual circle arclength, with no artificial angular multiplicity. -/
theorem gluingThinCylinderCurvature_totalVariation_univ (r : ℝ)
    {ε : ℝ} (hε : 0 < ε) (b : ContDiffBump (0 : ℝ)) (δ : ℝ) :
    (gluingThinCylinderCurvature r ε b δ).totalVariation univ =
      ENNReal.ofReal (∫ t : ℝ in Icc (-δ) δ,
        |deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) t|) *
        ENNReal.ofReal (2 * Real.pi) := by
  have hI : Integrable
      (fun p : Circle × Ioo (-δ) δ =>
        |deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) p.2.1|)
      (gluingThinCylinderCoordinateMeasure δ) := by
    simpa [gluingThinCylinderCurvatureDensity] using
      (gluingThinCylinderCurvatureDensity_integrable r hε b δ).abs
  rw [gluingThinCylinderCurvature_totalVariation r hε b δ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun _ => abs_nonneg _)]
  rw [gluingThinCylinderCoordinateMeasure, integral_prod _ hI]
  simp only [integral_const, smul_eq_mul]
  rw [measureReal_def, gluingCircleAngularLengthMeasure_univ,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi),
    gluingThinRadialMeasure, integral_subtype_comap measurableSet_Ioo
      (fun t : ℝ => |deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) t|),
    ← integral_Icc_eq_integral_Ioo]
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.pi), mul_comm]

theorem gluingThinCylinderCurvature_uniform_totalVariation_bound
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (b : ContDiffBump (0 : ℝ)) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (gluingThinCylinderCurvature r ε b δ).totalVariation univ ≤ B := by
  obtain ⟨B, hB, hb⟩ := gluingCollarLocalizedCurvatureOnRectangle_uniform_totalVariation_bound
    hr hδ b (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  refine ⟨B, hB, ?_⟩
  intro ε hε hε1
  rw [gluingThinCylinderCurvature_totalVariation_univ r hε b δ]
  simpa [gluingCollarLocalizedCurvatureOnRectangle_totalVariation_univ r hε b δ
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] using hb ε hε hε1

theorem gluingThinCylinder_radial_integrable {f : ℝ → ℝ} (hf : Continuous f) (δ : ℝ) :
    Integrable (fun p : Circle × Ioo (-δ) δ => f p.2.1)
      (gluingThinCylinderCoordinateMeasure δ) := by
  have hi : IntegrableOn f (Icc (-δ) δ) :=
    hf.continuousOn.integrableOn_compact isCompact_Icc
  have hs := (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mp
    (hi.mono_set Ioo_subset_Icc_self)
  change Integrable (fun t : Ioo (-δ) δ => f t.1) (gluingThinRadialMeasure δ) at hs
  exact hs.comp_snd gluingCircleAngularLengthMeasure

/-- Actual coordinate area, derived from the metric determinant `W²`. -/
def gluingThinCylinderArea (r ε : ℝ) (b : ContDiffBump (0 : ℝ)) (δ : ℝ) :
    Measure (Circle × Ioo (-δ) δ) :=
  (gluingThinCylinderCoordinateMeasure δ).withDensity
    (fun p => ENNReal.ofReal (gluingCollarLocalizedSmoothWarp r ε b p.2.1))

instance gluingThinCylinderArea_isFinite (r ε : ℝ) (b : ContDiffBump (0 : ℝ)) (δ : ℝ) :
    IsFiniteMeasure (gluingThinCylinderArea r ε b δ) :=
  isFiniteMeasure_withDensity_ofReal
    (gluingThinCylinder_radial_integrable (gluingCollarLocalizedSmoothWarp_continuous r ε b) δ).2

/-- Gaussian curvature computed from the genuine warped Levi-Civita
connection, evaluated at the actual cylinder's radial coordinate. -/
def gluingThinCylinderGaussian (r ε : ℝ) (b : ContDiffBump (0 : ℝ)) {δ : ℝ}
    (p : Circle × Ioo (-δ) δ) : ℝ :=
  gluingWarpedGaussianCurvature (gluingCollarLocalizedSmoothWarp r ε b) (p.2.1, 0)

theorem gluingThinCylinderGaussian_eq {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (b : ContDiffBump (0 : ℝ)) {δ : ℝ} (p : Circle × Ioo (-δ) δ) :
    gluingThinCylinderGaussian r ε b p =
      -deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) p.2.1 /
        gluingCollarLocalizedSmoothWarp r ε b p.2.1 :=
  gluingCollarLocalizedSmoothWarp_gaussianCurvature hr hε b (p.2.1, 0)

theorem gluingThinCylinderGaussian_continuous {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (b : ContDiffBump (0 : ℝ)) (δ : ℝ) :
    Continuous (gluingThinCylinderGaussian r ε b (δ := δ)) := by
  have hfun : gluingThinCylinderGaussian r ε b (δ := δ) = fun p =>
      -deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) p.2.1 /
        gluingCollarLocalizedSmoothWarp r ε b p.2.1 :=
    funext (gluingThinCylinderGaussian_eq hr hε b)
  rw [hfun]
  exact (gluingThinCylinderCurvatureDensity_continuous r hε b δ).div
    ((gluingCollarLocalizedSmoothWarp_continuous r ε b).comp
      (continuous_subtype_val.comp continuous_snd))
    (fun p => (gluingCollarLocalizedSmoothWarp_pos hr hε.le b p.2.1).ne')

theorem gluingThinCylinderGaussian_mul_warp {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (b : ContDiffBump (0 : ℝ)) {δ : ℝ} (p : Circle × Ioo (-δ) δ) :
    gluingCollarLocalizedSmoothWarp r ε b p.2.1 * gluingThinCylinderGaussian r ε b p =
      gluingThinCylinderCurvatureDensity r ε b p := by
  rw [gluingThinCylinderGaussian_eq hr hε b, gluingThinCylinderCurvatureDensity,
    mul_div_cancel₀ _ (gluingCollarLocalizedSmoothWarp_pos hr hε.le b p.2.1).ne']

theorem gluingThinCylinderGaussian_integrable_area {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (b : ContDiffBump (0 : ℝ)) (δ : ℝ) :
    Integrable (gluingThinCylinderGaussian r ε b) (gluingThinCylinderArea r ε b δ) := by
  rw [gluingThinCylinderArea]
  apply (integrable_withDensity_iff_integrable_smul'
    (((gluingCollarLocalizedSmoothWarp_continuous r ε b).comp
      (continuous_subtype_val.comp continuous_snd)).measurable.ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
  have heq : (fun p : Circle × Ioo (-δ) δ =>
      (ENNReal.ofReal (gluingCollarLocalizedSmoothWarp r ε b p.2.1)).toReal •
        gluingThinCylinderGaussian r ε b p) = gluingThinCylinderCurvatureDensity r ε b := by
    funext p
    rw [ENNReal.toReal_ofReal (gluingCollarLocalizedSmoothWarp_pos hr hε.le b p.2.1).le,
      smul_eq_mul, gluingThinCylinderGaussian_mul_warp hr hε b]
  change Integrable (fun p : Circle × Ioo (-δ) δ =>
    (ENNReal.ofReal (gluingCollarLocalizedSmoothWarp r ε b p.2.1)).toReal •
      gluingThinCylinderGaussian r ε b p) (gluingThinCylinderCoordinateMeasure δ)
  rw [heq]
  exact gluingThinCylinderCurvatureDensity_integrable r hε b δ

theorem gluingThinCylinderCurvature_eq_area_withDensity_gaussian {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (b : ContDiffBump (0 : ℝ)) (δ : ℝ) :
    gluingThinCylinderCurvature r ε b δ =
      (gluingThinCylinderArea r ε b δ).withDensityᵥ (gluingThinCylinderGaussian r ε b) := by
  have heq : (fun p : Circle × Ioo (-δ) δ =>
      (ENNReal.ofReal (gluingCollarLocalizedSmoothWarp r ε b p.2.1)).toReal •
        gluingThinCylinderGaussian r ε b p) = gluingThinCylinderCurvatureDensity r ε b := by
    funext p
    rw [ENNReal.toReal_ofReal (gluingCollarLocalizedSmoothWarp_pos hr hε.le b p.2.1).le,
      smul_eq_mul, gluingThinCylinderGaussian_mul_warp hr hε b]
  have hfg : Integrable (fun p : Circle × Ioo (-δ) δ =>
      (ENNReal.ofReal (gluingCollarLocalizedSmoothWarp r ε b p.2.1)).toReal •
        gluingThinCylinderGaussian r ε b p) (gluingThinCylinderCoordinateMeasure δ) := by
    rw [heq]
    exact gluingThinCylinderCurvatureDensity_integrable r hε b δ
  have h := withDensityᵥ_smul_eq_withDensityᵥ_withDensity'
    (μ := gluingThinCylinderCoordinateMeasure δ)
    (f := fun p => ENNReal.ofReal (gluingCollarLocalizedSmoothWarp r ε b p.2.1))
    (g := gluingThinCylinderGaussian r ε b)
    (((gluingCollarLocalizedSmoothWarp_continuous r ε b).comp
      (continuous_subtype_val.comp continuous_snd)).measurable.ennreal_ofReal.aemeasurable)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
    hfg
  simpa only [heq, gluingThinCylinderCurvature, gluingThinCylinderArea] using h

theorem signedMeasure_map_withDensity_of_embedding {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {f : α → β} (hf : MeasurableEmbedding f)
    (μ : Measure α) {g : β → ℝ} (hI : Integrable (g ∘ f) μ) :
    (μ.withDensityᵥ (g ∘ f)).map f = (Measure.map f μ).withDensityᵥ g := by
  ext s hs
  rw [VectorMeasure.map_apply _ hf.measurable hs, withDensityᵥ_apply hI (hf.measurable hs),
    withDensityᵥ_apply (hf.integrable_map_iff.mpr hI) hs,
    Measure.restrict_map hf.measurable hs, hf.integral_map]
  rfl

theorem signedMeasure_withDensity_add_measure {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) {g : α → ℝ} (hμ : Integrable g μ) (hν : Integrable g ν) :
    (μ + ν).withDensityᵥ g = μ.withDensityᵥ g + ν.withDensityᵥ g := by
  ext s hs
  rw [withDensityᵥ_apply (hμ.add_measure hν) hs, _root_.add_apply,
    withDensityᵥ_apply hμ hs, withDensityᵥ_apply hν hs, Measure.restrict_add,
    integral_add_measure hμ.integrableOn hν.integrableOn]

theorem signedMeasure_withDensity_finsetSum_measure {α ι : Type*} [MeasurableSpace α]
    (μ : ι → Measure α) {g : α → ℝ} (s : Finset ι)
    (hI : ∀ i ∈ s, Integrable g (μ i)) :
    (∑ i ∈ s, μ i).withDensityᵥ g = ∑ i ∈ s, (μ i).withDensityᵥ g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    ext E hE
    rw [withDensityᵥ_apply (by simp) hE]
    simp
  | insert i s his ih =>
    have hi := hI i (Finset.mem_insert_self _ _)
    have hs : ∀ j ∈ s, Integrable g (μ j) := fun j hj => hI j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert his, signedMeasure_withDensity_add_measure _ _ hi
      (integrable_finsetSum_measure.mpr hs), ih hs, Finset.sum_insert his]

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

theorem thinRadialInterval_subset_original (P : ExerciseGluingPreparation C g n genera X) :
    Ioo (-gluingThinSeamWidth C g) (gluingThinSeamWidth C g) ⊆
      Ioo (-gluingDepth C g) (gluingDepth C g) := by
  intro t ht
  constructor <;> linarith [ht.1, ht.2, P.thinSeamWidth_lt_depth]

/-- The actual inclusion of the original radial thin interval into its
unchanged native collar interval. -/
def thinRadialInclusion (P : ExerciseGluingPreparation C g n genera X) :
    Ioo (-gluingThinSeamWidth C g) (gluingThinSeamWidth C g) →
      Ioo (-gluingDepth C g) (gluingDepth C g) :=
  Set.inclusion P.thinRadialInterval_subset_original

/-- Literal injective native seam-cylinder parametrization, restricted
only to the proved disjoint thin interval. -/
def thinSeamCylinderMap (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (p : Circle × Ioo (-gluingThinSeamWidth C g) (gluingThinSeamWidth C g)) :
    P.GluedCarrier :=
  (P.seamCylinderHomeomorph k (p.1, P.thinRadialInclusion p.2)).1

theorem thinSeamCylinderMap_isOpenEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Topology.IsOpenEmbedding (P.thinSeamCylinderMap k) := by
  have hi : Topology.IsOpenEmbedding P.thinRadialInclusion :=
    Topology.IsOpenEmbedding.inclusion P.thinRadialInterval_subset_original
      (isOpen_Ioo.preimage continuous_subtype_val)
  have hp := (Topology.IsOpenEmbedding.id (X := Circle)).prodMap hi
  exact ((P.gluedSeamNeighborhood_isOpen k).isOpenEmbedding_subtypeVal.comp
    (P.seamCylinderHomeomorph k).isOpenEmbedding).comp hp

theorem thinSeamCylinderMap_measurableEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    MeasurableEmbedding (P.thinSeamCylinderMap k) :=
  (P.thinSeamCylinderMap_isOpenEmbedding k).measurableEmbedding

theorem range_thinSeamCylinderMap (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) : range (P.thinSeamCylinderMap k) = P.thinSeamCollar k := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨(p.1, P.thinRadialInclusion p.2), ?_, rfl⟩
    exact abs_lt.mpr p.2.2
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(p.1, ⟨p.2.1, abs_lt.mp hp⟩), rfl⟩

/-- The unchanged actual native area outside all patched thin strips. -/
def gluedChainSmoothOutsideArea (P : ExerciseGluingPreparation C g n genera X) :
    Measure P.GluedCarrier :=
  P.gluedChainAreaMeasure.restrict (⋃ k : Fin (n - 1), P.thinSeamCollar k)ᶜ

instance gluedChainSmoothOutsideArea_isFinite
    (P : ExerciseGluingPreparation C g n genera X) : IsFiniteMeasure P.gluedChainSmoothOutsideArea := by
  unfold gluedChainSmoothOutsideArea
  infer_instance

/-- Actual signed Gaussian density pushed through the literal injective
native cylinder of one seam, using the canonical metric's actual cutoff. -/
def gluedChainSmoothSeamCurvature (P : ExerciseGluingPreparation C g n genera X)
    (ε : ℝ) (k : Fin (n - 1)) : SignedMeasure P.GluedCarrier :=
  (gluingThinCylinderCurvature (gluingRadius C g) ε P.seamSmoothingCutoff
    (gluingThinSeamWidth C g)).map (P.thinSeamCylinderMap k)

/-- The global smooth curvature candidate on the original carrier:
negative original area outside the actual thin patches, and the actual
signed Gaussian densities inside them. Only disjoint thin strips are used. -/
def gluedChainSmoothCurvature (P : ExerciseGluingPreparation C g n genera X)
    (ε : ℝ) : SignedMeasure P.GluedCarrier :=
  -P.gluedChainSmoothOutsideArea.toSignedMeasure +
    ∑ k : Fin (n - 1), P.gluedChainSmoothSeamCurvature ε k

theorem gluedChainSmoothSeamCurvature_totalVariation
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (k : Fin (n - 1)) :
    (P.gluedChainSmoothSeamCurvature ε k).totalVariation =
      Measure.map (P.thinSeamCylinderMap k)
        (gluingThinCylinderCurvature (gluingRadius C g) ε P.seamSmoothingCutoff
          (gluingThinSeamWidth C g)).totalVariation := by
  rw [gluedChainSmoothSeamCurvature, signedMeasure_totalVariation_eq_variation,
    (P.thinSeamCylinderMap_measurableEmbedding k).variation_map,
    ← signedMeasure_totalVariation_eq_variation]

theorem gluedChainSmoothSeamCurvature_totalVariation_univ
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (k : Fin (n - 1)) :
    (P.gluedChainSmoothSeamCurvature ε k).totalVariation univ =
      (gluingThinCylinderCurvature (gluingRadius C g) ε P.seamSmoothingCutoff
        (gluingThinSeamWidth C g)).totalVariation univ := by
  rw [P.gluedChainSmoothSeamCurvature_totalVariation ε k,
    Measure.map_apply (P.thinSeamCylinderMap_measurableEmbedding k).measurable MeasurableSet.univ]
  rfl

/-- Finite variation is proved for the genuine signed global measure;
both Jordan signs in the thin patches are retained. -/
instance gluedChainSmoothCurvature_totalVariation_isFinite
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) :
    IsFiniteMeasure (P.gluedChainSmoothCurvature ε).totalVariation := by
  unfold SignedMeasure.totalVariation
  infer_instance

theorem gluedChainSmoothCurvature_totalVariation_regular
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) :
    Measure.Regular (P.gluedChainSmoothCurvature ε).totalVariation := by
  letI := P.gluedCarrierIntrinsicMetricSpace
  infer_instance

/-- The actual global variation is controlled by native outside area and
the finite sum of genuine cylinder absolute-curvature measures. -/
theorem gluedChainSmoothCurvature_totalVariation_le
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) :
    (P.gluedChainSmoothCurvature ε).totalVariation ≤
      P.gluedChainSmoothOutsideArea +
        ∑ k : Fin (n - 1), (P.gluedChainSmoothSeamCurvature ε k).totalVariation := by
  rw [signedMeasure_totalVariation_eq_variation, gluedChainSmoothCurvature]
  have hsum := VectorMeasure.variation_finsetSum_le Finset.univ
    (fun k : Fin (n - 1) => P.gluedChainSmoothSeamCurvature ε k)
  have hadd := VectorMeasure.variation_add_le
    (μ := -P.gluedChainSmoothOutsideArea.toSignedMeasure)
    (ν := ∑ k : Fin (n - 1), P.gluedChainSmoothSeamCurvature ε k)
  exact hadd.trans (by
    simpa [VectorMeasure.variation_neg, signedMeasure_totalVariation_eq_variation, add_comm] using
      add_le_add_left hsum P.gluedChainSmoothOutsideArea)

/-- A single finite variation bound works for all canonical smoothing
scales `0<ε≤1`, with no bounded-curvature hypothesis on the approximants. -/
theorem gluedChainSmoothCurvature_uniform_totalVariation_bound
    (P : ExerciseGluingPreparation C g n genera X) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (P.gluedChainSmoothCurvature ε).totalVariation univ ≤ B := by
  obtain ⟨B, hB, hb⟩ := gluingThinCylinderCurvature_uniform_totalVariation_bound
    P.radius_pos P.thinSeamWidth_pos P.seamSmoothingCutoff
  refine ⟨P.gluedChainAreaMeasure univ + ∑ _k : Fin (n - 1), B, ?_, ?_⟩
  · exact ENNReal.add_lt_top.mpr ⟨measure_lt_top _ _, ENNReal.sum_lt_top.mpr fun _ _ => hB⟩
  · intro ε hε hε1
    have hglobal := Measure.le_iff.mp (P.gluedChainSmoothCurvature_totalVariation_le ε)
      univ MeasurableSet.univ
    simp only [Measure.add_apply, Measure.finsetSum_apply] at hglobal
    apply hglobal.trans
    apply add_le_add
    · exact Measure.restrict_le_self univ
    · apply Finset.sum_le_sum
      intro k _
      rw [P.gluedChainSmoothSeamCurvature_totalVariation_univ ε k]
      exact hb ε hε hε1

theorem gluedChainSmoothSeamCurvature_restrict_own_thinCollar
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (k : Fin (n - 1)) :
    (P.gluedChainSmoothSeamCurvature ε k).restrict (P.thinSeamCollar k) =
      P.gluedChainSmoothSeamCurvature ε k := by
  rw [gluedChainSmoothSeamCurvature,
    VectorMeasure.restrict_map _ (P.thinSeamCylinderMap_measurableEmbedding k).measurable
      (P.thinSeamCollar_isOpen k).measurableSet]
  have hpre : P.thinSeamCylinderMap k ⁻¹' P.thinSeamCollar k = univ := by
    rw [← P.range_thinSeamCylinderMap k, preimage_range]
  rw [hpre, VectorMeasure.restrict_univ]

theorem gluedChainSmoothSeamCurvature_restrict_distinct_thinCollar
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ)
    {k l : Fin (n - 1)} (hkl : k ≠ l) :
    (P.gluedChainSmoothSeamCurvature ε k).restrict (P.thinSeamCollar l) = 0 := by
  rw [gluedChainSmoothSeamCurvature,
    VectorMeasure.restrict_map _ (P.thinSeamCylinderMap_measurableEmbedding k).measurable
      (P.thinSeamCollar_isOpen l).measurableSet]
  have hpre : P.thinSeamCylinderMap k ⁻¹' P.thinSeamCollar l = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hk : P.thinSeamCylinderMap k p ∈ P.thinSeamCollar k := by
      rw [← P.range_thinSeamCylinderMap k]
      exact ⟨p, rfl⟩
    exact disjoint_left.mp (P.closedThinSeamCollar_disjoint hkl)
      (P.thinSeamCollar_subset_closedThinSeamCollar k hk)
      (P.thinSeamCollar_subset_closedThinSeamCollar l hp)
  simp [hpre]

theorem gluedChainSmoothOutsideArea_restrict_thinCollar
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedChainSmoothOutsideArea.restrict (P.thinSeamCollar k) = 0 := by
  rw [gluedChainSmoothOutsideArea,
    Measure.restrict_restrict (P.thinSeamCollar_isOpen k).measurableSet]
  have hzero : P.thinSeamCollar k ∩ (⋃ l : Fin (n - 1), P.thinSeamCollar l)ᶜ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx.2 (mem_iUnion.mpr ⟨k, hx.1⟩)
  rw [hzero, Measure.restrict_empty]

/-- Restriction of the actual global measure to a thin strip is exactly
its own pushed Gaussian density. Other seam contributions vanish by the
proved native separation, not an assumed disjointness contract. -/
theorem gluedChainSmoothCurvature_restrict_thinCollar
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (k : Fin (n - 1)) :
    (P.gluedChainSmoothCurvature ε).restrict (P.thinSeamCollar k) =
      P.gluedChainSmoothSeamCurvature ε k := by
  classical
  rw [gluedChainSmoothCurvature, VectorMeasure.restrict_add, VectorMeasure.restrict_neg,
    VectorMeasure.restrict_toSignedMeasure (P.thinSeamCollar_isOpen k).measurableSet]
  simp only [P.gluedChainSmoothOutsideArea_restrict_thinCollar k,
    Measure.toSignedMeasure_zero, neg_zero, zero_add]
  have hsum := map_sum (VectorMeasure.restrictGm (P.thinSeamCollar k))
    (fun l : Fin (n - 1) => P.gluedChainSmoothSeamCurvature ε l) Finset.univ
  simp only [VectorMeasure.restrictGm_apply] at hsum
  change (∑ l : Fin (n - 1), P.gluedChainSmoothSeamCurvature ε l).restrict _ = _
  rw [hsum, Finset.sum_eq_single k]
  · exact P.gluedChainSmoothSeamCurvature_restrict_own_thinCollar ε k
  · intro l _ hlk
    exact P.gluedChainSmoothSeamCurvature_restrict_distinct_thinCollar ε hlk
  · simp

/-- Action of each actual native seam measure is the literal signed
Gaussian density integral on its original circle/radial cylinder. -/
theorem gluedChainSmoothSeamCurvature_apply
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 < ε)
    (k : Fin (n - 1)) {s : Set P.GluedCarrier} (hs : MeasurableSet s) :
    P.gluedChainSmoothSeamCurvature ε k s =
      ∫ p in P.thinSeamCylinderMap k ⁻¹' s,
        gluingThinCylinderCurvatureDensity (gluingRadius C g) ε P.seamSmoothingCutoff p
        ∂gluingThinCylinderCoordinateMeasure (gluingThinSeamWidth C g) := by
  rw [gluedChainSmoothSeamCurvature,
    VectorMeasure.map_apply _ (P.thinSeamCylinderMap_measurableEmbedding k).measurable hs]
  exact withDensityᵥ_apply
    (gluingThinCylinderCurvatureDensity_integrable _ hε _ _)
    ((P.thinSeamCylinderMap_measurableEmbedding k).measurable hs)

/-- Literal coordinate matrix of the actual globally patched tangent
tensor, evaluated in an original real angular seam chart. -/
def gluedSmoothSeamCoordinateMetric (P : ExerciseGluingPreparation C g n genera X)
    (ε : ℝ) (k : Fin (n - 1)) (θ : ℝ) (p : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let q := (P.seamAngularComplexChart k θ).symm (Complex.equivRealProdCLM.symm p)
  let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
  let i : atlas ℂ P.GluedCarrier := ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩
  fun a b => P.gluedSmoothTangentInner ε q
    ((Z.localTriv i).symmL ℝ q (if a = 0 then 1 else Complex.I))
    ((Z.localTriv i).symmL ℝ q (if b = 0 then 1 else Complex.I))

/-- On the actual thin-strip chart domain, the global tensor's coordinate
matrix is genuinely the metric used in the proved Levi-Civita computation. -/
theorem gluedSmoothSeamCoordinateMetric_eq_warped
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (k : Fin (n - 1)) (θ : ℝ)
    {p : ℝ × ℝ} (hp : Complex.equivRealProdCLM.symm p ∈ (P.seamAngularComplexChart k θ).target)
    (hthin : (P.seamAngularComplexChart k θ).symm (Complex.equivRealProdCLM.symm p) ∈
      P.thinSeamCollar k) :
    P.gluedSmoothSeamCoordinateMetric ε k θ p =
      gluingWarpedMetric (gluingCollarLocalizedSmoothWarp (gluingRadius C g) ε
        P.seamSmoothingCutoff) p := by
  ext a b
  dsimp only [gluedSmoothSeamCoordinateMetric]
  rw [P.gluedSmoothTangentInner_in_thin_seam_chart ε k θ _
    ((P.seamAngularComplexChart k θ).map_target hp) hthin,
    (P.seamAngularComplexChart k θ).right_inv hp]
  fin_cases a <;> fin_cases b <;> simp [gluingWarpedMetric]

/-- The literal signed density used by the global curvature measure is
Gaussian curvature times the area determinant of the actual global tensor
in each genuine thin-strip real chart. -/
theorem gluedSmoothSeamCoordinateMetric_gaussianDensity
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 < ε)
    (k : Fin (n - 1)) (θ : ℝ) {p : ℝ × ℝ}
    (hp : Complex.equivRealProdCLM.symm p ∈ (P.seamAngularComplexChart k θ).target)
    (hthin : (P.seamAngularComplexChart k θ).symm (Complex.equivRealProdCLM.symm p) ∈
      P.thinSeamCollar k) :
    gluingCollarLocalizedCurvatureDensity (gluingRadius C g) ε P.seamSmoothingCutoff p =
      gluingWarpedGaussianCurvature (gluingCollarLocalizedSmoothWarp (gluingRadius C g) ε
        P.seamSmoothingCutoff) p * Real.sqrt (P.gluedSmoothSeamCoordinateMetric ε k θ p).det := by
  rw [P.gluedSmoothSeamCoordinateMetric_eq_warped ε k θ hp hthin]
  exact gluingCollarLocalizedCurvatureDensity_eq_gaussian_mul_area P.radius_pos hε _ p

/-- The metric area of an actual smoothed thin cylinder, transported
through the original injective native cylinder map. -/
def gluedChainSmoothSeamArea (P : ExerciseGluingPreparation C g n genera X)
    (ε : ℝ) (k : Fin (n - 1)) : Measure P.GluedCarrier :=
  Measure.map (P.thinSeamCylinderMap k)
    (gluingThinCylinderArea (gluingRadius C g) ε P.seamSmoothingCutoff (gluingThinSeamWidth C g))

instance gluedChainSmoothSeamArea_isFinite (P : ExerciseGluingPreparation C g n genera X)
    (ε : ℝ) (k : Fin (n - 1)) : IsFiniteMeasure (P.gluedChainSmoothSeamArea ε k) := by
  unfold gluedChainSmoothSeamArea
  infer_instance

/-- Actual patched metric area: original native area outside the patches
and the derived positive metric determinant in each disjoint thin cylinder. -/
def gluedChainSmoothAreaMeasure (P : ExerciseGluingPreparation C g n genera X)
    (ε : ℝ) : Measure P.GluedCarrier :=
  P.gluedChainSmoothOutsideArea + ∑ k : Fin (n - 1), P.gluedChainSmoothSeamArea ε k

instance gluedChainSmoothAreaMeasure_isFinite (P : ExerciseGluingPreparation C g n genera X)
    (ε : ℝ) : IsFiniteMeasure (P.gluedChainSmoothAreaMeasure ε) := by
  unfold gluedChainSmoothAreaMeasure
  infer_instance

instance gluedChainSmoothAreaMeasure_regular (P : ExerciseGluingPreparation C g n genera X)
    (ε : ℝ) : Measure.Regular (P.gluedChainSmoothAreaMeasure ε) := by
  letI := P.gluedCarrierIntrinsicMetricSpace
  infer_instance

/-- Measurable global extension of the genuinely computed Gaussian
curvature: `-1` outside the thin patches and the derived local Gaussian
quotient inside the unique actual thin cylinder. -/
def gluedChainSmoothGaussian (P : ExerciseGluingPreparation C g n genera X)
    (ε : ℝ) (q : P.GluedCarrier) : ℝ :=
  -1 + ∑ k : Fin (n - 1), Function.extend (P.thinSeamCylinderMap k)
    (fun p => gluingThinCylinderGaussian (gluingRadius C g) ε P.seamSmoothingCutoff p + 1)
    (fun _ => 0) q

theorem gluedChainSmoothGaussian_measurable (P : ExerciseGluingPreparation C g n genera X)
    {ε : ℝ} (hε : 0 < ε) : Measurable (P.gluedChainSmoothGaussian ε) := by
  apply Measurable.add measurable_const
  apply Finset.measurable_sum
  intro k _
  exact (P.thinSeamCylinderMap_measurableEmbedding k).measurable_extend
    ((gluingThinCylinderGaussian_continuous P.radius_pos hε P.seamSmoothingCutoff
      (gluingThinSeamWidth C g)).measurable.add_const 1) measurable_const

theorem gluedChainSmoothGaussian_eq_neg_one_of_outside
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) {q : P.GluedCarrier}
    (hq : ∀ k : Fin (n - 1), q ∉ P.thinSeamCollar k) :
    P.gluedChainSmoothGaussian ε q = -1 := by
  unfold gluedChainSmoothGaussian
  have hz : (∑ k : Fin (n - 1), Function.extend (P.thinSeamCylinderMap k)
      (fun p => gluingThinCylinderGaussian (gluingRadius C g) ε P.seamSmoothingCutoff p + 1)
      (fun _ => 0) q) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    apply Function.extend_apply'
    rintro ⟨p, hp⟩
    apply hq k
    rw [← P.range_thinSeamCylinderMap k, ← hp]
    exact ⟨p, rfl⟩
  rw [hz, add_zero]

/-- The global computed Gaussian field pulls back exactly to the genuine
Levi-Civita Gaussian quotient on each original thin cylinder. -/
theorem gluedChainSmoothGaussian_thinSeamCylinderMap
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (k : Fin (n - 1))
    (p : Circle × Ioo (-gluingThinSeamWidth C g) (gluingThinSeamWidth C g)) :
    P.gluedChainSmoothGaussian ε (P.thinSeamCylinderMap k p) =
      gluingThinCylinderGaussian (gluingRadius C g) ε P.seamSmoothingCutoff p := by
  classical
  unfold gluedChainSmoothGaussian
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

theorem gluedChainSmoothGaussian_integrable_outsideArea
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) :
    Integrable (P.gluedChainSmoothGaussian ε) P.gluedChainSmoothOutsideArea := by
  have hU : MeasurableSet (⋃ k : Fin (n - 1), P.thinSeamCollar k) :=
    (isOpen_iUnion fun k => P.thinSeamCollar_isOpen k).measurableSet
  have hEq : P.gluedChainSmoothGaussian ε =ᵐ[P.gluedChainSmoothOutsideArea] fun _ => -1 := by
    filter_upwards [ae_restrict_mem hU.compl] with q hq
    exact P.gluedChainSmoothGaussian_eq_neg_one_of_outside ε
      (fun k hk => hq (mem_iUnion.mpr ⟨k, hk⟩))
  exact (integrable_const (-1 : ℝ)).congr hEq.symm

theorem gluedChainSmoothGaussian_integrable_seamArea
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 < ε) (k : Fin (n - 1)) :
    Integrable (P.gluedChainSmoothGaussian ε) (P.gluedChainSmoothSeamArea ε k) := by
  rw [gluedChainSmoothSeamArea,
    (P.thinSeamCylinderMap_measurableEmbedding k).integrable_map_iff]
  have heq : (P.gluedChainSmoothGaussian ε ∘ P.thinSeamCylinderMap k) =
      gluingThinCylinderGaussian (gluingRadius C g) ε P.seamSmoothingCutoff :=
    funext (P.gluedChainSmoothGaussian_thinSeamCylinderMap ε k)
  rw [heq]
  exact gluingThinCylinderGaussian_integrable_area P.radius_pos hε _ _

theorem gluedChainSmoothGaussian_integrable_area
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 < ε) :
    Integrable (P.gluedChainSmoothGaussian ε) (P.gluedChainSmoothAreaMeasure ε) := by
  apply (P.gluedChainSmoothGaussian_integrable_outsideArea ε).add_measure
  exact integrable_finsetSum_measure.mpr fun k _ =>
    P.gluedChainSmoothGaussian_integrable_seamArea hε k

theorem gluedChainSmoothOutsideArea_withDensity_gaussian
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) :
    P.gluedChainSmoothOutsideArea.withDensityᵥ (P.gluedChainSmoothGaussian ε) =
      -P.gluedChainSmoothOutsideArea.toSignedMeasure := by
  have hU : MeasurableSet (⋃ k : Fin (n - 1), P.thinSeamCollar k) :=
    (isOpen_iUnion fun k => P.thinSeamCollar_isOpen k).measurableSet
  have hEq : P.gluedChainSmoothGaussian ε =ᵐ[P.gluedChainSmoothOutsideArea] fun _ => -1 := by
    filter_upwards [ae_restrict_mem hU.compl] with q hq
    exact P.gluedChainSmoothGaussian_eq_neg_one_of_outside ε
      (fun k hk => hq (mem_iUnion.mpr ⟨k, hk⟩))
  rw [WithDensityᵥEq.congr_ae hEq]
  ext s hs
  rw [withDensityᵥ_apply (integrable_const _) hs, _root_.neg_apply,
    Measure.toSignedMeasure_apply_measurable hs, integral_const]
  simp [smul_eq_mul]

theorem gluedChainSmoothSeamArea_withDensity_gaussian
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 < ε) (k : Fin (n - 1)) :
    (P.gluedChainSmoothSeamArea ε k).withDensityᵥ (P.gluedChainSmoothGaussian ε) =
      P.gluedChainSmoothSeamCurvature ε k := by
  have heq : (P.gluedChainSmoothGaussian ε ∘ P.thinSeamCylinderMap k) =
      gluingThinCylinderGaussian (gluingRadius C g) ε P.seamSmoothingCutoff :=
    funext (P.gluedChainSmoothGaussian_thinSeamCylinderMap ε k)
  rw [gluedChainSmoothSeamArea,
    ← signedMeasure_map_withDensity_of_embedding (P.thinSeamCylinderMap_measurableEmbedding k) _
      (by rw [heq]; exact gluingThinCylinderGaussian_integrable_area P.radius_pos hε _ _), heq,
    ← gluingThinCylinderCurvature_eq_area_withDensity_gaussian P.radius_pos hε]
  rfl

/-- The actual transported signed curvature is exactly the computed
Gaussian field integrated against the derived patched metric area. -/
theorem gluedChainSmoothCurvature_eq_area_withDensity_gaussian
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 < ε) :
    P.gluedChainSmoothCurvature ε =
      (P.gluedChainSmoothAreaMeasure ε).withDensityᵥ (P.gluedChainSmoothGaussian ε) := by
  rw [gluedChainSmoothAreaMeasure,
    signedMeasure_withDensity_add_measure _ _
      (P.gluedChainSmoothGaussian_integrable_outsideArea ε)
      (integrable_finsetSum_measure.mpr fun k _ => P.gluedChainSmoothGaussian_integrable_seamArea hε k),
    signedMeasure_withDensity_finsetSum_measure _ Finset.univ
      (fun k _ => P.gluedChainSmoothGaussian_integrable_seamArea hε k),
    P.gluedChainSmoothOutsideArea_withDensity_gaussian ε]
  simp only [P.gluedChainSmoothSeamArea_withDensity_gaussian hε]
  rfl

/-- Jordan variation is exactly absolute Gaussian curvature times the
actual patched area, so positive localization defects are counted. -/
theorem gluedChainSmoothCurvature_totalVariation_eq_absGaussian
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 < ε) :
    (P.gluedChainSmoothCurvature ε).totalVariation =
      (P.gluedChainSmoothAreaMeasure ε).withDensity
        (fun q => ENNReal.ofReal |P.gluedChainSmoothGaussian ε q|) := by
  rw [P.gluedChainSmoothCurvature_eq_area_withDensity_gaussian hε]
  exact signedMeasure_withDensity_totalVariation_of_integrable _
    (P.gluedChainSmoothGaussian_measurable hε) (P.gluedChainSmoothGaussian_integrable_area hε)

/-- Uniform absolute Gaussian-curvature integral of the constructed
patches, using the actual area and all internally computed Gaussian values. -/
theorem gluedChainSmoothGaussian_uniform_abs_integral_bound
    (P : ExerciseGluingPreparation C g n genera X) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (∫⁻ q, ENNReal.ofReal |P.gluedChainSmoothGaussian ε q|
        ∂P.gluedChainSmoothAreaMeasure ε) ≤ B := by
  obtain ⟨B, hB, hb⟩ := P.gluedChainSmoothCurvature_uniform_totalVariation_bound
  refine ⟨B, hB, ?_⟩
  intro ε hε hε1
  have h := hb ε hε hε1
  rwa [P.gluedChainSmoothCurvature_totalVariation_eq_absGaussian hε,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h

/-- Actual native tensor coefficients in an original interior chart. -/
def gluedSmoothInteriorCoordinateMetric (P : ExerciseGluingPreparation C g n genera X)
    (ε : ℝ) (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    (p : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let q := e.symm (Complex.equivRealProdCLM.symm p)
  let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
  let i : atlas ℂ P.GluedCarrier := ⟨e, Or.inl he⟩
  fun a b => P.gluedSmoothTangentInner ε q
    ((Z.localTriv i).symmL ℝ q (if a = 0 then 1 else Complex.I))
    ((Z.localTriv i).symmL ℝ q (if b = 0 then 1 else Complex.I))

/-- Outside the actual patches the literal native tensor coefficients
are exactly those of the original Poincaré metric. -/
theorem gluedSmoothInteriorCoordinateMetric_eq_hyperbolic
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    {p : ℝ × ℝ} (hp : Complex.equivRealProdCLM.symm p ∈ e.target)
    (houtside : ∀ k : Fin (n - 1), e.symm (Complex.equivRealProdCLM.symm p) ∉ P.thinSeamCollar k) :
    P.gluedSmoothInteriorCoordinateMetric ε e he p = hyperbolicGaussianMetric p := by
  ext a b
  dsimp only [gluedSmoothInteriorCoordinateMetric]
  rw [P.gluedSmoothTangentInner_eq_native_of_outside_thinCollars ε _ houtside,
    P.gluedTangentInner_in_chart e (Or.inl he) _ (e.map_target hp),
    P.gluingChartTangentForm_interior e he, e.right_inv hp]
  fin_cases a <;> fin_cases b <;>
    simp [hyperbolicGaussianMetric, gluingComplexHalfPlaneTangentForm_apply, div_eq_mul_inv]

/-- In every genuine exterior interior chart, the global computed value
is the Gaussian curvature derived from the actual Poincaré connection. -/
theorem gluedChainSmoothGaussian_in_exterior_interior_chart
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    {p : ℝ × ℝ} (hp : Complex.equivRealProdCLM.symm p ∈ e.target)
    (houtside : ∀ k : Fin (n - 1), e.symm (Complex.equivRealProdCLM.symm p) ∉ P.thinSeamCollar k) :
    P.gluedChainSmoothGaussian ε (e.symm (Complex.equivRealProdCLM.symm p)) =
      hyperbolicGaussianCurvature p := by
  have hy : 0 < p.2 := by
    simpa using P.gluedInteriorComplexChart_target_im_pos e he hp
  rw [P.gluedChainSmoothGaussian_eq_neg_one_of_outside ε houtside,
    hyperbolicGaussianCurvature_eq_neg_one hy]

theorem gluedChainSmoothGaussian_seamAngularPoint
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 < ε)
    (k : Fin (n - 1)) (θ : ℝ) (a : GluingSeamAngularDomain C g θ)
    (hthin : P.seamAngularPoint k θ a ∈ P.thinSeamCollar k) :
    P.gluedChainSmoothGaussian ε (P.seamAngularPoint k θ a) =
      gluingWarpedGaussianCurvature (gluingCollarLocalizedSmoothWarp (gluingRadius C g) ε
        P.seamSmoothingCutoff) (a.1.1, a.2.1) := by
  have hrad : |a.1.1| < gluingThinSeamWidth C g :=
    (P.seamCylinderHomeomorph_mem_thinSeamCollar_iff k (Circle.exp a.2.1, a.1)).mp hthin
  let p : Circle × Ioo (-gluingThinSeamWidth C g) (gluingThinSeamWidth C g) :=
    (Circle.exp a.2.1, ⟨a.1.1, abs_lt.mp hrad⟩)
  change P.gluedChainSmoothGaussian ε (P.thinSeamCylinderMap k p) = _
  rw [P.gluedChainSmoothGaussian_thinSeamCylinderMap ε k p,
    gluingThinCylinderGaussian_eq P.radius_pos hε,
    gluingCollarLocalizedSmoothWarp_gaussianCurvature P.radius_pos hε]

/-- Exact computed Gaussian value in every actual thin-strip real chart,
linked to the actual native tensor coefficient identity above. -/
theorem gluedChainSmoothGaussian_in_thin_seam_chart
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 < ε)
    (k : Fin (n - 1)) (θ : ℝ) {p : ℝ × ℝ}
    (hp : Complex.equivRealProdCLM.symm p ∈ (P.seamAngularComplexChart k θ).target)
    (hthin : (P.seamAngularComplexChart k θ).symm (Complex.equivRealProdCLM.symm p) ∈
      P.thinSeamCollar k) :
    P.gluedChainSmoothGaussian ε
        ((P.seamAngularComplexChart k θ).symm (Complex.equivRealProdCLM.symm p)) =
      gluingWarpedGaussianCurvature (gluingCollarLocalizedSmoothWarp (gluingRadius C g) ε
        P.seamSmoothingCutoff) p := by
  have hsource := (P.seamAngularComplexChart k θ).map_target hp
  rw [P.seamAngularComplexChart_source] at hsource
  obtain ⟨a, ha⟩ := hsource
  have hcoord : gluingSeamAngularModel C g θ a = Complex.equivRealProdCLM.symm p := by
    rw [← P.seamAngularComplexChart_apply k θ a, ha,
      (P.seamAngularComplexChart k θ).right_inv hp]
  have hrad : a.1.1 = p.1 := by
    simpa using congrArg Complex.re hcoord
  have hang : a.2.1 = p.2 := by
    simpa using congrArg Complex.im hcoord
  have hpair : (a.1.1, a.2.1) = p := Prod.ext hrad hang
  have h := P.gluedChainSmoothGaussian_seamAngularPoint hε k θ a (ha.symm ▸ hthin)
  simpa only [ha, hpair] using h

/-- The transported density is the global field times the actual native
coordinate metric's area determinant on every real thin-strip chart. -/
theorem gluedSmoothSeamCoordinateMetric_globalGaussianDensity
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 < ε)
    (k : Fin (n - 1)) (θ : ℝ) {p : ℝ × ℝ}
    (hp : Complex.equivRealProdCLM.symm p ∈ (P.seamAngularComplexChart k θ).target)
    (hthin : (P.seamAngularComplexChart k θ).symm (Complex.equivRealProdCLM.symm p) ∈
      P.thinSeamCollar k) :
    gluingCollarLocalizedCurvatureDensity (gluingRadius C g) ε P.seamSmoothingCutoff p =
      P.gluedChainSmoothGaussian ε
        ((P.seamAngularComplexChart k θ).symm (Complex.equivRealProdCLM.symm p)) *
          Real.sqrt (P.gluedSmoothSeamCoordinateMetric ε k θ p).det := by
  rw [P.gluedChainSmoothGaussian_in_thin_seam_chart hε k θ hp hthin]
  exact P.gluedSmoothSeamCoordinateMetric_gaussianDensity hε k θ hp hthin

#print axioms signedMeasure_totalVariation_eq_variation
#print axioms gluingThinCylinderCurvature_totalVariation_univ
#print axioms thinSeamCylinderMap_measurableEmbedding
#print axioms gluedChainSmoothCurvature_uniform_totalVariation_bound
#print axioms gluedChainSmoothCurvature_restrict_thinCollar
#print axioms gluedSmoothSeamCoordinateMetric_eq_warped
#print axioms gluedSmoothInteriorCoordinateMetric_eq_hyperbolic
#print axioms gluedChainSmoothCurvature_eq_area_withDensity_gaussian
#print axioms gluedChainSmoothCurvature_totalVariation_eq_absGaussian
#print axioms gluedChainSmoothGaussian_in_thin_seam_chart
#print axioms gluedChainSmoothGaussian_in_exterior_interior_chart
#print axioms gluedChainSmoothGaussian_uniform_abs_integral_bound

end ExerciseGluingPreparation

end
end SystolicGrowth
