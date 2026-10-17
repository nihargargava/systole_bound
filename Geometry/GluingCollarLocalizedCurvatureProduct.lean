module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarLocalizedCurvature
public import Geometry.GluingCollarLocalizedCurvatureMass
public import Geometry.GluingWarpedGaussianCurvature
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Actual signed curvature densities of localized smooth collars

Localization need not preserve nonpositive curvature. Its signed density
is therefore integrated as a genuine signed measure, with both Jordan parts.
The absolute variation on compact coordinate rectangles is uniformly bounded
in the smoothing parameter by the proved radial estimate. Identification
with Gaussian curvature uses the warped metric's connection separately.
-/

open Set Filter MeasureTheory
open scoped ENNReal

namespace SystolicGrowth

/-- The genuine Jordan variation of an integrable signed density is exactly
the positive measure with its absolute density. -/
theorem signedMeasure_withDensity_totalVariation_of_integrable
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : α → ℝ} (hf : Measurable f) (hI : Integrable f μ) :
    SignedMeasure.totalVariation (μ.withDensityᵥ f) =
      μ.withDensity (fun x => ENNReal.ofReal |f x|) := by
  letI : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (f x)) :=
    isFiniteMeasure_withDensity_ofReal hI.2
  letI : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (-f x)) :=
    isFiniteMeasure_withDensity_ofReal hI.neg.2
  let j : JordanDecomposition α :=
    { posPart := μ.withDensity fun x => ENNReal.ofReal (f x)
      negPart := μ.withDensity fun x => ENNReal.ofReal (-f x)
      mutuallySingular := withDensity_ofReal_mutuallySingular hf }
  have hj : j.toSignedMeasure = μ.withDensityᵥ f := by
    exact (withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hI).symm
  rw [← hj, SignedMeasure.totalVariation,
    JordanDecomposition.toJordanDecomposition_toSignedMeasure]
  change μ.withDensity (fun x => ENNReal.ofReal (f x)) +
    μ.withDensity (fun x => ENNReal.ofReal (-f x)) = _
  rw [← withDensity_add_left hf.ennreal_ofReal]
  congr 1
  funext x
  by_cases hx : 0 ≤ f x
  · simp [abs_of_nonneg hx, ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr hx)]
  · have hx' : f x ≤ 0 := (lt_of_not_ge hx).le
    simp [abs_of_nonpos hx', ENNReal.ofReal_eq_zero.mpr hx']

/-- The second derivative at the actual positive cutoff boundary is native,
by uniqueness of one-sided derivatives of the genuine smooth first derivative. -/
theorem gluingCollarLocalizedSmoothWarp_second_deriv_eq_native_of_radius_ge
    (r : ℝ) {ε R : ℝ} (hε : 0 < ε) (b : ContDiffBump (0 : ℝ))
    (hR : b.rOut ≤ R) :
    deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) R = gluingCollarWarp r R := by
  have hRpos : 0 < R := b.rOut_pos.trans_le hR
  have hd := (gluingCollarLocalizedSmoothWarp_contDiff r hε b 2).differentiable_deriv_two R
  have hw : HasDerivWithinAt (deriv (gluingCollarLocalizedSmoothWarp r ε b))
      (gluingCollarWarp r R) (Ici R) R := by
    apply (gluingCollarWarp_hasDerivAt_deriv r hRpos.ne').hasDerivWithinAt.congr_of_mem
    · intro s hs
      rw [gluingCollarLocalizedSmoothWarp_deriv_eq_native_of_radius_ge r hε b (hR.trans hs),
        gluingCollarWarp_deriv_pos r (hRpos.trans_le hs)]
    · exact self_mem_Ici
  exact (hd.hasDerivAt.hasDerivWithinAt.derivWithin
    (uniqueDiffWithinAt_Ici R)).symm.trans (hw.derivWithin (uniqueDiffWithinAt_Ici R))

/-- The same exact curvature identity at the negative cutoff boundary. -/
theorem gluingCollarLocalizedSmoothWarp_second_deriv_neg_eq_native_of_radius_ge
    (r : ℝ) {ε R : ℝ} (hε : 0 < ε) (b : ContDiffBump (0 : ℝ))
    (hR : b.rOut ≤ R) :
    deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) (-R) = gluingCollarWarp r (-R) := by
  have hRpos : 0 < R := b.rOut_pos.trans_le hR
  have htneg : -R < 0 := by linarith
  have hd := (gluingCollarLocalizedSmoothWarp_contDiff r hε b 2).differentiable_deriv_two (-R)
  have hw : HasDerivWithinAt (deriv (gluingCollarLocalizedSmoothWarp r ε b))
      (gluingCollarWarp r (-R)) (Iic (-R)) (-R) := by
    apply (gluingCollarWarp_hasDerivAt_deriv r htneg.ne).hasDerivWithinAt.congr_of_mem
    · intro s hs
      change s ≤ -R at hs
      have hsneg : s < 0 := lt_of_le_of_lt hs htneg
      have hsrad : b.rOut ≤ -s := by linarith
      have heq := gluingCollarLocalizedSmoothWarp_deriv_neg_eq_native_of_radius_ge
        r hε b hsrad
      rw [gluingCollarWarp_deriv_neg r hsneg]
      simpa only [neg_neg, sub_eq_add_neg] using heq
    · exact self_mem_Iic
  exact (hd.hasDerivAt.hasDerivWithinAt.derivWithin
    (uniqueDiffWithinAt_Iic (-R))).symm.trans (hw.derivWithin (uniqueDiffWithinAt_Iic (-R)))

/-- The actual localized second derivative equals native area density
throughout the exterior, including both support boundaries. -/
theorem gluingCollarLocalizedSmoothWarp_second_deriv_eq_native_of_abs_radius_ge
    (r : ℝ) {ε t : ℝ} (hε : 0 < ε) (b : ContDiffBump (0 : ℝ))
    (ht : b.rOut ≤ |t|) :
    deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) t = gluingCollarWarp r t := by
  rcases le_total 0 t with hpos | hneg
  · rw [abs_of_nonneg hpos] at ht
    exact gluingCollarLocalizedSmoothWarp_second_deriv_eq_native_of_radius_ge r hε b ht
  · rw [abs_of_nonpos hneg] at ht
    simpa only [neg_neg] using
      gluingCollarLocalizedSmoothWarp_second_deriv_neg_eq_native_of_radius_ge r hε b ht

/-- The localized metric has genuine Gaussian curvature −1 wherever the
actual cutoff is zero, even on the cutoff boundary. -/
theorem gluingCollarLocalizedGaussianCurvature_eq_neg_one_of_radius_ge
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (b : ContDiffBump (0 : ℝ))
    (p : ℝ × ℝ) (hp : b.rOut ≤ |p.1|) :
    gluingWarpedGaussianCurvature (gluingCollarLocalizedSmoothWarp r ε b) p = -1 := by
  rw [gluingCollarLocalizedSmoothWarp_gaussianCurvature hr hε,
    gluingCollarLocalizedSmoothWarp_second_deriv_eq_native_of_abs_radius_ge r hε b hp,
    gluingCollarLocalizedSmoothWarp_eq_native r ε b hp, neg_div,
    div_self (gluingCollarWarp_pos hr p.1).ne']

/-- The true signed density, allowing both signs after localization. -/
noncomputable def gluingCollarLocalizedCurvatureDensity (r ε : ℝ)
    (b : ContDiffBump (0 : ℝ)) (p : ℝ × ℝ) : ℝ :=
  -deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) p.1

theorem gluingCollarLocalizedCurvatureDensity_continuous (r : ℝ)
    {ε : ℝ} (hε : 0 < ε) (b : ContDiffBump (0 : ℝ)) :
    Continuous (gluingCollarLocalizedCurvatureDensity r ε b) :=
  ((gluingCollarLocalizedSmoothWarp_contDiff r hε b 2).deriv'.continuous_deriv_one.comp
    continuous_fst).neg

/-- The density is the actual Gaussian curvature times the actual metric
area density, derived from its compatible torsion-free connection. -/
theorem gluingCollarLocalizedCurvatureDensity_eq_gaussian_mul_area
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (b : ContDiffBump (0 : ℝ)) (p : ℝ × ℝ) :
    gluingCollarLocalizedCurvatureDensity r ε b p =
      gluingWarpedGaussianCurvature (gluingCollarLocalizedSmoothWarp r ε b) p *
        Real.sqrt (gluingWarpedMetric (gluingCollarLocalizedSmoothWarp r ε b) p).det := by
  exact (gluingCollarLocalizedSmoothWarp_gaussianCurvature_mul_areaDensity hr hε b p).symm

/-- Actual finite signed measure obtained by integrating the density on
the original coordinate rectangle. -/
noncomputable def gluingCollarLocalizedCurvatureOnRectangle
    (r ε : ℝ) (b : ContDiffBump (0 : ℝ)) (R u v : ℝ) : SignedMeasure (ℝ × ℝ) :=
  ((volume.prod volume).restrict (Icc (-R) R ×ˢ Icc u v)).withDensityᵥ
    (gluingCollarLocalizedCurvatureDensity r ε b)

/-- The actual density is integrable for every positive smoothing parameter. -/
theorem gluingCollarLocalizedCurvatureDensity_integrableOn_rectangle
    (r : ℝ) {ε : ℝ} (hε : 0 < ε) (b : ContDiffBump (0 : ℝ)) (R u v : ℝ) :
    IntegrableOn (gluingCollarLocalizedCurvatureDensity r ε b)
      (Icc (-R) R ×ˢ Icc u v) (volume.prod volume) :=
  (gluingCollarLocalizedCurvatureDensity_continuous r hε b).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)

/-- Its action is the literal curvature integral, never an assigned measure. -/
theorem gluingCollarLocalizedCurvatureOnRectangle_apply
    (r : ℝ) {ε : ℝ} (hε : 0 < ε) (b : ContDiffBump (0 : ℝ)) (R u v : ℝ)
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) :
    gluingCollarLocalizedCurvatureOnRectangle r ε b R u v s =
      ∫ p in s, gluingCollarLocalizedCurvatureDensity r ε b p
        ∂(volume.prod volume).restrict (Icc (-R) R ×ˢ Icc u v) := by
  exact withDensityᵥ_apply
    (gluingCollarLocalizedCurvatureDensity_integrableOn_rectangle r hε b R u v) hs

/-- The exact Jordan total variation is the absolute actual density. Both
signs introduced by localization are accounted for, not discarded. -/
theorem gluingCollarLocalizedCurvatureOnRectangle_totalVariation
    (r : ℝ) {ε : ℝ} (hε : 0 < ε) (b : ContDiffBump (0 : ℝ)) (R u v : ℝ) :
    (gluingCollarLocalizedCurvatureOnRectangle r ε b R u v).totalVariation =
      ((volume.prod volume).restrict (Icc (-R) R ×ˢ Icc u v)).withDensity
        (fun p => ENNReal.ofReal
          |deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) p.1|) := by
  rw [gluingCollarLocalizedCurvatureOnRectangle,
    signedMeasure_withDensity_totalVariation_of_integrable _
      (gluingCollarLocalizedCurvatureDensity_continuous r hε b).measurable
      (gluingCollarLocalizedCurvatureDensity_integrableOn_rectangle r hε b R u v)]
  congr 1
  funext p
  simp [gluingCollarLocalizedCurvatureDensity]

/-- The actual variation mass on a rectangle is its genuine radial integral
times its angular length. -/
theorem gluingCollarLocalizedCurvatureOnRectangle_totalVariation_univ
    (r : ℝ) {ε : ℝ} (hε : 0 < ε) (b : ContDiffBump (0 : ℝ)) (R : ℝ)
    {u v : ℝ} (huv : u ≤ v) :
    (gluingCollarLocalizedCurvatureOnRectangle r ε b R u v).totalVariation univ =
      ENNReal.ofReal (∫ t : ℝ in Icc (-R) R,
        |deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) t|) *
      ENNReal.ofReal (v - u) := by
  have hI := (gluingCollarLocalizedCurvatureDensity_integrableOn_rectangle
    r hε b R u v).abs
  have hI' : IntegrableOn
      (fun p : ℝ × ℝ => |deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) p.1|)
      (Icc (-R) R ×ˢ Icc u v) (volume.prod volume) := by
    simpa only [IntegrableOn, gluingCollarLocalizedCurvatureDensity, abs_neg] using hI
  rw [gluingCollarLocalizedCurvatureOnRectangle_totalVariation r hε b R u v,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hI' (Eventually.of_forall fun _ => abs_nonneg _)]
  have hfactor := setIntegral_prod_mul
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun t => |deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) t|)
    (fun _ => (1 : ℝ)) (Icc (-R) R) (Icc u v)
  simp only [mul_one] at hfactor
  rw [hfactor, integral_const, measureReal_restrict_apply_univ, measureReal_def,
    Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr huv), smul_eq_mul, mul_one,
    ENNReal.ofReal_mul (integral_nonneg fun _ => abs_nonneg _)]

/-- Actual signed two-dimensional curvature has uniformly bounded total
variation on every fixed rectangle, independently of `0<ε≤1`. -/
theorem gluingCollarLocalizedCurvatureOnRectangle_uniform_totalVariation_bound
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (b : ContDiffBump (0 : ℝ))
    {u v : ℝ} (huv : u ≤ v) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (gluingCollarLocalizedCurvatureOnRectangle r ε b R u v).totalVariation univ ≤ B := by
  obtain ⟨B, _hB, hbound⟩ :=
    gluingCollarLocalizedSmoothWarp_uniform_abs_second_deriv_integral_bound hr hR b
  refine ⟨ENNReal.ofReal B * ENNReal.ofReal (v - u), by finiteness, ?_⟩
  intro ε hε hε1
  rw [gluingCollarLocalizedCurvatureOnRectangle_totalVariation_univ r hε b R huv]
  gcongr
  exact hbound ε hε hε1

#print axioms gluingCollarLocalizedCurvatureOnRectangle_apply
#print axioms signedMeasure_withDensity_totalVariation_of_integrable
#print axioms gluingCollarLocalizedCurvatureDensity_eq_gaussian_mul_area
#print axioms gluingCollarLocalizedGaussianCurvature_eq_neg_one_of_radius_ge
#print axioms gluingCollarLocalizedCurvatureOnRectangle_totalVariation
#print axioms gluingCollarLocalizedCurvatureOnRectangle_uniform_totalVariation_bound

end SystolicGrowth
