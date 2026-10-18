module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarCurvatureMeasure
public import Geometry.GluingCollarSeamMetric
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Two-dimensional coordinate curvature of the original Fermi collar

The proved radial weak second-derivative measure is multiplied by angular
Lebesgue measure. Its area density, seam line and exact rectangle masses
are genuine locally finite coordinate measures. Identification with the
intrinsic surface curvature is a separate bounded-integral-curvature step.
-/

open Set MeasureTheory

namespace SystolicGrowth

/-- **Math.** The coordinate area density of the actual Fermi warp. -/
noncomputable def gluingCollarCoordinateAreaMeasure (r : ℝ) : Measure (ℝ × ℝ) :=
  (volume.prod volume).withDensity (fun p => ENNReal.ofReal (gluingCollarWarp r p.1))

instance gluingCollarCoordinateAreaMeasure_isLocallyFinite (r : ℝ) :
    IsLocallyFiniteMeasure (gluingCollarCoordinateAreaMeasure r) :=
  IsLocallyFiniteMeasure.withDensity_ofReal ((gluingCollarWarp_continuous r).comp continuous_fst)

instance gluingCollarCoordinateAreaMeasure_restrict_rectangle_isFinite
    (r a b u v : ℝ) :
    IsFiniteMeasure ((gluingCollarCoordinateAreaMeasure r).restrict (Icc a b ×ˢ Icc u v)) := by
  exact isFiniteMeasure_restrict.mpr
    (ne_of_lt (isCompact_Icc.prod isCompact_Icc).measure_lt_top)

/-- **Math.** The positive magnitude of the coordinate curvature input,
including the proved negative-curvature seam coefficient. -/
noncomputable def gluingCollarCoordinateCurvatureMagnitude (r : ℝ) : Measure (ℝ × ℝ) :=
  (gluingCollarRadialSecondDerivativeMeasure r).prod volume

instance gluingCollarCoordinateCurvatureMagnitude_isLocallyFinite (r : ℝ) :
    IsLocallyFiniteMeasure (gluingCollarCoordinateCurvatureMagnitude r) := by
  unfold gluingCollarCoordinateCurvatureMagnitude
  infer_instance

instance gluingCollarCoordinateCurvatureMagnitude_regular (r : ℝ) :
    Measure.Regular (gluingCollarCoordinateCurvatureMagnitude r) := inferInstance

/-- **Math.** The actual product curvature input splits into the native
area density and its original seam-line measure, with coefficient `2 cosh r`. -/
theorem gluingCollarCoordinateCurvatureMagnitude_eq_area_add_seam (r : ℝ) :
    gluingCollarCoordinateCurvatureMagnitude r = gluingCollarCoordinateAreaMeasure r +
      ENNReal.ofReal (2 * Real.cosh r) •
        Measure.map (fun u : ℝ => ((0 : ℝ), u)) volume := by
  rw [gluingCollarCoordinateCurvatureMagnitude, gluingCollarRadialSecondDerivativeMeasure,
    Measure.add_prod, Measure.prod_smul_left, Measure.dirac_prod]
  rw [prod_withDensity_left (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (f := fun s => ENNReal.ofReal (gluingCollarWarp r s))
    (ENNReal.measurable_ofReal.comp (gluingCollarWarp_continuous r).measurable)]
  rfl

theorem gluingCollarCoordinateAreaMeasure_le_curvatureMagnitude (r : ℝ) :
    gluingCollarCoordinateAreaMeasure r ≤ gluingCollarCoordinateCurvatureMagnitude r := by
  rw [gluingCollarCoordinateCurvatureMagnitude_eq_area_add_seam]
  apply Measure.le_iff.mpr
  intro s _hs
  rw [Measure.add_apply]
  exact le_add_right le_rfl

/-- **Math.** A coordinate seam segment has precisely its derivative-jump
curvature mass; the smooth density contributes no seam mass. -/
theorem gluingCollarCoordinateCurvatureMagnitude_seam (r u v : ℝ) :
    gluingCollarCoordinateCurvatureMagnitude r (({0} : Set ℝ) ×ˢ Icc u v) =
      ENNReal.ofReal (2 * Real.cosh r) * ENNReal.ofReal (v - u) := by
  rw [gluingCollarCoordinateCurvatureMagnitude, Measure.prod_prod,
    gluingCollarRadialSecondDerivativeMeasure_singleton_zero, Real.volume_Icc]

/-- **Math.** Every symmetric coordinate rectangle has its exact area-plus-
seam curvature mass, with no finite-crossing or finite-variation hypothesis. -/
theorem gluingCollarCoordinateCurvatureMagnitude_rectangle
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (u v : ℝ) :
    gluingCollarCoordinateCurvatureMagnitude r (Icc (-R) R ×ˢ Icc u v) =
      ENNReal.ofReal (2 * Real.cosh (r + R)) * ENNReal.ofReal (v - u) := by
  rw [gluingCollarCoordinateCurvatureMagnitude, Measure.prod_prod,
    gluingCollarRadialSecondDerivativeMeasure_Icc hr hR, Real.volume_Icc]

instance gluingCollarCoordinateCurvatureMagnitude_restrict_rectangle_isFinite
    (r a b u v : ℝ) :
    IsFiniteMeasure ((gluingCollarCoordinateCurvatureMagnitude r).restrict
      (Icc a b ×ˢ Icc u v)) := by
  exact isFiniteMeasure_restrict.mpr
    (ne_of_lt (isCompact_Icc.prod isCompact_Icc).measure_lt_top)

/-- **Math.** The signed coordinate curvature on an actual bounded
rectangle is negative area density minus its genuine seam-line atom. -/
noncomputable def gluingCollarCoordinateCurvatureOnRectangle
    (r R u v : ℝ) : SignedMeasure (ℝ × ℝ) :=
  -((gluingCollarCoordinateCurvatureMagnitude r).restrict
    (Icc (-R) R ×ˢ Icc u v)).toSignedMeasure

theorem gluingCollarCoordinateCurvatureOnRectangle_nonpositive (r R u v : ℝ) :
    gluingCollarCoordinateCurvatureOnRectangle r R u v ≤ 0 :=
  neg_nonpos.mpr (Measure.zero_le_toSignedMeasure _)

/-- **Math.** The actual coordinate curvature is bounded above by negative
coordinate area on every bounded rectangle; the seam has the correct sign. -/
theorem gluingCollarCoordinateCurvatureOnRectangle_le_neg_area (r R u v : ℝ) :
    gluingCollarCoordinateCurvatureOnRectangle r R u v ≤
      -((gluingCollarCoordinateAreaMeasure r).restrict (Icc (-R) R ×ˢ Icc u v)).toSignedMeasure := by
  have h : ((gluingCollarCoordinateAreaMeasure r).restrict
        (Icc (-R) R ×ˢ Icc u v)).toSignedMeasure ≤
      ((gluingCollarCoordinateCurvatureMagnitude r).restrict
        (Icc (-R) R ×ˢ Icc u v)).toSignedMeasure :=
    (Measure.toSignedMeasure_le_toSignedMeasure_iff _ _).mpr
      (Measure.restrict_mono (Set.Subset.refl _)
        (gluingCollarCoordinateAreaMeasure_le_curvatureMagnitude r))
  apply VectorMeasure.le_iff.mpr
  intro s hs
  rw [gluingCollarCoordinateCurvatureOnRectangle, neg_apply, neg_apply]
  exact neg_le_neg (VectorMeasure.le_iff.mp h s hs)

/-- **Math.** The coordinate signed curvature has exactly the constructed
finite total variation, including its original seam contribution. -/
theorem gluingCollarCoordinateCurvatureOnRectangle_totalVariation (r R u v : ℝ) :
    (gluingCollarCoordinateCurvatureOnRectangle r R u v).totalVariation =
      (gluingCollarCoordinateCurvatureMagnitude r).restrict (Icc (-R) R ×ˢ Icc u v) := by
  let μ := (gluingCollarCoordinateCurvatureMagnitude r).restrict (Icc (-R) R ×ˢ Icc u v)
  let j : JordanDecomposition (ℝ × ℝ) :=
    { posPart := μ
      negPart := 0
      mutuallySingular := Measure.MutuallySingular.zero_right }
  have hj : j.toSignedMeasure = μ.toSignedMeasure := by
    simp [j, JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_zero]
  change (-μ.toSignedMeasure).totalVariation = μ
  rw [SignedMeasure.totalVariation_neg, ← hj, SignedMeasure.totalVariation,
    JordanDecomposition.toJordanDecomposition_toSignedMeasure]
  simp [j]

instance gluingCollarCoordinateCurvatureOnRectangle_totalVariation_isFinite (r R u v : ℝ) :
    IsFiniteMeasure (gluingCollarCoordinateCurvatureOnRectangle r R u v).totalVariation := by
  rw [gluingCollarCoordinateCurvatureOnRectangle_totalVariation]
  infer_instance

theorem gluingCollarCoordinateCurvatureOnRectangle_totalVariation_univ
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (u v : ℝ) :
    (gluingCollarCoordinateCurvatureOnRectangle r R u v).totalVariation univ =
      ENNReal.ofReal (2 * Real.cosh (r + R)) * ENNReal.ofReal (v - u) := by
  rw [gluingCollarCoordinateCurvatureOnRectangle_totalVariation, Measure.restrict_apply_univ]
  exact gluingCollarCoordinateCurvatureMagnitude_rectangle hr hR u v

/-- The length density of the original coordinate seam, whose actual
native collar metric is `sinh r` times angular displacement. -/
noncomputable def gluingCollarCoordinateSeamLengthMeasure (r : ℝ) : Measure (ℝ × ℝ) :=
  ENNReal.ofReal (Real.sinh r) • Measure.map (fun u : ℝ => ((0 : ℝ), u)) volume

instance gluingCollarCoordinateSeamLengthMeasure_isLocallyFinite (r : ℝ) :
    IsLocallyFiniteMeasure (gluingCollarCoordinateSeamLengthMeasure r) := by
  letI : IsFiniteMeasure (ENNReal.ofReal (Real.sinh r) • Measure.dirac (0 : ℝ)) :=
    (Measure.dirac (0 : ℝ)).smul_finite ENNReal.ofReal_ne_top
  rw [gluingCollarCoordinateSeamLengthMeasure, ← Measure.dirac_prod,
    ← Measure.prod_smul_left]
  infer_instance

instance gluingCollarCoordinateSeamLengthMeasure_restrict_rectangle_isFinite
    (r a b u v : ℝ) :
    IsFiniteMeasure ((gluingCollarCoordinateSeamLengthMeasure r).restrict
      (Icc a b ×ˢ Icc u v)) := by
  exact isFiniteMeasure_restrict.mpr
    (ne_of_lt (isCompact_Icc.prod isCompact_Icc).measure_lt_top)

/-- The genuine seam-length density gives the exact length of every
original angular segment, including a reversed or empty interval. -/
theorem gluingCollarCoordinateSeamLengthMeasure_segment (r u v : ℝ) :
    gluingCollarCoordinateSeamLengthMeasure r (({0} : Set ℝ) ×ˢ Icc u v) =
      ENNReal.ofReal (Real.sinh r) * ENNReal.ofReal (v - u) := by
  rw [gluingCollarCoordinateSeamLengthMeasure, ← Measure.dirac_prod,
    Measure.smul_apply, Measure.prod_prod, Measure.dirac_apply_of_mem (mem_singleton 0),
    one_mul, Real.volume_Icc]
  rfl

/-- The coordinate seam measure is justified by the length of the actual
native collar C¹ seam segment, not merely by naming a line measure. -/
theorem gluingCollarCoordinateSeamLengthMeasure_eq_native_seam_length
    {r : ℝ} (hr : 0 < r) {u v : ℝ} (huv : u ≤ v) :
    gluingCollarCoordinateSeamLengthMeasure r (({0} : Set ℝ) ×ˢ Icc u v) =
      gluingCollarModelPathELength hr
        (gluingCollarLinearSegment ((u : ℂ) * Complex.I) ((v : ℂ) * Complex.I)) 0 1 := by
  rw [gluingCollarCoordinateSeamLengthMeasure_segment,
    gluingCollarModelPathELength_seam_linearSegment,
    abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr huv),
    ← ENNReal.ofReal_mul (Real.sinh_pos_iff.mpr hr).le]

/-- In the original angular coordinate, the positive curvature magnitude
is area plus `2 coth r` times actual seam-length density. -/
theorem gluingCollarCoordinateCurvatureMagnitude_eq_area_add_seam_length
    {r : ℝ} (hr : 0 < r) :
    gluingCollarCoordinateCurvatureMagnitude r = gluingCollarCoordinateAreaMeasure r +
      ENNReal.ofReal (2 * (Real.cosh r / Real.sinh r)) •
        gluingCollarCoordinateSeamLengthMeasure r := by
  have hsinh : 0 < Real.sinh r := Real.sinh_pos_iff.mpr hr
  have hcoefficient : 0 ≤ 2 * (Real.cosh r / Real.sinh r) := by positivity
  rw [gluingCollarCoordinateCurvatureMagnitude_eq_area_add_seam,
    gluingCollarCoordinateSeamLengthMeasure, smul_smul,
    ← ENNReal.ofReal_mul hcoefficient]
  congr 2
  congr 1
  field_simp

/-- The signed coordinate curvature on every actual bounded window is
negative area minus `2 coth r` times the original native seam arclength
density. This does not yet identify global intrinsic surface curvature. -/
theorem gluingCollarCoordinateCurvatureOnRectangle_eq_neg_area_sub_seam_length
    {r : ℝ} (hr : 0 < r) (R u v : ℝ) :
    gluingCollarCoordinateCurvatureOnRectangle r R u v =
      -((gluingCollarCoordinateAreaMeasure r).restrict (Icc (-R) R ×ˢ Icc u v)).toSignedMeasure -
        (2 * (Real.cosh r / Real.sinh r)) •
          ((gluingCollarCoordinateSeamLengthMeasure r).restrict
            (Icc (-R) R ×ˢ Icc u v)).toSignedMeasure := by
  have hsinh : 0 < Real.sinh r := Real.sinh_pos_iff.mpr hr
  let k : ℝ := 2 * (Real.cosh r / Real.sinh r)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  let μ := (gluingCollarCoordinateSeamLengthMeasure r).restrict (Icc (-R) R ×ˢ Icc u v)
  letI : IsFiniteMeasure (ENNReal.ofReal k • μ) := μ.smul_finite ENNReal.ofReal_ne_top
  have hsmul : (ENNReal.ofReal k • μ).toSignedMeasure = k • μ.toSignedMeasure := by
    change (k.toNNReal • μ).toSignedMeasure = _
    rw [Measure.toSignedMeasure_smul]
    change (k.toNNReal : ℝ) • μ.toSignedMeasure = _
    rw [Real.coe_toNNReal k hk]
  have hmeasure : (gluingCollarCoordinateCurvatureMagnitude r).restrict
      (Icc (-R) R ×ˢ Icc u v) =
      (gluingCollarCoordinateAreaMeasure r).restrict (Icc (-R) R ×ˢ Icc u v) +
        ENNReal.ofReal k • μ := by
    rw [gluingCollarCoordinateCurvatureMagnitude_eq_area_add_seam_length hr,
      Measure.restrict_add, Measure.restrict_smul]
  have hsigned := Measure.toSignedMeasure_congr hmeasure
  rw [gluingCollarCoordinateCurvatureOnRectangle, hsigned,
    Measure.toSignedMeasure_add, hsmul, neg_add, sub_eq_add_neg]

/-- Genuine compact tensor tests identify the actual coordinate product
measure with the radial weak second derivative in two dimensions. Both
pairings are integrable; this is not an equality of undefined integrals. -/
theorem gluingCollarCoordinateCurvatureMagnitude_weak_second_derivative_tensor
    {r : ℝ} (hr : 0 < r) {φ ψ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφsupport : HasCompactSupport φ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ) :
    Integrable (fun p : ℝ × ℝ => φ p.1 * ψ p.2)
      (gluingCollarCoordinateCurvatureMagnitude r) ∧
    Integrable (fun p : ℝ × ℝ => gluingCollarWarp r p.1 *
      deriv (deriv φ) p.1 * ψ p.2) (volume.prod volume) ∧
    (∫ p : ℝ × ℝ, φ p.1 * ψ p.2 ∂gluingCollarCoordinateCurvatureMagnitude r) =
      ∫ p : ℝ × ℝ, gluingCollarWarp r p.1 * deriv (deriv φ) p.1 * ψ p.2
        ∂volume.prod volume := by
  have hφint : Integrable φ (gluingCollarRadialSecondDerivativeMeasure r) :=
    hφ.continuous.integrable_of_hasCompactSupport hφsupport
  have hψint : Integrable ψ := hψ.integrable_of_hasCompactSupport hψsupport
  have hderiv : Continuous (deriv (deriv φ)) := hφ.deriv'.continuous_deriv_one
  have hproductsupport : HasCompactSupport
      (fun s => gluingCollarWarp r s * deriv (deriv φ) s) :=
    hφsupport.deriv.deriv.mul_left
  have hproductint : Integrable (fun s => gluingCollarWarp r s * deriv (deriv φ) s) :=
    ((gluingCollarWarp_continuous r).mul hderiv).integrable_of_hasCompactSupport hproductsupport
  refine ⟨hφint.mul_prod hψint, hproductint.mul_prod hψint, ?_⟩
  rw [gluingCollarCoordinateCurvatureMagnitude, integral_prod_mul,
    gluingCollarRadialSecondDerivativeMeasure_weak_second_derivative hr hφ hφsupport,
    ← integral_prod_mul]

#print axioms gluingCollarCoordinateCurvatureMagnitude_eq_area_add_seam
#print axioms gluingCollarCoordinateCurvatureMagnitude_rectangle
#print axioms gluingCollarCoordinateCurvatureOnRectangle_totalVariation
#print axioms gluingCollarCoordinateCurvatureOnRectangle_le_neg_area
#print axioms gluingCollarCoordinateSeamLengthMeasure_eq_native_seam_length
#print axioms gluingCollarCoordinateCurvatureMagnitude_eq_area_add_seam_length
#print axioms gluingCollarCoordinateCurvatureOnRectangle_eq_neg_area_sub_seam_length
#print axioms gluingCollarCoordinateCurvatureMagnitude_weak_second_derivative_tensor

end SystolicGrowth
