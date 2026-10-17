module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarWarp
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

@[expose] public section

/-!
# The measure-valued radial second derivative of the actual collar warp

The literal warp `sinh (r + |s|)` has a smooth density and the seam atom
`2 cosh r`. Their sum is a locally finite positive measure; its action on
actual C² test functions is proved to be the weak second derivative.
The negative radial measure is the curvature input for the original angular
coordinate, not an assertion of bounded integral curvature for the surface.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SystolicGrowth

/-- The genuine positive radial distribution measure: native warp density
plus the exact derivative-jump atom at the original seam coordinate zero. -/
noncomputable def gluingCollarRadialSecondDerivativeMeasure (r : ℝ) : Measure ℝ :=
  volume.withDensity (fun s => ENNReal.ofReal (gluingCollarWarp r s)) +
    ENNReal.ofReal (2 * Real.cosh r) • Measure.dirac 0

/-- The density is continuous and the seam atom finite, hence the actual
radial distribution measure is locally finite. -/
instance gluingCollarRadialSecondDerivativeMeasure_isLocallyFinite (r : ℝ) :
    IsLocallyFiniteMeasure (gluingCollarRadialSecondDerivativeMeasure r) := by
  letI : IsLocallyFiniteMeasure
      (volume.withDensity fun s => ENNReal.ofReal (gluingCollarWarp r s)) :=
    IsLocallyFiniteMeasure.withDensity_ofReal (gluingCollarWarp_continuous r)
  letI : IsFiniteMeasure (ENNReal.ofReal (2 * Real.cosh r) • Measure.dirac (0 : ℝ)) :=
    (Measure.dirac (0 : ℝ)).smul_finite ENNReal.ofReal_ne_top
  refine ⟨fun s => ?_⟩
  obtain ⟨U, hU, hfinite⟩ :=
    (volume.withDensity fun t => ENNReal.ofReal (gluingCollarWarp r t)).finiteAt_nhds s
  refine ⟨U, hU, ?_⟩
  rw [gluingCollarRadialSecondDerivativeMeasure, Measure.add_apply]
  exact ENNReal.add_lt_top.mpr ⟨hfinite, measure_lt_top _ _⟩

/-- On the original real radial line this locally finite Borel measure is
regular, hence has the compact inner regularity required of a Radon measure. -/
instance gluingCollarRadialSecondDerivativeMeasure_regular (r : ℝ) :
    Measure.Regular (gluingCollarRadialSecondDerivativeMeasure r) := inferInstance

/-- Only the derivative-jump atom charges the seam point. -/
theorem gluingCollarRadialSecondDerivativeMeasure_singleton_zero (r : ℝ) :
    gluingCollarRadialSecondDerivativeMeasure r {0} = ENNReal.ofReal (2 * Real.cosh r) := by
  simp [gluingCollarRadialSecondDerivativeMeasure, Measure.add_apply]

/-- Exact native warp mass on a symmetric bounded collar window, before
adding the seam atom. -/
theorem gluingCollarWarp_integral_symmetric_window (r : ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ s in -R..R, gluingCollarWarp r s) =
      2 * (Real.cosh (r + R) - Real.cosh r) := by
  have hcont := gluingCollarWarp_continuous r
  have hminus : (∫ s in -R..0, gluingCollarWarp r s) =
      -Real.cosh r - -Real.cosh (r + R) := by
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (show -R ≤ (0 : ℝ) by linarith)
      ((Real.continuous_cosh.comp (continuous_const.sub continuous_id)).neg.continuousOn)
      (f := fun s : ℝ => -Real.cosh (r - s)) (f' := gluingCollarWarp r)
      (by
        intro s hs
        rw [gluingCollarWarp_eq_of_nonpos r hs.2.le]
        convert (((hasDerivAt_id s).const_sub r).cosh.neg) using 1 <;> simp [id_eq]
        funext u
        simp only [Pi.neg_apply])
      (hcont.intervalIntegrable (-R) 0)
    simpa only [sub_zero, sub_neg_eq_add] using hFTC
  have hplus : (∫ s in 0..R, gluingCollarWarp r s) =
      Real.cosh (r + R) - Real.cosh r := by
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR.le
      ((Real.continuous_cosh.comp (continuous_const.add continuous_id)).continuousOn)
      (f := fun s : ℝ => Real.cosh (r + s)) (f' := gluingCollarWarp r)
      (by
        intro s hs
        rw [gluingCollarWarp_eq_of_nonneg r hs.1.le]
        simpa using (((hasDerivAt_id s).const_add r).cosh))
      (hcont.intervalIntegrable 0 R)
    simpa only [add_zero] using hFTC
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (-R) 0) (hcont.intervalIntegrable 0 R), hminus, hplus]
  ring

/-- The density mass and seam atom combine to the exact bounded-window
mass `2 cosh (r+R)` in the unchanged radial coordinate. -/
theorem gluingCollarRadialSecondDerivativeMeasure_Icc {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) :
    gluingCollarRadialSecondDerivativeMeasure r (Icc (-R) R) =
      ENNReal.ofReal (2 * Real.cosh (r + R)) := by
  have hwarp := gluingCollarWarp_continuous r
  have hnonneg : ∀ s : ℝ, 0 ≤ gluingCollarWarp r s :=
    fun s => (gluingCollarWarp_pos hr s).le
  have hmass : (volume.withDensity fun s => ENNReal.ofReal (gluingCollarWarp r s))
      (Icc (-R) R) = ENNReal.ofReal (2 * (Real.cosh (r + R) - Real.cosh r)) := by
    rw [withDensity_apply _ measurableSet_Icc,
      ← ofReal_integral_eq_lintegral_ofReal hwarp.integrableOn_Icc
        (Filter.Eventually.of_forall hnonneg), integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show -R ≤ R by linarith),
      gluingCollarWarp_integral_symmetric_window r hR]
  have hcosh : Real.cosh r ≤ Real.cosh (r + R) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_pos hr, abs_of_pos (by linarith : 0 < r + R)]
    linarith
  have hbulk : 0 ≤ 2 * (Real.cosh (r + R) - Real.cosh r) := by linarith
  have hatom : 0 ≤ 2 * Real.cosh r := by positivity
  have hzero : (0 : ℝ) ∈ Icc (-R) R := ⟨by linarith, hR.le⟩
  rw [gluingCollarRadialSecondDerivativeMeasure, Measure.add_apply, hmass,
    Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Icc]
  simp only [indicator_of_mem hzero, Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hbulk hatom]
  congr 1
  ring

/-- Every bounded closed window has a genuinely finite radial distribution
measure, not a supplied finite-variation assumption. -/
instance gluingCollarRadialSecondDerivativeMeasure_restrict_Icc_isFinite
    (r a b : ℝ) :
    IsFiniteMeasure ((gluingCollarRadialSecondDerivativeMeasure r).restrict (Icc a b)) := by
  exact (isFiniteMeasure_restrict).mpr (ne_of_lt isCompact_Icc.measure_lt_top)

/-- The actual radial measure pairs with a continuous test as the warp
density plus the original seam jump. -/
theorem gluingCollarRadialSecondDerivativeMeasure_integral_Icc
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    {φ : ℝ → ℝ} (hφ : Continuous φ) :
    (∫ s in Icc (-R) R, φ s ∂gluingCollarRadialSecondDerivativeMeasure r) =
      (∫ s in -R..R, gluingCollarWarp r s * φ s) + 2 * Real.cosh r * φ 0 := by
  let density := volume.withDensity (fun s => ENNReal.ofReal (gluingCollarWarp r s))
  let atom := ENNReal.ofReal (2 * Real.cosh r) • Measure.dirac (0 : ℝ)
  letI : IsLocallyFiniteMeasure density :=
    IsLocallyFiniteMeasure.withDensity_ofReal (gluingCollarWarp_continuous r)
  letI : IsFiniteMeasure atom :=
    (Measure.dirac (0 : ℝ)).smul_finite ENNReal.ofReal_ne_top
  have hd : IntegrableOn φ (Icc (-R) R) density := hφ.integrableOn_Icc
  have ha : IntegrableOn φ (Icc (-R) R) atom := hφ.integrableOn_Icc
  have hzero : (0 : ℝ) ∈ Icc (-R) R := ⟨by linarith, hR.le⟩
  change (∫ s, φ s ∂(density + atom).restrict (Icc (-R) R)) = _
  rw [Measure.restrict_add, integral_add_measure hd ha]
  have hdensity : (∫ s in Icc (-R) R, φ s ∂density) =
      ∫ s in -R..R, gluingCollarWarp r s * φ s := by
    rw [show density = volume.withDensity
      (fun s => ENNReal.ofReal (gluingCollarWarp r s)) from rfl,
      setIntegral_withDensity_eq_setIntegral_toReal_smul
        ((gluingCollarWarp_continuous r).measurable.ennreal_ofReal)
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) φ measurableSet_Icc]
    simp only [ENNReal.toReal_ofReal (gluingCollarWarp_pos hr _).le, smul_eq_mul]
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show -R ≤ R by linarith)]
  have hatom : (∫ s in Icc (-R) R, φ s ∂atom) = 2 * Real.cosh r * φ 0 := by
    dsimp [atom]
    rw [Measure.restrict_smul, restrict_dirac]
    simp only [if_pos hzero, integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (show 0 ≤ 2 * Real.cosh r by positivity), smul_eq_mul]
  rw [hdensity, hatom]

/-- Exact weak second-derivative pairing on the native collar window.
The endpoint conditions are the ordinary compact-test boundary conditions. -/
theorem gluingCollarRadialSecondDerivativeMeasure_weak_second_derivative_Icc
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφleft : φ (-R) = 0) (hφright : φ R = 0)
    (hφ'left : deriv φ (-R) = 0) (hφ'right : deriv φ R = 0) :
    (∫ s in Icc (-R) R, φ s ∂gluingCollarRadialSecondDerivativeMeasure r) =
      ∫ s in -R..R, gluingCollarWarp r s * deriv (deriv φ) s := by
  have hφ' : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have hφ'' : Continuous (deriv (deriv φ)) := hφ'.continuous_deriv_one
  have hweak := gluingCollarWarp_integral_second_deriv_sub r
    (show -R < (0 : ℝ) by linarith) hR hφ hφleft hφright hφ'left hφ'right
  simp_rw [mul_sub] at hweak
  rw [intervalIntegral.integral_sub
    (f := fun s => gluingCollarWarp r s * deriv (deriv φ) s)
    (g := fun s => gluingCollarWarp r s * φ s)
    (((gluingCollarWarp_continuous r).mul hφ'').intervalIntegrable (-R) R)
    (((gluingCollarWarp_continuous r).mul hφ.continuous).intervalIntegrable (-R) R)] at hweak
  rw [gluingCollarRadialSecondDerivativeMeasure_integral_Icc hr hR hφ.continuous]
  linarith

/-- Against every compactly supported C² test, the constructed locally
finite measure is exactly the global weak second derivative of the literal
native warp. No test window or boundary hypotheses remain in this corollary. -/
theorem gluingCollarRadialSecondDerivativeMeasure_weak_second_derivative
    {r : ℝ} (hr : 0 < r) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupport : HasCompactSupport φ) :
    (∫ s, φ s ∂gluingCollarRadialSecondDerivativeMeasure r) =
      ∫ s, gluingCollarWarp r s * deriv (deriv φ) s := by
  obtain ⟨R, hR, hbound⟩ := hsupport.isCompact.isBounded.exists_pos_norm_lt
  have hinside : tsupport φ ⊆ Ioo (-R) R := by
    intro s hs
    exact abs_lt.mp (by simpa only [Real.norm_eq_abs] using hbound s hs)
  have hleft : -R ∉ tsupport φ := by
    intro hs
    exact (lt_irrefl (-R)) (hinside hs).1
  have hright : R ∉ tsupport φ := by
    intro hs
    exact (lt_irrefl R) (hinside hs).2
  have hφzero (s : ℝ) (hs : s ∉ tsupport φ) : φ s = 0 :=
    Function.notMem_support.mp (fun h => hs (subset_tsupport φ h))
  have hφoutside (s : ℝ) (hs : s ∉ Icc (-R) R) : s ∉ tsupport φ :=
    fun h => hs (Ioo_subset_Icc_self (hinside h))
  have hφ''outside (s : ℝ) (hs : s ∉ Icc (-R) R) : deriv (deriv φ) s = 0 :=
    deriv_of_notMem_tsupport (fun h => hφoutside s hs (tsupport_deriv_subset h))
  have hweak := gluingCollarRadialSecondDerivativeMeasure_weak_second_derivative_Icc
    hr hR hφ (hφzero (-R) hleft) (hφzero R hright)
    (deriv_of_notMem_tsupport hleft) (deriv_of_notMem_tsupport hright)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun s hs => hφzero s (hφoutside s hs))] at hweak
  rw [intervalIntegral.integral_of_le (show -R ≤ R by linarith),
    ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun s hs => by rw [hφ''outside s hs, mul_zero])] at hweak
  exact hweak

/-- The radial signed curvature input on an actual bounded collar window
is the negative weak second-derivative measure. This does not yet identify
the full two-dimensional intrinsic curvature measure. -/
noncomputable def gluingCollarRadialCurvatureMeasureOnWindow (r R : ℝ) : SignedMeasure ℝ :=
  -((gluingCollarRadialSecondDerivativeMeasure r).restrict (Icc (-R) R)).toSignedMeasure

/-- The radial signed curvature is nonpositive, including its negative
seam atom. -/
theorem gluingCollarRadialCurvatureMeasureOnWindow_nonpositive (r R : ℝ) :
    gluingCollarRadialCurvatureMeasureOnWindow r R ≤ 0 := by
  exact neg_nonpos.mpr (Measure.zero_le_toSignedMeasure _)

/-- The actual negative radial seam atom has the original coefficient
`-2 cosh r`; it is not absorbed into the smooth density. -/
theorem gluingCollarRadialCurvatureMeasureOnWindow_singleton_zero
    (r : ℝ) {R : ℝ} (hR : 0 < R) :
    gluingCollarRadialCurvatureMeasureOnWindow r R {0} = -2 * Real.cosh r := by
  have hzero : (0 : ℝ) ∈ Icc (-R) R := ⟨by linarith, hR.le⟩
  have hsubset : ({0} : Set ℝ) ⊆ Icc (-R) R := singleton_subset_iff.mpr hzero
  rw [gluingCollarRadialCurvatureMeasureOnWindow, neg_apply,
    Measure.toSignedMeasure_apply_measurable (measurableSet_singleton 0), measureReal_def,
    Measure.restrict_apply (measurableSet_singleton 0), inter_eq_left.mpr hsubset,
    gluingCollarRadialSecondDerivativeMeasure_singleton_zero,
    ENNReal.toReal_ofReal (show 0 ≤ 2 * Real.cosh r by positivity)]
  ring

/-- Its total variation is exactly the actual restricted positive radial
measure, rather than an unproved finite-variation premise. -/
theorem gluingCollarRadialCurvatureMeasureOnWindow_totalVariation (r R : ℝ) :
    (gluingCollarRadialCurvatureMeasureOnWindow r R).totalVariation =
      (gluingCollarRadialSecondDerivativeMeasure r).restrict (Icc (-R) R) := by
  let μ := (gluingCollarRadialSecondDerivativeMeasure r).restrict (Icc (-R) R)
  let j : JordanDecomposition ℝ :=
    { posPart := μ
      negPart := 0
      mutuallySingular := Measure.MutuallySingular.zero_right }
  have hj : j.toSignedMeasure = μ.toSignedMeasure := by
    simp [j, JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_zero]
  change (-μ.toSignedMeasure).totalVariation = μ
  rw [SignedMeasure.totalVariation_neg, ← hj, SignedMeasure.totalVariation,
    JordanDecomposition.toJordanDecomposition_toSignedMeasure]
  simp [j]

/-- Finite variation on every actual bounded radial window is proved from
the constructed density and atom. -/
instance gluingCollarRadialCurvatureMeasureOnWindow_totalVariation_isFinite
    (r R : ℝ) :
    IsFiniteMeasure (gluingCollarRadialCurvatureMeasureOnWindow r R).totalVariation := by
  rw [gluingCollarRadialCurvatureMeasureOnWindow_totalVariation]
  infer_instance

/-- Bounded native collar windows have an exact finite radial curvature
variation, including the seam contribution. -/
theorem gluingCollarRadialCurvatureMeasureOnWindow_totalVariation_univ
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    (gluingCollarRadialCurvatureMeasureOnWindow r R).totalVariation univ =
      ENNReal.ofReal (2 * Real.cosh (r + R)) := by
  rw [gluingCollarRadialCurvatureMeasureOnWindow_totalVariation]
  simpa only [Measure.restrict_apply_univ] using
    gluingCollarRadialSecondDerivativeMeasure_Icc hr hR

#print axioms gluingCollarRadialSecondDerivativeMeasure_isLocallyFinite
#print axioms gluingCollarRadialSecondDerivativeMeasure_regular
#print axioms gluingCollarRadialSecondDerivativeMeasure_Icc
#print axioms gluingCollarRadialSecondDerivativeMeasure_weak_second_derivative_Icc
#print axioms gluingCollarRadialSecondDerivativeMeasure_weak_second_derivative
#print axioms gluingCollarRadialCurvatureMeasureOnWindow_totalVariation
#print axioms gluingCollarRadialCurvatureMeasureOnWindow_totalVariation_univ
#print axioms gluingCollarRadialCurvatureMeasureOnWindow_singleton_zero

end SystolicGrowth
