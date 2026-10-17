module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarSmoothWarp
public import Geometry.GluingCollarCurvatureMeasure
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-!
# Weak curvature convergence for the actual smooth collar approximations

The smooth second derivatives pair by integration by parts. Uniform warp
approximation gives an explicit compact-test error bound and convergence to
the original radial curvature measure, including its seam atom.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SystolicGrowth

/-- **Math.** The literal smooth warp pairs with every compact C² test by
the genuine second derivative. Both integrations by parts are justified. -/
theorem gluingCollarSmoothWarp_weak_second_derivative
    (r : ℝ) {ε : ℝ} (hε : 0 < ε) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupport : HasCompactSupport φ) :
    (∫ s, gluingCollarSmoothWarp r ε s * deriv (deriv φ) s) =
      ∫ s, deriv (deriv (gluingCollarSmoothWarp r ε)) s * φ s := by
  let F := gluingCollarSmoothWarp r ε
  have hF : ContDiff ℝ 2 F := gluingCollarSmoothWarp_contDiff r hε 2
  have hF' : ContDiff ℝ 1 (deriv F) := hF.deriv'
  have hφ' : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have h1 := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := F) (u' := deriv F) (v := deriv φ) (v' := deriv (deriv φ))
    (fun s _ => (hF.differentiable (by norm_num) s).hasDerivAt)
    (fun s _ => (hφ.differentiable_deriv_two s).hasDerivAt)
    ((hF.continuous.mul hφ'.continuous_deriv_one).integrable_of_hasCompactSupport
      hsupport.deriv.deriv.mul_left)
    ((hF'.continuous.mul hφ'.continuous).integrable_of_hasCompactSupport
      hsupport.deriv.mul_left)
    ((hF.continuous.mul hφ'.continuous).integrable_of_hasCompactSupport
      hsupport.deriv.mul_left)
  have h2 := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := deriv F) (u' := deriv (deriv F)) (v := φ) (v' := deriv φ)
    (fun s _ => (hF.differentiable_deriv_two s).hasDerivAt)
    (fun s _ => (hφ.differentiable (by norm_num) s).hasDerivAt)
    ((hF'.continuous.mul hφ'.continuous).integrable_of_hasCompactSupport
      hsupport.deriv.mul_left)
    ((hF'.continuous_deriv_one.mul hφ.continuous).integrable_of_hasCompactSupport
      hsupport.mul_left)
    ((hF'.continuous.mul hφ.continuous).integrable_of_hasCompactSupport
      hsupport.mul_left)
  dsimp only [F] at h1 h2
  rw [h1, h2, neg_neg]

/-- **Math.** The smooth weak second-derivative pairing differs from the
actual native curvature measure by at most an explicit vanishing error. -/
theorem gluingCollarSmoothWarp_curvature_pairing_error
    {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupport : HasCompactSupport φ) :
    |(∫ s, gluingCollarSmoothWarp r ε s * deriv (deriv φ) s) -
        (∫ s, φ s ∂gluingCollarRadialSecondDerivativeMeasure r)| ≤
      Real.cosh r * ε * ∫ s, |deriv (deriv φ) s| := by
  have hφ'' : Continuous (deriv (deriv φ)) := hφ.deriv'.continuous_deriv_one
  have hFs : Continuous (gluingCollarSmoothWarp r ε) := by
    unfold gluingCollarSmoothWarp
    fun_prop
  have hI : Integrable (fun s : ℝ => gluingCollarSmoothWarp r ε s * deriv (deriv φ) s) :=
    (hFs.mul hφ'').integrable_of_hasCompactSupport hsupport.deriv.deriv.mul_left
  have hJ : Integrable (fun s : ℝ => gluingCollarWarp r s * deriv (deriv φ) s) :=
    ((gluingCollarWarp_continuous r).mul hφ'').integrable_of_hasCompactSupport
      hsupport.deriv.deriv.mul_left
  have hAbs : Integrable (fun s : ℝ => |deriv (deriv φ) s|) :=
    hφ''.abs.integrable_of_hasCompactSupport hsupport.deriv.deriv.abs
  rw [gluingCollarRadialSecondDerivativeMeasure_weak_second_derivative hr hφ hsupport,
    ← integral_sub hI hJ]
  calc
    _ ≤ ∫ s, |gluingCollarSmoothWarp r ε s * deriv (deriv φ) s -
        gluingCollarWarp r s * deriv (deriv φ) s| := abs_integral_le_integral_abs
    _ ≤ ∫ s, (Real.cosh r * ε) * |deriv (deriv φ) s| := by
      apply integral_mono (hI.sub hJ).abs (hAbs.const_mul _)
      intro s
      dsimp only [Pi.sub_apply]
      rw [← sub_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (gluingCollarSmoothWarp_uniform_bound r hε s) (abs_nonneg _)
    _ = _ := integral_const_mul _ _

/-- **Math.** The genuine smooth second-derivative distributions converge
to the native seam-containing measure against every compact C² test. -/
theorem gluingCollarSmoothWarp_curvature_pairing_tendsto
    {r : ℝ} (hr : 0 < r) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupport : HasCompactSupport φ) :
    Tendsto (fun ε : ℝ => ∫ s, deriv (deriv (gluingCollarSmoothWarp r ε)) s * φ s)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ s, φ s ∂gluingCollarRadialSecondDerivativeMeasure r)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ‖(∫ s, deriv (deriv (gluingCollarSmoothWarp r ε)) s * φ s) -
        (∫ s, φ s ∂gluingCollarRadialSecondDerivativeMeasure r)‖ ≤
      Real.cosh r * ε * ∫ s, |deriv (deriv φ) s| := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [← gluingCollarSmoothWarp_weak_second_derivative r hε hφ hsupport,
      Real.norm_eq_abs]
    exact gluingCollarSmoothWarp_curvature_pairing_error hr hε.le hφ hsupport
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound
  have hlim : Tendsto
      (fun ε : ℝ => Real.cosh r * ε * ∫ s, |deriv (deriv φ) s|)
      (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hc : Continuous (fun ε : ℝ => Real.cosh r * ε * ∫ s, |deriv (deriv φ) s|) := by
      fun_prop
    simpa using hc.tendsto 0
  exact hlim.mono_left nhdsWithin_le_nhds

/-- The actual smooth radial second-derivative measure. Its positivity in
the required approximation range follows from the proved curvature defect. -/
noncomputable def gluingCollarSmoothRadialSecondDerivativeMeasure (r ε : ℝ) : Measure ℝ :=
  volume.withDensity (fun s => ENNReal.ofReal
    (deriv (deriv (gluingCollarSmoothWarp r ε)) s))

theorem gluingCollarSmoothWarp_second_deriv_pos {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hε1 : ε ≤ 1) (s : ℝ) :
    0 < deriv (deriv (gluingCollarSmoothWarp r ε)) s := by
  have h := gluingCollarSmoothWarp_second_deriv_sub_nonneg r hε hε1 s
  linarith [gluingCollarSmoothWarp_pos hr ε s]

instance gluingCollarSmoothRadialSecondDerivativeMeasure_isLocallyFinite
    (r : ℝ) {ε : ℝ} [hε : Fact (0 < ε)] :
    IsLocallyFiniteMeasure (gluingCollarSmoothRadialSecondDerivativeMeasure r ε) := by
  exact IsLocallyFiniteMeasure.withDensity_ofReal
    (gluingCollarSmoothWarp_contDiff r hε.out 2).deriv'.continuous_deriv_one

/-- **Math.** The positive smooth measures have exactly the proved weak
second-derivative pairings, rather than an assigned curvature premise. -/
theorem gluingCollarSmoothRadialSecondDerivativeMeasure_pairing
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (hε1 : ε ≤ 1) {φ : ℝ → ℝ} :
    (∫ s, φ s ∂gluingCollarSmoothRadialSecondDerivativeMeasure r ε) =
      ∫ s, deriv (deriv (gluingCollarSmoothWarp r ε)) s * φ s := by
  rw [gluingCollarSmoothRadialSecondDerivativeMeasure,
    integral_withDensity_eq_integral_toReal_smul
      ((gluingCollarSmoothWarp_contDiff r hε 2).deriv'.continuous_deriv_one.measurable.ennreal_ofReal)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (gluingCollarSmoothWarp_second_deriv_pos hr hε hε1 _).le,
    smul_eq_mul]

theorem gluingCollarSmoothWarp_deriv_neg (r : ℝ) {ε : ℝ}
    (hε : 0 < ε) (s : ℝ) :
    deriv (gluingCollarSmoothWarp r ε) (-s) =
      -deriv (gluingCollarSmoothWarp r ε) s := by
  rw [gluingCollarSmoothWarp_deriv r hε, gluingCollarSmoothWarp_deriv r hε]
  simp only [Real.sinh_neg, Real.cosh_neg, neg_sq]
  ring

/-- The approximating derivative is bounded by the unchanged one-sided
native derivative throughout every positive radial window. -/
theorem gluingCollarSmoothWarp_deriv_le_native {r ε s : ℝ}
    (hε : 0 < ε) (hs : 0 ≤ s) :
    deriv (gluingCollarSmoothWarp r ε) s ≤ Real.cosh (r + s) := by
  have hroot : 0 < Real.sqrt (Real.sinh s ^ 2 + ε ^ 2) := by
    apply Real.sqrt_pos.mpr
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)
  have hsinh : 0 ≤ Real.sinh s := Real.sinh_nonneg_iff.mpr hs
  have hlo : Real.sinh s ≤ Real.sqrt (Real.sinh s ^ 2 + ε ^ 2) := by
    have h := Real.sqrt_le_sqrt
      (le_add_of_nonneg_right (a := Real.sinh s ^ 2) (sq_nonneg ε))
    rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg hsinh] at h
  have hratio : Real.sinh s / Real.sqrt (Real.sinh s ^ 2 + ε ^ 2) ≤ 1 :=
    (div_le_one hroot).mpr hlo
  have hterm : Real.sinh s * Real.cosh s / Real.sqrt (Real.sinh s ^ 2 + ε ^ 2) ≤
      Real.cosh s := by
    calc
      _ = (Real.sinh s / Real.sqrt (Real.sinh s ^ 2 + ε ^ 2)) * Real.cosh s := by ring
      _ ≤ 1 * Real.cosh s := mul_le_mul_of_nonneg_right hratio (Real.cosh_pos s).le
      _ = _ := one_mul _
  rw [gluingCollarSmoothWarp_deriv r hε, Real.cosh_add]
  have h := mul_le_mul_of_nonneg_left hterm (Real.cosh_pos r).le
  nlinarith

/-- **Math.** Smooth curvature on the genuine bounded radial window has
exact mass given by the actual endpoint derivative, with no mass premise. -/
theorem gluingCollarSmoothRadialSecondDerivativeMeasure_Icc
    {r ε R : ℝ} (hr : 0 < r) (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R) :
    gluingCollarSmoothRadialSecondDerivativeMeasure r ε (Icc (-R) R) =
      ENNReal.ofReal (2 * deriv (gluingCollarSmoothWarp r ε) R) := by
  have hF := gluingCollarSmoothWarp_contDiff r hε 2
  have hF' : ContDiff ℝ 1 (deriv (gluingCollarSmoothWarp r ε)) := hF.deriv'
  have hF'' := hF'.continuous_deriv_one
  have hFTC : (∫ s in -R..R, deriv (deriv (gluingCollarSmoothWarp r ε)) s) =
      2 * deriv (gluingCollarSmoothWarp r ε) R := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (show -R ≤ R by linarith) hF'.continuous.continuousOn
      (fun s _ => (hF.differentiable_deriv_two s).hasDerivAt)
      (hF''.intervalIntegrable (-R) R), gluingCollarSmoothWarp_deriv_neg r hε]
    ring
  rw [gluingCollarSmoothRadialSecondDerivativeMeasure, withDensity_apply _ measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal hF''.integrableOn_Icc
      (Eventually.of_forall fun s => (gluingCollarSmoothWarp_second_deriv_pos hr hε hε1 s).le),
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show -R ≤ R by linarith), hFTC]

/-- **Math.** Every actual smooth approximant has radial curvature mass
bounded by the original seam-containing window mass, uniformly in ε. -/
theorem gluingCollarSmoothRadialSecondDerivativeMeasure_Icc_le_native
    {r ε R : ℝ} (hr : 0 < r) (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R) :
    gluingCollarSmoothRadialSecondDerivativeMeasure r ε (Icc (-R) R) ≤
      gluingCollarRadialSecondDerivativeMeasure r (Icc (-R) R) := by
  rw [gluingCollarSmoothRadialSecondDerivativeMeasure_Icc hr hε hε1 hR,
    gluingCollarRadialSecondDerivativeMeasure_Icc hr hR]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left (gluingCollarSmoothWarp_deriv_le_native hε hR.le)
    (by norm_num)

/-- **Math.** The positive smooth curvature measures themselves converge
against every compact C² test; the limit is the original density and atom. -/
theorem gluingCollarSmoothRadialSecondDerivativeMeasure_pairing_tendsto
    {r : ℝ} (hr : 0 < r) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupport : HasCompactSupport φ) :
    Tendsto (fun ε : ℝ => ∫ s, φ s ∂gluingCollarSmoothRadialSecondDerivativeMeasure r ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ s, φ s ∂gluingCollarRadialSecondDerivativeMeasure r)) := by
  apply (gluingCollarSmoothWarp_curvature_pairing_tendsto hr hφ hsupport).congr'
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with ε hε hε1
  exact (gluingCollarSmoothRadialSecondDerivativeMeasure_pairing hr hε hε1.le).symm

#print axioms gluingCollarSmoothWarp_weak_second_derivative
#print axioms gluingCollarSmoothWarp_curvature_pairing_error
#print axioms gluingCollarSmoothWarp_curvature_pairing_tendsto
#print axioms gluingCollarSmoothRadialSecondDerivativeMeasure_pairing
#print axioms gluingCollarSmoothRadialSecondDerivativeMeasure_Icc_le_native
#print axioms gluingCollarSmoothRadialSecondDerivativeMeasure_pairing_tendsto

end SystolicGrowth
