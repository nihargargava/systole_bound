module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.HyperbolicArea
public import Vendored.RiemannDynamics.Hyperbolic.DiskModel.DiskMetric
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# Exact hyperbolic area through the actual Cayley coordinates

The Cayley change of variables is proved for Mathlib's original upper-half-plane
measure. Its real Jacobian and the transformation of the original imaginary-part
density are computed explicitly, rather than supplied as measure data.
-/

open MeasureTheory Set Metric UpperHalfPlane
open scoped ENNReal NNReal UpperHalfPlane

namespace SystolicGrowth

noncomputable section

open Vendored.RiemannDynamics

/-- The actual real derivative of the Cayley map. -/
def cayleyAreaFDeriv (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.toSpanSingleton ℂ (2 * Complex.I / (1 - z) ^ 2)).restrictScalars ℝ

theorem cayleyToHalfPlane_hasDerivAt {z : ℂ} (hz : 1 - z ≠ 0) :
    HasDerivAt cayleyToHalfPlane (2 * Complex.I / (1 - z) ^ 2) z := by
  have h := (((hasDerivAt_id z).const_add 1).const_mul Complex.I).div
    ((hasDerivAt_id z).const_sub 1) hz
  change HasDerivAt (fun w : ℂ => Complex.I * (1 + w) / (1 - w))
    ((Complex.I * 1 * (1 - z) - Complex.I * (1 + z) * -1) / (1 - z) ^ 2) z at h
  convert h using 1
  congr 1
  ring

theorem cayleyToHalfPlane_hasFDerivAt {z : ℂ} (hz : 1 - z ≠ 0) :
    HasFDerivAt cayleyToHalfPlane (cayleyAreaFDeriv z) z :=
  (cayleyToHalfPlane_hasDerivAt hz).hasFDerivAt.restrictScalars ℝ

theorem cayleyAreaFDeriv_det (z : ℂ) :
    (cayleyAreaFDeriv z).det = 4 / ‖1 - z‖ ^ 4 := by
  simp [cayleyAreaFDeriv, ContinuousLinearMap.det, LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq, ← pow_mul]
  norm_num

/-- Cancellation of the actual Cayley Jacobian with the original `y⁻²` density. -/
theorem cayleyArea_density {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ENNReal.ofReal |(cayleyAreaFDeriv z).det| *
        (↑((1 / ‖(cayleyToHalfPlane z).im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (4 / (1 - ‖z‖ ^ 2) ^ 2) := by
  have him := cayleyToHalfPlane_im_pos hz
  have hn : ‖1 - z‖ ≠ 0 := norm_ne_zero_iff.mpr (one_sub_ne_zero_of_mem_ball hz)
  have hzsq : 1 - ‖z‖ ^ 2 ≠ 0 := by
    have hz' : ‖z‖ < 1 := by simpa using hz
    nlinarith [norm_nonneg z]
  rw [cayleyAreaFDeriv_det, abs_of_nonneg (by positivity)]
  rw [← ENNReal.ofReal_coe_nnreal]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one,
    coe_nnnorm, Real.norm_eq_abs]
  rw [abs_of_pos him, cayleyToHalfPlane_im]
  field_simp

/-- Genuine density change of variables on every measurable subset of the
original unit disk. -/
theorem lintegral_cayleyToHalfPlane_image {s : Set ℂ}
    (hs : MeasurableSet s) (hsub : s ⊆ ball (0 : ℂ) 1) :
    (∫⁻ w : ℂ in cayleyToHalfPlane '' s,
      (↑((1 / ‖w.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) =
      ∫⁻ z : ℂ in s, ENNReal.ofReal (4 / (1 - ‖z‖ ^ 2) ^ 2) := by
  have hinj : InjOn cayleyToHalfPlane s := by
    intro z hz w hw heq
    have h := congrArg halfPlaneToCayley heq
    simpa only [halfPlaneToCayley_cayleyToHalfPlane (hsub hz),
      halfPlaneToCayley_cayleyToHalfPlane (hsub hw)] using h
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun z hz => (cayleyToHalfPlane_hasFDerivAt
      (one_sub_ne_zero_of_mem_ball (hsub hz))).hasFDerivWithinAt) hinj]
  exact setLIntegral_congr_fun hs fun z hz => cayleyArea_density (hsub hz)

/-- The original upper-half-plane subset corresponding to a Cayley-disk set. -/
def hyperbolicCayleyImage (s : Set ℂ) : Set ℍ :=
  {τ | halfPlaneToCayley τ ∈ s}

theorem coe_image_hyperbolicCayleyImage {s : Set ℂ}
    (hsub : s ⊆ ball (0 : ℂ) 1) :
    UpperHalfPlane.coe '' hyperbolicCayleyImage s = cayleyToHalfPlane '' s := by
  ext w
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨halfPlaneToCayley τ, hτ,
      cayleyToHalfPlane_halfPlaneToCayley τ.im_pos⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨diskToHalfPlane (hsub hz), ?_, rfl⟩
    change halfPlaneToCayley (cayleyToHalfPlane z) ∈ s
    rwa [halfPlaneToCayley_cayleyToHalfPlane (hsub hz)]

/-- Actual hyperbolic area equals the derived disk-coordinate area integral. -/
theorem volume_hyperbolicCayleyImage {s : Set ℂ}
    (hs : MeasurableSet s) (hsub : s ⊆ ball (0 : ℂ) 1) :
    volume (hyperbolicCayleyImage s) =
      ∫⁻ z : ℂ in s, ENNReal.ofReal (4 / (1 - ‖z‖ ^ 2) ^ 2) := by
  rw [UpperHalfPlane.volume_eq_lintegral, coe_image_hyperbolicCayleyImage hsub]
  exact lintegral_cayleyToHalfPlane_image hs hsub

/-- Polar integration on an actual Euclidean disk, using Mathlib's proved
Jacobian theorem. -/
theorem lintegral_disk_radial (ρ : ℝ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z : ℂ in ball (0 : ℂ) ρ, f ‖z‖) =
      ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ u : ℝ in Ioo 0 ρ, ENNReal.ofReal u * f u := by
  rw [← lintegral_indicator measurableSet_ball,
    ← Complex.lintegral_comp_polarCoord_symm]
  have hpolar :
      (∫⁻ p : ℝ × ℝ in polarCoord.target,
        ENNReal.ofReal p.1 •
          (ball (0 : ℂ) ρ).indicator (fun z : ℂ => f ‖z‖)
            (Complex.polarCoord.symm p)) =
        ∫⁻ p : ℝ × ℝ in Ioo 0 ρ ×ˢ Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal p.1 * f p.1 := by
    simp only [polarCoord_target]
    rw [← lintegral_indicator (measurableSet_Ioi.prod measurableSet_Ioo),
      ← lintegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
    apply lintegral_congr
    intro p
    by_cases hp : 0 < p.1
    · have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
        rw [Complex.norm_polarCoord_symm, abs_of_pos hp]
      have hind : (ball (0 : ℂ) ρ).indicator (fun z : ℂ => f ‖z‖)
          (Complex.polarCoord.symm p) = if p.1 < ρ then f p.1 else 0 := by
        by_cases hρ : p.1 < ρ
        · rw [indicator_of_mem (show Complex.polarCoord.symm p ∈ ball (0 : ℂ) ρ by
              rwa [Metric.mem_ball, dist_zero_right, hn]), hn, if_pos hρ]
        · rw [indicator_of_notMem (show Complex.polarCoord.symm p ∉ ball (0 : ℂ) ρ by
              rwa [Metric.mem_ball, dist_zero_right, hn]), if_neg hρ]
      simp only [Set.indicator_apply]
      rw [hind]
      by_cases hangle : p.2 ∈ Ioo (-Real.pi) Real.pi <;>
        by_cases hρ : p.1 < ρ <;>
        simp only [mem_prod, mem_Ioi, mem_Ioo] at hangle ⊢ <;>
        simp [hp, hangle, hρ, smul_eq_mul]
    · simp [hp]
  rw [hpolar]
  change (∫⁻ p : ℝ × ℝ in Ioo 0 ρ ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal p.1 * f p.1 ∂volume.prod volume) = _
  rw [setLIntegral_prod _ (by fun_prop)]
  simp only [setLIntegral_const, Real.volume_Ioo]
  rw [show Real.pi - -Real.pi = 2 * Real.pi by ring,
    lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]

/-- The derived radial area density has a literal elementary antiderivative. -/
theorem diskAreaRadial_hasDerivAt {u : ℝ} (hu : 1 - u ^ 2 ≠ 0) :
    HasDerivAt (fun v : ℝ => 2 / (1 - v ^ 2)) (4 * u / (1 - u ^ 2) ^ 2) u := by
  have h := (hasDerivAt_const u (2 : ℝ)).div
    (((hasDerivAt_id u).pow 2).const_sub 1) hu
  simp only [id_eq, Pi.pow_apply] at h
  norm_num at h
  convert h using 1
  all_goals first | rfl | ring

theorem diskAreaRadial_integral {ρ : ℝ} (hρ : 0 < ρ) (hρone : ρ < 1) :
    (∫ u : ℝ in (0 : ℝ)..ρ, 4 * u / (1 - u ^ 2) ^ 2) =
      2 / (1 - ρ ^ 2) - 2 := by
  have hden : ∀ u ∈ Icc 0 ρ, 1 - u ^ 2 ≠ 0 := by
    intro u hu
    have huone : u < 1 := hu.2.trans_lt hρone
    nlinarith [hu.1]
  have hcont : ContinuousOn (fun u : ℝ => 4 * u / (1 - u ^ 2) ^ 2) (Icc 0 ρ) := by
    exact (continuous_const.mul continuous_id).continuousOn.div
      ((continuous_const.sub (continuous_id.pow 2)).continuousOn.pow 2)
      (fun u hu => pow_ne_zero 2 (hden u hu))
  have hint : IntervalIntegrable (fun u : ℝ => 4 * u / (1 - u ^ 2) ^ 2) volume 0 ρ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hρ.le).mpr hcont.integrableOn_Icc
  have hderiv : ∀ u ∈ uIcc 0 ρ,
      HasDerivAt (fun v : ℝ => 2 / (1 - v ^ 2)) (4 * u / (1 - u ^ 2) ^ 2) u := by
    rw [uIcc_of_le hρ.le]
    intro u hu
    exact diskAreaRadial_hasDerivAt (hden u hu)
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- Exact integral of the derived Cayley area density on a genuine disk. -/
theorem lintegral_diskAreaDensity {ρ : ℝ} (hρ : 0 < ρ) (hρone : ρ < 1) :
    (∫⁻ z : ℂ in ball (0 : ℂ) ρ, ENNReal.ofReal (4 / (1 - ‖z‖ ^ 2) ^ 2)) =
      ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (2 / (1 - ρ ^ 2) - 2) := by
  rw [lintegral_disk_radial ρ (fun u : ℝ => ENNReal.ofReal (4 / (1 - u ^ 2) ^ 2))
    (by fun_prop)]
  congr 1
  have hden : ∀ u ∈ Icc 0 ρ, 1 - u ^ 2 ≠ 0 := by
    intro u hu
    have huone : u < 1 := hu.2.trans_lt hρone
    nlinarith [hu.1]
  have hcont : ContinuousOn (fun u : ℝ => 4 * u / (1 - u ^ 2) ^ 2) (Icc 0 ρ) := by
    exact (continuous_const.mul continuous_id).continuousOn.div
      ((continuous_const.sub (continuous_id.pow 2)).continuousOn.pow 2)
      (fun u hu => pow_ne_zero 2 (hden u hu))
  have hint : IntegrableOn (fun u : ℝ => 4 * u / (1 - u ^ 2) ^ 2) (Ioo 0 ρ) volume :=
    hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo 0 ρ)]
      (fun u : ℝ => 4 * u / (1 - u ^ 2) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact div_nonneg (mul_nonneg (by norm_num) hu.1.le) (sq_nonneg _)
  calc
    (∫⁻ u : ℝ in Ioo 0 ρ,
        ENNReal.ofReal u * ENNReal.ofReal (4 / (1 - u ^ 2) ^ 2)) =
        ∫⁻ u : ℝ in Ioo 0 ρ, ENNReal.ofReal (4 * u / (1 - u ^ 2) ^ 2) := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro u hu
      dsimp only
      rw [← ENNReal.ofReal_mul hu.1.le]
      congr 1
      ring
    _ = ENNReal.ofReal (∫ u : ℝ in Ioo 0 ρ, 4 * u / (1 - u ^ 2) ^ 2) :=
      (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    _ = ENNReal.ofReal (2 / (1 - ρ ^ 2) - 2) := by
      rw [← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le hρ.le, diskAreaRadial_integral hρ hρone]

/-- The disk coordinate reads the original hyperbolic distance to `I`. -/
theorem norm_halfPlaneToCayley_eq_tanh_half_dist (τ : ℍ) :
    ‖halfPlaneToCayley τ‖ = Real.tanh (dist (I : ℍ) τ / 2) := by
  rw [halfPlaneToCayley, norm_div, dist_comm (I : ℍ) τ, UpperHalfPlane.tanh_half_dist]
  simp only [Complex.dist_eq, UpperHalfPlane.coe_I, Complex.conj_I, sub_neg_eq_add]

/-- Original hyperbolic balls are exactly the inverse Cayley images of their
actual Euclidean radial disks. -/
theorem hyperbolicCayleyImage_ball (R : ℝ) :
    hyperbolicCayleyImage (ball (0 : ℂ) (Real.tanh (R / 2))) = ball (I : ℍ) R := by
  ext τ
  simp only [hyperbolicCayleyImage, mem_setOf_eq, Metric.mem_ball,
    dist_zero_right, norm_halfPlaneToCayley_eq_tanh_half_dist, dist_comm τ (I : ℍ)]
  have h := Real.artanh_lt_artanh_iff
    (mem_Ioo.mpr ⟨Real.neg_one_lt_tanh (dist (I : ℍ) τ / 2),
      Real.tanh_lt_one (dist (I : ℍ) τ / 2)⟩)
    (mem_Ioo.mpr ⟨Real.neg_one_lt_tanh (R / 2), Real.tanh_lt_one (R / 2)⟩)
  rw [Real.artanh_tanh, Real.artanh_tanh] at h
  rw [← h]
  exact div_lt_div_iff_of_pos_right (by norm_num)

/-- The elementary disk radial antiderivative becomes the hyperbolic radial
area factor under the actual `tanh(R/2)` coordinate. -/
theorem diskAreaRadial_tanh_half (R : ℝ) :
    2 / (1 - Real.tanh (R / 2) ^ 2) - 2 = Real.cosh R - 1 := by
  have hc : Real.cosh (R / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have hid := Real.cosh_sq_sub_sinh_sq (R / 2)
  have hdouble := Real.cosh_two_mul (R / 2)
  rw [show 2 * (R / 2) = R by ring] at hdouble
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  nlinarith

/-- Exact area of the original positive-radius hyperbolic metric ball. -/
theorem volume_hyperbolic_ball_exact (o : ℍ) {R : ℝ} (hR : 0 < R) :
    volume (ball o R) = ENNReal.ofReal (2 * Real.pi * (Real.cosh R - 1)) := by
  rw [volume_ball_eq_volume_ball_I o R, ← hyperbolicCayleyImage_ball R]
  have hρ : 0 < Real.tanh (R / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
  have hρone := Real.tanh_lt_one (R / 2)
  rw [volume_hyperbolicCayleyImage measurableSet_ball (ball_subset_ball hρone.le),
    lintegral_diskAreaDensity hρ hρone, diskAreaRadial_tanh_half,
    ← ENNReal.ofReal_mul Real.two_pi_pos.le]

#print axioms cayleyToHalfPlane_hasFDerivAt
#print axioms volume_hyperbolicCayleyImage
#print axioms volume_hyperbolic_ball_exact

end

end SystolicGrowth
