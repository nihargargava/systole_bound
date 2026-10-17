module

public import Geometry.HyperbolicArea
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

open MeasureTheory Set
open scoped ENNReal UpperHalfPlane

namespace SystolicGrowth

/-! # An elementary upper bound for hyperbolic ball area

Splitting the Euclidean disk at height `exp (-r / 3)` gives two vertical
strips. Integrating the hyperbolic density on the strips avoids the exact
disk-area formula and gives an exponential rate sufficient for choosing
the two gluing centers.
-/

private theorem lintegral_inv_sq_Ioi {a : ℝ} (ha : 0 < a) :
    (∫⁻ y : ℝ in Ioi a, ENNReal.ofReal (1 / y ^ 2)) = ENNReal.ofReal (1 / a) := by
  have heq : (∫⁻ y : ℝ in Ioi a, ENNReal.ofReal (1 / y ^ 2)) =
      ∫⁻ y : ℝ in Ioi a, ENNReal.ofReal (y ^ (-2 : ℝ)) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp only
    rw [Real.rpow_neg (ha.trans hy).le, Real.rpow_two, one_div]
  rw [heq, ← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha)]
  · rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha]
    norm_num [Real.rpow_neg_one, one_div]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact Real.rpow_nonneg (ha.trans hy).le _

noncomputable def Internal.HyperbolicBallUpperVolumeHelpers.upperStrip (w a : ℝ) : Set ℂ :=
  Complex.measurableEquivRealProd ⁻¹' (Ioo (-w) w ×ˢ Ioi a)

private theorem measurableSet_upperStrip (w a : ℝ) : MeasurableSet (Internal.HyperbolicBallUpperVolumeHelpers.upperStrip w a) :=
  (measurableSet_Ioo.prod measurableSet_Ioi).preimage
    Complex.measurableEquivRealProd.measurable

private theorem density_lintegral_upperStrip {w a : ℝ} (_hw : 0 ≤ w) (ha : 0 < a) :
    (∫⁻ z : ℂ in Internal.HyperbolicBallUpperVolumeHelpers.upperStrip w a, ↑((1 / ‖z.im‖₊) ^ 2 : NNReal)) =
      ENNReal.ofReal (2 * w / a) := by
  have hmeas : Measurable (fun p : ℝ × ℝ ↦ ENNReal.ofReal (1 / p.2 ^ 2)) := by
    fun_prop
  have hpoint : (fun z : ℂ ↦ ↑((1 / ‖z.im‖₊) ^ 2 : NNReal)) =
      (fun p : ℝ × ℝ ↦ ENNReal.ofReal (1 / p.2 ^ 2)) ∘
        Complex.measurableEquivRealProd := by
    funext z
    simp only [Function.comp_apply, Complex.measurableEquivRealProd_apply]
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    simp [sq_abs]
  rw [hpoint, Internal.HyperbolicBallUpperVolumeHelpers.upperStrip]
  simp only [Function.comp_def]
  rw [
    Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage
      (measurableSet_Ioo.prod measurableSet_Ioi) hmeas, Measure.volume_eq_prod,
    setLIntegral_prod _ hmeas.aemeasurable]
  dsimp only
  rw [lintegral_inv_sq_Ioi ha, setLIntegral_const, Real.volume_Ioo]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / a)]
  congr 1
  ring

private theorem ball_I_subset_upperStrips {r : ℝ} (hr : 0 ≤ r) :
    Metric.ball ((UpperHalfPlane.I : ℍ).center r : ℂ) (Real.sinh r) ⊆
      Internal.HyperbolicBallUpperVolumeHelpers.upperStrip (2 * Real.exp (r / 3)) (Real.exp (-r)) ∪
        Internal.HyperbolicBallUpperVolumeHelpers.upperStrip (Real.exp r) (Real.exp (-r / 3)) := by
  intro z hz
  have hnorm : ‖z - ((UpperHalfPlane.I : ℍ).center r : ℂ)‖ < Real.sinh r :=
    by simpa only [dist_eq_norm] using Metric.mem_ball.mp hz
  have hre : |z.re| < Real.sinh r := by
    simpa using (Complex.abs_re_le_norm
      (z - ((UpperHalfPlane.I : ℍ).center r : ℂ))).trans_lt hnorm
  have him : |z.im - Real.cosh r| < Real.sinh r := by
    simpa using (Complex.abs_im_le_norm
      (z - ((UpperHalfPlane.I : ℍ).center r : ℂ))).trans_lt hnorm
  have hbottom : Real.exp (-r) < z.im := by
    have hlo := (abs_lt.mp him).1
    linarith [Real.cosh_sub_sinh r]
  have hsinh : Real.sinh r ≤ Real.exp r := by
    rw [Real.sinh_eq]
    linarith [Real.exp_pos r, Real.exp_pos (-r)]
  have hcosh : Real.cosh r ≤ Real.exp r := by
    rw [Real.cosh_eq]
    have := Real.exp_le_exp.mpr (show -r ≤ r by linarith)
    linarith
  by_cases ht : z.im ≤ Real.exp (-r / 3)
  · apply Or.inl
    have hsq : z.re ^ 2 + (z.im - Real.cosh r) ^ 2 < Real.sinh r ^ 2 := by
      have h := (sq_lt_sq₀ (norm_nonneg _)
        (Real.sinh_nonneg_iff.mpr hr)).mpr hnorm
      rw [Complex.sq_norm] at h
      simpa [Complex.normSq_apply, pow_two] using h
    have hx : z.re ^ 2 < 2 * Real.cosh r * z.im := by
      nlinarith [sq_nonneg z.im, Real.cosh_sq r]
    have hprod : Real.exp r * Real.exp (-r / 3) = Real.exp (r / 3) ^ 2 := by
      rw [← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      ring
    have hupper : 2 * Real.cosh r * z.im ≤ 2 * Real.exp (r / 3) ^ 2 := by
      calc
        2 * Real.cosh r * z.im ≤ 2 * Real.exp r * z.im :=
          mul_le_mul_of_nonneg_right (by linarith) ((Real.exp_pos (-r)).trans hbottom).le
        _ ≤ 2 * Real.exp r * Real.exp (-r / 3) :=
          mul_le_mul_of_nonneg_left ht (by positivity)
        _ = 2 * Real.exp (r / 3) ^ 2 := by rw [mul_assoc, hprod]
    have habs : |z.re| < 2 * Real.exp (r / 3) := by
      apply (sq_lt_sq₀ (abs_nonneg _) (by positivity)).mp
      rw [sq_abs]
      nlinarith [Real.exp_pos (r / 3)]
    exact ⟨abs_lt.mp habs, hbottom⟩
  · apply Or.inr
    exact ⟨abs_lt.mp (hre.trans_le hsinh), lt_of_not_ge ht⟩

/-- A coarse explicit ball-area upper bound. Its exponent `4/3` is
strictly below `3/2`, which suffices at the gluing separation scale
`D / log g → 2/3`; no exact disk-area formula is required. -/
theorem volume_ball_le_ofReal_six_mul_exp_four_thirds (o : ℍ) {r : ℝ}
    (hr : 0 ≤ r) :
    volume (Metric.ball o r) ≤ ENNReal.ofReal (6 * Real.exp (4 * r / 3)) := by
  rw [volume_ball_eq_volume_ball_I, UpperHalfPlane.volume_eq_lintegral,
    UpperHalfPlane.image_coe_ball]
  simp only [UpperHalfPlane.I_im, one_mul]
  calc
    _ ≤ ∫⁻ z : ℂ in Internal.HyperbolicBallUpperVolumeHelpers.upperStrip (2 * Real.exp (r / 3)) (Real.exp (-r)) ∪
        Internal.HyperbolicBallUpperVolumeHelpers.upperStrip (Real.exp r) (Real.exp (-r / 3)),
        ↑((1 / ‖z.im‖₊) ^ 2 : NNReal) :=
      lintegral_mono_set (ball_I_subset_upperStrips hr)
    _ ≤ (∫⁻ z : ℂ in Internal.HyperbolicBallUpperVolumeHelpers.upperStrip (2 * Real.exp (r / 3)) (Real.exp (-r)),
        ↑((1 / ‖z.im‖₊) ^ 2 : NNReal)) +
        ∫⁻ z : ℂ in Internal.HyperbolicBallUpperVolumeHelpers.upperStrip (Real.exp r) (Real.exp (-r / 3)),
          ↑((1 / ‖z.im‖₊) ^ 2 : NNReal) := lintegral_union_le _ _ _
    _ = ENNReal.ofReal (6 * Real.exp (4 * r / 3)) := by
      rw [density_lintegral_upperStrip (by positivity) (Real.exp_pos _),
        density_lintegral_upperStrip (by positivity) (Real.exp_pos _),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      simp only [mul_div_assoc]
      have h₁ : Real.exp (r / 3) / Real.exp (-r) = Real.exp (4 * r / 3) := by
        rw [← Real.exp_sub]
        congr 1
        ring
      have h₂ : Real.exp r / Real.exp (-r / 3) = Real.exp (4 * r / 3) := by
        rw [← Real.exp_sub]
        congr 1
        ring
      rw [h₁, h₂]
      ring_nf

#print axioms volume_ball_le_ofReal_six_mul_exp_four_thirds

end SystolicGrowth
