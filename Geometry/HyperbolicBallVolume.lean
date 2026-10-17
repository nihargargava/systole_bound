module

public import Geometry.HyperbolicArea
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

@[expose] public section

open MeasureTheory Set
open scoped ENNReal UpperHalfPlane

namespace SystolicGrowth

/-! ## Quantitative area of hyperbolic balls

This file develops explicit lower bounds for the invariant measure of balls in
the Poincaré upper half-plane.  The estimates are deliberately elementary: a
thin Euclidean rectangle near the bottom of the disk representing a
hyperbolic ball already has area growing exponentially with the radius.
-/

noncomputable def Internal.HyperbolicBallVolumeHelpers.lowerRectangle (r : ℝ) : Set ℂ :=
  Complex.measurableEquivRealProd ⁻¹'
    (Ioo (-(1 / 4 : ℝ)) (1 / 4) ×ˢ
      Ioo ((3 / 2 : ℝ) * Real.exp (-r)) (2 * Real.exp (-r)))

private lemma measurableSet_lowerRectangle (r : ℝ) :
    MeasurableSet (Internal.HyperbolicBallVolumeHelpers.lowerRectangle r) := by
  exact (measurableSet_Ioo.prod measurableSet_Ioo).preimage
    Complex.measurableEquivRealProd.measurable

private lemma volume_lowerRectangle (r : ℝ) :
    volume (Internal.HyperbolicBallVolumeHelpers.lowerRectangle r) = ENNReal.ofReal (Real.exp (-r) / 4) := by
  rw [Internal.HyperbolicBallVolumeHelpers.lowerRectangle,
    Complex.volume_preserving_equiv_real_prod.measure_preimage
      (measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet]
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
    Real.volume_Ioo, Real.volume_Ioo]
  rw [show (1 / 4 : ℝ) - -(1 / 4) = 1 / 2 by norm_num,
    show 2 * Real.exp (-r) - 3 / 2 * Real.exp (-r) = Real.exp (-r) / 2 by ring]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (1 / 2 : ℝ))]
  congr 1
  ring

private lemma lowerRectangle_subset_ball_I {r : ℝ} (hr : Real.log 2 ≤ r) :
    Internal.HyperbolicBallVolumeHelpers.lowerRectangle r ⊆
      Metric.ball ((UpperHalfPlane.I : ℍ).center r : ℂ) (Real.sinh r) := by
  let b := Real.exp (-r)
  have hrpos : 0 < r := (Real.log_pos (by norm_num)).trans_le hr
  have hbpos : 0 < b := by dsimp [b]; positivity
  have hb : b ≤ 1 / 2 := by
    calc
      b = Real.exp (-r) := rfl
      _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (neg_le_neg hr)
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hb_sq : b ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg (b - 1 / 2)]
  have hRpos : 0 < Real.sinh r := Real.sinh_pos_iff.mpr hrpos
  have hprod : Real.exp r * b = 1 := by
    dsimp [b]
    rw [← Real.exp_add]
    simp
  have hRb : Real.sinh r * b = (1 - b ^ 2) / 2 := by
    rw [Real.sinh_eq]
    calc
      (Real.exp r - Real.exp (-r)) / 2 * b =
          (Real.exp r * b - b ^ 2) / 2 := by dsimp [b]; ring
      _ = (1 - b ^ 2) / 2 := by rw [hprod]
  intro w hw
  change (w.re, w.im) ∈
    Ioo (-(1 / 4 : ℝ)) (1 / 4) ×ˢ Ioo (3 / 2 * b) (2 * b) at hw
  rcases hw with ⟨⟨hrelo, hrehi⟩, ⟨himlo, himhi⟩⟩
  have hre_sq : w.re ^ 2 < (1 / 4 : ℝ) ^ 2 := by
    have habs : |w.re| < 1 / 4 := (abs_lt).2 ⟨hrelo, hrehi⟩
    have hs := (sq_lt_sq₀ (abs_nonneg w.re) (by norm_num : (0 : ℝ) ≤ 1 / 4)).2 habs
    simpa [sq_abs] using hs
  let d := w.im - b
  have hdlo : b / 2 < d := by dsimp [d]; linarith
  have hdhi : d < b := by dsimp [d]; linarith
  have hdpos : 0 < d := by linarith
  have hd_sq : d ^ 2 < b ^ 2 :=
    (sq_lt_sq₀ hdpos.le hbpos.le).2 hdhi
  have hleft : w.re ^ 2 + d ^ 2 < 3 / 8 := by nlinarith
  have hright : 3 / 8 ≤ 2 * Real.sinh r * d := by
    have : Real.sinh r * b < 2 * Real.sinh r * d := by nlinarith
    nlinarith [hRb]
  have hcosh : Real.cosh r = Real.sinh r + b := by
    dsimp [b]
    nlinarith [Real.cosh_sub_sinh r]
  have hsq :
      w.re ^ 2 + (w.im - Real.cosh r) ^ 2 < Real.sinh r ^ 2 := by
    dsimp [d] at hleft hright ⊢
    rw [hcosh]
    nlinarith
  rw [Metric.mem_ball, Complex.dist_eq,
    ← sq_lt_sq₀ (norm_nonneg _) hRpos.le, Complex.sq_norm]
  simpa [Complex.normSq_apply, pow_two] using hsq

private lemma density_lower_on_lowerRectangle {r : ℝ} {w : ℂ}
    (hw : w ∈ Internal.HyperbolicBallVolumeHelpers.lowerRectangle r) :
    ENNReal.ofReal (1 / (4 * Real.exp (-r) ^ 2)) ≤
      ↑((1 / ‖w.im‖₊) ^ 2 : NNReal) := by
  let b := Real.exp (-r)
  have hbpos : 0 < b := by dsimp [b]; positivity
  change (w.re, w.im) ∈
    Ioo (-(1 / 4 : ℝ)) (1 / 4) ×ˢ Ioo (3 / 2 * b) (2 * b) at hw
  rcases hw with ⟨_, ⟨himlo, himhi⟩⟩
  have himpos : 0 < w.im := by nlinarith
  have hinv : 1 / (2 * b) ≤ 1 / w.im :=
    one_div_le_one_div_of_le himpos himhi.le
  have hsquare : (1 / (2 * b)) ^ 2 ≤ (1 / w.im) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hinv
  have hreal : 1 / (4 * b ^ 2) ≤ (1 / w.im) ^ 2 := calc
    1 / (4 * b ^ 2) = (1 / (2 * b)) ^ 2 := by field_simp; ring
    _ ≤ (1 / w.im) ^ 2 := hsquare
  rw [ENNReal.ofReal_le_coe]
  norm_cast
  simpa [b, Real.nnnorm_of_nonneg himpos.le] using hreal

private lemma density_mul_volume_lowerRectangle (r : ℝ) :
    ENNReal.ofReal (1 / (4 * Real.exp (-r) ^ 2)) * volume (Internal.HyperbolicBallVolumeHelpers.lowerRectangle r) =
      ENNReal.ofReal (Real.exp r / 16) := by
  rw [volume_lowerRectangle, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.exp_neg]
  field_simp
  ring

/-- A completely explicit exponential lower bound for the hyperbolic area of
a ball.  The constant is not optimal (the exact area is
`2 * π * (cosh r - 1)`), but this elementary estimate is enough to recover
the logarithmic scale of systolic upper bounds. -/
theorem ofReal_exp_div_sixteen_le_volume_ball (z : ℍ) {r : ℝ}
    (hr : Real.log 2 ≤ r) :
    ENNReal.ofReal (Real.exp r / 16) ≤ volume (Metric.ball z r) := by
  rw [volume_ball_eq_volume_ball_I z r, UpperHalfPlane.volume_eq_lintegral,
    UpperHalfPlane.image_coe_ball]
  simp only [UpperHalfPlane.I_im, one_mul]
  calc
    ENNReal.ofReal (Real.exp r / 16) =
        ENNReal.ofReal (1 / (4 * Real.exp (-r) ^ 2)) *
          volume (Internal.HyperbolicBallVolumeHelpers.lowerRectangle r) := (density_mul_volume_lowerRectangle r).symm
    _ = ∫⁻ _w in Internal.HyperbolicBallVolumeHelpers.lowerRectangle r,
          ENNReal.ofReal (1 / (4 * Real.exp (-r) ^ 2)) :=
      (setLIntegral_const (Internal.HyperbolicBallVolumeHelpers.lowerRectangle r) _).symm
    _ ≤ ∫⁻ w in Internal.HyperbolicBallVolumeHelpers.lowerRectangle r, ↑((1 / ‖w.im‖₊) ^ 2 : NNReal) :=
      setLIntegral_mono' (measurableSet_lowerRectangle r)
        fun _w hw ↦ density_lower_on_lowerRectangle hw
    _ ≤ ∫⁻ w in Metric.ball ((UpperHalfPlane.I : ℍ).center r : ℂ)
          (Real.sinh r), ↑((1 / ‖w.im‖₊) ^ 2 : NNReal) :=
      lintegral_mono_set (lowerRectangle_subset_ball_I hr)

/-- Real-valued form of `ofReal_exp_div_sixteen_le_volume_ball`. -/
theorem exp_div_sixteen_le_volume_real_ball (z : ℍ) {r : ℝ}
    (hr : Real.log 2 ≤ r) :
    Real.exp r / 16 ≤ volume.real (Metric.ball z r) := by
  have h := ofReal_exp_div_sixteen_le_volume_ball z hr
  have h' := ENNReal.toReal_mono (measure_ball_ne_top (x := z) (r := r)) h
  have hnonneg : 0 ≤ Real.exp r / 16 := div_nonneg (Real.exp_pos r).le (by norm_num)
  rw [ENNReal.toReal_ofReal hnonneg] at h'
  simpa [Measure.real] using h'

/-- Inverting the exponential area lower bound gives a logarithmic radius
bound whenever the area of a ball is bounded above. -/
theorem radius_le_log_sixteen_mul_of_volume_real_ball_le
    (z : ℍ) {r A : ℝ} (hr : Real.log 2 ≤ r)
    (hvolume : volume.real (Metric.ball z r) ≤ A) :
    r ≤ Real.log (16 * A) := by
  have hlower := exp_div_sixteen_le_volume_real_ball z hr
  have hA : 0 < A :=
    (div_pos (Real.exp_pos r) (by norm_num)).trans_le (hlower.trans hvolume)
  have hexp : Real.exp r ≤ 16 * A := by nlinarith
  calc
    r = Real.log (Real.exp r) := (Real.log_exp r).symm
    _ ≤ Real.log (16 * A) := Real.log_le_log (Real.exp_pos r) hexp

end SystolicGrowth
