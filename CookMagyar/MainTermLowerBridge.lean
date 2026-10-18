module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.MainTerm
public import CookMagyar.RealDensityMeasureBridge

@[expose] public section

namespace SystolicGrowth
namespace CookMagyarCircle

/-! # From the real density bound to the circle-method main term

The real singular integral now has an unconditional positive lower bound.
This module records the remaining arithmetic input needed to turn it into
the main-term lower bound: a real, target-uniform lower bound for the
singular series.
-/

/-- A real lower bound for the singular series combines with the proved
real-place density bound to control the singular coefficient. -/
theorem cubicSingularCoefficient_ge_of_singularSeries_re_lower
    {n N T : ℕ} (hn : 4 ≤ n)
    (hwindow : CookMagyarReal.NormalizedTargetWindow n
      (CookMagyarReal.normalizedTarget N T))
    {c : ℝ} (hc : 0 ≤ c)
    (hseriesIm : (CookMagyarFiniteFourier.singularSeries n T).im = 0)
    (hseriesLower : c ≤ (CookMagyarFiniteFourier.singularSeries n T).re) :
    c * (CookMagyarReal.geometricDensityLowerBound n).toReal ≤
      cubicSingularCoefficient n N T := by
  let mu := CookMagyarReal.normalizedTarget N T
  have hfourier :=
    CookMagyarReal.hasCubicRealFourierInversion_of_normalizedTargetWindow n hn
  have hintegral : CookMagyarReal.singularIntegral n mu =
      (CookMagyarReal.geometricCubicDensityReal n mu : ℂ) :=
    (hfourier mu hwindow).2
  have hlower : (CookMagyarReal.geometricDensityLowerBound n).toReal ≤
      CookMagyarReal.geometricCubicDensityReal n mu := by
    have h := CookMagyarReal.singularIntegral_re_uniform_lower_bound_of_normalizedTargetWindow
      hn hwindow
    rw [hintegral, Complex.ofReal_re] at h
    exact h
  have hgeo : 0 ≤ CookMagyarReal.geometricCubicDensityReal n mu :=
    le_of_lt (CookMagyarReal.geometricCubicDensityReal_pos (by omega) hwindow)
  calc
    c * (CookMagyarReal.geometricDensityLowerBound n).toReal ≤
        c * CookMagyarReal.geometricCubicDensityReal n mu :=
      mul_le_mul_of_nonneg_left hlower hc
    _ ≤ (CookMagyarFiniteFourier.singularSeries n T).re *
          CookMagyarReal.geometricCubicDensityReal n mu :=
      mul_le_mul_of_nonneg_right hseriesLower hgeo
    _ = cubicSingularCoefficient n N T := by
      simp [cubicSingularCoefficient, mu, hintegral, Complex.mul_re, hseriesIm]

/-- The corresponding lower bound at the natural cubic main scale. -/
theorem cubicSingularMainTerm_ge_of_singularSeries_re_lower
    {n N T : ℕ} (hn : 4 ≤ n) (hN : 0 < N)
    (hwindow : CookMagyarReal.NormalizedTargetWindow n
      (CookMagyarReal.normalizedTarget N T))
    {c : ℝ} (hc : 0 ≤ c)
    (hseriesIm : (CookMagyarFiniteFourier.singularSeries n T).im = 0)
    (hseriesLower : c ≤ (CookMagyarFiniteFourier.singularSeries n T).re) :
    (c * (CookMagyarReal.geometricDensityLowerBound n).toReal) *
      cubicMainScale n N ≤ cubicSingularMainTerm n N T := by
  unfold cubicSingularMainTerm
  exact mul_le_mul_of_nonneg_right
    (cubicSingularCoefficient_ge_of_singularSeries_re_lower
      hn hwindow hc hseriesIm hseriesLower)
    (cubicMainScale_pos hN).le

end CookMagyarCircle
end SystolicGrowth
