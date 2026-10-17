module

public import Geometry.ComplexSobolevClassicalRepresentative
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

@[expose] public section

/-!
# Smooth mollification of compact `C¹` complex-plane tests

The normalized smooth bumps give one sequence of compactly supported smooth
tests converging pointwise both in value and in every classical directional
derivative. This supplies the approximation step for extending weak first
derivative identities from smooth compact tests to `C¹` compact tests.
-/

open Filter MeasureTheory ContinuousLinearMap
open scoped ContDiff Topology Convolution

namespace SystolicGrowth

noncomputable section

/-- The explicit radii are exposed for uniform support control of mollified tests. -/
def complexShrinkingBump (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := 1 / ((n : ℝ) + 2)
  rOut := 2 / ((n : ℝ) + 2)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    apply div_lt_div_of_pos_right (by norm_num) (by positivity)

private theorem complexShrinkingBump_rOut_tendsto :
    Tendsto (fun n => (complexShrinkingBump n).rOut) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => (2 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0)
  exact Filter.Tendsto.const_div_atTop
    (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop) 2

/-- Normalized convolution with the fixed shrinking bumps. -/
def complexMollify (n : ℕ) (f : ℂ → ℂ) : ℂ → ℂ :=
  (complexShrinkingBump n).normed volume ⋆[lsmul ℝ ℝ, volume] f

theorem complexMollify_tendsto (f : ℂ → ℂ) (hf : Continuous f) (x : ℂ) :
    Tendsto (fun n => complexMollify n f x) atTop (𝓝 (f x)) := by
  exact ContDiffBump.convolution_tendsto_right_of_continuous
    complexShrinkingBump_rOut_tendsto hf x

theorem complexMollify_smooth (f : ℂ → ℂ) (hf : LocallyIntegrable f volume)
    (n : ℕ) : ContDiff ℝ ∞ (complexMollify n f) := by
  exact (complexShrinkingBump n).hasCompactSupport_normed.contDiff_convolution_left
    _ (complexShrinkingBump n).contDiff_normed hf

theorem complexMollify_compact (f : ℂ → ℂ) (hf : HasCompactSupport f)
    (n : ℕ) : HasCompactSupport (complexMollify n f) := by
  exact (complexShrinkingBump n).hasCompactSupport_normed.convolution _ hf

/-- The derivative of the mollification is the convolution of the same
kernel with the actual classical derivative of the original `C¹` map. -/
theorem complexMollify_hasFDerivAt (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (n : ℕ) (x : ℂ) :
    HasFDerivAt (complexMollify n f)
      (((complexShrinkingBump n).normed volume ⋆[
        (lsmul ℝ ℝ).precompR ℂ, volume] fderiv ℝ f) x) x := by
  have hb : Continuous ((complexShrinkingBump n).normed volume) :=
    ((complexShrinkingBump n).contDiff_normed (n := 0)).continuous
  exact hfc.hasFDerivAt_convolution_right (lsmul ℝ ℝ)
    hb.locallyIntegrable
    hf x

/-- First derivatives converge pointwise as the normalized bumps shrink. -/
theorem complexMollify_fderiv_tendsto (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (x : ℂ) :
    Tendsto (fun n => fderiv ℝ (complexMollify n f) x) atTop
      (𝓝 (fderiv ℝ f x)) := by
  have hD : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have ht := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) (g := fderiv ℝ f) complexShrinkingBump_rOut_tendsto hD x
  have heq (n : ℕ) :
      fderiv ℝ (complexMollify n f) x =
        ((complexShrinkingBump n).normed volume ⋆[
          lsmul ℝ ℝ, volume] fderiv ℝ f) x := by
    have h := (complexMollify_hasFDerivAt f hf hfc n x).fderiv
    convert h using 1
    simp only [MeasureTheory.convolution]
    congr 1
  exact ht.congr' (Filter.Eventually.of_forall fun n => (heq n).symm)

/-- A uniform bound survives normalized mollification, with an explicit
constant sufficient for dominated convergence. -/
theorem complexMollify_norm_le (f : ℂ → ℂ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (n : ℕ) (x : ℂ) :
    ‖complexMollify n f x‖ ≤ 3 * C := by
  have hdist (y : ℂ) (_ : y ∈ Metric.ball x (complexShrinkingBump n).rOut) :
      dist (f y) (f x) ≤ 2 * C := by
    calc
      dist (f y) (f x) = ‖f y - f x‖ := dist_eq_norm _ _
      _ ≤ ‖f y‖ + ‖f x‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (hC y) (hC x)
      _ = 2 * C := by ring
  have hd := (complexShrinkingBump n).dist_normed_convolution_le
    (μ := volume) hf.aestronglyMeasurable hdist
  change dist (complexMollify n f x) (f x) ≤ 2 * C at hd
  calc
    ‖complexMollify n f x‖ ≤ dist (complexMollify n f x) (f x) + ‖f x‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using
        norm_add_le (complexMollify n f x - f x) (f x)
    _ ≤ 2 * C + C := add_le_add hd (hC x)
    _ = 3 * C := by ring

#print axioms complexMollify_tendsto
#print axioms complexMollify_smooth
#print axioms complexMollify_compact
#print axioms complexMollify_hasFDerivAt
#print axioms complexMollify_fderiv_tendsto
#print axioms complexMollify_norm_le

end

end SystolicGrowth
