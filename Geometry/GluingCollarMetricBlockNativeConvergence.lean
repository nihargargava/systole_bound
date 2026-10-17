module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarFiniteMetricBlockChainDistance
public import Geometry.GluingCollarFiniteMetricBlockNativeRetraction
public import Geometry.GluingCollarFiniteChainConvergence

@[expose] public section

/-!
# Native distance convergence of the actual metric-block approximants

The exact whole-chain bridge transfers the already proved native distance
limit to genuine metric spaces. The inverse distortion has its original
clipping factor divided by the Fermi curvature scale; it tends to one.
-/

open Set Filter
open scoped Topology

namespace SystolicGrowth

/-- The actual Fermi scale tends to one as the strip width tends to zero. -/
theorem gluingCollarMetricBlock_scale_tendsto
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => Real.sqrt (1 - ε n)) atTop (𝓝 1) := by
  simpa only [Function.comp_def, sub_zero, Real.sqrt_one] using
    (Real.continuous_sqrt.tendsto (1 - 0)).comp
      (tendsto_const_nhds.sub hε)

/-- The genuine inverse distortion is positive at every positive scale. -/
theorem gluingCollarMetricBlock_distortion_pos
    {r R lam ε : ℝ} (hε : 0 ≤ ε) (hlam : 0 < lam) :
    0 < (1 + ε * Real.cosh (|r| + R)) ^ 2 / lam := by
  positivity

/-- The native inverse clipping distortion, including the curvature scale,
tends to one; no metric comparison is assumed here. -/
theorem gluingCollarMetricBlock_distortion_tendsto
    (r R : ℝ) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => (1 + ε n * Real.cosh (|r| + R)) ^ 2 /
      Real.sqrt (1 - ε n)) atTop (𝓝 1) := by
  have hnum : Tendsto (fun n => (1 + ε n * Real.cosh (|r| + R)) ^ 2)
      atTop (𝓝 1) := by
    simpa only [zero_mul, add_zero, one_pow] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
        (hε.mul_const (Real.cosh (|r| + R)))).pow 2
  simpa only [Pi.div_def, div_self (by norm_num : (1 : ℝ) ≠ 0)] using
    hnum.div (gluingCollarMetricBlock_scale_tendsto ε hε) (by norm_num)

/-- Distances between actual forward images in the native metric-block limit
converge to the true native collar distance on a fixed radial window. -/
theorem gluingCollarFiniteMetricBlockNativeForward_dist_tendsto
    {r R c : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 < ε n) (hεlt : ∀ n, ε n < 1)
    (hscale : Tendsto ε atTop (𝓝 0))
    (x y : {z : ℂ // z.re ∈ Icc (-R) R}) :
    letI := gluingCollarModelMetricSpace hr
    letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
    Tendsto (fun n => dist
      (gluingCollarFiniteMetricBlockNativeForward (r := r) hR
        (Real.sqrt_pos.mpr (sub_pos.mpr (hεlt n))) (hε n) c x)
      (gluingCollarFiniteMetricBlockNativeForward (r := r) hR
        (Real.sqrt_pos.mpr (sub_pos.mpr (hεlt n))) (hε n) c y))
      atTop (𝓝 (dist x y)) := by
  letI := gluingCollarModelMetricSpace hr
  letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
  have hD := gluingCollarFiniteFinChainEDist_tendsto (c := c)
    hr hR ε hε hscale x.2 y.2
  have hreal := (ENNReal.tendsto_toReal
    (gluingCollarModelEDist_lt_top hr x.1 y.1).ne).comp hD
  have hlim := (gluingCollarMetricBlock_scale_tendsto ε hscale).mul hreal
  have hnative : (gluingCollarModelEDist hr x.1 y.1).toReal = dist x y := by
    rw [← gluingCollarModelMetricSpace_edist hr, edist_dist, ENNReal.toReal_ofReal dist_nonneg]
    rfl
  have heq (n : ℕ) : dist
      (gluingCollarFiniteMetricBlockNativeForward (r := r) hR
        (Real.sqrt_pos.mpr (sub_pos.mpr (hεlt n))) (hε n) c x)
      (gluingCollarFiniteMetricBlockNativeForward (r := r) hR
        (Real.sqrt_pos.mpr (sub_pos.mpr (hεlt n))) (hε n) c y) =
      Real.sqrt (1 - ε n) *
        (gluingCollarFiniteFinChainEDist r R (Real.sqrt (1 - ε n)) (ε n)
          (gluingCollarFiniteFinTargetMap r c (ε n) (hε n) x.1)
          (gluingCollarFiniteFinTargetMap r c (ε n) (hε n) y.1)).toReal := by
    exact gluingCollarFiniteMetricBlockChainMap_dist_eq_of_window hR
      (Real.sqrt_pos.mpr (sub_pos.mpr (hεlt n))) _ _
      (gluingCollarFiniteFinTargetMap_window (hε n) x.1 x.2)
      (gluingCollarFiniteFinTargetMap_window (hε n) y.1 y.2)
  simpa only [heq, one_mul, hnative, Function.comp_def] using hlim

#print axioms gluingCollarFiniteMetricBlockNativeForward_dist_tendsto

end SystolicGrowth
