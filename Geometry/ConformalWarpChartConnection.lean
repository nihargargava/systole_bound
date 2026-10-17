module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ConformalRiemannianMetric
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Jacobi.ChartCurvatureNaturality
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

/-!
# The actual Christoffel connection of a conformally scaled warped chart

This calculation stays in the original selected chart. The metric is
`exp (2 * f) * (dx² + W(x)² dy²)`, with unrestricted smooth dependence of
`f` on both coordinates. Metric compatibility along actual affine curves
and torsion-freeness determine the actual chart Christoffel operator.
No connection or curvature formula is supplied as an input.
-/

open Bundle Manifold Riemannian Set Filter
open scoped ContDiff Manifold Topology

namespace SystolicGrowth

noncomputable section

local instance conformalWarpComplexFinrankNonzero : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by simp [Complex.finrank_real_complex]⟩

/-- **Math.** The literal conformally scaled warped coordinate inner product. -/
def conformalWarpMetricInner (f : ℂ → ℝ) (W : ℝ → ℝ) (z a b : ℂ) : ℝ :=
  Real.exp (2 * f z) * (a.re * b.re + W z.re ^ 2 * a.im * b.im)

/-- **Math.** The actual coordinate first partials of the logarithmic factor. -/
def conformalPartialReal (f : ℂ → ℝ) (z : ℂ) : ℝ := fderiv ℝ f z 1

/-- **Math.** The actual coordinate first partial in the imaginary direction. -/
def conformalPartialImag (f : ℂ → ℝ) (z : ℂ) : ℝ := fderiv ℝ f z Complex.I

theorem conformalFDeriv_eq_partials (f : ℂ → ℝ) (z a : ℂ) :
    fderiv ℝ f z a = conformalPartialReal f z * a.re + conformalPartialImag f z * a.im := by
  have ha : a = a.re • (1 : ℂ) + a.im • Complex.I := by
    apply Complex.ext <;> simp
  calc
    fderiv ℝ f z a = fderiv ℝ f z (a.re • (1 : ℂ) + a.im • Complex.I) := congrArg (fderiv ℝ f z) ha
    _ = conformalPartialReal f z * a.re + conformalPartialImag f z * a.im := by
      simp only [map_add, map_smul, smul_eq_mul, conformalPartialReal, conformalPartialImag]
      ring

/-- **Math.** The candidate is explicitly defined in terms of the true
first derivatives; the following theorem identifies it with the metric's
actual Levi-Civita chart Christoffel operator. -/
def conformalWarpChristoffel (f : ℂ → ℝ) (W : ℝ → ℝ) (z a b : ℂ) : ℂ :=
  Complex.mk
    (conformalPartialReal f z * a.re * b.re +
      conformalPartialImag f z * (a.re * b.im + a.im * b.re) -
      (W z.re * deriv W z.re + W z.re ^ 2 * conformalPartialReal f z) * a.im * b.im)
    (-(conformalPartialImag f z / W z.re ^ 2) * a.re * b.re +
      (conformalPartialReal f z + deriv W z.re / W z.re) * (a.re * b.im + a.im * b.re) +
      conformalPartialImag f z * a.im * b.im)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold (modelWithCornersSelf ℝ ℂ) ∞ M]

/-- **Math.** Differentiate the actual metric pairing along an actual
affine coordinate curve. Compatibility yields its Christoffel balance,
with no assumed directional metric-derivative identity. -/
theorem conformalWarpChartMetric_deriv_balance_of_eventually
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M) (α : M)
    (f : ℂ → ℝ) (W : ℝ → ℝ)
    (hf : ContDiffOn ℝ ∞ f (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (hW : ContDiff ℝ ∞ W)
    {z : ℂ} (hz : z ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (hmetric : ∀ᶠ q in 𝓝 z, ∀ a b,
      chartMetricInner g α q a b = conformalWarpMetricInner f W q a b) (a b c : ℂ) :
    2 * Real.exp (2 * f z) *
        (fderiv ℝ f z a * (b.re * c.re + W z.re ^ 2 * b.im * c.im) +
          W z.re * deriv W z.re * a.re * b.im * c.im) =
      chartMetricInner g α z (Jacobi.chartChristoffelBilin g α z a b) c +
        chartMetricInner g α z b (Jacobi.chartChristoffelBilin g α z a c) := by
  let I := modelWithCornersSelf ℝ ℂ
  let line : ℝ → ℂ := fun t => z + t • a
  have hline (t : ℝ) : HasDerivAt line a t := by
    simpa only [line, id_eq, one_smul] using ((hasDerivAt_id t).smul_const a).const_add z
  have hline0 : line 0 = z := by simp [line]
  have htarget := (isOpen_extChartAt_target (I := I) α).mem_nhds hz
  have hbase : (extChartAt I α).symm z ∈ (trivializationAt ℂ (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source, ← extChartAt_source I α]
    exact (extChartAt I α).map_target hz
  have hG (i j : Fin (Module.finrank ℝ ℂ)) : DifferentiableAt ℝ (chartGramOnE g α i j) (line 0) := by
    rw [hline0]
    exact ((chartGramOnE_contDiffOn g α i j).contDiffAt htarget).differentiableAt (by simp)
  have halong := hasDerivAt_chartMetricInner_along g α line (fun _ => b) (fun _ => c)
    (hline 0).differentiableAt (differentiableAt_const b) (differentiableAt_const c)
    hG (by simpa only [hline0] using hbase)
  have hfz := (hf.contDiffAt htarget).differentiableAt (by simp)
  have hfl : HasDerivAt (fun t => f (line t)) (fderiv ℝ f z a) 0 := by
    have hfd : HasFDerivAt f (fderiv ℝ f z) (line 0) := by
      simpa only [hline0] using hfz.hasFDerivAt
    exact hfd.comp_hasDerivAt 0 (hline 0)
  have hre : HasDerivAt (fun t => (line t).re) a.re 0 :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (hline 0)
  have hwl : HasDerivAt (fun t => W (line t).re) (deriv W z.re * a.re) 0 := by
    have hwd : HasDerivAt W (deriv W z.re) (line 0).re := by
      simpa only [hline0] using (hW.differentiable (by simp) z.re).hasDerivAt
    exact hwd.comp 0 hre
  have hexp := (hfl.const_mul 2).exp
  have hwarped := (hasDerivAt_const 0 (b.re * c.re)).add
    (((hwl.pow 2).mul_const b.im).mul_const c.im)
  have hmodel : HasDerivAt (fun t => conformalWarpMetricInner f W (line t) b c)
      (2 * Real.exp (2 * f z) *
        (fderiv ℝ f z a * (b.re * c.re + W z.re ^ 2 * b.im * c.im) +
          W z.re * deriv W z.re * a.re * b.im * c.im)) 0 := by
    exact (hexp.mul hwarped).congr_deriv (by
      simp only [Pi.add_apply, Pi.pow_apply, hline0, Nat.cast_ofNat, zero_add]
      ring)
  have heq : (fun t => chartMetricInner g α (line t) b c) =ᶠ[𝓝 0]
      fun t => conformalWarpMetricInner f W (line t) b c := by
    have ht : ∀ᶠ q in 𝓝 (line 0), ∀ b c,
        chartMetricInner g α q b c = conformalWarpMetricInner f W q b c := by
      rw [hline0]
      exact hmetric
    filter_upwards [(hline 0).continuousAt.eventually ht] with t ht
    exact ht b c
  have h := halong.deriv
  rw [heq.deriv_eq, hmodel.deriv] at h
  simpa only [covariantDerivCoord_def, hline0, (hline 0).deriv, deriv_const,
    zero_add, Jacobi.chartChristoffelBilin_apply] using h

/-- **Math.** The literal coordinate form determines the ACTUAL
Christoffel operator through metric compatibility and torsion-freeness.
The original chosen model basis need not be the real/imaginary basis. -/
theorem conformalWarpChartChristoffel_eq_of_eventually
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M) (α : M)
    (f : ℂ → ℝ) (W : ℝ → ℝ)
    (hf : ContDiffOn ℝ ∞ f (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (hW : ContDiff ℝ ∞ W) (hWpos : ∀ t, 0 < W t)
    {z : ℂ} (hz : z ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (hmetric : ∀ᶠ q in 𝓝 z, ∀ a b,
      chartMetricInner g α q a b = conformalWarpMetricInner f W q a b) (a b : ℂ) :
    Jacobi.chartChristoffelBilin g α z a b = conformalWarpChristoffel f W z a b := by
  let Γ := Jacobi.chartChristoffelBilin g α z
  let D : ℂ → ℂ → ℂ → ℝ := fun a b c =>
    2 * Real.exp (2 * f z) *
      (fderiv ℝ f z a * (b.re * c.re + W z.re ^ 2 * b.im * c.im) +
        W z.re * deriv W z.re * a.re * b.im * c.im)
  have hbalance (a b c : ℂ) : D a b c = chartMetricInner g α z (Γ a b) c +
      chartMetricInner g α z b (Γ a c) :=
    conformalWarpChartMetric_deriv_balance_of_eventually g α f W hf hW hz hmetric a b c
  have hsymm (a b : ℂ) : Γ a b = Γ b a := Jacobi.chartChristoffelBilin_symm g α z a b
  have hkoszul (a b c : ℂ) : 2 * chartMetricInner g α z (Γ a b) c =
      D a b c + D b a c - D c a b := by
    have h1 := hbalance a b c
    have h2 := hbalance b a c
    have h3 := hbalance c a b
    rw [hsymm b a] at h2
    rw [hsymm c a, hsymm c b] at h3
    rw [chartMetricInner_symm g α z (Γ a c) b] at h3
    linarith
  have hpair (a b c : ℂ) : chartMetricInner g α z (Γ a b) c =
      conformalWarpMetricInner f W z (conformalWarpChristoffel f W z a b) c := by
    have h := hkoszul a b c
    dsimp only [D] at h
    rw [conformalFDeriv_eq_partials f z a, conformalFDeriv_eq_partials f z b,
      conformalFDeriv_eq_partials f z c] at h
    unfold conformalWarpMetricInner conformalWarpChristoffel
    dsimp only
    have hWne := (hWpos z.re).ne'
    field_simp [hWne]
    nlinarith [h]
  have heq : Γ a b = conformalWarpChristoffel f W z a b := by
    have hm : ∀ a b, chartMetricInner g α z a b = conformalWarpMetricInner f W z a b :=
      hmetric.self_of_nhds
    apply Complex.ext
    · have h := hpair a b 1
      rw [hm] at h
      dsimp [conformalWarpMetricInner] at h
      have hexp : Real.exp (2 * f z) ≠ 0 := (Real.exp_pos _).ne'
      exact mul_left_cancel₀ hexp (by simpa using h)
    · have h := hpair a b Complex.I
      rw [hm] at h
      dsimp [conformalWarpMetricInner] at h
      have hc : Real.exp (2 * f z) * W z.re ^ 2 ≠ 0 :=
        mul_ne_zero (Real.exp_pos _).ne' (pow_ne_zero 2 (hWpos z.re).ne')
      apply mul_left_cancel₀ hc
      simpa only [Complex.I_re, Complex.I_im, mul_zero, zero_mul, zero_add, mul_one, mul_assoc] using h
  exact heq

/-- **Math.** The full-target form is a specialization of the genuinely
local metric-derivative balance; the local form is used for collar patches. -/
theorem conformalWarpChartMetric_deriv_balance
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M) (α : M)
    (f : ℂ → ℝ) (W : ℝ → ℝ)
    (hf : ContDiffOn ℝ ∞ f (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (hW : ContDiff ℝ ∞ W)
    (hmetric : ∀ z ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target, ∀ a b,
      chartMetricInner g α z a b = conformalWarpMetricInner f W z a b)
    {z : ℂ} (hz : z ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target) (a b c : ℂ) :
    2 * Real.exp (2 * f z) *
        (fderiv ℝ f z a * (b.re * c.re + W z.re ^ 2 * b.im * c.im) +
          W z.re * deriv W z.re * a.re * b.im * c.im) =
      chartMetricInner g α z (Jacobi.chartChristoffelBilin g α z a b) c +
        chartMetricInner g α z b (Jacobi.chartChristoffelBilin g α z a c) := by
  apply conformalWarpChartMetric_deriv_balance_of_eventually g α f W hf hW hz _ a b c
  filter_upwards [(isOpen_extChartAt_target α).mem_nhds hz] with q hq
  exact hmetric q hq

/-- **Math.** The original full-target public contract follows from the
local Christoffel theorem, without strengthening any metric input. -/
theorem conformalWarpChartChristoffel_eq
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M) (α : M)
    (f : ℂ → ℝ) (W : ℝ → ℝ)
    (hf : ContDiffOn ℝ ∞ f (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (hW : ContDiff ℝ ∞ W) (hWpos : ∀ t, 0 < W t)
    (hmetric : ∀ z ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target, ∀ a b,
      chartMetricInner g α z a b = conformalWarpMetricInner f W z a b)
    {z : ℂ} (hz : z ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target) (a b : ℂ) :
    Jacobi.chartChristoffelBilin g α z a b = conformalWarpChristoffel f W z a b := by
  apply conformalWarpChartChristoffel_eq_of_eventually g α f W hf hW hWpos hz _ a b
  filter_upwards [(isOpen_extChartAt_target α).mem_nhds hz] with q hq
  exact hmetric q hq

#print axioms conformalWarpChartMetric_deriv_balance
#print axioms conformalWarpChartChristoffel_eq
#print axioms conformalWarpChartMetric_deriv_balance_of_eventually
#print axioms conformalWarpChartChristoffel_eq_of_eventually

end

end SystolicGrowth
