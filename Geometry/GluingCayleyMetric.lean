module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingPolarCollar
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

/-!
# The actual inverse Cayley derivative and metric pullback

We differentiate the explicit centered inverse Cayley map used by
`gluingDiscChartInverse`. Its real tangent map pulls back the half-plane
Poincare form to the disk Poincare form. These are coordinate tangent-form
identities, not a statement identifying an induced Riemannian distance with
the existing hyperbolic distance, nor a global glued tensor construction.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane ComplexConjugate

namespace SystolicGrowth

/-- The ambient rational expression of the actual centered inverse disk chart. -/
noncomputable def gluingCenteredCayley (o : ℍ) (w : ℂ) : ℂ :=
  (o.re : ℂ) + (o.im : ℂ) * Vendored.RiemannDynamics.cayleyToHalfPlane w

@[simp] theorem gluingDiscChartInverse_coe (o : ℍ) (w : ball (0 : ℂ) 1) :
    (gluingDiscChartInverse o w : ℂ) = gluingCenteredCayley o w := rfl

theorem gluingCenteredCayley_eq (o : ℍ) (w : ℂ) :
    gluingCenteredCayley o w =
      (o.re : ℂ) + (o.im : ℂ) * Complex.I * (1 + w) / (1 - w) := by
  simp [gluingCenteredCayley, Vendored.RiemannDynamics.cayleyToHalfPlane, mul_div_assoc,
    mul_assoc]

/-- The derivative coefficient of the actual inverse chart. -/
noncomputable def gluingCenteredCayleyDeriv (o : ℍ) (w : ℂ) : ℂ :=
  (o.im : ℂ) * 2 * Complex.I / (1 - w) ^ 2

theorem gluingCenteredCayley_hasDerivAt (o : ℍ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    HasDerivAt (gluingCenteredCayley o) (gluingCenteredCayleyDeriv o w) w := by
  have hne : (1 : ℂ) - w ≠ 0 := Vendored.RiemannDynamics.one_sub_ne_zero_of_mem_ball hw
  have hC : HasDerivAt Vendored.RiemannDynamics.cayleyToHalfPlane
      (2 * Complex.I / (1 - w) ^ 2) w := by
    unfold Vendored.RiemannDynamics.cayleyToHalfPlane
    convert (((hasDerivAt_id w).const_add 1).const_mul Complex.I).div
      ((hasDerivAt_id w).const_sub 1) hne using 1 <;>
      first | rfl | (simp only [id_eq]; ring)
  change HasDerivAt (fun x : ℂ =>
    (o.re : ℂ) + (o.im : ℂ) * Vendored.RiemannDynamics.cayleyToHalfPlane x) _ w
  convert (hC.const_mul (o.im : ℂ)).const_add (o.re : ℂ) using 1 <;>
    first | rfl | simp [gluingCenteredCayleyDeriv, mul_div_assoc, mul_assoc]

/-- The real-linear tangent derivative obtained from the proved complex derivative. -/
noncomputable def gluingCenteredCayleyFDeriv (o : ℍ) (w : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.toSpanSingleton ℂ (gluingCenteredCayleyDeriv o w)).restrictScalars ℝ

@[simp] theorem gluingCenteredCayleyFDeriv_apply (o : ℍ) (w v : ℂ) :
    gluingCenteredCayleyFDeriv o w v =
      (o.im : ℂ) * 2 * Complex.I * v / (1 - w) ^ 2 := by
  simp [gluingCenteredCayleyFDeriv, gluingCenteredCayleyDeriv, smul_eq_mul]
  ring

theorem gluingCenteredCayley_hasFDerivAt (o : ℍ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    HasFDerivAt (gluingCenteredCayley o) (gluingCenteredCayleyFDeriv o w) w :=
  (gluingCenteredCayley_hasDerivAt o hw).hasFDerivAt.restrictScalars ℝ

theorem gluingCenteredCayley_im (o : ℍ) (w : ℂ) :
    (gluingCenteredCayley o w).im =
      o.im * (1 - ‖w‖ ^ 2) / ‖(1 : ℂ) - w‖ ^ 2 := by
  simp [gluingCenteredCayley, Vendored.RiemannDynamics.cayleyToHalfPlane_im, mul_div_assoc]

theorem gluingDiscChartInverse_im (o : ℍ) (w : ball (0 : ℂ) 1) :
    (gluingDiscChartInverse o w).im =
      o.im * (1 - ‖(w : ℂ)‖ ^ 2) / ‖(1 : ℂ) - w‖ ^ 2 :=
  gluingCenteredCayley_im o w

private theorem re_scalar_mul_conj (a v u : ℂ) :
    ((a * v) * conj (a * u)).re = ‖a‖ ^ 2 * (v * conj u).re := by
  calc
    ((a * v) * conj (a * u)).re = (a * conj a * (v * conj u)).re := by
      rw [map_mul]
      congr 1
      ring
    _ = ‖a‖ ^ 2 * (v * conj u).re := by
      rw [Complex.mul_conj', ← Complex.ofReal_pow]
      exact Complex.re_ofReal_mul _ _

theorem norm_gluingCenteredCayleyDeriv_sq (o : ℍ) (w : ℂ) :
    ‖gluingCenteredCayleyDeriv o w‖ ^ 2 =
      4 * o.im ^ 2 / (‖(1 : ℂ) - w‖ ^ 2) ^ 2 := by
  simp [gluingCenteredCayleyDeriv, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos o.im_pos]
  ring

/-- The actual half-plane Poincare tangent form. -/
noncomputable def gluingHalfPlaneTangentForm (z : ℍ) (v u : ℂ) : ℝ :=
  (v * conj u).re / z.im ^ 2

/-- The actual unit-disk Poincare tangent form. -/
noncomputable def gluingDiskTangentForm (w v u : ℂ) : ℝ :=
  4 * (v * conj u).re / (1 - ‖w‖ ^ 2) ^ 2

/-- The real tangent pullback along the actual centered inverse Cayley chart. -/
theorem gluingDiscChartInverse_tangentForm_pullback (o : ℍ)
    (w : ball (0 : ℂ) 1) (v u : ℂ) :
    gluingHalfPlaneTangentForm (gluingDiscChartInverse o w)
      (gluingCenteredCayleyFDeriv o w v) (gluingCenteredCayleyFDeriv o w u) =
      gluingDiskTangentForm w v u := by
  have hd : ‖(1 : ℂ) - w‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Vendored.RiemannDynamics.one_sub_ne_zero_of_mem_ball w.2)
  have hn : ‖(w : ℂ)‖ < 1 := by simpa only [mem_ball, dist_zero_right] using w.2
  have hr : 1 - ‖(w : ℂ)‖ ^ 2 ≠ 0 := by
    have : 0 < 1 - ‖(w : ℂ)‖ ^ 2 := by nlinarith [norm_nonneg (w : ℂ)]
    exact this.ne'
  have ha (x : ℂ) : gluingCenteredCayleyFDeriv o w x = gluingCenteredCayleyDeriv o w * x := by
    simp [gluingCenteredCayleyFDeriv, smul_eq_mul, mul_comm]
  unfold gluingHalfPlaneTangentForm gluingDiskTangentForm
  rw [ha v, ha u, re_scalar_mul_conj, norm_gluingCenteredCayleyDeriv_sq,
    gluingDiscChartInverse_im]
  field_simp [hd, hr, o.im_pos.ne']

#print axioms gluingCenteredCayley_hasDerivAt
#print axioms gluingCenteredCayley_hasFDerivAt
#print axioms gluingDiscChartInverse_tangentForm_pullback

end SystolicGrowth
