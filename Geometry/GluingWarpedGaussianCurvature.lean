module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarLocalizedSmoothWarp
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-!
# Gaussian curvature of the actual smooth warped coordinate metric

We construct the coordinate metric `dt² + W(t)² dθ²`, its inverse,
connection coefficients, and the Riemann tensor using actual coordinate
derivatives. Torsion freedom, metric compatibility and the coordinate Koszul
formula are proved. The sectional quotient and metric area determinant then
give Gaussian curvature `-W''/W` and signed curvature density `-W''`.
-/

open Set
open scoped Topology BigOperators

namespace SystolicGrowth

noncomputable section

/-- The literal coordinate tensor of `dt² + W(t)² dθ²`. -/
def gluingWarpedMetric (W : ℝ → ℝ) (x : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = j then if i = 0 then 1 else W x.1 ^ 2 else 0

/-- The literal inverse coordinate tensor, valid for a positive warp. -/
def gluingWarpedInverseMetric (W : ℝ → ℝ) (x : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = j then if i = 0 then 1 else (W x.1 ^ 2)⁻¹ else 0

/-- Genuine directional coordinate partials, using the real Fréchet derivative. -/
def gluingWarpedCoordinatePartial (f : (ℝ × ℝ) → ℝ) (i : Fin 2) (x : ℝ × ℝ) : ℝ :=
  fderiv ℝ f x (if i = 0 then (1, 0) else (0, 1))

theorem gluingWarpedCoordinatePartial_radial {f : ℝ → ℝ} {t f' : ℝ}
    (hf : HasDerivAt f f' t) (θ : ℝ) (i : Fin 2) :
    gluingWarpedCoordinatePartial (fun x : ℝ × ℝ => f x.1) i (t, θ) =
      if i = 0 then f' else 0 := by
  have h := hf.hasFDerivAt.comp (t, θ)
    (hasFDerivAt_fst : HasFDerivAt (Prod.fst : ℝ × ℝ → ℝ)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (t, θ))
  rw [gluingWarpedCoordinatePartial]
  change fderiv ℝ (f ∘ Prod.fst) (t, θ) _ = _
  rw [h.fderiv]
  fin_cases i <;> simp

theorem gluingWarpedCoordinatePartial_const (a : ℝ) (i : Fin 2) (x : ℝ × ℝ) :
    gluingWarpedCoordinatePartial (fun _ => a) i x = 0 := by
  simp [gluingWarpedCoordinatePartial]

/-- Actual connection coefficients, with upper index first. -/
def gluingWarpedChristoffel (W : ℝ → ℝ) (l i j : Fin 2) (x : ℝ × ℝ) : ℝ :=
  if l = 0 then
    if i = 1 ∧ j = 1 then -(W x.1 * deriv W x.1) else 0
  else
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then deriv W x.1 / W x.1 else 0

/-- Literal derivative-plus-connection-composition curvature tensor:
`R(eᵢ,eⱼ)eₖ`, with output component `l`. -/
def gluingWarpedRiemann (W : ℝ → ℝ) (l k i j : Fin 2) (x : ℝ × ℝ) : ℝ :=
  gluingWarpedCoordinatePartial (gluingWarpedChristoffel W l j k) i x -
    gluingWarpedCoordinatePartial (gluingWarpedChristoffel W l i k) j x +
      ∑ m : Fin 2, (gluingWarpedChristoffel W l i m x *
        gluingWarpedChristoffel W m j k x - gluingWarpedChristoffel W l j m x *
          gluingWarpedChristoffel W m i k x)

theorem gluingWarpedMetric_det (W : ℝ → ℝ) (x : ℝ × ℝ) :
    (gluingWarpedMetric W x).det = W x.1 ^ 2 := by
  simp [Matrix.det_fin_two, gluingWarpedMetric]

theorem gluingWarpedMetric_areaDensity {W : ℝ → ℝ} {x : ℝ × ℝ} (hW : 0 < W x.1) :
    Real.sqrt (gluingWarpedMetric W x).det = W x.1 := by
  rw [gluingWarpedMetric_det, Real.sqrt_sq_eq_abs, abs_of_pos hW]

theorem gluingWarpedMetric_inverse {W : ℝ → ℝ} {x : ℝ × ℝ} (hW : W x.1 ≠ 0) :
    gluingWarpedMetric W x * gluingWarpedInverseMetric W x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, gluingWarpedMetric,
      gluingWarpedInverseMetric, hW]

/-- The bilinear form evaluated from the literal coordinate metric tensor. -/
def gluingWarpedMetricForm (W : ℝ → ℝ) (x : ℝ × ℝ) (v w : Fin 2 → ℝ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, gluingWarpedMetric W x i j * v i * w j

theorem gluingWarpedMetricForm_apply (W : ℝ → ℝ) (x : ℝ × ℝ) (v w : Fin 2 → ℝ) :
    gluingWarpedMetricForm W x v w = v 0 * w 0 + W x.1 ^ 2 * v 1 * w 1 := by
  simp [gluingWarpedMetricForm, gluingWarpedMetric]

theorem gluingWarpedMetricForm_symmetric (W : ℝ → ℝ) (x : ℝ × ℝ) (v w : Fin 2 → ℝ) :
    gluingWarpedMetricForm W x v w = gluingWarpedMetricForm W x w v := by
  rw [gluingWarpedMetricForm_apply, gluingWarpedMetricForm_apply]
  ring

/-- A positive warp gives an actual positive-definite metric, not only
a nonzero determinant. -/
theorem gluingWarpedMetricForm_pos {W : ℝ → ℝ} {x : ℝ × ℝ}
    (hpos : 0 < W x.1) {v : Fin 2 → ℝ} (hv : v ≠ 0) :
    0 < gluingWarpedMetricForm W x v v := by
  have hv' : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    funext i
    fin_cases i <;> simp [h]
  rw [gluingWarpedMetricForm_apply]
  rcases hv' with h | h
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (W x.1 * v 1)]
  · have hp := mul_pos (sq_pos_of_pos hpos) (sq_pos_of_ne_zero h)
    nlinarith [sq_nonneg (v 0)]

theorem gluingWarpedMetric_contDiff {W : ℝ → ℝ} (hW : ContDiff ℝ 2 W)
    (i j : Fin 2) : ContDiff ℝ 2 (fun x : ℝ × ℝ => gluingWarpedMetric W x i j) := by
  have hw : ContDiff ℝ 2 (fun x : ℝ × ℝ => W x.1) := hW.comp contDiff_fst
  fin_cases i <;> fin_cases j <;> simp [gluingWarpedMetric]
  all_goals first | exact contDiff_const | exact hw.pow 2

/-- The constructed connection is genuinely torsion free in these
commuting coordinate directions. -/
theorem gluingWarpedChristoffel_torsion_free (W : ℝ → ℝ) (l i j : Fin 2) (x : ℝ × ℝ) :
    gluingWarpedChristoffel W l i j x = gluingWarpedChristoffel W l j i x := by
  fin_cases l <;> fin_cases i <;> fin_cases j <;> simp [gluingWarpedChristoffel]

theorem gluingWarpedMetric_coordinatePartial {W : ℝ → ℝ}
    (hW : ContDiff ℝ 2 W) (i j k : Fin 2) (x : ℝ × ℝ) :
    gluingWarpedCoordinatePartial (fun y => gluingWarpedMetric W y j k) i x =
      if i = 0 ∧ j = 1 ∧ k = 1 then 2 * W x.1 * deriv W x.1 else 0 := by
  have hd := (hW.differentiable (by norm_num) x.1).hasDerivAt
  fin_cases j <;> fin_cases k
  · simpa [gluingWarpedMetric] using
      gluingWarpedCoordinatePartial_const 1 i x
  · simpa [gluingWarpedMetric] using gluingWarpedCoordinatePartial_const 0 i x
  · simpa [gluingWarpedMetric] using gluingWarpedCoordinatePartial_const 0 i x
  · have hh := gluingWarpedCoordinatePartial_radial (hd.pow 2) x.2 i
    simpa [gluingWarpedMetric, mul_assoc, mul_comm, mul_left_comm] using hh

/-- The derivative of the warped metric in an arbitrary constant coordinate
direction. This is the basis-change form of
`gluingWarpedMetric_coordinatePartial`: only the radial component of the
direction contributes, so later calculations may use any linear coordinate
basis without identifying it with the standard coordinate axes. -/
theorem gluingWarpedMetric_directionalPartial {W : ℝ → ℝ}
    (hW : ContDiff ℝ 2 W) (x : ℝ × ℝ) (v : Fin 2 → ℝ) (i j : Fin 2) :
    fderiv ℝ (fun y : ℝ × ℝ => gluingWarpedMetric W y i j) x (v 0, v 1) =
      if i = 1 ∧ j = 1 then 2 * W x.1 * deriv W x.1 * v 0 else 0 := by
  have h0 : fderiv ℝ (fun y : ℝ × ℝ => gluingWarpedMetric W y i j) x (1, 0) =
      gluingWarpedCoordinatePartial (fun y => gluingWarpedMetric W y i j) 0 x := by
    simp [gluingWarpedCoordinatePartial]
  have h1 : fderiv ℝ (fun y : ℝ × ℝ => gluingWarpedMetric W y i j) x (0, 1) =
      gluingWarpedCoordinatePartial (fun y => gluingWarpedMetric W y i j) 1 x := by
    simp [gluingWarpedCoordinatePartial]
  calc
    fderiv ℝ (fun y : ℝ × ℝ => gluingWarpedMetric W y i j) x (v 0, v 1)
        = fderiv ℝ (fun y : ℝ × ℝ => gluingWarpedMetric W y i j) x
            (v 0 • (1, 0) + v 1 • (0, 1)) := by
              congr 1
              ext <;> simp
    _ = v 0 * gluingWarpedCoordinatePartial
            (fun y => gluingWarpedMetric W y i j) 0 x +
          v 1 * gluingWarpedCoordinatePartial
            (fun y => gluingWarpedMetric W y i j) 1 x := by
          rw [map_add, map_smul, map_smul, h0, h1]
          simp [smul_eq_mul]
    _ = if i = 1 ∧ j = 1 then 2 * W x.1 * deriv W x.1 * v 0 else 0 := by
          rw [gluingWarpedMetric_coordinatePartial hW 0 i j x,
            gluingWarpedMetric_coordinatePartial hW 1 i j x]
          by_cases hi : i = 1
          · by_cases hj : j = 1
            · simp [hi, hj]
              ring
            · simp [hi, hj]
          · by_cases hj : j = 1
            · simp [hi, hj]
            · simp [hi, hj]

/-- The same formula for a complex chart direction, interpreted through its
real and imaginary coordinates. In particular it applies to each vector of
the arbitrary model basis `Module.finBasis ℝ ℂ`. -/
theorem gluingWarpedMetric_complexDirectionalPartial {W : ℝ → ℝ}
    (hW : ContDiff ℝ 2 W) (x : ℝ × ℝ) (z : ℂ) (i j : Fin 2) :
    fderiv ℝ (fun y : ℝ × ℝ => gluingWarpedMetric W y i j) x (z.re, z.im) =
      if i = 1 ∧ j = 1 then 2 * W x.1 * deriv W x.1 * z.re else 0 := by
  simpa using gluingWarpedMetric_directionalPartial hW x
    (fun a : Fin 2 => if a = 0 then z.re else z.im) i j

/-- The literal metric-compatibility equation holds with actual partials
of the constructed metric, rather than supplied tensor derivatives. -/
theorem gluingWarpedChristoffel_metric_compatible {W : ℝ → ℝ}
    (hW : ContDiff ℝ 2 W) {x : ℝ × ℝ} (hpos : 0 < W x.1) (i j k : Fin 2) :
    gluingWarpedCoordinatePartial (fun y => gluingWarpedMetric W y j k) i x =
      ∑ l : Fin 2, (gluingWarpedChristoffel W l i j x * gluingWarpedMetric W x l k +
        gluingWarpedChristoffel W l i k x * gluingWarpedMetric W x j l) := by
  rw [gluingWarpedMetric_coordinatePartial hW]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [gluingWarpedChristoffel, gluingWarpedMetric]
  all_goals (field_simp [hpos.ne']; ring)

/-- The connection is derived by the coordinate Koszul formula from the
actual inverse metric and actual coordinate derivatives. -/
theorem gluingWarpedChristoffel_eq_metric_formula {W : ℝ → ℝ}
    (hW : ContDiff ℝ 2 W) {x : ℝ × ℝ} (hpos : 0 < W x.1) (l i j : Fin 2) :
    gluingWarpedChristoffel W l i j x = (1 / 2 : ℝ) *
      ∑ m : Fin 2, gluingWarpedInverseMetric W x l m *
        (gluingWarpedCoordinatePartial (fun y => gluingWarpedMetric W y m j) i x +
          gluingWarpedCoordinatePartial (fun y => gluingWarpedMetric W y i m) j x -
            gluingWarpedCoordinatePartial (fun y => gluingWarpedMetric W y i j) m x) := by
  simp only [gluingWarpedMetric_coordinatePartial hW]
  fin_cases l <;> fin_cases i <;> fin_cases j <;>
    simp [gluingWarpedChristoffel, gluingWarpedInverseMetric]
  all_goals field_simp [hpos.ne']

/-- Actual partial derivatives of all the Christoffel coefficients. -/
theorem gluingWarpedChristoffel_coordinatePartial {W : ℝ → ℝ}
    (hW : ContDiff ℝ 2 W) {x : ℝ × ℝ} (hpos : 0 < W x.1) (d l i j : Fin 2) :
    gluingWarpedCoordinatePartial (gluingWarpedChristoffel W l i j) d x =
      if d = 0 then
        if l = 0 then
          if i = 1 ∧ j = 1 then
            -(deriv W x.1 ^ 2 + W x.1 * deriv (deriv W) x.1) else 0
        else
          if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then
            (deriv (deriv W) x.1 * W x.1 - deriv W x.1 ^ 2) / W x.1 ^ 2 else 0
      else 0 := by
  have h₁ := (hW.differentiable (by norm_num) x.1).hasDerivAt
  have h₂ := (hW.differentiable_deriv_two x.1).hasDerivAt
  have hmul := gluingWarpedCoordinatePartial_radial (h₁.mul h₂).neg x.2 d
  have hdiv := gluingWarpedCoordinatePartial_radial (h₂.div h₁ hpos.ne') x.2 d
  fin_cases l <;> fin_cases i <;> fin_cases j
  all_goals unfold gluingWarpedChristoffel
  all_goals simp only [Fin.isValue]
  all_goals first
  | simpa [sq, mul_comm, mul_left_comm, mul_assoc, Pi.mul_apply, Pi.neg_apply] using hmul
  | simpa [sq, mul_comm, mul_left_comm, mul_assoc, Pi.div_apply] using hdiv
  | simpa using gluingWarpedCoordinatePartial_const 0 d x

/-- All components of the actual Riemann tensor are computed from the
proved connection derivatives and its literal composition terms. -/
theorem gluingWarpedRiemann_eq {W : ℝ → ℝ}
    (hW : ContDiff ℝ 2 W) {x : ℝ × ℝ} (hpos : 0 < W x.1) (l k i j : Fin 2) :
    gluingWarpedRiemann W l k i j x =
      (-deriv (deriv W) x.1 / W x.1) *
        ((if l = i then 1 else 0) * gluingWarpedMetric W x j k -
          (if l = j then 1 else 0) * gluingWarpedMetric W x i k) := by
  unfold gluingWarpedRiemann
  simp only [gluingWarpedChristoffel_coordinatePartial hW hpos]
  fin_cases l <;> fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [gluingWarpedChristoffel, gluingWarpedMetric] <;>
      field_simp [hpos.ne'] <;> ring

/-- The actual Riemann tensor applied multilinearly to arbitrary tangent
vectors, with every summand the computed connection curvature. -/
def gluingWarpedRiemannVector (W : ℝ → ℝ) (x : ℝ × ℝ)
    (u v w : Fin 2 → ℝ) (l : Fin 2) : ℝ :=
  ∑ k : Fin 2, ∑ i : Fin 2, ∑ j : Fin 2,
    gluingWarpedRiemann W l k i j x * u i * v j * w k

/-- The sectional numerator for arbitrary tangent vectors is the same
Gaussian factor times the metric Gram determinant. -/
theorem gluingWarpedRiemannVector_metricForm {W : ℝ → ℝ}
    (hW : ContDiff ℝ 2 W) {x : ℝ × ℝ} (hpos : 0 < W x.1) (u v : Fin 2 → ℝ) :
    gluingWarpedMetricForm W x (gluingWarpedRiemannVector W x u v v) u =
      (-deriv (deriv W) x.1 / W x.1) *
        (gluingWarpedMetricForm W x u u * gluingWarpedMetricForm W x v v -
          gluingWarpedMetricForm W x u v ^ 2) := by
  simp [gluingWarpedMetricForm, gluingWarpedRiemannVector,
    gluingWarpedRiemann_eq hW hpos, gluingWarpedMetric]
  ring

theorem gluingWarpedMetricForm_gram (W : ℝ → ℝ) (x : ℝ × ℝ) (u v : Fin 2 → ℝ) :
    gluingWarpedMetricForm W x u u * gluingWarpedMetricForm W x v v -
        gluingWarpedMetricForm W x u v ^ 2 =
      W x.1 ^ 2 * (u 0 * v 1 - u 1 * v 0) ^ 2 := by
  simp only [gluingWarpedMetricForm_apply]
  ring

/-- The actual sectional quotient has the derived Gaussian value on
every genuine two-dimensional tangent plane, not just the coordinate plane. -/
theorem gluingWarpedSectionalCurvature_eq {W : ℝ → ℝ}
    (hW : ContDiff ℝ 2 W) {x : ℝ × ℝ} (hpos : 0 < W x.1) (u v : Fin 2 → ℝ)
    (hplane : u 0 * v 1 - u 1 * v 0 ≠ 0) :
    gluingWarpedMetricForm W x (gluingWarpedRiemannVector W x u v v) u /
        (gluingWarpedMetricForm W x u u * gluingWarpedMetricForm W x v v -
          gluingWarpedMetricForm W x u v ^ 2) =
      -deriv (deriv W) x.1 / W x.1 := by
  rw [gluingWarpedRiemannVector_metricForm hW hpos]
  apply mul_div_cancel_right₀
  rw [gluingWarpedMetricForm_gram]
  exact mul_ne_zero (pow_ne_zero 2 hpos.ne') (pow_ne_zero 2 hplane)

/-- The genuine sectional quotient of the two coordinate directions.
Its numerator contracts the actual Riemann tensor with the actual metric. -/
def gluingWarpedGaussianCurvature (W : ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  (∑ l : Fin 2, gluingWarpedMetric W x 0 l * gluingWarpedRiemann W l 1 0 1 x) /
    (gluingWarpedMetric W x 0 0 * gluingWarpedMetric W x 1 1 -
      gluingWarpedMetric W x 0 1 * gluingWarpedMetric W x 1 0)

/-- The Gaussian curvature is derived from the constructed compatible,
torsion-free metric connection; it is not a stipulated curvature density. -/
theorem gluingWarpedGaussianCurvature_eq {W : ℝ → ℝ}
    (hW : ContDiff ℝ 2 W) {x : ℝ × ℝ} (hpos : 0 < W x.1) :
    gluingWarpedGaussianCurvature W x = -deriv (deriv W) x.1 / W x.1 := by
  unfold gluingWarpedGaussianCurvature
  simp only [gluingWarpedRiemann_eq hW hpos]
  simp [gluingWarpedMetric, hpos.ne']

/-- Multiplication by the actual metric area determinant gives the signed
Gaussian-curvature density `-W''`. -/
theorem gluingWarpedGaussianCurvature_mul_areaDensity {W : ℝ → ℝ}
    (hW : ContDiff ℝ 2 W) {x : ℝ × ℝ} (hpos : 0 < W x.1) :
    gluingWarpedGaussianCurvature W x * Real.sqrt (gluingWarpedMetric W x).det =
      -deriv (deriv W) x.1 := by
  rw [gluingWarpedGaussianCurvature_eq hW hpos, gluingWarpedMetric_areaDensity hpos]
  exact div_mul_cancel₀ _ hpos.ne'

/-- The actual localized collar warp satisfies every hypothesis of the
connection and curvature computation for each positive smoothing scale. -/
theorem gluingCollarLocalizedSmoothWarp_gaussianCurvature
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (b : ContDiffBump (0 : ℝ)) (x : ℝ × ℝ) :
    gluingWarpedGaussianCurvature (gluingCollarLocalizedSmoothWarp r ε b) x =
      -deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) x.1 /
        gluingCollarLocalizedSmoothWarp r ε b x.1 :=
  gluingWarpedGaussianCurvature_eq
    (gluingCollarLocalizedSmoothWarp_contDiff r hε b 2)
    (gluingCollarLocalizedSmoothWarp_pos hr hε.le b x.1)

/-- Actual localized smooth metrics have signed curvature density exactly
the negative literal second derivative used in the proved weak limit. -/
theorem gluingCollarLocalizedSmoothWarp_gaussianCurvature_mul_areaDensity
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (b : ContDiffBump (0 : ℝ)) (x : ℝ × ℝ) :
    gluingWarpedGaussianCurvature (gluingCollarLocalizedSmoothWarp r ε b) x *
        Real.sqrt (gluingWarpedMetric (gluingCollarLocalizedSmoothWarp r ε b) x).det =
      -deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) x.1 :=
  gluingWarpedGaussianCurvature_mul_areaDensity
    (gluingCollarLocalizedSmoothWarp_contDiff r hε b 2)
    (gluingCollarLocalizedSmoothWarp_pos hr hε.le b x.1)

#print axioms gluingWarpedChristoffel_metric_compatible
#print axioms gluingWarpedMetric_directionalPartial
#print axioms gluingWarpedMetric_complexDirectionalPartial
#print axioms gluingWarpedChristoffel_eq_metric_formula
#print axioms gluingWarpedRiemann_eq
#print axioms gluingWarpedSectionalCurvature_eq
#print axioms gluingWarpedGaussianCurvature_eq
#print axioms gluingCollarLocalizedSmoothWarp_gaussianCurvature_mul_areaDensity

end
end SystolicGrowth
