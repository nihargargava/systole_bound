module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingWarpedGaussianCurvature
public import Geometry.GluingChartMetric

@[expose] public section

/-!
# Gaussian curvature of the original Poincaré coordinate metric

The literal upper-half-plane tensor, actual coordinate partial derivatives,
metric-compatible torsion-free connection and its curvature are constructed.
Their sectional quotient is −1 and their Gram area density is y⁻². The tensor
is identified with the original native interior-chart bilinear form.
-/

open Set
open scoped BigOperators

namespace SystolicGrowth

noncomputable section

/-- The original Poincaré coordinate tensor. Only positive heights are used. -/
def hyperbolicGaussianMetric (x : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = j then (x.2 ^ 2)⁻¹ else 0

def hyperbolicGaussianInverseMetric (x : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = j then x.2 ^ 2 else 0

def hyperbolicGaussianMetricForm (x : ℝ × ℝ) (v w : Fin 2 → ℝ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, hyperbolicGaussianMetric x i j * v i * w j

theorem hyperbolicGaussianMetricForm_apply (x : ℝ × ℝ) (v w : Fin 2 → ℝ) :
    hyperbolicGaussianMetricForm x v w = (x.2 ^ 2)⁻¹ * (v 0 * w 0 + v 1 * w 1) := by
  simp [hyperbolicGaussianMetricForm, hyperbolicGaussianMetric]
  ring

/-- Exact identification with the original native Poincaré chart metric. -/
theorem hyperbolicGaussianMetricForm_eq_native (z v w : ℂ) :
    hyperbolicGaussianMetricForm (z.re, z.im) ![v.re, v.im] ![w.re, w.im] =
      gluingComplexHalfPlaneTangentForm z v w := by
  rw [hyperbolicGaussianMetricForm_apply, gluingComplexHalfPlaneTangentForm_apply]
  simp [Complex.mul_re, div_eq_mul_inv]
  ring

theorem hyperbolicGaussianMetric_inverse {x : ℝ × ℝ} (hy : x.2 ≠ 0) :
    hyperbolicGaussianMetric x * hyperbolicGaussianInverseMetric x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, hyperbolicGaussianMetric, hyperbolicGaussianInverseMetric, hy]

theorem hyperbolicGaussianMetric_det (x : ℝ × ℝ) :
    (hyperbolicGaussianMetric x).det = ((x.2 ^ 2)⁻¹) ^ 2 := by
  simp [Matrix.det_fin_two, hyperbolicGaussianMetric, pow_two]

theorem hyperbolicGaussianMetric_areaDensity (x : ℝ × ℝ) :
    Real.sqrt (hyperbolicGaussianMetric x).det = (x.2 ^ 2)⁻¹ := by
  rw [hyperbolicGaussianMetric_det, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]

theorem hyperbolicGaussianMetricForm_pos {x : ℝ × ℝ} (hy : 0 < x.2)
    {v : Fin 2 → ℝ} (hv : v ≠ 0) : 0 < hyperbolicGaussianMetricForm x v v := by
  have hv' : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    funext i
    fin_cases i <;> simp [h]
  rw [hyperbolicGaussianMetricForm_apply]
  apply mul_pos (inv_pos.mpr (sq_pos_of_pos hy))
  rcases hv' with h | h
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (v 1)]
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (v 0)]

theorem hyperbolicGaussianCoordinatePartial_vertical {f : ℝ → ℝ} {t f' : ℝ}
    (hf : HasDerivAt f f' t) (a : ℝ) (i : Fin 2) :
    gluingWarpedCoordinatePartial (fun x : ℝ × ℝ => f x.2) i (a, t) =
      if i = 1 then f' else 0 := by
  have h := hf.hasFDerivAt.comp (a, t)
    (hasFDerivAt_snd : HasFDerivAt (Prod.snd : ℝ × ℝ → ℝ)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (a, t))
  rw [gluingWarpedCoordinatePartial]
  change fderiv ℝ (f ∘ Prod.snd) (a, t) _ = _
  rw [h.fderiv]
  fin_cases i <;> simp

private theorem inverse_square_hasDerivAt {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun t : ℝ => (t ^ 2)⁻¹) (-2 / y ^ 3) y := by
  convert ((hasDerivAt_id y).pow 2).inv (pow_ne_zero 2 hy) using 1 <;> try rfl
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  field_simp [hy]

theorem hyperbolicGaussianMetric_coordinatePartial {x : ℝ × ℝ} (hy : x.2 ≠ 0)
    (d i j : Fin 2) :
    gluingWarpedCoordinatePartial (fun z => hyperbolicGaussianMetric z i j) d x =
      if d = 1 ∧ i = j then -2 / x.2 ^ 3 else 0 := by
  by_cases hij : i = j
  · subst j
    simpa [hyperbolicGaussianMetric] using
      hyperbolicGaussianCoordinatePartial_vertical (inverse_square_hasDerivAt hy) x.1 d
  · simp only [hyperbolicGaussianMetric, if_neg hij]
    rw [gluingWarpedCoordinatePartial_const]
    simp [hij]

def hyperbolicChristoffelCoefficient (l i j : Fin 2) : ℝ :=
  if l = 0 then if i ≠ j then -1 else 0
  else if i = j then if i = 0 then 1 else -1 else 0

/-- Connection derived below by the actual coordinate Koszul formula. -/
def hyperbolicChristoffel (l i j : Fin 2) (x : ℝ × ℝ) : ℝ :=
  hyperbolicChristoffelCoefficient l i j / x.2

theorem hyperbolicChristoffel_torsion_free (l i j : Fin 2) (x : ℝ × ℝ) :
    hyperbolicChristoffel l i j x = hyperbolicChristoffel l j i x := by
  fin_cases l <;> fin_cases i <;> fin_cases j <;>
    simp [hyperbolicChristoffel, hyperbolicChristoffelCoefficient]

theorem hyperbolicChristoffel_metric_compatible {x : ℝ × ℝ} (hy : 0 < x.2)
    (d i j : Fin 2) :
    gluingWarpedCoordinatePartial (fun z => hyperbolicGaussianMetric z i j) d x =
      ∑ l : Fin 2, (hyperbolicChristoffel l d i x * hyperbolicGaussianMetric x l j +
        hyperbolicChristoffel l d j x * hyperbolicGaussianMetric x i l) := by
  rw [hyperbolicGaussianMetric_coordinatePartial hy.ne']
  fin_cases d <;> fin_cases i <;> fin_cases j <;>
    simp [hyperbolicChristoffel, hyperbolicChristoffelCoefficient, hyperbolicGaussianMetric]
  all_goals field_simp
  all_goals ring

theorem hyperbolicChristoffel_eq_metric_formula {x : ℝ × ℝ} (hy : 0 < x.2)
    (l i j : Fin 2) :
    hyperbolicChristoffel l i j x = (1 / 2 : ℝ) *
      ∑ m : Fin 2, hyperbolicGaussianInverseMetric x l m *
        (gluingWarpedCoordinatePartial (fun z => hyperbolicGaussianMetric z m j) i x +
          gluingWarpedCoordinatePartial (fun z => hyperbolicGaussianMetric z i m) j x -
            gluingWarpedCoordinatePartial (fun z => hyperbolicGaussianMetric z i j) m x) := by
  simp only [hyperbolicGaussianMetric_coordinatePartial hy.ne']
  fin_cases l <;> fin_cases i <;> fin_cases j <;>
    simp [hyperbolicChristoffel, hyperbolicChristoffelCoefficient, hyperbolicGaussianInverseMetric]
  all_goals field_simp [hy.ne']

theorem hyperbolicChristoffel_coordinatePartial {x : ℝ × ℝ} (hy : x.2 ≠ 0)
    (d l i j : Fin 2) :
    gluingWarpedCoordinatePartial (hyperbolicChristoffel l i j) d x =
      if d = 1 then -hyperbolicChristoffelCoefficient l i j / x.2 ^ 2 else 0 := by
  have h := ((hasDerivAt_id x.2).inv hy).const_mul (hyperbolicChristoffelCoefficient l i j)
  have hh := hyperbolicGaussianCoordinatePartial_vertical h x.1 d
  unfold hyperbolicChristoffel
  simpa [div_eq_mul_inv, neg_mul, mul_neg] using hh

/-- The genuine derivative-plus-connection-composition Riemann tensor. -/
def hyperbolicRiemann (l k i j : Fin 2) (x : ℝ × ℝ) : ℝ :=
  gluingWarpedCoordinatePartial (hyperbolicChristoffel l j k) i x -
    gluingWarpedCoordinatePartial (hyperbolicChristoffel l i k) j x +
      ∑ m : Fin 2, (hyperbolicChristoffel l i m x * hyperbolicChristoffel m j k x -
        hyperbolicChristoffel l j m x * hyperbolicChristoffel m i k x)

theorem hyperbolicRiemann_eq {x : ℝ × ℝ} (hy : 0 < x.2) (l k i j : Fin 2) :
    hyperbolicRiemann l k i j x =
      -((if l = i then 1 else 0) * hyperbolicGaussianMetric x j k -
        (if l = j then 1 else 0) * hyperbolicGaussianMetric x i k) := by
  unfold hyperbolicRiemann
  simp only [hyperbolicChristoffel_coordinatePartial hy.ne']
  fin_cases l <;> fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [hyperbolicChristoffel, hyperbolicChristoffelCoefficient, hyperbolicGaussianMetric] <;>
      field_simp [hy.ne'] <;> ring

/-- The computed connection curvature applied to arbitrary tangent vectors. -/
def hyperbolicRiemannVector (x : ℝ × ℝ) (u v w : Fin 2 → ℝ) (l : Fin 2) : ℝ :=
  ∑ k : Fin 2, ∑ i : Fin 2, ∑ j : Fin 2,
    hyperbolicRiemann l k i j x * u i * v j * w k

theorem hyperbolicRiemannVector_metricForm {x : ℝ × ℝ} (hy : 0 < x.2)
    (u v : Fin 2 → ℝ) :
    hyperbolicGaussianMetricForm x (hyperbolicRiemannVector x u v v) u =
      -(hyperbolicGaussianMetricForm x u u * hyperbolicGaussianMetricForm x v v -
        hyperbolicGaussianMetricForm x u v ^ 2) := by
  simp [hyperbolicGaussianMetricForm, hyperbolicRiemannVector,
    hyperbolicRiemann_eq hy, hyperbolicGaussianMetric]
  ring

theorem hyperbolicGaussianMetricForm_gram (x : ℝ × ℝ) (u v : Fin 2 → ℝ) :
    hyperbolicGaussianMetricForm x u u * hyperbolicGaussianMetricForm x v v -
        hyperbolicGaussianMetricForm x u v ^ 2 =
      ((x.2 ^ 2)⁻¹) ^ 2 * (u 0 * v 1 - u 1 * v 0) ^ 2 := by
  simp only [hyperbolicGaussianMetricForm_apply]
  ring

/-- Every genuine tangent plane has curvature −1, not merely the coordinate plane. -/
theorem hyperbolicSectionalCurvature_eq_neg_one {x : ℝ × ℝ} (hy : 0 < x.2)
    (u v : Fin 2 → ℝ) (hplane : u 0 * v 1 - u 1 * v 0 ≠ 0) :
    hyperbolicGaussianMetricForm x (hyperbolicRiemannVector x u v v) u /
      (hyperbolicGaussianMetricForm x u u * hyperbolicGaussianMetricForm x v v -
        hyperbolicGaussianMetricForm x u v ^ 2) = -1 := by
  rw [hyperbolicRiemannVector_metricForm hy]
  have hgram : hyperbolicGaussianMetricForm x u u * hyperbolicGaussianMetricForm x v v -
      hyperbolicGaussianMetricForm x u v ^ 2 ≠ 0 := by
    rw [hyperbolicGaussianMetricForm_gram]
    exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero (pow_ne_zero 2 hy.ne')))
      (pow_ne_zero 2 hplane)
  rw [neg_div, div_self hgram]

def hyperbolicGaussianCurvature (x : ℝ × ℝ) : ℝ :=
  (∑ l : Fin 2, hyperbolicGaussianMetric x 0 l * hyperbolicRiemann l 1 0 1 x) /
    (hyperbolicGaussianMetric x 0 0 * hyperbolicGaussianMetric x 1 1 -
      hyperbolicGaussianMetric x 0 1 * hyperbolicGaussianMetric x 1 0)

theorem hyperbolicGaussianCurvature_eq_neg_one {x : ℝ × ℝ} (hy : 0 < x.2) :
    hyperbolicGaussianCurvature x = -1 := by
  unfold hyperbolicGaussianCurvature
  simp only [hyperbolicRiemann_eq hy]
  simp [hyperbolicGaussianMetric, hy.ne']

theorem hyperbolicGaussianCurvature_mul_areaDensity {x : ℝ × ℝ} (hy : 0 < x.2) :
    hyperbolicGaussianCurvature x * Real.sqrt (hyperbolicGaussianMetric x).det =
      -(x.2 ^ 2)⁻¹ := by
  rw [hyperbolicGaussianCurvature_eq_neg_one hy, hyperbolicGaussianMetric_areaDensity]
  ring

#print axioms hyperbolicGaussianMetricForm_eq_native
#print axioms hyperbolicChristoffel_metric_compatible
#print axioms hyperbolicChristoffel_eq_metric_formula
#print axioms hyperbolicRiemann_eq
#print axioms hyperbolicSectionalCurvature_eq_neg_one
#print axioms hyperbolicGaussianCurvature_mul_areaDensity

end
end SystolicGrowth
