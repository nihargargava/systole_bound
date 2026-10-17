module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.DirichletCyclicBoundary
public import Geometry.GluingCircleTransport
public import Mathlib.Analysis.SpecialFunctions.Artanh

@[expose] public section

/-!
# Actual centered hyperbolic polar collar coordinates

The centered disk chart is the actual affine normalization followed by the
Cayley transform. Its norm is `tanh (dist o z / 2)`. Inverting that radial
formula gives polar coordinates on each positive-radius open annulus, with
angular coordinate in `Circle` and radial coordinate exactly `dist o z`.
All coordinate maps are explicit; this file makes no differentiability or
warped-metric identification claim.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane Topology ComplexConjugate

namespace SystolicGrowth

/-- The disk-chart norm reads the actual hyperbolic radius. -/
theorem norm_discChart_eq_tanh_half_dist (o z : ℍ) :
    ‖Vendored.RiemannDynamics.discChart o z‖ = Real.tanh (dist o z / 2) := by
  rw [Vendored.RiemannDynamics.discChart_eq, norm_div,
    ← Complex.dist_eq, ← Complex.dist_eq]
  rw [← UpperHalfPlane.tanh_half_dist z o, dist_comm]

/-- Explicit inverse of the centered disk chart. -/
noncomputable def gluingDiscChartInverse (o : ℍ) (u : ball (0 : ℂ) 1) : ℍ :=
  ⟨(o.re : ℂ) + (o.im : ℂ) * Vendored.RiemannDynamics.cayleyToHalfPlane u, by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, zero_mul, add_zero, zero_add]
    exact mul_pos o.im_pos (Vendored.RiemannDynamics.cayleyToHalfPlane_im_pos u.2)⟩

theorem discChart_gluingDiscChartInverse (o : ℍ) (u : ball (0 : ℂ) 1) :
    Vendored.RiemannDynamics.discChart o (gluingDiscChartInverse o u) = u := by
  have him : (o.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr o.im_pos.ne'
  have hnormal : (((gluingDiscChartInverse o u : ℍ) : ℂ) - (o.re : ℂ)) /
      (o.im : ℂ) = Vendored.RiemannDynamics.cayleyToHalfPlane u := by
    change (((o.re : ℂ) + (o.im : ℂ) * Vendored.RiemannDynamics.cayleyToHalfPlane u) -
      (o.re : ℂ)) / (o.im : ℂ) = _
    field_simp
    ring
  unfold Vendored.RiemannDynamics.discChart
  rw [hnormal]
  exact Vendored.RiemannDynamics.halfPlaneToCayley_cayleyToHalfPlane u.2

theorem gluingDiscChartInverse_continuous (o : ℍ) : Continuous (gluingDiscChartInverse o) := by
  apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
  change Continuous (fun u : ball (0 : ℂ) 1 =>
    (o.re : ℂ) + (o.im : ℂ) * (Complex.I * (1 + (u : ℂ)) / (1 - (u : ℂ))))
  exact continuous_const.add (continuous_const.mul
    ((continuous_const.mul (continuous_const.add continuous_subtype_val)).div
      (continuous_const.sub continuous_subtype_val)
      (fun u => Vendored.RiemannDynamics.one_sub_ne_zero_of_mem_ball u.2)))

private theorem tanh_half_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Real.tanh (t / 2) := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr (by linarith)) (Real.cosh_pos _).le

theorem Internal.GluingPolarCollarHelpers.tanh_half_pos {t : ℝ} (ht : 0 < t) : 0 < Real.tanh (t / 2) := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)

private theorem continuous_tanh_half : Continuous (fun t : ℝ => Real.tanh (t / 2)) := by
  simp_rw [Real.tanh_eq_sinh_div_cosh]
  exact (Real.continuous_sinh.comp (continuous_id.div_const 2)).div
    (Real.continuous_cosh.comp (continuous_id.div_const 2)) (fun t => (Real.cosh_pos _).ne')

theorem Internal.GluingPolarCollarHelpers.gluingPolarDisk_mem_ball (u : Circle) (t : ℝ) :
    (Real.tanh (t / 2) : ℂ) * (u : ℂ) ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball, dist_zero_right, norm_mul, Circle.norm_coe, mul_one,
    Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_tanh_lt_one _

/-- The actual polar point is the centered inverse Cayley image of
`tanh(t/2) * u`, not a choice of a point with prescribed coordinates. -/
noncomputable def gluingPolarPoint (o : ℍ) (u : Circle) (t : ℝ) : ℍ :=
  gluingDiscChartInverse o
    ⟨(Real.tanh (t / 2) : ℂ) * (u : ℂ), Internal.GluingPolarCollarHelpers.gluingPolarDisk_mem_ball u t⟩

theorem discChart_gluingPolarPoint (o : ℍ) (u : Circle) (t : ℝ) :
    Vendored.RiemannDynamics.discChart o (gluingPolarPoint o u t) =
      (Real.tanh (t / 2) : ℂ) * (u : ℂ) :=
  discChart_gluingDiscChartInverse o _

/-- The explicit inverse has exactly the prescribed hyperbolic radius. -/
theorem dist_gluingPolarPoint (o : ℍ) (u : Circle) {t : ℝ} (ht : 0 ≤ t) :
    dist o (gluingPolarPoint o u t) = t := by
  have hnorm : ‖Vendored.RiemannDynamics.discChart o (gluingPolarPoint o u t)‖ =
      Real.tanh (t / 2) := by
    rw [discChart_gluingPolarPoint, norm_mul, Circle.norm_coe, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tanh_half_nonneg ht)]
  rw [norm_discChart_eq_tanh_half_dist] at hnorm
  have h := Real.tanh_injective hnorm
  linarith

theorem gluingPolarPoint_continuous (o : ℍ) :
    Continuous (fun p : Circle × ℝ => gluingPolarPoint o p.1 p.2) := by
  have hangle : Continuous (fun p : Circle × ℝ => (p.1 : ℂ)) :=
    continuous_subtype_val.comp continuous_fst
  have hradius : Continuous (fun p : Circle × ℝ => (Real.tanh (p.2 / 2) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_tanh_half.comp continuous_snd)
  exact (gluingDiscChartInverse_continuous o).comp
    ((hradius.mul hangle).subtype_mk (fun p => Internal.GluingPolarCollarHelpers.gluingPolarDisk_mem_ball p.1 p.2))

/-- The actual open annulus, with hyperbolic distance as its radial data. -/
abbrev GluingPolarAnnulus (o : ℍ) (r R : ℝ) := {z : ℍ // dist o z ∈ Ioo r R}

theorem Internal.GluingPolarCollarHelpers.gluingPolarAnnulus_ne_center
    (o : ℍ) (r R : ℝ) (hr : 0 < r) (z : GluingPolarAnnulus o r R) : z.1 ≠ o := by
  intro hz
  have h := z.2.1
  rw [hz, dist_self] at h
  linarith

/-- The actual angular direction on the positive-radius annulus. -/
noncomputable def gluingPolarAngle
    (o : ℍ) (r R : ℝ) (hr : 0 < r) (z : GluingPolarAnnulus o r R) : Circle :=
  ⟨hyperbolicRadialDirection o z.1, by
    apply mem_sphere_zero_iff_norm.mpr
    have hne := Vendored.RiemannDynamics.discChart_ne_zero
      (Internal.GluingPolarCollarHelpers.gluingPolarAnnulus_ne_center o r R hr z)
    rw [hyperbolicRadialDirection, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr hne)]⟩

theorem gluingPolarAngle_continuous (o : ℍ) (r R : ℝ) (hr : 0 < r) :
    Continuous (gluingPolarAngle o r R hr) := by
  apply Continuous.subtype_mk
  have hc : Continuous (fun z : GluingPolarAnnulus o r R =>
      Vendored.RiemannDynamics.discChart o z.1) :=
    (continuous_discChart o).comp continuous_subtype_val
  exact hc.div (Complex.continuous_ofReal.comp hc.norm) (fun z =>
    Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr
      (Vendored.RiemannDynamics.discChart_ne_zero
        (Internal.GluingPolarCollarHelpers.gluingPolarAnnulus_ne_center o r R hr z))).ne')

/-- The explicit annulus-valued inverse coordinate map. -/
noncomputable def gluingPolarCollarInverse (o : ℍ) (r R : ℝ) (hr : 0 < r)
    (p : Circle × Ioo r R) : GluingPolarAnnulus o r R :=
  ⟨gluingPolarPoint o p.1 p.2.1, by
    rw [dist_gluingPolarPoint o p.1 (hr.trans p.2.2.1).le]
    exact p.2.2⟩

theorem gluingPolarCollarInverse_continuous (o : ℍ) (r R : ℝ) (hr : 0 < r) :
    Continuous (gluingPolarCollarInverse o r R hr) := by
  have hproj : Continuous (fun p : Circle × Ioo r R => (p.1, (p.2 : ℝ))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hpoint := (gluingPolarPoint_continuous o).comp hproj
  exact hpoint.subtype_mk (fun p => by
    change dist o (gluingPolarPoint o p.1 p.2.1) ∈ Ioo r R
    rw [dist_gluingPolarPoint o p.1 (hr.trans p.2.2.1).le]
    exact p.2.2)

/-- The concrete centered polar collar homeomorphism. The radius is the
actual hyperbolic distance, not the Euclidean disk-chart norm. -/
noncomputable def gluingPolarCollarHomeomorph (o : ℍ) (r R : ℝ) (hr : 0 < r) :
    GluingPolarAnnulus o r R ≃ₜ Circle × Ioo r R where
  toFun z := (gluingPolarAngle o r R hr z, ⟨dist o z.1, z.2⟩)
  invFun := gluingPolarCollarInverse o r R hr
  left_inv z := by
    apply Subtype.ext
    apply discChart_injective o
    change Vendored.RiemannDynamics.discChart o
      (gluingPolarPoint o (gluingPolarAngle o r R hr z) (dist o z.1)) =
        Vendored.RiemannDynamics.discChart o z.1
    rw [discChart_gluingPolarPoint, ← norm_discChart_eq_tanh_half_dist]
    change (‖Vendored.RiemannDynamics.discChart o z.1‖ : ℂ) *
      (Vendored.RiemannDynamics.discChart o z.1 /
        (‖Vendored.RiemannDynamics.discChart o z.1‖ : ℂ)) =
      Vendored.RiemannDynamics.discChart o z.1
    have hne : (‖Vendored.RiemannDynamics.discChart o z.1‖ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr
        (Vendored.RiemannDynamics.discChart_ne_zero
          (Internal.GluingPolarCollarHelpers.gluingPolarAnnulus_ne_center o r R hr z))).ne'
    field_simp
  right_inv p := by
    have ht : 0 < (p.2 : ℝ) := hr.trans p.2.2.1
    apply Prod.ext
    · apply Circle.ext
      change hyperbolicRadialDirection o (gluingPolarPoint o p.1 p.2.1) = (p.1 : ℂ)
      rw [hyperbolicRadialDirection, discChart_gluingPolarPoint, norm_mul,
        Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Internal.GluingPolarCollarHelpers.tanh_half_pos ht)]
      simpa only [mul_comm] using
        mul_div_cancel_right₀ (p.1 : ℂ) (Complex.ofReal_ne_zero.mpr (Internal.GluingPolarCollarHelpers.tanh_half_pos ht).ne')
    · apply Subtype.ext
      exact dist_gluingPolarPoint o p.1 ht.le
  continuous_toFun :=
    (gluingPolarAngle_continuous o r R hr).prodMk
      ((continuous_const.dist continuous_subtype_val).subtype_mk (fun z => z.2))
  continuous_invFun := gluingPolarCollarInverse_continuous o r R hr

/-- The radial coordinate is exactly the actual centered distance. -/
@[simp] theorem gluingPolarCollarHomeomorph_radial
    (o : ℍ) (r R : ℝ) (hr : 0 < r) (z : GluingPolarAnnulus o r R) :
    ((gluingPolarCollarHomeomorph o r R hr z).2 : ℝ) = dist o z.1 := rfl

/-- The inverse coordinate map has the displayed explicit polar formula. -/
@[simp] theorem gluingPolarCollarHomeomorph_symm_apply
    (o : ℍ) (r R : ℝ) (hr : 0 < r) (p : Circle × Ioo r R) :
    ((gluingPolarCollarHomeomorph o r R hr).symm p).1 = gluingPolarPoint o p.1 p.2.1 := rfl

/-- The chosen affine center transport introduces no angular phase factor. -/
theorem discChart_toSL2R (o z : ℍ) :
    Vendored.RiemannDynamics.discChart o (o.toSL2R • z) =
      Vendored.RiemannDynamics.discChart (I : ℍ) z := by
  have hS : (Real.sqrt o.im : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr o.im_pos).ne'
  have h := Vendored.RiemannDynamics.discChart_smul o.toSL2R (I : ℍ) z
  simpa [UpperHalfPlane.coe_toSL2R, hS] using h

/-- The actual half-plane reflection conjugates centered disk coordinates. -/
theorem discChart_gluingMirror (o z : ℍ) :
    Vendored.RiemannDynamics.discChart (gluingMirror o) (gluingMirror z) =
      conj (Vendored.RiemannDynamics.discChart o z) := by
  rw [Vendored.RiemannDynamics.discChart_eq, Vendored.RiemannDynamics.discChart_eq]
  simp only [gluingMirror, map_div₀, map_sub, map_neg, Complex.conj_conj]
  rw [show -(conj (z : ℂ)) - -(conj (o : ℂ)) =
      -((conj (z : ℂ)) - (conj (o : ℂ))) by ring,
    show -(conj (z : ℂ)) - -(o : ℂ) = -((conj (z : ℂ)) - (o : ℂ)) by ring,
    neg_div_neg_eq]

/-- The exact reflected attachment acts by complex conjugation in the
polar charts of its actual source and target centers. -/
theorem discChart_gluingCircleMap (o p z : ℍ) :
    Vendored.RiemannDynamics.discChart p (gluingCircleMap o p z) =
      conj (Vendored.RiemannDynamics.discChart o z) := by
  unfold gluingCircleMap
  rw [discChart_toSL2R]
  have hm := discChart_gluingMirror (I : ℍ) (o.toSL2R⁻¹ • z)
  rw [gluingMirror_I] at hm
  rw [hm]
  congr 1
  have h := discChart_toSL2R o (o.toSL2R⁻¹ • z)
  simpa only [smul_inv_smul] using h.symm

/-- Reflection preserves the actual radius and reverses the angular
coordinate by the group inverse in `Circle`. -/
theorem gluingCircleMap_gluingPolarPoint (o p : ℍ) (u : Circle) (t : ℝ) :
    gluingCircleMap o p (gluingPolarPoint o u t) = gluingPolarPoint p u⁻¹ t := by
  apply discChart_injective p
  rw [discChart_gluingCircleMap, discChart_gluingPolarPoint, discChart_gluingPolarPoint,
    map_mul, Complex.conj_ofReal, Circle.coe_inv_eq_conj]

#print axioms dist_gluingPolarPoint
#print axioms gluingPolarCollarHomeomorph
#print axioms gluingPolarCollarHomeomorph_radial
#print axioms gluingCircleMap_gluingPolarPoint

end SystolicGrowth
