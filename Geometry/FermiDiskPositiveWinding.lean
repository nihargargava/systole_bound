module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceTwoCenterDiskChart
public import Geometry.GluingPolarCollar
public import Geometry.ConvexPuncturedDomainCircle

@[expose] public section

/-!
# Positive winding of the oriented Fermi disk chart

The complex chart uses transverse real and axial imaginary coordinates.
Its centered Cayley image has positive scalar product with `-I * z`.
This gives the nonvanishing straight homotopy needed to compare its boundary
with positive polar winding; the quarter-turn is retained explicitly.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane ComplexConjugate ContinuousMap unitInterval MatrixGroups

namespace SystolicGrowth

noncomputable section

/-- The literal oriented Fermi chart before its actual deck transport. -/
def orientedFermiDiskPoint (m a b : ℝ) (z : ℂ) : ℍ :=
  gluingFinFermiPoint 1 (m + a * z.im) (b * z.re)

private theorem real_mul_tanh_nonneg {b : ℝ} (hb : 0 < b) (r : ℝ) :
    0 ≤ r * Real.tanh (b * r) := by
  rw [Real.tanh_eq_sinh_div_cosh, ← mul_div_assoc]
  apply div_nonneg _ (Real.cosh_pos _).le
  rcases le_total 0 r with hr | hr
  · exact mul_nonneg hr (Real.sinh_nonneg_iff.mpr (mul_nonneg hb.le hr))
  · exact mul_nonneg_of_nonpos_of_nonpos hr
      (Real.sinh_nonpos_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hb.le hr))

private theorem real_mul_tanh_pos {b : ℝ} (hb : 0 < b) {r : ℝ} (hr : r ≠ 0) :
    0 < r * Real.tanh (b * r) := by
  rw [Real.tanh_eq_sinh_div_cosh, ← mul_div_assoc]
  apply div_pos _ (Real.cosh_pos _)
  rcases lt_or_gt_of_ne hr with hr | hr
  · exact mul_pos_of_neg_of_neg hr
      (Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg hb hr))
  · exact mul_pos hr (Real.sinh_pos_iff.mpr (mul_pos hb hr))

private theorem real_mul_exp_sq_sub_nonneg {a : ℝ} (ha : 0 < a) (m r : ℝ) :
    0 ≤ r * (Real.exp (m + a * r) ^ 2 - Real.exp m ^ 2) := by
  rcases le_total 0 r with hr | hr
  · apply mul_nonneg hr
    have he : Real.exp m ≤ Real.exp (m + a * r) :=
      Real.exp_le_exp.mpr (by nlinarith)
    nlinarith [Real.exp_pos m]
  · apply mul_nonneg_of_nonpos_of_nonpos hr
    have he : Real.exp (m + a * r) ≤ Real.exp m :=
      Real.exp_le_exp.mpr (by nlinarith)
    nlinarith [Real.exp_pos (m + a * r)]

private theorem real_mul_exp_sq_sub_pos {a : ℝ} (ha : 0 < a) (m : ℝ)
    {r : ℝ} (hr : r ≠ 0) :
    0 < r * (Real.exp (m + a * r) ^ 2 - Real.exp m ^ 2) := by
  rcases lt_or_gt_of_ne hr with hr | hr
  · apply mul_pos_of_neg_of_neg hr
    have he : Real.exp (m + a * r) < Real.exp m :=
      Real.exp_lt_exp.mpr (by nlinarith)
    nlinarith [Real.exp_pos (m + a * r)]
  · apply mul_pos hr
    have he : Real.exp m < Real.exp (m + a * r) :=
      Real.exp_lt_exp.mpr (by nlinarith)
    nlinarith [Real.exp_pos m]

/-- Exact real part of the centered Cayley chart on the oriented Fermi map. -/
theorem orientedFermiDiskPoint_discChart_re (m a b : ℝ) (z : ℂ) :
    (Vendored.RiemannDynamics.discChart (orientedFermiDiskPoint m a b 0)
      (orientedFermiDiskPoint m a b z)).re =
      (Real.exp (m + a * z.im) ^ 2 - Real.exp m ^ 2) /
        Complex.normSq ((orientedFermiDiskPoint m a b z : ℂ) -
          conj (orientedFermiDiskPoint m a b 0 : ℂ)) := by
  rw [Vendored.RiemannDynamics.discChart_eq, Complex.div_re]
  have hn := gluingFinFermiPoint_norm 1 (m + a * z.im) (b * z.re)
  have hsq := Complex.sq_norm (orientedFermiDiskPoint m a b z : ℂ)
  simp only [orientedFermiDiskPoint, Complex.zero_re, Complex.zero_im, mul_zero,
    add_zero, gluingFinFermiPoint_re, gluingFinFermiPoint_im, one_mul,
    Real.tanh_zero, Real.cosh_zero, div_one, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
    sub_zero, sub_neg_eq_add] at *
  rw [← add_div]
  congr 1
  rw [hn] at hsq
  rw [Complex.normSq_apply] at hsq
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, gluingFinFermiPoint_re,
    gluingFinFermiPoint_im, one_mul] at hsq
  nlinarith

/-- Exact imaginary part, including the quarter-turn's negative sign. -/
theorem orientedFermiDiskPoint_discChart_im (m a b : ℝ) (z : ℂ) :
    (Vendored.RiemannDynamics.discChart (orientedFermiDiskPoint m a b 0)
      (orientedFermiDiskPoint m a b z)).im =
      -(2 * Real.exp m * Real.exp (m + a * z.im) * Real.tanh (b * z.re)) /
        Complex.normSq ((orientedFermiDiskPoint m a b z : ℂ) -
          conj (orientedFermiDiskPoint m a b 0 : ℂ)) := by
  rw [Vendored.RiemannDynamics.discChart_eq, Complex.div_im]
  simp only [orientedFermiDiskPoint, Complex.zero_re, Complex.zero_im, mul_zero,
    add_zero, gluingFinFermiPoint_re, gluingFinFermiPoint_im, one_mul,
    Real.tanh_zero, Real.cosh_zero, div_one, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
    sub_zero, sub_neg_eq_add]
  ring

/-- The Cayley image and the positive quarter-turned coordinate point make
an acute angle. This is strict for every nonzero coordinate point. -/
theorem orientedFermiDiskPoint_discChart_positiveDot (m : ℝ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {z : ℂ} (hz : z ≠ 0) :
    0 < z.im *
        (Vendored.RiemannDynamics.discChart (orientedFermiDiskPoint m a b 0)
          (orientedFermiDiskPoint m a b z)).re -
      z.re *
        (Vendored.RiemannDynamics.discChart (orientedFermiDiskPoint m a b 0)
          (orientedFermiDiskPoint m a b z)).im := by
  rw [orientedFermiDiskPoint_discChart_re, orientedFermiDiskPoint_discChart_im]
  let D := Complex.normSq ((orientedFermiDiskPoint m a b z : ℂ) -
    conj (orientedFermiDiskPoint m a b 0 : ℂ))
  have hD : 0 < D := Complex.normSq_pos.mpr
    (Vendored.RiemannDynamics.sub_conj_ne_zero _ _)
  have hx := real_mul_tanh_nonneg hb z.re
  have hy := real_mul_exp_sq_sub_nonneg ha m z.im
  have hxy : 0 < z.im * (Real.exp (m + a * z.im) ^ 2 - Real.exp m ^ 2) +
      (2 * Real.exp m * Real.exp (m + a * z.im)) *
        (z.re * Real.tanh (b * z.re)) := by
    by_cases hre : z.re = 0
    · have him : z.im ≠ 0 := by
        intro him
        apply hz
        apply Complex.ext <;> simpa using (by assumption)
      exact add_pos_of_pos_of_nonneg (real_mul_exp_sq_sub_pos ha m him)
        (mul_nonneg (by positivity) hx)
    · exact add_pos_of_nonneg_of_pos hy
        (mul_pos (by positivity) (real_mul_tanh_pos hb hre))
  have heq : z.im * ((Real.exp (m + a * z.im) ^ 2 - Real.exp m ^ 2) / D) -
      z.re * (-(2 * Real.exp m * Real.exp (m + a * z.im) *
        Real.tanh (b * z.re)) / D) =
      (z.im * (Real.exp (m + a * z.im) ^ 2 - Real.exp m ^ 2) +
        (2 * Real.exp m * Real.exp (m + a * z.im)) *
          (z.re * Real.tanh (b * z.re))) / D := by ring
  rw [heq]
  exact div_pos hxy hD

#print axioms orientedFermiDiskPoint_discChart_positiveDot

/-- The actual global oriented Fermi disk homeomorphism. -/
def orientedFermiDiskHomeomorph (m a b : ℝ) (ha : 0 < a) (hb : 0 < b) : ℂ ≃ₜ ℍ :=
  (orientedEllipseCoordinateHomeomorph m a b ha.ne' hb.ne').trans
    (ExerciseGluingPreparation.gluingFinFermiHomeomorph 1 one_pos)

@[simp]
theorem orientedFermiDiskHomeomorph_apply (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (z : ℂ) :
    orientedFermiDiskHomeomorph m a b ha hb z = orientedFermiDiskPoint m a b z := rfl

/-- Positive polar angle corresponding to the coordinate orientation. -/
def fermiPositivePolarAngle (θ : Circle) : Circle :=
  ⟨-Complex.I * (θ : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    simp only [norm_mul, norm_neg, Complex.norm_I, Circle.norm_coe, one_mul]⟩

theorem fermiPositivePolarAngle_continuous : Continuous fermiPositivePolarAngle := by
  exact (continuous_const.mul continuous_subtype_val).subtype_mk _

/-- Pull back the literal positive polar circle by the actual Fermi chart. -/
def fermiPositivePolarCoordinate (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (ρ : ℝ) (θ : Circle) : ℂ :=
  (orientedFermiDiskHomeomorph m a b ha hb).symm
    (gluingPolarPoint (orientedFermiDiskPoint m a b 0) (fermiPositivePolarAngle θ) ρ)

set_option backward.isDefEq.respectTransparency false in
theorem fermiPositivePolarCoordinate_continuous (m a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (ρ : ℝ) :
    Continuous (fermiPositivePolarCoordinate m a b ha hb ρ) := by
  have hp : Continuous (fun θ : Circle =>
      gluingPolarPoint (orientedFermiDiskPoint m a b 0) (fermiPositivePolarAngle θ) ρ) := by
    have hc : Continuous (fun θ : Circle => (fermiPositivePolarAngle θ : ℂ)) :=
      continuous_subtype_val.comp fermiPositivePolarAngle_continuous
    have hd : Continuous (fun θ : Circle =>
        (Real.tanh (ρ / 2) : ℂ) * (fermiPositivePolarAngle θ : ℂ)) :=
      continuous_const.mul hc
    have hmem : ∀ θ : Circle,
        (Real.tanh (ρ / 2) : ℂ) * (fermiPositivePolarAngle θ : ℂ) ∈ ball (0 : ℂ) 1 := by
      intro θ
      rw [mem_ball_zero_iff, norm_mul, Circle.norm_coe, mul_one,
        Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_tanh_lt_one _
    change Continuous (fun θ : Circle => gluingDiscChartInverse
      (orientedFermiDiskPoint m a b 0) ⟨_, hmem θ⟩)
    exact (gluingDiscChartInverse_continuous _).comp (hd.subtype_mk hmem)
  unfold fermiPositivePolarCoordinate
  exact (orientedFermiDiskHomeomorph m a b ha hb).symm.continuous.comp hp

@[simp]
theorem orientedFermiDiskPoint_positivePolarCoordinate (m a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (ρ : ℝ) (θ : Circle) :
    orientedFermiDiskPoint m a b (fermiPositivePolarCoordinate m a b ha hb ρ θ) =
      gluingPolarPoint (orientedFermiDiskPoint m a b 0) (fermiPositivePolarAngle θ) ρ :=
  (orientedFermiDiskHomeomorph m a b ha hb).apply_symm_apply _

theorem fermiPositivePolarCoordinate_ne_zero (m a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) {ρ : ℝ} (hρ : 0 < ρ) (θ : Circle) :
    fermiPositivePolarCoordinate m a b ha hb ρ θ ≠ 0 := by
  intro hzero
  have he := orientedFermiDiskPoint_positivePolarCoordinate m a b ha hb ρ θ
  rw [hzero] at he
  have hdist := dist_gluingPolarPoint (orientedFermiDiskPoint m a b 0)
    (fermiPositivePolarAngle θ) hρ.le
  rw [← he, dist_self] at hdist
  exact hρ.ne' hdist.symm

/-- The actual polar circle pulled back into the Fermi coordinates lies in
the same open angular half-plane as its coordinate-circle parameter. -/
theorem fermiPositivePolarCoordinate_positiveDot (m a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) {ρ : ℝ} (hρ : 0 < ρ) (θ : Circle) :
    0 < (fermiPositivePolarCoordinate m a b ha hb ρ θ).re * (θ : ℂ).re +
      (fermiPositivePolarCoordinate m a b ha hb ρ θ).im * (θ : ℂ).im := by
  let q := fermiPositivePolarCoordinate m a b ha hb ρ θ
  have h := orientedFermiDiskPoint_discChart_positiveDot m ha hb
    (fermiPositivePolarCoordinate_ne_zero m a b ha hb hρ θ)
  rw [orientedFermiDiskPoint_positivePolarCoordinate, discChart_gluingPolarPoint] at h
  simp only [fermiPositivePolarAngle, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, neg_mul, zero_mul,
    zero_sub, zero_add, neg_neg, one_mul] at h
  have hk : 0 < Real.tanh (ρ / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
  have h' : 0 < Real.tanh (ρ / 2) *
      (q.re * (θ : ℂ).re + q.im * (θ : ℂ).im) := by
    convert h using 1
    dsimp only [q]
    ring
  exact (mul_pos_iff_of_pos_left hk).mp h'

/-- Every coordinate ball contains a uniform actual positive-radius polar
circle, since the global chart is a homeomorphism at its center. -/
theorem exists_small_fermiPositivePolarCoordinate_norm_lt (m a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (ρ : ℝ), 0 ≤ ρ → ρ < ε → ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate m a b ha hb ρ θ‖ < δ := by
  let e := orientedFermiDiskHomeomorph m a b ha hb
  have hO : IsOpen (e.symm ⁻¹' ball (0 : ℂ) δ) :=
    isOpen_ball.preimage e.symm.continuous
  have hmem : e 0 ∈ e.symm ⁻¹' ball (0 : ℂ) δ := by simpa using hδ
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO (e 0) hmem
  refine ⟨ε, hε, ?_⟩
  intro ρ hρ hρε θ
  have hz : gluingPolarPoint (orientedFermiDiskPoint m a b 0)
      (fermiPositivePolarAngle θ) ρ ∈ ball (e 0) ε := by
    rw [mem_ball, dist_comm]
    exact (dist_gluingPolarPoint _ _ hρ).trans_lt hρε
  exact mem_ball_zero_iff.mp (hball hz)

#print axioms fermiPositivePolarCoordinate_positiveDot
#print axioms exists_small_fermiPositivePolarCoordinate_norm_lt

/-- Interpolate in the actual coordinate ball, not in an unrelated quotient
or in the whole upper half-plane. -/
def fermiPositiveCoordinateInterpolation (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (ℓ ρ : ℝ) (t : I) (θ : Circle) : ℂ :=
  (1 - (t : ℝ)) • (ℓ • (θ : ℂ)) +
    (t : ℝ) • fermiPositivePolarCoordinate m a b ha hb ρ θ

/-- The straight comparison never crosses the deleted center. -/
theorem fermiPositiveCoordinateInterpolation_ne_zero (m a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) {ℓ ρ : ℝ} (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (t : I) (θ : Circle) :
    fermiPositiveCoordinateInterpolation m a b ha hb ℓ ρ t θ ≠ 0 := by
  have hd := fermiPositivePolarCoordinate_positiveDot m a b ha hb hρ θ
  have hs : (θ : ℂ).re ^ 2 + (θ : ℂ).im ^ 2 = 1 := by
    have h := Complex.sq_norm (θ : ℂ)
    rw [Circle.norm_coe, Complex.normSq_apply] at h
    nlinarith
  have hc : 0 < (1 - (t : ℝ)) * ℓ + (t : ℝ) *
      ((fermiPositivePolarCoordinate m a b ha hb ρ θ).re * (θ : ℂ).re +
        (fermiPositivePolarCoordinate m a b ha hb ρ θ).im * (θ : ℂ).im) := by
    by_cases ht : (t : ℝ) = 1
    · simpa [ht] using hd
    · have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 ht
      exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) hℓ)
        (mul_nonneg t.2.1 hd.le)
  intro hz
  have hzero : (fermiPositiveCoordinateInterpolation m a b ha hb ℓ ρ t θ).re *
      (θ : ℂ).re + (fermiPositiveCoordinateInterpolation m a b ha hb ℓ ρ t θ).im *
        (θ : ℂ).im = 0 := by rw [hz]; simp
  have heq : (fermiPositiveCoordinateInterpolation m a b ha hb ℓ ρ t θ).re *
      (θ : ℂ).re + (fermiPositiveCoordinateInterpolation m a b ha hb ℓ ρ t θ).im *
        (θ : ℂ).im = (1 - (t : ℝ)) * ℓ + (t : ℝ) *
          ((fermiPositivePolarCoordinate m a b ha hb ρ θ).re * (θ : ℂ).re +
            (fermiPositivePolarCoordinate m a b ha hb ρ θ).im * (θ : ℂ).im) := by
    simp only [fermiPositiveCoordinateInterpolation, Complex.add_re, Complex.add_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul]
    calc
      _ = (1 - (t : ℝ)) * ℓ * ((θ : ℂ).re ^ 2 + (θ : ℂ).im ^ 2) +
          (t : ℝ) * ((fermiPositivePolarCoordinate m a b ha hb ρ θ).re * (θ : ℂ).re +
            (fermiPositivePolarCoordinate m a b ha hb ρ θ).im * (θ : ℂ).im) := by ring
      _ = _ := by rw [hs, mul_one]
  rw [heq] at hzero
  exact hc.ne' hzero

/-- Both endpoints lie in the same convex coordinate ball, so the literal
comparison stays in that ball. -/
theorem fermiPositiveCoordinateInterpolation_norm_lt (m a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) {ℓ ρ δ : ℝ} (hℓ : 0 < ℓ) (hℓδ : ℓ < δ)
    (hq : ∀ θ : Circle, ‖fermiPositivePolarCoordinate m a b ha hb ρ θ‖ < δ)
    (t : I) (θ : Circle) :
    ‖fermiPositiveCoordinateInterpolation m a b ha hb ℓ ρ t θ‖ < δ := by
  have hθ : ℓ • (θ : ℂ) ∈ ball (0 : ℂ) δ := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hℓ,
      Circle.norm_coe, mul_one]
    exact hℓδ
  have hq' : fermiPositivePolarCoordinate m a b ha hb ρ θ ∈ ball (0 : ℂ) δ :=
    mem_ball_zero_iff.mpr (hq θ)
  exact mem_ball_zero_iff.mp ((convex_iff_add_mem.mp (convex_ball (0 : ℂ) δ))
    hθ hq' (sub_nonneg.mpr t.2.2) t.2.1 (by ring))

/-- The actual small polar circle in the punctured coordinate ball. -/
def fermiPositivePolarCoordinateMap (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (ρ δ : ℝ) (hρ : 0 < ρ)
    (hq : ∀ θ : Circle, ‖fermiPositivePolarCoordinate m a b ha hb ρ θ‖ < δ) :
    C(Circle, convexPuncturedDomain (ball (0 : ℂ) δ)) where
  toFun θ := ⟨fermiPositivePolarCoordinate m a b ha hb ρ θ,
    mem_ball_zero_iff.mpr (hq θ),
    fermiPositivePolarCoordinate_ne_zero m a b ha hb hρ θ⟩
  continuous_toFun := (fermiPositivePolarCoordinate_continuous m a b ha hb ρ).subtype_mk _

/-- A genuine homotopy in the punctured coordinate ball from its positive
coordinate circle to the literal positive polar circle. -/
def fermiPositivePolarCoordinateHomotopy (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (ℓ ρ δ : ℝ) (hℓ : 0 < ℓ) (hℓδ : ℓ < δ) (hρ : 0 < ρ)
    (hq : ∀ θ : Circle, ‖fermiPositivePolarCoordinate m a b ha hb ρ θ‖ < δ) :
    (convexPuncturedCircleInclusion (ball (0 : ℂ) δ) ℓ hℓ
      (fun θ => by simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ, Circle.norm_coe] using hℓδ)).Homotopy
      (fermiPositivePolarCoordinateMap m a b ha hb ρ δ hρ hq) where
  toContinuousMap :=
    { toFun p := ⟨fermiPositiveCoordinateInterpolation m a b ha hb ℓ ρ p.1 p.2,
        mem_ball_zero_iff.mpr
          (fermiPositiveCoordinateInterpolation_norm_lt m a b ha hb hℓ hℓδ hq p.1 p.2),
        fermiPositiveCoordinateInterpolation_ne_zero m a b ha hb hℓ hρ p.1 p.2⟩
      continuous_toFun := by
        have ht : Continuous (fun p : I × Circle => (p.1 : ℝ)) :=
          continuous_subtype_val.comp continuous_fst
        have hθ0 : Continuous (fun θ : Circle => (θ : ℂ)) := continuous_subtype_val
        have hθ : Continuous (fun p : I × Circle => ℓ • (p.2 : ℂ)) :=
          (continuous_const : Continuous (fun _ : I × Circle => ℓ)).smul
            (hθ0.comp continuous_snd)
        have hq' := (fermiPositivePolarCoordinate_continuous m a b ha hb ρ).comp
          (continuous_snd : Continuous (fun p : I × Circle => p.2))
        exact (((continuous_const.sub ht).smul hθ).add (ht.smul hq')).subtype_mk _ }
  map_zero_left θ := by
    apply Subtype.ext
    simp [fermiPositiveCoordinateInterpolation, convexPuncturedCircleInclusion]
  map_one_left θ := by
    apply Subtype.ext
    simp [fermiPositiveCoordinateInterpolation, fermiPositivePolarCoordinateMap]

#print axioms fermiPositivePolarCoordinateHomotopy

/-- Positive one-turn classes are identified by the genuine comparison
homotopy's actual basepoint track. -/
theorem fermiPositivePolarCoordinateHomotopy_fundamentalGroup
    (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (ℓ ρ δ : ℝ) (hℓ : 0 < ℓ) (hℓδ : ℓ < δ) (hρ : 0 < ρ)
    (hq : ∀ θ : Circle, ‖fermiPositivePolarCoordinate m a b ha hb ρ θ‖ < δ)
    (θ : Circle) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath
        ((fermiPositivePolarCoordinateHomotopy m a b ha hb ℓ ρ δ hℓ hℓδ hρ hq).evalAt θ)
      ⟦(circleOneTurnLoop θ).map
        (convexPuncturedCircleInclusion (ball (0 : ℂ) δ) ℓ hℓ
          (fun θ => by simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ, Circle.norm_coe]
            using hℓδ)).continuous⟧ =
      ⟦(circleOneTurnLoop θ).map
        (fermiPositivePolarCoordinateMap m a b ha hb ρ δ hρ hq).continuous⟧ := by
  let H := fermiPositivePolarCoordinateHomotopy m a b ha hb ℓ ρ δ hℓ hℓδ hρ hq
  let p := (circleOneTurnLoop θ).map
    (convexPuncturedCircleInclusion (ball (0 : ℂ) δ) ℓ hℓ
      (fun θ => by simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ, Circle.norm_coe] using hℓδ)).continuous
  let q := (circleOneTurnLoop θ).map
    (fermiPositivePolarCoordinateMap m a b ha hb ρ δ hρ hq).continuous
  let γ := H.evalAt θ
  have hhom : (p.trans γ).Homotopic (γ.trans q) :=
    Path.Homotopic.map_trans_evalAt H (circleOneTurnLoop θ)
  have heq := Path.Homotopic.Quotient.eq.mpr hhom
  change Path.Homotopic.Quotient.mk (γ.symm.trans (p.trans γ)) =
    Path.Homotopic.Quotient.mk q
  rw [Path.Homotopic.Quotient.mk_trans, heq,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    ← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

/-- The comparison's polar radius is constructed inside the coordinate
ball, rather than assumed to fit. -/
theorem exists_small_fermiPositivePolarCoordinateHomotopy
    (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hℓδ : ℓ < δ) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ,
      ∃ hq : ∀ θ : Circle, ‖fermiPositivePolarCoordinate m a b ha hb ρ θ‖ < δ,
        Nonempty ((convexPuncturedCircleInclusion (ball (0 : ℂ) δ) ℓ hℓ
          (fun θ => by simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ, Circle.norm_coe]
            using hℓδ)).Homotopy
          (fermiPositivePolarCoordinateMap m a b ha hb ρ δ hρ hq)) := by
  obtain ⟨ε, hε, hsmall⟩ :=
    exists_small_fermiPositivePolarCoordinate_norm_lt m a b ha hb (hℓ.trans hℓδ)
  have hρ : 0 < ε / 2 := half_pos hε
  have hq : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate m a b ha hb (ε / 2) θ‖ < δ :=
    hsmall (ε / 2) hρ.le (by linarith)
  exact ⟨ε / 2, hρ, hq,
    ⟨fermiPositivePolarCoordinateHomotopy m a b ha hb (ℓ := ℓ)
      (ε / 2) δ hℓ hℓδ hρ hq⟩⟩

#print axioms fermiPositivePolarCoordinateHomotopy_fundamentalGroup
#print axioms exists_small_fermiPositivePolarCoordinateHomotopy

/-- The genuine unit phase introduced by an actual orientation-preserving
upper-half-plane transformation at the chosen center. -/
def gluingPolarSLPhase (γ : SL(2, ℝ)) (o : ℍ) : Circle :=
  ⟨conj (((γ 1 0 : ℝ) : ℂ) * (o : ℂ) + ((γ 1 1 : ℝ) : ℂ)) /
    (((γ 1 0 : ℝ) : ℂ) * (o : ℂ) + ((γ 1 1 : ℝ) : ℂ)), by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div, Complex.norm_conj, div_self]
    exact norm_ne_zero_iff.mpr
      (Vendored.RiemannDynamics.denom_ne_zero γ (by simpa using o.im_ne_zero))⟩

/-- Deck transport changes the original polar parameter by exactly that
unit phase; it never reverses positive winding. -/
theorem gluingPolarPoint_smul (γ : SL(2, ℝ)) (o : ℍ) (θ : Circle) (ρ : ℝ) :
    γ • gluingPolarPoint o θ ρ =
      gluingPolarPoint (γ • o) (gluingPolarSLPhase γ o * θ) ρ := by
  apply discChart_injective (γ • o)
  rw [Vendored.RiemannDynamics.discChart_smul, discChart_gluingPolarPoint,
    discChart_gluingPolarPoint]
  have hphase :
      ((((γ 1 0 : ℝ) : ℂ) * conj (o : ℂ) + ((γ 1 1 : ℝ) : ℂ)) /
        (((γ 1 0 : ℝ) : ℂ) * (o : ℂ) + ((γ 1 1 : ℝ) : ℂ))) =
      (gluingPolarSLPhase γ o : ℂ) := by
    simp [gluingPolarSLPhase, map_add, map_mul]
  rw [hphase, Circle.coe_mul]
  ring

/-- A literal unit-circle rotation sends the actual positive one-turn path
to the actual positive one-turn path at the rotated point. -/
theorem circleOneTurnLoop_map_mul_left (u θ : Circle) :
    (circleOneTurnLoop θ).map
      (continuous_const.mul continuous_id : Continuous (fun v : Circle => u * v)) =
      circleOneTurnLoop (u * θ) := by
  apply Path.ext
  funext t
  simp only [Path.map_coe, Function.comp_apply, circleOneTurnLoop_apply,
    Circle.exp_add, Circle.exp_arg, mul_assoc]
  rfl

#print axioms gluingPolarPoint_smul
#print axioms circleOneTurnLoop_map_mul_left

end

end SystolicGrowth
