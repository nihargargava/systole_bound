module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.HalfPlaneSpinAction
public import Geometry.GluingPolarSpinMultiplier

@[expose] public section

/-!
# The actual bounding spin restriction of a polar disk

The explicit polar multiplier determines a continuous direction in the
component's genuine spin orbit carrier. Its square is the actual radial
tangent direction. One literal turn closes the frame path, while its unique
lift under the proved double covering ends at the distinct antipode. These
are concrete deleted-disk boundary data, not a glued surface spin structure.
-/

open UpperHalfPlane
open scoped UpperHalfPlane unitInterval

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- The actual unit-valued polar radial square root. -/
def gluingPolarSpinCircle (p : ℝ × ℝ) : Circle :=
  ⟨gluingPolarSpinMultiplier p,
    mem_sphere_zero_iff_norm.mpr (norm_gluingPolarSpinMultiplier p)⟩

@[simp] theorem gluingPolarSpinCircle_coe (p : ℝ × ℝ) :
    (gluingPolarSpinCircle p : ℂ) = gluingPolarSpinMultiplier p := rfl

theorem continuous_gluingPolarSpinCircle : Continuous gluingPolarSpinCircle :=
  continuous_gluingPolarSpinMultiplier.subtype_mk _

theorem gluingPolarSpinCircle_add_two_pi (ρ θ : ℝ) :
    gluingPolarSpinCircle (ρ, θ + 2 * Real.pi) =
      -gluingPolarSpinCircle (ρ, θ) := by
  apply Circle.coe_injective
  exact gluingPolarSpinMultiplier_add_two_pi ρ θ

/-- An actual spin frame at the literal centered polar point. -/
def gluingPolarSpinFrame (o : ℍ) (p : ℝ × ℝ) : HalfPlaneSpinFrame :=
  ⟨gluingPolarPoint o (Circle.exp p.2) p.1, gluingPolarSpinCircle p⟩

/-- The corresponding actual oriented radial frame. -/
def gluingPolarTangentFrame (o : ℍ) (p : ℝ × ℝ) : HalfPlaneTangentFrame :=
  halfPlaneSpinSquare (gluingPolarSpinFrame o p)

theorem continuous_gluingPolarSpinFrame (o : ℍ) :
    Continuous (gluingPolarSpinFrame o) := by
  apply continuous_induced_rng.mpr
  exact ((gluingPolarPoint_continuous o).comp
    ((Circle.exp.continuous.comp continuous_snd).prodMk continuous_fst)).prodMk
      continuous_gluingPolarSpinCircle

theorem continuous_gluingPolarTangentFrame (o : ℍ) :
    Continuous (gluingPolarTangentFrame o) :=
  continuous_halfPlaneSpinSquare.comp (continuous_gluingPolarSpinFrame o)

/-- This is the literal radial differential, not a selected abstract frame. -/
theorem gluingPolarTangentFrame_phase_eq_normalized_radial_fderiv
    (o : ℍ) (p : ℝ × ℝ) :
    ((gluingPolarTangentFrame o p).phase : ℂ) =
      (fderiv ℝ (gluingPolarLift o) p) (1, 0) /
        (‖(fderiv ℝ (gluingPolarLift o) p) (1, 0)‖ : ℂ) :=
  gluingPolarSpinMultiplier_sq_eq_normalized_radial_fderiv o p

/-- The actual spin frame, including its surface point, returns antipodally. -/
theorem gluingPolarSpinFrame_add_two_pi (o : ℍ) (ρ θ : ℝ) :
    gluingPolarSpinFrame o (ρ, θ + 2 * Real.pi) =
      halfPlaneSpinAntipode (gluingPolarSpinFrame o (ρ, θ)) := by
  apply HalfPlaneSpinFrame.ext
  · change gluingPolarPoint o (Circle.exp (θ + 2 * Real.pi)) ρ =
      gluingPolarPoint o (Circle.exp θ) ρ
    rw [Circle.exp_add_two_pi]
  · exact gluingPolarSpinCircle_add_two_pi ρ θ

/-- The actual radial frame is periodic after one complete turn. -/
theorem gluingPolarTangentFrame_add_two_pi (o : ℍ) (ρ θ : ℝ) :
    gluingPolarTangentFrame o (ρ, θ + 2 * Real.pi) =
      gluingPolarTangentFrame o (ρ, θ) := by
  change halfPlaneSpinSquare (gluingPolarSpinFrame o (ρ, θ + 2 * Real.pi)) = _
  rw [gluingPolarSpinFrame_add_two_pi]
  exact (halfPlaneSpinSquare_eq_iff _ _).mpr (Or.inr rfl)

/-- The boundary tangent is the actual positive angular differential. -/
theorem gluingPolarLift_angular_fderiv_eq_radial (o : ℍ) (p : ℝ × ℝ) :
    (fderiv ℝ (gluingPolarLift o) p) (0, 1) =
      Complex.I * (Real.sinh p.1 : ℂ) *
        (fderiv ℝ (gluingPolarLift o) p) (1, 0) := by
  rw [(gluingPolarLift_hasFDerivAt o p).fderiv, gluingPolarLiftFDeriv_apply,
    gluingPolarLiftFDeriv_apply]
  simp only [Complex.ofReal_zero, Complex.ofReal_one, mul_zero, mul_one, add_zero, zero_add]
  have hs : Real.sinh p.1 = 2 * Real.sinh (p.1 / 2) * Real.cosh (p.1 / 2) := by
    calc
      Real.sinh p.1 = Real.sinh (2 * (p.1 / 2)) := by congr 1; ring
      _ = _ := Real.sinh_two_mul _
  rw [hs, gluingPolarDiskLift, Real.tanh_eq_sinh_div_cosh]
  push_cast
  have hc : (Real.cosh (p.1 / 2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
  field_simp

theorem gluingPolarLift_normalized_angular_eq_radial (o : ℍ) (p : ℝ × ℝ)
    (hρ : 0 < p.1) :
    (fderiv ℝ (gluingPolarLift o) p) (0, 1) /
      (‖(fderiv ℝ (gluingPolarLift o) p) (0, 1)‖ : ℂ) =
      Complex.I * ((fderiv ℝ (gluingPolarLift o) p) (1, 0) /
        (‖(fderiv ℝ (gluingPolarLift o) p) (1, 0)‖ : ℂ)) := by
  have hs : 0 < Real.sinh p.1 := Real.sinh_pos_iff.mpr hρ
  have hn : ‖(fderiv ℝ (gluingPolarLift o) p) (0, 1)‖ =
      Real.sinh p.1 * ‖(fderiv ℝ (gluingPolarLift o) p) (1, 0)‖ := by
    simp only [gluingPolarLift_angular_fderiv_eq_radial, norm_mul, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, one_mul]
  rw [hn, gluingPolarLift_angular_fderiv_eq_radial, Complex.ofReal_mul]
  rw [mul_comm Complex.I (Real.sinh p.1 : ℂ), mul_assoc,
    mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr hs.ne'), mul_div_assoc]

private theorem polarBoundaryHalfAngle_sq :
    (Circle.exp (Real.pi / 4) : ℂ) ^ 2 = Complex.I := by
  rw [Circle.coe_exp, pow_two, ← Complex.exp_add]
  have h : ((Real.pi / 4 : ℝ) : ℂ) * Complex.I +
      ((Real.pi / 4 : ℝ) : ℂ) * Complex.I = (Real.pi : ℂ) / 2 * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_pi_div_two_mul_I]

/-- Rotate the actual radial spin direction by a fixed half right angle. -/
def gluingPolarBoundarySpinFrame (o : ℍ) (p : ℝ × ℝ) : HalfPlaneSpinFrame :=
  ⟨gluingPolarPoint o (Circle.exp p.2) p.1,
    Circle.exp (Real.pi / 4) * gluingPolarSpinCircle p⟩

/-- The genuine positive boundary-tangent frame. -/
def gluingPolarBoundaryTangentFrame (o : ℍ) (p : ℝ × ℝ) : HalfPlaneTangentFrame :=
  halfPlaneSpinSquare (gluingPolarBoundarySpinFrame o p)

theorem continuous_gluingPolarBoundarySpinFrame (o : ℍ) :
    Continuous (gluingPolarBoundarySpinFrame o) := by
  apply continuous_induced_rng.mpr
  exact ((gluingPolarPoint_continuous o).comp
    ((Circle.exp.continuous.comp continuous_snd).prodMk continuous_fst)).prodMk
      (continuous_const.mul continuous_gluingPolarSpinCircle)

theorem continuous_gluingPolarBoundaryTangentFrame (o : ℍ) :
    Continuous (gluingPolarBoundaryTangentFrame o) :=
  continuous_halfPlaneSpinSquare.comp (continuous_gluingPolarBoundarySpinFrame o)

/-- Its square is identified with the literal angular differential at every
positive-radius boundary point. -/
theorem gluingPolarBoundaryTangentFrame_phase_eq_normalized_angular_fderiv
    (o : ℍ) (p : ℝ × ℝ) (hρ : 0 < p.1) :
    ((gluingPolarBoundaryTangentFrame o p).phase : ℂ) =
      (fderiv ℝ (gluingPolarLift o) p) (0, 1) /
        (‖(fderiv ℝ (gluingPolarLift o) p) (0, 1)‖ : ℂ) := by
  change (↑(Circle.exp (Real.pi / 4) * gluingPolarSpinCircle p) : ℂ) ^ 2 = _
  rw [Circle.coe_mul, mul_pow, polarBoundaryHalfAngle_sq, gluingPolarSpinCircle_coe,
    gluingPolarSpinMultiplier_sq_eq_normalized_radial_fderiv,
    gluingPolarLift_normalized_angular_eq_radial o p hρ]

theorem gluingPolarBoundarySpinFrame_add_two_pi (o : ℍ) (ρ θ : ℝ) :
    gluingPolarBoundarySpinFrame o (ρ, θ + 2 * Real.pi) =
      halfPlaneSpinAntipode (gluingPolarBoundarySpinFrame o (ρ, θ)) := by
  apply HalfPlaneSpinFrame.ext
  · change gluingPolarPoint o (Circle.exp (θ + 2 * Real.pi)) ρ =
      gluingPolarPoint o (Circle.exp θ) ρ
    rw [Circle.exp_add_two_pi]
  · change Circle.exp (Real.pi / 4) * gluingPolarSpinCircle (ρ, θ + 2 * Real.pi) =
      -(Circle.exp (Real.pi / 4) * gluingPolarSpinCircle (ρ, θ))
    rw [gluingPolarSpinCircle_add_two_pi, mul_neg]

theorem gluingPolarBoundaryTangentFrame_add_two_pi (o : ℍ) (ρ θ : ℝ) :
    gluingPolarBoundaryTangentFrame o (ρ, θ + 2 * Real.pi) =
      gluingPolarBoundaryTangentFrame o (ρ, θ) := by
  change halfPlaneSpinSquare (gluingPolarBoundarySpinFrame o (ρ, θ + 2 * Real.pi)) = _
  rw [gluingPolarBoundarySpinFrame_add_two_pi]
  exact (halfPlaneSpinSquare_eq_iff _ _).mpr (Or.inr rfl)

namespace ClosedHyperbolicSurface

/-- The actual radial spin direction in the unchanged component quotient. -/
def polarSpinFrame {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ θ : ℝ) : X.SpinCarrier :=
  Quotient.mk _ (gluingPolarSpinFrame o (ρ, θ))

/-- The actual radial oriented direction in the component frame quotient. -/
def polarTangentFrame {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ θ : ℝ) : X.TangentFrameCarrier :=
  Quotient.mk _ (gluingPolarTangentFrame o (ρ, θ))

@[simp] theorem spinSquare_polarSpinFrame {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ θ : ℝ) :
    X.spinSquare (X.polarSpinFrame o ρ θ) = X.polarTangentFrame o ρ θ := rfl

@[simp] theorem spinBase_polarSpinFrame {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ θ : ℝ) :
    X.spinBase (X.polarSpinFrame o ρ θ) =
      X.orbitProjection (gluingPolarPoint o (Circle.exp θ) ρ) := rfl

@[simp] theorem tangentFrameBase_polarTangentFrame {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) (ρ θ : ℝ) :
    X.tangentFrameBase (X.polarTangentFrame o ρ θ) =
      X.orbitProjection (gluingPolarPoint o (Circle.exp θ) ρ) := rfl

theorem continuous_polarSpinFrame {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ : ℝ) : Continuous (X.polarSpinFrame o ρ) :=
  continuous_quotient_mk'.comp ((continuous_gluingPolarSpinFrame o).comp
    (continuous_const.prodMk continuous_id))

theorem continuous_polarTangentFrame {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ : ℝ) : Continuous (X.polarTangentFrame o ρ) :=
  continuous_quotient_mk'.comp ((continuous_gluingPolarTangentFrame o).comp
    (continuous_const.prodMk continuous_id))

theorem polarSpinFrame_add_two_pi {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ θ : ℝ) :
    X.polarSpinFrame o ρ (θ + 2 * Real.pi) =
      X.spinAntipode (X.polarSpinFrame o ρ θ) :=
  congrArg (Quotient.mk _) (gluingPolarSpinFrame_add_two_pi o ρ θ)

theorem polarTangentFrame_add_two_pi {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ θ : ℝ) :
    X.polarTangentFrame o ρ (θ + 2 * Real.pi) = X.polarTangentFrame o ρ θ :=
  congrArg (Quotient.mk _) (gluingPolarTangentFrame_add_two_pi o ρ θ)

theorem polarTangentFrame_periodic {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ : ℝ) : Function.Periodic (X.polarTangentFrame o ρ) (2 * Real.pi) :=
  X.polarTangentFrame_add_two_pi o ρ

/-- The spin turn cannot accidentally close under the actual component deck group. -/
theorem polarSpinFrame_add_two_pi_ne {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ θ : ℝ) :
    X.polarSpinFrame o ρ (θ + 2 * Real.pi) ≠ X.polarSpinFrame o ρ θ := by
  rw [X.polarSpinFrame_add_two_pi]
  exact X.spinAntipode_ne _

/-- The actual unit-interval polar spin turn. -/
def polarSpinTurn {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ θ : ℝ) :
    Path (X.polarSpinFrame o ρ θ) (X.spinAntipode (X.polarSpinFrame o ρ θ)) where
  toFun t := X.polarSpinFrame o ρ (θ + 2 * Real.pi * (t : ℝ))
  continuous_toFun := (X.continuous_polarSpinFrame o ρ).comp
    (continuous_const.add (continuous_const.mul continuous_subtype_val))
  source' := by simp
  target' := by simpa using
    X.polarSpinFrame_add_two_pi o ρ θ

/-- The actual closed radial-frame turn on the same polar circle. -/
def polarTangentTurn {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ θ : ℝ) : Path (X.polarTangentFrame o ρ θ) (X.polarTangentFrame o ρ θ) where
  toFun t := X.polarTangentFrame o ρ (θ + 2 * Real.pi * (t : ℝ))
  continuous_toFun := (X.continuous_polarTangentFrame o ρ).comp
    (continuous_const.add (continuous_const.mul continuous_subtype_val))
  source' := by simp
  target' := by simpa using
    X.polarTangentFrame_add_two_pi o ρ θ

@[simp] theorem spinSquare_polarSpinTurn {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ θ : ℝ) (t : I) :
    X.spinSquare (X.polarSpinTurn o ρ θ t) = X.polarTangentTurn o ρ θ t := rfl

/-- The literal polar square root is the unique lift selected by the actual
covering map, with its actual initial spin direction. -/
theorem liftPath_polarTangentTurn {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ θ : ℝ) :
    X.spinSquare_isCoveringMap.liftPath (X.polarTangentTurn o ρ θ)
      (X.polarSpinFrame o ρ θ) (X.polarTangentTurn o ρ θ).source =
        (X.polarSpinTurn o ρ θ : C(I, X.SpinCarrier)) := by
  symm
  apply (X.spinSquare_isCoveringMap.eq_liftPath_iff'
    (X.polarTangentTurn o ρ θ).source).mpr
  exact ⟨rfl, (X.polarSpinTurn o ρ θ).source⟩

/-- The genuine lifted boundary-frame turn ends at the opposite spin direction. -/
theorem liftPath_polarTangentTurn_one {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ θ : ℝ) :
    X.spinSquare_isCoveringMap.liftPath (X.polarTangentTurn o ρ θ)
      (X.polarSpinFrame o ρ θ) (X.polarTangentTurn o ρ θ).source 1 =
        X.spinAntipode (X.polarSpinFrame o ρ θ) := by
  rw [X.liftPath_polarTangentTurn]
  exact (X.polarSpinTurn o ρ θ).target

theorem liftPath_polarTangentTurn_one_ne {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ θ : ℝ) :
    X.spinSquare_isCoveringMap.liftPath (X.polarTangentTurn o ρ θ)
      (X.polarSpinFrame o ρ θ) (X.polarTangentTurn o ρ θ).source 1 ≠
        X.polarSpinFrame o ρ θ := by
  rw [X.liftPath_polarTangentTurn_one]
  exact X.spinAntipode_ne _

/-- The actual positive boundary-tangent spin direction. -/
def polarBoundarySpinFrame {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ θ : ℝ) : X.SpinCarrier :=
  Quotient.mk _ (gluingPolarBoundarySpinFrame o (ρ, θ))

def polarBoundaryTangentFrame {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ θ : ℝ) : X.TangentFrameCarrier :=
  Quotient.mk _ (gluingPolarBoundaryTangentFrame o (ρ, θ))

@[simp] theorem spinSquare_polarBoundarySpinFrame {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) (ρ θ : ℝ) :
    X.spinSquare (X.polarBoundarySpinFrame o ρ θ) =
      X.polarBoundaryTangentFrame o ρ θ := rfl

theorem continuous_polarBoundarySpinFrame {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ : ℝ) : Continuous (X.polarBoundarySpinFrame o ρ) :=
  continuous_quotient_mk'.comp ((continuous_gluingPolarBoundarySpinFrame o).comp
    (continuous_const.prodMk continuous_id))

theorem continuous_polarBoundaryTangentFrame {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ : ℝ) : Continuous (X.polarBoundaryTangentFrame o ρ) :=
  continuous_quotient_mk'.comp ((continuous_gluingPolarBoundaryTangentFrame o).comp
    (continuous_const.prodMk continuous_id))

theorem polarBoundarySpinFrame_add_two_pi {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ θ : ℝ) :
    X.polarBoundarySpinFrame o ρ (θ + 2 * Real.pi) =
      X.spinAntipode (X.polarBoundarySpinFrame o ρ θ) :=
  congrArg (Quotient.mk _) (gluingPolarBoundarySpinFrame_add_two_pi o ρ θ)

theorem polarBoundaryTangentFrame_add_two_pi {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ θ : ℝ) :
    X.polarBoundaryTangentFrame o ρ (θ + 2 * Real.pi) =
      X.polarBoundaryTangentFrame o ρ θ :=
  congrArg (Quotient.mk _) (gluingPolarBoundaryTangentFrame_add_two_pi o ρ θ)

/-- The boundary-tangent spin path has actual antipodal endpoints. -/
def polarBoundarySpinTurn {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ θ : ℝ) :
    Path (X.polarBoundarySpinFrame o ρ θ)
      (X.spinAntipode (X.polarBoundarySpinFrame o ρ θ)) where
  toFun t := X.polarBoundarySpinFrame o ρ (θ + 2 * Real.pi * (t : ℝ))
  continuous_toFun := (X.continuous_polarBoundarySpinFrame o ρ).comp
    (continuous_const.add (continuous_const.mul continuous_subtype_val))
  source' := by simp
  target' := by simpa using X.polarBoundarySpinFrame_add_two_pi o ρ θ

/-- The literal closed positive tangent-frame turn along the polar boundary. -/
def polarBoundaryTangentTurn {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ θ : ℝ) :
    Path (X.polarBoundaryTangentFrame o ρ θ) (X.polarBoundaryTangentFrame o ρ θ) where
  toFun t := X.polarBoundaryTangentFrame o ρ (θ + 2 * Real.pi * (t : ℝ))
  continuous_toFun := (X.continuous_polarBoundaryTangentFrame o ρ).comp
    (continuous_const.add (continuous_const.mul continuous_subtype_val))
  source' := by simp
  target' := by simpa using X.polarBoundaryTangentFrame_add_two_pi o ρ θ

/-- Actual boundary-tangent monodromy for the genuine component double cover. -/
theorem liftPath_polarBoundaryTangentTurn_one {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ θ : ℝ) :
    X.spinSquare_isCoveringMap.liftPath (X.polarBoundaryTangentTurn o ρ θ)
      (X.polarBoundarySpinFrame o ρ θ) (X.polarBoundaryTangentTurn o ρ θ).source 1 =
        X.spinAntipode (X.polarBoundarySpinFrame o ρ θ) := by
  have h : (X.polarBoundarySpinTurn o ρ θ : C(I, X.SpinCarrier)) =
      X.spinSquare_isCoveringMap.liftPath (X.polarBoundaryTangentTurn o ρ θ)
        (X.polarBoundarySpinFrame o ρ θ) (X.polarBoundaryTangentTurn o ρ θ).source := by
    apply (X.spinSquare_isCoveringMap.eq_liftPath_iff'
      (X.polarBoundaryTangentTurn o ρ θ).source).mpr
    exact ⟨rfl, (X.polarBoundarySpinTurn o ρ θ).source⟩
  rw [← h]
  exact (X.polarBoundarySpinTurn o ρ θ).target

theorem liftPath_polarBoundaryTangentTurn_one_ne {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) (ρ θ : ℝ) :
    X.spinSquare_isCoveringMap.liftPath (X.polarBoundaryTangentTurn o ρ θ)
      (X.polarBoundarySpinFrame o ρ θ) (X.polarBoundaryTangentTurn o ρ θ).source 1 ≠
        X.polarBoundarySpinFrame o ρ θ := by
  rw [X.liftPath_polarBoundaryTangentTurn_one]
  exact X.spinAntipode_ne _

end ClosedHyperbolicSurface

#print axioms gluingPolarTangentFrame_phase_eq_normalized_radial_fderiv
#print axioms ClosedHyperbolicSurface.polarSpinFrame_add_two_pi_ne
#print axioms ClosedHyperbolicSurface.liftPath_polarTangentTurn
#print axioms ClosedHyperbolicSurface.liftPath_polarTangentTurn_one_ne
#print axioms gluingPolarLift_angular_fderiv_eq_radial
#print axioms gluingPolarBoundaryTangentFrame_phase_eq_normalized_angular_fderiv
#print axioms ClosedHyperbolicSurface.liftPath_polarBoundaryTangentTurn_one_ne

end
end SystolicGrowth
