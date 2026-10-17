module

public import Geometry.GluingFermiTangentIdentification
public import Geometry.GluingPolarArea
public import Geometry.GluingNativeUnitTangentCharts

@[expose] public section

/-!
# Genuine component tangent sheets and Fermi unit-vector transport

The actual component tangent-orbit carrier admits a variable-radius preferred
sheet over every embedded outer ball. Literal hyperbolic unit vectors are
transported by the actual full Fermi differentials, including their genuine
imaginary-height scaling. These are inputs to native tangent-bundle descent.
The interior sheet is identified with the original native unit tangent
bundle; on both collar sides the true Fermi inverse gives a continuous
native unit vector, and literal boundary clutching makes those vectors equal.
-/

open UpperHalfPlane Topology
open scoped MatrixGroups UpperHalfPlane

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ClosedHyperbolicSurface

variable {g : ℕ} (X : ClosedHyperbolicSurface g)

/-- Actual tangent directions whose base lies in the projected outer ball. -/
abbrev TangentBallCarrier (o : ℍ) (R : ℝ) :=
  {q : X.TangentFrameCarrier // X.tangentFrameBase q ∈
    X.orbitProjection '' Metric.ball o R}

def tangentBallParam (o : ℍ) (R : ℝ) (p : Metric.ball o R × Circle) :
    X.TangentBallCarrier o R :=
  ⟨Quotient.mk _ (⟨p.1.1, p.2⟩ : HalfPlaneTangentFrame), p.1.1, p.1.2, rfl⟩

theorem tangentBallParam_injective (o : ℍ) {R : ℝ} (hR : 2 * R < X.systole) :
    Function.Injective (X.tangentBallParam o R) := by
  intro p q h
  have hc := congrArg Subtype.val h
  have hb := congrArg X.tangentFrameBase hc
  have hp : p.1.1 = q.1.1 := quotientMk_injOn_ball X o R hR p.1.2 q.1.2 hb
  have hp' : p.1 = q.1 := Subtype.ext hp
  obtain ⟨A, hA⟩ := MulAction.mem_orbit_iff.mp
    (MulAction.orbitRel_apply.mp (Quotient.exact hc))
  have ha : A • q.1.1 = q.1.1 := by
    have ht := congrArg HalfPlaneTangentFrame.point hA
    change (A : SL(2, ℝ)) • q.1.1 = p.1.1 at ht
    change (A : SL(2, ℝ)) • q.1.1 = q.1.1
    simpa only [hp] using ht
  have hAone := X.free A q.1.1 ha
  subst A
  rw [one_smul] at hA
  exact Prod.ext hp' (congrArg HalfPlaneTangentFrame.phase hA).symm

theorem tangentBallParam_surjective (o : ℍ) (R : ℝ) :
    Function.Surjective (X.tangentBallParam o R) := by
  rintro ⟨q, hq⟩
  induction q using Quotient.inductionOn with
  | h q =>
    obtain ⟨z, hz, he⟩ := hq
    obtain ⟨A, hA⟩ := MulAction.mem_orbit_iff.mp
      (MulAction.orbitRel_apply.mp (Quotient.exact he))
    let v : HalfPlaneTangentFrame := A • q
    refine ⟨(⟨z, hz⟩, v.phase), ?_⟩
    apply Subtype.ext
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨A, ?_⟩
    apply HalfPlaneTangentFrame.ext
    · exact hA
    · rfl

theorem continuous_tangentBallParam (o : ℍ) (R : ℝ) :
    Continuous (X.tangentBallParam o R) :=
  (continuous_quotient_mk'.comp
    (halfPlaneTangentFrameHomeomorph.symm.continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))).subtype_mk _

theorem tangentBallParam_isOpenMap (o : ℍ) (R : ℝ) :
    IsOpenMap (X.tangentBallParam o R) := by
  have hf : IsOpenMap (fun p : Metric.ball o R × Circle =>
      (⟨p.1.1, p.2⟩ : HalfPlaneTangentFrame)) :=
    halfPlaneTangentFrameHomeomorph.symm.isOpenMap.comp
      (Metric.isOpen_ball.isOpenMap_subtype_val.prodMap IsOpenMap.id)
  have hq := X.tangentFrameOrbitProjection_isQuotientCoveringMap.isCoveringMap.isOpenMap.comp hf
  exact hq.subtype_mk _

/-- A genuine variable-radius preferred frame sheet, rather than only
fixed boundary-circle coordinates. -/
def tangentBallHomeomorph (o : ℍ) {R : ℝ} (hR : 2 * R < X.systole) :
    (Metric.ball o R × Circle) ≃ₜ X.TangentBallCarrier o R :=
  IsHomeomorph.homeomorph (X.tangentBallParam o R)
    ⟨X.continuous_tangentBallParam o R, X.tangentBallParam_isOpenMap o R,
      X.tangentBallParam_injective o hR, X.tangentBallParam_surjective o R⟩

@[simp] theorem tangentBallHomeomorph_apply
    (o : ℍ) {R : ℝ} (hR : 2 * R < X.systole) (p : Metric.ball o R × Circle) :
    X.tangentBallHomeomorph o hR p = X.tangentBallParam o R p := rfl

end ClosedHyperbolicSurface

private theorem polar_radial_norm_eq_im (o : ℍ) (p : ℝ × ℝ) :
    ‖fderiv ℝ (gluingPolarLift o) p (1, 0)‖ = (gluingPolarLift o p).im := by
  rw [(gluingPolarLift_hasFDerivAt o p).fderiv]
  have hsq := gluingPolarLiftFDeriv_radial_norm_sq o p
  have hi : 0 < (gluingPolarLift o p).im :=
    (gluingPolarPoint o (Circle.exp p.2) p.1).im_pos
  nlinarith [norm_nonneg (gluingPolarLiftFDeriv o p (1, 0))]

theorem gluingFermiIncomingLift_radial_norm_eq_im (o : ℍ) (r : ℝ) (p : ℝ × ℝ) :
    ‖fderiv ℝ (gluingFermiIncomingLift o r) p (1, 0)‖ =
      (gluingFermiIncomingLift o r p).im := by
  rw [gluingFermiIncomingLift_radial_fderiv]
  exact polar_radial_norm_eq_im o (r + p.1, p.2)

theorem gluingFermiOutgoingLift_radial_norm_eq_im (o : ℍ) (r : ℝ) (p : ℝ × ℝ) :
    ‖fderiv ℝ (gluingFermiOutgoingLift o r) p (1, 0)‖ =
      (gluingFermiOutgoingLift o r p).im := by
  rw [gluingFermiOutgoingLift_radial_fderiv, norm_neg]
  exact polar_radial_norm_eq_im o (r - p.1, -p.2)

private theorem incoming_radial_eq_unit_root (o : ℍ) (r : ℝ) (p : ℝ × ℝ) :
    fderiv ℝ (gluingFermiIncomingLift o r) p (1, 0) =
      ((gluingFermiIncomingLift o r p).im : ℂ) *
        (gluingFermiIncomingSpinCircle r p : ℂ) ^ 2 := by
  rw [gluingFermiIncomingSpinCircle_sq_eq_normalized_radial_fderiv o,
    gluingFermiIncomingLift_radial_norm_eq_im]
  have hi : (gluingFermiIncomingLift o r p).im ≠ 0 :=
    (gluingPolarPoint o (Circle.exp p.2) (r + p.1)).im_pos.ne'
  rw [mul_comm ((gluingFermiIncomingLift o r p).im : ℂ),
    div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hi)]

private theorem outgoing_radial_eq_unit_root (o : ℍ) (r : ℝ) (p : ℝ × ℝ) :
    fderiv ℝ (gluingFermiOutgoingLift o r) p (1, 0) =
      ((gluingFermiOutgoingLift o r p).im : ℂ) *
        (gluingFermiOutgoingSpinCircle r p : ℂ) ^ 2 := by
  rw [gluingFermiOutgoingSpinCircle_sq_eq_normalized_radial_fderiv o,
    gluingFermiOutgoingLift_radial_norm_eq_im]
  have hi : (gluingFermiOutgoingLift o r p).im ≠ 0 :=
    (gluingPolarPoint o (Circle.exp (-p.2)) (r - p.1)).im_pos.ne'
  rw [mul_comm ((gluingFermiOutgoingLift o r p).im : ℂ),
    div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hi)]

/-- The genuine full coordinate transition sends the literal hyperbolic
unit vector to the literal incoming unit vector, with the actual height
scales. Thus phase matching does not discard metric normalization. -/
theorem gluingFermiBoundaryTangentTransition_unit_vector
    (oIn oOut : ℍ) {r : ℝ} (hr : 0 < r) (θ : ℝ) (u : ℂ) :
    gluingFermiBoundaryTangentTransition oIn oOut hr θ
      (((gluingFermiOutgoingLift oOut r (0, θ)).im : ℂ) * u) =
        ((gluingFermiIncomingLift oIn r (0, θ)).im : ℂ) *
          ((gluingFermiBoundarySpinCircle r (Circle.exp θ) : ℂ) ^ 2 * u) := by
  rw [gluingFermiBoundaryTangentTransition_apply,
    gluingFermiBoundarySpinCircle_exp, gluingFermiBoundarySpinMultiplier,
    Circle.coe_div, div_pow]
  unfold gluingFermiBoundaryTangentScalar
  rw [incoming_radial_eq_unit_root, outgoing_radial_eq_unit_root]
  have hi : (gluingFermiOutgoingLift oOut r (0, θ)).im ≠ 0 := by
    simpa [gluingFermiOutgoingLift, gluingPolarLift] using
      (gluingPolarPoint oOut (Circle.exp (-θ)) r).im_pos.ne'
  have hiC : ((gluingFermiOutgoingLift oOut r (0, θ)).im : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hi
  have hu : (gluingFermiOutgoingSpinCircle r (0, θ) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  field_simp [hiC, hu]

/-- Actual outgoing and incoming unit directions related by the literal
seam clutching give exactly the same signed Fermi tangent vector. -/
theorem gluingFermiBoundary_unit_vectors_inverse_eq
    (oIn oOut : ℍ) {r : ℝ} (hr : 0 < r) (θ : ℝ) (u : Circle) :
    (gluingFermiIncomingDerivEquiv oIn r (0, θ) (by simpa using hr)).symm
      (((gluingFermiIncomingLift oIn r (0, θ)).im : ℂ) *
        ((gluingFermiBoundarySpinCircle r (Circle.exp θ) : ℂ) ^ 2 * (u : ℂ))) =
      (gluingFermiOutgoingDerivEquiv oOut r (0, θ) (by simpa using hr)).symm
        (((gluingFermiOutgoingLift oOut r (0, θ)).im : ℂ) * (u : ℂ)) := by
  let DIn := gluingFermiIncomingDerivEquiv oIn r (0, θ) (by simpa using hr)
  let DOut := gluingFermiOutgoingDerivEquiv oOut r (0, θ) (by simpa using hr)
  apply DIn.injective
  rw [DIn.apply_symm_apply]
  exact (gluingFermiBoundaryTangentTransition_unit_vector oIn oOut hr θ (u : ℂ)).symm

private theorem halfPlane_circle_unit_vector (z : ℍ) (u : Circle) :
    gluingHalfPlaneTangentForm z ((z.im : ℂ) * u) ((z.im : ℂ) * u) = 1 := by
  have hn : ‖(z.im : ℂ) * (u : ℂ)‖ = z.im := by
    simp [abs_of_pos z.im_pos]
  unfold gluingHalfPlaneTangentForm
  rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re, hn]
  exact div_self (pow_ne_zero 2 z.im_pos.ne')

def gluingFermiIncomingUnitVectorCoordinates (o : ℍ) (r : ℝ) (p : ℝ × ℝ)
    (hp : 0 < r + p.1) (u : Circle) : ℝ × ℝ :=
  (gluingFermiIncomingDerivEquiv o r p hp).symm
    (((gluingFermiIncomingLift o r p).im : ℂ) * (u : ℂ))

def gluingFermiOutgoingUnitVectorCoordinates (o : ℍ) (r : ℝ) (p : ℝ × ℝ)
    (hp : 0 < r - p.1) (u : Circle) : ℝ × ℝ :=
  (gluingFermiOutgoingDerivEquiv o r p hp).symm
    (((gluingFermiOutgoingLift o r p).im : ℂ) * (u : ℂ))

private theorem complexMk_weight (a b w : ℝ) :
    (⟨a, w * b⟩ : ℂ) = (a : ℂ) + Complex.I * (w : ℂ) * (b : ℂ) := by
  apply Complex.ext <;> simp

/-- The full inverse differential has the literal weighted polar coordinates.
This identity controls both continuity and the native orthonormal gauge. -/
theorem gluingFermiIncomingUnitVectorCoordinates_weighted
    (o : ℍ) (r : ℝ) (p : ℝ × ℝ) (hp : 0 < r + p.1) (u : Circle) :
    let v := gluingFermiIncomingUnitVectorCoordinates o r p hp u
    (⟨v.1, Real.sinh (r + p.1) * v.2⟩ : ℂ) =
      (u : ℂ) / (gluingFermiIncomingSpinCircle r p : ℂ) ^ 2 := by
  let v := gluingFermiIncomingUnitVectorCoordinates o r p hp u
  have hv : (gluingFermiIncomingDerivEquiv o r p hp : (ℝ × ℝ) →L[ℝ] ℂ) v =
      ((gluingFermiIncomingLift o r p).im : ℂ) * (u : ℂ) :=
    (gluingFermiIncomingDerivEquiv o r p hp).apply_symm_apply _
  rw [gluingFermiIncomingDerivEquiv_toCLM,
    gluingFermiIncomingLift_fderiv_eq_radial, incoming_radial_eq_unit_root] at hv
  have hi : ((gluingFermiIncomingLift o r p).im : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (gluingPolarPoint o (Circle.exp p.2) (r + p.1)).im_pos.ne'
  change (⟨v.1, Real.sinh (r + p.1) * v.2⟩ : ℂ) = _
  rw [complexMk_weight]
  apply (eq_div_iff (pow_ne_zero 2 (Circle.coe_ne_zero _))).mpr
  apply mul_left_cancel₀ hi
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hv

theorem gluingFermiOutgoingUnitVectorCoordinates_weighted
    (o : ℍ) (r : ℝ) (p : ℝ × ℝ) (hp : 0 < r - p.1) (u : Circle) :
    let v := gluingFermiOutgoingUnitVectorCoordinates o r p hp u
    (⟨v.1, Real.sinh (r - p.1) * v.2⟩ : ℂ) =
      (u : ℂ) / (gluingFermiOutgoingSpinCircle r p : ℂ) ^ 2 := by
  let v := gluingFermiOutgoingUnitVectorCoordinates o r p hp u
  have hv : (gluingFermiOutgoingDerivEquiv o r p hp : (ℝ × ℝ) →L[ℝ] ℂ) v =
      ((gluingFermiOutgoingLift o r p).im : ℂ) * (u : ℂ) :=
    (gluingFermiOutgoingDerivEquiv o r p hp).apply_symm_apply _
  rw [gluingFermiOutgoingDerivEquiv_toCLM,
    gluingFermiOutgoingLift_fderiv_eq_radial, outgoing_radial_eq_unit_root] at hv
  have hi : ((gluingFermiOutgoingLift o r p).im : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (gluingPolarPoint o (Circle.exp (-p.2)) (r - p.1)).im_pos.ne'
  change (⟨v.1, Real.sinh (r - p.1) * v.2⟩ : ℂ) = _
  rw [complexMk_weight]
  apply (eq_div_iff (pow_ne_zero 2 (Circle.coe_ne_zero _))).mpr
  apply mul_left_cancel₀ hi
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hv

theorem gluingFermiIncomingUnitVectorCoordinates_eq
    (o : ℍ) (r : ℝ) (p : ℝ × ℝ) (hp : 0 < r + p.1) (u : Circle) :
    gluingFermiIncomingUnitVectorCoordinates o r p hp u =
      (((u : ℂ) / (gluingFermiIncomingSpinCircle r p : ℂ) ^ 2).re,
        ((u : ℂ) / (gluingFermiIncomingSpinCircle r p : ℂ) ^ 2).im /
          Real.sinh (r + p.1)) := by
  have h := gluingFermiIncomingUnitVectorCoordinates_weighted o r p hp u
  apply Prod.ext
  · exact congrArg Complex.re h
  · apply (eq_div_iff (Real.sinh_pos_iff.mpr hp).ne').mpr
    simpa only [mul_comm] using congrArg Complex.im h

theorem gluingFermiOutgoingUnitVectorCoordinates_eq
    (o : ℍ) (r : ℝ) (p : ℝ × ℝ) (hp : 0 < r - p.1) (u : Circle) :
    gluingFermiOutgoingUnitVectorCoordinates o r p hp u =
      (((u : ℂ) / (gluingFermiOutgoingSpinCircle r p : ℂ) ^ 2).re,
        ((u : ℂ) / (gluingFermiOutgoingSpinCircle r p : ℂ) ^ 2).im /
          Real.sinh (r - p.1)) := by
  have h := gluingFermiOutgoingUnitVectorCoordinates_weighted o r p hp u
  apply Prod.ext
  · exact congrArg Complex.re h
  · apply (eq_div_iff (Real.sinh_pos_iff.mpr hp).ne').mpr
    simpa only [mul_comm] using congrArg Complex.im h

/-- Actual inverse Fermi unit directions vary continuously on their true
positive-radius domain; no continuity of an assumed phase atlas is used. -/
theorem continuous_gluingFermiIncomingUnitVectorCoordinates
    (o : ℍ) (r : ℝ) {A : Type*} [TopologicalSpace A]
    (p : A → ℝ × ℝ) (hp : ∀ a, 0 < r + (p a).1) (u : A → Circle)
    (hpc : Continuous p) (huc : Continuous u) :
    Continuous (fun a => gluingFermiIncomingUnitVectorCoordinates o r (p a) (hp a) (u a)) := by
  have he : (fun a => gluingFermiIncomingUnitVectorCoordinates o r (p a) (hp a) (u a)) =
      (fun a => (((u a : ℂ) / (gluingFermiIncomingSpinCircle r (p a) : ℂ) ^ 2).re,
        ((u a : ℂ) / (gluingFermiIncomingSpinCircle r (p a) : ℂ) ^ 2).im /
          Real.sinh (r + (p a).1))) := by
    funext a
    exact gluingFermiIncomingUnitVectorCoordinates_eq o r (p a) (hp a) (u a)
  rw [he]
  have hq : Continuous (fun a => (u a : ℂ) /
      (gluingFermiIncomingSpinCircle r (p a) : ℂ) ^ 2) :=
    (continuous_subtype_val.comp huc).div
      ((continuous_subtype_val.comp ((continuous_gluingFermiIncomingSpinCircle r).comp hpc)).pow 2)
      (fun a => pow_ne_zero 2 (Circle.coe_ne_zero _))
  exact (Complex.continuous_re.comp hq).prodMk
    ((Complex.continuous_im.comp hq).div
      (Real.continuous_sinh.comp (continuous_const.add hpc.fst))
      (fun a => (Real.sinh_pos_iff.mpr (hp a)).ne'))

theorem continuous_gluingFermiOutgoingUnitVectorCoordinates
    (o : ℍ) (r : ℝ) {A : Type*} [TopologicalSpace A]
    (p : A → ℝ × ℝ) (hp : ∀ a, 0 < r - (p a).1) (u : A → Circle)
    (hpc : Continuous p) (huc : Continuous u) :
    Continuous (fun a => gluingFermiOutgoingUnitVectorCoordinates o r (p a) (hp a) (u a)) := by
  have he : (fun a => gluingFermiOutgoingUnitVectorCoordinates o r (p a) (hp a) (u a)) =
      (fun a => (((u a : ℂ) / (gluingFermiOutgoingSpinCircle r (p a) : ℂ) ^ 2).re,
        ((u a : ℂ) / (gluingFermiOutgoingSpinCircle r (p a) : ℂ) ^ 2).im /
          Real.sinh (r - (p a).1))) := by
    funext a
    exact gluingFermiOutgoingUnitVectorCoordinates_eq o r (p a) (hp a) (u a)
  rw [he]
  have hq : Continuous (fun a => (u a : ℂ) /
      (gluingFermiOutgoingSpinCircle r (p a) : ℂ) ^ 2) :=
    (continuous_subtype_val.comp huc).div
      ((continuous_subtype_val.comp ((continuous_gluingFermiOutgoingSpinCircle r).comp hpc)).pow 2)
      (fun a => pow_ne_zero 2 (Circle.coe_ne_zero _))
  exact (Complex.continuous_re.comp hq).prodMk
    ((Complex.continuous_im.comp hq).div
      (Real.continuous_sinh.comp (continuous_const.sub hpc.fst))
      (fun a => (Real.sinh_pos_iff.mpr (hp a)).ne'))

theorem gluingFermiIncomingUnitVectorCoordinates_unit
    (o : ℍ) (r : ℝ) (p : ℝ × ℝ) (hp : 0 < r + p.1) (u : Circle) :
    let v := gluingFermiIncomingUnitVectorCoordinates o r p hp u
    v.1 ^ 2 + Real.sinh (r + p.1) ^ 2 * v.2 ^ 2 = 1 := by
  let v := gluingFermiIncomingUnitVectorCoordinates o r p hp u
  have h := gluingPolarLift_fderiv_tangentForm_pullback o (r + p.1, p.2) v v
  rw [← gluingFermiIncomingLift_fderiv_apply o r p v,
    ← gluingFermiIncomingDerivEquiv_toCLM o r p hp] at h
  have hv : (gluingFermiIncomingDerivEquiv o r p hp : (ℝ × ℝ) →L[ℝ] ℂ) v =
      ((gluingFermiIncomingLift o r p).im : ℂ) * (u : ℂ) :=
    (gluingFermiIncomingDerivEquiv o r p hp).apply_symm_apply _
  rw [hv] at h
  have hu := halfPlane_circle_unit_vector
    (gluingPolarPoint o (Circle.exp p.2) (r + p.1)) u
  change gluingHalfPlaneTangentForm _
    (((gluingFermiIncomingLift o r p).im : ℂ) * (u : ℂ))
    (((gluingFermiIncomingLift o r p).im : ℂ) * (u : ℂ)) = 1 at hu
  change v.1 ^ 2 + Real.sinh (r + p.1) ^ 2 * v.2 ^ 2 = 1
  rw [hu] at h
  nlinarith [h]

theorem gluingFermiOutgoingUnitVectorCoordinates_unit
    (o : ℍ) (r : ℝ) (p : ℝ × ℝ) (hp : 0 < r - p.1) (u : Circle) :
    let v := gluingFermiOutgoingUnitVectorCoordinates o r p hp u
    v.1 ^ 2 + Real.sinh (r - p.1) ^ 2 * v.2 ^ 2 = 1 := by
  let v := gluingFermiOutgoingUnitVectorCoordinates o r p hp u
  have h := gluingPolarLift_fderiv_tangentForm_pullback o (r - p.1, -p.2) v v
  have hv : fderiv ℝ (gluingPolarLift o) (r - p.1, -p.2) v =
      -(((gluingFermiOutgoingLift o r p).im : ℂ) * (u : ℂ)) := by
    have he : fderiv ℝ (gluingFermiOutgoingLift o r) p v =
        ((gluingFermiOutgoingLift o r p).im : ℂ) * (u : ℂ) := by
      rw [← gluingFermiOutgoingDerivEquiv_toCLM o r p hp]
      exact (gluingFermiOutgoingDerivEquiv o r p hp).apply_symm_apply _
    rw [gluingFermiOutgoingLift_fderiv_apply] at he
    exact neg_eq_iff_eq_neg.mp he
  rw [hv] at h
  have hu := halfPlane_circle_unit_vector
    (gluingPolarPoint o (Circle.exp (-p.2)) (r - p.1)) u
  change gluingHalfPlaneTangentForm _
    (((gluingFermiOutgoingLift o r p).im : ℂ) * (u : ℂ))
    (((gluingFermiOutgoingLift o r p).im : ℂ) * (u : ℂ)) = 1 at hu
  have hneg : ∀ z : ℍ, ∀ w : ℂ,
      gluingHalfPlaneTangentForm z (-w) (-w) = gluingHalfPlaneTangentForm z w w := by
    intros
    simp [gluingHalfPlaneTangentForm]
  rw [hneg, hu] at h
  change v.1 ^ 2 + Real.sinh (r - p.1) ^ 2 * v.2 ^ 2 = 1
  nlinarith [h]

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

theorem Internal.GluingComponentTangentTransportHelpers.seamPoint_mem_chart (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (θ : ℝ) (p : GluingSeamAngularDomain C g θ) :
    P.seamAngularPoint k θ p ∈ (P.seamAngularComplexChart k θ).source := by
  rw [P.seamAngularComplexChart_source]
  exact ⟨p, rfl⟩

/-- The true signed Fermi coordinates of the incoming physical unit vector,
expressed in the original complex seam chart. -/
def incomingNativeUnitCoordinates (P : ExerciseGluingPreparation C g n genera X)
    (o : ℍ) (θ : ℝ) (p : GluingSeamAngularDomain C g θ)
    (hs : 0 ≤ p.1.1) (u : Circle) : ℂ :=
  let v := gluingFermiIncomingUnitVectorCoordinates o (gluingRadius C g)
    (p.1.1, -p.2.1) (by linarith [P.radius_pos]) u
  ⟨v.1, -v.2⟩

/-- The true signed Fermi coordinates of the outgoing physical unit vector. -/
def outgoingNativeUnitCoordinates (P : ExerciseGluingPreparation C g n genera X)
    (o : ℍ) (θ : ℝ) (p : GluingSeamAngularDomain C g θ)
    (hs : p.1.1 ≤ 0) (u : Circle) : ℂ :=
  let v := gluingFermiOutgoingUnitVectorCoordinates o (gluingRadius C g)
    (p.1.1, -p.2.1) (by linarith [P.radius_pos]) u
  ⟨v.1, -v.2⟩

theorem incomingNativeUnitCoordinates_unit
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (o : ℍ) (θ : ℝ) (p : GluingSeamAngularDomain C g θ)
    (hs : 0 ≤ p.1.1) (u : Circle) :
    P.gluingChartTangentForm (P.seamAngularComplexChart k θ)
      (P.seamAngularComplexChart k θ (P.seamAngularPoint k θ p))
      (P.incomingNativeUnitCoordinates o θ p hs u)
      (P.incomingNativeUnitCoordinates o θ p hs u) = 1 := by
  have h := gluingFermiIncomingUnitVectorCoordinates_unit o (gluingRadius C g)
    (p.1.1, -p.2.1) (by linarith [P.radius_pos]) u
  simpa [P.seamAngularComplexChart_apply, P.gluingChartTangentForm_seam,
    gluingComplexCollarTangentForm_apply, gluingCollarTangentForm_self,
    incomingNativeUnitCoordinates, gluingSeamAngularModel,
    gluingCollarWarp, abs_of_nonneg hs, pow_two, mul_assoc] using h

theorem outgoingNativeUnitCoordinates_unit
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (o : ℍ) (θ : ℝ) (p : GluingSeamAngularDomain C g θ)
    (hs : p.1.1 ≤ 0) (u : Circle) :
    P.gluingChartTangentForm (P.seamAngularComplexChart k θ)
      (P.seamAngularComplexChart k θ (P.seamAngularPoint k θ p))
      (P.outgoingNativeUnitCoordinates o θ p hs u)
      (P.outgoingNativeUnitCoordinates o θ p hs u) = 1 := by
  have h := gluingFermiOutgoingUnitVectorCoordinates_unit o (gluingRadius C g)
    (p.1.1, -p.2.1) (by linarith [P.radius_pos]) u
  simpa [P.seamAngularComplexChart_apply, P.gluingChartTangentForm_seam,
    gluingComplexCollarTangentForm_apply, gluingCollarTangentForm_self,
    outgoingNativeUnitCoordinates, gluingSeamAngularModel,
    gluingCollarWarp, abs_of_nonpos hs, sub_eq_add_neg, pow_two, mul_assoc] using h

/-- A physical component unit vector, transported by the actual Fermi
differential into the true native tangent bundle. -/
def incomingNativeUnitTangent (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (o : ℍ) (θ : ℝ) (p : GluingSeamAngularDomain C g θ)
    (hs : 0 ≤ p.1.1) (u : Circle) : P.NativeUnitTangentFiber (P.seamAngularPoint k θ p) :=
  P.nativeUnitTangentOfCoordinates (P.seamAngularComplexChart k θ)
    (Or.inr ⟨k, θ, rfl⟩) (P.seamAngularPoint k θ p) (Internal.GluingComponentTangentTransportHelpers.seamPoint_mem_chart P k θ p)
    (P.incomingNativeUnitCoordinates o θ p hs u)
    (P.incomingNativeUnitCoordinates_unit k o θ p hs u)

def outgoingNativeUnitTangent (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (o : ℍ) (θ : ℝ) (p : GluingSeamAngularDomain C g θ)
    (hs : p.1.1 ≤ 0) (u : Circle) : P.NativeUnitTangentFiber (P.seamAngularPoint k θ p) :=
  P.nativeUnitTangentOfCoordinates (P.seamAngularComplexChart k θ)
    (Or.inr ⟨k, θ, rfl⟩) (P.seamAngularPoint k θ p) (Internal.GluingComponentTangentTransportHelpers.seamPoint_mem_chart P k θ p)
    (P.outgoingNativeUnitCoordinates o θ p hs u)
    (P.outgoingNativeUnitCoordinates_unit k o θ p hs u)

def incomingNativeUnitTangentTotal (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (o : ℍ) (θ : ℝ) (p : GluingSeamAngularDomain C g θ)
    (hs : 0 ≤ p.1.1) (u : Circle) : P.NativeUnitTangentCarrier :=
  P.nativeUnitTangentOfCoordinatesTotal (P.seamAngularComplexChart k θ)
    (Or.inr ⟨k, θ, rfl⟩) (P.seamAngularPoint k θ p) (Internal.GluingComponentTangentTransportHelpers.seamPoint_mem_chart P k θ p)
    (P.incomingNativeUnitCoordinates o θ p hs u)
    (P.incomingNativeUnitCoordinates_unit k o θ p hs u)

def outgoingNativeUnitTangentTotal (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (o : ℍ) (θ : ℝ) (p : GluingSeamAngularDomain C g θ)
    (hs : p.1.1 ≤ 0) (u : Circle) : P.NativeUnitTangentCarrier :=
  P.nativeUnitTangentOfCoordinatesTotal (P.seamAngularComplexChart k θ)
    (Or.inr ⟨k, θ, rfl⟩) (P.seamAngularPoint k θ p) (Internal.GluingComponentTangentTransportHelpers.seamPoint_mem_chart P k θ p)
    (P.outgoingNativeUnitCoordinates o θ p hs u)
    (P.outgoingNativeUnitCoordinates_unit k o θ p hs u)

theorem continuous_incomingNativeUnitTangentTotal
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (o : ℍ) (θ : ℝ)
    {A : Type*} [TopologicalSpace A] (p : A → GluingSeamAngularDomain C g θ)
    (hs : ∀ a, 0 ≤ (p a).1.1) (u : A → Circle)
    (hpc : Continuous p) (huc : Continuous u) :
    Continuous (fun a => P.incomingNativeUnitTangentTotal k o θ (p a) (hs a) (u a)) := by
  have hv := continuous_gluingFermiIncomingUnitVectorCoordinates o (gluingRadius C g)
    (fun a => ((p a).1.1, -(p a).2.1))
    (fun a => by dsimp; linarith [P.radius_pos, hs a]) u
    ((continuous_subtype_val.comp hpc.fst).prodMk
      (continuous_subtype_val.comp hpc.snd).neg) huc
  exact P.nativeUnitTangentOfCoordinatesTotal_continuous
    (P.seamAngularComplexChart k θ) (Or.inr ⟨k, θ, rfl⟩)
    (fun a => P.seamAngularPoint k θ (p a))
    (fun a => P.incomingNativeUnitCoordinates o θ (p a) (hs a) (u a))
    (fun a => Internal.GluingComponentTangentTransportHelpers.seamPoint_mem_chart P k θ (p a))
    (fun a => P.incomingNativeUnitCoordinates_unit k o θ (p a) (hs a) (u a))
    ((P.seamAngularPoint_isOpenEmbedding k θ).continuous.comp hpc)
    (Complex.equivRealProdCLM.symm.continuous.comp (hv.fst.prodMk hv.snd.neg))

theorem continuous_outgoingNativeUnitTangentTotal
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (o : ℍ) (θ : ℝ)
    {A : Type*} [TopologicalSpace A] (p : A → GluingSeamAngularDomain C g θ)
    (hs : ∀ a, (p a).1.1 ≤ 0) (u : A → Circle)
    (hpc : Continuous p) (huc : Continuous u) :
    Continuous (fun a => P.outgoingNativeUnitTangentTotal k o θ (p a) (hs a) (u a)) := by
  have hv := continuous_gluingFermiOutgoingUnitVectorCoordinates o (gluingRadius C g)
    (fun a => ((p a).1.1, -(p a).2.1))
    (fun a => by dsimp; linarith [P.radius_pos, hs a]) u
    ((continuous_subtype_val.comp hpc.fst).prodMk
      (continuous_subtype_val.comp hpc.snd).neg) huc
  exact P.nativeUnitTangentOfCoordinatesTotal_continuous
    (P.seamAngularComplexChart k θ) (Or.inr ⟨k, θ, rfl⟩)
    (fun a => P.seamAngularPoint k θ (p a))
    (fun a => P.outgoingNativeUnitCoordinates o θ (p a) (hs a) (u a))
    (fun a => Internal.GluingComponentTangentTransportHelpers.seamPoint_mem_chart P k θ (p a))
    (fun a => P.outgoingNativeUnitCoordinates_unit k o θ (p a) (hs a) (u a))
    ((P.seamAngularPoint_isOpenEmbedding k θ).continuous.comp hpc)
    (Complex.equivRealProdCLM.symm.continuous.comp (hv.fst.prodMk hv.snd.neg))

/-- Literal Fermi clutching agrees in the actual native tangent fiber.
This compares the full vectors, not merely their normalized phases. -/
theorem nativeUnitTangent_boundary_clutching
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (oIn oOut : ℍ) (θ : ℝ) (p : GluingSeamAngularDomain C g θ)
    (hs : p.1.1 = 0) (u : Circle) :
    P.incomingNativeUnitTangent k oIn θ p (by rw [hs])
        (gluingFermiBoundarySpinCircle (gluingRadius C g) (Circle.exp (-p.2.1)) ^ 2 * u) =
      P.outgoingNativeUnitTangent k oOut θ p (by rw [hs]) u := by
  have h := gluingFermiBoundary_unit_vectors_inverse_eq oIn oOut P.radius_pos (-p.2.1) u
  have hv : P.incomingNativeUnitCoordinates oIn θ p (by rw [hs])
      (gluingFermiBoundarySpinCircle (gluingRadius C g) (Circle.exp (-p.2.1)) ^ 2 * u) =
      P.outgoingNativeUnitCoordinates oOut θ p (by rw [hs]) u := by
    unfold incomingNativeUnitCoordinates outgoingNativeUnitCoordinates
      gluingFermiIncomingUnitVectorCoordinates gluingFermiOutgoingUnitVectorCoordinates
    simp only [hs, Circle.coe_mul, Circle.coe_pow]
    exact congrArg (fun v : ℝ × ℝ => (⟨v.1, -v.2⟩ : ℂ)) h
  apply Subtype.ext
  exact congrArg
    (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
      (⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩ : atlas ℂ P.GluedCarrier)).symmL
        ℝ (P.seamAngularPoint k θ p)) hv

section Interior

variable (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
  (z : ℍ) (ρ : ℝ) (hρ : 0 < ρ) (h4 : 4 * ρ < (X i).systole)
  (hq : ∀ w : Metric.ball z ρ,
    (Quotient.mk'' w.1 : (X i).Carrier) ∈ P.componentInteriorSet i)
  (hf : Topology.IsOpenEmbedding (fun w : Metric.ball z ρ =>
    P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' w.1, hq w⟩)))

/-- The actual preferred component ball is the source of its true native
interior chart, with its original topology. -/
def interiorBallSourceHomeomorph :
    Metric.ball z ρ ≃ₜ (P.gluedInteriorComplexChart i z ρ hρ hq hf).source :=
  hf.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (P.gluedInteriorComplexChart_source i z ρ hρ hq hf).symm)

@[simp] theorem interiorBallSourceHomeomorph_apply (w : Metric.ball z ρ) :
    (P.interiorBallSourceHomeomorph i z ρ hρ hq hf w).1 =
      P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' w.1, hq w⟩) := rfl

/-- Genuine preferred physical unit frames are homeomorphic to the original
native unit tangent bundle over the corresponding interior chart. -/
def interiorBallNativeUnitHomeomorph :
    (Metric.ball z ρ × Circle) ≃ₜ
      P.NativeUnitTangentOver (P.gluedInteriorComplexChart i z ρ hρ hq hf) :=
  ((P.interiorBallSourceHomeomorph i z ρ hρ hq hf).prodCongr
    (Homeomorph.refl Circle)).trans
      (P.nativeUnitTangentBundleHomeomorph
        (P.gluedInteriorComplexChart i z ρ hρ hq hf)
        (Or.inl ⟨i, z, ρ, hρ, h4, hq, hf, rfl⟩))

/-- This is a homeomorphism from the actual component frame orbit carrier,
not a newly supplied phase bundle. -/
def interiorTangentNativeUnitHomeomorph :
    (X i).TangentBallCarrier z ρ ≃ₜ
      P.NativeUnitTangentOver (P.gluedInteriorComplexChart i z ρ hρ hq hf) :=
  ((X i).tangentBallHomeomorph z (by linarith)).symm.trans
    (P.interiorBallNativeUnitHomeomorph i z ρ hρ h4 hq hf)

theorem interiorBallNativeUnitHomeomorph_coordinates (w : Metric.ball z ρ) (u : Circle) :
    P.nativeUnitTangentCoord (P.gluedInteriorComplexChart i z ρ hρ hq hf)
      (Or.inl ⟨i, z, ρ, hρ, h4, hq, hf, rfl⟩)
      ((P.interiorBallNativeUnitHomeomorph i z ρ hρ h4 hq hf (w, u)).1.1.proj)
      ⟨(P.interiorBallNativeUnitHomeomorph i z ρ hρ h4 hq hf (w, u)).1.1.snd,
        (P.interiorBallNativeUnitHomeomorph i z ρ hρ h4 hq hf (w, u)).1.2⟩ =
      (w.1.im : ℂ) * (u : ℂ) := by
  change P.nativeUnitTangentCoord _ _ _
    (P.nativeUnitTangentParam _ _ _
      (P.interiorBallSourceHomeomorph i z ρ hρ hq hf w).property u) = _
  rw [P.nativeUnitTangentCoord_param]
  have he : P.IsGluedInteriorComplexChart (P.gluedInteriorComplexChart i z ρ hρ hq hf) :=
    ⟨i, z, ρ, hρ, h4, hq, hf, rfl⟩
  rw [P.gluingChartTangentForm_interior _ he, P.interiorBallSourceHomeomorph_apply,
    P.gluedInteriorComplexChart_apply, gluingComplexHalfPlaneTangentForm_apply,
    Complex.mul_conj', Circle.norm_coe]
  simp only [Complex.ofReal_one, one_pow, Complex.one_re]
  rw [Real.sqrt_div (by norm_num), Real.sqrt_one, Real.sqrt_sq_eq_abs]
  change (1 / |w.1.im|)⁻¹ • (u : ℂ) = (w.1.im : ℂ) * (u : ℂ)
  rw [abs_of_pos w.1.im_pos, one_div, inv_inv]
  rfl

end Interior

end ExerciseGluingPreparation

#print axioms ClosedHyperbolicSurface.tangentBallParam_injective
#print axioms ClosedHyperbolicSurface.tangentBallHomeomorph
#print axioms gluingFermiBoundaryTangentTransition_unit_vector
#print axioms gluingFermiBoundary_unit_vectors_inverse_eq
#print axioms gluingFermiIncomingUnitVectorCoordinates_unit
#print axioms gluingFermiOutgoingUnitVectorCoordinates_unit
#print axioms gluingFermiIncomingUnitVectorCoordinates_weighted
#print axioms gluingFermiOutgoingUnitVectorCoordinates_weighted
#print axioms ExerciseGluingPreparation.incomingNativeUnitCoordinates_unit
#print axioms ExerciseGluingPreparation.outgoingNativeUnitCoordinates_unit
#print axioms ExerciseGluingPreparation.nativeUnitTangent_boundary_clutching
#print axioms continuous_gluingFermiIncomingUnitVectorCoordinates
#print axioms continuous_gluingFermiOutgoingUnitVectorCoordinates
#print axioms ExerciseGluingPreparation.continuous_incomingNativeUnitTangentTotal
#print axioms ExerciseGluingPreparation.continuous_outgoingNativeUnitTangentTotal
#print axioms ExerciseGluingPreparation.interiorTangentNativeUnitHomeomorph
#print axioms ExerciseGluingPreparation.interiorBallNativeUnitHomeomorph_coordinates

end

end SystolicGrowth
