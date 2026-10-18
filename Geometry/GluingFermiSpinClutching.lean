module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingPolarSpinCover

@[expose] public section

/-!
# Concrete spin clutching across an oriented Fermi seam

In the corrected orientation, the incoming polar coordinates are
`(r+t, θ)` and the outgoing coordinates are `(r-t, -θ)`. Their actual radial
differentials determine explicit unit square roots. The ratio at `t=0`
is genuinely periodic and therefore gives a continuous circle-valued seam
transition. Its square is the ratio of the actual normalized Fermi radial
differentials. No global spin structure or surface-relator parity is assumed.
-/

open UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- The literal incoming branch in the corrected oriented Fermi coordinates. -/
def gluingFermiIncomingLift (o : ℍ) (r : ℝ) (p : ℝ × ℝ) : ℂ :=
  gluingPolarLift o (r + p.1, p.2)

/-- The literal outgoing branch includes both actual signed reflections. -/
def gluingFermiOutgoingLift (o : ℍ) (r : ℝ) (p : ℝ × ℝ) : ℂ :=
  gluingPolarLift o (r - p.1, -p.2)

theorem gluingFermiIncomingLift_radial_fderiv (o : ℍ) (r : ℝ) (p : ℝ × ℝ) :
    (fderiv ℝ (gluingFermiIncomingLift o r) p) (1, 0) =
      (fderiv ℝ (gluingPolarLift o) (r + p.1, p.2)) (1, 0) := by
  have hparam := ((hasFDerivAt_const r p).add
    (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).prodMk
      (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  have h := (gluingPolarLift_hasFDerivAt o (r + p.1, p.2)).comp p hparam
  change HasFDerivAt (gluingFermiIncomingLift o r) _ p at h
  rw [h.fderiv, (gluingPolarLift_hasFDerivAt o (r + p.1, p.2)).fderiv]
  simp

theorem gluingFermiOutgoingLift_radial_fderiv (o : ℍ) (r : ℝ) (p : ℝ × ℝ) :
    (fderiv ℝ (gluingFermiOutgoingLift o r) p) (1, 0) =
      -(fderiv ℝ (gluingPolarLift o) (r - p.1, -p.2)) (1, 0) := by
  have hparam := ((hasFDerivAt_const r p).sub
    (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).prodMk
      (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).neg
  have h := (gluingPolarLift_hasFDerivAt o (r - p.1, -p.2)).comp p hparam
  change HasFDerivAt (gluingFermiOutgoingLift o r) _ p at h
  rw [h.fderiv, (gluingPolarLift_hasFDerivAt o (r - p.1, -p.2)).fderiv]
  simp
  simpa using map_neg (gluingPolarLiftFDeriv o (r - p.1, -p.2)) ((1, 0) : ℝ × ℝ)

/-- The positive incoming Fermi radial square root. -/
def gluingFermiIncomingSpinCircle (r : ℝ) (p : ℝ × ℝ) : Circle :=
  gluingPolarSpinCircle (r + p.1, p.2)

/-- The outgoing radial reflection contributes the explicit square root `i`. -/
def gluingFermiOutgoingSpinCircle (r : ℝ) (p : ℝ × ℝ) : Circle :=
  Circle.exp (Real.pi / 2) * gluingPolarSpinCircle (r - p.1, -p.2)

theorem gluingFermiIncomingSpinCircle_sq_eq_normalized_radial_fderiv
    (o : ℍ) (r : ℝ) (p : ℝ × ℝ) :
    (gluingFermiIncomingSpinCircle r p : ℂ) ^ 2 =
      (fderiv ℝ (gluingFermiIncomingLift o r) p) (1, 0) /
        (‖(fderiv ℝ (gluingFermiIncomingLift o r) p) (1, 0)‖ : ℂ) := by
  rw [gluingFermiIncomingLift_radial_fderiv]
  exact gluingPolarSpinMultiplier_sq_eq_normalized_radial_fderiv o (r + p.1, p.2)

theorem gluingFermiOutgoingSpinCircle_sq_eq_normalized_radial_fderiv
    (o : ℍ) (r : ℝ) (p : ℝ × ℝ) :
    (gluingFermiOutgoingSpinCircle r p : ℂ) ^ 2 =
      (fderiv ℝ (gluingFermiOutgoingLift o r) p) (1, 0) /
        (‖(fderiv ℝ (gluingFermiOutgoingLift o r) p) (1, 0)‖ : ℂ) := by
  rw [gluingFermiOutgoingLift_radial_fderiv, norm_neg, neg_div]
  change (↑(Circle.exp (Real.pi / 2) * gluingPolarSpinCircle (r - p.1, -p.2)) : ℂ) ^ 2 = _
  rw [Circle.coe_mul, mul_pow, Circle.coe_exp]
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.exp_pi_div_two_mul_I, Complex.I_sq, neg_one_mul]
  rw [gluingPolarSpinCircle_coe,
    gluingPolarSpinMultiplier_sq_eq_normalized_radial_fderiv]

theorem continuous_gluingFermiIncomingSpinCircle (r : ℝ) :
    Continuous (gluingFermiIncomingSpinCircle r) :=
  continuous_gluingPolarSpinCircle.comp
    ((continuous_const.add continuous_fst).prodMk continuous_snd)

theorem continuous_gluingFermiOutgoingSpinCircle (r : ℝ) :
    Continuous (gluingFermiOutgoingSpinCircle r) :=
  continuous_const.mul (continuous_gluingPolarSpinCircle.comp
    ((continuous_const.sub continuous_fst).prodMk continuous_snd.neg))

/-- The actual relative square root between the two oriented radial frames. -/
def gluingFermiBoundarySpinMultiplier (r θ : ℝ) : Circle :=
  gluingFermiIncomingSpinCircle r (0, θ) / gluingFermiOutgoingSpinCircle r (0, θ)

theorem continuous_gluingFermiBoundarySpinMultiplier (r : ℝ) :
    Continuous (gluingFermiBoundarySpinMultiplier r) :=
  ((continuous_gluingFermiIncomingSpinCircle r).comp
    (continuous_const.prodMk continuous_id)).div'
      ((continuous_gluingFermiOutgoingSpinCircle r).comp
        (continuous_const.prodMk continuous_id))

theorem gluingPolarSpinCircle_neg_add_two_pi (r θ : ℝ) :
    gluingPolarSpinCircle (r, -(θ + 2 * Real.pi)) =
      -gluingPolarSpinCircle (r, -θ) := by
  have h := gluingPolarSpinCircle_add_two_pi r (-(θ + 2 * Real.pi))
  rw [show -(θ + 2 * Real.pi) + 2 * Real.pi = -θ by ring] at h
  simpa only [neg_neg] using congrArg Neg.neg h.symm

/-- The two actual antiperiodic radial roots cancel their signs. -/
theorem gluingFermiBoundarySpinMultiplier_periodic (r : ℝ) :
    Function.Periodic (gluingFermiBoundarySpinMultiplier r) (2 * Real.pi) := by
  intro θ
  apply Circle.coe_injective
  simp only [gluingFermiBoundarySpinMultiplier, gluingFermiIncomingSpinCircle,
    gluingFermiOutgoingSpinCircle, add_zero, sub_zero, gluingPolarSpinCircle_add_two_pi,
    gluingPolarSpinCircle_neg_add_two_pi, Circle.coe_div, Circle.coe_mul, Circle.coe_neg]
  rw [mul_neg, neg_div_neg_eq]

/-- The concrete periodic transition on the actual boundary circle. -/
def gluingFermiBoundarySpinCircle (r : ℝ) (u : Circle) : Circle :=
  (gluingFermiBoundarySpinMultiplier_periodic r).lift
    (AddCircle.homeomorphCircle'.symm u)

@[simp] theorem gluingFermiBoundarySpinCircle_exp (r θ : ℝ) :
    gluingFermiBoundarySpinCircle r (Circle.exp θ) =
      gluingFermiBoundarySpinMultiplier r θ := by
  unfold gluingFermiBoundarySpinCircle
  rw [← AddCircle.homeomorphCircle'_apply_mk θ]
  rw [Homeomorph.symm_apply_apply, Function.Periodic.lift_coe]

theorem continuous_gluingFermiBoundarySpinCircle (r : ℝ) :
    Continuous (gluingFermiBoundarySpinCircle r) := by
  have h : Continuous (gluingFermiBoundarySpinMultiplier_periodic r).lift := by
    unfold Function.Periodic.lift
    exact (continuous_gluingFermiBoundarySpinMultiplier r).quotient_liftOn' _
  exact h.comp AddCircle.homeomorphCircle'.symm.continuous

/-- The circle transition squares to the ratio of the two literal Fermi
radial derivative phases, at their actual component points. -/
theorem gluingFermiBoundarySpinCircle_sq_eq_radial_phase_ratio
    (oIn oOut : ℍ) (r θ : ℝ) :
    (gluingFermiBoundarySpinCircle r (Circle.exp θ) : ℂ) ^ 2 =
      ((fderiv ℝ (gluingFermiIncomingLift oIn r) (0, θ)) (1, 0) /
        (‖(fderiv ℝ (gluingFermiIncomingLift oIn r) (0, θ)) (1, 0)‖ : ℂ)) /
      ((fderiv ℝ (gluingFermiOutgoingLift oOut r) (0, θ)) (1, 0) /
        (‖(fderiv ℝ (gluingFermiOutgoingLift oOut r) (0, θ)) (1, 0)‖ : ℂ)) := by
  rw [gluingFermiBoundarySpinCircle_exp, gluingFermiBoundarySpinMultiplier,
    Circle.coe_div, div_pow,
    gluingFermiIncomingSpinCircle_sq_eq_normalized_radial_fderiv oIn,
    gluingFermiOutgoingSpinCircle_sq_eq_normalized_radial_fderiv oOut]

/-- The actual reflected boundary angle and fiberwise spin transition. -/
def gluingFermiBoundarySpinHomeomorph (r : ℝ) :
    Circle × Circle ≃ₜ Circle × Circle where
  toFun p := (p.1⁻¹, gluingFermiBoundarySpinCircle r p.1⁻¹ * p.2)
  invFun p := (p.1⁻¹, (gluingFermiBoundarySpinCircle r p.1)⁻¹ * p.2)
  left_inv p := by
    apply Prod.ext
    · simp
    · simp
  right_inv p := by
    apply Prod.ext
    · simp
    · simp
  continuous_toFun := continuous_fst.inv.prodMk
    (((continuous_gluingFermiBoundarySpinCircle r).comp continuous_fst.inv).mul continuous_snd)
  continuous_invFun := continuous_fst.inv.prodMk
    (((continuous_gluingFermiBoundarySpinCircle r).comp continuous_fst).inv.mul continuous_snd)

/-- The corresponding literal tangent-direction transition. -/
def gluingFermiBoundaryTangentHomeomorph (r : ℝ) :
    Circle × Circle ≃ₜ Circle × Circle where
  toFun p := (p.1⁻¹, gluingFermiBoundarySpinCircle r p.1⁻¹ ^ 2 * p.2)
  invFun p := (p.1⁻¹, (gluingFermiBoundarySpinCircle r p.1 ^ 2)⁻¹ * p.2)
  left_inv p := by
    apply Prod.ext
    · simp
    · simp
  right_inv p := by
    apply Prod.ext
    · simp
    · simp
  continuous_toFun := by
    have h : Continuous (fun p : Circle × Circle =>
        gluingFermiBoundarySpinCircle r p.1⁻¹ ^ 2) :=
      ((continuous_gluingFermiBoundarySpinCircle r).comp continuous_fst.inv).pow 2
    exact continuous_fst.inv.prodMk (h.mul continuous_snd)
  continuous_invFun := by
    have h : Continuous (fun p : Circle × Circle =>
        gluingFermiBoundarySpinCircle r p.1 ^ 2) :=
      ((continuous_gluingFermiBoundarySpinCircle r).comp continuous_fst).pow 2
    exact continuous_fst.inv.prodMk (h.inv.mul continuous_snd)

/-- The genuine two boundary homeomorphisms commute exactly with squaring. -/
theorem gluingFermiBoundarySpinHomeomorph_square (r : ℝ) (p : Circle × Circle) :
    Prod.map id (fun u : Circle => u ^ 2) (gluingFermiBoundarySpinHomeomorph r p) =
      gluingFermiBoundaryTangentHomeomorph r (Prod.map id (fun u : Circle => u ^ 2) p) := by
  apply Prod.ext
  · rfl
  · exact mul_pow _ _ _

/-- This transition sends the original outgoing radial root to the actual
incoming radial root, with the prescribed reflected circle point. -/
theorem gluingFermiBoundarySpinHomeomorph_radial_roots (r θ : ℝ) :
    gluingFermiBoundarySpinHomeomorph r
      (Circle.exp (-θ), gluingFermiOutgoingSpinCircle r (0, θ)) =
        (Circle.exp θ, gluingFermiIncomingSpinCircle r (0, θ)) := by
  apply Prod.ext
  · simp [gluingFermiBoundarySpinHomeomorph, Circle.exp_neg]
  · change gluingFermiBoundarySpinCircle r (Circle.exp (-θ))⁻¹ *
      gluingFermiOutgoingSpinCircle r (0, θ) = gluingFermiIncomingSpinCircle r (0, θ)
    rw [Circle.exp_neg, inv_inv, gluingFermiBoundarySpinCircle_exp]
    simp [gluingFermiBoundarySpinMultiplier, div_eq_mul_inv, mul_assoc]

#print axioms gluingFermiIncomingLift_radial_fderiv
#print axioms gluingFermiOutgoingLift_radial_fderiv
#print axioms gluingFermiBoundarySpinMultiplier_periodic
#print axioms continuous_gluingFermiBoundarySpinCircle
#print axioms gluingFermiBoundarySpinCircle_sq_eq_radial_phase_ratio
#print axioms gluingFermiBoundarySpinHomeomorph_square
#print axioms gluingFermiBoundarySpinHomeomorph_radial_roots

end
end SystolicGrowth
