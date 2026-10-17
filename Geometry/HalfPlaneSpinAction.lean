module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.HalfPlaneSpinMultiplier
public import Geometry.SurfaceDeckCovering
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Data.Set.Card

@[expose] public section

/-!
# The actual half-plane spin and oriented-frame actions

The denominator cocycle acts on two distinct copies of the half-plane times
the unit circle. Squaring the circle coordinate intertwines the spin action
with the genuine normalized tangent action. Its fibers are exactly the two
antipodal points. This construction is over the actual SL₂ action; it does
not assert the existence of a lift for a projective surface group.
-/

open UpperHalfPlane
open Topology
open scoped MatrixGroups UpperHalfPlane

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- The actual unit-valued denominator cocycle. -/
def halfPlaneSpinCircle (A : SL(2, ℝ)) (z : ℍ) : Circle :=
  ⟨halfPlaneSpinMultiplier A z,
    mem_sphere_zero_iff_norm.mpr (norm_halfPlaneSpinMultiplier A z)⟩

@[simp] theorem halfPlaneSpinCircle_coe (A : SL(2, ℝ)) (z : ℍ) :
    (halfPlaneSpinCircle A z : ℂ) = halfPlaneSpinMultiplier A z := rfl

theorem halfPlaneSpinCircle_mul (A B : SL(2, ℝ)) (z : ℍ) :
    halfPlaneSpinCircle (A * B) z =
      halfPlaneSpinCircle A (B • z) * halfPlaneSpinCircle B z := by
  apply Circle.coe_injective
  exact halfPlaneSpinMultiplier_mul A B z

@[simp] theorem halfPlaneSpinCircle_one (z : ℍ) :
    halfPlaneSpinCircle 1 z = 1 := by
  apply Circle.coe_injective
  simp

@[simp] theorem halfPlaneSpinCircle_neg_one (z : ℍ) :
    halfPlaneSpinCircle (-1) z = -1 := by
  apply Circle.coe_injective
  simp

theorem continuous_halfPlaneSpinCircle (A : SL(2, ℝ)) :
    Continuous (halfPlaneSpinCircle A) :=
  (continuous_halfPlaneSpinMultiplier A).subtype_mk _

/-- The multiplier is jointly continuous in the actual matrix and point. -/
theorem continuous_halfPlaneSpinMultiplier_uncurry :
    Continuous (fun p : SL(2, ℝ) × ℍ => halfPlaneSpinMultiplier p.1 p.2) := by
  have hD : Continuous
      (fun p : SL(2, ℝ) × ℍ => halfPlaneSpinDenominator p.1 p.2) := by
    unfold halfPlaneSpinDenominator
    fun_prop
  exact (Complex.continuous_ofReal.comp hD.norm).div hD
    (fun p => halfPlaneSpinDenominator_ne_zero p.1 p.2)

theorem continuous_halfPlaneSpinCircle_uncurry :
    Continuous (fun p : SL(2, ℝ) × ℍ => halfPlaneSpinCircle p.1 p.2) :=
  continuous_halfPlaneSpinMultiplier_uncurry.subtype_mk _

/-- A genuine separate carrier for spin directions over the half-plane. -/
@[ext] structure HalfPlaneSpinFrame where
  point : ℍ
  phase : Circle

/-- A genuine separate carrier for oriented tangent directions. -/
@[ext] structure HalfPlaneTangentFrame where
  point : ℍ
  phase : Circle

instance : TopologicalSpace HalfPlaneSpinFrame :=
  TopologicalSpace.induced (fun q => (q.point, q.phase)) inferInstance

instance : TopologicalSpace HalfPlaneTangentFrame :=
  TopologicalSpace.induced (fun q => (q.point, q.phase)) inferInstance

theorem continuous_halfPlaneSpinFrame_point :
    Continuous HalfPlaneSpinFrame.point := by
  exact continuous_fst.comp (show Continuous
    (fun q : HalfPlaneSpinFrame => (q.point, q.phase)) from continuous_induced_dom)

theorem continuous_halfPlaneSpinFrame_phase :
    Continuous HalfPlaneSpinFrame.phase := by
  exact continuous_snd.comp (show Continuous
    (fun q : HalfPlaneSpinFrame => (q.point, q.phase)) from continuous_induced_dom)

theorem continuous_halfPlaneTangentFrame_point :
    Continuous HalfPlaneTangentFrame.point := by
  exact continuous_fst.comp (show Continuous
    (fun q : HalfPlaneTangentFrame => (q.point, q.phase)) from continuous_induced_dom)

theorem continuous_halfPlaneTangentFrame_phase :
    Continuous HalfPlaneTangentFrame.phase := by
  exact continuous_snd.comp (show Continuous
    (fun q : HalfPlaneTangentFrame => (q.point, q.phase)) from continuous_induced_dom)

/-- The topology is exactly the ordinary product topology. -/
def halfPlaneSpinFrameHomeomorph : HalfPlaneSpinFrame ≃ₜ ℍ × Circle where
  toFun q := (q.point, q.phase)
  invFun q := ⟨q.1, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

/-- The oriented-frame carrier also has exactly the product topology. -/
def halfPlaneTangentFrameHomeomorph : HalfPlaneTangentFrame ≃ₜ ℍ × Circle where
  toFun q := (q.point, q.phase)
  invFun q := ⟨q.1, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

instance : T2Space HalfPlaneSpinFrame := halfPlaneSpinFrameHomeomorph.isEmbedding.t2Space
instance : T2Space HalfPlaneTangentFrame := halfPlaneTangentFrameHomeomorph.isEmbedding.t2Space

instance : LocallyCompactSpace HalfPlaneSpinFrame :=
  halfPlaneSpinFrameHomeomorph.isClosedEmbedding.locallyCompactSpace

instance : LocallyCompactSpace HalfPlaneTangentFrame :=
  halfPlaneTangentFrameHomeomorph.isClosedEmbedding.locallyCompactSpace

instance : MulAction SL(2, ℝ) HalfPlaneSpinFrame where
  smul A q := ⟨A • q.point, halfPlaneSpinCircle A q.point * q.phase⟩
  one_smul q := by
    apply HalfPlaneSpinFrame.ext
    · exact one_smul SL(2, ℝ) q.point
    · change halfPlaneSpinCircle 1 q.point * q.phase = q.phase
      simp
  mul_smul A B q := by
    apply HalfPlaneSpinFrame.ext
    · exact mul_smul A B q.point
    · change halfPlaneSpinCircle (A * B) q.point * q.phase =
        halfPlaneSpinCircle A (B • q.point) *
          (halfPlaneSpinCircle B q.point * q.phase)
      simp only [halfPlaneSpinCircle_mul, mul_assoc]

instance : MulAction SL(2, ℝ) HalfPlaneTangentFrame where
  smul A q := ⟨A • q.point, halfPlaneSpinCircle A q.point ^ 2 * q.phase⟩
  one_smul q := by
    apply HalfPlaneTangentFrame.ext
    · exact one_smul SL(2, ℝ) q.point
    · change halfPlaneSpinCircle 1 q.point ^ 2 * q.phase = q.phase
      simp
  mul_smul A B q := by
    apply HalfPlaneTangentFrame.ext
    · exact mul_smul A B q.point
    · change halfPlaneSpinCircle (A * B) q.point ^ 2 * q.phase =
        halfPlaneSpinCircle A (B • q.point) ^ 2 *
          (halfPlaneSpinCircle B q.point ^ 2 * q.phase)
      simp only [halfPlaneSpinCircle_mul, mul_pow, mul_assoc]

@[simp] theorem halfPlaneSpinFrame_smul_point (A : SL(2, ℝ)) (q : HalfPlaneSpinFrame) :
    (A • q).point = A • q.point := rfl

@[simp] theorem halfPlaneSpinFrame_smul_phase (A : SL(2, ℝ)) (q : HalfPlaneSpinFrame) :
    (A • q).phase = halfPlaneSpinCircle A q.point * q.phase := rfl

@[simp] theorem halfPlaneTangentFrame_smul_point (A : SL(2, ℝ))
    (q : HalfPlaneTangentFrame) : (A • q).point = A • q.point := rfl

@[simp] theorem halfPlaneTangentFrame_smul_phase (A : SL(2, ℝ))
    (q : HalfPlaneTangentFrame) :
    (A • q).phase = halfPlaneSpinCircle A q.point ^ 2 * q.phase := rfl

/-- The frame action is the phase of the literal native Möbius derivative. -/
theorem halfPlaneTangentFrame_smul_phase_eq_native_deriv (A : SL(2, ℝ))
    (q : HalfPlaneTangentFrame) :
    ((A • q).phase : ℂ) =
      (deriv (fun w : ℂ => ((A • UpperHalfPlane.ofComplex w : ℍ) : ℂ))
        (q.point : ℂ) /
      (‖deriv (fun w : ℂ => ((A • UpperHalfPlane.ofComplex w : ℍ) : ℂ))
        (q.point : ℂ)‖ : ℂ)) * (q.phase : ℂ) := by
  rw [halfPlaneTangentFrame_smul_phase, Circle.coe_mul, Circle.coe_pow,
    halfPlaneSpinCircle_coe, halfPlaneSpinMultiplier_sq_eq_normalized_native_deriv]

instance : ContinuousConstSMul SL(2, ℝ) HalfPlaneSpinFrame where
  continuous_const_smul A := by
    apply continuous_induced_rng.mpr
    exact ((continuous_const_smul A).comp continuous_halfPlaneSpinFrame_point).prodMk
      (((continuous_halfPlaneSpinCircle A).comp
        continuous_halfPlaneSpinFrame_point).mul continuous_halfPlaneSpinFrame_phase)

instance : ContinuousConstSMul SL(2, ℝ) HalfPlaneTangentFrame where
  continuous_const_smul A := by
    apply continuous_induced_rng.mpr
    exact ((continuous_const_smul A).comp continuous_halfPlaneTangentFrame_point).prodMk
      ((((continuous_halfPlaneSpinCircle A).comp
        continuous_halfPlaneTangentFrame_point).pow 2).mul
          continuous_halfPlaneTangentFrame_phase)

instance : ContinuousSMul SL(2, ℝ) HalfPlaneSpinFrame where
  continuous_smul := by
    apply continuous_induced_rng.mpr
    exact (continuous_fst.smul
      (continuous_halfPlaneSpinFrame_point.comp continuous_snd)).prodMk
      ((continuous_halfPlaneSpinCircle_uncurry.comp
        (continuous_fst.prodMk
          (continuous_halfPlaneSpinFrame_point.comp continuous_snd))).mul
        (continuous_halfPlaneSpinFrame_phase.comp continuous_snd))

instance : ContinuousSMul SL(2, ℝ) HalfPlaneTangentFrame where
  continuous_smul := by
    apply continuous_induced_rng.mpr
    exact (continuous_fst.smul
      (continuous_halfPlaneTangentFrame_point.comp continuous_snd)).prodMk
      (((continuous_halfPlaneSpinCircle_uncurry.comp
        (continuous_fst.prodMk
          (continuous_halfPlaneTangentFrame_point.comp continuous_snd))).pow 2).mul
        (continuous_halfPlaneTangentFrame_phase.comp continuous_snd))

/-- The literal fiberwise double map. -/
def halfPlaneSpinSquare (q : HalfPlaneSpinFrame) : HalfPlaneTangentFrame :=
  ⟨q.point, q.phase ^ 2⟩

theorem continuous_halfPlaneSpinSquare : Continuous halfPlaneSpinSquare := by
  apply continuous_induced_rng.mpr
  exact continuous_halfPlaneSpinFrame_point.prodMk
    (continuous_halfPlaneSpinFrame_phase.pow 2)

theorem halfPlaneSpinSquare_smul (A : SL(2, ℝ)) (q : HalfPlaneSpinFrame) :
    halfPlaneSpinSquare (A • q) = A • halfPlaneSpinSquare q := by
  apply HalfPlaneTangentFrame.ext
  · rfl
  · exact mul_pow _ _ _

/-- The nontrivial antipodal involution on actual spin directions. -/
def halfPlaneSpinAntipode (q : HalfPlaneSpinFrame) : HalfPlaneSpinFrame :=
  ⟨q.point, -q.phase⟩

theorem continuous_halfPlaneSpinAntipode : Continuous halfPlaneSpinAntipode := by
  apply continuous_induced_rng.mpr
  exact continuous_halfPlaneSpinFrame_point.prodMk
    continuous_halfPlaneSpinFrame_phase.neg

theorem halfPlaneSpinAntipode_smul (A : SL(2, ℝ)) (q : HalfPlaneSpinFrame) :
    halfPlaneSpinAntipode (A • q) = A • halfPlaneSpinAntipode q := by
  apply HalfPlaneSpinFrame.ext
  · rfl
  · change -(halfPlaneSpinCircle A q.point * q.phase) =
      halfPlaneSpinCircle A q.point * -q.phase
    exact (mul_neg _ _).symm

/-- The central matrix acts by the nontrivial deck involution of squaring. -/
theorem halfPlaneSpinFrame_neg_one_smul (q : HalfPlaneSpinFrame) :
    (-1 : SL(2, ℝ)) • q = halfPlaneSpinAntipode q := by
  apply HalfPlaneSpinFrame.ext
  · change (-1 : SL(2, ℝ)) • q.point = q.point
    apply UpperHalfPlane.ext
    simp [UpperHalfPlane.coe_specialLinearGroup_apply,
      Matrix.SpecialLinearGroup.coe_neg]
  · simp [halfPlaneSpinAntipode]

/-- The same central matrix acts trivially on actual oriented frames. -/
theorem halfPlaneTangentFrame_neg_one_smul (q : HalfPlaneTangentFrame) :
    (-1 : SL(2, ℝ)) • q = q := by
  apply HalfPlaneTangentFrame.ext
  · change (-1 : SL(2, ℝ)) • q.point = q.point
    apply UpperHalfPlane.ext
    simp [UpperHalfPlane.coe_specialLinearGroup_apply,
      Matrix.SpecialLinearGroup.coe_neg]
  · simp

@[simp] theorem halfPlaneSpinAntipode_involutive (q : HalfPlaneSpinFrame) :
    halfPlaneSpinAntipode (halfPlaneSpinAntipode q) = q := by
  apply HalfPlaneSpinFrame.ext <;> simp [halfPlaneSpinAntipode]

theorem halfPlaneSpinAntipode_ne (q : HalfPlaneSpinFrame) :
    halfPlaneSpinAntipode q ≠ q := by
  intro h
  have hphase : -(q.phase : ℂ) = q.phase := congrArg
    (fun p : HalfPlaneSpinFrame => (p.phase : ℂ)) h
  have hz : (q.phase : ℂ) = 0 := by linear_combination -(1 / 2 : ℂ) * hphase
  have hn := Circle.norm_coe q.phase
  rw [hz, norm_zero] at hn
  norm_num at hn

/-- Equality after squaring is exactly equality or antipodal equality. -/
theorem halfPlaneSpinSquare_eq_iff (q r : HalfPlaneSpinFrame) :
    halfPlaneSpinSquare q = halfPlaneSpinSquare r ↔
      q = r ∨ q = halfPlaneSpinAntipode r := by
  constructor
  · intro h
    have hp : q.point = r.point := congrArg HalfPlaneTangentFrame.point h
    have hs : (q.phase : ℂ) ^ 2 = (r.phase : ℂ) ^ 2 :=
      congrArg (fun p : HalfPlaneTangentFrame => (p.phase : ℂ)) h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hs | hs
    · exact Or.inl (HalfPlaneSpinFrame.ext hp (Circle.coe_injective hs))
    · exact Or.inr (HalfPlaneSpinFrame.ext hp (Circle.coe_injective hs))
  · rintro (rfl | rfl)
    · rfl
    · apply HalfPlaneTangentFrame.ext <;> simp [halfPlaneSpinSquare, halfPlaneSpinAntipode]

/-- Every oriented direction has an actual spin preimage. -/
theorem halfPlaneSpinSquare_surjective : Function.Surjective halfPlaneSpinSquare := by
  intro q
  refine ⟨⟨q.point, Circle.exp (Complex.arg q.phase / 2)⟩, ?_⟩
  apply HalfPlaneTangentFrame.ext
  · rfl
  · change Circle.exp (Complex.arg q.phase / 2) ^ 2 = q.phase
    rw [pow_two, ← Circle.exp_add]
    rw [show Complex.arg q.phase / 2 + Complex.arg q.phase / 2 =
      Complex.arg q.phase by ring, Circle.exp_arg]

/-- Actual squaring on the circle has genuine local inverse branches. -/
theorem circleSquare_isLocalHomeomorph :
    IsLocalHomeomorph (fun u : Circle => u ^ 2) := by
  have hd : IsLocalHomeomorph (fun t : ℝ => 2 * t) :=
    (Homeomorph.mulLeft₀ (2 : ℝ) (by norm_num)).isLocalHomeomorph
  have heq : (fun u : Circle => u ^ 2) ∘ Circle.exp =
      Circle.exp ∘ (fun t : ℝ => 2 * t) := by
    funext t
    change Circle.exp t ^ 2 = Circle.exp (2 * t)
    rw [pow_two, ← Circle.exp_add]
    congr 1
    ring
  have hc : IsLocalHomeomorph ((fun u : Circle => u ^ 2) ∘ Circle.exp) := by
    rw [heq]
    exact Circle.isCoveringMap_exp.isLocalHomeomorph.comp hd
  have h := (hc.isLocalHomeomorphOn (s := Set.univ)).of_comp_right
    (Circle.isCoveringMap_exp.isLocalHomeomorph.isLocalHomeomorphOn (s := Set.univ))
  rw [Set.image_univ, Circle.exp_surjective.range_eq] at h
  exact isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr h

/-- Local inverse branches on the actual product carriers, not just a
finite-fiber assertion. -/
theorem halfPlaneSpinSquare_isLocalHomeomorph : IsLocalHomeomorph halfPlaneSpinSquare := by
  have hp : IsLocalHomeomorph (Prod.map (id : ℍ → ℍ) (fun u : Circle => u ^ 2)) := by
    apply IsLocalHomeomorph.mk
    intro q
    obtain ⟨e, hq, he⟩ := circleSquare_isLocalHomeomorph q.2
    refine ⟨(OpenPartialHomeomorph.refl ℍ).prod e, ⟨Set.mem_univ _, hq⟩, ?_⟩
    intro r _hr
    apply Prod.ext
    · rfl
    · exact congrFun he r.2
  have h := halfPlaneTangentFrameHomeomorph.symm.isLocalHomeomorph.comp
    (hp.comp halfPlaneSpinFrameHomeomorph.isLocalHomeomorph)
  exact h

namespace ClosedHyperbolicSurface

/-- The concrete spin-direction orbit space of an already constructed
special-linear marked component. -/
abbrev SpinCarrier {g : ℕ} (X : ClosedHyperbolicSurface g) :=
  MulAction.orbitRel.Quotient X.deckGroup HalfPlaneSpinFrame

/-- The concrete oriented-direction orbit space, with its actual action. -/
abbrev TangentFrameCarrier {g : ℕ} (X : ClosedHyperbolicSurface g) :=
  MulAction.orbitRel.Quotient X.deckGroup HalfPlaneTangentFrame

instance {g : ℕ} (X : ClosedHyperbolicSurface g) :
    IsCancelSMul X.deckGroup HalfPlaneSpinFrame :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr fun A q h =>
    X.free A q.point (congrArg HalfPlaneSpinFrame.point h)

instance {g : ℕ} (X : ClosedHyperbolicSurface g) :
    IsCancelSMul X.deckGroup HalfPlaneTangentFrame :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr fun A q h =>
    X.free A q.point (congrArg HalfPlaneTangentFrame.point h)

instance {g : ℕ} (X : ClosedHyperbolicSurface g) :
    ProperlyDiscontinuousSMul X.deckGroup HalfPlaneSpinFrame where
  finite_disjoint_inter_image {K L} hK hL := by
    apply (ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := X.deckGroup)
      (hK.image continuous_halfPlaneSpinFrame_point)
      (hL.image continuous_halfPlaneSpinFrame_point)).subset
    rintro A ⟨q, ⟨r, hr, rfl⟩, hq⟩
    refine ⟨A • r.point, ⟨r.point, ⟨r, hr, rfl⟩, rfl⟩, ?_⟩
    exact ⟨A • r, hq, rfl⟩

instance {g : ℕ} (X : ClosedHyperbolicSurface g) :
    ProperlyDiscontinuousSMul X.deckGroup HalfPlaneTangentFrame where
  finite_disjoint_inter_image {K L} hK hL := by
    apply (ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := X.deckGroup)
      (hK.image continuous_halfPlaneTangentFrame_point)
      (hL.image continuous_halfPlaneTangentFrame_point)).subset
    rintro A ⟨q, ⟨r, hr, rfl⟩, hq⟩
    refine ⟨A • r.point, ⟨r.point, ⟨r, hr, rfl⟩, rfl⟩, ?_⟩
    exact ⟨A • r, hq, rfl⟩

/-- The spin orbit projection has genuine free, properly discontinuous sheets. -/
theorem spinOrbitProjection_isQuotientCoveringMap {g : ℕ}
    (X : ClosedHyperbolicSurface g) :
    IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel X.deckGroup
      HalfPlaneSpinFrame)) X.deckGroup :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- The frame orbit projection likewise has genuine covering sheets. -/
theorem tangentFrameOrbitProjection_isQuotientCoveringMap {g : ℕ}
    (X : ClosedHyperbolicSurface g) :
    IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel X.deckGroup
      HalfPlaneTangentFrame)) X.deckGroup :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- Squaring descends through the actual component deck action. -/
def spinSquare {g : ℕ} (X : ClosedHyperbolicSurface g) :
    X.SpinCarrier → X.TangentFrameCarrier :=
  Quotient.map' halfPlaneSpinSquare fun q r h => by
    obtain ⟨A, hA⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨A, ?_⟩
    change (A : SL(2, ℝ)) • halfPlaneSpinSquare r = halfPlaneSpinSquare q
    change (A : SL(2, ℝ)) • r = q at hA
    rw [← halfPlaneSpinSquare_smul, hA]

theorem continuous_spinSquare {g : ℕ} (X : ClosedHyperbolicSurface g) :
    Continuous X.spinSquare :=
  (continuous_quotient_mk'.comp continuous_halfPlaneSpinSquare).quotient_lift _

theorem spinSquare_surjective {g : ℕ} (X : ClosedHyperbolicSurface g) :
    Function.Surjective X.spinSquare := by
  intro q
  induction q using Quotient.inductionOn with
  | h q =>
    obtain ⟨r, rfl⟩ := halfPlaneSpinSquare_surjective q
    exact ⟨Quotient.mk _ r, rfl⟩

/-- The antipodal involution descends through the actual component action. -/
def spinAntipode {g : ℕ} (X : ClosedHyperbolicSurface g) :
    X.SpinCarrier → X.SpinCarrier :=
  Quotient.map' halfPlaneSpinAntipode fun q r h => by
    obtain ⟨A, hA⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨A, ?_⟩
    change (A : SL(2, ℝ)) • halfPlaneSpinAntipode r = halfPlaneSpinAntipode q
    change (A : SL(2, ℝ)) • r = q at hA
    rw [← halfPlaneSpinAntipode_smul, hA]

theorem continuous_spinAntipode {g : ℕ} (X : ClosedHyperbolicSurface g) :
    Continuous X.spinAntipode :=
  (continuous_quotient_mk'.comp continuous_halfPlaneSpinAntipode).quotient_lift _

@[simp] theorem spinAntipode_involutive {g : ℕ} (X : ClosedHyperbolicSurface g)
    (q : X.SpinCarrier) : X.spinAntipode (X.spinAntipode q) = q := by
  induction q using Quotient.inductionOn with
  | h q => exact congrArg (Quotient.mk _) (halfPlaneSpinAntipode_involutive q)

/-- Base-action freeness prevents a deck translate from identifying the
two actual antipodal spin directions. -/
theorem spinAntipode_ne {g : ℕ} (X : ClosedHyperbolicSurface g)
    (q : X.SpinCarrier) : X.spinAntipode q ≠ q := by
  induction q using Quotient.inductionOn with
  | h q =>
    intro h
    obtain ⟨A, hA⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp
      (Quotient.exact h))
    have hp : A • q.point = q.point := congrArg HalfPlaneSpinFrame.point hA
    have hAone := X.free A q.point hp
    subst A
    rw [one_smul] at hA
    exact halfPlaneSpinAntipode_ne q hA.symm

/-- The genuine component quotient still has exactly antipodal square fibers. -/
theorem spinSquare_eq_iff {g : ℕ} (X : ClosedHyperbolicSurface g)
    (q r : X.SpinCarrier) :
    X.spinSquare q = X.spinSquare r ↔ q = r ∨ q = X.spinAntipode r := by
  induction q using Quotient.inductionOn with
  | h q =>
    induction r using Quotient.inductionOn with
    | h r =>
      constructor
      · intro h
        obtain ⟨A, hA⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp
          (Quotient.exact h))
        change (A : SL(2, ℝ)) • halfPlaneSpinSquare r = halfPlaneSpinSquare q at hA
        rw [← halfPlaneSpinSquare_smul] at hA
        rcases (halfPlaneSpinSquare_eq_iff q ((A : SL(2, ℝ)) • r)).mp hA.symm with
          hq | hq
        · apply Or.inl
          apply Quotient.sound
          apply MulAction.orbitRel_apply.mpr
          exact MulAction.mem_orbit_iff.mpr ⟨A, hq.symm⟩
        · apply Or.inr
          apply Quotient.sound
          apply MulAction.orbitRel_apply.mpr
          refine MulAction.mem_orbit_iff.mpr ⟨A, ?_⟩
          change (A : SL(2, ℝ)) • halfPlaneSpinAntipode r = q
          rw [← halfPlaneSpinAntipode_smul]
          exact hq.symm
      · rintro (h | h)
        · exact congrArg X.spinSquare h
        · rw [h]
          exact congrArg (Quotient.mk _)
            ((halfPlaneSpinSquare_eq_iff (halfPlaneSpinAntipode r) r).mpr (Or.inr rfl))

/-- The actual component spin map has genuine local inverse sheets, obtained
from the upstairs local branches and the original free deck-covering sheets. -/
theorem spinSquare_isLocalHomeomorph {g : ℕ} (X : ClosedHyperbolicSurface g) :
    IsLocalHomeomorph X.spinSquare := by
  have hc : IsLocalHomeomorph (X.spinSquare ∘
      Quotient.mk (MulAction.orbitRel X.deckGroup HalfPlaneSpinFrame)) :=
    X.tangentFrameOrbitProjection_isQuotientCoveringMap.isCoveringMap.isLocalHomeomorph.comp
      halfPlaneSpinSquare_isLocalHomeomorph
  have h := (hc.isLocalHomeomorphOn (s := Set.univ)).of_comp_right
    (X.spinOrbitProjection_isQuotientCoveringMap.isCoveringMap.isLocalHomeomorph.isLocalHomeomorphOn
      (s := Set.univ))
  rw [Set.image_univ,
    X.spinOrbitProjection_isQuotientCoveringMap.surjective.range_eq] at h
  exact isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr h

theorem spinSquare_isQuotientMap {g : ℕ} (X : ClosedHyperbolicSurface g) :
    IsQuotientMap X.spinSquare :=
  X.spinSquare_isLocalHomeomorph.isOpenMap.isQuotientMap
    X.continuous_spinSquare X.spinSquare_surjective

/-- Saturation of a closed set adds exactly its continuous antipodal image. -/
theorem spinSquare_isClosedMap {g : ℕ} (X : ClosedHyperbolicSurface g) :
    IsClosedMap X.spinSquare := by
  intro C hC
  apply X.spinSquare_isQuotientMap.isClosed_preimage.mp
  have heq : X.spinSquare ⁻¹' (X.spinSquare '' C) =
      C ∪ X.spinAntipode ⁻¹' C := by
    ext q
    constructor
    · rintro ⟨r, hr, hqr⟩
      rcases (X.spinSquare_eq_iff q r).mp hqr.symm with h | h
      · exact Or.inl (h ▸ hr)
      · right
        change X.spinAntipode q ∈ C
        rwa [h, X.spinAntipode_involutive]
    · rintro (hq | hq)
      · exact ⟨q, hq, rfl⟩
      · refine ⟨X.spinAntipode q, hq, ?_⟩
        exact (X.spinSquare_eq_iff (X.spinAntipode q) q).mpr (Or.inr rfl)
  rw [heq]
  exact hC.union (hC.preimage X.continuous_spinAntipode)

/-- Every literal fiber consists of two distinct antipodal points. -/
theorem spinSquare_fiber {g : ℕ} (X : ClosedHyperbolicSurface g)
    (q : X.SpinCarrier) :
    X.spinSquare ⁻¹' {X.spinSquare q} = {q, X.spinAntipode q} := by
  ext r
  exact X.spinSquare_eq_iff r q

/-- The concrete spin-direction quotient is a genuine double covering of
the actual oriented-frame quotient of the original hyperbolic component. -/
theorem spinSquare_isCoveringMap {g : ℕ} (X : ClosedHyperbolicSurface g) :
    IsCoveringMap X.spinSquare := by
  apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
  apply X.spinSquare_isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
  · intro q _hq
    obtain ⟨r, rfl⟩ := X.spinSquare_surjective q
    rw [X.spinSquare_fiber]
    exact (Set.finite_singleton _).insert _
  · exact X.spinSquare_isLocalHomeomorph.isLocalHomeomorphOn

/-- The cardinality is literally two at every frame, including downstairs. -/
theorem spinSquare_fiber_ncard {g : ℕ} (X : ClosedHyperbolicSurface g)
    (q : X.TangentFrameCarrier) : (X.spinSquare ⁻¹' {q}).ncard = 2 := by
  obtain ⟨r, rfl⟩ := X.spinSquare_surjective q
  rw [X.spinSquare_fiber]
  exact Set.ncard_pair (X.spinAntipode_ne r).symm

/-- The spin carrier lies over the unchanged native component. -/
def spinBase {g : ℕ} (X : ClosedHyperbolicSurface g) : X.SpinCarrier → X.Carrier :=
  Quotient.map' HalfPlaneSpinFrame.point fun q r h => by
    obtain ⟨A, hA⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    apply MulAction.orbitRel_apply.mpr
    exact MulAction.mem_orbit_iff.mpr ⟨A, congrArg HalfPlaneSpinFrame.point hA⟩

/-- The frame carrier lies over the same unchanged component. -/
def tangentFrameBase {g : ℕ} (X : ClosedHyperbolicSurface g) :
    X.TangentFrameCarrier → X.Carrier :=
  Quotient.map' HalfPlaneTangentFrame.point fun q r h => by
    obtain ⟨A, hA⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    apply MulAction.orbitRel_apply.mpr
    exact MulAction.mem_orbit_iff.mpr ⟨A, congrArg HalfPlaneTangentFrame.point hA⟩

theorem continuous_spinBase {g : ℕ} (X : ClosedHyperbolicSurface g) :
    Continuous X.spinBase :=
  (continuous_quotient_mk'.comp continuous_halfPlaneSpinFrame_point).quotient_lift _

theorem continuous_tangentFrameBase {g : ℕ} (X : ClosedHyperbolicSurface g) :
    Continuous X.tangentFrameBase :=
  (continuous_quotient_mk'.comp continuous_halfPlaneTangentFrame_point).quotient_lift _

/-- The actual double map preserves the native surface point exactly. -/
@[simp] theorem tangentFrameBase_spinSquare {g : ℕ} (X : ClosedHyperbolicSurface g)
    (q : X.SpinCarrier) : X.tangentFrameBase (X.spinSquare q) = X.spinBase q := by
  induction q using Quotient.inductionOn with
  | h q => rfl

end ClosedHyperbolicSurface

#print axioms halfPlaneSpinSquare_smul
#print axioms halfPlaneSpinSquare_eq_iff
#print axioms halfPlaneSpinSquare_surjective
#print axioms continuous_halfPlaneSpinMultiplier_uncurry
#print axioms halfPlaneSpinFrame_neg_one_smul
#print axioms ClosedHyperbolicSurface.spinOrbitProjection_isQuotientCoveringMap
#print axioms ClosedHyperbolicSurface.tangentFrameOrbitProjection_isQuotientCoveringMap
#print axioms ClosedHyperbolicSurface.spinSquare_surjective
#print axioms ClosedHyperbolicSurface.spinAntipode_ne
#print axioms ClosedHyperbolicSurface.spinSquare_eq_iff
#print axioms halfPlaneSpinSquare_isLocalHomeomorph
#print axioms ClosedHyperbolicSurface.spinSquare_isCoveringMap
#print axioms halfPlaneTangentFrame_smul_phase_eq_native_deriv
#print axioms ClosedHyperbolicSurface.spinSquare_fiber_ncard
#print axioms ClosedHyperbolicSurface.tangentFrameBase_spinSquare

end
end SystolicGrowth
