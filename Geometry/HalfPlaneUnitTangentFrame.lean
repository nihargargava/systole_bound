module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.UpperHalfPlaneRiemannianMetric
public import Geometry.HalfPlaneSpinAction
public import Geometry.GluingNativeTangentDescent

@[expose] public section

/-!
# Actual Poincaré unit tangent frames

The physical vector at `z` corresponding to a unit phase `u` is `im(z) * u`.
These frames are identified with the literal Poincaré-unit tangent total
bundle, with its actual bundle topology. The full Möbius derivative, rather
than an unrelated phase action, realizes their special-linear action.
-/

open Bundle Manifold Set UpperHalfPlane Topology
open scoped MatrixGroups UpperHalfPlane Manifold ContDiff RealInnerProductSpace

noncomputable section

namespace SystolicGrowth

set_option backward.isDefEq.respectTransparency false

abbrev HalfPlaneUnitTangentCarrier :=
  {v : TotalSpace ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ) : ℍ → Type) //
    upperHalfPlanePoincareMetric.inner v.proj v.snd v.snd = 1}

abbrev Internal.HalfPlaneUnitTangentFrameHelpers.halfPlaneTangentTrivialization :=
  trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ)) UpperHalfPlane.I

private theorem halfPlaneTangentTrivialization_apply
    (v : TotalSpace ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ) : ℍ → Type)) :
    Internal.HalfPlaneUnitTangentFrameHelpers.halfPlaneTangentTrivialization v = (v.proj, v.snd) := by
  apply Prod.ext
  · rfl
  · have hb : v.proj ∈ Internal.HalfPlaneUnitTangentFrameHelpers.halfPlaneTangentTrivialization.baseSet := mem_univ _
    rw [← Internal.HalfPlaneUnitTangentFrameHelpers.halfPlaneTangentTrivialization.continuousLinearMapAt_apply_of_mem ℝ hb]
    rw [TangentBundle.continuousLinearMapAt_trivializationAt (mem_univ _)]
    change mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      (fun z : ℍ => (z : ℂ)) v.proj v.snd = v.snd
    rw [upperHalfPlane_coe_mfderiv_real]
    rfl

private theorem continuous_halfPlaneTangent_vector :
    Continuous (fun v : TotalSpace ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : ℍ → Type) => v.snd) := by
  have h := Internal.HalfPlaneUnitTangentFrameHelpers.halfPlaneTangentTrivialization.continuousOn.comp_continuous continuous_id
    (fun v => show v ∈ Internal.HalfPlaneUnitTangentFrameHelpers.halfPlaneTangentTrivialization.source from mem_univ _)
  exact h.snd.congr (fun v => congrArg Prod.snd (halfPlaneTangentTrivialization_apply v))

private theorem continuous_halfPlaneTangent_mk :
    Continuous (fun p : ℍ × ℂ =>
      (⟨p.1, p.2⟩ : TotalSpace ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ) : ℍ → Type))) := by
  have h := Internal.HalfPlaneUnitTangentFrameHelpers.halfPlaneTangentTrivialization.continuousOn_symm.comp_continuous continuous_id
    (fun p => show p ∈ Internal.HalfPlaneUnitTangentFrameHelpers.halfPlaneTangentTrivialization.target from ⟨mem_univ _, mem_univ _⟩)
  apply h.congr
  intro p
  have he := Internal.HalfPlaneUnitTangentFrameHelpers.halfPlaneTangentTrivialization.left_inv
    (show (⟨p.1, p.2⟩ : TotalSpace ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : ℍ → Type)) ∈
        Internal.HalfPlaneUnitTangentFrameHelpers.halfPlaneTangentTrivialization.source from mem_univ _)
  change Internal.HalfPlaneUnitTangentFrameHelpers.halfPlaneTangentTrivialization.toOpenPartialHomeomorph.symm
    (Internal.HalfPlaneUnitTangentFrameHelpers.halfPlaneTangentTrivialization ⟨p.1, p.2⟩) = _ at he
  rw [halfPlaneTangentTrivialization_apply] at he
  exact (Internal.HalfPlaneUnitTangentFrameHelpers.halfPlaneTangentTrivialization.toPretrivialization.mk_symm
    (mem_univ _) p.2).trans he

/-- **Math.** The actual unit vector of a physical half-plane frame. -/
def halfPlaneFrameUnitTangent (q : HalfPlaneTangentFrame) : HalfPlaneUnitTangentCarrier := by
  refine ⟨⟨q.point, q.point.im • (q.phase : ℂ)⟩, ?_⟩
  rw [upperHalfPlanePoincareMetric_inner, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, abs_of_pos q.point.im_pos, Circle.norm_coe, mul_one]
  exact div_self (pow_ne_zero 2 q.point.im_pos.ne')

/-- **Math.** A literal Poincaré-unit tangent vector has norm `im(z)`. -/
theorem halfPlaneUnitTangent_norm (v : HalfPlaneUnitTangentCarrier) :
    @norm ℂ inferInstance v.val.snd = v.val.proj.im := by
  have h := v.property
  rw [upperHalfPlanePoincareMetric_inner, real_inner_self_eq_norm_sq] at h
  have hsq : (@norm ℂ inferInstance v.val.snd) ^ 2 = v.val.proj.im ^ 2 :=
    (div_eq_one_iff_eq (pow_ne_zero 2 v.val.proj.im_pos.ne')).mp h
  nlinarith [@norm_nonneg ℂ inferInstance v.val.snd, v.val.proj.im_pos]

/-- **Math.** Recover the true phase by dividing the actual tangent vector
by its positive hyperbolic height scale. -/
def halfPlaneUnitTangentFrame (v : HalfPlaneUnitTangentCarrier) : HalfPlaneTangentFrame where
  point := v.val.proj
  phase := ⟨v.val.proj.im⁻¹ • v.val.snd, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr v.val.proj.im_pos),
      halfPlaneUnitTangent_norm, inv_mul_cancel₀ v.val.proj.im_pos.ne']⟩

@[simp] theorem halfPlaneUnitTangentFrame_frame (q : HalfPlaneTangentFrame) :
    halfPlaneUnitTangentFrame (halfPlaneFrameUnitTangent q) = q := by
  apply HalfPlaneTangentFrame.ext
  · rfl
  · apply Subtype.ext
    change q.point.im⁻¹ • (q.point.im • (q.phase : ℂ)) = (q.phase : ℂ)
    rw [smul_smul, inv_mul_cancel₀ q.point.im_pos.ne', one_smul]

@[simp] theorem halfPlaneFrameUnitTangent_frame (v : HalfPlaneUnitTangentCarrier) :
    halfPlaneFrameUnitTangent (halfPlaneUnitTangentFrame v) = v := by
  apply Subtype.ext
  change TotalSpace.mk v.val.proj
    (v.val.proj.im • (v.val.proj.im⁻¹ • v.val.snd)) = v.val
  rw [smul_smul, mul_inv_cancel₀ v.val.proj.im_pos.ne', one_smul]

theorem continuous_halfPlaneFrameUnitTangent : Continuous halfPlaneFrameUnitTangent := by
  apply Continuous.subtype_mk
  have hp := continuous_halfPlaneTangentFrame_point
  have hu := continuous_subtype_val.comp continuous_halfPlaneTangentFrame_phase
  exact continuous_halfPlaneTangent_mk.comp
    (hp.prodMk ((UpperHalfPlane.continuous_im.comp hp).smul hu))

theorem continuous_halfPlaneUnitTangentFrame : Continuous halfPlaneUnitTangentFrame := by
  apply continuous_induced_rng.mpr
  have hp : Continuous (fun v : HalfPlaneUnitTangentCarrier => v.val.proj) :=
    (FiberBundle.continuous_proj ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ) : ℍ → Type)).comp
      continuous_subtype_val
  have hv : Continuous (fun v : HalfPlaneUnitTangentCarrier => v.val.snd) :=
    continuous_halfPlaneTangent_vector.comp continuous_subtype_val
  have hi := (UpperHalfPlane.continuous_im.comp hp).inv₀
    (fun v => v.val.proj.im_pos.ne')
  exact hp.prodMk ((hi.smul hv).subtype_mk _)

/-- **Math.** Physical oriented frames are exactly the genuine unit total
bundle of the actual Poincaré metric, with its unchanged bundle topology. -/
def halfPlaneUnitTangentHomeomorph : HalfPlaneTangentFrame ≃ₜ HalfPlaneUnitTangentCarrier where
  toFun := halfPlaneFrameUnitTangent
  invFun := halfPlaneUnitTangentFrame
  left_inv := halfPlaneUnitTangentFrame_frame
  right_inv := halfPlaneFrameUnitTangent_frame
  continuous_toFun := continuous_halfPlaneFrameUnitTangent
  continuous_invFun := continuous_halfPlaneUnitTangentFrame

@[simp] theorem halfPlaneUnitTangentHomeomorph_proj (q : HalfPlaneTangentFrame) :
    (halfPlaneUnitTangentHomeomorph q).val.proj = q.point := rfl

/-- **Math.** Actual unit-frame transport is the full physical Möbius
derivative, including its height factor, not merely a phase equality. -/
theorem halfPlaneUnitTangentHomeomorph_smul_vector (A : SL(2, ℝ))
    (q : HalfPlaneTangentFrame) :
    (halfPlaneUnitTangentHomeomorph (A • q)).val.snd =
      fderiv ℝ (gluingDeckComplex A) (q.point : ℂ)
        (halfPlaneUnitTangentHomeomorph q).val.snd := by
  change (A • q.point : ℍ).im •
    ((halfPlaneSpinCircle A q.point ^ 2 * q.phase : Circle) : ℂ) =
      fderiv ℝ (gluingDeckComplex A) (q.point : ℂ)
        (q.point.im • (q.phase : ℂ))
  simp only [Circle.coe_mul, Circle.coe_pow, Complex.real_smul]
  exact (gluingDeckComplex_fderiv_unit_vector A q.point (q.phase : ℂ)).symm

#print axioms halfPlaneUnitTangentHomeomorph
#print axioms halfPlaneUnitTangentHomeomorph_smul_vector

end SystolicGrowth
