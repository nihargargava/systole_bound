module

public import Geometry.DiscProjectiveHolonomy
public import Geometry.HalfPlaneUnitTangentFrame

@[expose] public section

/-!
# Actual projective tangent action on the half-plane

The true special-linear tangent action is trivial on its genuine center,
so it descends coherently to PSL₂. Its action retains the literal base map
and full physical Möbius derivative on the actual Poincaré unit tangent
bundle, independently of a choice of special-linear representative.
-/

open UpperHalfPlane Topology Set Filter
open scoped MatrixGroups UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SystolicGrowth

/-- **Math.** Every element of the actual SL₂ center fixes every genuine
oriented tangent frame. Both `I` and `-I` act trivially on tangent phases. -/
theorem halfPlaneTangentFrame_smul_eq_self_of_mem_center
    (A : SL(2, ℝ)) (hA : A ∈ Subgroup.center SL(2, ℝ))
    (q : HalfPlaneTangentFrame) : A • q = q := by
  have hpoint := (sl2_smul_eq_self_iff_mem_center A).mpr hA
  rcases (Vendored.RiemannDynamics.smul_id_iff_pm_one A).mp hpoint with h | h
  · have hAone : A = 1 := Subtype.ext (by simpa using h)
    rw [hAone, one_smul]
  · have hAneg : A = (-1 : SL(2, ℝ)) := Subtype.ext (by simpa using h)
    rw [hAneg]
    exact halfPlaneTangentFrame_neg_one_smul q

/-- **Math.** The actual tangent action descends as a genuine permutation
homomorphism, not a collection of independently selected SL₂ actions. -/
def projectiveHalfPlaneTangentPermHom : PSL(2, ℝ) →* Equiv.Perm HalfPlaneTangentFrame :=
  QuotientGroup.lift (Subgroup.center SL(2, ℝ))
    (MulAction.toPermHom SL(2, ℝ) HalfPlaneTangentFrame)
    (fun A hA => Equiv.ext (halfPlaneTangentFrame_smul_eq_self_of_mem_center A hA))

instance projectiveHalfPlaneTangentMulAction : MulAction PSL(2, ℝ) HalfPlaneTangentFrame :=
  MulAction.compHom HalfPlaneTangentFrame projectiveHalfPlaneTangentPermHom

@[simp]
theorem projective_mk_halfPlaneTangentFrame_smul (A : SL(2, ℝ))
    (q : HalfPlaneTangentFrame) :
    (QuotientGroup.mk' (Subgroup.center SL(2, ℝ)) A : PSL(2, ℝ)) • q = A • q := rfl

/-- **Math.** The descended tangent action has exactly the already
constructed projective base action, at every actual frame. -/
@[simp]
theorem projective_halfPlaneTangentFrame_smul_point (γ : PSL(2, ℝ))
    (q : HalfPlaneTangentFrame) : (γ • q).point = γ • q.point := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(2, ℝ)) γ
  rfl

instance projectiveHalfPlaneTangentContinuousConstSMul :
    ContinuousConstSMul PSL(2, ℝ) HalfPlaneTangentFrame where
  continuous_const_smul γ := by
    obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(2, ℝ)) γ
    change Continuous (fun q : HalfPlaneTangentFrame => A • q)
    exact continuous_const_smul A

instance projectiveHalfPlaneTangentFaithfulSMul : FaithfulSMul PSL(2, ℝ) HalfPlaneTangentFrame where
  eq_of_smul_eq_smul := by
    intro γ δ h
    apply eq_of_smul_eq_smul (α := ℍ)
    intro z
    have hp := congrArg HalfPlaneTangentFrame.point (h (⟨z, 1⟩ : HalfPlaneTangentFrame))
    simpa only [projective_halfPlaneTangentFrame_smul_point] using hp

/-- **Math.** The actual projective half-plane base map, totalized in the
standard complex coordinates. At every genuine half-plane point this is
the original Möbius map, and derivatives use that genuine local branch. -/
def projectiveHalfPlaneComplex (γ : PSL(2, ℝ)) (w : ℂ) : ℂ :=
  ((γ • UpperHalfPlane.ofComplex w : ℍ) : ℂ)

/-- **Math.** A representative's rational Möbius expression agrees locally
with the actual projective complex map near every half-plane point. -/
theorem projectiveHalfPlaneComplex_mk_eventuallyEq (A : SL(2, ℝ)) (z : ℍ) :
    projectiveHalfPlaneComplex (QuotientGroup.mk' (Subgroup.center SL(2, ℝ)) A) =ᶠ[𝓝 (z : ℂ)]
      gluingDeckComplex A := by
  have hU : {w : ℂ | 0 < w.im} ∈ 𝓝 (z : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds z.im_pos
  filter_upwards [hU] with w hw
  change ((A • UpperHalfPlane.ofComplex w : ℍ) : ℂ) = gluingDeckComplex A w
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  exact (gluingDeckComplex_coe A (⟨w, hw⟩ : ℍ)).symm

/-- **Math.** The derivative of the actual projective map equals the full
real Möbius derivative of any special-linear representative. This equality
is local at the genuine half-plane point, not an equality of fallback maps. -/
theorem projectiveHalfPlaneComplex_mk_fderiv (A : SL(2, ℝ)) (z : ℍ) :
    fderiv ℝ (projectiveHalfPlaneComplex
      (QuotientGroup.mk' (Subgroup.center SL(2, ℝ)) A)) (z : ℂ) =
        fderiv ℝ (gluingDeckComplex A) (z : ℂ) :=
  (projectiveHalfPlaneComplex_mk_eventuallyEq A z).fderiv_eq

/-- **Math.** The actual projective frame action pushes genuine Poincaré
unit vectors by the full physical real differential of its own base map.
The result is independent of every SL₂ representative choice. -/
theorem projective_halfPlaneUnitTangentHomeomorph_smul_vector
    (γ : PSL(2, ℝ)) (q : HalfPlaneTangentFrame) :
    (halfPlaneUnitTangentHomeomorph (γ • q)).val.snd =
      fderiv ℝ (projectiveHalfPlaneComplex γ) (q.point : ℂ)
        (halfPlaneUnitTangentHomeomorph q).val.snd := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(2, ℝ)) γ
  rw [projective_mk_halfPlaneTangentFrame_smul, projectiveHalfPlaneComplex_mk_fderiv]
  exact halfPlaneUnitTangentHomeomorph_smul_vector A q

/-- **Math.** Equal projective representatives give literally the same
full real tangent differential at every actual half-plane point. -/
theorem gluingDeckComplex_fderiv_eq_of_projective_eq
    (A B : SL(2, ℝ))
    (hAB : QuotientGroup.mk' (Subgroup.center SL(2, ℝ)) A =
      QuotientGroup.mk' (Subgroup.center SL(2, ℝ)) B) (z : ℍ) :
    fderiv ℝ (gluingDeckComplex A) (z : ℂ) = fderiv ℝ (gluingDeckComplex B) (z : ℂ) := by
  rw [← projectiveHalfPlaneComplex_mk_fderiv A z,
    ← projectiveHalfPlaneComplex_mk_fderiv B z, hAB]

#print axioms projectiveHalfPlaneTangentPermHom
#print axioms projective_halfPlaneTangentFrame_smul_point
#print axioms projectiveHalfPlaneTangentContinuousConstSMul
#print axioms projective_halfPlaneUnitTangentHomeomorph_smul_vector
#print axioms gluingDeckComplex_fderiv_eq_of_projective_eq

end SystolicGrowth
