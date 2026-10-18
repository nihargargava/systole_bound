module

public import Vendored.RiemannDynamics.Uniformization.DiscAutomorphisms
public import Vendored.RiemannDynamics.Teichmuller.PolygonGeometry
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.Algebra.Group.Action.End

@[expose] public section

/-!
# Coherent projective realization of analytic disc actions

The fixed Cayley equivalence transports analytic automorphisms of the native
open disc to the native upper half-plane. The imported classification supplies
SL₂ representatives. Their ambiguity is exactly the center, so their PSL₂
classes compose without making a coherent choice of SL₂ lifts.

This is a generic adapter for an actual analytic disc action. It does not
identify a surface's metric universal cover or solve the SL₂ lift obstruction.
-/

open scoped MatrixGroups UpperHalfPlane Manifold ContDiff

namespace SystolicGrowth

open Vendored.RiemannDynamics

/-- The native open unit disc, with its existing analytic manifold structure. -/
abbrev AnalyticUnitDisc := ↥unitDiscOpens

/-- Analytic diffeomorphisms of the native open unit disc. -/
abbrev AnalyticDiscAutomorphism :=
  AnalyticUnitDisc ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ AnalyticUnitDisc

/-- The fixed Cayley equivalence; neither carrier nor its topology is replaced. -/
noncomputable def discCayleyEquiv : AnalyticUnitDisc ≃ ℍ where
  toFun z := diskToHalfPlane z.property
  invFun τ := ⟨halfPlaneToCayley τ, halfPlaneToCayley_mem_ball τ.im_pos⟩
  left_inv z := Subtype.ext (halfPlaneToCayley_cayleyToHalfPlane z.property)
  right_inv τ := UpperHalfPlane.ext (cayleyToHalfPlane_halfPlaneToCayley τ.im_pos)

@[simp]
theorem discCayleyEquiv_coe (z : AnalyticUnitDisc) :
    (discCayleyEquiv z : ℂ) = cayleyToHalfPlane (z : ℂ) := rfl

/-- The fixed Cayley equivalence preserves the actual topologies, so compact
native disc sets can be transported to the final upper-half-plane carrier. -/
noncomputable def discCayleyHomeomorph : AnalyticUnitDisc ≃ₜ ℍ where
  toEquiv := discCayleyEquiv
  continuous_toFun := by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    change Continuous (fun z : AnalyticUnitDisc =>
      Complex.I * (1 + (z : ℂ)) / (1 - (z : ℂ)))
    exact (continuous_const.mul (continuous_const.add continuous_subtype_val)).div
      (continuous_const.sub continuous_subtype_val)
      (fun z => one_sub_ne_zero_of_mem_ball z.property)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (UpperHalfPlane.continuous_coe.sub continuous_const).div
      (UpperHalfPlane.continuous_coe.add continuous_const)
      (fun τ => add_I_ne_zero_of_im_pos τ.im_pos)

/-- Compactness is transported by this exact Cayley map, not by an unrelated
abstract disc/half-plane equivalence. -/
theorem isCompact_discCayley_image {K : Set AnalyticUnitDisc} (hK : IsCompact K) :
    IsCompact (discCayleyEquiv '' K) :=
  hK.image discCayleyHomeomorph.continuous

/-- The SL₂ action kernel is its actual center, consisting of the two scalars ±I. -/
theorem sl2_smul_eq_self_iff_mem_center (A : SL(2, ℝ)) :
    (∀ τ : ℍ, A • τ = τ) ↔ A ∈ Subgroup.center SL(2, ℝ) := by
  rw [smul_id_iff_pm_one, Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro (hA | hA)
    · exact ⟨1, by simp, by simpa using hA.symm⟩
    · exact ⟨-1, by simp, by simpa [← Matrix.diagonal_neg] using hA.symm⟩
  · rintro ⟨r, hr, hA⟩
    have hr2 : r ^ 2 = 1 := by simpa using hr
    rcases sq_eq_one_iff.mp hr2 with hr | hr
    · left
      simpa [hr] using hA.symm
    · right
      simpa [hr, ← Matrix.diagonal_neg] using hA.symm

/-- The native Möbius action descends to PSL₂, not to the full SL₂ preimage
of a surface group. -/
noncomputable def projectiveHalfPlanePermHom : PSL(2, ℝ) →* Equiv.Perm ℍ :=
  QuotientGroup.lift (Subgroup.center SL(2, ℝ)) (MulAction.toPermHom SL(2, ℝ) ℍ)
    (fun A hA => Equiv.ext ((sl2_smul_eq_self_iff_mem_center A).mpr hA))

noncomputable instance projectiveHalfPlaneMulAction : MulAction PSL(2, ℝ) ℍ :=
  MulAction.compHom ℍ projectiveHalfPlanePermHom

@[simp]
theorem projective_mk_smul (A : SL(2, ℝ)) (τ : ℍ) :
    (QuotientGroup.mk' (Subgroup.center SL(2, ℝ)) A : PSL(2, ℝ)) • τ = A • τ := rfl

/-- Two SL₂ representatives define the same PSL₂ element precisely when
their actual upper-half-plane actions agree. -/
theorem sl2_projective_eq_iff (A B : SL(2, ℝ)) :
    QuotientGroup.mk' (Subgroup.center SL(2, ℝ)) A =
      QuotientGroup.mk' (Subgroup.center SL(2, ℝ)) B ↔
        ∀ τ : ℍ, A • τ = B • τ := by
  constructor
  · intro h τ
    exact congrArg (fun γ : PSL(2, ℝ) => γ • τ) h
  · intro h
    apply QuotientGroup.eq.mpr
    apply (sl2_smul_eq_self_iff_mem_center (A⁻¹ * B)).mp
    intro τ
    rw [mul_smul, ← h τ, inv_smul_smul]

instance projectiveHalfPlaneFaithfulSMul : FaithfulSMul PSL(2, ℝ) ℍ where
  eq_of_smul_eq_smul := by
    intro a b h
    obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(2, ℝ)) a
    obtain ⟨B, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(2, ℝ)) b
    exact (sl2_projective_eq_iff A B).mpr h

theorem Internal.DiscProjectiveHolonomyHelpers.exists_sl2_discCayley (e : AnalyticDiscAutomorphism) :
    ∃ A : SL(2, ℝ), ∀ z : AnalyticUnitDisc,
      A • discCayleyEquiv z = discCayleyEquiv (e z) := by
  obtain ⟨A, hA⟩ := exists_sl2_of_diffeomorph_unitDisc e
  refine ⟨A, fun z => ?_⟩
  obtain ⟨τ, τ', hτ, hτ', h⟩ := hA z
  have hτC : τ = discCayleyEquiv z := UpperHalfPlane.ext hτ
  have hτ'C : τ' = discCayleyEquiv (e z) := UpperHalfPlane.ext hτ'
  simpa only [hτC, hτ'C] using h

/-- The canonical projective class of an analytic disc automorphism. Only the
representative is chosen; its projective class is determined by its action. -/
noncomputable def discProjective (e : AnalyticDiscAutomorphism) : PSL(2, ℝ) :=
  QuotientGroup.mk' (Subgroup.center SL(2, ℝ))
    (Classical.choose (Internal.DiscProjectiveHolonomyHelpers.exists_sl2_discCayley e))

@[simp]
theorem discProjective_smul_cayley (e : AnalyticDiscAutomorphism)
    (z : AnalyticUnitDisc) :
    discProjective e • discCayleyEquiv z = discCayleyEquiv (e z) :=
  Classical.choose_spec (Internal.DiscProjectiveHolonomyHelpers.exists_sl2_discCayley e) z

/-- The projective realization is characterized by the exact fixed Cayley action. -/
theorem discProjective_eq_iff (e : AnalyticDiscAutomorphism) (γ : PSL(2, ℝ)) :
    discProjective e = γ ↔
      ∀ z : AnalyticUnitDisc, γ • discCayleyEquiv z = discCayleyEquiv (e z) := by
  constructor
  · rintro rfl
    exact discProjective_smul_cayley e
  · intro h
    apply eq_of_smul_eq_smul (α := ℍ)
    intro τ
    obtain ⟨z, rfl⟩ := discCayleyEquiv.surjective τ
    exact (discProjective_smul_cayley e z).trans (h z).symm

@[simp]
theorem discProjective_refl :
    discProjective (Diffeomorph.refl 𝓘(ℂ) AnalyticUnitDisc ω) = 1 := by
  apply (discProjective_eq_iff _ _).mpr
  intro z
  exact one_smul _ _

/-- `trans` applies the first diffeomorphism before the second, so the order
agrees with ordinary left group actions. -/
@[simp]
theorem discProjective_trans (e f : AnalyticDiscAutomorphism) :
    discProjective (e.trans f) = discProjective f * discProjective e := by
  apply (discProjective_eq_iff _ _).mpr
  intro z
  rw [mul_smul, discProjective_smul_cayley, discProjective_smul_cayley]
  rfl

theorem discProjective_injective : Function.Injective discProjective := by
  intro e f h
  apply Diffeomorph.ext
  intro z
  apply discCayleyEquiv.injective
  rw [← discProjective_smul_cayley, ← discProjective_smul_cayley, h]

/-- An actual group action by analytic disc diffeomorphisms has coherent
projective holonomy. The hypotheses are just the identity and composition
laws of that action, not assumptions about its projective realization. -/
noncomputable def discActionProjectiveHom {G : Type*} [Group G]
    (e : G → AnalyticDiscAutomorphism)
    (h_one : ∀ z, e 1 z = z)
    (h_mul : ∀ a b z, e (a * b) z = e a (e b z)) : G →* PSL(2, ℝ) where
  toFun a := discProjective (e a)
  map_one' := by
    apply (discProjective_eq_iff _ _).mpr
    intro z
    rw [h_one, one_smul]
  map_mul' a b := by
    apply (discProjective_eq_iff _ _).mpr
    intro z
    rw [mul_smul, discProjective_smul_cayley, discProjective_smul_cayley, h_mul]

@[simp]
theorem discActionProjectiveHom_smul_cayley {G : Type*} [Group G]
    (e : G → AnalyticDiscAutomorphism)
    (h_one : ∀ z, e 1 z = z)
    (h_mul : ∀ a b z, e (a * b) z = e a (e b z))
    (a : G) (z : AnalyticUnitDisc) :
    discActionProjectiveHom e h_one h_mul a • discCayleyEquiv z =
      discCayleyEquiv (e a z) := discProjective_smul_cayley (e a) z

/-- The projective homomorphism acts on every native upper-half-plane point
by the Cayley conjugate of the given analytic action. -/
theorem discActionProjectiveHom_smul {G : Type*} [Group G]
    (e : G → AnalyticDiscAutomorphism)
    (h_one : ∀ z, e 1 z = z)
    (h_mul : ∀ a b z, e (a * b) z = e a (e b z))
    (a : G) (τ : ℍ) :
    discActionProjectiveHom e h_one h_mul a • τ =
      discCayleyEquiv (e a (discCayleyEquiv.symm τ)) := by
  simpa only [Equiv.apply_symm_apply] using
    discActionProjectiveHom_smul_cayley e h_one h_mul a (discCayleyEquiv.symm τ)

/-- Faithfulness of the original analytic action is preserved by the
projective adapter. -/
theorem discActionProjectiveHom_injective {G : Type*} [Group G]
    (e : G → AnalyticDiscAutomorphism)
    (h_one : ∀ z, e 1 z = z)
    (h_mul : ∀ a b z, e (a * b) z = e a (e b z))
    (he : Function.Injective e) :
    Function.Injective (discActionProjectiveHom e h_one h_mul) := by
  intro a b h
  exact he (discProjective_injective h)

/-- A coherent special-linear lift acts by the same fixed Cayley conjugacy.
The lift is an input to this transport lemma, not a claimed construction of
the still-missing geometric lift. -/
theorem discActionSpecialLinearLift_smul_cayley {G : Type*} [Group G]
    (e : G → AnalyticDiscAutomorphism)
    (h_one : ∀ z, e 1 z = z)
    (h_mul : ∀ a b z, e (a * b) z = e a (e b z))
    (ρ : G →* SL(2, ℝ))
    (hρ : (QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp ρ =
      discActionProjectiveHom e h_one h_mul)
    (a : G) (z : AnalyticUnitDisc) :
    ρ a • discCayleyEquiv z = discCayleyEquiv (e a z) := by
  have haction := congrArg (fun γ : PSL(2, ℝ) => γ • discCayleyEquiv z)
    (DFunLike.congr_fun hρ a)
  change ρ a • discCayleyEquiv z =
    discActionProjectiveHom e h_one h_mul a • discCayleyEquiv z at haction
  exact haction.trans (discActionProjectiveHom_smul_cayley e h_one h_mul a z)

/-- A compact orbit-cover for the actual analytic disc action transports to
the image of its coherent lift, not the full projective inverse image. This
preserves the exact all-points/existential-image-element output contract. -/
theorem discActionSpecialLinearLift_compact_orbit_cover {G : Type*} [Group G]
    (e : G → AnalyticDiscAutomorphism)
    (h_one : ∀ z, e 1 z = z)
    (h_mul : ∀ a b z, e (a * b) z = e a (e b z))
    (ρ : G →* SL(2, ℝ))
    (hρ : (QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp ρ =
      discActionProjectiveHom e h_one h_mul)
    (K : Set AnalyticUnitDisc) (hK : IsCompact K)
    (hcover : ∀ z : AnalyticUnitDisc, ∃ a : G, e a z ∈ K) :
    ∃ K' : Set ℍ, IsCompact K' ∧
      ∀ τ : ℍ, ∃ γ : ρ.range, γ • τ ∈ K' := by
  refine ⟨discCayleyEquiv '' K, isCompact_discCayley_image hK, ?_⟩
  intro τ
  obtain ⟨a, ha⟩ := hcover (discCayleyEquiv.symm τ)
  refine ⟨⟨ρ a, ⟨a, rfl⟩⟩, e a (discCayleyEquiv.symm τ), ha, ?_⟩
  change discCayleyEquiv (e a (discCayleyEquiv.symm τ)) = ρ a • τ
  simpa only [Equiv.apply_symm_apply] using
    (discActionSpecialLinearLift_smul_cayley e h_one h_mul ρ hρ a
      (discCayleyEquiv.symm τ)).symm

#print axioms discCayleyHomeomorph
#print axioms isCompact_discCayley_image
#print axioms discActionSpecialLinearLift_smul_cayley
#print axioms discActionSpecialLinearLift_compact_orbit_cover

end SystolicGrowth
