module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.HalfPlaneSpinAction
public import Geometry.DiscProjectiveHolonomy
public import Mathlib.Topology.Maps.Proper.Basic

@[expose] public section

/-!
# Genuine half-plane spin lifts

The actual spin action is faithful, unlike its projective tangent action.
Every continuous lift of a prescribed matrix's tangent action is exactly
one of its two signed spin actions. This is the local classification needed
to recover special-linear holonomy from an actual transported spin cover;
no global surface spin identification is assumed to have been constructed.
-/

open UpperHalfPlane Topology
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace SystolicGrowth

set_option backward.isDefEq.respectTransparency false

instance halfPlaneSpinFrameConnectedSpace : ConnectedSpace HalfPlaneSpinFrame :=
  halfPlaneSpinFrameHomeomorph.symm.surjective.connectedSpace
    halfPlaneSpinFrameHomeomorph.symm.continuous

/-- **Math.** The canonical genuine spin square is proper: its circle
factor is compact, and the half-plane base is unchanged. -/
theorem halfPlaneSpinSquare_isProperMap : IsProperMap halfPlaneSpinSquare := by
  have hs : IsProperMap (fun u : Circle => u ^ 2) := (continuous_id.pow 2).isProperMap
  have hp := (isProperMap_id (X := ℍ)).prodMap hs
  exact halfPlaneTangentFrameHomeomorph.symm.isProperMap.comp
    (hp.comp halfPlaneSpinFrameHomeomorph.isProperMap)

/-- **Math.** The actual canonical square has genuine evenly covered
neighborhoods on the entire half-plane tangent-frame carrier. -/
theorem halfPlaneSpinSquare_isCoveringMap : IsCoveringMap halfPlaneSpinSquare := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  apply halfPlaneSpinSquare_isProperMap.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
  · intro r _
    obtain ⟨q, rfl⟩ := halfPlaneSpinSquare_surjective r
    have h : halfPlaneSpinSquare ⁻¹' {halfPlaneSpinSquare q} =
        {q, halfPlaneSpinAntipode q} := by
      ext s
      exact halfPlaneSpinSquare_eq_iff s q
    rw [h]
    exact (Set.finite_singleton _).insert _
  · simpa only [Set.preimage_univ] using
      halfPlaneSpinSquare_isLocalHomeomorph.isLocalHomeomorphOn (s := Set.univ)

/-- **Math.** A matrix fixing every genuine spin frame is the identity:
the only possible projective kernel element `-I` is excluded by antipodes. -/
theorem halfPlaneSpinFrame_eq_one_of_forall_smul_eq_self
    (A : SL(2, ℝ)) (hA : ∀ q : HalfPlaneSpinFrame, A • q = q) : A = 1 := by
  have hpoint : ∀ z : ℍ, A • z = z := fun z =>
    congrArg HalfPlaneSpinFrame.point (hA ⟨z, 1⟩)
  rcases (Vendored.RiemannDynamics.smul_id_iff_pm_one A).mp hpoint with h | h
  · exact Subtype.ext (by simpa using h)
  · have hneg : A = (-1 : SL(2, ℝ)) := Subtype.ext (by simpa using h)
    have hframe := hA (⟨UpperHalfPlane.I, 1⟩ : HalfPlaneSpinFrame)
    rw [hneg, halfPlaneSpinFrame_neg_one_smul] at hframe
    exact False.elim (halfPlaneSpinAntipode_ne _ hframe)

instance halfPlaneSpinFrameFaithfulSMul : FaithfulSMul SL(2, ℝ) HalfPlaneSpinFrame := by
  rw [faithfulSMul_iff]
  exact halfPlaneSpinFrame_eq_one_of_forall_smul_eq_self

/-- **Math.** Two continuous lifts through actual spin squaring agree
globally if they agree at one frame; the domain is genuinely connected. -/
theorem halfPlaneSpinLift_eq_of_comp_eq
    {f g : HalfPlaneSpinFrame → HalfPlaneSpinFrame}
    (hf : Continuous f) (hg : Continuous g)
    (hsquare : halfPlaneSpinSquare ∘ f = halfPlaneSpinSquare ∘ g)
    (q : HalfPlaneSpinFrame) (hq : f q = g q) : f = g :=
  (T2Space.isSeparatedMap halfPlaneSpinSquare).eq_of_comp_eq
    halfPlaneSpinSquare_isLocalHomeomorph.isLocallyInjective hf hg hsquare q hq

/-- **Math.** The central matrix changes the actual spin lift by its
nontrivial antipode, while retaining the same actual tangent action. -/
theorem halfPlaneSpinFrame_neg_smul (A : SL(2, ℝ)) (q : HalfPlaneSpinFrame) :
    (-A) • q = halfPlaneSpinAntipode (A • q) := by
  rw [show -A = (-1 : SL(2, ℝ)) * A by simp, mul_smul,
    halfPlaneSpinFrame_neg_one_smul]

/-- **Math.** Any continuous spin lift of the genuine tangent action of
`A` is globally the spin action of `A` or `-A`; the sign is not postulated. -/
theorem halfPlaneSpinLift_eq_signed_smul
    (A : SL(2, ℝ)) (f : HalfPlaneSpinFrame → HalfPlaneSpinFrame)
    (hf : Continuous f)
    (hsquare : ∀ q, halfPlaneSpinSquare (f q) = A • halfPlaneSpinSquare q) :
    f = (fun q => A • q) ∨ f = (fun q => (-A) • q) := by
  let q₀ : HalfPlaneSpinFrame := ⟨UpperHalfPlane.I, 1⟩
  have hq₀ : halfPlaneSpinSquare (f q₀) = halfPlaneSpinSquare (A • q₀) := by
    rw [halfPlaneSpinSquare_smul, hsquare]
  rcases (halfPlaneSpinSquare_eq_iff _ _).mp hq₀ with h | h
  · left
    apply halfPlaneSpinLift_eq_of_comp_eq hf (continuous_const_smul A) _ q₀ h
    funext q
    exact (hsquare q).trans (halfPlaneSpinSquare_smul A q).symm
  · right
    have hnegative : f q₀ = (-A) • q₀ := by
      rw [halfPlaneSpinFrame_neg_smul]
      exact h
    apply halfPlaneSpinLift_eq_of_comp_eq hf (continuous_const_smul (-A)) _ q₀ hnegative
    funext q
    rw [Function.comp_apply, Function.comp_apply, halfPlaneSpinFrame_neg_smul]
    have hantip : halfPlaneSpinSquare (halfPlaneSpinAntipode (A • q)) =
        halfPlaneSpinSquare (A • q) :=
      (halfPlaneSpinSquare_eq_iff _ _).mpr (Or.inr rfl)
    exact (hsquare q).trans ((halfPlaneSpinSquare_smul A q).symm.trans hantip.symm)

/-- **Math.** A genuine continuous spin lift determines one and only one
special-linear matrix, with the prescribed projective class. -/
theorem existsUnique_sl2_halfPlaneSpinLift
    (A : SL(2, ℝ)) (f : HalfPlaneSpinFrame → HalfPlaneSpinFrame)
    (hf : Continuous f)
    (hsquare : ∀ q, halfPlaneSpinSquare (f q) = A • halfPlaneSpinSquare q) :
    ∃! B : SL(2, ℝ), (∀ q : HalfPlaneSpinFrame, B • q = f q) ∧
      QuotientGroup.mk' (Subgroup.center SL(2, ℝ)) B =
        QuotientGroup.mk' (Subgroup.center SL(2, ℝ)) A := by
  have hmatrix : ∃ B : SL(2, ℝ), ∀ q : HalfPlaneSpinFrame, B • q = f q := by
    rcases halfPlaneSpinLift_eq_signed_smul A f hf hsquare with h | h
    · exact ⟨A, fun q => (congrFun h q).symm⟩
    · exact ⟨-A, fun q => (congrFun h q).symm⟩
  obtain ⟨B, hB⟩ := hmatrix
  have hprojective : QuotientGroup.mk' (Subgroup.center SL(2, ℝ)) B =
      QuotientGroup.mk' (Subgroup.center SL(2, ℝ)) A := by
    apply (sl2_projective_eq_iff B A).mpr
    intro z
    have h := hsquare (⟨z, 1⟩ : HalfPlaneSpinFrame)
    rw [← hB, halfPlaneSpinSquare_smul] at h
    exact congrArg HalfPlaneTangentFrame.point h
  refine ⟨B, ⟨hB, hprojective⟩, ?_⟩
  intro D hD
  apply eq_of_smul_eq_smul (α := HalfPlaneSpinFrame)
  intro q
  exact (hD.1 q).trans (hB q).symm

/-- **Math.** A genuine action by continuous lifts of actual projective
tangent maps automatically recovers a coherent special-linear homomorphism.
Matrix coherence is proved from the given geometric action, not assumed.
The construction of that geometric spin action is a separate obligation. -/
theorem exists_sl2_hom_of_continuous_halfPlaneSpinAction
    {G : Type*} [Group G] (A : G → SL(2, ℝ))
    (f : G → HalfPlaneSpinFrame → HalfPlaneSpinFrame)
    (hf : ∀ a, Continuous (f a))
    (hsquare : ∀ a q, halfPlaneSpinSquare (f a q) = A a • halfPlaneSpinSquare q)
    (hone : ∀ q, f 1 q = q)
    (hmul : ∀ a b q, f (a * b) q = f a (f b q)) :
    ∃ ρ : G →* SL(2, ℝ), (∀ a q, ρ a • q = f a q) ∧
      ∀ a, QuotientGroup.mk' (Subgroup.center SL(2, ℝ)) (ρ a) =
        QuotientGroup.mk' (Subgroup.center SL(2, ℝ)) (A a) := by
  classical
  have h : ∀ a, ∃ B : SL(2, ℝ), (∀ q : HalfPlaneSpinFrame, B • q = f a q) ∧
      QuotientGroup.mk' (Subgroup.center SL(2, ℝ)) B =
        QuotientGroup.mk' (Subgroup.center SL(2, ℝ)) (A a) :=
    fun a => (existsUnique_sl2_halfPlaneSpinLift (A a) (f a) (hf a) (hsquare a)).exists
  choose B hB hprojective using h
  let ρ : G →* SL(2, ℝ) :=
    { toFun := B
      map_one' := by
        apply eq_of_smul_eq_smul (α := HalfPlaneSpinFrame)
        intro q
        rw [hB, hone, one_smul]
      map_mul' a b := by
        apply eq_of_smul_eq_smul (α := HalfPlaneSpinFrame)
        intro q
        rw [mul_smul, hB, hB, hB, hmul] }
  exact ⟨ρ, hB, hprojective⟩

#print axioms halfPlaneSpinFrame_eq_one_of_forall_smul_eq_self
#print axioms halfPlaneSpinSquare_isCoveringMap
#print axioms halfPlaneSpinLift_eq_of_comp_eq
#print axioms halfPlaneSpinLift_eq_signed_smul
#print axioms existsUnique_sl2_halfPlaneSpinLift
#print axioms exists_sl2_hom_of_continuous_halfPlaneSpinAction

end SystolicGrowth
