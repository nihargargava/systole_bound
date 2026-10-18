module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Core.SystolicCore
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.Algebra.Ring.Commute

@[expose] public section

/-!
# The actual surface relator and projective lifting

Chosen special-linear lifts of the actual presented-group generators descend
to one coherent representation exactly when the original ordered product of
handle commutators is the identity. The product is independent of all choices
of lifts, and lies in the center. This is an algebraic obstruction criterion;
no Euler-parity vanishing or geometric holonomy is asserted.
-/

open scoped MatrixGroups commutatorElement

namespace SystolicGrowth

/-- Evaluation of the actual ordered surface word is the ordered product
of the corresponding handle commutators. -/
theorem lift_surfaceRelator_eq_prod_commutators
    {H : Type*} [Group H] {g : ℕ} (A : SurfaceGenerator g → H) :
    FreeGroup.lift A (surfaceRelator g) =
      (List.ofFn fun i : Fin g => ⁅A (i, false), A (i, true)⁆).prod := by
  simp only [surfaceRelator, map_list_prod, List.map_ofFn,
    Function.comp_def, map_commutatorElement, FreeGroup.lift_apply_of]

private theorem commutatorElement_mul_center
    {H : Type*} [Group H] (a b c d : H)
    (hc : c ∈ Subgroup.center H) (hd : d ∈ Subgroup.center H) :
    ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  have hcb : ⁅c, b * d⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.mpr
      ((Subgroup.mem_center_iff.mp hc (b * d)).symm)
  have had : ⁅a, d⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.mpr (Subgroup.mem_center_iff.mp hd a)
  rw [commutatorElement_mul_left_eq_conj_mul, hcb]
  simp only [mul_one, mul_inv_cancel, one_mul]
  rw [commutatorElement_mul_right_eq_mul_conj, had]
  simp

private theorem commutatorElement_eq_of_center_quotient_eq
    {H : Type*} [Group H] {a b a' b' : H}
    (ha : QuotientGroup.mk' (Subgroup.center H) a =
      QuotientGroup.mk' (Subgroup.center H) a')
    (hb : QuotientGroup.mk' (Subgroup.center H) b =
      QuotientGroup.mk' (Subgroup.center H) b') :
    ⁅a, b⁆ = ⁅a', b'⁆ := by
  obtain ⟨c, hc, hac⟩ := (QuotientGroup.mk'_eq_mk' (N := Subgroup.center H)).mp ha
  obtain ⟨d, hd, hbd⟩ := (QuotientGroup.mk'_eq_mk' (N := Subgroup.center H)).mp hb
  rw [← hac, ← hbd]
  exact (commutatorElement_mul_center a b c d hc hd).symm

/-- The lift of the actual surface word does not change when any generator
lift is changed by an element of the center. -/
theorem lift_surfaceRelator_eq_of_projective_generators
    {R : Type*} [CommRing R] {g : ℕ}
    (A B : SurfaceGenerator g → SL(2, R))
    (hAB : ∀ s, QuotientGroup.mk' (Subgroup.center SL(2, R)) (A s) =
      QuotientGroup.mk' (Subgroup.center SL(2, R)) (B s)) :
    FreeGroup.lift A (surfaceRelator g) = FreeGroup.lift B (surfaceRelator g) := by
  rw [lift_surfaceRelator_eq_prod_commutators, lift_surfaceRelator_eq_prod_commutators]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  exact commutatorElement_eq_of_center_quotient_eq (hAB (i, false)) (hAB (i, true))

/-- Chosen lifts killing the original surface relator give one coherent
special-linear representation, with the exact chosen generators and original
projective representation. -/
theorem exists_surfaceGroup_lift_of_relator
    {R : Type*} [CommRing R] {g : ℕ}
    (ρbar : SurfaceGroup g →* PSL(2, R)) (A : SurfaceGenerator g → SL(2, R))
    (hA : ∀ s, QuotientGroup.mk' (Subgroup.center SL(2, R)) (A s) =
      ρbar (PresentedGroup.of s))
    (hrel : FreeGroup.lift A (surfaceRelator g) = 1) :
    ∃ ρ : SurfaceGroup g →* SL(2, R),
      (∀ s, ρ (PresentedGroup.of s) = A s) ∧
        (QuotientGroup.mk' (Subgroup.center SL(2, R))).comp ρ = ρbar := by
  have hrels : ∀ r ∈ ({surfaceRelator g} : Set (FreeGroup (SurfaceGenerator g))),
      FreeGroup.lift A r = 1 := by
    intro r hr
    rwa [Set.mem_singleton_iff.mp hr]
  let ρ : SurfaceGroup g →* SL(2, R) := PresentedGroup.toGroup hrels
  have hgen : ∀ s, ρ (PresentedGroup.of s) = A s :=
    fun _ => PresentedGroup.toGroup.of hrels
  refine ⟨ρ, hgen, ?_⟩
  apply PresentedGroup.ext
  intro s
  rw [MonoidHom.comp_apply, hgen]
  exact hA s

/-- A projective representation sends the actual surface word to the identity;
therefore its special-linear lifted word lies in the center. -/
theorem lift_surfaceRelator_mem_center
    {R : Type*} [CommRing R] {g : ℕ}
    (ρbar : SurfaceGroup g →* PSL(2, R)) (A : SurfaceGenerator g → SL(2, R))
    (hA : ∀ s, QuotientGroup.mk' (Subgroup.center SL(2, R)) (A s) =
      ρbar (PresentedGroup.of s)) :
    FreeGroup.lift A (surfaceRelator g) ∈ Subgroup.center SL(2, R) := by
  have hfree : (QuotientGroup.mk' (Subgroup.center SL(2, R))).comp (FreeGroup.lift A) =
      ρbar.comp (PresentedGroup.mk ({surfaceRelator g} : Set _)) := by
    apply FreeGroup.ext_hom
    intro s
    simpa only [MonoidHom.comp_apply, FreeGroup.lift_apply_of, PresentedGroup.of] using hA s
  rw [← QuotientGroup.ker_mk' (Subgroup.center SL(2, R))]
  apply MonoidHom.mem_ker.mpr
  change ((QuotientGroup.mk' (Subgroup.center SL(2, R))).comp (FreeGroup.lift A))
    (surfaceRelator g) = 1
  rw [hfree, MonoidHom.comp_apply,
    PresentedGroup.one_of_mem (Set.mem_singleton (surfaceRelator g)), map_one]

/-- The existence of any coherent projective lift forces the same unchanged
ordered relator to vanish for every choice of generator lifts. -/
theorem lift_surfaceRelator_eq_one_of_projective_lift
    {R : Type*} [CommRing R] {g : ℕ}
    (ρbar : SurfaceGroup g →* PSL(2, R)) (A : SurfaceGenerator g → SL(2, R))
    (hA : ∀ s, QuotientGroup.mk' (Subgroup.center SL(2, R)) (A s) =
      ρbar (PresentedGroup.of s))
    (ρ : SurfaceGroup g →* SL(2, R))
    (hρ : (QuotientGroup.mk' (Subgroup.center SL(2, R))).comp ρ = ρbar) :
    FreeGroup.lift A (surfaceRelator g) = 1 := by
  let B : SurfaceGenerator g → SL(2, R) := fun s => ρ (PresentedGroup.of s)
  have hAB : ∀ s, QuotientGroup.mk' (Subgroup.center SL(2, R)) (A s) =
      QuotientGroup.mk' (Subgroup.center SL(2, R)) (B s) := by
    intro s
    rw [hA]
    exact (DFunLike.congr_fun hρ (PresentedGroup.of s)).symm
  rw [lift_surfaceRelator_eq_of_projective_generators A B hAB]
  have hfree : FreeGroup.lift B =
      ρ.comp (PresentedGroup.mk ({surfaceRelator g} : Set _)) := by
    apply FreeGroup.ext_hom
    intro s
    simp only [FreeGroup.lift_apply_of, MonoidHom.comp_apply]
    rfl
  rw [hfree, MonoidHom.comp_apply,
    PresentedGroup.one_of_mem (Set.mem_singleton (surfaceRelator g)), map_one]

/-- The surface projective lifting obstruction is exactly the value of the
original ordered relator, independently of the chosen generator lifts. -/
theorem exists_surfaceGroup_projective_lift_iff
    {R : Type*} [CommRing R] {g : ℕ}
    (ρbar : SurfaceGroup g →* PSL(2, R)) (A : SurfaceGenerator g → SL(2, R))
    (hA : ∀ s, QuotientGroup.mk' (Subgroup.center SL(2, R)) (A s) =
      ρbar (PresentedGroup.of s)) :
    (∃ ρ : SurfaceGroup g →* SL(2, R),
      (QuotientGroup.mk' (Subgroup.center SL(2, R))).comp ρ = ρbar) ↔
        FreeGroup.lift A (surfaceRelator g) = 1 := by
  constructor
  · rintro ⟨ρ, hρ⟩
    exact lift_surfaceRelator_eq_one_of_projective_lift ρbar A hA ρ hρ
  · intro hrel
    obtain ⟨ρ, _, hρ⟩ := exists_surfaceGroup_lift_of_relator ρbar A hA hrel
    exact ⟨ρ, hρ⟩

/-- Over a domain, the actual surface lifting obstruction is either `I` or
`-I`. This dichotomy does not assert that the sign is positive. -/
theorem lift_surfaceRelator_eq_one_or_neg_one
    {R : Type*} [CommRing R] [NoZeroDivisors R] {g : ℕ}
    (ρbar : SurfaceGroup g →* PSL(2, R)) (A : SurfaceGenerator g → SL(2, R))
    (hA : ∀ s, QuotientGroup.mk' (Subgroup.center SL(2, R)) (A s) =
      ρbar (PresentedGroup.of s)) :
    FreeGroup.lift A (surfaceRelator g) = 1 ∨
      FreeGroup.lift A (surfaceRelator g) = -1 := by
  obtain ⟨r, hr, hscalar⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp
    (lift_surfaceRelator_mem_center ρbar A hA)
  have hr' : r = 1 ∨ r = -1 := sq_eq_one_iff.mp (by simpa using hr)
  rcases hr' with rfl | rfl
  · left
    apply Subtype.ext
    simpa using hscalar.symm
  · right
    apply Subtype.ext
    simpa only [map_neg, map_one, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one] using hscalar.symm

/-- A coherent lift of a faithful projective surface representation is itself
faithful; equality upstairs implies equality under the original representation. -/
theorem injective_surfaceGroup_projective_lift
    {R : Type*} [CommRing R] {g : ℕ}
    (ρbar : SurfaceGroup g →* PSL(2, R)) (ρ : SurfaceGroup g →* SL(2, R))
    (hρ : (QuotientGroup.mk' (Subgroup.center SL(2, R))).comp ρ = ρbar)
    (hfaithful : Function.Injective ρbar) : Function.Injective ρ := by
  intro a b hab
  apply hfaithful
  have hp := congrArg (QuotientGroup.mk' (Subgroup.center SL(2, R))) hab
  simpa only [← MonoidHom.comp_apply, hρ] using hp

/-- The image of an actual lift of faithful real projective holonomy excludes
`-I`. This is a statement about the lifted image, not the full inverse image
of the projective subgroup. -/
theorem neg_one_notMem_range_surfaceGroup_projective_lift
    {g : ℕ} (ρbar : SurfaceGroup g →* PSL(2, ℝ)) (ρ : SurfaceGroup g →* SL(2, ℝ))
    (hρ : (QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp ρ = ρbar)
    (hfaithful : Function.Injective ρbar) : (-1 : SL(2, ℝ)) ∉ ρ.range := by
  have hnegcenter : (-1 : SL(2, ℝ)) ∈ Subgroup.center SL(2, ℝ) := by
    apply Subgroup.mem_center_iff.mpr
    intro a
    rw [mul_neg_one, neg_one_mul]
  have hprojectneg : QuotientGroup.mk' (Subgroup.center SL(2, ℝ)) (-1) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [QuotientGroup.ker_mk']
    exact hnegcenter
  rintro ⟨γ, hγ⟩
  have hproject : ρbar γ = 1 := by
    rw [← hρ, MonoidHom.comp_apply, hγ]
    exact hprojectneg
  have hγone : γ = 1 := hfaithful (hproject.trans (map_one ρbar).symm)
  rw [hγone, map_one] at hγ
  have hentry : (1 : ℝ) = -1 := by
    simpa using congrArg (fun a : SL(2, ℝ) =>
      (a : Matrix (Fin 2) (Fin 2) ℝ) 0 0) hγ
  norm_num at hentry

/-- The relator constructor, consumed by a faithful real projective
representation, produces a faithful special-linear representation whose own
image excludes `-I`, with the exact selected generator lifts. -/
theorem exists_faithful_surfaceGroup_lift_of_relator
    {g : ℕ} (ρbar : SurfaceGroup g →* PSL(2, ℝ))
    (A : SurfaceGenerator g → SL(2, ℝ))
    (hA : ∀ s, QuotientGroup.mk' (Subgroup.center SL(2, ℝ)) (A s) =
      ρbar (PresentedGroup.of s))
    (hfaithful : Function.Injective ρbar)
    (hrel : FreeGroup.lift A (surfaceRelator g) = 1) :
    ∃ ρ : SurfaceGroup g →* SL(2, ℝ),
      (∀ s, ρ (PresentedGroup.of s) = A s) ∧
        (QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp ρ = ρbar ∧
          Function.Injective ρ ∧ (-1 : SL(2, ℝ)) ∉ ρ.range := by
  obtain ⟨ρ, hgen, hρ⟩ := exists_surfaceGroup_lift_of_relator ρbar A hA hrel
  exact ⟨ρ, hgen, hρ, injective_surfaceGroup_projective_lift ρbar ρ hρ hfaithful,
    neg_one_notMem_range_surfaceGroup_projective_lift ρbar ρ hρ hfaithful⟩

#print axioms lift_surfaceRelator_eq_prod_commutators
#print axioms lift_surfaceRelator_eq_of_projective_generators
#print axioms exists_surfaceGroup_lift_of_relator
#print axioms lift_surfaceRelator_mem_center
#print axioms lift_surfaceRelator_eq_one_of_projective_lift
#print axioms exists_surfaceGroup_projective_lift_iff
#print axioms lift_surfaceRelator_eq_one_or_neg_one
#print axioms injective_surfaceGroup_projective_lift
#print axioms neg_one_notMem_range_surfaceGroup_projective_lift
#print axioms exists_faithful_surfaceGroup_lift_of_relator

end SystolicGrowth
