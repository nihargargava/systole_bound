module

public import Core.SystolicCore
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

open scoped commutatorElement

namespace SystolicGrowth

/-! # Additive characters of the surface group

This file records the algebraic input needed by a combinatorial
Gauss--Bonnet argument: the real additive-character space of the standard
genus-`g` surface group has dimension `2g`.
-/

/-- Real-valued additive characters of a multiplicative group. -/
def AdditiveCharacterSpace (G : Type*) [Group G] : Submodule ℝ (G → ℝ) where
  carrier := {f | ∀ x y, f (x * y) = f x + f y}
  zero_mem' := by simp
  add_mem' := by
    intro f h hf hh x y
    simp only [Pi.add_apply, hf x y, hh x y]
    ring
  smul_mem' := by
    intro c f hf x y
    simp only [Pi.smul_apply, hf x y, smul_eq_mul]
    ring

/-- An additive character vanishes at the identity. -/
@[simp] theorem AdditiveCharacterSpace.apply_one
    {G : Type*} [Group G] (f : AdditiveCharacterSpace G) :
    (f : G → ℝ) 1 = 0 := by
  have h := f.2 1 1
  simp only [one_mul] at h
  linarith

/-- Regard an additive character as a homomorphism to the multiplicative
copy of the additive real group. -/
def AdditiveCharacterSpace.toMultiplicativeHom
    {G : Type*} [Group G] (f : AdditiveCharacterSpace G) :
    G →* Multiplicative ℝ where
  toFun x := Multiplicative.ofAdd ((f : G → ℝ) x)
  map_one' := by simp
  map_mul' x y := by
    change Multiplicative.ofAdd ((f : G → ℝ) (x * y)) =
      Multiplicative.ofAdd ((f : G → ℝ) x + (f : G → ℝ) y)
    rw [f.2 x y]

/-- The surface relator is killed by every assignment of real values to its
generators, because the target group is commutative. -/
theorem Internal.SurfaceCharacterRankHelpers.surfaceRelator_map_eq_one (g : ℕ)
    (v : SurfaceGenerator g → ℝ) :
    FreeGroup.lift (fun x ↦ Multiplicative.ofAdd (v x)) (surfaceRelator g) = 1 := by
  rw [surfaceRelator, map_list_prod]
  apply List.prod_eq_one
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)

/-- Extend arbitrary values on the standard generators to an additive
character of the presented surface group. -/
noncomputable def extendSurfaceCharacter (g : ℕ)
    (v : SurfaceGenerator g → ℝ) : AdditiveCharacterSpace (SurfaceGroup g) := by
  let F : SurfaceGroup g →* Multiplicative ℝ :=
    PresentedGroup.toGroup (f := fun x ↦ Multiplicative.ofAdd (v x)) (by
      intro r hr
      rw [Set.mem_singleton_iff.mp hr]
      exact Internal.SurfaceCharacterRankHelpers.surfaceRelator_map_eq_one g v)
  refine ⟨fun x ↦ Multiplicative.toAdd (F x), ?_⟩
  intro x y
  change Multiplicative.toAdd (F (x * y)) =
    Multiplicative.toAdd (F x) + Multiplicative.toAdd (F y)
  rw [show F (x * y) = F x * F y from map_mul F x y]
  rfl

@[simp] theorem extendSurfaceCharacter_apply_of (g : ℕ)
    (v : SurfaceGenerator g → ℝ) (x : SurfaceGenerator g) :
    (extendSurfaceCharacter g v : SurfaceGroup g → ℝ) (PresentedGroup.of x) = v x := by
  simp [extendSurfaceCharacter]

/-- Additive characters of a presented group agree when they agree on all
standard generators. -/
theorem surfaceCharacter_ext {g : ℕ}
    {f h : AdditiveCharacterSpace (SurfaceGroup g)}
    (heq : ∀ x : SurfaceGenerator g,
      (f : SurfaceGroup g → ℝ) (PresentedGroup.of x) =
        (h : SurfaceGroup g → ℝ) (PresentedGroup.of x)) : f = h := by
  apply Subtype.ext
  funext y
  have H : AdditiveCharacterSpace.toMultiplicativeHom f =
      AdditiveCharacterSpace.toMultiplicativeHom h := by
    apply PresentedGroup.ext
    intro x
    exact congrArg Multiplicative.ofAdd (heq x)
  have Hy := congrArg (fun q ↦ q y) H
  exact congrArg Multiplicative.toAdd Hy

/-- Reindex additive characters along a group equivalence. -/
def reindexAdditiveCharacter {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (f : AdditiveCharacterSpace G) : AdditiveCharacterSpace H := by
  refine ⟨fun y ↦ (f : G → ℝ) (e.symm y), ?_⟩
  intro x y
  change (f : G → ℝ) (e.symm (x * y)) =
    (f : G → ℝ) (e.symm x) + (f : G → ℝ) (e.symm y)
  rw [e.symm.map_mul, f.2]

/-- A group equivalence induces a linear equivalence of its real additive
character spaces. -/
def additiveCharacterLinearEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) : AdditiveCharacterSpace G ≃ₗ[ℝ] AdditiveCharacterSpace H :=
  LinearEquiv.ofLinear
    { toFun := reindexAdditiveCharacter e
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    { toFun := reindexAdditiveCharacter e.symm
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    (by
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      funext x
      change (f : H → ℝ) (e (e.symm x)) = (f : H → ℝ) x
      rw [e.apply_symm_apply])
    (by
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      funext x
      change (f : G → ℝ) (e.symm (e x)) = (f : G → ℝ) x
      rw [e.symm_apply_apply])

/-- Restrict an additive character to the standard surface generators. -/
def restrictSurfaceCharacter (g : ℕ) :
    AdditiveCharacterSpace (SurfaceGroup g) →ₗ[ℝ] (SurfaceGenerator g → ℝ) where
  toFun f x := (f : SurfaceGroup g → ℝ) (PresentedGroup.of x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Extension from generator values is linear. -/
noncomputable def extendSurfaceCharacterLinear (g : ℕ) :
    (SurfaceGenerator g → ℝ) →ₗ[ℝ] AdditiveCharacterSpace (SurfaceGroup g) where
  toFun := extendSurfaceCharacter g
  map_add' v w := by
    apply surfaceCharacter_ext
    intro x
    simp
  map_smul' c v := by
    apply surfaceCharacter_ext
    intro x
    simp

/-- The additive-character space of the surface group is freely determined
by the values on its `2g` standard generators. -/
noncomputable def surfaceCharacterLinearEquiv (g : ℕ) :
    AdditiveCharacterSpace (SurfaceGroup g) ≃ₗ[ℝ] (SurfaceGenerator g → ℝ) :=
  LinearEquiv.ofLinear (restrictSurfaceCharacter g) (extendSurfaceCharacterLinear g)
    (by
      apply LinearMap.ext
      intro v
      funext x
      simp [restrictSurfaceCharacter, extendSurfaceCharacterLinear])
    (by
      apply LinearMap.ext
      intro f
      apply surfaceCharacter_ext
      intro x
      simp [restrictSurfaceCharacter, extendSurfaceCharacterLinear])

/-- The real character space of a genus-`g` surface group has dimension
exactly `2g`. -/
theorem finrank_surfaceCharacterSpace (g : ℕ) :
    Module.finrank ℝ (AdditiveCharacterSpace (SurfaceGroup g)) = 2 * g := by
  rw [(surfaceCharacterLinearEquiv g).finrank_eq]
  simp [SurfaceGenerator, Nat.mul_comm]

/-- The marking of a closed hyperbolic surface identifies the dimension of
the deck group's character space with twice the recorded genus. -/
theorem ClosedHyperbolicSurface.finrank_deckGroupCharacterSpace
    {g : ℕ} (X : ClosedHyperbolicSurface g) :
    Module.finrank ℝ (AdditiveCharacterSpace X.deckGroup) = 2 * g := by
  rw [(additiveCharacterLinearEquiv X.marking).finrank_eq]
  exact finrank_surfaceCharacterSpace g

end SystolicGrowth
