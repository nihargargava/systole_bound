module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.GroupTheory.PushoutI
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Geometry.GluingSeamFundamentalGroup

@[expose] public section

/-!
# Trivial amalgams of free groups

An indexed amalgam of groups that are free, over a subsingleton base, is the
free group on the disjoint union of the factor generators. The maps below are
the canonical maps supplied by the actual factor equivalences and pushout.
-/

namespace SystolicGrowth

noncomputable section

variable {ι : Type*} {H : Type*} {G : ι → Type*} {A : ι → Type*}
variable [Group H] [Subsingleton H] [∀ i, Group (G i)]

/-- The canonical inclusion of one factor's free generators into the free
group on all factor generators. -/
def freeGroupTrivialAmalgamFactorMap (A : ι → Type*) (i : ι) :
    FreeGroup (A i) →* FreeGroup (Σ j, A j) :=
  FreeGroup.lift fun a => FreeGroup.of ⟨i, a⟩

/-- The unique homomorphism from the trivial base group to a target group. -/
def freeGroupTrivialAmalgamTrivialMap (H K : Type*) [Group H] [Group K] : H →* K where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := by simp

theorem Internal.FreeGroupTrivialAmalgamHelpers.freeGroupTrivialAmalgamTrivialMap_unique
    {H K : Type*} [Group H] [Subsingleton H] [Group K] (f : H →* K) :
    f = freeGroupTrivialAmalgamTrivialMap H K := by
  ext h
  have hh : h = 1 := Subsingleton.elim _ _
  simp [freeGroupTrivialAmalgamTrivialMap, hh]

/-- The canonical map from the amalgam to the free group on all factor
generators, defined using the factor equivalences. -/
def freeGroupTrivialAmalgamForward
    (φ : ∀ i, H →* G i) (e : ∀ i, G i ≃* FreeGroup (A i)) :
    Monoid.PushoutI φ →* FreeGroup (Σ i, A i) := by
  let f : ∀ i, G i →* FreeGroup (Σ i, A i) := fun i =>
    (freeGroupTrivialAmalgamFactorMap A i).comp (e i).toMonoidHom
  let k : H →* FreeGroup (Σ i, A i) :=
    freeGroupTrivialAmalgamTrivialMap H (FreeGroup (Σ i, A i))
  have hf : ∀ i, (f i).comp (φ i) = k := by
    intro i
    exact Internal.FreeGroupTrivialAmalgamHelpers.freeGroupTrivialAmalgamTrivialMap_unique ((f i).comp (φ i))
  exact Monoid.PushoutI.lift f k hf

/-- Send each global free generator to the corresponding actual factor
generator. -/
def freeGroupTrivialAmalgamBackward
    (φ : ∀ i, H →* G i) (e : ∀ i, G i ≃* FreeGroup (A i)) :
    FreeGroup (Σ i, A i) →* Monoid.PushoutI φ :=
  FreeGroup.lift fun x =>
    Monoid.PushoutI.of x.1 ((e x.1).symm (FreeGroup.of x.2))

omit [Subsingleton H] in
private theorem freeGroupTrivialAmalgamBackward_comp_factor
    (φ : ∀ i, H →* G i) (e : ∀ i, G i ≃* FreeGroup (A i)) (i : ι) :
    (freeGroupTrivialAmalgamBackward φ e).comp
        (freeGroupTrivialAmalgamFactorMap A i) =
      (Monoid.PushoutI.of i).comp (e i).symm.toMonoidHom := by
  apply FreeGroup.lift.symm.injective
  funext a
  simp [freeGroupTrivialAmalgamBackward, freeGroupTrivialAmalgamFactorMap]

theorem Internal.FreeGroupTrivialAmalgamHelpers.freeGroupTrivialAmalgamForward_backward
    (φ : ∀ i, H →* G i) (e : ∀ i, G i ≃* FreeGroup (A i)) :
    (freeGroupTrivialAmalgamForward φ e).comp
        (freeGroupTrivialAmalgamBackward φ e) = MonoidHom.id _ := by
  apply FreeGroup.lift.symm.injective
  funext x
  rcases x with ⟨i, a⟩
  simp [freeGroupTrivialAmalgamForward, freeGroupTrivialAmalgamBackward,
    freeGroupTrivialAmalgamFactorMap]

theorem Internal.FreeGroupTrivialAmalgamHelpers.freeGroupTrivialAmalgamBackward_forward
    (φ : ∀ i, H →* G i) (e : ∀ i, G i ≃* FreeGroup (A i)) :
    (freeGroupTrivialAmalgamBackward φ e).comp
        (freeGroupTrivialAmalgamForward φ e) = MonoidHom.id _ := by
  apply Monoid.PushoutI.hom_ext
  · intro i
    ext g
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
    rw [freeGroupTrivialAmalgamForward, Monoid.PushoutI.lift_of]
    change (freeGroupTrivialAmalgamBackward φ e)
      (freeGroupTrivialAmalgamFactorMap A i ((e i) g)) = _
    rw [← MonoidHom.comp_apply, freeGroupTrivialAmalgamBackward_comp_factor]
    simp
  · ext h
    have hh : h = 1 := Subsingleton.elim _ _
    subst h
    simp [MonoidHom.comp_apply,
      freeGroupTrivialAmalgamForward, freeGroupTrivialAmalgamTrivialMap]

/-- The canonical free-group equivalence for an indexed pushout over a
subsingleton group. -/
def freeGroupTrivialAmalgamEquiv
    (φ : ∀ i, H →* G i) (e : ∀ i, G i ≃* FreeGroup (A i)) :
    Monoid.PushoutI φ ≃* FreeGroup (Σ i, A i) where
  toFun := freeGroupTrivialAmalgamForward φ e
  invFun := freeGroupTrivialAmalgamBackward φ e
  left_inv x := by
    have h := Internal.FreeGroupTrivialAmalgamHelpers.freeGroupTrivialAmalgamBackward_forward φ e
    exact congrArg (fun f : Monoid.PushoutI φ →* Monoid.PushoutI φ => f x) h
  right_inv x := by
    have h := Internal.FreeGroupTrivialAmalgamHelpers.freeGroupTrivialAmalgamForward_backward φ e
    exact congrArg (fun f : FreeGroup (Σ i, A i) →* FreeGroup (Σ i, A i) => f x) h
  map_mul' := (freeGroupTrivialAmalgamForward φ e).map_mul

/-- On each actual factor, the amalgam equivalence is its given free
equivalence followed by the literal summand inclusion. -/
@[simp]
theorem freeGroupTrivialAmalgamEquiv_of
    (φ : ∀ i, H →* G i) (e : ∀ i, G i ≃* FreeGroup (A i))
    (i : ι) (g : G i) :
    freeGroupTrivialAmalgamEquiv φ e (Monoid.PushoutI.of i g) =
      freeGroupTrivialAmalgamFactorMap A i (e i g) := by
  simp [freeGroupTrivialAmalgamEquiv, freeGroupTrivialAmalgamForward,
    freeGroupTrivialAmalgamFactorMap]

/-- In particular, the actual factor generator corresponding to `a` maps to
the tagged global generator `(i, a)`. -/
@[simp]
theorem freeGroupTrivialAmalgamEquiv_factorGenerator
    (φ : ∀ i, H →* G i) (e : ∀ i, G i ≃* FreeGroup (A i))
    (i : ι) (a : A i) :
    freeGroupTrivialAmalgamEquiv φ e
      (Monoid.PushoutI.of i ((e i).symm (FreeGroup.of a))) =
        FreeGroup.of ⟨i, a⟩ := by
  simp [freeGroupTrivialAmalgamEquiv, freeGroupTrivialAmalgamForward,
    freeGroupTrivialAmalgamFactorMap]

/-- Each global free generator is the image of the corresponding factor
generator under the inverse equivalence. -/
@[simp]
theorem freeGroupTrivialAmalgamEquiv_symm_generator
    (φ : ∀ i, H →* G i) (e : ∀ i, G i ≃* FreeGroup (A i))
    (i : ι) (a : A i) :
    (freeGroupTrivialAmalgamEquiv φ e).symm (FreeGroup.of ⟨i, a⟩) =
      Monoid.PushoutI.of i ((e i).symm (FreeGroup.of a)) := by
  simp [freeGroupTrivialAmalgamEquiv, freeGroupTrivialAmalgamBackward]

/-- The circle's based fundamental group is the free group on its single
positive generator. -/
def circleFundamentalGroupFreeEquiv (θ : Circle) :
    FundamentalGroup Circle θ ≃* FreeGroup Unit :=
  (circleFundamentalGroupEquivIntegers θ).trans
    ((MulOpposite.opMulEquiv (M := Multiplicative ℤ)).symm.trans
      FreeGroup.mulEquivIntOfUnique.symm)

/-- The positive one-turn loop is the literal positive free generator. -/
theorem circleFundamentalGroupFreeEquiv_oneTurn (θ : Circle) :
    circleFundamentalGroupFreeEquiv θ ⟦circleOneTurnLoop θ⟧ = FreeGroup.of () := by
  change ((MulOpposite.opMulEquiv (M := Multiplicative ℤ)).symm.trans
      FreeGroup.mulEquivIntOfUnique.symm)
    (circleFundamentalGroupEquivIntegers θ
      (⟦circleOneTurnLoop θ⟧ : FundamentalGroup Circle θ)) = _
  rw [circleFundamentalGroupEquivIntegers_oneTurn]
  change FreeGroup.mulEquivIntOfUnique.symm
    ((MulOpposite.opMulEquiv (M := Multiplicative ℤ)).symm
      (MulOpposite.op (Multiplicative.ofAdd (1 : ℤ)))) = FreeGroup.of ()
  have hop : (MulOpposite.opMulEquiv (M := Multiplicative ℤ)).symm
      (MulOpposite.op (Multiplicative.ofAdd (1 : ℤ))) =
        Multiplicative.ofAdd (1 : ℤ) := by
    apply (MulOpposite.opMulEquiv (M := Multiplicative ℤ)).injective
    simp
  rw [hop]
  apply FreeGroup.mulEquivIntOfUnique.injective
  change (1 : ℤ) = FreeGroup.equivIntOfUnique (FreeGroup.of ())
  simp [FreeGroup.equivIntOfUnique]

#print axioms freeGroupTrivialAmalgamEquiv
#print axioms freeGroupTrivialAmalgamEquiv_of
#print axioms freeGroupTrivialAmalgamEquiv_factorGenerator
#print axioms freeGroupTrivialAmalgamEquiv_symm_generator
#print axioms circleFundamentalGroupFreeEquiv_oneTurn

end

end SystolicGrowth
