module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.GroupTheory.PushoutI
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

set_option maxHeartbeats 1000000

/-!
# Free marking for a native prefix attachment

This is the algebraic pushout step for adjoining one component to a marked
prefix. The shared incoming peripheral generator is identified with the
actual word in the previous prefix; the outgoing word keeps its ordered sign.
-/

namespace SystolicGrowth

noncomputable section

universe u

/-- The prefix exterior factor and the next component with its retained
incoming peripheral letter. -/
abbrev surfacePrefixPeripheralFactor (A B : Type u) : Bool → Type u
  | true => FreeGroup A
  | false => FreeGroup (B ⊕ Unit)

@[reducible]
instance {A B : Type u} (b : Bool) :
    Group (surfacePrefixPeripheralFactor A B b) := by
  cases b <;> infer_instance

/-- Both sides receive the same positive overlap circle. On the old prefix
it is the inverse of the existing word; on the new component it is the
inverse of the retained incoming letter. -/
def surfacePrefixPeripheralBaseMap {A B : Type u} (w : FreeGroup A)
    (b : Bool) : FreeGroup Unit →* surfacePrefixPeripheralFactor A B b := by
  cases b
  · exact FreeGroup.lift fun _ : Unit => (FreeGroup.of (Sum.inr () : B ⊕ Unit))⁻¹
  · exact FreeGroup.lift fun _ : Unit => w⁻¹

/-- Map the old prefix generators and the new component handles to the
disjoint union. The retained incoming letter is sent to the old peripheral
word. -/
def surfacePrefixPeripheralForwardFactor {A B : Type u} (w : FreeGroup A)
    (b : Bool) : surfacePrefixPeripheralFactor A B b →* FreeGroup (A ⊕ B) := by
  cases b
  · exact FreeGroup.lift fun x : B ⊕ Unit => match x with
      | Sum.inl b => FreeGroup.of (Sum.inr b)
      | Sum.inr _ => FreeGroup.map (Sum.inl : A → A ⊕ B) w
  · exact FreeGroup.map (Sum.inl : A → A ⊕ B)

theorem Internal.SurfacePrefixPeripheralAmalgamHelpers.surfacePrefixPeripheralForwardFactor_compatible
    {A B : Type u} (w : FreeGroup A) (b : Bool) :
    (surfacePrefixPeripheralForwardFactor (B := B) w b).comp
        (surfacePrefixPeripheralBaseMap (B := B) w b) =
      FreeGroup.lift (fun _ : Unit =>
        (FreeGroup.map (Sum.inl : A → A ⊕ B) w)⁻¹) := by
  apply FreeGroup.lift.symm.injective
  funext u
  cases u
  change ((surfacePrefixPeripheralForwardFactor (B := B) w b).comp
    (surfacePrefixPeripheralBaseMap (B := B) w b)) (FreeGroup.of ()) = _
  cases b <;> simp [surfacePrefixPeripheralForwardFactor,
    surfacePrefixPeripheralBaseMap]

/-- The universal-property map from the actual prefix pushout to the free
group on the previous and new handle generators. -/
def surfacePrefixPeripheralForward {A B : Type u} (w : FreeGroup A) :
    Monoid.PushoutI (surfacePrefixPeripheralBaseMap (B := B) w) →*
      FreeGroup (A ⊕ B) :=
  Monoid.PushoutI.lift (surfacePrefixPeripheralForwardFactor (B := B) w)
    (FreeGroup.lift (fun _ : Unit =>
      (FreeGroup.map (Sum.inl : A → A ⊕ B) w)⁻¹))
    (Internal.SurfacePrefixPeripheralAmalgamHelpers.surfacePrefixPeripheralForwardFactor_compatible (B := B) w)

/-- Send each generator of the disjoint-union free group back to the actual
factor in the pushout. -/
def surfacePrefixPeripheralBackward {A B : Type u} (w : FreeGroup A) :
    FreeGroup (A ⊕ B) →* Monoid.PushoutI
      (surfacePrefixPeripheralBaseMap (B := B) w) :=
  FreeGroup.lift fun x : A ⊕ B => match x with
    | Sum.inl a => Monoid.PushoutI.of true (FreeGroup.of a)
    | Sum.inr b => Monoid.PushoutI.of false (FreeGroup.of (Sum.inl b))

private theorem surfacePrefixPeripheralIncoming_eq_oldWord
    {A B : Type u} (w : FreeGroup A) :
    Monoid.PushoutI.of (φ := surfacePrefixPeripheralBaseMap (B := B) w) true w =
      Monoid.PushoutI.of (φ := surfacePrefixPeripheralBaseMap (B := B) w)
        false (FreeGroup.of (Sum.inr ())) := by
  have hbase :=
    (Monoid.PushoutI.of_apply_eq_base
      (surfacePrefixPeripheralBaseMap (B := B) w) true (FreeGroup.of ())).trans
    (Monoid.PushoutI.of_apply_eq_base
      (surfacePrefixPeripheralBaseMap (B := B) w) false (FreeGroup.of ())).symm
  simp only [surfacePrefixPeripheralBaseMap, FreeGroup.lift_apply_of] at hbase
  simpa [map_inv] using congrArg (fun x : Monoid.PushoutI
    (surfacePrefixPeripheralBaseMap (B := B) w) => x⁻¹) hbase

private theorem surfacePrefixPeripheralBackward_inl
    {A B : Type u} (w : FreeGroup A) :
    (surfacePrefixPeripheralBackward (B := B) w).comp
        (FreeGroup.map (Sum.inl : A → A ⊕ B)) =
      Monoid.PushoutI.of (φ := surfacePrefixPeripheralBaseMap (B := B) w) true := by
  apply FreeGroup.lift.symm.injective
  funext a
  simp [surfacePrefixPeripheralBackward]

private theorem surfacePrefixPeripheralBackward_forwardFactor
    {A B : Type u} (w : FreeGroup A) (b : Bool) :
    (surfacePrefixPeripheralBackward (B := B) w).comp
        (surfacePrefixPeripheralForwardFactor (B := B) w b) =
      (Monoid.PushoutI.of (φ := surfacePrefixPeripheralBaseMap (B := B) w) b) := by
  cases b
  · apply FreeGroup.lift.symm.injective
    funext x
    cases x with
    | inl b => simp [surfacePrefixPeripheralForwardFactor,
        surfacePrefixPeripheralBackward]
    | inr u =>
      cases u
      have hleft := congrArg
        (fun f : FreeGroup A →* Monoid.PushoutI
          (surfacePrefixPeripheralBaseMap (B := B) w) => f w)
        (surfacePrefixPeripheralBackward_inl (B := B) w)
      change ((surfacePrefixPeripheralBackward (B := B) w).comp
          (surfacePrefixPeripheralForwardFactor (B := B) w false))
          (FreeGroup.of (Sum.inr () : B ⊕ Unit)) =
        Monoid.PushoutI.of
          (φ := surfacePrefixPeripheralBaseMap (B := B) w) false
          (FreeGroup.of (Sum.inr () : B ⊕ Unit))
      simpa only [MonoidHom.comp_apply, surfacePrefixPeripheralForwardFactor,
        FreeGroup.lift_apply_of] using
        hleft.trans (surfacePrefixPeripheralIncoming_eq_oldWord (B := B) w)
  · apply FreeGroup.lift.symm.injective
    funext a
    simp [surfacePrefixPeripheralForwardFactor,
      surfacePrefixPeripheralBackward]

theorem Internal.SurfacePrefixPeripheralAmalgamHelpers.surfacePrefixPeripheralBackward_forward
    {A B : Type u} (w : FreeGroup A) :
    (surfacePrefixPeripheralBackward (B := B) w).comp
        (surfacePrefixPeripheralForward (B := B) w) = MonoidHom.id _ := by
  apply Monoid.PushoutI.hom_ext_nonempty
  intro b
  ext x
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply,
    surfacePrefixPeripheralForward, Monoid.PushoutI.lift_of]
  exact congrArg (fun f : surfacePrefixPeripheralFactor A B b →* _ => f x)
    (surfacePrefixPeripheralBackward_forwardFactor (B := B) w b)

theorem Internal.SurfacePrefixPeripheralAmalgamHelpers.surfacePrefixPeripheralForward_backward
    {A B : Type u} (w : FreeGroup A) :
    (surfacePrefixPeripheralForward (B := B) w).comp
        (surfacePrefixPeripheralBackward (B := B) w) = MonoidHom.id _ := by
  apply FreeGroup.lift.symm.injective
  funext x
  cases x with
  | inl a => simp [surfacePrefixPeripheralForward,
      surfacePrefixPeripheralBackward, surfacePrefixPeripheralForwardFactor]
  | inr b => simp [surfacePrefixPeripheralForward,
      surfacePrefixPeripheralBackward, surfacePrefixPeripheralForwardFactor]

/-- The native prefix amalgam is freely generated by the old prefix handles
and the new component handles. -/
def surfacePrefixPeripheralAmalgamEquiv {A B : Type u} (w : FreeGroup A) :
    Monoid.PushoutI (surfacePrefixPeripheralBaseMap (B := B) w) ≃*
      FreeGroup (A ⊕ B) where
  toFun := surfacePrefixPeripheralForward (B := B) w
  invFun := surfacePrefixPeripheralBackward (B := B) w
  left_inv x := congrArg
    (fun f : Monoid.PushoutI (surfacePrefixPeripheralBaseMap (B := B) w) →* _ => f x)
    (Internal.SurfacePrefixPeripheralAmalgamHelpers.surfacePrefixPeripheralBackward_forward (B := B) w)
  right_inv x := congrArg
    (fun f : FreeGroup (A ⊕ B) →* FreeGroup (A ⊕ B) => f x)
    (Internal.SurfacePrefixPeripheralAmalgamHelpers.surfacePrefixPeripheralForward_backward (B := B) w)
  map_mul' := (surfacePrefixPeripheralForward (B := B) w).map_mul

/-- Old prefix generators retain the left summand tag. -/
@[simp]
theorem surfacePrefixPeripheralAmalgamEquiv_leftGenerator
    {A B : Type u} (w : FreeGroup A) (a : A) :
    surfacePrefixPeripheralAmalgamEquiv (B := B) w
      (Monoid.PushoutI.of true (FreeGroup.of a)) = FreeGroup.of (Sum.inl a) := by
  simp [surfacePrefixPeripheralAmalgamEquiv, surfacePrefixPeripheralForward,
    surfacePrefixPeripheralForwardFactor]

/-- New component handles retain the right summand tag. -/
@[simp]
theorem surfacePrefixPeripheralAmalgamEquiv_rightGenerator
    {A B : Type u} (w : FreeGroup A) (b : B) :
    surfacePrefixPeripheralAmalgamEquiv (B := B) w
      (Monoid.PushoutI.of false (FreeGroup.of (Sum.inl b))) =
        FreeGroup.of (Sum.inr b) := by
  simp [surfacePrefixPeripheralAmalgamEquiv, surfacePrefixPeripheralForward,
    surfacePrefixPeripheralForwardFactor]

/-- The retained incoming letter is identified with the old prefix word. -/
@[simp]
theorem surfacePrefixPeripheralAmalgamEquiv_incoming
    {A B : Type u} (w : FreeGroup A) :
    surfacePrefixPeripheralAmalgamEquiv (B := B) w
      (Monoid.PushoutI.of false (FreeGroup.of (Sum.inr ()))) =
        FreeGroup.map (Sum.inl : A → A ⊕ B) w := by
  simp [surfacePrefixPeripheralAmalgamEquiv, surfacePrefixPeripheralForward,
    surfacePrefixPeripheralForwardFactor]

/-- The complete new handle subgroup maps by the right summand inclusion. -/
theorem surfacePrefixPeripheralAmalgamEquiv_rightHandleMap
    {A B : Type u} (w : FreeGroup A) (h : FreeGroup B) :
    surfacePrefixPeripheralAmalgamEquiv (B := B) w
      (Monoid.PushoutI.of false
        (FreeGroup.map (Sum.inl : B → B ⊕ Unit) h)) =
      FreeGroup.map (Sum.inr : B → A ⊕ B) h := by
  have hcomp :
      ((surfacePrefixPeripheralAmalgamEquiv (B := B) w).toMonoidHom.comp
        (Monoid.PushoutI.of
          (φ := surfacePrefixPeripheralBaseMap (B := B) w) false)).comp
        (FreeGroup.map (Sum.inl : B → B ⊕ Unit)) =
      FreeGroup.map (Sum.inr : B → A ⊕ B) := by
    apply FreeGroup.lift.symm.injective
    funext b
    change surfacePrefixPeripheralAmalgamEquiv (B := B) w
        (Monoid.PushoutI.of
          (φ := surfacePrefixPeripheralBaseMap (B := B) w) false
          (FreeGroup.of (Sum.inl b))) = FreeGroup.of (Sum.inr b)
    exact surfacePrefixPeripheralAmalgamEquiv_rightGenerator (B := B) w b
  exact congrArg (fun f : FreeGroup B →* FreeGroup (A ⊕ B) => f h) hcomp

/-- The next outgoing peripheral word, with its physical order and inverse
sign, is preserved by the prefix amalgam marking. -/
theorem surfacePrefixPeripheralAmalgamEquiv_outgoing
    {A B : Type u} (w : FreeGroup A) (h : FreeGroup B) :
    surfacePrefixPeripheralAmalgamEquiv (B := B) w
      (Monoid.PushoutI.of false
        ((FreeGroup.of (Sum.inr ()) *
          FreeGroup.map (Sum.inl : B → B ⊕ Unit) h)⁻¹)) =
      (FreeGroup.map (Sum.inl : A → A ⊕ B) w *
        FreeGroup.map (Sum.inr : B → A ⊕ B) h)⁻¹ := by
  rw [(Monoid.PushoutI.of
        (φ := surfacePrefixPeripheralBaseMap (B := B) w) false).map_inv,
    (surfacePrefixPeripheralAmalgamEquiv (B := B) w).map_inv,
    (Monoid.PushoutI.of
      (φ := surfacePrefixPeripheralBaseMap (B := B) w) false).map_mul,
    (surfacePrefixPeripheralAmalgamEquiv (B := B) w).map_mul]
  apply (inv_inj).mp
  rw [surfacePrefixPeripheralAmalgamEquiv_incoming,
    surfacePrefixPeripheralAmalgamEquiv_rightHandleMap]

#print axioms surfacePrefixPeripheralAmalgamEquiv
#print axioms surfacePrefixPeripheralAmalgamEquiv_incoming
#print axioms surfacePrefixPeripheralAmalgamEquiv_outgoing

end
end SystolicGrowth
