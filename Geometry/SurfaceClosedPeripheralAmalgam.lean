module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.GroupTheory.PushoutI
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.PresentedGroup

@[expose] public section

/-!
# Close the last peripheral amalgam

The left positive overlap loop is the inverse of the prefix word, while the
right positive overlap loop is the final component word. The resulting
amalgam has the single ordered relation `prefix * final = 1`.
-/

namespace SystolicGrowth

noncomputable section

universe u

/-- The two free factors at the final closed seam. -/
abbrev surfaceClosedPeripheralFactor (A B : Type u) : Bool → Type u
  | true => FreeGroup A
  | false => FreeGroup B

@[reducible]
instance {A B : Type u} (b : Bool) : Group (surfaceClosedPeripheralFactor A B b) := by
  cases b <;> infer_instance

/-- The literal last surface relator after tagging old and final handles. -/
def surfaceClosedPeripheralRelator {A B : Type u}
    (w : FreeGroup A) (h : FreeGroup B) : FreeGroup (A ⊕ B) :=
  FreeGroup.map (Sum.inl : A → A ⊕ B) w *
    FreeGroup.map (Sum.inr : B → A ⊕ B) h

/-- Positive overlap winding maps to the inverse prefix word on the left and
to the final incoming word on the right. -/
def surfaceClosedPeripheralBaseMap {A B : Type u}
    (w : FreeGroup A) (h : FreeGroup B) (b : Bool) :
    FreeGroup Unit →* surfaceClosedPeripheralFactor A B b := by
  cases b
  · exact FreeGroup.lift fun _ : Unit => h
  · exact FreeGroup.lift fun _ : Unit => w⁻¹

/-- The quotient by the actual ordered endpoint relation. -/
abbrev surfaceClosedPeripheralPresentation {A B : Type u}
    (w : FreeGroup A) (h : FreeGroup B) :=
  PresentedGroup ({surfaceClosedPeripheralRelator w h} :
    Set (FreeGroup (A ⊕ B)))

def Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralForwardFactor {A B : Type u}
    (w : FreeGroup A) (h : FreeGroup B) (b : Bool) :
    surfaceClosedPeripheralFactor A B b →* surfaceClosedPeripheralPresentation w h := by
  cases b
  · exact (PresentedGroup.mk _).comp (FreeGroup.map (Sum.inr : B → A ⊕ B))
  · exact (PresentedGroup.mk _).comp (FreeGroup.map (Sum.inl : A → A ⊕ B))

def Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralForwardBase {A B : Type u}
    (w : FreeGroup A) (h : FreeGroup B) :
    FreeGroup Unit →* surfaceClosedPeripheralPresentation w h :=
  FreeGroup.lift fun _ : Unit =>
    PresentedGroup.mk _ (FreeGroup.map (Sum.inl : A → A ⊕ B) w)⁻¹

private theorem surfaceClosedPeripheral_relator_eq_one {A B : Type u}
    (w : FreeGroup A) (h : FreeGroup B) :
    (PresentedGroup.mk ({surfaceClosedPeripheralRelator w h} :
      Set (FreeGroup (A ⊕ B))) (surfaceClosedPeripheralRelator w h)) = 1 :=
  PresentedGroup.one_of_mem (Set.mem_singleton _)

theorem Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralForwardFactor_compatible
    {A B : Type u} (w : FreeGroup A) (h : FreeGroup B) (b : Bool) :
    (Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralForwardFactor w h b).comp
        (surfaceClosedPeripheralBaseMap w h b) =
      Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralForwardBase w h := by
  apply FreeGroup.lift.symm.injective
  funext u
  cases u
  change ((Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralForwardFactor w h b).comp
      (surfaceClosedPeripheralBaseMap w h b)) (FreeGroup.of ()) =
    (Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralForwardBase w h) (FreeGroup.of ())
  cases b
  · simp only [MonoidHom.comp_apply, surfaceClosedPeripheralBaseMap,
      FreeGroup.lift_apply_of, Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralForwardFactor]
    simp only [Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralForwardBase, FreeGroup.lift_apply_of]
    have hr := surfaceClosedPeripheral_relator_eq_one w h
    change PresentedGroup.mk _ (FreeGroup.map Sum.inl w) *
        PresentedGroup.mk _ (FreeGroup.map Sum.inr h) = 1 at hr
    change PresentedGroup.mk _ (FreeGroup.map Sum.inr h) =
      (PresentedGroup.mk _ (FreeGroup.map Sum.inl w))⁻¹
    exact eq_inv_of_mul_eq_one_right hr
  · simp [surfaceClosedPeripheralBaseMap, Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralForwardFactor,
      Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralForwardBase]

/-- The map from the actual amalgam to its one-relator presentation. -/
def surfaceClosedPeripheralForward {A B : Type u}
    (w : FreeGroup A) (h : FreeGroup B) :
    Monoid.PushoutI (surfaceClosedPeripheralBaseMap w h) →*
      surfaceClosedPeripheralPresentation w h :=
  Monoid.PushoutI.lift (Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralForwardFactor w h)
    (Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralForwardBase w h)
    (Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralForwardFactor_compatible w h)

def Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralFreeToPushout {A B : Type u}
    (w : FreeGroup A) (h : FreeGroup B) :
    FreeGroup (A ⊕ B) →* Monoid.PushoutI (surfaceClosedPeripheralBaseMap w h) :=
  FreeGroup.lift fun x => match x with
    | Sum.inl a => Monoid.PushoutI.of true (FreeGroup.of a)
    | Sum.inr b => Monoid.PushoutI.of false (FreeGroup.of b)

theorem Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralFreeToPushout_relator_eq_one
    {A B : Type u} (w : FreeGroup A) (h : FreeGroup B) :
    Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralFreeToPushout w h (surfaceClosedPeripheralRelator w h) = 1 := by
  have hbase :=
    (Monoid.PushoutI.of_apply_eq_base (surfaceClosedPeripheralBaseMap w h)
      true (FreeGroup.of ())).trans
      (Monoid.PushoutI.of_apply_eq_base (surfaceClosedPeripheralBaseMap w h)
        false (FreeGroup.of ())).symm
  simp only [surfaceClosedPeripheralBaseMap, FreeGroup.lift_apply_of,
    map_inv] at hbase
  have hleft :
      Monoid.PushoutI.of true w =
        (Monoid.PushoutI.of
          (φ := surfaceClosedPeripheralBaseMap w h) false h)⁻¹ := by
    simpa only [map_inv, inv_inv] using congrArg (fun x : Monoid.PushoutI
      (surfaceClosedPeripheralBaseMap w h) => x⁻¹) hbase
  have hcompLeft :
      (Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralFreeToPushout w h).comp
        (FreeGroup.map (Sum.inl : A → A ⊕ B)) =
      Monoid.PushoutI.of (φ := surfaceClosedPeripheralBaseMap w h) true := by
    apply FreeGroup.ext_hom
    intro a
    simp [Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralFreeToPushout]
  have hcompRight :
      (Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralFreeToPushout w h).comp
        (FreeGroup.map (Sum.inr : B → A ⊕ B)) =
      Monoid.PushoutI.of (φ := surfaceClosedPeripheralBaseMap w h) false := by
    apply FreeGroup.ext_hom
    intro b
    simp [Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralFreeToPushout]
  rw [surfaceClosedPeripheralRelator, map_mul]
  have hw := congrArg (fun f : FreeGroup A →* _ => f w) hcompLeft
  have hh := congrArg (fun f : FreeGroup B →* _ => f h) hcompRight
  change ((Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralFreeToPushout w h).comp
      (FreeGroup.map (Sum.inl : A → A ⊕ B))) w *
    ((Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralFreeToPushout w h).comp
      (FreeGroup.map (Sum.inr : B → A ⊕ B))) h = 1
  rw [hw, hh, hleft]
  exact inv_mul_cancel _

/-- Extend the factor inclusions to a map out of the final presentation. -/
def surfaceClosedPeripheralBackward {A B : Type u}
    (w : FreeGroup A) (h : FreeGroup B) :
    surfaceClosedPeripheralPresentation w h →*
      Monoid.PushoutI (surfaceClosedPeripheralBaseMap w h) :=
  PresentedGroup.toGroup
    (f := fun x => match x with
      | Sum.inl a => Monoid.PushoutI.of true (FreeGroup.of a)
      | Sum.inr b => Monoid.PushoutI.of false (FreeGroup.of b))
    (by
      intro r hr
      have hr' : r = surfaceClosedPeripheralRelator w h := by
        simpa using hr
      subst r
      exact Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralFreeToPushout_relator_eq_one w h)

private theorem surfaceClosedPeripheralBackward_leftGenerator
    {A B : Type u} (w : FreeGroup A) (h : FreeGroup B) (a : A) :
    surfaceClosedPeripheralBackward w h (PresentedGroup.of (Sum.inl a)) =
      Monoid.PushoutI.of (φ := surfaceClosedPeripheralBaseMap w h) true
        (FreeGroup.of a) := by
  simp only [surfaceClosedPeripheralBackward, PresentedGroup.toGroup.of]

private theorem surfaceClosedPeripheralBackward_rightGenerator
    {A B : Type u} (w : FreeGroup A) (h : FreeGroup B) (b : B) :
    surfaceClosedPeripheralBackward w h (PresentedGroup.of (Sum.inr b)) =
      Monoid.PushoutI.of (φ := surfaceClosedPeripheralBaseMap w h) false
        (FreeGroup.of b) := by
  simp only [surfaceClosedPeripheralBackward, PresentedGroup.toGroup.of]

theorem Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheral_backward_forward
    {A B : Type u} (w : FreeGroup A) (h : FreeGroup B) :
    (surfaceClosedPeripheralBackward w h).comp
        (surfaceClosedPeripheralForward w h) = MonoidHom.id _ := by
  apply Monoid.PushoutI.hom_ext_nonempty
  intro b
  cases b
  · apply FreeGroup.ext_hom
    intro x
    change surfaceClosedPeripheralBackward w h
      (PresentedGroup.of (Sum.inr x)) =
        Monoid.PushoutI.of
          (φ := surfaceClosedPeripheralBaseMap w h) false (FreeGroup.of x)
    exact surfaceClosedPeripheralBackward_rightGenerator w h x
  · apply FreeGroup.ext_hom
    intro x
    change surfaceClosedPeripheralBackward w h
      (PresentedGroup.of (Sum.inl x)) =
        Monoid.PushoutI.of
          (φ := surfaceClosedPeripheralBaseMap w h) true (FreeGroup.of x)
    exact surfaceClosedPeripheralBackward_leftGenerator w h x

theorem Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheral_forward_backward
    {A B : Type u} (w : FreeGroup A) (h : FreeGroup B) :
    (surfaceClosedPeripheralForward w h).comp
        (surfaceClosedPeripheralBackward w h) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro x
  cases x with
  | inl a =>
      change surfaceClosedPeripheralForward w h
        (surfaceClosedPeripheralBackward w h (PresentedGroup.of (Sum.inl a))) = _
      rw [surfaceClosedPeripheralBackward_leftGenerator]
      simp [surfaceClosedPeripheralForward, Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralForwardFactor,
        PresentedGroup.of]
  | inr b =>
      change surfaceClosedPeripheralForward w h
        (surfaceClosedPeripheralBackward w h (PresentedGroup.of (Sum.inr b))) = _
      rw [surfaceClosedPeripheralBackward_rightGenerator]
      simp [surfaceClosedPeripheralForward, Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralForwardFactor,
        PresentedGroup.of]

/-- The endpoint amalgam is exactly the quotient by the ordered product of
the prefix and final component words. -/
def surfaceClosedPeripheralAmalgamEquiv {A B : Type u}
    (w : FreeGroup A) (h : FreeGroup B) :
    Monoid.PushoutI (surfaceClosedPeripheralBaseMap w h) ≃*
      surfaceClosedPeripheralPresentation w h where
  toFun := surfaceClosedPeripheralForward w h
  invFun := surfaceClosedPeripheralBackward w h
  left_inv x := congrArg
    (fun f : Monoid.PushoutI (surfaceClosedPeripheralBaseMap w h) →* _ => f x)
    (Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheral_backward_forward w h)
  right_inv x := congrArg
    (fun f : surfaceClosedPeripheralPresentation w h →* _ => f x)
    (Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheral_forward_backward w h)
  map_mul' := (surfaceClosedPeripheralForward w h).map_mul

@[simp]
theorem surfaceClosedPeripheralAmalgamEquiv_left
    {A B : Type u} (w : FreeGroup A) (h : FreeGroup B) (a : A) :
    surfaceClosedPeripheralAmalgamEquiv w h
      (Monoid.PushoutI.of true (FreeGroup.of a)) =
        PresentedGroup.of (Sum.inl a) := by
  simp [surfaceClosedPeripheralAmalgamEquiv, surfaceClosedPeripheralForward,
    Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralForwardFactor, PresentedGroup.of]

@[simp]
theorem surfaceClosedPeripheralAmalgamEquiv_right
    {A B : Type u} (w : FreeGroup A) (h : FreeGroup B) (b : B) :
    surfaceClosedPeripheralAmalgamEquiv w h
      (Monoid.PushoutI.of false (FreeGroup.of b)) =
        PresentedGroup.of (Sum.inr b) := by
  simp [surfaceClosedPeripheralAmalgamEquiv, surfaceClosedPeripheralForward,
    Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralForwardFactor, PresentedGroup.of]

theorem surfaceClosedPeripheralAmalgamEquiv_leftWord
    {A B : Type u} (w : FreeGroup A) (h : FreeGroup B) (x : FreeGroup A) :
    surfaceClosedPeripheralAmalgamEquiv w h
      (Monoid.PushoutI.of true x) =
        PresentedGroup.mk _ (FreeGroup.map (Sum.inl : A → A ⊕ B) x) := by
  simp [surfaceClosedPeripheralAmalgamEquiv, surfaceClosedPeripheralForward,
    Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralForwardFactor]

theorem surfaceClosedPeripheralAmalgamEquiv_rightWord
    {A B : Type u} (w : FreeGroup A) (h : FreeGroup B) (x : FreeGroup B) :
    surfaceClosedPeripheralAmalgamEquiv w h
      (Monoid.PushoutI.of false x) =
        PresentedGroup.mk _ (FreeGroup.map (Sum.inr : B → A ⊕ B) x) := by
  simp [surfaceClosedPeripheralAmalgamEquiv, surfaceClosedPeripheralForward,
    Internal.SurfaceClosedPeripheralAmalgamHelpers.surfaceClosedPeripheralForwardFactor]

#print axioms surfaceClosedPeripheralAmalgamEquiv
#print axioms surfaceClosedPeripheralAmalgamEquiv_left
#print axioms surfaceClosedPeripheralAmalgamEquiv_right
#print axioms surfaceClosedPeripheralAmalgamEquiv_leftWord
#print axioms surfaceClosedPeripheralAmalgamEquiv_rightWord
#print axioms surfaceClosedPeripheralForward
#print axioms surfaceClosedPeripheralBackward

end
end SystolicGrowth
