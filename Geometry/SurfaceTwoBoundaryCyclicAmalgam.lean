module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.GroupTheory.PushoutI
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Tactic.Group

@[expose] public section

/-!
# Eliminate the outgoing boundary in the actual cyclic amalgam

The exterior sends positive boundary winding to the inverse handle word;
the local disk sends it to lower winding times upper winding. Their pushout
is free on the handles and the retained lower boundary. Conjugating the
handle marking gives the ordered physical relation `left * handles * right`.
-/

namespace SystolicGrowth

noncomputable section

/-- Change all groups in a genuine amalgam diagram by compatible group
equivalences. The resulting map preserves each literal factor inclusion. -/
def Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.groupAmalgamDiagramForward
    {ι H K : Type*} {G F : ι → Type*}
    [Group H] [Group K] [∀ i, Group (G i)] [∀ i, Group (F i)]
    (φ : ∀ i, H →* G i) (ψ : ∀ i, K →* F i)
    (eH : H ≃* K) (eG : ∀ i, G i ≃* F i)
    (h : ∀ i, (eG i).toMonoidHom.comp (φ i) = (ψ i).comp eH.toMonoidHom) :
    Monoid.PushoutI φ →* Monoid.PushoutI ψ :=
  Monoid.PushoutI.lift
    (fun i => (Monoid.PushoutI.of i).comp (eG i).toMonoidHom)
    ((Monoid.PushoutI.base ψ).comp eH.toMonoidHom) (by
      intro i
      ext x
      have hx := congrArg (fun f : H →* F i => f x) (h i)
      change eG i (φ i x) = ψ i (eH x) at hx
      change Monoid.PushoutI.of i (eG i (φ i x)) = Monoid.PushoutI.base ψ (eH x)
      rw [hx, Monoid.PushoutI.of_apply_eq_base])

theorem Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.groupAmalgamDiagram_compatible_symm
    {ι H K : Type*} {G F : ι → Type*}
    [Group H] [Group K] [∀ i, Group (G i)] [∀ i, Group (F i)]
    (φ : ∀ i, H →* G i) (ψ : ∀ i, K →* F i)
    (eH : H ≃* K) (eG : ∀ i, G i ≃* F i)
    (h : ∀ i, (eG i).toMonoidHom.comp (φ i) = (ψ i).comp eH.toMonoidHom) :
    ∀ i, (eG i).symm.toMonoidHom.comp (ψ i) =
      (φ i).comp eH.symm.toMonoidHom := by
  intro i
  ext x
  apply (eG i).injective
  have hx := congrArg (fun f : H →* F i => f (eH.symm x)) (h i)
  simpa using hx.symm

theorem Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.groupAmalgamDiagramForward_inverse
    {ι H K : Type*} {G F : ι → Type*}
    [Group H] [Group K] [∀ i, Group (G i)] [∀ i, Group (F i)]
    (φ : ∀ i, H →* G i) (ψ : ∀ i, K →* F i)
    (eH : H ≃* K) (eG : ∀ i, G i ≃* F i)
    (h : ∀ i, (eG i).toMonoidHom.comp (φ i) = (ψ i).comp eH.toMonoidHom) :
    (Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.groupAmalgamDiagramForward ψ φ eH.symm (fun i => (eG i).symm)
      (Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.groupAmalgamDiagram_compatible_symm φ ψ eH eG h)).comp
        (Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.groupAmalgamDiagramForward φ ψ eH eG h) = MonoidHom.id _ := by
  apply Monoid.PushoutI.hom_ext
  · intro i
    ext x
    simp [Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.groupAmalgamDiagramForward]
  · ext x
    simp [Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.groupAmalgamDiagramForward]

/-- The compatible equivalences of the overlap and both actual factors
induce an equivalence of their full based amalgams. -/
def groupAmalgamDiagramEquiv
    {ι H K : Type*} {G F : ι → Type*}
    [Group H] [Group K] [∀ i, Group (G i)] [∀ i, Group (F i)]
    (φ : ∀ i, H →* G i) (ψ : ∀ i, K →* F i)
    (eH : H ≃* K) (eG : ∀ i, G i ≃* F i)
    (h : ∀ i, (eG i).toMonoidHom.comp (φ i) = (ψ i).comp eH.toMonoidHom) :
    Monoid.PushoutI φ ≃* Monoid.PushoutI ψ where
  toFun := Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.groupAmalgamDiagramForward φ ψ eH eG h
  invFun := Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.groupAmalgamDiagramForward ψ φ eH.symm (fun i => (eG i).symm)
    (Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.groupAmalgamDiagram_compatible_symm φ ψ eH eG h)
  left_inv x := congrArg (fun f : Monoid.PushoutI φ →* _ => f x)
    (Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.groupAmalgamDiagramForward_inverse φ ψ eH eG h)
  right_inv x := congrArg (fun f : Monoid.PushoutI ψ →* _ => f x)
    (Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.groupAmalgamDiagramForward_inverse ψ φ eH.symm (fun i => (eG i).symm)
      (Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.groupAmalgamDiagram_compatible_symm φ ψ eH eG h))
  map_mul' := (Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.groupAmalgamDiagramForward φ ψ eH eG h).map_mul

/-- For a genuine cyclic overlap, checking the one positive generator
establishes the entire diagram compatibility needed for the amalgam map. -/
theorem groupAmalgamDiagram_compatible_of_freeUnit
    {ι H : Type*} {G F : ι → Type*}
    [Group H] [∀ i, Group (G i)] [∀ i, Group (F i)]
    (φ : ∀ i, H →* G i) (ψ : ∀ i, FreeGroup Unit →* F i)
    (eH : H ≃* FreeGroup Unit) (eG : ∀ i, G i ≃* F i)
    (h : ∀ i, eG i (φ i (eH.symm (FreeGroup.of ()))) = ψ i (FreeGroup.of ())) :
    ∀ i, (eG i).toMonoidHom.comp (φ i) = (ψ i).comp eH.toMonoidHom := by
  intro i
  have heq : ((eG i).toMonoidHom.comp (φ i)).comp eH.symm.toMonoidHom = ψ i := by
    apply FreeGroup.lift.symm.injective
    funext u
    cases u
    exact h i
  ext x
  have hx := congrArg (fun f : FreeGroup Unit →* F i => f (eH x)) heq
  simpa using hx

@[simp]
theorem groupAmalgamDiagramEquiv_of
    {ι H K : Type*} {G F : ι → Type*}
    [Group H] [Group K] [∀ i, Group (G i)] [∀ i, Group (F i)]
    (φ : ∀ i, H →* G i) (ψ : ∀ i, K →* F i)
    (eH : H ≃* K) (eG : ∀ i, G i ≃* F i)
    (h : ∀ i, (eG i).toMonoidHom.comp (φ i) = (ψ i).comp eH.toMonoidHom)
    (i : ι) (x : G i) :
    groupAmalgamDiagramEquiv φ ψ eH eG h (Monoid.PushoutI.of i x) =
      Monoid.PushoutI.of i (eG i x) := by
  simp [groupAmalgamDiagramEquiv, Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.groupAmalgamDiagramForward]

/-- Exterior handles (`true`) and the two literal local disk letters (`false`). -/
abbrev surfaceTwoBoundaryCyclicFactor (A : Type) : Bool → Type
  | true => FreeGroup A
  | false => FreeGroup Bool

@[reducible]
instance {A : Type} (b : Bool) : Group (surfaceTwoBoundaryCyclicFactor A b) :=
  match b with
  | true => inferInstance
  | false => inferInstance

/-- The common positive circle maps to the inverse exterior word and the
ordered lower/upper local word. -/
def surfaceTwoBoundaryCyclicBaseMap {A : Type} (w : FreeGroup A)
    (b : Bool) : FreeGroup Unit →* surfaceTwoBoundaryCyclicFactor A b :=
  match b with
  | true => FreeGroup.lift (fun _ => w⁻¹)
  | false => FreeGroup.lift (fun _ => FreeGroup.of true * FreeGroup.of false)

/-- Include all handles with the one common conjugation required by the
ordered physical peripheral relation. -/
def surfaceTwoBoundaryCyclicHandleMap (A : Type) :
    FreeGroup A →* FreeGroup (A ⊕ Unit) where
  toFun h := FreeGroup.of (Sum.inr ()) * FreeGroup.map Sum.inl h *
    (FreeGroup.of (Sum.inr ()))⁻¹
  map_one' := by simp
  map_mul' h k := by simp [mul_assoc]

def surfaceTwoBoundaryCyclicForwardFactor {A : Type} (w : FreeGroup A)
    (b : Bool) : surfaceTwoBoundaryCyclicFactor A b →* FreeGroup (A ⊕ Unit) :=
  match b with
  | true => surfaceTwoBoundaryCyclicHandleMap A
  | false => FreeGroup.lift (fun b => if b then FreeGroup.of (Sum.inr ()) else
      (FreeGroup.of (Sum.inr ()) * FreeGroup.map Sum.inl w)⁻¹)

theorem Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.surfaceTwoBoundaryCyclicForwardFactor_compatible
    {A : Type} (w : FreeGroup A) (b : Bool) :
    (surfaceTwoBoundaryCyclicForwardFactor w b).comp
        (surfaceTwoBoundaryCyclicBaseMap w b) =
      FreeGroup.lift (fun _ : Unit =>
        surfaceTwoBoundaryCyclicHandleMap A (w⁻¹)) := by
  apply FreeGroup.lift.symm.injective
  funext a
  cases a
  change ((surfaceTwoBoundaryCyclicForwardFactor w b).comp
    (surfaceTwoBoundaryCyclicBaseMap w b)) (FreeGroup.of ()) = _
  cases b <;> simp [surfaceTwoBoundaryCyclicForwardFactor,
    surfaceTwoBoundaryCyclicBaseMap, surfaceTwoBoundaryCyclicHandleMap, mul_assoc]

def surfaceTwoBoundaryCyclicForward {A : Type} (w : FreeGroup A) :
    Monoid.PushoutI (surfaceTwoBoundaryCyclicBaseMap w) →* FreeGroup (A ⊕ Unit) :=
  Monoid.PushoutI.lift (surfaceTwoBoundaryCyclicForwardFactor w)
    (FreeGroup.lift (fun _ : Unit => surfaceTwoBoundaryCyclicHandleMap A (w⁻¹)))
    (Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.surfaceTwoBoundaryCyclicForwardFactor_compatible w)

/-- The retained lower boundary is the literal local factor generator. -/
def surfaceTwoBoundaryCyclicLower {A : Type} (w : FreeGroup A) :
    Monoid.PushoutI (surfaceTwoBoundaryCyclicBaseMap w) :=
  Monoid.PushoutI.of false (FreeGroup.of true)

def surfaceTwoBoundaryCyclicBackward {A : Type} (w : FreeGroup A) :
    FreeGroup (A ⊕ Unit) →* Monoid.PushoutI (surfaceTwoBoundaryCyclicBaseMap w) :=
  FreeGroup.lift (fun x => match x with
    | Sum.inl a => (surfaceTwoBoundaryCyclicLower w)⁻¹ *
        Monoid.PushoutI.of true (FreeGroup.of a) * surfaceTwoBoundaryCyclicLower w
    | Sum.inr _ => surfaceTwoBoundaryCyclicLower w)

def Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.surfaceTwoBoundaryCyclicBackwardHandles {A : Type} (w : FreeGroup A) :
    FreeGroup A →* Monoid.PushoutI (surfaceTwoBoundaryCyclicBaseMap w) where
  toFun h := (surfaceTwoBoundaryCyclicLower w)⁻¹ *
    Monoid.PushoutI.of true h * surfaceTwoBoundaryCyclicLower w
  map_one' := by simp
  map_mul' h k := by simp [mul_assoc]

private theorem surfaceTwoBoundaryCyclicBackward_include {A : Type} (w : FreeGroup A) :
    (surfaceTwoBoundaryCyclicBackward w).comp (FreeGroup.map Sum.inl) =
      Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.surfaceTwoBoundaryCyclicBackwardHandles w := by
  apply FreeGroup.lift.symm.injective
  funext a
  simp [surfaceTwoBoundaryCyclicBackward, Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.surfaceTwoBoundaryCyclicBackwardHandles]

private theorem surfaceTwoBoundaryCyclicBackward_forwardFactor
    {A : Type} (w : FreeGroup A) (b : Bool) :
    (surfaceTwoBoundaryCyclicBackward w).comp
        (surfaceTwoBoundaryCyclicForwardFactor w b) = Monoid.PushoutI.of b := by
  have hhandles (h : FreeGroup A) :
      surfaceTwoBoundaryCyclicBackward w (FreeGroup.map Sum.inl h) =
        (surfaceTwoBoundaryCyclicLower w)⁻¹ * Monoid.PushoutI.of true h *
          surfaceTwoBoundaryCyclicLower w :=
    congrArg (fun f : FreeGroup A →* _ => f h) (surfaceTwoBoundaryCyclicBackward_include w)
  cases b
  · apply FreeGroup.lift.symm.injective
    funext b
    change surfaceTwoBoundaryCyclicBackward w
      (surfaceTwoBoundaryCyclicForwardFactor w false (FreeGroup.of b)) =
        Monoid.PushoutI.of false (FreeGroup.of b)
    cases b
    · have hbase :=
        (Monoid.PushoutI.of_apply_eq_base (surfaceTwoBoundaryCyclicBaseMap w)
          true (FreeGroup.of ())).trans
        (Monoid.PushoutI.of_apply_eq_base (surfaceTwoBoundaryCyclicBaseMap w)
          false (FreeGroup.of ())).symm
      simp only [surfaceTwoBoundaryCyclicBaseMap, FreeGroup.lift_apply_of, map_inv,
        map_mul] at hbase
      simp only [surfaceTwoBoundaryCyclicForwardFactor,
        FreeGroup.lift_apply_of, Bool.false_eq_true, if_false, map_inv, map_mul]
      rw [hhandles]
      simp only [surfaceTwoBoundaryCyclicBackward, FreeGroup.lift_apply_of]
      change (surfaceTwoBoundaryCyclicLower w *
        ((surfaceTwoBoundaryCyclicLower w)⁻¹ * Monoid.PushoutI.of true w *
          surfaceTwoBoundaryCyclicLower w))⁻¹ = Monoid.PushoutI.of false (FreeGroup.of false)
      calc
        _ = (surfaceTwoBoundaryCyclicLower w)⁻¹ * (Monoid.PushoutI.of true w)⁻¹ := by
          group
        _ = Monoid.PushoutI.of false (FreeGroup.of false) := by
          rw [hbase]
          simp [surfaceTwoBoundaryCyclicLower]
    · simp [surfaceTwoBoundaryCyclicForwardFactor, surfaceTwoBoundaryCyclicBackward,
        surfaceTwoBoundaryCyclicLower]
  · apply DFunLike.ext
    intro h
    change surfaceTwoBoundaryCyclicBackward w
      (FreeGroup.of (Sum.inr ()) * FreeGroup.map Sum.inl h *
        (FreeGroup.of (Sum.inr ()))⁻¹) = Monoid.PushoutI.of true h
    simp only [map_mul, map_inv]
    rw [hhandles]
    simp [surfaceTwoBoundaryCyclicBackward, mul_assoc]

theorem Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.surfaceTwoBoundaryCyclicBackward_forward {A : Type} (w : FreeGroup A) :
    (surfaceTwoBoundaryCyclicBackward w).comp (surfaceTwoBoundaryCyclicForward w) =
      MonoidHom.id _ := by
  apply Monoid.PushoutI.hom_ext_nonempty
  intro b
  ext h
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply,
    surfaceTwoBoundaryCyclicForward, Monoid.PushoutI.lift_of]
  exact congrArg (fun f : surfaceTwoBoundaryCyclicFactor A b →* _ => f h)
    (surfaceTwoBoundaryCyclicBackward_forwardFactor w b)

theorem Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.surfaceTwoBoundaryCyclicForward_backward {A : Type} (w : FreeGroup A) :
    (surfaceTwoBoundaryCyclicForward w).comp (surfaceTwoBoundaryCyclicBackward w) =
      MonoidHom.id _ := by
  apply FreeGroup.lift.symm.injective
  funext x
  cases x with
  | inl a =>
      simp [surfaceTwoBoundaryCyclicBackward, surfaceTwoBoundaryCyclicForward,
        surfaceTwoBoundaryCyclicForwardFactor, surfaceTwoBoundaryCyclicLower,
        surfaceTwoBoundaryCyclicHandleMap, mul_assoc]
  | inr a =>
      cases a
      simp [surfaceTwoBoundaryCyclicBackward, surfaceTwoBoundaryCyclicForward,
        surfaceTwoBoundaryCyclicForwardFactor, surfaceTwoBoundaryCyclicLower]

/-- The literal cyclic amalgam is free on the handles and the retained
positive incoming boundary, with no injected presentation assumption. -/
def surfaceTwoBoundaryCyclicAmalgamEquiv {A : Type} (w : FreeGroup A) :
    Monoid.PushoutI (surfaceTwoBoundaryCyclicBaseMap w) ≃* FreeGroup (A ⊕ Unit) where
  toFun := surfaceTwoBoundaryCyclicForward w
  invFun := surfaceTwoBoundaryCyclicBackward w
  left_inv x := congrArg (fun f : Monoid.PushoutI (surfaceTwoBoundaryCyclicBaseMap w) →* _ => f x)
    (Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.surfaceTwoBoundaryCyclicBackward_forward w)
  right_inv x := congrArg (fun f : FreeGroup (A ⊕ Unit) →* _ => f x)
    (Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.surfaceTwoBoundaryCyclicForward_backward w)
  map_mul' := (surfaceTwoBoundaryCyclicForward w).map_mul

theorem surfaceTwoBoundaryCyclicAmalgamEquiv_lower {A : Type} (w : FreeGroup A) :
    surfaceTwoBoundaryCyclicAmalgamEquiv w
      (Monoid.PushoutI.of false (FreeGroup.of true)) = FreeGroup.of (Sum.inr ()) := by
  simp [surfaceTwoBoundaryCyclicAmalgamEquiv, surfaceTwoBoundaryCyclicForward,
    surfaceTwoBoundaryCyclicForwardFactor]

theorem surfaceTwoBoundaryCyclicAmalgamEquiv_upper {A : Type} (w : FreeGroup A) :
    surfaceTwoBoundaryCyclicAmalgamEquiv w
      (Monoid.PushoutI.of false (FreeGroup.of false)) =
        (FreeGroup.of (Sum.inr ()) * FreeGroup.map Sum.inl w)⁻¹ := by
  simp [surfaceTwoBoundaryCyclicAmalgamEquiv, surfaceTwoBoundaryCyclicForward,
    surfaceTwoBoundaryCyclicForwardFactor]

/-- The exterior factor's handle marking is conjugated once by the retained
positive lower boundary, preserving the same ordered peripheral relation. -/
theorem surfaceTwoBoundaryCyclicAmalgamEquiv_exterior
    {A : Type} (w h : FreeGroup A) :
    surfaceTwoBoundaryCyclicAmalgamEquiv w (Monoid.PushoutI.of true h) =
      FreeGroup.of (Sum.inr ()) * FreeGroup.map Sum.inl h *
        (FreeGroup.of (Sum.inr ()))⁻¹ := by
  simp [surfaceTwoBoundaryCyclicAmalgamEquiv, surfaceTwoBoundaryCyclicForward,
    surfaceTwoBoundaryCyclicForwardFactor, surfaceTwoBoundaryCyclicHandleMap]

/-- Retain the upper puncture when the actual incoming center has the larger
imaginary coordinate. No ordering of the original two centers is assumed. -/
def surfaceTwoBoundaryCyclicUpperForwardFactor {A : Type} (w : FreeGroup A)
    (b : Bool) : surfaceTwoBoundaryCyclicFactor A b →* FreeGroup (A ⊕ Unit) :=
  match b with
  | true => FreeGroup.map Sum.inl
  | false => FreeGroup.lift (fun b => if b then
      (FreeGroup.map Sum.inl w)⁻¹ * (FreeGroup.of (Sum.inr ()))⁻¹
      else FreeGroup.of (Sum.inr ()))

theorem Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.surfaceTwoBoundaryCyclicUpperForwardFactor_compatible
    {A : Type} (w : FreeGroup A) (b : Bool) :
    (surfaceTwoBoundaryCyclicUpperForwardFactor w b).comp
        (surfaceTwoBoundaryCyclicBaseMap w b) =
      FreeGroup.lift (fun _ : Unit => (FreeGroup.map Sum.inl w)⁻¹) := by
  apply FreeGroup.lift.symm.injective
  funext u
  cases u
  change ((surfaceTwoBoundaryCyclicUpperForwardFactor w b).comp
    (surfaceTwoBoundaryCyclicBaseMap w b)) (FreeGroup.of ()) = _
  cases b <;> simp [surfaceTwoBoundaryCyclicUpperForwardFactor,
    surfaceTwoBoundaryCyclicBaseMap, mul_assoc]

def surfaceTwoBoundaryCyclicUpperForward {A : Type} (w : FreeGroup A) :
    Monoid.PushoutI (surfaceTwoBoundaryCyclicBaseMap w) →* FreeGroup (A ⊕ Unit) :=
  Monoid.PushoutI.lift (surfaceTwoBoundaryCyclicUpperForwardFactor w)
    (FreeGroup.lift (fun _ : Unit => (FreeGroup.map Sum.inl w)⁻¹))
    (Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.surfaceTwoBoundaryCyclicUpperForwardFactor_compatible w)

def surfaceTwoBoundaryCyclicUpperBackward {A : Type} (w : FreeGroup A) :
    FreeGroup (A ⊕ Unit) →* Monoid.PushoutI (surfaceTwoBoundaryCyclicBaseMap w) :=
  FreeGroup.lift (fun x => match x with
    | Sum.inl a => Monoid.PushoutI.of true (FreeGroup.of a)
    | Sum.inr _ => Monoid.PushoutI.of false (FreeGroup.of false))

private theorem surfaceTwoBoundaryCyclicUpperBackward_include
    {A : Type} (w : FreeGroup A) :
    (surfaceTwoBoundaryCyclicUpperBackward w).comp (FreeGroup.map Sum.inl) =
      Monoid.PushoutI.of (φ := surfaceTwoBoundaryCyclicBaseMap w) true := by
  apply FreeGroup.lift.symm.injective
  funext a
  simp [surfaceTwoBoundaryCyclicUpperBackward]

private theorem surfaceTwoBoundaryCyclicUpperBackward_forwardFactor
    {A : Type} (w : FreeGroup A) (b : Bool) :
    (surfaceTwoBoundaryCyclicUpperBackward w).comp
        (surfaceTwoBoundaryCyclicUpperForwardFactor w b) = Monoid.PushoutI.of b := by
  have hhandles (h : FreeGroup A) :
      surfaceTwoBoundaryCyclicUpperBackward w (FreeGroup.map Sum.inl h) =
        Monoid.PushoutI.of true h :=
    congrArg (fun f : FreeGroup A →* _ => f h)
      (surfaceTwoBoundaryCyclicUpperBackward_include w)
  cases b
  · apply FreeGroup.lift.symm.injective
    funext b
    change surfaceTwoBoundaryCyclicUpperBackward w
      (surfaceTwoBoundaryCyclicUpperForwardFactor w false (FreeGroup.of b)) =
        Monoid.PushoutI.of false (FreeGroup.of b)
    cases b
    · simp [surfaceTwoBoundaryCyclicUpperForwardFactor,
        surfaceTwoBoundaryCyclicUpperBackward]
    · have hbase :=
        (Monoid.PushoutI.of_apply_eq_base (surfaceTwoBoundaryCyclicBaseMap w)
          true (FreeGroup.of ())).trans
        (Monoid.PushoutI.of_apply_eq_base (surfaceTwoBoundaryCyclicBaseMap w)
          false (FreeGroup.of ())).symm
      simp only [surfaceTwoBoundaryCyclicBaseMap, FreeGroup.lift_apply_of,
        map_inv, map_mul] at hbase
      simp only [surfaceTwoBoundaryCyclicUpperForwardFactor, FreeGroup.lift_apply_of,
        ite_true]
      change surfaceTwoBoundaryCyclicUpperBackward w
        ((FreeGroup.map Sum.inl w)⁻¹ * (FreeGroup.of (Sum.inr ()))⁻¹) =
          Monoid.PushoutI.of false (FreeGroup.of true)
      simp only [map_mul, map_inv]
      rw [hhandles]
      simp only [surfaceTwoBoundaryCyclicUpperBackward, FreeGroup.lift_apply_of]
      rw [hbase]
      simp [mul_assoc]
  · exact surfaceTwoBoundaryCyclicUpperBackward_include w

theorem Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.surfaceTwoBoundaryCyclicUpperBackward_forward
    {A : Type} (w : FreeGroup A) :
    (surfaceTwoBoundaryCyclicUpperBackward w).comp
        (surfaceTwoBoundaryCyclicUpperForward w) = MonoidHom.id _ := by
  apply Monoid.PushoutI.hom_ext_nonempty
  intro b
  ext h
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply,
    surfaceTwoBoundaryCyclicUpperForward, Monoid.PushoutI.lift_of]
  exact congrArg (fun f : surfaceTwoBoundaryCyclicFactor A b →* _ => f h)
    (surfaceTwoBoundaryCyclicUpperBackward_forwardFactor w b)

theorem Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.surfaceTwoBoundaryCyclicUpperForward_backward
    {A : Type} (w : FreeGroup A) :
    (surfaceTwoBoundaryCyclicUpperForward w).comp
        (surfaceTwoBoundaryCyclicUpperBackward w) = MonoidHom.id _ := by
  apply FreeGroup.lift.symm.injective
  funext x
  cases x with
  | inl a =>
      simp [surfaceTwoBoundaryCyclicUpperBackward, surfaceTwoBoundaryCyclicUpperForward,
        surfaceTwoBoundaryCyclicUpperForwardFactor]
  | inr a =>
      cases a
      simp [surfaceTwoBoundaryCyclicUpperBackward, surfaceTwoBoundaryCyclicUpperForward,
        surfaceTwoBoundaryCyclicUpperForwardFactor]

/-- The same actual cyclic amalgam, freely marked by the handles and the
positive upper puncture. This covers the other actual center ordering. -/
def surfaceTwoBoundaryCyclicUpperAmalgamEquiv {A : Type} (w : FreeGroup A) :
    Monoid.PushoutI (surfaceTwoBoundaryCyclicBaseMap w) ≃* FreeGroup (A ⊕ Unit) where
  toFun := surfaceTwoBoundaryCyclicUpperForward w
  invFun := surfaceTwoBoundaryCyclicUpperBackward w
  left_inv x := congrArg
    (fun f : Monoid.PushoutI (surfaceTwoBoundaryCyclicBaseMap w) →* _ => f x)
    (Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.surfaceTwoBoundaryCyclicUpperBackward_forward w)
  right_inv x := congrArg (fun f : FreeGroup (A ⊕ Unit) →* _ => f x)
    (Internal.SurfaceTwoBoundaryCyclicAmalgamHelpers.surfaceTwoBoundaryCyclicUpperForward_backward w)
  map_mul' := (surfaceTwoBoundaryCyclicUpperForward w).map_mul

theorem surfaceTwoBoundaryCyclicUpperAmalgamEquiv_upper {A : Type} (w : FreeGroup A) :
    surfaceTwoBoundaryCyclicUpperAmalgamEquiv w
      (Monoid.PushoutI.of false (FreeGroup.of false)) = FreeGroup.of (Sum.inr ()) := by
  simp [surfaceTwoBoundaryCyclicUpperAmalgamEquiv, surfaceTwoBoundaryCyclicUpperForward,
    surfaceTwoBoundaryCyclicUpperForwardFactor]

theorem surfaceTwoBoundaryCyclicUpperAmalgamEquiv_lower {A : Type} (w : FreeGroup A) :
    surfaceTwoBoundaryCyclicUpperAmalgamEquiv w
      (Monoid.PushoutI.of false (FreeGroup.of true)) =
        (FreeGroup.of (Sum.inr ()) * FreeGroup.map Sum.inl w)⁻¹ := by
  simp [surfaceTwoBoundaryCyclicUpperAmalgamEquiv, surfaceTwoBoundaryCyclicUpperForward,
    surfaceTwoBoundaryCyclicUpperForwardFactor]

theorem surfaceTwoBoundaryCyclicUpperAmalgamEquiv_exterior
    {A : Type} (w h : FreeGroup A) :
    surfaceTwoBoundaryCyclicUpperAmalgamEquiv w (Monoid.PushoutI.of true h) =
      FreeGroup.map Sum.inl h := by
  simp [surfaceTwoBoundaryCyclicUpperAmalgamEquiv, surfaceTwoBoundaryCyclicUpperForward,
    surfaceTwoBoundaryCyclicUpperForwardFactor]

#print axioms groupAmalgamDiagramEquiv
#print axioms groupAmalgamDiagramEquiv_of
#print axioms groupAmalgamDiagram_compatible_of_freeUnit
#print axioms surfaceTwoBoundaryCyclicAmalgamEquiv
#print axioms surfaceTwoBoundaryCyclicAmalgamEquiv_lower
#print axioms surfaceTwoBoundaryCyclicAmalgamEquiv_upper
#print axioms surfaceTwoBoundaryCyclicAmalgamEquiv_exterior
#print axioms surfaceTwoBoundaryCyclicUpperAmalgamEquiv
#print axioms surfaceTwoBoundaryCyclicUpperAmalgamEquiv_upper
#print axioms surfaceTwoBoundaryCyclicUpperAmalgamEquiv_lower
#print axioms surfaceTwoBoundaryCyclicUpperAmalgamEquiv_exterior

end
end SystolicGrowth
