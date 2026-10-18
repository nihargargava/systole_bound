module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.CategoryTheory.SingleObj
public import Vendored.ClassicalVanKampen.ClassicalSVK.Pushout

@[expose] public section

/-!
# Groupoid descent for two possibly disconnected open sets

The actual classical van Kampen pushout supplies a chosen functor with exact
restrictions and uniqueness. No component is required to be connected and no
basepoint is chosen in the overlap. The based homomorphism at any ambient point
uses Mathlib's reversed categorical composition convention.
-/

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

namespace SystolicGrowth

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The literal inclusion of the overlap into the first open set. -/
def twoOpenCoverOverlapLeft (U V : Set X) : C(↥(U ∩ V), U) where
  toFun x := ⟨x.1, x.2.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The literal inclusion of the overlap into the second open set. -/
def twoOpenCoverOverlapRight (U V : Set X) : C(↥(U ∩ V), V) where
  toFun x := ⟨x.1, x.2.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The literal subtype inclusion into the original ambient space. -/
def twoOpenCoverInclusion (U : Set X) : C(U, X) where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val

section GeneralTarget

variable {C : Type} [Category.{0} C] {U V : Set X}
  (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
  (FU : FundamentalGroupoid U ⥤ C) (FV : FundamentalGroupoid V ⥤ C)
  (hcompat : FundamentalGroupoid.map (twoOpenCoverOverlapLeft U V) ⋙ FU =
    FundamentalGroupoid.map (twoOpenCoverOverlapRight U V) ⋙ FV)

include hcompat in
theorem Internal.TwoOpenCoverGroupoidDescentHelpers.twoOpenCoverCompatibleCat :
    (FundamentalGroupoid.map (twoOpenCoverOverlapLeft U V)).toCatHom ≫ FU.toCatHom =
      (FundamentalGroupoid.map (twoOpenCoverOverlapRight U V)).toCatHom ≫ FV.toCatHom := by
  apply Cat.ext
  exact hcompat

/-- The chosen descendant of compatible functors on an actual two-open cover.
The construction is the descendant of the proved fundamental-groupoid pushout. -/
def twoOpenCoverGroupoidDesc : FundamentalGroupoid X ⥤ C :=
  ((Vendored.ClassicalVanKampen.ClassicalSVK.classicalOpenCoverPushout
    U V hU hV hcover).desc FU.toCatHom FV.toCatHom
      (Internal.TwoOpenCoverGroupoidDescentHelpers.twoOpenCoverCompatibleCat FU FV hcompat)).toFunctor

/-- Descent restricts exactly, not merely up to natural isomorphism, on the first side. -/
theorem twoOpenCoverGroupoidDesc_comp_left :
    FundamentalGroupoid.map (twoOpenCoverInclusion U) ⋙
        twoOpenCoverGroupoidDesc hU hV hcover FU FV hcompat = FU := by
  exact congrArg Cat.Hom.toFunctor
    ((Vendored.ClassicalVanKampen.ClassicalSVK.classicalOpenCoverPushout
      U V hU hV hcover).inl_desc FU.toCatHom FV.toCatHom
        (Internal.TwoOpenCoverGroupoidDescentHelpers.twoOpenCoverCompatibleCat FU FV hcompat))

/-- Descent restricts exactly on the second side. -/
theorem twoOpenCoverGroupoidDesc_comp_right :
    FundamentalGroupoid.map (twoOpenCoverInclusion V) ⋙
        twoOpenCoverGroupoidDesc hU hV hcover FU FV hcompat = FV := by
  exact congrArg Cat.Hom.toFunctor
    ((Vendored.ClassicalVanKampen.ClassicalSVK.classicalOpenCoverPushout
      U V hU hV hcover).inr_desc FU.toCatHom FV.toCatHom
        (Internal.TwoOpenCoverGroupoidDescentHelpers.twoOpenCoverCompatibleCat FU FV hcompat))

include hU hV hcover in
/-- A functor on the ambient groupoid is determined by its two exact restrictions. -/
theorem twoOpenCoverGroupoid_ext (F G : FundamentalGroupoid X ⥤ C)
    (hleft : FundamentalGroupoid.map (twoOpenCoverInclusion U) ⋙ F =
      FundamentalGroupoid.map (twoOpenCoverInclusion U) ⋙ G)
    (hright : FundamentalGroupoid.map (twoOpenCoverInclusion V) ⋙ F =
      FundamentalGroupoid.map (twoOpenCoverInclusion V) ⋙ G) : F = G := by
  have hcat : F.toCatHom = G.toCatHom :=
    (Vendored.ClassicalVanKampen.ClassicalSVK.classicalOpenCoverPushout
      U V hU hV hcover).hom_ext
        (by apply Cat.ext; exact hleft) (by apply Cat.ext; exact hright)
  exact congrArg Cat.Hom.toFunctor hcat

/-- Every functor with the specified restrictions equals the chosen descendant. -/
theorem twoOpenCoverGroupoidDesc_unique (F : FundamentalGroupoid X ⥤ C)
    (hleft : FundamentalGroupoid.map (twoOpenCoverInclusion U) ⋙ F = FU)
    (hright : FundamentalGroupoid.map (twoOpenCoverInclusion V) ⋙ F = FV) :
    F = twoOpenCoverGroupoidDesc hU hV hcover FU FV hcompat := by
  apply twoOpenCoverGroupoid_ext hU hV hcover
  · exact hleft.trans (twoOpenCoverGroupoidDesc_comp_left hU hV hcover FU FV hcompat).symm
  · exact hright.trans (twoOpenCoverGroupoidDesc_comp_right hU hV hcover FU FV hcompat).symm

end GeneralTarget

section SingleObjectTarget

variable {H : Type} [Group H]

/-- Evaluate a single-object-valued groupoid functor on loops at an arbitrary point. -/
def fundamentalGroupoidFunctorHom (F : FundamentalGroupoid X ⥤ SingleObj H) (x : X) :
    FundamentalGroup X x →* H where
  toFun γ := F.map γ
  map_one' := F.map_id (FundamentalGroupoid.mk x)
  map_mul' γ δ := F.map_comp δ γ

@[simp]
theorem fundamentalGroupoidFunctorHom_apply
    (F : FundamentalGroupoid X ⥤ SingleObj H) (x : X) (γ : FundamentalGroup X x) :
    fundamentalGroupoidFunctorHom F x γ = F.map γ := rfl

variable {U V : Set X}
  (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
  (FU : FundamentalGroupoid U ⥤ SingleObj H)
  (FV : FundamentalGroupoid V ⥤ SingleObj H)
  (hcompat : FundamentalGroupoid.map (twoOpenCoverOverlapLeft U V) ⋙ FU =
    FundamentalGroupoid.map (twoOpenCoverOverlapRight U V) ⋙ FV)

/-- Literal evaluation of the descendant on any first-side morphism. -/
theorem twoOpenCoverGroupoidDesc_map_left
    {a b : FundamentalGroupoid U} (γ : a ⟶ b) :
    (twoOpenCoverGroupoidDesc hU hV hcover FU FV hcompat).map
        ((FundamentalGroupoid.map (twoOpenCoverInclusion U)).map γ) = FU.map γ := by
  exact congrArg (fun F : FundamentalGroupoid U ⥤ SingleObj H => (F.map γ : H))
    (twoOpenCoverGroupoidDesc_comp_left hU hV hcover FU FV hcompat)

/-- Literal evaluation of the descendant on any second-side morphism. -/
theorem twoOpenCoverGroupoidDesc_map_right
    {a b : FundamentalGroupoid V} (γ : a ⟶ b) :
    (twoOpenCoverGroupoidDesc hU hV hcover FU FV hcompat).map
        ((FundamentalGroupoid.map (twoOpenCoverInclusion V)).map γ) = FV.map γ := by
  exact congrArg (fun F : FundamentalGroupoid V ⥤ SingleObj H => (F.map γ : H))
    (twoOpenCoverGroupoidDesc_comp_right hU hV hcover FU FV hcompat)

/-- The actual descended based homomorphism at any ambient point, including points
outside the overlap. -/
def twoOpenCoverGroupHom (x : X) : FundamentalGroup X x →* H :=
  fundamentalGroupoidFunctorHom
    (twoOpenCoverGroupoidDesc hU hV hcover FU FV hcompat) x

@[simp]
theorem twoOpenCoverGroupHom_apply (x : X) (γ : FundamentalGroup X x) :
    twoOpenCoverGroupHom hU hV hcover FU FV hcompat x γ =
      (twoOpenCoverGroupoidDesc hU hV hcover FU FV hcompat).map γ := rfl

/-- The based descendant preserves the first-side loop map at every first-side point. -/
theorem twoOpenCoverGroupHom_comp_left (x : U) :
    (twoOpenCoverGroupHom hU hV hcover FU FV hcompat x.1).comp
        (FundamentalGroup.map (twoOpenCoverInclusion U) x) =
      fundamentalGroupoidFunctorHom FU x := by
  ext γ
  exact twoOpenCoverGroupoidDesc_map_left hU hV hcover FU FV hcompat γ

/-- The based descendant preserves the second-side loop map at every second-side point. -/
theorem twoOpenCoverGroupHom_comp_right (x : V) :
    (twoOpenCoverGroupHom hU hV hcover FU FV hcompat x.1).comp
        (FundamentalGroup.map (twoOpenCoverInclusion V) x) =
      fundamentalGroupoidFunctorHom FV x := by
  ext γ
  exact twoOpenCoverGroupoidDesc_map_right hU hV hcover FU FV hcompat γ

/-- The based consumer of uniqueness retains any prescribed ambient loop functor. -/
theorem twoOpenCoverGroupHom_eq (F : FundamentalGroupoid X ⥤ SingleObj H)
    (hleft : FundamentalGroupoid.map (twoOpenCoverInclusion U) ⋙ F = FU)
    (hright : FundamentalGroupoid.map (twoOpenCoverInclusion V) ⋙ F = FV) (x : X) :
    twoOpenCoverGroupHom hU hV hcover FU FV hcompat x =
      fundamentalGroupoidFunctorHom F x := by
  rw [twoOpenCoverGroupHom, ← twoOpenCoverGroupoidDesc_unique hU hV hcover FU FV hcompat
    F hleft hright]

end SingleObjectTarget

#print axioms twoOpenCoverGroupoidDesc
#print axioms twoOpenCoverGroupoidDesc_comp_left
#print axioms twoOpenCoverGroupoidDesc_comp_right
#print axioms twoOpenCoverGroupoid_ext
#print axioms twoOpenCoverGroupoidDesc_unique
#print axioms twoOpenCoverGroupoidDesc_map_left
#print axioms twoOpenCoverGroupoidDesc_map_right
#print axioms twoOpenCoverGroupHom
#print axioms twoOpenCoverGroupHom_comp_left
#print axioms twoOpenCoverGroupHom_comp_right
#print axioms twoOpenCoverGroupHom_eq

end

end SystolicGrowth
