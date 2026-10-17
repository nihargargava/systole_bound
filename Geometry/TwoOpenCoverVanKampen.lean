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
# Based fundamental groups from groupoid descent

Connecting paths convert a based group homomorphism into a functor on the
whole fundamental groupoid. Compatible paths on the overlap will allow the
actual open-cover pushout to descend these functors.
-/

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

namespace SystolicGrowth

noncomputable section

/-- Extend a based homomorphism over a groupoid using actual connecting
morphisms. Multiplication follows Mathlib's endomorphism convention. -/
def basedGroupoidFunctor {C : Type*} [Groupoid C] (x : C)
    {H : Type*} [Group H] (ρ : End x →* H) (p : ∀ y : C, x ⟶ y) :
    C ⥤ SingleObj H where
  obj _ := SingleObj.star H
  map {y z} f := ρ (p y ≫ f ≫ inv (p z))
  map_id y := by
    change ρ (p y ≫ 𝟙 y ≫ inv (p y)) = 1
    simp
    exact ρ.map_one
  map_comp {y z w} f g := by
    change ρ (p y ≫ (f ≫ g) ≫ inv (p w)) =
      ρ (p z ≫ g ≫ inv (p w)) * ρ (p y ≫ f ≫ inv (p z))
    rw [← ρ.map_mul]
    simp [End.mul_def, Category.assoc]

/-- A reflexive connecting path at the chosen basepoint retains precisely
the original based homomorphism, not a conjugate of it. -/
theorem basedGroupoidFunctor_map_base {C : Type*} [Groupoid C] (x : C)
    {H : Type*} [Group H] (ρ : End x →* H) (p : ∀ y : C, x ⟶ y)
    (hp : p x = 𝟙 x) (f : End x) :
    (basedGroupoidFunctor x ρ p).map f = ρ f := by
  simp [basedGroupoidFunctor, hp]

def Internal.TwoOpenCoverVanKampenHelpers.normalizedConnectingMorphisms {X : Type*} [TopologicalSpace X]
    {U : Set X} (hU : IsPathConnected U) (x : U) :
    ∀ y : FundamentalGroupoid U, FundamentalGroupoid.mk x ⟶ y := by
  classical
  exact fun y => if h : y = FundamentalGroupoid.mk x then eqToHom h.symm else
    Path.Homotopic.Quotient.mk
      (hU.joinedIn x.1 x.2 y.as.1 y.as.2).joined_subtype.somePath

private theorem normalizedConnectingMorphisms_base
    {X : Type*} [TopologicalSpace X] {U : Set X}
    (hU : IsPathConnected U) (x : U) :
    Internal.TwoOpenCoverVanKampenHelpers.normalizedConnectingMorphisms hU x (FundamentalGroupoid.mk x) =
      𝟙 (FundamentalGroupoid.mk x) := by
  simp [Internal.TwoOpenCoverVanKampenHelpers.normalizedConnectingMorphisms]

def Internal.TwoOpenCoverVanKampenHelpers.overlapLeftInclusion {X : Type*} [TopologicalSpace X]
    (U V : Set X) : C(↥(U ∩ V), U) where
  toFun y := ⟨y.1, y.2.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def Internal.TwoOpenCoverVanKampenHelpers.overlapRightInclusion {X : Type*} [TopologicalSpace X]
    (U V : Set X) : C(↥(U ∩ V), V) where
  toFun y := ⟨y.1, y.2.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def Internal.TwoOpenCoverVanKampenHelpers.coverLeftConnectingMorphisms {X : Type*} [TopologicalSpace X]
    {U V : Set X} (hU : IsPathConnected U) (hUV : IsPathConnected (U ∩ V))
    (x : ↥(U ∩ V)) :
    ∀ y : FundamentalGroupoid U,
      FundamentalGroupoid.mk (Internal.TwoOpenCoverVanKampenHelpers.overlapLeftInclusion U V x) ⟶ y := by
  classical
  exact fun y => if hy : y.as.1 ∈ V then
    (FundamentalGroupoid.map (Internal.TwoOpenCoverVanKampenHelpers.overlapLeftInclusion U V)).map
      (Internal.TwoOpenCoverVanKampenHelpers.normalizedConnectingMorphisms hUV x (FundamentalGroupoid.mk ⟨y.as.1, y.as.2, hy⟩))
    else Path.Homotopic.Quotient.mk
      (hU.joinedIn x.1 x.2.1 y.as.1 y.as.2).joined_subtype.somePath

def Internal.TwoOpenCoverVanKampenHelpers.coverRightConnectingMorphisms {X : Type*} [TopologicalSpace X]
    {U V : Set X} (hV : IsPathConnected V) (hUV : IsPathConnected (U ∩ V))
    (x : ↥(U ∩ V)) :
    ∀ y : FundamentalGroupoid V,
      FundamentalGroupoid.mk (Internal.TwoOpenCoverVanKampenHelpers.overlapRightInclusion U V x) ⟶ y := by
  classical
  exact fun y => if hy : y.as.1 ∈ U then
    (FundamentalGroupoid.map (Internal.TwoOpenCoverVanKampenHelpers.overlapRightInclusion U V)).map
      (Internal.TwoOpenCoverVanKampenHelpers.normalizedConnectingMorphisms hUV x (FundamentalGroupoid.mk ⟨y.as.1, hy, y.as.2⟩))
    else Path.Homotopic.Quotient.mk
      (hV.joinedIn x.1 x.2.2 y.as.1 y.as.2).joined_subtype.somePath

private theorem coverLeftConnectingMorphisms_overlap
    {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU : IsPathConnected U) (hUV : IsPathConnected (U ∩ V))
    (x : ↥(U ∩ V)) (y : FundamentalGroupoid ↥(U ∩ V)) :
    Internal.TwoOpenCoverVanKampenHelpers.coverLeftConnectingMorphisms hU hUV x
        ((FundamentalGroupoid.map (Internal.TwoOpenCoverVanKampenHelpers.overlapLeftInclusion U V)).obj y) =
      (FundamentalGroupoid.map (Internal.TwoOpenCoverVanKampenHelpers.overlapLeftInclusion U V)).map
        (Internal.TwoOpenCoverVanKampenHelpers.normalizedConnectingMorphisms hUV x y) := by
  unfold Internal.TwoOpenCoverVanKampenHelpers.coverLeftConnectingMorphisms
  split_ifs with hy
  · rfl
  · exact (hy y.as.2.2).elim

private theorem coverRightConnectingMorphisms_overlap
    {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hV : IsPathConnected V) (hUV : IsPathConnected (U ∩ V))
    (x : ↥(U ∩ V)) (y : FundamentalGroupoid ↥(U ∩ V)) :
    Internal.TwoOpenCoverVanKampenHelpers.coverRightConnectingMorphisms hV hUV x
        ((FundamentalGroupoid.map (Internal.TwoOpenCoverVanKampenHelpers.overlapRightInclusion U V)).obj y) =
      (FundamentalGroupoid.map (Internal.TwoOpenCoverVanKampenHelpers.overlapRightInclusion U V)).map
        (Internal.TwoOpenCoverVanKampenHelpers.normalizedConnectingMorphisms hUV x y) := by
  unfold Internal.TwoOpenCoverVanKampenHelpers.coverRightConnectingMorphisms
  split_ifs with hy
  · rfl
  · exact (hy y.as.2.1).elim

private theorem coverLeftConnectingMorphisms_base
    {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU : IsPathConnected U) (hUV : IsPathConnected (U ∩ V)) (x : ↥(U ∩ V)) :
    Internal.TwoOpenCoverVanKampenHelpers.coverLeftConnectingMorphisms hU hUV x
        (FundamentalGroupoid.mk (Internal.TwoOpenCoverVanKampenHelpers.overlapLeftInclusion U V x)) =
      𝟙 (FundamentalGroupoid.mk (Internal.TwoOpenCoverVanKampenHelpers.overlapLeftInclusion U V x)) := by
  change Internal.TwoOpenCoverVanKampenHelpers.coverLeftConnectingMorphisms hU hUV x
    ((FundamentalGroupoid.map (Internal.TwoOpenCoverVanKampenHelpers.overlapLeftInclusion U V)).obj (FundamentalGroupoid.mk x)) = _
  rw [coverLeftConnectingMorphisms_overlap hU hUV x (FundamentalGroupoid.mk x),
    normalizedConnectingMorphisms_base]
  exact CategoryTheory.Functor.map_id _ _

private theorem coverRightConnectingMorphisms_base
    {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hV : IsPathConnected V) (hUV : IsPathConnected (U ∩ V)) (x : ↥(U ∩ V)) :
    Internal.TwoOpenCoverVanKampenHelpers.coverRightConnectingMorphisms hV hUV x
        (FundamentalGroupoid.mk (Internal.TwoOpenCoverVanKampenHelpers.overlapRightInclusion U V x)) =
      𝟙 (FundamentalGroupoid.mk (Internal.TwoOpenCoverVanKampenHelpers.overlapRightInclusion U V x)) := by
  change Internal.TwoOpenCoverVanKampenHelpers.coverRightConnectingMorphisms hV hUV x
    ((FundamentalGroupoid.map (Internal.TwoOpenCoverVanKampenHelpers.overlapRightInclusion U V)).obj (FundamentalGroupoid.mk x)) = _
  rw [coverRightConnectingMorphisms_overlap hV hUV x (FundamentalGroupoid.mk x),
    normalizedConnectingMorphisms_base]
  exact CategoryTheory.Functor.map_id _ _

private theorem basedGroupoidFunctor_comp
    {C D : Type*} [Groupoid C] [Groupoid D] (F : C ⥤ D) (x : C)
    {H : Type*} [Group H] (ρ : End (F.obj x) →* H)
    (p : ∀ y : C, x ⟶ y) (q : ∀ y : D, F.obj x ⟶ y)
    (hq : ∀ y : C, q (F.obj y) = F.map (p y)) :
    F ⋙ basedGroupoidFunctor (F.obj x) ρ q =
      basedGroupoidFunctor x (ρ.comp (F.mapEnd x)) p := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro y z f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change ρ (q (F.obj y) ≫ F.map f ≫ inv (q (F.obj z))) =
    ρ (F.map (p y ≫ f ≫ inv (p z)))
  rw [hq y, hq z]
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_inv]

private theorem coverBasedFunctors_compatible
    {X H : Type*} [TopologicalSpace X] [Group H] {U V : Set X}
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (hUV : IsPathConnected (U ∩ V)) (x : ↥(U ∩ V))
    (fU : FundamentalGroup U (Internal.TwoOpenCoverVanKampenHelpers.overlapLeftInclusion U V x) →* H)
    (fV : FundamentalGroup V (Internal.TwoOpenCoverVanKampenHelpers.overlapRightInclusion U V x) →* H)
    (hf : fU.comp (FundamentalGroup.map (Internal.TwoOpenCoverVanKampenHelpers.overlapLeftInclusion U V) x) =
      fV.comp (FundamentalGroup.map (Internal.TwoOpenCoverVanKampenHelpers.overlapRightInclusion U V) x)) :
    FundamentalGroupoid.map (Internal.TwoOpenCoverVanKampenHelpers.overlapLeftInclusion U V) ⋙
        basedGroupoidFunctor (FundamentalGroupoid.mk (Internal.TwoOpenCoverVanKampenHelpers.overlapLeftInclusion U V x))
          fU (Internal.TwoOpenCoverVanKampenHelpers.coverLeftConnectingMorphisms hU hUV x) =
      FundamentalGroupoid.map (Internal.TwoOpenCoverVanKampenHelpers.overlapRightInclusion U V) ⋙
        basedGroupoidFunctor (FundamentalGroupoid.mk (Internal.TwoOpenCoverVanKampenHelpers.overlapRightInclusion U V x))
          fV (Internal.TwoOpenCoverVanKampenHelpers.coverRightConnectingMorphisms hV hUV x) := by
  change FundamentalGroupoid.map (Internal.TwoOpenCoverVanKampenHelpers.overlapLeftInclusion U V) ⋙
      basedGroupoidFunctor
        ((FundamentalGroupoid.map (Internal.TwoOpenCoverVanKampenHelpers.overlapLeftInclusion U V)).obj (FundamentalGroupoid.mk x))
        fU (Internal.TwoOpenCoverVanKampenHelpers.coverLeftConnectingMorphisms hU hUV x) =
    FundamentalGroupoid.map (Internal.TwoOpenCoverVanKampenHelpers.overlapRightInclusion U V) ⋙
      basedGroupoidFunctor
        ((FundamentalGroupoid.map (Internal.TwoOpenCoverVanKampenHelpers.overlapRightInclusion U V)).obj (FundamentalGroupoid.mk x))
        fV (Internal.TwoOpenCoverVanKampenHelpers.coverRightConnectingMorphisms hV hUV x)
  rw [basedGroupoidFunctor_comp _ (FundamentalGroupoid.mk x) _ _ _
    (coverLeftConnectingMorphisms_overlap hU hUV x),
    basedGroupoidFunctor_comp _ (FundamentalGroupoid.mk x) _ _ _
    (coverRightConnectingMorphisms_overlap hV hUV x)]
  change basedGroupoidFunctor (FundamentalGroupoid.mk x)
      (fU.comp (FundamentalGroup.map (Internal.TwoOpenCoverVanKampenHelpers.overlapLeftInclusion U V) x)) _ =
    basedGroupoidFunctor (FundamentalGroupoid.mk x)
      (fV.comp (FundamentalGroup.map (Internal.TwoOpenCoverVanKampenHelpers.overlapRightInclusion U V) x)) _
  rw [hf]

/-- Compatible homomorphisms on the actual based open-cover groups descend
to the ambient fundamental group. No presentation or restricted class of
loops is assumed. The basepoint remains the original overlap point. -/
theorem exists_fundamentalGroup_hom_of_two_open_cover
    {X H : Type} [TopologicalSpace X] [Group H] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hpcU : IsPathConnected U) (hpcV : IsPathConnected V)
    (hpcUV : IsPathConnected (U ∩ V)) (x : ↥(U ∩ V))
    (fU : FundamentalGroup U ⟨x.1, x.2.1⟩ →* H)
    (fV : FundamentalGroup V ⟨x.1, x.2.2⟩ →* H)
    (hf : fU.comp (FundamentalGroup.map
        (⟨fun y => ⟨y.1, y.2.1⟩, continuous_subtype_val.subtype_mk _⟩ : C(↥(U ∩ V), U)) x) =
      fV.comp (FundamentalGroup.map
        (⟨fun y => ⟨y.1, y.2.2⟩, continuous_subtype_val.subtype_mk _⟩ : C(↥(U ∩ V), V)) x)) :
    ∃ f : FundamentalGroup X x.1 →* H,
      f.comp (FundamentalGroup.map
          (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) ⟨x.1, x.2.1⟩) = fU ∧
      f.comp (FundamentalGroup.map
          (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X)) ⟨x.1, x.2.2⟩) = fV := by
  let FU := basedGroupoidFunctor (FundamentalGroupoid.mk (Internal.TwoOpenCoverVanKampenHelpers.overlapLeftInclusion U V x))
    fU (Internal.TwoOpenCoverVanKampenHelpers.coverLeftConnectingMorphisms hpcU hpcUV x)
  let FV := basedGroupoidFunctor (FundamentalGroupoid.mk (Internal.TwoOpenCoverVanKampenHelpers.overlapRightInclusion U V x))
    fV (Internal.TwoOpenCoverVanKampenHelpers.coverRightConnectingMorphisms hpcV hpcUV x)
  let jU : C(U, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let jV : C(V, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let hpush := Vendored.ClassicalVanKampen.ClassicalSVK.classicalOpenCoverPushout
    U V hU hV hcover
  have hcompat :
      (FundamentalGroupoid.map (Internal.TwoOpenCoverVanKampenHelpers.overlapLeftInclusion U V)).toCatHom ≫ FU.toCatHom =
        (FundamentalGroupoid.map (Internal.TwoOpenCoverVanKampenHelpers.overlapRightInclusion U V)).toCatHom ≫ FV.toCatHom := by
    apply Cat.ext
    exact coverBasedFunctors_compatible hpcU hpcV hpcUV x fU fV hf
  let d := hpush.desc FU.toCatHom FV.toCatHom hcompat
  let F := d.toFunctor
  let f : FundamentalGroup X x.1 →* H :=
    { toFun := fun γ => F.map γ
      map_one' := F.map_id (FundamentalGroupoid.mk x.1)
      map_mul' := fun γ δ => F.map_comp δ γ }
  refine ⟨f, ?_, ?_⟩
  · ext γ
    change F.map ((FundamentalGroupoid.map jU).map γ) = fU γ
    have hrestrict : FundamentalGroupoid.map jU ⋙ F = FU :=
      congrArg Cat.Hom.toFunctor (hpush.inl_desc FU.toCatHom FV.toCatHom hcompat)
    have hγ := congrArg
      (fun G : FundamentalGroupoid U ⥤ SingleObj H => (G.map γ : H)) hrestrict
    exact hγ.trans (basedGroupoidFunctor_map_base _ _ _
      (coverLeftConnectingMorphisms_base hpcU hpcUV x) γ)
  · ext γ
    change F.map ((FundamentalGroupoid.map jV).map γ) = fV γ
    have hrestrict : FundamentalGroupoid.map jV ⋙ F = FV :=
      congrArg Cat.Hom.toFunctor (hpush.inr_desc FU.toCatHom FV.toCatHom hcompat)
    have hγ := congrArg
      (fun G : FundamentalGroupoid V ⥤ SingleObj H => (G.map γ : H)) hrestrict
    exact hγ.trans (basedGroupoidFunctor_map_base _ _ _
      (coverRightConnectingMorphisms_base hpcV hpcUV x) γ)

#print axioms exists_fundamentalGroup_hom_of_two_open_cover

end

end SystolicGrowth
