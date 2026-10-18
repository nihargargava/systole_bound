module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.TwoOpenCoverFundamentalGroup
public import Geometry.TwoOpenCoverVanKampen
public import Mathlib.GroupTheory.PushoutI

@[expose] public section

/-!
# The based fundamental group of an actual two-open cover

For a path-connected open cover with path-connected overlap, the canonical
amalgamated product of the two side groups over the overlap is the ambient
fundamental group. The Bool index convention is `true` = left side and
`false` = right side. Every map is induced by the literal subtype inclusion.
-/

open Set

namespace SystolicGrowth

noncomputable section

variable {X : Type} [TopologicalSpace X] {U V : Set X}

/-- The literal overlap inclusion into the left open set. The theorem uses
the same universe-zero scope as the existing based descent producer. -/
def twoOpenCoverAmalgamOverlapLeft (U V : Set X) : C(↥(U ∩ V), U) where
  toFun x := ⟨x.1, x.2.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The literal overlap inclusion into the right open set. -/
def twoOpenCoverAmalgamOverlapRight (U V : Set X) : C(↥(U ∩ V), V) where
  toFun x := ⟨x.1, x.2.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The literal inclusion of an open side into the ambient space. -/
def twoOpenCoverAmalgamInclusion (W : Set X) : C(W, X) where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val

/-- The based group on one side of an actual two-open cover. `true` selects
the left open set and `false` the right open set. -/
abbrev twoOpenCoverAmalgamSideGroup (U V : Set X) (q : ↥(U ∩ V)) (b : Bool) :=
  match b with
  | true => FundamentalGroup U (twoOpenCoverAmalgamOverlapLeft U V q)
  | false => FundamentalGroup V (twoOpenCoverAmalgamOverlapRight U V q)

instance twoOpenCoverAmalgamSideGroup_group (U V : Set X) (q : ↥(U ∩ V)) (b : Bool) :
    Group (twoOpenCoverAmalgamSideGroup U V q b) := by
  cases b <;> dsimp [twoOpenCoverAmalgamSideGroup] <;> infer_instance

/-- The two literal overlap-to-side maps in the Bool-indexed diagram. -/
def twoOpenCoverAmalgamSideMap (U V : Set X) (q : ↥(U ∩ V)) (b : Bool) :
    FundamentalGroup (↥(U ∩ V)) q →*
      twoOpenCoverAmalgamSideGroup U V q b :=
  match b with
  | true => FundamentalGroup.map (twoOpenCoverAmalgamOverlapLeft U V) q
  | false => FundamentalGroup.map (twoOpenCoverAmalgamOverlapRight U V) q

/-- The actual based amalgam of the two side groups along the actual overlap.
Its Bool-indexed factors use `true` for U and `false` for V. -/
abbrev twoOpenCoverFundamentalGroupAmalgam (U V : Set X) (q : ↥(U ∩ V)) :=
  Monoid.PushoutI (twoOpenCoverAmalgamSideMap U V q)

/-- The literal side-to-ambient based homomorphism. -/
def twoOpenCoverSideToAmbient (U V : Set X) (q : ↥(U ∩ V)) (b : Bool) :
    twoOpenCoverAmalgamSideGroup U V q b →* FundamentalGroup X q.1 :=
  match b with
  | true => FundamentalGroup.map (twoOpenCoverAmalgamInclusion U)
      (twoOpenCoverAmalgamOverlapLeft U V q)
  | false => FundamentalGroup.map (twoOpenCoverAmalgamInclusion V)
      (twoOpenCoverAmalgamOverlapRight U V q)

/-- The actual inclusion-induced homomorphism from the overlap group. -/
def twoOpenCoverOverlapToAmbient (U V : Set X) (q : ↥(U ∩ V)) :
    FundamentalGroup (↥(U ∩ V)) q →* FundamentalGroup X q.1 :=
  FundamentalGroup.map (twoOpenCoverAmalgamInclusion (U ∩ V)) q

theorem Internal.TwoOpenCoverAmalgamEquivHelpers.twoOpenCoverSideToAmbient_compatible (U V : Set X)
    (q : ↥(U ∩ V)) :
    ∀ b : Bool,
      (twoOpenCoverSideToAmbient U V q b).comp
        (twoOpenCoverAmalgamSideMap U V q b) =
          twoOpenCoverOverlapToAmbient U V q := by
  intro b
  cases b
  · ext γ
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
    rfl
  · ext γ
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
    rfl

/-- The canonical map from the actual based side-group amalgam to the actual
ambient fundamental group. -/
def twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup
    (U V : Set X) (q : ↥(U ∩ V)) :
    twoOpenCoverFundamentalGroupAmalgam U V q →* FundamentalGroup X q.1 :=
  Monoid.PushoutI.lift (twoOpenCoverSideToAmbient U V q)
    (twoOpenCoverOverlapToAmbient U V q)
    (Internal.TwoOpenCoverAmalgamEquivHelpers.twoOpenCoverSideToAmbient_compatible U V q)

@[simp]
theorem twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup_of
    (U V : Set X) (q : ↥(U ∩ V)) (b : Bool)
    (γ : twoOpenCoverAmalgamSideGroup U V q b) :
    twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup U V q
      (Monoid.PushoutI.of b γ) = twoOpenCoverSideToAmbient U V q b γ :=
  Monoid.PushoutI.lift_of _ _ _ γ

@[simp]
theorem twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup_base
    (U V : Set X) (q : ↥(U ∩ V))
    (γ : FundamentalGroup (↥(U ∩ V)) q) :
    twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup U V q
      (Monoid.PushoutI.base (twoOpenCoverAmalgamSideMap U V q) γ) =
        twoOpenCoverOverlapToAmbient U V q γ :=
  Monoid.PushoutI.lift_base _ _ _ γ

/-- The canonical amalgam map is surjective: every ambient based loop is
generated by loops from the two sides of the actual open cover. -/
theorem twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup_surjective
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hpcU : IsPathConnected U) (hpcV : IsPathConnected V)
    (hpcUV : IsPathConnected (U ∩ V)) (q : ↥(U ∩ V)) :
    Function.Surjective
      (twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup U V q) := by
  apply MonoidHom.range_eq_top.1
  have hxU : q.1 ∈ U := q.2.1
  have hxV : q.1 ∈ V := q.2.2
  apply fundamentalGroup_subgroup_eq_top_of_two_open_cover
    hU hV hcover hpcU hpcV hpcUV hxU hxV
    (MonoidHom.range (twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup U V q))
  · rintro γ ⟨δ, rfl⟩
    refine ⟨Monoid.PushoutI.of true δ, ?_⟩
    exact twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup_of U V q true δ
  · rintro γ ⟨δ, rfl⟩
    refine ⟨Monoid.PushoutI.of false δ, ?_⟩
    exact twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup_of U V q false δ

/-- The canonical amalgam map is injective: compatible side maps to the
amalgam descend across the actual open cover and give a left inverse. -/
theorem twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup_injective
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hpcU : IsPathConnected U) (hpcV : IsPathConnected V)
    (hpcUV : IsPathConnected (U ∩ V)) (q : ↥(U ∩ V)) :
    Function.Injective
      (twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup U V q) := by
  let x := q
  obtain ⟨f, hfU, hfV⟩ := exists_fundamentalGroup_hom_of_two_open_cover
    hU hV hcover hpcU hpcV hpcUV x
    (Monoid.PushoutI.of true :
      twoOpenCoverAmalgamSideGroup U V q true →*
        twoOpenCoverFundamentalGroupAmalgam U V q)
    (Monoid.PushoutI.of false :
      twoOpenCoverAmalgamSideGroup U V q false →*
        twoOpenCoverFundamentalGroupAmalgam U V q)
    (by
      ext γ
      exact (Monoid.PushoutI.of_apply_eq_base
        (twoOpenCoverAmalgamSideMap U V q) true γ).trans
          (Monoid.PushoutI.of_apply_eq_base
            (twoOpenCoverAmalgamSideMap U V q) false γ).symm)
  have hleft : f.comp
      (twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup U V q) =
        MonoidHom.id (twoOpenCoverFundamentalGroupAmalgam U V q) := by
    apply Monoid.PushoutI.hom_ext_nonempty
    intro b
    cases b
    · ext γ
      change f (twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup U V q
        (Monoid.PushoutI.of false γ)) = Monoid.PushoutI.of false γ
      rw [twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup_of]
      exact DFunLike.congr_fun hfV γ
    · ext γ
      change f (twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup U V q
        (Monoid.PushoutI.of true γ)) = Monoid.PushoutI.of true γ
      rw [twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup_of]
      exact DFunLike.congr_fun hfU γ
  intro a b hab
  have hab' := congrArg f hab
  have ha := DFunLike.congr_fun hleft a
  have hb := DFunLike.congr_fun hleft b
  change f (twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup U V q a) = a at ha
  change f (twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup U V q b) = b at hb
  rw [ha, hb] at hab'
  exact hab'

/-- The canonical actual open-cover amalgam map is bijective. -/
theorem twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup_bijective
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hpcU : IsPathConnected U) (hpcV : IsPathConnected V)
    (hpcUV : IsPathConnected (U ∩ V)) (q : ↥(U ∩ V)) :
    Function.Bijective
      (twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup U V q) :=
  ⟨twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup_injective
      hU hV hcover hpcU hpcV hpcUV q,
    twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup_surjective
      hU hV hcover hpcU hpcV hpcUV q⟩

/-- The based fundamental group of an actual path-connected open cover is the
amalgamated product of its two actual side groups over the actual overlap. -/
def twoOpenCoverFundamentalGroupAmalgamEquiv
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hpcU : IsPathConnected U) (hpcV : IsPathConnected V)
    (hpcUV : IsPathConnected (U ∩ V)) (q : ↥(U ∩ V)) :
    twoOpenCoverFundamentalGroupAmalgam U V q ≃*
      FundamentalGroup X q.1 :=
  MulEquiv.ofBijective
    (twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup U V q)
    (twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup_bijective
      hU hV hcover hpcU hpcV hpcUV q)

@[simp]
theorem twoOpenCoverFundamentalGroupAmalgamEquiv_of
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hpcU : IsPathConnected U) (hpcV : IsPathConnected V)
    (hpcUV : IsPathConnected (U ∩ V)) (q : ↥(U ∩ V))
    (b : Bool) (γ : twoOpenCoverAmalgamSideGroup U V q b) :
    twoOpenCoverFundamentalGroupAmalgamEquiv
      hU hV hcover hpcU hpcV hpcUV q (Monoid.PushoutI.of b γ) =
        twoOpenCoverSideToAmbient U V q b γ := rfl

@[simp]
theorem twoOpenCoverFundamentalGroupAmalgamEquiv_base
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hpcU : IsPathConnected U) (hpcV : IsPathConnected V)
    (hpcUV : IsPathConnected (U ∩ V)) (q : ↥(U ∩ V))
    (γ : FundamentalGroup (↥(U ∩ V)) q) :
    twoOpenCoverFundamentalGroupAmalgamEquiv
      hU hV hcover hpcU hpcV hpcUV q
        (Monoid.PushoutI.base (twoOpenCoverAmalgamSideMap U V q) γ) =
          twoOpenCoverOverlapToAmbient U V q γ := rfl

#print axioms twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup_bijective
#print axioms twoOpenCoverFundamentalGroupAmalgamEquiv_of

end

end SystolicGrowth
