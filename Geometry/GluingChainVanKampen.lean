module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainOpenCover
public import Geometry.GluingSeamFundamentalGroup
public import Mathlib.GroupTheory.PushoutI

@[expose] public section

/-!
# The actual based chain-cover amalgam

The two original open chain sides contain the same actual seam neighborhood.
Their based fundamental-group maps agree in the original glued carrier, so
Mathlib's algebraic pushout has a canonical map to its fundamental group.
This constructs the literal diagram needed by van Kampen; bijectivity is a
separate topological obligation, not a hypothesis of these constructions.
-/

open Set

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The actual open sides of the same native cut; `true` is the prefix. -/
def gluedChainCoverSide (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (b : Bool) : Set P.GluedCarrier :=
  if b then P.gluedChainPrefixNeighborhood k else P.gluedChainSuffixNeighborhood k

theorem Internal.GluingChainVanKampenHelpers.seamNeighborhood_subset_chainCoverSide
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (b : Bool) :
    P.gluedMk '' P.seamNeighborhood k ⊆ P.gluedChainCoverSide k b := by
  cases b <;> exact fun _ hx => Or.inr hx

/-- The literal inclusion of the actual overlap into either open side. -/
def gluedChainCoverOverlapInclusion (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (b : Bool) :
    C(↥(P.gluedMk '' P.seamNeighborhood k), ↥(P.gluedChainCoverSide k b)) where
  toFun x := ⟨x.1, Internal.GluingChainVanKampenHelpers.seamNeighborhood_subset_chainCoverSide P k b x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The literal inclusion of an actual open side into the original carrier. -/
def gluedChainCoverSideInclusion (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (b : Bool) : C(↥(P.gluedChainCoverSide k b), P.GluedCarrier) where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val

/-- The actual overlap inclusion into the original carrier. -/
def gluedChainCoverSeamInclusion (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) : C(↥(P.gluedMk '' P.seamNeighborhood k), P.GluedCarrier) where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val

/-- Both native side inclusions restrict to precisely the same overlap map. -/
theorem gluedChainCover_inclusions_comp
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (b : Bool) :
    (P.gluedChainCoverSideInclusion k b).comp (P.gluedChainCoverOverlapInclusion k b) =
      P.gluedChainCoverSeamInclusion k := rfl

/-- The side group is based at the literal image of the included seam point. -/
abbrev gluedChainCoverSideGroup (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (θ : Circle) (b : Bool) :=
  FundamentalGroup ↥(P.gluedChainCoverSide k b)
    (P.gluedChainCoverOverlapInclusion k b (P.gluedSeamCircleInclusion k θ))

/-- The actual induced overlap-to-side group map, with no basepoint change. -/
def gluedChainCoverOverlapGroupMap (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (θ : Circle) (b : Bool) :
    FundamentalGroup ↥(P.gluedMk '' P.seamNeighborhood k) (P.gluedSeamCircleInclusion k θ) →*
      P.gluedChainCoverSideGroup k θ b :=
  FundamentalGroup.map (P.gluedChainCoverOverlapInclusion k b)
    (P.gluedSeamCircleInclusion k θ)

/-- The actual induced side-to-carrier group map. -/
def gluedChainCoverSideGroupMap (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (θ : Circle) (b : Bool) :
    P.gluedChainCoverSideGroup k θ b →*
      FundamentalGroup P.GluedCarrier (P.gluedSeamCircleInclusion k θ).1 :=
  FundamentalGroup.map (P.gluedChainCoverSideInclusion k b)
    (P.gluedChainCoverOverlapInclusion k b (P.gluedSeamCircleInclusion k θ))

/-- The actual induced overlap-to-carrier group map. -/
def gluedChainCoverSeamGroupMap (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (θ : Circle) :
    FundamentalGroup ↥(P.gluedMk '' P.seamNeighborhood k) (P.gluedSeamCircleInclusion k θ) →*
      FundamentalGroup P.GluedCarrier (P.gluedSeamCircleInclusion k θ).1 :=
  FundamentalGroup.map (P.gluedChainCoverSeamInclusion k)
    (P.gluedSeamCircleInclusion k θ)

/-- The literal based fundamental-group square commutes on every loop class. -/
theorem gluedChainCover_groupMaps_comp
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (θ : Circle) (b : Bool) :
    (P.gluedChainCoverSideGroupMap k θ b).comp (P.gluedChainCoverOverlapGroupMap k θ b) =
      P.gluedChainCoverSeamGroupMap k θ := by
  ext γ
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
  rfl

/-- Mathlib's algebraic amalgam of the actual based open-cover groups. -/
abbrev gluedChainCoverAmalgam (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (θ : Circle) :=
  Monoid.PushoutI (P.gluedChainCoverOverlapGroupMap k θ)

/-- The canonical map for the native van Kampen problem. Its domain is the
actual overlap amalgam, not an assumed surface-group presentation. -/
def gluedChainCoverAmalgamToFundamentalGroup
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : Circle) :
    P.gluedChainCoverAmalgam k θ →*
      FundamentalGroup P.GluedCarrier (P.gluedSeamCircleInclusion k θ).1 :=
  Monoid.PushoutI.lift (P.gluedChainCoverSideGroupMap k θ)
    (P.gluedChainCoverSeamGroupMap k θ) (P.gluedChainCover_groupMaps_comp k θ)

/-- Each original side group maps by its actual continuous inclusion. -/
@[simp] theorem gluedChainCoverAmalgamToFundamentalGroup_of
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : Circle)
    (b : Bool) (γ : P.gluedChainCoverSideGroup k θ b) :
    P.gluedChainCoverAmalgamToFundamentalGroup k θ (Monoid.PushoutI.of b γ) =
      P.gluedChainCoverSideGroupMap k θ b γ :=
  Monoid.PushoutI.lift_of _ _ _ γ

/-- The actual overlap class has the same image through either side. -/
@[simp] theorem gluedChainCoverAmalgamToFundamentalGroup_base
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : Circle)
    (γ : FundamentalGroup ↥(P.gluedMk '' P.seamNeighborhood k)
      (P.gluedSeamCircleInclusion k θ)) :
    P.gluedChainCoverAmalgamToFundamentalGroup k θ
        (Monoid.PushoutI.base (P.gluedChainCoverOverlapGroupMap k θ) γ) =
      P.gluedChainCoverSeamGroupMap k θ γ :=
  Monoid.PushoutI.lift_base _ _ _ γ

/-- In the actual amalgam, the one-turn polar boundary has one common class
on both original sides. This is the geometric seam identification. -/
theorem gluedChainCoverAmalgam_oneTurn_eq
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : Circle) :
    (Monoid.PushoutI.of true
        (P.gluedChainCoverOverlapGroupMap k θ true ⟦P.gluedSeamOneTurnLoop k θ⟧) :
          P.gluedChainCoverAmalgam k θ) =
      Monoid.PushoutI.of false
        (P.gluedChainCoverOverlapGroupMap k θ false ⟦P.gluedSeamOneTurnLoop k θ⟧) := by
  exact (Monoid.PushoutI.of_apply_eq_base
    (P.gluedChainCoverOverlapGroupMap k θ) true ⟦P.gluedSeamOneTurnLoop k θ⟧).trans
      (Monoid.PushoutI.of_apply_eq_base
        (P.gluedChainCoverOverlapGroupMap k θ) false ⟦P.gluedSeamOneTurnLoop k θ⟧).symm

#print axioms gluedChainCover_groupMaps_comp
#print axioms gluedChainCoverAmalgamToFundamentalGroup
#print axioms gluedChainCoverAmalgamToFundamentalGroup_of
#print axioms gluedChainCoverAmalgamToFundamentalGroup_base
#print axioms gluedChainCoverAmalgam_oneTurn_eq

end

end SystolicGrowth.ExerciseGluingPreparation
