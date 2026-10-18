module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainPrefixBaseCases
public import Geometry.GluingChainPrefixSuffixRetraction
public import Geometry.GluingChainPrefixLeftFundamentalGroup
public import Geometry.FreeGroupTrivialAmalgam
public import Geometry.TwoOpenCoverAmalgamEquiv

@[expose] public section

/-!
# Van Kampen on the original retained prefixes

The recursive cut takes place inside the original closed prefix, retaining
its outgoing boundary. Its overlap is the full original two-sided seam, and
all maps use literal subtype inclusions and the original circle basepoint.
-/

open Set

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Math. The original circle point viewed in the retained prefix overlap. -/
def gluedChainPrefixSeamBasepoint
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val) (θ : Circle) :
    ↥(P.gluedChainPrefixCoverOverlap k j) :=
  P.gluedChainPrefixCoverOverlapHomeomorph k j hjk (P.gluedSeamCircleInclusion j θ)

/-- Math. The positive one-turn loop in the literal retained seam overlap. -/
def gluedChainPrefixOverlapOneTurnLoop
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val) (θ : Circle) :
    Path (P.gluedChainPrefixSeamBasepoint k j hjk θ)
      (P.gluedChainPrefixSeamBasepoint k j hjk θ) :=
  (P.gluedSeamOneTurnLoop j θ).map
    (P.gluedChainPrefixCoverOverlapHomeomorph k j hjk).continuous_toFun

/-- Math. The original positive seam winding gives the actual overlap its cyclic marking. -/
def gluedChainPrefixOverlapFreeEquiv
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val) (θ : Circle) :
    FundamentalGroup ↥(P.gluedChainPrefixCoverOverlap k j)
      (P.gluedChainPrefixSeamBasepoint k j hjk θ) ≃* FreeGroup Unit :=
  (P.gluedChainPrefixCoverOverlapFundamentalGroupEquiv k j hjk θ).symm.trans
    ((P.gluedSeamCircleFundamentalGroupEquiv j θ).trans
      (circleFundamentalGroupFreeEquiv θ))

set_option backward.isDefEq.respectTransparency false in
/-- Math. The cyclic marking reads the actual positive overlap loop as its generator. -/
theorem gluedChainPrefixOverlapFreeEquiv_oneTurn
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val) (θ : Circle) :
    P.gluedChainPrefixOverlapFreeEquiv k j hjk θ
      ⟦P.gluedChainPrefixOverlapOneTurnLoop k j hjk θ⟧ = FreeGroup.of () := by
  have hmap := P.gluedChainPrefixCoverOverlapFundamentalGroupEquiv_oneTurn k j hjk θ
  change P.gluedChainPrefixCoverOverlapFundamentalGroupEquiv k j hjk θ
    ⟦P.gluedSeamOneTurnLoop j θ⟧ =
      ⟦P.gluedChainPrefixOverlapOneTurnLoop k j hjk θ⟧ at hmap
  have hreduce : P.gluedChainPrefixOverlapFreeEquiv k j hjk θ
      (P.gluedChainPrefixCoverOverlapFundamentalGroupEquiv k j hjk θ
        ⟦P.gluedSeamOneTurnLoop j θ⟧) =
      circleFundamentalGroupFreeEquiv θ
        (P.gluedSeamCircleFundamentalGroupEquiv j θ ⟦P.gluedSeamOneTurnLoop j θ⟧) := by
    exact congrArg (fun γ : FundamentalGroup ↥(P.gluedMk '' P.seamNeighborhood j)
      (P.gluedSeamCircleInclusion j θ) =>
        circleFundamentalGroupFreeEquiv θ (P.gluedSeamCircleFundamentalGroupEquiv j θ γ))
      ((P.gluedChainPrefixCoverOverlapFundamentalGroupEquiv k j hjk θ).symm_apply_apply
        ⟦P.gluedSeamOneTurnLoop j θ⟧)
  exact (congrArg (P.gluedChainPrefixOverlapFreeEquiv k j hjk θ) hmap.symm).trans
    (hreduce.trans ((congrArg (circleFundamentalGroupFreeEquiv θ)
      (P.gluedSeamCircleFundamentalGroupEquiv_map_loop j θ (circleOneTurnLoop θ))).trans
        (circleFundamentalGroupFreeEquiv_oneTurn θ)))

set_option backward.isDefEq.respectTransparency false in
/-- Math. The inverse cyclic marking selects precisely the original positive turn. -/
theorem gluedChainPrefixOverlapFreeEquiv_symm_of
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val) (θ : Circle) :
    (P.gluedChainPrefixOverlapFreeEquiv k j hjk θ).symm (FreeGroup.of ()) =
      ⟦P.gluedChainPrefixOverlapOneTurnLoop k j hjk θ⟧ := by
  rw [← P.gluedChainPrefixOverlapFreeEquiv_oneTurn k j hjk θ]
  exact MulEquiv.symm_apply_apply _ _

/-- Math. The actual based diagram for an adjacent retained-prefix attachment. -/
abbrev gluedChainPrefixCoverAmalgam
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val) (θ : Circle) :=
  twoOpenCoverFundamentalGroupAmalgam
    (P.gluedChainPrefixCoverSide k j true)
    (P.gluedChainPrefixCoverSide k j false)
    (P.gluedChainPrefixSeamBasepoint k j hjk θ)

/-- Math. Native van Kampen for an adjacent retained-prefix attachment. -/
def gluedChainPrefixCoverFundamentalGroupEquiv
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val) (θ : Circle) :
    P.gluedChainPrefixCoverAmalgam k j (by omega) θ ≃*
      FundamentalGroup ↥(P.gluedChainPrefix k)
        (P.gluedChainPrefixSeamBasepoint k j (by omega) θ).val := by
  apply twoOpenCoverFundamentalGroupAmalgamEquiv
    (P.gluedChainPrefixCoverSide_isOpen k j true)
    (P.gluedChainPrefixCoverSide_isOpen k j false)
    (P.gluedChainPrefixCoverSide_union k j)
  · exact isPathConnected_iff_pathConnectedSpace.mpr
      (P.gluedChainPrefixLeftCoverSidePathConnectedSpace k j (by omega))
  · exact isPathConnected_iff_pathConnectedSpace.mpr
      (P.gluedChainPrefixRightCoverSidePathConnectedSpace k j hjk)
  · exact isPathConnected_iff_pathConnectedSpace.mpr
      (P.gluedChainPrefixCoverOverlapPathConnectedSpace k j (by omega))

set_option backward.isDefEq.respectTransparency false in
/-- Math. The native equivalence retains the literal side inclusion map. -/
@[simp] theorem gluedChainPrefixCoverFundamentalGroupEquiv_of
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val) (θ : Circle) (b : Bool)
    (γ : twoOpenCoverAmalgamSideGroup
      (P.gluedChainPrefixCoverSide k j true)
      (P.gluedChainPrefixCoverSide k j false)
      (P.gluedChainPrefixSeamBasepoint k j (by omega) θ) b) :
    P.gluedChainPrefixCoverFundamentalGroupEquiv k j hjk θ
      (Monoid.PushoutI.of (φ := twoOpenCoverAmalgamSideMap
        (P.gluedChainPrefixCoverSide k j true)
        (P.gluedChainPrefixCoverSide k j false)
        (P.gluedChainPrefixSeamBasepoint k j (by omega) θ)) b γ) =
        twoOpenCoverSideToAmbient
          (P.gluedChainPrefixCoverSide k j true)
          (P.gluedChainPrefixCoverSide k j false)
          (P.gluedChainPrefixSeamBasepoint k j (by omega) θ) b γ := by
  exact twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup_of _ _ _ b γ

set_option backward.isDefEq.respectTransparency false in
/-- Math. The native equivalence retains the literal seam inclusion map. -/
@[simp] theorem gluedChainPrefixCoverFundamentalGroupEquiv_base
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val) (θ : Circle)
    (γ : FundamentalGroup ↥(P.gluedChainPrefixCoverOverlap k j)
      (P.gluedChainPrefixSeamBasepoint k j (by omega) θ)) :
    P.gluedChainPrefixCoverFundamentalGroupEquiv k j hjk θ
      (Monoid.PushoutI.base
        (twoOpenCoverAmalgamSideMap
          (P.gluedChainPrefixCoverSide k j true)
          (P.gluedChainPrefixCoverSide k j false)
          (P.gluedChainPrefixSeamBasepoint k j (by omega) θ)) γ) =
      twoOpenCoverOverlapToAmbient
        (P.gluedChainPrefixCoverSide k j true)
        (P.gluedChainPrefixCoverSide k j false)
        (P.gluedChainPrefixSeamBasepoint k j (by omega) θ) γ := by
  exact twoOpenCoverFundamentalGroupAmalgamToFundamentalGroup_base _ _ _ γ

#print axioms gluedChainPrefixCoverFundamentalGroupEquiv
#print axioms gluedChainPrefixOverlapFreeEquiv
#print axioms gluedChainPrefixOverlapFreeEquiv_oneTurn
#print axioms gluedChainPrefixOverlapFreeEquiv_symm_of
#print axioms gluedChainPrefixCoverFundamentalGroupEquiv_of
#print axioms gluedChainPrefixCoverFundamentalGroupEquiv_base

end

end SystolicGrowth.ExerciseGluingPreparation
