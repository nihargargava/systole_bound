module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainPrefixOpenCover
public import Geometry.GluingChainFundamentalGroup
public import Geometry.TwoPuncturedDiskFreePresentation
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

@[expose] public section

/-!
# Based groups for the retained prefix cover

The restricted left side has the same based fundamental group as the original
closed prefix. The seam group likewise transports to the retained overlap by
the literal overlap homeomorphism, including its positive one-turn loop.
-/

open Set
open scoped ContinuousMap

namespace SystolicGrowth
namespace ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The original closed-prefix point, viewed in the actual retained left
cover side using the literal prefix homeomorphism. -/
def gluedChainPrefixLeftCoverBasepoint
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val)
    (x : ↥(P.gluedChainPrefix j)) :
    ↥(P.gluedChainPrefixCoverSide k j true) :=
  P.gluedChainPrefixLeftCoverSideHomeomorph k j hjk
    (P.gluedChainPrefixInclusion j x)

/-- At every original-prefix basepoint, the retained true side has the
actual based group of the original closed prefix. The map first uses the
literal left-side homeomorphism and then the native collar retraction. -/
def gluedChainPrefixLeftCoverFundamentalGroupEquiv
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val)
    (x : ↥(P.gluedChainPrefix j)) :
    FundamentalGroup ↥(P.gluedChainPrefixCoverSide k j true)
      (P.gluedChainPrefixLeftCoverBasepoint k j hjk x) ≃*
    FundamentalGroup ↥(P.gluedChainPrefix j) x := by
  let H := P.gluedChainPrefixLeftCoverSideHomeomorph k j hjk
  let u := P.gluedChainPrefixInclusion j x
  change FundamentalGroup ↥(P.gluedChainPrefixCoverSide k j true) (H u) ≃*
    FundamentalGroup ↥(P.gluedChainPrefix j) x
  exact (fundamentalGroupHomeomorphEquiv H u).symm.trans
    (P.gluedChainPrefixFundamentalGroupEquiv j x)

/-- The inverse based equivalence takes every literal closed-prefix loop to
its inclusion into the original prefix neighborhood, followed by the
literal inclusion into the retained left side. -/
theorem gluedChainPrefixLeftCoverFundamentalGroupEquiv_symm_apply_loop
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val)
    (x : ↥(P.gluedChainPrefix j)) (p : Path x x) :
    (P.gluedChainPrefixLeftCoverFundamentalGroupEquiv k j hjk x).symm
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        ((p.map (P.gluedChainPrefixInclusion j).continuous).map
          (P.gluedChainPrefixLeftCoverSideHomeomorph k j hjk).continuous_toFun)) := by
  let H := P.gluedChainPrefixLeftCoverSideHomeomorph k j hjk
  let u := P.gluedChainPrefixInclusion j x
  change fundamentalGroupHomeomorphEquiv H u
      ((P.gluedChainPrefixFundamentalGroupEquiv j x).symm ⟦p⟧) = _
  rw [P.gluedChainPrefixFundamentalGroupEquiv_symm_apply_loop]
  change FundamentalGroup.map (H : C(↥(P.gluedChainPrefixNeighborhood j),
      ↥(P.gluedChainPrefixCoverSide k j true))) u
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (p.map (P.gluedChainPrefixInclusion j).continuous))) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        ((p.map (P.gluedChainPrefixInclusion j).continuous).map H.continuous_toFun))
  rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]

/-- The actual based group equivalence from the original full seam image to
the overlap retained inside a later prefix. -/
def gluedChainPrefixCoverOverlapFundamentalGroupEquiv
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val) (θ : Circle) :
    FundamentalGroup ↥(P.gluedMk '' P.seamNeighborhood j)
      (P.gluedSeamCircleInclusion j θ) ≃*
    FundamentalGroup ↥(P.gluedChainPrefixCoverOverlap k j)
      (P.gluedChainPrefixCoverOverlapHomeomorph k j hjk
        (P.gluedSeamCircleInclusion j θ)) :=
  fundamentalGroupHomeomorphEquiv
    (P.gluedChainPrefixCoverOverlapHomeomorph k j hjk)
    (P.gluedSeamCircleInclusion j θ)

/-- Every based loop in the original seam group is mapped by the literal
overlap homeomorphism; in particular this applies to the actual seam turn. -/
theorem gluedChainPrefixCoverOverlapFundamentalGroupEquiv_apply_loop
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val) (θ : Circle)
    (p : Path (P.gluedSeamCircleInclusion j θ)
      (P.gluedSeamCircleInclusion j θ)) :
    P.gluedChainPrefixCoverOverlapFundamentalGroupEquiv k j hjk θ
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (p.map (P.gluedChainPrefixCoverOverlapHomeomorph k j hjk).continuous_toFun)) := by
  let H := P.gluedChainPrefixCoverOverlapHomeomorph k j hjk
  change FundamentalGroup.map (H : C(↥(P.gluedMk '' P.seamNeighborhood j),
      ↥(P.gluedChainPrefixCoverOverlap k j)))
      (P.gluedSeamCircleInclusion j θ)
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) = _
  rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]

/-- The seam generator in the retained overlap is the literal image of the
original positive one-turn seam loop, without a new basepoint or orientation
choice. -/
theorem gluedChainPrefixCoverOverlapFundamentalGroupEquiv_oneTurn
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val) (θ : Circle) :
    P.gluedChainPrefixCoverOverlapFundamentalGroupEquiv k j hjk θ
      (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (P.gluedSeamOneTurnLoop j θ))) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          ((P.gluedSeamOneTurnLoop j θ).map
            (P.gluedChainPrefixCoverOverlapHomeomorph k j hjk).continuous_toFun)) :=
  P.gluedChainPrefixCoverOverlapFundamentalGroupEquiv_apply_loop k j hjk θ
    (P.gluedSeamOneTurnLoop j θ)

#print axioms gluedChainPrefixLeftCoverBasepoint
#print axioms gluedChainPrefixLeftCoverFundamentalGroupEquiv
#print axioms gluedChainPrefixLeftCoverFundamentalGroupEquiv_symm_apply_loop
#print axioms gluedChainPrefixCoverOverlapFundamentalGroupEquiv
#print axioms gluedChainPrefixCoverOverlapFundamentalGroupEquiv_apply_loop
#print axioms gluedChainPrefixCoverOverlapFundamentalGroupEquiv_oneTurn

end

end ExerciseGluingPreparation
end SystolicGrowth
