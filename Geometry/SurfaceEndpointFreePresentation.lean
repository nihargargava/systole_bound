module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingEndpointPunctureBridge
public import Geometry.SurfaceOnePunctureFreePresentation
public import Geometry.SurfaceTwoCenterBoundarySpine

@[expose] public section

/-!
# Actual free presentations at the endpoints of the glued chain

The first and last components have one active puncture. Identify each actual
endpoint component with its original one-center punctured surface, then apply
the physical Dirichlet free presentation at the original angle-one basepoint.
-/

open UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

def Internal.SurfaceEndpointFreePresentationHelpers.endpointFirstIndex (hn : 2 ≤ n) : Fin n := ⟨0, by omega⟩

def Internal.SurfaceEndpointFreePresentationHelpers.endpointLastIndex (hn : 2 ≤ n) : Fin n := ⟨n - 1, by omega⟩

/-- The first component's actual outgoing puncture has the physical free
presentation supplied by its Dirichlet segments. -/
def firstEndpointPunctureFreeEquiv
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (B : DirichletBoundarySegments (X (Internal.SurfaceEndpointFreePresentationHelpers.endpointFirstIndex hn))
      (P.centers (Internal.SurfaceEndpointFreePresentationHelpers.endpointFirstIndex hn)).2) :
    FundamentalGroup
        (P.CenterPuncturedChainComponent (Internal.SurfaceEndpointFreePresentationHelpers.endpointFirstIndex hn))
        (P.componentRightPolarBoundaryMap (Internal.SurfaceEndpointFreePresentationHelpers.endpointFirstIndex hn) 1) ≃*
      FreeGroup B.IntrinsicBoundaryNonTreeEdge := by
  let i := Internal.SurfaceEndpointFreePresentationHelpers.endpointFirstIndex hn
  let q := P.componentRightPolarBoundaryMap i 1
  exact (P.firstEndpointPuncturedFundamentalGroupEquiv hn q).trans
    (B.intrinsicBoundaryPunctureFundamentalGroupFreeEquivAtAngle
      (gluingRadius C g) P.radius_pos (P.radius_twice_lt_componentSystole i) 1)

/-- The first component's original outgoing one-turn loop is the actual
peripheral word in that endpoint's physical non-tree generators. -/
theorem firstEndpointPunctureFreeEquiv_rightPolarBoundaryLoop
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (B : DirichletBoundarySegments (X (Internal.SurfaceEndpointFreePresentationHelpers.endpointFirstIndex hn))
      (P.centers (Internal.SurfaceEndpointFreePresentationHelpers.endpointFirstIndex hn)).2) :
    P.firstEndpointPunctureFreeEquiv hn B
      ⟦P.componentRightPolarBoundaryLoop (Internal.SurfaceEndpointFreePresentationHelpers.endpointFirstIndex hn)⟧ =
      FreeGroup.mk B.intrinsicBoundaryPeripheralLetters := by
  let i := Internal.SurfaceEndpointFreePresentationHelpers.endpointFirstIndex hn
  let q := P.componentRightPolarBoundaryMap i 1
  change B.intrinsicBoundaryPunctureFundamentalGroupFreeEquivAtAngle
      (gluingRadius C g) P.radius_pos (P.radius_twice_lt_componentSystole i) 1
      ⟦(P.componentRightPolarBoundaryLoop i).map
        (P.firstEndpointCenterPuncturedHomeomorph hn).continuous⟧ = _
  have hmap : (P.componentRightPolarBoundaryLoop i).map
      (P.firstEndpointCenterPuncturedHomeomorph hn).continuous =
      (X i).dirichletPuncturePolarOneTurn (P.centers i).2 (gluingRadius C g)
        P.radius_pos (P.radius_twice_lt_componentSystole i) 1 := by
    convert P.firstEndpointHomeomorph_map_rightPolarBoundaryLoop hn using 1
    all_goals rfl
  rw [hmap]
  exact B.intrinsicBoundaryPunctureFundamentalGroupFreeEquivAtAngle_polarOneTurn
    (gluingRadius C g) P.radius_pos (P.radius_twice_lt_componentSystole i) 1

/-- The last component's actual incoming puncture has the physical free
presentation supplied by its Dirichlet segments. -/
def lastEndpointPunctureFreeEquiv
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (B : DirichletBoundarySegments (X (Internal.SurfaceEndpointFreePresentationHelpers.endpointLastIndex hn))
      (P.centers (Internal.SurfaceEndpointFreePresentationHelpers.endpointLastIndex hn)).1) :
    FundamentalGroup
        (P.CenterPuncturedChainComponent (Internal.SurfaceEndpointFreePresentationHelpers.endpointLastIndex hn))
        (P.componentLeftPolarBoundaryMap (Internal.SurfaceEndpointFreePresentationHelpers.endpointLastIndex hn) 1) ≃*
      FreeGroup B.IntrinsicBoundaryNonTreeEdge := by
  let i := Internal.SurfaceEndpointFreePresentationHelpers.endpointLastIndex hn
  let q := P.componentLeftPolarBoundaryMap i 1
  exact (P.lastEndpointPuncturedFundamentalGroupEquiv hn q).trans
    (B.intrinsicBoundaryPunctureFundamentalGroupFreeEquivAtAngle
      (gluingRadius C g) P.radius_pos (P.radius_twice_lt_componentSystole i) 1)

/-- The last component's original incoming one-turn loop is the actual
peripheral word in that endpoint's physical non-tree generators. -/
theorem lastEndpointPunctureFreeEquiv_leftPolarBoundaryLoop
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (B : DirichletBoundarySegments (X (Internal.SurfaceEndpointFreePresentationHelpers.endpointLastIndex hn))
      (P.centers (Internal.SurfaceEndpointFreePresentationHelpers.endpointLastIndex hn)).1) :
    P.lastEndpointPunctureFreeEquiv hn B
      ⟦P.componentLeftPolarBoundaryLoop (Internal.SurfaceEndpointFreePresentationHelpers.endpointLastIndex hn)⟧ =
      FreeGroup.mk B.intrinsicBoundaryPeripheralLetters := by
  let i := Internal.SurfaceEndpointFreePresentationHelpers.endpointLastIndex hn
  let q := P.componentLeftPolarBoundaryMap i 1
  change B.intrinsicBoundaryPunctureFundamentalGroupFreeEquivAtAngle
      (gluingRadius C g) P.radius_pos (P.radius_twice_lt_componentSystole i) 1
      ⟦(P.componentLeftPolarBoundaryLoop i).map
        (P.lastEndpointCenterPuncturedHomeomorph hn).continuous⟧ = _
  have hmap : (P.componentLeftPolarBoundaryLoop i).map
      (P.lastEndpointCenterPuncturedHomeomorph hn).continuous =
      (X i).dirichletPuncturePolarOneTurn (P.centers i).1 (gluingRadius C g)
        P.radius_pos (P.radius_twice_lt_componentSystole i) 1 := by
    convert P.lastEndpointHomeomorph_map_leftPolarBoundaryLoop hn using 1
    all_goals rfl
  rw [hmap]
  exact B.intrinsicBoundaryPunctureFundamentalGroupFreeEquivAtAngle_polarOneTurn
    (gluingRadius C g) P.radius_pos (P.radius_twice_lt_componentSystole i) 1

#print axioms firstEndpointPunctureFreeEquiv
#print axioms firstEndpointPunctureFreeEquiv_rightPolarBoundaryLoop
#print axioms lastEndpointPunctureFreeEquiv
#print axioms lastEndpointPunctureFreeEquiv_leftPolarBoundaryLoop

end

end SystolicGrowth.ExerciseGluingPreparation
