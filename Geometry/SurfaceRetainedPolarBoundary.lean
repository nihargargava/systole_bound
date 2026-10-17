module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingPuncturedComponentHomotopy
public import Geometry.SurfaceEndpointFreePresentation
public import Geometry.SurfaceTwoCenterBoundarySpine
public import Geometry.SurfaceTwoCenterCutSpine

@[expose] public section

/-!
# Retained polar boundaries and their actual punctured images

The incoming and outgoing polar circles already lie in each retained
component. This file exposes them before inclusion into the twice-punctured
carrier and records that inclusion preserves their maps and angle-one loops
literally.
-/

open Metric UpperHalfPlane
open scoped ContinuousMap Topology UpperHalfPlane unitInterval

namespace SystolicGrowth
namespace ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

def Internal.SurfaceRetainedPolarBoundaryHelpers.retainedFirstIndex (hn : 2 ≤ n) : Fin n := ⟨0, by omega⟩

def Internal.SurfaceRetainedPolarBoundaryHelpers.retainedLastIndex (hn : 2 ≤ n) : Fin n := ⟨n - 1, by omega⟩

def Internal.SurfaceRetainedPolarBoundaryHelpers.retainedPolarSphereMap (o : ℍ) (r : ℝ) (hr : 0 < r) :
    C(Circle, sphere o r) where
  toFun θ := ⟨gluingPolarPoint o θ r, by
    simpa only [mem_sphere, dist_comm] using dist_gluingPolarPoint o θ hr.le⟩
  continuous_toFun := by
    have hθ : Continuous (fun θ : Circle => (θ, r)) :=
      continuous_id.prodMk continuous_const
    exact ((gluingPolarPoint_continuous o).comp hθ).subtype_mk _

/-- The actual retained incoming polar circle, before its literal inclusion
into the component with both punctures removed. -/
def componentRetainedLeftPolarBoundaryMap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    C(Circle, P.ChainComponent i) := by
  let s := Internal.SurfaceRetainedPolarBoundaryHelpers.retainedPolarSphereMap (P.centers i).1 (gluingRadius C g) P.radius_pos
  exact ⟨fun θ => P.leftCirclePoint i (s θ),
    (P.leftCirclePoint_isEmbedding i).continuous.comp s.continuous⟩

/-- The actual retained outgoing polar circle, before its literal inclusion
into the component with both punctures removed. -/
def componentRetainedRightPolarBoundaryMap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    C(Circle, P.ChainComponent i) := by
  let s := Internal.SurfaceRetainedPolarBoundaryHelpers.retainedPolarSphereMap (P.centers i).2 (gluingRadius C g) P.radius_pos
  exact ⟨fun θ => P.rightCirclePoint i (s θ),
    (P.rightCirclePoint_isEmbedding i).continuous.comp s.continuous⟩

/-- Literal inclusion sends the retained incoming circle to the existing
polar circle in the actual twice-punctured carrier. -/
theorem componentPunctureInclusion_comp_retainedLeftPolarBoundaryMap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    (P.componentPunctureInclusion i).comp (P.componentRetainedLeftPolarBoundaryMap i) =
      P.componentLeftPolarBoundaryMap i := by
  apply ContinuousMap.ext
  intro θ
  rfl

/-- Literal inclusion sends the retained outgoing circle to the existing
polar circle in the actual twice-punctured carrier. -/
theorem componentPunctureInclusion_comp_retainedRightPolarBoundaryMap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    (P.componentPunctureInclusion i).comp (P.componentRetainedRightPolarBoundaryMap i) =
      P.componentRightPolarBoundaryMap i := by
  apply ContinuousMap.ext
  intro θ
  rfl

/-- The positive one-turn loop on the retained incoming boundary, based at
its original angle-one point. -/
def componentRetainedLeftPolarBoundaryLoop
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Path (P.componentRetainedLeftPolarBoundaryMap i 1)
      (P.componentRetainedLeftPolarBoundaryMap i 1) :=
  (circleOneTurnLoop 1).map (P.componentRetainedLeftPolarBoundaryMap i).continuous

/-- The positive one-turn loop on the retained outgoing boundary, based at
its original angle-one point. -/
def componentRetainedRightPolarBoundaryLoop
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Path (P.componentRetainedRightPolarBoundaryMap i 1)
      (P.componentRetainedRightPolarBoundaryMap i 1) :=
  (circleOneTurnLoop 1).map (P.componentRetainedRightPolarBoundaryMap i).continuous

/-- Inclusion preserves the retained incoming one-turn representative
literally, with no change of basepoint or orientation. -/
theorem componentPunctureInclusion_map_retainedLeftPolarBoundaryLoop
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    (P.componentRetainedLeftPolarBoundaryLoop i).map
        (P.componentPunctureInclusion i).continuous =
      P.componentLeftPolarBoundaryLoop i := by
  rw [componentRetainedLeftPolarBoundaryLoop, componentLeftPolarBoundaryLoop,
    Path.map_map]
  congr 1

/-- Inclusion preserves the retained outgoing one-turn representative
literally, with no change of basepoint or orientation. -/
theorem componentPunctureInclusion_map_retainedRightPolarBoundaryLoop
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    (P.componentRetainedRightPolarBoundaryLoop i).map
        (P.componentPunctureInclusion i).continuous =
      P.componentRightPolarBoundaryLoop i := by
  rw [componentRetainedRightPolarBoundaryLoop, componentRightPolarBoundaryLoop,
    Path.map_map]
  congr 1

/-- The actual incoming polar connector, lifted to the retained component
with the same chosen angle and the same physical cut endpoint. -/
def componentRetainedTwoCenterCutLeftConnector
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Path (P.componentRetainedLeftPolarBoundaryMap i 1)
      (P.componentTwoCenterCutArc i 0) :=
  ((Circle.path 1 (P.componentTwoCenterCutLeftAngle i)).map
    (P.componentRetainedLeftPolarBoundaryMap i).continuous).cast rfl (by
      apply Subtype.ext
      exact (congrArg Subtype.val (P.componentTwoCenterCutLeftAngle_spec i)).symm)

/-- The actual outgoing polar connector in the retained component, with
its unchanged cut endpoint and angle-one endpoint. -/
def componentRetainedTwoCenterCutRightConnector
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Path (P.componentTwoCenterCutArc i 1)
      (P.componentRetainedRightPolarBoundaryMap i 1) :=
  ((Circle.path (P.componentTwoCenterCutRightAngle i) 1).map
    (P.componentRetainedRightPolarBoundaryMap i).continuous).cast (by
      apply Subtype.ext
      exact (congrArg Subtype.val (P.componentTwoCenterCutRightAngle_spec i)).symm) rfl

/-- The prescribed physical cut path already lies in the retained
component; no retraction-selected replacement connector is introduced. -/
def componentRetainedTwoCenterCutBasedPath
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Path (P.componentRetainedLeftPolarBoundaryMap i 1)
      (P.componentRetainedRightPolarBoundaryMap i 1) :=
  ((P.componentRetainedTwoCenterCutLeftConnector i).trans
    (P.componentTwoCenterCutArc i)).trans
      (P.componentRetainedTwoCenterCutRightConnector i)

set_option backward.isDefEq.respectTransparency false in
/-- Literal puncture inclusion preserves the entire prescribed retained
cut path, including both original polar connectors. -/
theorem componentPunctureInclusion_map_retainedTwoCenterCutBasedPath
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    (P.componentRetainedTwoCenterCutBasedPath i).map
      (P.componentPunctureInclusion i).continuous =
        P.componentTwoCenterCutBasedPath i := by
  have hleft : (P.componentRetainedTwoCenterCutLeftConnector i).map
      (P.componentPunctureInclusion i).continuous =
        P.componentTwoCenterCutLeftConnector i := by
    apply Path.ext
    funext t
    rfl
  have hright : (P.componentRetainedTwoCenterCutRightConnector i).map
      (P.componentPunctureInclusion i).continuous =
        P.componentTwoCenterCutRightConnector i := by
    apply Path.ext
    funext t
    rfl
  unfold componentRetainedTwoCenterCutBasedPath componentTwoCenterCutBasedPath
  rw [Path.map_trans, Path.map_trans, hleft, hright]

/-- The retained outgoing positive loop based at the incoming angle-one
point along the literal retained physical cut. -/
def componentRetainedRightPolarBoundaryLoopAlongCut
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Path (P.componentRetainedLeftPolarBoundaryMap i 1)
      (P.componentRetainedLeftPolarBoundaryMap i 1) :=
  (P.componentRetainedTwoCenterCutBasedPath i).trans
    ((P.componentRetainedRightPolarBoundaryLoop i).trans
      (P.componentRetainedTwoCenterCutBasedPath i).symm)

set_option backward.isDefEq.respectTransparency false in
/-- Inclusion preserves the outgoing cut-conjugated loop as an actual
path, not just up to homotopy or after a change of basepoint. -/
theorem componentPunctureInclusion_map_retainedRightPolarBoundaryLoopAlongCut
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    (P.componentRetainedRightPolarBoundaryLoopAlongCut i).map
      (P.componentPunctureInclusion i).continuous =
        P.componentRightPolarBoundaryLoopAlongCut i := by
  unfold componentRetainedRightPolarBoundaryLoopAlongCut componentRightPolarBoundaryLoopAlongCut
  rw [Path.map_trans, Path.map_trans, ← Path.map_symm,
    P.componentPunctureInclusion_map_retainedTwoCenterCutBasedPath,
    P.componentPunctureInclusion_map_retainedRightPolarBoundaryLoop]

set_option backward.isDefEq.respectTransparency false in
/-- Transport a based marking of the actual center-punctured component back
to the retained carrier at the unchanged incoming polar point. -/
def componentRetainedPolarMarkedFreeEquiv_of_punctureMarking
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {G : Type*} [Group G]
    (eOriginal : FundamentalGroup (P.CenterPuncturedChainComponent i)
      (P.componentLeftPolarBoundaryMap i 1) ≃* G) :
    FundamentalGroup (P.ChainComponent i)
      (P.componentRetainedLeftPolarBoundaryMap i 1) ≃* G :=
  (P.componentPunctureFundamentalGroupEquiv i
    (P.componentRetainedLeftPolarBoundaryMap i 1)).symm.trans eOriginal

set_option backward.isDefEq.respectTransparency false in
/-- The transported retained marking preserves both literal peripheral
values: the incoming positive loop and the outgoing positive loop conjugated
by the prescribed retained cut path. -/
theorem componentRetainedPolarMarkedFreeEquiv_of_punctureMarking_values
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {G : Type*} [Group G]
    (eOriginal : FundamentalGroup (P.CenterPuncturedChainComponent i)
      (P.componentLeftPolarBoundaryMap i 1) ≃* G)
    (wL wR : G)
    (hL : eOriginal ⟦P.componentLeftPolarBoundaryLoop i⟧ = wL)
    (hR : eOriginal ⟦P.componentRightPolarBoundaryLoopAlongCut i⟧ = wR) :
    P.componentRetainedPolarMarkedFreeEquiv_of_punctureMarking i eOriginal
        ⟦P.componentRetainedLeftPolarBoundaryLoop i⟧ = wL ∧
      P.componentRetainedPolarMarkedFreeEquiv_of_punctureMarking i eOriginal
        ⟦P.componentRetainedRightPolarBoundaryLoopAlongCut i⟧ = wR := by
  let q := P.componentRetainedLeftPolarBoundaryMap i 1
  let E := P.componentPunctureFundamentalGroupEquiv i q
  have hleftBack : E.symm ⟦P.componentRetainedLeftPolarBoundaryLoop i⟧ =
      ⟦P.componentLeftPolarBoundaryLoop i⟧ := by
    apply E.injective
    rw [E.apply_symm_apply,
      ← P.componentPunctureInclusion_map_retainedLeftPolarBoundaryLoop i]
    exact (P.componentPunctureFundamentalGroupEquiv_map_loop i q
      (P.componentRetainedLeftPolarBoundaryLoop i)).symm
  have hrightBack : E.symm ⟦P.componentRetainedRightPolarBoundaryLoopAlongCut i⟧ =
      ⟦P.componentRightPolarBoundaryLoopAlongCut i⟧ := by
    apply E.injective
    rw [E.apply_symm_apply,
      ← P.componentPunctureInclusion_map_retainedRightPolarBoundaryLoopAlongCut i]
    exact (P.componentPunctureFundamentalGroupEquiv_map_loop i q
      (P.componentRetainedRightPolarBoundaryLoopAlongCut i)).symm
  change eOriginal (E.symm ⟦P.componentRetainedLeftPolarBoundaryLoop i⟧) = wL ∧
    eOriginal (E.symm ⟦P.componentRetainedRightPolarBoundaryLoopAlongCut i⟧) = wR
  exact ⟨(congrArg eOriginal hleftBack).trans hL,
    (congrArg eOriginal hrightBack).trans hR⟩

/-- The first retained component's actual outgoing puncture has the physical
free presentation, transported through the literal puncture inclusion. -/
def firstEndpointRetainedFreeEquiv
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (B : DirichletBoundarySegments (X (Internal.SurfaceRetainedPolarBoundaryHelpers.retainedFirstIndex hn))
      (P.centers (Internal.SurfaceRetainedPolarBoundaryHelpers.retainedFirstIndex hn)).2) :
    FundamentalGroup (P.ChainComponent (Internal.SurfaceRetainedPolarBoundaryHelpers.retainedFirstIndex hn))
      (P.componentRetainedRightPolarBoundaryMap (Internal.SurfaceRetainedPolarBoundaryHelpers.retainedFirstIndex hn) 1) ≃*
      FreeGroup B.IntrinsicBoundaryNonTreeEdge := by
  let i := Internal.SurfaceRetainedPolarBoundaryHelpers.retainedFirstIndex hn
  let q := P.componentRetainedRightPolarBoundaryMap i 1
  exact (P.componentPunctureFundamentalGroupEquiv i q).symm.trans
    (P.firstEndpointPunctureFreeEquiv hn B)

/-- The first retained outgoing one-turn is the peripheral word in the
physical non-tree generators of its endpoint's Dirichlet segments. -/
theorem firstEndpointRetainedFreeEquiv_rightPolarBoundaryLoop
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (B : DirichletBoundarySegments (X (Internal.SurfaceRetainedPolarBoundaryHelpers.retainedFirstIndex hn))
      (P.centers (Internal.SurfaceRetainedPolarBoundaryHelpers.retainedFirstIndex hn)).2) :
    P.firstEndpointRetainedFreeEquiv hn B
      ⟦P.componentRetainedRightPolarBoundaryLoop (Internal.SurfaceRetainedPolarBoundaryHelpers.retainedFirstIndex hn)⟧ =
      FreeGroup.mk B.intrinsicBoundaryPeripheralLetters := by
  let i := Internal.SurfaceRetainedPolarBoundaryHelpers.retainedFirstIndex hn
  change P.firstEndpointPunctureFreeEquiv hn B
    ⟦(P.componentRetainedRightPolarBoundaryLoop i).map
      (P.componentPunctureInclusion i).continuous⟧ = _
  rw [P.componentPunctureInclusion_map_retainedRightPolarBoundaryLoop]
  convert P.firstEndpointPunctureFreeEquiv_rightPolarBoundaryLoop hn B using 1
  all_goals rfl

/-- The last retained component's actual incoming puncture has the physical
free presentation, transported through the literal puncture inclusion. -/
def lastEndpointRetainedFreeEquiv
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (B : DirichletBoundarySegments (X (Internal.SurfaceRetainedPolarBoundaryHelpers.retainedLastIndex hn))
      (P.centers (Internal.SurfaceRetainedPolarBoundaryHelpers.retainedLastIndex hn)).1) :
    FundamentalGroup (P.ChainComponent (Internal.SurfaceRetainedPolarBoundaryHelpers.retainedLastIndex hn))
      (P.componentRetainedLeftPolarBoundaryMap (Internal.SurfaceRetainedPolarBoundaryHelpers.retainedLastIndex hn) 1) ≃*
      FreeGroup B.IntrinsicBoundaryNonTreeEdge := by
  let i := Internal.SurfaceRetainedPolarBoundaryHelpers.retainedLastIndex hn
  let q := P.componentRetainedLeftPolarBoundaryMap i 1
  exact (P.componentPunctureFundamentalGroupEquiv i q).symm.trans
    (P.lastEndpointPunctureFreeEquiv hn B)

/-- The last retained incoming one-turn is the peripheral word in the
physical non-tree generators of its endpoint's Dirichlet segments. -/
theorem lastEndpointRetainedFreeEquiv_leftPolarBoundaryLoop
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (B : DirichletBoundarySegments (X (Internal.SurfaceRetainedPolarBoundaryHelpers.retainedLastIndex hn))
      (P.centers (Internal.SurfaceRetainedPolarBoundaryHelpers.retainedLastIndex hn)).1) :
    P.lastEndpointRetainedFreeEquiv hn B
      ⟦P.componentRetainedLeftPolarBoundaryLoop (Internal.SurfaceRetainedPolarBoundaryHelpers.retainedLastIndex hn)⟧ =
      FreeGroup.mk B.intrinsicBoundaryPeripheralLetters := by
  let i := Internal.SurfaceRetainedPolarBoundaryHelpers.retainedLastIndex hn
  change P.lastEndpointPunctureFreeEquiv hn B
    ⟦(P.componentRetainedLeftPolarBoundaryLoop i).map
      (P.componentPunctureInclusion i).continuous⟧ = _
  rw [P.componentPunctureInclusion_map_retainedLeftPolarBoundaryLoop]
  convert P.lastEndpointPunctureFreeEquiv_leftPolarBoundaryLoop hn B using 1
  all_goals rfl

#print axioms componentRetainedLeftPolarBoundaryMap
#print axioms componentRetainedRightPolarBoundaryMap
#print axioms componentPunctureInclusion_comp_retainedLeftPolarBoundaryMap
#print axioms componentPunctureInclusion_comp_retainedRightPolarBoundaryMap
#print axioms componentPunctureInclusion_map_retainedLeftPolarBoundaryLoop
#print axioms componentPunctureInclusion_map_retainedRightPolarBoundaryLoop
#print axioms componentPunctureInclusion_map_retainedTwoCenterCutBasedPath
#print axioms componentPunctureInclusion_map_retainedRightPolarBoundaryLoopAlongCut
#print axioms componentRetainedPolarMarkedFreeEquiv_of_punctureMarking
#print axioms componentRetainedPolarMarkedFreeEquiv_of_punctureMarking_values
#print axioms firstEndpointRetainedFreeEquiv
#print axioms firstEndpointRetainedFreeEquiv_rightPolarBoundaryLoop
#print axioms lastEndpointRetainedFreeEquiv
#print axioms lastEndpointRetainedFreeEquiv_leftPolarBoundaryLoop

end
end ExerciseGluingPreparation
end SystolicGrowth
