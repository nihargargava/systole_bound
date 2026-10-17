module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingPuncturedComponentHomotopy
public import Geometry.GluingConnected
public import Geometry.GluingSeamFundamentalGroup
public import Mathlib.Topology.Connected.LocallyPathConnected

@[expose] public section

/-!
# The two actual polar boundaries in a center-punctured component

The middle component of a chain has two actual punctures. This file records
their original polar loops in that center-punctured quotient and constructs a
path between their literal angle-one basepoints. The path gives the based
conjugate of the second peripheral loop. It does not assert that this path is
embedded or that its complement is a spine.
-/

open Set Metric
open scoped UpperHalfPlane Topology unitInterval ContinuousMap

namespace SystolicGrowth
namespace ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

def Internal.SurfaceTwoCenterBoundarySpineHelpers.polarSphereMap (o : ℍ) (r : ℝ) (hr : 0 < r) :
    C(Circle, sphere o r) where
  toFun θ := ⟨gluingPolarPoint o θ r, by
    simpa only [mem_sphere, dist_comm] using dist_gluingPolarPoint o θ hr.le⟩
  continuous_toFun := by
    have hθ : Continuous (fun θ : Circle => (θ, r)) :=
      continuous_id.prodMk continuous_const
    exact ((gluingPolarPoint_continuous o).comp hθ).subtype_mk _

/-- The actual two-center-punctured component is connected. Its existing
radial strong deformation retraction moves every point to the connected
retained component, while fixing that component pointwise. -/
theorem componentCenterPuncturedConnectedSpace
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    ConnectedSpace (P.CenterPuncturedChainComponent i) := by
  let A := P.CenterPuncturedChainComponent i
  letI : PreconnectedSpace A := by
    apply preconnectedSpace_of_forall_constant
    intro f hf x y
    letI : ConnectedSpace (P.ChainComponent i) :=
      isConnected_iff_connectedSpace.mp (P.puncturedComponentSet_isConnected i)
    let track (q : A) : Path q (P.componentPunctureInclusion i
        (P.componentPunctureRetraction i q)) := {
      toFun := fun t => P.componentPunctureHomotopyMap i (t, q)
      continuous_toFun := (P.componentPunctureHomotopyMap i).continuous.comp
        (continuous_id.prodMk continuous_const)
      source' := by simp
      target' := by apply Subtype.ext; rfl }
    have htrack (q : A) : f q =
        f (P.componentPunctureInclusion i (P.componentPunctureRetraction i q)) := by
      have hcont : Continuous (fun t : I => f (track q t)) := hf.comp (track q).continuous
      have h := PreconnectedSpace.constant (inferInstance : PreconnectedSpace I) hcont
        (x := 0) (y := 1)
      rw [(track q).source, (track q).target] at h
      exact h
    have hret : f (P.componentPunctureInclusion i (P.componentPunctureRetraction i x)) =
        f (P.componentPunctureInclusion i (P.componentPunctureRetraction i y)) :=
      PreconnectedSpace.constant (inferInstance : PreconnectedSpace (P.ChainComponent i))
        (hf.comp (P.componentPunctureInclusion i).continuous)
        (x := P.componentPunctureRetraction i x)
        (y := P.componentPunctureRetraction i y)
    exact (htrack x).trans (hret.trans (htrack y).symm)
  exact {
    toPreconnectedSpace := inferInstance
    toNonempty := by
      letI : ConnectedSpace (P.ChainComponent i) :=
        isConnected_iff_connectedSpace.mp (P.puncturedComponentSet_isConnected i)
      exact ⟨P.componentPunctureInclusion i (Classical.choice inferInstance)⟩ }

/-- The two-center-punctured component is an open subspace of the original
surface quotient. -/
theorem componentCenterPuncturedSet_isOpen
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    IsOpen (P.componentCenterPuncturedSet i) := by
  letI : T2Space (X i).Carrier := inferInstance
  rw [P.componentCenterPuncturedSet_eq i]
  have hdel : IsClosed
      ((if 0 < i.1 then {(Quotient.mk'' (P.centers i).1 : (X i).Carrier)} else ∅) ∪
       (if i.1 + 1 < n then {(Quotient.mk'' (P.centers i).2 : (X i).Carrier)} else ∅)) := by
    apply IsClosed.union
    · by_cases h : 0 < i.1
      · rw [if_pos h]
        exact isClosed_singleton
      · simp [h]
    · by_cases h : i.1 + 1 < n
      · rw [if_pos h]
        exact isClosed_singleton
      · simp [h]
  exact hdel.isOpen_compl

/-- The actual quotient with its two centers removed is path connected. The
quotient is locally path connected, and the previous theorem supplies its
connectedness without adding a connectivity hypothesis. -/
theorem componentCenterPuncturedPathConnectedSpace
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    PathConnectedSpace (P.CenterPuncturedChainComponent i) := by
  have hconn : IsConnected (P.componentCenterPuncturedSet i) :=
    isConnected_iff_connectedSpace.mpr (P.componentCenterPuncturedConnectedSpace i)
  have hpath : IsPathConnected (P.componentCenterPuncturedSet i) :=
    (P.componentCenterPuncturedSet_isOpen i).isConnected_iff_isPathConnected.mp hconn
  exact isPathConnected_iff_pathConnectedSpace.mp hpath

/-- The literal incoming polar circle, included in the actual quotient with
both punctures removed. -/
def componentLeftPolarBoundaryMap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    C(Circle, P.CenterPuncturedChainComponent i) := by
  let s := Internal.SurfaceTwoCenterBoundarySpineHelpers.polarSphereMap (P.centers i).1 (gluingRadius C g) P.radius_pos
  exact (P.componentPunctureInclusion i).comp
    ⟨fun θ => P.leftCirclePoint i (s θ),
      (P.leftCirclePoint_isEmbedding i).continuous.comp s.continuous⟩

/-- The literal outgoing polar circle, included in the actual quotient with
both punctures removed. -/
def componentRightPolarBoundaryMap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    C(Circle, P.CenterPuncturedChainComponent i) := by
  let s := Internal.SurfaceTwoCenterBoundarySpineHelpers.polarSphereMap (P.centers i).2 (gluingRadius C g) P.radius_pos
  exact (P.componentPunctureInclusion i).comp
    ⟨fun θ => P.rightCirclePoint i (s θ),
      (P.rightCirclePoint_isEmbedding i).continuous.comp s.continuous⟩

/-- The original positive one-turn loop around the actual left puncture. -/
def componentLeftPolarBoundaryLoop
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Path (P.componentLeftPolarBoundaryMap i 1) (P.componentLeftPolarBoundaryMap i 1) :=
  (circleOneTurnLoop 1).map (P.componentLeftPolarBoundaryMap i).continuous

/-- The original positive one-turn loop around the actual right puncture. -/
def componentRightPolarBoundaryLoop
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Path (P.componentRightPolarBoundaryMap i 1) (P.componentRightPolarBoundaryMap i 1) :=
  (circleOneTurnLoop 1).map (P.componentRightPolarBoundaryMap i).continuous

@[simp]
theorem componentLeftPolarBoundaryLoop_apply_coe
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (t : I) :
    (P.componentLeftPolarBoundaryLoop i t).1 =
      (Quotient.mk'' (gluingPolarPoint (P.centers i).1
        (circleOneTurnLoop 1 t) (gluingRadius C g)) : (X i).Carrier) := rfl

@[simp]
theorem componentRightPolarBoundaryLoop_apply_coe
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (t : I) :
    (P.componentRightPolarBoundaryLoop i t).1 =
      (Quotient.mk'' (gluingPolarPoint (P.centers i).2
        (circleOneTurnLoop 1 t) (gluingRadius C g)) : (X i).Carrier) := rfl

/-- A genuine path in the original two-center-punctured quotient joining the
actual incoming and outgoing polar basepoints. No abstract peripheral
presentation or preselected boundary word enters this construction. -/
def componentTwoCenterBoundaryArc
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (_hleft : 0 < i.1) (_hright : i.1 + 1 < n) :
    Path (P.componentLeftPolarBoundaryMap i 1) (P.componentRightPolarBoundaryMap i 1) := by
  letI : PathConnectedSpace (P.CenterPuncturedChainComponent i) :=
    P.componentCenterPuncturedPathConnectedSpace i
  exact PathConnectedSpace.somePath _ _

/-- Retain the original outgoing boundary representative as a loop based at
the incoming basepoint by conjugating with the actual cut path. -/
def componentRightPolarBoundaryLoopAtLeft
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (hleft : 0 < i.1) (hright : i.1 + 1 < n) :
    Path (P.componentLeftPolarBoundaryMap i 1) (P.componentLeftPolarBoundaryMap i 1) :=
  let arc := P.componentTwoCenterBoundaryArc i hleft hright
  arc.trans ((P.componentRightPolarBoundaryLoop i).trans arc.symm)

#print axioms componentCenterPuncturedConnectedSpace
#print axioms componentCenterPuncturedPathConnectedSpace
#print axioms componentLeftPolarBoundaryLoop
#print axioms componentRightPolarBoundaryLoopAtLeft

end
end ExerciseGluingPreparation
end SystolicGrowth
