module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceTwoCenterCutSpine
public import Geometry.SurfaceTwoCenterPolarRadiusHomotopy

@[expose] public section

/-!
# Preserve cut-based peripheral loops while shrinking polar radii

The radius homotopies move the literal left and right angle-one basepoints to
their original gluing-radius basepoints.  Concatenating these tracks with the
original concrete cut path gives a small-radius connector.  Its transported
right positive loop is exactly the original right loop conjugated along that
cut.  This file makes no claim that the connector lies in a coordinate disk.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane Topology unitInterval ContinuousMap

namespace SystolicGrowth
namespace ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The left angle-one endpoint equality used to cast the original cut path
onto the endpoint of the literal gluing-radius polar map. -/
theorem twoCenterPolarBoundaryMap_gluingRadius_one_left
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    P.twoCenterPolarBoundaryMap i true (gluingRadius C g) P.radius_pos le_rfl 1 =
      P.componentLeftPolarBoundaryMap i 1 := by
  exact congrArg (fun f : C(Circle, P.CenterPuncturedChainComponent i) => f 1)
    (P.twoCenterPolarBoundaryMap_gluingRadius_left i)

/-- The right angle-one endpoint equality used to cast the original cut path
onto the endpoint of the literal gluing-radius polar map. -/
theorem twoCenterPolarBoundaryMap_gluingRadius_one_right
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    P.twoCenterPolarBoundaryMap i false (gluingRadius C g) P.radius_pos le_rfl 1 =
      P.componentRightPolarBoundaryMap i 1 := by
  exact congrArg (fun f : C(Circle, P.CenterPuncturedChainComponent i) => f 1)
    (P.twoCenterPolarBoundaryMap_gluingRadius_right i)

/-- The literal positive one-turn polar loop at an arbitrary allowed small
radius in the original two-center-punctured component. -/
def componentTwoCenterSmallPolarBoundaryLoop
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (b : Bool)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) :
    Path (P.twoCenterPolarBoundaryMap i b ρ hρ hρr 1)
      (P.twoCenterPolarBoundaryMap i b ρ hρ hρr 1) :=
  (circleOneTurnLoop 1).map (P.twoCenterPolarBoundaryMap i b ρ hρ hρr).continuous

private theorem gluingRadiusLeftLoop_cast
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    (circleOneTurnLoop 1).map
        (P.twoCenterPolarBoundaryMap i true (gluingRadius C g) P.radius_pos le_rfl).continuous =
      (P.componentLeftPolarBoundaryLoop i).cast
        (P.twoCenterPolarBoundaryMap_gluingRadius_one_left i)
        (P.twoCenterPolarBoundaryMap_gluingRadius_one_left i) := by
  apply Path.ext
  funext t
  simp only [Path.cast_coe, Path.map_coe, Function.comp_apply,
    componentLeftPolarBoundaryLoop, twoCenterPolarBoundaryMap_gluingRadius_left]

private theorem gluingRadiusRightLoop_cast
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    (circleOneTurnLoop 1).map
        (P.twoCenterPolarBoundaryMap i false (gluingRadius C g) P.radius_pos le_rfl).continuous =
      (P.componentRightPolarBoundaryLoop i).cast
        (P.twoCenterPolarBoundaryMap_gluingRadius_one_right i)
        (P.twoCenterPolarBoundaryMap_gluingRadius_one_right i) := by
  apply Path.ext
  funext t
  simp only [Path.cast_coe, Path.map_coe, Function.comp_apply,
    componentRightPolarBoundaryLoop, twoCenterPolarBoundaryMap_gluingRadius_right]

private theorem transportPathClass_cast
    {Z : Type*} [TopologicalSpace Z] {x y y' : Z}
    (γ : Path x y) (p : Path x x) (L : Path y' y') (h : y' = y)
    (hRaw : FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (γ.symm.trans (p.trans γ))) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (L.cast h.symm h.symm))) :
    FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          ((γ.cast rfl h).symm.trans (p.trans (γ.cast rfl h)))) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L) := by
  cases h
  simpa using hRaw

def componentTwoCenterLeftPolarRadiusPathToOriginal
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) :
    Path (P.twoCenterPolarBoundaryMap i true ρ hρ hρr 1)
      (P.componentLeftPolarBoundaryMap i 1) :=
  (P.twoCenterPolarRadiusBasepointPath i true ρ (gluingRadius C g)
    hρ P.radius_pos hρr le_rfl).cast rfl
      (P.twoCenterPolarBoundaryMap_gluingRadius_one_left i).symm

def componentTwoCenterRightPolarRadiusPathToOriginal
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) :
    Path (P.twoCenterPolarBoundaryMap i false ρ hρ hρr 1)
      (P.componentRightPolarBoundaryMap i 1) :=
  (P.twoCenterPolarRadiusBasepointPath i false ρ (gluingRadius C g)
    hρ P.radius_pos hρr le_rfl).cast rfl
      (P.twoCenterPolarBoundaryMap_gluingRadius_one_right i).symm

/-- The actual small-radius connector: left radius track, original concrete
cut path, then the reversed right radius track.  Each radius track is cast to
the original endpoint using the exact gluing-radius map identity. -/
def componentTwoCenterSmallPolarCutBasedPath
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) :
    Path (P.twoCenterPolarBoundaryMap i true ρ hρ hρr 1)
      (P.twoCenterPolarBoundaryMap i false ρ hρ hρr 1) := by
  exact
    (P.componentTwoCenterLeftPolarRadiusPathToOriginal i ρ hρ hρr |>.trans
      (P.componentTwoCenterCutBasedPath i)).trans
      (P.componentTwoCenterRightPolarRadiusPathToOriginal i ρ hρ hρr).symm

/-- Expose the exact prescribed connector at the gluing-radius endpoints.
The private endpoint casts do not change its path values or associativity;
the reversed right track is still the original shrinking track. -/
theorem componentTwoCenterSmallPolarCutBasedPath_eq_radius_cut
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) :
    P.componentTwoCenterSmallPolarCutBasedPath i ρ hρ hρr =
      (((P.twoCenterPolarRadiusBasepointPath i true ρ (gluingRadius C g)
          hρ P.radius_pos hρr le_rfl).trans
        ((P.componentTwoCenterCutBasedPath i).cast
          (P.twoCenterPolarBoundaryMap_gluingRadius_one_left i)
          (P.twoCenterPolarBoundaryMap_gluingRadius_one_right i))).trans
        (P.twoCenterPolarRadiusBasepointPath i false ρ (gluingRadius C g)
          hρ P.radius_pos hρr le_rfl).symm) := by
  apply Path.ext
  funext t
  rfl

#print axioms componentTwoCenterSmallPolarCutBasedPath_eq_radius_cut

/-- Conjugate the small right positive polar loop by the small-radius cut
connector, based at the small left angle-one point. -/
def componentRightSmallPolarBoundaryLoopAlongCut
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) :
    Path (P.twoCenterPolarBoundaryMap i true ρ hρ hρr 1)
      (P.twoCenterPolarBoundaryMap i true ρ hρ hρr 1) :=
  let conn := P.componentTwoCenterSmallPolarCutBasedPath i ρ hρ hρr
  conn.trans ((P.componentTwoCenterSmallPolarBoundaryLoop i false ρ hρ hρr).trans conn.symm)

private theorem basedCutConjugate_transport_pathClass
    {Z : Type*} [TopologicalSpace Z] {x y z w : Z}
    (a : Path x y) (d : Path y z) (b : Path w z) (q : Path w w) :
    Path.Homotopic.Quotient.mk
      (a.symm.trans
        (((((a.trans d).trans b.symm).trans
          (q.trans ((a.trans d).trans b.symm).symm)).trans a))) =
    Path.Homotopic.Quotient.mk (d.trans ((b.symm.trans (q.trans b)).trans d.symm)) := by
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.trans_symm, Path.symm_symm, Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans]
  rw [← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans,
    Path.Homotopic.Quotient.trans_refl]

/-- Transporting the small left positive one-turn loop along its actual
radius track, cast to the original endpoint, recovers the original left
peripheral loop class. -/
theorem componentLeftSmallPolarBoundaryLoop_transport
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath
        (P.componentTwoCenterLeftPolarRadiusPathToOriginal i ρ hρ hρr)
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (P.componentTwoCenterSmallPolarBoundaryLoop i true ρ hρ hρr))) =
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (P.componentLeftPolarBoundaryLoop i)) := by
  let rawTrack := P.twoCenterPolarRadiusBasepointPath i true ρ (gluingRadius C g)
    hρ P.radius_pos hρr le_rfl
  let hleft := P.twoCenterPolarBoundaryMap_gluingRadius_one_left i
  have hRawTransport :=
    P.twoCenterPolarRadiusHomotopy_fundamentalGroup i true ρ (gluingRadius C g)
      hρ P.radius_pos hρr le_rfl
  have hRaw : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk
        (rawTrack.symm.trans
          ((P.componentTwoCenterSmallPolarBoundaryLoop i true ρ hρ hρr).trans rawTrack))) =
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      ((P.componentLeftPolarBoundaryLoop i).cast hleft hleft)) := by
    change FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          (rawTrack.symm.trans
            ((P.componentTwoCenterSmallPolarBoundaryLoop i true ρ hρ hρr).trans rawTrack))) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          ((P.componentLeftPolarBoundaryLoop i).cast hleft hleft)) at hRawTransport
    simpa only [componentTwoCenterSmallPolarBoundaryLoop, gluingRadiusLeftLoop_cast]
      using hRawTransport
  exact transportPathClass_cast rawTrack
    (P.componentTwoCenterSmallPolarBoundaryLoop i true ρ hρ hρr)
    (P.componentLeftPolarBoundaryLoop i) hleft.symm hRaw

/-- After transporting by the left radius track, the conjugated small right
positive loop is exactly the original right positive loop along the actual
cut, cast only to the radius-track endpoint identified by the gluing-radius
map theorem. -/
theorem componentRightSmallPolarBoundaryLoopAlongCut_transport
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath
        (P.componentTwoCenterLeftPolarRadiusPathToOriginal i ρ hρ hρr)
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (P.componentRightSmallPolarBoundaryLoopAlongCut i ρ hρ hρr))) =
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (P.componentRightPolarBoundaryLoopAlongCut i)) := by
  let rawLeftTrack := P.twoCenterPolarRadiusBasepointPath i true ρ
    (gluingRadius C g) hρ P.radius_pos hρr le_rfl
  let rawRightTrack := P.twoCenterPolarRadiusBasepointPath i false ρ
    (gluingRadius C g) hρ P.radius_pos hρr le_rfl
  let hright := P.twoCenterPolarBoundaryMap_gluingRadius_one_right i
  let leftTrack := P.componentTwoCenterLeftPolarRadiusPathToOriginal i ρ hρ hρr
  let rightTrack := P.componentTwoCenterRightPolarRadiusPathToOriginal i ρ hρ hρr
  let cut := P.componentTwoCenterCutBasedPath i
  let smallRight := P.componentTwoCenterSmallPolarBoundaryLoop i false ρ hρ hρr
  have hrightTransport := P.twoCenterPolarRadiusHomotopy_fundamentalGroup i false
    ρ (gluingRadius C g) hρ P.radius_pos hρr le_rfl
  have hrightRaw : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk
        (rawRightTrack.symm.trans (smallRight.trans rawRightTrack))) =
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      ((P.componentRightPolarBoundaryLoop i).cast hright hright)) := by
    change FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          (rawRightTrack.symm.trans (smallRight.trans rawRightTrack))) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          ((P.componentRightPolarBoundaryLoop i).cast hright hright)) at hrightTransport
    simpa only [componentTwoCenterSmallPolarBoundaryLoop, gluingRadiusRightLoop_cast]
      using hrightTransport
  have hrightLoop : Path.Homotopic.Quotient.mk
      (rightTrack.symm.trans (smallRight.trans rightTrack)) =
    Path.Homotopic.Quotient.mk (P.componentRightPolarBoundaryLoop i) := by
    change FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          (rightTrack.symm.trans (smallRight.trans rightTrack))) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (P.componentRightPolarBoundaryLoop i))
    exact transportPathClass_cast rawRightTrack smallRight
      (P.componentRightPolarBoundaryLoop i) hright.symm hrightRaw
  have hconj := congrArg (fun q : Path.Homotopic.Quotient _ _ =>
      (Path.Homotopic.Quotient.mk cut).trans
        (q.trans (Path.Homotopic.Quotient.mk cut.symm))) hrightLoop
  have hconj' : Path.Homotopic.Quotient.mk
      (cut.trans ((rightTrack.symm.trans (smallRight.trans rightTrack)).trans cut.symm)) =
    Path.Homotopic.Quotient.mk
      (cut.trans ((P.componentRightPolarBoundaryLoop i).trans cut.symm)) := by
    simpa only [Path.Homotopic.Quotient.mk_trans] using hconj
  have hpath := basedCutConjugate_transport_pathClass leftTrack cut rightTrack smallRight
  have hpath' : Path.Homotopic.Quotient.mk
      (leftTrack.symm.trans
        ((P.componentRightSmallPolarBoundaryLoopAlongCut i ρ hρ hρr).trans leftTrack)) =
      Path.Homotopic.Quotient.mk
        (cut.trans ((rightTrack.symm.trans (smallRight.trans rightTrack)).trans cut.symm)) := by
    simpa only [componentRightSmallPolarBoundaryLoopAlongCut,
      componentTwoCenterSmallPolarCutBasedPath] using hpath
  change FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk
        (leftTrack.symm.trans
          ((P.componentRightSmallPolarBoundaryLoopAlongCut i ρ hρ hρr).trans leftTrack))) = _
  calc
    _ = FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk
            (cut.trans ((rightTrack.symm.trans (smallRight.trans rightTrack)).trans cut.symm))) :=
      congrArg FundamentalGroup.fromPath hpath'
    _ = FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (P.componentRightPolarBoundaryLoopAlongCut i)) := by
      simpa only [componentRightPolarBoundaryLoopAlongCut,
        componentTwoCenterCutBasedPath, cut] using hconj'

/-- Transport an actual free marking from the selected small left polar
basepoint to the original gluing-radius basepoint. Both the left positive
loop and the right positive loop conjugated along the prescribed small cut
retain their exact marked values; the latter becomes the original cut-based
right loop. -/
theorem componentSmallPolarMarkedFreeEquiv_transport
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    {G : Type*} [Group G]
    (eSmall : FundamentalGroup (P.CenterPuncturedChainComponent i)
      (P.twoCenterPolarBoundaryMap i true ρ hρ hρr 1) ≃* G)
    (leftWord rightWord : G)
    (hleft : eSmall (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (P.componentTwoCenterSmallPolarBoundaryLoop i true ρ hρ hρr))) = leftWord)
    (hright : eSmall (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (P.componentRightSmallPolarBoundaryLoopAlongCut i ρ hρ hρr))) = rightWord) :
    ∃ e : FundamentalGroup (P.CenterPuncturedChainComponent i)
        (P.componentLeftPolarBoundaryMap i 1) ≃* G,
      e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (P.componentLeftPolarBoundaryLoop i))) = leftWord ∧
      e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (P.componentRightPolarBoundaryLoopAlongCut i))) = rightWord := by
  let τ := P.componentTwoCenterLeftPolarRadiusPathToOriginal i ρ hρ hρr
  let T := FundamentalGroup.fundamentalGroupMulEquivOfPath τ
  have hleftBack : T.symm
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (P.componentLeftPolarBoundaryLoop i))) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (P.componentTwoCenterSmallPolarBoundaryLoop i true ρ hρ hρr)) := by
    calc
      _ = T.symm (T (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (P.componentTwoCenterSmallPolarBoundaryLoop i true ρ hρ hρr)))) := by
        rw [P.componentLeftSmallPolarBoundaryLoop_transport i ρ hρ hρr]
      _ = _ := T.symm_apply_apply _
  have hrightBack : T.symm
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (P.componentRightPolarBoundaryLoopAlongCut i))) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (P.componentRightSmallPolarBoundaryLoopAlongCut i ρ hρ hρr)) := by
    calc
      _ = T.symm (T (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (P.componentRightSmallPolarBoundaryLoopAlongCut i ρ hρ hρr)))) := by
        rw [P.componentRightSmallPolarBoundaryLoopAlongCut_transport i ρ hρ hρr]
      _ = _ := T.symm_apply_apply _
  refine ⟨T.symm.trans eSmall, ?_, ?_⟩
  · change eSmall (T.symm (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (P.componentLeftPolarBoundaryLoop i)))) = leftWord
    rw [hleftBack, hleft]
  · change eSmall (T.symm (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (P.componentRightPolarBoundaryLoopAlongCut i)))) = rightWord
    rw [hrightBack, hright]

end
end ExerciseGluingPreparation
end SystolicGrowth

#print axioms SystolicGrowth.ExerciseGluingPreparation.componentLeftSmallPolarBoundaryLoop_transport
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentRightSmallPolarBoundaryLoopAlongCut_transport
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentSmallPolarMarkedFreeEquiv_transport
