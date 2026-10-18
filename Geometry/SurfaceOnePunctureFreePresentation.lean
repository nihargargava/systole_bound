module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceBoundaryGraphFreeBasis
public import Geometry.SurfaceBoundaryGraphPeripheralWord
public import Geometry.SurfaceBoundaryGraphPeripheralLetters
public import Geometry.CircleOneTurnRebase

@[expose] public section

/-!
# The actual one-punctured surface and its peripheral free word

Compose the native Dirichlet retraction and physical graph basis, retaining
the positive polar loop and its original angular basepoint. Only equal-point
transports occur; there is no arbitrary connecting-path conjugation.
-/

open UpperHalfPlane CategoryTheory
open scoped UpperHalfPlane

namespace SystolicGrowth.DirichletBoundarySegments

noncomputable section

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

def Internal.SurfaceOnePunctureFreePresentationHelpers.puncturePointEqEquiv {Y : Type*} [TopologicalSpace Y]
    {x y : Y} (h : x = y) : FundamentalGroup Y x ≃* FundamentalGroup Y y :=
  (eqToIso (congrArg FundamentalGroupoid.mk h)).conj

set_option backward.isDefEq.respectTransparency false in
private theorem puncturePointEqEquiv_apply {Y : Type*} [TopologicalSpace Y]
    {x y : Y} (h : x = y) (p : FundamentalGroup Y x) :
    Internal.SurfaceOnePunctureFreePresentationHelpers.puncturePointEqEquiv h p = FundamentalGroup.mapOfEq (ContinuousMap.id Y) h p := by
  subst y
  rw [FundamentalGroup.mapOfEq_apply]
  simp only [Internal.SurfaceOnePunctureFreePresentationHelpers.puncturePointEqEquiv, eqToIso_refl, Iso.refl_conj,
    Path.Homotopic.Quotient.cast_rfl_rfl]
  induction p using Quotient.inductionOn with
  | h p =>
      apply congrArg Path.Homotopic.Quotient.mk
      apply Path.ext
      funext t
      rfl

/-- The actual one-center-punctured quotient is free on its physical non-tree
edges, based at the original positive polar loop's angular basepoint. -/
def intrinsicBoundaryPunctureFundamentalGroupFreeEquiv
    (B : DirichletBoundarySegments X o) (r : ℝ) (hr : 0 < r)
    (hsys : 2 * r < X.systole) :
    FundamentalGroup (X.CenterPuncturedCarrier o)
        (X.dirichletPuncturePolarCircle o r hr hsys
          (B.intrinsicBoundaryAngularVertices 0)) ≃*
      FreeGroup B.IntrinsicBoundaryNonTreeEdge :=
  (B.intrinsicBoundaryGraphFundamentalGroupEquiv _).trans
    ((Internal.SurfaceOnePunctureFreePresentationHelpers.puncturePointEqEquiv
      ((B.intrinsicBoundaryGraphPolarBasepoint_eq r hr hsys).trans
        B.intrinsicBoundaryGraphVertices_zero_eq_root)).trans
      (B.intrinsicBoundaryGraphFundamentalGroupFreeEquiv B.intrinsicBoundaryPeripheralRoot))

set_option backward.isDefEq.respectTransparency false in
/-- The untouched positively oriented puncture loop reads as the actual
signed non-tree perimeter word under the genuine free presentation. -/
theorem intrinsicBoundaryPunctureFundamentalGroupFreeEquiv_polarOneTurn
    (B : DirichletBoundarySegments X o) (r : ℝ) (hr : 0 < r)
    (hsys : 2 * r < X.systole) :
    B.intrinsicBoundaryPunctureFundamentalGroupFreeEquiv r hr hsys
      ⟦X.dirichletPuncturePolarOneTurn o r hr hsys
        (B.intrinsicBoundaryAngularVertices 0)⟧ =
      FreeGroup.mk B.intrinsicBoundaryPeripheralLetters := by
  let hpoint := (B.intrinsicBoundaryGraphPolarBasepoint_eq r hr hsys).trans
    B.intrinsicBoundaryGraphVertices_zero_eq_root
  have hloop : Internal.SurfaceOnePunctureFreePresentationHelpers.puncturePointEqEquiv hpoint
      (B.intrinsicBoundaryGraphFundamentalGroupEquiv _
        ⟦X.dirichletPuncturePolarOneTurn o r hr hsys
          (B.intrinsicBoundaryAngularVertices 0)⟧) =
      B.intrinsicBoundaryFreeGeneratorHom B.intrinsicBoundaryPeripheralRoot
        B.intrinsicBoundaryPerimeterFreeWord := by
    rw [B.intrinsicBoundaryGraphFundamentalGroupEquiv_polarOneTurn r hr hsys,
      puncturePointEqEquiv_apply, FundamentalGroup.mapOfEq_apply]
    calc
      _ = (⟦B.intrinsicBoundaryGraphGeodLoop.cast
          B.intrinsicBoundaryGraphVertices_zero_eq_root.symm
          B.intrinsicBoundaryGraphVertices_zero_eq_root.symm⟧ :
        FundamentalGroup B.IntrinsicBoundaryGraph
          (B.intrinsicBoundaryGraphVertexInclusion B.intrinsicBoundaryPeripheralRoot)) := by
            apply congrArg Path.Homotopic.Quotient.mk
            apply Path.ext
            funext t
            rfl
      _ = _ := (B.intrinsicBoundaryGraphGeodLoop_sideWord).trans
        (B.intrinsicBoundaryFreeGeneratorHom_perimeterFreeWord_sideWord
          B.intrinsicBoundaryPeripheralRoot).symm
  change B.intrinsicBoundaryGraphFundamentalGroupFreeEquiv B.intrinsicBoundaryPeripheralRoot
    (Internal.SurfaceOnePunctureFreePresentationHelpers.puncturePointEqEquiv hpoint
      (B.intrinsicBoundaryGraphFundamentalGroupEquiv _
        ⟦X.dirichletPuncturePolarOneTurn o r hr hsys
          (B.intrinsicBoundaryAngularVertices 0)⟧)) = _
  rw [hloop, B.intrinsicBoundaryPeripheralLetters_mk]
  exact B.intrinsicBoundaryFreeReader_leftInverse B.intrinsicBoundaryPeripheralRoot _

/-- Positive polar winding is preserved by the literal circle connector,
after mapping it into the original center-punctured surface. -/
theorem intrinsicBoundaryPuncturePolarOneTurn_rebase
    (r : ℝ) (hr : 0 < r)
    (hsys : 2 * r < X.systole) (θ φ : Circle) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath
      ((Circle.path θ φ).map (X.dirichletPuncturePolarCircle o r hr hsys).continuous)
      ⟦X.dirichletPuncturePolarOneTurn o r hr hsys θ⟧ =
      ⟦X.dirichletPuncturePolarOneTurn o r hr hsys φ⟧ := by
  let f := X.dirichletPuncturePolarCircle o r hr hsys
  have hcircle := SystolicGrowth.circleOneTurnLoop_rebase_circlePath θ φ
  rw [SystolicGrowth.circleFundamentalGroupMulEquivOfPath_apply] at hcircle
  have hmap := congrArg (fun α : Path.Homotopic.Quotient φ φ => α.map f) hcircle
  change ⟦((Circle.path θ φ).map f.continuous).symm.trans
      (((SystolicGrowth.circleOneTurnLoop θ).map f.continuous).trans
        ((Circle.path θ φ).map f.continuous))⟧ =
    ⟦(SystolicGrowth.circleOneTurnLoop φ).map f.continuous⟧
  change ⟦((Circle.path θ φ).symm.trans
      ((SystolicGrowth.circleOneTurnLoop θ).trans (Circle.path θ φ))).map f.continuous⟧ =
    ⟦(SystolicGrowth.circleOneTurnLoop φ).map f.continuous⟧ at hmap
  simpa only [Path.map_trans, Path.map_symm] using hmap

/-- The actual free presentation at any original polar angle, in particular
the angle-one basepoints used by the chain seams. -/
def intrinsicBoundaryPunctureFundamentalGroupFreeEquivAtAngle
    (B : DirichletBoundarySegments X o) (r : ℝ) (hr : 0 < r)
    (hsys : 2 * r < X.systole) (θ : Circle) :
    FundamentalGroup (X.CenterPuncturedCarrier o)
        (X.dirichletPuncturePolarCircle o r hr hsys θ) ≃*
      FreeGroup B.IntrinsicBoundaryNonTreeEdge :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath
    ((Circle.path θ (B.intrinsicBoundaryAngularVertices 0)).map
      (X.dirichletPuncturePolarCircle o r hr hsys).continuous)).trans
    (B.intrinsicBoundaryPunctureFundamentalGroupFreeEquiv r hr hsys)

/-- The angle-one seam convention does not alter the literal positive
peripheral word of the actual punctured surface. -/
theorem intrinsicBoundaryPunctureFundamentalGroupFreeEquivAtAngle_polarOneTurn
    (B : DirichletBoundarySegments X o) (r : ℝ) (hr : 0 < r)
    (hsys : 2 * r < X.systole) (θ : Circle) :
    B.intrinsicBoundaryPunctureFundamentalGroupFreeEquivAtAngle r hr hsys θ
      ⟦X.dirichletPuncturePolarOneTurn o r hr hsys θ⟧ =
      FreeGroup.mk B.intrinsicBoundaryPeripheralLetters := by
  change B.intrinsicBoundaryPunctureFundamentalGroupFreeEquiv r hr hsys
    (FundamentalGroup.fundamentalGroupMulEquivOfPath
      ((Circle.path θ (B.intrinsicBoundaryAngularVertices 0)).map
        (X.dirichletPuncturePolarCircle o r hr hsys).continuous)
      ⟦X.dirichletPuncturePolarOneTurn o r hr hsys θ⟧) = _
  rw [intrinsicBoundaryPuncturePolarOneTurn_rebase r hr hsys θ
    (B.intrinsicBoundaryAngularVertices 0)]
  exact B.intrinsicBoundaryPunctureFundamentalGroupFreeEquiv_polarOneTurn r hr hsys

#print axioms intrinsicBoundaryPunctureFundamentalGroupFreeEquiv
#print axioms intrinsicBoundaryPunctureFundamentalGroupFreeEquiv_polarOneTurn
#print axioms intrinsicBoundaryPuncturePolarOneTurn_rebase
#print axioms intrinsicBoundaryPunctureFundamentalGroupFreeEquivAtAngle_polarOneTurn

end

end SystolicGrowth.DirichletBoundarySegments
