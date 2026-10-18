module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceBoundaryGraphFreeReader
public import Geometry.SurfaceBoundaryGraphRootedWordFunctor

@[expose] public section

/-!
# The actual free basis of the punctured boundary graph

The graph-to-free-group reader and the free-generator map are inverse on the
whole based fundamental group. The two inverse equations are proved from the
actual disconnected groupoid van Kampen cover, tree connectors, and physical
side paths; this packages those existing proofs as a genuine equivalence.
-/

open UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth.DirichletBoundarySegments

noncomputable section

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

/-- The actual based fundamental group of the paired-side spine is free on
its genuine non-tree physical edges. -/
def intrinsicBoundaryGraphFundamentalGroupFreeEquiv
    (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) :
    FundamentalGroup B.IntrinsicBoundaryGraph (B.intrinsicBoundaryGraphVertexInclusion r) ≃*
      FreeGroup B.IntrinsicBoundaryNonTreeEdge where
  toFun := B.intrinsicBoundaryFreeReader r
  invFun := B.intrinsicBoundaryFreeGeneratorHom r
  left_inv := by
    intro x
    have h := congrArg (fun f => f x)
      (B.intrinsicBoundaryFreeGeneratorHom_comp_wordHom r)
    change B.intrinsicBoundaryFreeGeneratorHom r
      ((B.intrinsicBoundaryGraphWordFunctor
        (fun e => B.intrinsicBoundaryFreeSideWord e.val)).map x) = x
    exact h
  right_inv := B.intrinsicBoundaryFreeReader_leftInverse r
  map_mul' := (B.intrinsicBoundaryFreeReader r).map_mul

/-- The basis equivalence reads the untouched original ordered perimeter
loop as its actual signed non-tree word. -/
theorem intrinsicBoundaryGraphFundamentalGroupFreeEquiv_perimeter
    (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) :
    B.intrinsicBoundaryGraphFundamentalGroupFreeEquiv r
      (⟦B.intrinsicBoundaryRootedPerimeterLoop r⟧ :
        FundamentalGroup B.IntrinsicBoundaryGraph (B.intrinsicBoundaryGraphVertexInclusion r)) =
      B.intrinsicBoundaryPerimeterFreeWord :=
  B.intrinsicBoundaryFreeReader_rootedPerimeterLoop r

#print axioms intrinsicBoundaryGraphFundamentalGroupFreeEquiv
#print axioms intrinsicBoundaryGraphFundamentalGroupFreeEquiv_perimeter

end

end SystolicGrowth.DirichletBoundarySegments
