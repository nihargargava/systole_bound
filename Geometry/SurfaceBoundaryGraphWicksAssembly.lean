module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceBoundaryGraphTreeOrbit
public import Geometry.SurfaceBoundaryGraphTreeSpliceSemantics
public import BuserSarnak.OrientableWicksResidualCertificate

@[expose] public section

/-!
# Constructing the actual peripheral Wicks certificate

The graph's literal signed peripheral word already has exact, unique signed
occurrences. If the actual tree-spliced side permutation is one orbit, its
first return to non-tree sides is one orbit; the proved transition conjugacy
then constructs the genuine one-vertex Wicks certificate. No orbit is assumed
for the word itself.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane Classical

namespace SystolicGrowth.DirichletBoundarySegments

noncomputable section

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

/-- The actual signed non-tree perimeter is a one-vertex Wicks word once the
actual tree-spliced side permutation has one orbit. The sole hypothesis is on
that concrete permutation; it is not packaged as a field of the certificate. -/
def intrinsicBoundaryWicksCertificate_of_treeSplicedOneOrbit
    (B : DirichletBoundarySegments X o)
    (horbit : ∀ i j : Fin B.intrinsicBoundaryRadialCuts.card,
      ∃ n : ℕ, B.intrinsicBoundaryTreeSplicedVertexPerm^[n] i = j) :
    OrientableWicksCertificate B.intrinsicBoundaryPeripheralLetters := by
  classical
  let retained : Fin B.intrinsicBoundaryRadialCuts.card → Prop :=
    B.intrinsicBoundaryRetainedSidePred
  let sideEquiv := B.intrinsicBoundaryRetainedSideEquiv
  have hreturnOrbit := finitePermutationFirstReturn_one_orbit
    B.intrinsicBoundaryTreeSplicedVertexPerm retained horbit
  have htransitionOrbit :
      ∀ u v : B.IntrinsicBoundaryNonTreeEdge × Bool,
        ∃ n : ℕ,
          (B.intrinsicBoundaryPeripheralLetters.formPerm *
            signedLetterPartnerPerm B.IntrinsicBoundaryNonTreeEdge)^[n] u = v := by
    apply one_orbit_of_conjugate
      (finitePermutationFirstReturn B.intrinsicBoundaryTreeSplicedVertexPerm retained)
      (B.intrinsicBoundaryPeripheralLetters.formPerm *
        signedLetterPartnerPerm B.IntrinsicBoundaryNonTreeEdge)
      sideEquiv.symm
    · intro x
      apply sideEquiv.injective
      rw [sideEquiv.apply_symm_apply,
        B.intrinsicBoundaryPeripheralTransition_treeFirstReturn,
        sideEquiv.apply_symm_apply]
    · exact hreturnOrbit
  exact wicksCertificateOfPhysicalOrbit
    B.intrinsicBoundaryPeripheralLetters
    B.intrinsicBoundaryPeripheralLetters_nodup
    B.intrinsicBoundaryPeripheralLetters_mem
    htransitionOrbit

#print axioms intrinsicBoundaryWicksCertificate_of_treeSplicedOneOrbit

end

end SystolicGrowth.DirichletBoundarySegments
