module

public import BuserSarnak.BuserSarnakLevelMarking
public import BuserSarnak.BuserSarnakHNNBaseCorridorClassification
public import BuserSarnak.BuserSarnakCorrectedCover

@[expose] public section

/-!
# Final assembly of the Buser--Sarnak marking

This file isolates the two remaining constructive inputs: faithfulness of the
explicit HNN action and a uniform family of finite Tietze certificates.  Once
they are supplied, all conversions to the surface marking and the main
`BuserSarnakInput` are theorem-backed definitions.
-/

namespace SystolicGrowth

noncomputable section

/-- Faithfulness of the explicit HNN boundary action propagates through the
projective quotient and the central extension to the lifted quaternion
presentation. -/
theorem liftedOctagonToQuaternion_injective_of_hnn
    (hHNN : Function.Injective octagonHNNToPGL23) :
    Function.Injective liftedOctagonToQuaternion := by
  have hpgl : Function.Injective projectiveOctagonToPGL23 :=
    projectiveOctagonToPGL23_injective_iff_hnn.mpr hHNN
  have hprojective : Function.Injective
      projectiveOctagonToProjectivizedQuaternion :=
    projectiveOctagonToProjectivizedQuaternion_injective_iff_pgl.mpr hpgl
  exact liftedOctagonToQuaternion_injective_iff_projective.mpr hprojective

/-- The two remaining exponent-kernel boundary estimates already suffice for
faithfulness of the lifted quaternion presentation. -/
theorem liftedOctagonToQuaternion_injective_of_cross_self
    (hcross : ∀ (u : ℤˣ) (g : OctagonBaseGroup),
      g ∈ octagonBaseExponentKernel →
        Set.MapsTo
          (fun p : OctagonProjectiveBoundary => octagonBaseToPGL23 g • p)
          (octagonHNNBoundarySet u) (octagonHNNBoundarySet (-u))ᶜ)
    (hself : ∀ (u : ℤˣ) (g : OctagonBaseGroup),
      g ∈ octagonBaseExponentKernel → g ≠ 1 →
        Set.MapsTo
          (fun p : OctagonProjectiveBoundary => octagonBaseToPGL23 g • p)
          (octagonHNNBoundarySet u) (octagonHNNBoundarySet u)ᶜ) :
    Function.Injective liftedOctagonToQuaternion :=
  liftedOctagonToQuaternion_injective_of_hnn
    (octagonHNNToPGL23_injective_of_cross_self hcross hself)

/-- A uniform family of the finite cleaned-presentation certificates, with
the quotient section and target genus fixed canonically. -/
structure BuserSarnakUniformLevelTargetPresentationData where
  certificate : ∀ (p : ℕ) [NeZero p]
      (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3),
    BuserSarnakLevelTargetPresentationData
      (buserSarnakCorrectionData p hp hp2 hp3)
      (canonicalBuserSarnakOctagonQuotientSectionData p)

namespace BuserSarnakUniformLevelTargetPresentationData

/-- Uniform finite certificates and faithfulness of the lifted octagon
presentation produce the required family of surface-group markings. -/
noncomputable def toBaseSurfaceMarking
    (C : BuserSarnakUniformLevelTargetPresentationData)
    (hfaith : Function.Injective liftedOctagonToQuaternion) :
    BuserSarnakBaseSurfaceMarking :=
  BuserSarnakBaseSurfaceMarking.mk (by
    intro p _ hp hp2 hp3
    exact (C.certificate p hp hp2 hp3).levelGroupMarking hfaith)

/-- The remaining infinite-group input can equivalently be supplied as
faithfulness of the explicit HNN map into `PGL(2, ℝ)`. -/
noncomputable def toBaseSurfaceMarkingOfHNN
    (C : BuserSarnakUniformLevelTargetPresentationData)
    (hHNN : Function.Injective octagonHNNToPGL23) :
    BuserSarnakBaseSurfaceMarking :=
  C.toBaseSurfaceMarking (liftedOctagonToQuaternion_injective_of_hnn hHNN)

/-- The proved corridor classification discharges the former HNN
faithfulness input.  Only the finite target-presentation certificates remain
to construct the base surface markings. -/
noncomputable def toBaseSurfaceMarkingUnconditional
    (C : BuserSarnakUniformLevelTargetPresentationData) :
    BuserSarnakBaseSurfaceMarking :=
  C.toBaseSurfaceMarking liftedOctagonToQuaternion_injective

/-- Boundary cross/self separation plus the finite certificates produces the
surface marking directly. -/
noncomputable def toBaseSurfaceMarkingOfCrossSelf
    (C : BuserSarnakUniformLevelTargetPresentationData)
    (hcross : ∀ (u : ℤˣ) (g : OctagonBaseGroup),
      g ∈ octagonBaseExponentKernel →
        Set.MapsTo
          (fun p : OctagonProjectiveBoundary => octagonBaseToPGL23 g • p)
          (octagonHNNBoundarySet u) (octagonHNNBoundarySet (-u))ᶜ)
    (hself : ∀ (u : ℤˣ) (g : OctagonBaseGroup),
      g ∈ octagonBaseExponentKernel → g ≠ 1 →
        Set.MapsTo
          (fun p : OctagonProjectiveBoundary => octagonBaseToPGL23 g • p)
          (octagonHNNBoundarySet u) (octagonHNNBoundarySet u)ᶜ) :
    BuserSarnakBaseSurfaceMarking :=
  C.toBaseSurfaceMarking
    (liftedOctagonToQuaternion_injective_of_cross_self hcross hself)

/-- Final handoff to the arithmetic family expected by the main reduction. -/
noncomputable def toBuserSarnakInputOfHNN
    (C : BuserSarnakUniformLevelTargetPresentationData)
    (hHNN : Function.Injective octagonHNNToPGL23) :
    BuserSarnakInput :=
  BuserSarnakBaseSurfaceMarking.toBuserSarnakInput
    (C.toBaseSurfaceMarkingOfHNN hHNN)

/-- Uniform finite target-presentation certificates now suffice by themselves
to construct the full arithmetic surface family used by the reduction. -/
noncomputable def toBuserSarnakInputUnconditional
    (C : BuserSarnakUniformLevelTargetPresentationData) :
    BuserSarnakInput :=
  C.toBaseSurfaceMarkingUnconditional.toBuserSarnakInput

/-- Exact final handoff from the two geometric boundary estimates and the
uniform finite Tietze certificates. -/
noncomputable def toBuserSarnakInputOfCrossSelf
    (C : BuserSarnakUniformLevelTargetPresentationData)
    (hcross : ∀ (u : ℤˣ) (g : OctagonBaseGroup),
      g ∈ octagonBaseExponentKernel →
        Set.MapsTo
          (fun p : OctagonProjectiveBoundary => octagonBaseToPGL23 g • p)
          (octagonHNNBoundarySet u) (octagonHNNBoundarySet (-u))ᶜ)
    (hself : ∀ (u : ℤˣ) (g : OctagonBaseGroup),
      g ∈ octagonBaseExponentKernel → g ≠ 1 →
        Set.MapsTo
          (fun p : OctagonProjectiveBoundary => octagonBaseToPGL23 g • p)
          (octagonHNNBoundarySet u) (octagonHNNBoundarySet u)ᶜ) :
    BuserSarnakInput :=
  BuserSarnakBaseSurfaceMarking.toBuserSarnakInput
    (C.toBaseSurfaceMarkingOfCrossSelf hcross hself)

end BuserSarnakUniformLevelTargetPresentationData

end

end SystolicGrowth
