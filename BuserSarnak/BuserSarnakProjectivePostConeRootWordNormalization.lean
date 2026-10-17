module

public import BuserSarnak.BuserSarnakProjectivePostConeDirectPresentation
public import BuserSarnak.BuserSarnakProjectiveFinalMarking

@[expose] public section

/-!
# Root-word normalization handoff

The direct post-cone calculation has reduced the projective presentation to a
single explicit root word.  This module records the exact final handoff: a
verified Tietze equivalence from that word to the standard surface relator
immediately produces the projective target-presentation data used by the
Buser--Sarnak marking construction.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete.Presentations

/-- Compose a root-word normalization with the verified cone and direct-tree
eliminations. -/
noncomputable def canonicalProjectiveConeTietzeEquivOfRootNormalization
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p)
    (N : TietzeEquiv
      ({canonicalProjectivePostConeDirectRootWord hp hp2} :
        Set (FreeGroup (CanonicalProjectivePostConeFinalGenerator hp hp2)))
      ({surfaceRelator (data.halfImageIndex + 1)} :
        Set (FreeGroup (SurfaceGenerator (data.halfImageIndex + 1))))) :
    TietzeEquiv (CanonicalProjectiveConeRelators p)
      ({surfaceRelator (data.halfImageIndex + 1)} :
        Set (FreeGroup (SurfaceGenerator (data.halfImageIndex + 1)))) :=
  (canonicalProjectiveConeTietzeEquivSingletonRoot hp hp2).trans N

/-- A root-word normalization certificate packages directly as the finite
projective target-presentation data needed by the unconditional marking
bridge. -/
noncomputable def canonicalProjectiveLevelTargetPresentationDataOfRootNormalization
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p)
    (N : TietzeEquiv
      ({canonicalProjectivePostConeDirectRootWord hp hp2} :
        Set (FreeGroup (CanonicalProjectivePostConeFinalGenerator hp hp2)))
      ({surfaceRelator (data.halfImageIndex + 1)} :
        Set (FreeGroup (SurfaceGenerator (data.halfImageIndex + 1))))) :
    BuserSarnakProjectiveLevelTargetPresentationData data
      (canonicalBuserSarnakProjectiveQuotientSectionData p) :=
  BuserSarnakProjectiveLevelTargetPresentationData.ofCanonicalProjectiveConeTietzeEquiv
    data (canonicalProjectiveConeTietzeEquivOfRootNormalization hp hp2 data N)

end

end SystolicGrowth
