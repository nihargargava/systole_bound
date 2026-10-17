module

public import BuserSarnak.BuserSarnakProjectivePostConeRootDynamics

@[expose] public section

/-!
# The concrete orientable Wicks certificate

The contracted root word retains every signed generator exactly once. Its
literal successor-after-partner rotation has one orbit by physical first
return, completing the finite certificate without a supplied orbit premise.
This does not yet construct the elementary Nielsen normalization program.
-/

namespace SystolicGrowth

noncomputable section

local instance rootWicksFinalGeneratorFintype
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Fintype (CanonicalProjectivePostConeFinalGenerator hp hp2) :=
  rawRootContourFinalGeneratorFintype hp hp2

/-- Every literal position is its unique displayed positive or negative
occurrence of its actual signed generator. -/
theorem canonicalProjectivePostConeRawRootContour_occurrences_exhaustive
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length) :
    i = canonicalProjectivePostConeRawRootContourPositivePosition hp hp2
        ((canonicalProjectivePostConeRawRootContour hp hp2).get i).1 ∨
      i = canonicalProjectivePostConeRawRootContourNegativePosition hp hp2
        ((canonicalProjectivePostConeRawRootContour hp hp2).get i).1 := by
  cases hs : ((canonicalProjectivePostConeRawRootContour hp hp2).get i).2 with
  | false =>
      right
      apply canonicalProjectivePostConeRawRootContour_get_injective hp hp2
      rw [canonicalProjectivePostConeRawRootContourNegativePosition_spec]
      exact Prod.ext rfl hs
  | true =>
      left
      apply canonicalProjectivePostConeRawRootContour_get_injective hp hp2
      rw [canonicalProjectivePostConeRawRootContourPositivePosition_spec]
      exact Prod.ext rfl hs

/-- The actual root word has the complete finite orientable Wicks
certificate, including its verified literal one-orbit rotation. -/
def canonicalProjectivePostConeRawRootContourWicksCertificate
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    OrientableWicksCertificate (canonicalProjectivePostConeRawRootContour hp hp2) where
  positive := canonicalProjectivePostConeRawRootContourPositivePosition hp hp2
  negative := canonicalProjectivePostConeRawRootContourNegativePosition hp hp2
  positive_spec := canonicalProjectivePostConeRawRootContourPositivePosition_spec hp hp2
  negative_spec := canonicalProjectivePostConeRawRootContourNegativePosition_spec hp hp2
  exhaustive := canonicalProjectivePostConeRawRootContour_occurrences_exhaustive hp hp2
  partner := canonicalProjectivePostConeRawRootContour_partner hp hp2
  partner_spec := canonicalProjectivePostConeRawRootContour_partner_spec hp hp2
  rotation := canonicalProjectivePostConeRawRootContour_rotation hp hp2
  rotation_eq _ := rfl
  one_orbit := canonicalProjectivePostConeRawRootContour_rotation_one_orbit hp hp2

#print axioms canonicalProjectivePostConeRawRootContour_occurrences_exhaustive
#print axioms canonicalProjectivePostConeRawRootContourWicksCertificate

end

end SystolicGrowth
