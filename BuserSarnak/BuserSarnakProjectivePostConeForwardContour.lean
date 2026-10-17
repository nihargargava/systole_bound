module

public import BuserSarnak.BuserSarnakProjectivePostConeRawContour

@[expose] public section

/-!
# Forward-oriented child contours

A recursive slot word replaces an oriented generator, so it is not always
the forward boundary of its child face. Normalize by the source bit at the
parent endpoint. The result is always the expanded suffix followed by the
expanded prefix, as a literal signed list rather than a free-group equality.
-/

namespace SystolicGrowth

noncomputable section

/-- The child boundary oriented in the actual forward polygon direction. -/
def canonicalProjectivePostConeRawForwardTreeWord
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool) :=
  if canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 slot then
    canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot
  else FreeGroup.invRev (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot)

/-- Both slot orientations give precisely the forward expanded child-face
boundary with its incoming pivot omitted. No reduction or cyclic-order
assumption is used. -/
theorem canonicalProjectivePostConeRawForwardTreeWord_eq_suffix_prefix
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    canonicalProjectivePostConeRawForwardTreeWord hp hp2 slot =
      canonicalProjectivePostConeRawContourSuffix hp hp2 slot
          (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) ++
        canonicalProjectivePostConeRawContourPrefix hp hp2 slot
          (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) := by
  classical
  rcases canonicalProjectivePostConeTreeSlot_endpoints_eq_physicalEndpoints hp hp2 slot with
    hforward | hreverse
  · have hbit := canonicalProjectivePostConeRawSlotLeftSourceBit_eq_true_of_left_source
      hp hp2 slot hforward.1
    have hright : slot.right ≠ projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) := by
      rw [hforward.2]
      exact (canonicalProjectivePostConeTreeSlot_edgeSource_ne_edgeTarget hp hp2 slot).symm
    simp only [canonicalProjectivePostConeRawForwardTreeWord, hbit, if_true]
    exact canonicalProjectivePostConeRawTreeWordBySlot_eq_splice_of_target hp hp2 slot hright
  · have hbit := canonicalProjectivePostConeRawSlotLeftSourceBit_eq_false_of_left_target
      hp hp2 slot hreverse.1
    simp only [canonicalProjectivePostConeRawForwardTreeWord, hbit, Bool.false_eq_true, if_false]
    rw [canonicalProjectivePostConeRawTreeWordBySlot_eq_splice_of_source hp hp2 slot hreverse.2,
      FreeGroup.invRev_append, FreeGroup.invRev_invRev, FreeGroup.invRev_invRev]

#print axioms canonicalProjectivePostConeRawForwardTreeWord_eq_suffix_prefix

end

end SystolicGrowth
