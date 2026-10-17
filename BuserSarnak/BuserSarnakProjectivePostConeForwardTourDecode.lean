module

public import BuserSarnak.BuserSarnakProjectivePostConeForwardEndpoints
public import BuserSarnak.BuserSarnakProjectivePostConePhysicalTour

@[expose] public section

/-!
# The normalized literal child contour is its physical forward tour

The equality here is ordered list equality, not equality of supports. Each
recursive insertion is decoded with its actual physical endpoint tag before
the reverse-depth induction identifies the constructed physical tour.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open scoped Classical

/-- Exact physical decoding of a classified term agrees with the constructed
term when the strictly deeper child decoders have already been identified. -/
theorem canonicalProjectivePostConeRawContourTermOfCasePhysicalList_eq_forward
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePolygonDart p))
    (hih : ∀ other hdeep,
      canonicalProjectivePostConeRawForwardTreePhysicalList hp hp2 other = ih other hdeep)
    (s : ProjectivePolygonSide)
    (c : CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s) :
    canonicalProjectivePostConeRawContourTermOfCasePhysicalList hp hp2 slot s c =
      canonicalProjectivePostConeForwardPhysicalTermOfCase hp hp2 slot ih s c := by
  cases c with
  | one _ => rfl
  | finalSource _ _ _ => rfl
  | finalTarget _ _ _ => rfl
  | deeperSource z child hsource hlabel hdeep =>
      rw [canonicalProjectivePostConeRawContourTermOfCasePhysicalList_deeperSource,
        hih child hdeep]
      rfl
  | deeperTarget z child htarget hlabel hdeep =>
      rw [canonicalProjectivePostConeRawContourTermOfCasePhysicalList_deeperTarget,
        hih child hdeep]
      rfl

/-- Selecting the pivot or its exact off-pivot case preserves physical order. -/
theorem canonicalProjectivePostConeRawContourTermPhysicalList_eq_forward
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePolygonDart p))
    (hih : ∀ other hdeep,
      canonicalProjectivePostConeRawForwardTreePhysicalList hp hp2 other = ih other hdeep)
    (s : ProjectivePolygonSide) :
    canonicalProjectivePostConeRawContourTermPhysicalList hp hp2 slot s =
      canonicalProjectivePostConeForwardPhysicalTerm hp hp2 slot ih s := by
  by_cases hs : s = canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot
  · subst s
    rw [canonicalProjectivePostConeRawContourTermPhysicalList_pivot]
    simp only [canonicalProjectivePostConeForwardPhysicalTerm, ↓reduceDIte]
  · rw [canonicalProjectivePostConeRawContourTermPhysicalList_eq_ofCase hp hp2 slot s hs,
      canonicalProjectivePostConeForwardPhysicalTerm, dif_neg hs]
    exact canonicalProjectivePostConeRawContourTermOfCasePhysicalList_eq_forward
      hp hp2 slot ih hih s _

/-- The normalized literal endpoint list equals the actual forward physical
tree tour by reverse-depth induction, including empty child lists. -/
theorem canonicalProjectivePostConeRawForwardTreePhysicalList_eq_forwardPhysicalTreeWord
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    canonicalProjectivePostConeRawForwardTreePhysicalList hp hp2 slot =
      canonicalProjectivePostConeForwardPhysicalTreeWord hp hp2 slot := by
  refine (canonicalProjectivePostConeDirectTreeDependencyWellFounded hp hp2).induction
    (C := fun slot => canonicalProjectivePostConeRawForwardTreePhysicalList hp hp2 slot =
      canonicalProjectivePostConeForwardPhysicalTreeWord hp hp2 slot) slot ?_
  intro slot ih
  rw [canonicalProjectivePostConeRawForwardTreePhysicalList_eq_suffix_prefix,
    canonicalProjectivePostConeRawContourTermsPhysicalList_eq_flatMap,
    canonicalProjectivePostConeRawContourTermsPhysicalList_eq_flatMap,
    canonicalProjectivePostConeForwardPhysicalTreeWord_eq]
  unfold canonicalProjectivePostConeForwardPhysicalTerms
    canonicalProjectivePostConeOffPivotSideCycle
  rw [List.flatMap_append]
  congr 1 <;> apply List.flatMap_congr <;> intro s hs <;>
    exact canonicalProjectivePostConeRawContourTermPhysicalList_eq_forward hp hp2 slot
      (fun other _ => canonicalProjectivePostConeForwardPhysicalTreeWord hp hp2 other)
      (fun other hdeep => ih other hdeep) s

/-- The actual normalized child endpoint list has the proved entry,
internal gaps, and exit, not merely the same retained support. -/
theorem canonicalProjectivePostConeRawForwardTreePhysicalList_isChain
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    (canonicalProjectivePostConeTreeSlotLeftBoundaryDart hp hp2 slot ::
      canonicalProjectivePostConeRawForwardTreePhysicalList hp hp2 slot ++
      [canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 slot]).IsChain
        (PositiveOrbitGap (canonicalProjectivePostConeDualFacePerm hp hp2)
          (fun d => d ∈ canonicalProjectivePostConeSurvivorSet hp hp2)) := by
  rw [canonicalProjectivePostConeRawForwardTreePhysicalList_eq_forwardPhysicalTreeWord]
  exact canonicalProjectivePostConeForwardPhysicalTreeWord_isChain hp hp2 slot

#print axioms canonicalProjectivePostConeRawForwardTreePhysicalList_eq_forwardPhysicalTreeWord
#print axioms canonicalProjectivePostConeRawForwardTreePhysicalList_isChain

end

end SystolicGrowth
