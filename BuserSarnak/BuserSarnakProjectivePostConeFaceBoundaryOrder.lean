module

public import BuserSarnak.BuserSarnakProjectiveDualFaceReturn
public import Mathlib.Data.List.Chain

@[expose] public section

/-!
# Exact forward face-side order around an omitted pivot

The expanded child boundary uses suffix then prefix. Before recursive
expansion these seven sides form the actual forward octagon path from the
incoming pivot back to that pivot. The root boundary has its own checked
last-to-first seam. These are positional facts, not free-group equations.
-/

namespace SystolicGrowth

noncomputable section

/-- All seven off-pivot sides, starting immediately after the pivot. -/
def canonicalProjectivePostConeOffPivotSideCycle (s : ProjectivePolygonSide) :
    List ProjectivePolygonSide :=
  canonicalProjectivePostConeBoundarySuffixSides s ++
    canonicalProjectivePostConeBoundaryPrefixSides s

@[simp] theorem canonicalProjectivePostConeOffPivotSideCycle_length
    (s : ProjectivePolygonSide) :
    (canonicalProjectivePostConeOffPivotSideCycle s).length = 7 := by
  cases s <;> rfl

@[simp] theorem mem_canonicalProjectivePostConeOffPivotSideCycle_iff
    (s t : ProjectivePolygonSide) :
    t ∈ canonicalProjectivePostConeOffPivotSideCycle s ↔ t ≠ s := by
  cases s <;> cases t <;> decide

theorem canonicalProjectivePostConeOffPivotSideCycle_nodup
    (s : ProjectivePolygonSide) :
    (canonicalProjectivePostConeOffPivotSideCycle s).Nodup := by
  cases s <;> decide

@[simp] theorem canonicalProjectivePostConeOffPivotSideCycle_head
    (s : ProjectivePolygonSide) :
    (canonicalProjectivePostConeOffPivotSideCycle s).head? = some s.next := by
  cases s <;> rfl

/-- Both seams of the suffix/prefix path use actual side successor. -/
theorem canonicalProjectivePostConeOffPivotSideCycle_isChain
    (s : ProjectivePolygonSide) :
    (s :: canonicalProjectivePostConeOffPivotSideCycle s ++ [s]).IsChain
      (fun t u => t.next = u) := by
  cases s <;> decide

/-- The root's eight-side boundary includes the last-to-first successor seam. -/
theorem canonicalProjectivePostConeBoundarySideCycle_isChain :
    (canonicalProjectivePostConeBoundarySideCycle ++ [ProjectivePolygonSide.a]).IsChain
      (fun t u => t.next = u) := by
  decide

/-- Package the off-pivot path as original darts of the same physical face. -/
def canonicalProjectivePostConeOffPivotDartCycle
    {p : ℕ} [NeZero p] (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) : List (CanonicalProjectivePolygonDart p) :=
  (canonicalProjectivePostConeOffPivotSideCycle s).map (fun t => (q, t))

/-- The geometric face permutation gives every step of the unexpanded
off-pivot dart path, including its incoming and outgoing seams. -/
theorem canonicalProjectivePostConeOffPivotDartCycle_isChain
    {p : ℕ} [NeZero p] (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide) :
    ((q, s) :: canonicalProjectivePostConeOffPivotDartCycle q s ++ [(q, s)]).IsChain
      (fun d e => projectivePolygonFaceSuccessorPerm S d = e) := by
  have h : ((s :: canonicalProjectivePostConeOffPivotSideCycle s ++ [s]).map
      (fun t => (q, t))).IsChain
      (fun d e => projectivePolygonFaceSuccessorPerm S d = e) :=
    (List.isChain_map _).mpr ((canonicalProjectivePostConeOffPivotSideCycle_isChain s).imp
      (fun t u htu => by simp only [projectivePolygonFaceSuccessorPerm_apply, htu]))
  simpa only [List.map_cons, List.map_append, List.map_nil,
    canonicalProjectivePostConeOffPivotDartCycle] using h

#print axioms canonicalProjectivePostConeOffPivotSideCycle_isChain
#print axioms canonicalProjectivePostConeOffPivotDartCycle_isChain

end

end SystolicGrowth
