module

public import BuserSarnak.BuserSarnakProjectivePostConeFaceBoundaryOrder
public import BuserSarnak.BuserSarnakProjectivePostConeOpenTourEdges
public import BuserSarnak.FiniteOrbitGapChain
public import BuserSarnak.FiniteOrbitCyclicGap

@[expose] public section

/-!
# Constructive forward physical tours of the selected dual tree

These lists retain actual polygon darts, rather than free-group letters.
Both orientations of a child edge insert its forward physical tour. Deleted
incoming edge occurrences are kept only as the two open-tour sentinels.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open scoped Classical

/-- Expand a certified side in forward physical order, independently of the
sign used to solve the associated free-group generator. -/
def canonicalProjectivePostConeForwardPhysicalTermOfCase
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePolygonDart p))
    (s : ProjectivePolygonSide)
    (c : CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s) :
    List (CanonicalProjectivePolygonDart p) :=
  match c with
  | .one _ => []
  | .finalSource z _ _ => [projectivePolygonPostConeEdgeSourceDart z]
  | .finalTarget z _ _ => [projectivePolygonPostConeEdgeTargetDart z]
  | .deeperSource _ other _ _ hdeep => ih other hdeep
  | .deeperTarget _ other _ _ hdeep => ih other hdeep

/-- The incoming pivot contributes no retained physical dart. Every other
side uses its exact proved raw-term classification. -/
def canonicalProjectivePostConeForwardPhysicalTerm
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePolygonDart p))
    (s : ProjectivePolygonSide) : List (CanonicalProjectivePolygonDart p) :=
  if hs : s = canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot then []
  else canonicalProjectivePostConeForwardPhysicalTermOfCase hp hp2 slot ih s
    (canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs)

/-- Expand a literal list of sides without reduction or reordering. -/
def canonicalProjectivePostConeForwardPhysicalTerms
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePolygonDart p))
    (sides : List ProjectivePolygonSide) : List (CanonicalProjectivePolygonDart p) :=
  sides.flatMap (canonicalProjectivePostConeForwardPhysicalTerm hp hp2 slot ih)

/-- A child tour follows suffix then prefix, for either physical orientation
of its incoming dual-tree edge. -/
def canonicalProjectivePostConeForwardPhysicalTreeWord
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    CanonicalProjectivePostConeTreeSlot hp hp2 → List (CanonicalProjectivePolygonDart p) :=
  (canonicalProjectivePostConeDirectTreeDependencyWellFounded hp hp2).fix
    (fun slot ih => canonicalProjectivePostConeForwardPhysicalTerms hp hp2 slot ih
      (canonicalProjectivePostConeOffPivotSideCycle
        (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)))

/-- The concrete forward recursion is an exact literal list equation. -/
theorem canonicalProjectivePostConeForwardPhysicalTreeWord_eq
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    canonicalProjectivePostConeForwardPhysicalTreeWord hp hp2 slot =
      canonicalProjectivePostConeForwardPhysicalTerms hp hp2 slot
        (fun other _ => canonicalProjectivePostConeForwardPhysicalTreeWord hp hp2 other)
        (canonicalProjectivePostConeOffPivotSideCycle
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) := by
  unfold canonicalProjectivePostConeForwardPhysicalTreeWord
  rw [WellFounded.fix_eq]

/-- Auxiliary side tails keep both child pivots until filtering. This makes
each expanded side an open tour ending at its same-face successor. -/
def canonicalProjectivePostConeForwardPhysicalTailOfCase
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePolygonDart p))
    (s : ProjectivePolygonSide)
    (c : CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s) :
    List (CanonicalProjectivePolygonDart p) :=
  match c with
  | .one _ => []
  | .finalSource _ _ _ => []
  | .finalTarget _ _ _ => []
  | .deeperSource _ other _ _ hdeep =>
      ih other hdeep ++ [canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 other]
  | .deeperTarget _ other _ _ hdeep =>
      ih other hdeep ++ [canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 other]

/-- Choose an augmented tail with the same exact classifier as the physical
retained term. -/
def canonicalProjectivePostConeForwardPhysicalTail
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePolygonDart p))
    (s : ProjectivePolygonSide) : List (CanonicalProjectivePolygonDart p) :=
  if hs : s = canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot then []
  else canonicalProjectivePostConeForwardPhysicalTailOfCase hp hp2 slot ih s
    (canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs)

/-- Every letter of a classified expansion is a physical survivor if this
is true for its strictly deeper child expansions. -/
theorem canonicalProjectivePostConeForwardPhysicalTermOfCase_mem_survivor
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePolygonDart p))
    (hih : ∀ other hdeep d, d ∈ ih other hdeep →
      d ∈ canonicalProjectivePostConeSurvivorSet hp hp2)
    (s : ProjectivePolygonSide)
    (c : CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s)
    (d : CanonicalProjectivePolygonDart p)
    (hd : d ∈ canonicalProjectivePostConeForwardPhysicalTermOfCase hp hp2 slot ih s c) :
    d ∈ canonicalProjectivePostConeSurvivorSet hp hp2 := by
  cases c with
  | one _ => cases hd
  | finalSource z _ hz =>
      simp only [canonicalProjectivePostConeForwardPhysicalTermOfCase,
        List.mem_singleton] at hd
      subst d
      exact ⟨Sum.inl (⟨z, hz⟩ : CanonicalProjectivePostConeFinalGenerator hp hp2), rfl⟩
  | finalTarget z _ hz =>
      simp only [canonicalProjectivePostConeForwardPhysicalTermOfCase,
        List.mem_singleton] at hd
      subst d
      exact ⟨Sum.inr (⟨z, hz⟩ : CanonicalProjectivePostConeFinalGenerator hp hp2), rfl⟩
  | deeperSource _ child _ _ hdeep => exact hih child hdeep d hd
  | deeperTarget _ child _ _ hdeep => exact hih child hdeep d hd

/-- Filtering the augmented physical block deletes exactly its trivial or
tree-pivot occurrences, leaving the certified physical expansion. -/
theorem canonicalProjectivePostConeForwardPhysicalTailOfCase_filter
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePolygonDart p))
    (hih : ∀ other hdeep d, d ∈ ih other hdeep →
      d ∈ canonicalProjectivePostConeSurvivorSet hp hp2)
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)
    (c : CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s) :
    ((slot.right.state, s) ::
      canonicalProjectivePostConeForwardPhysicalTailOfCase hp hp2 slot ih s c).filter
        (fun d => decide (d ∈ canonicalProjectivePostConeSurvivorSet hp hp2)) =
      canonicalProjectivePostConeForwardPhysicalTermOfCase hp hp2 slot ih s c := by
  cases c with
  | one hterm =>
      have hnot : (slot.right.state, s) ∉ canonicalProjectivePostConeSurvivorSet hp hp2 := by
        rw [not_mem_canonicalProjectivePostConeSurvivorSet_iff]
        exact Or.inl ((canonicalProjectiveConePostConeBoundaryTerm_eq_one_iff_primal_carrier
          hp hp2 (slot.right.state, s)).mp hterm)
      simp [canonicalProjectivePostConeForwardPhysicalTailOfCase,
        canonicalProjectivePostConeForwardPhysicalTermOfCase, hnot]
  | finalSource z hsource hz =>
      have heq : (slot.right.state, s) = projectivePolygonPostConeEdgeSourceDart z :=
        Prod.ext (congrArg ProjectivePolygonPostConeFace.state hsource.1) hsource.2.1
      have hmem : projectivePolygonPostConeEdgeSourceDart z ∈
          canonicalProjectivePostConeSurvivorSet hp hp2 :=
        ⟨Sum.inl (⟨z, hz⟩ : CanonicalProjectivePostConeFinalGenerator hp hp2), rfl⟩
      simp [canonicalProjectivePostConeForwardPhysicalTailOfCase,
        canonicalProjectivePostConeForwardPhysicalTermOfCase, heq, hmem]
  | finalTarget z htarget hz =>
      have heq : (slot.right.state, s) = projectivePolygonPostConeEdgeTargetDart z :=
        Prod.ext (congrArg ProjectivePolygonPostConeFace.state htarget.1) htarget.2.1
      have hmem : projectivePolygonPostConeEdgeTargetDart z ∈
          canonicalProjectivePostConeSurvivorSet hp hp2 :=
        ⟨Sum.inr (⟨z, hz⟩ : CanonicalProjectivePostConeFinalGenerator hp hp2), rfl⟩
      simp [canonicalProjectivePostConeForwardPhysicalTailOfCase,
        canonicalProjectivePostConeForwardPhysicalTermOfCase, heq, hmem]
  | deeperSource z child hsource hlabel hdeep =>
      have hcarrier : CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p
          slot.right.state s (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) := by
        rw [hlabel]
        exact Or.inl hsource
      have heq := (canonicalProjectivePostConeTreeSlot_childBoundaryDart_of_nonpivot_carrier
        hp hp2 slot child s hcarrier hs).2.1
      have hfilter : (ih child hdeep).filter
          (fun d => decide (d ∈ canonicalProjectivePostConeSurvivorSet hp hp2)) =
          ih child hdeep := List.filter_eq_self.mpr (by
        intro d hd
        simp only [decide_eq_true_eq]
        exact hih child hdeep d hd)
      simp [canonicalProjectivePostConeForwardPhysicalTailOfCase,
        canonicalProjectivePostConeForwardPhysicalTermOfCase, heq, List.filter_append,
        canonicalProjectivePostConeTreeSlotLeftBoundaryDart_not_survivor,
        canonicalProjectivePostConeTreeSlotRightBoundaryDart_not_survivor, hfilter]
  | deeperTarget z child htarget hlabel hdeep =>
      have hcarrier : CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p
          slot.right.state s (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) := by
        rw [hlabel]
        exact Or.inr htarget
      have heq := (canonicalProjectivePostConeTreeSlot_childBoundaryDart_of_nonpivot_carrier
        hp hp2 slot child s hcarrier hs).2.1
      have hfilter : (ih child hdeep).filter
          (fun d => decide (d ∈ canonicalProjectivePostConeSurvivorSet hp hp2)) =
          ih child hdeep := List.filter_eq_self.mpr (by
        intro d hd
        simp only [decide_eq_true_eq]
        exact hih child hdeep d hd)
      simp [canonicalProjectivePostConeForwardPhysicalTailOfCase,
        canonicalProjectivePostConeForwardPhysicalTermOfCase, heq, List.filter_append,
        canonicalProjectivePostConeTreeSlotLeftBoundaryDart_not_survivor,
        canonicalProjectivePostConeTreeSlotRightBoundaryDart_not_survivor, hfilter]

/-- Each augmented side block is an actual positive-gap tour from that side
to its forward same-face successor. -/
theorem canonicalProjectivePostConeForwardPhysicalTailOfCase_isChain
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePolygonDart p))
    (hih : ∀ other hdeep,
      (canonicalProjectivePostConeTreeSlotLeftBoundaryDart hp hp2 other ::
        ih other hdeep ++ [canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 other]).IsChain
          (PositiveOrbitGap (canonicalProjectivePostConeDualFacePerm hp hp2)
            (fun d => d ∈ canonicalProjectivePostConeSurvivorSet hp hp2)))
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)
    (c : CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s) :
    ((slot.right.state, s) ::
      canonicalProjectivePostConeForwardPhysicalTailOfCase hp hp2 slot ih s c ++
        [(slot.right.state, s.next)]).IsChain
      (PositiveOrbitGap (canonicalProjectivePostConeDualFacePerm hp hp2)
        (fun d => d ∈ canonicalProjectivePostConeSurvivorSet hp hp2)) := by
  cases c with
  | one hterm =>
      simp only [canonicalProjectivePostConeForwardPhysicalTailOfCase,
        List.cons_append, List.nil_append, List.isChain_pair]
      rw [← canonicalProjectivePostConeDualFacePerm_apply_of_boundaryTerm_eq_one
        hp hp2 (slot.right.state, s) hterm]
      exact positiveOrbitGap_step _ _ _
  | finalSource z hsource hz =>
      simp only [canonicalProjectivePostConeForwardPhysicalTailOfCase,
        List.cons_append, List.nil_append, List.isChain_pair]
      rw [← canonicalProjectivePostConeDualFacePerm_apply_of_nonTreeCarrier
        hp hp2 (slot.right.state, s) z (Or.inl hsource) hz]
      exact positiveOrbitGap_step _ _ _
  | finalTarget z htarget hz =>
      simp only [canonicalProjectivePostConeForwardPhysicalTailOfCase,
        List.cons_append, List.nil_append, List.isChain_pair]
      rw [← canonicalProjectivePostConeDualFacePerm_apply_of_nonTreeCarrier
        hp hp2 (slot.right.state, s) z (Or.inr htarget) hz]
      exact positiveOrbitGap_step _ _ _
  | deeperSource z child hsource hlabel hdeep =>
      have hcarrier : CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p
          slot.right.state s (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) := by
        rw [hlabel]
        exact Or.inl hsource
      have heq := (canonicalProjectivePostConeTreeSlot_childBoundaryDart_of_nonpivot_carrier
        hp hp2 slot child s hcarrier hs).2.1
      have hexit : canonicalProjectivePostConeDualFacePerm hp hp2
          (canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 child) =
          (slot.right.state, s.next) := by
        have hnext := congrArg (fun d : CanonicalProjectivePolygonDart p => (d.1, d.2.next)) heq
        exact (canonicalProjectivePostConeDualFacePerm_rightBoundaryDart hp hp2 child).trans
          hnext.symm
      have hlast := List.isChain_pair.mpr (show PositiveOrbitGap
        (canonicalProjectivePostConeDualFacePerm hp hp2)
        (fun d => d ∈ canonicalProjectivePostConeSurvivorSet hp hp2)
        (canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 child)
        (slot.right.state, s.next) from hexit ▸ positiveOrbitGap_step _ _ _)
      simpa only [canonicalProjectivePostConeForwardPhysicalTailOfCase,
        List.cons_append, List.append_assoc, List.nil_append, heq] using
        (List.isChain_split.mpr ⟨hih child hdeep, hlast⟩)
  | deeperTarget z child htarget hlabel hdeep =>
      have hcarrier : CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p
          slot.right.state s (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) := by
        rw [hlabel]
        exact Or.inr htarget
      have heq := (canonicalProjectivePostConeTreeSlot_childBoundaryDart_of_nonpivot_carrier
        hp hp2 slot child s hcarrier hs).2.1
      have hexit : canonicalProjectivePostConeDualFacePerm hp hp2
          (canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 child) =
          (slot.right.state, s.next) := by
        have hnext := congrArg (fun d : CanonicalProjectivePolygonDart p => (d.1, d.2.next)) heq
        exact (canonicalProjectivePostConeDualFacePerm_rightBoundaryDart hp hp2 child).trans
          hnext.symm
      have hlast := List.isChain_pair.mpr (show PositiveOrbitGap
        (canonicalProjectivePostConeDualFacePerm hp hp2)
        (fun d => d ∈ canonicalProjectivePostConeSurvivorSet hp hp2)
        (canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 child)
        (slot.right.state, s.next) from hexit ▸ positiveOrbitGap_step _ _ _)
      simpa only [canonicalProjectivePostConeForwardPhysicalTailOfCase,
        List.cons_append, List.append_assoc, List.nil_append, heq] using
        (List.isChain_split.mpr ⟨hih child hdeep, hlast⟩)

/-- Retainedness is preserved by any literal concatenation of classified
side expansions. -/
theorem canonicalProjectivePostConeForwardPhysicalTerms_mem_survivor
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePolygonDart p))
    (hih : ∀ other hdeep d, d ∈ ih other hdeep →
      d ∈ canonicalProjectivePostConeSurvivorSet hp hp2)
    (sides : List ProjectivePolygonSide) (d : CanonicalProjectivePolygonDart p)
    (hd : d ∈ canonicalProjectivePostConeForwardPhysicalTerms hp hp2 slot ih sides) :
    d ∈ canonicalProjectivePostConeSurvivorSet hp hp2 := by
  obtain ⟨s, _, hd⟩ := List.mem_flatMap.mp hd
  unfold canonicalProjectivePostConeForwardPhysicalTerm at hd
  split at hd
  · cases hd
  · exact canonicalProjectivePostConeForwardPhysicalTermOfCase_mem_survivor
      hp hp2 slot ih hih s _ d hd

/-- Stitch the seven augmented side tours using the checked octagon order,
then erase omitted interior points. Both entry and exit seams are included. -/
theorem canonicalProjectivePostConeForwardPhysicalTerms_isChain
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePolygonDart p))
    (hmem : ∀ other hdeep d, d ∈ ih other hdeep →
      d ∈ canonicalProjectivePostConeSurvivorSet hp hp2)
    (hchain : ∀ other hdeep,
      (canonicalProjectivePostConeTreeSlotLeftBoundaryDart hp hp2 other ::
        ih other hdeep ++ [canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 other]).IsChain
          (PositiveOrbitGap (canonicalProjectivePostConeDualFacePerm hp hp2)
            (fun d => d ∈ canonicalProjectivePostConeSurvivorSet hp hp2))) :
    (canonicalProjectivePostConeTreeSlotLeftBoundaryDart hp hp2 slot ::
      canonicalProjectivePostConeForwardPhysicalTerms hp hp2 slot ih
        (canonicalProjectivePostConeOffPivotSideCycle
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) ++
      [canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 slot]).IsChain
        (PositiveOrbitGap (canonicalProjectivePostConeDualFacePerm hp hp2)
          (fun d => d ∈ canonicalProjectivePostConeSurvivorSet hp hp2)) := by
  let successor : CanonicalProjectivePolygonDart p → CanonicalProjectivePolygonDart p :=
    fun d => (d.1, d.2.next)
  let base := canonicalProjectivePostConeOffPivotDartCycle slot.right.state
    (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)
  let tail : CanonicalProjectivePolygonDart p → List (CanonicalProjectivePolygonDart p) :=
    fun d => canonicalProjectivePostConeForwardPhysicalTail hp hp2 slot ih d.2
  let a := canonicalProjectivePostConeTreeSlotLeftBoundaryDart hp hp2 slot
  let b := canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 slot
  let P : CanonicalProjectivePolygonDart p → Prop :=
    fun d => d ∈ canonicalProjectivePostConeSurvivorSet hp hp2
  let R := PositiveOrbitGap (canonicalProjectivePostConeDualFacePerm hp hp2) P
  have hbase : (base ++ [b]).IsChain (fun d e => successor d = e) := by
    simpa only [base, b, successor, canonicalProjectivePostConeTreeSlotRightBoundaryDart,
      projectivePolygonFaceSuccessorPerm_apply, List.cons_append, List.tail_cons] using
      (canonicalProjectivePostConeOffPivotDartCycle_isChain
        (canonicalBuserSarnakProjectiveQuotientSectionData p) slot.right.state
        (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)).tail
  have htour : ∀ d ∈ base, (d :: tail d ++ [successor d]).IsChain R := by
    intro d hd
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hd
    have hne := (mem_canonicalProjectivePostConeOffPivotSideCycle_iff _ s).mp hs
    dsimp [tail, successor]
    rw [canonicalProjectivePostConeForwardPhysicalTail, dif_neg hne]
    exact canonicalProjectivePostConeForwardPhysicalTailOfCase_isChain
      hp hp2 slot ih hchain s hne _
  have hhead : base.head?.getD b =
      (slot.right.state, (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot).next) := by
    dsimp [base, b, canonicalProjectivePostConeOffPivotDartCycle,
      canonicalProjectivePostConeTreeSlotRightBoundaryDart]
    cases canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot <;> rfl
  have hanchor : R a (base.head?.getD b) := by
    rw [hhead, ← canonicalProjectivePostConeDualFacePerm_leftBoundaryDart hp hp2 slot]
    exact positiveOrbitGap_step _ _ _
  have haug : (a :: base.flatMap (fun d => d :: tail d) ++ [b]).IsChain R :=
    isChain_cons_flatMap_open_tours successor tail hbase htour hanchor
  have hfilter : (base.flatMap (fun d => d :: tail d)).filter (fun d => decide (P d)) =
      canonicalProjectivePostConeForwardPhysicalTerms hp hp2 slot ih
        (canonicalProjectivePostConeOffPivotSideCycle
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) := by
    dsimp [base, canonicalProjectivePostConeOffPivotDartCycle,
      canonicalProjectivePostConeForwardPhysicalTerms]
    rw [List.flatMap_map, List.filter_flatMap]
    apply List.flatMap_congr
    intro s hs
    have hne := (mem_canonicalProjectivePostConeOffPivotSideCycle_iff _ s).mp hs
    dsimp [tail, Function.comp_def]
    rw [canonicalProjectivePostConeForwardPhysicalTail, dif_neg hne,
      canonicalProjectivePostConeForwardPhysicalTerm, dif_neg hne]
    exact canonicalProjectivePostConeForwardPhysicalTailOfCase_filter
      hp hp2 slot ih hmem s hne _
  simpa only [hfilter] using positiveOrbitGap_isChain_filter_open haug

/-- Reverse-depth induction constructs the physical open tour and proves
that every interior point is retained. No global contour premise is used. -/
theorem canonicalProjectivePostConeForwardPhysicalTreeWord_properties
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    (∀ d ∈ canonicalProjectivePostConeForwardPhysicalTreeWord hp hp2 slot,
      d ∈ canonicalProjectivePostConeSurvivorSet hp hp2) ∧
    (canonicalProjectivePostConeTreeSlotLeftBoundaryDart hp hp2 slot ::
      canonicalProjectivePostConeForwardPhysicalTreeWord hp hp2 slot ++
      [canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 slot]).IsChain
        (PositiveOrbitGap (canonicalProjectivePostConeDualFacePerm hp hp2)
          (fun d => d ∈ canonicalProjectivePostConeSurvivorSet hp hp2)) := by
  refine (canonicalProjectivePostConeDirectTreeDependencyWellFounded hp hp2).induction
    (C := fun slot =>
      (∀ d ∈ canonicalProjectivePostConeForwardPhysicalTreeWord hp hp2 slot,
        d ∈ canonicalProjectivePostConeSurvivorSet hp hp2) ∧
      (canonicalProjectivePostConeTreeSlotLeftBoundaryDart hp hp2 slot ::
        canonicalProjectivePostConeForwardPhysicalTreeWord hp hp2 slot ++
        [canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 slot]).IsChain
          (PositiveOrbitGap (canonicalProjectivePostConeDualFacePerm hp hp2)
            (fun d => d ∈ canonicalProjectivePostConeSurvivorSet hp hp2))) slot ?_
  intro slot ih
  rw [canonicalProjectivePostConeForwardPhysicalTreeWord_eq]
  exact ⟨canonicalProjectivePostConeForwardPhysicalTerms_mem_survivor hp hp2 slot
      (fun other _ => canonicalProjectivePostConeForwardPhysicalTreeWord hp hp2 other)
      (fun other hdeep => (ih other hdeep).1) _,
    canonicalProjectivePostConeForwardPhysicalTerms_isChain hp hp2 slot
      (fun other _ => canonicalProjectivePostConeForwardPhysicalTreeWord hp hp2 other)
      (fun other hdeep => (ih other hdeep).1)
      (fun other hdeep => (ih other hdeep).2)⟩

theorem canonicalProjectivePostConeForwardPhysicalTreeWord_mem_survivor
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (d : CanonicalProjectivePolygonDart p)
    (hd : d ∈ canonicalProjectivePostConeForwardPhysicalTreeWord hp hp2 slot) :
    d ∈ canonicalProjectivePostConeSurvivorSet hp hp2 :=
  (canonicalProjectivePostConeForwardPhysicalTreeWord_properties hp hp2 slot).1 d hd

/-- Entry, all internal adjacencies, and exit hold also for an empty child
word, because both omitted sentinels remain in this open chain. -/
theorem canonicalProjectivePostConeForwardPhysicalTreeWord_isChain
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    (canonicalProjectivePostConeTreeSlotLeftBoundaryDart hp hp2 slot ::
      canonicalProjectivePostConeForwardPhysicalTreeWord hp hp2 slot ++
      [canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 slot]).IsChain
        (PositiveOrbitGap (canonicalProjectivePostConeDualFacePerm hp hp2)
          (fun d => d ∈ canonicalProjectivePostConeSurvivorSet hp hp2)) :=
  (canonicalProjectivePostConeForwardPhysicalTreeWord_properties hp hp2 slot).2

#print axioms canonicalProjectivePostConeForwardPhysicalTreeWord_isChain
#print axioms canonicalProjectivePostConeForwardPhysicalTreeWord_mem_survivor

/-- A forward child tour, including its outgoing sentinel, ends at the
same-face successor of its parent-side occurrence. -/
theorem canonicalProjectivePostConeForwardPhysicalTreeWord_extended_isChain
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    (canonicalProjectivePostConeTreeSlotLeftBoundaryDart hp hp2 slot ::
      (canonicalProjectivePostConeForwardPhysicalTreeWord hp hp2 slot ++
        [canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 slot]) ++
      [(slot.left.state,
        (canonicalProjectivePostConeTreeSlot_leftBoundarySide hp hp2 slot).next)]).IsChain
        (PositiveOrbitGap (canonicalProjectivePostConeDualFacePerm hp hp2)
          (fun d => d ∈ canonicalProjectivePostConeSurvivorSet hp hp2)) := by
  have hlast := List.isChain_pair.mpr (show PositiveOrbitGap
    (canonicalProjectivePostConeDualFacePerm hp hp2)
    (fun d => d ∈ canonicalProjectivePostConeSurvivorSet hp hp2)
    (canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 slot)
    (slot.left.state, (canonicalProjectivePostConeTreeSlot_leftBoundarySide hp hp2 slot).next)
      from (canonicalProjectivePostConeDualFacePerm_rightBoundaryDart hp hp2 slot) ▸
        positiveOrbitGap_step _ _ _)
  simpa only [List.cons_append, List.append_assoc, List.nil_append] using
    List.isChain_split.mpr
      ⟨canonicalProjectivePostConeForwardPhysicalTreeWord_isChain hp hp2 slot, hlast⟩

/-- A root-side expansion inserts the actual forward physical child tour
for either sign of a selected dual-tree label. -/
def canonicalProjectivePostConeForwardPhysicalRootTermOfCase
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide)
    (c : CanonicalProjectivePostConeRawRootContourTermCase hp hp2 q s) :
    List (CanonicalProjectivePolygonDart p) :=
  match c with
  | .one _ => []
  | .finalSource z _ _ => [projectivePolygonPostConeEdgeSourceDart z]
  | .finalTarget z _ _ => [projectivePolygonPostConeEdgeTargetDart z]
  | .treeSource z _ hz => canonicalProjectivePostConeForwardPhysicalTreeWord hp hp2
      (canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz)
  | .treeTarget z _ hz => canonicalProjectivePostConeForwardPhysicalTreeWord hp hp2
      (canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz)

/-- Select the root-side expansion without changing its physical ordering. -/
def canonicalProjectivePostConeForwardPhysicalRootTerm
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide) :
    List (CanonicalProjectivePolygonDart p) :=
  canonicalProjectivePostConeForwardPhysicalRootTermOfCase hp hp2 q s
    (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s)

/-- The root physical contour is the eight forward root-side expansions. -/
def canonicalProjectivePostConeForwardPhysicalRootWord
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) : List (CanonicalProjectivePolygonDart p) :=
  canonicalProjectivePostConeBoundarySideCycle.flatMap
    (canonicalProjectivePostConeForwardPhysicalRootTerm hp hp2 q)

/-- Root augmentation retains the omitted pivots until the cyclic path has
been assembled. -/
def canonicalProjectivePostConeForwardPhysicalRootTailOfCase
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide)
    (c : CanonicalProjectivePostConeRawRootContourTermCase hp hp2 q s) :
    List (CanonicalProjectivePolygonDart p) :=
  match c with
  | .one _ => []
  | .finalSource _ _ _ => []
  | .finalTarget _ _ _ => []
  | .treeSource z _ hz =>
      let slot := canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz
      canonicalProjectivePostConeForwardPhysicalTreeWord hp hp2 slot ++
        [canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 slot]
  | .treeTarget z _ hz =>
      let slot := canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz
      canonicalProjectivePostConeForwardPhysicalTreeWord hp hp2 slot ++
        [canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 slot]

def canonicalProjectivePostConeForwardPhysicalRootTail
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide) :
    List (CanonicalProjectivePolygonDart p) :=
  canonicalProjectivePostConeForwardPhysicalRootTailOfCase hp hp2 q s
    (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s)

theorem canonicalProjectivePostConeForwardPhysicalRootTermOfCase_mem_survivor
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide)
    (c : CanonicalProjectivePostConeRawRootContourTermCase hp hp2 q s)
    (d : CanonicalProjectivePolygonDart p)
    (hd : d ∈ canonicalProjectivePostConeForwardPhysicalRootTermOfCase hp hp2 q s c) :
    d ∈ canonicalProjectivePostConeSurvivorSet hp hp2 := by
  cases c with
  | one _ => cases hd
  | finalSource z _ hz =>
      simp only [canonicalProjectivePostConeForwardPhysicalRootTermOfCase,
        List.mem_singleton] at hd
      subst d
      exact ⟨Sum.inl (⟨z, hz⟩ : CanonicalProjectivePostConeFinalGenerator hp hp2), rfl⟩
  | finalTarget z _ hz =>
      simp only [canonicalProjectivePostConeForwardPhysicalRootTermOfCase,
        List.mem_singleton] at hd
      subst d
      exact ⟨Sum.inr (⟨z, hz⟩ : CanonicalProjectivePostConeFinalGenerator hp hp2), rfl⟩
  | treeSource z _ hz =>
      exact canonicalProjectivePostConeForwardPhysicalTreeWord_mem_survivor hp hp2
        (canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz) d hd
  | treeTarget z _ hz =>
      exact canonicalProjectivePostConeForwardPhysicalTreeWord_mem_survivor hp hp2
        (canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz) d hd

theorem canonicalProjectivePostConeForwardPhysicalRootWord_mem_survivor
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (d : CanonicalProjectivePolygonDart p)
    (hd : d ∈ canonicalProjectivePostConeForwardPhysicalRootWord hp hp2 q) :
    d ∈ canonicalProjectivePostConeSurvivorSet hp hp2 := by
  obtain ⟨s, _, hd⟩ := List.mem_flatMap.mp hd
  exact canonicalProjectivePostConeForwardPhysicalRootTermOfCase_mem_survivor hp hp2 q s _ d hd

theorem canonicalProjectivePostConeForwardPhysicalRootTailOfCase_isChain
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (s : ProjectivePolygonSide)
    (c : CanonicalProjectivePostConeRawRootContourTermCase hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state s) :
    (((canonicalProjectivePostConeTreeRoot hp hp2).state, s) ::
      canonicalProjectivePostConeForwardPhysicalRootTailOfCase hp hp2
        (canonicalProjectivePostConeTreeRoot hp hp2).state s c ++
      [((canonicalProjectivePostConeTreeRoot hp hp2).state, s.next)]).IsChain
        (PositiveOrbitGap (canonicalProjectivePostConeDualFacePerm hp hp2)
          (fun d => d ∈ canonicalProjectivePostConeSurvivorSet hp hp2)) := by
  cases c with
  | one hterm =>
      simp only [canonicalProjectivePostConeForwardPhysicalRootTailOfCase,
        List.cons_append, List.nil_append, List.isChain_pair]
      rw [← canonicalProjectivePostConeDualFacePerm_apply_of_boundaryTerm_eq_one
        hp hp2 ((canonicalProjectivePostConeTreeRoot hp hp2).state, s) hterm]
      exact positiveOrbitGap_step _ _ _
  | finalSource z hsource hz =>
      simp only [canonicalProjectivePostConeForwardPhysicalRootTailOfCase,
        List.cons_append, List.nil_append, List.isChain_pair]
      rw [← canonicalProjectivePostConeDualFacePerm_apply_of_nonTreeCarrier
        hp hp2 ((canonicalProjectivePostConeTreeRoot hp hp2).state, s) z (Or.inl hsource) hz]
      exact positiveOrbitGap_step _ _ _
  | finalTarget z htarget hz =>
      simp only [canonicalProjectivePostConeForwardPhysicalRootTailOfCase,
        List.cons_append, List.nil_append, List.isChain_pair]
      rw [← canonicalProjectivePostConeDualFacePerm_apply_of_nonTreeCarrier
        hp hp2 ((canonicalProjectivePostConeTreeRoot hp hp2).state, s) z (Or.inr htarget) hz]
      exact positiveOrbitGap_step _ _ _
  | treeSource z hsource hz =>
      let slot := canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz
      have hcarrier : CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p
          (canonicalProjectivePostConeTreeRoot hp hp2).state s
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) := by
        rw [canonicalProjectivePostConeDirectTreeSlotOfDeleted_label]
        exact Or.inl hsource
      have heq := (canonicalProjectivePostConeTreeSlot_rootBoundaryDart_of_physicalCarrier
        hp hp2 slot s hcarrier).2
      have hnext := congrArg (fun d : CanonicalProjectivePolygonDart p => (d.1, d.2.next)) heq
      change ((canonicalProjectivePostConeTreeRoot hp hp2).state, s.next) =
        (slot.left.state, (canonicalProjectivePostConeTreeSlot_leftBoundarySide hp hp2 slot).next)
        at hnext
      simpa only [canonicalProjectivePostConeForwardPhysicalRootTailOfCase,
        ← heq, ← hnext] using
        canonicalProjectivePostConeForwardPhysicalTreeWord_extended_isChain hp hp2 slot

  | treeTarget z htarget hz =>
      let slot := canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz
      have hcarrier : CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p
          (canonicalProjectivePostConeTreeRoot hp hp2).state s
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) := by
        rw [canonicalProjectivePostConeDirectTreeSlotOfDeleted_label]
        exact Or.inr htarget
      have heq := (canonicalProjectivePostConeTreeSlot_rootBoundaryDart_of_physicalCarrier
        hp hp2 slot s hcarrier).2
      have hnext := congrArg (fun d : CanonicalProjectivePolygonDart p => (d.1, d.2.next)) heq
      change ((canonicalProjectivePostConeTreeRoot hp hp2).state, s.next) =
        (slot.left.state, (canonicalProjectivePostConeTreeSlot_leftBoundarySide hp hp2 slot).next)
        at hnext
      simpa only [canonicalProjectivePostConeForwardPhysicalRootTailOfCase,
        ← heq, ← hnext] using
        canonicalProjectivePostConeForwardPhysicalTreeWord_extended_isChain hp hp2 slot

/-- The root's augmented side block deletes exactly the omitted physical
occurrences when filtered by survivor membership. -/
theorem canonicalProjectivePostConeForwardPhysicalRootTailOfCase_filter
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (s : ProjectivePolygonSide)
    (c : CanonicalProjectivePostConeRawRootContourTermCase hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state s) :
    (((canonicalProjectivePostConeTreeRoot hp hp2).state, s) ::
      canonicalProjectivePostConeForwardPhysicalRootTailOfCase hp hp2
        (canonicalProjectivePostConeTreeRoot hp hp2).state s c).filter
          (fun d => decide (d ∈ canonicalProjectivePostConeSurvivorSet hp hp2)) =
      canonicalProjectivePostConeForwardPhysicalRootTermOfCase hp hp2
        (canonicalProjectivePostConeTreeRoot hp hp2).state s c := by
  cases c with
  | one hterm =>
      have hnot : ((canonicalProjectivePostConeTreeRoot hp hp2).state, s) ∉
          canonicalProjectivePostConeSurvivorSet hp hp2 := by
        rw [not_mem_canonicalProjectivePostConeSurvivorSet_iff]
        exact Or.inl ((canonicalProjectiveConePostConeBoundaryTerm_eq_one_iff_primal_carrier
          hp hp2 ((canonicalProjectivePostConeTreeRoot hp hp2).state, s)).mp hterm)
      simp [canonicalProjectivePostConeForwardPhysicalRootTailOfCase,
        canonicalProjectivePostConeForwardPhysicalRootTermOfCase, hnot]
  | finalSource z hsource hz =>
      have heq : ((canonicalProjectivePostConeTreeRoot hp hp2).state, s) =
          projectivePolygonPostConeEdgeSourceDart z :=
        Prod.ext (congrArg ProjectivePolygonPostConeFace.state hsource.1) hsource.2.1
      have hmem : projectivePolygonPostConeEdgeSourceDart z ∈
          canonicalProjectivePostConeSurvivorSet hp hp2 :=
        ⟨Sum.inl (⟨z, hz⟩ : CanonicalProjectivePostConeFinalGenerator hp hp2), rfl⟩
      simp [canonicalProjectivePostConeForwardPhysicalRootTailOfCase,
        canonicalProjectivePostConeForwardPhysicalRootTermOfCase, heq, hmem]
  | finalTarget z htarget hz =>
      have heq : ((canonicalProjectivePostConeTreeRoot hp hp2).state, s) =
          projectivePolygonPostConeEdgeTargetDart z :=
        Prod.ext (congrArg ProjectivePolygonPostConeFace.state htarget.1) htarget.2.1
      have hmem : projectivePolygonPostConeEdgeTargetDart z ∈
          canonicalProjectivePostConeSurvivorSet hp hp2 :=
        ⟨Sum.inr (⟨z, hz⟩ : CanonicalProjectivePostConeFinalGenerator hp hp2), rfl⟩
      simp [canonicalProjectivePostConeForwardPhysicalRootTailOfCase,
        canonicalProjectivePostConeForwardPhysicalRootTermOfCase, heq, hmem]
  | treeSource z hsource hz =>
      let slot := canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz
      have hcarrier : CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p
          (canonicalProjectivePostConeTreeRoot hp hp2).state s
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) := by
        rw [canonicalProjectivePostConeDirectTreeSlotOfDeleted_label]
        exact Or.inl hsource
      have heq := (canonicalProjectivePostConeTreeSlot_rootBoundaryDart_of_physicalCarrier
        hp hp2 slot s hcarrier).2
      have hfilter : (canonicalProjectivePostConeForwardPhysicalTreeWord hp hp2 slot).filter
          (fun d => decide (d ∈ canonicalProjectivePostConeSurvivorSet hp hp2)) =
          canonicalProjectivePostConeForwardPhysicalTreeWord hp hp2 slot :=
        List.filter_eq_self.mpr (by
          intro d hd
          simp only [decide_eq_true_eq]
          exact canonicalProjectivePostConeForwardPhysicalTreeWord_mem_survivor hp hp2 slot d hd)
      simp only [canonicalProjectivePostConeForwardPhysicalRootTailOfCase,
        canonicalProjectivePostConeForwardPhysicalRootTermOfCase]
      rw [heq]
      change ((canonicalProjectivePostConeTreeSlotLeftBoundaryDart hp hp2 slot ::
        (canonicalProjectivePostConeForwardPhysicalTreeWord hp hp2 slot ++
          [canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 slot])).filter
          (fun d => decide (d ∈ canonicalProjectivePostConeSurvivorSet hp hp2))) =
          canonicalProjectivePostConeForwardPhysicalTreeWord hp hp2 slot
      simp [List.filter_append, canonicalProjectivePostConeTreeSlotLeftBoundaryDart_not_survivor,
        canonicalProjectivePostConeTreeSlotRightBoundaryDart_not_survivor, hfilter]
  | treeTarget z htarget hz =>
      let slot := canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz
      have hcarrier : CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p
          (canonicalProjectivePostConeTreeRoot hp hp2).state s
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) := by
        rw [canonicalProjectivePostConeDirectTreeSlotOfDeleted_label]
        exact Or.inr htarget
      have heq := (canonicalProjectivePostConeTreeSlot_rootBoundaryDart_of_physicalCarrier
        hp hp2 slot s hcarrier).2
      have hfilter : (canonicalProjectivePostConeForwardPhysicalTreeWord hp hp2 slot).filter
          (fun d => decide (d ∈ canonicalProjectivePostConeSurvivorSet hp hp2)) =
          canonicalProjectivePostConeForwardPhysicalTreeWord hp hp2 slot :=
        List.filter_eq_self.mpr (by
          intro d hd
          simp only [decide_eq_true_eq]
          exact canonicalProjectivePostConeForwardPhysicalTreeWord_mem_survivor hp hp2 slot d hd)
      simp only [canonicalProjectivePostConeForwardPhysicalRootTailOfCase,
        canonicalProjectivePostConeForwardPhysicalRootTermOfCase]
      rw [heq]
      change ((canonicalProjectivePostConeTreeSlotLeftBoundaryDart hp hp2 slot ::
        (canonicalProjectivePostConeForwardPhysicalTreeWord hp hp2 slot ++
          [canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 slot])).filter
          (fun d => decide (d ∈ canonicalProjectivePostConeSurvivorSet hp hp2))) =
          canonicalProjectivePostConeForwardPhysicalTreeWord hp hp2 slot
      simp [List.filter_append, canonicalProjectivePostConeTreeSlotLeftBoundaryDart_not_survivor,
        canonicalProjectivePostConeTreeSlotRightBoundaryDart_not_survivor, hfilter]
/-- The constructive root word is a literal cyclic positive-gap chain.
The filtered list may be empty; no nonempty-root or child hypothesis is used. -/
theorem canonicalProjectivePostConeForwardPhysicalRootWord_isChain
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    let word := canonicalProjectivePostConeForwardPhysicalRootWord hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state
    (word ++ word.take 1).IsChain
      (PositiveOrbitGap (canonicalProjectivePostConeDualFacePerm hp hp2)
        (fun d => d ∈ canonicalProjectivePostConeSurvivorSet hp hp2)) := by
  let q := (canonicalProjectivePostConeTreeRoot hp hp2).state
  let successor : CanonicalProjectivePolygonDart p → CanonicalProjectivePolygonDart p :=
    fun d => (d.1, d.2.next)
  let base := canonicalProjectivePostConeBoundarySideCycle.map (fun s => (q, s))
  let tail : CanonicalProjectivePolygonDart p → List (CanonicalProjectivePolygonDart p) :=
    fun d => canonicalProjectivePostConeForwardPhysicalRootTail hp hp2 q d.2
  let aug := base.flatMap (fun d => d :: tail d)
  let a : CanonicalProjectivePolygonDart p := (q, .a)
  let P : CanonicalProjectivePolygonDart p → Prop :=
    fun d => d ∈ canonicalProjectivePostConeSurvivorSet hp hp2
  let R := PositiveOrbitGap (canonicalProjectivePostConeDualFacePerm hp hp2) P
  have hbase : (base ++ [a]).IsChain (fun d e => successor d = e) := by
    have hmap : ((canonicalProjectivePostConeBoundarySideCycle ++ [ProjectivePolygonSide.a]).map
        (fun s => (q, s))).IsChain (fun d e => successor d = e) :=
      (List.isChain_map (fun s => (q, s))).mpr (canonicalProjectivePostConeBoundarySideCycle_isChain.imp
        (fun s t hst => show successor (q, s) = (q, t) from congrArg (fun u => (q, u)) hst))
    simpa only [base, a, List.map_append, List.map_singleton] using hmap
  have htour : ∀ d ∈ base, (d :: tail d ++ [successor d]).IsChain R := by
    intro d hd
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hd
    exact canonicalProjectivePostConeForwardPhysicalRootTailOfCase_isChain hp hp2 s _
  have haug : (aug ++ [a]).IsChain R :=
    isChain_flatMap_open_tours successor tail hbase htour
  have hhead : aug.take 1 = [a] := by
    dsimp [aug, base, canonicalProjectivePostConeBoundarySideCycle]
    simp only [List.map_cons, List.flatMap_cons, List.cons_append,
      List.take_succ_cons, List.take_zero]
    rfl
  have hclosed : (aug ++ aug.take 1).IsChain R := by simpa only [hhead] using haug
  have hfilter : aug.filter (fun d => decide (P d)) =
      canonicalProjectivePostConeForwardPhysicalRootWord hp hp2 q := by
    dsimp [aug, base, canonicalProjectivePostConeForwardPhysicalRootWord]
    rw [List.flatMap_map, List.filter_flatMap]
    apply List.flatMap_congr
    intro s _
    exact canonicalProjectivePostConeForwardPhysicalRootTailOfCase_filter hp hp2 s _
  have hfiltered := positiveOrbitGap_isChain_filter_cyclic hclosed
  simpa only [hfilter] using hfiltered

#print axioms canonicalProjectivePostConeForwardPhysicalRootWord_isChain
#print axioms canonicalProjectivePostConeForwardPhysicalRootWord_mem_survivor

end

end SystolicGrowth
