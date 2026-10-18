module

public import BuserSarnak.BuserSarnakProjectivePostConeSurvivorEmbedding
public import BuserSarnak.BuserSarnakProjectivePostConeForwardEndpoints
public import BuserSarnak.BuserSarnakProjectivePostConeOpenTourEdges

@[expose] public section

/-!
# Ordered physical decoding of the root contour

The root contour is decomposed through its actual occurrence-provenance tags.
No equality of physical darts is inferred from a signed-letter projection.
-/

namespace SystolicGrowth

noncomputable section

/-- Ordered physical occurrences of one classified root-face side term. -/
def canonicalProjectivePostConeRawRootContourTermOfCasePhysicalList
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide)
    (c : CanonicalProjectivePostConeRawRootContourTermCase hp hp2 q s) :
    List (CanonicalProjectivePolygonDart p) :=
  List.ofFn (fun i => canonicalProjectivePostConeSurvivingDart_embedding hp hp2
    (canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint hp hp2 c
      (canonicalProjectivePostConeRawRootContourTermOfCase_positionEquiv
        hp hp2 q s c i)).1)

/-- Decode the chosen root-side term, retaining its actual physical endpoint. -/
def canonicalProjectivePostConeRawRootContourTermPhysicalList
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide) :
    List (CanonicalProjectivePolygonDart p) :=
  canonicalProjectivePostConeRawRootContourTermOfCasePhysicalList hp hp2 q s
    (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s)

/-- Ordered physical decoding of any root-face side-list expansion. -/
def canonicalProjectivePostConeRawRootContourTermsPhysicalList
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (sides : List ProjectivePolygonSide) :
    List (CanonicalProjectivePolygonDart p) :=
  List.ofFn (fun i => canonicalProjectivePostConeSurvivingDart_embedding hp hp2
    (canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2 q sides
      (canonicalProjectivePostConeRawRootContourTerms_positionEquiv
        hp hp2 q sides i)).1)

/-- The empty side inventory has no physical occurrences. -/
@[simp] theorem canonicalProjectivePostConeRawRootContourTermsPhysicalList_nil
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) :
    canonicalProjectivePostConeRawRootContourTermsPhysicalList hp hp2 q [] = [] :=
  rfl

/-- The provenance decoder respects the literal ordered append at a side seam. -/
theorem canonicalProjectivePostConeRawRootContourTermsPhysicalList_cons
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) (ss : List ProjectivePolygonSide) :
    canonicalProjectivePostConeRawRootContourTermsPhysicalList hp hp2 q (s :: ss) =
      canonicalProjectivePostConeRawRootContourTermPhysicalList hp hp2 q s ++
        canonicalProjectivePostConeRawRootContourTermsPhysicalList hp hp2 q ss := by
  let headWord := canonicalProjectivePostConeRawRootContourTerm hp hp2 q s
  let tailWord := canonicalProjectivePostConeRawRootContourTerms hp hp2 q ss
  let hf := fun i : Fin headWord.length =>
    canonicalProjectivePostConeSurvivingDart_embedding hp hp2
      (canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint hp hp2
        (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s)
        (canonicalProjectivePostConeRawRootContourTerm_positionEquiv hp hp2 q s i)).1
  let tf := fun i : Fin tailWord.length =>
    canonicalProjectivePostConeSurvivingDart_embedding hp hp2
      (canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2 q ss
        (canonicalProjectivePostConeRawRootContourTerms_positionEquiv hp hp2 q ss i)).1
  have hlen : (canonicalProjectivePostConeRawRootContourTerms hp hp2 q (s :: ss)).length =
      headWord.length + tailWord.length := List.length_append
  unfold canonicalProjectivePostConeRawRootContourTermsPhysicalList
  rw [List.ofFn_congr hlen]
  change List.ofFn (fun i => canonicalProjectivePostConeSurvivingDart_embedding hp hp2
    (canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2 q (s :: ss)
      (canonicalProjectivePostConeRawRootContourTerms_positionEquiv hp hp2 q (s :: ss)
        (Fin.cast hlen.symm i))).1) = List.ofFn hf ++ List.ofFn tf
  have hfun : (fun i => canonicalProjectivePostConeSurvivingDart_embedding hp hp2
      (canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2 q (s :: ss)
        (canonicalProjectivePostConeRawRootContourTerms_positionEquiv hp hp2 q (s :: ss)
          (Fin.cast hlen.symm i))).1) = Fin.append hf tf := by
    funext i
    cases i using Fin.addCases with
    | left i =>
        rw [Fin.append_left]
        simp only [canonicalProjectivePostConeRawRootContourTerms_positionEquiv,
          canonicalProjectivePostConeRawAppendPositionSplit]
        change canonicalProjectivePostConeSurvivingDart_embedding hp hp2
          (canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2 q (s :: ss)
            ((Equiv.sumCongr (Equiv.refl _)
              (canonicalProjectivePostConeRawRootContourTerms_positionEquiv hp hp2 q ss))
              (finSumFinEquiv.symm (Fin.castAdd tailWord.length i)))).1 = hf i
        rw [finSumFinEquiv_symm_apply_castAdd]
        rfl
    | right i =>
        rw [Fin.append_right]
        simp only [canonicalProjectivePostConeRawRootContourTerms_positionEquiv,
          canonicalProjectivePostConeRawAppendPositionSplit]
        change canonicalProjectivePostConeSurvivingDart_embedding hp hp2
          (canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2 q (s :: ss)
            ((Equiv.sumCongr (Equiv.refl _)
              (canonicalProjectivePostConeRawRootContourTerms_positionEquiv hp hp2 q ss))
              (finSumFinEquiv.symm (Fin.natAdd headWord.length i)))).1 = tf i
        rw [finSumFinEquiv_symm_apply_natAdd]
        rfl
  rw [hfun, List.ofFn_fin_append]

/-- Root-side assembly is a literal physical flat-map, not merely a support equality. -/
theorem canonicalProjectivePostConeRawRootContourTermsPhysicalList_eq_flatMap
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (sides : List ProjectivePolygonSide) :
    canonicalProjectivePostConeRawRootContourTermsPhysicalList hp hp2 q sides =
      sides.flatMap (canonicalProjectivePostConeRawRootContourTermPhysicalList hp hp2 q) := by
  induction sides with
  | nil => rfl
  | cons s ss ih =>
      rw [canonicalProjectivePostConeRawRootContourTermsPhysicalList_cons,
        List.flatMap_cons, ih]

/-- The actual root-contour position embedding, read in its original order. -/
def canonicalProjectivePostConeRawRootPhysicalList
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    List (CanonicalProjectivePolygonDart p) :=
  List.ofFn (canonicalProjectivePostConeRawRootContourPosition_physicalEmbedding hp hp2)

/-- The root's exact position decoder gives its eight-side physical expansion. -/
theorem canonicalProjectivePostConeRawRootPhysicalList_eq_flatMap
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    canonicalProjectivePostConeRawRootPhysicalList hp hp2 =
      canonicalProjectivePostConeBoundarySideCycle.flatMap
        (canonicalProjectivePostConeRawRootContourTermPhysicalList hp hp2
          (canonicalProjectivePostConeTreeRoot hp hp2).state) := by
  change canonicalProjectivePostConeRawRootContourTermsPhysicalList hp hp2
    (canonicalProjectivePostConeTreeRoot hp hp2).state
    canonicalProjectivePostConeBoundarySideCycle = _
  exact canonicalProjectivePostConeRawRootContourTermsPhysicalList_eq_flatMap hp hp2 _ _

/-- Primal-tree sides contribute no retained physical occurrence. -/
@[simp] theorem canonicalProjectivePostConeRawRootContourTermOfCasePhysicalList_one
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide)
    (hterm : canonicalProjectiveConePostConeBoundaryTerm p q s = 1) :
    canonicalProjectivePostConeRawRootContourTermOfCasePhysicalList hp hp2 q s
      (.one hterm) = [] := rfl

/-- A retained source term decodes to the actual source dart of its physical edge. -/
@[simp] theorem canonicalProjectivePostConeRawRootContourTermOfCasePhysicalList_finalSource
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hsource : (⟨q⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeSource z ∧
      s = projectivePolygonPostConeEdgeSide z ∧
      canonicalProjectiveConePostConeBoundaryTerm p q s = FreeGroup.of z)
    (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
    canonicalProjectivePostConeRawRootContourTermOfCasePhysicalList hp hp2 q s
    (.finalSource z hsource hz) = [projectivePolygonPostConeEdgeSourceDart z] := by
  simp [canonicalProjectivePostConeRawRootContourTermOfCasePhysicalList,
    canonicalProjectivePostConeRawRootContourTermOfCase,
    canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint]
  rfl

/-- A retained target term decodes to the actual paired target dart. -/
@[simp] theorem canonicalProjectivePostConeRawRootContourTermOfCasePhysicalList_finalTarget
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (htarget : (⟨q⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeTarget z ∧
      s = projectivePolygonPostConeEdgeTargetSide z ∧
      canonicalProjectiveConePostConeBoundaryTerm p q s = (FreeGroup.of z)⁻¹)
    (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
    canonicalProjectivePostConeRawRootContourTermOfCasePhysicalList hp hp2 q s
      (.finalTarget z htarget hz) = [projectivePolygonPostConeEdgeTargetDart z] := by
  simp [canonicalProjectivePostConeRawRootContourTermOfCasePhysicalList,
    canonicalProjectivePostConeRawRootContourTermOfCase,
    canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint]
  rfl

/-- A root source-oriented tree insertion is the child's actual forward physical list. -/
theorem canonicalProjectivePostConeRawRootContourTermOfCasePhysicalList_treeSource
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (s : ProjectivePolygonSide) (z : CanonicalProjectiveConeKeptSymbol p)
    (hsource : (⟨(canonicalProjectivePostConeTreeRoot hp hp2).state⟩ :
        ProjectivePolygonPostConeFace p) = projectivePolygonPostConeEdgeSource z ∧
      s = projectivePolygonPostConeEdgeSide z ∧
      canonicalProjectiveConePostConeBoundaryTerm p
        (canonicalProjectivePostConeTreeRoot hp hp2).state s = FreeGroup.of z)
    (hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
    canonicalProjectivePostConeRawRootContourTermOfCasePhysicalList hp hp2
        (canonicalProjectivePostConeTreeRoot hp hp2).state s (.treeSource z hsource hz) =
      canonicalProjectivePostConeRawForwardTreePhysicalList hp hp2
        (canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz) := by
  let child := canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz
  have hlabel := canonicalProjectivePostConeDirectTreeSlotOfDeleted_label hp hp2 z hz
  have hcarrier : CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p
      (canonicalProjectivePostConeTreeRoot hp hp2).state s
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) := by
    rw [hlabel]
    exact Or.inl hsource
  have hroot := (canonicalProjectivePostConeTreeSlot_rootBoundaryDart_of_physicalCarrier
    hp hp2 child s hcarrier).1
  have hleft : child.left = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) := by
    rw [hlabel]
    exact hroot.trans hsource.1
  have hbit := canonicalProjectivePostConeRawSlotLeftSourceBit_eq_true_of_left_source
    hp hp2 child hleft
  simp [canonicalProjectivePostConeRawRootContourTermOfCasePhysicalList,
    canonicalProjectivePostConeRawRootContourTermOfCase,
    canonicalProjectivePostConeRawRootContourTermOfCase_positionEquiv,
    canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint,
    canonicalProjectivePostConeRawForwardTreePhysicalList,
    canonicalProjectivePostConeRawForwardTreeWordPosition_physicalEmbedding,
    canonicalProjectivePostConeRawForwardTreeWordPosition_endpoint,
    canonicalProjectivePostConeRawForwardTreeWordPosition_originalEquiv,
    canonicalProjectivePostConeRawForwardTreeWord, hbit, child]
  rfl

/-- Root target reversal reindexes occurrences exactly as child forward normalization. -/
theorem canonicalProjectivePostConeRawRootContourTermOfCasePhysicalList_treeTarget
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (s : ProjectivePolygonSide) (z : CanonicalProjectiveConeKeptSymbol p)
    (htarget : (⟨(canonicalProjectivePostConeTreeRoot hp hp2).state⟩ :
        ProjectivePolygonPostConeFace p) = projectivePolygonPostConeEdgeTarget z ∧
      s = projectivePolygonPostConeEdgeTargetSide z ∧
      canonicalProjectiveConePostConeBoundaryTerm p
        (canonicalProjectivePostConeTreeRoot hp hp2).state s = (FreeGroup.of z)⁻¹)
    (hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
    canonicalProjectivePostConeRawRootContourTermOfCasePhysicalList hp hp2
        (canonicalProjectivePostConeTreeRoot hp hp2).state s (.treeTarget z htarget hz) =
      canonicalProjectivePostConeRawForwardTreePhysicalList hp hp2
        (canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz) := by
  let child := canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz
  have hlabel := canonicalProjectivePostConeDirectTreeSlotOfDeleted_label hp hp2 z hz
  have hcarrier : CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p
      (canonicalProjectivePostConeTreeRoot hp hp2).state s
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) := by
    rw [hlabel]
    exact Or.inr htarget
  have hroot := (canonicalProjectivePostConeTreeSlot_rootBoundaryDart_of_physicalCarrier
    hp hp2 child s hcarrier).1
  have hleft : child.left = projectivePolygonPostConeEdgeTarget
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) := by
    rw [hlabel]
    exact hroot.trans htarget.1
  have hbit := canonicalProjectivePostConeRawSlotLeftSourceBit_eq_false_of_left_target
    hp hp2 child hleft
  simp [canonicalProjectivePostConeRawRootContourTermOfCasePhysicalList,
    canonicalProjectivePostConeRawRootContourTermOfCase,
    canonicalProjectivePostConeRawRootContourTermOfCase_positionEquiv,
    canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint,
    canonicalProjectivePostConeRawForwardTreePhysicalList,
    canonicalProjectivePostConeRawForwardTreeWordPosition_physicalEmbedding,
    canonicalProjectivePostConeRawForwardTreeWordPosition_endpoint,
    canonicalProjectivePostConeRawForwardTreeWordPosition_originalEquiv,
    canonicalProjectivePostConeRawForwardTreeWord, hbit, child]
  rfl

/-- Root-side expansion using normalized physical child decoders. -/
def canonicalProjectivePostConeRawForwardRootPhysicalTermOfCase
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide)
    (c : CanonicalProjectivePostConeRawRootContourTermCase hp hp2 q s) :
    List (CanonicalProjectivePolygonDart p) :=
  match c with
  | .one _ => []
  | .finalSource z _ _ => [projectivePolygonPostConeEdgeSourceDart z]
  | .finalTarget z _ _ => [projectivePolygonPostConeEdgeTargetDart z]
  | .treeSource z _ hz => canonicalProjectivePostConeRawForwardTreePhysicalList hp hp2
      (canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz)
  | .treeTarget z _ hz => canonicalProjectivePostConeRawForwardTreePhysicalList hp hp2
      (canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz)

/-- Normalized physical expansion of the root's selected side classifier. -/
def canonicalProjectivePostConeRawForwardRootPhysicalTerm
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide) :
    List (CanonicalProjectivePolygonDart p) :=
  canonicalProjectivePostConeRawForwardRootPhysicalTermOfCase hp hp2 q s
    (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s)

/-- Every classified root insertion preserves its complete ordered physical list. -/
theorem canonicalProjectivePostConeRawRootContourTermOfCasePhysicalList_eq_forward
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (s : ProjectivePolygonSide)
    (c : CanonicalProjectivePostConeRawRootContourTermCase hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state s) :
    canonicalProjectivePostConeRawRootContourTermOfCasePhysicalList hp hp2
        (canonicalProjectivePostConeTreeRoot hp hp2).state s c =
      canonicalProjectivePostConeRawForwardRootPhysicalTermOfCase hp hp2
        (canonicalProjectivePostConeTreeRoot hp hp2).state s c := by
  cases c with
  | one hterm => rfl
  | finalSource z hsource hz =>
      exact canonicalProjectivePostConeRawRootContourTermOfCasePhysicalList_finalSource
        hp hp2 _ s z hsource hz
  | finalTarget z htarget hz =>
      exact canonicalProjectivePostConeRawRootContourTermOfCasePhysicalList_finalTarget
        hp hp2 _ s z htarget hz
  | treeSource z hsource hz =>
      exact canonicalProjectivePostConeRawRootContourTermOfCasePhysicalList_treeSource
        hp hp2 s z hsource hz
  | treeTarget z htarget hz =>
      exact canonicalProjectivePostConeRawRootContourTermOfCasePhysicalList_treeTarget
        hp hp2 s z htarget hz

/-- Exact root position order equals the normalized physical eight-side expansion. -/
theorem canonicalProjectivePostConeRawRootPhysicalList_eq_forwardExpansion
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    canonicalProjectivePostConeRawRootPhysicalList hp hp2 =
      canonicalProjectivePostConeBoundarySideCycle.flatMap
        (canonicalProjectivePostConeRawForwardRootPhysicalTerm hp hp2
          (canonicalProjectivePostConeTreeRoot hp hp2).state) := by
  rw [canonicalProjectivePostConeRawRootPhysicalList_eq_flatMap]
  congr 1
  funext s
  exact canonicalProjectivePostConeRawRootContourTermOfCasePhysicalList_eq_forward hp hp2 s _

#print axioms canonicalProjectivePostConeRawRootContourTermsPhysicalList_cons
#print axioms canonicalProjectivePostConeRawRootPhysicalList_eq_flatMap
#print axioms canonicalProjectivePostConeRawRootContourTermOfCasePhysicalList_treeSource
#print axioms canonicalProjectivePostConeRawRootContourTermOfCasePhysicalList_treeTarget
#print axioms canonicalProjectivePostConeRawRootPhysicalList_eq_forwardExpansion

end

end SystolicGrowth
