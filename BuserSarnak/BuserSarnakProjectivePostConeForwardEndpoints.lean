module

public import BuserSarnak.BuserSarnakProjectivePostConeForwardContour
public import BuserSarnak.BuserSarnakProjectivePostConeSurvivorEmbedding

@[expose] public section

/-!
# Physical endpoint decoders for forward child contours

Normalize slot positions, not merely their signed letters. Inverse reversal
reverses occurrence order and toggles the Boolean orientation while preserving
the exact physical endpoint constructor.
-/

namespace SystolicGrowth

noncomputable section

/-- Reindex a forward child-word position in the original recursive slot word. -/
def canonicalProjectivePostConeRawForwardTreeWordPosition_originalEquiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    Fin (canonicalProjectivePostConeRawForwardTreeWord hp hp2 slot).length ≃
      Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot).length := by
  classical
  let word := canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot
  by_cases hbit : canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 slot = true
  · exact finCongr (congrArg List.length
      (by simp [canonicalProjectivePostConeRawForwardTreeWord, hbit]))
  · exact (finCongr (congrArg List.length
      (by simp [canonicalProjectivePostConeRawForwardTreeWord, hbit, word]))).trans
      (Equiv.ofBijective (@invRevPosition _ word) (invRevPosition_bijective word)).symm

/-- Normalization preserves the total number of occurrences. -/
theorem canonicalProjectivePostConeRawForwardTreeWord_length
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    (canonicalProjectivePostConeRawForwardTreeWord hp hp2 slot).length =
      (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot).length := by
  unfold canonicalProjectivePostConeRawForwardTreeWord
  split_ifs <;> simp

/-- The original occurrence number is unchanged in the forward slot orientation. -/
theorem canonicalProjectivePostConeRawForwardTreeWordPosition_originalEquiv_val_true
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hbit : canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 slot = true)
    (i : Fin (canonicalProjectivePostConeRawForwardTreeWord hp hp2 slot).length) :
    (canonicalProjectivePostConeRawForwardTreeWordPosition_originalEquiv
      hp hp2 slot i).val = i.val := by
  simp [canonicalProjectivePostConeRawForwardTreeWordPosition_originalEquiv, hbit]

/-- Reversal reverses occurrence numbers; it does not change endpoint identity. -/
theorem canonicalProjectivePostConeRawForwardTreeWordPosition_originalEquiv_val_false
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hbit : canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 slot = false)
    (i : Fin (canonicalProjectivePostConeRawForwardTreeWord hp hp2 slot).length) :
    (canonicalProjectivePostConeRawForwardTreeWordPosition_originalEquiv
      hp hp2 slot i).val =
      (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot).length - 1 - i.val := by
  let word := canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot
  let e := Equiv.ofBijective (@invRevPosition _ word) (invRevPosition_bijective word)
  have hlen : (canonicalProjectivePostConeRawForwardTreeWord hp hp2 slot).length =
      (FreeGroup.invRev word).length := by
    simp [canonicalProjectivePostConeRawForwardTreeWord, hbit, word]
  have hpos : invRevPosition
      (canonicalProjectivePostConeRawForwardTreeWordPosition_originalEquiv hp hp2 slot i) =
      Fin.cast hlen i := by
    change e (canonicalProjectivePostConeRawForwardTreeWordPosition_originalEquiv
      hp hp2 slot i) = Fin.cast hlen i
    simp only [canonicalProjectivePostConeRawForwardTreeWordPosition_originalEquiv,
      hbit, Bool.false_eq_true, ↓reduceDIte, Equiv.trans_apply, finCongr_apply]
    exact e.apply_symm_apply _
  have hval := congrArg Fin.val hpos
  simp only [invRevPosition, Fin.val_cast, Fin.val_rev] at hval
  change word.length -
    ((canonicalProjectivePostConeRawForwardTreeWordPosition_originalEquiv
      hp hp2 slot i).val + 1) = i.val at hval
  have hlt := (canonicalProjectivePostConeRawForwardTreeWordPosition_originalEquiv
    hp hp2 slot i).isLt
  change _ < word.length at hlt
  change _ = word.length - 1 - i.val
  omega

/-- Decode the exact retained occurrence and orientation in a normalized
forward child boundary. Only the orientation bit is toggled on reversal. -/
def canonicalProjectivePostConeRawForwardTreeWordPosition_endpoint
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (i : Fin (canonicalProjectivePostConeRawForwardTreeWord hp hp2 slot).length) :
    CanonicalProjectivePostConeSurvivingDart hp hp2 × Bool :=
  let endpoint := canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 slot
    (canonicalProjectivePostConeRawForwardTreeWordPosition_originalEquiv hp hp2 slot i)
  if canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 slot then endpoint
  else (endpoint.1, !endpoint.2)

/-- Place a forward-word occurrence at its actual original polygon dart. -/
def canonicalProjectivePostConeRawForwardTreeWordPosition_physicalEmbedding
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (i : Fin (canonicalProjectivePostConeRawForwardTreeWord hp hp2 slot).length) :
    CanonicalProjectivePolygonDart p :=
  canonicalProjectivePostConeSurvivingDart_embedding hp hp2
    (canonicalProjectivePostConeRawForwardTreeWordPosition_endpoint hp hp2 slot i).1

/-- Inverse reversal preserves the exact physical endpoint constructor. -/
theorem canonicalProjectivePostConeRawForwardTreeWordPosition_endpoint_fst
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (i : Fin (canonicalProjectivePostConeRawForwardTreeWord hp hp2 slot).length) :
    (canonicalProjectivePostConeRawForwardTreeWordPosition_endpoint hp hp2 slot i).1 =
      (canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 slot
        (canonicalProjectivePostConeRawForwardTreeWordPosition_originalEquiv
          hp hp2 slot i)).1 := by
  unfold canonicalProjectivePostConeRawForwardTreeWordPosition_endpoint
  split_ifs <;> rfl

/-- Distinct forward positions remain distinct actual physical darts. -/
theorem canonicalProjectivePostConeRawForwardTreeWordPosition_physicalEmbedding_injective
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    Function.Injective
      (canonicalProjectivePostConeRawForwardTreeWordPosition_physicalEmbedding hp hp2 slot) := by
  intro i j hij
  apply (canonicalProjectivePostConeRawForwardTreeWordPosition_originalEquiv
    hp hp2 slot).injective
  apply canonicalProjectivePostConeRawTreeWordPosition_endpoint_injective hp hp2 slot
  have h := canonicalProjectivePostConeSurvivingDart_embedding_injective hp hp2 hij
  simpa only [canonicalProjectivePostConeRawForwardTreeWordPosition_endpoint_fst] using h

/-- Ordered physical endpoints of the normalized open child boundary. -/
def canonicalProjectivePostConeRawForwardTreePhysicalList
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    List (CanonicalProjectivePolygonDart p) :=
  List.ofFn (canonicalProjectivePostConeRawForwardTreeWordPosition_physicalEmbedding
    hp hp2 slot)

/-- Ordered forward suffix/prefix position split, independent of slot orientation. -/
def canonicalProjectivePostConeRawForwardTreeWordPosition_split
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    Fin (canonicalProjectivePostConeRawForwardTreeWord hp hp2 slot).length ≃
      Fin (canonicalProjectivePostConeRawContourSuffix hp hp2 slot
        (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)).length ⊕
      Fin (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
        (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)).length :=
  (finCongr (congrArg List.length
    (canonicalProjectivePostConeRawForwardTreeWord_eq_suffix_prefix hp hp2 slot))).trans
    (canonicalProjectivePostConeRawAppendPositionSplit _ _)

/-- Physical endpoint decoder of an ordered side-list expansion. -/
def canonicalProjectivePostConeRawContourTermsPosition_endpoint
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (sides : List ProjectivePolygonSide)
    (i : Fin (canonicalProjectivePostConeRawContourTerms hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
      sides).length) : CanonicalProjectivePostConeSurvivingDart hp hp2 × Bool :=
  canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot
    (fun child _ => canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child)
    sides (canonicalProjectivePostConeRawContourTerms_originEquiv hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) sides i)

/-- The physical endpoint list of an ordered side expansion. -/
def canonicalProjectivePostConeRawContourTermsPhysicalList
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (sides : List ProjectivePolygonSide) : List (CanonicalProjectivePolygonDart p) :=
  List.ofFn (fun i => canonicalProjectivePostConeSurvivingDart_embedding hp hp2
    (canonicalProjectivePostConeRawContourTermsPosition_endpoint hp hp2 slot sides i).1)

/-- Forward suffix positions preserve the exact physical endpoint and sign
of the side-list decoder, in either orientation of the incoming edge. -/
theorem canonicalProjectivePostConeRawForwardTreeWordPosition_endpoint_suffix
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (i : Fin (canonicalProjectivePostConeRawContourSuffix hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)).length) :
    canonicalProjectivePostConeRawForwardTreeWordPosition_endpoint hp hp2 slot
        ((canonicalProjectivePostConeRawForwardTreeWordPosition_split
          hp hp2 slot).symm (Sum.inl i)) =
      canonicalProjectivePostConeRawContourTermsPosition_endpoint hp hp2 slot
        (canonicalProjectivePostConeBoundarySuffixSides
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) i := by
  classical
  let tag := canonicalProjectivePostConeRawContourSuffix_originEquiv hp hp2 slot i
  rcases canonicalProjectivePostConeTreeSlot_endpoints_eq_physicalEndpoints hp hp2 slot with
    hforward | hreverse
  · have hbit := canonicalProjectivePostConeRawSlotLeftSourceBit_eq_true_of_left_source
      hp hp2 slot hforward.1
    have ht : slot.right ≠ projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) := by
      rw [hforward.2]
      exact (canonicalProjectivePostConeTreeSlot_edgeSource_ne_edgeTarget hp hp2 slot).symm
    have hpos : canonicalProjectivePostConeRawForwardTreeWordPosition_originalEquiv
        hp hp2 slot ((canonicalProjectivePostConeRawForwardTreeWordPosition_split
          hp hp2 slot).symm (Sum.inl i)) =
        (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 slot).symm
          (.target ht (Sum.inl tag)) := by
      apply Fin.ext
      rw [canonicalProjectivePostConeRawForwardTreeWordPosition_originalEquiv_val_true
        hp hp2 slot hbit]
      simp only [canonicalProjectivePostConeRawTreeWordBySlot_originEquiv]
      dsimp only [Equiv.symm]
      split_ifs with hs
      · exact False.elim (ht hs.symm)
      · simp [canonicalProjectivePostConeRawForwardTreeWordPosition_split,
          canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_target,
          canonicalProjectivePostConeRawAppendPositionSplit, tag]
    unfold canonicalProjectivePostConeRawForwardTreeWordPosition_endpoint
    rw [hpos]
    simp only [hbit, ↓reduceIte, canonicalProjectivePostConeRawTreeWordPosition_endpoint,
      Equiv.apply_symm_apply]
    unfold canonicalProjectivePostConeRawTreeWordOrigin_endpoint
    rw [WellFounded.fix_eq]
    rfl
  · have hbit := canonicalProjectivePostConeRawSlotLeftSourceBit_eq_false_of_left_target
      hp hp2 slot hreverse.1
    have hs := hreverse.2
    have hpos : canonicalProjectivePostConeRawForwardTreeWordPosition_originalEquiv
        hp hp2 slot ((canonicalProjectivePostConeRawForwardTreeWordPosition_split
          hp hp2 slot).symm (Sum.inl i)) =
        (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 slot).symm
          (.source hs (Sum.inr tag)) := by
      apply Fin.ext
      rw [canonicalProjectivePostConeRawForwardTreeWordPosition_originalEquiv_val_false
        hp hp2 slot hbit]
      simp only [canonicalProjectivePostConeRawTreeWordBySlot_originEquiv]
      dsimp only [Equiv.symm]
      split_ifs with hsource
      · simp [canonicalProjectivePostConeRawForwardTreeWordPosition_split,
          canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_source,
          canonicalProjectivePostConeRawAppendPositionSplit,
          canonicalProjectivePostConeRawContourSuffix_invRev_originEquiv,
          canonicalProjectivePostConeRawContourTerms_invRev_originEquiv,
          canonicalProjectivePostConeRawContourSuffix_originEquiv, tag,
          invRevPosition, Fin.val_rev]
        rw [canonicalProjectivePostConeRawTreeWordBySlot_eq_splice_of_source
          hp hp2 slot hs]
        simp only [List.length_append, FreeGroup.invRev_length]
        have hi := i.isLt
        change _ = (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
          (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)).length +
          ((canonicalProjectivePostConeRawContourSuffix hp hp2 slot
            (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)).length -
            (i.val + 1))
        omega
      · exact False.elim (hsource hs.symm)
    unfold canonicalProjectivePostConeRawForwardTreeWordPosition_endpoint
    rw [hpos]
    simp only [hbit, Bool.false_eq_true, ↓reduceIte,
      canonicalProjectivePostConeRawTreeWordPosition_endpoint, Equiv.apply_symm_apply]
    unfold canonicalProjectivePostConeRawTreeWordOrigin_endpoint
    rw [WellFounded.fix_eq]
    simp only [canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step, Sum.elim_inr,
      Bool.not_not]
    rfl

/-- Forward prefix positions preserve the exact physical endpoint and sign;
the source-oriented raw splice has its two sign flips canceled. -/
theorem canonicalProjectivePostConeRawForwardTreeWordPosition_endpoint_prefix
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (i : Fin (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)).length) :
    canonicalProjectivePostConeRawForwardTreeWordPosition_endpoint hp hp2 slot
        ((canonicalProjectivePostConeRawForwardTreeWordPosition_split
          hp hp2 slot).symm (Sum.inr i)) =
      canonicalProjectivePostConeRawContourTermsPosition_endpoint hp hp2 slot
        (canonicalProjectivePostConeBoundaryPrefixSides
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) i := by
  classical
  let tag := canonicalProjectivePostConeRawContourPrefix_originEquiv hp hp2 slot i
  rcases canonicalProjectivePostConeTreeSlot_endpoints_eq_physicalEndpoints hp hp2 slot with
    hforward | hreverse
  · have hbit := canonicalProjectivePostConeRawSlotLeftSourceBit_eq_true_of_left_source
      hp hp2 slot hforward.1
    have ht : slot.right ≠ projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) := by
      rw [hforward.2]
      exact (canonicalProjectivePostConeTreeSlot_edgeSource_ne_edgeTarget hp hp2 slot).symm
    have hpos : canonicalProjectivePostConeRawForwardTreeWordPosition_originalEquiv
        hp hp2 slot ((canonicalProjectivePostConeRawForwardTreeWordPosition_split
          hp hp2 slot).symm (Sum.inr i)) =
        (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 slot).symm
          (.target ht (Sum.inr tag)) := by
      apply Fin.ext
      rw [canonicalProjectivePostConeRawForwardTreeWordPosition_originalEquiv_val_true
        hp hp2 slot hbit]
      simp only [canonicalProjectivePostConeRawTreeWordBySlot_originEquiv]
      dsimp only [Equiv.symm]
      split_ifs with hs
      · exact False.elim (ht hs.symm)
      · simp [canonicalProjectivePostConeRawForwardTreeWordPosition_split,
          canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_target,
          canonicalProjectivePostConeRawAppendPositionSplit, tag]
    unfold canonicalProjectivePostConeRawForwardTreeWordPosition_endpoint
    rw [hpos]
    simp only [hbit, ↓reduceIte, canonicalProjectivePostConeRawTreeWordPosition_endpoint,
      Equiv.apply_symm_apply]
    unfold canonicalProjectivePostConeRawTreeWordOrigin_endpoint
    rw [WellFounded.fix_eq]
    rfl
  · have hbit := canonicalProjectivePostConeRawSlotLeftSourceBit_eq_false_of_left_target
      hp hp2 slot hreverse.1
    have hs := hreverse.2
    have hpos : canonicalProjectivePostConeRawForwardTreeWordPosition_originalEquiv
        hp hp2 slot ((canonicalProjectivePostConeRawForwardTreeWordPosition_split
          hp hp2 slot).symm (Sum.inr i)) =
        (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 slot).symm
          (.source hs (Sum.inl tag)) := by
      apply Fin.ext
      rw [canonicalProjectivePostConeRawForwardTreeWordPosition_originalEquiv_val_false
        hp hp2 slot hbit]
      simp only [canonicalProjectivePostConeRawTreeWordBySlot_originEquiv]
      dsimp only [Equiv.symm]
      split_ifs with hsource
      · simp [canonicalProjectivePostConeRawForwardTreeWordPosition_split,
          canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_source,
          canonicalProjectivePostConeRawAppendPositionSplit,
          canonicalProjectivePostConeRawContourPrefix_invRev_originEquiv,
          canonicalProjectivePostConeRawContourTerms_invRev_originEquiv,
          canonicalProjectivePostConeRawContourPrefix_originEquiv, tag,
          invRevPosition, Fin.val_rev]
        rw [canonicalProjectivePostConeRawTreeWordBySlot_eq_splice_of_source
          hp hp2 slot hs]
        simp only [List.length_append, FreeGroup.invRev_length]
        change _ = (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
          (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)).length -
          (i.val + 1)
        omega
      · exact False.elim (hsource hs.symm)
    unfold canonicalProjectivePostConeRawForwardTreeWordPosition_endpoint
    rw [hpos]
    simp only [hbit, Bool.false_eq_true, ↓reduceIte,
      canonicalProjectivePostConeRawTreeWordPosition_endpoint, Equiv.apply_symm_apply]
    unfold canonicalProjectivePostConeRawTreeWordOrigin_endpoint
    rw [WellFounded.fix_eq]
    simp only [canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step, Sum.elim_inl,
      Bool.not_not]
    rfl

/-- The actual decoded forward endpoint list is the suffix endpoint list
followed by the prefix endpoint list. This is literal ordered equality. -/
theorem canonicalProjectivePostConeRawForwardTreePhysicalList_eq_suffix_prefix
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    canonicalProjectivePostConeRawForwardTreePhysicalList hp hp2 slot =
      canonicalProjectivePostConeRawContourTermsPhysicalList hp hp2 slot
          (canonicalProjectivePostConeBoundarySuffixSides
            (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) ++
        canonicalProjectivePostConeRawContourTermsPhysicalList hp hp2 slot
          (canonicalProjectivePostConeBoundaryPrefixSides
            (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) := by
  let suffixWord := canonicalProjectivePostConeRawContourSuffix hp hp2 slot
    (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
  let prefixWord := canonicalProjectivePostConeRawContourPrefix hp hp2 slot
    (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
  let sf := fun i : Fin suffixWord.length =>
    canonicalProjectivePostConeSurvivingDart_embedding hp hp2
      (canonicalProjectivePostConeRawContourTermsPosition_endpoint hp hp2 slot
        (canonicalProjectivePostConeBoundarySuffixSides
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) i).1
  let pf := fun i : Fin prefixWord.length =>
    canonicalProjectivePostConeSurvivingDart_embedding hp hp2
      (canonicalProjectivePostConeRawContourTermsPosition_endpoint hp hp2 slot
        (canonicalProjectivePostConeBoundaryPrefixSides
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) i).1
  have hdecode : ∀ i, canonicalProjectivePostConeRawForwardTreeWordPosition_physicalEmbedding
      hp hp2 slot i = Sum.elim sf pf
        (canonicalProjectivePostConeRawForwardTreeWordPosition_split hp hp2 slot i) := by
    intro i
    rw [← (canonicalProjectivePostConeRawForwardTreeWordPosition_split
      hp hp2 slot).symm_apply_apply i]
    rcases htag : canonicalProjectivePostConeRawForwardTreeWordPosition_split
        hp hp2 slot i with j | j
    · simp only [Equiv.apply_symm_apply, Sum.elim_inl,
        canonicalProjectivePostConeRawForwardTreeWordPosition_physicalEmbedding]
      rw [canonicalProjectivePostConeRawForwardTreeWordPosition_endpoint_suffix]
    · simp only [Equiv.apply_symm_apply, Sum.elim_inr,
        canonicalProjectivePostConeRawForwardTreeWordPosition_physicalEmbedding]
      rw [canonicalProjectivePostConeRawForwardTreeWordPosition_endpoint_prefix]
  have hlen : (canonicalProjectivePostConeRawForwardTreeWord hp hp2 slot).length =
      suffixWord.length + prefixWord.length := by
    rw [canonicalProjectivePostConeRawForwardTreeWord_eq_suffix_prefix]
    exact List.length_append
  unfold canonicalProjectivePostConeRawForwardTreePhysicalList
  rw [List.ofFn_congr hlen]
  change List.ofFn (fun i => canonicalProjectivePostConeRawForwardTreeWordPosition_physicalEmbedding
    hp hp2 slot (Fin.cast hlen.symm i)) = List.ofFn sf ++ List.ofFn pf
  have hfun : (fun i => canonicalProjectivePostConeRawForwardTreeWordPosition_physicalEmbedding
      hp hp2 slot (Fin.cast hlen.symm i)) = Fin.append sf pf := by
    funext i
    rw [hdecode]
    cases i using Fin.addCases with
    | left i =>
        simp [canonicalProjectivePostConeRawForwardTreeWordPosition_split,
          canonicalProjectivePostConeRawAppendPositionSplit, Fin.append]
        change Sum.elim sf pf
          (finSumFinEquiv.symm (Fin.castAdd prefixWord.length i)) = sf i
        rw [finSumFinEquiv_symm_apply_castAdd]
        rfl
    | right i =>
        simp [canonicalProjectivePostConeRawForwardTreeWordPosition_split,
          canonicalProjectivePostConeRawAppendPositionSplit, Fin.append]
        change Sum.elim sf pf
          (finSumFinEquiv.symm (Fin.natAdd suffixWord.length i)) = pf i
        rw [finSumFinEquiv_symm_apply_natAdd]
        rfl
  rw [hfun, List.ofFn_fin_append]

/-- Ordered physical occurrences of one classified off-pivot side term. -/
def canonicalProjectivePostConeRawContourTermOfCasePhysicalList
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (s : ProjectivePolygonSide)
    (c : CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s) :
    List (CanonicalProjectivePolygonDart p) :=
  List.ofFn (fun i => canonicalProjectivePostConeSurvivingDart_embedding hp hp2
    (canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child)
      c (canonicalProjectivePostConeRawContourTermOfCase_positionEquiv hp hp2 slot
        (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) c i)).1)

/-- A degenerate side contributes no physical occurrence. -/
@[simp] theorem canonicalProjectivePostConeRawContourTermOfCasePhysicalList_one
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) (s : ProjectivePolygonSide)
    (hone : canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s = 1) :
    canonicalProjectivePostConeRawContourTermOfCasePhysicalList hp hp2 slot s (.one hone) =
      [] := rfl

/-- A retained source side contributes its actual source dart. -/
@[simp] theorem canonicalProjectivePostConeRawContourTermOfCasePhysicalList_finalSource
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (s : ProjectivePolygonSide) (z : CanonicalProjectiveConeKeptSymbol p)
    (hsource : (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeSource z ∧
      s = projectivePolygonPostConeEdgeSide z ∧
      canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s = FreeGroup.of z)
    (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
    canonicalProjectivePostConeRawContourTermOfCasePhysicalList hp hp2 slot s
      (.finalSource z hsource hz) = [projectivePolygonPostConeEdgeSourceDart z] := rfl

/-- A retained target side contributes its actual target dart. -/
@[simp] theorem canonicalProjectivePostConeRawContourTermOfCasePhysicalList_finalTarget
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (s : ProjectivePolygonSide) (z : CanonicalProjectiveConeKeptSymbol p)
    (htarget : (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeTarget z ∧
      s = projectivePolygonPostConeEdgeTargetSide z ∧
      canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s = (FreeGroup.of z)⁻¹)
    (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
    canonicalProjectivePostConeRawContourTermOfCasePhysicalList hp hp2 slot s
      (.finalTarget z htarget hz) = [projectivePolygonPostConeEdgeTargetDart z] := rfl

/-- A source child insertion is the normalized forward child list, not an
arbitrary permutation of its signed letters. -/
theorem canonicalProjectivePostConeRawContourTermOfCasePhysicalList_deeperSource
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (s : ProjectivePolygonSide) (z : CanonicalProjectiveConeKeptSymbol p)
    (hsource : (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeSource z ∧
      s = projectivePolygonPostConeEdgeSide z ∧
      canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s = FreeGroup.of z)
    (hlabel : canonicalProjectivePostConeTreeSlotLabel hp hp2 child = z)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child) :
    canonicalProjectivePostConeRawContourTermOfCasePhysicalList hp hp2 slot s
        (.deeperSource z child hsource hlabel hdeep) =
      canonicalProjectivePostConeRawForwardTreePhysicalList hp hp2 child := by
  have hj := canonicalProjectivePostConeRawContourTermCase_deeperSource_join
    hp hp2 slot child z hsource.1 hlabel hdeep
  have hface : slot.right = projectivePolygonPostConeEdgeSource z := by
    apply ProjectivePolygonPostConeFace.stateEquiv.injective
    exact congrArg ProjectivePolygonPostConeFace.state hsource.1
  have hleft : child.left = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) := by
    rw [hlabel]
    exact hj.symm.trans hface
  have hbit := canonicalProjectivePostConeRawSlotLeftSourceBit_eq_true_of_left_source
    hp hp2 child hleft
  simp [canonicalProjectivePostConeRawContourTermOfCasePhysicalList,
    canonicalProjectivePostConeRawContourTermOfCase,
    canonicalProjectivePostConeRawContourTermOfCase_positionEquiv,
    canonicalProjectivePostConeRawTermOrigin_endpoint,
    canonicalProjectivePostConeRawForwardTreePhysicalList,
    canonicalProjectivePostConeRawForwardTreeWordPosition_physicalEmbedding,
    canonicalProjectivePostConeRawForwardTreeWordPosition_endpoint,
    canonicalProjectivePostConeRawForwardTreeWordPosition_originalEquiv,
    canonicalProjectivePostConeRawForwardTreeWord,
    canonicalProjectivePostConeRawTreeWordPosition_endpoint, hbit]
  rfl

/-- A target child insertion reverses its raw positions exactly as the
normalization does; both denote the same ordered physical forward child list. -/
theorem canonicalProjectivePostConeRawContourTermOfCasePhysicalList_deeperTarget
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (s : ProjectivePolygonSide) (z : CanonicalProjectiveConeKeptSymbol p)
    (htarget : (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeTarget z ∧
      s = projectivePolygonPostConeEdgeTargetSide z ∧
      canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s = (FreeGroup.of z)⁻¹)
    (hlabel : canonicalProjectivePostConeTreeSlotLabel hp hp2 child = z)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child) :
    canonicalProjectivePostConeRawContourTermOfCasePhysicalList hp hp2 slot s
        (.deeperTarget z child htarget hlabel hdeep) =
      canonicalProjectivePostConeRawForwardTreePhysicalList hp hp2 child := by
  have hj := canonicalProjectivePostConeRawContourTermCase_deeperTarget_join
    hp hp2 slot child z htarget.1 hlabel hdeep
  have hface : slot.right = projectivePolygonPostConeEdgeTarget z := by
    apply ProjectivePolygonPostConeFace.stateEquiv.injective
    exact congrArg ProjectivePolygonPostConeFace.state htarget.1
  have hleft : child.left = projectivePolygonPostConeEdgeTarget
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) := by
    rw [hlabel]
    exact hj.symm.trans hface
  have hbit := canonicalProjectivePostConeRawSlotLeftSourceBit_eq_false_of_left_target
    hp hp2 child hleft
  simp [canonicalProjectivePostConeRawContourTermOfCasePhysicalList,
    canonicalProjectivePostConeRawContourTermOfCase,
    canonicalProjectivePostConeRawContourTermOfCase_positionEquiv,
    canonicalProjectivePostConeRawTermOrigin_endpoint,
    canonicalProjectivePostConeRawForwardTreePhysicalList,
    canonicalProjectivePostConeRawForwardTreeWordPosition_physicalEmbedding,
    canonicalProjectivePostConeRawForwardTreeWordPosition_endpoint,
    canonicalProjectivePostConeRawForwardTreeWordPosition_originalEquiv,
    canonicalProjectivePostConeRawForwardTreeWord,
    canonicalProjectivePostConeRawTreeWordPosition_endpoint, hbit]
  rfl

#print axioms canonicalProjectivePostConeRawForwardTreeWordPosition_endpoint_suffix
#print axioms canonicalProjectivePostConeRawForwardTreeWordPosition_endpoint_prefix
#print axioms canonicalProjectivePostConeRawForwardTreePhysicalList_eq_suffix_prefix
#print axioms canonicalProjectivePostConeRawContourTermOfCasePhysicalList_deeperSource
#print axioms canonicalProjectivePostConeRawContourTermOfCasePhysicalList_deeperTarget

/-- Decoded finite lists split into the left and right offset blocks when
the decoder respects the canonical finite sum decomposition. -/
theorem ofFn_eq_append_of_finSumSplit
    {α : Type*} {n m k : ℕ} (hlen : n = m + k)
    (decode : Fin n → α) (left : Fin m → α) (right : Fin k → α)
    (hleft : ∀ i, decode (((finCongr hlen).trans finSumFinEquiv.symm).symm
      (Sum.inl i)) = left i)
    (hright : ∀ i, decode (((finCongr hlen).trans finSumFinEquiv.symm).symm
      (Sum.inr i)) = right i) :
    List.ofFn decode = List.ofFn left ++ List.ofFn right := by
  let e := (finCongr hlen).trans finSumFinEquiv.symm
  have hdecode : ∀ i, decode i = Sum.elim left right (e i) := by
    intro i
    rw [← e.symm_apply_apply i]
    rcases htag : e i with j | j
    · simpa only [Equiv.apply_symm_apply, Sum.elim_inl] using hleft j
    · simpa only [Equiv.apply_symm_apply, Sum.elim_inr] using hright j
  rw [List.ofFn_congr hlen]
  have hfun : (fun i => decode (Fin.cast hlen.symm i)) = Fin.append left right := by
    funext i
    rw [hdecode]
    cases i using Fin.addCases with
    | left i =>
        simp only [e, Equiv.trans_apply, finCongr_apply, Fin.cast_cast,
          Fin.cast_refl, id_eq, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl,
          Fin.append_left]
    | right i =>
        simp only [e, Equiv.trans_apply, finCongr_apply, Fin.cast_cast,
          Fin.cast_refl, id_eq, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr,
          Fin.append_right]
  rw [hfun, List.ofFn_fin_append]

/-- Physical endpoint decoder for one side's selected literal expansion. -/
def canonicalProjectivePostConeRawContourTermPosition_endpoint
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) (s : ProjectivePolygonSide)
    (i : Fin (canonicalProjectivePostConeRawContourTerm hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) s).length) :
    CanonicalProjectivePostConeSurvivingDart hp hp2 × Bool :=
  canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot
    (fun child _ => canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child)
    s (canonicalProjectivePostConeRawContourSide_positionEquiv hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) s i)

/-- The physical list of a selected side term. -/
def canonicalProjectivePostConeRawContourTermPhysicalList
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) (s : ProjectivePolygonSide) :
    List (CanonicalProjectivePolygonDart p) :=
  List.ofFn (fun i => canonicalProjectivePostConeSurvivingDart_embedding hp hp2
    (canonicalProjectivePostConeRawContourTermPosition_endpoint hp hp2 slot s i).1)

set_option backward.isDefEq.respectTransparency false in
/-- Ordered side-list decoding respects head/tail concatenation. -/
theorem canonicalProjectivePostConeRawContourTermsPhysicalList_cons
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (s : ProjectivePolygonSide) (ss : List ProjectivePolygonSide) :
    canonicalProjectivePostConeRawContourTermsPhysicalList hp hp2 slot (s :: ss) =
      canonicalProjectivePostConeRawContourTermPhysicalList hp hp2 slot s ++
        canonicalProjectivePostConeRawContourTermsPhysicalList hp hp2 slot ss := by
  unfold canonicalProjectivePostConeRawContourTermsPhysicalList
    canonicalProjectivePostConeRawContourTermPhysicalList
  apply ofFn_eq_append_of_finSumSplit
    (by simp [canonicalProjectivePostConeRawContourTerms])
  · intro i
    unfold canonicalProjectivePostConeRawContourTermsPosition_endpoint
      canonicalProjectivePostConeRawContourTermPosition_endpoint
    change canonicalProjectivePostConeSurvivingDart_embedding hp hp2
      (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot
        (fun child _ => canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child)
        (s :: ss) ((canonicalProjectivePostConeRawContourTerms_originEquiv hp hp2 slot
          (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) (s :: ss))
          ((canonicalProjectivePostConeRawContourTerms_positionSplit_cons hp hp2 slot
            (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
            s ss).symm (Sum.inl i)))).1 = _
    change canonicalProjectivePostConeSurvivingDart_embedding hp hp2
      (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot
        (fun child _ => canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child)
        (s :: ss) ((Equiv.sumCongr
          (canonicalProjectivePostConeRawContourSide_positionEquiv hp hp2 slot
            (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) s)
          (canonicalProjectivePostConeRawContourTerms_originEquiv hp hp2 slot
            (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) ss))
          ((canonicalProjectivePostConeRawContourTerms_positionSplit_cons hp hp2 slot
            (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) s ss)
            ((canonicalProjectivePostConeRawContourTerms_positionSplit_cons hp hp2 slot
              (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
              s ss).symm (Sum.inl i))))).1 = _
    rw [Equiv.apply_symm_apply]
    rfl
  · intro i
    unfold canonicalProjectivePostConeRawContourTermsPosition_endpoint
    change canonicalProjectivePostConeSurvivingDart_embedding hp hp2
      (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot
        (fun child _ => canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child)
        (s :: ss) ((canonicalProjectivePostConeRawContourTerms_originEquiv hp hp2 slot
          (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) (s :: ss))
          ((canonicalProjectivePostConeRawContourTerms_positionSplit_cons hp hp2 slot
            (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
            s ss).symm (Sum.inr i)))).1 = _
    change canonicalProjectivePostConeSurvivingDart_embedding hp hp2
      (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot
        (fun child _ => canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child)
        (s :: ss) ((Equiv.sumCongr
          (canonicalProjectivePostConeRawContourSide_positionEquiv hp hp2 slot
            (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) s)
          (canonicalProjectivePostConeRawContourTerms_originEquiv hp hp2 slot
            (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) ss))
          ((canonicalProjectivePostConeRawContourTerms_positionSplit_cons hp hp2 slot
            (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) s ss)
            ((canonicalProjectivePostConeRawContourTerms_positionSplit_cons hp hp2 slot
              (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
              s ss).symm (Sum.inr i))))).1 = _
    rw [Equiv.apply_symm_apply]
    rfl

/-- The physical side-list expansion is exactly the flat concatenation of
the selected physical side terms, with no support-only replacement. -/
theorem canonicalProjectivePostConeRawContourTermsPhysicalList_eq_flatMap
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (sides : List ProjectivePolygonSide) :
    canonicalProjectivePostConeRawContourTermsPhysicalList hp hp2 slot sides =
      sides.flatMap (canonicalProjectivePostConeRawContourTermPhysicalList hp hp2 slot) := by
  induction sides with
  | nil => rfl
  | cons s ss ih =>
      rw [canonicalProjectivePostConeRawContourTermsPhysicalList_cons, ih, List.flatMap_cons]

/-- The pivot contributes no retained physical occurrence. -/
theorem canonicalProjectivePostConeRawContourTermPhysicalList_pivot
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    canonicalProjectivePostConeRawContourTermPhysicalList hp hp2 slot
      (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) = [] := by
  simp [canonicalProjectivePostConeRawContourTermPhysicalList,
    canonicalProjectivePostConeRawContourTerm]

/-- Selecting an off-pivot classifier preserves the ordered physical term
decoder, including its exact dependent origin tag. -/
theorem canonicalProjectivePostConeRawContourTermPhysicalList_eq_ofCase
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) :
    canonicalProjectivePostConeRawContourTermPhysicalList hp hp2 slot s =
      canonicalProjectivePostConeRawContourTermOfCasePhysicalList hp hp2 slot s
        (canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs) := by
  simp [canonicalProjectivePostConeRawContourTermPhysicalList,
    canonicalProjectivePostConeRawContourTermPosition_endpoint,
    canonicalProjectivePostConeRawSideOrigin_endpoint, hs]
  unfold canonicalProjectivePostConeRawContourTermOfCasePhysicalList
    canonicalProjectivePostConeRawContourTerm_positionEquiv
  simp [canonicalProjectivePostConeRawContourTerm_eq_termOfCase hp hp2 slot
    (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) s hs]

#print axioms canonicalProjectivePostConeRawContourTermsPhysicalList_cons
#print axioms canonicalProjectivePostConeRawContourTermsPhysicalList_eq_flatMap
#print axioms canonicalProjectivePostConeRawContourTermPhysicalList_eq_ofCase

end

end SystolicGrowth
