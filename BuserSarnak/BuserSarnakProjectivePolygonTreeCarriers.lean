module

public import BuserSarnak.BuserSarnakProjectivePolygonDarts
public import BuserSarnak.BuserSarnakProjectiveCanonicalTree
public import BuserSarnak.BuserSarnakProjectivePolygonPostConeQuiver

@[expose] public section

/-!
# Canonical tree carriers in projective polygon darts

Each degenerate Schreier symbol is carried by a distinguished positive polygon
side and by the paired side at its tree target.  This local interface records
their exact boundary incidences for the cut argument, without asserting any
global dual connectivity.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete

noncomputable local instance buserSarnakProjectivePolygonTreeCarriersRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

/-- A directed side occurrence in a canonical projective polygon face. -/
abbrev CanonicalProjectivePolygonDart (p : ℕ) [NeZero p] :=
  BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide

namespace BuserSarnakProjectiveQuotientSectionData

/-- The terminal state of the positively oriented raw Schreier symbol carried
by a polygon side occurrence. -/
def polygonSideRawSymbolTarget
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) : BuserSarnakProjectiveReductionRange p :=
  S.schreierData.toFiniteQuotientSchreierData.transition
    (S.polygonSideRawSymbol q s).1 (S.polygonSideRawSymbol q s).2

/-- The raw symbol points along a forward boundary side, except for the two
inverse `a` and `c` occurrences where it points opposite the traversal. -/
theorem polygonSideRawSymbol_source_eq_boundaryEndpoint
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) :
    (S.polygonSideRawSymbol q s).1 =
      match s with
      | .cInv | .aInv => S.polygonSideEnd q s
      | _ => S.polygonSideStart q s := by
  cases s <;> rfl

/-- The terminal endpoint of a raw symbol is the other boundary endpoint of
the side occurrence. -/
theorem polygonSideRawSymbolTarget_eq_otherBoundaryEndpoint
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) :
    S.polygonSideRawSymbolTarget q s =
      match s with
      | .cInv | .aInv => S.polygonSideStart q s
      | _ => S.polygonSideEnd q s := by
  cases s
  · rfl
  · rfl
  · exact S.schreierData.toFiniteQuotientSchreierData.transition_after_inverseTransition
      (S.polygonAfterE1 q) .c
  · rfl
  · exact S.schreierData.toFiniteQuotientSchreierData.transition_after_inverseTransition
      (S.polygonAfterE2 q) .a
  · rfl
  · rfl
  · simp only [polygonSideRawSymbolTarget, polygonSideRawSymbol,
      polygonSideEnd, polygonSideMove, polygonSideStart]

end BuserSarnakProjectiveQuotientSectionData

/-- The positive boundary dart carrying the raw tree symbol `z`. -/
def canonicalProjectivePolygonTreeSourceDart
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    CanonicalProjectivePolygonDart p :=
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  let s := z.1.2.positivePolygonSide
  (S.polygonSideBase z.1.1 s, s)

/-- The paired boundary dart which begins at the target of the tree edge
underlying `z`. -/
def canonicalProjectivePolygonTreeTargetDart
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    CanonicalProjectivePolygonDart p :=
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  S.polygonSidePartner
    (canonicalProjectivePolygonTreeSourceDart z).1
    (canonicalProjectivePolygonTreeSourceDart z).2

/-- A local polygon dart is one of the two carrier occurrences of a given
canonical tree edge. -/
def IsCanonicalProjectivePolygonTreeCarrier
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p)
    (d : CanonicalProjectivePolygonDart p) : Prop :=
  d = canonicalProjectivePolygonTreeSourceDart z ∨
    d = canonicalProjectivePolygonTreeTargetDart z

private theorem canonicalProjectivePolygonTreeSourceDart_side
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    (canonicalProjectivePolygonTreeSourceDart z).2 = z.1.2.positivePolygonSide :=
  rfl

/-- The source carrier has exactly the raw Schreier label of its tree edge. -/
theorem canonicalProjectivePolygonTreeSourceDart_rawSymbol
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
      (canonicalProjectivePolygonTreeSourceDart z).1
      (canonicalProjectivePolygonTreeSourceDart z).2 = z.1 := by
  simpa [canonicalProjectivePolygonTreeSourceDart] using
    polygonSideRawSymbol_polygonSideBase_positive
      (canonicalBuserSarnakProjectiveQuotientSectionData p) z.1.1 z.1.2

/-- The source carrier begins at the source state of its tree edge. -/
theorem polygonSideStart_canonicalProjectivePolygonTreeSourceDart
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart
      (canonicalProjectivePolygonTreeSourceDart z).1
      (canonicalProjectivePolygonTreeSourceDart z).2 = z.1.1 := by
  simp [canonicalProjectivePolygonTreeSourceDart,
    BuserSarnakProjectiveQuotientSectionData.polygonSideStart_base]

/-- The source carrier ends at the target state of its tree edge. -/
theorem polygonSideEnd_canonicalProjectivePolygonTreeSourceDart
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideEnd
      (canonicalProjectivePolygonTreeSourceDart z).1
      (canonicalProjectivePolygonTreeSourceDart z).2 =
      (canonicalBuserSarnakProjectiveDegenerateTarget p z).1 := by
  change (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideMove
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart
        (canonicalProjectivePolygonTreeSourceDart z).1
        (canonicalProjectivePolygonTreeSourceDart z).2)
      (canonicalProjectivePolygonTreeSourceDart z).2 = _
  rw [polygonSideStart_canonicalProjectivePolygonTreeSourceDart]
  change (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideMove
      z.1.1 z.1.2.positivePolygonSide =
      (CanonicalProjectiveTreeSchreierData p).transition z.1.1 z.1.2
  cases z.1.2 <;> rfl

/-- The target carrier is the polygon-side partner of the source carrier. -/
theorem canonicalProjectivePolygonTreeTargetDart_eq_partner
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    canonicalProjectivePolygonTreeTargetDart z =
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
        (canonicalProjectivePolygonTreeSourceDart z).1
        (canonicalProjectivePolygonTreeSourceDart z).2 :=
  rfl

/-- The target carrier begins at the target of its canonical tree edge. -/
theorem polygonSideStart_canonicalProjectivePolygonTreeTargetDart
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart
      (canonicalProjectivePolygonTreeTargetDart z).1
      (canonicalProjectivePolygonTreeTargetDart z).2 =
      (canonicalBuserSarnakProjectiveDegenerateTarget p z).1 := by
  rw [canonicalProjectivePolygonTreeTargetDart_eq_partner,
    BuserSarnakProjectiveQuotientSectionData.polygonSidePartner_start,
    polygonSideEnd_canonicalProjectivePolygonTreeSourceDart]

/-- Along a canonical tree edge, the source carrier starts at strictly smaller
canonical word height than the target carrier. -/
theorem canonicalProjectiveWordHeight_sourceCarrier_lt_targetCarrier
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    canonicalProjectiveWordHeight p
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart
          (canonicalProjectivePolygonTreeSourceDart z).1
          (canonicalProjectivePolygonTreeSourceDart z).2) <
      canonicalProjectiveWordHeight p
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart
          (canonicalProjectivePolygonTreeTargetDart z).1
          (canonicalProjectivePolygonTreeTargetDart z).2) := by
  rw [polygonSideStart_canonicalProjectivePolygonTreeSourceDart,
    polygonSideStart_canonicalProjectivePolygonTreeTargetDart]
  exact canonicalProjectiveWordHeight_lt_transition_of_isDegenerate z.2

/-- The two carrier darts of a canonical tree edge begin at distinct primal
vertices. -/
theorem polygonSideStart_treeSourceDart_ne_treeTargetDart
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart
        (canonicalProjectivePolygonTreeSourceDart z).1
        (canonicalProjectivePolygonTreeSourceDart z).2 ≠
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart
        (canonicalProjectivePolygonTreeTargetDart z).1
        (canonicalProjectivePolygonTreeTargetDart z).2 := by
  intro h
  have hlt := canonicalProjectiveWordHeight_sourceCarrier_lt_targetCarrier z
  rw [h] at hlt
  exact (Nat.lt_irrefl _) hlt

/-- Pairing the target carrier recovers the source carrier. -/
theorem polygonSidePartner_canonicalProjectivePolygonTreeTargetDart
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
      (canonicalProjectivePolygonTreeTargetDart z).1
      (canonicalProjectivePolygonTreeTargetDart z).2 =
      canonicalProjectivePolygonTreeSourceDart z := by
  rw [canonicalProjectivePolygonTreeTargetDart_eq_partner]
  exact BuserSarnakProjectiveQuotientSectionData.polygonSidePartner_involutive
    (canonicalBuserSarnakProjectiveQuotientSectionData p)
    (canonicalProjectivePolygonTreeSourceDart z).1
    (canonicalProjectivePolygonTreeSourceDart z).2

/-- The paired carrier preserves a non-cone raw label, while a cone carrier
uses the raw symbol at the opposite endpoint of its involution orbit. -/
theorem canonicalProjectivePolygonTreeTargetDart_rawSymbol
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
      (canonicalProjectivePolygonTreeTargetDart z).1
      (canonicalProjectivePolygonTreeTargetDart z).2 =
      match z.1.2 with
      | .a | .c => z.1
      | .e1 | .e2 | .e3 | .e4 =>
          ((canonicalBuserSarnakProjectiveDegenerateTarget p z).1, z.1.2) := by
  rw [canonicalProjectivePolygonTreeTargetDart_eq_partner]
  have h := BuserSarnakProjectiveQuotientSectionData.polygonSideRawSymbol_partner
    (canonicalBuserSarnakProjectiveQuotientSectionData p)
    (canonicalProjectivePolygonTreeSourceDart z).1
    (canonicalProjectivePolygonTreeSourceDart z).2
  rw [canonicalProjectivePolygonTreeSourceDart_rawSymbol] at h
  rcases z with ⟨⟨r, x⟩, hz⟩
  cases x <;>
    simpa only [canonicalProjectivePolygonTreeSourceDart_side,
      ProjectiveOctagonGenerator.positivePolygonSide,
      canonicalBuserSarnakProjectiveDegenerateTarget] using h

/-- A carrier is incident to the source or target of the tree edge it
represents. -/
theorem polygonSideStart_of_isCanonicalProjectivePolygonTreeCarrier
    {p : ℕ} [NeZero p]
    {z : CanonicalBuserSarnakProjectiveDegenerateSymbol p}
    {d : CanonicalProjectivePolygonDart p}
    (hd : IsCanonicalProjectivePolygonTreeCarrier z d) :
    (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart d.1 d.2 =
        z.1.1 ∨
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart d.1 d.2 =
        (canonicalBuserSarnakProjectiveDegenerateTarget p z).1 := by
  rcases hd with hsource | htarget
  · left
    rw [hsource]
    exact polygonSideStart_canonicalProjectivePolygonTreeSourceDart z
  · right
    rw [htarget]
    exact polygonSideStart_canonicalProjectivePolygonTreeTargetDart z

/-- A polygon dart is determined by its side and the primal vertex at which
that side starts. -/
theorem canonicalProjectivePolygonDart_eq_of_side_start_eq
    {p : ℕ} [NeZero p]
    {q q' : BuserSarnakProjectiveReductionRange p}
    {s s' : ProjectivePolygonSide}
    (hside : s = s')
    (hstart :
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart q s =
        (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart q' s') :
    (q, s) = (q', s') := by
  subst s'
  apply Prod.ext
  · calc
      q = (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideBase
          ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart q s) s :=
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideBase_start q s).symm
      _ = (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideBase
          ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart q' s) s := by
        rw [hstart]
      _ = q' := (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideBase_start q' s
  · rfl

/-- A dart carrying a raw symbol on a forward boundary occurrence is its
source carrier. -/
theorem canonicalProjectivePolygonDart_eq_treeSourceDart_of_side_start_eq
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide)
    (hside : s = (canonicalProjectivePolygonTreeSourceDart z).2)
    (hstart :
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart q s =
        (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart
          (canonicalProjectivePolygonTreeSourceDart z).1
          (canonicalProjectivePolygonTreeSourceDart z).2) :
    (q, s) = canonicalProjectivePolygonTreeSourceDart z :=
  canonicalProjectivePolygonDart_eq_of_side_start_eq hside hstart

/-- A dart carrying a raw symbol on an inverse boundary occurrence is its
target carrier. -/
theorem canonicalProjectivePolygonDart_eq_treeTargetDart_of_side_start_eq
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide)
    (hside : s = (canonicalProjectivePolygonTreeTargetDart z).2)
    (hstart :
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart q s =
        (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart
          (canonicalProjectivePolygonTreeTargetDart z).1
          (canonicalProjectivePolygonTreeTargetDart z).2) :
    (q, s) = canonicalProjectivePolygonTreeTargetDart z :=
  canonicalProjectivePolygonDart_eq_of_side_start_eq hside hstart

/-- Every polygon dart carrying the raw symbol of a canonical tree edge is
one of that edge's source or target carriers.  Cone sides contribute only the
source carrier; the second carrier is retained explicitly to cover the paired
physical side. -/
theorem canonicalProjectivePolygonDart_eq_treeSource_or_treeTarget_of_rawSymbol_eq
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide)
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p)
    (hraw : (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol q s =
      z.1) :
    (q, s) = canonicalProjectivePolygonTreeSourceDart z ∨
      (q, s) = canonicalProjectivePolygonTreeTargetDart z := by
  rcases z with ⟨⟨r, x⟩, hz⟩
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  cases s with
  | a =>
      have hx : x = .a := (congrArg Prod.snd hraw).symm
      subst x
      left
      apply canonicalProjectivePolygonDart_eq_treeSourceDart_of_side_start_eq
        (⟨(r, .a), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p) q .a
      · rfl
      · calc
          S.polygonSideStart q .a = r := congrArg Prod.fst hraw
          _ = S.polygonSideStart
              (canonicalProjectivePolygonTreeSourceDart
                (⟨(r, .a), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p)).1
              (canonicalProjectivePolygonTreeSourceDart
                (⟨(r, .a), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p)).2 :=
            (polygonSideStart_canonicalProjectivePolygonTreeSourceDart
              (⟨(r, .a), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p)).symm
  | e1 =>
      have hx : x = .e1 := (congrArg Prod.snd hraw).symm
      subst x
      left
      apply canonicalProjectivePolygonDart_eq_treeSourceDart_of_side_start_eq
        (⟨(r, .e1), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p) q .e1
      · rfl
      · calc
          S.polygonSideStart q .e1 = r := congrArg Prod.fst hraw
          _ = S.polygonSideStart
              (canonicalProjectivePolygonTreeSourceDart
                (⟨(r, .e1), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p)).1
              (canonicalProjectivePolygonTreeSourceDart
                (⟨(r, .e1), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p)).2 :=
            (polygonSideStart_canonicalProjectivePolygonTreeSourceDart
              (⟨(r, .e1), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p)).symm
  | cInv =>
      have hx : x = .c := (congrArg Prod.snd hraw).symm
      subst x
      right
      apply canonicalProjectivePolygonDart_eq_treeTargetDart_of_side_start_eq
        (⟨(r, .c), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p) q .cInv
      · rfl
      · have htarget : S.polygonSideRawSymbolTarget q .cInv =
            S.schreierData.toFiniteQuotientSchreierData.transition r .c := by
            simp only [BuserSarnakProjectiveQuotientSectionData.polygonSideRawSymbolTarget]
            rw [hraw]
        calc
          S.polygonSideStart q .cInv = S.polygonSideRawSymbolTarget q .cInv := by
            symm
            exact S.polygonSideRawSymbolTarget_eq_otherBoundaryEndpoint q .cInv
          _ = (canonicalBuserSarnakProjectiveDegenerateTarget p
                (⟨(r, .c), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p)).1 := by
            exact htarget
          _ = S.polygonSideStart
              (canonicalProjectivePolygonTreeTargetDart
                (⟨(r, .c), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p)).1
              (canonicalProjectivePolygonTreeTargetDart
                (⟨(r, .c), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p)).2 :=
            (polygonSideStart_canonicalProjectivePolygonTreeTargetDart
              (⟨(r, .c), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p)).symm
  | e2 =>
      have hx : x = .e2 := (congrArg Prod.snd hraw).symm
      subst x
      left
      apply canonicalProjectivePolygonDart_eq_treeSourceDart_of_side_start_eq
        (⟨(r, .e2), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p) q .e2
      · rfl
      · calc
          S.polygonSideStart q .e2 = r := congrArg Prod.fst hraw
          _ = S.polygonSideStart
              (canonicalProjectivePolygonTreeSourceDart
                (⟨(r, .e2), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p)).1
              (canonicalProjectivePolygonTreeSourceDart
                (⟨(r, .e2), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p)).2 :=
            (polygonSideStart_canonicalProjectivePolygonTreeSourceDart
              (⟨(r, .e2), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p)).symm
  | aInv =>
      have hx : x = .a := (congrArg Prod.snd hraw).symm
      subst x
      right
      apply canonicalProjectivePolygonDart_eq_treeTargetDart_of_side_start_eq
        (⟨(r, .a), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p) q .aInv
      · rfl
      · have htarget : S.polygonSideRawSymbolTarget q .aInv =
            S.schreierData.toFiniteQuotientSchreierData.transition r .a := by
            simp only [BuserSarnakProjectiveQuotientSectionData.polygonSideRawSymbolTarget]
            rw [hraw]
        calc
          S.polygonSideStart q .aInv = S.polygonSideRawSymbolTarget q .aInv := by
            symm
            exact S.polygonSideRawSymbolTarget_eq_otherBoundaryEndpoint q .aInv
          _ = (canonicalBuserSarnakProjectiveDegenerateTarget p
                (⟨(r, .a), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p)).1 := by
            exact htarget
          _ = S.polygonSideStart
              (canonicalProjectivePolygonTreeTargetDart
                (⟨(r, .a), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p)).1
              (canonicalProjectivePolygonTreeTargetDart
                (⟨(r, .a), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p)).2 :=
            (polygonSideStart_canonicalProjectivePolygonTreeTargetDart
              (⟨(r, .a), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p)).symm
  | e3 =>
      have hx : x = .e3 := (congrArg Prod.snd hraw).symm
      subst x
      left
      apply canonicalProjectivePolygonDart_eq_treeSourceDart_of_side_start_eq
        (⟨(r, .e3), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p) q .e3
      · rfl
      · calc
          S.polygonSideStart q .e3 = r := congrArg Prod.fst hraw
          _ = S.polygonSideStart
              (canonicalProjectivePolygonTreeSourceDart
                (⟨(r, .e3), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p)).1
              (canonicalProjectivePolygonTreeSourceDart
                (⟨(r, .e3), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p)).2 :=
            (polygonSideStart_canonicalProjectivePolygonTreeSourceDart
              (⟨(r, .e3), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p)).symm
  | c =>
      have hx : x = .c := (congrArg Prod.snd hraw).symm
      subst x
      left
      apply canonicalProjectivePolygonDart_eq_treeSourceDart_of_side_start_eq
        (⟨(r, .c), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p) q .c
      · rfl
      · calc
          S.polygonSideStart q .c = r := congrArg Prod.fst hraw
          _ = S.polygonSideStart
              (canonicalProjectivePolygonTreeSourceDart
                (⟨(r, .c), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p)).1
              (canonicalProjectivePolygonTreeSourceDart
                (⟨(r, .c), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p)).2 :=
            (polygonSideStart_canonicalProjectivePolygonTreeSourceDart
              (⟨(r, .c), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p)).symm
  | e4 =>
      have hx : x = .e4 := (congrArg Prod.snd hraw).symm
      subst x
      left
      apply canonicalProjectivePolygonDart_eq_treeSourceDart_of_side_start_eq
        (⟨(r, .e4), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p) q .e4
      · rfl
      · calc
          S.polygonSideStart q .e4 = r := congrArg Prod.fst hraw
          _ = S.polygonSideStart
              (canonicalProjectivePolygonTreeSourceDart
                (⟨(r, .e4), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p)).1
              (canonicalProjectivePolygonTreeSourceDart
                (⟨(r, .e4), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p)).2 :=
            (polygonSideStart_canonicalProjectivePolygonTreeSourceDart
              (⟨(r, .e4), hz⟩ : CanonicalBuserSarnakProjectiveDegenerateSymbol p)).symm

/-- A raw-label equality packages the dart as one of the two physical
carriers of the corresponding tree edge. -/
theorem isCanonicalProjectivePolygonTreeCarrier_of_rawSymbol_eq
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide)
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p)
    (hraw : (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol q s =
      z.1) :
    IsCanonicalProjectivePolygonTreeCarrier z (q, s) :=
  canonicalProjectivePolygonDart_eq_treeSource_or_treeTarget_of_rawSymbol_eq q s z hraw

/-- At the target state of a tree edge, a dart carrying that edge's raw
symbol is necessarily its unique target carrier. -/
theorem canonicalProjectivePolygonDart_eq_treeTargetDart_of_rawSymbol_eq_of_start_eq_target
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide)
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p)
    (hraw : (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol q s =
      z.1)
    (hstart :
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart q s =
        (canonicalBuserSarnakProjectiveDegenerateTarget p z).1) :
    (q, s) = canonicalProjectivePolygonTreeTargetDart z := by
  rcases canonicalProjectivePolygonDart_eq_treeSource_or_treeTarget_of_rawSymbol_eq
    q s z hraw with hsource | htarget
  · exfalso
    apply polygonSideStart_treeSourceDart_ne_treeTargetDart z
    calc
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart
          (canonicalProjectivePolygonTreeSourceDart z).1
          (canonicalProjectivePolygonTreeSourceDart z).2 =
        (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart q s := by
          exact (congrArg
            (fun d : CanonicalProjectivePolygonDart p =>
              (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart d.1 d.2)
            hsource).symm
      _ = (canonicalBuserSarnakProjectiveDegenerateTarget p z).1 := hstart
      _ = (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart
          (canonicalProjectivePolygonTreeTargetDart z).1
          (canonicalProjectivePolygonTreeTargetDart z).2 :=
        (polygonSideStart_canonicalProjectivePolygonTreeTargetDart z).symm
  · exact htarget

/-- If the paired side carries a tree edge and this side starts at that edge's
target, then this side is the edge's unique target carrier. -/
theorem canonicalProjectivePolygonDart_eq_treeTargetDart_of_partnerRawSymbol_eq_of_start_eq_target
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide)
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p)
    (hraw : (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2 = z.1)
    (hstart :
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart q s =
        (canonicalBuserSarnakProjectiveDegenerateTarget p z).1) :
    (q, s) = canonicalProjectivePolygonTreeTargetDart z := by
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  have hcarrier : IsCanonicalProjectivePolygonTreeCarrier z
      (S.polygonSidePartner q s) :=
    isCanonicalProjectivePolygonTreeCarrier_of_rawSymbol_eq
      (S.polygonSidePartner q s).1 (S.polygonSidePartner q s).2 z hraw
  rcases hcarrier with hsource | htarget
  · calc
      (q, s) = S.polygonSidePartner (S.polygonSidePartner q s).1
          (S.polygonSidePartner q s).2 := (S.polygonSidePartner_involutive q s).symm
      _ = S.polygonSidePartner (canonicalProjectivePolygonTreeSourceDart z).1
          (canonicalProjectivePolygonTreeSourceDart z).2 := by rw [hsource]
      _ = canonicalProjectivePolygonTreeTargetDart z :=
        (canonicalProjectivePolygonTreeTargetDart_eq_partner z).symm
  · exfalso
    have hdsource : (q, s) = canonicalProjectivePolygonTreeSourceDart z := by
      calc
        (q, s) = S.polygonSidePartner (S.polygonSidePartner q s).1
            (S.polygonSidePartner q s).2 := (S.polygonSidePartner_involutive q s).symm
        _ = S.polygonSidePartner (canonicalProjectivePolygonTreeTargetDart z).1
            (canonicalProjectivePolygonTreeTargetDart z).2 := by rw [htarget]
        _ = canonicalProjectivePolygonTreeSourceDart z :=
          polygonSidePartner_canonicalProjectivePolygonTreeTargetDart z
    apply polygonSideStart_treeSourceDart_ne_treeTargetDart z
    calc
      S.polygonSideStart (canonicalProjectivePolygonTreeSourceDart z).1
          (canonicalProjectivePolygonTreeSourceDart z).2 = S.polygonSideStart q s := by
            have hq : q = (canonicalProjectivePolygonTreeSourceDart z).1 := by
              simpa using congrArg Prod.fst hdsource
            have hs : s = (canonicalProjectivePolygonTreeSourceDart z).2 := by
              simpa using congrArg Prod.snd hdsource
            rw [hq, hs]
      _ = (canonicalBuserSarnakProjectiveDegenerateTarget p z).1 := hstart
      _ = S.polygonSideStart (canonicalProjectivePolygonTreeTargetDart z).1
          (canonicalProjectivePolygonTreeTargetDart z).2 :=
        (polygonSideStart_canonicalProjectivePolygonTreeTargetDart z).symm

/-- Tree target carriers are unique, because canonical tree edges have
distinct target states. -/
theorem canonicalProjectivePolygonTreeTargetDart_injective
    {p : ℕ} [NeZero p] :
    Function.Injective (@canonicalProjectivePolygonTreeTargetDart p _) := by
  intro z w hzw
  apply canonicalBuserSarnakProjectiveDegenerateTarget_injective p
  apply Subtype.ext
  have hstart := congrArg
    (fun d : CanonicalProjectivePolygonDart p =>
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart d.1 d.2)
    hzw
  rw [polygonSideStart_canonicalProjectivePolygonTreeTargetDart,
    polygonSideStart_canonicalProjectivePolygonTreeTargetDart] at hstart
  exact hstart

/-- Equality of target-carrier starts already identifies the underlying
canonical tree edge. -/
theorem canonicalProjectivePolygonTreeTargetDart_eq_of_start_eq
    {p : ℕ} [NeZero p]
    (z w : CanonicalBuserSarnakProjectiveDegenerateSymbol p)
    (hstart :
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart
        (canonicalProjectivePolygonTreeTargetDart z).1
        (canonicalProjectivePolygonTreeTargetDart z).2 =
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart
        (canonicalProjectivePolygonTreeTargetDart w).1
        (canonicalProjectivePolygonTreeTargetDart w).2) :
    z = w := by
  apply canonicalBuserSarnakProjectiveDegenerateTarget_injective p
  apply Subtype.ext
  rw [polygonSideStart_canonicalProjectivePolygonTreeTargetDart,
    polygonSideStart_canonicalProjectivePolygonTreeTargetDart] at hstart
  exact hstart

end

end SystolicGrowth
