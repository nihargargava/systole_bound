module

public import BuserSarnak.BuserSarnakProjectivePolygonRelators

@[expose] public section

/-!
# Side pairing for projective polygon lifts

The polygon relators are the faces of the finite projective cover.  This file
makes their eight directed side occurrences and their reverse pairings
explicit.  The involutive pairing is the combinatorial datum from which the
remaining dual-graph Tietze eliminations will be selected.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

noncomputable local instance buserSarnakProjectivePolygonPairingRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

/-- The eight directed sides of the projective octagon polygon relation. -/
inductive ProjectivePolygonSide where
  | a | e1 | cInv | e2 | aInv | e3 | c | e4
  deriving DecidableEq

/-- Exhaustive finite enumeration of the eight polygon sides. -/
instance instFintypeProjectivePolygonSide : Fintype ProjectivePolygonSide :=
  Fintype.ofList [.a, .e1, .cInv, .e2, .aInv, .e3, .c, .e4] (by
    intro s
    cases s <;> simp)

@[simp] theorem card_projectivePolygonSide :
    Fintype.card ProjectivePolygonSide = 8 := by
  decide

/-- The projective generator labelling a polygon side. -/
def ProjectivePolygonSide.generator : ProjectivePolygonSide → ProjectiveOctagonGenerator
  | .a | .aInv => .a
  | .e1 => .e1
  | .cInv | .c => .c
  | .e2 => .e2
  | .e3 => .e3
  | .e4 => .e4

/-- The oppositely oriented occurrence of the same polygon side. -/
def ProjectivePolygonSide.reverse : ProjectivePolygonSide → ProjectivePolygonSide
  | .a => .aInv
  | .aInv => .a
  | .cInv => .c
  | .c => .cInv
  | .e1 => .e1
  | .e2 => .e2
  | .e3 => .e3
  | .e4 => .e4

@[simp] theorem ProjectivePolygonSide.reverse_reverse
    (s : ProjectivePolygonSide) : s.reverse.reverse = s := by
  cases s <;> rfl

@[simp] theorem ProjectivePolygonSide.generator_reverse
    (s : ProjectivePolygonSide) : s.reverse.generator = s.generator := by
  cases s <;> rfl

namespace BuserSarnakProjectiveQuotientSectionData

/-- The quotient state at which the indicated side begins in the polygon
based at `q`. -/
def polygonSideStart
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p) :
    ProjectivePolygonSide → BuserSarnakProjectiveReductionRange p
  | .a => q
  | .e1 => S.polygonAfterA q
  | .cInv => S.polygonAfterE1 q
  | .e2 => S.polygonAfterCInv q
  | .aInv => S.polygonAfterE2 q
  | .e3 => S.polygonAfterAInv q
  | .c => S.polygonAfterE3 q
  | .e4 => S.polygonAfterC q

/-- Move across the indicated directed polygon side from a specified state. -/
def polygonSideMove
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p) :
    ProjectivePolygonSide → BuserSarnakProjectiveReductionRange p
  | .a => S.schreierData.toFiniteQuotientSchreierData.transition q .a
  | .e1 => S.schreierData.toFiniteQuotientSchreierData.transition q .e1
  | .cInv => S.schreierData.toFiniteQuotientSchreierData.inverseTransition q .c
  | .e2 => S.schreierData.toFiniteQuotientSchreierData.transition q .e2
  | .aInv => S.schreierData.toFiniteQuotientSchreierData.inverseTransition q .a
  | .e3 => S.schreierData.toFiniteQuotientSchreierData.transition q .e3
  | .c => S.schreierData.toFiniteQuotientSchreierData.transition q .c
  | .e4 => S.schreierData.toFiniteQuotientSchreierData.transition q .e4

/-- The quotient state at which the indicated side ends. -/
def polygonSideEnd
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) : BuserSarnakProjectiveReductionRange p :=
  S.polygonSideMove (S.polygonSideStart q s) s

/-- Recover the base face from a side and the state at which that side starts. -/
def polygonSideBase
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p) :
    ProjectivePolygonSide → BuserSarnakProjectiveReductionRange p
  | .a => q
  | .e1 => S.schreierData.toFiniteQuotientSchreierData.inverseTransition q .a
  | .cInv =>
      S.schreierData.toFiniteQuotientSchreierData.inverseTransition
        (S.schreierData.toFiniteQuotientSchreierData.inverseTransition q .e1) .a
  | .e2 =>
      S.schreierData.toFiniteQuotientSchreierData.inverseTransition
        (S.schreierData.toFiniteQuotientSchreierData.inverseTransition
          (S.schreierData.toFiniteQuotientSchreierData.transition q .c) .e1) .a
  | .aInv =>
      S.schreierData.toFiniteQuotientSchreierData.inverseTransition
        (S.schreierData.toFiniteQuotientSchreierData.inverseTransition
          (S.schreierData.toFiniteQuotientSchreierData.transition
            (S.schreierData.toFiniteQuotientSchreierData.inverseTransition q .e2) .c) .e1) .a
  | .e3 =>
      S.schreierData.toFiniteQuotientSchreierData.inverseTransition
        (S.schreierData.toFiniteQuotientSchreierData.inverseTransition
          (S.schreierData.toFiniteQuotientSchreierData.transition
            (S.schreierData.toFiniteQuotientSchreierData.inverseTransition
              (S.schreierData.toFiniteQuotientSchreierData.transition q .a) .e2) .c) .e1) .a
  | .c =>
      S.schreierData.toFiniteQuotientSchreierData.inverseTransition
        (S.schreierData.toFiniteQuotientSchreierData.inverseTransition
          (S.schreierData.toFiniteQuotientSchreierData.transition
            (S.schreierData.toFiniteQuotientSchreierData.inverseTransition
              (S.schreierData.toFiniteQuotientSchreierData.transition
                (S.schreierData.toFiniteQuotientSchreierData.inverseTransition q .e3) .a) .e2) .c) .e1) .a
  | .e4 =>
      S.schreierData.toFiniteQuotientSchreierData.inverseTransition
        (S.schreierData.toFiniteQuotientSchreierData.inverseTransition
          (S.schreierData.toFiniteQuotientSchreierData.transition
            (S.schreierData.toFiniteQuotientSchreierData.inverseTransition
              (S.schreierData.toFiniteQuotientSchreierData.transition
                (S.schreierData.toFiniteQuotientSchreierData.inverseTransition
                  (S.schreierData.toFiniteQuotientSchreierData.inverseTransition q .c) .e3) .a) .e2) .c) .e1) .a

/-- Crossing a side and then its reverse returns to the original state. -/
theorem polygonSideMove_reverse
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) :
    S.polygonSideMove (S.polygonSideMove q s) s.reverse = q := by
  cases s
  · exact S.schreierData.toFiniteQuotientSchreierData.inverseTransition_after_transition q .a
  · exact S.cone_transition_twice q .e1
  · exact S.schreierData.toFiniteQuotientSchreierData.transition_after_inverseTransition q .c
  · exact S.cone_transition_twice q .e2
  · exact S.schreierData.toFiniteQuotientSchreierData.transition_after_inverseTransition q .a
  · exact S.cone_transition_twice q .e3
  · exact S.schreierData.toFiniteQuotientSchreierData.inverseTransition_after_transition q .c
  · exact S.cone_transition_twice q .e4

/-- Recovering the base of a polygon side from its actual start state returns
the original face. -/
theorem polygonSideBase_start
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) :
    S.polygonSideBase (S.polygonSideStart q s) s = q := by
  cases s <;>
    simp [polygonSideBase, polygonSideStart, polygonAfterA, polygonAfterE1,
      polygonAfterCInv, polygonAfterE2, polygonAfterAInv, polygonAfterE3,
      polygonAfterC]

/-- Starting the indicated side from its recovered base returns the supplied
side-start state. -/
theorem polygonSideStart_base
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) :
    S.polygonSideStart (S.polygonSideBase q s) s = q := by
  cases s <;>
    simp [polygonSideBase, polygonSideStart, polygonAfterA, polygonAfterE1,
      polygonAfterCInv, polygonAfterE2, polygonAfterAInv, polygonAfterE3,
      polygonAfterC]

/-- The paired occurrence of a directed side: it starts where the original
side ends and has the reverse orientation. -/
def polygonSidePartner
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) :
    BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide :=
  (S.polygonSideBase (S.polygonSideEnd q s) s.reverse, s.reverse)

/-- The paired side starts precisely at the endpoint of the original side. -/
theorem polygonSidePartner_start
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) :
    S.polygonSideStart (S.polygonSidePartner q s).1
      (S.polygonSidePartner q s).2 = S.polygonSideEnd q s := by
  simp [polygonSidePartner, polygonSideStart_base]

/-- The paired side ends precisely at the start of the original side. -/
theorem polygonSidePartner_end
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) :
    S.polygonSideEnd (S.polygonSidePartner q s).1
      (S.polygonSidePartner q s).2 = S.polygonSideStart q s := by
  rw [polygonSideEnd]
  rw [S.polygonSidePartner_start q s]
  exact S.polygonSideMove_reverse (S.polygonSideStart q s) s

/-- Pairing polygon-side occurrences is an involution. -/
theorem polygonSidePartner_involutive
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) :
    S.polygonSidePartner (S.polygonSidePartner q s).1
      (S.polygonSidePartner q s).2 = (q, s) := by
  have hend := S.polygonSidePartner_end q s
  change
    (S.polygonSideBase
      (S.polygonSideEnd (S.polygonSidePartner q s).1
        (S.polygonSidePartner q s).2)
      (S.polygonSidePartner q s).2.reverse,
      (S.polygonSidePartner q s).2.reverse) = (q, s)
  rw [hend]
  simp [polygonSidePartner, S.polygonSideBase_start q s]

end BuserSarnakProjectiveQuotientSectionData

end

end SystolicGrowth
