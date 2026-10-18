module

public import BuserSarnak.BuserSarnakProjectivePostConePolygonTargetFactors
public import BuserSarnak.BuserSarnakProjectivePolygonTreeCarriers

@[expose] public section

/-!
# Physical carriers of post-cone boundary terms

This module begins the converse to the endpoint factorization: a nontrivial
polygon boundary term must be carried by a retained physical edge. The
nondegenerate cone case is the delicate part because the lower cone symbol is
eliminated in favour of its upper partner.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

noncomputable local instance buserSarnakProjectivePostConeBoundaryCarriersRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

noncomputable local instance buserSarnakProjectivePostConeBoundaryCarriersDegenerateDecidable
    {p : ℕ} [NeZero p] :
    DecidablePred (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol :=
  Classical.decPred _

noncomputable local instance buserSarnakProjectivePostConeBoundaryCarriersEliminationDecidable
    {p : ℕ} [NeZero p] :
    DecidablePred (@isCanonicalProjectiveConeEliminationSymbol p _) :=
  Classical.decPred _

/-- A nonzero boundary term is carried either by the positive source
occurrence or by the inverse target occurrence of one retained physical edge. -/
def CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrier
    (p : ℕ) [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) : Prop :=
  ∃ z : CanonicalProjectiveConeKeptSymbol p,
    ((⟨q⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeSource z ∧
      s = projectivePolygonPostConeEdgeSide z ∧
      canonicalProjectiveConePostConeBoundaryTerm p q s = FreeGroup.of z) ∨
    ((⟨q⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeTarget z ∧
      s = projectivePolygonPostConeEdgeTargetSide z ∧
      canonicalProjectiveConePostConeBoundaryTerm p q s = (FreeGroup.of z)⁻¹)

/-- A fixed boundary occurrence has at most one retained physical carrier.
This records the literal-generator uniqueness needed when transporting raw
source/target classifications across a paired side. -/
theorem canonicalProjectiveConePostConeBoundaryTermPhysicalCarrier_witness_unique
    {p : ℕ} [NeZero p]
    {q : BuserSarnakProjectiveReductionRange p} {s : ProjectivePolygonSide}
    {z z' : CanonicalProjectiveConeKeptSymbol p}
    (hz :
      ((⟨q⟩ : ProjectivePolygonPostConeFace p) =
          projectivePolygonPostConeEdgeSource z ∧
        s = projectivePolygonPostConeEdgeSide z ∧
        canonicalProjectiveConePostConeBoundaryTerm p q s = FreeGroup.of z) ∨
      ((⟨q⟩ : ProjectivePolygonPostConeFace p) =
          projectivePolygonPostConeEdgeTarget z ∧
        s = projectivePolygonPostConeEdgeTargetSide z ∧
        canonicalProjectiveConePostConeBoundaryTerm p q s = (FreeGroup.of z)⁻¹))
    (hz' :
      ((⟨q⟩ : ProjectivePolygonPostConeFace p) =
          projectivePolygonPostConeEdgeSource z' ∧
        s = projectivePolygonPostConeEdgeSide z' ∧
        canonicalProjectiveConePostConeBoundaryTerm p q s = FreeGroup.of z') ∨
      ((⟨q⟩ : ProjectivePolygonPostConeFace p) =
          projectivePolygonPostConeEdgeTarget z' ∧
        s = projectivePolygonPostConeEdgeTargetSide z' ∧
        canonicalProjectiveConePostConeBoundaryTerm p q s = (FreeGroup.of z')⁻¹)) :
    z = z' := by
  classical
  rcases hz with hz | hz <;> rcases hz' with hz' | hz'
  · exact FreeGroup.of_injective (hz.2.2.symm.trans hz'.2.2)
  · exfalso
    have h := congrArg FreeGroup.toWord (hz.2.2.symm.trans hz'.2.2)
    simpa [FreeGroup.toWord_of, FreeGroup.toWord_inv, FreeGroup.invRev] using h
  · exfalso
    have h := congrArg FreeGroup.toWord (hz.2.2.symm.trans hz'.2.2)
    simpa [FreeGroup.toWord_of, FreeGroup.toWord_inv, FreeGroup.invRev] using h
  · apply FreeGroup.of_injective
    simpa using congrArg Inv.inv (hz.2.2.symm.trans hz'.2.2)

/-- Pairing a boundary occurrence transports its physical carrier to the
oppositely oriented occurrence of the same retained edge. -/
theorem canonicalProjectiveConePostConeBoundaryTermPhysicalCarrier_partner
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide)
    (h : CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrier p q s) :
    CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrier p
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2 := by
  classical
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  rcases h with ⟨z, hsource | htarget⟩
  · refine ⟨z, Or.inr ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · change (⟨(S.polygonSidePartner q s).1⟩ : ProjectivePolygonPostConeFace p) =
        (⟨(S.polygonSidePartner
          (projectivePolygonPostConeEdgeSource z).state
          (projectivePolygonPostConeEdgeSide z)).1⟩ : ProjectivePolygonPostConeFace p)
      rw [show q = (projectivePolygonPostConeEdgeSource z).state by
        exact congrArg ProjectivePolygonPostConeFace.state hsource.1]
      rw [show s = projectivePolygonPostConeEdgeSide z by exact hsource.2.1]
    · change (S.polygonSidePartner q s).2 =
        projectivePolygonPostConeEdgeTargetSide z
      rw [show q = (projectivePolygonPostConeEdgeSource z).state by
        exact congrArg ProjectivePolygonPostConeFace.state hsource.1]
      rw [show s = projectivePolygonPostConeEdgeSide z by exact hsource.2.1]
      rfl
    · have hpair : S.polygonSidePartner q s =
          ((projectivePolygonPostConeEdgeTarget z).state,
            projectivePolygonPostConeEdgeTargetSide z) := by
        rw [show q = (projectivePolygonPostConeEdgeSource z).state by
          exact congrArg ProjectivePolygonPostConeFace.state hsource.1]
        rw [show s = projectivePolygonPostConeEdgeSide z by exact hsource.2.1]
        rfl
      rw [hpair]
      exact canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 z
  · refine ⟨z, Or.inl ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · change (⟨(S.polygonSidePartner q s).1⟩ : ProjectivePolygonPostConeFace p) =
        (⟨(projectivePolygonPostConeEdgeSource z).state⟩ : ProjectivePolygonPostConeFace p)
      have hq : q = (projectivePolygonPostConeEdgeTarget z).state :=
        congrArg ProjectivePolygonPostConeFace.state htarget.1
      have hs : s = projectivePolygonPostConeEdgeTargetSide z := htarget.2.1
      rw [hq, hs]
      simp only [projectivePolygonPostConeEdgeTarget,
        projectivePolygonPostConeEdgeTargetSide]
      have hinv := S.polygonSidePartner_involutive
        (projectivePolygonPostConeEdgeSource z).state
        (projectivePolygonPostConeEdgeSide z)
      apply congrArg ProjectivePolygonPostConeFace.mk
      exact congrArg Prod.fst hinv
    · change (S.polygonSidePartner q s).2 =
        projectivePolygonPostConeEdgeSide z
      have hq : q = (projectivePolygonPostConeEdgeTarget z).state :=
        congrArg ProjectivePolygonPostConeFace.state htarget.1
      have hs : s = projectivePolygonPostConeEdgeTargetSide z := htarget.2.1
      rw [hq, hs]
      simp only [projectivePolygonPostConeEdgeTarget,
        projectivePolygonPostConeEdgeTargetSide]
      have hinv := S.polygonSidePartner_involutive
        (projectivePolygonPostConeEdgeSource z).state
        (projectivePolygonPostConeEdgeSide z)
      exact congrArg Prod.snd hinv
    · have hq : q = (projectivePolygonPostConeEdgeTarget z).state :=
          congrArg ProjectivePolygonPostConeFace.state htarget.1
      have hs : s = projectivePolygonPostConeEdgeTargetSide z := htarget.2.1
      have hpair : S.polygonSidePartner q s =
          ((projectivePolygonPostConeEdgeSource z).state,
            projectivePolygonPostConeEdgeSide z) := by
        rw [hq, hs]
        simp only [projectivePolygonPostConeEdgeTarget,
          projectivePolygonPostConeEdgeTargetSide]
        exact S.polygonSidePartner_involutive _ _
      rw [hpair]
      exact canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq z

/-- When both raw symbols in a cone pair survive the canonical Schreier tree,
the boundary term at the positive side's base face has an explicit retained
physical carrier. The two branches distinguish whether the displayed raw
symbol is the retained upper endpoint or the eliminated lower endpoint. -/
theorem canonicalProjectiveConePostConeConeBaseBoundaryTerm_edge_factor
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (e : ProjectiveOctagonConeGenerator)
    (r : BuserSarnakProjectiveReductionRange p)
    (hsource : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (r, e.lift))
    (htarget : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (buserSarnakProjectiveConePartner p e r, e.lift)) :
    let S := canonicalBuserSarnakProjectiveQuotientSectionData p
    let side := e.lift.positivePolygonSide
    let F := S.polygonSideBase r side
    ∃ z : CanonicalProjectiveConeKeptSymbol p,
      ((F, side) = ((projectivePolygonPostConeEdgeSource z).state,
        projectivePolygonPostConeEdgeSide z) ∧
        canonicalProjectiveConePostConeBoundaryTerm p F side = FreeGroup.of z) ∨
      ((F, side) = ((projectivePolygonPostConeEdgeTarget z).state,
        projectivePolygonPostConeEdgeTargetSide z) ∧
        canonicalProjectiveConePostConeBoundaryTerm p F side = (FreeGroup.of z)⁻¹) := by
  classical
  dsimp
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  let side := e.lift.positivePolygonSide
  let F := S.polygonSideBase r side
  let G := (S.polygonSidePartner F side).1
  have hside_reverse : side.reverse = side := by
    dsimp [side, ProjectiveOctagonGenerator.positivePolygonSide]
    cases e <;> rfl
  have hpartner_side : (S.polygonSidePartner F side).2 = side := by
    simp [BuserSarnakProjectiveQuotientSectionData.polygonSidePartner, hside_reverse]
  have hstartG : S.polygonSideStart G side =
      buserSarnakProjectiveConePartner p e r := by
    change S.polygonSideStart (S.polygonSidePartner F side).1 side =
      buserSarnakProjectiveConePartner p e r
    have hstart := S.polygonSidePartner_start F side
    rw [hpartner_side] at hstart
    rw [hstart]
    change S.polygonSideMove (S.polygonSideStart F side) side =
      buserSarnakProjectiveConePartner p e r
    rw [show S.polygonSideStart F side = r by
      exact S.polygonSideStart_base r side]
    cases e <;> rfl
  have hbaseG : S.polygonSideBase (buserSarnakProjectiveConePartner p e r) side = G := by
    rw [← hstartG]
    exact S.polygonSideBase_start G side
  have hback : S.polygonSidePartner G side = (F, side) := by
    change S.polygonSidePartner (S.polygonSidePartner F side).1 side = (F, side)
    have hinvolutive := S.polygonSidePartner_involutive F side
    rw [hpartner_side] at hinvolutive
    exact hinvolutive
  by_cases hlt : buserSarnakProjectiveConeRank p r <
      buserSarnakProjectiveConeRank p (buserSarnakProjectiveConePartner p e r)
  · let i : BuserSarnakProjectiveConePairIndex p := ⟨e, ⟨r, hlt⟩⟩
    have hiSource : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
        (canonicalProjectiveConePairSource i) := by
      simpa [i, canonicalProjectiveConePairSource] using hsource
    have hiTarget : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
        (canonicalProjectiveConePairTarget i) := by
      simpa [i, canonicalProjectiveConePairTarget] using htarget
    let z := canonicalProjectiveConeKeptTarget i hiSource hiTarget
    have htargetDart : (F, side) =
        ((projectivePolygonPostConeEdgeTarget z).state,
          projectivePolygonPostConeEdgeTargetSide z) := by
      apply Prod.ext
      · change F = (S.polygonSidePartner
          (S.polygonSideBase (buserSarnakProjectiveConePartner p e r) side) side).1
        rw [hbaseG]
        exact (congrArg Prod.fst hback).symm
      · change side = (S.polygonSidePartner
          (S.polygonSideBase (buserSarnakProjectiveConePartner p e r) side) side).2
        rw [hbaseG]
        exact (congrArg Prod.snd hback).symm
    refine ⟨z, Or.inr ⟨htargetDart, ?_⟩⟩
    have hterm := canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 z
    have htargetState := congrArg Prod.fst htargetDart
    have htargetSide := congrArg Prod.snd htargetDart
    change F = (projectivePolygonPostConeEdgeTarget z).state at htargetState
    change side = projectivePolygonPostConeEdgeTargetSide z at htargetSide
    change canonicalProjectiveConePostConeBoundaryTerm p
      (projectivePolygonPostConeEdgeTarget z).state
      (projectivePolygonPostConeEdgeTargetSide z) = _ at hterm
    rw [← htargetState, ← htargetSide] at hterm
    exact hterm
  · have hrank_ne : buserSarnakProjectiveConeRank p
        (buserSarnakProjectiveConePartner p e r) ≠
          buserSarnakProjectiveConeRank p r := by
      intro h
      apply buserSarnakProjectiveConePartner_ne p hp hp2 e r
      exact buserSarnakProjectiveConeRank_injective p h
    have hreverse : buserSarnakProjectiveConeRank p
        (buserSarnakProjectiveConePartner p e r) <
          buserSarnakProjectiveConeRank p r :=
      lt_of_le_of_ne (Nat.le_of_not_gt hlt) hrank_ne
    let i : BuserSarnakProjectiveConePairIndex p :=
      ⟨e, ⟨buserSarnakProjectiveConePartner p e r, by simpa using hreverse⟩⟩
    have hiSource : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
        (canonicalProjectiveConePairSource i) := by
      simpa [i, canonicalProjectiveConePairSource] using htarget
    have hiTarget : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
        (canonicalProjectiveConePairTarget i) := by
      simpa [i, canonicalProjectiveConePairTarget] using hsource
    let z := canonicalProjectiveConeKeptTarget i hiSource hiTarget
    have htargetRaw : canonicalProjectiveConePairTarget i = (r, e.lift) := by
      simp [i, canonicalProjectiveConePairTarget,
        buserSarnakProjectiveConePartner_partner]
    have hsourceDart : (F, side) =
        ((projectivePolygonPostConeEdgeSource z).state,
          projectivePolygonPostConeEdgeSide z) := by
      change (F, side) =
        (S.polygonSideBase (canonicalProjectiveConePairTarget i).1
          (canonicalProjectiveConePairTarget i).2.positivePolygonSide,
        (canonicalProjectiveConePairTarget i).2.positivePolygonSide)
      rw [htargetRaw]
    refine ⟨z, Or.inl ⟨hsourceDart, ?_⟩⟩
    have hterm := canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq z
    have hsourceState := congrArg Prod.fst hsourceDart
    have hsourceSide := congrArg Prod.snd hsourceDart
    change F = (projectivePolygonPostConeEdgeSource z).state at hsourceState
    change side = projectivePolygonPostConeEdgeSide z at hsourceSide
    rw [← hsourceState, ← hsourceSide] at hterm
    exact hterm

/-- The cone-base factorization packaged as a physical-carrier witness. -/
theorem canonicalProjectiveConePostConeConeBaseBoundaryTerm_physicalCarrier
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (e : ProjectiveOctagonConeGenerator)
    (r : BuserSarnakProjectiveReductionRange p)
    (hsource : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (r, e.lift))
    (htarget : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (buserSarnakProjectiveConePartner p e r, e.lift)) :
    let S := canonicalBuserSarnakProjectiveQuotientSectionData p
    let side := e.lift.positivePolygonSide
    let F := S.polygonSideBase r side
    CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrier p F side := by
  dsimp
  obtain ⟨z, hsourceDart | htargetDart⟩ :=
    canonicalProjectiveConePostConeConeBaseBoundaryTerm_edge_factor hp hp2 e r hsource htarget
  · refine ⟨z, Or.inl ⟨?_, ?_, hsourceDart.2⟩⟩
    · have hstate := congrArg Prod.fst hsourceDart.1
      change _ = (projectivePolygonPostConeEdgeSource z).state at hstate
      exact congrArg ProjectivePolygonPostConeFace.mk hstate
    · exact congrArg Prod.snd hsourceDart.1
  · refine ⟨z, Or.inr ⟨?_, ?_, htargetDart.2⟩⟩
    · have hstate := congrArg Prod.fst htargetDart.1
      change _ = (projectivePolygonPostConeEdgeTarget z).state at hstate
      exact congrArg ProjectivePolygonPostConeFace.mk hstate
    · exact congrArg Prod.snd htargetDart.1

/-- Every positive cone-side boundary term is trivial or has a retained
physical carrier.  The two degenerate cases collapse by the cone-pair
relation; otherwise the base-carrier theorem supplies the exact label. -/
theorem canonicalProjectiveConePostConeConeBoundaryTerm_eq_one_or_physicalCarrier
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p)
    (e : ProjectiveOctagonConeGenerator) :
    canonicalProjectiveConePostConeBoundaryTerm p q e.lift.positivePolygonSide = 1 ∨
      CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrier p q
        e.lift.positivePolygonSide := by
  classical
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  let side := e.lift.positivePolygonSide
  let r := S.polygonSideStart q side
  have hbase : S.polygonSideBase r side = q := by
    exact S.polygonSideBase_start q side
  have hraw : S.polygonSideRawSymbol q side = (r, e.lift) := by
    cases e <;> rfl
  have hterm : canonicalProjectiveConePostConeBoundaryTerm p q side =
      canonicalProjectiveConeFirstStageSubstitution p
        ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord (r, e.lift)) := by
    cases e <;>
      simp only [S, side, ProjectiveOctagonConeGenerator.lift,
        ProjectiveOctagonGenerator.positivePolygonSide] at hraw ⊢ <;>
      simp only [canonicalProjectiveConePostConeBoundaryTerm,
        canonicalProjectiveConePostConeSideWord] <;>
      rw [hraw]
  by_cases hsource : (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (r, e.lift)
  · left
    rw [hterm, (CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord_of_degenerate
      hsource, map_one]
  · by_cases htarget : (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
        (buserSarnakProjectiveConePartner p e r, e.lift)
    · left
      have htarget' : (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
          ((CanonicalProjectiveConeSchreierData p).transition r e.lift, e.lift) := by
        exact htarget
      have htarget_word :
          canonicalProjectiveConeFirstStageSubstitution p
            ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
              ((CanonicalProjectiveConeSchreierData p).transition r e.lift, e.lift)) = 1 := by
        rw [(CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord_of_degenerate
          htarget', map_one]
      have hpair := canonicalProjectiveConeFirstStageSubstitution_conePair_eq_one hp hp2 r e
      rw [map_mul] at hpair
      rw [hterm]
      calc
        canonicalProjectiveConeFirstStageSubstitution p
            ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord (r, e.lift)) =
            canonicalProjectiveConeFirstStageSubstitution p
              ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord (r, e.lift)) * 1 :=
              (mul_one _).symm
        _ = canonicalProjectiveConeFirstStageSubstitution p
              ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord (r, e.lift)) *
            canonicalProjectiveConeFirstStageSubstitution p
              ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
                ((CanonicalProjectiveConeSchreierData p).transition r e.lift, e.lift)) := by
              rw [htarget_word]
        _ = 1 := hpair
    · right
      rw [← hbase]
      exact canonicalProjectiveConePostConeConeBaseBoundaryTerm_physicalCarrier
        hp hp2 e r hsource htarget
/-- The non-cone side `a` is trivial exactly at a degenerate raw symbol and
otherwise has a positive physical carrier. -/
private theorem canonicalProjectiveConePostConeBoundaryTerm_a_eq_one_or_physicalCarrier
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) :
    canonicalProjectiveConePostConeBoundaryTerm p q .a = 1 ∨
      CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrier p q .a := by
  classical
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  by_cases hdeg : (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (S.polygonSideRawSymbol q .a)
  · left
    simp only [canonicalProjectiveConePostConeBoundaryTerm,
      canonicalProjectiveConePostConeSideWord]
    rw [(CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord_of_degenerate hdeg]
    exact map_one _
  · let raw : CanonicalProjectiveConeNondegenerateSymbol p :=
      ⟨S.polygonSideRawSymbol q .a, hdeg⟩
    have hraw_generator : raw.1.2 = .a := by
      simp [raw, BuserSarnakProjectiveQuotientSectionData.polygonSideRawSymbol]
    have hraw_kept : ¬ isCanonicalProjectiveConeEliminationSymbol raw := by
      apply canonicalProjectiveConeNoncone_not_eliminated raw
      exact Or.inl hraw_generator
    let z : CanonicalProjectiveConeKeptSymbol p := ⟨raw, hraw_kept⟩
    right
    refine ⟨z, Or.inl ⟨?_, ?_, ?_⟩⟩
    · change (⟨q⟩ : ProjectivePolygonPostConeFace p) =
        ⟨S.polygonSideBase raw.1.1 raw.1.2.positivePolygonSide⟩
      apply congrArg ProjectivePolygonPostConeFace.mk
      dsimp [raw]
      rfl
    · change .a = raw.1.2.positivePolygonSide
      dsimp [raw]
      rfl
    · simp only [canonicalProjectiveConePostConeBoundaryTerm,
        canonicalProjectiveConePostConeSideWord]
      rw [(CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord_of_not_degenerate hdeg]
      change canonicalProjectiveConeFirstStageSubstitution p (FreeGroup.of raw) = _
      rw [canonicalProjectiveConeFirstStageSubstitution_of_kept z]

/-- The non-cone side `c` is trivial exactly at a degenerate raw symbol and
otherwise has a positive physical carrier. -/
private theorem canonicalProjectiveConePostConeBoundaryTerm_c_eq_one_or_physicalCarrier
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) :
    canonicalProjectiveConePostConeBoundaryTerm p q .c = 1 ∨
      CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrier p q .c := by
  classical
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  by_cases hdeg : (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (S.polygonSideRawSymbol q .c)
  · left
    simp only [canonicalProjectiveConePostConeBoundaryTerm,
      canonicalProjectiveConePostConeSideWord]
    rw [(CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord_of_degenerate hdeg]
    exact map_one _
  · let raw : CanonicalProjectiveConeNondegenerateSymbol p :=
      ⟨S.polygonSideRawSymbol q .c, hdeg⟩
    have hraw_generator : raw.1.2 = .c := by
      simp [raw, BuserSarnakProjectiveQuotientSectionData.polygonSideRawSymbol]
    have hraw_kept : ¬ isCanonicalProjectiveConeEliminationSymbol raw := by
      apply canonicalProjectiveConeNoncone_not_eliminated raw
      exact Or.inr hraw_generator
    let z : CanonicalProjectiveConeKeptSymbol p := ⟨raw, hraw_kept⟩
    right
    refine ⟨z, Or.inl ⟨?_, ?_, ?_⟩⟩
    · change (⟨q⟩ : ProjectivePolygonPostConeFace p) =
        ⟨S.polygonSideBase raw.1.1 raw.1.2.positivePolygonSide⟩
      apply congrArg ProjectivePolygonPostConeFace.mk
      change q = S.polygonSideBase (S.polygonSideStart q .c) .c
      exact (S.polygonSideBase_start q .c).symm
    · change .c = raw.1.2.positivePolygonSide
      dsimp [raw]
      rfl
    · simp only [canonicalProjectiveConePostConeBoundaryTerm,
        canonicalProjectiveConePostConeSideWord]
      rw [(CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord_of_not_degenerate hdeg]
      change canonicalProjectiveConeFirstStageSubstitution p (FreeGroup.of raw) = _
      rw [canonicalProjectiveConeFirstStageSubstitution_of_kept z]

/-- The inverse non-cone side `a⁻¹` is trivial or has an inverse target
carrier. -/
private theorem canonicalProjectiveConePostConeBoundaryTerm_aInv_eq_one_or_physicalCarrier
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) :
    canonicalProjectiveConePostConeBoundaryTerm p q .aInv = 1 ∨
      CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrier p q .aInv := by
  classical
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  by_cases hdeg : (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (S.polygonSideRawSymbol q .aInv)
  · left
    simp only [canonicalProjectiveConePostConeBoundaryTerm,
      canonicalProjectiveConePostConeSideWord]
    rw [(CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord_of_degenerate hdeg]
    simp
  · let raw : CanonicalProjectiveConeNondegenerateSymbol p :=
      ⟨S.polygonSideRawSymbol q .aInv, hdeg⟩
    have hraw_generator : raw.1.2 = .a := by
      simp [raw, BuserSarnakProjectiveQuotientSectionData.polygonSideRawSymbol]
    have hraw_kept : ¬ isCanonicalProjectiveConeEliminationSymbol raw := by
      apply canonicalProjectiveConeNoncone_not_eliminated raw
      exact Or.inl hraw_generator
    let z : CanonicalProjectiveConeKeptSymbol p := ⟨raw, hraw_kept⟩
    have hsourceDart : S.polygonSidePartner q .aInv =
        (S.polygonSideBase (S.polygonAfterAInv q) .a, .a) := by
      rfl
    have htargetDart : S.polygonSidePartner
        (S.polygonSideBase (S.polygonAfterAInv q) .a) .a = (q, .aInv) := by
      have hinv := S.polygonSidePartner_involutive q .aInv
      rw [hsourceDart] at hinv
      exact hinv
    right
    refine ⟨z, Or.inr ⟨?_, ?_, ?_⟩⟩
    · change (⟨q⟩ : ProjectivePolygonPostConeFace p) =
        ⟨(S.polygonSidePartner
          (S.polygonSideBase raw.1.1 raw.1.2.positivePolygonSide)
          raw.1.2.positivePolygonSide).1⟩
      apply congrArg ProjectivePolygonPostConeFace.mk
      dsimp [raw]
      exact (congrArg Prod.fst htargetDart).symm
    · change .aInv = (S.polygonSidePartner
        (S.polygonSideBase raw.1.1 raw.1.2.positivePolygonSide)
        raw.1.2.positivePolygonSide).2
      dsimp [raw]
      exact (congrArg Prod.snd htargetDart).symm
    · simp only [canonicalProjectiveConePostConeBoundaryTerm,
        canonicalProjectiveConePostConeSideWord]
      rw [(CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord_of_not_degenerate hdeg]
      change (canonicalProjectiveConeFirstStageSubstitution p (FreeGroup.of raw))⁻¹ = _
      rw [canonicalProjectiveConeFirstStageSubstitution_of_kept z]

/-- The inverse non-cone side `c⁻¹` is trivial or has an inverse target
carrier. -/
private theorem canonicalProjectiveConePostConeBoundaryTerm_cInv_eq_one_or_physicalCarrier
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) :
    canonicalProjectiveConePostConeBoundaryTerm p q .cInv = 1 ∨
      CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrier p q .cInv := by
  classical
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  by_cases hdeg : (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (S.polygonSideRawSymbol q .cInv)
  · left
    simp only [canonicalProjectiveConePostConeBoundaryTerm,
      canonicalProjectiveConePostConeSideWord]
    rw [(CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord_of_degenerate hdeg]
    simp
  · let raw : CanonicalProjectiveConeNondegenerateSymbol p :=
      ⟨S.polygonSideRawSymbol q .cInv, hdeg⟩
    have hraw_generator : raw.1.2 = .c := by
      simp [raw, BuserSarnakProjectiveQuotientSectionData.polygonSideRawSymbol]
    have hraw_kept : ¬ isCanonicalProjectiveConeEliminationSymbol raw := by
      apply canonicalProjectiveConeNoncone_not_eliminated raw
      exact Or.inr hraw_generator
    let z : CanonicalProjectiveConeKeptSymbol p := ⟨raw, hraw_kept⟩
    have hsourceDart : S.polygonSidePartner q .cInv =
        (S.polygonSideBase (S.polygonAfterCInv q) .c, .c) := by
      rfl
    have htargetDart : S.polygonSidePartner
        (S.polygonSideBase (S.polygonAfterCInv q) .c) .c = (q, .cInv) := by
      have hinv := S.polygonSidePartner_involutive q .cInv
      rw [hsourceDart] at hinv
      exact hinv
    right
    refine ⟨z, Or.inr ⟨?_, ?_, ?_⟩⟩
    · change (⟨q⟩ : ProjectivePolygonPostConeFace p) =
        ⟨(S.polygonSidePartner
          (S.polygonSideBase raw.1.1 raw.1.2.positivePolygonSide)
          raw.1.2.positivePolygonSide).1⟩
      apply congrArg ProjectivePolygonPostConeFace.mk
      dsimp [raw]
      exact (congrArg Prod.fst htargetDart).symm
    · change .cInv = (S.polygonSidePartner
        (S.polygonSideBase raw.1.1 raw.1.2.positivePolygonSide)
        raw.1.2.positivePolygonSide).2
      dsimp [raw]
      exact (congrArg Prod.snd htargetDart).symm
    · simp only [canonicalProjectiveConePostConeBoundaryTerm,
        canonicalProjectiveConePostConeSideWord]
      rw [(CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord_of_not_degenerate hdeg]
      change (canonicalProjectiveConeFirstStageSubstitution p (FreeGroup.of raw))⁻¹ = _
      rw [canonicalProjectiveConeFirstStageSubstitution_of_kept z]

/-- Every post-cone polygon boundary term is trivial or an exact signed
occurrence of a retained physical edge. -/
theorem canonicalProjectiveConePostConeBoundaryTerm_eq_one_or_physicalCarrier
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) :
    canonicalProjectiveConePostConeBoundaryTerm p q s = 1 ∨
      CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrier p q s := by
  cases s with
  | a => exact canonicalProjectiveConePostConeBoundaryTerm_a_eq_one_or_physicalCarrier q
  | e1 => simpa [ProjectiveOctagonConeGenerator.lift,
      ProjectiveOctagonGenerator.positivePolygonSide] using
      canonicalProjectiveConePostConeConeBoundaryTerm_eq_one_or_physicalCarrier hp hp2 q .e1
  | cInv => exact canonicalProjectiveConePostConeBoundaryTerm_cInv_eq_one_or_physicalCarrier q
  | e2 => simpa [ProjectiveOctagonConeGenerator.lift,
      ProjectiveOctagonGenerator.positivePolygonSide] using
      canonicalProjectiveConePostConeConeBoundaryTerm_eq_one_or_physicalCarrier hp hp2 q .e2
  | aInv => exact canonicalProjectiveConePostConeBoundaryTerm_aInv_eq_one_or_physicalCarrier q
  | e3 => simpa [ProjectiveOctagonConeGenerator.lift,
      ProjectiveOctagonGenerator.positivePolygonSide] using
      canonicalProjectiveConePostConeConeBoundaryTerm_eq_one_or_physicalCarrier hp hp2 q .e3
  | c => exact canonicalProjectiveConePostConeBoundaryTerm_c_eq_one_or_physicalCarrier q
  | e4 => simpa [ProjectiveOctagonConeGenerator.lift,
      ProjectiveOctagonGenerator.positivePolygonSide] using
      canonicalProjectiveConePostConeConeBoundaryTerm_eq_one_or_physicalCarrier hp hp2 q .e4


end

end SystolicGrowth
