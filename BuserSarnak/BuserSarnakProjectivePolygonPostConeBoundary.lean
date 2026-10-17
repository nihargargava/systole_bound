module

public import BuserSarnak.BuserSarnakProjectiveCanonicalTree
public import BuserSarnak.BuserSarnakProjectivePolygonPostConeCut
public import BuserSarnak.BuserSarnakProjectivePolygonTreeCarriers

@[expose] public section

/-!
# Canonical tree symbols on the post-cone boundary

This module packages the canonical tree symbols detected by crossings of the
root component in the physical post-cone quiver.  It deliberately records
only the finite boundary carrier set; the later local dart argument decides
how these carriers meet at a primal vertex.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete

noncomputable local instance buserSarnakProjectivePolygonPostConeBoundaryRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

noncomputable local instance buserSarnakProjectivePolygonPostConeBoundaryDegenerateFintype
    (p : ℕ) [NeZero p] : Fintype (CanonicalBuserSarnakProjectiveDegenerateSymbol p) :=
  Fintype.ofFinite _

/-- A canonical tree symbol is carried by a crossing dart when it is the raw
label of that dart or of its paired occurrence. -/
def projectivePolygonPostConeCrossingCarries
    (p : ℕ) [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) : Prop :=
  ∃ q : BuserSarnakProjectiveReductionRange p, ∃ s : ProjectivePolygonSide,
    projectivePolygonPostConeCrossing q s ∧
      (z.1 = (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol q s ∨
        z.1 = (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
          ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
          ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2)

/-- The finite family of canonical tree symbols carried by root-component
crossing darts. -/
noncomputable def projectivePolygonPostConeCrossingTreeSymbols
    (p : ℕ) [NeZero p] :
    Finset (CanonicalBuserSarnakProjectiveDegenerateSymbol p) := by
  classical
  exact Finset.univ.filter (projectivePolygonPostConeCrossingCarries p)

/-- Membership in the crossing boundary set is exactly a crossing-dart
carrier witness. -/
theorem mem_projectivePolygonPostConeCrossingTreeSymbols_iff
    {p : ℕ} [NeZero p]
    {z : CanonicalBuserSarnakProjectiveDegenerateSymbol p} :
    z ∈ projectivePolygonPostConeCrossingTreeSymbols p ↔
      projectivePolygonPostConeCrossingCarries p z := by
  classical
  simp [projectivePolygonPostConeCrossingTreeSymbols]

/-- Every root-component crossing contributes a canonical degenerate symbol
to the finite crossing boundary set, with its displayed raw carrier. -/
theorem projectivePolygonPostConeCrossing_exists_mem_treeSymbols
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide)
    (hcross : projectivePolygonPostConeCrossing q s) :
    ∃ z ∈ projectivePolygonPostConeCrossingTreeSymbols p,
      z.1 = (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol q s ∨
        z.1 = (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
          ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
          ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2 := by
  rcases projectivePolygonPostConeCrossing_raw_or_partner_degenerate hp hp2 q s hcross with
    hraw | hpartner
  · let z : CanonicalBuserSarnakProjectiveDegenerateSymbol p :=
      ⟨(canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol q s, hraw⟩
    refine ⟨z, (mem_projectivePolygonPostConeCrossingTreeSymbols_iff).mpr ?_, Or.inl rfl⟩
    exact ⟨q, s, hcross, Or.inl rfl⟩
  · let z : CanonicalBuserSarnakProjectiveDegenerateSymbol p :=
      ⟨(canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2,
        hpartner⟩
    refine ⟨z, (mem_projectivePolygonPostConeCrossingTreeSymbols_iff).mpr ?_, Or.inr rfl⟩
    exact ⟨q, s, hcross, Or.inr rfl⟩

/-- A member of the finite crossing boundary set exposes a crossing dart and
the equality identifying the symbol with one of its two raw carriers. -/
theorem projectivePolygonPostConeCrossing_carrier_of_mem_treeSymbols
    {p : ℕ} [NeZero p]
    {z : CanonicalBuserSarnakProjectiveDegenerateSymbol p}
    (hz : z ∈ projectivePolygonPostConeCrossingTreeSymbols p) :
    ∃ q : BuserSarnakProjectiveReductionRange p, ∃ s : ProjectivePolygonSide,
      projectivePolygonPostConeCrossing q s ∧
        (z.1 = (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol q s ∨
          z.1 = (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
            ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
            ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2) :=
  (mem_projectivePolygonPostConeCrossingTreeSymbols_iff).mp hz

/-- Every boundary tree symbol has a crossing at its distinguished target
carrier.  A crossing witnessed on the opposite carrier is transported across
the paired polygon side. -/
theorem projectivePolygonPostConeCrossing_treeTargetDart_of_mem_treeSymbols
    {p : ℕ} [NeZero p]
    {z : CanonicalBuserSarnakProjectiveDegenerateSymbol p}
    (hz : z ∈ projectivePolygonPostConeCrossingTreeSymbols p) :
    projectivePolygonPostConeCrossing
      (canonicalProjectivePolygonTreeTargetDart z).1
      (canonicalProjectivePolygonTreeTargetDart z).2 := by
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  rcases projectivePolygonPostConeCrossing_carrier_of_mem_treeSymbols hz with
    ⟨q, s, hcross, hraw | hpartner⟩
  · have hcarrier : IsCanonicalProjectivePolygonTreeCarrier z (q, s) :=
      isCanonicalProjectivePolygonTreeCarrier_of_rawSymbol_eq q s z hraw.symm
    rcases hcarrier with hsource | htarget
    · have hq : q = (canonicalProjectivePolygonTreeSourceDart z).1 := by
        simpa using congrArg Prod.fst hsource
      have hs : s = (canonicalProjectivePolygonTreeSourceDart z).2 := by
        simpa using congrArg Prod.snd hsource
      have hsourceCross : projectivePolygonPostConeCrossing
          (canonicalProjectivePolygonTreeSourceDart z).1
          (canonicalProjectivePolygonTreeSourceDart z).2 := by
        simpa only [hq, hs] using hcross
      rw [canonicalProjectivePolygonTreeTargetDart_eq_partner]
      exact (projectivePolygonPostConeCrossing_partner_iff
        (canonicalProjectivePolygonTreeSourceDart z).1
        (canonicalProjectivePolygonTreeSourceDart z).2).mpr hsourceCross
    · have hq : q = (canonicalProjectivePolygonTreeTargetDart z).1 := by
        simpa using congrArg Prod.fst htarget
      have hs : s = (canonicalProjectivePolygonTreeTargetDart z).2 := by
        simpa using congrArg Prod.snd htarget
      simpa only [hq, hs] using hcross
  · have hpartnerCross : projectivePolygonPostConeCrossing
        (S.polygonSidePartner q s).1 (S.polygonSidePartner q s).2 :=
      (projectivePolygonPostConeCrossing_partner_iff q s).mpr hcross
    have hcarrier : IsCanonicalProjectivePolygonTreeCarrier z
        (S.polygonSidePartner q s) :=
      isCanonicalProjectivePolygonTreeCarrier_of_rawSymbol_eq
        (S.polygonSidePartner q s).1 (S.polygonSidePartner q s).2 z hpartner.symm
    rcases hcarrier with hsource | htarget
    · have hq : (S.polygonSidePartner q s).1 =
          (canonicalProjectivePolygonTreeSourceDart z).1 := by
        simpa using congrArg Prod.fst hsource
      have hs : (S.polygonSidePartner q s).2 =
          (canonicalProjectivePolygonTreeSourceDart z).2 := by
        simpa using congrArg Prod.snd hsource
      have hsourceCross : projectivePolygonPostConeCrossing
          (canonicalProjectivePolygonTreeSourceDart z).1
          (canonicalProjectivePolygonTreeSourceDart z).2 := by
        simpa only [hq, hs] using hpartnerCross
      rw [canonicalProjectivePolygonTreeTargetDart_eq_partner]
      exact (projectivePolygonPostConeCrossing_partner_iff
        (canonicalProjectivePolygonTreeSourceDart z).1
        (canonicalProjectivePolygonTreeSourceDart z).2).mpr hsourceCross
    · have hq : (S.polygonSidePartner q s).1 =
          (canonicalProjectivePolygonTreeTargetDart z).1 := by
        simpa using congrArg Prod.fst htarget
      have hs : (S.polygonSidePartner q s).2 =
          (canonicalProjectivePolygonTreeTargetDart z).2 := by
        simpa using congrArg Prod.snd htarget
      simpa only [hq, hs] using hpartnerCross

end

end SystolicGrowth
