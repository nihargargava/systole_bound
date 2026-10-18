module

public import BuserSarnak.BuserSarnakProjectivePostConeTreeBoundaryOrder
public import Mathlib.Data.Fintype.OfMap

@[expose] public section

/-!
# Canonical post-cone tree-elimination data

The leaf-to-root boundary triangularity theorem is converted into fully
final-alphabet defining words.  The words are chosen from the quotient range;
their defining relators are then redundant consequences of the first-stage
polygon presentation.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

noncomputable local instance canonicalProjectivePostConeTreeDataDecidable
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    DecidablePred (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2) :=
  canonicalProjectivePostConeTreeEliminationDecidable hp hp2

/-- Include a word on the final non-tree alphabet into the first-stage
post-cone alphabet. -/
noncomputable def canonicalProjectivePostConeFinalInclusion
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    FreeGroup (Presented.GeneratorPartition.Kept
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) →*
      FreeGroup (CanonicalProjectiveConeKeptSymbol p) :=
  FreeGroup.lift fun z => FreeGroup.of z.1

@[simp] theorem canonicalProjectivePostConeFinalInclusion_of
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : Presented.GeneratorPartition.Kept
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) :
    canonicalProjectivePostConeFinalInclusion hp hp2 (FreeGroup.of z) =
      FreeGroup.of z.1 := by
  simp [canonicalProjectivePostConeFinalInclusion]

/-- The final-alphabet inclusion followed by the first-stage presented-group
quotient. -/
noncomputable def canonicalProjectivePostConeFinalQuotientMap
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    FreeGroup (Presented.GeneratorPartition.Kept
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) →*
      FreeGroup (CanonicalProjectiveConeKeptSymbol p) ⧸
        Subgroup.normalClosure (CanonicalProjectiveConeFirstStageRelators p) :=
  (QuotientGroup.mk' (Subgroup.normalClosure
    (CanonicalProjectiveConeFirstStageRelators p))).comp
      (canonicalProjectivePostConeFinalInclusion hp hp2)

@[simp] theorem canonicalProjectivePostConeFinalQuotientMap_of
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : Presented.GeneratorPartition.Kept
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) :
    canonicalProjectivePostConeFinalQuotientMap hp hp2 (FreeGroup.of z) =
      (QuotientGroup.mk' (Subgroup.normalClosure
        (CanonicalProjectiveConeFirstStageRelators p))) (FreeGroup.of z.1) := by
  simp [canonicalProjectivePostConeFinalQuotientMap]

private theorem canonicalProjectivePostConeTreeSlotDependencyWellFounded
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    WellFounded (fun child parent : CanonicalProjectivePostConeTreeSlot hp hp2 =>
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child) := by
  letI : DecidableEq (CanonicalProjectivePostConeTreeSlot hp hp2) := Classical.decEq _
  letI : Fintype (CanonicalProjectivePostConeTreeSlot hp hp2) :=
    Fintype.ofList (canonicalProjectivePostConeTreeSlotEliminationOrder hp hp2)
      (mem_canonicalProjectivePostConeTreeSlotEliminationOrder hp hp2)
  letI : IsTrans (CanonicalProjectivePostConeTreeSlot hp hp2)
      (fun child parent : CanonicalProjectivePostConeTreeSlot hp hp2 =>
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent <
          canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child) :=
    ⟨by
      intro a b c hab hbc
      exact lt_trans hbc hab⟩
  letI : Std.Irrefl (fun child parent : CanonicalProjectivePostConeTreeSlot hp hp2 =>
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child) :=
    ⟨by
      intro x hx
      exact (Nat.lt_irrefl _ hx)⟩
  exact Finite.wellFounded_of_trans_of_irrefl _

private theorem canonicalProjectiveConePostConeBoundaryPrefixSuffix_mem
    {p : ℕ} [NeZero p] {Q : Type*} [Group Q]
    (f : FreeGroup (CanonicalProjectiveConeKeptSymbol p) →* Q)
    (H : Subgroup Q)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide)
    (h : ∀ t : ProjectivePolygonSide, t ≠ s →
      f (canonicalProjectiveConePostConeBoundaryTerm p q t) ∈ H) :
    f (canonicalProjectiveConePostConeBoundaryPrefix p q s) ∈ H ∧
      f (canonicalProjectiveConePostConeBoundarySuffix p q s) ∈ H := by
  cases s <;>
    simp only [canonicalProjectiveConePostConeBoundaryPrefix,
      canonicalProjectiveConePostConeBoundarySuffix, map_one, map_mul] <;>
    constructor <;>
    repeat' first
      | exact H.one_mem
      | apply H.mul_mem
      | exact h _ (by decide)

private theorem canonicalProjectiveConePostConeBoundaryTerm_mem_range_of_deeper
    {p : ℕ} [NeZero p] {Q : Type*} [Group Q]
    (hp : p.Prime) (hp2 : p ≠ 2)
    (M : FreeGroup (Presented.GeneratorPartition.Kept
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) →* Q)
    (pi : FreeGroup (CanonicalProjectiveConeKeptSymbol p) →* Q)
    (hfinal : ∀ (z : CanonicalProjectiveConeKeptSymbol p)
      (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z),
      M (FreeGroup.of ⟨z, hz⟩) = pi (FreeGroup.of z))
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      pi (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 other)) ∈ M.range)
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) :
    pi (canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s) ∈ M.range := by
  rcases canonicalProjectiveConePostConeBoundaryTerm_at_treeTarget_eq_one_or_nonTree_or_deeper_of_ne_rightFactorSide
      hp hp2 slot s hs with hterm | ⟨z, hcarrier, hz⟩ | ⟨z, other, hcarrier, hlabel, hdepth⟩
  · rw [hterm]
    simp
  · rcases hcarrier with hsource | htarget
    · rw [hsource.2.2]
      exact ⟨FreeGroup.of ⟨z, hz⟩, hfinal z hz⟩
    · rw [htarget.2.2]
      have hzmem : pi (FreeGroup.of z) ∈ M.range :=
        ⟨FreeGroup.of ⟨z, hz⟩, hfinal z hz⟩
      simpa only [map_inv] using M.range.inv_mem hzmem
  · rw [← hlabel] at hcarrier
    rcases hcarrier with hsource | htarget
    · rw [hsource.2.2]
      exact ih other hdepth
    · rw [htarget.2.2]
      simpa only [map_inv] using M.range.inv_mem (ih other hdepth)

/-- Each selected tree label already lies in the subgroup generated by the
final non-tree alphabet in the first-stage presented quotient. -/
theorem canonicalProjectivePostConeTreeSlotLabel_mem_finalQuotientRange
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    (QuotientGroup.mk' (Subgroup.normalClosure
      (CanonicalProjectiveConeFirstStageRelators p)))
      (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) ∈
      (canonicalProjectivePostConeFinalQuotientMap hp hp2).range := by
  let pi : FreeGroup (CanonicalProjectiveConeKeptSymbol p) →*
      FreeGroup (CanonicalProjectiveConeKeptSymbol p) ⧸
        Subgroup.normalClosure (CanonicalProjectiveConeFirstStageRelators p) :=
    QuotientGroup.mk' (Subgroup.normalClosure
      (CanonicalProjectiveConeFirstStageRelators p))
  let M := canonicalProjectivePostConeFinalQuotientMap hp hp2
  have hfinal : ∀ (z : CanonicalProjectiveConeKeptSymbol p)
      (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z),
      M (FreeGroup.of ⟨z, hz⟩) = pi (FreeGroup.of z) := by
    intro z hz
    let k : Presented.GeneratorPartition.Kept
        (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2) := ⟨z, hz⟩
    change (QuotientGroup.mk' (Subgroup.normalClosure
      (CanonicalProjectiveConeFirstStageRelators p)))
        (canonicalProjectivePostConeFinalInclusion hp hp2 (FreeGroup.of k)) =
      (QuotientGroup.mk' (Subgroup.normalClosure
        (CanonicalProjectiveConeFirstStageRelators p))) (FreeGroup.of z)
    rw [canonicalProjectivePostConeFinalInclusion_of hp hp2 k]
  change pi (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) ∈ M.range
  refine (canonicalProjectivePostConeTreeSlotDependencyWellFounded hp hp2).induction
    (C := fun slot => pi (FreeGroup.of
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) ∈ M.range) slot ?_
  intro slot ih
  have hterm : ∀ t : ProjectivePolygonSide,
      t ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot →
      pi (canonicalProjectiveConePostConeBoundaryTerm p slot.right.state t) ∈ M.range := by
    intro t ht
    exact canonicalProjectiveConePostConeBoundaryTerm_mem_range_of_deeper
      hp hp2 M pi hfinal slot ih t ht
  obtain ⟨hprefix, hsuffix⟩ :=
    canonicalProjectiveConePostConeBoundaryPrefixSuffix_mem pi M.range
      slot.right.state (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) hterm
  have hrel : pi (canonicalProjectiveConePostConePolygonWord p slot.right.state) = 1 := by
    have hrel' : RelatorEquivalent (CanonicalProjectiveConeFirstStageRelators p)
        (canonicalProjectiveConePostConePolygonWord p slot.right.state) 1 :=
      RelatorEquivalent.of_mem
        (canonicalProjectiveConePostConePolygonWord_mem_firstStageRelators slot.right.state)
    rw [relatorEquivalent_iff_eq_in_presentedQuotient] at hrel'
    exact hrel'
  rw [canonicalProjectivePostConeTreeSlot_polygonWord_right_factor hp hp2 slot] at hrel
  rcases hprefix with ⟨u, hu⟩
  rcases hsuffix with ⟨v, hv⟩
  unfold canonicalProjectivePostConeTreeSlotRightFactorWord at hrel
  by_cases hsource : slot.right = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)
  · rw [if_pos hsource] at hrel
    simp only [map_mul] at hrel
    rw [← hu, ← hv] at hrel
    refine ⟨u⁻¹ * v⁻¹, ?_⟩
    have hx : pi (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) =
        (M u)⁻¹ * (M v)⁻¹ := by
      calc
        pi (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) =
            (M u)⁻¹ *
              (M u * pi (FreeGroup.of
                (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) * M v) *
                (M v)⁻¹ := by group
        _ = (M u)⁻¹ * 1 * (M v)⁻¹ := by rw [hrel]
        _ = (M u)⁻¹ * (M v)⁻¹ := by simp
    calc
      M (u⁻¹ * v⁻¹) = (M u)⁻¹ * (M v)⁻¹ := by simp
      _ = pi (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) := hx.symm
  · rw [if_neg hsource] at hrel
    simp only [map_mul, map_inv] at hrel
    rw [← hu, ← hv] at hrel
    refine ⟨v * u, ?_⟩
    have hx : pi (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) =
        M v * M u := by
      calc
        pi (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) =
            M v * (M u *
              (pi (FreeGroup.of
                (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)))⁻¹ * M v)⁻¹ *
                M u := by group
        _ = M v * 1⁻¹ * M u := by rw [hrel]
        _ = M v * M u := by simp
    calc
      M (v * u) = M v * M u := by simp
      _ = pi (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) := hx.symm

/-- Every deleted-generator subtype has a final-alphabet preimage in the
first-stage quotient. -/
theorem canonicalProjectivePostConeDeletedGenerator_mem_finalQuotientRange
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : Presented.GeneratorPartition.Deleted
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) :
    (QuotientGroup.mk' (Subgroup.normalClosure
      (CanonicalProjectiveConeFirstStageRelators p))) (FreeGroup.of z.1) ∈
      (canonicalProjectivePostConeFinalQuotientMap hp hp2).range := by
  rcases z.2 with ⟨slot, hslot⟩
  rw [← hslot]
  exact canonicalProjectivePostConeTreeSlotLabel_mem_finalQuotientRange hp hp2 slot

theorem canonicalProjectivePostConeDeletedGenerator_exists_finalWord
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : Presented.GeneratorPartition.Deleted
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) :
    ∃ w : FreeGroup (Presented.GeneratorPartition.Kept
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)),
      canonicalProjectivePostConeFinalQuotientMap hp hp2 w =
        (QuotientGroup.mk' (Subgroup.normalClosure
          (CanonicalProjectiveConeFirstStageRelators p))) (FreeGroup.of z.1) :=
  (MonoidHom.mem_range.mp
    (canonicalProjectivePostConeDeletedGenerator_mem_finalQuotientRange hp hp2 z))

/-- A final-alphabet word chosen for each deleted tree generator. -/
noncomputable def canonicalProjectivePostConeTreeEliminationWord
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : Presented.GeneratorPartition.Deleted
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) :
    FreeGroup (Presented.GeneratorPartition.Kept
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) :=
  Classical.choose
    (canonicalProjectivePostConeDeletedGenerator_exists_finalWord hp hp2 z)

theorem canonicalProjectivePostConeTreeEliminationWord_spec
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : Presented.GeneratorPartition.Deleted
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) :
    canonicalProjectivePostConeFinalQuotientMap hp hp2
      (canonicalProjectivePostConeTreeEliminationWord hp hp2 z) =
        (QuotientGroup.mk' (Subgroup.normalClosure
          (CanonicalProjectiveConeFirstStageRelators p))) (FreeGroup.of z.1) :=
  Classical.choose_spec
    (canonicalProjectivePostConeDeletedGenerator_exists_finalWord hp hp2 z)

/-- The defining relation for a selected tree generator follows from the
first-stage relators. -/
theorem canonicalProjectivePostConeTreeEliminationWord_directRelator
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : Presented.GeneratorPartition.Deleted
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) :
    RelatorEquivalent (CanonicalProjectiveConeFirstStageRelators p)
      (FreeGroup.of z.1 *
        (canonicalProjectivePostConeFinalInclusion hp hp2
          (canonicalProjectivePostConeTreeEliminationWord hp hp2 z))⁻¹) 1 := by
  let pi : FreeGroup (CanonicalProjectiveConeKeptSymbol p) →*
      FreeGroup (CanonicalProjectiveConeKeptSymbol p) ⧸
        Subgroup.normalClosure (CanonicalProjectiveConeFirstStageRelators p) :=
    QuotientGroup.mk' (Subgroup.normalClosure
      (CanonicalProjectiveConeFirstStageRelators p))
  let M := canonicalProjectivePostConeFinalQuotientMap hp hp2
  have hword := canonicalProjectivePostConeTreeEliminationWord_spec hp hp2 z
  rw [relatorEquivalent_iff_eq_in_presentedQuotient]
  change pi (FreeGroup.of z.1 *
    (canonicalProjectivePostConeFinalInclusion hp hp2
      (canonicalProjectivePostConeTreeEliminationWord hp hp2 z))⁻¹) = 1
  rw [map_mul, map_inv]
  change pi (FreeGroup.of z.1) *
    (M (canonicalProjectivePostConeTreeEliminationWord hp hp2 z))⁻¹ = 1
  rw [hword]
  simp [pi]

theorem canonicalProjectivePostConeTreeEliminationPulledBackDefinedRelator
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : Presented.GeneratorPartition.Deleted
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) :
    (FreeGroup.freeGroupCongr
      (Presented.GeneratorPartition.equiv
        (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2))).symm
      (FreeGroup.of (Sum.inr z) *
        (Presented.includeAdjoinedGenerators
          (Presented.GeneratorPartition.Kept
            (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2))
          (Presented.GeneratorPartition.Deleted
            (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2))
          (canonicalProjectivePostConeTreeEliminationWord hp hp2 z))⁻¹) =
      FreeGroup.of z.1 *
        (canonicalProjectivePostConeFinalInclusion hp hp2
          (canonicalProjectivePostConeTreeEliminationWord hp hp2 z))⁻¹ := by
  simp [FreeGroup.freeGroupCongr, Presented.GeneratorPartition.equiv,
    Presented.includeAdjoinedGenerators, canonicalProjectivePostConeFinalInclusion]
  rw [← MonoidHom.comp_apply]
  congr 1
  ext x
  simp

/-- The predicate-based defining relators for all tree slots are redundant. -/
theorem canonicalProjectivePostConeTreeDefinedGeneratorRelators_subset_normalClosure
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    @Presented.definedGeneratorRelatorsOfPredicate
      (CanonicalProjectiveConeKeptSymbol p)
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)
      (canonicalProjectivePostConeTreeEliminationDecidable hp hp2)
      (canonicalProjectivePostConeTreeEliminationWord hp hp2) ⊆
      Subgroup.normalClosure (CanonicalProjectiveConeFirstStageRelators p) := by
  intro r hr
  change r ∈ (FreeGroup.freeGroupCongr
    (Presented.GeneratorPartition.equiv
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2))).symm ''
      Presented.definedGeneratorRelators
        (canonicalProjectivePostConeTreeEliminationWord hp hp2) at hr
  rcases hr with ⟨q, ⟨z, rfl⟩, rfl⟩
  rw [canonicalProjectivePostConeTreeEliminationPulledBackDefinedRelator hp hp2 z]
  exact RelatorEquivalent.mem_normalClosure_of_eq_one
    (canonicalProjectivePostConeTreeEliminationWord_directRelator hp hp2 z)

/-- The canonical leaf order and quotient-chosen final words supply the
complete second-stage tree-elimination package. -/
noncomputable def canonicalProjectivePostConeTreeEliminationData
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    CanonicalProjectivePostConeTreeEliminationData hp hp2 where
  eliminationOrder := canonicalProjectivePostConeTreeSlotEliminationOrder hp hp2
  eliminationOrder_nodup := canonicalProjectivePostConeTreeSlotEliminationOrder_nodup hp hp2
  mem_eliminationOrder := mem_canonicalProjectivePostConeTreeSlotEliminationOrder hp hp2
  word := canonicalProjectivePostConeTreeEliminationWord hp hp2
  definingRelatorsRedundant :=
    canonicalProjectivePostConeTreeDefinedGeneratorRelators_subset_normalClosure hp hp2

/-- The concrete two-move Tietze script that eliminates all selected
post-cone tree generators. -/
noncomputable def canonicalProjectivePostConeTreeVerifiedTietzeScript
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :=
  CanonicalProjectivePostConeTreeEliminationData.verifiedTietzeScript hp hp2
    (canonicalProjectivePostConeTreeEliminationData hp hp2)

@[simp] theorem canonicalProjectivePostConeTreeVerifiedTietzeScript_moveCount
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    (canonicalProjectivePostConeTreeVerifiedTietzeScript hp hp2).moveCount = 2 :=
  CanonicalProjectivePostConeTreeEliminationData.verifiedTietzeScript_moveCount hp hp2
    (canonicalProjectivePostConeTreeEliminationData hp hp2)

end

end SystolicGrowth
