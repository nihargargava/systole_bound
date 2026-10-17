module

public import BuserSarnak.BuserSarnakProjectivePostConeTietze

@[expose] public section

/-!
# Definitional elimination plans for labelled polygon trees

The Tietze library can eliminate a predicate-selected family of generators in
one substitution once its defining words use only the final kept alphabet.
For the post-cone polygon stage, the needed geometric input is a leaf-to-root
tree-slot order, recursively expanded final words, and proofs that their
defining relators follow from the first-stage polygon relators.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete.Presentations

universe u v

/-- Data which turns a finite labelled family into a batch of definitional
Tietze eliminations after its defining words have been expanded into the final
kept alphabet. -/
structure LabelledFiniteDefinitionalEliminationPlan
    (Slot : Type u) (G : Type v) (label : Slot → G)
    (R : Set (FreeGroup G)) where
  delete : G → Prop
  decidableDelete : DecidablePred delete
  slotEquivDeleted : Slot ≃ Presented.GeneratorPartition.Deleted delete
  slotLabel_eq_deleted : ∀ slot : Slot, (slotEquivDeleted slot).1 = label slot
  order : List Slot
  order_nodup : order.Nodup
  mem_order : ∀ slot : Slot, slot ∈ order
  word : Presented.GeneratorPartition.Deleted delete →
    FreeGroup (Presented.GeneratorPartition.Kept delete)
  definingRelatorsRedundant :
    @Presented.definedGeneratorRelatorsOfPredicate G delete decidableDelete word ⊆
      Subgroup.normalClosure R

namespace LabelledFiniteDefinitionalEliminationPlan

variable {Slot : Type u} {G : Type v} {label : Slot → G} {R : Set (FreeGroup G)}

/-- Slot labels are injective when slots enumerate the deleted generators. -/
theorem label_injective
    (D : LabelledFiniteDefinitionalEliminationPlan Slot G label R) :
    Function.Injective label := by
  intro x y hxy
  apply D.slotEquivDeleted.injective
  apply Subtype.ext
  calc
    (D.slotEquivDeleted x).1 = label x := D.slotLabel_eq_deleted x
    _ = label y := hxy
    _ = (D.slotEquivDeleted y).1 := (D.slotLabel_eq_deleted y).symm

/-- The deletion predicate is exactly the range of the displayed slot labels. -/
theorem delete_iff_exists_slot
    (D : LabelledFiniteDefinitionalEliminationPlan Slot G label R)
    (z : G) :
    D.delete z ↔ ∃ slot : Slot, label slot = z := by
  constructor
  · intro hz
    obtain ⟨slot, hslot⟩ := D.slotEquivDeleted.surjective ⟨z, hz⟩
    refine ⟨slot, ?_⟩
    calc
      label slot = (D.slotEquivDeleted slot).1 := (D.slotLabel_eq_deleted slot).symm
      _ = z := congrArg Subtype.val hslot
  · rintro ⟨slot, hslot⟩
    rw [← hslot, ← D.slotLabel_eq_deleted slot]
    exact (D.slotEquivDeleted slot).2

/-- The plan's order lists distinct generator labels. -/
theorem label_order_nodup
    (D : LabelledFiniteDefinitionalEliminationPlan Slot G label R) :
    (D.order.map label).Nodup :=
  D.order_nodup.map D.label_injective

/-- Add redundant defining relators, then substitute every selected generator
by its final defining word. -/
noncomputable def verifiedTietzeScript
    (D : LabelledFiniteDefinitionalEliminationPlan Slot G label R) :
    VerifiedTietzeScript
      (Presentation.ofRelators R)
      (Presentation.ofRelators
        (@Presented.relatorsAfterSubstitutingDefinedGeneratorsOfPredicate G R D.delete
          D.decidableDelete D.word)) := by
  letI := D.decidableDelete
  exact
    (VerifiedTietzeScript.replaceRelators
      (R := R)
      (S := R ∪ Presented.definedGeneratorRelatorsOfPredicate D.delete D.word)
      (by
        intro r hr
        exact RelatorEquivalent.of_mem (Or.inl hr))
      (by
        intro r hr
        rcases hr with hr | hr
        · exact RelatorEquivalent.of_mem hr
        · exact RelatorEquivalent.of_mem_normalClosure
            (D.definingRelatorsRedundant hr))).trans
      (VerifiedTietzeScript.substituteDefinedGeneratorsAlongEquiv R
        (Presented.GeneratorPartition.equiv D.delete) D.word)

/-- The generic certificate has one relator-adjunction and one substitution. -/
@[simp] theorem verifiedTietzeScript_trace
    (D : LabelledFiniteDefinitionalEliminationPlan Slot G label R) :
    D.verifiedTietzeScript.trace =
      [.replaceRelators, .substituteDefinedGenerators] :=
  rfl

@[simp] theorem verifiedTietzeScript_moveCount
    (D : LabelledFiniteDefinitionalEliminationPlan Slot G label R) :
    D.verifiedTietzeScript.moveCount = 2 :=
  rfl

end LabelledFiniteDefinitionalEliminationPlan

/-- A finite labelled rooted arborescence feeds the generic plan through its
total-arrow type. -/
abbrev LabelledRootedArborescenceEliminationPlan
    {V : Type u} [Quiver V]
    (T : WideSubquiver (Quiver.Symmetrify V)) [Quiver.Arborescence T]
    {G : Type v} (label : Quiver.Total T → G)
    (R : Set (FreeGroup G)) :=
  LabelledFiniteDefinitionalEliminationPlan (Quiver.Total T) G label R

/-- The retained generators carried by canonical physical-tree arrows. -/
def isCanonicalProjectivePostConeTreeEliminationSymbol
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectiveConeKeptSymbol p) : Prop :=
  ∃ slot : CanonicalProjectivePostConeTreeSlot hp hp2,
    canonicalProjectivePostConeTreeSlotLabel hp hp2 slot = z

@[instance_reducible] noncomputable def canonicalProjectivePostConeTreeEliminationDecidable
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    DecidablePred (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2) :=
  Classical.decPred _

/-- The injective tree-slot labelling identifies slots with precisely the
selected retained-generator subtype. -/
noncomputable def canonicalProjectivePostConeTreeSlotEquivDeleted
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    CanonicalProjectivePostConeTreeSlot hp hp2 ≃
      Presented.GeneratorPartition.Deleted
        (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2) := by
  refine Equiv.ofBijective
    (fun slot => ⟨canonicalProjectivePostConeTreeSlotLabel hp hp2 slot, ⟨slot, rfl⟩⟩) ?_
  constructor
  · intro x y hxy
    apply canonicalProjectivePostConeTreeSlotLabel_injective hp hp2
    exact congrArg Subtype.val hxy
  · intro z
    rcases z.2 with ⟨slot, hslot⟩
    refine ⟨slot, ?_⟩
    apply Subtype.ext
    exact hslot

/-- A general plan over the canonical post-cone tree-slot interface. -/
abbrev CanonicalProjectivePostConeTreeEliminationPlan
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) : Type := by
  letI : Quiver.Arborescence (projectivePolygonPostConeCanonicalSpanningTree hp hp2) :=
    projectivePolygonPostConeCanonicalSpanningTreeArborescence hp hp2
  exact LabelledRootedArborescenceEliminationPlan
    (projectivePolygonPostConeCanonicalSpanningTree hp hp2)
    (canonicalProjectivePostConeTreeSlotLabel hp hp2)
    (CanonicalProjectiveConeFirstStageRelators p)

/-- Concrete leaf-order data required by the post-cone polygon stage.  Its
words are fully expanded into the non-tree alphabet, allowing one predicate
substitution after redundant defining relators are introduced. -/
structure CanonicalProjectivePostConeTreeEliminationData
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) where
  eliminationOrder : List (CanonicalProjectivePostConeTreeSlot hp hp2)
  eliminationOrder_nodup : eliminationOrder.Nodup
  mem_eliminationOrder : ∀ slot : CanonicalProjectivePostConeTreeSlot hp hp2,
    slot ∈ eliminationOrder
  word : Presented.GeneratorPartition.Deleted
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2) →
    FreeGroup (Presented.GeneratorPartition.Kept
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2))
  definingRelatorsRedundant :
    @Presented.definedGeneratorRelatorsOfPredicate
      (CanonicalProjectiveConeKeptSymbol p)
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)
      (canonicalProjectivePostConeTreeEliminationDecidable hp hp2) word ⊆
      Subgroup.normalClosure (CanonicalProjectiveConeFirstStageRelators p)

namespace CanonicalProjectivePostConeTreeEliminationData

variable {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)

/-- Package the concrete canonical data as the generic labelled plan. -/
noncomputable def toPlan
    (D : CanonicalProjectivePostConeTreeEliminationData hp hp2) :
    CanonicalProjectivePostConeTreeEliminationPlan hp hp2 where
  delete := isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2
  decidableDelete := canonicalProjectivePostConeTreeEliminationDecidable hp hp2
  slotEquivDeleted := canonicalProjectivePostConeTreeSlotEquivDeleted hp hp2
  slotLabel_eq_deleted := by intro slot; rfl
  order := D.eliminationOrder
  order_nodup := D.eliminationOrder_nodup
  mem_order := D.mem_eliminationOrder
  word := D.word
  definingRelatorsRedundant := D.definingRelatorsRedundant

/-- The promised two-move certificate from any completed leaf-order plan. -/
noncomputable def verifiedTietzeScript
    (D : CanonicalProjectivePostConeTreeEliminationData hp hp2) :
    VerifiedTietzeScript
      (Presentation.ofRelators (CanonicalProjectiveConeFirstStageRelators p))
      (Presentation.ofRelators
        (@Presented.relatorsAfterSubstitutingDefinedGeneratorsOfPredicate
          (CanonicalProjectiveConeKeptSymbol p)
          (CanonicalProjectiveConeFirstStageRelators p)
          (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)
          (canonicalProjectivePostConeTreeEliminationDecidable hp hp2) D.word)) :=
  LabelledFiniteDefinitionalEliminationPlan.verifiedTietzeScript (toPlan hp hp2 D)

@[simp] theorem verifiedTietzeScript_trace
    (D : CanonicalProjectivePostConeTreeEliminationData hp hp2) :
    (verifiedTietzeScript hp hp2 D).trace =
      [.replaceRelators, .substituteDefinedGenerators] :=
  LabelledFiniteDefinitionalEliminationPlan.verifiedTietzeScript_trace (toPlan hp hp2 D)

@[simp] theorem verifiedTietzeScript_moveCount
    (D : CanonicalProjectivePostConeTreeEliminationData hp hp2) :
    (verifiedTietzeScript hp hp2 D).moveCount = 2 :=
  LabelledFiniteDefinitionalEliminationPlan.verifiedTietzeScript_moveCount (toPlan hp hp2 D)

/-- The concrete leaf order has no repeated generator labels. -/
theorem eliminationOrder_label_nodup
    (D : CanonicalProjectivePostConeTreeEliminationData hp hp2) :
    (D.eliminationOrder.map (canonicalProjectivePostConeTreeSlotLabel hp hp2)).Nodup :=
  LabelledFiniteDefinitionalEliminationPlan.label_order_nodup (toPlan hp hp2 D)

end CanonicalProjectivePostConeTreeEliminationData

end

end SystolicGrowth
