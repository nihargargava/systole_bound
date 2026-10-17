module

public import BuserSarnak.BuserSarnakProjectivePostConeTietze
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-!
# A canonical leaf-to-root order for the post-cone tree

The physical post-cone spanning tree is directed away from its root.  This
module packages its total arrows in a finite deterministic order: larger
target depth comes first, with a finite enumeration only to break ties.
This is the combinatorial order needed to expand child defining words before
their parent polygon relation is used in the second Tietze stage.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

noncomputable local instance projectivePostConeLeafOrderRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

noncomputable local instance projectivePostConeLeafOrderFaceFintype
    (p : ℕ) [NeZero p] : Fintype (ProjectivePolygonPostConeFace p) :=
  Fintype.ofEquiv _ ProjectivePolygonPostConeFace.stateEquiv.symm

noncomputable local instance projectivePostConeLeafOrderFaceDecidableEq
    (p : ℕ) [NeZero p] : DecidableEq (ProjectivePolygonPostConeFace p) :=
  Classical.decEq _

noncomputable local instance projectivePostConeLeafOrderTreeVertexFintype
    {p : ℕ} [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) :
    Fintype (projectivePolygonPostConeCanonicalSpanningTree hp hp2) := by
  change Fintype (ProjectivePolygonPostConeFace p)
  infer_instance

noncomputable local instance projectivePostConeLeafOrderTreeVertexDecidableEq
    {p : ℕ} [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) :
    DecidableEq (projectivePolygonPostConeCanonicalSpanningTree hp hp2) := by
  change DecidableEq (ProjectivePolygonPostConeFace p)
  infer_instance

noncomputable local instance projectivePostConeLeafOrderSlotFintype
    {p : ℕ} [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) :
    Fintype (CanonicalProjectivePostConeTreeSlot hp hp2) := by
  letI := projectivePolygonPostConeCanonicalSpanningTreeArborescence hp hp2
  letI : Fintype {q : projectivePolygonPostConeCanonicalSpanningTree hp hp2 //
      q ≠ Quiver.root (projectivePolygonPostConeCanonicalSpanningTree hp hp2)} :=
    Fintype.subtype
      (Finset.univ.filter fun q =>
        q ≠ Quiver.root (projectivePolygonPostConeCanonicalSpanningTree hp hp2))
      (by simp)
  exact Fintype.ofEquiv _
    (ReidemeisterSchreier.Quiver.Arborescence.totalEquivNonRoot
      (projectivePolygonPostConeCanonicalSpanningTree hp hp2)).symm

/-- The arborescence distance from the post-cone root to a physical-tree
face. -/
noncomputable def canonicalProjectivePostConeTreeVertexDepth
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : projectivePolygonPostConeCanonicalSpanningTree hp hp2) : ℕ := by
  letI := projectivePolygonPostConeCanonicalSpanningTreeArborescence hp hp2
  exact (default : Quiver.Path
    (Quiver.root (projectivePolygonPostConeCanonicalSpanningTree hp hp2)) q).length

/-- The root-distance of the source of a selected physical-tree edge. -/
noncomputable def canonicalProjectivePostConeTreeSlotSourceDepth
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) : ℕ :=
  canonicalProjectivePostConeTreeVertexDepth hp hp2 slot.left

/-- The root-distance of the target of a selected physical-tree edge. -/
noncomputable def canonicalProjectivePostConeTreeSlotTargetDepth
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) : ℕ :=
  canonicalProjectivePostConeTreeVertexDepth hp hp2 slot.right

/-- Every canonical physical-tree arrow moves one level away from the root. -/
theorem canonicalProjectivePostConeTreeSlot_depth_succ
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    canonicalProjectivePostConeTreeSlotSourceDepth hp hp2 slot + 1 =
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot := by
  letI := projectivePolygonPostConeCanonicalSpanningTreeArborescence hp hp2
  unfold canonicalProjectivePostConeTreeSlotSourceDepth
    canonicalProjectivePostConeTreeSlotTargetDepth
    canonicalProjectivePostConeTreeVertexDepth
  have hpath :
      ((default : Quiver.Path
        (Quiver.root (projectivePolygonPostConeCanonicalSpanningTree hp hp2))
        slot.left).cons slot.hom : Quiver.Path
        (Quiver.root (projectivePolygonPostConeCanonicalSpanningTree hp hp2))
        slot.right) = default :=
    Subsingleton.elim _ _
  simpa using congrArg Quiver.Path.length hpath

/-- Consecutive tree arrows point strictly farther from the root.  Thus a
child slot has already been processed when its parent slot is considered in a
descending-depth elimination. -/
theorem canonicalProjectivePostConeTreeSlot_targetDepth_lt_of_right_eq_left
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    {parent child : CanonicalProjectivePostConeTreeSlot hp hp2}
    (hcomposable : parent.right = child.left) :
    canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child := by
  have hmiddle :
      canonicalProjectivePostConeTreeSlotSourceDepth hp hp2 child =
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent := by
    unfold canonicalProjectivePostConeTreeSlotSourceDepth
      canonicalProjectivePostConeTreeSlotTargetDepth
    rw [← hcomposable]
  have hchild := canonicalProjectivePostConeTreeSlot_depth_succ hp hp2 child
  omega

/-- A deterministic key for leaf-to-root elimination.  The first coordinate
orders depth in reverse, and the second makes ties strict. -/
noncomputable def canonicalProjectivePostConeTreeSlotOrderKey
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    Lex (OrderDual ℕ × Fin
      (Fintype.card (CanonicalProjectivePostConeTreeSlot hp hp2))) :=
  toLex
    (OrderDual.toDual (canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot),
      Fintype.equivFin (CanonicalProjectivePostConeTreeSlot hp hp2) slot)

/-- The deterministic leaf-to-root key separates physical-tree slots. -/
theorem canonicalProjectivePostConeTreeSlotOrderKey_injective
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Injective (canonicalProjectivePostConeTreeSlotOrderKey hp hp2) := by
  intro s t hst
  apply (Fintype.equivFin (CanonicalProjectivePostConeTreeSlot hp hp2)).injective
  have hindex := congrArg (fun x => (ofLex x).2) hst
  simpa [canonicalProjectivePostConeTreeSlotOrderKey] using hindex

/-- The linear order induced by the deterministic leaf-to-root key. -/
@[instance_reducible] noncomputable def canonicalProjectivePostConeTreeSlotOrder
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    LinearOrder (CanonicalProjectivePostConeTreeSlot hp hp2) :=
  LinearOrder.lift'
    (canonicalProjectivePostConeTreeSlotOrderKey hp hp2)
    (canonicalProjectivePostConeTreeSlotOrderKey_injective hp hp2)

/-- The finite canonical list of tree slots, deepest targets first. -/
noncomputable def canonicalProjectivePostConeTreeSlotEliminationOrder
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    List (CanonicalProjectivePostConeTreeSlot hp hp2) := by
  letI := canonicalProjectivePostConeTreeSlotOrder hp hp2
  exact Finset.univ.sort (· ≤ ·)

/-- The canonical leaf-to-root list contains no repeated slots. -/
theorem canonicalProjectivePostConeTreeSlotEliminationOrder_nodup
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    (canonicalProjectivePostConeTreeSlotEliminationOrder hp hp2).Nodup := by
  letI := canonicalProjectivePostConeTreeSlotOrder hp hp2
  exact Finset.sort_nodup _ _

/-- Every canonical physical-tree slot appears in the leaf-to-root list. -/
theorem mem_canonicalProjectivePostConeTreeSlotEliminationOrder
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    slot ∈ canonicalProjectivePostConeTreeSlotEliminationOrder hp hp2 := by
  letI := canonicalProjectivePostConeTreeSlotOrder hp hp2
  unfold canonicalProjectivePostConeTreeSlotEliminationOrder
  change slot ∈ Finset.univ.sort (· ≤ ·)
  exact (Finset.mem_sort (s := (Finset.univ :
    Finset (CanonicalProjectivePostConeTreeSlot hp hp2))) (r := (· ≤ ·))).mpr
    (Finset.mem_univ _)

/-- The canonical list is increasing for its deterministic leaf-to-root key. -/
theorem canonicalProjectivePostConeTreeSlotEliminationOrder_pairwise
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    (canonicalProjectivePostConeTreeSlotEliminationOrder hp hp2).Pairwise
      (fun s t =>
        canonicalProjectivePostConeTreeSlotOrderKey hp hp2 s ≤
          canonicalProjectivePostConeTreeSlotOrderKey hp hp2 t) := by
  letI := canonicalProjectivePostConeTreeSlotOrder hp hp2
  unfold canonicalProjectivePostConeTreeSlotEliminationOrder
  change (Finset.univ.sort (· ≤ ·)).Pairwise (fun s t =>
    canonicalProjectivePostConeTreeSlotOrderKey hp hp2 s ≤
      canonicalProjectivePostConeTreeSlotOrderKey hp hp2 t)
  apply (Finset.pairwise_sort (Finset.univ :
    Finset (CanonicalProjectivePostConeTreeSlot hp hp2)) (· ≤ ·)).imp
  intro s t hst
  change canonicalProjectivePostConeTreeSlotOrderKey hp hp2 s ≤
    canonicalProjectivePostConeTreeSlotOrderKey hp hp2 t at hst
  exact hst

/-- Comparing leaf-to-root keys reverses the target-depth inequality. -/
theorem canonicalProjectivePostConeTreeSlotTargetDepth_le_of_orderKey_le
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    {s t : CanonicalProjectivePostConeTreeSlot hp hp2}
    (hkey : canonicalProjectivePostConeTreeSlotOrderKey hp hp2 s ≤
      canonicalProjectivePostConeTreeSlotOrderKey hp hp2 t) :
    canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 t ≤
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 s := by
  rw [Prod.Lex.le_iff] at hkey
  rcases hkey with hkey | hkey
  · exact (OrderDual.toDual_lt_toDual.mp (by
      simpa [canonicalProjectivePostConeTreeSlotOrderKey] using hkey)).le
  · have hdepth : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 s =
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 t := by
      exact OrderDual.toDual.injective (by
        simpa [canonicalProjectivePostConeTreeSlotOrderKey] using hkey.1)
    exact hdepth.ge

/-- Along the canonical list, target depths are non-increasing.  Hence every
strict child depth is eliminated before its parent depth. -/
theorem canonicalProjectivePostConeTreeSlotEliminationOrder_pairwise_depth
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    (canonicalProjectivePostConeTreeSlotEliminationOrder hp hp2).Pairwise
      (fun s t =>
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 t ≤
          canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 s) := by
  exact (canonicalProjectivePostConeTreeSlotEliminationOrder_pairwise hp hp2).imp
    (fun hkey => canonicalProjectivePostConeTreeSlotTargetDepth_le_of_orderKey_le
      hp hp2 hkey)

end

end SystolicGrowth
