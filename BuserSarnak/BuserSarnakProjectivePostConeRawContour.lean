module

public import BuserSarnak.BoundaryWords

@[expose] public section

/-!
# Rooted-tree transport of signed boundary occurrences

`BoundaryWords` constructs the unreduced boundary words and the inclusions
between adjacent tree vertices. This module transports occurrences along
rooted-tree paths, identifies their surviving edge endpoints, and proves the
exact positive and negative multiplicities in the final boundary word.

The existing module name is retained for downstream imports.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

attribute [local instance] rawAllFacesContourRangeFintype

private theorem canonicalProjectivePostConeTreePath_toList_length
    {V : Type*} [Quiver V] {a b : V} (path : Quiver.Path a b) :
    path.toList.length = path.length := by
  induction path with
  | nil => rfl
  | cons path edge ih => simp [Quiver.Path.toList, Quiver.Path.length, ih]

private theorem canonicalProjectivePostConeTreePath_toList_getLast?
    {V : Type*} [Quiver V] {a b : V} (path : Quiver.Path a b) :
    path.toList.getLast? = if path.length = 0 then none else some a := by
  induction path with
  | nil => rfl
  | cons path edge ih =>
      cases path with
      | nil => simp [Quiver.Path.toList, Quiver.Path.length]
      | cons path edge =>
          simpa [Quiver.Path.toList, Quiver.Path.length] using ih

/-- Equal-length initial segments of equal paths end at the same vertex.
This is the list-level path fact used to separate sibling rooted regions. -/
private theorem canonicalProjectivePostConeTreePath_prefix_endpoint_eq
    {V : Type*} [Quiver V] {root q₁ q₂ r : V}
    (prefix₁ : Quiver.Path root q₁) (prefix₂ : Quiver.Path root q₂)
    (tail₁ : Quiver.Path q₁ r) (tail₂ : Quiver.Path q₂ r)
    (hlen : prefix₁.length = prefix₂.length)
    (hpath : prefix₁.comp tail₁ = prefix₂.comp tail₂) : q₁ = q₂ := by
  have hlist : tail₁.toList ++ prefix₁.toList = tail₂.toList ++ prefix₂.toList := by
    simpa only [Quiver.Path.toList_comp] using
      congrArg Quiver.Path.toList hpath
  have htotal := congrArg Quiver.Path.length hpath
  have hsum : prefix₁.length + tail₁.length =
      prefix₂.length + tail₂.length := by
    simpa only [Quiver.Path.length_comp] using htotal
  have htail : tail₁.length = tail₂.length := by omega
  have htailList : tail₁.toList.length = tail₂.toList.length := by
    simpa only [canonicalProjectivePostConeTreePath_toList_length] using htail
  have htailListEq : tail₁.toList = tail₂.toList := by
    have htake := congrArg (fun l => l.take tail₁.toList.length) hlist
    simpa [List.take_append, htailList] using htake
  by_cases hzero : tail₁.length = 0
  · have hzero₂ : tail₂.length = 0 := by omega
    exact (Quiver.Path.eq_of_length_zero tail₁ hzero).trans
      (Quiver.Path.eq_of_length_zero tail₂ hzero₂).symm
  · have hlast := congrArg List.getLast? htailListEq
    have hlast₁ : tail₁.toList.getLast? = some q₁ := by
      rw [canonicalProjectivePostConeTreePath_toList_getLast?]
      simp [hzero]
    have hlast₂ : tail₂.toList.getLast? = some q₂ := by
      rw [canonicalProjectivePostConeTreePath_toList_getLast?]
      have hzero₂ : tail₂.length ≠ 0 := by omega
      simp [hzero₂]
    rw [hlast₁, hlast₂] at hlast
    exact Option.some.inj hlast

/-- A tree vertex `q` is an ancestor of `r` when the unique root-to-`q`
arborescence path is a prefix of the unique root-to-`r` path. This definition
uses the actual path structure, not a comparison of vertex depths. -/
def canonicalProjectivePostConeTreeAncestor
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q r : CanonicalProjectivePostConeTreeVertex hp hp2) : Prop := by
  letI : Quiver.Arborescence
      (projectivePolygonPostConeCanonicalSpanningTree hp hp2) :=
    projectivePolygonPostConeCanonicalSpanningTreeArborescence hp hp2
  exact ∃ tail : Quiver.Path q r,
    (default : Quiver.Path
      (Quiver.root (projectivePolygonPostConeCanonicalSpanningTree hp hp2)) q).comp tail =
      (default : Quiver.Path
        (Quiver.root (projectivePolygonPostConeCanonicalSpanningTree hp hp2)) r)

/-- The ancestor relation is reflexive. -/
theorem canonicalProjectivePostConeTreeAncestor_refl
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : CanonicalProjectivePostConeTreeVertex hp hp2) :
    canonicalProjectivePostConeTreeAncestor hp hp2 q q := by
  letI : Quiver.Arborescence
      (projectivePolygonPostConeCanonicalSpanningTree hp hp2) :=
    projectivePolygonPostConeCanonicalSpanningTreeArborescence hp hp2
  refine ⟨Quiver.Path.nil, ?_⟩
  simp

/-- Prefix witnesses compose, so the ancestor relation is transitive. -/
theorem canonicalProjectivePostConeTreeAncestor_trans
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    {q r s : CanonicalProjectivePostConeTreeVertex hp hp2}
    (hqr : canonicalProjectivePostConeTreeAncestor hp hp2 q r)
    (hrs : canonicalProjectivePostConeTreeAncestor hp hp2 r s) :
    canonicalProjectivePostConeTreeAncestor hp hp2 q s := by
  letI : Quiver.Arborescence
      (projectivePolygonPostConeCanonicalSpanningTree hp hp2) :=
    projectivePolygonPostConeCanonicalSpanningTreeArborescence hp hp2
  rcases hqr with ⟨u, hu⟩
  rcases hrs with ⟨v, hv⟩
  refine ⟨u.comp v, ?_⟩
  calc
    (default : Quiver.Path
      (Quiver.root (projectivePolygonPostConeCanonicalSpanningTree hp hp2)) q).comp
        (u.comp v) =
        (((default : Quiver.Path
          (Quiver.root (projectivePolygonPostConeCanonicalSpanningTree hp hp2)) q).comp u).comp v) :=
      (Quiver.Path.comp_assoc _ _ _).symm
    _ = (default : Quiver.Path
      (Quiver.root (projectivePolygonPostConeCanonicalSpanningTree hp hp2)) r).comp v := by
        rw [hu]
    _ = (default : Quiver.Path
      (Quiver.root (projectivePolygonPostConeCanonicalSpanningTree hp hp2)) s) := hv

/-- The path suffix in an ancestor witness accounts for the difference in
root distances. -/
theorem canonicalProjectivePostConeTreeAncestor_depth_eq
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    {q r : CanonicalProjectivePostConeTreeVertex hp hp2}
    (hqr : canonicalProjectivePostConeTreeAncestor hp hp2 q r) :
    ∃ tail : Quiver.Path q r,
      canonicalProjectivePostConeTreeVertexDepth hp hp2 q + tail.length =
        canonicalProjectivePostConeTreeVertexDepth hp hp2 r := by
  letI : Quiver.Arborescence
      (projectivePolygonPostConeCanonicalSpanningTree hp hp2) :=
    projectivePolygonPostConeCanonicalSpanningTreeArborescence hp hp2
  rcases hqr with ⟨tail, hpath⟩
  refine ⟨tail, ?_⟩
  have hlen := congrArg Quiver.Path.length hpath
  simpa [canonicalProjectivePostConeTreeVertexDepth, Quiver.Path.length_comp] using hlen

/-- Proper descendants have strictly greater root depth. -/
theorem canonicalProjectivePostConeTreeAncestor_depth_lt
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    {q r : CanonicalProjectivePostConeTreeVertex hp hp2}
    (hqr : canonicalProjectivePostConeTreeAncestor hp hp2 q r)
    (hneq : q ≠ r) :
    canonicalProjectivePostConeTreeVertexDepth hp hp2 q <
      canonicalProjectivePostConeTreeVertexDepth hp hp2 r := by
  obtain ⟨tail, hdepth⟩ :=
    canonicalProjectivePostConeTreeAncestor_depth_eq hp hp2 hqr
  have htail : tail.length ≠ 0 := by
    intro hzero
    exact hneq (Quiver.Path.eq_of_length_zero tail hzero)
  have htailPos : 0 < tail.length := Nat.pos_of_ne_zero htail
  omega

/-- A descendant of a strict descendant cannot return to the original
vertex. This is the separation fact between current-face and child origins. -/
theorem canonicalProjectivePostConeTreeAncestor_ne_of_strict_descendant
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    {q r s : CanonicalProjectivePostConeTreeVertex hp hp2}
    (hdepth : canonicalProjectivePostConeTreeVertexDepth hp hp2 q <
      canonicalProjectivePostConeTreeVertexDepth hp hp2 r)
    (hrs : canonicalProjectivePostConeTreeAncestor hp hp2 r s) : s ≠ q := by
  intro hs
  have hrq : canonicalProjectivePostConeTreeAncestor hp hp2 r q := by
    simpa [hs] using hrs
  have hrne : r ≠ q := by
    intro heq
    have hdepthEq := congrArg (canonicalProjectivePostConeTreeVertexDepth hp hp2) heq
    omega
  have hback := canonicalProjectivePostConeTreeAncestor_depth_lt hp hp2 hrq hrne
  omega

/-- The root is an ancestor of every tree vertex. -/
theorem canonicalProjectivePostConeTreeRoot_ancestor
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : CanonicalProjectivePostConeTreeVertex hp hp2) :
    canonicalProjectivePostConeTreeAncestor hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2) q := by
  letI : Quiver.Arborescence
      (projectivePolygonPostConeCanonicalSpanningTree hp hp2) :=
    projectivePolygonPostConeCanonicalSpanningTreeArborescence hp hp2
  let root := Quiver.root (projectivePolygonPostConeCanonicalSpanningTree hp hp2)
  let rootPath : Quiver.Path root root :=
    (Quiver.Arborescence.uniquePath root).default
  have hrootPath : rootPath = Quiver.Path.nil :=
    (Quiver.Arborescence.uniquePath root).uniq Quiver.Path.nil |>.symm
  refine ⟨(default : Quiver.Path root q), ?_⟩
  change rootPath.comp _ = _
  rw [hrootPath]
  exact Quiver.Path.nil_comp _

/-- Every canonical physical-tree slot points from an ancestor vertex to a
strict descendant vertex in the arborescence. -/
theorem canonicalProjectivePostConeTreeAncestor_of_slot
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    canonicalProjectivePostConeTreeAncestor hp hp2 slot.left slot.right := by
  letI : Quiver.Arborescence
      (projectivePolygonPostConeCanonicalSpanningTree hp hp2) :=
    projectivePolygonPostConeCanonicalSpanningTreeArborescence hp hp2
  refine ⟨slot.hom.toPath, ?_⟩
  exact Subsingleton.elim _ _

/-- A proper rooted region splits at its first directed tree edge: every
descendant other than `q` belongs below some immediate successor of `q`. -/
theorem canonicalProjectivePostConeTreeAncestor_exists_firstStep
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    {q r : CanonicalProjectivePostConeTreeVertex hp hp2}
    (hqr : canonicalProjectivePostConeTreeAncestor hp hp2 q r)
    (hneq : q ≠ r) :
    ∃ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      child.left = q ∧
        canonicalProjectivePostConeTreeAncestor hp hp2 child.right r := by
  letI : Quiver.Arborescence
      (projectivePolygonPostConeCanonicalSpanningTree hp hp2) :=
    projectivePolygonPostConeCanonicalSpanningTreeArborescence hp hp2
  rcases hqr with ⟨path, hpath⟩
  have hpathPositive : path.length ≠ 0 := by
    intro hzero
    exact hneq (Quiver.Path.eq_of_length_zero path hzero)
  obtain ⟨c, first, tail, hdecomp, _⟩ :=
    (Quiver.Path.length_ne_zero_iff_eq_comp path).mp hpathPositive
  refine ⟨⟨q, c, first⟩, rfl, ?_⟩
  change canonicalProjectivePostConeTreeAncestor hp hp2 c r
  refine ⟨tail, ?_⟩
  have hrootChild :
      (default : Quiver.Path
        (Quiver.root (projectivePolygonPostConeCanonicalSpanningTree hp hp2)) q).comp
          first.toPath =
        (default : Quiver.Path
          (Quiver.root (projectivePolygonPostConeCanonicalSpanningTree hp hp2)) c) :=
    Subsingleton.elim _ _
  calc
    (default : Quiver.Path
      (Quiver.root (projectivePolygonPostConeCanonicalSpanningTree hp hp2)) c).comp tail =
        ((default : Quiver.Path
          (Quiver.root (projectivePolygonPostConeCanonicalSpanningTree hp hp2)) q).comp
            first.toPath).comp tail := by rw [hrootChild]
    _ = (default : Quiver.Path
        (Quiver.root (projectivePolygonPostConeCanonicalSpanningTree hp hp2)) q).comp
          (first.toPath.comp tail) := Quiver.Path.comp_assoc _ _ _
    _ = (default : Quiver.Path
        (Quiver.root (projectivePolygonPostConeCanonicalSpanningTree hp hp2)) r) := by
          rw [hdecomp] at hpath
          exact hpath

/-- The first tree slot leaving a rooted region is unique. Two candidate
slots with the same parent and with target regions containing a common
descendant must have the same target, by uniqueness of root paths. -/
theorem canonicalProjectivePostConeTreeAncestor_firstStep_unique
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    {q r : CanonicalProjectivePostConeTreeVertex hp hp2}
    (slot₁ slot₂ : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hleft₁ : slot₁.left = q) (hleft₂ : slot₂.left = q)
    (h₁ : canonicalProjectivePostConeTreeAncestor hp hp2 slot₁.right r)
    (h₂ : canonicalProjectivePostConeTreeAncestor hp hp2 slot₂.right r) :
    slot₁ = slot₂ := by
  letI : Quiver.Arborescence
      (projectivePolygonPostConeCanonicalSpanningTree hp hp2) :=
    projectivePolygonPostConeCanonicalSpanningTreeArborescence hp hp2
  let root := Quiver.root (projectivePolygonPostConeCanonicalSpanningTree hp hp2)
  let rootPathQ : Quiver.Path root q := default
  let first₁ : q ⟶ slot₁.right := hleft₁ ▸ slot₁.hom
  let first₂ : q ⟶ slot₂.right := hleft₂ ▸ slot₂.hom
  let prefix₁ : Quiver.Path root slot₁.right := rootPathQ.comp first₁.toPath
  let prefix₂ : Quiver.Path root slot₂.right := rootPathQ.comp first₂.toPath
  rcases h₁ with ⟨tail₁, htail₁⟩
  rcases h₂ with ⟨tail₂, htail₂⟩
  have hpref₁ : prefix₁ = (default : Quiver.Path root slot₁.right) :=
    Subsingleton.elim _ _
  have hpref₂ : prefix₂ = (default : Quiver.Path root slot₂.right) :=
    Subsingleton.elim _ _
  have hfull₁ : prefix₁.comp tail₁ = (default : Quiver.Path root r) := by
    calc
      prefix₁.comp tail₁ = (default : Quiver.Path root slot₁.right).comp tail₁ := by
        rw [hpref₁]
      _ = (default : Quiver.Path root r) := htail₁
  have hfull₂ : prefix₂.comp tail₂ = (default : Quiver.Path root r) := by
    calc
      prefix₂.comp tail₂ = (default : Quiver.Path root slot₂.right).comp tail₂ := by
        rw [hpref₂]
      _ = (default : Quiver.Path root r) := htail₂
  have hlen₁ : prefix₁.length = canonicalProjectivePostConeTreeVertexDepth hp hp2 q + 1 := by
    simp [prefix₁, rootPathQ, first₁, canonicalProjectivePostConeTreeVertexDepth]
  have hlen₂ : prefix₂.length = canonicalProjectivePostConeTreeVertexDepth hp hp2 q + 1 := by
    simp [prefix₂, rootPathQ, first₂, canonicalProjectivePostConeTreeVertexDepth]
  have hlen : prefix₁.length = prefix₂.length := hlen₁.trans hlen₂.symm
  have htarget : slot₁.right = slot₂.right :=
    canonicalProjectivePostConeTreePath_prefix_endpoint_eq
      prefix₁ prefix₂ tail₁ tail₂ hlen (hfull₁.trans hfull₂.symm)
  exact canonicalProjectivePostConeTreeSlot_injective_right hp hp2 htarget

/-- Every proper descendant face determines exactly one first child slot of
the rooted region containing it. -/
theorem canonicalProjectivePostConeTreeAncestor_existsUnique_firstStep
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    {q r : CanonicalProjectivePostConeTreeVertex hp hp2}
    (hqr : canonicalProjectivePostConeTreeAncestor hp hp2 q r)
    (hneq : q ≠ r) :
    ∃! child : CanonicalProjectivePostConeTreeSlot hp hp2,
      child.left = q ∧
        canonicalProjectivePostConeTreeAncestor hp hp2 child.right r := by
  obtain ⟨child, hleft, hchild⟩ :=
    canonicalProjectivePostConeTreeAncestor_exists_firstStep hp hp2 hqr hneq
  refine ⟨child, ⟨hleft, hchild⟩, ?_⟩
  intro other hother
  exact (canonicalProjectivePostConeTreeAncestor_firstStep_unique
    hp hp2 child other hleft hother.1 hchild hother.2).symm

/-- The preferred physical endpoints remain distinct after they are viewed as
vertices of the symmetrized wide subquiver. -/
theorem canonicalProjectivePostConeRawSlotSource_ne_target_vertex
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    (projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) :
        CanonicalProjectivePostConeTreeVertex hp hp2) ≠
    (projectivePolygonPostConeEdgeTarget
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) :
        CanonicalProjectivePostConeTreeVertex hp hp2) := by
  classical
  intro h
  apply canonicalProjectivePostConeTreeSlot_edgeSource_ne_edgeTarget hp hp2 slot
  change projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) =
    projectivePolygonPostConeEdgeTarget
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) at h
  exact h

/-- Source-orientation bit for the left endpoint, in the actual tree-vertex
type. -/
noncomputable def canonicalProjectivePostConeRawSlotLeftSourceBit
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) : Bool := by
  classical
  exact if slot.left = (projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) :
        CanonicalProjectivePostConeTreeVertex hp hp2) then true else false

/-- Source-orientation bit for the right endpoint, in the actual tree-vertex
type. -/
noncomputable def canonicalProjectivePostConeRawSlotRightSourceBit
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) : Bool := by
  classical
  exact if slot.right = (projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) :
        CanonicalProjectivePostConeTreeVertex hp hp2) then true else false

/-- At the first slot leaving the root contour, the left-source bit records
whether the root embedding preserves or reverses signs. -/
theorem canonicalProjectivePostConeRawSlotLeftSourceBit_eq_true_of_left_source
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hsource : slot.left = (projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) :
        CanonicalProjectivePostConeTreeVertex hp hp2)) :
    canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 slot = true := by
  classical
  unfold canonicalProjectivePostConeRawSlotLeftSourceBit
  rw [if_pos hsource]

/-- If a slot starts at the physical target, its left-source bit is false. -/
theorem canonicalProjectivePostConeRawSlotLeftSourceBit_eq_false_of_left_target
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (htarget : slot.left = (projectivePolygonPostConeEdgeTarget
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) :
        CanonicalProjectivePostConeTreeVertex hp hp2)) :
    canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 slot = false := by
  classical
  have hne := canonicalProjectivePostConeRawSlotSource_ne_target_vertex hp hp2 slot
  unfold canonicalProjectivePostConeRawSlotLeftSourceBit
  rw [if_neg (fun hsource => hne (hsource.symm.trans htarget))]

/-- The endpoint indicators are opposite because the physical source and
target are distinct. -/
theorem canonicalProjectivePostConeRawSlotRightSourceBit_eq_not_left
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    canonicalProjectivePostConeRawSlotRightSourceBit hp hp2 slot =
      !canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 slot := by
  classical
  let source : CanonicalProjectivePostConeTreeVertex hp hp2 :=
    projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)
  let target : CanonicalProjectivePostConeTreeVertex hp hp2 :=
    projectivePolygonPostConeEdgeTarget
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)
  have hneq : source ≠ target := by
    intro h
    apply canonicalProjectivePostConeTreeSlot_edgeSource_ne_edgeTarget hp hp2 slot
    change projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) =
      projectivePolygonPostConeEdgeTarget
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) at h
    exact h
  have hendpoints := canonicalProjectivePostConeTreeSlot_endpoints_eq_physicalEndpoints
    hp hp2 slot
  have hendpoints' : (slot.left = source ∧ slot.right = target) ∨
      (slot.left = target ∧ slot.right = source) := by
    simpa [source, target] using hendpoints
  simpa [canonicalProjectivePostConeRawSlotLeftSourceBit,
      canonicalProjectivePostConeRawSlotRightSourceBit, source] using
    (boolEndpointSource_flip source target slot.left slot.right hneq hendpoints')

/-- Across an adjacent splice, the local orientation change is XOR of the
left-source bits of the parent and child slots. -/
theorem canonicalProjectivePostConeRawSlotStepFlip_eq_leftXor
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (parent child : CanonicalProjectivePostConeTreeSlot hp hp2) :
    canonicalProjectivePostConeRawSlotStepFlip hp hp2 parent child =
      boolXor (canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 parent)
        (canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 child) := by
  classical
  have hflip : canonicalProjectivePostConeRawSlotStepFlip hp hp2 parent child =
      (canonicalProjectivePostConeRawSlotRightSourceBit hp hp2 parent ==
        canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 child) := by
    unfold canonicalProjectivePostConeRawSlotStepFlip
      canonicalProjectivePostConeRawSlotRightSourceBit
      canonicalProjectivePostConeRawSlotLeftSourceBit
    by_cases hparent : parent.right =
        (projectivePolygonPostConeEdgeSource
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 parent) :
            CanonicalProjectivePostConeTreeVertex hp hp2)
    · by_cases hchild : child.left =
          (projectivePolygonPostConeEdgeSource
            (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) :
              CanonicalProjectivePostConeTreeVertex hp hp2)
      · rw [if_pos hparent, if_pos hchild]
        simp [hparent]; rfl
      · rw [if_pos hparent, if_neg hchild]
        simp [hparent]; rfl
    · by_cases hchild : child.left =
          (projectivePolygonPostConeEdgeSource
            (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) :
              CanonicalProjectivePostConeTreeVertex hp hp2)
      · rw [if_neg hparent, if_pos hchild]
        simp [hparent, hchild]; rfl
      · rw [if_neg hparent, if_neg hchild]
        simp [hparent, hchild]
  rw [hflip, canonicalProjectivePostConeRawSlotRightSourceBit_eq_not_left]
  cases canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 parent <;>
    cases canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 child <;> rfl

/-- Apply a recorded orientation flip to a signed occurrence. -/
def canonicalProjectivePostConeFlipSignedLetter
    {X : Type*} (flip : Bool) (letter : X × Bool) : X × Bool :=
  (letter.1, if flip then !letter.2 else letter.2)

/-- Adjacent-slot occurrence transport with its exact orientation parity
exposed; the sign change is determined by the two physical orientations. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_child_orientedIndexEmbedding_of_adjacent
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (parent child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hjoin : parent.right = child.left) :
    ∃ f : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).length →
        Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 parent).length,
      Function.Injective f ∧ ∀ i,
        (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 parent).get (f i) =
          canonicalProjectivePostConeFlipSignedLetter
            (canonicalProjectivePostConeRawSlotStepFlip hp hp2 parent child)
            ((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i) := by
  classical
  by_cases hchildSource : child.left = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child)
  · have hstep := canonicalProjectivePostConeRawTreeWordBySlot_child_source_sublist_of_adjacent
      hp hp2 parent child hjoin hchildSource
    by_cases hparentSource : parent.right = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 parent)
    · obtain ⟨e, he⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
        (hstep.1 hparentSource)
      refine ⟨fun i => e (invRevPosition i), ?_, ?_⟩
      · intro i j hij
        exact (invRevPosition_bijective _).1 (e.injective hij)
      · intro i
        have hget := (he (invRevPosition i)).symm.trans (get_invRevPosition _ i)
        have hflip : canonicalProjectivePostConeRawSlotStepFlip hp hp2 parent child = true := by
          unfold canonicalProjectivePostConeRawSlotStepFlip
          rw [if_pos hparentSource, if_pos hchildSource]
        rw [hflip]
        simpa [canonicalProjectivePostConeFlipSignedLetter] using hget
    · obtain ⟨e, he⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
        (hstep.2 hparentSource)
      refine ⟨e, e.injective, ?_⟩
      intro i
      have hget := (he i).symm
      have hflip : canonicalProjectivePostConeRawSlotStepFlip hp hp2 parent child = false := by
        unfold canonicalProjectivePostConeRawSlotStepFlip
        rw [if_neg hparentSource, if_pos hchildSource]
      rw [hflip]
      simpa [canonicalProjectivePostConeFlipSignedLetter] using hget
  · have hchildTarget : child.left = projectivePolygonPostConeEdgeTarget
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) := by
      rcases canonicalProjectivePostConeTreeSlot_left_eq_physicalSource_or_target
          hp hp2 child with hsource | htarget
      · exact (hchildSource hsource).elim
      · exact htarget
    have hstep := canonicalProjectivePostConeRawTreeWordBySlot_child_target_sublist_of_adjacent
      hp hp2 parent child hjoin hchildTarget
    by_cases hparentSource : parent.right = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 parent)
    · obtain ⟨e, he⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
        (hstep.1 hparentSource)
      refine ⟨e, e.injective, ?_⟩
      intro i
      have hget := (he i).symm
      have hflip : canonicalProjectivePostConeRawSlotStepFlip hp hp2 parent child = false := by
        unfold canonicalProjectivePostConeRawSlotStepFlip
        rw [if_pos hparentSource, if_neg hchildSource]
      rw [hflip]
      simpa [canonicalProjectivePostConeFlipSignedLetter] using hget
    · obtain ⟨e, he⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
        (hstep.2 hparentSource)
      refine ⟨fun i => e (invRevPosition i), ?_, ?_⟩
      · intro i j hij
        exact (invRevPosition_bijective _).1 (e.injective hij)
      · intro i
        have hget := (he (invRevPosition i)).symm.trans (get_invRevPosition _ i)
        have hflip : canonicalProjectivePostConeRawSlotStepFlip hp hp2 parent child = true := by
          unfold canonicalProjectivePostConeRawSlotStepFlip
          rw [if_neg hparentSource, if_neg hchildSource]
        rw [hflip]
        simpa [canonicalProjectivePostConeFlipSignedLetter] using hget

/-- Every slot word can be transported along its canonically determined
parent chain to a literal occurrence embedding in the root contour.  The
chain is not an extra input: at each non-root face it uses the unique
incoming arrow of the canonical arborescence.  Its physical orientations
determine whether all signs are preserved or all flipped. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_root_indexEmbedding
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (child : CanonicalProjectivePostConeTreeSlot hp hp2) :
    ∃ f : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).length →
        Fin (canonicalProjectivePostConeRawRootContour hp hp2).length,
      Function.Injective f ∧
        ((∀ i, (canonicalProjectivePostConeRawRootContour hp hp2).get (f i) =
          (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i) ∨
        (∀ i, (canonicalProjectivePostConeRawRootContour hp hp2).get (f i) =
          (((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).1,
            !((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).2))) := by
  let vertexDepth := canonicalProjectivePostConeTreeVertexDepth hp hp2
  have descend : ∀ n (q : projectivePolygonPostConeCanonicalSpanningTree hp hp2)
      (hdepth : vertexDepth q = n)
      (child : CanonicalProjectivePostConeTreeSlot hp hp2) (hleft : child.left = q),
      ∃ f : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).length →
          Fin (canonicalProjectivePostConeRawRootContour hp hp2).length,
        Function.Injective f ∧
          ((∀ i, (canonicalProjectivePostConeRawRootContour hp hp2).get (f i) =
            (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i) ∨
          (∀ i, (canonicalProjectivePostConeRawRootContour hp hp2).get (f i) =
            (((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).1,
              !((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).2))) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro q hdepth child hleft
      by_cases hroot : q = canonicalProjectivePostConeTreeRoot hp hp2
      · have hleftRoot : child.left = canonicalProjectivePostConeTreeRoot hp hp2 :=
          hleft.trans hroot
        rcases canonicalProjectivePostConeTreeSlot_left_eq_physicalSource_or_target
            hp hp2 child with hsource | htarget
        · obtain ⟨f, hf, hget⟩ :=
            canonicalProjectivePostConeRawRootContour_child_source_indexEmbedding
              hp hp2 child hleftRoot hsource
          exact ⟨f, hf, Or.inl hget⟩
        · obtain ⟨f, hf, hget⟩ :=
            canonicalProjectivePostConeRawRootContour_child_target_indexEmbedding
              hp hp2 child hleftRoot htarget
          exact ⟨f, hf, Or.inr hget⟩
      · let parent := canonicalProjectivePostConeTreeIncomingSlot hp hp2 q hroot
        have hparentRight : parent.right = q :=
          canonicalProjectivePostConeTreeIncomingSlot_right hp hp2 q hroot
        have hjoin : parent.right = child.left := hparentRight.trans hleft.symm
        have hparentDepth : vertexDepth parent.left < n := by
          have hstep := canonicalProjectivePostConeTreeSlot_depth_succ hp hp2 parent
          change canonicalProjectivePostConeTreeSlotSourceDepth hp hp2 parent + 1 =
            canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent at hstep
          have htarget : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent = n := by
            change vertexDepth parent.right = n
            rw [hparentRight, hdepth]
          have hsource : canonicalProjectivePostConeTreeSlotSourceDepth hp hp2 parent =
              vertexDepth parent.left := rfl
          rw [hsource, htarget] at hstep
          omega
        obtain ⟨f, hf, hlocal⟩ :=
          canonicalProjectivePostConeRawTreeWordBySlot_child_indexEmbedding_of_adjacent
            hp hp2 parent child hjoin
        obtain ⟨g, hg, hglobal⟩ := ih (vertexDepth parent.left) hparentDepth
            parent.left rfl parent rfl
        refine ⟨g ∘ f, hg.comp hf, ?_⟩
        rcases hlocal with hlocal | hlocal <;>
          rcases hglobal with hglobal | hglobal
        · left
          intro i
          rw [Function.comp_apply, hglobal, hlocal]
        · right
          intro i
          change (canonicalProjectivePostConeRawRootContour hp hp2).get (g (f i)) = _
          calc
            _ = (((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 parent).get (f i)).1,
                  !((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 parent).get (f i)).2) :=
              hglobal (f i)
            _ = (((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).1,
                  !((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).2) :=
              congrArg (fun a : CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool =>
                (a.1, !a.2)) (hlocal i)
        · right
          intro i
          change (canonicalProjectivePostConeRawRootContour hp hp2).get (g (f i)) = _
          calc
            _ = (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 parent).get (f i) :=
              hglobal (f i)
            _ = (((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).1,
                  !((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).2) :=
              hlocal i
        · left
          intro i
          change (canonicalProjectivePostConeRawRootContour hp hp2).get (g (f i)) = _
          calc
            _ = (((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 parent).get (f i)).1,
                  !((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 parent).get (f i)).2) :=
              hglobal (f i)
            _ = (((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).1,
                  !(!((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).2)) :=
              congrArg (fun a : CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool =>
                (a.1, !a.2)) (hlocal i)
            _ = (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i := by
              cases hval : (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i with
              | mk a b => cases b <;> rfl
  exact descend (canonicalProjectivePostConeTreeVertexDepth hp hp2 child.left)
    child.left rfl child rfl

/-- Boolean composition law for successive orientation changes. -/
def canonicalProjectivePostConeRawBoolXor (a b : Bool) : Bool :=
  if a then !b else b

theorem canonicalProjectivePostConeFlipSignedLetter_comp
    {X : Type*} (a b : Bool) (letter : X × Bool) :
    canonicalProjectivePostConeFlipSignedLetter a
        (canonicalProjectivePostConeFlipSignedLetter b letter) =
      canonicalProjectivePostConeFlipSignedLetter
        (canonicalProjectivePostConeRawBoolXor a b) letter := by
  cases a <;> cases b <;> cases letter with
  | mk x sign => cases sign <;> rfl

/-- The canonical root-path embedding has a completely determined parity:
its total sign flip is the complement of the final slot's left-source bit.
The induction follows unique incoming slots and composes each local XOR. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_root_embedding_parity
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (child : CanonicalProjectivePostConeTreeSlot hp hp2) :
    ∃ (f : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).length →
        Fin (canonicalProjectivePostConeRawRootContour hp hp2).length) (flip : Bool),
      Function.Injective f ∧
        (∀ i, (canonicalProjectivePostConeRawRootContour hp hp2).get (f i) =
          canonicalProjectivePostConeFlipSignedLetter flip
            ((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i)) ∧
        flip = !canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 child := by
  let vertexDepth := canonicalProjectivePostConeTreeVertexDepth hp hp2
  have descend : ∀ n (q : projectivePolygonPostConeCanonicalSpanningTree hp hp2)
      (hdepth : vertexDepth q = n)
      (child : CanonicalProjectivePostConeTreeSlot hp hp2) (hleft : child.left = q),
      ∃ (f : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).length →
          Fin (canonicalProjectivePostConeRawRootContour hp hp2).length) (flip : Bool),
        Function.Injective f ∧
          (∀ i, (canonicalProjectivePostConeRawRootContour hp hp2).get (f i) =
            canonicalProjectivePostConeFlipSignedLetter flip
              ((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i)) ∧
          flip = !canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 child := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro q hdepth child hleft
      by_cases hroot : q = canonicalProjectivePostConeTreeRoot hp hp2
      · have hleftRoot : child.left = canonicalProjectivePostConeTreeRoot hp hp2 :=
          hleft.trans hroot
        rcases canonicalProjectivePostConeTreeSlot_left_eq_physicalSource_or_target
            hp hp2 child with hsource | htarget
        · obtain ⟨f, hf, hget⟩ :=
            canonicalProjectivePostConeRawRootContour_child_source_indexEmbedding
              hp hp2 child hleftRoot hsource
          have hbit := canonicalProjectivePostConeRawSlotLeftSourceBit_eq_true_of_left_source
            hp hp2 child hsource
          refine ⟨f, false, hf, ?_, ?_⟩
          · intro i
            simpa [canonicalProjectivePostConeFlipSignedLetter] using hget i
          · rw [hbit]
            rfl
        · obtain ⟨f, hf, hget⟩ :=
            canonicalProjectivePostConeRawRootContour_child_target_indexEmbedding
              hp hp2 child hleftRoot htarget
          have hbit := canonicalProjectivePostConeRawSlotLeftSourceBit_eq_false_of_left_target
            hp hp2 child htarget
          refine ⟨f, true, hf, ?_, ?_⟩
          · intro i
            simpa [canonicalProjectivePostConeFlipSignedLetter] using hget i
          · rw [hbit]
            rfl
      · let parent := canonicalProjectivePostConeTreeIncomingSlot hp hp2 q hroot
        have hparentRight : parent.right = q :=
          canonicalProjectivePostConeTreeIncomingSlot_right hp hp2 q hroot
        have hjoin : parent.right = child.left := hparentRight.trans hleft.symm
        have hparentDepth : vertexDepth parent.left < n := by
          have hstep := canonicalProjectivePostConeTreeSlot_depth_succ hp hp2 parent
          change canonicalProjectivePostConeTreeSlotSourceDepth hp hp2 parent + 1 =
            canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent at hstep
          have htarget : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent = n := by
            change vertexDepth parent.right = n
            rw [hparentRight, hdepth]
          have hsource : canonicalProjectivePostConeTreeSlotSourceDepth hp hp2 parent =
              vertexDepth parent.left := rfl
          rw [hsource, htarget] at hstep
          omega
        obtain ⟨f, hf, hlocal⟩ :=
          canonicalProjectivePostConeRawTreeWordBySlot_child_orientedIndexEmbedding_of_adjacent
            hp hp2 parent child hjoin
        obtain ⟨g, flipGlobal, hg, hglobal, hglobalParity⟩ :=
          ih (vertexDepth parent.left) hparentDepth parent.left rfl parent rfl
        let flipTotal := canonicalProjectivePostConeRawBoolXor flipGlobal
          (canonicalProjectivePostConeRawSlotStepFlip hp hp2 parent child)
        refine ⟨g ∘ f, flipTotal, hg.comp hf, ?_, ?_⟩
        · intro i
          rw [Function.comp_apply]
          calc
            (canonicalProjectivePostConeRawRootContour hp hp2).get (g (f i)) =
                canonicalProjectivePostConeFlipSignedLetter flipGlobal
                  ((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 parent).get (f i)) :=
              hglobal (f i)
            _ = canonicalProjectivePostConeFlipSignedLetter flipGlobal
                  (canonicalProjectivePostConeFlipSignedLetter
                    (canonicalProjectivePostConeRawSlotStepFlip hp hp2 parent child)
                    ((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i)) :=
              congrArg (canonicalProjectivePostConeFlipSignedLetter flipGlobal) (hlocal i)
            _ = canonicalProjectivePostConeFlipSignedLetter flipTotal
                  ((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i) := by
              simpa [flipTotal] using
                (canonicalProjectivePostConeFlipSignedLetter_comp flipGlobal
                  (canonicalProjectivePostConeRawSlotStepFlip hp hp2 parent child)
                  ((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i))
        · change canonicalProjectivePostConeRawBoolXor flipGlobal
              (canonicalProjectivePostConeRawSlotStepFlip hp hp2 parent child) =
            !canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 child
          rw [hglobalParity, canonicalProjectivePostConeRawSlotStepFlip_eq_leftXor]
          cases canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 parent <;>
            cases canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 child <;> rfl
  exact descend (canonicalProjectivePostConeTreeVertexDepth hp hp2 child.left)
    child.left rfl child rfl

/-- The composed root-path embedding exposes its total orientation parity
as a Boolean, so it can be compared across the source and target paths of a
paired physical edge. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_root_orientedIndexEmbedding
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (child : CanonicalProjectivePostConeTreeSlot hp hp2) :
    ∃ (f : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).length →
        Fin (canonicalProjectivePostConeRawRootContour hp hp2).length) (flip : Bool),
      Function.Injective f ∧ ∀ i,
        (canonicalProjectivePostConeRawRootContour hp hp2).get (f i) =
          canonicalProjectivePostConeFlipSignedLetter flip
            ((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i) := by
  obtain ⟨f, flip, hf, htransport, _hparity⟩ :=
    canonicalProjectivePostConeRawTreeWordBySlot_root_embedding_parity hp hp2 child
  exact ⟨f, flip, hf, htransport⟩

/-- Transport a literal slot occurrence to a root position while retaining the
exact parity formula for its sign, rather than only a preserved/flipped
disjunction. -/
theorem canonicalProjectivePostConeRawRootContour_exists_exact_transport_of_mem_slot
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (letter : CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool)
    (hletter : letter ∈ canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) :
    ∃ (flip : Bool),
      flip = !canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 child ∧
      ∃ i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length,
        (canonicalProjectivePostConeRawRootContour hp hp2).get i =
          canonicalProjectivePostConeFlipSignedLetter flip letter := by
  obtain ⟨f, flip, hf, htransport, hparity⟩ :=
    canonicalProjectivePostConeRawTreeWordBySlot_root_embedding_parity hp hp2 child
  rcases List.mem_iff_getElem.mp hletter with ⟨i, hi, hget⟩
  let i' : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).length :=
    ⟨i, hi⟩
  refine ⟨flip, hparity, f i', ?_⟩
  calc
    (canonicalProjectivePostConeRawRootContour hp hp2).get (f i') =
        canonicalProjectivePostConeFlipSignedLetter flip
          ((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i') :=
      htransport i'
    _ = canonicalProjectivePostConeFlipSignedLetter flip letter :=
      congrArg (canonicalProjectivePostConeFlipSignedLetter flip)
        (by simpa [i'] using hget)

/-- A retained edge's source occurrence in a non-root incoming slot is
transported to a positive literal in the root contour. -/
theorem canonicalProjectivePostConeRawRootContour_exists_positive_of_incoming_source
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : projectivePolygonPostConeCanonicalSpanningTree hp hp2)
    (hq : q ≠ canonicalProjectivePostConeTreeRoot hp hp2)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2)
    (hsource : projectivePolygonPostConeEdgeSource z.1 = q) :
    ∃ i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length,
      (canonicalProjectivePostConeRawRootContour hp hp2).get i = (z, true) := by
  let slot := canonicalProjectivePostConeTreeIncomingSlot hp hp2 q hq
  have hslot := canonicalProjectivePostConeRawIncomingSlot_mem_source
    hp hp2 q hq z hsource
  by_cases horient : slot.right = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)
  · have hmem := hslot.1 (by simpa [slot] using horient)
    obtain ⟨flip, hparity, i, htransport⟩ :=
      canonicalProjectivePostConeRawRootContour_exists_exact_transport_of_mem_slot
        hp hp2 slot (z, false) hmem
    have hright : canonicalProjectivePostConeRawSlotRightSourceBit hp hp2 slot = true := by
      unfold canonicalProjectivePostConeRawSlotRightSourceBit
      rw [if_pos horient]
    have hflip : flip = true := by
      calc
        flip = !canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 slot := hparity
        _ = canonicalProjectivePostConeRawSlotRightSourceBit hp hp2 slot :=
          (canonicalProjectivePostConeRawSlotRightSourceBit_eq_not_left hp hp2 slot).symm
        _ = true := hright
    refine ⟨i, ?_⟩
    calc
      (canonicalProjectivePostConeRawRootContour hp hp2).get i =
          canonicalProjectivePostConeFlipSignedLetter flip (z, false) := htransport
      _ = (z, true) := by rw [hflip]; rfl
  · have hmem := hslot.2 (by simpa [slot] using horient)
    obtain ⟨flip, hparity, i, htransport⟩ :=
      canonicalProjectivePostConeRawRootContour_exists_exact_transport_of_mem_slot
        hp hp2 slot (z, true) hmem
    have hright : canonicalProjectivePostConeRawSlotRightSourceBit hp hp2 slot = false := by
      unfold canonicalProjectivePostConeRawSlotRightSourceBit
      rw [if_neg horient]
    have hflip : flip = false := by
      calc
        flip = !canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 slot := hparity
        _ = canonicalProjectivePostConeRawSlotRightSourceBit hp hp2 slot :=
          (canonicalProjectivePostConeRawSlotRightSourceBit_eq_not_left hp hp2 slot).symm
        _ = false := hright
    refine ⟨i, ?_⟩
    calc
      (canonicalProjectivePostConeRawRootContour hp hp2).get i =
          canonicalProjectivePostConeFlipSignedLetter flip (z, true) := htransport
      _ = (z, true) := by rw [hflip]; rfl

/-- A retained edge's target occurrence in a non-root incoming slot is
transported to a negative literal in the root contour. -/
theorem canonicalProjectivePostConeRawRootContour_exists_negative_of_incoming_target
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : projectivePolygonPostConeCanonicalSpanningTree hp hp2)
    (hq : q ≠ canonicalProjectivePostConeTreeRoot hp hp2)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2)
    (htarget : projectivePolygonPostConeEdgeTarget z.1 = q) :
    ∃ i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length,
      (canonicalProjectivePostConeRawRootContour hp hp2).get i = (z, false) := by
  let slot := canonicalProjectivePostConeTreeIncomingSlot hp hp2 q hq
  have hslot := canonicalProjectivePostConeRawIncomingSlot_mem_target
    hp hp2 q hq z htarget
  by_cases horient : slot.right = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)
  · have hmem := hslot.1 (by simpa [slot] using horient)
    obtain ⟨flip, hparity, i, htransport⟩ :=
      canonicalProjectivePostConeRawRootContour_exists_exact_transport_of_mem_slot
        hp hp2 slot (z, true) hmem
    have hright : canonicalProjectivePostConeRawSlotRightSourceBit hp hp2 slot = true := by
      unfold canonicalProjectivePostConeRawSlotRightSourceBit
      rw [if_pos horient]
    have hflip : flip = true := by
      calc
        flip = !canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 slot := hparity
        _ = canonicalProjectivePostConeRawSlotRightSourceBit hp hp2 slot :=
          (canonicalProjectivePostConeRawSlotRightSourceBit_eq_not_left hp hp2 slot).symm
        _ = true := hright
    refine ⟨i, ?_⟩
    calc
      (canonicalProjectivePostConeRawRootContour hp hp2).get i =
          canonicalProjectivePostConeFlipSignedLetter flip (z, true) := htransport
      _ = (z, false) := by rw [hflip]; rfl
  · have hmem := hslot.2 (by simpa [slot] using horient)
    obtain ⟨flip, hparity, i, htransport⟩ :=
      canonicalProjectivePostConeRawRootContour_exists_exact_transport_of_mem_slot
        hp hp2 slot (z, false) hmem
    have hright : canonicalProjectivePostConeRawSlotRightSourceBit hp hp2 slot = false := by
      unfold canonicalProjectivePostConeRawSlotRightSourceBit
      rw [if_neg horient]
    have hflip : flip = false := by
      calc
        flip = !canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 slot := hparity
        _ = canonicalProjectivePostConeRawSlotRightSourceBit hp hp2 slot :=
          (canonicalProjectivePostConeRawSlotRightSourceBit_eq_not_left hp hp2 slot).symm
        _ = false := hright
    refine ⟨i, ?_⟩
    calc
      (canonicalProjectivePostConeRawRootContour hp hp2).get i =
          canonicalProjectivePostConeFlipSignedLetter flip (z, false) := htransport
      _ = (z, false) := by rw [hflip]; rfl

/-- A literal signed occurrence in a slot word survives at a concrete
position of the contracted root contour, with its orientation either
preserved or flipped uniformly along the unique tree path.  This is the
membership-level form of the root-position embedding, suitable for assembling
the positive and negative occurrence maps of a Wicks certificate. -/
theorem canonicalProjectivePostConeRawRootContour_exists_signed_occurrence_of_mem_slot
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (letter : CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool)
    (hletter : letter ∈ canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) :
    (∃ i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length,
      (canonicalProjectivePostConeRawRootContour hp hp2).get i = letter) ∨
    (∃ i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length,
      (canonicalProjectivePostConeRawRootContour hp hp2).get i =
        (letter.1, !letter.2)) := by
  rcases List.mem_iff_getElem.mp hletter with ⟨i, hi, hget⟩
  let i' : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).length :=
    ⟨i, hi⟩
  obtain ⟨f, hf, htransport⟩ :=
    canonicalProjectivePostConeRawTreeWordBySlot_root_indexEmbedding hp hp2 child
  rcases htransport with hsame | hflip
  · left
    refine ⟨f i', ?_⟩
    rw [hsame]
    simpa [i'] using hget
  · right
    refine ⟨f i', ?_⟩
    rw [hflip]
    simpa [i'] using congrArg (fun a : CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool =>
      (a.1, !a.2)) hget

/-- Every retained final generator has a literal occurrence in the contracted
root contour.  For a generator based at a non-root source face, its occurrence
is first found in that face's unique incoming-slot word and then transported
along the composed root-position embedding.  This proves support coverage;
the exact positive/negative multiplicity and one-orbit Wicks conditions
remain separate obligations. -/
theorem canonicalProjectivePostConeRawRootContour_exists_occurrence_of_generator
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2) :
    ∃ i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length,
      ((canonicalProjectivePostConeRawRootContour hp hp2).get i).1 = z := by
  let q := projectivePolygonPostConeEdgeSource z.1
  by_cases hroot : q = canonicalProjectivePostConeTreeRoot hp hp2
  · have hrootState : (projectivePolygonPostConeEdgeSource z.1).state =
        (canonicalProjectivePostConeTreeRoot hp hp2).state := by
      exact congrArg ProjectivePolygonPostConeFace.state hroot
    obtain ⟨i, hi⟩ :=
      canonicalProjectivePostConeRawRootContour_exists_positive_occurrence_of_root_source
        hp hp2 z hrootState
    exact ⟨i, congrArg Prod.fst hi⟩
  · let slot := canonicalProjectivePostConeTreeIncomingSlot hp hp2 q hroot
    have hslot := canonicalProjectivePostConeRawIncomingSlot_mem_source
      hp hp2 q hroot z rfl
    have hmem : (z, true) ∈ canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot ∨
        (z, false) ∈ canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot := by
      by_cases horient : slot.right = projectivePolygonPostConeEdgeSource
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)
      · exact Or.inr (hslot.1 horient)
      · exact Or.inl (hslot.2 horient)
    rcases hmem with hmem | hmem
    · rcases canonicalProjectivePostConeRawRootContour_exists_signed_occurrence_of_mem_slot
        hp hp2 slot (z, true) hmem with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact ⟨i, congrArg Prod.fst hi⟩
      · exact ⟨i, congrArg Prod.fst hi⟩
    · rcases canonicalProjectivePostConeRawRootContour_exists_signed_occurrence_of_mem_slot
        hp hp2 slot (z, false) hmem with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact ⟨i, congrArg Prod.fst hi⟩
      · exact ⟨i, congrArg Prod.fst hi⟩

/-- The positive source occurrence of every retained generator survives at a
literal root-contour position. The root case is already a root boundary term;
the non-root case uses the exact path-parity transport. -/
theorem canonicalProjectivePostConeRawRootContour_exists_positive_occurrence_of_generator
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2) :
    ∃ i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length,
      (canonicalProjectivePostConeRawRootContour hp hp2).get i = (z, true) := by
  let q := projectivePolygonPostConeEdgeSource z.1
  by_cases hroot : q = canonicalProjectivePostConeTreeRoot hp hp2
  · have hrootState : (projectivePolygonPostConeEdgeSource z.1).state =
        (canonicalProjectivePostConeTreeRoot hp hp2).state :=
      congrArg ProjectivePolygonPostConeFace.state hroot
    exact canonicalProjectivePostConeRawRootContour_exists_positive_occurrence_of_root_source
      hp hp2 z hrootState
  · exact canonicalProjectivePostConeRawRootContour_exists_positive_of_incoming_source
      hp hp2 q hroot z rfl

/-- The negative target occurrence of every retained generator survives at a
literal root-contour position. Its sign is opposite to the source occurrence
because the source-indicator XOR along each root path telescopes. -/
theorem canonicalProjectivePostConeRawRootContour_exists_negative_occurrence_of_generator
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2) :
    ∃ i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length,
      (canonicalProjectivePostConeRawRootContour hp hp2).get i = (z, false) := by
  let q := projectivePolygonPostConeEdgeTarget z.1
  by_cases hroot : q = canonicalProjectivePostConeTreeRoot hp hp2
  · have hrootState : (projectivePolygonPostConeEdgeTarget z.1).state =
        (canonicalProjectivePostConeTreeRoot hp hp2).state :=
      congrArg ProjectivePolygonPostConeFace.state hroot
    exact canonicalProjectivePostConeRawRootContour_exists_negative_occurrence_of_root_target
      hp hp2 z hrootState
  · exact canonicalProjectivePostConeRawRootContour_exists_negative_of_incoming_target
      hp hp2 q hroot z rfl

/-- Choose one literal root position for each signed generator. The positive
and negative choices form a single injective map, so the root contour contains
at least two distinct positions per retained generator. -/
noncomputable def canonicalProjectivePostConeRawRootContourPositivePosition
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2) :
    Fin (canonicalProjectivePostConeRawRootContour hp hp2).length :=
  Classical.choose
    (canonicalProjectivePostConeRawRootContour_exists_positive_occurrence_of_generator
      hp hp2 z)

theorem canonicalProjectivePostConeRawRootContourPositivePosition_spec
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2) :
    (canonicalProjectivePostConeRawRootContour hp hp2).get
      (canonicalProjectivePostConeRawRootContourPositivePosition hp hp2 z) = (z, true) :=
  Classical.choose_spec
    (canonicalProjectivePostConeRawRootContour_exists_positive_occurrence_of_generator
      hp hp2 z)

noncomputable def canonicalProjectivePostConeRawRootContourNegativePosition
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2) :
    Fin (canonicalProjectivePostConeRawRootContour hp hp2).length :=
  Classical.choose
    (canonicalProjectivePostConeRawRootContour_exists_negative_occurrence_of_generator
      hp hp2 z)

theorem canonicalProjectivePostConeRawRootContourNegativePosition_spec
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2) :
    (canonicalProjectivePostConeRawRootContour hp hp2).get
      (canonicalProjectivePostConeRawRootContourNegativePosition hp hp2 z) = (z, false) :=
  Classical.choose_spec
    (canonicalProjectivePostConeRawRootContour_exists_negative_occurrence_of_generator
      hp hp2 z)

noncomputable def canonicalProjectivePostConeRawRootContour_signedPosition
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) →
      Fin (canonicalProjectivePostConeRawRootContour hp hp2).length := by
  classical
  exact fun s => match s with
    | Sum.inl z => canonicalProjectivePostConeRawRootContourPositivePosition hp hp2 z
    | Sum.inr z => canonicalProjectivePostConeRawRootContourNegativePosition hp hp2 z

/-- A retained physical dart is a particular endpoint occurrence of a final
generator. The two constructors distinguish its physical source dart from
its physical target dart, even when recording both under the same generator
label. This is the finite occurrence type whose positions must be shown to
exhaust the contracted root contour. -/
abbrev CanonicalProjectivePostConeSurvivingDart
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :=
  Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
    (CanonicalProjectivePostConeFinalGenerator hp hp2)

/-- The final edge label carried by a physical dart. -/
def canonicalProjectivePostConeSurvivingDartGenerator
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2) :=
  d.elim id id

/-- The face containing a physical dart before the tree contraction. -/
def canonicalProjectivePostConeSurvivingDartFace
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2) :
    ProjectivePolygonPostConeFace p :=
  d.elim
    (fun z => projectivePolygonPostConeEdgeSource z.1)
    (fun z => projectivePolygonPostConeEdgeTarget z.1)

/-- The polygon side representing a physical dart in its face's boundary. -/
def canonicalProjectivePostConeSurvivingDartSide
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2) :
    ProjectivePolygonSide :=
  d.elim (fun z => projectivePolygonPostConeEdgeSide z.1)
    (fun z => projectivePolygonPostConeEdgeTargetSide z.1)

/-- The orientation bit belonging to a physical dart's uncontracted
boundary occurrence. -/
def canonicalProjectivePostConeSurvivingDartPositive
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2) : Bool :=
  d.elim (fun _ => true) (fun _ => false)

/-- At the current face, a non-pivot physical dart is represented by exactly
its signed singleton in the raw slot contour. This identifies the local
position before the separate concatenation-offset problem. -/
theorem canonicalProjectivePostConeSurvivingDart_current_rawTerm
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2)
    (hface : canonicalProjectivePostConeSurvivingDartFace hp hp2 d =
      (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p))
    (hside : canonicalProjectivePostConeSurvivingDartSide hp hp2 d ≠
      canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) :
    canonicalProjectivePostConeRawContourTerm hp hp2 slot ih
      (canonicalProjectivePostConeSurvivingDartSide hp hp2 d) =
        [(canonicalProjectivePostConeSurvivingDartGenerator hp hp2 d,
          canonicalProjectivePostConeSurvivingDartPositive hp hp2 d)] := by
  cases d with
  | inl z =>
      have hzeta : (⟨z.1, z.2⟩ : CanonicalProjectivePostConeFinalGenerator hp hp2) = z :=
        Subtype.ext rfl
      change projectivePolygonPostConeEdgeSource z.1 = _ at hface
      change projectivePolygonPostConeEdgeSide z.1 ≠ _ at hside
      rw [← hzeta]
      exact canonicalProjectivePostConeRawContourTerm_eq_source_letter
        hp hp2 slot ih z.1 z.2 hface.symm hside
  | inr z =>
      have hzeta : (⟨z.1, z.2⟩ : CanonicalProjectivePostConeFinalGenerator hp hp2) = z :=
        Subtype.ext rfl
      change projectivePolygonPostConeEdgeTarget z.1 = _ at hface
      change projectivePolygonPostConeEdgeTargetSide z.1 ≠ _ at hside
      rw [← hzeta]
      exact canonicalProjectivePostConeRawContourTerm_eq_target_letter
        hp hp2 slot ih z.1 z.2 hface.symm hside

/-- A positive final-source case in a raw side term is the corresponding
physical source dart at the current face and side. -/
theorem canonicalProjectivePostConeSurvivingDart_of_finalSourceTermCase
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (s : ProjectivePolygonSide) (z : CanonicalProjectiveConeKeptSymbol p)
    (hsource :
      (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
          projectivePolygonPostConeEdgeSource z ∧
        s = projectivePolygonPostConeEdgeSide z ∧
        canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s =
          FreeGroup.of z)
    (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
    ∃ d : CanonicalProjectivePostConeSurvivingDart hp hp2,
      canonicalProjectivePostConeSurvivingDartFace hp hp2 d =
          (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) ∧
        canonicalProjectivePostConeSurvivingDartSide hp hp2 d = s ∧
        canonicalProjectivePostConeSurvivingDartGenerator hp hp2 d = ⟨z, hz⟩ ∧
        canonicalProjectivePostConeSurvivingDartPositive hp hp2 d = true := by
  refine ⟨Sum.inl ⟨z, hz⟩, ?_, ?_, rfl, rfl⟩
  · exact hsource.1.symm
  · exact hsource.2.1.symm

/-- A negative final-target case in a raw side term is the corresponding
physical target dart at the current face and side. -/
theorem canonicalProjectivePostConeSurvivingDart_of_finalTargetTermCase
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (s : ProjectivePolygonSide) (z : CanonicalProjectiveConeKeptSymbol p)
    (htarget :
      (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
          projectivePolygonPostConeEdgeTarget z ∧
        s = projectivePolygonPostConeEdgeTargetSide z ∧
        canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s =
          (FreeGroup.of z)⁻¹)
    (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
    ∃ d : CanonicalProjectivePostConeSurvivingDart hp hp2,
      canonicalProjectivePostConeSurvivingDartFace hp hp2 d =
          (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) ∧
        canonicalProjectivePostConeSurvivingDartSide hp hp2 d = s ∧
        canonicalProjectivePostConeSurvivingDartGenerator hp hp2 d = ⟨z, hz⟩ ∧
        canonicalProjectivePostConeSurvivingDartPositive hp hp2 d = false := by
  refine ⟨Sum.inr ⟨z, hz⟩, ?_, ?_, rfl, rfl⟩
  · exact htarget.1.symm
  · exact htarget.2.1.symm

/-- The classifier selected at the current face-side occurrence of a
surviving source dart is its unique final-source case. The physical endpoint
and side determine the original boundary carrier, so this identification is
independent of the recursively substituted child word. -/
theorem canonicalProjectivePostConeRawContourTermCase_eq_finalSource_of_dart
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2)
    (hface : projectivePolygonPostConeEdgeSource z.1 =
      (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p))
    (hside : projectivePolygonPostConeEdgeSide z.1 = s) :
    ∃ hterm : canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s =
        FreeGroup.of z.1,
      canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs =
        .finalSource z.1 ⟨hface.symm, hside.symm, hterm⟩ z.2 := by
  let hstate : (projectivePolygonPostConeEdgeSource z.1).state = slot.right.state :=
    congrArg ProjectivePolygonPostConeFace.state hface
  have hterm : canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
      s = FreeGroup.of z.1 := by
    rw [← hside, ← hstate]
    exact canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq z.1
  refine ⟨hterm, ?_⟩
  exact canonicalProjectivePostConeRawContourTermCase_unique hp hp2 slot s _ _

/-- The classifier selected at the current face-side occurrence of a
surviving target dart is its unique final-target case. Its negative sign is
the physical target orientation before any recursive inverse reversal. -/
theorem canonicalProjectivePostConeRawContourTermCase_eq_finalTarget_of_dart
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2)
    (hface : projectivePolygonPostConeEdgeTarget z.1 =
      (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p))
    (hside : projectivePolygonPostConeEdgeTargetSide z.1 = s) :
    ∃ hterm : canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s =
        (FreeGroup.of z.1)⁻¹,
      canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs =
        .finalTarget z.1 ⟨hface.symm, hside.symm, hterm⟩ z.2 := by
  let hstate : (projectivePolygonPostConeEdgeTarget z.1).state = slot.right.state :=
    congrArg ProjectivePolygonPostConeFace.state hface
  have hterm : canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
      s = (FreeGroup.of z.1)⁻¹ := by
    rw [← hside, ← hstate]
    exact canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 z.1
  refine ⟨hterm, ?_⟩
  exact canonicalProjectivePostConeRawContourTermCase_unique hp hp2 slot s _ _

/-- A surviving dart based at a slot's right face cannot occupy that slot's
pivot side: the pivot carrier is the eliminated tree label, while every
surviving dart label satisfies the complementary final-symbol predicate. -/
theorem canonicalProjectivePostConeSurvivingDart_side_ne_pivot_of_face
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2)
    (hface : canonicalProjectivePostConeSurvivingDartFace hp hp2 d =
      (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p)) :
    canonicalProjectivePostConeSurvivingDartSide hp hp2 d ≠
      canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot := by
  classical
  intro hside
  let w := canonicalProjectivePostConeTreeSlotLabel hp hp2 slot
  have hsourceOrTarget :=
    canonicalProjectivePostConeTreeSlot_right_eq_physicalSource_or_target hp hp2 slot
  by_cases hslotSource : slot.right = projectivePolygonPostConeEdgeSource w
  · have hslotTerm : canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
        (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) =
        FreeGroup.of w := by
      rw [show slot.right.state = (projectivePolygonPostConeEdgeSource w).state by
        exact congrArg ProjectivePolygonPostConeFace.state hslotSource,
        show canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot =
          projectivePolygonPostConeEdgeSide w by
            change (if slot.right = projectivePolygonPostConeEdgeSource w then
              projectivePolygonPostConeEdgeSide w else
              projectivePolygonPostConeEdgeTargetSide w) =
              projectivePolygonPostConeEdgeSide w
            rw [if_pos hslotSource]]
      exact canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq w
    cases d with
    | inl z =>
      have hstate : (projectivePolygonPostConeEdgeSource z.1).state = slot.right.state :=
        congrArg ProjectivePolygonPostConeFace.state hface
      have hterm : canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) =
          FreeGroup.of z.1 := by
        rw [← hside, ← hstate]
        exact canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq z.1
      have hword : FreeGroup.of z.1 = FreeGroup.of w := hterm.symm.trans hslotTerm
      have hlabel : z.1 = w := FreeGroup.of_injective hword
      exact z.2 ⟨slot, hlabel.symm⟩
    | inr z =>
      have hstate : (projectivePolygonPostConeEdgeTarget z.1).state = slot.right.state :=
        congrArg ProjectivePolygonPostConeFace.state hface
      have hterm : canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) =
          (FreeGroup.of z.1)⁻¹ := by
        rw [← hside, ← hstate]
        exact canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 z.1
      have hword : FreeGroup.of w = (FreeGroup.of z.1)⁻¹ := hslotTerm.symm.trans hterm
      exact (BoundaryWords.Internal.freeGroup_of_ne_inv w z.1 hword).elim
  · have hslotTarget : slot.right = projectivePolygonPostConeEdgeTarget w := by
      rcases hsourceOrTarget with h | h
      · exact (hslotSource h).elim
      · exact h
    have hslotTerm : canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
        (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) =
        (FreeGroup.of w)⁻¹ := by
      rw [show slot.right.state = (projectivePolygonPostConeEdgeTarget w).state by
        exact congrArg ProjectivePolygonPostConeFace.state hslotTarget,
        show canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot =
          projectivePolygonPostConeEdgeTargetSide w by
            change (if slot.right = projectivePolygonPostConeEdgeSource w then
              projectivePolygonPostConeEdgeSide w else
              projectivePolygonPostConeEdgeTargetSide w) =
              projectivePolygonPostConeEdgeTargetSide w
            rw [if_neg hslotSource]]
      exact canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 w
    cases d with
    | inl z =>
      have hstate : (projectivePolygonPostConeEdgeSource z.1).state = slot.right.state :=
        congrArg ProjectivePolygonPostConeFace.state hface
      have hterm : canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) =
          FreeGroup.of z.1 := by
        rw [← hside, ← hstate]
        exact canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq z.1
      have hword : FreeGroup.of z.1 = (FreeGroup.of w)⁻¹ := hterm.symm.trans hslotTerm
      exact (BoundaryWords.Internal.freeGroup_of_ne_inv z.1 w hword).elim
    | inr z =>
      have hstate : (projectivePolygonPostConeEdgeTarget z.1).state = slot.right.state :=
        congrArg ProjectivePolygonPostConeFace.state hface
      have hterm : canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) =
          (FreeGroup.of z.1)⁻¹ := by
        rw [← hside, ← hstate]
        exact canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 z.1
      have hword : (FreeGroup.of z.1)⁻¹ = (FreeGroup.of w)⁻¹ := hterm.symm.trans hslotTerm
      have hword' : FreeGroup.of z.1 = FreeGroup.of w := by
        have hinv := congrArg Inv.inv hword
        simpa using hinv
      have hlabel : z.1 = w := FreeGroup.of_injective hword'
      exact z.2 ⟨slot, hlabel.symm⟩

/-- Every surviving dart based at the current face occurs in the local raw
contour; the pivot-side exclusion is discharged from its physical carrier. -/
theorem canonicalProjectivePostConeSurvivingDart_current_rawTerm_of_face
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2)
    (hface : canonicalProjectivePostConeSurvivingDartFace hp hp2 d =
      (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p)) :
    canonicalProjectivePostConeRawContourTerm hp hp2 slot ih
      (canonicalProjectivePostConeSurvivingDartSide hp hp2 d) =
        [(canonicalProjectivePostConeSurvivingDartGenerator hp hp2 d,
          canonicalProjectivePostConeSurvivingDartPositive hp hp2 d)] := by
  apply canonicalProjectivePostConeSurvivingDart_current_rawTerm
    hp hp2 slot ih d hface
  exact canonicalProjectivePostConeSurvivingDart_side_ne_pivot_of_face
    hp hp2 slot d hface

/-- A current-face dart is represented by the unique position in its
singleton side term, and its side-origin decoder returns that dart. -/
theorem canonicalProjectivePostConeSurvivingDart_exists_current_sideOrigin
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2)
    (hface : canonicalProjectivePostConeSurvivingDartFace hp hp2 d =
      (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p)) :
    ∃ tag : CanonicalProjectivePostConeRawContourSideOriginTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
      (canonicalProjectivePostConeSurvivingDartSide hp hp2 d),
      canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot
        (fun child _ => canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child)
        (canonicalProjectivePostConeSurvivingDartSide hp hp2 d) tag =
        (d, canonicalProjectivePostConeSurvivingDartPositive hp hp2 d) := by
  classical
  let ih := fun child
      (_hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child) =>
      canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child
  let recEndpoint := fun child
      (_hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child) =>
      canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child
  have hcurrent := canonicalProjectivePostConeSurvivingDart_current_rawTerm_of_face
    hp hp2 slot ih d hface
  have hs := canonicalProjectivePostConeSurvivingDart_side_ne_pivot_of_face
    hp hp2 slot d hface
  cases d with
  | inl z =>
      change projectivePolygonPostConeEdgeSource z.1 =
        (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) at hface
      let s := projectivePolygonPostConeEdgeSide z.1
      have hs' : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot := by
        simpa [s, canonicalProjectivePostConeSurvivingDartSide] using hs
      have hword : canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s = [(z, true)] := by
        simpa [s, canonicalProjectivePostConeSurvivingDartSide,
          canonicalProjectivePostConeSurvivingDartGenerator,
          canonicalProjectivePostConeSurvivingDartPositive] using hcurrent
      have hpos : 0 < (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s).length := by
        rw [hword]
        simp
      let i : Fin (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s).length := ⟨0, hpos⟩
      let e := canonicalProjectivePostConeRawContourSide_positionEquiv hp hp2 slot ih s
      let tag := e i
      refine ⟨tag, ?_⟩
      unfold canonicalProjectivePostConeRawSideOrigin_endpoint
      split
      · rename_i hpivot
        exact (hs' hpivot).elim
      · rename_i hoff
        change s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot at hoff
        obtain ⟨hterm, hcase⟩ :=
          canonicalProjectivePostConeRawContourTermCase_eq_finalSource_of_dart
            hp hp2 slot s hoff z hface rfl
        have hi : e.symm tag = i := by
          dsimp [e, tag]
          exact Equiv.symm_apply_apply _ _
        change canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot recEndpoint
          (canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hoff)
          (canonicalProjectivePostConeRawContourTerm_positionEquiv hp hp2 slot ih s hoff
            (e.symm tag)) = (Sum.inl z, true)
        rw [hi]
        exact canonicalProjectivePostConeRawTermOrigin_endpoint_of_finalSource
          hp hp2 slot recEndpoint z.1
          ⟨hface.symm, rfl, hterm⟩ z.2 hcase
          (canonicalProjectivePostConeRawContourTerm_positionEquiv
            hp hp2 slot ih s hoff i)
  | inr z =>
      change projectivePolygonPostConeEdgeTarget z.1 =
        (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) at hface
      let s := projectivePolygonPostConeEdgeTargetSide z.1
      have hs' : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot := by
        simpa [s, canonicalProjectivePostConeSurvivingDartSide] using hs
      have hword : canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s = [(z, false)] := by
        simpa [s, canonicalProjectivePostConeSurvivingDartSide,
          canonicalProjectivePostConeSurvivingDartGenerator,
          canonicalProjectivePostConeSurvivingDartPositive] using hcurrent
      have hpos : 0 < (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s).length := by
        rw [hword]
        simp
      let i : Fin (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s).length := ⟨0, hpos⟩
      let e := canonicalProjectivePostConeRawContourSide_positionEquiv hp hp2 slot ih s
      let tag := e i
      refine ⟨tag, ?_⟩
      unfold canonicalProjectivePostConeRawSideOrigin_endpoint
      split
      · rename_i hpivot
        exact (hs' hpivot).elim
      · rename_i hoff
        change s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot at hoff
        obtain ⟨hterm, hcase⟩ :=
          canonicalProjectivePostConeRawContourTermCase_eq_finalTarget_of_dart
            hp hp2 slot s hoff z hface rfl
        have hi : e.symm tag = i := by
          dsimp [e, tag]
          exact Equiv.symm_apply_apply _ _
        change canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot recEndpoint
          (canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hoff)
          (canonicalProjectivePostConeRawContourTerm_positionEquiv hp hp2 slot ih s hoff
            (e.symm tag)) = (Sum.inr z, false)
        rw [hi]
        exact canonicalProjectivePostConeRawTermOrigin_endpoint_of_finalTarget
          hp hp2 slot recEndpoint z.1
          ⟨hface.symm, rfl, hterm⟩ z.2 hcase
          (canonicalProjectivePostConeRawContourTerm_positionEquiv
            hp hp2 slot ih s hoff i)

/-- Every surviving dart based at the current slot vertex is represented by
an origin tag of the complete slot splice. The source splice may flip the
orientation bit, but never changes the underlying physical dart. -/
theorem canonicalProjectivePostConeSurvivingDart_exists_current_slotOrigin
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2)
    (hface : canonicalProjectivePostConeSurvivingDartFace hp hp2 d =
      (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p)) :
    ∃ tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 slot,
      (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 slot tag).1 = d := by
  classical
  let ih := fun child
      (_hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child) =>
      canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child
  let recEndpoint := fun child
      (_hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child) =>
      canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child
  obtain ⟨sideTag, hsideTag⟩ :=
    canonicalProjectivePostConeSurvivingDart_exists_current_sideOrigin
      hp hp2 slot d hface
  have hnotPivot := canonicalProjectivePostConeSurvivingDart_side_ne_pivot_of_face
    hp hp2 slot d hface
  let s := canonicalProjectivePostConeSurvivingDartSide hp hp2 d
  rcases canonicalProjectivePostConeBoundarySide_mem_prefix_or_suffix s
      (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) hnotPivot
    with hprefix | hsuffix
  · obtain ⟨listTag, hlist⟩ :=
      canonicalProjectivePostConeRawTermsOrigin_endpoint_exists_of_mem
        hp hp2 slot recEndpoint
        (canonicalProjectivePostConeBoundaryPrefixSides
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
        s hprefix sideTag
    by_cases horient : projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) = slot.right
    · refine ⟨.source horient.symm (Sum.inl listTag), ?_⟩
      unfold canonicalProjectivePostConeRawTreeWordOrigin_endpoint
      rw [WellFounded.fix_eq]
      change (canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step
        hp hp2 slot recEndpoint (.source horient.symm (Sum.inl listTag))).1 = d
      change (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot
        recEndpoint (canonicalProjectivePostConeBoundaryPrefixSides
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
        listTag).1 = d
      calc
        _ = (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot
            recEndpoint s sideTag).1 := congrArg Prod.fst hlist
        _ = d := congrArg Prod.fst hsideTag
    · refine ⟨.target (by intro h; exact horient h.symm) (Sum.inr listTag), ?_⟩
      unfold canonicalProjectivePostConeRawTreeWordOrigin_endpoint
      rw [WellFounded.fix_eq]
      change (canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step
        hp hp2 slot recEndpoint
        (.target (by intro h; exact horient h.symm) (Sum.inr listTag))).1 = d
      change (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot
        recEndpoint (canonicalProjectivePostConeBoundaryPrefixSides
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
        listTag).1 = d
      calc
        _ = (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot
            recEndpoint s sideTag).1 := congrArg Prod.fst hlist
        _ = d := congrArg Prod.fst hsideTag
  · obtain ⟨listTag, hlist⟩ :=
      canonicalProjectivePostConeRawTermsOrigin_endpoint_exists_of_mem
        hp hp2 slot recEndpoint
        (canonicalProjectivePostConeBoundarySuffixSides
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
        s hsuffix sideTag
    by_cases horient : projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) = slot.right
    · refine ⟨.source horient.symm (Sum.inr listTag), ?_⟩
      unfold canonicalProjectivePostConeRawTreeWordOrigin_endpoint
      rw [WellFounded.fix_eq]
      change (canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step
        hp hp2 slot recEndpoint (.source horient.symm (Sum.inr listTag))).1 = d
      change (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot
        recEndpoint (canonicalProjectivePostConeBoundarySuffixSides
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
        listTag).1 = d
      calc
        _ = (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot
            recEndpoint s sideTag).1 := congrArg Prod.fst hlist
        _ = d := congrArg Prod.fst hsideTag
    · refine ⟨.target (by intro h; exact horient h.symm) (Sum.inl listTag), ?_⟩
      unfold canonicalProjectivePostConeRawTreeWordOrigin_endpoint
      rw [WellFounded.fix_eq]
      change (canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step
        hp hp2 slot recEndpoint
        (.target (by intro h; exact horient h.symm) (Sum.inl listTag))).1 = d
      change (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot
        recEndpoint (canonicalProjectivePostConeBoundarySuffixSides
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
        listTag).1 = d
      calc
        _ = (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot
            recEndpoint s sideTag).1 := congrArg Prod.fst hlist
        _ = d := congrArg Prod.fst hsideTag

/-- A fixed face-side occurrence determines at most one surviving endpoint
dart. The boundary term is a positive free generator at a physical source
and its inverse at a physical target, so its literal factorization determines
both the generator and the endpoint role. -/
theorem canonicalProjectivePostConeSurvivingDart_face_side_injective
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d e : CanonicalProjectivePostConeSurvivingDart hp hp2)
    (hface : canonicalProjectivePostConeSurvivingDartFace hp hp2 d =
      canonicalProjectivePostConeSurvivingDartFace hp hp2 e)
    (hside : canonicalProjectivePostConeSurvivingDartSide hp hp2 d =
      canonicalProjectivePostConeSurvivingDartSide hp hp2 e) : d = e := by
  classical
  cases d with
  | inl z =>
    cases e with
    | inl z' =>
      change projectivePolygonPostConeEdgeSource z.1 =
        projectivePolygonPostConeEdgeSource z'.1 at hface
      change projectivePolygonPostConeEdgeSide z.1 =
        projectivePolygonPostConeEdgeSide z'.1 at hside
      have hstate := congrArg ProjectivePolygonPostConeFace.state hface
      have hword : FreeGroup.of z.1 = FreeGroup.of z'.1 := by
        calc
          FreeGroup.of z.1 =
              canonicalProjectiveConePostConeBoundaryTerm p
                (projectivePolygonPostConeEdgeSource z.1).state
                (projectivePolygonPostConeEdgeSide z.1) :=
            (canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq z.1).symm
          _ = canonicalProjectiveConePostConeBoundaryTerm p
                (projectivePolygonPostConeEdgeSource z'.1).state
                (projectivePolygonPostConeEdgeSide z'.1) := by
            rw [hstate, hside]
          _ = FreeGroup.of z'.1 :=
            canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq z'.1
      apply congrArg Sum.inl
      exact Subtype.ext (FreeGroup.of_injective hword)
    | inr z' =>
      change projectivePolygonPostConeEdgeSource z.1 =
        projectivePolygonPostConeEdgeTarget z'.1 at hface
      change projectivePolygonPostConeEdgeSide z.1 =
        projectivePolygonPostConeEdgeTargetSide z'.1 at hside
      have hstate := congrArg ProjectivePolygonPostConeFace.state hface
      have hword : FreeGroup.of z.1 = (FreeGroup.of z'.1)⁻¹ := by
        calc
          FreeGroup.of z.1 =
              canonicalProjectiveConePostConeBoundaryTerm p
                (projectivePolygonPostConeEdgeSource z.1).state
                (projectivePolygonPostConeEdgeSide z.1) :=
            (canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq z.1).symm
          _ = canonicalProjectiveConePostConeBoundaryTerm p
                (projectivePolygonPostConeEdgeTarget z'.1).state
                (projectivePolygonPostConeEdgeTargetSide z'.1) := by
            rw [hstate, hside]
          _ = (FreeGroup.of z'.1)⁻¹ :=
            canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 z'.1
      exact (BoundaryWords.Internal.freeGroup_of_ne_inv z.1 z'.1 hword).elim
  | inr z =>
    cases e with
    | inl z' =>
      change projectivePolygonPostConeEdgeTarget z.1 =
        projectivePolygonPostConeEdgeSource z'.1 at hface
      change projectivePolygonPostConeEdgeTargetSide z.1 =
        projectivePolygonPostConeEdgeSide z'.1 at hside
      have hstate := congrArg ProjectivePolygonPostConeFace.state hface
      have hword : FreeGroup.of z'.1 = (FreeGroup.of z.1)⁻¹ := by
        calc
          FreeGroup.of z'.1 =
              canonicalProjectiveConePostConeBoundaryTerm p
                (projectivePolygonPostConeEdgeSource z'.1).state
                (projectivePolygonPostConeEdgeSide z'.1) :=
            (canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq z'.1).symm
          _ = canonicalProjectiveConePostConeBoundaryTerm p
                (projectivePolygonPostConeEdgeTarget z.1).state
                (projectivePolygonPostConeEdgeTargetSide z.1) := by
            rw [← hstate, ← hside]
          _ = (FreeGroup.of z.1)⁻¹ :=
            canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 z.1
      exact (BoundaryWords.Internal.freeGroup_of_ne_inv z'.1 z.1 hword).elim
    | inr z' =>
      change projectivePolygonPostConeEdgeTarget z.1 =
        projectivePolygonPostConeEdgeTarget z'.1 at hface
      change projectivePolygonPostConeEdgeTargetSide z.1 =
        projectivePolygonPostConeEdgeTargetSide z'.1 at hside
      have hstate := congrArg ProjectivePolygonPostConeFace.state hface
      have hinv : (FreeGroup.of z.1)⁻¹ = (FreeGroup.of z'.1)⁻¹ := by
        calc
          (FreeGroup.of z.1)⁻¹ =
              canonicalProjectiveConePostConeBoundaryTerm p
                (projectivePolygonPostConeEdgeTarget z.1).state
                (projectivePolygonPostConeEdgeTargetSide z.1) :=
            (canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 z.1).symm
          _ = canonicalProjectiveConePostConeBoundaryTerm p
                (projectivePolygonPostConeEdgeTarget z'.1).state
                (projectivePolygonPostConeEdgeTargetSide z'.1) := by
            rw [hstate, hside]
          _ = (FreeGroup.of z'.1)⁻¹ :=
            canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 z'.1
      have hword : FreeGroup.of z.1 = FreeGroup.of z'.1 := by
        have hinv' := congrArg Inv.inv hinv
        simpa using hinv'
      apply congrArg Sum.inr
      exact Subtype.ext (FreeGroup.of_injective hword)

/-- If a tree edge incident to a slot's right endpoint has strictly greater
target depth, then it is an outgoing child edge from that endpoint. The other
endpoint order would make it the same incoming slot. -/
theorem canonicalProjectivePostConeTreeSlot_right_eq_left_of_incident_deeper
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (parent child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
    (hincident : parent.right = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) ∨
      parent.right = projectivePolygonPostConeEdgeTarget
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 child)) :
    parent.right = child.left := by
  rcases canonicalProjectivePostConeTreeSlot_endpoints_eq_physicalEndpoints
      hp hp2 child with hforward | hreverse
  · rcases hincident with hsource | htarget
    · exact hsource.trans hforward.1.symm
    · have hchildRight : child.right = parent.right := hforward.2.trans htarget.symm
      have hsame := canonicalProjectivePostConeTreeSlot_injective_right hp hp2 hchildRight
      subst child
      exact (Nat.lt_irrefl _ hdeep).elim
  · rcases hincident with hsource | htarget
    · have hchildRight : child.right = parent.right := hreverse.2.trans hsource.symm
      have hsame := canonicalProjectivePostConeTreeSlot_injective_right hp hp2 hchildRight
      subst child
      exact (Nat.lt_irrefl _ hdeep).elim
    · exact htarget.trans hreverse.1.symm

/-- A deeper-source classifier's physical label is the adjacent child slot;
its face incidence plus the strict depth inequality fixes the tree direction. -/
theorem canonicalProjectivePostConeRawContourTermCase_deeperSource_join
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (parent child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hface :
      (⟨parent.right.state⟩ : ProjectivePolygonPostConeFace p) =
          projectivePolygonPostConeEdgeSource z)
    (hlabel : canonicalProjectivePostConeTreeSlotLabel hp hp2 child = z)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child) :
    parent.right = child.left := by
  have hincident : parent.right = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) := by
    apply ProjectivePolygonPostConeFace.stateEquiv.injective
    have hstate := congrArg ProjectivePolygonPostConeFace.state hface
    rw [hlabel]
    exact hstate
  exact canonicalProjectivePostConeTreeSlot_right_eq_left_of_incident_deeper
    hp hp2 parent child hdeep (Or.inl hincident)

/-- Target-oriented version of the deeper-source incidence bridge. -/
theorem canonicalProjectivePostConeRawContourTermCase_deeperTarget_join
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (parent child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hface :
      (⟨parent.right.state⟩ : ProjectivePolygonPostConeFace p) =
          projectivePolygonPostConeEdgeTarget z)
    (hlabel : canonicalProjectivePostConeTreeSlotLabel hp hp2 child = z)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child) :
    parent.right = child.left := by
  have hincident : parent.right = projectivePolygonPostConeEdgeTarget
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) := by
    apply ProjectivePolygonPostConeFace.stateEquiv.injective
    have hstate := congrArg ProjectivePolygonPostConeFace.state hface
    rw [hlabel]
    exact hstate
  exact canonicalProjectivePostConeTreeSlot_right_eq_left_of_incident_deeper
    hp hp2 parent child hdeep (Or.inr hincident)

/-- A surviving dart belongs to the rooted region at `q` exactly when its
physical endpoint face lies below `q` in the directed tree. -/
def canonicalProjectivePostConeSurvivingDartInRegion
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : CanonicalProjectivePostConeTreeVertex hp hp2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2) : Prop :=
  canonicalProjectivePostConeTreeAncestor hp hp2 q
    (canonicalProjectivePostConeSurvivingDartFace hp hp2 d)

private theorem canonicalProjectivePostConeDirectTreeSlot_left_eq_root_of_endpoint
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z)
    (hincident : projectivePolygonPostConeEdgeSource z =
        canonicalProjectivePostConeTreeRoot hp hp2 ∨
      projectivePolygonPostConeEdgeTarget z =
        canonicalProjectivePostConeTreeRoot hp hp2) :
    (canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz).left =
      canonicalProjectivePostConeTreeRoot hp hp2 := by
  let child := canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz
  have hlabel : canonicalProjectivePostConeTreeSlotLabel hp hp2 child = z := by
    exact canonicalProjectivePostConeDirectTreeSlotOfDeleted_label hp hp2 z hz
  rcases canonicalProjectivePostConeTreeSlot_endpoints_eq_physicalEndpoints
      hp hp2 child with hforward | hreverse
  · rcases hincident with hsource | htarget
    · have hsource' : projectivePolygonPostConeEdgeSource
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) =
            canonicalProjectivePostConeTreeRoot hp hp2 := by
        rw [hlabel]
        exact hsource
      exact hforward.1.trans hsource'
    · have hright : child.right = canonicalProjectivePostConeTreeRoot hp hp2 := by
        have htarget' : projectivePolygonPostConeEdgeTarget
            (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) =
              canonicalProjectivePostConeTreeRoot hp hp2 := by
          rw [hlabel]
          exact htarget
        exact hforward.2.trans htarget'
      exact (canonicalProjectivePostConeTreeSlot_right_ne_root hp hp2 child hright).elim
  · rcases hincident with hsource | htarget
    · have hright : child.right = canonicalProjectivePostConeTreeRoot hp hp2 := by
        have hsource' : projectivePolygonPostConeEdgeSource
            (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) =
              canonicalProjectivePostConeTreeRoot hp hp2 := by
          rw [hlabel]
          exact hsource
        exact hreverse.2.trans hsource'
      exact (canonicalProjectivePostConeTreeSlot_right_ne_root hp hp2 child hright).elim
    · have htarget' : projectivePolygonPostConeEdgeTarget
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) =
            canonicalProjectivePostConeTreeRoot hp hp2 := by
        rw [hlabel]
        exact htarget
      exact hreverse.1.trans htarget'

/-- Every dart in a rooted region is either based at that region's root face
or belongs to exactly one immediate child region. This is the disjoint
tree-region partition, before the separate face-side/list-position bridge. -/
theorem canonicalProjectivePostConeSurvivingDart_region_current_or_child
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : CanonicalProjectivePostConeTreeVertex hp hp2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2)
    (hd : canonicalProjectivePostConeSurvivingDartInRegion hp hp2 q d) :
    (canonicalProjectivePostConeSurvivingDartFace hp hp2 d :
      CanonicalProjectivePostConeTreeVertex hp hp2) = q ∨
    ∃! child : CanonicalProjectivePostConeTreeSlot hp hp2,
      child.left = q ∧
        canonicalProjectivePostConeSurvivingDartInRegion hp hp2 child.right d := by
  let r : CanonicalProjectivePostConeTreeVertex hp hp2 :=
    canonicalProjectivePostConeSurvivingDartFace hp hp2 d
  change canonicalProjectivePostConeTreeAncestor hp hp2 q r at hd
  by_cases hqr : q = r
  · exact Or.inl hqr.symm
  · exact Or.inr
      (canonicalProjectivePostConeTreeAncestor_existsUnique_firstStep
        hp hp2 hd hqr)

/-- A dart in the region below a tree slot cannot be based at that slot's
parent vertex. -/
theorem canonicalProjectivePostConeSurvivingDart_childRegion_ne_parent
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2)
    (hd : canonicalProjectivePostConeSurvivingDartInRegion hp hp2 child.right d) :
    canonicalProjectivePostConeSurvivingDartFace hp hp2 d ≠ child.left := by
  have hdepth := canonicalProjectivePostConeTreeAncestor_depth_lt hp hp2
    (canonicalProjectivePostConeTreeAncestor_of_slot hp hp2 child)
    (canonicalProjectivePostConeTreeSlot_left_ne_right hp hp2 child)
  exact canonicalProjectivePostConeTreeAncestor_ne_of_strict_descendant
    hp hp2 hdepth hd

/-- The source and target faces of a physical tree-slot label are distinct,
since that slot has distinct left and right vertices. -/
theorem canonicalProjectivePostConeTreeSlotLabel_source_ne_target
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) ≠
      projectivePolygonPostConeEdgeTarget
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) := by
  rcases canonicalProjectivePostConeTreeSlot_endpoints_eq_physicalEndpoints
      hp hp2 slot with hforward | hreverse
  · intro h
    exact canonicalProjectivePostConeTreeSlot_left_ne_right hp hp2 slot
      (hforward.1.trans (h.trans hforward.2.symm))
  · intro h
    exact canonicalProjectivePostConeTreeSlot_left_ne_right hp hp2 slot
      (hreverse.1.trans (h.symm.trans hreverse.2.symm))

/-- The root-side occurrence attached to a tree slot is the side of its
physical label at the slot's left endpoint. -/
noncomputable def canonicalProjectivePostConeTreeSlot_leftBoundarySide
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) : ProjectivePolygonSide := by
  classical
  let z := canonicalProjectivePostConeTreeSlotLabel hp hp2 slot
  exact if slot.left = projectivePolygonPostConeEdgeSource z then
    projectivePolygonPostConeEdgeSide z
  else projectivePolygonPostConeEdgeTargetSide z

/-- If the slot's left endpoint is the label's source, its left boundary
side is the physical source side. -/
theorem canonicalProjectivePostConeTreeSlot_leftBoundarySide_eq_source
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hleft : slot.left = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) :
    canonicalProjectivePostConeTreeSlot_leftBoundarySide hp hp2 slot =
      projectivePolygonPostConeEdgeSide (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) := by
  classical
  unfold canonicalProjectivePostConeTreeSlot_leftBoundarySide
  rw [if_pos hleft]

/-- If the slot's left endpoint is the label's target, it cannot also be its
source; its left boundary side is therefore the physical target side. -/
theorem canonicalProjectivePostConeTreeSlot_leftBoundarySide_eq_target
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hleft : slot.left = projectivePolygonPostConeEdgeTarget
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) :
    canonicalProjectivePostConeTreeSlot_leftBoundarySide hp hp2 slot =
      projectivePolygonPostConeEdgeTargetSide
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) := by
  classical
  have hnotSource : slot.left ≠ projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) := by
    intro hsource
    exact canonicalProjectivePostConeTreeSlotLabel_source_ne_target hp hp2 slot
      (hsource.symm.trans hleft)
  unfold canonicalProjectivePostConeTreeSlot_leftBoundarySide
  rw [if_neg hnotSource]

/-- Every surviving dart lies in the root region. -/
theorem canonicalProjectivePostConeSurvivingDart_mem_rootRegion
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2) :
    canonicalProjectivePostConeSurvivingDartInRegion hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2) d := by
  exact canonicalProjectivePostConeTreeRoot_ancestor hp hp2
    (canonicalProjectivePostConeSurvivingDartFace hp hp2 d :
      CanonicalProjectivePostConeTreeVertex hp hp2)

/-- The rooted dart region is the subtype of physical endpoint occurrences
whose endpoint faces descend from `q`. -/
def canonicalProjectivePostConeSurvivingDartRegion
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : CanonicalProjectivePostConeTreeVertex hp hp2) :=
  {d : CanonicalProjectivePostConeSurvivingDart hp hp2 //
    canonicalProjectivePostConeSurvivingDartInRegion hp hp2 q d}

/-- A final-source classifier tag decodes to a dart based at the current
slot vertex. This is the terminal case of the recursive region invariant. -/
theorem canonicalProjectivePostConeRawTermOrigin_finalSource_region
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hface :
      (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeSource z)
    (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
    canonicalProjectivePostConeTreeAncestor hp hp2 slot.right
      (canonicalProjectivePostConeSurvivingDartFace hp hp2
        (Sum.inl (⟨z, hz⟩ : CanonicalProjectivePostConeFinalGenerator hp hp2))) := by
  have hvertex :
      (projectivePolygonPostConeEdgeSource z : CanonicalProjectivePostConeTreeVertex hp hp2) =
        slot.right := by
    exact hface.symm
  rw [show canonicalProjectivePostConeSurvivingDartFace hp hp2
      (Sum.inl (⟨z, hz⟩ : CanonicalProjectivePostConeFinalGenerator hp hp2)) =
        projectivePolygonPostConeEdgeSource z by rfl]
  rw [hvertex]
  exact canonicalProjectivePostConeTreeAncestor_refl hp hp2 slot.right

/-- The final-target classifier case likewise lands at the current vertex. -/
theorem canonicalProjectivePostConeRawTermOrigin_finalTarget_region
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hface :
      (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeTarget z)
    (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
    canonicalProjectivePostConeTreeAncestor hp hp2 slot.right
      (canonicalProjectivePostConeSurvivingDartFace hp hp2
        (Sum.inr (⟨z, hz⟩ : CanonicalProjectivePostConeFinalGenerator hp hp2))) := by
  have hvertex :
      (projectivePolygonPostConeEdgeTarget z : CanonicalProjectivePostConeTreeVertex hp hp2) =
        slot.right := hface.symm
  rw [show canonicalProjectivePostConeSurvivingDartFace hp hp2
      (Sum.inr (⟨z, hz⟩ : CanonicalProjectivePostConeFinalGenerator hp hp2)) =
        projectivePolygonPostConeEdgeTarget z by rfl]
  rw [hvertex]
  exact canonicalProjectivePostConeTreeAncestor_refl hp hp2 slot.right

/-- At a classified term, recursive endpoint decoding remains in the rooted
region. Final cases are current-face occurrences; deeper cases cross the
identified child edge and then use the child induction hypothesis. -/
theorem canonicalProjectivePostConeRawTermOrigin_endpoint_region
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (hrec : ∀ (child : CanonicalProjectivePostConeTreeSlot hp hp2)
      (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
      (tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child),
      canonicalProjectivePostConeTreeAncestor hp hp2 child.right
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (rec child hdeep tag).1))
    {s : ProjectivePolygonSide}
    (c : CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s)
    (tag : CanonicalProjectivePostConeRawContourTermPositionTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
      c) :
    canonicalProjectivePostConeTreeAncestor hp hp2 slot.right
      (canonicalProjectivePostConeSurvivingDartFace hp hp2
        (canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot rec c tag).1) := by
  cases c with
  | one hterm => exact tag.elim
  | finalSource z hsource hz =>
      exact canonicalProjectivePostConeRawTermOrigin_finalSource_region
        hp hp2 slot z hsource.1 hz
  | finalTarget z htarget hz =>
      exact canonicalProjectivePostConeRawTermOrigin_finalTarget_region
        hp hp2 slot z htarget.1 hz
  | deeperSource z child hsource hlabel hdeep =>
      have hjoin := canonicalProjectivePostConeRawContourTermCase_deeperSource_join
        hp hp2 slot child z hsource.1 hlabel hdeep
      have hparentChild :
          canonicalProjectivePostConeTreeAncestor hp hp2 slot.right child.left := by
        rw [hjoin]
        exact canonicalProjectivePostConeTreeAncestor_refl hp hp2 child.left
      exact canonicalProjectivePostConeTreeAncestor_trans hp hp2 hparentChild
        (canonicalProjectivePostConeTreeAncestor_trans hp hp2
          (canonicalProjectivePostConeTreeAncestor_of_slot hp hp2 child)
          (hrec child hdeep
            (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child tag)))
  | deeperTarget z child htarget hlabel hdeep =>
      have hjoin := canonicalProjectivePostConeRawContourTermCase_deeperTarget_join
        hp hp2 slot child z htarget.1 hlabel hdeep
      have hparentChild :
          canonicalProjectivePostConeTreeAncestor hp hp2 slot.right child.left := by
        rw [hjoin]
        exact canonicalProjectivePostConeTreeAncestor_refl hp hp2 child.left
      exact canonicalProjectivePostConeTreeAncestor_trans hp hp2 hparentChild
        (canonicalProjectivePostConeTreeAncestor_trans hp hp2
          (canonicalProjectivePostConeTreeAncestor_of_slot hp hp2 child)
          (hrec child hdeep
            (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child tag)))

/-- A deeper-source term origin cannot decode back to the current vertex:
its endpoint lies below the strict child of this slot. -/
theorem canonicalProjectivePostConeRawTermOrigin_deeperSource_not_current
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 other →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (hrec : ∀ other hdeep tag,
      canonicalProjectivePostConeTreeAncestor hp hp2 other.right
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (rec other hdeep tag).1))
    (s : ProjectivePolygonSide)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hsource :
      (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeSource z ∧
      s = projectivePolygonPostConeEdgeSide z ∧
      canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s = FreeGroup.of z)
    (hlabel : canonicalProjectivePostConeTreeSlotLabel hp hp2 child = z)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
    (tag : CanonicalProjectivePostConeRawContourTermPositionTag hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
      (.deeperSource z child hsource hlabel hdeep)) :
    canonicalProjectivePostConeSurvivingDartFace hp hp2
      (canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot rec
        (.deeperSource z child hsource hlabel hdeep) tag).1 ≠ slot.right := by
  have hjoin := canonicalProjectivePostConeRawContourTermCase_deeperSource_join
    hp hp2 slot child z hsource.1 hlabel hdeep
  have hstrict := canonicalProjectivePostConeTreeSlot_targetDepth_lt_of_right_eq_left
    hp hp2 hjoin
  have hstrictDepth : canonicalProjectivePostConeTreeVertexDepth hp hp2 slot.right <
      canonicalProjectivePostConeTreeVertexDepth hp hp2 child.right := by
    exact hstrict
  exact canonicalProjectivePostConeTreeAncestor_ne_of_strict_descendant hp hp2
    hstrictDepth
    (hrec child hdeep
      (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child tag))

/-- The same strict-region separation holds for a deeper-target term; its
inverse-reversal changes sign but not the terminal physical endpoint. -/
theorem canonicalProjectivePostConeRawTermOrigin_deeperTarget_not_current
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 other →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (hrec : ∀ other hdeep tag,
      canonicalProjectivePostConeTreeAncestor hp hp2 other.right
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (rec other hdeep tag).1))
    (s : ProjectivePolygonSide)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (htarget :
      (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeTarget z ∧
      s = projectivePolygonPostConeEdgeTargetSide z ∧
      canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s =
        (FreeGroup.of z)⁻¹)
    (hlabel : canonicalProjectivePostConeTreeSlotLabel hp hp2 child = z)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
    (tag : CanonicalProjectivePostConeRawContourTermPositionTag hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
      (.deeperTarget z child htarget hlabel hdeep)) :
    canonicalProjectivePostConeSurvivingDartFace hp hp2
      (canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot rec
        (.deeperTarget z child htarget hlabel hdeep) tag).1 ≠ slot.right := by
  have hjoin := canonicalProjectivePostConeRawContourTermCase_deeperTarget_join
    hp hp2 slot child z htarget.1 hlabel hdeep
  have hstrict := canonicalProjectivePostConeTreeSlot_targetDepth_lt_of_right_eq_left
    hp hp2 hjoin
  have hstrictDepth : canonicalProjectivePostConeTreeVertexDepth hp hp2 slot.right <
      canonicalProjectivePostConeTreeVertexDepth hp hp2 child.right := by
    exact hstrict
  exact canonicalProjectivePostConeTreeAncestor_ne_of_strict_descendant hp hp2
    hstrictDepth
    (hrec child hdeep
      (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child tag))

/-- A term-origin tag decodes at the current vertex exactly in a final
source/target classifier case, never in the empty or deeper cases. -/
theorem canonicalProjectivePostConeRawTermOrigin_endpoint_eq_current_iff_final
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 other →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (hrec : ∀ other hdeep tag,
      canonicalProjectivePostConeTreeAncestor hp hp2 other.right
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (rec other hdeep tag).1))
    {s : ProjectivePolygonSide}
    (c : CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s)
    (tag : CanonicalProjectivePostConeRawContourTermPositionTag hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) c) :
    (canonicalProjectivePostConeSurvivingDartFace hp hp2
      (canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot rec c tag).1 =
        slot.right) ↔
      (∃ z hz hsource,
        c = .finalSource z hsource hz) ∨
      (∃ z hz htarget,
        c = .finalTarget z htarget hz) := by
  constructor
  · intro hcurrent
    cases c with
    | one hterm => exact tag.elim
    | finalSource z hsource hz => exact Or.inl ⟨z, hz, hsource, rfl⟩
    | finalTarget z htarget hz => exact Or.inr ⟨z, hz, htarget, rfl⟩
    | deeperSource z child hsource hlabel hdeep =>
        exact (canonicalProjectivePostConeRawTermOrigin_deeperSource_not_current
          hp hp2 slot child rec hrec s z hsource hlabel hdeep tag hcurrent).elim
    | deeperTarget z child htarget hlabel hdeep =>
        exact (canonicalProjectivePostConeRawTermOrigin_deeperTarget_not_current
          hp hp2 slot child rec hrec s z htarget hlabel hdeep tag hcurrent).elim
  · rintro (⟨z, hz, hsource, rfl⟩ | ⟨z, hz, htarget, rfl⟩)
    · change projectivePolygonPostConeEdgeSource z = slot.right
      exact hsource.1.symm
    · change projectivePolygonPostConeEdgeTarget z = slot.right
      exact htarget.1.symm

/-- The unique polygon side at a parent vertex occupied by a particular
labelled child edge. -/
noncomputable def canonicalProjectivePostConeRawParentSideForChild
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (parent child : CanonicalProjectivePostConeTreeSlot hp hp2) :
    ProjectivePolygonSide := by
  classical
  exact if parent.right = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child)
    then projectivePolygonPostConeEdgeSide
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child)
    else projectivePolygonPostConeEdgeTargetSide
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child)

/-- A strict child edge cannot occupy the pivot side of its parent slot.
Both sides carry unique physical boundary labels; if the child carrier were
the pivot carrier, slot-label injectivity would identify the two tree edges,
contradicting the strict depth increase. -/
theorem canonicalProjectivePostConeRawParentSideForChild_ne_pivot
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (parent child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
    (hjoin : parent.right = child.left) :
    canonicalProjectivePostConeRawParentSideForChild hp hp2 parent child ≠
      canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 parent := by
  classical
  let parentLabel := canonicalProjectivePostConeTreeSlotLabel hp hp2 parent
  let childLabel := canonicalProjectivePostConeTreeSlotLabel hp hp2 child
  let childSide := canonicalProjectivePostConeRawParentSideForChild hp hp2 parent child
  have hchildCarrier :
      CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p
        parent.right.state childSide childLabel := by
    rcases canonicalProjectivePostConeTreeSlot_endpoints_eq_physicalEndpoints
        hp hp2 child with hforward | hreverse
    · have hface : parent.right = projectivePolygonPostConeEdgeSource childLabel :=
        hjoin.trans hforward.1
      have hface' : (⟨parent.right.state⟩ : ProjectivePolygonPostConeFace p) =
          projectivePolygonPostConeEdgeSource childLabel := by
        apply ProjectivePolygonPostConeFace.stateEquiv.injective
        exact congrArg ProjectivePolygonPostConeFace.state hface
      have hside : childSide = projectivePolygonPostConeEdgeSide childLabel := by
        change (if parent.right = projectivePolygonPostConeEdgeSource childLabel then
          projectivePolygonPostConeEdgeSide childLabel else
          projectivePolygonPostConeEdgeTargetSide childLabel) =
            projectivePolygonPostConeEdgeSide childLabel
        rw [if_pos hface]
      have hstate := congrArg ProjectivePolygonPostConeFace.state hface'
      have hterm : canonicalProjectiveConePostConeBoundaryTerm p
          parent.right.state childSide = FreeGroup.of childLabel := by
        rw [hside, hstate]
        exact canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq childLabel
      exact Or.inl ⟨hface', hside, hterm⟩
    · have hface : parent.right = projectivePolygonPostConeEdgeTarget childLabel :=
        hjoin.trans hreverse.1
      have hface' : (⟨parent.right.state⟩ : ProjectivePolygonPostConeFace p) =
          projectivePolygonPostConeEdgeTarget childLabel := by
        apply ProjectivePolygonPostConeFace.stateEquiv.injective
        exact congrArg ProjectivePolygonPostConeFace.state hface
      have hnotSource : parent.right ≠ projectivePolygonPostConeEdgeSource childLabel := by
        intro hsource
        exact (canonicalProjectivePostConeTreeSlot_edgeSource_ne_edgeTarget
          hp hp2 child) (hsource.symm.trans hface)
      have hside : childSide = projectivePolygonPostConeEdgeTargetSide childLabel := by
        change (if parent.right = projectivePolygonPostConeEdgeSource childLabel then
          projectivePolygonPostConeEdgeSide childLabel else
          projectivePolygonPostConeEdgeTargetSide childLabel) =
            projectivePolygonPostConeEdgeTargetSide childLabel
        rw [if_neg hnotSource]
      have hstate := congrArg ProjectivePolygonPostConeFace.state hface'
      have hterm : canonicalProjectiveConePostConeBoundaryTerm p
          parent.right.state childSide = (FreeGroup.of childLabel)⁻¹ := by
        rw [hside, hstate]
        exact canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 childLabel
      exact Or.inr ⟨hface', hside, hterm⟩
  have hparentCarrier :
      CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p
        parent.right.state
        (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 parent) parentLabel := by
    rcases canonicalProjectivePostConeTreeSlot_right_eq_physicalSource_or_target
        hp hp2 parent with hsource | htarget
    · have hside : canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 parent =
          projectivePolygonPostConeEdgeSide parentLabel := by
        change (if parent.right = projectivePolygonPostConeEdgeSource parentLabel then
          projectivePolygonPostConeEdgeSide parentLabel else
          projectivePolygonPostConeEdgeTargetSide parentLabel) =
            projectivePolygonPostConeEdgeSide parentLabel
        rw [if_pos hsource]
      have hface : (⟨parent.right.state⟩ : ProjectivePolygonPostConeFace p) =
          projectivePolygonPostConeEdgeSource parentLabel := by
        apply ProjectivePolygonPostConeFace.stateEquiv.injective
        exact congrArg ProjectivePolygonPostConeFace.state hsource
      have hstate := congrArg ProjectivePolygonPostConeFace.state hface
      have hterm : canonicalProjectiveConePostConeBoundaryTerm p parent.right.state
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 parent) =
            FreeGroup.of parentLabel := by
        rw [hside, hstate]
        exact canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq parentLabel
      exact Or.inl ⟨hface, hside, hterm⟩
    · have hnotSource : parent.right ≠ projectivePolygonPostConeEdgeSource parentLabel := by
        intro hsource
        exact (canonicalProjectivePostConeTreeSlot_edgeSource_ne_edgeTarget
          hp hp2 parent) (hsource.symm.trans htarget)
      have hside : canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 parent =
          projectivePolygonPostConeEdgeTargetSide parentLabel := by
        change (if parent.right = projectivePolygonPostConeEdgeSource parentLabel then
          projectivePolygonPostConeEdgeSide parentLabel else
          projectivePolygonPostConeEdgeTargetSide parentLabel) =
            projectivePolygonPostConeEdgeTargetSide parentLabel
        rw [if_neg hnotSource]
      have hface : (⟨parent.right.state⟩ : ProjectivePolygonPostConeFace p) =
          projectivePolygonPostConeEdgeTarget parentLabel := by
        apply ProjectivePolygonPostConeFace.stateEquiv.injective
        exact congrArg ProjectivePolygonPostConeFace.state htarget
      have hstate := congrArg ProjectivePolygonPostConeFace.state hface
      have hterm : canonicalProjectiveConePostConeBoundaryTerm p parent.right.state
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 parent) =
            (FreeGroup.of parentLabel)⁻¹ := by
        rw [hside, hstate]
        exact canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 parentLabel
      exact Or.inr ⟨hface, hside, hterm⟩
  intro hside
  have hparentCarrier' :
      CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p
        parent.right.state childSide parentLabel := by
    change CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p
      parent.right.state
      (canonicalProjectivePostConeRawParentSideForChild hp hp2 parent child) parentLabel
    rw [hside]
    exact hparentCarrier
  have hlabels := canonicalProjectiveConePostConeBoundaryTermPhysicalCarrier_witness_unique
    hchildCarrier hparentCarrier'
  have hslots : child = parent := by
    apply canonicalProjectivePostConeTreeSlotLabel_injective hp hp2
    simpa [childLabel, parentLabel] using hlabels
  subst child
  exact (Nat.lt_irrefl _ hdeep).elim

/-- A child-word position can be lifted to a side-origin position when the
parent's boundary term is the child's deeper-source carrier. The local
off-pivot proof is chosen here, so the side decoder and the term decoder use
the same classifier index. -/
theorem canonicalProjectivePostConeRawSideOrigin_exists_of_deeperSource
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 other →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (s : ProjectivePolygonSide)
    (hsource :
      (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeSource
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) ∧
      s = projectivePolygonPostConeEdgeSide
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) ∧
      canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s =
        FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 child))
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
    (i : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).length) :
    ∃ sideTag : CanonicalProjectivePostConeRawContourSideOriginTag hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s,
      (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot rec s sideTag).1 =
        (rec child hdeep
          (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child i)).1 := by
  classical
  let childLabel := canonicalProjectivePostConeTreeSlotLabel hp hp2 child
  have hparentSource : slot.right = projectivePolygonPostConeEdgeSource childLabel := by
    apply ProjectivePolygonPostConeFace.stateEquiv.injective
    exact congrArg ProjectivePolygonPostConeFace.state hsource.1
  have hparentSide : s = canonicalProjectivePostConeRawParentSideForChild
      hp hp2 slot child := by
    change s = (if slot.right = projectivePolygonPostConeEdgeSource childLabel
      then projectivePolygonPostConeEdgeSide childLabel
      else projectivePolygonPostConeEdgeTargetSide childLabel)
    rw [if_pos hparentSource]
    exact hsource.2.1
  have hjoin := canonicalProjectivePostConeRawContourTermCase_deeperSource_join
    hp hp2 slot child childLabel hsource.1 rfl hdeep
  have hsideNe : canonicalProjectivePostConeRawParentSideForChild hp hp2 slot child ≠
      canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot :=
    canonicalProjectivePostConeRawParentSideForChild_ne_pivot
      hp hp2 slot child hdeep hjoin
  by_cases hs : s = canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot
  · exact False.elim (hsideNe (hparentSide.symm.trans hs))
  ·
    let ih := fun other
        (_hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
          canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other) =>
        canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other
    let c := canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs
    have hcase : c = .deeperSource childLabel child hsource rfl hdeep := by
      exact canonicalProjectivePostConeRawContourTermCase_unique hp hp2 slot s c
        (.deeperSource childLabel child hsource rfl hdeep)
    let tagTypeEq := congrArg
      (CanonicalProjectivePostConeRawContourTermPositionTag hp hp2 slot ih (s := s)) hcase
    let childTermTag : CanonicalProjectivePostConeRawContourTermPositionTag
        hp hp2 slot ih (s := s) (.deeperSource childLabel child hsource rfl hdeep) := i
    let termTag : CanonicalProjectivePostConeRawContourTermPositionTag hp hp2 slot ih
        (s := s) c := Eq.mpr tagTypeEq childTermTag
    let termEquiv := canonicalProjectivePostConeRawContourTerm_positionEquiv
      hp hp2 slot ih s hs
    let termPosition := termEquiv.symm termTag
    let sideEquiv := canonicalProjectivePostConeRawContourSide_positionEquiv
      hp hp2 slot ih s
    let sideTag := sideEquiv termPosition
    refine ⟨sideTag, ?_⟩
    have hterm : canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot rec c
        (termEquiv termPosition) = rec child hdeep
          (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child i) := by
      have hposition : termEquiv termPosition = termTag :=
        Equiv.apply_symm_apply termEquiv termTag
      rw [hposition]
      have htransport := canonicalProjectivePostConeRawTermOrigin_endpoint_eq_rec_of_deeperSource
        hp hp2 slot child rec childLabel hsource rfl hdeep c hcase termTag
      have hcast : Eq.mp tagTypeEq termTag = i := by
        dsimp [termTag, childTermTag]
        exact BoundaryWords.Internal.eq_mp_mpr_cancel tagTypeEq i
      have hdecoded : canonicalProjectivePostConeRawTreeWordBySlot_originEquiv
          hp hp2 child (Eq.mp tagTypeEq termTag) =
            canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child i :=
        congrArg (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child) hcast
      exact htransport.trans (congrArg (rec child hdeep) hdecoded)
    have hside : canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot rec s sideTag =
        canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot rec c
          (termEquiv termPosition) := by
      simp [canonicalProjectivePostConeRawSideOrigin_endpoint, hs,
        ih, sideTag, sideEquiv, termPosition, termEquiv, c]
    exact (congrArg Prod.fst hside).trans
      (by simpa using congrArg Prod.fst hterm)

/-- The same child-position lift for a deeper-target carrier. The local
inverse-reversal changes the sign but preserves the endpoint dart. -/
theorem canonicalProjectivePostConeRawSideOrigin_exists_of_deeperTarget
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 other →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (s : ProjectivePolygonSide)
    (htarget :
      (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeTarget
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) ∧
      s = projectivePolygonPostConeEdgeTargetSide
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) ∧
      canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s =
        (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 child))⁻¹)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
    (i : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).length) :
    ∃ sideTag : CanonicalProjectivePostConeRawContourSideOriginTag hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s,
      (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot rec s sideTag).1 =
        (rec child hdeep
          (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child i)).1 := by
  classical
  let childLabel := canonicalProjectivePostConeTreeSlotLabel hp hp2 child
  have hparentTarget : slot.right = projectivePolygonPostConeEdgeTarget childLabel := by
    apply ProjectivePolygonPostConeFace.stateEquiv.injective
    exact congrArg ProjectivePolygonPostConeFace.state htarget.1
  have hnotSource : slot.right ≠ projectivePolygonPostConeEdgeSource childLabel := by
    intro hsource
    exact (canonicalProjectivePostConeTreeSlot_edgeSource_ne_edgeTarget hp hp2 child)
      (hsource.symm.trans hparentTarget)
  have hparentSide : s = canonicalProjectivePostConeRawParentSideForChild
      hp hp2 slot child := by
    change s = (if slot.right = projectivePolygonPostConeEdgeSource childLabel
      then projectivePolygonPostConeEdgeSide childLabel
      else projectivePolygonPostConeEdgeTargetSide childLabel)
    rw [if_neg hnotSource]
    exact htarget.2.1
  have hjoin := canonicalProjectivePostConeRawContourTermCase_deeperTarget_join
    hp hp2 slot child childLabel htarget.1 rfl hdeep
  have hsideNe : canonicalProjectivePostConeRawParentSideForChild hp hp2 slot child ≠
      canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot :=
    canonicalProjectivePostConeRawParentSideForChild_ne_pivot
      hp hp2 slot child hdeep hjoin
  by_cases hs : s = canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot
  · exact False.elim (hsideNe (hparentSide.symm.trans hs))
  ·
    let ih := fun other
        (_hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
          canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other) =>
        canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other
    let c := canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs
    have hcase : c = .deeperTarget childLabel child htarget rfl hdeep := by
      exact canonicalProjectivePostConeRawContourTermCase_unique hp hp2 slot s c
        (.deeperTarget childLabel child htarget rfl hdeep)
    let tagTypeEq := congrArg
      (CanonicalProjectivePostConeRawContourTermPositionTag hp hp2 slot ih (s := s)) hcase
    let childTermTag : CanonicalProjectivePostConeRawContourTermPositionTag
        hp hp2 slot ih (s := s) (.deeperTarget childLabel child htarget rfl hdeep) := i
    let termTag : CanonicalProjectivePostConeRawContourTermPositionTag hp hp2 slot ih
        (s := s) c := Eq.mpr tagTypeEq childTermTag
    let termEquiv := canonicalProjectivePostConeRawContourTerm_positionEquiv
      hp hp2 slot ih s hs
    let termPosition := termEquiv.symm termTag
    let sideEquiv := canonicalProjectivePostConeRawContourSide_positionEquiv
      hp hp2 slot ih s
    let sideTag := sideEquiv termPosition
    refine ⟨sideTag, ?_⟩
    have hterm : canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot rec c
        (termEquiv termPosition) =
          (fun endpoint => (endpoint.1, !endpoint.2))
            (rec child hdeep
              (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child i)) := by
      have hposition : termEquiv termPosition = termTag :=
        Equiv.apply_symm_apply termEquiv termTag
      rw [hposition]
      have htransport := canonicalProjectivePostConeRawTermOrigin_endpoint_eq_flip_rec_of_deeperTarget
        hp hp2 slot child rec childLabel htarget rfl hdeep c hcase termTag
      have hcast : Eq.mp tagTypeEq termTag = i := by
        dsimp [termTag, childTermTag]
        exact BoundaryWords.Internal.eq_mp_mpr_cancel tagTypeEq i
      have hdecoded : canonicalProjectivePostConeRawTreeWordBySlot_originEquiv
          hp hp2 child (Eq.mp tagTypeEq termTag) =
            canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child i :=
        congrArg (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child) hcast
      exact htransport.trans
        (congrArg (fun endpoint => (endpoint.1, !endpoint.2))
          (congrArg (rec child hdeep) hdecoded))
    have hside : canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot rec s sideTag =
        canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot rec c
          (termEquiv termPosition) := by
      simp [canonicalProjectivePostConeRawSideOrigin_endpoint, hs,
        ih, sideTag, sideEquiv, termPosition, termEquiv, c]
    exact (congrArg Prod.fst hside).trans
      (by simpa using congrArg Prod.fst hterm)

/-- Any origin in an adjacent child slot lifts to an origin in its parent
slot. The physical endpoint orientation selects the corresponding
deeper-source or deeper-target classifier, and the list/splice bridge then
places that occurrence in the parent word. -/
theorem canonicalProjectivePostConeRawTreeWordOrigin_exists_of_child
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (parent child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hjoin : parent.right = child.left)
    (tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child) :
    ∃ parentTag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 parent,
      (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 parent parentTag).1 =
        (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child tag).1 := by
  classical
  let recEndpoint := fun other
      (_hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other) =>
      canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 other
  let childEndpoint := canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child
  let e := canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child
  let i := e.symm tag
  have hi : e i = tag := Equiv.apply_symm_apply e tag
  have hdeep := canonicalProjectivePostConeTreeSlot_targetDepth_lt_of_right_eq_left
    hp hp2 hjoin
  let childLabel := canonicalProjectivePostConeTreeSlotLabel hp hp2 child
  let s := canonicalProjectivePostConeRawParentSideForChild hp hp2 parent child
  rcases canonicalProjectivePostConeTreeSlot_endpoints_eq_physicalEndpoints
      hp hp2 child with hforward | hreverse
  · have hface : parent.right = projectivePolygonPostConeEdgeSource childLabel :=
      hjoin.trans hforward.1
    have hface' : (⟨parent.right.state⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeSource childLabel := by
      apply ProjectivePolygonPostConeFace.stateEquiv.injective
      exact congrArg ProjectivePolygonPostConeFace.state hface
    have hside : s = projectivePolygonPostConeEdgeSide childLabel := by
      change (if parent.right = projectivePolygonPostConeEdgeSource childLabel
        then projectivePolygonPostConeEdgeSide childLabel
        else projectivePolygonPostConeEdgeTargetSide childLabel) = _
      rw [if_pos hface]
    have hstate := congrArg ProjectivePolygonPostConeFace.state hface'
    have hterm : canonicalProjectiveConePostConeBoundaryTerm p parent.right.state s =
        FreeGroup.of childLabel := by
      rw [hside, hstate]
      exact canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq childLabel
    obtain ⟨sideTag, hside⟩ :=
      canonicalProjectivePostConeRawSideOrigin_exists_of_deeperSource
        hp hp2 parent child recEndpoint s ⟨hface', hside, hterm⟩ hdeep i
    have hchildTag : recEndpoint child hdeep (e i) = childEndpoint tag := by
      dsimp [recEndpoint, childEndpoint]
      rw [hi]
    have hside' :
        (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 parent
          recEndpoint s sideTag).1 = (childEndpoint tag).1 := by
      calc
        _ = (recEndpoint child hdeep (e i)).1 := hside
        _ = (childEndpoint tag).1 := congrArg Prod.fst hchildTag
    obtain ⟨parentTag, hparent⟩ :=
      canonicalProjectivePostConeRawTreeWordOrigin_exists_of_sideOrigin
        hp hp2 parent s sideTag (childEndpoint tag) hside'
    exact ⟨parentTag, hparent⟩
  · have hface : parent.right = projectivePolygonPostConeEdgeTarget childLabel :=
      hjoin.trans hreverse.1
    have hface' : (⟨parent.right.state⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeTarget childLabel := by
      apply ProjectivePolygonPostConeFace.stateEquiv.injective
      exact congrArg ProjectivePolygonPostConeFace.state hface
    have hnotSource : parent.right ≠ projectivePolygonPostConeEdgeSource childLabel := by
      intro hsource
      exact (canonicalProjectivePostConeTreeSlot_edgeSource_ne_edgeTarget
        hp hp2 child) (hsource.symm.trans hface)
    have hside : s = projectivePolygonPostConeEdgeTargetSide childLabel := by
      change (if parent.right = projectivePolygonPostConeEdgeSource childLabel
        then projectivePolygonPostConeEdgeSide childLabel
        else projectivePolygonPostConeEdgeTargetSide childLabel) = _
      rw [if_neg hnotSource]
    have hstate := congrArg ProjectivePolygonPostConeFace.state hface'
    have hterm : canonicalProjectiveConePostConeBoundaryTerm p parent.right.state s =
        (FreeGroup.of childLabel)⁻¹ := by
      rw [hside, hstate]
      exact canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 childLabel
    obtain ⟨sideTag, hside⟩ :=
      canonicalProjectivePostConeRawSideOrigin_exists_of_deeperTarget
        hp hp2 parent child recEndpoint s ⟨hface', hside, hterm⟩ hdeep i
    have hchildTag : recEndpoint child hdeep (e i) = childEndpoint tag := by
      dsimp [recEndpoint, childEndpoint]
      rw [hi]
    have hside' :
        (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 parent
          recEndpoint s sideTag).1 = (childEndpoint tag).1 := by
      calc
        _ = (recEndpoint child hdeep (e i)).1 := hside
        _ = (childEndpoint tag).1 := congrArg Prod.fst hchildTag
    obtain ⟨parentTag, hparent⟩ :=
      canonicalProjectivePostConeRawTreeWordOrigin_exists_of_sideOrigin
        hp hp2 parent s sideTag (childEndpoint tag) hside'
    exact ⟨parentTag, hparent⟩

/-- Every non-current classified term origin is in the region of its exact
deeper child. The tag's child position is retained unchanged, including in a
target-oriented term where only the sign is inverted. -/
theorem canonicalProjectivePostConeRawTermOrigin_exists_childRegion_of_ne_current
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (hrec : ∀ (child : CanonicalProjectivePostConeTreeSlot hp hp2)
      (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
      (tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child),
      canonicalProjectivePostConeTreeAncestor hp hp2 child.right
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (rec child hdeep tag).1))
    {s : ProjectivePolygonSide}
    (c : CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s)
    (tag : CanonicalProjectivePostConeRawContourTermPositionTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) c)
    (hnotCurrent : canonicalProjectivePostConeSurvivingDartFace hp hp2
      (canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot rec c tag).1 ≠
        slot.right) :
    ∃ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      slot.right = child.left ∧
        s = canonicalProjectivePostConeRawParentSideForChild hp hp2 slot child ∧
        canonicalProjectivePostConeTreeAncestor hp hp2 child.right
          (canonicalProjectivePostConeSurvivingDartFace hp hp2
            (canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot rec c tag).1) := by
  classical
  cases c with
  | one hterm => exact tag.elim
  | finalSource z hsource hz =>
      have hcurrent : canonicalProjectivePostConeSurvivingDartFace hp hp2
          (canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot rec
            (.finalSource z hsource hz) tag).1 = slot.right := by
        change projectivePolygonPostConeEdgeSource z = slot.right
        exact hsource.1.symm
      exact (hnotCurrent hcurrent).elim
  | finalTarget z htarget hz =>
      have hcurrent : canonicalProjectivePostConeSurvivingDartFace hp hp2
          (canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot rec
            (.finalTarget z htarget hz) tag).1 = slot.right := by
        change projectivePolygonPostConeEdgeTarget z = slot.right
        exact htarget.1.symm
      exact (hnotCurrent hcurrent).elim
  | deeperSource z child hsource hlabel hdeep =>
      have hjoin := canonicalProjectivePostConeRawContourTermCase_deeperSource_join
        hp hp2 slot child z hsource.1 hlabel hdeep
      have hsource' : slot.right = projectivePolygonPostConeEdgeSource
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) := by
        apply ProjectivePolygonPostConeFace.stateEquiv.injective
        have hstate := congrArg ProjectivePolygonPostConeFace.state hsource.1
        rw [hlabel]
        exact hstate
      have hside : s = if slot.right = projectivePolygonPostConeEdgeSource
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 child)
        then projectivePolygonPostConeEdgeSide
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 child)
        else projectivePolygonPostConeEdgeTargetSide
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) := by
        rw [if_pos hsource', hlabel]
        exact hsource.2.1
      exact ⟨child, hjoin, by
        simpa [canonicalProjectivePostConeRawParentSideForChild, hsource'] using hside,
        hrec child hdeep
          (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child tag)⟩
  | deeperTarget z child htarget hlabel hdeep =>
      have hjoin := canonicalProjectivePostConeRawContourTermCase_deeperTarget_join
        hp hp2 slot child z htarget.1 hlabel hdeep
      have htarget' : slot.right = projectivePolygonPostConeEdgeTarget
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) := by
        apply ProjectivePolygonPostConeFace.stateEquiv.injective
        have hstate := congrArg ProjectivePolygonPostConeFace.state htarget.1
        rw [hlabel]
        exact hstate
      have hnotSource : slot.right ≠ projectivePolygonPostConeEdgeSource
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) := by
        intro heq
        exact (canonicalProjectivePostConeTreeSlot_edgeSource_ne_edgeTarget
          hp hp2 child) (heq.symm.trans htarget')
      have hside : s = if slot.right = projectivePolygonPostConeEdgeSource
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 child)
        then projectivePolygonPostConeEdgeSide
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 child)
        else projectivePolygonPostConeEdgeTargetSide
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) := by
        rw [if_neg hnotSource, hlabel]
        exact htarget.2.1
      exact ⟨child, hjoin, by
        simpa [canonicalProjectivePostConeRawParentSideForChild, hnotSource] using hside,
        hrec child hdeep
          (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child tag)⟩

/-- Under injectivity of each deeper slot decoder, a fixed classified term
has no two positions representing the same physical endpoint dart. The
recursive cases reduce exactly to the corresponding child origin. -/
theorem canonicalProjectivePostConeRawTermOrigin_injective_of_children
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child) →
      Function.Injective fun tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child =>
        (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child tag).1)
    {s : ProjectivePolygonSide}
    (c : CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s)
    (tag tag' : CanonicalProjectivePostConeRawContourTermPositionTag hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) c)
    (hsame : (canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child)
      c tag).1 =
        (canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot
          (fun child _ => canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child)
          c tag').1) :
    tag = tag' := by
  cases c with
  | one hterm => exact tag.elim
  | finalSource z hsource hz =>
      change Fin 1 at tag tag'
      apply Fin.ext
      omega
  | finalTarget z htarget hz =>
      change Fin 1 at tag tag'
      apply Fin.ext
      omega
  | deeperSource z child hsource hlabel hdeep =>
      let e := canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child
      have hchild :
          (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child (e tag)).1 =
            (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child (e tag')).1 := by
        exact hsame
      exact e.injective (ih child hdeep hchild)
  | deeperTarget z child htarget hlabel hdeep =>
      let e := canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child
      have hchild :
          (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child (e tag)).1 =
            (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child (e tag')).1 := by
        exact hsame
      exact e.injective (ih child hdeep hchild)

/-- At a fixed side, two raw-term position origins that decode at the
current face must be the same local position. The empty and recursive cases
cannot decode there; each final case is a singleton. This is the
current/current branch of the later rooted-region injectivity argument. -/
theorem canonicalProjectivePostConeRawTermOrigin_eq_of_current
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 other →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (hrec : ∀ other hdeep tag,
      canonicalProjectivePostConeTreeAncestor hp hp2 other.right
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (rec other hdeep tag).1))
    {s : ProjectivePolygonSide}
    (c : CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s)
    (tag tag' : CanonicalProjectivePostConeRawContourTermPositionTag hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
      c)
    (hcurrent : canonicalProjectivePostConeSurvivingDartFace hp hp2
      (canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot rec c tag).1 =
        slot.right) :
    tag = tag' := by
  cases c with
  | one hterm => exact tag.elim
  | finalSource z hsource hz =>
      change Fin 1 at tag tag'
      apply Fin.ext
      omega
  | finalTarget z htarget hz =>
      change Fin 1 at tag tag'
      apply Fin.ext
      omega
  | deeperSource z child hsource hlabel hdeep =>
      exact (canonicalProjectivePostConeRawTermOrigin_deeperSource_not_current
        hp hp2 slot child rec hrec s z hsource hlabel hdeep tag hcurrent).elim
  | deeperTarget z child htarget hlabel hdeep =>
      exact (canonicalProjectivePostConeRawTermOrigin_deeperTarget_not_current
        hp hp2 slot child rec hrec s z htarget hlabel hdeep tag hcurrent).elim

/-- On a non-pivot side, current-vertex decoding is equivalent to its
selected classifier being a final-source or final-target case. -/
theorem canonicalProjectivePostConeRawSideOrigin_endpoint_eq_current_iff_final
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 other →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (hrec : ∀ other hdeep tag,
      canonicalProjectivePostConeTreeAncestor hp hp2 other.right
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (rec other hdeep tag).1))
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)
    (tag : CanonicalProjectivePostConeRawContourSideOriginTag hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s) :
    (canonicalProjectivePostConeSurvivingDartFace hp hp2
      (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot rec s tag).1 =
        slot.right) ↔
      (∃ z hz hsource,
        canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs =
          .finalSource z hsource hz) ∨
      (∃ z hz htarget,
        canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs =
          .finalTarget z htarget hz) := by
  classical
  let i := (canonicalProjectivePostConeRawContourSide_positionEquiv hp hp2 slot
    (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s).symm tag
  let c := canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs
  let ctag := canonicalProjectivePostConeRawContourTerm_positionEquiv
    hp hp2 slot (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
    s hs i
  have hiff := canonicalProjectivePostConeRawTermOrigin_endpoint_eq_current_iff_final
    hp hp2 slot rec hrec c ctag
  simpa [canonicalProjectivePostConeRawSideOrigin_endpoint, dif_neg hs,
    c, ctag] using hiff

/-- If a side-origin decodes to the current face, its side is exactly the
physical side of the decoded dart. The final-source/target classifier carries
this incidence explicitly. -/
theorem canonicalProjectivePostConeRawSideOrigin_side_eq_dartSide_of_current
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 other →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (hrec : ∀ other hdeep tag,
      canonicalProjectivePostConeTreeAncestor hp hp2 other.right
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (rec other hdeep tag).1))
    (s : ProjectivePolygonSide)
    (tag : CanonicalProjectivePostConeRawContourSideOriginTag hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s)
    (hcurrent : canonicalProjectivePostConeSurvivingDartFace hp hp2
      (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot rec s tag).1 =
        slot.right) :
    s = canonicalProjectivePostConeSurvivingDartSide hp hp2
      (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot rec s tag).1 := by
  classical
  by_cases hs : s = canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot
  · have htag : Empty := by
      simpa [CanonicalProjectivePostConeRawContourSideOriginTag, hs] using tag
    exact htag.elim
  · let c := canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs
    let sideEquiv := canonicalProjectivePostConeRawContourSide_positionEquiv hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s
    let termEquiv := canonicalProjectivePostConeRawContourTerm_positionEquiv hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s hs
    let i := sideEquiv.symm tag
    let ctag := termEquiv i
    have hfinal := (canonicalProjectivePostConeRawSideOrigin_endpoint_eq_current_iff_final
      hp hp2 slot rec hrec s hs tag).mp hcurrent
    rcases hfinal with ⟨z, hz, hsource, hcase⟩ | ⟨z, hz, htarget, hcase⟩
    · have hdecoded := canonicalProjectivePostConeRawTermOrigin_endpoint_of_finalSource
        hp hp2 slot rec z hsource hz hcase ctag
      have hsideEndpoint : canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot
          rec s tag = (Sum.inl ⟨z, hz⟩, true) := by
        simpa [canonicalProjectivePostConeRawSideOrigin_endpoint, dif_neg hs,
          c, ctag] using hdecoded
      rw [congrArg Prod.fst hsideEndpoint]
      change s = projectivePolygonPostConeEdgeSide z
      exact hsource.2.1
    · have hdecoded := canonicalProjectivePostConeRawTermOrigin_endpoint_of_finalTarget
        hp hp2 slot rec z htarget hz hcase ctag
      have hsideEndpoint : canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot
          rec s tag = (Sum.inr ⟨z, hz⟩, false) := by
        simpa [canonicalProjectivePostConeRawSideOrigin_endpoint, dif_neg hs,
          c, ctag] using hdecoded
      rw [congrArg Prod.fst hsideEndpoint]
      change s = projectivePolygonPostConeEdgeTargetSide z
      exact htarget.2.1

/-- Any non-current side origin lies in the rooted region of the unique child
slot entered by its selected deeper classifier. This extracts the recursive
child occurrence needed for the global injectivity induction. -/
theorem canonicalProjectivePostConeRawSideOrigin_exists_childRegion_of_ne_current
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (hrec : ∀ child hdeep tag,
      canonicalProjectivePostConeTreeAncestor hp hp2 child.right
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (rec child hdeep tag).1))
    (s : ProjectivePolygonSide)
    (tag : CanonicalProjectivePostConeRawContourSideOriginTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) s)
    (hnotCurrent : canonicalProjectivePostConeSurvivingDartFace hp hp2
      (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot rec s tag).1 ≠
        slot.right) :
    ∃ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      slot.right = child.left ∧
        s = canonicalProjectivePostConeRawParentSideForChild hp hp2 slot child ∧
        canonicalProjectivePostConeTreeAncestor hp hp2 child.right
          (canonicalProjectivePostConeSurvivingDartFace hp hp2
            (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot rec s tag).1) := by
  classical
  by_cases hs : s = canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot
  · have htag : Empty := by
      simpa [CanonicalProjectivePostConeRawContourSideOriginTag, hs] using tag
    exact htag.elim
  · let sideEquiv := canonicalProjectivePostConeRawContourSide_positionEquiv hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) s
    let i := sideEquiv.symm tag
    let c := canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs
    let termEquiv := canonicalProjectivePostConeRawContourTerm_positionEquiv hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) s hs
    let ctag := termEquiv i
    have hsideTerm : canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot
        rec s tag = canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot rec c ctag := by
      simp [canonicalProjectivePostConeRawSideOrigin_endpoint, hs, i, sideEquiv,
        c, ctag, termEquiv]
    have htermNotCurrent : canonicalProjectivePostConeSurvivingDartFace hp hp2
        (canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot rec c ctag).1 ≠
          slot.right := by
      intro hcurrent
      apply hnotCurrent
      rw [hsideTerm]
      exact hcurrent
    have hrec' : ∀ child hdeep childTag,
        canonicalProjectivePostConeTreeAncestor hp hp2 child.right
          (canonicalProjectivePostConeSurvivingDartFace hp hp2
            (rec child hdeep childTag).1) := hrec
    obtain ⟨child, hjoin, hside, hchildRegion⟩ :=
      canonicalProjectivePostConeRawTermOrigin_exists_childRegion_of_ne_current
        hp hp2 slot rec hrec' c ctag htermNotCurrent
    refine ⟨child, hjoin, hside, ?_⟩
    rw [hsideTerm]
    exact hchildRegion

/-- Two origin positions in the same side term cannot decode to the same
 current-face dart unless they are identical. This lifts singleton uniqueness
 through the pivot-aware side-position equivalence. -/
theorem canonicalProjectivePostConeRawSideOrigin_eq_of_current
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 other →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (hrec : ∀ other hdeep tag,
      canonicalProjectivePostConeTreeAncestor hp hp2 other.right
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (rec other hdeep tag).1))
    (s : ProjectivePolygonSide)
    (tag tag' : CanonicalProjectivePostConeRawContourSideOriginTag hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s)
    (hcurrent : canonicalProjectivePostConeSurvivingDartFace hp hp2
      (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot rec s tag).1 =
        slot.right) :
    tag = tag' := by
  classical
  by_cases hs : s = canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot
  · have htag : Empty := by
      simpa [CanonicalProjectivePostConeRawContourSideOriginTag, hs] using tag
    exact htag.elim
  · let c := canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs
    let sideEquiv := canonicalProjectivePostConeRawContourSide_positionEquiv hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s
    let termEquiv := canonicalProjectivePostConeRawContourTerm_positionEquiv hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s hs
    let i := sideEquiv.symm tag
    let i' := sideEquiv.symm tag'
    have htagType : CanonicalProjectivePostConeRawContourTermPositionTag hp hp2 slot
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) c := by
      simpa [CanonicalProjectivePostConeRawContourSideOriginTag, hs, c] using tag
    have htag'Type : CanonicalProjectivePostConeRawContourTermPositionTag hp hp2 slot
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) c := by
      simpa [CanonicalProjectivePostConeRawContourSideOriginTag, hs, c] using tag'
    have htagEq : termEquiv i = termEquiv i' := by
      apply canonicalProjectivePostConeRawTermOrigin_eq_of_current
        hp hp2 slot rec hrec c (termEquiv i) (termEquiv i')
      simpa [canonicalProjectivePostConeRawSideOrigin_endpoint, hs, i, c,
        sideEquiv, termEquiv] using hcurrent
    have hi : i = i' := termEquiv.injective htagEq
    exact sideEquiv.symm.injective hi

/-- Heterogeneous form of current-side origin uniqueness, for use inside a
dependent selected-side sigma. -/
theorem canonicalProjectivePostConeRawSideOrigin_heq_of_current
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 other →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (hrec : ∀ other hdeep tag,
      canonicalProjectivePostConeTreeAncestor hp hp2 other.right
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (rec other hdeep tag).1))
    {s s' : ProjectivePolygonSide}
    (tag : CanonicalProjectivePostConeRawContourSideOriginTag hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s)
    (tag' : CanonicalProjectivePostConeRawContourSideOriginTag hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s')
    (hside : s = s')
    (hcurrent : canonicalProjectivePostConeSurvivingDartFace hp hp2
      (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot rec s tag).1 =
        slot.right) : HEq tag tag' := by
  cases hside
  exact heq_of_eq (canonicalProjectivePostConeRawSideOrigin_eq_of_current
    hp hp2 slot rec hrec s tag tag' hcurrent)

/-- For a fixed polygon side, endpoint decoding is injective by induction on
the strictly deeper child slot. This is the recursive same-side branch of
origin exhaustion. -/
theorem canonicalProjectivePostConeRawSideOrigin_injective_of_children
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child) →
      Function.Injective fun tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child =>
        (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child tag).1)
    (s : ProjectivePolygonSide)
    (tag tag' : CanonicalProjectivePostConeRawContourSideOriginTag hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s)
    (hsame : (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child)
      s tag).1 =
        (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot
          (fun child _ => canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child)
          s tag').1) :
    tag = tag' := by
  classical
  by_cases hs : s = canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot
  · have htag : Empty := by
      simpa [CanonicalProjectivePostConeRawContourSideOriginTag, hs] using tag
    exact htag.elim
  · let c := canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs
    let sideEquiv := canonicalProjectivePostConeRawContourSide_positionEquiv hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s
    let termEquiv := canonicalProjectivePostConeRawContourTerm_positionEquiv hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s hs
    let i := sideEquiv.symm tag
    let i' := sideEquiv.symm tag'
    have htagEq : termEquiv i = termEquiv i' := by
      apply canonicalProjectivePostConeRawTermOrigin_injective_of_children
        hp hp2 slot ih c (termEquiv i) (termEquiv i')
      simpa [canonicalProjectivePostConeRawSideOrigin_endpoint, hs, i, c,
        sideEquiv, termEquiv] using hsame
    have hi : i = i' := termEquiv.injective htagEq
    exact sideEquiv.symm.injective hi

/-- Heterogeneous form of recursive same-side origin injectivity, for
dependent selected-side sigma tags. -/
theorem canonicalProjectivePostConeRawSideOrigin_heq_of_children
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child) →
      Function.Injective fun tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child =>
        (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child tag).1)
    {s s' : ProjectivePolygonSide}
    (tag : CanonicalProjectivePostConeRawContourSideOriginTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) s)
    (tag' : CanonicalProjectivePostConeRawContourSideOriginTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) s')
    (hside : s = s')
    (hsame : (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child)
      s tag).1 =
        (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot
          (fun child _ => canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child)
          s' tag').1) : HEq tag tag' := by
  cases hside
  exact heq_of_eq (canonicalProjectivePostConeRawSideOrigin_injective_of_children
    hp hp2 slot ih s tag tag' hsame)

/-- In a duplicate-free side list, two origins that decode to the same dart
at the current face are equal. The side is recovered from the physical dart,
then the local side-origin uniqueness theorem identifies its position. -/
theorem canonicalProjectivePostConeRawTermsOrigin_eq_of_current
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (hrec : ∀ child hdeep tag,
      canonicalProjectivePostConeTreeAncestor hp hp2 child.right
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (rec child hdeep tag).1))
    (sides : List ProjectivePolygonSide) (hnodup : sides.Nodup)
    (tag tag' : CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
      sides)
    (hcurrent : canonicalProjectivePostConeSurvivingDartFace hp hp2
      (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot rec sides tag).1 =
        slot.right)
    (hsame : (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot rec
      sides tag).1 = (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot rec
        sides tag').1) :
    tag = tag' := by
  classical
  let selected := canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot
    (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
    sides tag
  let selected' := canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot
    (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
    sides tag'
  let endpoint := canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot rec
    sides tag
  let endpoint' := canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot rec
    sides tag'
  let sideEndpoint := canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot rec
    selected.1 selected.2
  let sideEndpoint' := canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot rec
    selected'.1 selected'.2
  have hrepresented := canonicalProjectivePostConeRawTermsOrigin_endpoint_eq_selectedSide
    hp hp2 slot rec sides tag
  have hrepresented' := canonicalProjectivePostConeRawTermsOrigin_endpoint_eq_selectedSide
    hp hp2 slot rec sides tag'
  have hcurrent' : canonicalProjectivePostConeSurvivingDartFace hp hp2 endpoint'.1 =
      slot.right := by
    change canonicalProjectivePostConeSurvivingDartFace hp hp2
        (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot rec sides tag').1 =
      slot.right
    rw [← hsame]
    exact hcurrent
  have hsideCurrent : canonicalProjectivePostConeSurvivingDartFace hp hp2 sideEndpoint.1 =
      slot.right := by
    have hface := congrArg (fun x : Sum _ _ × Bool =>
      canonicalProjectivePostConeSurvivingDartFace hp hp2 x.1) hrepresented
    exact hface.symm.trans hcurrent
  have hsideCurrent' : canonicalProjectivePostConeSurvivingDartFace hp hp2 sideEndpoint'.1 =
      slot.right := by
    have hface := congrArg (fun x : Sum _ _ × Bool =>
      canonicalProjectivePostConeSurvivingDartFace hp hp2 x.1) hrepresented'
    exact hface.symm.trans hcurrent'
  have hside1 := canonicalProjectivePostConeRawSideOrigin_side_eq_dartSide_of_current
    hp hp2 slot rec hrec selected.1 selected.2 hsideCurrent
  have hside2 := canonicalProjectivePostConeRawSideOrigin_side_eq_dartSide_of_current
    hp hp2 slot rec hrec selected'.1 selected'.2 hsideCurrent'
  have hrepresentedSide := congrArg (fun x : Sum _ _ × Bool =>
    canonicalProjectivePostConeSurvivingDartSide hp hp2 x.1) hrepresented
  have hrepresentedSide' := congrArg (fun x : Sum _ _ × Bool =>
    canonicalProjectivePostConeSurvivingDartSide hp hp2 x.1) hrepresented'
  have hphysicalSide := congrArg
    (canonicalProjectivePostConeSurvivingDartSide hp hp2) hsame
  have hselectedSide : selected.1 = selected'.1 := by
    calc
      selected.1 = canonicalProjectivePostConeSurvivingDartSide hp hp2 endpoint.1 :=
        hside1.trans hrepresentedSide.symm
      _ = canonicalProjectivePostConeSurvivingDartSide hp hp2 endpoint'.1 := hphysicalSide
      _ = selected'.1 := hrepresentedSide'.trans hside2.symm
  have hselected : selected = selected' := by
    rw [Sigma.ext_iff]
    exact ⟨hselectedSide,
      canonicalProjectivePostConeRawSideOrigin_heq_of_current
        hp hp2 slot rec hrec selected.2 selected'.2 hselectedSide hsideCurrent⟩
  exact canonicalProjectivePostConeRawTermsOrigin_eq_of_selectedSide_eq
    hp hp2 slot (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
    sides hnodup tag tag' hselected

/-- A non-current origin in a side-list block lies in the region of the
child selected by its local classifier. The selected polygon side is exactly
the side of that child edge at the parent vertex. -/
theorem canonicalProjectivePostConeRawTermsOrigin_exists_childRegion_of_ne_current
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (hrec : ∀ child hdeep tag,
      canonicalProjectivePostConeTreeAncestor hp hp2 child.right
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (rec child hdeep tag).1))
    (sides : List ProjectivePolygonSide)
    (tag : CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
      sides)
    (hnotCurrent : canonicalProjectivePostConeSurvivingDartFace hp hp2
      (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot rec sides tag).1 ≠
        slot.right) :
    ∃ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      slot.right = child.left ∧
        (canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot
          (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
          sides tag).1 =
            canonicalProjectivePostConeRawParentSideForChild hp hp2 slot child ∧
        canonicalProjectivePostConeTreeAncestor hp hp2 child.right
          (canonicalProjectivePostConeSurvivingDartFace hp hp2
            (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot rec sides tag).1) := by
  classical
  let selected := canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot
    (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
    sides tag
  have hrepresented := canonicalProjectivePostConeRawTermsOrigin_endpoint_eq_selectedSide
    hp hp2 slot rec sides tag
  have hsideNotCurrent : canonicalProjectivePostConeSurvivingDartFace hp hp2
      (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot rec
        selected.1 selected.2).1 ≠ slot.right := by
    intro hcurrent
    apply hnotCurrent
    have hface := congrArg (fun x : Sum _ _ × Bool =>
      canonicalProjectivePostConeSurvivingDartFace hp hp2 x.1) hrepresented
    exact hface.trans hcurrent
  obtain ⟨child, hjoin, hside, hchildRegion⟩ :=
    canonicalProjectivePostConeRawSideOrigin_exists_childRegion_of_ne_current
      hp hp2 slot rec hrec selected.1 selected.2 hsideNotCurrent
  refine ⟨child, hjoin, ?_, ?_⟩
  · exact hside
  · rw [← hrepresented] at hchildRegion
    exact hchildRegion

/-- Recursive side-list-origin injectivity. Current origins use the already
proved face-side uniqueness; non-current origins enter a unique first-child
region, and duplicate-free side lists then identify their selected positions. -/
theorem canonicalProjectivePostConeRawTermsOrigin_injective_of_children
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      (_hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child) →
      Function.Injective fun tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child =>
        (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child tag).1)
    (hrec : ∀ (child : CanonicalProjectivePostConeTreeSlot hp hp2)
      (_hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
      (tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child),
      canonicalProjectivePostConeTreeAncestor hp hp2 child.right
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child tag).1))
    (sides : List ProjectivePolygonSide) (hnodup : sides.Nodup)
    (tag tag' : CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
      sides)
    (hsame : (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot
      (fun child _hdeep => canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child)
      sides tag).1 =
        (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot
          (fun child _hdeep => canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child)
          sides tag').1) :
    tag = tag' := by
  classical
  let recEndpoint := fun child
      (_hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child) =>
      canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child
  let selected := canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot
    (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) sides tag
  let selected' := canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot
    (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) sides tag'
  let endpoint := canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot recEndpoint
    sides tag
  let endpoint' := canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot recEndpoint
    sides tag'
  have hrepresented := canonicalProjectivePostConeRawTermsOrigin_endpoint_eq_selectedSide
    hp hp2 slot recEndpoint sides tag
  have hrepresented' := canonicalProjectivePostConeRawTermsOrigin_endpoint_eq_selectedSide
    hp hp2 slot recEndpoint sides tag'
  by_cases hcurrent : canonicalProjectivePostConeSurvivingDartFace hp hp2 endpoint.1 = slot.right
  · exact canonicalProjectivePostConeRawTermsOrigin_eq_of_current hp hp2 slot recEndpoint hrec
      sides hnodup tag tag' hcurrent hsame
  · have hnotCurrent' : canonicalProjectivePostConeSurvivingDartFace hp hp2 endpoint'.1 ≠
        slot.right := by
      intro hcurrent'
      apply hcurrent
      have hface := congrArg (canonicalProjectivePostConeSurvivingDartFace hp hp2) hsame
      exact hface.trans hcurrent'
    obtain ⟨child, hjoin, hside, hchildRegion⟩ :=
      canonicalProjectivePostConeRawTermsOrigin_exists_childRegion_of_ne_current
        hp hp2 slot recEndpoint hrec sides tag hcurrent
    obtain ⟨child', hjoin', hside', hchildRegion'⟩ :=
      canonicalProjectivePostConeRawTermsOrigin_exists_childRegion_of_ne_current
        hp hp2 slot recEndpoint hrec sides tag' hnotCurrent'
    have hfaceEq := congrArg (canonicalProjectivePostConeSurvivingDartFace hp hp2) hsame
    have hchildRegionAtTag :
        canonicalProjectivePostConeTreeAncestor hp hp2 child'.right
          (canonicalProjectivePostConeSurvivingDartFace hp hp2 endpoint.1) := by
      rw [← hfaceEq] at hchildRegion'
      exact hchildRegion'
    have hchild : child = child' :=
      canonicalProjectivePostConeTreeAncestor_firstStep_unique hp hp2 child child'
        hjoin.symm hjoin'.symm hchildRegion hchildRegionAtTag
    have hselectedSide : selected.1 = selected'.1 := by
      calc
        selected.1 = canonicalProjectivePostConeRawParentSideForChild hp hp2 slot child := hside
        _ = canonicalProjectivePostConeRawParentSideForChild hp hp2 slot child' := by
          rw [hchild]
        _ = selected'.1 := hside'.symm
    have hsideDartEq :
        (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot recEndpoint
          selected.1 selected.2).1 =
        (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot recEndpoint
          selected'.1 selected'.2).1 := by
      calc
        _ = endpoint.1 := (congrArg Prod.fst hrepresented).symm
        _ = endpoint'.1 := hsame
        _ = _ := congrArg Prod.fst hrepresented'
    have hselectedHEq := canonicalProjectivePostConeRawSideOrigin_heq_of_children
      hp hp2 slot ih selected.2 selected'.2 hselectedSide hsideDartEq
    have hselectedEq : selected = selected' := by
      rw [Sigma.ext_iff]
      exact ⟨hselectedSide, hselectedHEq⟩
    exact canonicalProjectivePostConeRawTermsOrigin_eq_of_selectedSide_eq
      hp hp2 slot (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
      sides hnodup tag tag' hselectedEq

/-- Origins in different side-list blocks but with the same physical dart
select the same polygon side. Current darts use their physical incidence;
deeper darts use the unique child region and its parent-side label. -/
theorem canonicalProjectivePostConeRawTermsOrigin_selectedSide_eq_of_same_dart
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (hrec : ∀ (child : CanonicalProjectivePostConeTreeSlot hp hp2)
      (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
      (tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child),
      canonicalProjectivePostConeTreeAncestor hp hp2 child.right
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (rec child hdeep tag).1))
    (sides sides' : List ProjectivePolygonSide)
    (tag : CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
      sides)
    (tag' : CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
      sides')
    (hsame : (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot rec sides tag).1 =
      (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot rec sides' tag').1) :
    (canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
      sides tag).1 =
    (canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
      sides' tag').1 := by
  classical
  let selected := canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot
    (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) sides tag
  let selected' := canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot
    (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) sides' tag'
  let endpoint := canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot rec sides tag
  let endpoint' := canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot rec sides' tag'
  have hrepresented := canonicalProjectivePostConeRawTermsOrigin_endpoint_eq_selectedSide
    hp hp2 slot rec sides tag
  have hrepresented' := canonicalProjectivePostConeRawTermsOrigin_endpoint_eq_selectedSide
    hp hp2 slot rec sides' tag'
  by_cases hcurrent : canonicalProjectivePostConeSurvivingDartFace hp hp2 endpoint.1 = slot.right
  · have hcurrent' : canonicalProjectivePostConeSurvivingDartFace hp hp2 endpoint'.1 =
        slot.right := by
      have hface := congrArg (canonicalProjectivePostConeSurvivingDartFace hp hp2) hsame
      exact hface.symm.trans hcurrent
    have hsideCurrent : canonicalProjectivePostConeSurvivingDartFace hp hp2
        (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot rec
          selected.1 selected.2).1 = slot.right := by
      have hface := congrArg (fun x : Sum _ _ × Bool =>
        canonicalProjectivePostConeSurvivingDartFace hp hp2 x.1) hrepresented
      exact hface.symm.trans hcurrent
    have hsideCurrent' : canonicalProjectivePostConeSurvivingDartFace hp hp2
        (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot rec
          selected'.1 selected'.2).1 = slot.right := by
      have hface := congrArg (fun x : Sum _ _ × Bool =>
        canonicalProjectivePostConeSurvivingDartFace hp hp2 x.1) hrepresented'
      exact hface.symm.trans hcurrent'
    have hside1 := canonicalProjectivePostConeRawSideOrigin_side_eq_dartSide_of_current
      hp hp2 slot rec hrec selected.1 selected.2 hsideCurrent
    have hside2 := canonicalProjectivePostConeRawSideOrigin_side_eq_dartSide_of_current
      hp hp2 slot rec hrec selected'.1 selected'.2 hsideCurrent'
    have hrepresentedSide := congrArg (fun x : Sum _ _ × Bool =>
      canonicalProjectivePostConeSurvivingDartSide hp hp2 x.1) hrepresented
    have hrepresentedSide' := congrArg (fun x : Sum _ _ × Bool =>
      canonicalProjectivePostConeSurvivingDartSide hp hp2 x.1) hrepresented'
    have hphysicalSide := congrArg
      (canonicalProjectivePostConeSurvivingDartSide hp hp2) hsame
    calc
      selected.1 = canonicalProjectivePostConeSurvivingDartSide hp hp2 endpoint.1 :=
        hside1.trans hrepresentedSide.symm
      _ = canonicalProjectivePostConeSurvivingDartSide hp hp2 endpoint'.1 := hphysicalSide
      _ = selected'.1 := hrepresentedSide'.trans hside2.symm
  · have hnotCurrent' : canonicalProjectivePostConeSurvivingDartFace hp hp2 endpoint'.1 ≠
        slot.right := by
      intro hcurrent'
      apply hcurrent
      have hface := congrArg (canonicalProjectivePostConeSurvivingDartFace hp hp2) hsame
      exact hface.trans hcurrent'
    obtain ⟨child, hjoin, hside, hchildRegion⟩ :=
      canonicalProjectivePostConeRawTermsOrigin_exists_childRegion_of_ne_current
        hp hp2 slot rec hrec sides tag hcurrent
    obtain ⟨child', hjoin', hside', hchildRegion'⟩ :=
      canonicalProjectivePostConeRawTermsOrigin_exists_childRegion_of_ne_current
        hp hp2 slot rec hrec sides' tag' hnotCurrent'
    have hfaceEq := congrArg (canonicalProjectivePostConeSurvivingDartFace hp hp2) hsame
    have hchildRegionAtTag :
        canonicalProjectivePostConeTreeAncestor hp hp2 child'.right
          (canonicalProjectivePostConeSurvivingDartFace hp hp2 endpoint.1) := by
      rw [← hfaceEq] at hchildRegion'
      exact hchildRegion'
    have hchild : child = child' :=
      canonicalProjectivePostConeTreeAncestor_firstStep_unique hp hp2 child child'
        hjoin.symm hjoin'.symm hchildRegion hchildRegionAtTag
    calc
      selected.1 = canonicalProjectivePostConeRawParentSideForChild hp hp2 slot child := hside
      _ = canonicalProjectivePostConeRawParentSideForChild hp hp2 slot child' := by
        rw [hchild]
      _ = selected'.1 := hside'.symm

/-- Injectivity of the complete recursive slot-origin decoder follows by
induction on child slots. Within one prefix/suffix block use side-list
injectivity; across the two blocks, a physical dart determines a common
selected side, contradicting their disjointness. -/
theorem canonicalProjectivePostConeRawTreeWordOrigin_injective_of_children
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child) →
      Function.Injective fun tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child =>
        (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child tag).1)
    (hrec : ∀ (child : CanonicalProjectivePostConeTreeSlot hp hp2)
      (_hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
      (tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child),
      canonicalProjectivePostConeTreeAncestor hp hp2 child.right
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child tag).1))
    (tag tag' : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 slot)
    (hsame : (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 slot tag).1 =
      (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 slot tag').1) :
    tag = tag' := by
  classical
  let recEndpoint := fun child
      (_hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child) =>
      canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child
  have hsameStep :
      (canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step hp hp2 slot recEndpoint tag).1 =
        (canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step hp hp2 slot recEndpoint tag').1 := by
    unfold canonicalProjectivePostConeRawTreeWordOrigin_endpoint at hsame
    rw [WellFounded.fix_eq] at hsame
    exact hsame
  cases tag with
  | source hsource blocks =>
      cases tag' with
      | source hsource' blocks' =>
          have hsourceEq : hsource = hsource' := Subsingleton.elim _ _
          cases blocks with
          | inl prefixTag =>
              cases blocks' with
              | inl prefixTag' =>
                  have hlistSame :
                      (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot recEndpoint
                        (canonicalProjectivePostConeBoundaryPrefixSides
                          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                        prefixTag).1 =
                      (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot recEndpoint
                        (canonicalProjectivePostConeBoundaryPrefixSides
                          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                        prefixTag').1 := by
                    simpa [canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step] using hsameStep
                  have htag := canonicalProjectivePostConeRawTermsOrigin_injective_of_children
                    hp hp2 slot ih hrec
                    (canonicalProjectivePostConeBoundaryPrefixSides
                      (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                    (canonicalProjectivePostConeBoundaryPrefixSides_nodup _)
                    prefixTag prefixTag' hlistSame
                  cases hsourceEq
                  cases htag
                  rfl
              | inr suffixTag' =>
                  have hlistSame :
                      (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot recEndpoint
                        (canonicalProjectivePostConeBoundaryPrefixSides
                          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                        prefixTag).1 =
                      (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot recEndpoint
                        (canonicalProjectivePostConeBoundarySuffixSides
                          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                        suffixTag').1 := by
                    simpa [canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step] using hsameStep
                  have hside := canonicalProjectivePostConeRawTermsOrigin_selectedSide_eq_of_same_dart
                    hp hp2 slot recEndpoint hrec
                    (canonicalProjectivePostConeBoundaryPrefixSides
                      (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                    (canonicalProjectivePostConeBoundarySuffixSides
                      (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                    prefixTag suffixTag' hlistSame
                  have hprefix := canonicalProjectivePostConeRawTermsOrigin_selectedSide_mem
                    hp hp2 slot
                    (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
                    _ prefixTag
                  have hsuffix := canonicalProjectivePostConeRawTermsOrigin_selectedSide_mem
                    hp hp2 slot
                    (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
                    _ suffixTag'
                  have hboth :
                      (canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot
                        (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
                        _ prefixTag).1 ∈
                        canonicalProjectivePostConeBoundarySuffixSides
                          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) := by
                    rw [hside]
                    exact hsuffix
                  exact False.elim ((canonicalProjectivePostConeBoundaryPrefixSuffix_disjoint
                    (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) _)
                    ⟨hprefix, hboth⟩)
          | inr suffixTag =>
              cases blocks' with
              | inl prefixTag' =>
                  have hlistSame :
                      (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot recEndpoint
                        (canonicalProjectivePostConeBoundarySuffixSides
                          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                        suffixTag).1 =
                      (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot recEndpoint
                        (canonicalProjectivePostConeBoundaryPrefixSides
                          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                        prefixTag').1 := by
                    simpa [canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step] using hsameStep
                  have hside := canonicalProjectivePostConeRawTermsOrigin_selectedSide_eq_of_same_dart
                    hp hp2 slot recEndpoint hrec
                    (canonicalProjectivePostConeBoundarySuffixSides
                      (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                    (canonicalProjectivePostConeBoundaryPrefixSides
                      (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                    suffixTag prefixTag' hlistSame
                  have hsuffix := canonicalProjectivePostConeRawTermsOrigin_selectedSide_mem
                    hp hp2 slot
                    (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
                    _ suffixTag
                  have hprefix := canonicalProjectivePostConeRawTermsOrigin_selectedSide_mem
                    hp hp2 slot
                    (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
                    _ prefixTag'
                  have hprefixAtSuffix :
                      (canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot
                        (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
                        _ suffixTag).1 ∈
                        canonicalProjectivePostConeBoundaryPrefixSides
                          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) := by
                    rw [hside]
                    exact hprefix
                  exact False.elim ((canonicalProjectivePostConeBoundaryPrefixSuffix_disjoint
                    (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) _)
                    ⟨hprefixAtSuffix, hsuffix⟩)
              | inr suffixTag' =>
                  have hlistSame :
                      (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot recEndpoint
                        (canonicalProjectivePostConeBoundarySuffixSides
                          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                        suffixTag).1 =
                      (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot recEndpoint
                        (canonicalProjectivePostConeBoundarySuffixSides
                          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                        suffixTag').1 := by
                    simpa [canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step] using hsameStep
                  have htag := canonicalProjectivePostConeRawTermsOrigin_injective_of_children
                    hp hp2 slot ih hrec
                    (canonicalProjectivePostConeBoundarySuffixSides
                      (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                    (canonicalProjectivePostConeBoundarySuffixSides_nodup _)
                    suffixTag suffixTag' hlistSame
                  cases hsourceEq
                  cases htag
                  rfl
      | target htarget blocks' => exact (htarget hsource).elim
  | target htarget blocks =>
      cases tag' with
      | source hsource blocks' => exact (htarget hsource).elim
      | target htarget' blocks' =>
          have htargetEq : htarget = htarget' := Subsingleton.elim _ _
          cases blocks with
          | inl suffixTag =>
              cases blocks' with
              | inl suffixTag' =>
                  have hlistSame :
                      (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot recEndpoint
                        (canonicalProjectivePostConeBoundarySuffixSides
                          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                        suffixTag).1 =
                      (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot recEndpoint
                        (canonicalProjectivePostConeBoundarySuffixSides
                          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                        suffixTag').1 := by
                    simpa [canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step] using hsameStep
                  have htag := canonicalProjectivePostConeRawTermsOrigin_injective_of_children
                    hp hp2 slot ih hrec
                    (canonicalProjectivePostConeBoundarySuffixSides
                      (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                    (canonicalProjectivePostConeBoundarySuffixSides_nodup _)
                    suffixTag suffixTag' hlistSame
                  cases htargetEq
                  cases htag
                  rfl
              | inr prefixTag' =>
                  have hlistSame :
                      (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot recEndpoint
                        (canonicalProjectivePostConeBoundarySuffixSides
                          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                        suffixTag).1 =
                      (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot recEndpoint
                        (canonicalProjectivePostConeBoundaryPrefixSides
                          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                        prefixTag').1 := by
                    simpa [canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step] using hsameStep
                  have hside := canonicalProjectivePostConeRawTermsOrigin_selectedSide_eq_of_same_dart
                    hp hp2 slot recEndpoint hrec
                    (canonicalProjectivePostConeBoundarySuffixSides
                      (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                    (canonicalProjectivePostConeBoundaryPrefixSides
                      (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                    suffixTag prefixTag' hlistSame
                  have hsuffix := canonicalProjectivePostConeRawTermsOrigin_selectedSide_mem
                    hp hp2 slot
                    (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
                    _ suffixTag
                  have hprefix := canonicalProjectivePostConeRawTermsOrigin_selectedSide_mem
                    hp hp2 slot
                    (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
                    _ prefixTag'
                  have hsuffixAtPrefix :
                      (canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot
                        (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
                        _ suffixTag).1 ∈
                        canonicalProjectivePostConeBoundaryPrefixSides
                          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) := by
                    rw [hside]
                    exact hprefix
                  exact False.elim ((canonicalProjectivePostConeBoundaryPrefixSuffix_disjoint
                    (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) _)
                    ⟨hsuffixAtPrefix, hsuffix⟩)
           | inr prefixTag =>
             cases blocks' with
             | inl suffixTag' =>
                  have hlistSame :
                      (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot recEndpoint
                        (canonicalProjectivePostConeBoundaryPrefixSides
                          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                        prefixTag).1 =
                      (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot recEndpoint
                        (canonicalProjectivePostConeBoundarySuffixSides
                          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                        suffixTag').1 := by
                    simpa [canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step] using hsameStep
                  have hside := canonicalProjectivePostConeRawTermsOrigin_selectedSide_eq_of_same_dart
                    hp hp2 slot recEndpoint hrec
                    (canonicalProjectivePostConeBoundaryPrefixSides
                      (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                    (canonicalProjectivePostConeBoundarySuffixSides
                      (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                    prefixTag suffixTag' hlistSame
                  have hprefix := canonicalProjectivePostConeRawTermsOrigin_selectedSide_mem
                    hp hp2 slot
                    (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
                    _ prefixTag
                  have hsuffix := canonicalProjectivePostConeRawTermsOrigin_selectedSide_mem
                    hp hp2 slot
                    (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
                    _ suffixTag'
                  have hprefixAtSuffix :
                      (canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot
                        (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
                        _ prefixTag).1 ∈
                        canonicalProjectivePostConeBoundarySuffixSides
                          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) := by
                    rw [hside]
                    exact hsuffix
                  exact False.elim ((canonicalProjectivePostConeBoundaryPrefixSuffix_disjoint
                    (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) _)
                    ⟨hprefix, hprefixAtSuffix⟩)
             | inr prefixTag' =>
                  have hlistSame :
                      (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot recEndpoint
                        (canonicalProjectivePostConeBoundaryPrefixSides
                          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                        prefixTag).1 =
                      (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot recEndpoint
                        (canonicalProjectivePostConeBoundaryPrefixSides
                          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                        prefixTag').1 := by
                    simpa [canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step] using hsameStep
                  have htag := canonicalProjectivePostConeRawTermsOrigin_injective_of_children
                    hp hp2 slot ih hrec
                    (canonicalProjectivePostConeBoundaryPrefixSides
                      (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
                    (canonicalProjectivePostConeBoundaryPrefixSides_nodup _)
                    prefixTag prefixTag' hlistSame
                  cases htargetEq
                  cases htag
                  rfl

/-- If a side's selected classifier is a deeper-source case, none of its
origin tags can decode at the parent vertex. -/
theorem canonicalProjectivePostConeRawSideOrigin_endpoint_ne_current_of_deeperSource
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 other →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (hrec : ∀ other hdeep tag,
      canonicalProjectivePostConeTreeAncestor hp hp2 other.right
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (rec other hdeep tag).1))
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hsource :
      (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeSource z ∧
      s = projectivePolygonPostConeEdgeSide z ∧
      canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s = FreeGroup.of z)
    (hlabel : canonicalProjectivePostConeTreeSlotLabel hp hp2 child = z)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
    (tag : CanonicalProjectivePostConeRawContourSideOriginTag hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s) :
    canonicalProjectivePostConeSurvivingDartFace hp hp2
      (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot rec s tag).1 ≠
        slot.right := by
  intro hcurrent
  have hfinal :=
    (canonicalProjectivePostConeRawSideOrigin_endpoint_eq_current_iff_final
      hp hp2 slot rec hrec s hs tag).mp hcurrent
  have hclass : canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs =
      .deeperSource z child hsource hlabel hdeep :=
    canonicalProjectivePostConeRawContourTermCase_unique hp hp2 slot s
      (canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs)
      (.deeperSource z child hsource hlabel hdeep)
  rcases hfinal with ⟨z', hz', hsource', hcase⟩ | ⟨z', hz', htarget', hcase⟩
  · rw [show canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs =
      .deeperSource z child hsource hlabel hdeep from hclass] at hcase
    cases hcase
  · rw [show canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs =
      .deeperSource z child hsource hlabel hdeep from hclass] at hcase
    cases hcase

/-- Target-oriented counterpart of the side-origin parent separation lemma. -/
theorem canonicalProjectivePostConeRawSideOrigin_endpoint_ne_current_of_deeperTarget
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 other →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (hrec : ∀ other hdeep tag,
      canonicalProjectivePostConeTreeAncestor hp hp2 other.right
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (rec other hdeep tag).1))
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (htarget :
      (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeTarget z ∧
      s = projectivePolygonPostConeEdgeTargetSide z ∧
      canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s =
        (FreeGroup.of z)⁻¹)
    (hlabel : canonicalProjectivePostConeTreeSlotLabel hp hp2 child = z)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
    (tag : CanonicalProjectivePostConeRawContourSideOriginTag hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s) :
    canonicalProjectivePostConeSurvivingDartFace hp hp2
      (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot rec s tag).1 ≠
        slot.right := by
  intro hcurrent
  have hfinal :=
    (canonicalProjectivePostConeRawSideOrigin_endpoint_eq_current_iff_final
      hp hp2 slot rec hrec s hs tag).mp hcurrent
  have hclass : canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs =
      .deeperTarget z child htarget hlabel hdeep :=
    canonicalProjectivePostConeRawContourTermCase_unique hp hp2 slot s
      (canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs)
      (.deeperTarget z child htarget hlabel hdeep)
  rcases hfinal with ⟨z', hz', hsource', hcase⟩ | ⟨z', hz', htarget', hcase⟩
  · rw [show canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs =
      .deeperTarget z child htarget hlabel hdeep from hclass] at hcase
    cases hcase
  · rw [show canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs =
      .deeperTarget z child htarget hlabel hdeep from hclass] at hcase
    cases hcase

/-- Lift a side origin into the ordered side-list while preserving separation
from the current vertex. -/
theorem canonicalProjectivePostConeRawTermsOrigin_exists_of_mem_ne_current
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (sides : List ProjectivePolygonSide) (s : ProjectivePolygonSide)
    (hs : s ∈ sides)
    (tag : CanonicalProjectivePostConeRawContourSideOriginTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) s)
    (hside : canonicalProjectivePostConeSurvivingDartFace hp hp2
      (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot rec s tag).1 ≠
        slot.right) :
    ∃ listTag : CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot
        (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
        sides,
      canonicalProjectivePostConeSurvivingDartFace hp hp2
        (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot rec
          sides listTag).1 ≠ slot.right := by
  obtain ⟨listTag, hlist⟩ :=
    canonicalProjectivePostConeRawTermsOrigin_endpoint_exists_of_mem
      hp hp2 slot rec sides s hs tag
  refine ⟨listTag, ?_⟩
  intro hcurrent
  apply hside
  rw [← hlist]
  exact hcurrent

/-- Current-vertex decoding for a nested side-list tag is classified by the
selected side's term case. The non-pivot hypothesis follows from the side tag
itself, but is explicit here to keep the dependent classifier transparent. -/
theorem canonicalProjectivePostConeRawTermsOrigin_endpoint_eq_current_iff_final
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (hrec : ∀ child hdeep tag,
      canonicalProjectivePostConeTreeAncestor hp hp2 child.right
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (rec child hdeep tag).1))
    (sides : List ProjectivePolygonSide)
    (tag : CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
      sides)
    (hs : (canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
      sides tag).1 ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) :
    (canonicalProjectivePostConeSurvivingDartFace hp hp2
      (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot rec sides tag).1 =
        slot.right) ↔
      (∃ z hz hsource,
        canonicalProjectivePostConeRawContourTermCase hp hp2 slot
          (canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot
            (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
            sides tag).1 hs = .finalSource z hsource hz) ∨
      (∃ z hz htarget,
        canonicalProjectivePostConeRawContourTermCase hp hp2 slot
          (canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot
            (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
            sides tag).1 hs = .finalTarget z htarget hz) := by
  rw [canonicalProjectivePostConeRawTermsOrigin_endpoint_eq_selectedSide]
  exact canonicalProjectivePostConeRawSideOrigin_endpoint_eq_current_iff_final
    hp hp2 slot rec hrec
    (canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
      sides tag).1 hs
    (canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
      sides tag).2

/-- Proposition that the selected term classifier of a side-list origin is a
final physical source or target, with the pivot exclusion proof obtained from
the existence of the side tag itself. -/
noncomputable def canonicalProjectivePostConeRawTermsOrigin_isFinalClassifier
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (sides : List ProjectivePolygonSide)
    (tag : CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
      sides) : Prop := by
  let selected := canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot
    (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
    sides tag
  let hs := canonicalProjectivePostConeRawTermsOrigin_selectedSide_ne_pivot
    hp hp2 slot
    (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
    sides tag
  exact (∃ z hz hsource,
      canonicalProjectivePostConeRawContourTermCase hp hp2 slot selected.1 hs =
        .finalSource z hsource hz) ∨
    (∃ z hz htarget,
      canonicalProjectivePostConeRawContourTermCase hp hp2 slot selected.1 hs =
        .finalTarget z htarget hz)

/-- The list classifier predicate is equivalent to the decoded endpoint lying
at the current vertex. This packages the selected-side pivot proof so callers
can transfer current/non-current facts without comparing dependent tags. -/
theorem canonicalProjectivePostConeRawTermsOrigin_isFinalClassifier_iff_current
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (hrec : ∀ child hdeep tag,
      canonicalProjectivePostConeTreeAncestor hp hp2 child.right
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (rec child hdeep tag).1))
    (sides : List ProjectivePolygonSide)
    (tag : CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
      sides) :
    canonicalProjectivePostConeRawTermsOrigin_isFinalClassifier
        hp hp2 slot sides tag ↔
      canonicalProjectivePostConeSurvivingDartFace hp hp2
        (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot rec
          sides tag).1 = slot.right := by
  let hs := canonicalProjectivePostConeRawTermsOrigin_selectedSide_ne_pivot
    hp hp2 slot
    (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
    sides tag
  simpa [canonicalProjectivePostConeRawTermsOrigin_isFinalClassifier, hs] using
    (canonicalProjectivePostConeRawTermsOrigin_endpoint_eq_current_iff_final
      hp hp2 slot rec hrec sides tag hs).symm

/-- The final-classifier predicate follows exactly the ordered prefix/suffix
and source/target block ordering of a complete slot-origin tag. -/
def canonicalProjectivePostConeRawTreeWordOriginTag_isFinalClassifier
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 slot → Prop
  | .source _ (.inl tag) =>
      canonicalProjectivePostConeRawTermsOrigin_isFinalClassifier hp hp2 slot
        (canonicalProjectivePostConeBoundaryPrefixSides
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) tag
  | .source _ (.inr tag) =>
      canonicalProjectivePostConeRawTermsOrigin_isFinalClassifier hp hp2 slot
        (canonicalProjectivePostConeBoundarySuffixSides
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) tag
  | .target _ (.inl tag) =>
      canonicalProjectivePostConeRawTermsOrigin_isFinalClassifier hp hp2 slot
        (canonicalProjectivePostConeBoundarySuffixSides
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) tag
  | .target _ (.inr tag) =>
      canonicalProjectivePostConeRawTermsOrigin_isFinalClassifier hp hp2 slot
        (canonicalProjectivePostConeBoundaryPrefixSides
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) tag

/-- Side-origin decoding preserves the same rooted-region invariant; the
pivot side has no origin and every other side delegates to its term case. -/
theorem canonicalProjectivePostConeRawSideOrigin_endpoint_region
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (hrec : ∀ child hdeep tag,
      canonicalProjectivePostConeTreeAncestor hp hp2 child.right
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (rec child hdeep tag).1))
    (s : ProjectivePolygonSide)
    (tag : CanonicalProjectivePostConeRawContourSideOriginTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) s) :
    canonicalProjectivePostConeTreeAncestor hp hp2 slot.right
      (canonicalProjectivePostConeSurvivingDartFace hp hp2
        (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot rec s tag).1) := by
  classical
  by_cases hs : s = canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot
  · have htag : Empty := by
      simpa [CanonicalProjectivePostConeRawContourSideOriginTag, hs] using tag
    exact htag.elim
  · let i := (canonicalProjectivePostConeRawContourSide_positionEquiv hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) s).symm tag
    let c := canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs
    let ctag := canonicalProjectivePostConeRawContourTerm_positionEquiv
      hp hp2 slot (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
      s hs i
    have hterm := canonicalProjectivePostConeRawTermOrigin_endpoint_region
      hp hp2 slot rec hrec c ctag
    simpa [canonicalProjectivePostConeRawSideOrigin_endpoint, dif_neg hs] using hterm

/-- The ordered side-list fold preserves the rooted-region invariant at
each list origin, including duplicate side values at distinct offsets. -/
theorem canonicalProjectivePostConeRawTermsOrigin_endpoint_region
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (hrec : ∀ child hdeep tag,
      canonicalProjectivePostConeTreeAncestor hp hp2 child.right
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (rec child hdeep tag).1))
    (sides : List ProjectivePolygonSide)
    (tag : CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
      sides) :
    canonicalProjectivePostConeTreeAncestor hp hp2 slot.right
      (canonicalProjectivePostConeSurvivingDartFace hp hp2
        (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot rec sides tag).1) := by
  induction sides with
  | nil => exact tag.elim
  | cons s sides ih =>
      cases tag with
      | inl sideTag =>
          simpa [canonicalProjectivePostConeRawTermsOrigin_endpoint] using
            canonicalProjectivePostConeRawSideOrigin_endpoint_region
              hp hp2 slot rec hrec s sideTag
      | inr tailTag =>
          simpa [canonicalProjectivePostConeRawTermsOrigin_endpoint] using ih tailTag

/-- One complete slot splice preserves the rooted-region invariant. -/
theorem canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step_region
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (hrec : ∀ child hdeep tag,
      canonicalProjectivePostConeTreeAncestor hp hp2 child.right
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (rec child hdeep tag).1))
    (tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 slot) :
    canonicalProjectivePostConeTreeAncestor hp hp2 slot.right
      (canonicalProjectivePostConeSurvivingDartFace hp hp2
        (canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step hp hp2 slot rec tag).1) := by
  cases tag with
  | source hsource blocks =>
      cases blocks with
      | inl origin =>
          exact canonicalProjectivePostConeRawTermsOrigin_endpoint_region
            hp hp2 slot rec hrec
            (canonicalProjectivePostConeBoundaryPrefixSides
              (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) origin
      | inr origin =>
          exact canonicalProjectivePostConeRawTermsOrigin_endpoint_region
            hp hp2 slot rec hrec
            (canonicalProjectivePostConeBoundarySuffixSides
              (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) origin
  | target htarget blocks =>
      cases blocks with
      | inl origin =>
          exact canonicalProjectivePostConeRawTermsOrigin_endpoint_region
            hp hp2 slot rec hrec
            (canonicalProjectivePostConeBoundarySuffixSides
              (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) origin
      | inr origin =>
          exact canonicalProjectivePostConeRawTermsOrigin_endpoint_region
            hp hp2 slot rec hrec
            (canonicalProjectivePostConeBoundaryPrefixSides
              (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) origin

/-- By well-founded induction on the finite tree, every recursively decoded
slot origin lies below its slot's right vertex. -/
theorem canonicalProjectivePostConeRawTreeWordOrigin_endpoint_region
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 slot) :
    canonicalProjectivePostConeTreeAncestor hp hp2 slot.right
      (canonicalProjectivePostConeSurvivingDartFace hp hp2
        (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 slot tag).1) := by
  classical
  refine ((canonicalProjectivePostConeDirectTreeDependencyWellFounded hp hp2).induction
    (C := fun slot => ∀ tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 slot,
      canonicalProjectivePostConeTreeAncestor hp hp2 slot.right
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 slot tag).1))
    slot ?_) tag
  intro slot ih tag
  unfold canonicalProjectivePostConeRawTreeWordOrigin_endpoint
  rw [WellFounded.fix_eq]
  exact canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step_region
    hp hp2 slot
    (fun child _ => canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child)
    (fun child hdeep tag => ih child hdeep tag) tag

/-- Recursive endpoint decoding is injective on complete slot-origin tags.
This follows by well-founded induction from child injectivity and the fact
that the ordered prefix/suffix blocks are disjoint. -/
theorem canonicalProjectivePostConeRawTreeWordOrigin_injective
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (tag tag' : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 slot)
    (hsame : (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 slot tag).1 =
      (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 slot tag').1) :
    tag = tag' := by
  classical
  refine ((canonicalProjectivePostConeDirectTreeDependencyWellFounded hp hp2).induction
    (C := fun slot => ∀ (tag tag' :
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 slot),
      (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 slot tag).1 =
        (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 slot tag').1 →
      tag = tag')
    slot ?_) tag tag' hsame
  intro slot ih tag tag' hsame
  let recEndpoint := fun child
      (_hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child) =>
      canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child
  have hrec : ∀ child hdeep childTag,
      canonicalProjectivePostConeTreeAncestor hp hp2 child.right
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (recEndpoint child hdeep childTag).1) := by
    intro child hdeep childTag
    exact canonicalProjectivePostConeRawTreeWordOrigin_endpoint_region
      hp hp2 child childTag
  exact canonicalProjectivePostConeRawTreeWordOrigin_injective_of_children
    hp hp2 slot ih hrec tag tag' hsame

/-- Distinct literal positions in a recursive slot word decode to distinct
physical endpoint occurrences. -/
theorem canonicalProjectivePostConeRawTreeWordPosition_endpoint_injective
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (i j : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot).length)
    (hsame : (canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 slot i).1 =
      (canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 slot j).1) :
    i = j := by
  let e := canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 slot
  apply e.injective
  exact canonicalProjectivePostConeRawTreeWordOrigin_injective hp hp2 slot (e i) (e j) hsame

/-- For a complete slot-origin tag, current-vertex decoding is equivalent
to a final source/target classifier in its selected side-list block. -/
theorem canonicalProjectivePostConeRawTreeWordOrigin_endpoint_eq_current_iff_final
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 slot) :
    (canonicalProjectivePostConeSurvivingDartFace hp hp2
      (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 slot tag).1 =
        slot.right) ↔
      canonicalProjectivePostConeRawTreeWordOriginTag_isFinalClassifier
        hp hp2 slot tag := by
  let recEndpoint := fun child
      (_hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child) =>
      canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child
  have hrec : ∀ child hdeep childTag,
      canonicalProjectivePostConeTreeAncestor hp hp2 child.right
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (recEndpoint child hdeep childTag).1) := by
    intro child hdeep childTag
    exact canonicalProjectivePostConeRawTreeWordOrigin_endpoint_region
      hp hp2 child childTag
  cases tag with
  | source hsource blocks =>
      cases blocks with
      | inl listTag =>
          have hlist := canonicalProjectivePostConeRawTermsOrigin_endpoint_eq_current_iff_final
            hp hp2 slot recEndpoint hrec
            (canonicalProjectivePostConeBoundaryPrefixSides
              (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
            listTag
            (canonicalProjectivePostConeRawTermsOrigin_selectedSide_ne_pivot hp hp2 slot
              (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
              (canonicalProjectivePostConeBoundaryPrefixSides
                (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
              listTag)
          unfold canonicalProjectivePostConeRawTreeWordOrigin_endpoint
          rw [WellFounded.fix_eq]
          change (canonicalProjectivePostConeSurvivingDartFace hp hp2
            (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot recEndpoint
              (canonicalProjectivePostConeBoundaryPrefixSides
                (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
              listTag).1 = slot.right) ↔
            canonicalProjectivePostConeRawTermsOrigin_isFinalClassifier hp hp2 slot
              (canonicalProjectivePostConeBoundaryPrefixSides
                (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
              listTag
          exact hlist
      | inr listTag =>
          have hlist := canonicalProjectivePostConeRawTermsOrigin_endpoint_eq_current_iff_final
            hp hp2 slot recEndpoint hrec
            (canonicalProjectivePostConeBoundarySuffixSides
              (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
            listTag
            (canonicalProjectivePostConeRawTermsOrigin_selectedSide_ne_pivot hp hp2 slot
              (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
              (canonicalProjectivePostConeBoundarySuffixSides
                (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
              listTag)
          unfold canonicalProjectivePostConeRawTreeWordOrigin_endpoint
          rw [WellFounded.fix_eq]
          change (canonicalProjectivePostConeSurvivingDartFace hp hp2
            (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot recEndpoint
              (canonicalProjectivePostConeBoundarySuffixSides
                (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
              listTag).1 = slot.right) ↔
            canonicalProjectivePostConeRawTermsOrigin_isFinalClassifier hp hp2 slot
              (canonicalProjectivePostConeBoundarySuffixSides
                (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
              listTag
          exact hlist
  | target htarget blocks =>
      cases blocks with
      | inl listTag =>
          have hlist := canonicalProjectivePostConeRawTermsOrigin_endpoint_eq_current_iff_final
            hp hp2 slot recEndpoint hrec
            (canonicalProjectivePostConeBoundarySuffixSides
              (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
            listTag
            (canonicalProjectivePostConeRawTermsOrigin_selectedSide_ne_pivot hp hp2 slot
              (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
              (canonicalProjectivePostConeBoundarySuffixSides
                (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
              listTag)
          unfold canonicalProjectivePostConeRawTreeWordOrigin_endpoint
          rw [WellFounded.fix_eq]
          change (canonicalProjectivePostConeSurvivingDartFace hp hp2
            (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot recEndpoint
              (canonicalProjectivePostConeBoundarySuffixSides
                (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
              listTag).1 = slot.right) ↔
            canonicalProjectivePostConeRawTermsOrigin_isFinalClassifier hp hp2 slot
              (canonicalProjectivePostConeBoundarySuffixSides
                (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
              listTag
          exact hlist
      | inr listTag =>
          have hlist := canonicalProjectivePostConeRawTermsOrigin_endpoint_eq_current_iff_final
            hp hp2 slot recEndpoint hrec
            (canonicalProjectivePostConeBoundaryPrefixSides
              (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
            listTag
            (canonicalProjectivePostConeRawTermsOrigin_selectedSide_ne_pivot hp hp2 slot
              (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
              (canonicalProjectivePostConeBoundaryPrefixSides
                (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
              listTag)
          unfold canonicalProjectivePostConeRawTreeWordOrigin_endpoint
          rw [WellFounded.fix_eq]
          change (canonicalProjectivePostConeSurvivingDartFace hp hp2
            (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot recEndpoint
              (canonicalProjectivePostConeBoundaryPrefixSides
                (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
              listTag).1 = slot.right) ↔
            canonicalProjectivePostConeRawTermsOrigin_isFinalClassifier hp hp2 slot
              (canonicalProjectivePostConeBoundaryPrefixSides
                (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
              listTag
          exact hlist

/-- Any complete slot origin whose selected side classifier is deeper than
the current face is disjoint from the current vertex. -/
theorem canonicalProjectivePostConeRawTreeWordOrigin_endpoint_ne_current_of_not_final
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 slot)
    (hnotFinal : ¬ canonicalProjectivePostConeRawTreeWordOriginTag_isFinalClassifier
      hp hp2 slot tag) :
    canonicalProjectivePostConeSurvivingDartFace hp hp2
      (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 slot tag).1 ≠
        slot.right := by
  intro hcurrent
  exact hnotFinal
    ((canonicalProjectivePostConeRawTreeWordOrigin_endpoint_eq_current_iff_final
      hp hp2 slot tag).mp hcurrent)

/-- Every raw slot-word position decodes to a dart in the rooted region of
that slot's right endpoint. -/
theorem canonicalProjectivePostConeRawTreeWordPosition_endpoint_region
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (i : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot).length) :
    canonicalProjectivePostConeSurvivingDartInRegion hp hp2 slot.right
      (canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 slot i).1 := by
  exact canonicalProjectivePostConeRawTreeWordOrigin_endpoint_region hp hp2 slot
    ((canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 slot) i)

/-- Every root-term provenance tag decodes to a dart in the global rooted
region. In a tree case the classifier's deleted edge is the first child edge
at the root, so the already-proved local child-region invariant applies. -/
theorem canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint_region
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (s : ProjectivePolygonSide)
    (c : CanonicalProjectivePostConeRawRootContourTermCase hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state s)
    (tag : CanonicalProjectivePostConeRawRootContourTermPositionTag hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state s c) :
    canonicalProjectivePostConeSurvivingDartInRegion hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2)
      (canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
        hp hp2 c tag).1 := by
  let root := canonicalProjectivePostConeTreeRoot hp hp2
  have hrootState : (⟨root.state⟩ : ProjectivePolygonPostConeFace p) = root := by
    exact ProjectivePolygonPostConeFace.stateEquiv.symm_apply_apply root
  cases c with
  | one hone => exact tag.elim
  | finalSource z hsource hz =>
      have hface : projectivePolygonPostConeEdgeSource z = root :=
        hsource.1.symm.trans hrootState
      change canonicalProjectivePostConeTreeAncestor hp hp2 root
        (projectivePolygonPostConeEdgeSource z)
      rw [hface]
      exact canonicalProjectivePostConeTreeAncestor_refl hp hp2 _
  | finalTarget z htarget hz =>
      have hface : projectivePolygonPostConeEdgeTarget z = root :=
        htarget.1.symm.trans hrootState
      change canonicalProjectivePostConeTreeAncestor hp hp2 root
        (projectivePolygonPostConeEdgeTarget z)
      rw [hface]
      exact canonicalProjectivePostConeTreeAncestor_refl hp hp2 _
  | treeSource z hsource hz =>
      let child := canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz
      have hincident : projectivePolygonPostConeEdgeSource z = root :=
        hsource.1.symm.trans hrootState
      have hleft := canonicalProjectivePostConeDirectTreeSlot_left_eq_root_of_endpoint
        hp hp2 z hz (Or.inl hincident)
      have hrootChild : canonicalProjectivePostConeTreeAncestor hp hp2 root child.right := by
        simpa [child, hleft] using canonicalProjectivePostConeTreeAncestor_of_slot
          hp hp2 child
      have hlocal := canonicalProjectivePostConeRawTreeWordPosition_endpoint_region
        hp hp2 child tag
      change canonicalProjectivePostConeTreeAncestor hp hp2 root
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
            hp hp2 (.treeSource z hsource hz) tag).1)
      simpa [canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint,
        child, root] using
          canonicalProjectivePostConeTreeAncestor_trans
          hp hp2 hrootChild hlocal
  | treeTarget z htarget hz =>
      let child := canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz
      have hincident : projectivePolygonPostConeEdgeTarget z = root :=
        htarget.1.symm.trans hrootState
      have hleft := canonicalProjectivePostConeDirectTreeSlot_left_eq_root_of_endpoint
        hp hp2 z hz (Or.inr hincident)
      have hrootChild : canonicalProjectivePostConeTreeAncestor hp hp2 root child.right := by
        simpa [child, hleft] using canonicalProjectivePostConeTreeAncestor_of_slot
          hp hp2 child
      have hlocal := canonicalProjectivePostConeRawTreeWordPosition_endpoint_region
        hp hp2 child tag
      change canonicalProjectivePostConeTreeAncestor hp hp2 root
        (canonicalProjectivePostConeSurvivingDartFace hp hp2
          (canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
            hp hp2 (.treeTarget z htarget hz) tag).1)
      simpa [canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint,
        child, root] using
          canonicalProjectivePostConeTreeAncestor_trans
          hp hp2 hrootChild hlocal

/-- A nested root-side-list tag always decodes to a dart below the root. -/
theorem canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint_region
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (sides : List ProjectivePolygonSide)
    (tag : CanonicalProjectivePostConeRawRootContourTermsPositionTag hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state sides) :
    canonicalProjectivePostConeSurvivingDartInRegion hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2)
      (canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2
        (canonicalProjectivePostConeTreeRoot hp hp2).state sides tag).1 := by
  induction sides with
  | nil => cases tag
  | cons s ss ih =>
      cases tag with
      | inl head =>
          exact canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint_region
            hp hp2 s
            (canonicalProjectivePostConeRawRootContourTermCase hp hp2
              (canonicalProjectivePostConeTreeRoot hp hp2).state s)
            ((canonicalProjectivePostConeRawRootContourTerm_positionEquiv hp hp2
              (canonicalProjectivePostConeTreeRoot hp hp2).state s) head)
      | inr tail => exact ih tail

/-- Convert a root-contour index to its physical endpoint dart by first
decoding its exact side and term provenance tag. -/
noncomputable def canonicalProjectivePostConeRawRootContourPosition_endpoint
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length) :
    CanonicalProjectivePostConeSurvivingDart hp hp2 :=
  (canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2
    (canonicalProjectivePostConeTreeRoot hp hp2).state
    canonicalProjectivePostConeBoundarySideCycle
    (canonicalProjectivePostConeRawRootContour_positionEquiv hp hp2 i)).1

/-- Every decoded root-contour dart lies in the full rooted region. -/
theorem canonicalProjectivePostConeRawRootContourPosition_endpoint_region
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length) :
    canonicalProjectivePostConeSurvivingDartInRegion hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2)
      (canonicalProjectivePostConeRawRootContourPosition_endpoint hp hp2 i) := by
  exact canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint_region
    hp hp2 canonicalProjectivePostConeBoundarySideCycle
    (canonicalProjectivePostConeRawRootContour_positionEquiv hp hp2 i)

/-- Reading a root-contour index recovers the exact signed letter decoded
from its endpoint provenance. -/
theorem canonicalProjectivePostConeRawRootContourPosition_endpoint_get
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length) :
    (canonicalProjectivePostConeRawRootContour hp hp2).get i =
      canonicalProjectivePostConeEndpointSignedLetter hp hp2
        (canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2
          (canonicalProjectivePostConeTreeRoot hp hp2).state
          canonicalProjectivePostConeBoundarySideCycle
          (canonicalProjectivePostConeRawRootContour_positionEquiv hp hp2 i)) := by
  let e := canonicalProjectivePostConeRawRootContour_positionEquiv hp hp2
  have h := canonicalProjectivePostConeRawRootContour_positionEquiv_get hp hp2 (e i)
  have hindex : e.symm (e i) = i := e.symm_apply_apply i
  rw [hindex] at h
  simpa [e, canonicalProjectivePostConeRawRootContour_positionEquiv] using h

/-- Every retained dart based at the root face has a root-side provenance
tag whose endpoint is that exact source/target occurrence. This is the
current-face branch of root-contour coverage; descendant darts still require
the first-child lift. -/
private theorem canonicalProjectivePostConeRawRootTermEndpointTag_cast
    {α : Type*} {β : Type*} {P : α → Type*}
    (f : ∀ a, P a → β) {a b : α} (h : a = b) (x : P b) :
    f a (h.symm ▸ x) = f b x := by
  cases h
  rfl

theorem canonicalProjectivePostConeRawRootContourTermsPositionTag_exists_of_root_current_dart
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2)
    (hface : canonicalProjectivePostConeSurvivingDartFace hp hp2 d =
      canonicalProjectivePostConeTreeRoot hp hp2) :
    ∃ tag : CanonicalProjectivePostConeRawRootContourTermsPositionTag hp hp2
        (canonicalProjectivePostConeTreeRoot hp hp2).state
        canonicalProjectivePostConeBoundarySideCycle,
      canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2
        (canonicalProjectivePostConeTreeRoot hp hp2).state
        canonicalProjectivePostConeBoundarySideCycle tag =
          (d, canonicalProjectivePostConeSurvivingDartPositive hp hp2 d) := by
  classical
  cases d with
  | inl z =>
      change projectivePolygonPostConeEdgeSource z.1 =
        canonicalProjectivePostConeTreeRoot hp hp2 at hface
      let q := (canonicalProjectivePostConeTreeRoot hp hp2).state
      let s := projectivePolygonPostConeEdgeSide z.1
      have hs : s ∈ canonicalProjectivePostConeBoundarySideCycle := by
        cases hgen : z.1.1.1.2 <;>
          simp [s, projectivePolygonPostConeEdgeSide,
            ProjectiveOctagonGenerator.positivePolygonSide,
            canonicalProjectivePostConeBoundarySideCycle, hgen]
      have hstate : (projectivePolygonPostConeEdgeSource z.1).state = q := by
        exact congrArg ProjectivePolygonPostConeFace.state hface
      have hsourceFace : (⟨q⟩ : ProjectivePolygonPostConeFace p) =
          projectivePolygonPostConeEdgeSource z.1 := by
        apply ProjectivePolygonPostConeFace.stateEquiv.injective
        change q = (projectivePolygonPostConeEdgeSource z.1).state
        exact hstate.symm
      have hboundaryTerm : canonicalProjectiveConePostConeBoundaryTerm p q s =
          FreeGroup.of z.1 := by
        rw [← hstate]
        simpa [s] using canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq z.1
      let finalCase := CanonicalProjectivePostConeRawRootContourTermCase.finalSource
        z.1 ⟨hsourceFace, rfl, hboundaryTerm⟩ z.2
      have hcase : canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s =
          finalCase := by
        simpa [finalCase, q, s] using
          canonicalProjectivePostConeRawRootContourTermCase_eq_finalSource_of_root_source
            hp hp2 z.1 z.2 hface
      have hzeta :
          (⟨z.1, z.2⟩ : CanonicalProjectivePostConeFinalGenerator hp hp2) = z :=
        Subtype.eta z z.2
      have zeroTag : CanonicalProjectivePostConeRawRootContourTermPositionTag hp hp2
          q s finalCase := by
        change Fin 1
        exact ⟨0, by decide⟩
      let termTag : CanonicalProjectivePostConeRawRootContourTermPositionTag hp hp2
          q s (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s) :=
        hcase.symm ▸ zeroTag
      let e := canonicalProjectivePostConeRawRootContourTerm_positionEquiv hp hp2 q s
      let i : Fin (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s).length :=
        e.symm termTag
      have hdecode :
          canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint hp hp2
            (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s)
            (e i) = (Sum.inl z, true) := by
        have htransport := canonicalProjectivePostConeRawRootTermEndpointTag_cast
          (fun c t => canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
            hp hp2 c t) hcase zeroTag
        calc
          canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint hp hp2
              (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s) (e i) =
              canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint hp hp2
                (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s)
                termTag := by
                  congr 1
                  exact Equiv.apply_symm_apply e termTag
          _ = canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint hp hp2
                finalCase zeroTag := htransport
          _ = (Sum.inl z, true) := by
                simp [finalCase,
                  canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint,
                  hzeta]
      obtain ⟨tag, htag⟩ :=
        canonicalProjectivePostConeRawRootContourTermsPositionTag_exists_of_mem
          hp hp2 q canonicalProjectivePostConeBoundarySideCycle s hs i
      refine ⟨tag, ?_⟩
      rw [htag]
      simpa [q, canonicalProjectivePostConeSurvivingDartPositive] using hdecode
  | inr z =>
      change projectivePolygonPostConeEdgeTarget z.1 =
        canonicalProjectivePostConeTreeRoot hp hp2 at hface
      let q := (canonicalProjectivePostConeTreeRoot hp hp2).state
      let s := projectivePolygonPostConeEdgeTargetSide z.1
      have hs : s ∈ canonicalProjectivePostConeBoundarySideCycle := by
        cases s <;> simp [canonicalProjectivePostConeBoundarySideCycle]
      have hstate : (projectivePolygonPostConeEdgeTarget z.1).state = q := by
        exact congrArg ProjectivePolygonPostConeFace.state hface
      have htargetFace : (⟨q⟩ : ProjectivePolygonPostConeFace p) =
          projectivePolygonPostConeEdgeTarget z.1 := by
        apply ProjectivePolygonPostConeFace.stateEquiv.injective
        change q = (projectivePolygonPostConeEdgeTarget z.1).state
        exact hstate.symm
      have hboundaryTerm : canonicalProjectiveConePostConeBoundaryTerm p q s =
          (FreeGroup.of z.1)⁻¹ := by
        rw [← hstate]
        simpa [s, projectivePolygonPostConeEdgeTargetSide] using
          canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 z.1
      let finalCase := CanonicalProjectivePostConeRawRootContourTermCase.finalTarget
        z.1 ⟨htargetFace, rfl, hboundaryTerm⟩ z.2
      have hcase : canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s =
          finalCase := by
        simpa [finalCase, q, s] using
          canonicalProjectivePostConeRawRootContourTermCase_eq_finalTarget_of_root_target
            hp hp2 z.1 z.2 hface
      have hzeta :
          (⟨z.1, z.2⟩ : CanonicalProjectivePostConeFinalGenerator hp hp2) = z :=
        Subtype.eta z z.2
      have zeroTag : CanonicalProjectivePostConeRawRootContourTermPositionTag hp hp2
          q s finalCase := by
        change Fin 1
        exact ⟨0, by decide⟩
      let termTag : CanonicalProjectivePostConeRawRootContourTermPositionTag hp hp2
          q s (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s) :=
        hcase.symm ▸ zeroTag
      let e := canonicalProjectivePostConeRawRootContourTerm_positionEquiv hp hp2 q s
      let i : Fin (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s).length :=
        e.symm termTag
      have hdecode :
          canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint hp hp2
            (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s)
            (e i) = (Sum.inr z, false) := by
        have htransport := canonicalProjectivePostConeRawRootTermEndpointTag_cast
          (fun c t => canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
            hp hp2 c t) hcase zeroTag
        calc
          canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint hp hp2
              (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s) (e i) =
              canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint hp hp2
                (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s)
                termTag := by
                  congr 1
                  exact Equiv.apply_symm_apply e termTag
          _ = canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint hp hp2
                finalCase zeroTag := htransport
          _ = (Sum.inr z, false) := by
                simp [finalCase,
                  canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint,
                  hzeta]
      obtain ⟨tag, htag⟩ :=
        canonicalProjectivePostConeRawRootContourTermsPositionTag_exists_of_mem
          hp hp2 q canonicalProjectivePostConeBoundarySideCycle s hs i
      refine ⟨tag, ?_⟩
      rw [htag]
      simpa [q, canonicalProjectivePostConeSurvivingDartPositive] using hdecode

/-- Every surviving dart in a slot's rooted tree region has a complete
slot-word origin. At the current vertex this is the local side/list bridge;
below it, the dart is lifted through its unique first child at each step. -/
theorem canonicalProjectivePostConeRawTreeWordOrigin_exists_of_region
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2)
    (hd : canonicalProjectivePostConeSurvivingDartInRegion hp hp2 slot.right d) :
    ∃ tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 slot,
      (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 slot tag).1 = d := by
  classical
  refine (canonicalProjectivePostConeDirectTreeDependencyWellFounded hp hp2).induction
    (C := fun slot => ∀ d : CanonicalProjectivePostConeSurvivingDart hp hp2,
      canonicalProjectivePostConeSurvivingDartInRegion hp hp2 slot.right d →
        ∃ tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 slot,
          (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 slot tag).1 = d)
    slot ?_ d hd
  intro slot ih d hd
  rcases canonicalProjectivePostConeSurvivingDart_region_current_or_child
      hp hp2 slot.right d hd with hcurrent | hchild
  · have hface : canonicalProjectivePostConeSurvivingDartFace hp hp2 d =
        (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) := by
      apply ProjectivePolygonPostConeFace.stateEquiv.injective
      change (canonicalProjectivePostConeSurvivingDartFace hp hp2 d).state =
        slot.right.state
      exact congrArg (fun v : CanonicalProjectivePostConeTreeVertex hp hp2 => v.1)
        hcurrent
    exact canonicalProjectivePostConeSurvivingDart_exists_current_slotOrigin
      hp hp2 slot d hface
  · rcases hchild with ⟨child, ⟨hleft, hchildRegion⟩, _hunique⟩
    have hjoin : slot.right = child.left := hleft.symm
    have hdeep := canonicalProjectivePostConeTreeSlot_targetDepth_lt_of_right_eq_left
      hp hp2 hjoin
    obtain ⟨childTag, hchildTag⟩ := ih child hdeep d hchildRegion
    obtain ⟨parentTag, hparentTag⟩ :=
      canonicalProjectivePostConeRawTreeWordOrigin_exists_of_child
        hp hp2 slot child hjoin childTag
    exact ⟨parentTag, hparentTag.trans hchildTag⟩

/-- The region-origin theorem gives a literal position in the local raw
slot word, not merely an abstract recursively nested provenance tag. -/
theorem canonicalProjectivePostConeRawTreeWordPosition_exists_of_region
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2)
    (hd : canonicalProjectivePostConeSurvivingDartInRegion hp hp2 slot.right d) :
    ∃ i : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot).length,
      (canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 slot i).1 = d := by
  obtain ⟨tag, htag⟩ :=
    canonicalProjectivePostConeRawTreeWordOrigin_exists_of_region hp hp2 slot d hd
  let e := canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 slot
  refine ⟨e.symm tag, ?_⟩
  simpa [canonicalProjectivePostConeRawTreeWordPosition_endpoint, e] using htag

/-- The local unreduced slot-word positions are in bijection with the
physical surviving darts in the rooted region at the slot's right vertex.
This packages recursive occurrence exhaustion together with endpoint
injectivity. -/
noncomputable def canonicalProjectivePostConeRawTreeWordPosition_regionEquiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot).length ≃
      canonicalProjectivePostConeSurvivingDartRegion hp hp2 slot.right :=
  Equiv.ofBijective
    (fun i =>
      ⟨(canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 slot i).1,
        canonicalProjectivePostConeRawTreeWordPosition_endpoint_region hp hp2 slot i⟩)
    ⟨by
      intro i j hij
      apply canonicalProjectivePostConeRawTreeWordPosition_endpoint_injective
        hp hp2 slot
      exact congrArg Subtype.val hij,
    by
      intro d
      obtain ⟨i, hi⟩ := canonicalProjectivePostConeRawTreeWordPosition_exists_of_region
        hp hp2 slot d.1 d.2
      refine ⟨i, ?_⟩
      exact Subtype.ext hi⟩

/-- A whole child slot's rooted region is represented in the root contour
through the deleted edge's unique root-side expansion. The endpoint tag
retains the exact physical dart, including target-side orientation flips. -/
theorem canonicalProjectivePostConeRawRootContourTermsPositionTag_exists_of_root_child_region
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hleft : child.left = canonicalProjectivePostConeTreeRoot hp hp2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2)
    (hd : canonicalProjectivePostConeSurvivingDartInRegion hp hp2 child.right d) :
    ∃ i : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).length,
      ∃ tag : CanonicalProjectivePostConeRawRootContourTermsPositionTag hp hp2
        (canonicalProjectivePostConeTreeRoot hp hp2).state
        canonicalProjectivePostConeBoundarySideCycle,
      (canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 child i).1 = d ∧
      canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2
        (canonicalProjectivePostConeTreeRoot hp hp2).state
        canonicalProjectivePostConeBoundarySideCycle tag =
        canonicalProjectivePostConeFlipSignedLetter
          (!canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 child)
          (canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 child i) := by
  classical
  let root := canonicalProjectivePostConeTreeRoot hp hp2
  let q := root.state
  let z := canonicalProjectivePostConeTreeSlotLabel hp hp2 child
  have hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z :=
    ⟨child, rfl⟩
  have hslot : canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz = child :=
    canonicalProjectivePostConeDirectTreeSlotOfDeleted_eq_of_label hp hp2 z hz child rfl
  obtain ⟨i, hi⟩ := canonicalProjectivePostConeRawTreeWordPosition_exists_of_region
    hp hp2 child d hd
  rcases canonicalProjectivePostConeTreeSlot_left_eq_physicalSource_or_target
      hp hp2 child with hsource | htarget
  · have hrootSource : projectivePolygonPostConeEdgeSource z = root :=
      hsource.symm.trans hleft
    let s := projectivePolygonPostConeEdgeSide z
    have hs : s ∈ canonicalProjectivePostConeBoundarySideCycle := by
      cases s <;> simp [canonicalProjectivePostConeBoundarySideCycle]
    have hstate : (projectivePolygonPostConeEdgeSource z).state = q :=
      congrArg ProjectivePolygonPostConeFace.state hrootSource
    have hsourceFace : (⟨q⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeSource z := by
      apply ProjectivePolygonPostConeFace.stateEquiv.injective
      change q = (projectivePolygonPostConeEdgeSource z).state
      exact hstate.symm
    have hboundaryTerm : canonicalProjectiveConePostConeBoundaryTerm p q s =
        FreeGroup.of z := by
      rw [← hstate]
      simpa [s] using canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq z
    let treeCase := CanonicalProjectivePostConeRawRootContourTermCase.treeSource
      z ⟨hsourceFace, rfl, hboundaryTerm⟩ hz
    have hcase : canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s =
        treeCase := by
      simpa [treeCase, q, root, s] using
        canonicalProjectivePostConeRawRootContourTermCase_eq_treeSource_of_root_source
          hp hp2 z hz hrootSource
    let baseTag : CanonicalProjectivePostConeRawRootContourTermPositionTag hp hp2
        q s treeCase := by
      change Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2
        (canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz)).length
      exact hslot.symm ▸ i
    have hbase : canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
        hp hp2 treeCase baseTag =
          canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 child i := by
      have htransport := canonicalProjectivePostConeRawRootTermEndpointTag_cast
        (fun slot j => canonicalProjectivePostConeRawTreeWordPosition_endpoint
          hp hp2 slot j) hslot i
      simpa [treeCase, canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint,
        baseTag, id] using htransport
    let termTag : CanonicalProjectivePostConeRawRootContourTermPositionTag hp hp2
        q s (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s) :=
      hcase.symm ▸ baseTag
    let e := canonicalProjectivePostConeRawRootContourTerm_positionEquiv hp hp2 q s
    let k : Fin (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s).length :=
      e.symm termTag
    have hdecode :
        canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint hp hp2
          (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s) (e k) =
          canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 child i := by
      have htransport := canonicalProjectivePostConeRawRootTermEndpointTag_cast
        (fun c t => canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
          hp hp2 c t) hcase baseTag
      calc
        canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint hp hp2
            (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s) (e k) =
            canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint hp hp2
              (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s) termTag := by
                exact congrArg (canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
                  hp hp2 (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s))
                  (Equiv.apply_symm_apply e termTag)
        _ = canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint hp hp2
              treeCase baseTag := htransport
        _ = canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 child i := hbase
    obtain ⟨tag, htag⟩ :=
      canonicalProjectivePostConeRawRootContourTermsPositionTag_exists_of_mem
        hp hp2 q canonicalProjectivePostConeBoundarySideCycle s hs k
    have hleftbit :=
      canonicalProjectivePostConeRawSlotLeftSourceBit_eq_true_of_left_source
        hp hp2 child hsource
    refine ⟨i, tag, hi, ?_⟩
    rw [hleftbit]
    exact htag.trans hdecode
  · have hrootTarget : projectivePolygonPostConeEdgeTarget z = root :=
      htarget.symm.trans hleft
    let s := projectivePolygonPostConeEdgeTargetSide z
    have hs : s ∈ canonicalProjectivePostConeBoundarySideCycle := by
      cases s <;> simp [canonicalProjectivePostConeBoundarySideCycle]
    have hstate : (projectivePolygonPostConeEdgeTarget z).state = q :=
      congrArg ProjectivePolygonPostConeFace.state hrootTarget
    have htargetFace : (⟨q⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeTarget z := by
      apply ProjectivePolygonPostConeFace.stateEquiv.injective
      change q = (projectivePolygonPostConeEdgeTarget z).state
      exact hstate.symm
    have hboundaryTerm : canonicalProjectiveConePostConeBoundaryTerm p q s =
        (FreeGroup.of z)⁻¹ := by
      rw [← hstate]
      dsimp [s, projectivePolygonPostConeEdgeTargetSide]
      exact canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 z
    let treeCase := CanonicalProjectivePostConeRawRootContourTermCase.treeTarget
      z ⟨htargetFace, rfl, hboundaryTerm⟩ hz
    have hcase : canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s =
        treeCase := by
      simpa [treeCase, q, root, s] using
        canonicalProjectivePostConeRawRootContourTermCase_eq_treeTarget_of_root_target
          hp hp2 z hz hrootTarget
    let baseTag : CanonicalProjectivePostConeRawRootContourTermPositionTag hp hp2
        q s treeCase := by
      change Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2
        (canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz)).length
      exact hslot.symm ▸ i
    have hbase : canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
        hp hp2 treeCase baseTag =
          (fun endpoint => (endpoint.1, !endpoint.2))
            (canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 child i) := by
      have htransport := canonicalProjectivePostConeRawRootTermEndpointTag_cast
        (fun slot j => canonicalProjectivePostConeRawTreeWordPosition_endpoint
          hp hp2 slot j) hslot i
      have hflip := congrArg (fun endpoint : Sum _ _ × Bool => (endpoint.1, !endpoint.2))
        htransport
      simpa [treeCase, canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint,
        baseTag, id] using hflip
    let termTag : CanonicalProjectivePostConeRawRootContourTermPositionTag hp hp2
        q s (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s) :=
      hcase.symm ▸ baseTag
    let e := canonicalProjectivePostConeRawRootContourTerm_positionEquiv hp hp2 q s
    let k : Fin (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s).length :=
      e.symm termTag
    have hdecode :
        canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint hp hp2
          (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s) (e k) =
          (fun endpoint => (endpoint.1, !endpoint.2))
            (canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 child i) := by
      have htransport := canonicalProjectivePostConeRawRootTermEndpointTag_cast
        (fun c t => canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
          hp hp2 c t) hcase baseTag
      calc
        canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint hp hp2
            (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s) (e k) =
            canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint hp hp2
              (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s) termTag := by
                exact congrArg (canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
                  hp hp2 (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s))
                  (Equiv.apply_symm_apply e termTag)
        _ = canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint hp hp2
              treeCase baseTag := htransport
        _ = (fun endpoint => (endpoint.1, !endpoint.2))
              (canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 child i) := hbase
    obtain ⟨tag, htag⟩ :=
      canonicalProjectivePostConeRawRootContourTermsPositionTag_exists_of_mem
        hp hp2 q canonicalProjectivePostConeBoundarySideCycle s hs k
    have hleftbit :=
      canonicalProjectivePostConeRawSlotLeftSourceBit_eq_false_of_left_target
        hp hp2 child htarget
    refine ⟨i, tag, hi, ?_⟩
    rw [hleftbit]
    exact htag.trans hdecode

/-- Every surviving physical dart in the root's tree region is represented by
some nested side/term position tag in the literal root contour. The proof
uses the disjoint current-face/first-child partition and preserves the
occurrence provenance at every stage. -/
theorem canonicalProjectivePostConeRawRootContourTermsPositionTag_exists_of_region
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2)
    (hd : canonicalProjectivePostConeSurvivingDartInRegion hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2) d) :
    ∃ tag : CanonicalProjectivePostConeRawRootContourTermsPositionTag hp hp2
        (canonicalProjectivePostConeTreeRoot hp hp2).state
        canonicalProjectivePostConeBoundarySideCycle,
      ∃ sign : Bool,
        canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2
          (canonicalProjectivePostConeTreeRoot hp hp2).state
          canonicalProjectivePostConeBoundarySideCycle tag = (d, sign) := by
  rcases canonicalProjectivePostConeSurvivingDart_region_current_or_child
      hp hp2 (canonicalProjectivePostConeTreeRoot hp hp2) d hd with
    hcurrent | hchild
  · have hface : canonicalProjectivePostConeSurvivingDartFace hp hp2 d =
        canonicalProjectivePostConeTreeRoot hp hp2 := by
      apply ProjectivePolygonPostConeFace.stateEquiv.injective
      change (canonicalProjectivePostConeSurvivingDartFace hp hp2 d).state =
        (canonicalProjectivePostConeTreeRoot hp hp2).state
      exact congrArg (fun v : CanonicalProjectivePostConeTreeVertex hp hp2 => v.1)
        hcurrent
    obtain ⟨tag, htag⟩ :=
      canonicalProjectivePostConeRawRootContourTermsPositionTag_exists_of_root_current_dart
        hp hp2 d hface
    exact ⟨tag, canonicalProjectivePostConeSurvivingDartPositive hp hp2 d, htag⟩
  · rcases hchild with ⟨child, ⟨hleft, hregion⟩, _hunique⟩
    obtain ⟨i, tag, hi, htag⟩ :=
      canonicalProjectivePostConeRawRootContourTermsPositionTag_exists_of_root_child_region
        hp hp2 child hleft d hregion
    refine ⟨tag,
      (canonicalProjectivePostConeFlipSignedLetter
        (!canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 child)
        (canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 child i)).2,
      ?_⟩
    calc
      canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2
          (canonicalProjectivePostConeTreeRoot hp hp2).state
          canonicalProjectivePostConeBoundarySideCycle tag =
        canonicalProjectivePostConeFlipSignedLetter
          (!canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 child)
          (canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 child i) := htag
      _ = (d, (canonicalProjectivePostConeFlipSignedLetter
          (!canonicalProjectivePostConeRawSlotLeftSourceBit hp hp2 child)
          (canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 child i)).2) := by
        apply Prod.ext
        · simpa [canonicalProjectivePostConeFlipSignedLetter] using hi
        · rfl

/-- The root-contour endpoint decoder is surjective onto the physical dart
occurrence type. Its injectivity is a separate uniqueness/exhaustion lemma. -/
theorem canonicalProjectivePostConeRawRootContourPosition_endpoint_surjective
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Surjective (canonicalProjectivePostConeRawRootContourPosition_endpoint
      hp hp2) := by
  intro d
  obtain ⟨tag, sign, htag⟩ :=
    canonicalProjectivePostConeRawRootContourTermsPositionTag_exists_of_region
      hp hp2 d (canonicalProjectivePostConeSurvivingDart_mem_rootRegion hp hp2 d)
  let e := canonicalProjectivePostConeRawRootContour_positionEquiv hp hp2
  refine ⟨e.symm tag, ?_⟩
  simpa [canonicalProjectivePostConeRawRootContourPosition_endpoint, e] using
    congrArg Prod.fst htag

/-- For a decoded dart based at the root, the selected boundary side is the
physical side of that dart. -/
theorem canonicalProjectivePostConeRawRootContourTermPositionTag_side_eq_dartSide_of_current
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (s : ProjectivePolygonSide)
    (c : CanonicalProjectivePostConeRawRootContourTermCase hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state s)
    (tag : CanonicalProjectivePostConeRawRootContourTermPositionTag hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state s c)
    (hcurrent : canonicalProjectivePostConeSurvivingDartFace hp hp2
      (canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
        hp hp2 c tag).1 = canonicalProjectivePostConeTreeRoot hp hp2) :
    s = canonicalProjectivePostConeSurvivingDartSide hp hp2
      (canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
        hp hp2 c tag).1 := by
  let root := canonicalProjectivePostConeTreeRoot hp hp2
  have hrootState : (⟨root.state⟩ : ProjectivePolygonPostConeFace p) = root := by
    exact ProjectivePolygonPostConeFace.stateEquiv.symm_apply_apply root
  cases c with
  | one hone => exact tag.elim
  | finalSource z hsource hz =>
      change s = projectivePolygonPostConeEdgeSide z
      exact hsource.2.1
  | finalTarget z htarget hz =>
      change s = projectivePolygonPostConeEdgeTargetSide z
      exact htarget.2.1
  | treeSource z hsource hz =>
      let child := canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz
      have hincident : projectivePolygonPostConeEdgeSource z = root :=
        hsource.1.symm.trans hrootState
      have hleft := canonicalProjectivePostConeDirectTreeSlot_left_eq_root_of_endpoint
        hp hp2 z hz (Or.inl hincident)
      have hregion : canonicalProjectivePostConeSurvivingDartInRegion hp hp2 child.right
          (canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 child tag).1 :=
        canonicalProjectivePostConeRawTreeWordPosition_endpoint_region hp hp2 child tag
      have hnot := canonicalProjectivePostConeSurvivingDart_childRegion_ne_parent
        hp hp2 child _ hregion
      have hfaceNe : canonicalProjectivePostConeSurvivingDartFace hp hp2
          (canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
            hp hp2 (.treeSource z hsource hz) tag).1 ≠ root := by
        change canonicalProjectivePostConeSurvivingDartFace hp hp2
          (canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 child tag).1 ≠ root
        intro hface
        exact hnot (hface.trans hleft.symm)
      exact False.elim (hfaceNe hcurrent)
  | treeTarget z htarget hz =>
      let child := canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz
      have hincident : projectivePolygonPostConeEdgeTarget z = root :=
        htarget.1.symm.trans hrootState
      have hleft := canonicalProjectivePostConeDirectTreeSlot_left_eq_root_of_endpoint
        hp hp2 z hz (Or.inr hincident)
      have hregion : canonicalProjectivePostConeSurvivingDartInRegion hp hp2 child.right
          (canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 child tag).1 :=
        canonicalProjectivePostConeRawTreeWordPosition_endpoint_region hp hp2 child tag
      have hnot := canonicalProjectivePostConeSurvivingDart_childRegion_ne_parent
        hp hp2 child _ hregion
      have hfaceNe : canonicalProjectivePostConeSurvivingDartFace hp hp2
          (canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
            hp hp2 (.treeTarget z htarget hz) tag).1 ≠ root := by
        change canonicalProjectivePostConeSurvivingDartFace hp hp2
          (canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 child tag).1 ≠ root
        intro hface
        exact hnot (hface.trans hleft.symm)
      exact False.elim (hfaceNe hcurrent)

/-- A non-current root-term tag lies in a unique direct-child region, and its
selected root side is the boundary side of that child slot. -/
theorem canonicalProjectivePostConeRawRootContourTermPositionTag_child_side
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (s : ProjectivePolygonSide)
    (c : CanonicalProjectivePostConeRawRootContourTermCase hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state s)
    (tag : CanonicalProjectivePostConeRawRootContourTermPositionTag hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state s c)
    (hnotcurrent : canonicalProjectivePostConeSurvivingDartFace hp hp2
      (canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
        hp hp2 c tag).1 ≠ canonicalProjectivePostConeTreeRoot hp hp2) :
    ∃ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      child.left = canonicalProjectivePostConeTreeRoot hp hp2 ∧
        s = canonicalProjectivePostConeTreeSlot_leftBoundarySide hp hp2 child ∧
        canonicalProjectivePostConeSurvivingDartInRegion hp hp2 child.right
          (canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
            hp hp2 c tag).1 := by
  let root := canonicalProjectivePostConeTreeRoot hp hp2
  have hrootState : (⟨root.state⟩ : ProjectivePolygonPostConeFace p) = root := by
    exact ProjectivePolygonPostConeFace.stateEquiv.symm_apply_apply root
  cases c with
  | one hone => exact tag.elim
  | finalSource z hsource hz =>
      have hface : canonicalProjectivePostConeSurvivingDartFace hp hp2
          (canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
            hp hp2 (.finalSource z hsource hz) tag).1 = root := by
        change projectivePolygonPostConeEdgeSource z = root
        exact hsource.1.symm.trans hrootState
      exact False.elim (hnotcurrent hface)
  | finalTarget z htarget hz =>
      have hface : canonicalProjectivePostConeSurvivingDartFace hp hp2
          (canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
            hp hp2 (.finalTarget z htarget hz) tag).1 = root := by
        change projectivePolygonPostConeEdgeTarget z = root
        exact htarget.1.symm.trans hrootState
      exact False.elim (hnotcurrent hface)
  | treeSource z hsource hz =>
      let child := canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz
      have hincident : projectivePolygonPostConeEdgeSource z = root :=
        hsource.1.symm.trans hrootState
      have hleft := canonicalProjectivePostConeDirectTreeSlot_left_eq_root_of_endpoint
        hp hp2 z hz (Or.inl hincident)
      have hlabel : canonicalProjectivePostConeTreeSlotLabel hp hp2 child = z :=
        canonicalProjectivePostConeDirectTreeSlotOfDeleted_label hp hp2 z hz
      have hslotSource : child.left = projectivePolygonPostConeEdgeSource
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) := by
        rw [hlabel]
        exact hleft.trans hincident.symm
      have hslotSide : canonicalProjectivePostConeTreeSlot_leftBoundarySide hp hp2 child =
          projectivePolygonPostConeEdgeSide z := by
        simpa [hlabel] using
          canonicalProjectivePostConeTreeSlot_leftBoundarySide_eq_source
            hp hp2 child hslotSource
      have hside : s = canonicalProjectivePostConeTreeSlot_leftBoundarySide hp hp2 child := by
        calc
          s = projectivePolygonPostConeEdgeSide z := hsource.2.1
          _ = canonicalProjectivePostConeTreeSlot_leftBoundarySide hp hp2 child :=
            hslotSide.symm
      refine ⟨child, hleft, hside, ?_⟩
      change canonicalProjectivePostConeSurvivingDartInRegion hp hp2 child.right
        (canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 child tag).1
      exact canonicalProjectivePostConeRawTreeWordPosition_endpoint_region
        hp hp2 child tag
  | treeTarget z htarget hz =>
      let child := canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz
      have hincident : projectivePolygonPostConeEdgeTarget z = root :=
        htarget.1.symm.trans hrootState
      have hleft := canonicalProjectivePostConeDirectTreeSlot_left_eq_root_of_endpoint
        hp hp2 z hz (Or.inr hincident)
      have hlabel : canonicalProjectivePostConeTreeSlotLabel hp hp2 child = z :=
        canonicalProjectivePostConeDirectTreeSlotOfDeleted_label hp hp2 z hz
      have hslotTarget : child.left = projectivePolygonPostConeEdgeTarget
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) := by
        rw [hlabel]
        exact hleft.trans hincident.symm
      have hslotSide : canonicalProjectivePostConeTreeSlot_leftBoundarySide hp hp2 child =
          projectivePolygonPostConeEdgeTargetSide z := by
        simpa [hlabel] using
          canonicalProjectivePostConeTreeSlot_leftBoundarySide_eq_target
            hp hp2 child hslotTarget
      have hside : s = canonicalProjectivePostConeTreeSlot_leftBoundarySide hp hp2 child := by
        calc
          s = projectivePolygonPostConeEdgeTargetSide z := htarget.2.1
          _ = canonicalProjectivePostConeTreeSlot_leftBoundarySide hp hp2 child :=
            hslotSide.symm
      refine ⟨child, hleft, hside, ?_⟩
      change canonicalProjectivePostConeSurvivingDartInRegion hp hp2 child.right
        (canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 child tag).1
      exact canonicalProjectivePostConeRawTreeWordPosition_endpoint_region
        hp hp2 child tag

/-- A term-position decoder at the root lies either at the current face or
inside a child region attached directly to the root. -/
theorem canonicalProjectivePostConeRawRootContourTermPositionTag_root_current_or_child
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (s : ProjectivePolygonSide)
    (c : CanonicalProjectivePostConeRawRootContourTermCase hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state s)
    (tag : CanonicalProjectivePostConeRawRootContourTermPositionTag hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state s c) :
    canonicalProjectivePostConeSurvivingDartFace hp hp2
        (canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
          hp hp2 c tag).1 = canonicalProjectivePostConeTreeRoot hp hp2 ∨
      ∃ child : CanonicalProjectivePostConeTreeSlot hp hp2,
        child.left = canonicalProjectivePostConeTreeRoot hp hp2 ∧
          canonicalProjectivePostConeSurvivingDartInRegion hp hp2 child.right
            (canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
              hp hp2 c tag).1 := by
  let root := canonicalProjectivePostConeTreeRoot hp hp2
  have hrootState : (⟨root.state⟩ : ProjectivePolygonPostConeFace p) = root := by
    exact ProjectivePolygonPostConeFace.stateEquiv.symm_apply_apply root
  cases c with
  | one hone => exact tag.elim
  | finalSource z hsource hz =>
      apply Or.inl
      change projectivePolygonPostConeEdgeSource z = root
      exact hsource.1.symm.trans hrootState
  | finalTarget z htarget hz =>
      apply Or.inl
      change projectivePolygonPostConeEdgeTarget z = root
      exact htarget.1.symm.trans hrootState
  | treeSource z hsource hz =>
      apply Or.inr
      let child := canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz
      have hincident : projectivePolygonPostConeEdgeSource z = root :=
        hsource.1.symm.trans hrootState
      have hleft := canonicalProjectivePostConeDirectTreeSlot_left_eq_root_of_endpoint
        hp hp2 z hz (Or.inl hincident)
      refine ⟨child, hleft, ?_⟩
      change canonicalProjectivePostConeSurvivingDartInRegion hp hp2 child.right
        (canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 child tag).1
      exact canonicalProjectivePostConeRawTreeWordPosition_endpoint_region
        hp hp2 child tag
  | treeTarget z htarget hz =>
      apply Or.inr
      let child := canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz
      have hincident : projectivePolygonPostConeEdgeTarget z = root :=
        htarget.1.symm.trans hrootState
      have hleft := canonicalProjectivePostConeDirectTreeSlot_left_eq_root_of_endpoint
        hp hp2 z hz (Or.inr hincident)
      refine ⟨child, hleft, ?_⟩
      change canonicalProjectivePostConeSurvivingDartInRegion hp hp2 child.right
        (canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 child tag).1
      exact canonicalProjectivePostConeRawTreeWordPosition_endpoint_region
        hp hp2 child tag

/-- A nested root-side tag decodes either to a dart based at the root or to a
dart in one actual first-child region. This matches the tree-region partition
and is the classification needed for cross-case injectivity. -/
theorem canonicalProjectivePostConeRawRootContourTermsPositionTag_root_current_or_child
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (sides : List ProjectivePolygonSide)
    (tag : CanonicalProjectivePostConeRawRootContourTermsPositionTag hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state sides) :
    canonicalProjectivePostConeSurvivingDartFace hp hp2
        (canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2
          (canonicalProjectivePostConeTreeRoot hp hp2).state sides tag).1 =
          canonicalProjectivePostConeTreeRoot hp hp2 ∨
      ∃ child : CanonicalProjectivePostConeTreeSlot hp hp2,
        child.left = canonicalProjectivePostConeTreeRoot hp hp2 ∧
          canonicalProjectivePostConeSurvivingDartInRegion hp hp2 child.right
            (canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2
              (canonicalProjectivePostConeTreeRoot hp hp2).state sides tag).1 := by
  induction sides with
  | nil => cases tag
  | cons s ss ih =>
      cases tag with
      | inl head =>
          exact canonicalProjectivePostConeRawRootContourTermPositionTag_root_current_or_child
            hp hp2 s
            (canonicalProjectivePostConeRawRootContourTermCase hp hp2
              (canonicalProjectivePostConeTreeRoot hp hp2).state s)
            ((canonicalProjectivePostConeRawRootContourTerm_positionEquiv hp hp2
              (canonicalProjectivePostConeTreeRoot hp hp2).state s) head)
      | inr tail => exact ih tail

/-- A nested root tag remembers the physical boundary side at the current
face, or the exact child-slot boundary side for a descendant dart. -/
theorem canonicalProjectivePostConeRawRootContourTermsPositionTag_side_origin
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (sides : List ProjectivePolygonSide)
    (tag : CanonicalProjectivePostConeRawRootContourTermsPositionTag hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state sides) :
    (canonicalProjectivePostConeSurvivingDartFace hp hp2
        (canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2
          (canonicalProjectivePostConeTreeRoot hp hp2).state sides tag).1 =
          canonicalProjectivePostConeTreeRoot hp hp2 ∧
      canonicalProjectivePostConeRawRootContourTermsPositionTag_side hp hp2
        (canonicalProjectivePostConeTreeRoot hp hp2).state sides tag =
          canonicalProjectivePostConeSurvivingDartSide hp hp2
            (canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2
              (canonicalProjectivePostConeTreeRoot hp hp2).state sides tag).1) ∨
    ∃ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      child.left = canonicalProjectivePostConeTreeRoot hp hp2 ∧
        canonicalProjectivePostConeRawRootContourTermsPositionTag_side hp hp2
          (canonicalProjectivePostConeTreeRoot hp hp2).state sides tag =
            canonicalProjectivePostConeTreeSlot_leftBoundarySide hp hp2 child ∧
        canonicalProjectivePostConeSurvivingDartInRegion hp hp2 child.right
          (canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2
            (canonicalProjectivePostConeTreeRoot hp hp2).state sides tag).1 := by
  induction sides with
  | nil => cases tag
  | cons s ss ih =>
      cases tag with
      | inl head =>
          let c := canonicalProjectivePostConeRawRootContourTermCase hp hp2
            (canonicalProjectivePostConeTreeRoot hp hp2).state s
          let termTag := canonicalProjectivePostConeRawRootContourTerm_positionEquiv
            hp hp2 (canonicalProjectivePostConeTreeRoot hp hp2).state s head
          change (canonicalProjectivePostConeSurvivingDartFace hp hp2
              (canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
                hp hp2 c termTag).1 = canonicalProjectivePostConeTreeRoot hp hp2 ∧
            s = canonicalProjectivePostConeSurvivingDartSide hp hp2
              (canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
                hp hp2 c termTag).1) ∨
            ∃ child : CanonicalProjectivePostConeTreeSlot hp hp2,
              child.left = canonicalProjectivePostConeTreeRoot hp hp2 ∧
                s = canonicalProjectivePostConeTreeSlot_leftBoundarySide hp hp2 child ∧
                canonicalProjectivePostConeSurvivingDartInRegion hp hp2 child.right
                  (canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
                    hp hp2 c termTag).1
          by_cases hcurrent : canonicalProjectivePostConeSurvivingDartFace hp hp2
              (canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
                hp hp2 c termTag).1 = canonicalProjectivePostConeTreeRoot hp hp2
          · exact Or.inl ⟨hcurrent,
              canonicalProjectivePostConeRawRootContourTermPositionTag_side_eq_dartSide_of_current
                hp hp2 s c termTag hcurrent⟩
          · obtain ⟨child, hleft, hside, hregion⟩ :=
              canonicalProjectivePostConeRawRootContourTermPositionTag_child_side
                hp hp2 s c termTag hcurrent
            exact Or.inr ⟨child, hleft, hside, hregion⟩
      | inr tail =>
          simpa [canonicalProjectivePostConeRawRootContourTermsPositionTag_side,
            canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint] using ih tail

/-- Within a fixed root-side classifier case, the decoded physical dart
determines the local term-position tag. Final cases are singletons; recursive
cases inherit the already-proved injectivity of the child slot decoder. -/
theorem canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint_injective
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    {q : BuserSarnakProjectiveReductionRange p} {s : ProjectivePolygonSide}
    (c : CanonicalProjectivePostConeRawRootContourTermCase hp hp2 q s) :
    Function.Injective fun tag : CanonicalProjectivePostConeRawRootContourTermPositionTag
        hp hp2 q s c =>
      (canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint hp hp2 c tag).1 := by
  cases c with
  | one hone =>
      intro tag tag' _
      exact tag.elim
  | finalSource z hsource hz =>
      intro tag tag' _
      change Fin 1 at tag
      change Fin 1 at tag'
      apply Fin.ext
      omega
  | finalTarget z htarget hz =>
      intro tag tag' _
      change Fin 1 at tag
      change Fin 1 at tag'
      apply Fin.ext
      omega
  | treeSource z hsource hz =>
      let slot := canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz
      intro tag tag' hsame
      change (canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 slot tag).1 =
        (canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 slot tag').1 at hsame
      exact canonicalProjectivePostConeRawTreeWordPosition_endpoint_injective
        hp hp2 slot tag tag' hsame
  | treeTarget z htarget hz =>
      let slot := canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz
      intro tag tag' hsame
      change (canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 slot tag).1 =
        (canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 slot tag').1 at hsame
      exact canonicalProjectivePostConeRawTreeWordPosition_endpoint_injective
        hp hp2 slot tag tag' hsame

/-- A position in the head-side term cannot decode to the same physical dart
as a position in the tail-side expansion when the side list has no repeated
head value. Current darts are distinguished by their physical side; descendant
darts are distinguished by their unique first-child slot. -/
private theorem canonicalProjectivePostConeRawRootContourTerms_head_ne_tail
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (s : ProjectivePolygonSide) (ss : List ProjectivePolygonSide)
    (hs : s ∉ ss)
    (head : Fin (canonicalProjectivePostConeRawRootContourTerm hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state s).length)
    (tail : CanonicalProjectivePostConeRawRootContourTermsPositionTag hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state ss) :
    (canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state (s :: ss)
      (Sum.inl head)).1 ≠
    (canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state (s :: ss)
      (Sum.inr tail)).1 := by
  classical
  let rootVertex := canonicalProjectivePostConeTreeRoot hp hp2
  let rootFace : ProjectivePolygonPostConeFace p := rootVertex
  let q := rootVertex.state
  let leftDart := (canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint
    hp hp2 q (s :: ss) (Sum.inl head)).1
  let rightDart := (canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint
    hp hp2 q (s :: ss) (Sum.inr tail)).1
  intro hsame
  have hdarts : leftDart = rightDart := hsame
  have hrootRegion := canonicalProjectivePostConeSurvivingDart_mem_rootRegion
    hp hp2 leftDart
  have hleftOrigin := canonicalProjectivePostConeRawRootContourTermsPositionTag_side_origin
    hp hp2 (s :: ss) (Sum.inl head)
  have hrightOrigin := canonicalProjectivePostConeRawRootContourTermsPositionTag_side_origin
    hp hp2 (s :: ss) (Sum.inr tail)
  have htailMem := canonicalProjectivePostConeRawRootContourTermsPositionTag_side_mem
    hp hp2 q ss tail
  by_cases hcurrent : canonicalProjectivePostConeSurvivingDartFace hp hp2 leftDart = rootFace
  · have hrightFace : canonicalProjectivePostConeSurvivingDartFace hp hp2 rightDart =
        rootFace := (congrArg (canonicalProjectivePostConeSurvivingDartFace hp hp2) hdarts).symm.trans
          hcurrent
    rcases hleftOrigin with ⟨hleftFace, hleftSide⟩ |
      ⟨child, hchildLeft, hchildSide, hchildRegion⟩
    · have hsideLeft : s = canonicalProjectivePostConeSurvivingDartSide hp hp2 leftDart := by
        change s = canonicalProjectivePostConeSurvivingDartSide hp hp2 leftDart at hleftSide
        exact hleftSide
      rcases hrightOrigin with ⟨_hrightFaceEq, hrightSide⟩ |
        ⟨child', hchildLeft', hchildSide', hchildRegion'⟩
      · have hsideRight : canonicalProjectivePostConeRawRootContourTermsPositionTag_side
            hp hp2 q ss tail = canonicalProjectivePostConeSurvivingDartSide hp hp2 rightDart := by
          change canonicalProjectivePostConeRawRootContourTermsPositionTag_side
            hp hp2 q ss tail = canonicalProjectivePostConeSurvivingDartSide hp hp2 rightDart
            at hrightSide
          exact hrightSide
        have hsideEq : s =
            canonicalProjectivePostConeRawRootContourTermsPositionTag_side hp hp2 q ss tail :=
          hsideLeft.trans ((congrArg (canonicalProjectivePostConeSurvivingDartSide hp hp2)
            hdarts).trans hsideRight.symm)
        have hmem : s ∈ ss := by
          rw [hsideEq]
          exact htailMem
        exact hs hmem
      · have hnot : canonicalProjectivePostConeSurvivingDartFace hp hp2 rightDart ≠ rootFace := by
          intro hface
          have hparentNe := canonicalProjectivePostConeSurvivingDart_childRegion_ne_parent
            hp hp2 child' rightDart hchildRegion'
          exact hparentNe (hface.trans hchildLeft'.symm)
        exact hnot hrightFace
    · have hnot : canonicalProjectivePostConeSurvivingDartFace hp hp2 leftDart ≠ rootFace := by
        intro hface
        have hparentNe := canonicalProjectivePostConeSurvivingDart_childRegion_ne_parent
          hp hp2 child leftDart hchildRegion
        exact hparentNe (hface.trans hchildLeft.symm)
      exact hnot hcurrent
  · rcases hleftOrigin with hleftCurrent | ⟨childA, hleftA, hsideA, hregionA⟩
    · exact hcurrent hleftCurrent.1
    rcases hrightOrigin with hrightCurrent | ⟨childB, hleftB, hsideB, hregionB⟩
    · have hface : canonicalProjectivePostConeSurvivingDartFace hp hp2 leftDart = rootFace := by
        exact (congrArg (canonicalProjectivePostConeSurvivingDartFace hp hp2) hdarts).trans
          hrightCurrent.1
      exact hcurrent hface
    · have hregionB' : canonicalProjectivePostConeSurvivingDartInRegion hp hp2 childB.right
        leftDart := by
          rw [hdarts]
          exact hregionB
      rcases canonicalProjectivePostConeSurvivingDart_region_current_or_child
          hp hp2 rootVertex leftDart hrootRegion with hroot | ⟨child, hchild, hunique⟩
      · exact hcurrent hroot
      · have hchildAeq : childA = child := hunique childA ⟨hleftA, hregionA⟩
        have hchildBeq : childB = child := hunique childB ⟨hleftB, hregionB'⟩
        have hsideEq : s =
            canonicalProjectivePostConeRawRootContourTermsPositionTag_side hp hp2 q ss tail := by
          calc
            s = canonicalProjectivePostConeTreeSlot_leftBoundarySide hp hp2 childA := hsideA
            _ = canonicalProjectivePostConeTreeSlot_leftBoundarySide hp hp2 child :=
              congrArg (canonicalProjectivePostConeTreeSlot_leftBoundarySide hp hp2) hchildAeq
            _ = canonicalProjectivePostConeTreeSlot_leftBoundarySide hp hp2 childB :=
              (congrArg (canonicalProjectivePostConeTreeSlot_leftBoundarySide hp hp2) hchildBeq).symm
            _ = canonicalProjectivePostConeRawRootContourTermsPositionTag_side hp hp2 q ss tail :=
              hsideB.symm
        have hmem : s ∈ ss := by
          rw [hsideEq]
          exact htailMem
        exact hs hmem

/-- When the ordered side list has no repeated directed side, its nested
root-tag decoder is injective. Head/tail collisions are ruled out by the
current-face/unique-child split; same-side collisions use local term-tag
injectivity. -/
theorem canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint_injective_of_nodup
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (sides : List ProjectivePolygonSide) (hnodup : sides.Nodup) :
    Function.Injective fun tag : CanonicalProjectivePostConeRawRootContourTermsPositionTag
      hp hp2 (canonicalProjectivePostConeTreeRoot hp hp2).state sides =>
      (canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2
        (canonicalProjectivePostConeTreeRoot hp hp2).state sides tag).1 := by
  induction sides with
  | nil =>
      intro tag tag' _
      cases tag
  | cons s ss ih =>
      rcases List.nodup_cons.mp hnodup with ⟨hs, hss⟩
      intro tag tag' hsame
      cases tag with
      | inl head =>
          cases tag' with
          | inl head' =>
              let q := (canonicalProjectivePostConeTreeRoot hp hp2).state
              let c := canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s
              let e := canonicalProjectivePostConeRawRootContourTerm_positionEquiv hp hp2 q s
              have hlocal :
                  (canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
                    hp hp2 c (e head)).1 =
                  (canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
                    hp hp2 c (e head')).1 := by
                exact hsame
              have htag : e head = e head' :=
                canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint_injective
                  hp hp2 c hlocal
              exact congrArg Sum.inl (e.injective htag)
          | inr tail =>
              exact False.elim <|
                canonicalProjectivePostConeRawRootContourTerms_head_ne_tail
                  hp hp2 s ss hs head tail hsame
      | inr tail =>
          cases tag' with
          | inl head =>
              exact False.elim <|
                canonicalProjectivePostConeRawRootContourTerms_head_ne_tail
                  hp hp2 s ss hs head tail hsame.symm
          | inr tail' =>
              apply congrArg Sum.inr
              apply ih hss
              exact hsame

/-- The eight-side root-contour provenance decoder is injective. -/
theorem canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint_injective
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Injective fun tag : CanonicalProjectivePostConeRawRootContourTermsPositionTag
      hp hp2 (canonicalProjectivePostConeTreeRoot hp hp2).state
        canonicalProjectivePostConeBoundarySideCycle =>
      (canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2
        (canonicalProjectivePostConeTreeRoot hp hp2).state
        canonicalProjectivePostConeBoundarySideCycle tag).1 := by
  exact canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint_injective_of_nodup
    hp hp2 canonicalProjectivePostConeBoundarySideCycle
    canonicalProjectivePostConeBoundarySideCycle_nodup

/-- Distinct positions in the literal root contour decode to distinct
physical endpoint darts. -/
theorem canonicalProjectivePostConeRawRootContourPosition_endpoint_injective
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Injective (canonicalProjectivePostConeRawRootContourPosition_endpoint hp hp2) := by
  let e := canonicalProjectivePostConeRawRootContour_positionEquiv hp hp2
  intro i j hsame
  apply e.injective
  exact canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint_injective
    hp hp2 hsame

/-- Literal root-contour positions are in bijection with the surviving
physical source/target dart occurrences. -/
noncomputable def canonicalProjectivePostConeRawRootContourPosition_endpointEquiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Fin (canonicalProjectivePostConeRawRootContour hp hp2).length ≃
      CanonicalProjectivePostConeSurvivingDart hp hp2 :=
  Equiv.ofBijective (canonicalProjectivePostConeRawRootContourPosition_endpoint hp hp2)
    ⟨canonicalProjectivePostConeRawRootContourPosition_endpoint_injective hp hp2,
      canonicalProjectivePostConeRawRootContourPosition_endpoint_surjective hp hp2⟩

/-- Every retained physical dart has a selected literal position carrying
its label and orientation. This follows from root-contour endpoint
surjectivity and records the exact signed letter at that position. -/
theorem canonicalProjectivePostConeRawRootContour_exists_position_of_dart
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2) :
    ∃ i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length,
      (canonicalProjectivePostConeRawRootContour hp hp2).get i =
        (canonicalProjectivePostConeSurvivingDartGenerator hp hp2 d,
          canonicalProjectivePostConeSurvivingDartPositive hp hp2 d) := by
  cases d with
  | inl z =>
      exact canonicalProjectivePostConeRawRootContour_exists_positive_occurrence_of_generator
        hp hp2 z
  | inr z =>
      exact canonicalProjectivePostConeRawRootContour_exists_negative_occurrence_of_generator
        hp hp2 z

theorem canonicalProjectivePostConeRawRootContour_signedPosition_injective
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Injective (canonicalProjectivePostConeRawRootContour_signedPosition hp hp2) := by
  classical
  intro a b hab
  cases a with
  | inl x =>
    cases b with
    | inl y =>
      have hpositions := congrArg (canonicalProjectivePostConeRawRootContour hp hp2).get hab
      simp only [canonicalProjectivePostConeRawRootContour_signedPosition] at hpositions
      have hletter :=
        (canonicalProjectivePostConeRawRootContourPositivePosition_spec hp hp2 x).symm.trans
          (hpositions.trans
            (canonicalProjectivePostConeRawRootContourPositivePosition_spec hp hp2 y))
      have hxy : x = y := congrArg Prod.fst hletter
      subst y
      rfl
    | inr y =>
      have hpositions := congrArg (canonicalProjectivePostConeRawRootContour hp hp2).get hab
      simp only [canonicalProjectivePostConeRawRootContour_signedPosition] at hpositions
      have hletter :=
        (canonicalProjectivePostConeRawRootContourPositivePosition_spec hp hp2 x).symm.trans
          (hpositions.trans
            (canonicalProjectivePostConeRawRootContourNegativePosition_spec hp hp2 y))
      have hsign := congrArg Prod.snd hletter
      cases hsign
  | inr x =>
    cases b with
    | inl y =>
      have hpositions := congrArg (canonicalProjectivePostConeRawRootContour hp hp2).get hab
      simp only [canonicalProjectivePostConeRawRootContour_signedPosition] at hpositions
      have hletter :=
        (canonicalProjectivePostConeRawRootContourNegativePosition_spec hp hp2 x).symm.trans
          (hpositions.trans
            (canonicalProjectivePostConeRawRootContourPositivePosition_spec hp hp2 y))
      have hsign := congrArg Prod.snd hletter
      cases hsign
    | inr y =>
      have hpositions := congrArg (canonicalProjectivePostConeRawRootContour hp hp2).get hab
      simp only [canonicalProjectivePostConeRawRootContour_signedPosition] at hpositions
      have hletter :=
        (canonicalProjectivePostConeRawRootContourNegativePosition_spec hp hp2 x).symm.trans
          (hpositions.trans
            (canonicalProjectivePostConeRawRootContourNegativePosition_spec hp hp2 y))
      have hxy : x = y := congrArg Prod.fst hletter
      subst y
      rfl

/-- The chosen root-contour position of a physical endpoint occurrence. -/
noncomputable def canonicalProjectivePostConeSurvivingDartPosition
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2) :
    Fin (canonicalProjectivePostConeRawRootContour hp hp2).length :=
  canonicalProjectivePostConeRawRootContour_signedPosition hp hp2 d

/-- The chosen position retains the dart's generator and source/target sign. -/
theorem canonicalProjectivePostConeSurvivingDartPosition_spec
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2) :
    (canonicalProjectivePostConeRawRootContour hp hp2).get
      (canonicalProjectivePostConeSurvivingDartPosition hp hp2 d) =
        (canonicalProjectivePostConeSurvivingDartGenerator hp hp2 d,
          canonicalProjectivePostConeSurvivingDartPositive hp hp2 d) := by
  cases d with
  | inl z => exact canonicalProjectivePostConeRawRootContourPositivePosition_spec hp hp2 z
  | inr z => exact canonicalProjectivePostConeRawRootContourNegativePosition_spec hp hp2 z

/-- Distinct physical dart occurrences have distinct selected positions. -/
theorem canonicalProjectivePostConeSurvivingDartPosition_injective
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Injective (canonicalProjectivePostConeSurvivingDartPosition hp hp2) :=
  canonicalProjectivePostConeRawRootContour_signedPosition_injective hp hp2

/-- The literal root-contour length is bounded below by the number of signed
retained generators. An upper bound of the same size would yield exact
exhaustion and the Wicks occurrence equivalence. -/
noncomputable local instance rawRootContourFinalGeneratorFintype
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Fintype (CanonicalProjectivePostConeFinalGenerator hp hp2) := by
  classical
  letI : DecidablePred
      (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol :=
    Classical.decPred _
  letI : Fintype (CanonicalProjectiveConeNondegenerateSymbol p) :=
    Fintype.subtype
      (Finset.univ.filter fun z =>
        ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol z)
      (by simp)
  letI : DecidablePred (@isCanonicalProjectiveConeEliminationSymbol p _) :=
    Classical.decPred _
  letI : Fintype (CanonicalProjectiveConeKeptSymbol p) :=
    Fintype.subtype
      (Finset.univ.filter fun z => ¬ isCanonicalProjectiveConeEliminationSymbol z)
      (by simp)
  exact Fintype.subtype
    (Finset.univ.filter fun z =>
      ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z)
    (by simp)

noncomputable local instance rawSurvivingDartRegionFintype
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : CanonicalProjectivePostConeTreeVertex hp hp2) :
    Fintype (canonicalProjectivePostConeSurvivingDartRegion hp hp2 q) :=
  by
    classical
    letI : DecidablePred
        (canonicalProjectivePostConeSurvivingDartInRegion hp hp2 q) :=
      Classical.decPred _
    exact Fintype.subtype
      (Finset.univ.filter fun d =>
        canonicalProjectivePostConeSurvivingDartInRegion hp hp2 q d)
      (by simp)

/-- The root region consists of every physical source/target dart exactly
once. This identifies the canonical finite region with the whole dart type. -/
noncomputable def canonicalProjectivePostConeSurvivingDart_rootRegionEquiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    canonicalProjectivePostConeSurvivingDartRegion hp hp2
        (canonicalProjectivePostConeTreeRoot hp hp2) ≃
      CanonicalProjectivePostConeSurvivingDart hp hp2 where
  toFun := Subtype.val
  invFun := fun d => ⟨d,
    canonicalProjectivePostConeSurvivingDart_mem_rootRegion hp hp2 d⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The root physical-dart region has exactly two occurrences for each
retained final generator. -/
theorem canonicalProjectivePostConeSurvivingDart_rootRegion_card
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Fintype.card
        (canonicalProjectivePostConeSurvivingDartRegion hp hp2
          (canonicalProjectivePostConeTreeRoot hp hp2)) =
      2 * Fintype.card (CanonicalProjectivePostConeFinalGenerator hp hp2) := by
  classical
  rw [Fintype.card_congr
    (canonicalProjectivePostConeSurvivingDart_rootRegionEquiv hp hp2)]
  change Fintype.card
      (CanonicalProjectivePostConeFinalGenerator hp hp2 ⊕
        CanonicalProjectivePostConeFinalGenerator hp hp2) = _
  rw [Fintype.card_sum]
  omega

/-- The exact root-position equivalence gives two literal contour
occurrences for every retained generator: one at its source and one at its
target. -/
theorem canonicalProjectivePostConeRawRootContour_length_eq_two_mul_card_finalGenerator
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    (canonicalProjectivePostConeRawRootContour hp hp2).length =
      2 * Fintype.card (CanonicalProjectivePostConeFinalGenerator hp hp2) := by
  classical
  have hcard := Fintype.card_congr
    (canonicalProjectivePostConeRawRootContourPosition_endpointEquiv hp hp2)
  simp only [Fintype.card_fin, Fintype.card_sum] at hcard
  omega

theorem two_mul_card_finalGenerator_le_rawRootContour_length
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    2 * Fintype.card (CanonicalProjectivePostConeFinalGenerator hp hp2) ≤
      (canonicalProjectivePostConeRawRootContour hp hp2).length := by
  classical
  have hcard := Fintype.card_le_of_injective
    (canonicalProjectivePostConeRawRootContour_signedPosition hp hp2)
    (canonicalProjectivePostConeRawRootContour_signedPosition_injective hp hp2)
  have hcard' :
      Fintype.card (CanonicalProjectivePostConeFinalGenerator hp hp2) +
        Fintype.card (CanonicalProjectivePostConeFinalGenerator hp hp2) ≤
          (canonicalProjectivePostConeRawRootContour hp hp2).length := by
    simpa [Fintype.card_sum] using hcard
  omega

/-- The signed-position injection is a bijection as soon as the root contour
has no more positions than the two signed copies of the final alphabet. -/
theorem canonicalProjectivePostConeRawRootContour_signedPosition_bijective_of_length_le
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (hupper : (canonicalProjectivePostConeRawRootContour hp hp2).length ≤
      2 * Fintype.card (CanonicalProjectivePostConeFinalGenerator hp hp2)) :
    Function.Bijective (canonicalProjectivePostConeRawRootContour_signedPosition hp hp2) := by
  refine ⟨canonicalProjectivePostConeRawRootContour_signedPosition_injective hp hp2, ?_⟩
  intro i
  by_contra hnot
  have hnotSurjective : ¬ Function.Surjective
      (canonicalProjectivePostConeRawRootContour_signedPosition hp hp2) := by
    intro hsurjective
    exact hnot (hsurjective i)
  have hlt := Fintype.card_lt_of_injective_not_surjective
    (canonicalProjectivePostConeRawRootContour_signedPosition hp hp2)
    (canonicalProjectivePostConeRawRootContour_signedPosition_injective hp hp2)
    hnotSurjective
  simp only [Fintype.card_sum, Fintype.card_fin] at hlt
  have hlower := two_mul_card_finalGenerator_le_rawRootContour_length hp hp2
  omega

/-- The chosen positive/negative occurrence positions exhaust the literal
root contour, by the exact endpoint cardinality theorem. -/
theorem canonicalProjectivePostConeRawRootContour_signedPosition_bijective
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Bijective (canonicalProjectivePostConeRawRootContour_signedPosition hp hp2) := by
  apply canonicalProjectivePostConeRawRootContour_signedPosition_bijective_of_length_le
    hp hp2
  rw [canonicalProjectivePostConeRawRootContour_length_eq_two_mul_card_finalGenerator
    hp hp2]

/-- The other physical endpoint of each retained generator also contributes
a literal signed occurrence to the root contour. When the target face is the
root, its sign is exactly negative; otherwise this records the occurrence
transported from the target face's incoming slot. The stronger exact-sign
theorem `canonicalProjectivePostConeRawRootContour_exists_negative_occurrence_of_generator`
is now available; this disjunctive result is retained for compatibility. -/
theorem canonicalProjectivePostConeRawRootContour_exists_signed_occurrence_of_target_generator
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2) :
    (∃ i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length,
      (canonicalProjectivePostConeRawRootContour hp hp2).get i = (z, true)) ∨
    (∃ i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length,
      (canonicalProjectivePostConeRawRootContour hp hp2).get i = (z, false)) := by
  let q := projectivePolygonPostConeEdgeTarget z.1
  by_cases hroot : q = canonicalProjectivePostConeTreeRoot hp hp2
  · have hrootState : (projectivePolygonPostConeEdgeTarget z.1).state =
        (canonicalProjectivePostConeTreeRoot hp hp2).state :=
      congrArg ProjectivePolygonPostConeFace.state hroot
    obtain ⟨i, hi⟩ :=
      canonicalProjectivePostConeRawRootContour_exists_negative_occurrence_of_root_target
        hp hp2 z hrootState
    exact Or.inr ⟨i, hi⟩
  · let slot := canonicalProjectivePostConeTreeIncomingSlot hp hp2 q hroot
    have hslot := canonicalProjectivePostConeRawIncomingSlot_mem_target
      hp hp2 q hroot z rfl
    have hmem : (z, true) ∈ canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot ∨
        (z, false) ∈ canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot := by
      by_cases horient : slot.right = projectivePolygonPostConeEdgeSource
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)
      · exact Or.inl (hslot.1 horient)
      · exact Or.inr (hslot.2 horient)
    rcases hmem with hmem | hmem
    · rcases canonicalProjectivePostConeRawRootContour_exists_signed_occurrence_of_mem_slot
        hp hp2 slot (z, true) hmem with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact Or.inl ⟨i, hi⟩
      · exact Or.inr ⟨i, hi⟩
    · rcases canonicalProjectivePostConeRawRootContour_exists_signed_occurrence_of_mem_slot
        hp hp2 slot (z, false) hmem with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact Or.inr ⟨i, hi⟩
      · exact Or.inl ⟨i, hi⟩

end

end SystolicGrowth

#print axioms SystolicGrowth.canonicalProjectivePostConeRawRootContourTermsPositionTag_exists_of_root_child_region
#print axioms SystolicGrowth.canonicalProjectivePostConeRawRootContourTermsPositionTag_exists_of_region
