module

public import BuserSarnak.BuserSarnakProjectivePolygonTreeCarriers
public import BuserSarnak.FiniteCycleSplice
public import Mathlib.Data.List.OfFn

@[expose] public section

/-!
# The two local vertex cycles at a canonical primal tree edge

The polygon dart rotation is a single 8-cycle on each primal vertex. This
module packages those local cycles as ordered lists and proves that the two
cycles at the endpoints of every canonical Schreier-tree edge are disjoint.
These are the concrete blocks needed to apply the generic successor-swap
splice theorem.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete

/-- The ordered eight darts encountered from a chosen corner under the local
vertex rotation. -/
def projectiveVertexDartOrbitList
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (d : BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide) :
    List (BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide) :=
  List.ofFn fun i : Fin 8 => (S.polygonVertexRotateDart^[i.val]) d

theorem polygonVertexRotateDart_iterate_injective_finEight
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (d : BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide) :
    Function.Injective (fun i : Fin 8 => (S.polygonVertexRotateDart^[i.val]) d) := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · let k := j.val - i.val
    have hdecomp : j.val = i.val + k := by omega
    change (S.polygonVertexRotateDart^[i.val]) d =
      (S.polygonVertexRotateDart^[j.val]) d at hij
    have hcomp :
        (S.polygonVertexRotateDart^[j.val]) d =
          (S.polygonVertexRotateDart^[i.val])
            ((S.polygonVertexRotateDart^[k]) d) := by
      rw [hdecomp, ← Function.iterate_add_apply]
    have hiter :
        (S.polygonVertexRotateDart^[i.val]) d =
          (S.polygonVertexRotateDart^[i.val])
            ((S.polygonVertexRotateDart^[k]) d) := hij.trans hcomp
    have hfix : (S.polygonVertexRotateDart^[k]) d = d :=
      ((S.polygonVertexRotateDart_bijective.1.iterate i.val) hiter).symm
    have hpos : 0 < j.val - i.val := by omega
    have hltEight : j.val - i.val < 8 := by omega
    have hside :
        (ProjectivePolygonSide.vertexRotate^[j.val - i.val]) d.2 = d.2 := by
      have hsecond := congrArg Prod.snd hfix
      simpa [S.polygonVertexRotateDart_side_iterate] using hsecond
    exact (ProjectivePolygonSide.vertexRotate_iterate_ne_self_of_pos_lt_eight
      d.2 hpos hltEight) hside
  · let k := i.val - j.val
    have hdecomp : i.val = j.val + k := by omega
    change (S.polygonVertexRotateDart^[i.val]) d =
      (S.polygonVertexRotateDart^[j.val]) d at hij
    have hcomp :
        (S.polygonVertexRotateDart^[i.val]) d =
          (S.polygonVertexRotateDart^[j.val])
            ((S.polygonVertexRotateDart^[k]) d) := by
      rw [hdecomp, ← Function.iterate_add_apply]
    have hiter :
        (S.polygonVertexRotateDart^[j.val]) d =
          (S.polygonVertexRotateDart^[j.val])
            ((S.polygonVertexRotateDart^[k]) d) := hij.symm.trans hcomp
    have hfix : (S.polygonVertexRotateDart^[k]) d = d :=
      ((S.polygonVertexRotateDart_bijective.1.iterate j.val) hiter).symm
    have hpos : 0 < i.val - j.val := by omega
    have hltEight : i.val - j.val < 8 := by omega
    have hside :
        (ProjectivePolygonSide.vertexRotate^[i.val - j.val]) d.2 = d.2 := by
      have hsecond := congrArg Prod.snd hfix
      simpa [S.polygonVertexRotateDart_side_iterate] using hsecond
    exact (ProjectivePolygonSide.vertexRotate_iterate_ne_self_of_pos_lt_eight
      d.2 hpos hltEight) hside

theorem projectiveVertexDartOrbitList_nodup
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (d : BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide) :
    (projectiveVertexDartOrbitList S d).Nodup := by
  exact List.nodup_ofFn.mpr (polygonVertexRotateDart_iterate_injective_finEight S d)

theorem projectiveVertexDartOrbitList_length
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (d : BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide) :
    (projectiveVertexDartOrbitList S d).length = 8 := by
  simp [projectiveVertexDartOrbitList]

theorem projectiveVertexDartOrbitList_start
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (d : BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide)
    (i : Fin 8) :
    S.polygonSideStart
        ((S.polygonVertexRotateDart^[i.val]) d).1
        ((S.polygonVertexRotateDart^[i.val]) d).2 =
      S.polygonSideStart d.1 d.2 := by
  exact S.polygonVertexRotateDart_start_iterate d.1 d.2 i.val

/-- The source and target vertex cycles of any canonical primal tree edge
have disjoint dart supports. -/
theorem canonicalProjectiveTreeEndpointOrbitLists_disjoint
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    List.Disjoint
      (projectiveVertexDartOrbitList
        (canonicalBuserSarnakProjectiveQuotientSectionData p)
        (canonicalProjectivePolygonTreeSourceDart z))
      (projectiveVertexDartOrbitList
        (canonicalBuserSarnakProjectiveQuotientSectionData p)
        (canonicalProjectivePolygonTreeTargetDart z)) := by
  apply List.disjoint_left.mpr
  intro d hdSource hdTarget
  have hdSource' : d ∈ Set.range (fun i : Fin 8 =>
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonVertexRotateDart^[i.val]
        (canonicalProjectivePolygonTreeSourceDart z)) := by
    exact (List.mem_ofFn' _ _).mp hdSource
  have hdTarget' : d ∈ Set.range (fun i : Fin 8 =>
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonVertexRotateDart^[i.val]
        (canonicalProjectivePolygonTreeTargetDart z)) := by
    exact (List.mem_ofFn' _ _).mp hdTarget
  obtain ⟨i, hi⟩ := hdSource'
  obtain ⟨j, hj⟩ := hdTarget'
  have hstart := congrArg
    (fun e : BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide =>
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideStart e.1 e.2)
    (hj.trans hi.symm)
  have hsource := projectiveVertexDartOrbitList_start
    (canonicalBuserSarnakProjectiveQuotientSectionData p)
    (canonicalProjectivePolygonTreeSourceDart z) i
  have htarget := projectiveVertexDartOrbitList_start
    (canonicalBuserSarnakProjectiveQuotientSectionData p)
    (canonicalProjectivePolygonTreeTargetDart z) j
  exact (polygonSideStart_treeSourceDart_ne_treeTargetDart z)
    (hsource.symm.trans (hstart.symm.trans htarget))

/-- Rotating the source endpoint cycle puts its paired tree dart at the end
of the ordered block, ready for the successor splice. -/
theorem projectiveVertexDartOrbitList_rotate_one_eq_drop_append
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (d : BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide) :
    (projectiveVertexDartOrbitList S d).rotate 1 =
      (projectiveVertexDartOrbitList S d).drop 1 ++ [d] := by
  rw [List.rotate_eq_drop_append_take]
  · simp [projectiveVertexDartOrbitList]
  · simp [projectiveVertexDartOrbitList]

/-- The target endpoint cycle starts with its paired tree dart. -/
theorem projectiveVertexDartOrbitList_eq_cons_drop_one
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (d : BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide) :
    projectiveVertexDartOrbitList S d =
      d :: (projectiveVertexDartOrbitList S d).drop 1 := by
  simp [projectiveVertexDartOrbitList]

/-- After cutting each endpoint cycle at the actual paired tree darts, the
successor swap merges them into one cycle. This is the concrete local
contraction law for every canonical primal tree edge. -/
theorem canonicalProjectiveTreeEdge_successorSplice_isCycle
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    let S := canonicalBuserSarnakProjectiveQuotientSectionData p
    Equiv.Perm.IsCycle
      (List.formPerm
          ((projectiveVertexDartOrbitList S (canonicalProjectivePolygonTreeSourceDart z)).rotate 1) *
        Equiv.swap (canonicalProjectivePolygonTreeSourceDart z)
          (canonicalProjectivePolygonTreeTargetDart z) *
        List.formPerm
          (projectiveVertexDartOrbitList S (canonicalProjectivePolygonTreeTargetDart z))) := by
  dsimp
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  let a := canonicalProjectivePolygonTreeSourceDart z
  let b := canonicalProjectivePolygonTreeTargetDart z
  let left := projectiveVertexDartOrbitList S a
  let right := projectiveVertexDartOrbitList S b
  have ha : a ∈ left := by
    apply (List.mem_ofFn' _ _).2
    exact ⟨⟨0, by omega⟩, rfl⟩
  have hb : b ∈ right := by
    apply (List.mem_ofFn' _ _).2
    exact ⟨⟨0, by omega⟩, rfl⟩
  have hleftNodup := projectiveVertexDartOrbitList_nodup S a
  have hrightNodup := projectiveVertexDartOrbitList_nodup S b
  have hcycle := formPerm_splice_isCycle_of_mem left right a b
    hleftNodup hrightNodup (canonicalProjectiveTreeEndpointOrbitLists_disjoint z)
    ha hb (by rw [projectiveVertexDartOrbitList_length]; omega)
    (by rw [projectiveVertexDartOrbitList_length]; omega)
  rw [← List.formPerm_rotate left hleftNodup 1] at hcycle
  exact hcycle

theorem projectiveVertexDartOrbitList_formPerm_isCycle
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (d : BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide) :
    Equiv.Perm.IsCycle (List.formPerm (projectiveVertexDartOrbitList S d)) := by
  apply List.isCycle_formPerm (projectiveVertexDartOrbitList_nodup S d)
  rw [projectiveVertexDartOrbitList_length]
  omega

/-- The full boundary list after the local successor splice at a canonical
tree edge. -/
def canonicalProjectiveTreeEdgeSplicedWord
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    List (BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide) :=
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  (projectiveVertexDartOrbitList S (canonicalProjectivePolygonTreeSourceDart z)).rotate 1 ++
    projectiveVertexDartOrbitList S (canonicalProjectivePolygonTreeTargetDart z)

/-- The permutation obtained from the literal post-splice boundary list. -/
noncomputable def canonicalProjectiveTreeEdgeSplicedPerm
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    Equiv.Perm (BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide) :=
  List.formPerm (canonicalProjectiveTreeEdgeSplicedWord z)

/-- A canonical tree-edge splice has an explicit nodup list representative
whose elements are exactly the two original vertex-cycle blocks, and whose
`formPerm` is the concrete spliced permutation. This is the data needed to
carry an already-merged component into a later tree attachment. -/
theorem canonicalProjectiveTreeEdge_mergedCycleList_exists
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    ∃ merged : List (BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide),
      merged.Nodup ∧
      (∀ d, d ∈ merged ↔
        d ∈ projectiveVertexDartOrbitList
          (canonicalBuserSarnakProjectiveQuotientSectionData p)
          (canonicalProjectivePolygonTreeSourceDart z) ∨
        d ∈ projectiveVertexDartOrbitList
          (canonicalBuserSarnakProjectiveQuotientSectionData p)
          (canonicalProjectivePolygonTreeTargetDart z)) ∧
      List.formPerm merged = canonicalProjectiveTreeEdgeSplicedPerm z := by
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  let a := canonicalProjectivePolygonTreeSourceDart z
  let b := canonicalProjectivePolygonTreeTargetDart z
  let left := projectiveVertexDartOrbitList S a
  let right := projectiveVertexDartOrbitList S b
  have ha : a ∈ left := by
    apply (List.mem_ofFn' _ _).2
    exact ⟨⟨0, by omega⟩, rfl⟩
  have hb : b ∈ right := by
    apply (List.mem_ofFn' _ _).2
    exact ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨merged, hnodup, hmem, hform⟩ :=
    formPerm_splice_word_of_mem left right a b
      (projectiveVertexDartOrbitList_nodup S a)
      (projectiveVertexDartOrbitList_nodup S b)
      (canonicalProjectiveTreeEndpointOrbitLists_disjoint z) ha hb
  have hrot := projectiveVertexDartOrbitList_rotate_one_eq_drop_append S a
  have hright := projectiveVertexDartOrbitList_eq_cons_drop_one S b
  have hrot' : left.rotate 1 = left.drop 1 ++ [a] := by
    simpa [left] using hrot
  have hright' : right = b :: right.drop 1 := by
    simpa [right] using hright
  have hleftPerm : List.formPerm (left.drop 1 ++ [a]) = List.formPerm left := by
    rw [← hrot]
    exact List.formPerm_rotate left (projectiveVertexDartOrbitList_nodup S a) 1
  have hrightPerm : List.formPerm (b :: right.drop 1) = List.formPerm right := by
    rw [← hright]
  have hactual : List.formPerm (canonicalProjectiveTreeEdgeSplicedWord z) =
      List.formPerm left * Equiv.swap a b * List.formPerm right := by
    change List.formPerm (left.rotate 1 ++ right) = _
    calc
      List.formPerm (left.rotate 1 ++ right) =
          List.formPerm (left.drop 1 ++ [a] ++ b :: right.drop 1) := by
        rw [hrot', hright']
        simp [List.append_assoc]
      _ = List.formPerm (left.drop 1 ++ [a]) * Equiv.swap a b *
          List.formPerm (b :: right.drop 1) :=
        formPerm_append_splice_eq (left.drop 1) (right.drop 1) a b
      _ = List.formPerm left * Equiv.swap a b * List.formPerm right := by
        rw [hleftPerm, hrightPerm]
  refine ⟨merged, hnodup, ?_, ?_⟩
  · intro d
    simpa [left, right, S] using hmem d
  · calc
      List.formPerm merged = List.formPerm left * Equiv.swap a b * List.formPerm right := hform
      _ = List.formPerm (canonicalProjectiveTreeEdgeSplicedWord z) := hactual.symm
      _ = canonicalProjectiveTreeEdgeSplicedPerm z := rfl

def canonicalProjectiveTreeEdgeSurvivorPredicate
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    {d : BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide //
      canonicalProjectiveTreeEdgeSplicedPerm z d ≠ d} → Prop :=
  fun d => d.1 ≠ canonicalProjectivePolygonTreeSourceDart z ∧
    d.1 ≠ canonicalProjectivePolygonTreeTargetDart z

theorem canonicalProjectiveTreeEdgeSplicedWord_nodup
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    (canonicalProjectiveTreeEdgeSplicedWord z).Nodup := by
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  let a := canonicalProjectivePolygonTreeSourceDart z
  let b := canonicalProjectivePolygonTreeTargetDart z
  let left := projectiveVertexDartOrbitList S a
  let right := projectiveVertexDartOrbitList S b
  have hdisj : List.Disjoint (left.rotate 1) right := by
    apply List.disjoint_left.mpr
    intro x hxLeft hxRight
    have hxLeft' : x ∈ left := List.mem_rotate.mp hxLeft
    exact (List.disjoint_left.mp
      (canonicalProjectiveTreeEndpointOrbitLists_disjoint z) hxLeft') hxRight
  change (left.rotate 1 ++ right).Nodup
  rw [List.nodup_append']
  exact ⟨(List.nodup_rotate).2 (projectiveVertexDartOrbitList_nodup S a),
    projectiveVertexDartOrbitList_nodup S b, hdisj⟩

theorem canonicalProjectiveTreeEdgeSplicedWord_length
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    (canonicalProjectiveTreeEdgeSplicedWord z).length = 16 := by
  simp [canonicalProjectiveTreeEdgeSplicedWord,
    projectiveVertexDartOrbitList_length]

theorem canonicalProjectiveTreeEdgeSplicedPerm_isCycle
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    Equiv.Perm.IsCycle (canonicalProjectiveTreeEdgeSplicedPerm z) := by
  apply List.isCycle_formPerm
    (canonicalProjectiveTreeEdgeSplicedWord_nodup z)
  rw [canonicalProjectiveTreeEdgeSplicedWord_length]
  omega

/-- Deleting the two paired tree darts leaves a nonempty subset of the
spliced cycle's moved support. The first surviving dart is the next dart in
the source vertex cycle. -/
theorem canonicalProjectiveTreeEdgeSurvivorPredicate_nonempty
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    ∃ d, canonicalProjectiveTreeEdgeSurvivorPredicate z d := by
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  let a := canonicalProjectivePolygonTreeSourceDart z
  let b := canonicalProjectivePolygonTreeTargetDart z
  let f := canonicalProjectiveTreeEdgeSplicedPerm z
  let c := S.polygonVertexRotateDart a
  have hcmemLeft : c ∈ projectiveVertexDartOrbitList S a := by
    apply (List.mem_ofFn' _ _).2
    exact ⟨⟨1, by omega⟩, rfl⟩
  have hcmem : c ∈ canonicalProjectiveTreeEdgeSplicedWord z := by
    change c ∈ ((projectiveVertexDartOrbitList S a).rotate 1 ++
      projectiveVertexDartOrbitList S b)
    exact List.mem_append.mpr <| Or.inl <| List.mem_rotate.mpr hcmemLeft
  have hcmoved : f c ≠ c := by
    change List.formPerm (canonicalProjectiveTreeEdgeSplicedWord z) c ≠ c
    exact (List.formPerm_apply_mem_ne_self_iff _
      (canonicalProjectiveTreeEdgeSplicedWord_nodup z) c hcmem).2
      (by rw [canonicalProjectiveTreeEdgeSplicedWord_length]; omega)
  have hca : c ≠ a := by
    intro h
    have hside : ProjectivePolygonSide.vertexRotate a.2 = a.2 := by
      have hs : c.2 = ProjectivePolygonSide.vertexRotate a.2 := by
        change (S.polygonVertexRotateDart a).2 = ProjectivePolygonSide.vertexRotate a.2
        exact S.polygonVertexRotate_side a.1 a.2
      exact hs.symm.trans (congrArg Prod.snd h)
    exact (ProjectivePolygonSide.vertexRotate_iterate_ne_self_of_pos_lt_eight
      a.2 (n := 1) (by norm_num) (by norm_num)) (by simpa using hside)
  have hcstart : S.polygonSideStart c.1 c.2 = S.polygonSideStart a.1 a.2 := by
    simpa [c, BuserSarnakProjectiveQuotientSectionData.polygonVertexRotateDart,
      BuserSarnakProjectiveQuotientSectionData.polygonVertexRotate] using
      S.polygonVertexRotate_start a.1 a.2
  have hcb : c ≠ b := by
    intro h
    apply polygonSideStart_treeSourceDart_ne_treeTargetDart z
    calc
      S.polygonSideStart a.1 a.2 = S.polygonSideStart c.1 c.2 := hcstart.symm
      _ = S.polygonSideStart b.1 b.2 := by rw [h]
  exact ⟨⟨c, hcmoved⟩, hca, hcb⟩

/-- After a canonical primal edge splice, the first-return dynamics on the
remaining dart occurrences (with the paired tree darts removed) is still
transitive. This is the local deletion step required by the contraction
trace. -/
theorem canonicalProjectiveTreeEdge_afterDelete_firstReturn_one_orbit
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    let f := canonicalProjectiveTreeEdgeSplicedPerm z
    let P := canonicalProjectiveTreeEdgeSurvivorPredicate z
    let hreturn : ∀ x : {d : {d : BuserSarnakProjectiveReductionRange p ×
        ProjectivePolygonSide // f d ≠ d} // P d},
        ∃ n : ℕ, 0 < n ∧ P ((cycleSupportMap f)^[n] x.1) :=
      fun x => finiteOrbit_exists_positive_hit (cycleSupportMap f)
        (cycleSupportMap_injective f)
        (isCycle_support_iterate_transitive f
          (canonicalProjectiveTreeEdgeSplicedPerm_isCycle z))
        P (canonicalProjectiveTreeEdgeSurvivorPredicate_nonempty z) x.1
    ∀ x y : {d : {d : BuserSarnakProjectiveReductionRange p ×
        ProjectivePolygonSide // f d ≠ d} // P d},
      ∃ k : ℕ,
        (@finiteOrbitFirstReturn _ (cycleSupportMap f) P (Classical.decPred P) hreturn)^[k]
          x = y := by
  exact @isCycle_support_firstReturn_one_orbit _ _
    (canonicalProjectiveTreeEdgeSplicedPerm z)
    (canonicalProjectiveTreeEdgeSplicedPerm_isCycle z)
    (canonicalProjectiveTreeEdgeSurvivorPredicate z)
    (Classical.decPred (canonicalProjectiveTreeEdgeSurvivorPredicate z))
    (canonicalProjectiveTreeEdgeSurvivorPredicate_nonempty z)

end

#print axioms SystolicGrowth.polygonVertexRotateDart_iterate_injective_finEight
#print axioms SystolicGrowth.canonicalProjectiveTreeEndpointOrbitLists_disjoint
#print axioms SystolicGrowth.projectiveVertexDartOrbitList_formPerm_isCycle
#print axioms SystolicGrowth.canonicalProjectiveTreeEdge_successorSplice_isCycle
#print axioms SystolicGrowth.canonicalProjectiveTreeEdge_mergedCycleList_exists
#print axioms SystolicGrowth.canonicalProjectiveTreeEdgeSplicedWord_nodup
#print axioms SystolicGrowth.canonicalProjectiveTreeEdgeSplicedPerm_isCycle
#print axioms SystolicGrowth.canonicalProjectiveTreeEdgeSurvivorPredicate_nonempty
#print axioms SystolicGrowth.canonicalProjectiveTreeEdge_afterDelete_firstReturn_one_orbit

end SystolicGrowth
