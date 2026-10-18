module

public import BuserSarnak.BuserSarnakProjectiveVertexCycleBlocks

@[expose] public section

/-!
# Exact support of the local primal vertex cycles

The eight-dart orbit based at a corner consists of every dart starting at
that primal vertex, not merely a subset of them.  Choosing the `a`-side dart
at each quotient state therefore gives disjoint local cycle blocks covering
all polygon darts.  These support identities are independent of the dual
face tree and are the input for contracting the canonical primal tree.
-/

namespace SystolicGrowth

noncomputable section

/-- The explicit side rotation visits every polygon side within eight steps. -/
theorem ProjectivePolygonSide.exists_vertexRotate_iterate_finEight
    (s t : ProjectivePolygonSide) :
    ∃ i : Fin 8, (ProjectivePolygonSide.vertexRotate^[i.val]) s = t := by
  cases s <;> cases t <;> decide

namespace BuserSarnakProjectiveQuotientSectionData

/-- A polygon dart is determined by its side and the primal vertex at its
start, for any projective quotient section. -/
theorem polygonDart_eq_of_side_start_eq
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    {d e : BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide}
    (hside : d.2 = e.2)
    (hstart : S.polygonSideStart d.1 d.2 = S.polygonSideStart e.1 e.2) :
    d = e := by
  apply Prod.ext
  · calc
      d.1 = S.polygonSideBase (S.polygonSideStart d.1 d.2) d.2 :=
        (S.polygonSideBase_start d.1 d.2).symm
      _ = S.polygonSideBase (S.polygonSideStart e.1 e.2) e.2 := by
        rw [hstart, hside]
      _ = e.1 := S.polygonSideBase_start e.1 e.2
  · exact hside

end BuserSarnakProjectiveQuotientSectionData

/-- The local eight-dart orbit contains exactly the darts starting at the
same primal vertex as its base dart. -/
theorem mem_projectiveVertexDartOrbitList_iff_start_eq
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (d e : BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide) :
    e ∈ projectiveVertexDartOrbitList S d ↔
      S.polygonSideStart e.1 e.2 = S.polygonSideStart d.1 d.2 := by
  constructor
  · intro he
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp he
    exact projectiveVertexDartOrbitList_start S d i
  · intro hstart
    obtain ⟨i, hi⟩ :=
      ProjectivePolygonSide.exists_vertexRotate_iterate_finEight d.2 e.2
    apply (List.mem_ofFn' _ _).mpr
    refine ⟨i, ?_⟩
    apply S.polygonDart_eq_of_side_start_eq
    · exact (S.polygonVertexRotateDart_side_iterate d.1 d.2 i.val).trans hi
    · exact (projectiveVertexDartOrbitList_start S d i).trans hstart.symm

/-- Local vertex-cycle supports are disjoint whenever their primal vertices
are distinct. -/
theorem projectiveVertexDartOrbitLists_disjoint_of_start_ne
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (d e : BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide)
    (hne : S.polygonSideStart d.1 d.2 ≠ S.polygonSideStart e.1 e.2) :
    List.Disjoint (projectiveVertexDartOrbitList S d)
      (projectiveVertexDartOrbitList S e) := by
  apply List.disjoint_left.mpr
  intro a haD haE
  have hD := (mem_projectiveVertexDartOrbitList_iff_start_eq S d a).mp haD
  have hE := (mem_projectiveVertexDartOrbitList_iff_start_eq S e a).mp haE
  exact hne (hD.symm.trans hE)

/-- Choose the `a`-side dart, whose primal start is exactly `q`, as the base
of the local vertex cycle at `q`. -/
def projectivePrimalVertexDartOrbitList
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p) :
    List (BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide) :=
  projectiveVertexDartOrbitList S (q, .a)

/-- A canonical-base vertex block consists precisely of the darts starting
at its quotient state. -/
@[simp] theorem mem_projectivePrimalVertexDartOrbitList_iff
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (d : BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide) :
    d ∈ projectivePrimalVertexDartOrbitList S q ↔
      S.polygonSideStart d.1 d.2 = q := by
  exact mem_projectiveVertexDartOrbitList_iff_start_eq S (q, .a) d

theorem projectivePrimalVertexDartOrbitList_nodup
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p) :
    (projectivePrimalVertexDartOrbitList S q).Nodup :=
  projectiveVertexDartOrbitList_nodup S (q, .a)

@[simp] theorem projectivePrimalVertexDartOrbitList_length
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p) :
    (projectivePrimalVertexDartOrbitList S q).length = 8 :=
  projectiveVertexDartOrbitList_length S (q, .a)

/-- The canonical-base local cycles at different primal vertices have
disjoint dart supports. -/
theorem projectivePrimalVertexDartOrbitLists_disjoint
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    {q r : BuserSarnakProjectiveReductionRange p} (hne : q ≠ r) :
    List.Disjoint (projectivePrimalVertexDartOrbitList S q)
      (projectivePrimalVertexDartOrbitList S r) :=
  projectiveVertexDartOrbitLists_disjoint_of_start_ne S (q, .a) (r, .a) hne

/-- Every polygon dart lies in the unique local cycle at its primal start. -/
theorem projectivePrimalVertexDartOrbitList_covers
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (d : BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide) :
    d ∈ projectivePrimalVertexDartOrbitList S
      (S.polygonSideStart d.1 d.2) := by
  exact (mem_projectivePrimalVertexDartOrbitList_iff S _ d).mpr rfl

end

#print axioms SystolicGrowth.ProjectivePolygonSide.exists_vertexRotate_iterate_finEight
#print axioms SystolicGrowth.BuserSarnakProjectiveQuotientSectionData.polygonDart_eq_of_side_start_eq
#print axioms SystolicGrowth.mem_projectiveVertexDartOrbitList_iff_start_eq
#print axioms SystolicGrowth.projectiveVertexDartOrbitLists_disjoint_of_start_ne
#print axioms SystolicGrowth.mem_projectivePrimalVertexDartOrbitList_iff
#print axioms SystolicGrowth.projectivePrimalVertexDartOrbitLists_disjoint
#print axioms SystolicGrowth.projectivePrimalVertexDartOrbitList_covers

end SystolicGrowth
