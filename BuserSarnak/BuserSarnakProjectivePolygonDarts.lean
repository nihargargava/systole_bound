module

public import BuserSarnak.BuserSarnakProjectivePolygonPairing

@[expose] public section

/-!
# Darts around vertices of the projective polygon cover

The eight sides of a polygon boundary carry a cyclic successor.  Crossing a
side and advancing once around the adjacent face rotates a directed side dart
around one primal vertex.  This is the local combinatorial input for the
tree--cotree connectivity argument after cone elimination.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

noncomputable local instance buserSarnakProjectivePolygonDartsRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

/-- The next directed side in the oriented octagon boundary. -/
def ProjectivePolygonSide.next : ProjectivePolygonSide → ProjectivePolygonSide
  | .a => .e1
  | .e1 => .cInv
  | .cInv => .e2
  | .e2 => .aInv
  | .aInv => .e3
  | .e3 => .c
  | .c => .e4
  | .e4 => .a

/-- Advancing once after reversing a side gives the side component of the
vertex-dart rotation. -/
def ProjectivePolygonSide.vertexRotate : ProjectivePolygonSide → ProjectivePolygonSide :=
  fun s => s.reverse.next

/-- Explicit side cycle induced by the vertex-dart rotation. -/
@[simp] theorem ProjectivePolygonSide.vertexRotate_a :
    ProjectivePolygonSide.a.vertexRotate = .e3 := rfl

@[simp] theorem ProjectivePolygonSide.vertexRotate_e3 :
    ProjectivePolygonSide.e3.vertexRotate = .c := rfl

@[simp] theorem ProjectivePolygonSide.vertexRotate_c :
    ProjectivePolygonSide.c.vertexRotate = .e2 := rfl

@[simp] theorem ProjectivePolygonSide.vertexRotate_e2 :
    ProjectivePolygonSide.e2.vertexRotate = .aInv := rfl

@[simp] theorem ProjectivePolygonSide.vertexRotate_aInv :
    ProjectivePolygonSide.aInv.vertexRotate = .e1 := rfl

@[simp] theorem ProjectivePolygonSide.vertexRotate_e1 :
    ProjectivePolygonSide.e1.vertexRotate = .cInv := rfl

@[simp] theorem ProjectivePolygonSide.vertexRotate_cInv :
    ProjectivePolygonSide.cInv.vertexRotate = .e4 := rfl

@[simp] theorem ProjectivePolygonSide.vertexRotate_e4 :
    ProjectivePolygonSide.e4.vertexRotate = .a := rfl

/-- One full circuit of the explicit side rotation has length eight. -/
@[simp] theorem ProjectivePolygonSide.vertexRotate_iterate_eight
    (s : ProjectivePolygonSide) :
    (ProjectivePolygonSide.vertexRotate^[8]) s = s := by
  cases s <;> rfl

/-- No proper positive iterate below eight fixes a polygon side. -/
theorem ProjectivePolygonSide.vertexRotate_iterate_ne_self_of_pos_lt_eight
    (s : ProjectivePolygonSide) {n : ℕ}
    (hnpos : 0 < n) (hnlt : n < 8) :
    (ProjectivePolygonSide.vertexRotate^[n]) s ≠ s := by
  interval_cases n <;>
    cases s <;>
    simp_all [Function.iterate_succ_apply', ProjectivePolygonSide.vertexRotate,
      ProjectivePolygonSide.next, ProjectivePolygonSide.reverse]

namespace BuserSarnakProjectiveQuotientSectionData

/-- The start of the next side is the endpoint of the current side. -/
theorem polygonSideStart_next
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) :
    S.polygonSideStart q s.next = S.polygonSideEnd q s := by
  cases s
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change q = S.schreierData.toFiniteQuotientSchreierData.transition
      (S.polygonAfterC q) .e4
    exact (S.polygonAfterE4_eq q).symm

/-- Cross a side and advance to the next side of the adjacent face. -/
def polygonVertexRotate
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) :
    BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide :=
  ((S.polygonSidePartner q s).1, (S.polygonSidePartner q s).2.next)

/-- Package vertex-dart rotation as an endomorphism of all face-side darts. -/
def polygonVertexRotateDart
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p) :
    BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide →
      BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide :=
  fun d => S.polygonVertexRotate d.1 d.2

/-- Vertex-dart rotation preserves the primal vertex at which the directed
side begins. -/
theorem polygonVertexRotate_start
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) :
    S.polygonSideStart (S.polygonVertexRotate q s).1
      (S.polygonVertexRotate q s).2 = S.polygonSideStart q s := by
  rw [polygonVertexRotate, S.polygonSideStart_next,
    S.polygonSidePartner_end q s]

/-- The side component of a rotated dart is the explicit vertex cycle. -/
@[simp] theorem polygonVertexRotate_side
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) :
    (S.polygonVertexRotate q s).2 = s.vertexRotate := by
  simp [polygonVertexRotate, polygonSidePartner,
    ProjectivePolygonSide.vertexRotate]

/-- Iterating vertex-dart rotation applies the explicit side rotation at the
same rate. -/
theorem polygonVertexRotateDart_side_iterate
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) :
    ∀ n : ℕ,
      ((S.polygonVertexRotateDart^[n]) (q, s)).2 =
        (ProjectivePolygonSide.vertexRotate^[n]) s := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rw [polygonVertexRotateDart, S.polygonVertexRotate_side]
      rw [ih, Function.iterate_succ_apply']

/-- Iterated vertex-dart rotation continues to start at the same primal
vertex. -/
theorem polygonVertexRotateDart_start_iterate
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) :
    ∀ n : ℕ,
      S.polygonSideStart ((S.polygonVertexRotateDart^[n]) (q, s)).1
        ((S.polygonVertexRotateDart^[n]) (q, s)).2 =
          S.polygonSideStart q s := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change S.polygonSideStart
          (S.polygonVertexRotate ((S.polygonVertexRotateDart^[n]) (q, s)).1
            ((S.polygonVertexRotateDart^[n]) (q, s)).2).1
          (S.polygonVertexRotate ((S.polygonVertexRotateDart^[n]) (q, s)).1
            ((S.polygonVertexRotateDart^[n]) (q, s)).2).2 = _
      rw [S.polygonVertexRotate_start]
      exact ih

/-- Eight successive vertex-dart rotations return to the original dart. -/
theorem polygonVertexRotateDart_iterate_eight
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) :
    (S.polygonVertexRotateDart^[8]) (q, s) = (q, s) := by
  let d := (S.polygonVertexRotateDart^[8]) (q, s)
  have hside : d.2 = s := by
    simpa [d] using S.polygonVertexRotateDart_side_iterate q s 8
  have hstart : S.polygonSideStart d.1 s = S.polygonSideStart q s := by
    have h := S.polygonVertexRotateDart_start_iterate q s 8
    change S.polygonSideStart d.1 d.2 = S.polygonSideStart q s at h
    simpa only [hside] using h
  apply Prod.ext
  · change d.1 = q
    calc
      d.1 = S.polygonSideBase (S.polygonSideStart d.1 s) s :=
        (S.polygonSideBase_start d.1 s).symm
      _ = S.polygonSideBase (S.polygonSideStart q s) s :=
        congrArg (fun x => S.polygonSideBase x s) hstart
      _ = q := S.polygonSideBase_start q s
  · exact hside

/-- Seven further rotations undo one vertex-dart rotation on the left. -/
theorem polygonVertexRotateDart_iterate_seven_leftInverse
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p) :
    Function.LeftInverse (S.polygonVertexRotateDart^[7])
      S.polygonVertexRotateDart := by
  rintro ⟨q, s⟩
  calc
    (S.polygonVertexRotateDart^[7])
        (S.polygonVertexRotateDart (q, s)) =
      (S.polygonVertexRotateDart^[Nat.succ 7]) (q, s) :=
        (Function.iterate_succ_apply S.polygonVertexRotateDart 7 (q, s)).symm
    _ = (q, s) := S.polygonVertexRotateDart_iterate_eight q s

/-- Seven rotations also undo one vertex-dart rotation on the right. -/
theorem polygonVertexRotateDart_iterate_seven_rightInverse
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p) :
    Function.RightInverse (S.polygonVertexRotateDart^[7])
      S.polygonVertexRotateDart := by
  rintro ⟨q, s⟩
  calc
    S.polygonVertexRotateDart
        ((S.polygonVertexRotateDart^[7]) (q, s)) =
      (S.polygonVertexRotateDart^[Nat.succ 7]) (q, s) :=
        (Function.iterate_succ_apply' S.polygonVertexRotateDart 7 (q, s)).symm
    _ = (q, s) := S.polygonVertexRotateDart_iterate_eight q s

/-- Vertex-dart rotation is a permutation of the finite dart set. -/
theorem polygonVertexRotateDart_bijective
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p) :
    Function.Bijective S.polygonVertexRotateDart :=
  ⟨S.polygonVertexRotateDart_iterate_seven_leftInverse.injective,
    fun d => ⟨(S.polygonVertexRotateDart^[7]) d,
      S.polygonVertexRotateDart_iterate_seven_rightInverse d⟩⟩

end BuserSarnakProjectiveQuotientSectionData

end

end SystolicGrowth
