module

public import BuserSarnak.BuserSarnakProjectivePolygonPostConeQuiver
public import BuserSarnak.BuserSarnakProjectivePolygonDarts

@[expose] public section

/-!
# Connectivity reduction for the post-cone physical quiver

The full directed polygon-side quiver is already connected.  This module
reduces survivor-edge connectivity to explicit path repairs for its individual
side arrows.  The remaining tree--cotree proof must construct those repairs
for the canonical section's deleted primal edges.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

noncomputable local instance buserSarnakProjectivePolygonPostConeConnectivityRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

/-- Regard a face of the full directed polygon-side quiver as a vertex of the
symmetrized physical post-cone quiver. -/
def canonicalProjectivePolygonFaceToPostConeFace
    {p : ℕ} [NeZero p]
    (q : ProjectivePolygonFace (canonicalBuserSarnakProjectiveQuotientSectionData p)) :
    Quiver.Symmetrify (ProjectivePolygonPostConeFace p) :=
  ⟨q.state⟩

private theorem projectivePolygonPostCone_path_of_edge
    {p : ℕ} [NeZero p]
    {q r : ProjectivePolygonPostConeFace p} (e : q ⟶ r) :
    Nonempty (@Quiver.Path (Quiver.Symmetrify (ProjectivePolygonPostConeFace p))
      (Quiver.symmetrifyQuiver (ProjectivePolygonPostConeFace p)) q r) :=
  ⟨Quiver.Hom.toPath (Sum.inl e)⟩

private theorem projectivePolygonPostCone_path_of_reverse_edge
    {p : ℕ} [NeZero p]
    {q r : ProjectivePolygonPostConeFace p} (e : q ⟶ r) :
    Nonempty (@Quiver.Path (Quiver.Symmetrify (ProjectivePolygonPostConeFace p))
      (Quiver.symmetrifyQuiver (ProjectivePolygonPostConeFace p)) r q) :=
  ⟨Quiver.Hom.toPath (Sum.inr e)⟩

private theorem projectivePolygonPostCone_oneEdge_of_positive_noncone
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide)
    (hs : s = .a ∨ s = .c)
    (hraw : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol q s)) :
    Nonempty (@Quiver.Path (Quiver.Symmetrify (ProjectivePolygonPostConeFace p))
      (Quiver.symmetrifyQuiver (ProjectivePolygonPostConeFace p))
      (⟨q⟩ : ProjectivePolygonPostConeFace p)
      ⟨((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1⟩) := by
  rcases hs with rfl | rfl
  · let z := canonicalProjectiveConeKeptPolygonNonconeSide q .a hraw (Or.inl rfl)
    apply projectivePolygonPostCone_path_of_edge
    exact ⟨z, rfl, rfl⟩
  · let S := canonicalBuserSarnakProjectiveQuotientSectionData p
    let z := canonicalProjectiveConeKeptPolygonNonconeSide q .c hraw (Or.inr rfl)
    apply projectivePolygonPostCone_path_of_edge
    refine ⟨z, ?_, ?_⟩
    · change (⟨S.polygonSideBase (S.polygonSideStart q .c) .c⟩ :
          ProjectivePolygonPostConeFace p) = ⟨q⟩
      rw [S.polygonSideBase_start q .c]
    · change ⟨(S.polygonSidePartner
        (S.polygonSideBase (S.polygonSideStart q .c) .c) .c).1⟩ =
        (⟨(S.polygonSidePartner q .c).1⟩ : ProjectivePolygonPostConeFace p)
      rw [S.polygonSideBase_start q .c]

private theorem projectivePolygonPostCone_oneEdge_of_cone_raw
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (e : ProjectiveOctagonConeGenerator)
    (r : BuserSarnakProjectiveReductionRange p)
    (hsource : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (r, e.lift))
    (htarget : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (buserSarnakProjectiveConePartner p e r, e.lift)) :
    Nonempty (@Quiver.Path (Quiver.Symmetrify (ProjectivePolygonPostConeFace p))
      (Quiver.symmetrifyQuiver (ProjectivePolygonPostConeFace p))
      (⟨(canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideBase r
        e.lift.positivePolygonSide⟩ : ProjectivePolygonPostConeFace p)
      ⟨((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideBase r
          e.lift.positivePolygonSide)
        e.lift.positivePolygonSide).1⟩) := by
  classical
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
  change Nonempty (@Quiver.Path (Quiver.Symmetrify (ProjectivePolygonPostConeFace p))
    (Quiver.symmetrifyQuiver (ProjectivePolygonPostConeFace p))
    (⟨F⟩ : ProjectivePolygonPostConeFace p) ⟨G⟩)
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
    apply projectivePolygonPostCone_path_of_reverse_edge
    refine ⟨z, ?_, ?_⟩
    · change (⟨S.polygonSideBase (buserSarnakProjectiveConePartner p e r) side⟩ :
          ProjectivePolygonPostConeFace p) = ⟨G⟩
      rw [hbaseG]
    · change (⟨(S.polygonSidePartner
          (S.polygonSideBase (buserSarnakProjectiveConePartner p e r) side) side).1⟩ :
          ProjectivePolygonPostConeFace p) = ⟨F⟩
      rw [hbaseG]
      exact congrArg ProjectivePolygonPostConeFace.mk (congrArg Prod.fst hback)
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
    apply projectivePolygonPostCone_path_of_edge
    refine ⟨z, ?_, ?_⟩
    · apply congrArg ProjectivePolygonPostConeFace.mk
      simp [z, i, canonicalProjectiveConeKeptTarget,
        canonicalProjectiveConePairTarget,
        projectivePolygonPostConeEdgeSide, F, side, S]
    · apply congrArg ProjectivePolygonPostConeFace.mk
      simp [z, i, canonicalProjectiveConeKeptTarget,
        canonicalProjectiveConePairTarget,
        projectivePolygonPostConeEdgeSource, projectivePolygonPostConeEdgeSide,
        F, G, side, S]

/-- A polygon side whose two raw Schreier labels survive the canonical tree
and the cone stage is represented by one physical post-cone edge. -/
theorem projectivePolygonPostCone_oneEdge_of_raw_and_partner_nondegenerate
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide)
    (hraw : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol q s))
    (hpartner : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2)) :
    Nonempty (Quiver.Path
      (canonicalProjectivePolygonFaceToPostConeFace
        (⟨q⟩ : ProjectivePolygonFace
          (canonicalBuserSarnakProjectiveQuotientSectionData p)))
      (canonicalProjectivePolygonFaceToPostConeFace
        (⟨((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1⟩ :
          ProjectivePolygonFace
            (canonicalBuserSarnakProjectiveQuotientSectionData p)))) := by
  classical
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  change Nonempty (@Quiver.Path (Quiver.Symmetrify (ProjectivePolygonPostConeFace p))
    (Quiver.symmetrifyQuiver (ProjectivePolygonPostConeFace p))
    (⟨q⟩ : Quiver.Symmetrify (ProjectivePolygonPostConeFace p))
    ⟨(S.polygonSidePartner q s).1⟩)
  cases s with
  | a =>
      exact projectivePolygonPostCone_oneEdge_of_positive_noncone q .a (Or.inl rfl) hraw
  | e1 =>
      let r := S.polygonSideRawSymbol q .e1 |>.1
      have hsource : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
          (r, ProjectiveOctagonGenerator.e1) := by
        exact hraw
      have htarget : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
          (buserSarnakProjectiveConePartner p .e1 r, ProjectiveOctagonGenerator.e1) := by
        change ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
          (S.schreierData.toFiniteQuotientSchreierData.transition
            (S.polygonSideRawSymbol q .e1).1
            (S.polygonSideRawSymbol q .e1).2,
            (S.polygonSideRawSymbol q .e1).2)
        have hpair : S.polygonSideRawSymbol (S.polygonSidePartner q .e1).1
            (S.polygonSidePartner q .e1).2 =
            (S.schreierData.toFiniteQuotientSchreierData.transition
              (S.polygonSideRawSymbol q .e1).1
              (S.polygonSideRawSymbol q .e1).2,
              (S.polygonSideRawSymbol q .e1).2) := by
          simpa using S.polygonSideRawSymbol_partner q .e1
        rw [← hpair]
        exact hpartner
      obtain ⟨path⟩ := projectivePolygonPostCone_oneEdge_of_cone_raw hp hp2 .e1 r
        hsource htarget
      have hbase : S.polygonSideBase r .e1 = q := by
        change S.polygonSideBase (S.polygonSideStart q .e1) .e1 = q
        exact S.polygonSideBase_start q .e1
      exact ⟨by
        simpa [S, ProjectiveOctagonConeGenerator.lift,
          ProjectiveOctagonGenerator.positivePolygonSide, hbase] using path⟩
  | cInv =>
      let q' := (S.polygonSidePartner q .cInv).1
      have hraw' : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
          (S.polygonSideRawSymbol q' .c) := by
        change ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
          (S.polygonSideRawSymbol (S.polygonSidePartner q .cInv).1
            (S.polygonSidePartner q .cInv).2)
        exact hpartner
      obtain ⟨path⟩ := projectivePolygonPostCone_oneEdge_of_positive_noncone q' .c
        (Or.inr rfl) hraw'
      have htarget : S.polygonSidePartner q' .c = (q, .cInv) := by
        change S.polygonSidePartner (S.polygonSidePartner q .cInv).1
          (S.polygonSidePartner q .cInv).2 = (q, .cInv)
        exact S.polygonSidePartner_involutive q .cInv
      rw [htarget] at path
      exact ⟨path.reverse⟩
  | e2 =>
      let r := S.polygonSideRawSymbol q .e2 |>.1
      have hsource : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
          (r, ProjectiveOctagonGenerator.e2) := by
        exact hraw
      have htarget : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
          (buserSarnakProjectiveConePartner p .e2 r, ProjectiveOctagonGenerator.e2) := by
        change ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
          (S.schreierData.toFiniteQuotientSchreierData.transition
            (S.polygonSideRawSymbol q .e2).1
            (S.polygonSideRawSymbol q .e2).2,
            (S.polygonSideRawSymbol q .e2).2)
        have hpair : S.polygonSideRawSymbol (S.polygonSidePartner q .e2).1
            (S.polygonSidePartner q .e2).2 =
            (S.schreierData.toFiniteQuotientSchreierData.transition
              (S.polygonSideRawSymbol q .e2).1
              (S.polygonSideRawSymbol q .e2).2,
              (S.polygonSideRawSymbol q .e2).2) := by
          simpa using S.polygonSideRawSymbol_partner q .e2
        rw [← hpair]
        exact hpartner
      obtain ⟨path⟩ := projectivePolygonPostCone_oneEdge_of_cone_raw hp hp2 .e2 r
        hsource htarget
      have hbase : S.polygonSideBase r .e2 = q := by
        change S.polygonSideBase (S.polygonSideStart q .e2) .e2 = q
        exact S.polygonSideBase_start q .e2
      exact ⟨by
        simpa [S, ProjectiveOctagonConeGenerator.lift,
          ProjectiveOctagonGenerator.positivePolygonSide, hbase] using path⟩
  | aInv =>
      let q' := (S.polygonSidePartner q .aInv).1
      have hraw' : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
          (S.polygonSideRawSymbol q' .a) := by
        change ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
          (S.polygonSideRawSymbol (S.polygonSidePartner q .aInv).1
            (S.polygonSidePartner q .aInv).2)
        exact hpartner
      obtain ⟨path⟩ := projectivePolygonPostCone_oneEdge_of_positive_noncone q' .a
        (Or.inl rfl) hraw'
      have htarget : S.polygonSidePartner q' .a = (q, .aInv) := by
        change S.polygonSidePartner (S.polygonSidePartner q .aInv).1
          (S.polygonSidePartner q .aInv).2 = (q, .aInv)
        exact S.polygonSidePartner_involutive q .aInv
      rw [htarget] at path
      exact ⟨path.reverse⟩
  | e3 =>
      let r := S.polygonSideRawSymbol q .e3 |>.1
      have hsource : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
          (r, ProjectiveOctagonGenerator.e3) := by
        exact hraw
      have htarget : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
          (buserSarnakProjectiveConePartner p .e3 r, ProjectiveOctagonGenerator.e3) := by
        change ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
          (S.schreierData.toFiniteQuotientSchreierData.transition
            (S.polygonSideRawSymbol q .e3).1
            (S.polygonSideRawSymbol q .e3).2,
            (S.polygonSideRawSymbol q .e3).2)
        have hpair : S.polygonSideRawSymbol (S.polygonSidePartner q .e3).1
            (S.polygonSidePartner q .e3).2 =
            (S.schreierData.toFiniteQuotientSchreierData.transition
              (S.polygonSideRawSymbol q .e3).1
              (S.polygonSideRawSymbol q .e3).2,
              (S.polygonSideRawSymbol q .e3).2) := by
          simpa using S.polygonSideRawSymbol_partner q .e3
        rw [← hpair]
        exact hpartner
      obtain ⟨path⟩ := projectivePolygonPostCone_oneEdge_of_cone_raw hp hp2 .e3 r
        hsource htarget
      have hbase : S.polygonSideBase r .e3 = q := by
        change S.polygonSideBase (S.polygonSideStart q .e3) .e3 = q
        exact S.polygonSideBase_start q .e3
      exact ⟨by
        simpa [S, ProjectiveOctagonConeGenerator.lift,
          ProjectiveOctagonGenerator.positivePolygonSide, hbase] using path⟩
  | c =>
      exact projectivePolygonPostCone_oneEdge_of_positive_noncone q .c (Or.inr rfl) hraw
  | e4 =>
      let r := S.polygonSideRawSymbol q .e4 |>.1
      have hsource : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
          (r, ProjectiveOctagonGenerator.e4) := by
        exact hraw
      have htarget : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
          (buserSarnakProjectiveConePartner p .e4 r, ProjectiveOctagonGenerator.e4) := by
        change ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
          (S.schreierData.toFiniteQuotientSchreierData.transition
            (S.polygonSideRawSymbol q .e4).1
            (S.polygonSideRawSymbol q .e4).2,
            (S.polygonSideRawSymbol q .e4).2)
        have hpair : S.polygonSideRawSymbol (S.polygonSidePartner q .e4).1
            (S.polygonSidePartner q .e4).2 =
            (S.schreierData.toFiniteQuotientSchreierData.transition
              (S.polygonSideRawSymbol q .e4).1
              (S.polygonSideRawSymbol q .e4).2,
              (S.polygonSideRawSymbol q .e4).2) := by
          simpa using S.polygonSideRawSymbol_partner q .e4
        rw [← hpair]
        exact hpartner
      obtain ⟨path⟩ := projectivePolygonPostCone_oneEdge_of_cone_raw hp hp2 .e4 r
        hsource htarget
      have hbase : S.polygonSideBase r .e4 = q := by
        change S.polygonSideBase (S.polygonSideStart q .e4) .e4 = q
        exact S.polygonSideBase_start q .e4
      exact ⟨by
        simpa [S, ProjectiveOctagonConeGenerator.lift,
          ProjectiveOctagonGenerator.positivePolygonSide, hbase] using path⟩

/-- If every full polygon-side arrow can be repaired by a path of surviving
physical edges, then the physical quiver is rooted-connected. -/
theorem projectivePolygonPostConeRootedConnected_of_fullEdgeRepair
    {p : ℕ} [NeZero p]
  (repair : ∀ ⦃q r :
      ProjectivePolygonFace (canonicalBuserSarnakProjectiveQuotientSectionData p)⦄,
      (q ⟶ r) → Nonempty (Quiver.Path
        (canonicalProjectivePolygonFaceToPostConeFace q)
      (canonicalProjectivePolygonFaceToPostConeFace r))) :
    Quiver.RootedConnected (projectivePolygonPostConeRoot p) := by
  constructor
  rintro ⟨v⟩
  let target :
      ProjectivePolygonFace (canonicalBuserSarnakProjectiveQuotientSectionData p) :=
    ⟨v⟩
  obtain ⟨fullPath⟩ :=
    (ProjectivePolygonFace.rootedConnected
      (canonicalBuserSarnakProjectiveQuotientSectionData p)).nonempty_path target
  have liftPath : ∀ {q r :
      ProjectivePolygonFace (canonicalBuserSarnakProjectiveQuotientSectionData p)},
      Quiver.Path q r → Nonempty (Quiver.Path
        (canonicalProjectivePolygonFaceToPostConeFace q)
        (canonicalProjectivePolygonFaceToPostConeFace r)) := by
    intro q r path
    induction path with
    | nil => exact ⟨.nil⟩
    | cons path edge ih =>
        rcases ih with ⟨path⟩
        rcases repair edge with ⟨edgePath⟩
        exact ⟨path.comp edgePath⟩
  obtain ⟨path⟩ := liftPath fullPath
  simpa [canonicalProjectivePolygonFaceToPostConeFace, target,
    ProjectivePolygonFace.root, projectivePolygonPostConeRoot] using
    (show Nonempty (Quiver.Path
      (canonicalProjectivePolygonFaceToPostConeFace
        (ProjectivePolygonFace.root
          (canonicalBuserSarnakProjectiveQuotientSectionData p)))
      (canonicalProjectivePolygonFaceToPostConeFace target)) from ⟨path⟩)

end

end SystolicGrowth
