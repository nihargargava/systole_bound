module

public import BuserSarnak.BuserSarnakProjectivePolygonPostConeBoundary
public import BuserSarnak.BuserSarnakProjectivePolygonPostConeDartCycle
public import BuserSarnak.BuserSarnakProjectivePolygonTreeCarriers

@[expose] public section

/-!
# Rooted connectivity of the post-cone projective polygon quiver

The finite tree--cotree argument removes every possible root-component cut.
A crossing supplies a canonical tree carrier; choosing one of maximal target
height makes its target a leaf of the crossing boundary.  The eight darts at
that primal vertex then rule out the crossing by the explicit dart cycle.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete

/-- If the paired occurrence of a polygon dart carries a canonical tree
symbol, then the original dart is one of that edge's two physical carriers. -/
theorem isCanonicalProjectivePolygonTreeCarrier_of_partnerRawSymbol_eq
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide)
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p)
    (hraw : (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2 = z.1) :
    IsCanonicalProjectivePolygonTreeCarrier z (q, s) := by
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  have hcarrier : IsCanonicalProjectivePolygonTreeCarrier z (S.polygonSidePartner q s) :=
    isCanonicalProjectivePolygonTreeCarrier_of_rawSymbol_eq
      (S.polygonSidePartner q s).1 (S.polygonSidePartner q s).2 z (by simpa [S] using hraw)
  rcases hcarrier with hsource | htarget
  · right
    calc
      (q, s) = S.polygonSidePartner (S.polygonSidePartner q s).1
          (S.polygonSidePartner q s).2 :=
        (BuserSarnakProjectiveQuotientSectionData.polygonSidePartner_involutive S q s).symm
      _ = S.polygonSidePartner (canonicalProjectivePolygonTreeSourceDart z).1
          (canonicalProjectivePolygonTreeSourceDart z).2 := by rw [hsource]
      _ = canonicalProjectivePolygonTreeTargetDart z := rfl
  · left
    calc
      (q, s) = S.polygonSidePartner (S.polygonSidePartner q s).1
          (S.polygonSidePartner q s).2 :=
        (BuserSarnakProjectiveQuotientSectionData.polygonSidePartner_involutive S q s).symm
      _ = S.polygonSidePartner (canonicalProjectivePolygonTreeTargetDart z).1
          (canonicalProjectivePolygonTreeTargetDart z).2 := by rw [htarget]
      _ = canonicalProjectivePolygonTreeSourceDart z :=
        polygonSidePartner_canonicalProjectivePolygonTreeTargetDart z

/-- A raw-label witness from either side of a paired polygon edge identifies
the original dart as a carrier of the displayed canonical tree symbol. -/
theorem isCanonicalProjectivePolygonTreeCarrier_of_raw_or_partnerRawSymbol_eq
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide)
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p)
    (hraw : z.1 = (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol q s ∨
      z.1 = (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2) :
    IsCanonicalProjectivePolygonTreeCarrier z (q, s) := by
  rcases hraw with hraw | hraw
  · exact isCanonicalProjectivePolygonTreeCarrier_of_rawSymbol_eq q s z hraw.symm
  · exact isCanonicalProjectivePolygonTreeCarrier_of_partnerRawSymbol_eq q s z hraw.symm

/-- At a maximal target height in the crossing boundary, every nontrivial
rotation of that target carrier is a noncrossing. -/
theorem projectivePolygonPostConeDart_not_crossing_of_maxTargetHeight
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    {z : CanonicalBuserSarnakProjectiveDegenerateSymbol p}
    (hmax : ∀ w ∈ projectivePolygonPostConeCrossingTreeSymbols p,
      canonicalProjectiveWordHeight p (canonicalProjectiveTreeTarget p w) ≤
        canonicalProjectiveWordHeight p (canonicalProjectiveTreeTarget p z))
    (n : ℕ) (hnpos : 0 < n) (hnlt : n < 8) :
    ¬ projectivePolygonPostConeDartCrossing
      (((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonVertexRotateDart^[n])
        (canonicalProjectivePolygonTreeTargetDart z)) := by
  intro hcross
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  let d := (S.polygonVertexRotateDart^[n]) (canonicalProjectivePolygonTreeTargetDart z)
  have hcross' : projectivePolygonPostConeCrossing d.1 d.2 := by
    simpa [S, d, projectivePolygonPostConeDartCrossing] using hcross
  obtain ⟨w, hw, hraw⟩ :=
    projectivePolygonPostConeCrossing_exists_mem_treeSymbols hp hp2 d.1 d.2 hcross'
  have hcarrier : IsCanonicalProjectivePolygonTreeCarrier w d :=
    isCanonicalProjectivePolygonTreeCarrier_of_raw_or_partnerRawSymbol_eq d.1 d.2 w hraw
  have hstart : S.polygonSideStart d.1 d.2 =
      S.polygonSideStart (canonicalProjectivePolygonTreeTargetDart z).1
        (canonicalProjectivePolygonTreeTargetDart z).2 := by
    simpa [S, d] using S.polygonVertexRotateDart_start_iterate
      (canonicalProjectivePolygonTreeTargetDart z).1
      (canonicalProjectivePolygonTreeTargetDart z).2 n
  have hincident : w.1.1 = canonicalProjectiveTreeTarget p z ∨
      canonicalProjectiveTreeTarget p w = canonicalProjectiveTreeTarget p z := by
    rcases polygonSideStart_of_isCanonicalProjectivePolygonTreeCarrier hcarrier with
      hsource | htarget
    · left
      change w.1.1 = (canonicalBuserSarnakProjectiveDegenerateTarget p z).1
      calc
        w.1.1 = S.polygonSideStart d.1 d.2 := hsource.symm
        _ = S.polygonSideStart (canonicalProjectivePolygonTreeTargetDart z).1
            (canonicalProjectivePolygonTreeTargetDart z).2 := hstart
        _ = (canonicalBuserSarnakProjectiveDegenerateTarget p z).1 :=
          polygonSideStart_canonicalProjectivePolygonTreeTargetDart z
    · right
      change (canonicalBuserSarnakProjectiveDegenerateTarget p w).1 =
        (canonicalBuserSarnakProjectiveDegenerateTarget p z).1
      calc
        (canonicalBuserSarnakProjectiveDegenerateTarget p w).1 =
            S.polygonSideStart d.1 d.2 := htarget.symm
        _ = S.polygonSideStart (canonicalProjectivePolygonTreeTargetDart z).1
            (canonicalProjectivePolygonTreeTargetDart z).2 := hstart
        _ = (canonicalBuserSarnakProjectiveDegenerateTarget p z).1 :=
          polygonSideStart_canonicalProjectivePolygonTreeTargetDart z
  have hwz : w = z :=
    canonicalProjectiveTree_maxTarget_incident_eq hw hmax hincident
  subst w
  have hdtarget : d = canonicalProjectivePolygonTreeTargetDart z := by
    rcases hcarrier with hsource | htarget
    · exfalso
      apply polygonSideStart_treeSourceDart_ne_treeTargetDart z
      calc
        S.polygonSideStart (canonicalProjectivePolygonTreeSourceDart z).1
            (canonicalProjectivePolygonTreeSourceDart z).2 = S.polygonSideStart d.1 d.2 :=
          congrArg (fun e : CanonicalProjectivePolygonDart p =>
            S.polygonSideStart e.1 e.2) hsource.symm
        _ = S.polygonSideStart (canonicalProjectivePolygonTreeTargetDart z).1
            (canonicalProjectivePolygonTreeTargetDart z).2 := hstart
    · exact htarget
  have hside := congrArg Prod.snd hdtarget
  have hrotateSide := S.polygonVertexRotateDart_side_iterate
    (canonicalProjectivePolygonTreeTargetDart z).1
    (canonicalProjectivePolygonTreeTargetDart z).2 n
  apply ProjectivePolygonSide.vertexRotate_iterate_ne_self_of_pos_lt_eight
    (canonicalProjectivePolygonTreeTargetDart z).2 hnpos hnlt
  calc
    (ProjectivePolygonSide.vertexRotate^[n])
        (canonicalProjectivePolygonTreeTargetDart z).2 = d.2 := by
      simpa [S, d] using hrotateSide.symm
    _ = (canonicalProjectivePolygonTreeTargetDart z).2 := hside

/-- Every quotient state is connected to the physical post-cone root. -/
theorem projectivePolygonPostConeRootComponent_all
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) :
    projectivePolygonPostConeRootComponent p q := by
  by_contra hq
  obtain ⟨r, s, hcross⟩ :=
    exists_projectivePolygonPostConeCrossing_of_not_rootComponent hq
  obtain ⟨w, hw, _⟩ :=
    projectivePolygonPostConeCrossing_exists_mem_treeSymbols hp hp2 r s hcross
  obtain ⟨z, hz, hmax⟩ := canonicalProjectiveTree_exists_maxTargetHeight
    (projectivePolygonPostConeCrossingTreeSymbols p) ⟨w, hw⟩
  have htargetCrossing : projectivePolygonPostConeDartCrossing
      (canonicalProjectivePolygonTreeTargetDart z) :=
    projectivePolygonPostConeCrossing_treeTargetDart_of_mem_treeSymbols hz
  have hrot : ∀ n : ℕ, 1 ≤ n → n ≤ 7 →
      ¬ projectivePolygonPostConeDartCrossing
        (((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonVertexRotateDart^[n])
          (canonicalProjectivePolygonTreeTargetDart z)) := by
    intro n hn1 hn7
    exact projectivePolygonPostConeDart_not_crossing_of_maxTargetHeight hp hp2 hmax n
      (by omega) (by omega)
  have hnot := projectivePolygonPostConeDart_not_crossing_of_rotations_not_crossing
    (canonicalProjectivePolygonTreeTargetDart z).1
    (canonicalProjectivePolygonTreeTargetDart z).2 hrot
  exact hnot htargetCrossing

/-- The symmetrized physical post-cone quiver is rooted-connected. -/
theorem projectivePolygonPostConeRootedConnected
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Quiver.RootedConnected (projectivePolygonPostConeRoot p) := by
  constructor
  rintro ⟨q⟩
  simpa [projectivePolygonPostConeRootComponent, projectivePolygonPostConeVertex,
    canonicalProjectivePolygonFaceToPostConeFace, projectivePolygonPostConeRoot] using
    (projectivePolygonPostConeRootComponent_all hp hp2 q)

/-- The now-unconditional (at odd prime levels) geodesic physical spanning
tree.  This packages the rooted-connectivity theorem into the exact tree type
used by the second Tietze stage. -/
noncomputable def projectivePolygonPostConeCanonicalSpanningTree
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    WideSubquiver (Quiver.Symmetrify (ProjectivePolygonPostConeFace p)) := by
  letI : Quiver.RootedConnected (projectivePolygonPostConeRoot p) :=
    projectivePolygonPostConeRootedConnected hp hp2
  exact projectivePolygonPostConeSpanningTree p

/-- The arborescence structure on the explicit physical spanning tree. -/
@[instance_reducible] noncomputable def projectivePolygonPostConeCanonicalSpanningTreeArborescence
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Quiver.Arborescence (projectivePolygonPostConeCanonicalSpanningTree hp hp2) := by
  unfold projectivePolygonPostConeCanonicalSpanningTree
  letI : Quiver.RootedConnected (projectivePolygonPostConeRoot p) :=
    projectivePolygonPostConeRootedConnected hp hp2
  infer_instance

end

end SystolicGrowth
