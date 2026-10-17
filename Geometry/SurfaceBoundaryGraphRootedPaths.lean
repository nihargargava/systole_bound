module

public import Geometry.SurfaceBoundaryGraphWordFunctor
public import Geometry.SurfaceBoundaryGraphComponentPaths
public import Mathlib.Topology.Subpath

@[expose] public section

/-!
# Actual rooted paths for the physical star--midsection cover

The star paths use the original vertex-star contractions and the actual
selected-tree connectors. Middle paths use the canonical physical side and
its literal interval prefix at the inverse homeomorphism parameter.
-/

open Set UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth

noncomputable section

private theorem rooted_paths_homotopic_in_contractible
    {A : Type*} [TopologicalSpace A] (S : Set A) [ContractibleSpace S]
    {x y : A} (p q : Path x y) (hp : ∀ t, p t ∈ S) (hq : ∀ t, q t ∈ S) :
    p.Homotopic q := by
  have hx : x ∈ S := by simpa only [p.source] using hp 0
  have hy : y ∈ S := by simpa only [p.target] using hp 1
  let pS : Path (⟨x, hx⟩ : S) ⟨y, hy⟩ :=
    { toFun t := ⟨p t, hp t⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := Subtype.ext p.source
      target' := Subtype.ext p.target }
  let qS : Path (⟨x, hx⟩ : S) ⟨y, hy⟩ :=
    { toFun t := ⟨q t, hq t⟩
      continuous_toFun := q.continuous.subtype_mk _
      source' := Subtype.ext q.source
      target' := Subtype.ext q.target }
  have h := (SimplyConnectedSpace.paths_homotopic pS qS).map
    ⟨Subtype.val, continuous_subtype_val⟩
  simpa only [show pS.map continuous_subtype_val = p by ext t; rfl,
    show qS.map continuous_subtype_val = q by ext t; rfl] using h

private theorem rooted_trans_mem {A : Type*} [TopologicalSpace A] {S : Set A}
    {x y z : A} (p : Path x y) (q : Path y z)
    (hp : ∀ t, p t ∈ S) (hq : ∀ t, q t ∈ S) (t : unitInterval) :
    p.trans q t ∈ S := by
  rw [Path.trans_apply]
  split_ifs
  · exact hp _
  · exact hq _

private theorem rooted_prefix_suffix {A : Type*} [TopologicalSpace A]
    {r a q b : A} (ca : Path r a) (cb : Path r b)
    (p : Path a q) (s : Path q b) (γ : Path a b) (h : (p.trans s).Homotopic γ) :
    ((ca.trans p).trans (cb.trans s.symm).symm).Homotopic
      ((ca.trans γ).trans cb.symm) := by
  rw [Path.trans_symm, Path.symm_symm]
  exact (Path.Homotopic.trans_assoc _ _ _).symm.trans
    (((Path.Homotopic.trans_assoc _ _ _).trans ((Path.Homotopic.refl _).hcomp h)).hcomp
      (Path.Homotopic.refl _))

namespace DirichletBoundarySegments

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

/-- **Math.** The unique actual vertex whose open star contains this point. -/
def intrinsicBoundaryStarVertex (B : DirichletBoundarySegments X o)
    (q : B.intrinsicBoundaryGraphStarUnion) : B.IntrinsicBoundaryGraphVertex :=
  Classical.choose (mem_iUnion.mp q.property)

theorem intrinsicBoundaryStarVertex_mem (B : DirichletBoundarySegments X o)
    (q : B.intrinsicBoundaryGraphStarUnion) :
    q.val ∈ B.intrinsicBoundaryGraphVertexStar (B.intrinsicBoundaryStarVertex q) :=
  Classical.choose_spec (mem_iUnion.mp q.property)

theorem intrinsicBoundaryStarVertex_eq_of_mem (B : DirichletBoundarySegments X o)
    (q : B.intrinsicBoundaryGraphStarUnion) (v : B.IntrinsicBoundaryGraphVertex)
    (hv : q.val ∈ B.intrinsicBoundaryGraphVertexStar v) :
    B.intrinsicBoundaryStarVertex q = v :=
  B.intrinsicBoundaryGraphVertexStar_mem_unique (B.intrinsicBoundaryStarVertex_mem q) hv

/-- **Math.** The center-to-point path of the genuine star contraction. -/
def intrinsicBoundaryGraphStarCenterPath (B : DirichletBoundarySegments X o)
    (v : B.IntrinsicBoundaryGraphVertex) (q : B.intrinsicBoundaryGraphVertexStar v) :
    Path (B.intrinsicBoundaryGraphVertexInclusion v) q.val :=
  ((B.intrinsicBoundaryGraphVertexStarContraction v).evalAt q).symm.map continuous_subtype_val

theorem intrinsicBoundaryGraphStarCenterPath_mem (B : DirichletBoundarySegments X o)
    (v : B.IntrinsicBoundaryGraphVertex) (q : B.intrinsicBoundaryGraphVertexStar v)
    (t : unitInterval) :
    B.intrinsicBoundaryGraphStarCenterPath v q t ∈ B.intrinsicBoundaryGraphVertexStar v :=
  (((B.intrinsicBoundaryGraphVertexStarContraction v).evalAt q).symm t).property

/-- **Math.** An actual root-to-star point path, using the unique actual vertex. -/
def intrinsicBoundaryGraphStarRootedPath (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) (q : B.intrinsicBoundaryGraphStarUnion) :
    Path (B.intrinsicBoundaryGraphVertexInclusion r) q.val :=
  (B.intrinsicBoundaryTreeConnector r (B.intrinsicBoundaryStarVertex q)).trans
    (B.intrinsicBoundaryGraphStarCenterPath (B.intrinsicBoundaryStarVertex q)
      ⟨q.val, B.intrinsicBoundaryStarVertex_mem q⟩)

theorem intrinsicBoundaryGraphStarRootedPath_eq_of_mem (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) (q : B.intrinsicBoundaryGraphStarUnion)
    (v : B.IntrinsicBoundaryGraphVertex) (hv : q.val ∈ B.intrinsicBoundaryGraphVertexStar v) :
    B.intrinsicBoundaryGraphStarRootedPath r q =
      (B.intrinsicBoundaryTreeConnector r v).trans
        (B.intrinsicBoundaryGraphStarCenterPath v ⟨q.val, hv⟩) := by
  have h := B.intrinsicBoundaryStarVertex_eq_of_mem q v hv
  subst v
  rfl

/-- **Math.** The literal original side prefix, with its true start vertex. -/
def intrinsicBoundaryGraphSidePrefix (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) (s : unitInterval) :
    Path (B.intrinsicBoundaryGraphVertexInclusion (B.intrinsicBoundaryGraphSideStart i))
      (B.intrinsicBoundaryGraphSidePath i s) :=
  ((B.intrinsicBoundaryGraphSidePath i).subpath 0 s).cast (Path.source _).symm rfl

/-- **Math.** The literal original side suffix, with its true end vertex. -/
def intrinsicBoundaryGraphSideSuffix (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) (s : unitInterval) :
    Path (B.intrinsicBoundaryGraphSidePath i s)
      (B.intrinsicBoundaryGraphVertexInclusion (B.intrinsicBoundaryGraphSideEnd i)) :=
  ((B.intrinsicBoundaryGraphSidePath i).subpath s 1).cast rfl (Path.target _).symm

/-- **Math.** The exact inverse-homeomorphism parameter of the original side. -/
def intrinsicBoundaryGraphMidsectionParameter (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) (q : B.intrinsicBoundaryGraphEdgeMidsection i) :
    unitInterval :=
  let s := (B.intrinsicBoundaryGraphMidsectionHomeomorph i).symm q
  ⟨s.val, by constructor <;> linarith [s.property.1, s.property.2]⟩

theorem intrinsicBoundaryGraphMidsectionParameter_point (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) (q : B.intrinsicBoundaryGraphEdgeMidsection i) :
    B.intrinsicBoundaryGraphSidePath i (B.intrinsicBoundaryGraphMidsectionParameter i q) = q.val := by
  have h := congrArg Subtype.val ((B.intrinsicBoundaryGraphMidsectionHomeomorph i).apply_symm_apply q)
  rw [B.intrinsicBoundaryGraphMidsectionHomeomorph_apply] at h
  exact h

theorem intrinsicBoundaryGraphMidsectionParameter_bounds (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) (q : B.intrinsicBoundaryGraphEdgeMidsection i) :
    (1 / 4 : ℝ) < B.intrinsicBoundaryGraphMidsectionParameter i q ∧
      (B.intrinsicBoundaryGraphMidsectionParameter i q : ℝ) < 3 / 4 :=
  ((B.intrinsicBoundaryGraphMidsectionHomeomorph i).symm q).property

private theorem midsectionParameter_initial (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) (q : B.intrinsicBoundaryGraphEdgeMidsection i)
    (hq : q.val ∈ B.intrinsicBoundaryGraphInitialOverlap i) :
    (B.intrinsicBoundaryGraphMidsectionParameter i q : ℝ) < 1 / 3 := by
  obtain ⟨s, hs, hsq⟩ := hq
  have h : (B.intrinsicBoundaryGraphMidsectionHomeomorph i).symm q = s := by
    apply (B.intrinsicBoundaryGraphMidsectionHomeomorph i).injective
    rw [(B.intrinsicBoundaryGraphMidsectionHomeomorph i).apply_symm_apply]
    exact Subtype.ext hsq.symm
  change (((B.intrinsicBoundaryGraphMidsectionHomeomorph i).symm q).val : ℝ) < 1 / 3
  rw [h]
  exact hs

private theorem midsectionParameter_terminal (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) (q : B.intrinsicBoundaryGraphEdgeMidsection i)
    (hq : q.val ∈ B.intrinsicBoundaryGraphTerminalOverlap i) :
    (2 / 3 : ℝ) < B.intrinsicBoundaryGraphMidsectionParameter i q := by
  obtain ⟨s, hs, hsq⟩ := hq
  have h : (B.intrinsicBoundaryGraphMidsectionHomeomorph i).symm q = s := by
    apply (B.intrinsicBoundaryGraphMidsectionHomeomorph i).injective
    rw [(B.intrinsicBoundaryGraphMidsectionHomeomorph i).apply_symm_apply]
    exact Subtype.ext hsq.symm
  change (2 / 3 : ℝ) < ((B.intrinsicBoundaryGraphMidsectionHomeomorph i).symm q).val
  rw [h]
  exact hs

private theorem sidePrefix_mem_startStar (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) (s : unitInterval)
    (hs : (s : ℝ) < 1 / 3) (t : unitInterval) :
    B.intrinsicBoundaryGraphSidePrefix i s t ∈
      B.intrinsicBoundaryGraphVertexStar (B.intrinsicBoundaryGraphSideStart i) := by
  change Quotient.mk B.intrinsicBoundaryIntervalSetoid (i, Icc.convexComb 0 s t) ∈ _
  rw [B.intrinsicBoundaryGraphVertexStar_mem_mk]
  refine Or.inl ⟨?_, rfl⟩
  rw [Icc.coe_convexComb]
  change (1 - (t : ℝ)) * 0 + (t : ℝ) * s < 1 / 3
  have h := mul_le_mul_of_nonneg_right (unitInterval.le_one t) (unitInterval.nonneg s)
  linarith

private theorem sideSuffix_mem_endStar (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) (s : unitInterval)
    (hs : (2 / 3 : ℝ) < s) (t : unitInterval) :
    B.intrinsicBoundaryGraphSideSuffix i s t ∈
      B.intrinsicBoundaryGraphVertexStar (B.intrinsicBoundaryGraphSideEnd i) := by
  change Quotient.mk B.intrinsicBoundaryIntervalSetoid (i, Icc.convexComb s 1 t) ∈ _
  rw [B.intrinsicBoundaryGraphVertexStar_mem_mk]
  refine Or.inr ⟨?_, rfl⟩
  rw [Icc.coe_convexComb]
  change (2 / 3 : ℝ) < (1 - (t : ℝ)) * s + (t : ℝ) * 1
  nlinarith [mul_nonneg (unitInterval.nonneg t) (unitInterval.one_minus_nonneg s)]

private theorem sidePrefix_trans_suffix (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) (s : unitInterval) :
    ((B.intrinsicBoundaryGraphSidePrefix i s).trans
      (B.intrinsicBoundaryGraphSideSuffix i s)).Homotopic (B.intrinsicBoundaryGraphSidePath i) := by
  have h := (show (((B.intrinsicBoundaryGraphSidePath i).subpath 0 s).trans
      ((B.intrinsicBoundaryGraphSidePath i).subpath s 1)).Homotopic
        ((B.intrinsicBoundaryGraphSidePath i).subpath 0 1) from
    ⟨Path.Homotopy.subpathTransSubpath _ _ _ _⟩).pathCast
      (Path.source _).symm (Path.target _).symm
  have hfull : ((B.intrinsicBoundaryGraphSidePath i).subpath 0 1).cast
      (Path.source _).symm (Path.target _).symm = B.intrinsicBoundaryGraphSidePath i := by
    ext t
    simp only [Path.cast_coe, Path.subpath_zero_one]
  have hparts : (((B.intrinsicBoundaryGraphSidePath i).subpath 0 s).trans
      ((B.intrinsicBoundaryGraphSidePath i).subpath s 1)).cast
      (Path.source _).symm (Path.target _).symm =
        (B.intrinsicBoundaryGraphSidePrefix i s).trans (B.intrinsicBoundaryGraphSideSuffix i s) := by
    ext t
    rfl
  simpa only [hparts, hfull] using h

def Internal.SurfaceBoundaryGraphRootedPathsHelpers.midsectionRootedPathOnSide (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) (i : Fin B.intrinsicBoundaryRadialCuts.card)
    (q : B.intrinsicBoundaryGraphEdgeMidsection i) :
    Path (B.intrinsicBoundaryGraphVertexInclusion r) q.val :=
  (B.intrinsicBoundaryTreeConnector r (B.intrinsicBoundaryGraphSideStart i)).trans
    ((B.intrinsicBoundaryGraphSidePrefix i (B.intrinsicBoundaryGraphMidsectionParameter i q)).cast
      rfl (B.intrinsicBoundaryGraphMidsectionParameter_point i q).symm)

/-- **Math.** The alternative middle root path follows the canonical original
physical side from its actual initial vertex to the exact interval parameter. -/
def intrinsicBoundaryGraphMidsectionRootedPath (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) (q : B.intrinsicBoundaryGraphMidsectionUnion) :
    Path (B.intrinsicBoundaryGraphVertexInclusion r) q.val :=
  Internal.SurfaceBoundaryGraphRootedPathsHelpers.midsectionRootedPathOnSide B r (B.intrinsicBoundaryMidsectionEdge q).val
    ⟨q.val, B.intrinsicBoundaryMidsectionEdge_mem q⟩

private theorem midsectionRootedPath_eq_of_mem (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) (q : B.intrinsicBoundaryGraphMidsectionUnion)
    (e : B.IntrinsicBoundaryPhysicalEdge)
    (he : q.val ∈ B.intrinsicBoundaryGraphEdgeMidsection e.val) :
    B.intrinsicBoundaryGraphMidsectionRootedPath r q =
      Internal.SurfaceBoundaryGraphRootedPathsHelpers.midsectionRootedPathOnSide B r e.val ⟨q.val, he⟩ := by
  have h := B.intrinsicBoundaryMidsectionEdge_eq_of_mem q e he
  subst e
  rfl

theorem Internal.SurfaceBoundaryGraphRootedPathsHelpers.outsideStar_midsection (B : DirichletBoundarySegments X o)
    (q : B.IntrinsicBoundaryGraph) (hs : q ∉ B.intrinsicBoundaryGraphStarUnion) :
    q ∈ B.intrinsicBoundaryGraphMidsectionUnion := by
  have hq : q ∈ B.intrinsicBoundaryGraphStarUnion ∪ B.intrinsicBoundaryGraphMidsectionUnion := by
    rw [B.intrinsicBoundaryGraphStarUnion_union_midsectionUnion]
    trivial
  exact hq.resolve_left hs

/-- **Math.** A genuine root-to-point path on the entire actual physical graph.
The star branch uses the contraction; the other branch is the literal side prefix. -/
def intrinsicBoundaryGraphRootedPath (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) (q : B.IntrinsicBoundaryGraph) :
    Path (B.intrinsicBoundaryGraphVertexInclusion r) q := by
  classical
  exact if hs : q ∈ B.intrinsicBoundaryGraphStarUnion then
    B.intrinsicBoundaryGraphStarRootedPath r ⟨q, hs⟩ else
    B.intrinsicBoundaryGraphMidsectionRootedPath r ⟨q, Internal.SurfaceBoundaryGraphRootedPathsHelpers.outsideStar_midsection B q hs⟩

theorem intrinsicBoundaryGraphRootedPath_of_star (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) (q : B.intrinsicBoundaryGraphStarUnion) :
    B.intrinsicBoundaryGraphRootedPath r q.val = B.intrinsicBoundaryGraphStarRootedPath r q := by
  classical
  rw [intrinsicBoundaryGraphRootedPath, dif_pos q.property]

theorem intrinsicBoundaryGraphRootedPath_of_not_star (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) (q : B.intrinsicBoundaryGraphMidsectionUnion)
    (hs : q.val ∉ B.intrinsicBoundaryGraphStarUnion) :
    B.intrinsicBoundaryGraphRootedPath r q.val = B.intrinsicBoundaryGraphMidsectionRootedPath r q := by
  classical
  rw [intrinsicBoundaryGraphRootedPath, dif_neg hs]

/-- **Math.** Transport along any actual star-side path preserves the actual
rooted path class, since that path remains in one genuine contractible star. -/
theorem intrinsicBoundaryGraphRootedPath_star_transport (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) {x y : B.intrinsicBoundaryGraphStarUnion}
    (γ : Path x y) :
    ((B.intrinsicBoundaryGraphRootedPath r x.val).trans
      (γ.map continuous_subtype_val)).Homotopic (B.intrinsicBoundaryGraphRootedPath r y.val) := by
  let v := B.intrinsicBoundaryStarVertex x
  have hx := B.intrinsicBoundaryStarVertex_mem x
  have hγ := B.intrinsicBoundaryGraphStarUnion_path_mem γ hx
  have hy : y.val ∈ B.intrinsicBoundaryGraphVertexStar v := by
    simpa only [Path.target] using hγ 1
  rw [B.intrinsicBoundaryGraphRootedPath_of_star r x,
    B.intrinsicBoundaryGraphRootedPath_of_star r y,
    B.intrinsicBoundaryGraphStarRootedPath_eq_of_mem r x v hx,
    B.intrinsicBoundaryGraphStarRootedPath_eq_of_mem r y v hy]
  have htail := rooted_paths_homotopic_in_contractible (B.intrinsicBoundaryGraphVertexStar v)
    ((B.intrinsicBoundaryGraphStarCenterPath v ⟨x.val, hx⟩).trans
      (γ.map continuous_subtype_val))
    (B.intrinsicBoundaryGraphStarCenterPath v ⟨y.val, hy⟩)
    (rooted_trans_mem _ _ (B.intrinsicBoundaryGraphStarCenterPath_mem v _) hγ)
    (B.intrinsicBoundaryGraphStarCenterPath_mem v _)
  exact (Path.Homotopic.trans_assoc _ _ _).trans ((Path.Homotopic.refl _).hcomp htail)

/-- **Math.** Transport along any actual middle path preserves the literal
canonical-side rooted path. The whole path remains in its actual interval chart. -/
theorem intrinsicBoundaryGraphMidsectionRootedPath_transport
    (B : DirichletBoundarySegments X o) (r : B.IntrinsicBoundaryGraphVertex)
    {x y : B.intrinsicBoundaryGraphMidsectionUnion} (γ : Path x y) :
    ((B.intrinsicBoundaryGraphMidsectionRootedPath r x).trans
      (γ.map continuous_subtype_val)).Homotopic
        (B.intrinsicBoundaryGraphMidsectionRootedPath r y) := by
  let e := B.intrinsicBoundaryMidsectionEdge x
  have hx := B.intrinsicBoundaryMidsectionEdge_mem x
  have hγ := B.intrinsicBoundaryGraphMidsectionUnion_path_mem γ hx
  have hy : y.val ∈ B.intrinsicBoundaryGraphEdgeMidsection e.val := by
    simpa only [Path.target] using hγ 1
  let sx := B.intrinsicBoundaryGraphMidsectionParameter e.val ⟨x.val, hx⟩
  let sy := B.intrinsicBoundaryGraphMidsectionParameter e.val ⟨y.val, hy⟩
  have hs := B.intrinsicBoundaryGraphMidsectionParameter_bounds e.val ⟨x.val, hx⟩
  have ht := B.intrinsicBoundaryGraphMidsectionParameter_bounds e.val ⟨y.val, hy⟩
  have hxs : B.intrinsicBoundaryGraphSidePath e.val sx = x.val :=
    B.intrinsicBoundaryGraphMidsectionParameter_point e.val ⟨x.val, hx⟩
  have hys : B.intrinsicBoundaryGraphSidePath e.val sy = y.val :=
    B.intrinsicBoundaryGraphMidsectionParameter_point e.val ⟨y.val, hy⟩
  let δ : Path x.val y.val :=
    ((B.intrinsicBoundaryGraphSidePath e.val).subpath sx sy).cast hxs.symm hys.symm
  have hδ : ∀ u, δ u ∈ B.intrinsicBoundaryGraphEdgeMidsection e.val := by
    intro u
    change Quotient.mk B.intrinsicBoundaryIntervalSetoid
      (e.val, Icc.convexComb sx sy u) ∈ _
    rw [B.intrinsicBoundaryGraphEdgeMidsection_mem_mk]
    refine ⟨Or.inl rfl, ?_⟩
    have hc := (convex_Ioo (1 / 4 : ℝ) (3 / 4)) hs ht
      (unitInterval.one_minus_nonneg u) (unitInterval.nonneg u) (sub_add_cancel 1 (u : ℝ))
    simpa only [Icc.coe_convexComb, smul_eq_mul, sx, sy, mem_Ioo] using hc
  have hmid := rooted_paths_homotopic_in_contractible
    (B.intrinsicBoundaryGraphEdgeMidsection e.val)
    (γ.map continuous_subtype_val) δ hγ hδ
  have hpref :
      (((B.intrinsicBoundaryGraphSidePrefix e.val sx).cast rfl hxs.symm).trans δ).Homotopic
        ((B.intrinsicBoundaryGraphSidePrefix e.val sy).cast rfl hys.symm) :=
    (show ((B.intrinsicBoundaryGraphSidePath e.val).subpath 0 sx |>.trans
        ((B.intrinsicBoundaryGraphSidePath e.val).subpath sx sy)).Homotopic
          ((B.intrinsicBoundaryGraphSidePath e.val).subpath 0 sy) from
      ⟨Path.Homotopy.subpathTransSubpath _ _ _ _⟩).pathCast
        (Path.source _).symm hys.symm
  rw [midsectionRootedPath_eq_of_mem B r x e hx,
    midsectionRootedPath_eq_of_mem B r y e hy]
  unfold Internal.SurfaceBoundaryGraphRootedPathsHelpers.midsectionRootedPathOnSide
  exact (Path.Homotopic.trans_assoc _ _ _).trans
    ((Path.Homotopic.refl _).hcomp
      (((Path.Homotopic.refl _).hcomp hmid).trans hpref))

/-- **Math.** On the actual initial arm, the middle prefix and genuine
star-based global path have the same endpoint-fixed homotopy class. -/
theorem intrinsicBoundaryGraphMidsectionRootedPath_initial
    (B : DirichletBoundarySegments X o) (r : B.IntrinsicBoundaryGraphVertex)
    (q : B.intrinsicBoundaryGraphMidsectionUnion) (e : B.IntrinsicBoundaryPhysicalEdge)
    (hq : q.val ∈ B.intrinsicBoundaryGraphInitialOverlap e.val) :
    (B.intrinsicBoundaryGraphMidsectionRootedPath r q).Homotopic
      (B.intrinsicBoundaryGraphRootedPath r q.val) := by
  have hm := B.intrinsicBoundaryGraphInitialOverlap_subset_midsection e.val hq
  have hs := B.intrinsicBoundaryGraphInitialOverlap_subset_star e.val hq
  let qS : B.intrinsicBoundaryGraphStarUnion := ⟨q.val, mem_iUnion.mpr ⟨_, hs⟩⟩
  rw [midsectionRootedPath_eq_of_mem B r q e hm,
    B.intrinsicBoundaryGraphRootedPath_of_star r qS,
    B.intrinsicBoundaryGraphStarRootedPath_eq_of_mem r qS
      (B.intrinsicBoundaryGraphSideStart e.val) hs]
  unfold Internal.SurfaceBoundaryGraphRootedPathsHelpers.midsectionRootedPathOnSide
  apply (Path.Homotopic.refl _).hcomp
  apply rooted_paths_homotopic_in_contractible
    (B.intrinsicBoundaryGraphVertexStar (B.intrinsicBoundaryGraphSideStart e.val))
  · exact sidePrefix_mem_startStar B e.val _ (midsectionParameter_initial B e.val _ hq)
  · exact B.intrinsicBoundaryGraphStarCenterPath_mem _ _

/-- **Math.** On the actual terminal arm, the difference of the middle
prefix and genuine global path is the original tree-rooted physical side loop. -/
theorem intrinsicBoundaryGraphMidsectionRootedPath_terminal
    (B : DirichletBoundarySegments X o) (r : B.IntrinsicBoundaryGraphVertex)
    (q : B.intrinsicBoundaryGraphMidsectionUnion) (e : B.IntrinsicBoundaryPhysicalEdge)
    (hq : q.val ∈ B.intrinsicBoundaryGraphTerminalOverlap e.val) :
    (Path.Homotopic.Quotient.mk
      ((B.intrinsicBoundaryGraphMidsectionRootedPath r q).trans
        (B.intrinsicBoundaryGraphRootedPath r q.val).symm) :
      FundamentalGroup B.IntrinsicBoundaryGraph (B.intrinsicBoundaryGraphVertexInclusion r)) =
        B.intrinsicBoundarySideGenerator r e.val := by
  have hm := B.intrinsicBoundaryGraphTerminalOverlap_subset_midsection e.val hq
  have hs := B.intrinsicBoundaryGraphTerminalOverlap_subset_star e.val hq
  let qS : B.intrinsicBoundaryGraphStarUnion := ⟨q.val, mem_iUnion.mpr ⟨_, hs⟩⟩
  let s := B.intrinsicBoundaryGraphMidsectionParameter e.val ⟨q.val, hm⟩
  have hpoint := B.intrinsicBoundaryGraphMidsectionParameter_point e.val ⟨q.val, hm⟩
  let pInit := (B.intrinsicBoundaryGraphSidePrefix e.val s).cast rfl hpoint.symm
  let pTerm := (B.intrinsicBoundaryGraphSideSuffix e.val s).cast hpoint.symm rfl
  have hcenter : (B.intrinsicBoundaryGraphStarCenterPath
      (B.intrinsicBoundaryGraphSideEnd e.val) ⟨q.val, hs⟩).Homotopic pTerm.symm := by
    apply rooted_paths_homotopic_in_contractible
      (B.intrinsicBoundaryGraphVertexStar (B.intrinsicBoundaryGraphSideEnd e.val))
    · exact B.intrinsicBoundaryGraphStarCenterPath_mem _ _
    · intro t
      exact sideSuffix_mem_endStar B e.val s (midsectionParameter_terminal B e.val _ hq) _
  have hroot : (B.intrinsicBoundaryGraphRootedPath r q.val).Homotopic
      ((B.intrinsicBoundaryTreeConnector r (B.intrinsicBoundaryGraphSideEnd e.val)).trans
        pTerm.symm) := by
    rw [B.intrinsicBoundaryGraphRootedPath_of_star r qS,
      B.intrinsicBoundaryGraphStarRootedPath_eq_of_mem r qS
        (B.intrinsicBoundaryGraphSideEnd e.val) hs]
    exact (Path.Homotopic.refl _).hcomp hcenter
  apply Path.Homotopic.Quotient.eq.mpr
  change ((B.intrinsicBoundaryGraphMidsectionRootedPath r q).trans
    (B.intrinsicBoundaryGraphRootedPath r q.val).symm).Homotopic
      (B.intrinsicBoundarySideLoop r e.val)
  rw [midsectionRootedPath_eq_of_mem B r q e hm]
  exact ((Path.Homotopic.refl _).hcomp hroot.symm₂).trans
    (rooted_prefix_suffix _ _ pInit pTerm _ (sidePrefix_trans_suffix B e.val s))

/-- **Math.** The actual rooted middle/global difference has exactly the
physical-side gauge. Initial and terminal arms are not identified on loop edges. -/
theorem intrinsicBoundaryGraphMidsectionRootedPath_gauge
    (B : DirichletBoundarySegments X o) (r : B.IntrinsicBoundaryGraphVertex)
    (q : B.intrinsicBoundaryGraphMidsectionUnion) :
    (Path.Homotopic.Quotient.mk
      ((B.intrinsicBoundaryGraphMidsectionRootedPath r q).trans
        (B.intrinsicBoundaryGraphRootedPath r q.val).symm) :
      FundamentalGroup B.IntrinsicBoundaryGraph (B.intrinsicBoundaryGraphVertexInclusion r)) =
        B.intrinsicBoundaryMidsectionGauge (fun e => B.intrinsicBoundarySideGenerator r e.val) q := by
  classical
  let e := B.intrinsicBoundaryMidsectionEdge q
  have hm := B.intrinsicBoundaryMidsectionEdge_mem q
  by_cases hs : q.val ∈ B.intrinsicBoundaryGraphStarUnion
  · have hhalves : q.val ∈ B.intrinsicBoundaryGraphInitialOverlap e.val ∪
        B.intrinsicBoundaryGraphTerminalOverlap e.val := by
      rw [← B.intrinsicBoundaryGraphStarUnion_inter_midsection_eq_halves e.val]
      exact ⟨hs, hm⟩
    rcases hhalves with hi | ht
    · rw [B.intrinsicBoundaryMidsectionGauge_initial _ q e hi]
      change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk (Path.refl _)
      apply Path.Homotopic.Quotient.eq.mpr
      exact (((B.intrinsicBoundaryGraphMidsectionRootedPath_initial r q e hi).hcomp
        (Path.Homotopic.refl _)).trans (Path.Homotopic.trans_symm _))
    · rw [B.intrinsicBoundaryMidsectionGauge_terminal _ q e ht]
      exact B.intrinsicBoundaryGraphMidsectionRootedPath_terminal r q e ht
  · have ht : q.val ∉ B.intrinsicBoundaryGraphTerminalOverlap e.val := by
      intro h
      exact hs (mem_iUnion.mpr ⟨_, B.intrinsicBoundaryGraphTerminalOverlap_subset_star e.val h⟩)
    rw [intrinsicBoundaryMidsectionGauge, if_neg ht,
      B.intrinsicBoundaryGraphRootedPath_of_not_star r q hs]
    change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk (Path.refl _)
    exact Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.trans_symm _)

/-- **Math.** The global root path at the actual root is nullhomotopic. -/
theorem intrinsicBoundaryGraphRootedPath_root_homotopic (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) :
    (B.intrinsicBoundaryGraphRootedPath r (B.intrinsicBoundaryGraphVertexInclusion r)).Homotopic
      (Path.refl (B.intrinsicBoundaryGraphVertexInclusion r)) := by
  have hr := B.intrinsicBoundaryGraphVertexInclusion_mem_star r
  let q : B.intrinsicBoundaryGraphStarUnion :=
    ⟨B.intrinsicBoundaryGraphVertexInclusion r, mem_iUnion.mpr ⟨r, hr⟩⟩
  change (B.intrinsicBoundaryGraphRootedPath r q.val).Homotopic (Path.refl q.val)
  rw [B.intrinsicBoundaryGraphRootedPath_of_star r q,
    B.intrinsicBoundaryGraphStarRootedPath_eq_of_mem r q r hr,
    B.intrinsicBoundaryTreeConnector_root]
  have hc := rooted_paths_homotopic_in_contractible (B.intrinsicBoundaryGraphVertexStar r)
    (B.intrinsicBoundaryGraphStarCenterPath r ⟨q.val, hr⟩)
    (Path.refl q.val) (B.intrinsicBoundaryGraphStarCenterPath_mem r _)
    (fun _ => hr)
  exact ((Path.Homotopic.refl _).hcomp hc).trans (Path.Homotopic.refl_trans _)

end DirichletBoundarySegments

end

end SystolicGrowth
