module

public import Geometry.SurfaceBoundaryGraphComponentPaths
public import Geometry.TwoOpenCoverGroupoidDescent
public import Mathlib.CategoryTheory.SingleObj

@[expose] public section

/-!
# Reading physical edge labels by the actual graph cover

The edge-side functor is a difference functor whose gauge changes between
the two genuine overlap arms. Its gauge need not be continuous: it labels
objects of a fundamental groupoid, not points of a topological target.
Agreement with the constant star-side functor will follow from arbitrary
overlap paths staying in one actual half-arm.
-/

open Set CategoryTheory UpperHalfPlane
open scoped Pointwise UpperHalfPlane Classical

namespace SystolicGrowth.DirichletBoundarySegments

noncomputable section

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

theorem Internal.SurfaceBoundaryGraphWordFunctorHelpers.canonicalMidsection_exists (B : DirichletBoundarySegments X o)
    (q : B.intrinsicBoundaryGraphMidsectionUnion) :
    ∃ e : B.IntrinsicBoundaryPhysicalEdge,
      q.1 ∈ B.intrinsicBoundaryGraphEdgeMidsection e.1 := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp q.2
  refine ⟨B.intrinsicBoundaryPhysicalEdge i, ?_⟩
  by_cases h : i < B.intrinsicCyclicPairing i
  · simpa only [intrinsicBoundaryPhysicalEdge, dif_pos h] using hi
  · simpa only [intrinsicBoundaryPhysicalEdge, dif_neg h,
      B.intrinsicBoundaryGraphEdgeMidsection_pair] using hi

/-- **Math.** The unique genuine physical edge containing an edge-side object. -/
def intrinsicBoundaryMidsectionEdge (B : DirichletBoundarySegments X o)
    (q : B.intrinsicBoundaryGraphMidsectionUnion) : B.IntrinsicBoundaryPhysicalEdge :=
  Classical.choose (Internal.SurfaceBoundaryGraphWordFunctorHelpers.canonicalMidsection_exists B q)

theorem intrinsicBoundaryMidsectionEdge_mem (B : DirichletBoundarySegments X o)
    (q : B.intrinsicBoundaryGraphMidsectionUnion) :
    q.1 ∈ B.intrinsicBoundaryGraphEdgeMidsection (B.intrinsicBoundaryMidsectionEdge q).1 :=
  Classical.choose_spec (Internal.SurfaceBoundaryGraphWordFunctorHelpers.canonicalMidsection_exists B q)

/-- **Math.** The choice retains the actual physical edge, not merely its endpoints. -/
theorem intrinsicBoundaryMidsectionEdge_eq_of_mem (B : DirichletBoundarySegments X o)
    (q : B.intrinsicBoundaryGraphMidsectionUnion) (e : B.IntrinsicBoundaryPhysicalEdge)
    (he : q.1 ∈ B.intrinsicBoundaryGraphEdgeMidsection e.1) :
    B.intrinsicBoundaryMidsectionEdge q = e := by
  exact B.intrinsicBoundaryGraphPhysicalMidsection_mem_unique
    (B.intrinsicBoundaryMidsectionEdge_mem q) he

variable {H : Type} [Group H]

/-- **Math.** The gauge is the assigned edge label on its terminal overlap
and one elsewhere. It is a categorical object label, not a continuous map. -/
def intrinsicBoundaryMidsectionGauge (B : DirichletBoundarySegments X o)
    (c : B.IntrinsicBoundaryPhysicalEdge → H)
    (q : B.intrinsicBoundaryGraphMidsectionUnion) : H :=
  if q.1 ∈ B.intrinsicBoundaryGraphTerminalOverlap (B.intrinsicBoundaryMidsectionEdge q).1
    then c (B.intrinsicBoundaryMidsectionEdge q) else 1

theorem intrinsicBoundaryMidsectionGauge_initial (B : DirichletBoundarySegments X o)
    (c : B.IntrinsicBoundaryPhysicalEdge → H)
    (q : B.intrinsicBoundaryGraphMidsectionUnion) (e : B.IntrinsicBoundaryPhysicalEdge)
    (he : q.1 ∈ B.intrinsicBoundaryGraphInitialOverlap e.1) :
    B.intrinsicBoundaryMidsectionGauge c q = 1 := by
  have hedge := B.intrinsicBoundaryMidsectionEdge_eq_of_mem q e
    (B.intrinsicBoundaryGraphInitialOverlap_subset_midsection e.1 he)
  rw [intrinsicBoundaryMidsectionGauge, hedge, if_neg]
  exact fun ht => Set.disjoint_left.mp
    (B.intrinsicBoundaryGraphOverlap_halves_disjoint e.1) he ht

theorem intrinsicBoundaryMidsectionGauge_terminal (B : DirichletBoundarySegments X o)
    (c : B.IntrinsicBoundaryPhysicalEdge → H)
    (q : B.intrinsicBoundaryGraphMidsectionUnion) (e : B.IntrinsicBoundaryPhysicalEdge)
    (he : q.1 ∈ B.intrinsicBoundaryGraphTerminalOverlap e.1) :
    B.intrinsicBoundaryMidsectionGauge c q = c e := by
  have hedge := B.intrinsicBoundaryMidsectionEdge_eq_of_mem q e
    (B.intrinsicBoundaryGraphTerminalOverlap_subset_midsection e.1 he)
  rw [intrinsicBoundaryMidsectionGauge, hedge, if_pos he]

/-- **Math.** Every actual star-side morphism has label one. -/
def intrinsicBoundaryGraphStarWordFunctor (B : DirichletBoundarySegments X o) :
    FundamentalGroupoid B.intrinsicBoundaryGraphStarUnion ⥤ SingleObj H :=
  SingleObj.differenceFunctor (fun _ => (1 : H))

/-- **Math.** The genuine edge-side difference functor reads the two endpoint gauges. -/
def intrinsicBoundaryGraphMidsectionWordFunctor (B : DirichletBoundarySegments X o)
    (c : B.IntrinsicBoundaryPhysicalEdge → H) :
    FundamentalGroupoid B.intrinsicBoundaryGraphMidsectionUnion ⥤ SingleObj H :=
  SingleObj.differenceFunctor (fun q => B.intrinsicBoundaryMidsectionGauge c q.as)

@[simp]
theorem intrinsicBoundaryGraphStarWordFunctor_map (B : DirichletBoundarySegments X o)
    {a b : FundamentalGroupoid B.intrinsicBoundaryGraphStarUnion} (f : a ⟶ b) :
    (B.intrinsicBoundaryGraphStarWordFunctor (H := H)).map f = (1 : H) := by
  simp [intrinsicBoundaryGraphStarWordFunctor, SingleObj.differenceFunctor]

@[simp]
theorem intrinsicBoundaryGraphMidsectionWordFunctor_map (B : DirichletBoundarySegments X o)
    (c : B.IntrinsicBoundaryPhysicalEdge → H)
    {a b : FundamentalGroupoid B.intrinsicBoundaryGraphMidsectionUnion} (f : a ⟶ b) :
    (B.intrinsicBoundaryGraphMidsectionWordFunctor c).map f =
      B.intrinsicBoundaryMidsectionGauge c b.as *
        (B.intrinsicBoundaryMidsectionGauge c a.as)⁻¹ := rfl

/-- **Math.** A genuine overlap morphism has equal endpoint gauges: an
arbitrary representing path stays in one of its two actual half-arms. -/
theorem intrinsicBoundaryMidsectionGauge_overlap (B : DirichletBoundarySegments X o)
    (c : B.IntrinsicBoundaryPhysicalEdge → H)
    {a b : FundamentalGroupoid
      ↥(B.intrinsicBoundaryGraphStarUnion ∩ B.intrinsicBoundaryGraphMidsectionUnion)}
    (f : a ⟶ b) :
    B.intrinsicBoundaryMidsectionGauge c
        (twoOpenCoverOverlapRight _ _ a.as) =
      B.intrinsicBoundaryMidsectionGauge c
        (twoOpenCoverOverlapRight _ _ b.as) := by
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective f
  let e := B.intrinsicBoundaryMidsectionEdge (twoOpenCoverOverlapRight _ _ a.as)
  have ha : a.as.1 ∈ B.intrinsicBoundaryGraphStarUnion ∩
      B.intrinsicBoundaryGraphEdgeMidsection e.1 :=
    ⟨a.as.2.1, B.intrinsicBoundaryMidsectionEdge_mem _⟩
  rw [B.intrinsicBoundaryGraphStarUnion_inter_midsection_eq_halves e.1] at ha
  rcases ha with ha | ha
  · have hb : b.as.1 ∈ B.intrinsicBoundaryGraphInitialOverlap e.1 := by
      simpa only [p.target] using B.intrinsicBoundaryGraphOverlap_path_mem_initial p ha 1
    rw [B.intrinsicBoundaryMidsectionGauge_initial c _ e ha,
      B.intrinsicBoundaryMidsectionGauge_initial c _ e hb]
  · have hb : b.as.1 ∈ B.intrinsicBoundaryGraphTerminalOverlap e.1 := by
      simpa only [p.target] using B.intrinsicBoundaryGraphOverlap_path_mem_terminal p ha 1
    rw [B.intrinsicBoundaryMidsectionGauge_terminal c _ e ha,
      B.intrinsicBoundaryMidsectionGauge_terminal c _ e hb]

/-- **Math.** The actual star and middle functors agree strictly on the
whole disconnected overlap, not just on specially chosen edge paths. -/
theorem intrinsicBoundaryGraphWordFunctors_compatible (B : DirichletBoundarySegments X o)
    (c : B.IntrinsicBoundaryPhysicalEdge → H) :
    FundamentalGroupoid.map (twoOpenCoverOverlapLeft
        B.intrinsicBoundaryGraphStarUnion B.intrinsicBoundaryGraphMidsectionUnion) ⋙
        B.intrinsicBoundaryGraphStarWordFunctor =
      FundamentalGroupoid.map (twoOpenCoverOverlapRight
        B.intrinsicBoundaryGraphStarUnion B.intrinsicBoundaryGraphMidsectionUnion) ⋙
        B.intrinsicBoundaryGraphMidsectionWordFunctor c := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro a b f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  simp only [Functor.comp_map, intrinsicBoundaryGraphStarWordFunctor_map,
    intrinsicBoundaryGraphMidsectionWordFunctor_map]
  change (1 : H) = B.intrinsicBoundaryMidsectionGauge c
      (twoOpenCoverOverlapRight _ _ b.as) *
        (B.intrinsicBoundaryMidsectionGauge c (twoOpenCoverOverlapRight _ _ a.as))⁻¹
  rw [B.intrinsicBoundaryMidsectionGauge_overlap c f]
  exact (mul_inv_cancel _).symm

/-- **Math.** Genuine word reading on the original physical graph, descended
from its actual open cover with no presentation or generation premise. -/
def intrinsicBoundaryGraphWordFunctor (B : DirichletBoundarySegments X o)
    (c : B.IntrinsicBoundaryPhysicalEdge → H) :
    FundamentalGroupoid B.IntrinsicBoundaryGraph ⥤ SingleObj H :=
  twoOpenCoverGroupoidDesc B.intrinsicBoundaryGraphStarUnion_isOpen
    B.intrinsicBoundaryGraphMidsectionUnion_isOpen
    B.intrinsicBoundaryGraphStarUnion_union_midsectionUnion
    B.intrinsicBoundaryGraphStarWordFunctor (B.intrinsicBoundaryGraphMidsectionWordFunctor c)
    (B.intrinsicBoundaryGraphWordFunctors_compatible c)

theorem intrinsicBoundaryGraphWordFunctor_comp_star (B : DirichletBoundarySegments X o)
    (c : B.IntrinsicBoundaryPhysicalEdge → H) :
    FundamentalGroupoid.map (twoOpenCoverInclusion B.intrinsicBoundaryGraphStarUnion) ⋙
      B.intrinsicBoundaryGraphWordFunctor c = B.intrinsicBoundaryGraphStarWordFunctor :=
  twoOpenCoverGroupoidDesc_comp_left _ _ _ _ _ _

theorem intrinsicBoundaryGraphWordFunctor_comp_midsection (B : DirichletBoundarySegments X o)
    (c : B.IntrinsicBoundaryPhysicalEdge → H) :
    FundamentalGroupoid.map (twoOpenCoverInclusion B.intrinsicBoundaryGraphMidsectionUnion) ⋙
      B.intrinsicBoundaryGraphWordFunctor c = B.intrinsicBoundaryGraphMidsectionWordFunctor c :=
  twoOpenCoverGroupoidDesc_comp_right _ _ _ _ _ _

/-- **Math.** Every genuine star-side path has word one. -/
theorem intrinsicBoundaryGraphWordFunctor_map_star (B : DirichletBoundarySegments X o)
    (c : B.IntrinsicBoundaryPhysicalEdge → H)
    {a b : B.intrinsicBoundaryGraphStarUnion} (p : Path a b) :
    (B.intrinsicBoundaryGraphWordFunctor c).map
      (Path.Homotopic.Quotient.mk (p.map continuous_subtype_val) :
        FundamentalGroupoid.mk a.1 ⟶ FundamentalGroupoid.mk b.1) = (1 : H) := by
  change (B.intrinsicBoundaryGraphWordFunctor c).map
    ((FundamentalGroupoid.map (twoOpenCoverInclusion _)).map
      (Path.Homotopic.Quotient.mk p)) = _
  exact (twoOpenCoverGroupoidDesc_map_left _ _ _ _ _ _ _).trans
    (B.intrinsicBoundaryGraphStarWordFunctor_map _)

/-- **Math.** Every genuine middle-side path reads precisely its two endpoint gauges. -/
theorem intrinsicBoundaryGraphWordFunctor_map_midsection (B : DirichletBoundarySegments X o)
    (c : B.IntrinsicBoundaryPhysicalEdge → H)
    {a b : B.intrinsicBoundaryGraphMidsectionUnion} (p : Path a b) :
    (B.intrinsicBoundaryGraphWordFunctor c).map
      (Path.Homotopic.Quotient.mk (p.map continuous_subtype_val) :
        FundamentalGroupoid.mk a.1 ⟶ FundamentalGroupoid.mk b.1) =
        B.intrinsicBoundaryMidsectionGauge c b *
          (B.intrinsicBoundaryMidsectionGauge c a)⁻¹ := by
  change (B.intrinsicBoundaryGraphWordFunctor c).map
    ((FundamentalGroupoid.map (twoOpenCoverInclusion _)).map
      (Path.Homotopic.Quotient.mk p)) = _
  exact twoOpenCoverGroupoidDesc_map_right _ _ _ _ _ _ _

/-- **Math.** The actual word homomorphism uses the original chosen vertex basepoint. -/
def intrinsicBoundaryGraphWordHom (B : DirichletBoundarySegments X o)
    (c : B.IntrinsicBoundaryPhysicalEdge → H) (r : B.IntrinsicBoundaryGraphVertex) :
    FundamentalGroup B.IntrinsicBoundaryGraph (B.intrinsicBoundaryGraphVertexInclusion r) →* H :=
  fundamentalGroupoidFunctorHom (B.intrinsicBoundaryGraphWordFunctor c)
    (B.intrinsicBoundaryGraphVertexInclusion r)

@[simp]
theorem intrinsicBoundaryGraphWordHom_apply (B : DirichletBoundarySegments X o)
    (c : B.IntrinsicBoundaryPhysicalEdge → H) (r : B.IntrinsicBoundaryGraphVertex)
    (f : FundamentalGroup B.IntrinsicBoundaryGraph (B.intrinsicBoundaryGraphVertexInclusion r)) :
    B.intrinsicBoundaryGraphWordHom c r f = (B.intrinsicBoundaryGraphWordFunctor c).map f := rfl

variable {K : Type} [Group K]

/-- **Math.** Changing coefficient groups carries the genuine endpoint gauge along. -/
theorem intrinsicBoundaryMidsectionGauge_hom (B : DirichletBoundarySegments X o)
    (c : B.IntrinsicBoundaryPhysicalEdge → H) (f : H →* K)
    (q : B.intrinsicBoundaryGraphMidsectionUnion) :
    f (B.intrinsicBoundaryMidsectionGauge c q) =
      B.intrinsicBoundaryMidsectionGauge (fun e => f (c e)) q := by
  unfold intrinsicBoundaryMidsectionGauge
  split_ifs
  · rfl
  · exact f.map_one

private theorem starWordFunctor_hom (B : DirichletBoundarySegments X o) (f : H →* K) :
    B.intrinsicBoundaryGraphStarWordFunctor ⋙ f.toFunctor =
      B.intrinsicBoundaryGraphStarWordFunctor (H := K) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro a b p
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Functor.comp_map,
    intrinsicBoundaryGraphStarWordFunctor_map]
  exact f.map_one

private theorem midsectionWordFunctor_hom (B : DirichletBoundarySegments X o)
    (c : B.IntrinsicBoundaryPhysicalEdge → H) (f : H →* K) :
    B.intrinsicBoundaryGraphMidsectionWordFunctor c ⋙ f.toFunctor =
      B.intrinsicBoundaryGraphMidsectionWordFunctor (fun e => f (c e)) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro a b p
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Functor.comp_map,
    intrinsicBoundaryGraphMidsectionWordFunctor_map]
  change f (B.intrinsicBoundaryMidsectionGauge c b.as *
    (B.intrinsicBoundaryMidsectionGauge c a.as)⁻¹) = _
  rw [map_mul, map_inv, B.intrinsicBoundaryMidsectionGauge_hom,
    B.intrinsicBoundaryMidsectionGauge_hom]

/-- **Math.** Coefficient naturality is proved by uniqueness of the actual
groupoid descendant, so it holds on every ambient path class. -/
theorem intrinsicBoundaryGraphWordFunctor_hom (B : DirichletBoundarySegments X o)
    (c : B.IntrinsicBoundaryPhysicalEdge → H) (f : H →* K) :
    B.intrinsicBoundaryGraphWordFunctor c ⋙ f.toFunctor =
      B.intrinsicBoundaryGraphWordFunctor (fun e => f (c e)) := by
  apply twoOpenCoverGroupoid_ext B.intrinsicBoundaryGraphStarUnion_isOpen
    B.intrinsicBoundaryGraphMidsectionUnion_isOpen
    B.intrinsicBoundaryGraphStarUnion_union_midsectionUnion
  · rw [← Functor.assoc, B.intrinsicBoundaryGraphWordFunctor_comp_star,
      B.intrinsicBoundaryGraphWordFunctor_comp_star, starWordFunctor_hom]
  · rw [← Functor.assoc, B.intrinsicBoundaryGraphWordFunctor_comp_midsection,
      B.intrinsicBoundaryGraphWordFunctor_comp_midsection, midsectionWordFunctor_hom]

/-- **Math.** The same naturality retains the literal original vertex basepoint. -/
theorem intrinsicBoundaryGraphWordHom_hom (B : DirichletBoundarySegments X o)
    (c : B.IntrinsicBoundaryPhysicalEdge → H) (f : H →* K)
    (r : B.IntrinsicBoundaryGraphVertex) :
    f.comp (B.intrinsicBoundaryGraphWordHom c r) =
      B.intrinsicBoundaryGraphWordHom (fun e => f (c e)) r := by
  ext p
  exact congrArg (fun F : FundamentalGroupoid B.IntrinsicBoundaryGraph ⥤ SingleObj K =>
    (F.map p : K)) (B.intrinsicBoundaryGraphWordFunctor_hom c f)

end

end SystolicGrowth.DirichletBoundarySegments
