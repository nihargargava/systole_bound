module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.DirichletPairingSubdivision
public import Geometry.DirichletClosedEdgeIncidence

@[expose] public section

/-!
# The finite intrinsically subdivided Dirichlet edge family

The existing finite index `DirichletOpenEdgeIndex B B.intrinsicCornerCuts`
indexes the actual open geodesic pieces of all nondegenerate sections. Their
images are nonempty and pairwise disjoint. Inverse deck action determines a
unique partner edge and hence a fixed-point-free involutive equivalence.
The finite intrinsic exceptional set includes all cut images and the earlier
candidate exceptional points; its complement is exactly covered by the open
edges. No cyclic boundary order or polygon area formula is assumed.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane

namespace SystolicGrowth
namespace DirichletBoundarySegments

/-- The interior parameter of an intrinsic gap belongs to the unit interval. -/
theorem intrinsicCornerGap_interior_mem_Icc
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B)
    (e : DirichletParameterGap (B.intrinsicCornerCuts i))
    {u : ℝ} (hu : u ∈ Set.Ioo (e.left : ℝ) (e.right : ℝ)) :
    u ∈ Set.Icc (0 : ℝ) 1 := by
  have hl := B.intrinsicCornerCuts_subset_Icc i e.left.2
  have hr := B.intrinsicCornerCuts_subset_Icc i e.right.2
  exact ⟨le_trans hl.1 hu.1.le, le_trans hu.2.le hr.2⟩

/-- Each actual intrinsically subdivided open edge has nonempty image. -/
theorem intrinsicOpenEdgeImage_nonempty
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts) :
    (B.openEdgeImage B.intrinsicCornerCuts s).Nonempty := by
  exact (Set.nonempty_Ioo.mpr s.2.left_lt_right).image _

/-- The finite intrinsic subdivision retains disjoint open images. Different
sections cannot meet away from the old exceptional set; on one section this
is injectivity of interpolation and disjointness of consecutive gaps. -/
theorem intrinsicOpenEdgeImage_pairwise_disjoint
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    Pairwise (fun s t : DirichletOpenEdgeIndex B B.intrinsicCornerCuts =>
      Disjoint (B.openEdgeImage B.intrinsicCornerCuts s)
        (B.openEdgeImage B.intrinsicCornerCuts t)) := by
  intro s t hst
  rcases s with ⟨i, ei⟩
  rcases t with ⟨j, ej⟩
  by_cases hij : i = j
  · subst j
    have heij : ei ≠ ej := by
      intro h
      apply hst
      cases h
      rfl
    exact B.gap_images_disjoint_of_ne i (B.intrinsicCornerCuts i) ei ej heij
  · apply Set.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨u, hu, huz⟩ := hz
    obtain ⟨v, hv, hvz⟩ := hz'
    change Vendored.RiemannDynamics.geodInterp
      (B.endpoints i.1).1 (B.endpoints i.1).2 u = z at huz
    change Vendored.RiemannDynamics.geodInterp
      (B.endpoints j.1).1 (B.endpoints j.1).2 v = z at hvz
    have hregular := B.intrinsicCornerGap_interior_not_exceptional i ei hu
    rw [huz] at hregular
    have hzi : z ∈ Vendored.RiemannDynamics.geodSeg
        (B.endpoints i.1).1 (B.endpoints i.1).2 := by
      rw [← huz]
      exact Vendored.RiemannDynamics.geodInterp_mem_geodSeg _ _
        (B.intrinsicCornerGap_interior_mem_Icc i ei hu)
    have hzj : z ∈ Vendored.RiemannDynamics.geodSeg
        (B.endpoints j.1).1 (B.endpoints j.1).2 := by
      rw [← hvz]
      exact Vendored.RiemannDynamics.geodInterp_mem_geodSeg _ _
        (B.intrinsicCornerGap_interior_mem_Icc j ej hv)
    have hij' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    exact hregular (Or.inr (Or.inr ⟨i.1, j.1, hij', hzi, hzj⟩))

/-- Equality of actual intrinsic open images determines the edge index. The
same-section case rests on injective geodesic interpolation, not on any
invariance of a chosen candidate exceptional set. -/
theorem intrinsicOpenEdgeImage_injective
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    Function.Injective (B.openEdgeImage B.intrinsicCornerCuts) := by
  intro s t h
  by_contra hst
  obtain ⟨z, hz⟩ := B.intrinsicOpenEdgeImage_nonempty s
  have hzt : z ∈ B.openEdgeImage B.intrinsicCornerCuts t := by rwa [← h]
  exact Set.disjoint_left.mp (B.intrinsicOpenEdgeImage_pairwise_disjoint hst) hz hzt

/-- The actual inverse-deck partner of an intrinsically subdivided edge.
Existence follows from the transported genuine-corner cuts; uniqueness is
proved by equality of the nonempty disjoint open images. -/
noncomputable def inverseIntrinsicOpenEdge
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts) :
    DirichletOpenEdgeIndex B B.intrinsicCornerCuts :=
  ⟨B.inverseNondegenerateIndex s.1,
    Classical.choose (B.exists_inverse_intrinsicCornerGap_image s.1 s.2)⟩

/-- The partner is on the actual inverse-labeled nondegenerate section. -/
@[simp] theorem inverseIntrinsicOpenEdge_section
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts) :
    (B.inverseIntrinsicOpenEdge s).1 = B.inverseNondegenerateIndex s.1 := rfl

/-- The deck label of the partner edge is exactly the inverse deck label. -/
@[simp] theorem inverseIntrinsicOpenEdge_label
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts) :
    (B.inverseIntrinsicOpenEdge s).1.1.1 = s.1.1.1⁻¹ := rfl

/-- Exact transport of one open edge image by its inverse deck label. -/
theorem image_inv_smul_intrinsicOpenEdge
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts) :
    (fun z : ℍ => s.1.1.1⁻¹ • z) '' B.openEdgeImage B.intrinsicCornerCuts s =
      B.openEdgeImage B.intrinsicCornerCuts (B.inverseIntrinsicOpenEdge s) := by
  exact (Classical.choose_spec
    (B.exists_inverse_intrinsicCornerGap_image s.1 s.2)).1

/-- Applying the inverse-edge pairing twice returns the same edge, since the
two deck actions cancel and the actual open-edge image determines its index. -/
@[simp] theorem inverseIntrinsicOpenEdge_inverseIntrinsicOpenEdge
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts) :
    B.inverseIntrinsicOpenEdge (B.inverseIntrinsicOpenEdge s) = s := by
  apply B.intrinsicOpenEdgeImage_injective
  calc
    B.openEdgeImage B.intrinsicCornerCuts
        (B.inverseIntrinsicOpenEdge (B.inverseIntrinsicOpenEdge s)) =
      (fun z : ℍ => (B.inverseIntrinsicOpenEdge s).1.1.1⁻¹ • z) ''
        B.openEdgeImage B.intrinsicCornerCuts (B.inverseIntrinsicOpenEdge s) :=
      (B.image_inv_smul_intrinsicOpenEdge (B.inverseIntrinsicOpenEdge s)).symm
    _ = (fun z : ℍ => s.1.1.1 • z) ''
        ((fun z : ℍ => s.1.1.1⁻¹ • z) '' B.openEdgeImage B.intrinsicCornerCuts s) := by
      rw [B.inverseIntrinsicOpenEdge_label, inv_inv,
        ← B.image_inv_smul_intrinsicOpenEdge s]
    _ = B.openEdgeImage B.intrinsicCornerCuts s := by
      ext z
      constructor
      · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
        simpa only [smul_inv_smul] using hv
      · intro hz
        exact ⟨_, ⟨z, hz, rfl⟩, smul_inv_smul _ _⟩

/-- No edge is its own partner: their underlying deck section labels differ. -/
theorem inverseIntrinsicOpenEdge_ne_self
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts) :
    B.inverseIntrinsicOpenEdge s ≠ s := by
  intro h
  exact B.inverseNondegenerateIndex_ne_self s.1 (congrArg Sigma.fst h)

/-- The finite actual edge family carries a fixed-point-free inverse pairing
equivalence. This is not a cyclic polygon structure. -/
noncomputable def intrinsicOpenEdgePairing
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    DirichletOpenEdgeIndex B B.intrinsicCornerCuts ≃
      DirichletOpenEdgeIndex B B.intrinsicCornerCuts where
  toFun := B.inverseIntrinsicOpenEdge
  invFun := B.inverseIntrinsicOpenEdge
  left_inv := B.inverseIntrinsicOpenEdge_inverseIntrinsicOpenEdge
  right_inv := B.inverseIntrinsicOpenEdge_inverseIntrinsicOpenEdge

/-- The inverse equivalence has no fixed edge. -/
theorem intrinsicOpenEdgePairing_ne_self
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts) :
    B.intrinsicOpenEdgePairing s ≠ s :=
  B.inverseIntrinsicOpenEdge_ne_self s

/-- The same actual pairing carries closed edges exactly to closed edges. -/
theorem image_inv_smul_intrinsicClosedEdge
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts) :
    (fun z : ℍ => s.1.1.1⁻¹ • z) '' B.closedEdgeImage B.intrinsicCornerCuts s =
      B.closedEdgeImage B.intrinsicCornerCuts (B.inverseIntrinsicOpenEdge s) := by
  rw [← B.closure_openEdgeImage_eq_closedEdgeImage B.intrinsicCornerCuts s,
    ← B.closure_openEdgeImage_eq_closedEdgeImage B.intrinsicCornerCuts
      (B.inverseIntrinsicOpenEdge s)]
  calc
    _ = closure ((fun z : ℍ => s.1.1.1⁻¹ • z) ''
        B.openEdgeImage B.intrinsicCornerCuts s) :=
      (Homeomorph.smul s.1.1.1⁻¹).image_closure _
    _ = _ := congrArg closure (B.image_inv_smul_intrinsicOpenEdge s)

/-- Intrinsic cut images together with the old candidate exceptional points.
This enlarged finite set, rather than the old set alone, is the exact
complement of the intrinsically subdivided open-edge cover. -/
def intrinsicExceptionalPoints
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) : Set ℍ :=
  B.exceptionalPoints ∪ ⋃ i : NondegenerateIndex B,
    (fun t : ℝ => Vendored.RiemannDynamics.geodInterp
      (B.endpoints i.1).1 (B.endpoints i.1).2 t) ''
        (↑(B.intrinsicCornerCuts i) : Set ℝ)

/-- The intrinsic boundary exception set is finite. -/
theorem intrinsicExceptionalPoints_finite
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    B.intrinsicExceptionalPoints.Finite := by
  apply B.exceptionalPoints_finite.union
  apply Set.finite_iUnion
  intro i
  exact (B.intrinsicCornerCuts i).finite_toSet.image _

/-- Every intrinsic exception is a point of the actual Dirichlet frontier. -/
theorem intrinsicExceptionalPoints_subset_frontier
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    B.intrinsicExceptionalPoints ⊆
      frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) := by
  intro z hz
  rcases hz with hzold | hzcut
  · exact B.exceptionalPoints_subset_frontier hzold
  · obtain ⟨i, t, ht, rfl⟩ := Set.mem_iUnion.mp hzcut
    exact B.segment_subset_frontier i.1
      (Vendored.RiemannDynamics.geodInterp_mem_geodSeg _ _
        (B.intrinsicCornerCuts_subset_Icc i ht))

/-- Both endpoints of an intrinsic closed edge are intrinsic exceptions on
the actual frontier. No exact characterization by the old cut set is used. -/
theorem intrinsicClosedEdgeEndpoints_exceptional_frontier
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts) :
    (B.closedEdgeEndpoints B.intrinsicCornerCuts s).1 ∈ B.intrinsicExceptionalPoints ∧
      (B.closedEdgeEndpoints B.intrinsicCornerCuts s).2 ∈ B.intrinsicExceptionalPoints ∧
      (B.closedEdgeEndpoints B.intrinsicCornerCuts s).1 ∈
        frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) ∧
      (B.closedEdgeEndpoints B.intrinsicCornerCuts s).2 ∈
        frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) := by
  have hleft : (B.closedEdgeEndpoints B.intrinsicCornerCuts s).1 ∈
      B.intrinsicExceptionalPoints :=
    Or.inr (Set.mem_iUnion.mpr ⟨s.1, s.2.left.1, s.2.left.2, rfl⟩)
  have hright : (B.closedEdgeEndpoints B.intrinsicCornerCuts s).2 ∈
      B.intrinsicExceptionalPoints :=
    Or.inr (Set.mem_iUnion.mpr ⟨s.1, s.2.right.1, s.2.right.2, rfl⟩)
  exact ⟨hleft, hright, B.intrinsicExceptionalPoints_subset_frontier hleft,
    B.intrinsicExceptionalPoints_subset_frontier hright⟩

/-- All closed-edge endpoints lie in the finite intrinsic exception set. -/
theorem intrinsicClosedEdgeEndpointSet_subset_exceptional
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts) :
    B.closedEdgeEndpointSet B.intrinsicCornerCuts s ⊆ B.intrinsicExceptionalPoints := by
  intro z hz
  have hends := B.intrinsicClosedEdgeEndpoints_exceptional_frontier s
  rcases (by simpa [closedEdgeEndpointSet] using hz :
      z = (B.closedEdgeEndpoints B.intrinsicCornerCuts s).1 ∨
        z = (B.closedEdgeEndpoints B.intrinsicCornerCuts s).2) with rfl | rfl
  · exact hends.1
  · exact hends.2.1

/-- Intrinsic open edges avoid all intrinsic cut images, including cuts on
other sections, and therefore lie in the enlarged regular frontier. -/
theorem intrinsicOpenEdgeImage_subset_regular_frontier
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts) :
    B.openEdgeImage B.intrinsicCornerCuts s ⊆
      frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) \
        B.intrinsicExceptionalPoints := by
  intro z hz
  obtain ⟨u, hu, huz⟩ := hz
  change Vendored.RiemannDynamics.geodInterp
    (B.endpoints s.1.1).1 (B.endpoints s.1.1).2 u = z at huz
  have hzi : z ∈ Vendored.RiemannDynamics.geodSeg
      (B.endpoints s.1.1).1 (B.endpoints s.1.1).2 := by
    rw [← huz]
    exact Vendored.RiemannDynamics.geodInterp_mem_geodSeg _ _
      (B.intrinsicCornerGap_interior_mem_Icc s.1 s.2 hu)
  have hregular : z ∉ B.exceptionalPoints := by
    rw [← huz]
    exact B.intrinsicCornerGap_interior_not_exceptional s.1 s.2 hu
  refine ⟨B.segment_subset_frontier s.1.1 hzi, ?_⟩
  rintro (hzold | hzcut)
  · exact hregular hzold
  · obtain ⟨j, v, hv, hvz⟩ := Set.mem_iUnion.mp hzcut
    by_cases hij : s.1 = j
    · subst j
      have huv : u = v := geodInterp_injective_of_ne _ _ s.1.2
        (huz.trans hvz.symm)
      have hucut : u ∈ B.intrinsicCornerCuts s.1 := huv ▸ hv
      rcases s.2.adjacent u hucut with hleft | hright
      · exact (not_le_of_gt hu.1) hleft
      · exact (not_le_of_gt hu.2) hright
    · have hzj : z ∈ Vendored.RiemannDynamics.geodSeg
          (B.endpoints j.1).1 (B.endpoints j.1).2 := by
        rw [← hvz]
        exact Vendored.RiemannDynamics.geodInterp_mem_geodSeg _ _
          (B.intrinsicCornerCuts_subset_Icc j hv)
      have hij' : s.1.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      exact hregular (Or.inr (Or.inr ⟨s.1.1, j.1, hij', hzi, hzj⟩))

/-- Every frontier point outside the finite intrinsic exception set lies on
an actual intrinsic edge. Extra genuine-corner cuts are retained here. -/
theorem exists_intrinsicOpenEdgeImage_of_mem_regular_frontier
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o z : ℍ}
    (B : DirichletBoundarySegments X o)
    (hz : z ∈ frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) \
      B.intrinsicExceptionalPoints) :
    ∃ s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts,
      z ∈ B.openEdgeImage B.intrinsicCornerCuts s := by
  have hzold : z ∉ B.exceptionalPoints := fun h => hz.2 (Or.inl h)
  obtain ⟨i, hzi, _⟩ :=
    B.existsUnique_nondegenerate_section_of_not_exceptional hz.1 hzold
  rw [Vendored.RiemannDynamics.geodSeg_eq_image_geodInterp] at hzi
  obtain ⟨t, ht, htz⟩ := hzi
  have hnot : t ∉ B.intrinsicCornerCuts i := by
    intro htcut
    exact hz.2 (Or.inr (Set.mem_iUnion.mpr ⟨i, t, htcut, htz⟩))
  have hzero : (0 : ℝ) ∈ B.intrinsicCornerCuts i :=
    (B.mem_intrinsicCornerCuts_iff i 0).mpr (Or.inl rfl)
  have hone : (1 : ℝ) ∈ B.intrinsicCornerCuts i :=
    (B.mem_intrinsicCornerCuts_iff i 1).mpr (Or.inr (Or.inl rfl))
  have hbound : ∀ c ∈ B.intrinsicCornerCuts i, c ∈ Set.Icc (0 : ℝ) 1 := by
    intro c hc
    exact B.intrinsicCornerCuts_subset_Icc i hc
  rw [icc_eq_cuts_union_gaps (B.intrinsicCornerCuts i) hzero hone hbound] at ht
  obtain ⟨e, hte⟩ := Set.mem_iUnion.mp (ht.resolve_left hnot)
  exact ⟨⟨i, e⟩, t, hte, htz⟩

/-- The finite, pairwise-disjoint intrinsic edge family covers exactly the
Dirichlet frontier outside its finite intrinsic exceptional set. -/
theorem iUnion_intrinsicOpenEdgeImage_eq_regular_frontier
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    (⋃ s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts,
        B.openEdgeImage B.intrinsicCornerCuts s) =
      frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) \
        B.intrinsicExceptionalPoints := by
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨s, hzs⟩ := Set.mem_iUnion.mp hz
    exact B.intrinsicOpenEdgeImage_subset_regular_frontier s hzs
  · intro z hz
    exact Set.mem_iUnion.mpr
      (B.exists_intrinsicOpenEdgeImage_of_mem_regular_frontier hz)

/-- Distinct closed intrinsic edges can meet only at endpoints of both. This
does not assert a degree-two incidence graph or a global cyclic order. -/
theorem intrinsicClosedEdgeImage_inter_subset_endpointSets
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    {s t : DirichletOpenEdgeIndex B B.intrinsicCornerCuts} (hst : s ≠ t) :
    B.closedEdgeImage B.intrinsicCornerCuts s ∩ B.closedEdgeImage B.intrinsicCornerCuts t ⊆
      B.closedEdgeEndpointSet B.intrinsicCornerCuts s ∩
        B.closedEdgeEndpointSet B.intrinsicCornerCuts t := by
  intro z hz
  have hs := hz.1
  have ht := hz.2
  rw [B.closedEdgeImage_eq_open_union_endpoints] at hs ht
  have hse : z ∈ B.closedEdgeEndpointSet B.intrinsicCornerCuts s := by
    rcases hs with hso | hse
    · rcases ht with hto | hte
      · exact (Set.disjoint_left.mp (B.intrinsicOpenEdgeImage_pairwise_disjoint hst)
          hso hto).elim
      · have hregular := B.intrinsicOpenEdgeImage_subset_regular_frontier s hso
        exact (hregular.2
          (B.intrinsicClosedEdgeEndpointSet_subset_exceptional t hte)).elim
    · exact hse
  have hte : z ∈ B.closedEdgeEndpointSet B.intrinsicCornerCuts t := by
    rcases ht with hto | hte
    · have hregular := B.intrinsicOpenEdgeImage_subset_regular_frontier t hto
      exact (hregular.2
        (B.intrinsicClosedEdgeEndpointSet_subset_exceptional s hse)).elim
    · exact hte
  exact ⟨hse, hte⟩

#print axioms intrinsicOpenEdgeImage_pairwise_disjoint
#print axioms intrinsicOpenEdgeImage_injective
#print axioms image_inv_smul_intrinsicOpenEdge
#print axioms inverseIntrinsicOpenEdge_inverseIntrinsicOpenEdge
#print axioms inverseIntrinsicOpenEdge_ne_self
#print axioms intrinsicOpenEdgePairing
#print axioms image_inv_smul_intrinsicClosedEdge
#print axioms intrinsicExceptionalPoints_finite
#print axioms intrinsicClosedEdgeEndpoints_exceptional_frontier
#print axioms iUnion_intrinsicOpenEdgeImage_eq_regular_frontier
#print axioms intrinsicClosedEdgeImage_inter_subset_endpointSets

end DirichletBoundarySegments
end SystolicGrowth
