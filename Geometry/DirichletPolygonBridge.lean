module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.DirichletVertexFan
public import Vendored.RiemannDynamics.Teichmuller.PolygonGeometry

@[expose] public section

/-!
# Identifying the native polygon with the imported Dirichlet polygon

These maps keep the original domain, full sides and cyclic vertices. Side
surjectivity uses the finite actual frontier cover, not a bounding-radius
assumption on an arbitrary boundary package.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane

namespace SystolicGrowth

namespace ClosedHyperbolicSurface

/-- The actual free deck action has the weaker projective freeness required
by the imported polygon geometry. -/
theorem deck_fixing_point_acts_trivially {g : ℕ} (X : ClosedHyperbolicSurface g) :
    ∀ γ : X.deckGroup, (∃ z : ℍ, γ • z = z) → ∀ w : ℍ, γ • w = w := by
  rintro γ ⟨z, hz⟩ w
  rw [X.free γ z hz, one_smul]

/-- A fixed basepoint orbit is uniformly dense, using compactness of the
actual Dirichlet domain and its proved nearest-tile covering. -/
theorem exists_dirichlet_orbit_density_bound {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) :
    ∃ R : ℝ, ∀ z : ℍ, Metric.infDist z (MulAction.orbit X.deckGroup o) ≤ R := by
  obtain ⟨K, hK, hcover⟩ := X.exists_compact_covering
  have hcompact := X.isCompact_dirichletDomain_of_compact_covering o K hK hcover
  obtain ⟨R, hbound⟩ := (Metric.isBounded_iff_subset_closedBall o).mp hcompact.isBounded
  refine ⟨R, ?_⟩
  intro z
  obtain ⟨γ, hγ⟩ := Vendored.RiemannDynamics.exists_smul_mem_dirichletDomain
    (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ) o z
  calc
    Metric.infDist z (MulAction.orbit X.deckGroup o) ≤ dist z (γ⁻¹ • o) :=
      Metric.infDist_le_dist_of_mem (MulAction.mem_orbit_iff.mpr ⟨γ⁻¹, rfl⟩)
    _ = dist (γ • z) o := by
      rw [← dist_smul γ z (γ⁻¹ • o), smul_inv_smul]
    _ ≤ R := Metric.mem_closedBall.mp (hbound hγ)

/-- Freeness identifies deck elements from the image of one point. -/
theorem deck_smul_injective {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) :
    Function.Injective (fun γ : X.deckGroup => γ • o) := by
  intro γ δ h
  change γ • o = δ • o at h
  have hfix : (γ⁻¹ * δ) • o = o := by
    rw [mul_smul, ← h, inv_smul_smul]
  exact inv_mul_eq_one.mp (X.free _ o hfix)

end ClosedHyperbolicSurface

namespace DirichletBoundarySegments

/-- A native cyclic full edge is exactly the imported full Dirichlet side
section with its original deck label. -/
theorem intrinsicCyclicClosedEdge_eq_dirichletSideSet
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge i) =
      Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o
        (B.intrinsicCyclicEdge i).1.1.1 :=
  B.intrinsicClosedEdgeImage_eq_fullSection _

/-- Every actual native cyclic edge is a nondegenerate imported polygon
side; both endpoints are the original cyclic vertices. -/
theorem intrinsicCyclicClosedEdge_mem_polygonSides
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge i) ∈
      Vendored.RiemannDynamics.polygonSides X.deckGroup o := by
  refine ⟨(B.intrinsicCyclicEdge i).1.1.1, ⟨?_, ?_⟩,
    B.intrinsicCyclicClosedEdge_eq_dirichletSideSet i⟩
  · intro h
    exact (Finset.ne_of_mem_erase (B.intrinsicCyclicEdge i).1.1.2.1)
      (X.free _ o h)
  · rw [← B.intrinsicCyclicClosedEdge_eq_dirichletSideSet i,
      B.intrinsicCyclicEdge_closedImage_eq_geodSeg]
    exact ⟨B.intrinsicCyclicVertex i, Vendored.RiemannDynamics.left_mem_geodSeg _ _,
      B.intrinsicCyclicVertex (finRotate _ i), Vendored.RiemannDynamics.right_mem_geodSeg _ _,
      B.intrinsicCyclicVertex_next_ne i⟩

/-- The native edge label satisfies the imported side-element predicate. -/
theorem intrinsicCyclicEdge_isSideElement
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    Vendored.RiemannDynamics.IsSideElement X.deckGroup o
      (B.intrinsicCyclicEdge i).1.1.1 := by
  constructor
  · intro h
    exact (Finset.ne_of_mem_erase (B.intrinsicCyclicEdge i).1.1.2.1) (X.free _ o h)
  · rw [← B.intrinsicCyclicClosedEdge_eq_dirichletSideSet i,
      B.intrinsicCyclicEdge_closedImage_eq_geodSeg]
    exact ⟨B.intrinsicCyclicVertex i, Vendored.RiemannDynamics.left_mem_geodSeg _ _,
      B.intrinsicCyclicVertex (finRotate _ i), Vendored.RiemannDynamics.right_mem_geodSeg _ _,
      B.intrinsicCyclicVertex_next_ne i⟩

/-- Every imported nondegenerate side occurs among the native full sides.
Otherwise it meets each member of the finite frontier cover in at most one
point, contradicting its nondegenerate geodesic segment. -/
theorem exists_intrinsicCyclicClosedEdge_eq_polygonSide
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) {s : Set ℍ}
    (hs : s ∈ Vendored.RiemannDynamics.polygonSides X.deckGroup o) :
    ∃ i : Fin B.intrinsicBoundaryRadialCuts.card,
      B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge i) = s := by
  classical
  obtain ⟨R, hdense⟩ := X.exists_dirichlet_orbit_density_bound o
  obtain ⟨a, b, hab, hsseg⟩ := Vendored.RiemannDynamics.exists_geodSeg_of_polygonSide
    (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
    X.deck_fixing_point_acts_trivially (X.basepoint_mem_interior_dirichletDomain o) hdense hs
  obtain ⟨γ, hγ, rfl⟩ := hs
  by_contra hmissing
  have hinter : ∀ i : Fin B.intrinsicBoundaryRadialCuts.card,
      (Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o γ ∩
        B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge i)).Finite := by
    intro i
    have hmove : (B.intrinsicCyclicEdge i).1.1.1 • o ≠ o := by
      intro h
      exact (Finset.ne_of_mem_erase (B.intrinsicCyclicEdge i).1.1.2.1) (X.free _ o h)
    have hdistinct : γ • o ≠ (B.intrinsicCyclicEdge i).1.1.1 • o := by
      intro h
      have heq := X.deck_smul_injective o h
      apply hmissing
      refine ⟨i, ?_⟩
      rw [B.intrinsicCyclicClosedEdge_eq_dirichletSideSet, ← heq]
    apply Set.Subsingleton.finite
    intro z hz w hw
    apply hyperbolic_bisectors_inter_subsingleton (Ne.symm hγ.1) (Ne.symm hmove) hdistinct
    · rw [B.intrinsicCyclicClosedEdge_eq_dirichletSideSet] at hz
      exact ⟨hz.1.2, hz.2.2⟩
    · rw [B.intrinsicCyclicClosedEdge_eq_dirichletSideSet] at hw
      exact ⟨hw.1.2, hw.2.2⟩
  have hsfinite : (Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o γ).Finite := by
    apply (Set.finite_iUnion hinter).subset
    intro z hz
    have hzfront := X.mem_frontier_dirichletDomain_of_mem_bisector o γ
      (fun h => hγ.1 (by rw [h, one_smul])) hz.1 hz.2
    rw [← B.iUnion_intrinsicCyclicClosedEdge_eq_frontier] at hzfront
    obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hzfront
    exact Set.mem_iUnion.mpr ⟨i, hz, hzi⟩
  have himage : ((fun t : ℝ => Vendored.RiemannDynamics.geodInterp a b t) ''
      Set.Icc 0 1).Finite := by
    apply hsfinite.subset
    rintro z ⟨t, ht, rfl⟩
    rw [hsseg]
    exact Vendored.RiemannDynamics.geodInterp_mem_geodSeg a b ht
  have hIcc : (Set.Icc (0 : ℝ) 1).Finite :=
    (Set.finite_image_iff (geodInterp_injective_of_ne a b hab).injOn).mp himage
  exact (Set.Icc_infinite (by norm_num : (0 : ℝ) < 1)) hIcc

/-- The original cyclic side list enumerates exactly the imported polygon
side set, with no removal or replacement of native sides. -/
theorem range_intrinsicCyclicClosedEdge_eq_polygonSides
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    Set.range (fun i : Fin B.intrinsicBoundaryRadialCuts.card =>
      B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge i)) =
        Vendored.RiemannDynamics.polygonSides X.deckGroup o := by
  ext s
  constructor
  · rintro ⟨i, rfl⟩
    exact B.intrinsicCyclicClosedEdge_mem_polygonSides i
  · exact B.exists_intrinsicCyclicClosedEdge_eq_polygonSide

/-- Distinct native cyclic positions determine distinct imported full sides. -/
theorem intrinsicCyclicClosedEdge_injective
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    Function.Injective (fun i : Fin B.intrinsicBoundaryRadialCuts.card =>
      B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge i)) := by
  intro i j h
  apply B.intrinsicCyclicEdge_label_injective
  apply X.deck_smul_injective o
  apply Vendored.RiemannDynamics.smul_basepoint_eq_of_sideSet_eq
    (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
    X.deck_fixing_point_acts_trivially
  · exact B.intrinsicCyclicEdge_isSideElement i
  · exact B.intrinsicCyclicEdge_isSideElement j
  · simpa only [B.intrinsicCyclicClosedEdge_eq_dirichletSideSet] using h

/-- Counting the imported full sides gives the original number of cyclic
vertices, before any side-pair quotient is taken. -/
theorem ncard_polygonSides_eq_intrinsicBoundaryRadialCuts_card
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    (Vendored.RiemannDynamics.polygonSides X.deckGroup o).ncard =
      B.intrinsicBoundaryRadialCuts.card := by
  rw [← B.range_intrinsicCyclicClosedEdge_eq_polygonSides]
  rw [Set.ncard_range_of_injective B.intrinsicCyclicClosedEdge_injective, Nat.card_fin]

/-- The imported unordered side-pair count is half the number of original
cyclic sides. This uses the proved fixed-point-free side pairing on the same
full sections, without changing the native boundary enumeration. -/
theorem polygonSideCount_eq_intrinsicBoundarySideCount_half
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    2 * Vendored.RiemannDynamics.polygonSideCount X.deckGroup o =
      B.intrinsicBoundaryRadialCuts.card := by
  obtain ⟨R, hdense⟩ := X.exists_dirichlet_orbit_density_bound o
  exact (Vendored.RiemannDynamics.ncard_polygonSides
      (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
      X.deck_fixing_point_acts_trivially (X.basepoint_mem_interior_dirichletDomain o)
      hdense).symm.trans B.ncard_polygonSides_eq_intrinsicBoundaryRadialCuts_card

/-- Every original cyclic vertex is an endpoint of a genuine imported side. -/
theorem intrinsicCyclicVertex_mem_polygonVertices
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicCyclicVertex i ∈ Vendored.RiemannDynamics.polygonVertices X.deckGroup o := by
  obtain ⟨R, hdense⟩ := X.exists_dirichlet_orbit_density_bound o
  apply Vendored.RiemannDynamics.mem_polygonVertices_of_isSegEndpoint
    (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
    X.deck_fixing_point_acts_trivially (X.basepoint_mem_interior_dirichletDomain o) hdense
    (B.intrinsicCyclicClosedEdge_mem_polygonSides i)
  rw [B.intrinsicCyclicEdge_closedImage_eq_geodSeg]
  exact (Vendored.RiemannDynamics.isSegEndpoint_geodSeg_iff
    (B.intrinsicCyclicVertex_next_ne i)).mpr (Or.inl rfl)

/-- Every imported three-tile vertex is one of the original cyclic vertices. -/
theorem exists_intrinsicCyclicVertex_eq_polygonVertex
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) {v : ℍ}
    (hv : v ∈ Vendored.RiemannDynamics.polygonVertices X.deckGroup o) :
    ∃ i : Fin B.intrinsicBoundaryRadialCuts.card, B.intrinsicCyclicVertex i = v := by
  classical
  obtain ⟨R, hdense⟩ := X.exists_dirichlet_orbit_density_bound o
  have hfin : (Vendored.RiemannDynamics.tileCenters X.deckGroup o v).Finite :=
    (Vendored.RiemannDynamics.finite_contactSet
      (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ) o v).image _
  have h3 : 2 < (Vendored.RiemannDynamics.tileCenters X.deckGroup o v).ncard := hv.2
  rw [Set.two_lt_ncard hfin] at h3
  obtain ⟨c₁, hc₁, c₂, hc₂, c₃, hc₃, h12, _, _⟩ := h3
  have hmoving : ∃ c ∈ Vendored.RiemannDynamics.tileCenters X.deckGroup o v, c ≠ o := by
    by_cases h1 : c₁ = o
    · exact ⟨c₂, hc₂, fun h2 => h12 (h1.trans h2.symm)⟩
    · exact ⟨c₁, hc₁, h1⟩
  obtain ⟨_, ⟨γ, hγcontact, rfl⟩, hγmove⟩ := hmoving
  change γ • o ≠ o at hγmove
  have hzdist : dist v o = dist v (γ • o) := by
    rw [Vendored.RiemannDynamics.dist_basepoint_eq_infDist hv.1]
    exact hγcontact.symm
  have hfront := X.mem_frontier_dirichletDomain_of_mem_bisector o γ
    (fun h => hγmove (by rw [h, one_smul])) hv.1 hzdist
  rw [← B.iUnion_intrinsicCyclicClosedEdge_eq_frontier] at hfront
  obtain ⟨i, hvi⟩ := Set.mem_iUnion.mp hfront
  have hend := Vendored.RiemannDynamics.isSegEndpoint_of_vertex
    (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
    X.deck_fixing_point_acts_trivially (X.basepoint_mem_interior_dirichletDomain o) hdense hv
    (B.intrinsicCyclicClosedEdge_mem_polygonSides i) hvi
  rw [B.intrinsicCyclicEdge_closedImage_eq_geodSeg] at hend
  rcases (Vendored.RiemannDynamics.isSegEndpoint_geodSeg_iff
      (B.intrinsicCyclicVertex_next_ne i)).mp hend with h | h
  · exact ⟨i, h.symm⟩
  · exact ⟨finRotate _ i, h.symm⟩

/-- The imported vertex set is exactly the native cyclic list on the same
upper-half-plane carrier. -/
theorem range_intrinsicCyclicVertex_eq_polygonVertices
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    Set.range B.intrinsicCyclicVertex =
      Vendored.RiemannDynamics.polygonVertices X.deckGroup o := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact B.intrinsicCyclicVertex_mem_polygonVertices i
  · exact B.exists_intrinsicCyclicVertex_eq_polygonVertex

/-- The native previous/next corner angle satisfies the imported interior
angle predicate, using its actual two adjacent full sides. -/
theorem intrinsicCyclicVertex_prev_next_isInteriorAngleAt
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    Vendored.RiemannDynamics.IsInteriorAngleAt X.deckGroup o (B.intrinsicCyclicVertex i)
      (Vendored.RiemannDynamics.sectorAngle (B.intrinsicCyclicVertex i)
        (B.intrinsicCyclicVertex ((finRotate B.intrinsicBoundaryRadialCuts.card).symm i))
        (B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card i))) := by
  let p := (finRotate B.intrinsicBoundaryRadialCuts.card).symm i
  have hpi : finRotate B.intrinsicBoundaryRadialCuts.card p = i :=
    (finRotate B.intrinsicBoundaryRadialCuts.card).apply_symm_apply i
  have hpv : B.intrinsicCyclicVertex p ≠ B.intrinsicCyclicVertex i := by
    simpa only [hpi] using B.intrinsicCyclicVertex_next_ne p
  have hpi' : p ≠ i := fun h => hpv (congrArg B.intrinsicCyclicVertex h)
  refine ⟨B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge p),
    B.intrinsicCyclicClosedEdge_mem_polygonSides p,
    B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge i),
    B.intrinsicCyclicClosedEdge_mem_polygonSides i,
    fun h => hpi' (B.intrinsicCyclicClosedEdge_injective h), ?_, ?_,
    B.intrinsicCyclicVertex p, ?_, B.intrinsicCyclicVertex (finRotate _ i), ?_,
    hpv, Ne.symm (B.intrinsicCyclicVertex_next_ne i), rfl⟩
  · rw [B.intrinsicCyclicEdge_closedImage_eq_geodSeg, hpi]
    exact (Vendored.RiemannDynamics.isSegEndpoint_geodSeg_iff hpv).mpr (Or.inr rfl)
  · rw [B.intrinsicCyclicEdge_closedImage_eq_geodSeg]
    exact (Vendored.RiemannDynamics.isSegEndpoint_geodSeg_iff
      (B.intrinsicCyclicVertex_next_ne i)).mpr (Or.inl rfl)
  · rw [B.intrinsicCyclicEdge_closedImage_eq_geodSeg, hpi]
    exact Vendored.RiemannDynamics.left_mem_geodSeg _ _
  · rw [B.intrinsicCyclicEdge_closedImage_eq_geodSeg]
    exact Vendored.RiemannDynamics.right_mem_geodSeg _ _

end DirichletBoundarySegments

#print axioms DirichletBoundarySegments.range_intrinsicCyclicClosedEdge_eq_polygonSides
#print axioms DirichletBoundarySegments.ncard_polygonSides_eq_intrinsicBoundaryRadialCuts_card
#print axioms DirichletBoundarySegments.polygonSideCount_eq_intrinsicBoundarySideCount_half
#print axioms DirichletBoundarySegments.range_intrinsicCyclicVertex_eq_polygonVertices
#print axioms DirichletBoundarySegments.intrinsicCyclicVertex_prev_next_isInteriorAngleAt

end SystolicGrowth
