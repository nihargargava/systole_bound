module

public import Geometry.DirichletCyclicOrientation
public import Geometry.SurfaceOrbitMetric
public import Geometry.DirichletPuncturedSpine
public import Mathlib.Topology.Maps.Strict.Basic

@[expose] public section

/-! Physical finite side-interval coordinates on the actual Dirichlet boundary spine. -/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane

namespace SystolicGrowth.DirichletBoundarySegments

noncomputable section

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

/-- One literal unit interval for every actual cyclic side. -/
abbrev intrinsicBoundaryIntervalCarrier (B : DirichletBoundarySegments X o) :=
  Fin B.intrinsicBoundaryRadialCuts.card × unitInterval

/-- The physical point of an actual oriented side at its unit-interval parameter. -/
def intrinsicBoundaryIntervalPoint (B : DirichletBoundarySegments X o)
    (a : B.intrinsicBoundaryIntervalCarrier) : ℍ :=
  Vendored.RiemannDynamics.geodInterp (B.intrinsicCyclicVertex a.1)
    (B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card a.1)) a.2

theorem intrinsicBoundaryIntervalPoint_mem_closedEdge (B : DirichletBoundarySegments X o)
    (a : B.intrinsicBoundaryIntervalCarrier) :
    B.intrinsicBoundaryIntervalPoint a ∈
      B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge a.1) := by
  rw [B.intrinsicCyclicEdge_closedImage_eq_geodSeg]
  exact Vendored.RiemannDynamics.geodInterp_mem_geodSeg _ _ a.2.2

theorem intrinsicBoundaryIntervalPoint_mem_frontier (B : DirichletBoundarySegments X o)
    (a : B.intrinsicBoundaryIntervalCarrier) :
    B.intrinsicBoundaryIntervalPoint a ∈
      frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) := by
  rw [← B.iUnion_intrinsicCyclicClosedEdge_eq_frontier]
  exact mem_iUnion.mpr ⟨a.1, B.intrinsicBoundaryIntervalPoint_mem_closedEdge a⟩

theorem continuous_intrinsicBoundaryIntervalPoint (B : DirichletBoundarySegments X o) :
    Continuous B.intrinsicBoundaryIntervalPoint := by
  apply continuous_prod_of_discrete_left.2
  intro i
  change Continuous (fun t : unitInterval ↦ Vendored.RiemannDynamics.geodInterp
    (B.intrinsicCyclicVertex i)
      (B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card i)) t)
  exact Vendored.RiemannDynamics.continuous_geodInterp.comp
    (continuous_const.prodMk (continuous_const.prodMk continuous_subtype_val))

/-- Every original frontier point is represented by an actual finite side interval. -/
theorem range_intrinsicBoundaryIntervalPoint (B : DirichletBoundarySegments X o) :
    range B.intrinsicBoundaryIntervalPoint =
      frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) := by
  apply Subset.antisymm
  · rintro z ⟨a, rfl⟩
    exact B.intrinsicBoundaryIntervalPoint_mem_frontier a
  · intro z hz
    rw [← B.iUnion_intrinsicCyclicClosedEdge_eq_frontier] at hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    rw [B.intrinsicCyclicEdge_closedImage_eq_geodSeg,
      Vendored.RiemannDynamics.geodSeg_eq_image_geodInterp] at hi
    obtain ⟨t, ht, rfl⟩ := hi
    exact ⟨(i, ⟨t, ht⟩), rfl⟩

private theorem intervalPoint_notMem_endpoints (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) (t : unitInterval)
    (ht : (t : ℝ) ∈ Ioo (0 : ℝ) 1) :
    B.intrinsicBoundaryIntervalPoint (i, t) ∉
      B.closedEdgeEndpointSet B.intrinsicCornerCuts (B.intrinsicCyclicEdge i) := by
  have h0 : B.intrinsicBoundaryIntervalPoint (i, t) ≠ B.intrinsicCyclicVertex i := by
    intro hz
    have heq := geodInterp_injective_of_ne _ _ (B.intrinsicCyclicVertex_next_ne i)
      (hz.trans (Vendored.RiemannDynamics.geodInterp_zero _ _).symm)
    exact (ne_of_gt ht.1) heq
  have h1 : B.intrinsicBoundaryIntervalPoint (i, t) ≠
      B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card i) := by
    intro hz
    have heq := geodInterp_injective_of_ne _ _ (B.intrinsicCyclicVertex_next_ne i)
      (hz.trans (Vendored.RiemannDynamics.geodInterp_one _ _).symm)
    exact (ne_of_lt ht.2) heq
  rcases B.intrinsicCyclicEdge_endpoints_eq_or_swap i with h | h
  · simpa only [closedEdgeEndpointSet, h, mem_insert_iff, mem_singleton_iff,
      not_or] using And.intro h0 h1
  · simpa only [closedEdgeEndpointSet, h, mem_insert_iff, mem_singleton_iff,
      not_or] using And.intro h1 h0

private theorem intervalPoint_mem_openEdge (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) (t : unitInterval)
    (ht : (t : ℝ) ∈ Ioo (0 : ℝ) 1) :
    B.intrinsicBoundaryIntervalPoint (i, t) ∈
      B.openEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge i) := by
  have hclosed := B.intrinsicBoundaryIntervalPoint_mem_closedEdge (i, t)
  rw [B.closedEdgeImage_eq_open_union_endpoints] at hclosed
  exact hclosed.resolve_right (intervalPoint_notMem_endpoints B i t ht)

private theorem intervalPoint_eq_iff_of_interior (B : DirichletBoundarySegments X o)
    (i j : Fin B.intrinsicBoundaryRadialCuts.card) (t u : unitInterval)
    (ht : (t : ℝ) ∈ Ioo (0 : ℝ) 1)
    (heq : B.intrinsicBoundaryIntervalPoint (i, t) =
      B.intrinsicBoundaryIntervalPoint (j, u)) : i = j ∧ t = u := by
  have hij : i = j := by
    by_contra hij
    have hends := B.intrinsicClosedEdgeImage_inter_subset_endpointSets
      (fun h ↦ hij (B.intrinsicCyclicEdge_injective h))
      ⟨B.intrinsicBoundaryIntervalPoint_mem_closedEdge (i, t),
        heq.symm ▸ B.intrinsicBoundaryIntervalPoint_mem_closedEdge (j, u)⟩
    exact intervalPoint_notMem_endpoints B i t ht hends.1
  subst j
  refine ⟨rfl, Subtype.ext ?_⟩
  exact geodInterp_injective_of_ne _ _ (B.intrinsicCyclicVertex_next_ne i) heq

private theorem orbit_of_openEdge_eq_one_or_inverse
    (B : DirichletBoundarySegments X o)
    (s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts) {z : ℍ}
    (hz : z ∈ B.openEdgeImage B.intrinsicCornerCuts s) (γ : X.deckGroup)
    (hγz : γ • z ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) :
    γ = 1 ∨ γ = s.1.1.1⁻¹ := by
  by_cases hγ : γ = 1
  · exact Or.inl hγ
  right
  obtain ⟨u, hu, rfl⟩ := hz
  let z := Vendored.RiemannDynamics.geodInterp (B.endpoints s.1.1).1
    (B.endpoints s.1.1).2 u
  have hzseg := Vendored.RiemannDynamics.geodInterp_mem_geodSeg
    (B.endpoints s.1.1).1 (B.endpoints s.1.1).2
    (B.intrinsicCornerGap_interior_mem_Icc s.1 s.2 hu)
  have hzD : z ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o := by
    rw [← B.section_eq_segment s.1.1] at hzseg
    exact hzseg.1
  have hzside : dist z o = dist z (s.1.1.1 • o) := by
    rw [← B.section_eq_segment s.1.1] at hzseg
    exact hzseg.2
  have hzγ : dist z o = dist z (γ⁻¹ • o) := by
    apply le_antisymm (hzD γ⁻¹)
    have h := hγz γ
    have heq : dist (γ • z) o = dist z (γ⁻¹ • o) := by
      rw [← dist_smul γ z (γ⁻¹ • o), smul_inv_smul]
    rw [heq, dist_smul] at h
    exact h
  have hinv : γ⁻¹ = s.1.1.1 := by
    by_contra hinv
    have hcorner : z ∈ X.dirichletSectionCorners o s.1.1.1 :=
      ⟨hzD, hzside, γ⁻¹, inv_ne_one.mpr hγ, hinv, hzγ⟩
    have hcut : u ∈ B.intrinsicCornerCuts s.1 :=
      (B.mem_intrinsicCornerCuts_iff s.1 u).2
        (Or.inr (Or.inr ⟨B.intrinsicCornerGap_interior_mem_Icc s.1 s.2 hu, hcorner⟩))
    rcases s.2.adjacent u hcut with hle | hge
    · exact (not_le_of_gt hu.1) hle
    · exact (not_le_of_gt hu.2) hge
  exact inv_injective (by simpa using hinv)

/-- The original side involution, with precisely the reversed unit parameter. -/
def intrinsicBoundaryIntervalPair (B : DirichletBoundarySegments X o)
    (a : B.intrinsicBoundaryIntervalCarrier) : B.intrinsicBoundaryIntervalCarrier :=
  (B.intrinsicCyclicPairing a.1, unitInterval.symm a.2)

theorem intrinsicBoundaryIntervalPair_involutive (B : DirichletBoundarySegments X o) :
    Function.Involutive B.intrinsicBoundaryIntervalPair := by
  intro a
  exact Prod.ext (B.intrinsicCyclicPairing_involutive a.1) (unitInterval.symm_symm a.2)

/-- The physical pairing is the actual inverse deck transformation on every side point. -/
theorem intrinsicBoundaryIntervalPair_point (B : DirichletBoundarySegments X o)
    (a : B.intrinsicBoundaryIntervalCarrier) :
    B.intrinsicBoundaryIntervalPoint (B.intrinsicBoundaryIntervalPair a) =
      (B.intrinsicCyclicEdge a.1).1.1.1⁻¹ • B.intrinsicBoundaryIntervalPoint a :=
  (B.inverse_smul_intrinsicCyclicGeodInterp_eq_reverse a.1 a.2.2).symm

private theorem interval_orbit_eq_or_pair_of_interior (B : DirichletBoundarySegments X o)
    (a b : B.intrinsicBoundaryIntervalCarrier) (ha : (a.2 : ℝ) ∈ Ioo (0 : ℝ) 1)
    (γ : X.deckGroup) (hγ : γ • B.intrinsicBoundaryIntervalPoint a =
      B.intrinsicBoundaryIntervalPoint b) :
    b = a ∨ b = B.intrinsicBoundaryIntervalPair a := by
  have hbD : B.intrinsicBoundaryIntervalPoint b ∈
      Vendored.RiemannDynamics.dirichletDomain X.deckGroup o :=
    (Vendored.RiemannDynamics.isClosed_dirichletDomain X.deckGroup o).frontier_subset
      (B.intrinsicBoundaryIntervalPoint_mem_frontier b)
  rcases orbit_of_openEdge_eq_one_or_inverse B (B.intrinsicCyclicEdge a.1)
      (intervalPoint_mem_openEdge B a.1 a.2 ha) γ (hγ.symm ▸ hbD) with h | h
  · have hp : B.intrinsicBoundaryIntervalPoint (a.1, a.2) =
        B.intrinsicBoundaryIntervalPoint (b.1, b.2) := by simpa only [h, one_smul] using hγ
    have heq := intervalPoint_eq_iff_of_interior B a.1 b.1 a.2 b.2 ha hp
    exact Or.inl (Prod.ext heq.1.symm heq.2.symm)
  · have hp : B.intrinsicBoundaryIntervalPoint (B.intrinsicBoundaryIntervalPair a) =
        B.intrinsicBoundaryIntervalPoint b := by
      rw [B.intrinsicBoundaryIntervalPair_point]
      exact h ▸ hγ
    have hpair : ((unitInterval.symm a.2 : unitInterval) : ℝ) ∈ Ioo (0 : ℝ) 1 := by
      rw [unitInterval.coe_symm_eq]
      constructor <;> linarith [ha.1, ha.2]
    have heq := intervalPoint_eq_iff_of_interior B (B.intrinsicCyclicPairing a.1)
      b.1 (unitInterval.symm a.2) b.2 hpair hp
    exact Or.inr (Prod.ext heq.1.symm heq.2.symm)

/-- Endpoint incidences are retained as literal zero/one parameters. -/
def IsIntrinsicBoundaryIntervalEndpoint (B : DirichletBoundarySegments X o)
    (a : B.intrinsicBoundaryIntervalCarrier) : Prop := a.2 = 0 ∨ a.2 = 1

private theorem interval_interior_of_not_endpoint (B : DirichletBoundarySegments X o)
    (a : B.intrinsicBoundaryIntervalCarrier) (ha : ¬B.IsIntrinsicBoundaryIntervalEndpoint a) :
    (a.2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by
  have h0 : (a.2 : ℝ) ≠ 0 := fun h ↦ ha (Or.inl (Subtype.ext h))
  have h1 : (a.2 : ℝ) ≠ 1 := fun h ↦ ha (Or.inr (Subtype.ext h))
  exact ⟨lt_of_le_of_ne a.2.2.1 h0.symm, lt_of_le_of_ne a.2.2.2 h1⟩

private theorem interval_pair_endpoint_iff (B : DirichletBoundarySegments X o)
    (a : B.intrinsicBoundaryIntervalCarrier) :
    B.IsIntrinsicBoundaryIntervalEndpoint (B.intrinsicBoundaryIntervalPair a) ↔
      B.IsIntrinsicBoundaryIntervalEndpoint a := by
  simp only [IsIntrinsicBoundaryIntervalEndpoint, intrinsicBoundaryIntervalPair,
    unitInterval.symm_eq_zero, unitInterval.symm_eq_one, or_comm]

/-- Exactly the physical interval identifications: identical points, original reversed side
pairing, or actual orbit-equivalent endpoint vertices. -/
def intrinsicBoundaryIntervalRel (B : DirichletBoundarySegments X o)
    (a b : B.intrinsicBoundaryIntervalCarrier) : Prop :=
  a = b ∨ b = B.intrinsicBoundaryIntervalPair a ∨
    (B.IsIntrinsicBoundaryIntervalEndpoint a ∧ B.IsIntrinsicBoundaryIntervalEndpoint b ∧
      ∃ γ : X.deckGroup, γ • B.intrinsicBoundaryIntervalPoint a =
        B.intrinsicBoundaryIntervalPoint b)

theorem intrinsicBoundaryIntervalRel_iff_orbit (B : DirichletBoundarySegments X o)
    (a b : B.intrinsicBoundaryIntervalCarrier) :
    B.intrinsicBoundaryIntervalRel a b ↔
      ∃ γ : X.deckGroup, γ • B.intrinsicBoundaryIntervalPoint a =
        B.intrinsicBoundaryIntervalPoint b := by
  constructor
  · rintro (rfl | rfl | ⟨_, _, h⟩)
    · exact ⟨1, one_smul _ _⟩
    · exact ⟨(B.intrinsicCyclicEdge a.1).1.1.1⁻¹,
        (B.intrinsicBoundaryIntervalPair_point a).symm⟩
    · exact h
  · rintro ⟨γ, hγ⟩
    by_cases ha : B.IsIntrinsicBoundaryIntervalEndpoint a
    · have hb : B.IsIntrinsicBoundaryIntervalEndpoint b := by
        by_contra hb
        have hγinv : γ⁻¹ • B.intrinsicBoundaryIntervalPoint b =
            B.intrinsicBoundaryIntervalPoint a := by
          rw [← hγ, inv_smul_smul]
        rcases interval_orbit_eq_or_pair_of_interior B b a
            (interval_interior_of_not_endpoint B b hb) γ⁻¹ hγinv with h | h
        · exact hb (h ▸ ha)
        · exact hb ((interval_pair_endpoint_iff B b).1 (h ▸ ha))
      exact Or.inr (Or.inr ⟨ha, hb, γ, hγ⟩)
    · rcases interval_orbit_eq_or_pair_of_interior B a b
        (interval_interior_of_not_endpoint B a ha) γ hγ with h | h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inl h)

/-- The finite side-interval map into the original quotient surface. -/
def intrinsicBoundaryIntervalOrbitMap (B : DirichletBoundarySegments X o) :
    C(B.intrinsicBoundaryIntervalCarrier, X.Carrier) where
  toFun a := Quotient.mk'' (B.intrinsicBoundaryIntervalPoint a)
  continuous_toFun := continuous_quot_mk.comp
    B.continuous_intrinsicBoundaryIntervalPoint

/-- The map covers exactly the original frontier orbit-image, not a replacement graph. -/
theorem range_intrinsicBoundaryIntervalOrbitMap (B : DirichletBoundarySegments X o) :
    range B.intrinsicBoundaryIntervalOrbitMap =
      Quotient.mk'' '' frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) := by
  change range (Quotient.mk'' ∘ B.intrinsicBoundaryIntervalPoint) = _
  rw [range_comp, B.range_intrinsicBoundaryIntervalPoint]

/-- The physical boundary graph relation, realized as the kernel of its literal orbit map. -/
def intrinsicBoundaryIntervalSetoid (B : DirichletBoundarySegments X o) :
    Setoid B.intrinsicBoundaryIntervalCarrier := Setoid.ker B.intrinsicBoundaryIntervalOrbitMap

/-- The kernel has precisely the explicit side-pair and endpoint-vertex identifications. -/
theorem intrinsicBoundaryIntervalSetoid_iff (B : DirichletBoundarySegments X o)
    (a b : B.intrinsicBoundaryIntervalCarrier) :
    B.intrinsicBoundaryIntervalSetoid a b ↔ B.intrinsicBoundaryIntervalRel a b := by
  rw [B.intrinsicBoundaryIntervalRel_iff_orbit]
  change (Quotient.mk'' (B.intrinsicBoundaryIntervalPoint a) : X.Carrier) =
    Quotient.mk'' (B.intrinsicBoundaryIntervalPoint b) ↔ _
  constructor
  · intro h
    exact MulAction.mem_orbit_iff.mp (Quotient.exact h.symm)
  · rintro ⟨γ, hγ⟩
    exact (Quotient.sound (MulAction.mem_orbit_iff.mpr ⟨γ, hγ⟩)).symm

/-- The terminal point of each interval is literally the initial point of the next interval. -/
theorem intrinsicBoundaryIntervalSetoid_next (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryIntervalSetoid (i, 1)
      (finRotate B.intrinsicBoundaryRadialCuts.card i, 0) := by
  change (Quotient.mk'' (B.intrinsicBoundaryIntervalPoint (i, 1)) : X.Carrier) =
    Quotient.mk'' (B.intrinsicBoundaryIntervalPoint
      (finRotate B.intrinsicBoundaryRadialCuts.card i, 0))
  simp only [intrinsicBoundaryIntervalPoint, Set.Icc.coe_one, Set.Icc.coe_zero,
    Vendored.RiemannDynamics.geodInterp_one, Vendored.RiemannDynamics.geodInterp_zero]

/-- The graph's vertex relation is precisely the actual deck-orbit relation on cyclic vertices. -/
theorem intrinsicBoundaryIntervalSetoid_zero_iff (B : DirichletBoundarySegments X o)
    (i j : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryIntervalSetoid (i, 0) (j, 0) ↔
      ∃ γ : X.deckGroup, γ • B.intrinsicCyclicVertex i = B.intrinsicCyclicVertex j := by
  rw [B.intrinsicBoundaryIntervalSetoid_iff, B.intrinsicBoundaryIntervalRel_iff_orbit]
  simp only [intrinsicBoundaryIntervalPoint, Set.Icc.coe_zero,
    Vendored.RiemannDynamics.geodInterp_zero]

/-- The realized finite paired-side graph is homeomorphic to the actual boundary orbit-image. -/
def intrinsicBoundaryGraphHomeomorph (B : DirichletBoundarySegments X o) :
    Quotient B.intrinsicBoundaryIntervalSetoid ≃ₜ
      ↥(Quotient.mk'' '' frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) :
        Set X.Carrier) :=
  (Homeomorph.quotientKerEquivRange
    (B.intrinsicBoundaryIntervalOrbitMap.continuous.isClosedMap.isStrictMap
      B.intrinsicBoundaryIntervalOrbitMap.continuous)).trans
    (Homeomorph.setCongr B.range_intrinsicBoundaryIntervalOrbitMap)

/-- The graph homeomorphism evaluates each interval class at the original quotient point. -/
@[simp] theorem intrinsicBoundaryGraphHomeomorph_mk
    (B : DirichletBoundarySegments X o) (a : B.intrinsicBoundaryIntervalCarrier) :
    (B.intrinsicBoundaryGraphHomeomorph (Quotient.mk _ a)).1 =
      (Quotient.mk'' (B.intrinsicBoundaryIntervalPoint a) : X.Carrier) := rfl

/-- The physical side-interval coordinates cover the entire actual frontier. -/
def intrinsicBoundaryIntervalFrontierMap (B : DirichletBoundarySegments X o) :
    C(B.intrinsicBoundaryIntervalCarrier, X.DirichletFrontier o) :=
  ⟨fun a ↦ ⟨B.intrinsicBoundaryIntervalPoint a, B.intrinsicBoundaryIntervalPoint_mem_frontier a⟩,
    B.continuous_intrinsicBoundaryIntervalPoint.subtype_mk _⟩

theorem intrinsicBoundaryIntervalFrontierMap_surjective (B : DirichletBoundarySegments X o) :
    Function.Surjective B.intrinsicBoundaryIntervalFrontierMap := by
  intro z
  have hz : z.1 ∈ range B.intrinsicBoundaryIntervalPoint :=
    B.range_intrinsicBoundaryIntervalPoint.symm ▸ z.2
  obtain ⟨a, ha⟩ := hz
  exact ⟨a, Subtype.ext ha⟩

/-- The literal finite interval map onto the spine in the original center-punctured surface. -/
def intrinsicBoundaryIntervalSpineMap (B : DirichletBoundarySegments X o) :
    C(B.intrinsicBoundaryIntervalCarrier, X.dirichletBoundarySpine o) :=
  (X.dirichletFrontierSpineProjection o).comp B.intrinsicBoundaryIntervalFrontierMap

theorem intrinsicBoundaryIntervalSpineMap_surjective (B : DirichletBoundarySegments X o) :
    Function.Surjective B.intrinsicBoundaryIntervalSpineMap :=
  (X.dirichletFrontierSpineProjection_surjective o).comp
    B.intrinsicBoundaryIntervalFrontierMap_surjective

/-- Its quotient topology is the native spine topology, by compactness of the finite intervals. -/
theorem intrinsicBoundaryIntervalSpineMap_isQuotientMap (B : DirichletBoundarySegments X o) :
    Topology.IsQuotientMap B.intrinsicBoundaryIntervalSpineMap :=
  B.intrinsicBoundaryIntervalSpineMap.continuous.isClosedMap.isQuotientMap
    B.intrinsicBoundaryIntervalSpineMap.continuous B.intrinsicBoundaryIntervalSpineMap_surjective

/-- The physical paired-side graph is also exactly the native punctured-surface spine. -/
def intrinsicBoundaryGraphSpineHomeomorph (B : DirichletBoundarySegments X o) :
    Quotient B.intrinsicBoundaryIntervalSetoid ≃ₜ X.dirichletBoundarySpine o := by
  let f := B.intrinsicBoundaryIntervalSpineMap
  have hrespect : ∀ a b, B.intrinsicBoundaryIntervalSetoid a b → f a = f b := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact hab
  let F : Quotient B.intrinsicBoundaryIntervalSetoid → X.dirichletBoundarySpine o :=
    Quotient.lift f hrespect
  have hcont : Continuous F := f.continuous.quotient_lift hrespect
  have hbij : Function.Bijective F := by
    constructor
    · intro a b hab
      induction a using Quotient.inductionOn with | h a =>
        induction b using Quotient.inductionOn with | h b =>
          apply Quotient.sound
          exact congrArg (fun z : X.dirichletBoundarySpine o ↦ z.1.1) hab
    · intro z
      obtain ⟨a, ha⟩ := B.intrinsicBoundaryIntervalSpineMap_surjective z
      exact ⟨Quotient.mk _ a, ha⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F hbij) hcont

/-- Native evaluation keeps the original quotient point and only removes its center. -/
@[simp] theorem intrinsicBoundaryGraphSpineHomeomorph_mk
    (B : DirichletBoundarySegments X o) (a : B.intrinsicBoundaryIntervalCarrier) :
    (B.intrinsicBoundaryGraphSpineHomeomorph (Quotient.mk _ a)).1.1 =
      (Quotient.mk'' (B.intrinsicBoundaryIntervalPoint a) : X.Carrier) := rfl

/-- The original punctured surface's based fundamental group is exactly that of its physical
paired-side graph. This transports topology, not an assumed free basis or peripheral marking. -/
def intrinsicBoundaryGraphFundamentalGroupEquiv (B : DirichletBoundarySegments X o)
    (q : X.CenterPuncturedCarrier o) :
    FundamentalGroup (X.CenterPuncturedCarrier o) q ≃*
      FundamentalGroup (Quotient B.intrinsicBoundaryIntervalSetoid)
        (B.intrinsicBoundaryGraphSpineHomeomorph.symm (X.dirichletSpineRetraction o q)) := by
  let e := FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    B.intrinsicBoundaryGraphSpineHomeomorph.symm.toHomotopyEquiv
  have hbij : Function.Bijective (FundamentalGroup.map
      ⟨B.intrinsicBoundaryGraphSpineHomeomorph.symm,
        B.intrinsicBoundaryGraphSpineHomeomorph.symm.continuous⟩
        (X.dirichletSpineRetraction o q)) :=
    e.fullyFaithfulFunctor.map_bijective
      (FundamentalGroupoid.mk (X.dirichletSpineRetraction o q))
      (FundamentalGroupoid.mk (X.dirichletSpineRetraction o q))
  exact (X.dirichletSpineFundamentalGroupEquiv o q).trans
    (MulEquiv.ofBijective (FundamentalGroup.map
      ⟨B.intrinsicBoundaryGraphSpineHomeomorph.symm,
        B.intrinsicBoundaryGraphSpineHomeomorph.symm.continuous⟩
        (X.dirichletSpineRetraction o q)) hbij)

/-- Every actual loop representative, including the original polar loop, is transported by
the literal radial retraction followed by the physical graph homeomorphism. -/
theorem intrinsicBoundaryGraphFundamentalGroupEquiv_loop (B : DirichletBoundarySegments X o)
    (q : X.CenterPuncturedCarrier o) (p : Path q q) :
    B.intrinsicBoundaryGraphFundamentalGroupEquiv q (Path.Homotopic.Quotient.mk p) =
      Path.Homotopic.Quotient.mk
        ((p.map (X.dirichletSpineRetraction o).continuous).map
          B.intrinsicBoundaryGraphSpineHomeomorph.symm.continuous) := rfl

end

end SystolicGrowth.DirichletBoundarySegments
