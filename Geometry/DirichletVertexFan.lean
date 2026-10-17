module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.DirichletStrictCorners
public import Mathlib.MeasureTheory.Measure.AEDisjoint

@[expose] public section

/-!
# The original boundary-vertex fan of the actual Dirichlet polygon

For `n` genuine cyclic vertices, the `n - 2` indexed triples have apex
vertex zero and consecutive base vertices one through `n - 1`. The triples
retain the already constructed full sides and their original deck labels.
They have three distinct vertices and satisfy the actual strict supporting
inequalities. They cover exactly the original Dirichlet domain and are
pairwise disjoint almost everywhere; shared diagonals have hyperbolic area
zero. No fan coverage or disjointness premise is supplied.
-/

open Set UpperHalfPlane MeasureTheory
open scoped Pointwise UpperHalfPlane

namespace SystolicGrowth
namespace DirichletBoundarySegments

/-- The sides opposite the boundary apex in the `n - 2` fan: side numbers
one through `n - 2`, with no replacement by an interior-center cone fan. -/
def intrinsicVertexFanSideIndex
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (k : Fin (B.intrinsicBoundaryRadialCuts.card - 2)) :
    Fin B.intrinsicBoundaryRadialCuts.card :=
  ⟨k.1 + 1, by have := k.2; omega⟩

/-- The actual boundary-apex triangle vertices. At index `k` the triple is
precisely the cyclic vertices numbered `0`, `k + 1`, and `k + 2`. -/
noncomputable def intrinsicVertexFanVertices
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (k : Fin (B.intrinsicBoundaryRadialCuts.card - 2)) : ℍ × ℍ × ℍ :=
  (B.intrinsicCyclicVertex ⟨0, by have := B.three_le_intrinsicBoundaryRadialCuts_card; omega⟩,
    B.intrinsicCyclicVertex (B.intrinsicVertexFanSideIndex k),
    B.intrinsicCyclicVertex
      (finRotate B.intrinsicBoundaryRadialCuts.card (B.intrinsicVertexFanSideIndex k)))

/-- No fan base passes through the cyclic wrap: its terminal position is
the ordinary index `k + 2`. -/
theorem intrinsicVertexFanSideIndex_next
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (k : Fin (B.intrinsicBoundaryRadialCuts.card - 2)) :
    finRotate B.intrinsicBoundaryRadialCuts.card (B.intrinsicVertexFanSideIndex k) =
      ⟨k.1 + 2, by have := k.2; omega⟩ := by
  have hn := B.three_le_intrinsicBoundaryRadialCuts_card
  haveI : NeZero B.intrinsicBoundaryRadialCuts.card := ⟨by omega⟩
  apply Fin.ext
  rw [finRotate_apply, Fin.val_add, Fin.val_one']
  change (k.1 + 1 + 1 % B.intrinsicBoundaryRadialCuts.card) %
    B.intrinsicBoundaryRadialCuts.card = k.1 + 2
  rw [Nat.mod_eq_of_lt (by omega : 1 < B.intrinsicBoundaryRadialCuts.card)]
  rw [Nat.mod_eq_of_lt (by have := k.2; omega)]

/-- Each of the original boundary-apex fan triples has three distinct
genuine vertices, as required by the triangle certificate consumer. -/
theorem intrinsicVertexFanVertices_pairwise_ne
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (k : Fin (B.intrinsicBoundaryRadialCuts.card - 2)) :
    (B.intrinsicVertexFanVertices k).1 ≠ (B.intrinsicVertexFanVertices k).2.1 ∧
      (B.intrinsicVertexFanVertices k).1 ≠ (B.intrinsicVertexFanVertices k).2.2 ∧
        (B.intrinsicVertexFanVertices k).2.1 ≠ (B.intrinsicVertexFanVertices k).2.2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hi := B.intrinsicCyclicVertex_injective h
    have hv := congrArg Fin.val hi
    change 0 = k.1 + 1 at hv
    omega
  · intro h
    have hi := B.intrinsicCyclicVertex_injective h
    change (⟨0, _⟩ : Fin B.intrinsicBoundaryRadialCuts.card) =
      finRotate B.intrinsicBoundaryRadialCuts.card (B.intrinsicVertexFanSideIndex k) at hi
    rw [B.intrinsicVertexFanSideIndex_next k] at hi
    have hv := congrArg Fin.val hi
    change 0 = k.1 + 2 at hv
    omega
  · exact B.intrinsicCyclicVertex_next_ne (B.intrinsicVertexFanSideIndex k)

/-- Each fan base is exactly the corresponding original full labeled
Dirichlet side, compatible with the already proved cyclic side pairing. -/
theorem intrinsicVertexFan_base_eq_closedEdge
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (k : Fin (B.intrinsicBoundaryRadialCuts.card - 2)) :
    Vendored.RiemannDynamics.geodSeg
      (B.intrinsicVertexFanVertices k).2.1 (B.intrinsicVertexFanVertices k).2.2 =
        B.closedEdgeImage B.intrinsicCornerCuts
          (B.intrinsicCyclicEdge (B.intrinsicVertexFanSideIndex k)) :=
  (B.intrinsicCyclicEdge_closedImage_eq_geodSeg (B.intrinsicVertexFanSideIndex k)).symm

/-- The genuine boundary apex is strictly inside the distance halfspace
supporting each opposite fan base. This proves strict support from actual
geometry, rather than assuming that the chosen triples are a fan. -/
theorem intrinsicVertexFan_apex_strict_support
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (k : Fin (B.intrinsicBoundaryRadialCuts.card - 2)) :
    dist (B.intrinsicVertexFanVertices k).1 o <
      dist (B.intrinsicVertexFanVertices k).1
        ((B.intrinsicCyclicEdge (B.intrinsicVertexFanSideIndex k)).1.1.1 • o) := by
  apply B.intrinsicCyclicVertex_dist_lt_of_not_incident
    (B.intrinsicVertexFanSideIndex k)
    ⟨0, by have := B.three_le_intrinsicBoundaryRadialCuts_card; omega⟩
  · intro h
    have hv := congrArg Fin.val h
    change 0 = k.1 + 1 at hv
    omega
  · rw [B.intrinsicVertexFanSideIndex_next k]
    intro h
    have hv := congrArg Fin.val h
    change 0 = k.1 + 2 at hv
    omega

/-- Every one of these concrete fan triangles lies in the same actual
Dirichlet domain, by its full-group distance halfspaces. -/
theorem intrinsicVertexFan_triangle_subset_dirichletDomain
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (k : Fin (B.intrinsicBoundaryRadialCuts.card - 2)) :
    Vendored.RiemannDynamics.hyperbolicTriangle
      (B.intrinsicVertexFanVertices k).1 (B.intrinsicVertexFanVertices k).2.1
      (B.intrinsicVertexFanVertices k).2.2 ⊆
        Vendored.RiemannDynamics.dirichletDomain X.deckGroup o := by
  have hvertex (i : Fin B.intrinsicBoundaryRadialCuts.card) :
      B.intrinsicCyclicVertex i ∈
        Vendored.RiemannDynamics.dirichletDomain X.deckGroup o := by
    have hz : B.intrinsicCyclicVertex i ∈
        B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge i) := by
      rw [B.intrinsicCyclicEdge_closedImage_eq_geodSeg]
      exact Vendored.RiemannDynamics.left_mem_geodSeg _ _
    rw [B.intrinsicClosedEdgeImage_eq_fullSection] at hz
    exact hz.1
  have h1 : (B.intrinsicVertexFanVertices k).1 ∈
      Vendored.RiemannDynamics.dirichletDomain X.deckGroup o := hvertex _
  have h2 : (B.intrinsicVertexFanVertices k).2.1 ∈
      Vendored.RiemannDynamics.dirichletDomain X.deckGroup o := hvertex _
  have h3 : (B.intrinsicVertexFanVertices k).2.2 ∈
      Vendored.RiemannDynamics.dirichletDomain X.deckGroup o := hvertex _
  intro z hz
  apply Vendored.RiemannDynamics.mem_dirichletDomain.mpr
  intro γ
  exact Vendored.RiemannDynamics.geodCone_subset_dist_le
    ((Vendored.RiemannDynamics.mem_dirichletDomain.mp h1) γ)
    ((Vendored.RiemannDynamics.mem_dirichletDomain.mp h2) γ)
    ((Vendored.RiemannDynamics.mem_dirichletDomain.mp h3) γ) hz

/-- Each concrete fan triangle is measurable because it is the continuous
image of the compact unit parameter square. -/
theorem intrinsicVertexFan_triangle_measurable
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (k : Fin (B.intrinsicBoundaryRadialCuts.card - 2)) :
    MeasurableSet (Vendored.RiemannDynamics.hyperbolicTriangle
      (B.intrinsicVertexFanVertices k).1 (B.intrinsicVertexFanVertices k).2.1
      (B.intrinsicVertexFanVertices k).2.2) :=
  (Vendored.RiemannDynamics.isCompact_hyperbolicTriangle _ _ _).isClosed.measurableSet

private theorem mem_geodSeg_left_subsegment {a b c z : ℍ}
    (hb : b ∈ Vendored.RiemannDynamics.geodSeg a c)
    (hz : z ∈ Vendored.RiemannDynamics.geodSeg a b) :
    z ∈ Vendored.RiemannDynamics.geodSeg a c := by
  change dist a b + dist b c = dist a c at hb
  change dist a z + dist z b = dist a b at hz
  change dist a z + dist z c = dist a c
  have h1 := dist_triangle z b c
  have h2 := dist_triangle a z c
  linarith

/-- The original `n - 2` boundary-vertex fan covers exactly the same actual
Dirichlet domain. The two sides incident to the apex contribute only their
segments, already contained in the first and last listed fan triangles. -/
theorem iUnion_intrinsicVertexFan_triangle_eq_dirichletDomain
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    (⋃ k : Fin (B.intrinsicBoundaryRadialCuts.card - 2),
      Vendored.RiemannDynamics.hyperbolicTriangle
        (B.intrinsicVertexFanVertices k).1 (B.intrinsicVertexFanVertices k).2.1
        (B.intrinsicVertexFanVertices k).2.2) =
          Vendored.RiemannDynamics.dirichletDomain X.deckGroup o := by
  have hn := B.three_le_intrinsicBoundaryRadialCuts_card
  let zero : Fin B.intrinsicBoundaryRadialCuts.card := ⟨0, by omega⟩
  let apex := B.intrinsicCyclicVertex zero
  let first : Fin (B.intrinsicBoundaryRadialCuts.card - 2) := ⟨0, by omega⟩
  haveI : NeZero B.intrinsicBoundaryRadialCuts.card := ⟨by omega⟩
  have h0next : finRotate B.intrinsicBoundaryRadialCuts.card zero =
      B.intrinsicVertexFanSideIndex first := by
    apply Fin.ext
    rw [finRotate_apply, Fin.val_add, Fin.val_one']
    change (0 + 1 % B.intrinsicBoundaryRadialCuts.card) %
      B.intrinsicBoundaryRadialCuts.card = 1
    rw [Nat.mod_eq_of_lt (by omega : 1 < B.intrinsicBoundaryRadialCuts.card)]
    simpa using Nat.mod_eq_of_lt (by omega : 1 < B.intrinsicBoundaryRadialCuts.card)
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨k, hzk⟩ := Set.mem_iUnion.mp hz
    exact B.intrinsicVertexFan_triangle_subset_dirichletDomain k hzk
  · intro z hzD
    by_cases hza : z = apex
    · refine Set.mem_iUnion.mpr ⟨first, ?_⟩
      apply Vendored.RiemannDynamics.mem_geodCone.mpr
      refine ⟨(B.intrinsicVertexFanVertices first).2.1,
        Vendored.RiemannDynamics.left_mem_geodSeg _ _, ?_⟩
      rw [hza]
      exact Vendored.RiemannDynamics.left_mem_geodSeg _ _
    obtain ⟨K, hK, hcover⟩ := X.exists_compact_covering
    have hcompact := X.isCompact_dirichletDomain_of_compact_covering o K hK hcover
    obtain ⟨b, hbfront, hzb⟩ :=
      ClosedHyperbolicSurface.exists_mem_frontier_geodSeg_of_isCompact hcompact hzD hza
    rw [← B.iUnion_intrinsicCyclicClosedEdge_eq_frontier] at hbfront
    obtain ⟨i, hbside⟩ := Set.mem_iUnion.mp hbfront
    by_cases hi0 : i.1 = 0
    · have hizero : i = zero := Fin.ext hi0
      rw [hizero, B.intrinsicCyclicEdge_closedImage_eq_geodSeg, h0next] at hbside
      change b ∈ Vendored.RiemannDynamics.geodSeg apex
        (B.intrinsicVertexFanVertices first).2.1 at hbside
      refine Set.mem_iUnion.mpr ⟨first, ?_⟩
      apply Vendored.RiemannDynamics.mem_geodCone.mpr
      refine ⟨(B.intrinsicVertexFanVertices first).2.1,
        Vendored.RiemannDynamics.left_mem_geodSeg _ _, ?_⟩
      exact mem_geodSeg_left_subsegment hbside hzb
    by_cases hilast : i.1 + 1 = B.intrinsicBoundaryRadialCuts.card
    · let last : Fin (B.intrinsicBoundaryRadialCuts.card - 2) :=
        ⟨B.intrinsicBoundaryRadialCuts.card - 3, by omega⟩
      have hinext : finRotate B.intrinsicBoundaryRadialCuts.card i = zero := by
        apply Fin.ext
        rw [finRotate_apply, Fin.val_add, Fin.val_one']
        change (i.1 + 1 % B.intrinsicBoundaryRadialCuts.card) %
          B.intrinsicBoundaryRadialCuts.card = 0
        rw [Nat.mod_eq_of_lt (by omega : 1 < B.intrinsicBoundaryRadialCuts.card),
          hilast, Nat.mod_self]
      have hlastvertex : (B.intrinsicVertexFanVertices last).2.2 =
          B.intrinsicCyclicVertex i := by
        change B.intrinsicCyclicVertex
          (finRotate B.intrinsicBoundaryRadialCuts.card (B.intrinsicVertexFanSideIndex last)) = _
        rw [B.intrinsicVertexFanSideIndex_next]
        congr 1
        apply Fin.ext
        change B.intrinsicBoundaryRadialCuts.card - 3 + 2 = i.1
        omega
      rw [B.intrinsicCyclicEdge_closedImage_eq_geodSeg, hinext,
        Vendored.RiemannDynamics.geodSeg_comm, ← hlastvertex] at hbside
      refine Set.mem_iUnion.mpr ⟨last, ?_⟩
      apply Vendored.RiemannDynamics.mem_geodCone.mpr
      refine ⟨(B.intrinsicVertexFanVertices last).2.2,
        Vendored.RiemannDynamics.right_mem_geodSeg _ _, ?_⟩
      exact mem_geodSeg_left_subsegment hbside hzb
    · let k : Fin (B.intrinsicBoundaryRadialCuts.card - 2) := ⟨i.1 - 1, by omega⟩
      have hki : B.intrinsicVertexFanSideIndex k = i := by
        apply Fin.ext
        change i.1 - 1 + 1 = i.1
        omega
      refine Set.mem_iUnion.mpr ⟨k, ?_⟩
      apply Vendored.RiemannDynamics.mem_geodCone.mpr
      refine ⟨b, ?_, hzb⟩
      rw [B.intrinsicVertexFan_base_eq_closedEdge, hki]
      exact hbside

/-- The existing triangle fundamental-domain structure instantiated by the
actual `n - 2` boundary-vertex fan, with its exact original Dirichlet domain. -/
noncomputable def intrinsicVertexFanTriangleFundamentalDomain
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) : FiniteTriangleFundamentalDomain X where
  triangleCount := B.intrinsicBoundaryRadialCuts.card - 2
  vertices := B.intrinsicVertexFanVertices
  fundamentalDomain := Vendored.RiemannDynamics.dirichletDomain X.deckGroup o
  isFundamentalDomain := X.dirichletDomain_isFundamentalDomain o
  coveredByTriangles := by rw [B.iUnion_intrinsicVertexFan_triangle_eq_dirichletDomain]
  nondegenerate := B.intrinsicVertexFanVertices_pairwise_ne

private theorem bisector_terminal_point_of_strict_halfspace
    {p q a z w : ℍ} (hpq : p ≠ q) (ha : dist a p < dist a q)
    (hz : dist z p = dist z q) (hw : dist w p ≤ dist w q)
    (hzw : z ∈ Vendored.RiemannDynamics.geodSeg a w) : z = w := by
  obtain ⟨A, him, hre, h0⟩ := Vendored.RiemannDynamics.exists_mirror_normalizer hpq
  have hzre : (A • z).re = 0 :=
    (Vendored.RiemannDynamics.bisector_re_eq_zero him hre h0 z).mp hz
  have hazero : (A • a).re ≠ 0 := by
    intro hare
    exact ha.ne ((Vendored.RiemannDynamics.bisector_re_eq_zero him hre h0 a).mpr hare)
  have hzseg : A • z ∈ Vendored.RiemannDynamics.geodSeg (A • a) (A • w) := by
    rw [← Vendored.RiemannDynamics.smul_geodSeg]
    exact ⟨z, hzw, rfl⟩
  have hbetw := Vendored.RiemannDynamics.re_mem_geodSeg hzseg
  have hacomp : dist (A • a) (A • p) ≤ dist (A • a) (A • q) := by
    simpa only [dist_smul] using ha.le
  have hwcomp : dist (A • w) (A • p) ≤ dist (A • w) (A • q) := by
    simpa only [dist_smul] using hw
  have hmid : ((A • p).re + (A • q).re) / 2 = 0 := by rw [hre]; ring
  have hwre : (A • w).re = 0 := by
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · have hset := Vendored.RiemannDynamics.setOf_dist_le_eq_of_im_eq
        (a := A • p) (b := A • q) him.symm (by rw [hre]; linarith)
      change A • a ∈ {u : ℍ | dist u (A • p) ≤ dist u (A • q)} at hacomp
      change A • w ∈ {u : ℍ | dist u (A • p) ≤ dist u (A • q)} at hwcomp
      rw [hset, hmid] at hacomp hwcomp
      have haneg : (A • a).re < 0 := lt_of_le_of_ne hacomp hazero
      by_contra hwne
      have hwneg : (A • w).re < 0 := lt_of_le_of_ne hwcomp hwne
      have hmax : max (A • a).re (A • w).re < 0 := max_lt haneg hwneg
      rw [hzre] at hbetw
      exact (not_lt_of_ge hbetw.2) hmax
    · have hset := Vendored.RiemannDynamics.setOf_dist_le_eq_of_im_eq'
        (a := A • p) (b := A • q) him.symm (by rw [hre]; linarith)
      change A • a ∈ {u : ℍ | dist u (A • p) ≤ dist u (A • q)} at hacomp
      change A • w ∈ {u : ℍ | dist u (A • p) ≤ dist u (A • q)} at hwcomp
      rw [hset, hmid] at hacomp hwcomp
      have hapos : 0 < (A • a).re := lt_of_le_of_ne hacomp (Ne.symm hazero)
      by_contra hwne
      have hwpos : 0 < (A • w).re := lt_of_le_of_ne hwcomp (Ne.symm hwne)
      have hmin : 0 < min (A • a).re (A • w).re := lt_min hapos hwpos
      rw [hzre] at hbetw
      exact (not_lt_of_ge hbetw.1) hmin
  have hane : (A • a).re ≠ (A • w).re := by rwa [hwre]
  exact smul_left_cancel A (geodSeg_eq_right_of_re_eq hane hzseg (hzre.trans hwre.symm))

/-- Distinct triangles in the actual boundary-apex fan can meet only along
the two apex-to-base-vertex diagonals of the first triangle. Strict support
forces the two terminal base points on a shared apex ray to coincide. -/
theorem intrinsicVertexFan_triangle_inter_subset_diagonals
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    {k l : Fin (B.intrinsicBoundaryRadialCuts.card - 2)} (hkl : k ≠ l) :
    Vendored.RiemannDynamics.hyperbolicTriangle
        (B.intrinsicVertexFanVertices k).1 (B.intrinsicVertexFanVertices k).2.1
        (B.intrinsicVertexFanVertices k).2.2 ∩
      Vendored.RiemannDynamics.hyperbolicTriangle
        (B.intrinsicVertexFanVertices l).1 (B.intrinsicVertexFanVertices l).2.1
        (B.intrinsicVertexFanVertices l).2.2 ⊆
      Vendored.RiemannDynamics.geodSeg
        (B.intrinsicVertexFanVertices k).1 (B.intrinsicVertexFanVertices k).2.1 ∪
      Vendored.RiemannDynamics.geodSeg
        (B.intrinsicVertexFanVertices k).1 (B.intrinsicVertexFanVertices k).2.2 := by
  intro z hz
  by_cases hza : z = (B.intrinsicVertexFanVertices k).1
  · exact Or.inl (hza ▸ Vendored.RiemannDynamics.left_mem_geodSeg _ _)
  obtain ⟨b, hbbase, hzb⟩ := Vendored.RiemannDynamics.mem_geodCone.mp hz.1
  obtain ⟨c, hcbase, hzc⟩ := Vendored.RiemannDynamics.mem_geodCone.mp hz.2
  have hbedge : b ∈ B.closedEdgeImage B.intrinsicCornerCuts
      (B.intrinsicCyclicEdge (B.intrinsicVertexFanSideIndex k)) := by
    rwa [← B.intrinsicVertexFan_base_eq_closedEdge]
  have hcedge : c ∈ B.closedEdgeImage B.intrinsicCornerCuts
      (B.intrinsicCyclicEdge (B.intrinsicVertexFanSideIndex l)) := by
    rwa [← B.intrinsicVertexFan_base_eq_closedEdge]
  have hbsection := hbedge
  have hcsection := hcedge
  rw [B.intrinsicClosedEdgeImage_eq_fullSection] at hbsection hcsection
  have hbne : b ≠ (B.intrinsicVertexFanVertices k).1 := by
    intro h
    exact (B.intrinsicVertexFan_apex_strict_support k).ne (h ▸ hbsection.2)
  have hcne : c ≠ (B.intrinsicVertexFanVertices l).1 := by
    intro h
    exact (B.intrinsicVertexFan_apex_strict_support l).ne (h ▸ hcsection.2)
  have hdir : hyperbolicRadialDirection (B.intrinsicVertexFanVertices k).1 b =
      hyperbolicRadialDirection (B.intrinsicVertexFanVertices k).1 c :=
    (hyperbolicRadialDirection_eq_of_mem_geodSeg hzb hza).symm.trans
      (hyperbolicRadialDirection_eq_of_mem_geodSeg hzc hza)
  have hfocus (j : Fin (B.intrinsicBoundaryRadialCuts.card - 2)) :
      o ≠ (B.intrinsicCyclicEdge (B.intrinsicVertexFanSideIndex j)).1.1.1 • o := by
    intro h
    exact (Finset.ne_of_mem_erase
      (B.intrinsicCyclicEdge (B.intrinsicVertexFanSideIndex j)).1.1.2.1)
      (X.free _ o h.symm)
  have hbc : b = c := by
    rcases le_total
        ‖Vendored.RiemannDynamics.discChart (B.intrinsicVertexFanVertices k).1 b‖
        ‖Vendored.RiemannDynamics.discChart (B.intrinsicVertexFanVertices k).1 c‖ with h | h
    · exact bisector_terminal_point_of_strict_halfspace (hfocus k)
        (B.intrinsicVertexFan_apex_strict_support k) hbsection.2
        ((Vendored.RiemannDynamics.mem_dirichletDomain.mp hcsection.1) _)
        (mem_geodSeg_of_radialDirection_eq_of_norm_le hbne hdir h)
    · exact (bisector_terminal_point_of_strict_halfspace (hfocus l)
        (B.intrinsicVertexFan_apex_strict_support l) hcsection.2
        ((Vendored.RiemannDynamics.mem_dirichletDomain.mp hbsection.1) _)
        (mem_geodSeg_of_radialDirection_eq_of_norm_le hcne hdir.symm h)).symm
  rw [← hbc] at hcedge
  have hsidene : B.intrinsicCyclicEdge (B.intrinsicVertexFanSideIndex k) ≠
      B.intrinsicCyclicEdge (B.intrinsicVertexFanSideIndex l) := by
    intro h
    have hi := B.intrinsicCyclicEdge_injective h
    have hv := congrArg Fin.val hi
    change k.1 + 1 = l.1 + 1 at hv
    exact hkl (Fin.ext (by omega))
  have hbends :=
    (B.intrinsicClosedEdgeImage_inter_subset_endpointSets hsidene ⟨hbedge, hcedge⟩).1
  rcases B.intrinsicCyclicEdge_endpoints_eq_or_swap (B.intrinsicVertexFanSideIndex k)
      with hends | hends
  · simp only [closedEdgeEndpointSet, hends, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hbends
    rcases hbends with hb | hb
    · exact Or.inl (by simpa only [intrinsicVertexFanVertices, hb] using hzb)
    · exact Or.inr (by simpa only [intrinsicVertexFanVertices, hb] using hzb)
  · simp only [closedEdgeEndpointSet, hends, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hbends
    rcases hbends with hb | hb
    · exact Or.inr (by simpa only [intrinsicVertexFanVertices, hb] using hzb)
    · exact Or.inl (by simpa only [intrinsicVertexFanVertices, hb] using hzb)

/-- The actual `n - 2` boundary-vertex fan triangles are pairwise disjoint
almost everywhere for hyperbolic area. Their possible diagonal intersections
are geodesic segments, hence null. -/
theorem intrinsicVertexFan_triangle_ae_disjoint
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    Pairwise (fun k l : Fin (B.intrinsicBoundaryRadialCuts.card - 2) =>
      AEDisjoint volume
        (Vendored.RiemannDynamics.hyperbolicTriangle
          (B.intrinsicVertexFanVertices k).1 (B.intrinsicVertexFanVertices k).2.1
          (B.intrinsicVertexFanVertices k).2.2)
        (Vendored.RiemannDynamics.hyperbolicTriangle
          (B.intrinsicVertexFanVertices l).1 (B.intrinsicVertexFanVertices l).2.1
          (B.intrinsicVertexFanVertices l).2.2)) := by
  intro k l hkl
  exact measure_mono_null (B.intrinsicVertexFan_triangle_inter_subset_diagonals hkl)
    (measure_union_null (Vendored.RiemannDynamics.volume_geodSeg_eq_zero _ _)
      (Vendored.RiemannDynamics.volume_geodSeg_eq_zero _ _))

end DirichletBoundarySegments

#print axioms DirichletBoundarySegments.intrinsicVertexFanVertices_pairwise_ne
#print axioms DirichletBoundarySegments.intrinsicVertexFan_apex_strict_support
#print axioms DirichletBoundarySegments.intrinsicVertexFan_triangle_subset_dirichletDomain
#print axioms DirichletBoundarySegments.iUnion_intrinsicVertexFan_triangle_eq_dirichletDomain
#print axioms DirichletBoundarySegments.intrinsicVertexFanTriangleFundamentalDomain
#print axioms DirichletBoundarySegments.intrinsicVertexFan_triangle_inter_subset_diagonals
#print axioms DirichletBoundarySegments.intrinsicVertexFan_triangle_ae_disjoint

end SystolicGrowth
