module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.FiniteTriangleFundamentalDomain

@[expose] public section

/-!
# Finite labeled segments on a Dirichlet boundary

Each index is an actual nonidentity deck transformation whose bisector has a
nonempty section in the Dirichlet domain. The index is finite, and its section
is exactly one geodesic segment. The finite family covers the whole frontier.
Segments may still be degenerate or overlap: no cyclic polygon, side pairing,
or angle data is asserted here.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane

namespace SystolicGrowth

/-- The finite deck labels with a nonempty Dirichlet bisector section. -/
abbrev DirichletBoundarySegmentIndex {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (R : ℝ) :=
  {γ : X.deckGroup // γ ∈ (deckElementsDistLE X o (2 * R)).erase 1 ∧
    (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
      {z : ℍ | dist z o = dist z (γ • o)}).Nonempty}

/-- The segment labels lie in the finite bounded-displacement deck set. -/
instance {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) (R : ℝ) :
    Finite (DirichletBoundarySegmentIndex X o R) := by
  let F := (deckElementsDistLE X o (2 * R)).erase 1
  have hfinite : ({γ : X.deckGroup | γ ∈ F ∧
      (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
        {z : ℍ | dist z o = dist z (γ • o)}).Nonempty} : Set X.deckGroup).Finite := by
    apply F.finite_toSet.subset
    intro γ hγ
    exact hγ.1
  exact hfinite.to_subtype

/-- A concrete finite enumeration of the actual bisector labels. -/
noncomputable instance {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) (R : ℝ) :
    Fintype (DirichletBoundarySegmentIndex X o R) :=
  Fintype.ofFinite _

/-- Finite boundary data retaining each segment's original deck label.
The label of `i` is `i.1`, and `i.2` certifies its nontriviality and section
nonemptiness. -/
structure DirichletBoundarySegments {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) where
  radius : ℝ
  radius_pos : 0 < radius
  endpoints : DirichletBoundarySegmentIndex X o radius → ℍ × ℍ
  section_eq_segment : ∀ i : DirichletBoundarySegmentIndex X o radius,
    Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
      {z : ℍ | dist z o = dist z (i.1 • o)} =
        Vendored.RiemannDynamics.geodSeg (endpoints i).1 (endpoints i).2
  frontier_eq_iUnion :
    frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) =
      ⋃ i : DirichletBoundarySegmentIndex X o radius,
        Vendored.RiemannDynamics.geodSeg (endpoints i).1 (endpoints i).2

/-- Package the proved finite section cover without adding polygonal claims. -/
noncomputable def ClosedHyperbolicSurface.dirichletBoundarySegments
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) :
    DirichletBoundarySegments X o := by
  classical
  apply Classical.choice
  obtain ⟨R, hR, p, hsection, hfrontier⟩ :=
    X.exists_finite_geodSeg_boundary_cover_with_sections o
  exact ⟨⟨R, hR, p, hsection, hfrontier⟩⟩

namespace DirichletBoundarySegments

/-- An indexed segment lies on the Dirichlet frontier. -/
theorem segment_subset_frontier {g : ℕ} {X : ClosedHyperbolicSurface g}
    {o : ℍ} (B : DirichletBoundarySegments X o)
    (i : DirichletBoundarySegmentIndex X o B.radius) :
    Vendored.RiemannDynamics.geodSeg (B.endpoints i).1 (B.endpoints i).2 ⊆
      frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) := by
  intro z hz
  have hsection : z ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
      {z : ℍ | dist z o = dist z (i.1 • o)} := by
    rw [B.section_eq_segment i]
    exact hz
  exact X.mem_frontier_dirichletDomain_of_mem_bisector o i.1
    (Finset.ne_of_mem_erase i.2.1) hsection.1 hsection.2

/-- The endpoints of the finitely indexed boundary segments form a finite set. -/
theorem endpoints_finite {g : ℕ} {X : ClosedHyperbolicSurface g}
    {o : ℍ} (B : DirichletBoundarySegments X o) :
    {z : ℍ | ∃ i : DirichletBoundarySegmentIndex X o B.radius,
      z = (B.endpoints i).1 ∨ z = (B.endpoints i).2}.Finite := by
  classical
  have hleft : (Set.range (fun i : DirichletBoundarySegmentIndex X o B.radius =>
      (B.endpoints i).1)).Finite := Set.finite_range _
  have hright : (Set.range (fun i : DirichletBoundarySegmentIndex X o B.radius =>
      (B.endpoints i).2)).Finite := Set.finite_range _
  apply (hleft.union hright).subset
  intro z hz
  rcases hz with ⟨i, hzi | hzi⟩
  · exact Or.inl ⟨i, hzi.symm⟩
  · exact Or.inr ⟨i, hzi.symm⟩

/-- Every candidate endpoint belongs to the actual Dirichlet frontier.
This does not assert that it is a vertex of a reduced polygon. -/
theorem endpoints_subset_frontier {g : ℕ} {X : ClosedHyperbolicSurface g}
    {o : ℍ} (B : DirichletBoundarySegments X o) :
    {z : ℍ | ∃ i : DirichletBoundarySegmentIndex X o B.radius,
      z = (B.endpoints i).1 ∨ z = (B.endpoints i).2} ⊆
      frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) := by
  rintro z ⟨i, hzi | hzi⟩
  · rw [hzi]
    exact B.segment_subset_frontier i
      (Vendored.RiemannDynamics.left_mem_geodSeg _ _)
  · rw [hzi]
    exact B.segment_subset_frontier i
      (Vendored.RiemannDynamics.right_mem_geodSeg _ _)

end DirichletBoundarySegments

#print axioms ClosedHyperbolicSurface.dirichletBoundarySegments
#print axioms DirichletBoundarySegments.segment_subset_frontier
#print axioms DirichletBoundarySegments.endpoints_finite
#print axioms DirichletBoundarySegments.endpoints_subset_frontier

end SystolicGrowth
