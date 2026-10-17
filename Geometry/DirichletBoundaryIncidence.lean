module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.DirichletBisectorIntersections

@[expose] public section

/-!
# Incidence away from finitely many candidate boundary vertices

The boundary is a finite union of labeled geodesic segments. Away from
endpoints, degenerate sections, and intersections of differently labeled
sections, there is a unique nondegenerate section. This is an incidence
statement, not yet a cyclic polygon or a local manifold chart.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane

namespace SystolicGrowth
namespace DirichletBoundarySegments

/-- Candidate exceptional boundary points: endpoints, degenerate point
sections, and intersections between distinct labeled sections. -/
def exceptionalPoints {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) : Set ℍ :=
  {z | ∃ i : DirichletBoundarySegmentIndex X o B.radius,
    z = (B.endpoints i).1 ∨ z = (B.endpoints i).2} ∪
  (degeneratePoints B ∪
  {z | ∃ i j : DirichletBoundarySegmentIndex X o B.radius,
    i ≠ j ∧
    z ∈ Vendored.RiemannDynamics.geodSeg (B.endpoints i).1 (B.endpoints i).2 ∧
    z ∈ Vendored.RiemannDynamics.geodSeg (B.endpoints j).1 (B.endpoints j).2})

/-- Only finitely many points have ambiguous or endpoint incidence in the
finite boundary-section family. -/
theorem exceptionalPoints_finite {g : ℕ} {X : ClosedHyperbolicSurface g}
    {o : ℍ} (B : DirichletBoundarySegments X o) :
    (exceptionalPoints B).Finite := by
  exact B.endpoints_finite.union
    (B.degeneratePoints_finite.union B.pairwise_intersection_points_finite)

/-- Every exceptional point lies on the actual Dirichlet frontier. -/
theorem exceptionalPoints_subset_frontier
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    exceptionalPoints B ⊆
      frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) := by
  intro z hz
  rcases hz with hend | hdeg | hinter
  · exact B.endpoints_subset_frontier hend
  · obtain ⟨i, _, hzi⟩ := hdeg
    exact B.segment_subset_frontier i hzi
  · obtain ⟨i, _, _, hzi, _⟩ := hinter
    exact B.segment_subset_frontier i hzi

/-- A frontier point outside the finite exceptional set lies on exactly one
nondegenerate labeled section. -/
theorem existsUnique_nondegenerate_section_of_not_exceptional
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o z : ℍ}
    (B : DirichletBoundarySegments X o)
    (hzfront : z ∈ frontier
      (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o))
    (hzregular : z ∉ exceptionalPoints B) :
    ∃! i : NondegenerateIndex B,
      z ∈ Vendored.RiemannDynamics.geodSeg
        (B.endpoints i.1).1 (B.endpoints i.1).2 := by
  have hznotdeg : z ∉ degeneratePoints B := by
    intro hz
    exact hzregular (Or.inr (Or.inl hz))
  have hznondeg : z ∈ ⋃ i : NondegenerateIndex B,
      Vendored.RiemannDynamics.geodSeg
        (B.endpoints i.1).1 (B.endpoints i.1).2 := by
    rw [B.frontier_eq_nondegenerate_union_degenerate] at hzfront
    exact hzfront.resolve_right hznotdeg
  obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hznondeg
  refine ⟨i, hzi, ?_⟩
  intro j hzj
  by_contra hji
  have hij : i.1 ≠ j.1 := by
    intro h
    exact hji (Subtype.ext h).symm
  exact hzregular (Or.inr (Or.inr ⟨i.1, j.1, hij, hzi, hzj⟩))

/-- Every indexed geodesic section is closed in the hyperbolic plane. -/
theorem segment_isClosed {g : ℕ} {X : ClosedHyperbolicSurface g}
    {o : ℍ} (B : DirichletBoundarySegments X o)
    (i : DirichletBoundarySegmentIndex X o B.radius) :
    IsClosed (Vendored.RiemannDynamics.geodSeg
      (B.endpoints i).1 (B.endpoints i).2) := by
  change IsClosed {z : ℍ | dist (B.endpoints i).1 z +
    dist z (B.endpoints i).2 = dist (B.endpoints i).1 (B.endpoints i).2}
  exact isClosed_eq (by fun_prop) continuous_const

/-- Near a nonexceptional frontier point, all differently labeled sections
are absent. Thus the local frontier equals its unique candidate section;
this does not yet identify an open interval chart on that section. -/
theorem exists_open_unique_section_germ
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o z : ℍ}
    (B : DirichletBoundarySegments X o)
    (hzfront : z ∈ frontier
      (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o))
    (hzregular : z ∉ exceptionalPoints B) :
    ∃ i : NondegenerateIndex B, ∃ U : Set ℍ,
      IsOpen U ∧ z ∈ U ∧
      U ∩ frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) =
        U ∩ Vendored.RiemannDynamics.geodSeg
          (B.endpoints i.1).1 (B.endpoints i.1).2 ∧
      ∀ j : DirichletBoundarySegmentIndex X o B.radius, j ≠ i.1 →
        Disjoint U (Vendored.RiemannDynamics.geodSeg
          (B.endpoints j).1 (B.endpoints j).2) := by
  classical
  obtain ⟨i, hzi, _⟩ :=
    B.existsUnique_nondegenerate_section_of_not_exceptional hzfront hzregular
  let I := DirichletBoundarySegmentIndex X o B.radius
  let side (j : I) : Set ℍ :=
    Vendored.RiemannDynamics.geodSeg (B.endpoints j).1 (B.endpoints j).2
  let others : Set ℍ := ⋃ j : I, if j = i.1 then ∅ else side j
  let U : Set ℍ := othersᶜ
  have hothers_closed : IsClosed others := by
    apply isClosed_iUnion_of_finite
    intro j
    by_cases hj : j = i.1
    · simp [hj]
    · simpa [hj, side] using B.segment_isClosed j
  have hnone (j : I) (hj : j ≠ i.1) : z ∉ side j := by
    intro hzj
    have hij : i.1 ≠ j := Ne.symm hj
    exact hzregular (Or.inr (Or.inr ⟨i.1, j, hij, hzi, hzj⟩))
  have hzU : z ∈ U := by
    intro hzothers
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hzothers
    by_cases hji : j = i.1
    · simp [hji] at hj
    · exact hnone j hji (by simpa [hji] using hj)
  refine ⟨i, U, hothers_closed.isOpen_compl, hzU, ?_, ?_⟩
  · ext w
    constructor
    · rintro ⟨hwU, hwfront⟩
      rw [B.frontier_eq_iUnion] at hwfront
      obtain ⟨j, hwj⟩ := Set.mem_iUnion.mp hwfront
      by_cases hji : j = i.1
      · exact ⟨hwU, by simpa [side, hji] using hwj⟩
      · have hwothers : w ∈ others :=
          Set.mem_iUnion.mpr ⟨j, by simpa [hji] using hwj⟩
        exact (hwU hwothers).elim
    · rintro ⟨hwU, hwside⟩
      exact ⟨hwU, B.segment_subset_frontier i.1 hwside⟩
  · intro j hj
    apply Set.disjoint_left.mpr
    intro w hwU hwj
    exact hwU (Set.mem_iUnion.mpr ⟨j, by simpa [hj] using hwj⟩)

#print axioms exceptionalPoints_finite
#print axioms exceptionalPoints_subset_frontier
#print axioms existsUnique_nondegenerate_section_of_not_exceptional
#print axioms segment_isClosed
#print axioms exists_open_unique_section_germ

end DirichletBoundarySegments
end SystolicGrowth
