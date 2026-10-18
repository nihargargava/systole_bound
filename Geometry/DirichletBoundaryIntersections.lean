module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.DirichletBoundarySegments

@[expose] public section

/-!
# Removing degenerate candidates from a finite Dirichlet boundary cover

The finite bisector sections are geodesic segments, but some may be points.
This module isolates the nondegenerate indices and proves that the omitted
point sections form a finite set. It does not claim that distinct remaining
segments intersect only finitely: overlapping collinear candidates require
separate analysis before a cyclic polygon can be constructed.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane

namespace SystolicGrowth
namespace DirichletBoundarySegments

/-- Labels whose actual Dirichlet bisector section has distinct endpoints. -/
abbrev NondegenerateIndex {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :=
  {i : DirichletBoundarySegmentIndex X o B.radius //
    (B.endpoints i).1 ≠ (B.endpoints i).2}

/-- Removing degenerate labels preserves finiteness of the index. -/
instance {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) : Finite (NondegenerateIndex B) :=
  Finite.of_injective (fun i : NondegenerateIndex B => i.1)
    (fun _ _ h => Subtype.ext h)

/-- A finite enumeration of the remaining nondegenerate labels. -/
noncomputable instance {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) : Fintype (NondegenerateIndex B) :=
  Fintype.ofFinite _

/-- Points on bisector sections whose chosen endpoints coincide. -/
def degeneratePoints {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) : Set ℍ :=
  {z | ∃ i : DirichletBoundarySegmentIndex X o B.radius,
    (B.endpoints i).1 = (B.endpoints i).2 ∧
      z ∈ Vendored.RiemannDynamics.geodSeg
        (B.endpoints i).1 (B.endpoints i).2}

/-- Every degenerate segment is one of the finitely many candidate endpoints. -/
theorem degeneratePoints_finite {g : ℕ} {X : ClosedHyperbolicSurface g}
    {o : ℍ} (B : DirichletBoundarySegments X o) :
    (degeneratePoints B).Finite := by
  apply B.endpoints_finite.subset
  intro z hz
  obtain ⟨i, hdeg, hzseg⟩ := hz
  have hzeq : z = (B.endpoints i).2 := by
    simpa [hdeg, Vendored.RiemannDynamics.geodSeg_self] using hzseg
  exact ⟨i, Or.inr hzeq⟩

/-- The exact frontier is covered by the nondegenerate labeled segments,
apart from the explicitly finite set of degenerate point sections. -/
theorem frontier_eq_nondegenerate_union_degenerate
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) =
      (⋃ i : NondegenerateIndex B,
        Vendored.RiemannDynamics.geodSeg
          (B.endpoints i.1).1 (B.endpoints i.1).2) ∪
        degeneratePoints B := by
  rw [B.frontier_eq_iUnion]
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨i, hzseg⟩ := Set.mem_iUnion.mp hz
    by_cases hdeg : (B.endpoints i).1 = (B.endpoints i).2
    · exact Or.inr ⟨i, hdeg, hzseg⟩
    · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨i, hdeg⟩, hzseg⟩)
  · intro z hz
    rcases hz with hnondeg | hdeg
    · obtain ⟨i, hzseg⟩ := Set.mem_iUnion.mp hnondeg
      exact Set.mem_iUnion.mpr ⟨i.1, hzseg⟩
    · obtain ⟨i, _, hzseg⟩ := hdeg
      exact Set.mem_iUnion.mpr ⟨i, hzseg⟩

#print axioms degeneratePoints_finite
#print axioms frontier_eq_nondegenerate_union_degenerate

end DirichletBoundarySegments
end SystolicGrowth
