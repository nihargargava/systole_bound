module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.DirichletBoundaryCharts

@[expose] public section

/-!
# Finite parameter gaps on candidate Dirichlet sides

An adjacent pair of cuts indexes an open interval in the real parameter of a
candidate geodesic side. This is a linear subdivision of each individual side;
it does not equip the whole Dirichlet boundary with a cyclic order.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane

namespace SystolicGrowth

/-- An adjacent ordered pair of elements of a finite parameter cut set. -/
structure DirichletParameterGap (cuts : Finset ℝ) where
  left : {t : ℝ // t ∈ cuts}
  right : {t : ℝ // t ∈ cuts}
  left_lt_right : left.1 < right.1
  adjacent : ∀ c ∈ cuts, c ≤ left.1 ∨ right.1 ≤ c

/-- There are only finitely many gaps between elements of a finite cut set. -/
instance (cuts : Finset ℝ) : Finite (DirichletParameterGap cuts) :=
  Finite.of_injective (fun e : DirichletParameterGap cuts => (e.left, e.right)) (by
    intro e e' h
    cases e with
    | mk l r _ _ =>
      cases e' with
      | mk l' r' _ _ =>
        cases h
        rfl)

noncomputable instance (cuts : Finset ℝ) : Fintype (DirichletParameterGap cuts) :=
  Fintype.ofFinite _

/-- The cuts and their consecutive open intervals partition the unit interval
as a set. The intervals are not yet assembled into a cyclic boundary. -/
theorem icc_eq_cuts_union_gaps (cuts : Finset ℝ)
    (hzero : (0 : ℝ) ∈ cuts) (hone : (1 : ℝ) ∈ cuts)
    (hcuts : ∀ c ∈ cuts, c ∈ Set.Icc (0 : ℝ) 1) :
    Set.Icc (0 : ℝ) 1 =
      (↑cuts : Set ℝ) ∪ ⋃ e : DirichletParameterGap cuts,
        Set.Ioo (e.left : ℝ) (e.right : ℝ) := by
  ext t
  constructor
  · intro ht
    by_cases htcut : t ∈ cuts
    · exact Or.inl htcut
    have htzero : t ≠ 0 := by
      intro h
      subst t
      exact htcut hzero
    have htone : t ≠ 1 := by
      intro h
      subst t
      exact htcut hone
    have htIoo : t ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm htzero), lt_of_le_of_ne ht.2 htone⟩
    obtain ⟨l, r, hl, hr, _, _, hlt, htr, hadj⟩ :=
      DirichletBoundarySegments.exists_adjacent_cuts_around cuts hzero hone htIoo htcut
    let e : DirichletParameterGap cuts :=
      ⟨⟨l, hl⟩, ⟨r, hr⟩, lt_trans hlt htr, hadj⟩
    exact Or.inr (Set.mem_iUnion.mpr ⟨e, ⟨hlt, htr⟩⟩)
  · intro ht
    rcases ht with htcut | htgap
    · exact hcuts t htcut
    · obtain ⟨e, hte⟩ := Set.mem_iUnion.mp htgap
      have hleft := hcuts e.left.1 e.left.2
      have hright := hcuts e.right.1 e.right.2
      exact ⟨le_trans hleft.1 (le_of_lt hte.1),
        le_trans (le_of_lt hte.2) hright.2⟩

#print axioms icc_eq_cuts_union_gaps

namespace DirichletBoundarySegments

/-- A nondegenerate candidate segment is the union of its actual finite cut
points and the images of its adjacent open parameter gaps. The cut
characterization retains exactly the two endpoints and exceptional points. -/
theorem exists_geodSeg_parameter_subdivision
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B) :
    ∃ cuts : Finset ℝ,
      (∀ t : ℝ, t ∈ cuts ↔ t = 0 ∨ t = 1 ∨
        (t ∈ Set.Icc 0 1 ∧
          Vendored.RiemannDynamics.geodInterp
            (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈ B.exceptionalPoints)) ∧
      Vendored.RiemannDynamics.geodSeg
        (B.endpoints i.1).1 (B.endpoints i.1).2 =
        (fun t : ℝ => Vendored.RiemannDynamics.geodInterp
          (B.endpoints i.1).1 (B.endpoints i.1).2 t) '' (↑cuts : Set ℝ) ∪
        ⋃ e : DirichletParameterGap cuts,
          (fun t : ℝ => Vendored.RiemannDynamics.geodInterp
            (B.endpoints i.1).1 (B.endpoints i.1).2 t) ''
              Set.Ioo (e.left : ℝ) (e.right : ℝ) := by
  obtain ⟨cuts, hcuts⟩ := B.exists_finite_parameter_cuts i
  have hzero : (0 : ℝ) ∈ cuts := (hcuts 0).2 (Or.inl rfl)
  have hone : (1 : ℝ) ∈ cuts := (hcuts 1).2 (Or.inr (Or.inl rfl))
  have hbound : ∀ c ∈ cuts, c ∈ Set.Icc (0 : ℝ) 1 := by
    intro c hc
    rcases (hcuts c).1 hc with h0 | h1 | h
    · simp [h0]
    · simp [h1]
    · exact h.1
  refine ⟨cuts, hcuts, ?_⟩
  rw [Vendored.RiemannDynamics.geodSeg_eq_image_geodInterp]
  rw [icc_eq_cuts_union_gaps cuts hzero hone hbound,
    Set.image_union, Set.image_iUnion]

#print axioms exists_geodSeg_parameter_subdivision

/-- The interior of a gap between consecutive endpoint-and-exceptional cuts
contains no exceptional boundary point of the candidate section. -/
theorem gap_interior_not_exceptional
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B)
    (cuts : Finset ℝ)
    (hcuts : ∀ t : ℝ, t ∈ cuts ↔ t = 0 ∨ t = 1 ∨
      (t ∈ Set.Icc 0 1 ∧
        Vendored.RiemannDynamics.geodInterp
          (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈ B.exceptionalPoints))
    (e : DirichletParameterGap cuts) {u : ℝ}
    (hu : u ∈ Set.Ioo (e.left : ℝ) (e.right : ℝ)) :
    Vendored.RiemannDynamics.geodInterp
      (B.endpoints i.1).1 (B.endpoints i.1).2 u ∉ B.exceptionalPoints := by
  have hleft : (e.left : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    rcases (hcuts e.left.1).1 e.left.2 with h0 | h1 | h
    · simp [h0]
    · simp [h1]
    · exact h.1
  have hright : (e.right : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    rcases (hcuts e.right.1).1 e.right.2 with h0 | h1 | h
    · simp [h0]
    · simp [h1]
    · exact h.1
  exact B.geodInterp_not_exceptional_of_adjacent_cuts i cuts hcuts
    e.left.2 e.right.2 hleft.1 hright.2 e.left_lt_right e.adjacent u hu

#print axioms gap_interior_not_exceptional

/-- An interior point of one parameter gap lies on its given nondegenerate
candidate section and on no differently indexed nondegenerate section. -/
theorem gap_interior_unique_section
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B)
    (cuts : Finset ℝ)
    (hcuts : ∀ t : ℝ, t ∈ cuts ↔ t = 0 ∨ t = 1 ∨
      (t ∈ Set.Icc 0 1 ∧
        Vendored.RiemannDynamics.geodInterp
          (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈ B.exceptionalPoints))
    (e : DirichletParameterGap cuts) {u : ℝ}
    (hu : u ∈ Set.Ioo (e.left : ℝ) (e.right : ℝ)) :
    Vendored.RiemannDynamics.geodInterp
      (B.endpoints i.1).1 (B.endpoints i.1).2 u ∈
        Vendored.RiemannDynamics.geodSeg
          (B.endpoints i.1).1 (B.endpoints i.1).2 ∧
      ∀ j : NondegenerateIndex B,
        Vendored.RiemannDynamics.geodInterp
          (B.endpoints i.1).1 (B.endpoints i.1).2 u ∈
            Vendored.RiemannDynamics.geodSeg
              (B.endpoints j.1).1 (B.endpoints j.1).2 → j = i := by
  have hleft : (e.left : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    rcases (hcuts e.left.1).1 e.left.2 with h0 | h1 | h
    · simp [h0]
    · simp [h1]
    · exact h.1
  have hright : (e.right : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    rcases (hcuts e.right.1).1 e.right.2 with h0 | h1 | h
    · simp [h0]
    · simp [h1]
    · exact h.1
  have huIcc : u ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_trans hleft.1 (le_of_lt hu.1), le_trans (le_of_lt hu.2) hright.2⟩
  have huseg := Vendored.RiemannDynamics.geodInterp_mem_geodSeg
    (B.endpoints i.1).1 (B.endpoints i.1).2 huIcc
  have hfront := B.segment_subset_frontier i.1 huseg
  have hregular := B.gap_interior_not_exceptional i cuts hcuts e hu
  obtain ⟨k, hk, hunique⟩ :=
    B.existsUnique_nondegenerate_section_of_not_exceptional hfront hregular
  refine ⟨huseg, ?_⟩
  intro j hj
  exact (hunique j hj).trans (hunique i huseg).symm

#print axioms gap_interior_unique_section

end DirichletBoundarySegments

end SystolicGrowth
