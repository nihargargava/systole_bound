module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.DirichletClosedEdges

@[expose] public section

/-!
# Incidence of closed subdivided Dirichlet edges

An open edge acquires exactly its two cut endpoints on closure. Distinct
closed edges can intersect only at endpoints of both; no cyclic order or
vertex degree is asserted.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane

namespace SystolicGrowth

/-- The image of a real closed interval is its open-interval image together
with the images of its two endpoints. -/
theorem image_Icc_eq_image_Ioo_union_endpoints
    {Y : Type*} (f : ℝ → Y) {l r : ℝ} (hlr : l < r) :
    f '' Set.Icc l r = f '' Set.Ioo l r ∪ {f l, f r} := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    by_cases htl : t = l
    · subst t
      exact Or.inr (by simp)
    by_cases htr : t = r
    · subst t
      exact Or.inr (by simp)
    have htIoo : t ∈ Set.Ioo l r :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm htl), lt_of_le_of_ne ht.2 htr⟩
    exact Or.inl ⟨t, htIoo, rfl⟩
  · rintro (⟨t, ht, rfl⟩ | hz)
    · exact ⟨t, ⟨le_of_lt ht.1, le_of_lt ht.2⟩, rfl⟩
    · rcases (by simpa using hz : z = f l ∨ z = f r) with rfl | rfl
      · exact ⟨l, ⟨le_refl l, le_of_lt hlr⟩, rfl⟩
      · exact ⟨r, ⟨le_of_lt hlr, le_refl r⟩, rfl⟩

#print axioms image_Icc_eq_image_Ioo_union_endpoints

namespace DirichletBoundarySegments

/-- The two endpoint points of one indexed closed edge, as a finite set. -/
def closedEdgeEndpointSet
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (cuts : ∀ _i : NondegenerateIndex B, Finset ℝ)
    (s : DirichletOpenEdgeIndex B cuts) : Set ℍ :=
  {(B.closedEdgeEndpoints cuts s).1, (B.closedEdgeEndpoints cuts s).2}

/-- The two endpoint points of an indexed closed edge are distinct. -/
theorem closedEdgeEndpoints_ne
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (cuts : ∀ _i : NondegenerateIndex B, Finset ℝ)
    (s : DirichletOpenEdgeIndex B cuts) :
    (B.closedEdgeEndpoints cuts s).1 ≠ (B.closedEdgeEndpoints cuts s).2 := by
  intro heq
  have hparam := geodInterp_injective_of_ne
    (B.endpoints s.1.1).1 (B.endpoints s.1.1).2 s.1.2 heq
  exact (ne_of_lt s.2.left_lt_right) hparam

#print axioms closedEdgeEndpoints_ne

/-- A closed indexed edge consists exactly of its regular open image and its
two interpolated cut endpoints. -/
theorem closedEdgeImage_eq_open_union_endpoints
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (cuts : ∀ _i : NondegenerateIndex B, Finset ℝ)
    (s : DirichletOpenEdgeIndex B cuts) :
    B.closedEdgeImage cuts s =
      B.openEdgeImage cuts s ∪ B.closedEdgeEndpointSet cuts s := by
  exact image_Icc_eq_image_Ioo_union_endpoints _ s.2.left_lt_right

#print axioms closedEdgeImage_eq_open_union_endpoints

/-- Every point of a closed edge's endpoint pair lies in the finite
exceptional boundary set. -/
theorem closedEdgeEndpointSet_subset_exceptional
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (cuts : ∀ _i : NondegenerateIndex B, Finset ℝ)
    (hcuts : ∀ i : NondegenerateIndex B, ∀ t : ℝ,
      t ∈ cuts i ↔ t = 0 ∨ t = 1 ∨
        (t ∈ Set.Icc 0 1 ∧ Vendored.RiemannDynamics.geodInterp
          (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈ B.exceptionalPoints))
    (s : DirichletOpenEdgeIndex B cuts) :
    B.closedEdgeEndpointSet cuts s ⊆ B.exceptionalPoints := by
  intro z hz
  have hends := B.closedEdgeEndpoints_exceptional_frontier cuts hcuts s
  rcases (by simpa [closedEdgeEndpointSet] using hz :
      z = (B.closedEdgeEndpoints cuts s).1 ∨
        z = (B.closedEdgeEndpoints cuts s).2) with rfl | rfl
  · exact hends.1
  · exact hends.2.1

#print axioms closedEdgeEndpointSet_subset_exceptional

/-- Distinct closed indexed edges can meet only at points that are endpoints
of both. This does not bound vertex degree or impose a cyclic order. -/
theorem closedEdgeImage_inter_subset_endpointSets
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (cuts : ∀ _i : NondegenerateIndex B, Finset ℝ)
    (hcuts : ∀ i : NondegenerateIndex B, ∀ t : ℝ,
      t ∈ cuts i ↔ t = 0 ∨ t = 1 ∨
        (t ∈ Set.Icc 0 1 ∧ Vendored.RiemannDynamics.geodInterp
          (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈ B.exceptionalPoints))
    {s t : DirichletOpenEdgeIndex B cuts} (hst : s ≠ t) :
    B.closedEdgeImage cuts s ∩ B.closedEdgeImage cuts t ⊆
      B.closedEdgeEndpointSet cuts s ∩ B.closedEdgeEndpointSet cuts t := by
  intro z hz
  have hs := hz.1
  have ht := hz.2
  rw [B.closedEdgeImage_eq_open_union_endpoints] at hs ht
  have hse : z ∈ B.closedEdgeEndpointSet cuts s := by
    rcases hs with hso | hse
    · rcases ht with hto | hte
      · have hdisj : Disjoint (B.openEdgeImage cuts s) (B.openEdgeImage cuts t) :=
          (B.openEdgeImage_pairwise_disjoint cuts hcuts) hst
        exact ((Set.disjoint_left.mp hdisj) hso hto).elim
      · have hregular := B.openEdgeImage_subset_regular_frontier cuts hcuts s hso
        exact (hregular.2 (B.closedEdgeEndpointSet_subset_exceptional cuts hcuts t hte)).elim
    · exact hse
  have hte : z ∈ B.closedEdgeEndpointSet cuts t := by
    rcases ht with hto | hte
    · have hregular := B.openEdgeImage_subset_regular_frontier cuts hcuts t hto
      exact (hregular.2 (B.closedEdgeEndpointSet_subset_exceptional cuts hcuts s hse)).elim
    · exact hte
  exact ⟨hse, hte⟩

#print axioms closedEdgeImage_inter_subset_endpointSets

/-- The intersection of two distinct closed indexed edges is finite. -/
theorem closedEdgeImage_inter_finite
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (cuts : ∀ _i : NondegenerateIndex B, Finset ℝ)
    (hcuts : ∀ i : NondegenerateIndex B, ∀ t : ℝ,
      t ∈ cuts i ↔ t = 0 ∨ t = 1 ∨
        (t ∈ Set.Icc 0 1 ∧ Vendored.RiemannDynamics.geodInterp
          (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈ B.exceptionalPoints))
    {s t : DirichletOpenEdgeIndex B cuts} (hst : s ≠ t) :
    (B.closedEdgeImage cuts s ∩ B.closedEdgeImage cuts t).Finite := by
  have hfinite : (B.closedEdgeEndpointSet cuts s).Finite := by
    change (insert (B.closedEdgeEndpoints cuts s).1
      {(B.closedEdgeEndpoints cuts s).2} : Set ℍ).Finite
    exact Set.finite_insert.mpr (Set.finite_singleton _)
  exact hfinite.subset
    ((B.closedEdgeImage_inter_subset_endpointSets cuts hcuts hst).trans
      Set.inter_subset_left)

#print axioms closedEdgeImage_inter_finite

/-- Two distinct closed indexed edges share at most two endpoint points. -/
theorem closedEdgeImage_inter_ncard_le_two
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (cuts : ∀ _i : NondegenerateIndex B, Finset ℝ)
    (hcuts : ∀ i : NondegenerateIndex B, ∀ t : ℝ,
      t ∈ cuts i ↔ t = 0 ∨ t = 1 ∨
        (t ∈ Set.Icc 0 1 ∧ Vendored.RiemannDynamics.geodInterp
          (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈ B.exceptionalPoints))
    {s t : DirichletOpenEdgeIndex B cuts} (hst : s ≠ t) :
    (B.closedEdgeImage cuts s ∩ B.closedEdgeImage cuts t).ncard ≤ 2 := by
  have hfinite : (B.closedEdgeEndpointSet cuts s).Finite := by
    change (insert (B.closedEdgeEndpoints cuts s).1
      {(B.closedEdgeEndpoints cuts s).2} : Set ℍ).Finite
    exact Set.finite_insert.mpr (Set.finite_singleton _)
  have hsubset : B.closedEdgeImage cuts s ∩ B.closedEdgeImage cuts t ⊆
      B.closedEdgeEndpointSet cuts s :=
    (B.closedEdgeImage_inter_subset_endpointSets cuts hcuts hst).trans
      Set.inter_subset_left
  calc
    (B.closedEdgeImage cuts s ∩ B.closedEdgeImage cuts t).ncard ≤
        (B.closedEdgeEndpointSet cuts s).ncard := Set.ncard_le_ncard hsubset hfinite
    _ = 2 := by
      simpa [closedEdgeEndpointSet] using
        Set.ncard_pair (B.closedEdgeEndpoints_ne cuts s)

#print axioms closedEdgeImage_inter_ncard_le_two

end DirichletBoundarySegments

end SystolicGrowth
