module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.DirichletGapDisjointness

@[expose] public section

/-!
# Closed edges of the finite Dirichlet boundary subdivision

Consecutive parameter cuts determine closed geodesic subsegments. Their open
images are the regular frontier edges, while their cut endpoints lie in the
finite exceptional set. This does not supply global cyclic order.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane

namespace SystolicGrowth

/-- The image of a nonempty real open interval is dense in the image of its
closed interval under a continuous map to a Hausdorff space, when the latter
image is compact. -/
theorem closure_image_Ioo_eq_image_Icc
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (f : ℝ → Y) (hf : Continuous f) {l r : ℝ} (hlr : l < r) :
    closure (f '' Set.Ioo l r) = f '' Set.Icc l r := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · apply Set.image_mono
      intro t ht
      exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    · exact (isCompact_Icc.image hf).isClosed
  · rw [← closure_Ioo (ne_of_lt hlr)]
    exact image_closure_subset_closure_image hf

#print axioms closure_image_Ioo_eq_image_Icc

/-- A parameter subinterval of a nonconstant hyperbolic geodesic is exactly
the geodesic segment between its interpolated endpoints. -/
theorem geodInterp_image_Icc_eq_geodSeg
    (a b : ℍ) (hab : a ≠ b) {l r : ℝ} (hlr : l < r) :
    (fun t : ℝ => Vendored.RiemannDynamics.geodInterp a b t) '' Set.Icc l r =
      Vendored.RiemannDynamics.geodSeg
        (Vendored.RiemannDynamics.geodInterp a b l)
        (Vendored.RiemannDynamics.geodInterp a b r) := by
  let A := Vendored.RiemannDynamics.geodInterp a b l
  let C := Vendored.RiemannDynamics.geodInterp a b r
  let D := dist a b
  have hDpos : 0 < D := dist_pos.mpr hab
  have hDne : D ≠ 0 := hDpos.ne'
  have hdist_lr : dist A C = (r - l) * D := by
    dsimp [A, C, D]
    rw [Vendored.RiemannDynamics.dist_geodInterp_pair,
      abs_of_nonpos (sub_nonpos.mpr hlr.le)]
    ring
  have hforward {t : ℝ} (ht : t ∈ Set.Icc l r) :
      Vendored.RiemannDynamics.geodInterp a b t ∈
        Vendored.RiemannDynamics.geodSeg A C := by
    have hdist_lt : dist A (Vendored.RiemannDynamics.geodInterp a b t) =
        (t - l) * D := by
      dsimp [A, D]
      rw [Vendored.RiemannDynamics.dist_geodInterp_pair,
        abs_of_nonpos (sub_nonpos.mpr ht.1)]
      ring
    have hdist_tr : dist (Vendored.RiemannDynamics.geodInterp a b t) C =
        (r - t) * D := by
      dsimp [C, D]
      rw [Vendored.RiemannDynamics.dist_geodInterp_pair,
        abs_of_nonpos (sub_nonpos.mpr ht.2)]
      ring
    change dist A (Vendored.RiemannDynamics.geodInterp a b t) +
      dist (Vendored.RiemannDynamics.geodInterp a b t) C = dist A C
    rw [hdist_lt, hdist_tr, hdist_lr]
    ring
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact hforward ht
  · intro hz
    have hle : dist A z ≤ dist A C := by
      have hseg : dist A z + dist z C = dist A C := hz
      have hnonneg := dist_nonneg (x := z) (y := C)
      linarith
    let t : ℝ := l + dist A z / D
    have hqnonneg : 0 ≤ dist A z / D :=
      div_nonneg (dist_nonneg) hDpos.le
    have hqle : dist A z / D ≤ r - l :=
      (div_le_iff₀ hDpos).mpr (by rw [← hdist_lr]; exact hle)
    have htlo : l ≤ t := by dsimp [t]; linarith
    have hthi : t ≤ r := by dsimp [t]; linarith
    have hparam := hforward ⟨htlo, hthi⟩
    have hdist_at : dist A (Vendored.RiemannDynamics.geodInterp a b t) =
        (t - l) * D := by
      dsimp [A, D]
      rw [Vendored.RiemannDynamics.dist_geodInterp_pair,
        abs_of_nonpos (sub_nonpos.mpr htlo)]
      ring
    have htminus : t - l = dist A z / D := by dsimp [t]; ring
    have heqdist : dist A (Vendored.RiemannDynamics.geodInterp a b t) = dist A z := by
      rw [hdist_at, htminus]
      exact div_mul_cancel₀ _ hDne
    have heq := Vendored.RiemannDynamics.eq_of_mem_geodSeg_of_dist_eq
      hparam hz heqdist
    exact ⟨t, ⟨htlo, hthi⟩, heq⟩

#print axioms geodInterp_image_Icc_eq_geodSeg

namespace DirichletBoundarySegments

/-- The closed image of one consecutive pair of actual section cuts. -/
def closedEdgeImage
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (cuts : ∀ _i : NondegenerateIndex B, Finset ℝ)
    (s : DirichletOpenEdgeIndex B cuts) : Set ℍ :=
  (fun t : ℝ => Vendored.RiemannDynamics.geodInterp
    (B.endpoints s.1.1).1 (B.endpoints s.1.1).2 t) ''
      Set.Icc (s.2.left : ℝ) (s.2.right : ℝ)

/-- The two actual hyperbolic endpoints of a closed subdivided edge. -/
noncomputable def closedEdgeEndpoints
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (cuts : ∀ _i : NondegenerateIndex B, Finset ℝ)
    (s : DirichletOpenEdgeIndex B cuts) : ℍ × ℍ :=
  (Vendored.RiemannDynamics.geodInterp
      (B.endpoints s.1.1).1 (B.endpoints s.1.1).2 (s.2.left : ℝ),
    Vendored.RiemannDynamics.geodInterp
      (B.endpoints s.1.1).1 (B.endpoints s.1.1).2 (s.2.right : ℝ))

/-- The closed edge is exactly the closure of its regular open-edge image. -/
theorem closure_openEdgeImage_eq_closedEdgeImage
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (cuts : ∀ _i : NondegenerateIndex B, Finset ℝ)
    (s : DirichletOpenEdgeIndex B cuts) :
    closure (B.openEdgeImage cuts s) = B.closedEdgeImage cuts s := by
  have hpair : Continuous (fun t : ℝ =>
      ((B.endpoints s.1.1).1, (B.endpoints s.1.1).2, t)) := by fun_prop
  have hpath : Continuous (fun t : ℝ => Vendored.RiemannDynamics.geodInterp
      (B.endpoints s.1.1).1 (B.endpoints s.1.1).2 t) :=
    Vendored.RiemannDynamics.continuous_geodInterp.comp hpair
  exact closure_image_Ioo_eq_image_Icc _ hpath s.2.left_lt_right

#print axioms closure_openEdgeImage_eq_closedEdgeImage

/-- Each closed parameter edge is the genuine hyperbolic geodesic segment
between its two interpolated cut points. -/
theorem closedEdgeImage_eq_geodSeg
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (cuts : ∀ _i : NondegenerateIndex B, Finset ℝ)
    (s : DirichletOpenEdgeIndex B cuts) :
    B.closedEdgeImage cuts s =
      Vendored.RiemannDynamics.geodSeg
        (B.closedEdgeEndpoints cuts s).1 (B.closedEdgeEndpoints cuts s).2 := by
  exact geodInterp_image_Icc_eq_geodSeg _ _ s.1.2 s.2.left_lt_right

#print axioms closedEdgeImage_eq_geodSeg

/-- The interpolation of any actual endpoint-or-exceptional cut lies in the
finite exceptional boundary set. -/
theorem interp_mem_exceptional_of_mem_cut
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B)
    (cuts : Finset ℝ)
    (hcuts : ∀ t : ℝ, t ∈ cuts ↔ t = 0 ∨ t = 1 ∨
      (t ∈ Set.Icc 0 1 ∧ Vendored.RiemannDynamics.geodInterp
        (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈ B.exceptionalPoints))
    {t : ℝ} (ht : t ∈ cuts) :
    Vendored.RiemannDynamics.geodInterp
      (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈ B.exceptionalPoints := by
  rcases (hcuts t).1 ht with h0 | h1 | h
  · rw [h0, Vendored.RiemannDynamics.geodInterp_zero]
    exact Or.inl ⟨i.1, Or.inl rfl⟩
  · rw [h1, Vendored.RiemannDynamics.geodInterp_one]
    exact Or.inl ⟨i.1, Or.inr rfl⟩
  · exact h.2

#print axioms interp_mem_exceptional_of_mem_cut

/-- Both endpoints of each actual closed edge are exceptional points on the
Dirichlet frontier. -/
theorem closedEdgeEndpoints_exceptional_frontier
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (cuts : ∀ _i : NondegenerateIndex B, Finset ℝ)
    (hcuts : ∀ i : NondegenerateIndex B, ∀ t : ℝ,
      t ∈ cuts i ↔ t = 0 ∨ t = 1 ∨
        (t ∈ Set.Icc 0 1 ∧ Vendored.RiemannDynamics.geodInterp
          (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈ B.exceptionalPoints))
    (s : DirichletOpenEdgeIndex B cuts) :
    (B.closedEdgeEndpoints cuts s).1 ∈ B.exceptionalPoints ∧
      (B.closedEdgeEndpoints cuts s).2 ∈ B.exceptionalPoints ∧
      (B.closedEdgeEndpoints cuts s).1 ∈
        frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) ∧
      (B.closedEdgeEndpoints cuts s).2 ∈
        frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) := by
  have hleft := B.interp_mem_exceptional_of_mem_cut s.1 (cuts s.1)
    (hcuts s.1) s.2.left.2
  have hright := B.interp_mem_exceptional_of_mem_cut s.1 (cuts s.1)
    (hcuts s.1) s.2.right.2
  exact ⟨hleft, hright, B.exceptionalPoints_subset_frontier hleft,
    B.exceptionalPoints_subset_frontier hright⟩

#print axioms closedEdgeEndpoints_exceptional_frontier

end DirichletBoundarySegments

end SystolicGrowth
