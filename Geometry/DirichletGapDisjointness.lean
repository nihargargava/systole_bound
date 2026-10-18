module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.DirichletParameterSubdivision

@[expose] public section

/-!
# Disjoint interiors of subdivided Dirichlet sections

The open pieces of the finite per-section subdivision have disjoint images.
This is local incidence data, not a cyclic ordering or polygon side pairing.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane

namespace SystolicGrowth

namespace DirichletParameterGap

/-- A gap is determined by its two cut-subtype endpoints. -/
theorem ext {cuts : Finset ℝ} {e f : DirichletParameterGap cuts}
    (hleft : e.left = f.left) (hright : e.right = f.right) : e = f := by
  cases e with
  | mk el er _ _ =>
    cases f with
    | mk fl fr _ _ =>
      cases hleft
      cases hright
      rfl

/-- Distinct consecutive gaps in one finite cut set have disjoint open
parameter intervals. -/
theorem disjoint_Ioo_of_ne {cuts : Finset ℝ}
    (e f : DirichletParameterGap cuts) (hef : e ≠ f) :
    Disjoint (Set.Ioo (e.left : ℝ) (e.right : ℝ))
      (Set.Ioo (f.left : ℝ) (f.right : ℝ)) := by
  apply Set.disjoint_left.mpr
  intro t hte htf
  have hfl_le_el : (f.left : ℝ) ≤ e.left := by
    rcases e.adjacent f.left.1 f.left.2 with h | h
    · exact h
    · exact (not_le_of_gt (lt_trans htf.1 hte.2) h).elim
  have hel_le_fl : (e.left : ℝ) ≤ f.left := by
    rcases f.adjacent e.left.1 e.left.2 with h | h
    · exact h
    · exact (not_le_of_gt (lt_trans hte.1 htf.2) h).elim
  have her_le_fr : (e.right : ℝ) ≤ f.right := by
    rcases e.adjacent f.right.1 f.right.2 with h | h
    · exact (not_le_of_gt (lt_trans hte.1 htf.2) h).elim
    · exact h
  have hfr_le_er : (f.right : ℝ) ≤ e.right := by
    rcases f.adjacent e.right.1 e.right.2 with h | h
    · exact (not_le_of_gt (lt_trans htf.1 hte.2) h).elim
    · exact h
  have hleft : e.left = f.left := Subtype.ext (le_antisymm hel_le_fl hfl_le_el)
  have hright : e.right = f.right := Subtype.ext (le_antisymm her_le_fr hfr_le_er)
  exact hef (ext hleft hright)

#print axioms disjoint_Ioo_of_ne

end DirichletParameterGap

/-- Geodesic interpolation is injective in its parameter when the endpoints
are distinct. -/
theorem geodInterp_injective_of_ne (a b : ℍ) (hab : a ≠ b) :
    Function.Injective (Vendored.RiemannDynamics.geodInterp a b) := by
  intro s t hst
  have hd := Vendored.RiemannDynamics.dist_geodInterp_pair a b s t
  rw [hst, dist_self] at hd
  have hprod : |s - t| * dist a b = 0 := hd.symm
  have hdist : dist a b ≠ 0 := (dist_pos.mpr hab).ne'
  have hzero : |s - t| = 0 := (mul_eq_zero.mp hprod).resolve_right hdist
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

#print axioms geodInterp_injective_of_ne

namespace DirichletBoundarySegments

/-- Interior interpolation points of gaps on distinct candidate sections
cannot coincide. -/
theorem gap_interior_interp_ne_of_distinct_sections
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (i j : NondegenerateIndex B) (hij : i ≠ j)
    (cuts_i cuts_j : Finset ℝ)
    (hcuts_i : ∀ t : ℝ, t ∈ cuts_i ↔ t = 0 ∨ t = 1 ∨
      (t ∈ Set.Icc 0 1 ∧ Vendored.RiemannDynamics.geodInterp
        (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈ B.exceptionalPoints))
    (hcuts_j : ∀ t : ℝ, t ∈ cuts_j ↔ t = 0 ∨ t = 1 ∨
      (t ∈ Set.Icc 0 1 ∧ Vendored.RiemannDynamics.geodInterp
        (B.endpoints j.1).1 (B.endpoints j.1).2 t ∈ B.exceptionalPoints))
    (ei : DirichletParameterGap cuts_i) (ej : DirichletParameterGap cuts_j)
    {u v : ℝ} (hu : u ∈ Set.Ioo (ei.left : ℝ) (ei.right : ℝ))
    (hv : v ∈ Set.Ioo (ej.left : ℝ) (ej.right : ℝ)) :
    Vendored.RiemannDynamics.geodInterp
      (B.endpoints i.1).1 (B.endpoints i.1).2 u ≠
    Vendored.RiemannDynamics.geodInterp
      (B.endpoints j.1).1 (B.endpoints j.1).2 v := by
  intro heq
  have hi := (B.gap_interior_unique_section i cuts_i hcuts_i ei hu).2
  have hj := (B.gap_interior_unique_section j cuts_j hcuts_j ej hv).1
  have hj' : Vendored.RiemannDynamics.geodInterp
      (B.endpoints i.1).1 (B.endpoints i.1).2 u ∈
        Vendored.RiemannDynamics.geodSeg
          (B.endpoints j.1).1 (B.endpoints j.1).2 := by
    rw [heq]
    exact hj
  exact hij (hi j hj').symm

#print axioms gap_interior_interp_ne_of_distinct_sections

/-- Different gaps of one nondegenerate section have disjoint interpolated
open images. -/
theorem gap_images_disjoint_of_ne
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B)
    (cuts : Finset ℝ) (e f : DirichletParameterGap cuts) (hef : e ≠ f) :
    Disjoint
      ((fun u : ℝ => Vendored.RiemannDynamics.geodInterp
        (B.endpoints i.1).1 (B.endpoints i.1).2 u) ''
          Set.Ioo (e.left : ℝ) (e.right : ℝ))
      ((fun u : ℝ => Vendored.RiemannDynamics.geodInterp
        (B.endpoints i.1).1 (B.endpoints i.1).2 u) ''
          Set.Ioo (f.left : ℝ) (f.right : ℝ)) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨u, hu, rfl⟩ := hz
  obtain ⟨v, hv, heq⟩ := hz'
  have hvu : v = u :=
    geodInterp_injective_of_ne _ _ i.2 heq
  rw [hvu] at hv
  exact (Set.disjoint_left.mp (DirichletParameterGap.disjoint_Ioo_of_ne e f hef) hu) hv

#print axioms gap_images_disjoint_of_ne

/-- The finite index of open parameter gaps on all nondegenerate candidate
sections, for one choice of finite cuts on each section. -/
abbrev DirichletOpenEdgeIndex
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (cuts : ∀ _i : NondegenerateIndex B, Finset ℝ) :=
  Σ i : NondegenerateIndex B, DirichletParameterGap (cuts i)

/-- The actual hyperbolic image of one open parameter gap. -/
def openEdgeImage
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (cuts : ∀ _i : NondegenerateIndex B, Finset ℝ)
    (s : DirichletOpenEdgeIndex B cuts) : Set ℍ :=
  (fun u : ℝ => Vendored.RiemannDynamics.geodInterp
    (B.endpoints s.1.1).1 (B.endpoints s.1.1).2 u) ''
      Set.Ioo (s.2.left : ℝ) (s.2.right : ℝ)

/-- Distinct indexed open edges have disjoint images, for any family of the
actual endpoint-and-exceptional cut sets. -/
theorem openEdgeImage_pairwise_disjoint
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (cuts : ∀ _i : NondegenerateIndex B, Finset ℝ)
    (hcuts : ∀ i : NondegenerateIndex B, ∀ t : ℝ,
      t ∈ cuts i ↔ t = 0 ∨ t = 1 ∨
        (t ∈ Set.Icc 0 1 ∧ Vendored.RiemannDynamics.geodInterp
          (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈ B.exceptionalPoints)) :
    Pairwise (fun s t : DirichletOpenEdgeIndex B cuts =>
      Disjoint (B.openEdgeImage cuts s) (B.openEdgeImage cuts t)) := by
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
    exact B.gap_images_disjoint_of_ne i (cuts i) ei ej heij
  · apply Set.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨u, hu, hu_eq⟩ := hz
    obtain ⟨v, hv, hv_eq⟩ := hz'
    exact B.gap_interior_interp_ne_of_distinct_sections i j hij
      (cuts i) (cuts j) (hcuts i) (hcuts j) ei ej hu hv
        (hu_eq.trans hv_eq.symm)

#print axioms openEdgeImage_pairwise_disjoint

/-- There exists a finite family of actual open-edge images, indexed by
nondegenerate section labels and their consecutive cuts, with pairwise
disjoint interiors. No global cyclic polygon structure is asserted. -/
theorem exists_openEdgeImage_pairwise_disjoint
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    ∃ cuts : ∀ _i : NondegenerateIndex B, Finset ℝ,
      (∀ i : NondegenerateIndex B, ∀ t : ℝ,
        t ∈ cuts i ↔ t = 0 ∨ t = 1 ∨
          (t ∈ Set.Icc 0 1 ∧ Vendored.RiemannDynamics.geodInterp
            (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈ B.exceptionalPoints)) ∧
      Pairwise (fun s t : DirichletOpenEdgeIndex B cuts =>
        Disjoint (B.openEdgeImage cuts s) (B.openEdgeImage cuts t)) := by
  classical
  let cuts : ∀ i : NondegenerateIndex B, Finset ℝ :=
    fun i => Classical.choose (B.exists_finite_parameter_cuts i)
  have hcuts : ∀ i : NondegenerateIndex B, ∀ t : ℝ,
      t ∈ cuts i ↔ t = 0 ∨ t = 1 ∨
        (t ∈ Set.Icc 0 1 ∧ Vendored.RiemannDynamics.geodInterp
          (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈ B.exceptionalPoints) := by
    intro i t
    exact (Classical.choose_spec (B.exists_finite_parameter_cuts i)) t
  exact ⟨cuts, hcuts, B.openEdgeImage_pairwise_disjoint cuts hcuts⟩

#print axioms exists_openEdgeImage_pairwise_disjoint

/- TASK-SLOT GEOMETRY-REGULAR-EDGE-COVER: G06--G09 give the exact
regular-frontier cover by disjoint open-edge images; no cyclic order. -/

/-- The image of any actual parameter gap lies on the Dirichlet frontier
away from the finite exceptional set. -/
theorem openEdgeImage_subset_regular_frontier
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (cuts : ∀ _i : NondegenerateIndex B, Finset ℝ)
    (hcuts : ∀ i : NondegenerateIndex B, ∀ t : ℝ,
      t ∈ cuts i ↔ t = 0 ∨ t = 1 ∨
        (t ∈ Set.Icc 0 1 ∧ Vendored.RiemannDynamics.geodInterp
          (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈ B.exceptionalPoints))
    (s : DirichletOpenEdgeIndex B cuts) :
    B.openEdgeImage cuts s ⊆
      frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) \
        B.exceptionalPoints := by
  intro z hz
  obtain ⟨u, hu, rfl⟩ := hz
  have hseg : Vendored.RiemannDynamics.geodInterp
      (B.endpoints s.1.1).1 (B.endpoints s.1.1).2 u ∈
      Vendored.RiemannDynamics.geodSeg
        (B.endpoints s.1.1).1 (B.endpoints s.1.1).2 :=
    (B.gap_interior_unique_section s.1 (cuts s.1) (hcuts s.1) s.2 hu).1
  have hfront := B.segment_subset_frontier s.1.1 hseg
  have hregular := B.gap_interior_not_exceptional
    s.1 (cuts s.1) (hcuts s.1) s.2 hu
  exact ⟨hfront, hregular⟩

#print axioms openEdgeImage_subset_regular_frontier

/-- A parameter whose interpolation avoids the exceptional boundary set is
not one of the endpoint-or-exceptional cuts. -/
theorem regular_interp_not_mem_cuts
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B)
    (cuts : Finset ℝ)
    (hcuts : ∀ t : ℝ, t ∈ cuts ↔ t = 0 ∨ t = 1 ∨
      (t ∈ Set.Icc 0 1 ∧ Vendored.RiemannDynamics.geodInterp
        (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈ B.exceptionalPoints))
    {t : ℝ}
    (hregular : Vendored.RiemannDynamics.geodInterp
      (B.endpoints i.1).1 (B.endpoints i.1).2 t ∉ B.exceptionalPoints) :
    t ∉ cuts := by
  intro htcut
  rcases (hcuts t).1 htcut with ht0 | ht1 | htex
  · apply hregular
    have ha : Vendored.RiemannDynamics.geodInterp
        (B.endpoints i.1).1 (B.endpoints i.1).2 t = (B.endpoints i.1).1 := by
      simpa [ht0] using Vendored.RiemannDynamics.geodInterp_zero
        (B.endpoints i.1).1 (B.endpoints i.1).2
    exact Or.inl ⟨i.1, Or.inl ha⟩
  · apply hregular
    have hb : Vendored.RiemannDynamics.geodInterp
        (B.endpoints i.1).1 (B.endpoints i.1).2 t = (B.endpoints i.1).2 := by
      simpa [ht1] using Vendored.RiemannDynamics.geodInterp_one
        (B.endpoints i.1).1 (B.endpoints i.1).2
    exact Or.inl ⟨i.1, Or.inr hb⟩
  · exact hregular htex.2

#print axioms regular_interp_not_mem_cuts

/-- Every regular point of the Dirichlet frontier belongs to an actual open
edge image from the finite per-section subdivision. -/
theorem exists_openEdgeImage_of_mem_regular_frontier
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o z : ℍ}
    (B : DirichletBoundarySegments X o)
    (cuts : ∀ _i : NondegenerateIndex B, Finset ℝ)
    (hcuts : ∀ i : NondegenerateIndex B, ∀ t : ℝ,
      t ∈ cuts i ↔ t = 0 ∨ t = 1 ∨
        (t ∈ Set.Icc 0 1 ∧ Vendored.RiemannDynamics.geodInterp
          (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈ B.exceptionalPoints))
    (hz : z ∈ frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) \
      B.exceptionalPoints) :
    ∃ s : DirichletOpenEdgeIndex B cuts, z ∈ B.openEdgeImage cuts s := by
  obtain ⟨i, hzi, _⟩ :=
    B.existsUnique_nondegenerate_section_of_not_exceptional hz.1 hz.2
  rw [Vendored.RiemannDynamics.geodSeg_eq_image_geodInterp] at hzi
  obtain ⟨t, ht, htz⟩ := hzi
  have hregular : Vendored.RiemannDynamics.geodInterp
      (B.endpoints i.1).1 (B.endpoints i.1).2 t ∉ B.exceptionalPoints := by
    rw [htz]
    exact hz.2
  have hnot : t ∉ cuts i :=
    B.regular_interp_not_mem_cuts i (cuts i) (hcuts i) hregular
  have hzero : (0 : ℝ) ∈ cuts i := (hcuts i 0).2 (Or.inl rfl)
  have hone : (1 : ℝ) ∈ cuts i := (hcuts i 1).2 (Or.inr (Or.inl rfl))
  have ht0 : t ≠ 0 := by
    intro h
    exact hnot (h ▸ hzero)
  have ht1 : t ≠ 1 := by
    intro h
    exact hnot (h ▸ hone)
  have htIoo : t ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
  obtain ⟨l, r, hl, hr, _, _, hlt, htr, hadj⟩ :=
    exists_adjacent_cuts_around (cuts i) hzero hone htIoo hnot
  let e : DirichletParameterGap (cuts i) :=
    ⟨⟨l, hl⟩, ⟨r, hr⟩, lt_trans hlt htr, hadj⟩
  exact ⟨⟨i, e⟩, t, ⟨hlt, htr⟩, htz⟩

#print axioms exists_openEdgeImage_of_mem_regular_frontier

/-- The pairwise-disjoint indexed open-edge images cover exactly the regular
Dirichlet frontier. This remains a set-level statement, not a cyclic polygon. -/
theorem iUnion_openEdgeImage_eq_regular_frontier
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (cuts : ∀ _i : NondegenerateIndex B, Finset ℝ)
    (hcuts : ∀ i : NondegenerateIndex B, ∀ t : ℝ,
      t ∈ cuts i ↔ t = 0 ∨ t = 1 ∨
        (t ∈ Set.Icc 0 1 ∧ Vendored.RiemannDynamics.geodInterp
          (B.endpoints i.1).1 (B.endpoints i.1).2 t ∈ B.exceptionalPoints)) :
    (⋃ s : DirichletOpenEdgeIndex B cuts, B.openEdgeImage cuts s) =
      frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) \
        B.exceptionalPoints := by
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨s, hzs⟩ := Set.mem_iUnion.mp hz
    exact B.openEdgeImage_subset_regular_frontier cuts hcuts s hzs
  · intro z hz
    exact Set.mem_iUnion.mpr
      (B.exists_openEdgeImage_of_mem_regular_frontier cuts hcuts hz)

#print axioms iUnion_openEdgeImage_eq_regular_frontier

end DirichletBoundarySegments

end SystolicGrowth
