module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.DirichletCyclicOrientation

@[expose] public section

/-!
# No interior corners on full Dirichlet sections

After a common-focus bisector is normalized to the vertical axis, every
other distance comparison is affine in the squared height. A comparison
which holds at both section endpoints cannot have an isolated equality
in the relative interior. Consequently the actual intrinsic corner cuts
of a nondegenerate full Dirichlet section are precisely its two endpoints.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane

namespace SystolicGrowth

private theorem axis_dist_le_iff {a c t : ℍ} (ht : t.re = 0) :
    dist t a ≤ dist t c ↔
      c.im * (a.re ^ 2 + t.im ^ 2 + a.im ^ 2) ≤
        a.im * (c.re ^ 2 + t.im ^ 2 + c.im ^ 2) := by
  have hcos : dist t a ≤ dist t c ↔
      Real.cosh (dist t a) ≤ Real.cosh (dist t c) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg]
  rw [hcos, UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist', ht,
    zero_sub, zero_sub, neg_sq, neg_sq]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  constructor
  · intro h
    have hfactor : (2 * t.im) *
        (c.im * (a.re ^ 2 + t.im ^ 2 + a.im ^ 2)) ≤
        (2 * t.im) *
        (a.im * (c.re ^ 2 + t.im ^ 2 + c.im ^ 2)) := by
      nlinarith only [h]
    exact le_of_mul_le_mul_left hfactor (by positivity : (0 : ℝ) < 2 * t.im)
  · intro h
    have hfactor := mul_le_mul_of_nonneg_left h
      (by positivity : (0 : ℝ) ≤ 2 * t.im)
    nlinarith only [hfactor]

private theorem axis_halfspace_interior_contact
    {a c u v z : ℍ} (hu : u.re = 0) (hv : v.re = 0)
    (hz : z ∈ Vendored.RiemannDynamics.geodSeg u v)
    (hzu : z ≠ u) (hzv : z ≠ v)
    (huq : dist u a ≤ dist u c) (hvq : dist v a ≤ dist v c)
    (hzq : dist z a = dist z c) :
    dist u a = dist u c ∧ dist v a = dist v c := by
  obtain ⟨hzre, hlo, hhi⟩ :=
    Vendored.RiemannDynamics.mem_geodSeg_vertical (hu.trans hv.symm) hz
  have hz0 : z.re = 0 := hzre.trans hu
  have hzim_u : z.im ≠ u.im := by
    intro h
    exact hzu (ext_re_im hzre h)
  have hzim_v : z.im ≠ v.im := by
    intro h
    exact hzv (ext_re_im (hz0.trans hv.symm) h)
  have hkeyu := (axis_dist_le_iff hu).mp huq
  have hkeyv := (axis_dist_le_iff hv).mp hvq
  have hkeyz : c.im * (a.re ^ 2 + z.im ^ 2 + a.im ^ 2) =
      a.im * (c.re ^ 2 + z.im ^ 2 + c.im ^ 2) := by
    apply le_antisymm
    · exact (axis_dist_le_iff hz0).mp hzq.le
    · exact (axis_dist_le_iff (a := c) (c := a) hz0).mp hzq.ge
  have hslope : c.im = a.im := by
    have hmul_u : (c.im - a.im) * (u.im ^ 2 - z.im ^ 2) ≤ 0 := by
      nlinarith only [hkeyu, hkeyz]
    have hmul_v : (c.im - a.im) * (v.im ^ 2 - z.im ^ 2) ≤ 0 := by
      nlinarith only [hkeyv, hkeyz]
    rcases le_total u.im v.im with huv | hvu
    · rw [min_eq_left huv] at hlo
      rw [max_eq_right huv] at hhi
      have hul : u.im < z.im := lt_of_le_of_ne hlo hzim_u.symm
      have hvr : z.im < v.im := lt_of_le_of_ne hhi hzim_v
      have hul_sq : u.im ^ 2 - z.im ^ 2 < 0 := by
        nlinarith [u.im_pos, z.im_pos]
      have hvr_sq : 0 < v.im ^ 2 - z.im ^ 2 := by
        nlinarith [v.im_pos, z.im_pos]
      have hnonneg : 0 ≤ c.im - a.im := by
        by_contra h
        exact (not_lt_of_ge hmul_u) (mul_pos_of_neg_of_neg (lt_of_not_ge h) hul_sq)
      have hnonpos : c.im - a.im ≤ 0 := by
        by_contra h
        exact (not_lt_of_ge hmul_v) (mul_pos (lt_of_not_ge h) hvr_sq)
      linarith
    · rw [min_eq_right hvu] at hlo
      rw [max_eq_left hvu] at hhi
      have hvl : v.im < z.im := lt_of_le_of_ne hlo hzim_v.symm
      have hur : z.im < u.im := lt_of_le_of_ne hhi hzim_u
      have hvl_sq : v.im ^ 2 - z.im ^ 2 < 0 := by
        nlinarith [v.im_pos, z.im_pos]
      have hur_sq : 0 < u.im ^ 2 - z.im ^ 2 := by
        nlinarith [u.im_pos, z.im_pos]
      have hnonneg : 0 ≤ c.im - a.im := by
        by_contra h
        exact (not_lt_of_ge hmul_v) (mul_pos_of_neg_of_neg (lt_of_not_ge h) hvl_sq)
      have hnonpos : c.im - a.im ≤ 0 := by
        by_contra h
        exact (not_lt_of_ge hmul_u) (mul_pos (lt_of_not_ge h) hur_sq)
      linarith
  have hkey (t : ℍ) : c.im * (a.re ^ 2 + t.im ^ 2 + a.im ^ 2) =
      a.im * (c.re ^ 2 + t.im ^ 2 + c.im ^ 2) := by
    rw [hslope] at hkeyz ⊢
    nlinarith only [hkeyz]
  constructor
  · apply le_antisymm
    · exact huq
    · exact (axis_dist_le_iff (a := c) (c := a) hu).mpr (hkey u).ge
  · apply le_antisymm
    · exact hvq
    · exact (axis_dist_le_iff (a := c) (c := a) hv).mpr (hkey v).ge

/-- A distinct common-focus bisector cannot touch the relative interior of
a nondegenerate bisector segment while its closed distance halfspace contains
both endpoints. The endpoint comparisons are sufficient; no convexity or
strict-corner premise is assumed. -/
theorem hyperbolic_bisector_halfspace_interior_contact
    {o p q u v z : ℍ} (hop : o ≠ p) (hoq : o ≠ q) (huv : u ≠ v)
    (hup : dist u o = dist u p) (hvp : dist v o = dist v p)
    (huq : dist u o ≤ dist u q) (hvq : dist v o ≤ dist v q)
    (hz : z ∈ Vendored.RiemannDynamics.geodSeg u v)
    (hzu : z ≠ u) (hzv : z ≠ v) (hzq : dist z o = dist z q) :
    p = q := by
  obtain ⟨A, him, hre, h0⟩ :=
    Vendored.RiemannDynamics.exists_mirror_normalizer hop
  have hu0 : (A • u).re = 0 :=
    (Vendored.RiemannDynamics.bisector_re_eq_zero him hre h0 u).mp hup
  have hv0 : (A • v).re = 0 :=
    (Vendored.RiemannDynamics.bisector_re_eq_zero him hre h0 v).mp hvp
  have hz' : A • z ∈ Vendored.RiemannDynamics.geodSeg (A • u) (A • v) := by
    rw [← Vendored.RiemannDynamics.smul_geodSeg]
    exact ⟨z, hz, rfl⟩
  have hzu' : A • z ≠ A • u := fun h => hzu (smul_left_cancel A h)
  have hzv' : A • z ≠ A • v := fun h => hzv (smul_left_cancel A h)
  have huq' : dist (A • u) (A • o) ≤ dist (A • u) (A • q) := by
    simpa only [dist_smul] using huq
  have hvq' : dist (A • v) (A • o) ≤ dist (A • v) (A • q) := by
    simpa only [dist_smul] using hvq
  have hzq' : dist (A • z) (A • o) = dist (A • z) (A • q) := by
    simpa only [dist_smul] using hzq
  have hcontact := axis_halfspace_interior_contact hu0 hv0 hz' hzu' hzv' huq' hvq' hzq'
  have huq_eq : dist u o = dist u q := by
    simpa only [dist_smul] using hcontact.1
  have hvq_eq : dist v o = dist v q := by
    simpa only [dist_smul] using hcontact.2
  exact hyperbolic_bisector_two_points_focus_unique hop hoq huv hup hvp huq_eq hvq_eq

namespace DirichletBoundarySegments

/-- A genuine full-group two-label corner on a nondegenerate full section
is one of that section's two endpoints. -/
theorem dirichletSectionCorner_eq_endpoint
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B)
    {z : ℍ}
    (hz : z ∈ Vendored.RiemannDynamics.geodSeg
      (B.endpoints i.1).1 (B.endpoints i.1).2)
    (hcorner : z ∈ X.dirichletSectionCorners o i.1.1) :
    z = (B.endpoints i.1).1 ∨ z = (B.endpoints i.1).2 := by
  by_contra hends
  have hzu : z ≠ (B.endpoints i.1).1 := fun h => hends (Or.inl h)
  have hzv : z ≠ (B.endpoints i.1).2 := fun h => hends (Or.inr h)
  obtain ⟨_, _, δ, hδone, hδi, hzδ⟩ := hcorner
  have hu : (B.endpoints i.1).1 ∈
      Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
        {z : ℍ | dist z o = dist z (i.1.1 • o)} := by
    rw [B.section_eq_segment i.1]
    exact Vendored.RiemannDynamics.left_mem_geodSeg _ _
  have hv : (B.endpoints i.1).2 ∈
      Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
        {z : ℍ | dist z o = dist z (i.1.1 • o)} := by
    rw [B.section_eq_segment i.1]
    exact Vendored.RiemannDynamics.right_mem_geodSeg _ _
  have hoi : o ≠ i.1.1 • o := by
    intro h
    exact (Finset.ne_of_mem_erase i.1.2.1) (X.free i.1.1 o h.symm)
  have hoδ : o ≠ δ • o := by
    intro h
    exact hδone (X.free δ o h.symm)
  have hfoci : i.1.1 • o = δ • o :=
    hyperbolic_bisector_halfspace_interior_contact hoi hoδ i.2 hu.2 hv.2
      ((Vendored.RiemannDynamics.mem_dirichletDomain.mp hu.1) δ)
      ((Vendored.RiemannDynamics.mem_dirichletDomain.mp hv.1) δ)
      hz hzu hzv hzδ
  have hfix : (i.1.1⁻¹ * δ) • o = o := by
    calc
      (i.1.1⁻¹ * δ) • o = i.1.1⁻¹ • (δ • o) := mul_smul _ _ _
      _ = i.1.1⁻¹ • (i.1.1 • o) := congrArg (fun w => i.1.1⁻¹ • w) hfoci.symm
      _ = o := inv_smul_smul _ _
  exact hδi (inv_mul_eq_one.mp (X.free _ o hfix)).symm

/-- The relative interior of a full nondegenerate Dirichlet section contains
no genuine two-label corner, with the second label ranging over the full
deck group. -/
theorem geodInterp_not_mem_dirichletSectionCorners
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    Vendored.RiemannDynamics.geodInterp
      (B.endpoints i.1).1 (B.endpoints i.1).2 t ∉
        X.dirichletSectionCorners o i.1.1 := by
  intro hcorner
  have hz := Vendored.RiemannDynamics.geodInterp_mem_geodSeg
    (B.endpoints i.1).1 (B.endpoints i.1).2 ⟨ht.1.le, ht.2.le⟩
  rcases B.dirichletSectionCorner_eq_endpoint i hz hcorner with hleft | hright
  · have h0 := geodInterp_injective_of_ne _ _ i.2
      (hleft.trans (Vendored.RiemannDynamics.geodInterp_zero _ _).symm)
    exact ht.1.ne' h0
  · have h1 := geodInterp_injective_of_ne _ _ i.2
      (hright.trans (Vendored.RiemannDynamics.geodInterp_one _ _).symm)
    exact ht.2.ne h1

/-- The actual intrinsic subdivision of a nondegenerate full section has
only its two endpoint cuts. Thus no collinear interior subdivision needs
to be merged before constructing a boundary-vertex fan. -/
theorem intrinsicCornerCuts_eq_endpoints
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B) :
    B.intrinsicCornerCuts i = {0, 1} := by
  classical
  ext t
  rw [B.mem_intrinsicCornerCuts_iff i t]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h0 | h1 | ⟨ht, hcorner⟩)
    · exact Or.inl h0
    · exact Or.inr h1
    · by_cases h0 : t = 0
      · exact Or.inl h0
      by_cases h1 : t = 1
      · exact Or.inr h1
      exact (B.geodInterp_not_mem_dirichletSectionCorners i
        ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩ hcorner).elim
  · rintro (h0 | h1)
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)

/-- The sole intrinsic gap on a full nondegenerate section runs from the
original parameter zero to the original parameter one. -/
theorem intrinsicCornerGap_endpoints
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (i : NondegenerateIndex B)
    (e : DirichletParameterGap (B.intrinsicCornerCuts i)) :
    (e.left : ℝ) = 0 ∧ (e.right : ℝ) = 1 := by
  have hl : (e.left : ℝ) ∈ ({0, 1} : Finset ℝ) := by
    simpa only [B.intrinsicCornerCuts_eq_endpoints i] using e.left.2
  have hr : (e.right : ℝ) ∈ ({0, 1} : Finset ℝ) := by
    simpa only [B.intrinsicCornerCuts_eq_endpoints i] using e.right.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl hr
  rcases hl with hl | hl <;> rcases hr with hr | hr
  · exact (e.left_lt_right.ne (hl.trans hr.symm)).elim
  · exact ⟨hl, hr⟩
  · have hlt := e.left_lt_right
    rw [hl, hr] at hlt
    norm_num at hlt
  · exact (e.left_lt_right.ne (hl.trans hr.symm)).elim

/-- Each existing intrinsic closed edge is the entire original Dirichlet
section, rather than a proper collinear subsegment. -/
theorem intrinsicClosedEdgeImage_eq_fullSection
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts) :
    B.closedEdgeImage B.intrinsicCornerCuts s =
      Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
        {z : ℍ | dist z o = dist z (s.1.1.1 • o)} := by
  obtain ⟨hl, hr⟩ := B.intrinsicCornerGap_endpoints s.1 s.2
  rw [B.section_eq_segment s.1.1, B.closedEdgeImage_eq_geodSeg]
  simp only [closedEdgeEndpoints, hl, hr, Vendored.RiemannDynamics.geodInterp_zero,
    Vendored.RiemannDynamics.geodInterp_one]

/-- The original deck label determines an actual intrinsic edge. In
particular the cyclic boundary has no consecutive pieces of the same full
section that would require a collinear merging step. -/
theorem intrinsicOpenEdge_label_injective
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    Function.Injective (fun s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts =>
      s.1.1.1) := by
  rintro ⟨i, e⟩ ⟨j, f⟩ hlabel
  have hij : i = j := Subtype.ext (Subtype.ext hlabel)
  subst j
  obtain ⟨hel, her⟩ := B.intrinsicCornerGap_endpoints i e
  obtain ⟨hfl, hfr⟩ := B.intrinsicCornerGap_endpoints i f
  have hef : e = f := DirichletParameterGap.ext
    (Subtype.ext (hel.trans hfl.symm)) (Subtype.ext (her.trans hfr.symm))
  subst f
  rfl

/-- Distinct positions in the constructed cyclic boundary have distinct
full-section labels. This is derived from the intrinsic cut computation,
not an irredundancy assumption. -/
theorem intrinsicCyclicEdge_label_injective
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    Function.Injective (fun i => (B.intrinsicCyclicEdge i).1.1.1) := by
  intro i j hij
  exact B.intrinsicCyclicEdge_injective (B.intrinsicOpenEdge_label_injective hij)

/-- The meeting point of two consecutive actual full sections is a genuine
two-label Dirichlet corner. Their distinctness follows from the computed
intrinsic cuts and the constructed cyclic enumeration. -/
theorem intrinsicCyclicVertex_next_mem_dirichletSectionCorners
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card i) ∈
      X.dirichletSectionCorners o (B.intrinsicCyclicEdge i).1.1.1 := by
  let j := finRotate B.intrinsicBoundaryRadialCuts.card i
  have hji : j ≠ i := by
    intro h
    exact B.intrinsicCyclicVertex_next_ne i
      (congrArg B.intrinsicCyclicVertex h.symm)
  have hzright : B.intrinsicCyclicVertex j ∈
      B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge i) := by
    rw [B.intrinsicCyclicEdge_closedImage_eq_geodSeg]
    exact Vendored.RiemannDynamics.right_mem_geodSeg _ _
  have hzleft : B.intrinsicCyclicVertex j ∈
      B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge j) := by
    rw [B.intrinsicCyclicEdge_closedImage_eq_geodSeg]
    exact Vendored.RiemannDynamics.left_mem_geodSeg _ _
  have hzsection := hzright
  rw [B.intrinsicClosedEdgeImage_eq_fullSection] at hzsection
  refine ⟨hzsection.1, hzsection.2, (B.intrinsicCyclicEdge j).1.1.1,
    Finset.ne_of_mem_erase (B.intrinsicCyclicEdge j).1.1.2.1, ?_, ?_⟩
  · exact fun h => hji (B.intrinsicCyclicEdge_label_injective h)
  · exact B.intrinsicCyclicClosedEdge_mem_bisector j hzleft

/-- Every nonincident cyclic vertex is strictly on the basepoint side of
the bisector supporting an actual full side. This is the strict supporting
inequality needed for triangles in the original boundary-vertex fan. -/
theorem intrinsicCyclicVertex_dist_lt_of_not_incident
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (i j : Fin B.intrinsicBoundaryRadialCuts.card)
    (hji : j ≠ i)
    (hjnext : j ≠ finRotate B.intrinsicBoundaryRadialCuts.card i) :
    dist (B.intrinsicCyclicVertex j) o <
      dist (B.intrinsicCyclicVertex j) ((B.intrinsicCyclicEdge i).1.1.1 • o) := by
  have hzleft : B.intrinsicCyclicVertex j ∈
      B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge j) := by
    rw [B.intrinsicCyclicEdge_closedImage_eq_geodSeg]
    exact Vendored.RiemannDynamics.left_mem_geodSeg _ _
  have hzD := hzleft
  rw [B.intrinsicClosedEdgeImage_eq_fullSection] at hzD
  have hle := (Vendored.RiemannDynamics.mem_dirichletDomain.mp hzD.1)
    (B.intrinsicCyclicEdge i).1.1.1
  apply lt_of_le_of_ne hle
  intro heq
  have hzside : B.intrinsicCyclicVertex j ∈
      B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge i) := by
    rw [B.intrinsicClosedEdgeImage_eq_fullSection]
    exact ⟨hzD.1, heq⟩
  have hzexc : B.intrinsicCyclicVertex j ∈ B.intrinsicExceptionalPoints := by
    rw [← B.range_intrinsicCyclicVertex_eq_intrinsicExceptionalPoints]
    exact ⟨j, rfl⟩
  rw [B.closedEdgeImage_eq_open_union_endpoints] at hzside
  have hzends := hzside.resolve_left (fun hopen =>
    (B.intrinsicOpenEdgeImage_subset_regular_frontier (B.intrinsicCyclicEdge i) hopen).2
      hzexc)
  change B.intrinsicCyclicVertex j ∈
    {(B.closedEdgeEndpoints B.intrinsicCornerCuts (B.intrinsicCyclicEdge i)).1,
      (B.closedEdgeEndpoints B.intrinsicCornerCuts (B.intrinsicCyclicEdge i)).2} at hzends
  rcases B.intrinsicCyclicEdge_endpoints_eq_or_swap i with hends | hends <;>
    rw [hends] at hzends <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzends
  · rcases hzends with hi | hn
    · exact hji (B.intrinsicCyclicVertex_injective hi)
    · exact hjnext (B.intrinsicCyclicVertex_injective hn)
  · rcases hzends with hn | hi
    · exact hjnext (B.intrinsicCyclicVertex_injective hn)
    · exact hji (B.intrinsicCyclicVertex_injective hi)

end DirichletBoundarySegments

#print axioms hyperbolic_bisector_halfspace_interior_contact
#print axioms DirichletBoundarySegments.dirichletSectionCorner_eq_endpoint
#print axioms DirichletBoundarySegments.geodInterp_not_mem_dirichletSectionCorners
#print axioms DirichletBoundarySegments.intrinsicCornerCuts_eq_endpoints
#print axioms DirichletBoundarySegments.intrinsicClosedEdgeImage_eq_fullSection
#print axioms DirichletBoundarySegments.intrinsicCyclicEdge_label_injective
#print axioms DirichletBoundarySegments.intrinsicCyclicVertex_next_mem_dirichletSectionCorners
#print axioms DirichletBoundarySegments.intrinsicCyclicVertex_dist_lt_of_not_incident

end SystolicGrowth
