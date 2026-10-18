module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.DirichletBoundaryIntersections

@[expose] public section

/-!
# Intersections of hyperbolic bisectors with a common focus

Two distinct nontrivial bisectors sharing a focus cannot have two points in
common. This is an ambient upper-half-plane statement; the finite Dirichlet
sections and any future polygonal reduction can use it without claiming a
cyclic ordering or excluding redundant labels.
-/

open UpperHalfPlane
open scoped Pointwise UpperHalfPlane

namespace SystolicGrowth

private theorem axis_bisector_two_points_focus_unique
    {a b c z w : ℍ}
    (him : b.im = a.im) (hre : b.re = -a.re)
    (hca : c ≠ a) (hza : z.re = 0) (hwa : w.re = 0) (hzw : z ≠ w)
    (hzc : dist z a = dist z c) (hwc : dist w a = dist w c) :
    c = b := by
  have axis_key (t : ℍ) (ht : t.re = 0) (h : dist t a = dist t c) :
      c.im * (a.re ^ 2 + t.im ^ 2 + a.im ^ 2) =
        a.im * (c.re ^ 2 + t.im ^ 2 + c.im ^ 2) := by
    have hc := congrArg Real.cosh h
    rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist'] at hc
    rw [ht, zero_sub, zero_sub] at hc
    have hdena : 2 * t.im * a.im ≠ 0 := by positivity
    have hdenc : 2 * t.im * c.im ≠ 0 := by positivity
    rw [div_eq_div_iff hdena hdenc] at hc
    have hfactor : (2 * t.im) *
        (c.im * (a.re ^ 2 + t.im ^ 2 + a.im ^ 2)) =
        (2 * t.im) *
        (a.im * (c.re ^ 2 + t.im ^ 2 + c.im ^ 2)) := by
      nlinarith only [hc]
    exact mul_left_cancel₀ (by positivity : (2 * t.im : ℝ) ≠ 0) hfactor
  have hzkey := axis_key z hza hzc
  have hwkey := axis_key w hwa hwc
  have hmul : (c.im - a.im) * (z.im ^ 2 - w.im ^ 2) = 0 := by
    linear_combination hzkey - hwkey
  have hneqim : z.im ≠ w.im := by
    intro h
    exact hzw (ext_re_im (hza.trans hwa.symm) h)
  have hneqsq : z.im ^ 2 ≠ w.im ^ 2 := by
    intro h
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp h) with h | h
    · exact hneqim h
    · nlinarith [z.im_pos, w.im_pos]
  have hcim : c.im = a.im := by
    rcases mul_eq_zero.mp hmul with h | h
    · linarith
    · exact (hneqsq (sub_eq_zero.mp h)).elim
  have hsq : a.re ^ 2 = c.re ^ 2 := by
    rw [hcim] at hzkey
    have hprod : a.im * (a.re ^ 2 - c.re ^ 2) = 0 := by
      nlinarith only [hzkey]
    have hzero := (mul_eq_zero.mp hprod).resolve_left a.im_pos.ne'
    linarith
  have hcre : c.re = -a.re := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with h | h
    · exfalso
      apply hca
      exact ext_re_im h.symm hcim
    · linarith
  exact ext_re_im (hcre.trans hre.symm) (hcim.trans him.symm)

/-- With a fixed first focus, two nontrivial hyperbolic bisectors sharing
two distinct points have the same second focus. In particular, different
second foci give an intersection with at most one point. -/
theorem hyperbolic_bisector_two_points_focus_unique
    {o p q z w : ℍ} (hop : o ≠ p) (hoq : o ≠ q) (hzw : z ≠ w)
    (hzp : dist z o = dist z p) (hwp : dist w o = dist w p)
    (hzq : dist z o = dist z q) (hwq : dist w o = dist w q) :
    p = q := by
  obtain ⟨g, him, hre, h0⟩ :=
    Vendored.RiemannDynamics.exists_mirror_normalizer hop
  have hz0 : (g • z).re = 0 :=
    (Vendored.RiemannDynamics.bisector_re_eq_zero him hre h0 z).mp hzp
  have hw0 : (g • w).re = 0 :=
    (Vendored.RiemannDynamics.bisector_re_eq_zero him hre h0 w).mp hwp
  have hqo : g • q ≠ g • o := by
    intro h
    exact hoq (smul_left_cancel g h).symm
  have hzw' : g • z ≠ g • w := by
    intro h
    exact hzw (smul_left_cancel g h)
  have hzq' : dist (g • z) (g • o) = dist (g • z) (g • q) := by
    simpa only [dist_smul] using hzq
  have hwq' : dist (g • w) (g • o) = dist (g • w) (g • q) := by
    simpa only [dist_smul] using hwq
  have h := axis_bisector_two_points_focus_unique him hre hqo hz0 hw0 hzw' hzq' hwq'
  exact (smul_left_cancel g h).symm

/-- Distinct nontrivial hyperbolic bisectors with a common focus have at most
one intersection point in the upper half-plane. -/
theorem hyperbolic_bisectors_inter_subsingleton
    {o p q : ℍ} (hop : o ≠ p) (hoq : o ≠ q) (hpq : p ≠ q) :
    ({z : ℍ | dist z o = dist z p} ∩
      {z : ℍ | dist z o = dist z q}).Subsingleton := by
  intro z hz w hw
  by_contra hzw
  exact hpq (hyperbolic_bisector_two_points_focus_unique
    hop hoq hzw hz.1 hw.1 hz.2 hw.2)

namespace DirichletBoundarySegments

/-- Distinct deck labels in the finite boundary package have bisector
sections with at most one common point. This does not assert that all
segments are polygon sides or that their intersections are vertices. -/
theorem distinct_sections_inter_subsingleton
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (i j : DirichletBoundarySegmentIndex X o B.radius) (hij : i ≠ j) :
    ((Vendored.RiemannDynamics.geodSeg
      (B.endpoints i).1 (B.endpoints i).2) ∩
      (Vendored.RiemannDynamics.geodSeg
        (B.endpoints j).1 (B.endpoints j).2)).Subsingleton := by
  have hione : i.1 ≠ 1 := Finset.ne_of_mem_erase i.2.1
  have hjone : j.1 ≠ 1 := Finset.ne_of_mem_erase j.2.1
  have hoi : o ≠ i.1 • o := by
    intro h
    exact hione (X.free i.1 o h.symm)
  have hoj : o ≠ j.1 • o := by
    intro h
    exact hjone (X.free j.1 o h.symm)
  have hfo : i.1 • o ≠ j.1 • o := by
    intro h
    have hfix : (i.1⁻¹ * j.1) • o = o := by
      calc
        (i.1⁻¹ * j.1) • o = i.1⁻¹ • (j.1 • o) := mul_smul _ _ _
        _ = i.1⁻¹ • (i.1 • o) := congrArg (fun z => i.1⁻¹ • z) h.symm
        _ = o := inv_smul_smul _ _
    have hlabels : i.1 = j.1 := inv_mul_eq_one.mp (X.free _ o hfix)
    exact hij (Subtype.ext hlabels)
  have hbis := hyperbolic_bisectors_inter_subsingleton hoi hoj hfo
  intro z hz w hw
  apply hbis
  · have hzi : z ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
        {x : ℍ | dist x o = dist x (i.1 • o)} := by
      rw [B.section_eq_segment i]
      exact hz.1
    have hzj : z ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
        {x : ℍ | dist x o = dist x (j.1 • o)} := by
      rw [B.section_eq_segment j]
      exact hz.2
    exact ⟨hzi.2, hzj.2⟩
  · have hwi : w ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
        {x : ℍ | dist x o = dist x (i.1 • o)} := by
      rw [B.section_eq_segment i]
      exact hw.1
    have hwj : w ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
        {x : ℍ | dist x o = dist x (j.1 • o)} := by
      rw [B.section_eq_segment j]
      exact hw.2
    exact ⟨hwi.2, hwj.2⟩

/-- All points shared by two differently labeled candidate sections form a
finite set. These are candidate vertices, not yet a cyclic vertex list. -/
theorem pairwise_intersection_points_finite
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    {z : ℍ | ∃ i j : DirichletBoundarySegmentIndex X o B.radius,
      i ≠ j ∧
      z ∈ Vendored.RiemannDynamics.geodSeg (B.endpoints i).1 (B.endpoints i).2 ∧
      z ∈ Vendored.RiemannDynamics.geodSeg (B.endpoints j).1 (B.endpoints j).2}.Finite := by
  classical
  let I := DirichletBoundarySegmentIndex X o B.radius
  let side (i : I) : Set ℍ :=
    Vendored.RiemannDynamics.geodSeg (B.endpoints i).1 (B.endpoints i).2
  let intersections : Set ℍ := ⋃ i : I, ⋃ j : I,
    if i = j then ∅ else side i ∩ side j
  have hintersections : intersections.Finite := by
    apply Set.finite_iUnion
    intro i
    apply Set.finite_iUnion
    intro j
    by_cases hij : i = j
    · simp [hij]
    · simpa [intersections, side, hij] using
        (B.distinct_sections_inter_subsingleton i j hij).finite
  apply hintersections.subset
  rintro z ⟨i, j, hij, hzi, hzj⟩
  change z ∈ ⋃ i : I, ⋃ j : I, if i = j then ∅ else side i ∩ side j
  simp only [Set.mem_iUnion]
  refine ⟨i, j, ?_⟩
  simp [side, hij, hzi, hzj]

end DirichletBoundarySegments

#print axioms hyperbolic_bisector_two_points_focus_unique
#print axioms hyperbolic_bisectors_inter_subsingleton
#print axioms DirichletBoundarySegments.distinct_sections_inter_subsingleton
#print axioms DirichletBoundarySegments.pairwise_intersection_points_finite

end SystolicGrowth
