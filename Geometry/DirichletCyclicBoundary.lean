module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.DirichletIntrinsicEdges
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

@[expose] public section

/-!
# Radial positions of the actual Dirichlet boundary

The centre of the compact Dirichlet domain is interior. A point of its
frontier cannot occur before another point of the domain on a geodesic ray
from that centre: an active perpendicular bisector separates the centre
strictly from the opposite half-plane. The actual radial position map is a
homeomorphism from the frontier to the unit circle. The intrinsic exception
points determine a finite circle cutset, whose complement is exactly covered
by the radial images of the existing intrinsic open edges. A cyclic traversal
of that finite edge family is still a separate conclusion.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane

namespace SystolicGrowth

/-- On a nonvertical geodesic segment, its right endpoint is the unique
point with the right endpoint's real coordinate. -/
theorem geodSeg_eq_right_of_re_eq
    {a b z : ℍ} (hab : a.re ≠ b.re)
    (hz : z ∈ Vendored.RiemannDynamics.geodSeg a b) (hzre : z.re = b.re) : z = b := by
  have hzrad := Vendored.RiemannDynamics.mem_geodSeg_circle hab hz
  have hbrad := Vendored.RiemannDynamics.norm_sub_geodCenter hab
  have hsq : Complex.normSq
      ((z : ℂ) - (Vendored.RiemannDynamics.geodCenter a b : ℂ)) =
      Complex.normSq ((b : ℂ) - (Vendored.RiemannDynamics.geodCenter a b : ℂ)) := by
    rw [← Complex.sq_norm, ← Complex.sq_norm, hzrad, hbrad]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, UpperHalfPlane.coe_re,
    UpperHalfPlane.coe_im, sub_zero] at hsq
  rw [hzre] at hsq
  have hzim : z.im = b.im := by nlinarith [z.im_pos, b.im_pos]
  exact Vendored.RiemannDynamics.ext_re_im hzre hzim

/-- The disc-model chart at a fixed centre is continuous. -/
theorem continuous_discChart (o : ℍ) :
    Continuous (Vendored.RiemannDynamics.discChart o) := by
  have hfun : Vendored.RiemannDynamics.discChart o =
      (fun z : ℍ => ((z : ℂ) - (o : ℂ)) /
        ((z : ℂ) - (starRingEnd ℂ) (o : ℂ))) :=
    funext (Vendored.RiemannDynamics.discChart_eq o)
  rw [hfun]
  exact (UpperHalfPlane.continuous_coe.sub continuous_const).div
    (UpperHalfPlane.continuous_coe.sub continuous_const)
    (fun z => Vendored.RiemannDynamics.sub_conj_ne_zero o z)

/-- The disc-model chart determines the hyperbolic point. -/
theorem discChart_injective (o : ℍ) :
    Function.Injective (Vendored.RiemannDynamics.discChart o) := by
  intro z w h
  apply dist_eq_zero.mp
  rw [Vendored.RiemannDynamics.dist_eq_hDD o z w, h,
    Vendored.RiemannDynamics.hyperbolicDistDisk_self]

/-- The unit radial direction of a noncentral point, with the usual zero
value at the centre. The actual frontier never takes that zero value. -/
noncomputable def hyperbolicRadialDirection (o z : ℍ) : ℂ :=
  Vendored.RiemannDynamics.discChart o z /
    (‖Vendored.RiemannDynamics.discChart o z‖ : ℂ)

private theorem normalized_pos_mul (u : ℂ) {t : ℝ} (ht : 0 < t) :
    (t : ℂ) * u / (‖(t : ℂ) * u‖ : ℂ) = u / (‖u‖ : ℂ) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  push_cast
  exact mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr ht.ne')

/-- Radial direction is constant on the noncentral points of a geodesic ray. -/
theorem hyperbolicRadialDirection_eq_of_mem_geodSeg
    {o z w : ℍ} (hz : z ∈ Vendored.RiemannDynamics.geodSeg o w) (hzo : z ≠ o) :
    hyperbolicRadialDirection o z = hyperbolicRadialDirection o w := by
  obtain ⟨t, ht, hchart⟩ := Vendored.RiemannDynamics.discChart_smul_of_mem_geodSeg hz hzo
  unfold hyperbolicRadialDirection
  rw [hchart]
  exact normalized_pos_mul _ ht

/-- Two noncentral points with the same radial direction lie in their radial
norm order on one geodesic ray. The converse to the existing ray-chart lemma
uses the intermediate value theorem on the actual interpolation path. -/
theorem mem_geodSeg_of_radialDirection_eq_of_norm_le
    {o z w : ℍ} (hzo : z ≠ o)
    (hdir : hyperbolicRadialDirection o z = hyperbolicRadialDirection o w)
    (hnorm : ‖Vendored.RiemannDynamics.discChart o z‖ ≤
      ‖Vendored.RiemannDynamics.discChart o w‖) :
    z ∈ Vendored.RiemannDynamics.geodSeg o w := by
  let f : ℝ → ℍ := Vendored.RiemannDynamics.geodInterp o w
  have hf : Continuous f := Vendored.RiemannDynamics.continuous_geodInterp.comp
    (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  have hnormcont : Continuous (fun t : ℝ =>
      ‖Vendored.RiemannDynamics.discChart o (f t)‖) :=
    ((continuous_discChart o).comp hf).norm
  have htarget : ‖Vendored.RiemannDynamics.discChart o z‖ ∈ Set.Icc
      ‖Vendored.RiemannDynamics.discChart o (f 0)‖
      ‖Vendored.RiemannDynamics.discChart o (f 1)‖ := by
    simpa only [f, Vendored.RiemannDynamics.geodInterp_zero,
      Vendored.RiemannDynamics.geodInterp_one, Vendored.RiemannDynamics.discChart_self,
      norm_zero, Set.mem_Icc] using And.intro (norm_nonneg _) hnorm
  obtain ⟨t, ht, htnorm⟩ :=
    intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hnormcont.continuousOn htarget
  change ‖Vendored.RiemannDynamics.discChart o (f t)‖ =
    ‖Vendored.RiemannDynamics.discChart o z‖ at htnorm
  have htseg : f t ∈ Vendored.RiemannDynamics.geodSeg o w :=
    Vendored.RiemannDynamics.geodInterp_mem_geodSeg o w ht
  have hchartne : Vendored.RiemannDynamics.discChart o z ≠ 0 :=
    Vendored.RiemannDynamics.discChart_ne_zero hzo
  have hftne : f t ≠ o := by
    intro h
    rw [h, Vendored.RiemannDynamics.discChart_self, norm_zero] at htnorm
    exact hchartne (norm_eq_zero.mp htnorm.symm)
  have htdir := hyperbolicRadialDirection_eq_of_mem_geodSeg htseg hftne
  have hchart : Vendored.RiemannDynamics.discChart o (f t) =
      Vendored.RiemannDynamics.discChart o z := by
    have hquot := htdir.trans hdir.symm
    unfold hyperbolicRadialDirection at hquot
    rw [htnorm] at hquot
    exact (div_left_inj' (Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr hchartne).ne')).mp hquot
  rw [← discChart_injective o hchart]
  exact htseg

/-- Every point of the open unit disc is the chart of an actual hyperbolic
point at the chosen centre. The inverse is the existing Cayley transform,
followed by the inverse affine normalization. -/
theorem exists_discChart_eq (o : ℍ) {u : ℂ} (hu : ‖u‖ < 1) :
    ∃ w : ℍ, Vendored.RiemannDynamics.discChart o w = u := by
  have huBall : u ∈ Metric.ball (0 : ℂ) 1 := by
    rwa [Metric.mem_ball, dist_zero_right]
  let v : ℍ := Vendored.RiemannDynamics.diskToHalfPlane huBall
  let w : ℍ := ⟨(o.re : ℂ) + (o.im : ℂ) * (v : ℂ), by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, zero_mul, add_zero, zero_add, UpperHalfPlane.coe_im]
    exact mul_pos o.im_pos v.im_pos⟩
  refine ⟨w, ?_⟩
  have him : (o.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr o.im_pos.ne'
  have hnormal : ((w : ℂ) - (o.re : ℂ)) / (o.im : ℂ) = (v : ℂ) := by
    change (((o.re : ℂ) + (o.im : ℂ) * (v : ℂ)) - (o.re : ℂ)) /
      (o.im : ℂ) = (v : ℂ)
    field_simp
    ring
  unfold Vendored.RiemannDynamics.discChart
  rw [hnormal]
  exact Vendored.RiemannDynamics.halfPlaneToCayley_cayleyToHalfPlane huBall

namespace ClosedHyperbolicSurface

/-- A frontier point cannot precede another point of the Dirichlet domain on
a geodesic ray from the centre. The proof uses an actual active bisector,
not a star-shaped or cyclic-boundary assumption. -/
theorem frontier_point_eq_of_mem_basepoint_geodSeg
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) {z w : ℍ}
    (hz : z ∈ frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o))
    (hw : w ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)
    (hzw : z ∈ Vendored.RiemannDynamics.geodSeg o w) : z = w := by
  let B := X.dirichletBoundarySegments o
  have hz' := hz
  rw [B.frontier_eq_iUnion] at hz'
  obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz'
  have hsection : z ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
      {u : ℍ | dist u o = dist u (i.1 • o)} := by
    rw [B.section_eq_segment i]
    exact hzi
  have hpq : o ≠ i.1 • o := by
    intro hfix
    exact (Finset.ne_of_mem_erase i.2.1) (X.free i.1 o hfix.symm)
  obtain ⟨A, him, hre, h0⟩ := Vendored.RiemannDynamics.exists_mirror_normalizer hpq
  have hzre : (A • z).re = 0 :=
    (Vendored.RiemannDynamics.bisector_re_eq_zero him hre h0 z).mp hsection.2
  have hzseg : A • z ∈ Vendored.RiemannDynamics.geodSeg (A • o) (A • w) := by
    rw [← Vendored.RiemannDynamics.smul_geodSeg]
    exact ⟨z, hzw, rfl⟩
  have hbetw := Vendored.RiemannDynamics.re_mem_geodSeg hzseg
  have hwcomp : dist (A • w) (A • o) ≤ dist (A • w) (A • (i.1 • o)) := by
    simpa only [dist_smul] using
      (Vendored.RiemannDynamics.mem_dirichletDomain.mp hw) i.1
  have hmid : ((A • o).re + (A • (i.1 • o)).re) / 2 = 0 := by
    rw [hre]
    ring
  have hwre : (A • w).re = 0 := by
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · have hset := Vendored.RiemannDynamics.setOf_dist_le_eq_of_im_eq
        (a := A • o) (b := A • (i.1 • o)) him.symm (by rw [hre]; linarith)
      change A • w ∈ {u : ℍ | dist u (A • o) ≤ dist u (A • (i.1 • o))} at hwcomp
      rw [hset, hmid] at hwcomp
      change (A • w).re ≤ 0 at hwcomp
      by_contra hne
      have hwneg : (A • w).re < 0 := lt_of_le_of_ne hwcomp hne
      have hmax : max (A • o).re (A • w).re < 0 := max_lt hneg hwneg
      rw [hzre] at hbetw
      exact (not_lt_of_ge hbetw.2) hmax
    · have hset := Vendored.RiemannDynamics.setOf_dist_le_eq_of_im_eq'
        (a := A • o) (b := A • (i.1 • o)) him.symm (by rw [hre]; linarith)
      change A • w ∈ {u : ℍ | dist u (A • o) ≤ dist u (A • (i.1 • o))} at hwcomp
      rw [hset, hmid] at hwcomp
      change 0 ≤ (A • w).re at hwcomp
      by_contra hne
      have hwpos : 0 < (A • w).re := lt_of_le_of_ne hwcomp (Ne.symm hne)
      have hmin : 0 < min (A • o).re (A • w).re := lt_min hpos hwpos
      rw [hzre] at hbetw
      exact (not_lt_of_ge hbetw.1) hmin
  have hone : (A • o).re ≠ (A • w).re := by rwa [hwre]
  exact smul_left_cancel A
    (geodSeg_eq_right_of_re_eq hone hzseg (hzre.trans hwre.symm))

/-- Frontier points of the Dirichlet domain never coincide with its interior
centre. -/
theorem frontier_point_ne_basepoint
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) {z : ℍ}
    (hz : z ∈ frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)) :
    z ≠ o := by
  intro h
  rw [h] at hz
  exact Set.disjoint_left.mp disjoint_interior_frontier
    (X.basepoint_mem_interior_dirichletDomain o) hz

/-- Actual radial direction is injective on the entire Dirichlet frontier.
Equal directions put the points in norm order on one ray, whose domain exit
point is unique by the active-bisector argument. -/
theorem hyperbolicRadialDirection_injOn_frontier
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) :
    Set.InjOn (hyperbolicRadialDirection o)
      (frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)) := by
  intro z hz w hw hdir
  have hclosed := Vendored.RiemannDynamics.isClosed_dirichletDomain X.deckGroup o
  rcases le_total ‖Vendored.RiemannDynamics.discChart o z‖
      ‖Vendored.RiemannDynamics.discChart o w‖ with hzw | hwz
  · exact X.frontier_point_eq_of_mem_basepoint_geodSeg o hz (hclosed.frontier_subset hw)
      (mem_geodSeg_of_radialDirection_eq_of_norm_le
        (X.frontier_point_ne_basepoint o hz) hdir hzw)
  · exact (X.frontier_point_eq_of_mem_basepoint_geodSeg o hw (hclosed.frontier_subset hz)
      (mem_geodSeg_of_radialDirection_eq_of_norm_le
        (X.frontier_point_ne_basepoint o hw) hdir.symm hwz)).symm

/-- The actual radial position of a Dirichlet frontier point on the unit
circle. The centre is excluded by its proved interior membership. -/
noncomputable def dirichletBoundaryRadialPosition
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ)
    (z : frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)) : Circle :=
  ⟨hyperbolicRadialDirection o z.1, by
    apply mem_sphere_zero_iff_norm.mpr
    unfold hyperbolicRadialDirection
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_pos_iff.mpr
      (Vendored.RiemannDynamics.discChart_ne_zero
        (X.frontier_point_ne_basepoint o z.2))).ne'⟩

/-- The actual frontier-to-circle position map is continuous. -/
theorem continuous_dirichletBoundaryRadialPosition
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) :
    Continuous (X.dirichletBoundaryRadialPosition o) := by
  apply Continuous.subtype_mk
  have hchart : Continuous (fun z : frontier
      (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) =>
      Vendored.RiemannDynamics.discChart o z.1) :=
    (continuous_discChart o).comp continuous_subtype_val
  exact hchart.div (Complex.continuous_ofReal.comp hchart.norm) (fun z =>
    Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr
      (Vendored.RiemannDynamics.discChart_ne_zero
        (X.frontier_point_ne_basepoint o z.2))).ne')

/-- Distinct actual frontier points have distinct unit-circle positions. -/
theorem dirichletBoundaryRadialPosition_injective
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) :
    Function.Injective (X.dirichletBoundaryRadialPosition o) := by
  intro z w h
  apply Subtype.ext
  exact X.hyperbolicRadialDirection_injOn_frontier o z.2 w.2
    (congrArg (fun x : Circle => (x : ℂ)) h)

/-- Every radial unit-circle direction is attained by a point of the
Dirichlet frontier. A short initial ray lies in the proved interior ball;
compactness supplies its terminal frontier point. -/
theorem dirichletBoundaryRadialPosition_surjective
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) :
    Function.Surjective (X.dirichletBoundaryRadialPosition o) := by
  intro ξ
  have hu : ‖(1 / 2 : ℂ) * (ξ : ℂ)‖ < 1 := by
    rw [norm_mul, Circle.norm_coe, mul_one]
    norm_num
  obtain ⟨w, hwchart⟩ := exists_discChart_eq o hu
  have hwne : w ≠ o := by
    intro h
    rw [h, Vendored.RiemannDynamics.discChart_self] at hwchart
    exact (mul_ne_zero (by norm_num : (1 / 2 : ℂ) ≠ 0) ξ.coe_ne_zero) hwchart.symm
  have hdpos : 0 < dist o w := dist_pos.mpr hwne.symm
  obtain ⟨ε, hεpos, hball⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp (X.basepoint_mem_interior_dirichletDomain o))
  let t : ℝ := min (1 / 2) (ε / (2 * dist o w))
  have htpos : 0 < t := lt_min (by norm_num) (div_pos hεpos (by positivity))
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨htpos.le, (min_le_left _ _).trans (by norm_num)⟩
  let y : ℍ := Vendored.RiemannDynamics.geodInterp o w t
  have hdist : dist o y = t * dist o w :=
    Vendored.RiemannDynamics.dist_geodInterp_left o w htIcc
  have hyne : y ≠ o := by
    intro h
    rw [h, dist_self] at hdist
    exact (mul_pos htpos hdpos).ne' hdist.symm
  have hyball : y ∈ Metric.ball o ε := by
    rw [Metric.mem_ball, dist_comm, hdist]
    have htbound : t ≤ ε / (2 * dist o w) := min_le_right _ _
    have htd : t * dist o w ≤ ε / 2 := by
      have h := (le_div_iff₀ (by positivity : 0 < 2 * dist o w)).mp htbound
      nlinarith
    linarith
  have hyD : y ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o := hball hyball
  obtain ⟨K, hK, hcover⟩ := X.exists_compact_covering
  have hcompact := X.isCompact_dirichletDomain_of_compact_covering o K hK hcover
  obtain ⟨b, hb, hyb⟩ := exists_mem_frontier_geodSeg_of_isCompact hcompact hyD hyne
  refine ⟨⟨b, hb⟩, ?_⟩
  apply Circle.ext
  change hyperbolicRadialDirection o b = (ξ : ℂ)
  calc
    hyperbolicRadialDirection o b = hyperbolicRadialDirection o y :=
      (hyperbolicRadialDirection_eq_of_mem_geodSeg hyb hyne).symm
    _ = hyperbolicRadialDirection o w :=
      hyperbolicRadialDirection_eq_of_mem_geodSeg
        (Vendored.RiemannDynamics.geodInterp_mem_geodSeg o w htIcc) hyne
    _ = (ξ : ℂ) := by
      unfold hyperbolicRadialDirection
      rw [hwchart]
      simpa [Circle.norm_coe] using
        normalized_pos_mul (ξ : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)

/-- The actual compact Dirichlet frontier is homeomorphic to the radial
unit circle. This is proved from the domain and its centre, not supplied as
a polygon or cyclic-order hypothesis. -/
noncomputable def dirichletBoundaryRadialHomeomorph
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) :
    frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) ≃ₜ Circle := by
  have hfrontcompact : IsCompact
      (frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)) := by
    obtain ⟨K, hK, hcover⟩ := X.exists_compact_covering
    have hcompact := X.isCompact_dirichletDomain_of_compact_covering o K hK hcover
    exact hcompact.of_isClosed_subset isClosed_frontier
      (Vendored.RiemannDynamics.isClosed_dirichletDomain X.deckGroup o).frontier_subset
  letI : CompactSpace (frontier
      (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)) :=
    isCompact_iff_compactSpace.mp hfrontcompact
  exact IsHomeomorph.homeomorph (X.dirichletBoundaryRadialPosition o)
    (isHomeomorph_iff_continuous_bijective.mpr
      ⟨X.continuous_dirichletBoundaryRadialPosition o,
        X.dirichletBoundaryRadialPosition_injective o,
        X.dirichletBoundaryRadialPosition_surjective o⟩)

/-- The radial boundary homeomorphism uses the actual radial position map. -/
@[simp] theorem dirichletBoundaryRadialHomeomorph_apply
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ)
    (z : frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)) :
    X.dirichletBoundaryRadialHomeomorph o z = X.dirichletBoundaryRadialPosition o z := rfl

#print axioms frontier_point_eq_of_mem_basepoint_geodSeg
#print axioms hyperbolicRadialDirection_injOn_frontier
#print axioms dirichletBoundaryRadialPosition_surjective
#print axioms dirichletBoundaryRadialHomeomorph

end ClosedHyperbolicSurface

namespace DirichletBoundarySegments

/-- The finite positions on the radial unit circle of the actual intrinsic
exception points. No circle cuts or cyclic ordering are given as a premise. -/
noncomputable def intrinsicBoundaryRadialCuts
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) : Finset Circle :=
  ((B.intrinsicExceptionalPoints_finite.image (hyperbolicRadialDirection o)).preimage
    Circle.coe_injective.injOn).toFinset

/-- Exact membership in the actual radial cutset. -/
theorem mem_intrinsicBoundaryRadialCuts_iff
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (ξ : Circle) :
    ξ ∈ B.intrinsicBoundaryRadialCuts ↔
      ∃ z ∈ B.intrinsicExceptionalPoints, hyperbolicRadialDirection o z = (ξ : ℂ) := by
  unfold intrinsicBoundaryRadialCuts
  exact Set.Finite.mem_toFinset _

/-- Every radial cut position identifies exactly one intrinsic exception
point. The injectivity follows from the actual frontier ray uniqueness. -/
theorem existsUnique_intrinsicException_of_mem_radialCuts
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) {ξ : Circle}
    (hξ : ξ ∈ B.intrinsicBoundaryRadialCuts) :
    ∃! z : ℍ, z ∈ B.intrinsicExceptionalPoints ∧
      hyperbolicRadialDirection o z = (ξ : ℂ) := by
  obtain ⟨z, hz, hzξ⟩ := (B.mem_intrinsicBoundaryRadialCuts_iff ξ).mp hξ
  refine ⟨z, ⟨hz, hzξ⟩, ?_⟩
  intro w hw
  exact X.hyperbolicRadialDirection_injOn_frontier o
    (B.intrinsicExceptionalPoints_subset_frontier hw.1)
    (B.intrinsicExceptionalPoints_subset_frontier hz) (hw.2.trans hzξ.symm)

/-- The existing actual intrinsic edge images cover exactly the complement
of their finite radial cutset on the whole unit circle. This is coverage of
the actual pieces, not an assumed cyclic enumeration or arc adjacency. -/
theorem not_mem_intrinsicBoundaryRadialCuts_iff_exists_openEdge
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) (ξ : Circle) :
    ξ ∉ B.intrinsicBoundaryRadialCuts ↔
      ∃ s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts,
        (ξ : ℂ) ∈ hyperbolicRadialDirection o '' B.openEdgeImage B.intrinsicCornerCuts s := by
  constructor
  · intro hξ
    obtain ⟨z, hzξ⟩ := X.dirichletBoundaryRadialPosition_surjective o ξ
    have hdir : hyperbolicRadialDirection o z.1 = (ξ : ℂ) :=
      congrArg (fun x : Circle => (x : ℂ)) hzξ
    have hznot : z.1 ∉ B.intrinsicExceptionalPoints := by
      intro hz
      exact hξ ((B.mem_intrinsicBoundaryRadialCuts_iff ξ).mpr ⟨z.1, hz, hdir⟩)
    obtain ⟨s, hzs⟩ :=
      B.exists_intrinsicOpenEdgeImage_of_mem_regular_frontier ⟨z.2, hznot⟩
    exact ⟨s, z.1, hzs, hdir⟩
  · rintro ⟨s, z, hzs, hzξ⟩ hξ
    obtain ⟨w, hw, hwξ⟩ := (B.mem_intrinsicBoundaryRadialCuts_iff ξ).mp hξ
    have hzreg := B.intrinsicOpenEdgeImage_subset_regular_frontier s hzs
    have hzw : z = w := X.hyperbolicRadialDirection_injOn_frontier o hzreg.1
      (B.intrinsicExceptionalPoints_subset_frontier hw) (hzξ.trans hwξ.symm)
    exact hzreg.2 (hzw ▸ hw)

#print axioms existsUnique_intrinsicException_of_mem_radialCuts
#print axioms not_mem_intrinsicBoundaryRadialCuts_iff_exists_openEdge

end DirichletBoundarySegments

#print axioms geodSeg_eq_right_of_re_eq
#print axioms mem_geodSeg_of_radialDirection_eq_of_norm_le

end SystolicGrowth

namespace SystolicGrowth.DirichletBoundarySegments

/-- An actual intrinsic open edge is connected, since its defining
nonempty parameter gap is connected and geodesic interpolation is continuous. -/
theorem isConnected_intrinsicOpenEdgeImage
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts) :
    IsConnected (B.openEdgeImage B.intrinsicCornerCuts s) := by
  have hpath : Continuous (fun t : ℝ => Vendored.RiemannDynamics.geodInterp
      (B.endpoints s.1.1).1 (B.endpoints s.1.1).2 t) :=
    Vendored.RiemannDynamics.continuous_geodInterp.comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  exact (isConnected_Ioo s.2.left_lt_right).image _ hpath.continuousOn

/-- In the regular frontier, a closed intrinsic edge has exactly its open
edge points: both deleted endpoints are genuine intrinsic exceptions. -/
theorem intrinsicOpenEdgeImage_eq_closedEdgeImage_inter_regularFrontier
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts) :
    B.openEdgeImage B.intrinsicCornerCuts s =
      B.closedEdgeImage B.intrinsicCornerCuts s ∩
        (frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) \
          B.intrinsicExceptionalPoints) := by
  apply Set.Subset.antisymm
  · intro z hz
    refine ⟨?_, B.intrinsicOpenEdgeImage_subset_regular_frontier s hz⟩
    rw [B.closedEdgeImage_eq_open_union_endpoints]
    exact Or.inl hz
  · intro z hz
    rw [B.closedEdgeImage_eq_open_union_endpoints] at hz
    exact hz.1.resolve_right (fun he => hz.2.2
      (B.intrinsicClosedEdgeEndpointSet_subset_exceptional s he))

/-- The actual finite edge partition is clopen relative to the regular
frontier. Closedness uses the actual closed segments; openness uses the
finite union of all the other closed segments and exact frontier coverage. -/
theorem isClopen_intrinsicOpenEdge_preimage_regularFrontier
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts) :
    IsClopen ((↑) ⁻¹' B.openEdgeImage B.intrinsicCornerCuts s :
      Set ↥(frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) \
        B.intrinsicExceptionalPoints)) := by
  classical
  let R := frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) \
    B.intrinsicExceptionalPoints
  let A (t : DirichletOpenEdgeIndex B B.intrinsicCornerCuts) : Set R :=
    (↑) ⁻¹' B.closedEdgeImage B.intrinsicCornerCuts t
  have hA (t : DirichletOpenEdgeIndex B B.intrinsicCornerCuts) : IsClosed (A t) := by
    dsimp [A]
    rw [← B.closure_openEdgeImage_eq_closedEdgeImage]
    exact isClosed_closure.preimage continuous_subtype_val
  have heq (t : DirichletOpenEdgeIndex B B.intrinsicCornerCuts) :
      ((↑) ⁻¹' B.openEdgeImage B.intrinsicCornerCuts t : Set R) = A t := by
    ext z
    rw [B.intrinsicOpenEdgeImage_eq_closedEdgeImage_inter_regularFrontier]
    exact and_iff_left z.2
  have hcompl : (A s)ᶜ =
      ⋃ t : DirichletOpenEdgeIndex B B.intrinsicCornerCuts,
        if t = s then ∅ else A t := by
    ext z
    constructor
    · intro hz
      obtain ⟨t, hzt⟩ := B.exists_intrinsicOpenEdgeImage_of_mem_regular_frontier z.2
      have hts : t ≠ s := by
        intro hts
        subst t
        exact hz ((heq s) ▸ hzt)
      exact Set.mem_iUnion.mpr ⟨t, by simpa [hts] using ((heq t) ▸ hzt)⟩
    · intro hz hzs
      obtain ⟨t, hzt⟩ := Set.mem_iUnion.mp hz
      by_cases hts : t = s
      · simp [hts] at hzt
      · have hzt' : z.1 ∈ B.openEdgeImage B.intrinsicCornerCuts t :=
          (show z ∈ (↑) ⁻¹' B.openEdgeImage B.intrinsicCornerCuts t from
            (heq t).symm ▸ (by simpa [hts] using hzt))
        have hzs' : z.1 ∈ B.openEdgeImage B.intrinsicCornerCuts s :=
          (show z ∈ (↑) ⁻¹' B.openEdgeImage B.intrinsicCornerCuts s from
            (heq s).symm ▸ hzs)
        exact Set.disjoint_left.mp (B.intrinsicOpenEdgeImage_pairwise_disjoint hts)
          hzt' hzs'
  have hcomplclosed : IsClosed (A s)ᶜ := by
    rw [hcompl]
    exact isClosed_iUnion_of_finite (fun t => by
      split_ifs <;> first | exact isClosed_empty | exact hA t)
  rw [heq s]
  exact ⟨hA s, by simpa only [compl_compl] using hcomplclosed.isOpen_compl⟩

/-- Every intrinsic open edge is a whole connected component of the actual
frontier after its finite intrinsic exception set is deleted. -/
theorem connectedComponentIn_regularFrontier_eq_intrinsicOpenEdge
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o z : ℍ}
    (B : DirichletBoundarySegments X o)
    (s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts)
    (hz : z ∈ B.openEdgeImage B.intrinsicCornerCuts s) :
    connectedComponentIn
        (frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) \
          B.intrinsicExceptionalPoints) z =
      B.openEdgeImage B.intrinsicCornerCuts s := by
  let R := frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) \
    B.intrinsicExceptionalPoints
  have hzR : z ∈ R := B.intrinsicOpenEdgeImage_subset_regular_frontier s hz
  apply Set.Subset.antisymm
  · rw [connectedComponentIn_eq_image hzR]
    rintro w ⟨v, hv, rfl⟩
    exact isPreconnected_connectedComponent.subset_isClopen
      (B.isClopen_intrinsicOpenEdge_preimage_regularFrontier s)
      ⟨(⟨z, hzR⟩ : R), mem_connectedComponent, hz⟩ hv
  · exact (B.isConnected_intrinsicOpenEdgeImage s).isPreconnected.subset_connectedComponentIn
      hz (B.intrinsicOpenEdgeImage_subset_regular_frontier s)

#print axioms connectedComponentIn_regularFrontier_eq_intrinsicOpenEdge

end SystolicGrowth.DirichletBoundarySegments

namespace SystolicGrowth

/-- A connected open circle subset whose closed completion adds exactly
two distinct endpoints is one of the two directed arcs between them. -/
private theorem circle_open_connected_eq_arc_or_reverse
    {P Q : Set Circle} {a b : Circle} (hab : a ≠ b)
    (hP : IsConnected P) (hPo : IsOpen P) (hQc : IsClosed Q)
    (hQ : Q = P ∪ {a, b}) (hPe : Disjoint P {a, b}) :
    P = Circle.path a b '' Set.Ioo 0 1 ∨ P = Circle.path b a '' Set.Ioo 0 1 := by
  have hfill {x y : Circle} (hxy : x ≠ y) (heq : {x, y} = ({a, b} : Set Circle))
      (hsub : P ⊆ Set.range (Circle.path x y)) :
      P = Circle.path x y '' Set.Ioo 0 1 := by
    let U := Circle.path x y '' Set.Ioo 0 1
    have hPU : P ⊆ U := by
      rw [show U = (Set.range (Circle.path y x))ᶜ from
        (Circle.compl_range_path hxy.symm).symm]
      intro ξ hξ hξrev
      have hξe : ξ ∈ ({a, b} : Set Circle) := by
        rw [← heq, ← Circle.range_path_inter_range_path hxy]
        exact ⟨hsub hξ, hξrev⟩
      exact Set.disjoint_left.mp hPe hξ hξe
    have hUconn : IsConnected U :=
      (isConnected_Ioo (by exact zero_lt_one : (0 : unitInterval) < 1)).image _
        (Circle.path x y).continuous.continuousOn
    have hUe : Disjoint U {a, b} := by
      rw [← heq]
      apply Set.disjoint_left.mpr
      rintro ξ ⟨t, ht, rfl⟩ hξ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hξ
      rcases hξ with hξ | hξ
      · have htzero := (Circle.path_injective_of_ne hxy)
          (hξ.trans (Circle.path x y).source.symm)
        exact ht.1.ne' htzero
      · have htone := (Circle.path_injective_of_ne hxy)
          (hξ.trans (Circle.path x y).target.symm)
        exact ht.2.ne htone
    have heqQ : ((↑) ⁻¹' P : Set U) = (↑) ⁻¹' Q := by
      ext ξ
      rw [hQ]
      exact (or_iff_left (fun hξ => Set.disjoint_left.mp hUe ξ.2 hξ)).symm
    have hclopen : IsClopen ((↑) ⁻¹' P : Set U) :=
      ⟨heqQ ▸ hQc.preimage continuous_subtype_val,
        hPo.preimage continuous_subtype_val⟩
    have hUpre : IsPreconnected (Set.univ : Set U) := by
      rw [← Topology.IsInducing.subtypeVal.isPreconnected_image,
        Set.image_univ, Subtype.range_val]
      exact hUconn.isPreconnected
    obtain ⟨ξ, hξ⟩ := hP.nonempty
    have hUP := hUpre.subset_isClopen hclopen
      ⟨(⟨ξ, hPU hξ⟩ : U), Set.mem_univ _, hξ⟩
    exact hPU.antisymm (fun ζ hζ => hUP (Set.mem_univ (⟨ζ, hζ⟩ : U)))
  have hdisj : P ∩ (Set.range (Circle.path a b) ∩ Set.range (Circle.path b a)) = ∅ := by
    rw [Circle.range_path_inter_range_path hab]
    exact hPe.inter_eq
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hP.isPreconnected
      (Set.range (Circle.path a b)) (Set.range (Circle.path b a))
      (isCompact_range (Circle.path a b).continuous).isClosed
      (isCompact_range (Circle.path b a).continuous).isClosed
      (by rw [Circle.range_path_union_range_path hab]; exact Set.subset_univ _) hdisj with
      hsub | hsub
  · exact Or.inl (hfill hab rfl hsub)
  · exact Or.inr (hfill hab.symm (Set.pair_comm b a) hsub)

end SystolicGrowth

namespace SystolicGrowth.ClosedHyperbolicSurface

/-- The actual radial homeomorphism sends a frontier subset to precisely
its previously defined radial image, viewed as a subset of `Circle`. -/
theorem image_radialHomeomorph_preimage_of_subset_frontier
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) {S : Set ℍ}
    (hS : S ⊆ frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)) :
    X.dirichletBoundaryRadialHomeomorph o '' ((↑) ⁻¹' S) =
      ((↑) ⁻¹' (hyperbolicRadialDirection o '' S) : Set Circle) := by
  ext ξ
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.1, hz, rfl⟩
  · rintro ⟨z, hz, hzξ⟩
    exact ⟨⟨z, hS hz⟩, hz, Circle.coe_injective hzξ⟩

end SystolicGrowth.ClosedHyperbolicSurface

namespace SystolicGrowth.DirichletBoundarySegments

/-- Radial positions of an actual intrinsic open edge form a connected
subset of the circle, using the actual frontier homeomorphism. -/
theorem isConnected_intrinsicOpenEdgeRadialImage
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts) :
    IsConnected ((↑) ⁻¹' (hyperbolicRadialDirection o ''
      B.openEdgeImage B.intrinsicCornerCuts s) : Set Circle) := by
  have hsub : B.openEdgeImage B.intrinsicCornerCuts s ⊆
      frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) :=
    fun _ hz => (B.intrinsicOpenEdgeImage_subset_regular_frontier s hz).1
  rw [← X.image_radialHomeomorph_preimage_of_subset_frontier o hsub]
  apply (X.dirichletBoundaryRadialHomeomorph o).isConnected_image.mpr
  refine ⟨?_, Topology.IsInducing.subtypeVal.isPreconnected_image.mp ?_⟩
  · obtain ⟨z, hz⟩ := B.intrinsicOpenEdgeImage_nonempty s
    exact ⟨⟨z, hsub hz⟩, hz⟩
  · rw [Subtype.image_preimage_coe, inter_eq_right.mpr hsub]
    exact (B.isConnected_intrinsicOpenEdgeImage s).isPreconnected

/-- The radial image of an actual closed intrinsic edge is closed in the
circle. It is the homeomorphic image of its closed frontier subset. -/
theorem isClosed_intrinsicClosedEdgeRadialImage
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts) :
    IsClosed ((↑) ⁻¹' (hyperbolicRadialDirection o ''
      B.closedEdgeImage B.intrinsicCornerCuts s) : Set Circle) := by
  have hsub : B.closedEdgeImage B.intrinsicCornerCuts s ⊆
      frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) := by
    rw [← B.closure_openEdgeImage_eq_closedEdgeImage]
    exact closure_minimal
      (fun _ hz => (B.intrinsicOpenEdgeImage_subset_regular_frontier s hz).1)
      isClosed_frontier
  rw [← X.image_radialHomeomorph_preimage_of_subset_frontier o hsub]
  apply (X.dirichletBoundaryRadialHomeomorph o).isClosedMap
  rw [← B.closure_openEdgeImage_eq_closedEdgeImage]
  exact isClosed_closure.preimage continuous_subtype_val

/-- Radial positions of each actual open edge are open in the whole
circle, not merely relatively open in the regular frontier. -/
theorem isOpen_intrinsicOpenEdgeRadialImage
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts) :
    IsOpen ((↑) ⁻¹' (hyperbolicRadialDirection o ''
      B.openEdgeImage B.intrinsicCornerCuts s) : Set Circle) := by
  let F := frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)
  let R := F \ B.intrinsicExceptionalPoints
  have hsub : B.openEdgeImage B.intrinsicCornerCuts s ⊆ F :=
    fun _ hz => (B.intrinsicOpenEdgeImage_subset_regular_frontier s hz).1
  rw [← X.image_radialHomeomorph_preimage_of_subset_frontier o hsub]
  apply (X.dirichletBoundaryRadialHomeomorph o).isOpenMap
  obtain ⟨U, hU, hUeq⟩ :=
    (Topology.IsInducing.isOpen_iff (f := (Subtype.val : R → ℍ))
      Topology.IsInducing.subtypeVal).mp
    (B.isClopen_intrinsicOpenEdge_preimage_regularFrontier s).isOpen
  have heq : ((↑) ⁻¹' B.openEdgeImage B.intrinsicCornerCuts s : Set F) =
      (↑) ⁻¹' (U \ B.intrinsicExceptionalPoints) := by
    ext z
    constructor
    · intro hz
      have hzR : z.1 ∈ R := B.intrinsicOpenEdgeImage_subset_regular_frontier s hz
      exact ⟨show z.1 ∈ U from
        (show (⟨z.1, hzR⟩ : R) ∈ (↑) ⁻¹' U from
          hUeq.symm ▸ (show (⟨z.1, hzR⟩ : R) ∈
            (↑) ⁻¹' B.openEdgeImage B.intrinsicCornerCuts s from hz)), hzR.2⟩
    · intro hz
      have hzR : z.1 ∈ R := ⟨z.2, hz.2⟩
      exact show (⟨z.1, hzR⟩ : R) ∈
          (↑) ⁻¹' B.openEdgeImage B.intrinsicCornerCuts s from
        hUeq ▸ (show (⟨z.1, hzR⟩ : R) ∈ (↑) ⁻¹' U from hz.1)
  rw [heq]
  exact (IsOpen.inter hU B.intrinsicExceptionalPoints_finite.isClosed.isOpen_compl).preimage
    continuous_subtype_val

#print axioms isConnected_intrinsicOpenEdgeRadialImage
#print axioms isOpen_intrinsicOpenEdgeRadialImage

end SystolicGrowth.DirichletBoundarySegments

namespace SystolicGrowth.DirichletBoundarySegments

/-- The actual radial open edge is exactly one of the two directed circle
arcs between its two actual endpoints. No arc or cyclic ordering is supplied
as a geometric premise. -/
theorem intrinsicOpenEdgeRadialImage_eq_arc_or_reverse
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts) :
    let a := X.dirichletBoundaryRadialHomeomorph o
      ⟨(B.closedEdgeEndpoints B.intrinsicCornerCuts s).1,
        (B.intrinsicClosedEdgeEndpoints_exceptional_frontier s).2.2.1⟩
    let b := X.dirichletBoundaryRadialHomeomorph o
      ⟨(B.closedEdgeEndpoints B.intrinsicCornerCuts s).2,
        (B.intrinsicClosedEdgeEndpoints_exceptional_frontier s).2.2.2⟩
    ((↑) ⁻¹' (hyperbolicRadialDirection o ''
        B.openEdgeImage B.intrinsicCornerCuts s) : Set Circle) =
      Circle.path a b '' Set.Ioo 0 1 ∨
    ((↑) ⁻¹' (hyperbolicRadialDirection o ''
        B.openEdgeImage B.intrinsicCornerCuts s) : Set Circle) =
      Circle.path b a '' Set.Ioo 0 1 := by
  let H := X.dirichletBoundaryRadialHomeomorph o
  let a : Circle := H ⟨(B.closedEdgeEndpoints B.intrinsicCornerCuts s).1,
    (B.intrinsicClosedEdgeEndpoints_exceptional_frontier s).2.2.1⟩
  let b : Circle := H ⟨(B.closedEdgeEndpoints B.intrinsicCornerCuts s).2,
    (B.intrinsicClosedEdgeEndpoints_exceptional_frontier s).2.2.2⟩
  let P : Set Circle := (↑) ⁻¹' (hyperbolicRadialDirection o ''
    B.openEdgeImage B.intrinsicCornerCuts s)
  let Q : Set Circle := (↑) ⁻¹' (hyperbolicRadialDirection o ''
    B.closedEdgeImage B.intrinsicCornerCuts s)
  have hab : a ≠ b := by
    intro heq
    have hends := congrArg Subtype.val (H.injective heq)
    exact B.closedEdgeEndpoints_ne B.intrinsicCornerCuts s hends
  have hacut : a ∈ B.intrinsicBoundaryRadialCuts :=
    (B.mem_intrinsicBoundaryRadialCuts_iff a).mpr
      ⟨_, (B.intrinsicClosedEdgeEndpoints_exceptional_frontier s).1, rfl⟩
  have hbcut : b ∈ B.intrinsicBoundaryRadialCuts :=
    (B.mem_intrinsicBoundaryRadialCuts_iff b).mpr
      ⟨_, (B.intrinsicClosedEdgeEndpoints_exceptional_frontier s).2.1, rfl⟩
  have hPcut : ∀ ξ ∈ P, ξ ∉ B.intrinsicBoundaryRadialCuts := by
    intro ξ hξ
    exact (B.not_mem_intrinsicBoundaryRadialCuts_iff_exists_openEdge ξ).mpr ⟨s, hξ⟩
  have hPe : Disjoint P {a, b} := by
    apply Set.disjoint_left.mpr
    intro ξ hξ he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl
    · exact hPcut a hξ hacut
    · exact hPcut b hξ hbcut
  have hQ : Q = P ∪ {a, b} := by
    ext ξ
    constructor
    · rintro ⟨z, hz, hzξ⟩
      rw [B.closedEdgeImage_eq_open_union_endpoints] at hz
      rcases hz with hz | hz
      · exact Or.inl ⟨z, hz, hzξ⟩
      · simp only [closedEdgeEndpointSet, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact Or.inr (Or.inl (Circle.coe_injective hzξ).symm)
        · exact Or.inr (Or.inr (Circle.coe_injective hzξ).symm)
    · rintro (hξ | he)
      · obtain ⟨z, hz, hzξ⟩ := hξ
        refine ⟨z, ?_, hzξ⟩
        rw [B.closedEdgeImage_eq_open_union_endpoints]
        exact Or.inl hz
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
        rcases he with rfl | rfl
        · refine ⟨(B.closedEdgeEndpoints B.intrinsicCornerCuts s).1, ?_, rfl⟩
          rw [B.closedEdgeImage_eq_open_union_endpoints]
          exact Or.inr (by simp [closedEdgeEndpointSet])
        · refine ⟨(B.closedEdgeEndpoints B.intrinsicCornerCuts s).2, ?_, rfl⟩
          rw [B.closedEdgeImage_eq_open_union_endpoints]
          exact Or.inr (by simp [closedEdgeEndpointSet])
  exact circle_open_connected_eq_arc_or_reverse hab
    (B.isConnected_intrinsicOpenEdgeRadialImage s) (B.isOpen_intrinsicOpenEdgeRadialImage s)
    (B.isClosed_intrinsicClosedEdgeRadialImage s) hQ hPe

/-- Each actual edge joins distinct intrinsic radial cuts by a directed arc
whose interior contains no further intrinsic radial cut: actual adjacency. -/
theorem exists_intrinsicOpenEdgeRadialImage_adjacent_arc
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts) :
    ∃ a ∈ B.intrinsicBoundaryRadialCuts, ∃ b ∈ B.intrinsicBoundaryRadialCuts,
      a ≠ b ∧
      ((↑) ⁻¹' (hyperbolicRadialDirection o ''
        B.openEdgeImage B.intrinsicCornerCuts s) : Set Circle) =
        Circle.path a b '' Set.Ioo 0 1 ∧
      Disjoint (Circle.path a b '' Set.Ioo 0 1)
        (↑B.intrinsicBoundaryRadialCuts : Set Circle) := by
  let H := X.dirichletBoundaryRadialHomeomorph o
  let a : Circle := H ⟨(B.closedEdgeEndpoints B.intrinsicCornerCuts s).1,
    (B.intrinsicClosedEdgeEndpoints_exceptional_frontier s).2.2.1⟩
  let b : Circle := H ⟨(B.closedEdgeEndpoints B.intrinsicCornerCuts s).2,
    (B.intrinsicClosedEdgeEndpoints_exceptional_frontier s).2.2.2⟩
  have hab : a ≠ b := fun heq => B.closedEdgeEndpoints_ne B.intrinsicCornerCuts s
    (congrArg Subtype.val (H.injective heq))
  have ha : a ∈ B.intrinsicBoundaryRadialCuts :=
    (B.mem_intrinsicBoundaryRadialCuts_iff a).mpr
      ⟨_, (B.intrinsicClosedEdgeEndpoints_exceptional_frontier s).1, rfl⟩
  have hb : b ∈ B.intrinsicBoundaryRadialCuts :=
    (B.mem_intrinsicBoundaryRadialCuts_iff b).mpr
      ⟨_, (B.intrinsicClosedEdgeEndpoints_exceptional_frontier s).2.1, rfl⟩
  have hdisj : Disjoint
      ((↑) ⁻¹' (hyperbolicRadialDirection o ''
        B.openEdgeImage B.intrinsicCornerCuts s) : Set Circle)
      (↑B.intrinsicBoundaryRadialCuts : Set Circle) := by
    apply Set.disjoint_left.mpr
    intro ξ hξ hcut
    exact ((B.not_mem_intrinsicBoundaryRadialCuts_iff_exists_openEdge ξ).mpr
      ⟨s, hξ⟩) hcut
  rcases B.intrinsicOpenEdgeRadialImage_eq_arc_or_reverse s with h | h
  · exact ⟨a, ha, b, hb, hab, h, h ▸ hdisj⟩
  · exact ⟨b, hb, a, ha, hab.symm, h, h ▸ hdisj⟩

#print axioms intrinsicOpenEdgeRadialImage_eq_arc_or_reverse
#print axioms exists_intrinsicOpenEdgeRadialImage_adjacent_arc

end SystolicGrowth.DirichletBoundarySegments

namespace SystolicGrowth.DirichletBoundarySegments

/-- Each actual radial open edge is a whole connected component of the
circle minus the finite intrinsic radial cuts. Together with the directed
arc theorem this identifies the actual adjacent complementary arcs. -/
theorem connectedComponentIn_radialCutComplement_eq_intrinsicOpenEdge
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (s : DirichletOpenEdgeIndex B B.intrinsicCornerCuts) {ξ : Circle}
    (hξ : (ξ : ℂ) ∈ hyperbolicRadialDirection o ''
      B.openEdgeImage B.intrinsicCornerCuts s) :
    connectedComponentIn (↑B.intrinsicBoundaryRadialCuts : Set Circle)ᶜ ξ =
      ((↑) ⁻¹' (hyperbolicRadialDirection o ''
        B.openEdgeImage B.intrinsicCornerCuts s) : Set Circle) := by
  let R : Set Circle := (↑B.intrinsicBoundaryRadialCuts : Set Circle)ᶜ
  let P : Set Circle := (↑) ⁻¹' (hyperbolicRadialDirection o ''
    B.openEdgeImage B.intrinsicCornerCuts s)
  let Q : Set Circle := (↑) ⁻¹' (hyperbolicRadialDirection o ''
    B.closedEdgeImage B.intrinsicCornerCuts s)
  have hPR : P ⊆ R := fun ζ hζ =>
    (B.not_mem_intrinsicBoundaryRadialCuts_iff_exists_openEdge ζ).mpr ⟨s, hζ⟩
  have heq : ((↑) ⁻¹' P : Set R) = (↑) ⁻¹' Q := by
    ext ζ
    constructor
    · rintro ⟨z, hz, hzζ⟩
      refine ⟨z, ?_, hzζ⟩
      rw [B.closedEdgeImage_eq_open_union_endpoints]
      exact Or.inl hz
    · rintro ⟨z, hz, hzζ⟩
      rw [B.closedEdgeImage_eq_open_union_endpoints] at hz
      rcases hz with hz | he
      · exact ⟨z, hz, hzζ⟩
      · exact (ζ.2 ((B.mem_intrinsicBoundaryRadialCuts_iff ζ.1).mpr
          ⟨z, B.intrinsicClosedEdgeEndpointSet_subset_exceptional s he, hzζ⟩)).elim
  have hclopen : IsClopen ((↑) ⁻¹' P : Set R) := by
    refine ⟨?_, (B.isOpen_intrinsicOpenEdgeRadialImage s).preimage continuous_subtype_val⟩
    rw [heq]
    exact (B.isClosed_intrinsicClosedEdgeRadialImage s).preimage continuous_subtype_val
  have hξR : ξ ∈ R := hPR hξ
  apply Set.Subset.antisymm
  · rw [connectedComponentIn_eq_image hξR]
    rintro ζ ⟨v, hv, rfl⟩
    exact isPreconnected_connectedComponent.subset_isClopen hclopen
      ⟨(⟨ξ, hξR⟩ : R), mem_connectedComponent, hξ⟩ hv
  · exact (B.isConnected_intrinsicOpenEdgeRadialImage s).isPreconnected.subset_connectedComponentIn
      hξ hPR

#print axioms connectedComponentIn_radialCutComplement_eq_intrinsicOpenEdge

end SystolicGrowth.DirichletBoundarySegments
