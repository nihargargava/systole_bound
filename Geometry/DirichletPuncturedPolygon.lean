module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.DirichletCyclicBoundary
public import Mathlib.Topology.Homotopy.Basic

@[expose] public section

/-!
# The punctured actual Dirichlet polygon retracts onto its frontier

The existing radial frontier homeomorphism selects the unique exit point
on the ray through each noncentral point of the actual Dirichlet domain.
Geodesic interpolation increases its positive hyperbolic radius to that
exit radius. The resulting strong deformation retraction fixes the entire
original frontier at every time, as needed for quotient descent.
-/

open Set UpperHalfPlane
open scoped UpperHalfPlane unitInterval ContinuousMap

namespace SystolicGrowth
namespace ClosedHyperbolicSurface

noncomputable section

variable {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ)

/-- The actual closed Dirichlet domain with only its center removed. -/
abbrev PuncturedDirichletDomain :=
  {z : ℍ // z ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∧ z ≠ o}

/-- The entire frontier of the original Dirichlet domain. -/
abbrev DirichletFrontier :=
  ↥(frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o))

/-- The direction of a noncentral point in the actual Dirichlet domain. -/
def dirichletPunctureDirection (z : X.PuncturedDirichletDomain o) : Circle :=
  ⟨hyperbolicRadialDirection o z.1, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [hyperbolicRadialDirection, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr (Vendored.RiemannDynamics.discChart_ne_zero z.2.2))]⟩

theorem continuous_dirichletPunctureDirection :
    Continuous (X.dirichletPunctureDirection o) := by
  apply Continuous.subtype_mk
  have hc : Continuous (fun z : X.PuncturedDirichletDomain o =>
      Vendored.RiemannDynamics.discChart o z.1) :=
    (continuous_discChart o).comp continuous_subtype_val
  exact hc.div (Complex.continuous_ofReal.comp hc.norm) (fun z =>
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr
      (Vendored.RiemannDynamics.discChart_ne_zero z.2.2)))

/-- Literal inclusion of the complete actual frontier into the punctured domain. -/
def dirichletFrontierInclusion : C(X.DirichletFrontier o, X.PuncturedDirichletDomain o) where
  toFun z := ⟨z.1,
    (Vendored.RiemannDynamics.isClosed_dirichletDomain X.deckGroup o).frontier_subset z.2,
    X.frontier_point_ne_basepoint o z.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The unique actual frontier point with the given point's radial direction. -/
def dirichletPunctureRetraction : C(X.PuncturedDirichletDomain o, X.DirichletFrontier o) where
  toFun z := (X.dirichletBoundaryRadialHomeomorph o).symm (X.dirichletPunctureDirection o z)
  continuous_toFun := (X.dirichletBoundaryRadialHomeomorph o).symm.continuous.comp
    (X.continuous_dirichletPunctureDirection o)

@[simp]
theorem dirichletPunctureRetraction_inclusion (z : X.DirichletFrontier o) :
    X.dirichletPunctureRetraction o (X.dirichletFrontierInclusion o z) = z := by
  change (X.dirichletBoundaryRadialHomeomorph o).symm
    (X.dirichletBoundaryRadialHomeomorph o z) = z
  exact (X.dirichletBoundaryRadialHomeomorph o).symm_apply_apply z

theorem dirichletPunctureRetraction_direction (z : X.PuncturedDirichletDomain o) :
    hyperbolicRadialDirection o (X.dirichletPunctureRetraction o z).1 =
      hyperbolicRadialDirection o z.1 := by
  have h := congrArg (fun ξ : Circle => (ξ : ℂ))
    ((X.dirichletBoundaryRadialHomeomorph o).apply_symm_apply
      (X.dirichletPunctureDirection o z))
  exact h

/-- An exact angular identification determines the exit point through the
original radial boundary homeomorphism, with no change of parametrization. -/
theorem dirichletPunctureRetraction_eq_of_direction (z : X.PuncturedDirichletDomain o)
    (ξ : Circle) (hdir : hyperbolicRadialDirection o z.1 = (ξ : ℂ)) :
    X.dirichletPunctureRetraction o z = (X.dirichletBoundaryRadialHomeomorph o).symm ξ :=
  congrArg (X.dirichletBoundaryRadialHomeomorph o).symm (Circle.ext hdir)

/-- Every original noncentral domain point lies before its selected frontier
point on the same actual hyperbolic geodesic ray. -/
theorem dirichletPunctureRetraction_mem_geodSeg (z : X.PuncturedDirichletDomain o) :
    z.1 ∈ Vendored.RiemannDynamics.geodSeg o (X.dirichletPunctureRetraction o z).1 := by
  obtain ⟨K, hK, hcover⟩ := X.exists_compact_covering
  have hcompact := X.isCompact_dirichletDomain_of_compact_covering o K hK hcover
  obtain ⟨b, hb, hzb⟩ := exists_mem_frontier_geodSeg_of_isCompact hcompact z.2.1 z.2.2
  have hbexit : b = (X.dirichletPunctureRetraction o z).1 := by
    apply X.hyperbolicRadialDirection_injOn_frontier o hb
      (X.dirichletPunctureRetraction o z).2
    exact (hyperbolicRadialDirection_eq_of_mem_geodSeg hzb z.2.2).symm.trans
      (X.dirichletPunctureRetraction_direction o z).symm
  rwa [← hbexit]

theorem dirichletPunctureRetraction_radius_pos (z : X.PuncturedDirichletDomain o) :
    0 < dist o (X.dirichletPunctureRetraction o z).1 :=
  dist_pos.mpr (X.frontier_point_ne_basepoint o
    (X.dirichletPunctureRetraction o z).2).symm

theorem dirichletPunctureRetraction_radius_le (z : X.PuncturedDirichletDomain o) :
    dist o z.1 ≤ dist o (X.dirichletPunctureRetraction o z).1 := by
  have hseg : dist o z.1 + dist z.1 (X.dirichletPunctureRetraction o z).1 =
      dist o (X.dirichletPunctureRetraction o z).1 :=
    X.dirichletPunctureRetraction_mem_geodSeg o z
  linarith [dist_nonneg (x := z.1) (y := (X.dirichletPunctureRetraction o z).1)]

def dirichletPunctureParameter (p : I × X.PuncturedDirichletDomain o) : ℝ :=
  (1 - (p.1 : ℝ)) * (dist o p.2.1 / dist o (X.dirichletPunctureRetraction o p.2).1) +
    (p.1 : ℝ)

private theorem dirichletPunctureParameter_mem (p : I × X.PuncturedDirichletDomain o) :
    X.dirichletPunctureParameter o p ∈ Ioc (0 : ℝ) 1 := by
  have hdpos := X.dirichletPunctureRetraction_radius_pos o p.2
  have hquot : dist o p.2.1 / dist o (X.dirichletPunctureRetraction o p.2).1 ∈
      Ioc (0 : ℝ) 1 :=
    ⟨div_pos (dist_pos.mpr p.2.2.2.symm) hdpos,
      (div_le_one hdpos).mpr (X.dirichletPunctureRetraction_radius_le o p.2)⟩
  have h := (convex_Ioc (0 : ℝ) 1) hquot (show (1 : ℝ) ∈ Ioc (0 : ℝ) 1 by norm_num)
    (sub_nonneg.mpr p.1.2.2) p.1.2.1 (by ring)
  simpa only [dirichletPunctureParameter, smul_eq_mul, mul_one] using h

/-- Positive-radius interpolation along the ray to the original frontier. -/
def dirichletPuncturePushFn (p : I × X.PuncturedDirichletDomain o) : ℍ :=
  Vendored.RiemannDynamics.geodInterp o (X.dirichletPunctureRetraction o p.2).1
    (X.dirichletPunctureParameter o p)

theorem dirichletPuncturePushFn_mem_geodSeg (p : I × X.PuncturedDirichletDomain o) :
    X.dirichletPuncturePushFn o p ∈
      Vendored.RiemannDynamics.geodSeg o (X.dirichletPunctureRetraction o p.2).1 :=
  Vendored.RiemannDynamics.geodInterp_mem_geodSeg o _
    ⟨(X.dirichletPunctureParameter_mem o p).1.le,
      (X.dirichletPunctureParameter_mem o p).2⟩

/-- The interpolation remains in the actual geodesically convex domain. -/
theorem dirichletPuncturePushFn_mem (p : I × X.PuncturedDirichletDomain o) :
    X.dirichletPuncturePushFn o p ∈
      Vendored.RiemannDynamics.dirichletDomain X.deckGroup o := by
  apply Vendored.RiemannDynamics.mem_dirichletDomain.mpr
  intro γ
  apply Vendored.RiemannDynamics.geodSeg_subset_setOf_dist_le
    (show dist o o ≤ dist o (γ • o) by simp)
    ((Vendored.RiemannDynamics.mem_dirichletDomain.mp
      ((Vendored.RiemannDynamics.isClosed_dirichletDomain X.deckGroup o).frontier_subset
        (X.dirichletPunctureRetraction o p.2).2)) γ)
    (X.dirichletPuncturePushFn_mem_geodSeg o p)

/-- The honest hyperbolic radius is the positive affine interpolation of the
original radius and its actual frontier exit radius. -/
theorem dirichletPuncturePushFn_dist (p : I × X.PuncturedDirichletDomain o) :
    dist o (X.dirichletPuncturePushFn o p) =
      (1 - (p.1 : ℝ)) * dist o p.2.1 +
        (p.1 : ℝ) * dist o (X.dirichletPunctureRetraction o p.2).1 := by
  have hdne := (X.dirichletPunctureRetraction_radius_pos o p.2).ne'
  rw [dirichletPuncturePushFn, Vendored.RiemannDynamics.dist_geodInterp_left o _
    ⟨(X.dirichletPunctureParameter_mem o p).1.le,
      (X.dirichletPunctureParameter_mem o p).2⟩]
  unfold dirichletPunctureParameter
  field_simp

theorem dirichletPuncturePushFn_ne_center (p : I × X.PuncturedDirichletDomain o) :
    X.dirichletPuncturePushFn o p ≠ o := by
  have hdpos : 0 < dist o (X.dirichletPuncturePushFn o p) := by
    rw [dirichletPuncturePushFn, Vendored.RiemannDynamics.dist_geodInterp_left o _
      ⟨(X.dirichletPunctureParameter_mem o p).1.le,
        (X.dirichletPunctureParameter_mem o p).2⟩]
    exact mul_pos (X.dirichletPunctureParameter_mem o p).1
      (X.dirichletPunctureRetraction_radius_pos o p.2)
  exact (dist_pos.mp hdpos).symm

theorem dirichletPuncturePushFn_direction (p : I × X.PuncturedDirichletDomain o) :
    hyperbolicRadialDirection o (X.dirichletPuncturePushFn o p) =
      hyperbolicRadialDirection o p.2.1 :=
  (hyperbolicRadialDirection_eq_of_mem_geodSeg
    (X.dirichletPuncturePushFn_mem_geodSeg o p)
    (X.dirichletPuncturePushFn_ne_center o p)).trans
      (X.dirichletPunctureRetraction_direction o p.2)

theorem continuous_dirichletPuncturePushFn :
    Continuous (X.dirichletPuncturePushFn o) := by
  have hz : Continuous (fun p : I × X.PuncturedDirichletDomain o => p.2.1) :=
    continuous_subtype_val.comp continuous_snd
  have hb : Continuous (fun p : I × X.PuncturedDirichletDomain o =>
      (X.dirichletPunctureRetraction o p.2).1) :=
    continuous_subtype_val.comp ((X.dirichletPunctureRetraction o).continuous.comp continuous_snd)
  have ht : Continuous (fun p : I × X.PuncturedDirichletDomain o => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hquot : Continuous (fun p : I × X.PuncturedDirichletDomain o =>
      dist o p.2.1 / dist o (X.dirichletPunctureRetraction o p.2).1) :=
    (continuous_const.dist hz).div (continuous_const.dist hb)
    (fun p => (X.dirichletPunctureRetraction_radius_pos o p.2).ne')
  have hp : Continuous (X.dirichletPunctureParameter o) :=
    ((continuous_const.sub ht).mul hquot).add ht
  exact Vendored.RiemannDynamics.continuous_geodInterp.comp
    (continuous_const.prodMk (hb.prodMk hp))

@[simp]
theorem dirichletPuncturePushFn_zero (z : X.PuncturedDirichletDomain o) :
    X.dirichletPuncturePushFn o (0, z) = z.1 := by
  apply Vendored.RiemannDynamics.eq_of_mem_geodSeg_of_dist_eq
    (X.dirichletPuncturePushFn_mem_geodSeg o (0, z))
    (X.dirichletPunctureRetraction_mem_geodSeg o z)
  simp only [X.dirichletPuncturePushFn_dist o (0, z),
    show ((0 : I) : ℝ) = 0 from rfl, sub_zero, one_mul, zero_mul, add_zero]

@[simp]
theorem dirichletPuncturePushFn_one (z : X.PuncturedDirichletDomain o) :
    X.dirichletPuncturePushFn o (1, z) = (X.dirichletPunctureRetraction o z).1 := by
  simp only [dirichletPuncturePushFn, dirichletPunctureParameter,
    show ((1 : I) : ℝ) = 1 from rfl, sub_self, zero_mul, zero_add,
    Vendored.RiemannDynamics.geodInterp_one]

/-- Every frontier point is fixed throughout, including every side-pairing
and vertex representative required for descent to the original quotient. -/
theorem dirichletPuncturePushFn_fixed (p : I × X.PuncturedDirichletDomain o)
    (hp : p.2.1 ∈ frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)) :
    X.dirichletPuncturePushFn o p = p.2.1 := by
  have hret : (X.dirichletPunctureRetraction o p.2).1 = p.2.1 :=
    congrArg Subtype.val (X.dirichletPunctureRetraction_inclusion o ⟨p.2.1, hp⟩)
  have hdne : dist o p.2.1 ≠ 0 := (dist_pos.mpr p.2.2.2.symm).ne'
  unfold dirichletPuncturePushFn dirichletPunctureParameter
  rw [hret, div_self hdne]
  have ht : (1 - (p.1 : ℝ)) * 1 + (p.1 : ℝ) = 1 := by ring
  rw [ht, Vendored.RiemannDynamics.geodInterp_one]

/-- The complete native radial homotopy, valued in the actual punctured domain. -/
def dirichletPunctureHomotopyMap : C(I × X.PuncturedDirichletDomain o,
    X.PuncturedDirichletDomain o) where
  toFun p := ⟨X.dirichletPuncturePushFn o p,
    X.dirichletPuncturePushFn_mem o p, X.dirichletPuncturePushFn_ne_center o p⟩
  continuous_toFun := (X.continuous_dirichletPuncturePushFn o).subtype_mk _

@[simp]
theorem dirichletPunctureHomotopyMap_zero (z : X.PuncturedDirichletDomain o) :
    X.dirichletPunctureHomotopyMap o (0, z) = z :=
  Subtype.ext (X.dirichletPuncturePushFn_zero o z)

@[simp]
theorem dirichletPunctureHomotopyMap_one (z : X.PuncturedDirichletDomain o) :
    X.dirichletPunctureHomotopyMap o (1, z) =
      X.dirichletFrontierInclusion o (X.dirichletPunctureRetraction o z) :=
  Subtype.ext (X.dirichletPuncturePushFn_one o z)

theorem dirichletPunctureHomotopyMap_fixed (p : I × X.PuncturedDirichletDomain o)
    (hp : p.2.1 ∈ frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)) :
    X.dirichletPunctureHomotopyMap o p = p.2 :=
  Subtype.ext (X.dirichletPuncturePushFn_fixed o p hp)

/-- Genuine strong deformation retraction of the actual punctured Dirichlet
domain onto its entire original frontier. -/
def dirichletPunctureDeformationRetraction :
    (ContinuousMap.id (X.PuncturedDirichletDomain o)).HomotopyRel
      ((X.dirichletFrontierInclusion o).comp (X.dirichletPunctureRetraction o))
      {z | z.1 ∈ frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)} where
  toHomotopy :=
    { toContinuousMap := X.dirichletPunctureHomotopyMap o
      map_zero_left := X.dirichletPunctureHomotopyMap_zero o
      map_one_left := X.dirichletPunctureHomotopyMap_one o }
  prop' := fun t z hz => X.dirichletPunctureHomotopyMap_fixed o (t, z) hz

@[simp]
theorem dirichletPunctureDeformationRetraction_inclusion (t : I) (z : X.DirichletFrontier o) :
    X.dirichletPunctureDeformationRetraction o (t, X.dirichletFrontierInclusion o z) =
      X.dirichletFrontierInclusion o z :=
  X.dirichletPunctureHomotopyMap_fixed o (t, X.dirichletFrontierInclusion o z) z.2

end

end ClosedHyperbolicSurface
end SystolicGrowth
