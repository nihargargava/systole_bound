module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.Path

@[expose] public section

/-!
# A convex planar domain punctured at the center retracts to a literal circle

For every positive radius whose full Euclidean circle is contained in a convex
domain, the punctured domain strongly deformation retracts onto that circle.
The construction is the actual radial homotopy; no retraction data is assumed.
-/

open Set Metric
open scoped Topology unitInterval ContinuousMap

namespace SystolicGrowth

noncomputable section

/-- A convex planar domain with its origin removed. -/
abbrev convexPuncturedDomain (Ω : Set ℂ) := {z : ℂ // z ∈ Ω ∧ z ≠ 0}

/-- The literal radius-`ρ` endpoint of the radial homotopy at a nonzero point. -/
def convexPuncturedCircleEndpoint (ρ : ℝ) (z : ℂ) : ℂ :=
  ρ • (‖z‖⁻¹ • z)

/-- Normalize a nonzero complex point to the unit `Circle`. -/
def convexPuncturedUnitDirection (z : ℂ) (hz : z ≠ 0) : Circle := by
  refine ⟨‖z‖⁻¹ • z, ?_⟩
  apply mem_sphere_zero_iff_norm.mpr
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
  exact inv_mul_cancel₀ hn.ne'

/-- The normalized direction is indeed of unit norm. -/
@[simp]
theorem convexPuncturedUnitDirection_norm (z : ℂ) (hz : z ≠ 0) :
    ‖(convexPuncturedUnitDirection z hz : ℂ)‖ = 1 :=
  Circle.norm_coe _

/-- The radial endpoint lies on the literal circle of radius `ρ`. -/
theorem convexPuncturedCircleEndpoint_norm {ρ : ℝ} (hρ : 0 < ρ)
    {z : ℂ} (hz : z ≠ 0) :
    ‖convexPuncturedCircleEndpoint ρ z‖ = ρ := by
  unfold convexPuncturedCircleEndpoint
  have hdir : ‖‖z‖⁻¹ • z‖ = 1 := by
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    exact inv_mul_cancel₀ hn.ne'
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ, hdir]
  simp

/-- The radial endpoint is nonzero when its radius is positive. -/
theorem convexPuncturedCircleEndpoint_ne_zero {ρ : ℝ} (hρ : 0 < ρ)
    {z : ℂ} (hz : z ≠ 0) :
    convexPuncturedCircleEndpoint ρ z ≠ 0 := by
  unfold convexPuncturedCircleEndpoint
  exact smul_ne_zero hρ.ne' (smul_ne_zero (inv_ne_zero (norm_pos_iff.mpr hz).ne') hz)

/-- The radial endpoint equals the literal radius times the normalized unit
direction. -/
theorem convexPuncturedCircleEndpoint_eq_smul_direction {ρ : ℝ} {z : ℂ}
    (hz : z ≠ 0) :
    convexPuncturedCircleEndpoint ρ z =
      ρ • (convexPuncturedUnitDirection z hz : ℂ) := rfl

/-- At a point already on the radius-`ρ` circle, normalization followed by
rescaling is the identity. -/
theorem convexPuncturedCircleEndpoint_fixed {ρ : ℝ} {z : ℂ}
    (hρ : 0 < ρ) (hnorm : ‖z‖ = ρ) :
    convexPuncturedCircleEndpoint ρ z = z := by
  unfold convexPuncturedCircleEndpoint
  rw [hnorm]
  rw [show (ρ : ℝ) • (ρ⁻¹ • z) = (ρ * ρ⁻¹) • z by rw [smul_smul]]
  rw [mul_inv_cancel₀ hρ.ne', one_smul]

/-- The concrete radial interpolation between a point and its literal
radius-`ρ` endpoint. -/
def convexPuncturedRadialPush (ρ : ℝ) (t : I) (z : ℂ) : ℂ :=
  (1 - (t : ℝ)) • z + (t : ℝ) • convexPuncturedCircleEndpoint ρ z

/-- Rewriting the affine homotopy as a positive scalar multiple of the
original nonzero point. -/
theorem convexPuncturedRadialPush_eq_scale {ρ : ℝ} (t : I) {z : ℂ} :
    convexPuncturedRadialPush ρ t z =
      ((1 - (t : ℝ)) + (t : ℝ) * (ρ / ‖z‖)) • z := by
  unfold convexPuncturedRadialPush convexPuncturedCircleEndpoint
  calc
    (1 - (t : ℝ)) • z + (t : ℝ) • (ρ • (‖z‖⁻¹ • z)) =
        (1 - (t : ℝ)) • z + ((t : ℝ) * (ρ / ‖z‖)) • z := by
      rw [smul_smul, smul_smul]
      congr 1
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    _ = ((1 - (t : ℝ)) + (t : ℝ) * (ρ / ‖z‖)) • z := by rw [← add_smul]

/-- The homotopy scale stays strictly positive. -/
theorem convexPuncturedRadialPush_scale_pos {ρ : ℝ} (hρ : 0 < ρ)
    (t : I) {z : ℂ} (hz : z ≠ 0) :
    0 < (1 - (t : ℝ)) + (t : ℝ) * (ρ / ‖z‖) := by
  have hratio : 0 < ρ / ‖z‖ := div_pos hρ (norm_pos_iff.mpr hz)
  by_cases ht : (t : ℝ) = 1
  · rw [ht]
    simpa using hratio
  · have htlt : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 ht
    have hleft : 0 < 1 - (t : ℝ) := by linarith
    exact add_pos_of_pos_of_nonneg hleft
      (mul_nonneg t.2.1 hratio.le)

/-- The radial homotopy never passes through the deleted origin. -/
theorem convexPuncturedRadialPush_ne_zero {ρ : ℝ} (hρ : 0 < ρ)
    (t : I) {z : ℂ} (hz : z ≠ 0) :
    convexPuncturedRadialPush ρ t z ≠ 0 := by
  rw [convexPuncturedRadialPush_eq_scale t]
  exact smul_ne_zero (convexPuncturedRadialPush_scale_pos hρ t hz).ne' hz

@[simp]
theorem convexPuncturedRadialPush_zero (ρ : ℝ) (z : ℂ) :
    convexPuncturedRadialPush ρ 0 z = z := by
  simp [convexPuncturedRadialPush]

@[simp]
theorem convexPuncturedRadialPush_one {ρ : ℝ} (z : ℂ) :
    convexPuncturedRadialPush ρ 1 z = convexPuncturedCircleEndpoint ρ z := by
  simp [convexPuncturedRadialPush]

/-- Every point on the actual radius-`ρ` circle stays fixed throughout the
radial homotopy. -/
theorem convexPuncturedRadialPush_fixed {ρ : ℝ} (hρ : 0 < ρ)
    (t : I) {z : ℂ} (hnorm : ‖z‖ = ρ) :
    convexPuncturedRadialPush ρ t z = z := by
  rw [convexPuncturedRadialPush,
    convexPuncturedCircleEndpoint_fixed hρ hnorm]
  rw [← add_smul]
  rw [show (1 - (t : ℝ)) + (t : ℝ) = 1 by ring, one_smul]

/-- The exact circle of radius `ρ` contained in the convex domain. -/
def convexPuncturedDomainCircle (Ω : Set ℂ) (ρ : ℝ) :=
  {z : convexPuncturedDomain Ω | ‖z.1‖ = ρ}

/-- The literal inclusion of the normalized unit circle, scaled to radius `ρ`,
into the punctured convex domain. -/
def convexPuncturedCircleInclusion (Ω : Set ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (hΩcircle : ∀ θ : Circle, ρ • (θ : ℂ) ∈ Ω) :
    C(Circle, convexPuncturedDomain Ω) where
  toFun θ := ⟨ρ • (θ : ℂ), hΩcircle θ,
    smul_ne_zero hρ.ne' θ.coe_ne_zero⟩
  continuous_toFun := by
    have hc : Continuous (fun _ : Circle => (ρ : ℝ)) := continuous_const
    exact (hc.smul continuous_subtype_val).subtype_mk _

/-- Radial normalization is a continuous map from the punctured domain to
the unit `Circle`. -/
def convexPuncturedCircleRetraction (Ω : Set ℂ) :
    C(convexPuncturedDomain Ω, Circle) where
  toFun z := convexPuncturedUnitDirection z.1 z.2.2
  continuous_toFun := by
    have hz : Continuous (fun z : convexPuncturedDomain Ω => (z.1 : ℂ)) :=
      continuous_subtype_val
    have hnorm := hz.norm
    have hscale : Continuous (fun z : convexPuncturedDomain Ω => ‖z.1‖⁻¹) := by
      exact hnorm.inv₀ (fun z => (norm_pos_iff.mpr z.2.2).ne')
    have hdir : Continuous (fun z : convexPuncturedDomain Ω => ‖z.1‖⁻¹ • z.1) :=
      hscale.smul hz
    exact hdir.subtype_mk _

/-- The retraction fixes the included literal radius-`ρ` circle. -/
@[simp]
theorem convexPuncturedCircleRetraction_inclusion
    (Ω : Set ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hΩcircle : ∀ θ : Circle, ρ • (θ : ℂ) ∈ Ω) (θ : Circle) :
    convexPuncturedCircleRetraction Ω
      (convexPuncturedCircleInclusion Ω ρ hρ hΩcircle θ) = θ := by
  apply Circle.ext
  change ‖ρ • (θ : ℂ)‖⁻¹ • (ρ • (θ : ℂ)) = (θ : ℂ)
  have hnorm : ‖ρ • (θ : ℂ)‖ = ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ, Circle.norm_coe]
    simp
  rw [hnorm]
  rw [smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]

/-- The homotopy stays in `Ω` by convexity between its input and the actual
radius-`ρ` endpoint. -/
theorem convexPuncturedRadialPush_mem {Ω : Set ℂ} (hΩconv : Convex ℝ Ω)
    {ρ : ℝ} (hΩcircle : ∀ θ : Circle, ρ • (θ : ℂ) ∈ Ω)
    (t : I) {z : ℂ} (hzΩ : z ∈ Ω) (hz : z ≠ 0) :
    convexPuncturedRadialPush ρ t z ∈ Ω := by
  have hendpoint : convexPuncturedCircleEndpoint ρ z ∈ Ω := by
    rw [convexPuncturedCircleEndpoint_eq_smul_direction hz]
    exact hΩcircle (convexPuncturedUnitDirection z hz)
  have hcoef : (1 - (t : ℝ)) + (t : ℝ) = 1 := by ring
  exact (convex_iff_add_mem.mp hΩconv) hzΩ hendpoint
    (sub_nonneg.mpr t.2.2) t.2.1 hcoef

/-- The radial homotopy is continuous jointly in time and point. -/
theorem convexPuncturedRadialPush_continuous (Ω : Set ℂ) (ρ : ℝ) :
    Continuous (fun p : I × convexPuncturedDomain Ω =>
      convexPuncturedRadialPush ρ p.1 p.2.1) := by
  have ht : Continuous (fun p : I × convexPuncturedDomain Ω => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hz : Continuous (fun p : I × convexPuncturedDomain Ω => (p.2.1 : ℂ)) :=
    continuous_subtype_val.comp continuous_snd
  have hnorm := hz.norm
  have hrad : Continuous (fun p : I × convexPuncturedDomain Ω => ‖p.2.1‖⁻¹) := by
    exact hnorm.inv₀ (fun p => (norm_pos_iff.mpr p.2.2.2).ne')
  have hendpoint : Continuous (fun p : I × convexPuncturedDomain Ω =>
      ρ • (‖p.2.1‖⁻¹ • p.2.1)) :=
    (continuous_const : Continuous (fun _ : I × convexPuncturedDomain Ω => ρ)).smul
      (hrad.smul hz)
  exact ((continuous_const.sub ht).smul hz).add (ht.smul hendpoint)

/-- The actual strong deformation retraction onto the radius-`ρ` circle. -/
def convexPuncturedDomainCircleDeformationRetraction
    (Ω : Set ℂ) (ρ : ℝ) (hΩconv : Convex ℝ Ω) (hρ : 0 < ρ)
    (hΩcircle : ∀ θ : Circle, ρ • (θ : ℂ) ∈ Ω) :
    (ContinuousMap.id (convexPuncturedDomain Ω)).HomotopyRel
      ((convexPuncturedCircleInclusion Ω ρ hρ hΩcircle).comp
        (convexPuncturedCircleRetraction Ω))
      (convexPuncturedDomainCircle Ω ρ) where
  toHomotopy :=
    { toContinuousMap :=
        { toFun p := ⟨convexPuncturedRadialPush ρ p.1 p.2.1,
            convexPuncturedRadialPush_mem hΩconv hΩcircle p.1 p.2.2.1 p.2.2.2,
            convexPuncturedRadialPush_ne_zero hρ p.1 p.2.2.2⟩
          continuous_toFun := by
            exact (convexPuncturedRadialPush_continuous Ω ρ).subtype_mk _ }
      map_zero_left := fun z => Subtype.ext (convexPuncturedRadialPush_zero ρ z.1)
      map_one_left := fun z => by
        apply Subtype.ext
        change convexPuncturedRadialPush ρ 1 z.1 =
          ρ • (convexPuncturedCircleRetraction Ω z : ℂ)
        rw [convexPuncturedRadialPush_one,
          convexPuncturedCircleEndpoint_eq_smul_direction z.2.2]
        rfl }
  prop' := by
    intro t z hz
    apply Subtype.ext
    exact convexPuncturedRadialPush_fixed hρ t hz

/-- The punctured convex domain is homotopy equivalent to the unit circle. -/
def convexPuncturedDomainCircleHomotopyEquiv
    (Ω : Set ℂ) (ρ : ℝ) (hΩconv : Convex ℝ Ω) (hρ : 0 < ρ)
    (hΩcircle : ∀ θ : Circle, ρ • (θ : ℂ) ∈ Ω) :
    convexPuncturedDomain Ω ≃ₕ Circle where
  toFun := convexPuncturedCircleRetraction Ω
  invFun := convexPuncturedCircleInclusion Ω ρ hρ hΩcircle
  left_inv := ⟨(convexPuncturedDomainCircleDeformationRetraction
    Ω ρ hΩconv hρ hΩcircle).toHomotopy.symm⟩
  right_inv := by
    have hcomp :
        (convexPuncturedCircleRetraction Ω).comp
          (convexPuncturedCircleInclusion Ω ρ hρ hΩcircle) =
            ContinuousMap.id Circle := by
      apply ContinuousMap.ext
      intro θ
      exact convexPuncturedCircleRetraction_inclusion Ω ρ hρ hΩcircle θ
    rw [hcomp]

/-- The punctured convex domain is path connected, as witnessed by radial paths to
the contained circle, paths on that circle, and the reverse radial paths. -/
theorem convexPuncturedDomain_pathConnected
    (Ω : Set ℂ) (ρ : ℝ) (hΩconv : Convex ℝ Ω) (hρ : 0 < ρ)
    (hΩcircle : ∀ θ : Circle, ρ • (θ : ℂ) ∈ Ω) :
    PathConnectedSpace (convexPuncturedDomain Ω) := by
  let inc := convexPuncturedCircleInclusion Ω ρ hρ hΩcircle
  let ret := convexPuncturedCircleRetraction Ω
  let H := (convexPuncturedDomainCircleDeformationRetraction
    Ω ρ hΩconv hρ hΩcircle).toHomotopy
  let θ₀ : Circle := ⟨1, by simp⟩
  refine ⟨⟨inc θ₀⟩, fun x y => ?_⟩
  exact ⟨((H.evalAt x).trans
    ((Circle.path (ret x) (ret y)).map inc.continuous)).trans
      (H.evalAt y).symm⟩

/-- Radial normalization induces the actual based fundamental-group
isomorphism with the normalized unit circle. -/
def convexPuncturedDomainCircleFundamentalGroupEquiv
    (Ω : Set ℂ) (ρ : ℝ) (hΩconv : Convex ℝ Ω) (hρ : 0 < ρ)
    (hΩcircle : ∀ θ : Circle, ρ • (θ : ℂ) ∈ Ω)
    (z : convexPuncturedDomain Ω) :
    FundamentalGroup (convexPuncturedDomain Ω) z ≃*
      FundamentalGroup Circle (convexPuncturedCircleRetraction Ω z) := by
  let e := FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (convexPuncturedDomainCircleHomotopyEquiv Ω ρ hΩconv hρ hΩcircle)
  exact MulEquiv.ofBijective (FundamentalGroup.map
      (convexPuncturedCircleRetraction Ω) z)
    (e.fullyFaithfulFunctor.map_bijective (FundamentalGroupoid.mk z)
      (FundamentalGroupoid.mk z))

end

end SystolicGrowth
