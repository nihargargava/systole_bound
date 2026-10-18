module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceTwoCenterCutTubeEmbedding
public import Geometry.GluingFinFermiInverse
public import Vendored.RiemannDynamics.Hyperbolic.PlaneGeometry.Geodesics.Frame

@[expose] public section

/-!
# Global coordinates adapted to the actual two-center geodesic

This module starts the descended rectangle construction from a global
coordinate homeomorphism of the actual upper half-plane.  The central axis is
the geodesic joining the first center to the minimizing deck translate of the
second center; no neighborhood or collar is assumed.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane Topology unitInterval MatrixGroups

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The global scaled Fermi homeomorphism. -/
def gluingFinFermiHomeomorph (α : ℝ) (hα : 0 < α) : ℝ × ℝ ≃ₜ ℍ where
  toFun p := gluingFinFermiPoint α p.1 p.2
  invFun z := gluingFinFermiInverse α z
  left_inv p := gluingFinFermiInverse_point hα
  right_inv z := gluingFinFermiPoint_inverse_right hα z
  continuous_toFun := by
    have hcont : Continuous (fun p : ℝ × ℝ => gluingFinFermiLift α p) := by
      have htanh : Continuous (fun x : ℝ => Real.tanh x) := by
        have heq : (fun x : ℝ => Real.tanh x) =
            (fun x => Real.sinh x / Real.cosh x) := by
          funext x
          exact Real.tanh_eq_sinh_div_cosh x
        rw [heq]
        exact Real.continuous_sinh.div Real.continuous_cosh
          (fun x => (Real.cosh_pos x).ne')
      have hfirst : Continuous (fun p : ℝ × ℝ =>
          Real.exp (α * p.1) * Real.tanh (α * p.2)) := by
        exact (Real.continuous_exp.comp (by fun_prop)).mul
          (htanh.comp (by fun_prop))
      have hsecond : Continuous (fun p : ℝ × ℝ =>
          Real.exp (α * p.1) / Real.cosh (α * p.2)) := by
        exact (Real.continuous_exp.comp (by fun_prop)).div
          (Real.continuous_cosh.comp (by fun_prop))
          (fun p => (Real.cosh_pos _).ne')
      change Continuous (fun p : ℝ × ℝ =>
        Complex.ofReal (Real.exp (α * p.1) * Real.tanh (α * p.2)) +
          Complex.ofReal (Real.exp (α * p.1) / Real.cosh (α * p.2)) * Complex.I)
      exact (Complex.continuous_ofReal.comp hfirst).add
        ((Complex.continuous_ofReal.comp hsecond).mul continuous_const)
    exact hcont.upperHalfPlaneMk (fun p => by
      rw [gluingFinFermiLift_im]
      exact div_pos (Real.exp_pos _) (Real.cosh_pos _))
  continuous_invFun := by
    change Continuous (fun z : ℍ =>
      (gluingFinFermiRadialCoord α z, gluingFinFermiTransverseCoord α z))
    exact (continuous_gluingFinFermiRadialCoord α).prodMk
      (continuous_gluingFinFermiTransverseCoord α)

/-- The homeomorphism of the upper half-plane induced by an actual
`SL(2,ℝ)` deck transformation. -/
def upperHalfPlaneSLHomeomorph (γ : SL(2, ℝ)) : ℍ ≃ₜ ℍ where
  toFun z := γ • z
  invFun z := γ⁻¹ • z
  left_inv z := inv_smul_smul γ z
  right_inv z := smul_inv_smul γ z
  continuous_toFun := (isometry_smul ℍ γ).continuous
  continuous_invFun := (isometry_smul ℍ γ⁻¹).continuous

/-- An actual verticalizing transformation for the selected center segment.
Its existence is supplied by the vendored geometric theorem. -/
noncomputable def componentTwoCenterGeodesicVerticalizer
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) : SL(2, ℝ) :=
  Classical.choose (Vendored.RiemannDynamics.exists_verticalize
    (P.centers i).1 (P.componentCenterClosestDeck i • (P.centers i).2))

theorem componentTwoCenterGeodesicVerticalizer_spec
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    (P.componentTwoCenterGeodesicVerticalizer i • (P.centers i).1).re = 0 ∧
      (P.componentTwoCenterGeodesicVerticalizer i •
        (P.componentCenterClosestDeck i • (P.centers i).2)).re = 0 :=
  Classical.choose_spec (Vendored.RiemannDynamics.exists_verticalize
    (P.centers i).1 (P.componentCenterClosestDeck i • (P.centers i).2))

/-- Global Fermi coordinates transported back from the verticalized actual
minimizing center segment. -/
noncomputable def componentTwoCenterGeodesicCoordinateHomeomorph
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    ℝ × ℝ ≃ₜ ℍ :=
  (gluingFinFermiHomeomorph 1 one_pos).trans
    (upperHalfPlaneSLHomeomorph (P.componentTwoCenterGeodesicVerticalizer i)⁻¹)

@[simp]
theorem componentTwoCenterGeodesicCoordinateHomeomorph_apply
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (p : ℝ × ℝ) :
    P.componentTwoCenterGeodesicCoordinateHomeomorph i p =
      (P.componentTwoCenterGeodesicVerticalizer i)⁻¹ •
        gluingFinFermiPoint 1 p.1 p.2 := rfl

theorem componentTwoCenterGeodesicCoordinateHomeomorph_symm_apply
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (z : ℍ) :
    (P.componentTwoCenterGeodesicCoordinateHomeomorph i).symm z =
      gluingFinFermiInverse 1 (P.componentTwoCenterGeodesicVerticalizer i • z) := by
  change (gluingFinFermiHomeomorph 1 one_pos).symm
    ((upperHalfPlaneSLHomeomorph
      (P.componentTwoCenterGeodesicVerticalizer i)⁻¹).symm z) = _
  change gluingFinFermiInverse 1
    ((P.componentTwoCenterGeodesicVerticalizer i)⁻¹⁻¹ • z) = _
  simp

/-- On the vertical axis, the global inverse Fermi coordinates are logarithmic
height and zero transverse coordinate. -/
theorem gluingFinFermiInverse_eq_log_height_of_re_zero {z : ℍ}
    (hz : z.re = 0) :
    gluingFinFermiInverse 1 z = (Real.log z.im, 0) := by
  have hnorm : ‖(z : ℂ)‖ = z.im := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im, hz, zero_pow (by norm_num), zero_add,
      Real.sqrt_sq_eq_abs, abs_of_pos z.im_pos]
  apply Prod.ext
  · unfold gluingFinFermiInverse gluingFinFermiRadialCoord
    rw [hnorm]
    simp
  · unfold gluingFinFermiInverse gluingFinFermiTransverseCoord
    rw [hz]
    simp [Real.arsinh_zero]

/-- The left actual center has the logarithmic axial coordinate after
verticalization. -/
theorem componentTwoCenterGeodesicCoordinateHomeomorph_left_center
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    (P.componentTwoCenterGeodesicCoordinateHomeomorph i).symm (P.centers i).1 =
      (Real.log (P.componentTwoCenterGeodesicVerticalizer i • (P.centers i).1).im, 0) := by
  rw [P.componentTwoCenterGeodesicCoordinateHomeomorph_symm_apply]
  exact gluingFinFermiInverse_eq_log_height_of_re_zero
    (P.componentTwoCenterGeodesicVerticalizer_spec i).1

/-- The selected minimizing translate of the right actual center has its
logarithmic axial coordinate after verticalization. -/
theorem componentTwoCenterGeodesicCoordinateHomeomorph_right_center
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    (P.componentTwoCenterGeodesicCoordinateHomeomorph i).symm
      (P.componentCenterClosestDeck i • (P.centers i).2) =
      (Real.log (P.componentTwoCenterGeodesicVerticalizer i •
        (P.componentCenterClosestDeck i • (P.centers i).2)).im, 0) := by
  rw [P.componentTwoCenterGeodesicCoordinateHomeomorph_symm_apply]
  exact gluingFinFermiInverse_eq_log_height_of_re_zero
    (P.componentTwoCenterGeodesicVerticalizer_spec i).2

/-- Verticalized interpolation agrees with interpolation of the verticalized
endpoints. The proof uses isometry and uniqueness at fixed distance along the
geodesic segment. -/
theorem componentTwoCenterGeodesicVerticalizer_geodInterp
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (s : I) :
    P.componentTwoCenterGeodesicVerticalizer i •
        (Vendored.RiemannDynamics.geodInterp (P.centers i).1
          (P.componentCenterClosestDeck i • (P.centers i).2) s) =
      Vendored.RiemannDynamics.geodInterp
        (P.componentTwoCenterGeodesicVerticalizer i • (P.centers i).1)
        (P.componentTwoCenterGeodesicVerticalizer i •
          (P.componentCenterClosestDeck i • (P.centers i).2)) s := by
  let v := P.componentTwoCenterGeodesicVerticalizer i
  let a := (P.centers i).1
  let b := P.componentCenterClosestDeck i • (P.centers i).2
  apply Vendored.RiemannDynamics.eq_on_geodSeg_of_dist_eq
  · rw [← Vendored.RiemannDynamics.smul_geodSeg]
    exact ⟨Vendored.RiemannDynamics.geodInterp a b s,
      Vendored.RiemannDynamics.geodInterp_mem_geodSeg a b s.2, rfl⟩
  · exact Vendored.RiemannDynamics.geodInterp_mem_geodSeg (v • a) (v • b) s.2
  · rw [dist_smul,
      Vendored.RiemannDynamics.dist_geodInterp_left a b s.2,
      Vendored.RiemannDynamics.dist_geodInterp_left (v • a) (v • b) s.2,
      dist_smul]

/-- The global actual-center chart sends the affine logarithmic-height axis
exactly to the minimizing center geodesic. This statement covers the complete
center segment and does not depend on the truncated cut interval. -/
theorem componentTwoCenterGeodesicCoordinateHomeomorph_core
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (s : I) :
    P.componentTwoCenterGeodesicCoordinateHomeomorph i
        ((1 - (s : ℝ)) *
            Real.log (P.componentTwoCenterGeodesicVerticalizer i • (P.centers i).1).im +
          (s : ℝ) * Real.log (P.componentTwoCenterGeodesicVerticalizer i •
            (P.componentCenterClosestDeck i • (P.centers i).2)).im,
          0) =
      Vendored.RiemannDynamics.geodInterp (P.centers i).1
        (P.componentCenterClosestDeck i • (P.centers i).2) s := by
  let a' := P.componentTwoCenterGeodesicVerticalizer i • (P.centers i).1
  let b' := P.componentTwoCenterGeodesicVerticalizer i •
    (P.componentCenterClosestDeck i • (P.centers i).2)
  have haxis : a'.re = b'.re := by
    change (P.componentTwoCenterGeodesicVerticalizer i • (P.centers i).1).re =
      (P.componentTwoCenterGeodesicVerticalizer i •
        (P.componentCenterClosestDeck i • (P.centers i).2)).re
    rw [(P.componentTwoCenterGeodesicVerticalizer_spec i).1,
      (P.componentTwoCenterGeodesicVerticalizer_spec i).2]
  have hfermi : gluingFinFermiPoint 1
      ((1 - (s : ℝ)) * Real.log a'.im + (s : ℝ) * Real.log b'.im) 0 =
        Vendored.RiemannDynamics.geodInterp a' b' (s : ℝ) := by
    rw [Vendored.RiemannDynamics.geodInterp_vertical haxis]
    apply UpperHalfPlane.ext_re_im
    · simp [gluingFinFermiPoint_re, a', (P.componentTwoCenterGeodesicVerticalizer_spec i).1]
    · simp [gluingFinFermiPoint_im, Real.cosh_zero, one_mul]
  rw [componentTwoCenterGeodesicCoordinateHomeomorph_apply]
  change (P.componentTwoCenterGeodesicVerticalizer i)⁻¹ • _ = _
  rw [hfermi]
  rw [← P.componentTwoCenterGeodesicVerticalizer_geodInterp i s]
  simp

/-- The axial/transverse coordinates of the actual truncated cut rectangle.
The first coordinate is the affine logarithmic height obtained from the
global chart, restricted by the literal cut parameter. -/
def componentTwoCenterCutRectangleCoordinates
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (t : I) (u : ℝ) : ℝ × ℝ :=
  let s := P.componentTwoCenterCutCoordinate i t
  ((1 - (s : ℝ)) *
      Real.log (P.componentTwoCenterGeodesicVerticalizer i • (P.centers i).1).im +
    (s : ℝ) * Real.log (P.componentTwoCenterGeodesicVerticalizer i •
      (P.componentCenterClosestDeck i • (P.centers i).2)).im, u)

/-- The literal lifted rectangle map, using the global actual-center chart. -/
def componentTwoCenterCutRectangleLiftPoint
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (t : I) (u : ℝ) : ℍ :=
  P.componentTwoCenterGeodesicCoordinateHomeomorph i
    (P.componentTwoCenterCutRectangleCoordinates i t u)

@[simp]
theorem componentTwoCenterCutRectangleLiftPoint_apply
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (t : I) (u : ℝ) :
    P.componentTwoCenterCutRectangleLiftPoint i t u =
      (P.componentTwoCenterGeodesicVerticalizer i)⁻¹ •
        gluingFinFermiPoint 1
          (P.componentTwoCenterCutRectangleCoordinates i t u).1 u := rfl

/-- On the center line, the coordinate rectangle is exactly the literal
truncated lifted cut, not merely a homotopic or reparametrized arc. -/
theorem componentTwoCenterCutRectangleLiftPoint_axis
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (t : I) :
    P.componentTwoCenterCutRectangleLiftPoint i t 0 =
      P.componentTwoCenterLiftedCutPoint i t := by
  unfold componentTwoCenterCutRectangleLiftPoint componentTwoCenterCutRectangleCoordinates
  rw [componentTwoCenterGeodesicCoordinateHomeomorph_core]
  rfl

/-- Moving transversely at fixed radial coordinate has exact hyperbolic
length `|u|`; this supplies an explicit rectangle width inside the cut tube. -/
theorem componentTwoCenterCutRectangleLiftPoint_dist_axis
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (t : I) (u : ℝ) :
    dist (P.componentTwoCenterCutRectangleLiftPoint i t u)
      (P.componentTwoCenterCutRectangleLiftPoint i t 0) = |u| := by
  rw [componentTwoCenterCutRectangleLiftPoint_apply,
    componentTwoCenterCutRectangleLiftPoint_apply]
  have hrad : (P.componentTwoCenterCutRectangleCoordinates i t u).1 =
      (P.componentTwoCenterCutRectangleCoordinates i t 0).1 := rfl
  rw [hrad, dist_smul]
  have hcosh := gluingFinFermiPoint_cosh_dist 1
    (P.componentTwoCenterCutRectangleCoordinates i t u).1 u
    (P.componentTwoCenterCutRectangleCoordinates i t u).1 0
  have hcosh' : Real.cosh
      (dist (gluingFinFermiPoint 1
        (P.componentTwoCenterCutRectangleCoordinates i t u).1 u)
        (gluingFinFermiPoint 1
          (P.componentTwoCenterCutRectangleCoordinates i t u).1 0)) =
        Real.cosh |u| := by
    calc
      _ = Real.cosh u := by simpa using hcosh
      _ = Real.cosh |u| := (Real.cosh_abs u).symm
  exact Real.cosh_strictMonoOn.injOn
    (Set.mem_Ici.mpr dist_nonneg)
    (Set.mem_Ici.mpr (abs_nonneg u))
    hcosh'

/-- Every closed rectangle of transverse half-width smaller than `ε` lies
inside the actual `ε`-tube of the truncated cut. The width estimate is exact
in Fermi coordinates. -/
def componentTwoCenterCutRectangleTubeMap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ε δ : ℝ) (hδε : δ < ε) :
    (I × Set.Icc (-δ) δ) → P.componentTwoCenterLiftedCutTube i ε := by
  intro p
  refine ⟨P.componentTwoCenterCutRectangleLiftPoint i p.1 p.2, ?_⟩
  change Metric.infDist (P.componentTwoCenterCutRectangleLiftPoint i p.1 p.2)
    (P.componentTwoCenterLiftedCutSet i) < ε
  have hu : |(p.2 : ℝ)| ≤ δ := abs_le.mpr ⟨p.2.2.1, p.2.2.2⟩
  calc
    Metric.infDist (P.componentTwoCenterCutRectangleLiftPoint i p.1 p.2)
        (P.componentTwoCenterLiftedCutSet i) ≤
        dist (P.componentTwoCenterCutRectangleLiftPoint i p.1 p.2)
          (P.componentTwoCenterLiftedCutPoint i p.1) :=
      Metric.infDist_le_dist_of_mem ⟨p.1, rfl⟩
    _ = |(p.2 : ℝ)| := by
      rw [← P.componentTwoCenterCutRectangleLiftPoint_axis i p.1]
      exact P.componentTwoCenterCutRectangleLiftPoint_dist_axis i p.1 p.2
    _ ≤ δ := hu
    _ < ε := hδε

/-- The rectangle map is continuous as a map into the actual open cut tube. -/
theorem componentTwoCenterCutRectangleTubeMap_continuous
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ε δ : ℝ) (hδε : δ < ε) :
    Continuous (P.componentTwoCenterCutRectangleTubeMap i ε δ hδε) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : I × Set.Icc (-δ) δ =>
    P.componentTwoCenterGeodesicCoordinateHomeomorph i
      (P.componentTwoCenterCutRectangleCoordinates i p.1 p.2))
  exact (P.componentTwoCenterGeodesicCoordinateHomeomorph i).continuous.comp (by
    have hcut : Continuous (fun t : I =>
        (P.componentTwoCenterCutCoordinate i t : ℝ)) := by
      change Continuous (fun t : I =>
        (gluingRadius C g + t.val *
          (dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
              (Quotient.mk'' (P.centers i).2) - 2 * gluingRadius C g)) /
          dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
            (Quotient.mk'' (P.centers i).2))
      fun_prop
    unfold componentTwoCenterCutRectangleCoordinates
    have hparam : Continuous (fun p : I × Set.Icc (-δ) δ =>
        (P.componentTwoCenterCutCoordinate i p.1 : ℝ)) := hcut.comp continuous_fst
    have hlinear : Continuous (fun p : I × Set.Icc (-δ) δ =>
        (1 - (P.componentTwoCenterCutCoordinate i p.1 : ℝ)) *
            Real.log (P.componentTwoCenterGeodesicVerticalizer i • (P.centers i).1).im +
          (P.componentTwoCenterCutCoordinate i p.1 : ℝ) *
            Real.log (P.componentTwoCenterGeodesicVerticalizer i •
              (P.componentCenterClosestDeck i • (P.centers i).2)).im) := by
      exact ((continuous_const.sub hparam).mul continuous_const).add
        (hparam.mul continuous_const)
    exact hlinear.prodMk (continuous_subtype_val.comp continuous_snd))

/-- The literal lifted rectangle map is injective: its center axis projects
to the already embedded cut, and its second coordinate is preserved. -/
theorem componentTwoCenterCutRectangleLiftPoint_injective
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Function.Injective (fun p : I × ℝ =>
      P.componentTwoCenterCutRectangleLiftPoint i p.1 p.2) := by
  intro p q hpq
  have hcoords := (P.componentTwoCenterGeodesicCoordinateHomeomorph i).injective hpq
  have hrad : (P.componentTwoCenterCutRectangleCoordinates i p.1 p.2).1 =
      (P.componentTwoCenterCutRectangleCoordinates i q.1 q.2).1 :=
    congrArg Prod.fst hcoords
  have haxis : P.componentTwoCenterGeodesicCoordinateHomeomorph i
      (P.componentTwoCenterCutRectangleCoordinates i p.1 0) =
    P.componentTwoCenterGeodesicCoordinateHomeomorph i
      (P.componentTwoCenterCutRectangleCoordinates i q.1 0) :=
    congrArg (P.componentTwoCenterGeodesicCoordinateHomeomorph i)
      (Prod.ext hrad rfl)
  have hlift : P.componentTwoCenterLiftedCutPoint i p.1 =
      P.componentTwoCenterLiftedCutPoint i q.1 := by
    rw [← P.componentTwoCenterCutRectangleLiftPoint_axis i p.1,
      ← P.componentTwoCenterCutRectangleLiftPoint_axis i q.1]
    exact haxis
  have hcut : P.componentTwoCenterCutPoint i p.1 =
      P.componentTwoCenterCutPoint i q.1 := by
    simpa only [componentTwoCenterLiftedCutPoint_project] using
      congrArg (fun z : ℍ => (Quotient.mk'' z : (X i).Carrier)) hlift
  have ht := P.componentTwoCenterCutPoint_injective i hcut
  have hu : p.2 = q.2 := by
    simpa only [componentTwoCenterCutRectangleCoordinates] using
      congrArg Prod.snd hcoords
  exact Prod.ext ht hu

/-- Restricting the lifted rectangle map to its closed rectangular domain is
an embedding into the actual separated tube. -/
theorem componentTwoCenterCutRectangleTubeMap_isEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ε δ : ℝ) (hδε : δ < ε) :
    Topology.IsEmbedding (P.componentTwoCenterCutRectangleTubeMap i ε δ hδε) := by
  letI : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace (Set.Icc (-δ) δ) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace (I × Set.Icc (-δ) δ) := inferInstance
  exact ((P.componentTwoCenterCutRectangleTubeMap_continuous i ε δ hδε).isClosedEmbedding
    (fun p q hpq => by
      have hraw : P.componentTwoCenterCutRectangleLiftPoint i p.1 p.2 =
          P.componentTwoCenterCutRectangleLiftPoint i q.1 q.2 := by
        exact congrArg Subtype.val hpq
      have hpair : (p.1, (p.2 : ℝ)) = (q.1, (q.2 : ℝ)) :=
        P.componentTwoCenterCutRectangleLiftPoint_injective i hraw
      have ht : p.1 = q.1 := congrArg (fun x : I × ℝ => x.1) hpair
      have hu : (p.2 : ℝ) = (q.2 : ℝ) :=
        congrArg (fun x : I × ℝ => x.2) hpair
      exact Prod.ext ht (Subtype.ext hu))).isEmbedding

/-- The actual quotient projection of the cut rectangle into the surface
with its two active centers deleted. -/
def componentTwoCenterCutRectanglePuncturedMap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ε δ : ℝ) (hδε : δ < ε) (hε : ε < gluingRadius C g) :
    (I × Set.Icc (-δ) δ) → P.CenterPuncturedChainComponent i :=
  P.componentTwoCenterLiftedCutTubePuncturedProjection i ε hε ∘
    P.componentTwoCenterCutRectangleTubeMap i ε δ hδε

/-- Explicit representative formula for the rectangle's descended map. -/
@[simp]
theorem componentTwoCenterCutRectanglePuncturedMap_apply_val
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ε δ : ℝ) (hδε : δ < ε) (hε : ε < gluingRadius C g)
    (p : I × Set.Icc (-δ) δ) :
    (P.componentTwoCenterCutRectanglePuncturedMap i ε δ hδε hε p).1 =
      Quotient.mk'' (P.componentTwoCenterCutRectangleLiftPoint i p.1 p.2) := rfl

/-- The actual quotient projection remains an embedding on the closed
rectangle, by composing its lift embedding with the already-proved separated
tube projection. -/
theorem componentTwoCenterCutRectanglePuncturedMap_isEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ε δ : ℝ) (hδε : δ < ε) (hε : ε < gluingRadius C g)
    (hdisj : ∀ γ : (X i).deckGroup, γ ≠ 1 →
      Disjoint ((fun z : ℍ => γ • z) '' P.componentTwoCenterLiftedCutTube i ε)
        (P.componentTwoCenterLiftedCutTube i ε)) :
    Topology.IsEmbedding
      (P.componentTwoCenterCutRectanglePuncturedMap i ε δ hδε hε) := by
  letI : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace (Set.Icc (-δ) δ) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace (I × Set.Icc (-δ) δ) := inferInstance
  let hproj := P.componentTwoCenterLiftedCutTubePuncturedProjection_isOpenEmbedding
    i ε hε hdisj
  have hcont : Continuous
      (P.componentTwoCenterCutRectanglePuncturedMap i ε δ hδε hε) := by
    exact hproj.continuous.comp
      (P.componentTwoCenterCutRectangleTubeMap_continuous i ε δ hδε)
  have hinj : Function.Injective
      (P.componentTwoCenterCutRectanglePuncturedMap i ε δ hδε hε) := by
    intro p q hpq
    have hpqTube := hproj.injective hpq
    exact (P.componentTwoCenterCutRectangleTubeMap_isEmbedding i ε δ hδε).injective hpqTube
  exact (hcont.isClosedEmbedding hinj).isEmbedding

/-- The closed coordinate rectangle is homeomorphic to its literal image in
the actual punctured surface component. -/
noncomputable def componentTwoCenterCutRectanglePuncturedHomeomorphImage
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ε δ : ℝ) (hδε : δ < ε) (hε : ε < gluingRadius C g)
    (hdisj : ∀ γ : (X i).deckGroup, γ ≠ 1 →
      Disjoint ((fun z : ℍ => γ • z) '' P.componentTwoCenterLiftedCutTube i ε)
        (P.componentTwoCenterLiftedCutTube i ε)) :
    (I × Set.Icc (-δ) δ) ≃ₜ
      (P.componentTwoCenterCutRectanglePuncturedMap i ε δ hδε hε '' Set.univ) := by
  exact (Homeomorph.Set.univ (I × Set.Icc (-δ) δ)).symm.trans
    (Topology.IsEmbedding.homeomorphImage
      (P.componentTwoCenterCutRectanglePuncturedMap_isEmbedding i ε δ hδε hε hdisj)
      Set.univ)

/-- The central axis of the descended rectangle is exactly the physical cut
arc in the quotient. -/
theorem componentTwoCenterCutRectanglePuncturedMap_axis
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ε δ : ℝ) (hδε : δ < ε) (hε : ε < gluingRadius C g)
    (t : I) (hδ : 0 ≤ δ) :
    (P.componentTwoCenterCutRectanglePuncturedMap i ε δ hδε hε
      ⟨t, ⟨0, by linarith, hδ⟩⟩).1 = P.componentTwoCenterCutPoint i t := by
  rw [componentTwoCenterCutRectanglePuncturedMap_apply_val,
    componentTwoCenterCutRectangleLiftPoint_axis,
    componentTwoCenterLiftedCutPoint_project]

/-- The actual cut admits a positive-width closed coordinate rectangle which
embeds into the punctured surface and whose central axis is the actual cut.
The tube radius is obtained from the compact-cut deck-separation theorem; the
transverse half-width is chosen as half that radius. -/
theorem exists_componentTwoCenterCutRectangle
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    ∃ ε δ : ℝ, ∃ (hδε : δ < ε) (hε : ε < gluingRadius C g),
      0 < ε ∧ 0 < δ ∧
      (∀ γ : (X i).deckGroup, γ ≠ 1 →
        Disjoint ((fun z : ℍ => γ • z) '' P.componentTwoCenterLiftedCutTube i ε)
          (P.componentTwoCenterLiftedCutTube i ε)) ∧
      Topology.IsEmbedding
        (P.componentTwoCenterCutRectanglePuncturedMap i ε δ hδε hε) := by
  obtain ⟨ε, hε, hεradius, hdisj⟩ :=
    P.exists_componentTwoCenterLiftedCutTube_radius i
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδε : δ < ε := by dsimp [δ]; linarith
  refine ⟨ε, δ, hδε, hεradius, hε, hδ, hdisj, ?_⟩
  exact P.componentTwoCenterCutRectanglePuncturedMap_isEmbedding
    i ε δ hδε hεradius hdisj

#print axioms componentTwoCenterGeodesicCoordinateHomeomorph_core
#print axioms componentTwoCenterCutRectangleLiftPoint_dist_axis
#print axioms componentTwoCenterCutRectanglePuncturedMap_isEmbedding
#print axioms exists_componentTwoCenterCutRectangle

end

end SystolicGrowth.ExerciseGluingPreparation
