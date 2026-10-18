module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ConformalWarpLaplacian
public import Geometry.GluingConformalGaussianFormula

@[expose] public section

/-!
# Actual glued conformal curvature from the classical scalar PDE

The original canonical chart is used throughout. Its genuine seam
isothermal change converts the scalar PDE to the warped trace; exterior
interior charts use the literal Poincaré log factor. Thus the constructed
same-atlas conformal metric has the required intrinsic tensor identity.
The existence and regularity of the scalar solution remain analytic work.
-/

open Set Filter Bundle Manifold Riemannian
open scoped Manifold Topology ContDiff

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

local instance gluedConformalPDEComplexFinrankNonzero : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by simp [Complex.finrank_real_complex]⟩

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** The literal classical scalar equation in every isolated canonical
seam conformal neighborhood and every unchanged canonical interior
neighborhood. This contains no curvature conclusion for the new metric. -/
def GluedConformalClassicalPDE
    (P : ExerciseGluingPreparation C g n genera X) (u : P.GluedCarrier → ℝ) : Prop :=
  (∀ (b : P.GluedCarrier) (k : Fin (n - 1)) (θ : ℝ),
    chartAt ℂ b = P.seamAngularComplexChart k θ →
    (∀ l : Fin (n - 1), l ≠ k → b ∉ P.closedThinSeamCollar l) →
    Laplacian.laplacian (u ∘ (P.gluedCurvatureBoundedSeamConformalChart k θ).symm)
        (P.gluedCurvatureBoundedSeamConformalChart k θ b) =
      P.gluedCurvatureBoundedSeamConformalFactor
          (P.gluedCurvatureBoundedSeamConformalChart k θ b) ^ 2 *
        (P.gluedCurvatureBoundedGaussian b + Real.exp (2 * u b))) ∧
  (∀ b : P.GluedCarrier,
    P.IsGluedInteriorComplexChart (chartAt ℂ b) →
    (∀ k : Fin (n - 1), b ∉ P.closedThinSeamCollar k) →
    Laplacian.laplacian (u ∘ (chartAt ℂ b).symm) (chartAt ℂ b b) =
      (chartAt ℂ b b).im⁻¹ ^ 2 *
        (P.gluedCurvatureBoundedGaussian b + Real.exp (2 * u b)))

/-- **Math.** The actual isolated canonical seam PDE yields the full
intrinsic constant-curvature tensor of the constructed conformal metric. -/
theorem gluedConformalMetric_curvature_eq_of_seam_pde
    (P : ExerciseGluingPreparation C g n genera X) (u : P.GluedCarrier → ℝ)
    (hu : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞ u)
    (b : P.GluedCarrier) (k : Fin (n - 1)) (θ : ℝ)
    (hchart : chartAt ℂ b = P.seamAngularComplexChart k θ)
    (hother : ∀ l : Fin (n - 1), l ≠ k → b ∉ P.closedThinSeamCollar l)
    (hpde : Laplacian.laplacian (u ∘ (P.gluedCurvatureBoundedSeamConformalChart k θ).symm)
        (P.gluedCurvatureBoundedSeamConformalChart k θ b) =
      P.gluedCurvatureBoundedSeamConformalFactor
          (P.gluedCurvatureBoundedSeamConformalChart k θ b) ^ 2 *
        (P.gluedCurvatureBoundedGaussian b + Real.exp (2 * u b))) :
    let metric := conformalRiemannianMetric P.gluedCurvatureBoundedSmoothRiemannianMetric u hu
    ∀ x y : TangentSpace (modelWithCornersSelf ℝ ℂ) b,
      metric.metricInner b x x * metric.metricInner b y y - (metric.metricInner b x y) ^ 2 =
        metric.metricInner b (metric.leviCivitaConnection.curvatureOperatorAt b x y y) x := by
  let I := modelWithCornersSelf ℝ ℂ
  let e := P.seamAngularComplexChart k θ
  let ψ := P.gluedCurvatureBoundedSeamConformalChange
  let W := P.gluedCurvatureBoundedConformalWarp
  let f : ℂ → ℝ := u ∘ (extChartAt I b).symm
  let z := (extChartAt I b) b
  let metric := conformalRiemannianMetric P.gluedCurvatureBoundedSmoothRiemannianMetric u hu
  have hz : z ∈ (extChartAt I b).target := mem_extChartAt_target b
  have hpoint : (extChartAt I b).symm z = b := extChartAt_to_inv b
  have hcoord : z = e b := by
    simp only [z, extChartAt_coe, I, modelWithCornersSelf_coe, Function.comp_apply, id_eq, hchart, e]
  have hsymm : ((extChartAt I b).symm : ℂ → P.GluedCarrier) = e.symm := by
    simp only [extChartAt_coe_symm, I, modelWithCornersSelf_coe_symm, Function.comp_id, hchart, e]
  have hf : ContDiffOn ℝ ∞ f (extChartAt I b).target :=
    (hu.comp_contMDiffOn (contMDiffOn_extChartAt_symm b)).contDiffOn
  have hsymmCont : ContinuousAt (extChartAt I b).symm z :=
    (continuousOn_extChartAt_symm b).continuousAt ((isOpen_extChartAt_target b).mem_nhds hz)
  have hotherNear : ∀ᶠ q in 𝓝 z, ∀ l : Fin (n - 1), l ≠ k →
      (extChartAt I b).symm q ∉ P.closedThinSeamCollar l := by
    rw [Filter.eventually_all]
    intro l
    by_cases hl : l = k
    · exact Filter.Eventually.of_forall (fun _ h => (h hl).elim)
    · have hn : (extChartAt I b).symm z ∉ P.closedThinSeamCollar l := by rw [hpoint]; exact hother l hl
      filter_upwards [hsymmCont.preimage_mem_nhds
        ((P.closedThinSeamCollar_isCompact l).isClosed.isOpen_compl.mem_nhds hn)] with q hq _
      exact hq
  have hmetric : ∀ᶠ q in 𝓝 z, ∀ a d,
      chartMetricInner metric b q a d = conformalWarpMetricInner f W q a d := by
    filter_upwards [(isOpen_extChartAt_target b).mem_nhds hz, hotherNear] with q hq ho
    intro a d
    rw [conformalRiemannianMetric_chartMetricInner,
      P.gluedCurvatureBoundedSeam_chartMetricInner_eq k θ b hchart.symm hq a d ho]
    rfl
  have hb : b ∈ e.source := by simpa only [e, ← hchart] using (mem_chart_source ℂ b)
  have hthin : ∀ l : Fin (n - 1), l ≠ k → b ∉ P.thinSeamCollar l :=
    fun l hl h => hother l hl (P.thinSeamCollar_subset_closedThinSeamCollar l h)
  have hgauss : P.gluedCurvatureBoundedGaussian b = -(deriv (deriv W) z.re / W z.re) := by
    rw [P.gluedCurvatureBoundedGaussian_in_isolated_seam_chart k θ b hb hthin]
    change gluingWarpedGaussianCurvature W ((e b).re, (e b).im) = _
    rw [gluingWarpedGaussianCurvature_eq
      (P.gluedCurvatureBoundedConformalWarp_contDiff.of_le
        (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
      (P.gluedCurvatureBoundedConformalWarp_pos _), ← hcoord]
    exact neg_div _ _
  have hcomp : f ∘ ψ.symm = u ∘ (P.gluedCurvatureBoundedSeamConformalChart k θ).symm := by
    rw [gluedCurvatureBoundedSeamConformalChart, OpenPartialHomeomorph.coe_trans_symm]
    change (u ∘ (extChartAt I b).symm) ∘ ψ.symm = _
    rw [hsymm]
    rfl
  have hchange : ψ z = P.gluedCurvatureBoundedSeamConformalChart k θ b := by rw [hcoord]; rfl
  have hfactor : P.gluedCurvatureBoundedSeamConformalFactor (ψ z) = W z.re := by
    simp [ψ, W, gluedCurvatureBoundedSeamConformalFactor, gluedCurvatureBoundedSeamConformalChange,
      smoothWarpConformalFactor, smoothWarpConformalCoordinate]
  have hfz : f z = u b := by change u ((extChartAt I b).symm z) = _; rw [hpoint]
  have hiso : Laplacian.laplacian (f ∘ ψ.symm) (ψ z) =
      W z.re ^ 2 * (-(deriv (deriv W) z.re / W z.re) + Real.exp (2 * f z)) := by
    rw [hcomp]
    rw [← hchange] at hpde
    simpa only [hfactor, hgauss, hfz] using hpde
  have hwarp := smoothWarpConformalChart_pde_to_warped_trace
    P.gluedCurvatureBoundedConformalWarp_contDiff P.gluedCurvatureBoundedConformalWarp_pos
    (isOpen_extChartAt_target b) hf hz hiso
  have h := conformalWarpMetric_curvatureOperatorAt_eq_of_pde metric b f W hf
    P.gluedCurvatureBoundedConformalWarp_contDiff P.gluedCurvatureBoundedConformalWarp_pos hz hmetric hwarp
  rw [hpoint] at h
  exact h

private theorem exp_two_mul_add_log (v r : ℝ) (hr : 0 < r) :
    Real.exp (2 * (v + Real.log r)) = Real.exp (2 * v) * r ^ 2 := by
  rw [show 2 * (v + Real.log r) = 2 * v + (Real.log r + Real.log r) by ring,
    Real.exp_add, Real.exp_add, Real.exp_log hr, pow_two]

/-- **Math.** The literal unchanged-interior PDE, with its true
Poincaré coefficient, yields the same actual all-vector curvature identity. -/
theorem gluedConformalMetric_curvature_eq_of_interior_pde
    (P : ExerciseGluingPreparation C g n genera X) (u : P.GluedCarrier → ℝ)
    (hu : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞ u)
    (b : P.GluedCarrier) (hi : P.IsGluedInteriorComplexChart (chartAt ℂ b))
    (hout : ∀ k : Fin (n - 1), b ∉ P.closedThinSeamCollar k)
    (hpde : Laplacian.laplacian (u ∘ (chartAt ℂ b).symm) (chartAt ℂ b b) =
      (chartAt ℂ b b).im⁻¹ ^ 2 *
        (P.gluedCurvatureBoundedGaussian b + Real.exp (2 * u b))) :
    let metric := conformalRiemannianMetric P.gluedCurvatureBoundedSmoothRiemannianMetric u hu
    ∀ x y : TangentSpace (modelWithCornersSelf ℝ ℂ) b,
      metric.metricInner b x x * metric.metricInner b y y - (metric.metricInner b x y) ^ 2 =
        metric.metricInner b (metric.leviCivitaConnection.curvatureOperatorAt b x y y) x := by
  let I := modelWithCornersSelf ℝ ℂ
  let v : ℂ → ℝ := u ∘ (extChartAt I b).symm
  let l : ℂ → ℝ := fun q => Real.log (q.im⁻¹)
  let f : ℂ → ℝ := v + l
  let z := (extChartAt I b) b
  let metric := conformalRiemannianMetric P.gluedCurvatureBoundedSmoothRiemannianMetric u hu
  have hz : z ∈ (extChartAt I b).target := mem_extChartAt_target b
  have hpoint : (extChartAt I b).symm z = b := extChartAt_to_inv b
  have hcoord : z = chartAt ℂ b b := by
    simp only [z, extChartAt_coe, I, modelWithCornersSelf_coe, Function.comp_apply, id_eq]
  have hsymm : ((extChartAt I b).symm : ℂ → P.GluedCarrier) = (chartAt ℂ b).symm := by
    simp only [extChartAt_coe_symm, I, modelWithCornersSelf_coe_symm, Function.comp_id]
  have htarget : (extChartAt I b).target = (chartAt ℂ b).target := by
    simp [extChartAt, I]
  have hpos (q : ℂ) (hq : q ∈ (extChartAt I b).target) : 0 < q.im :=
    P.gluedInteriorComplexChart_target_im_pos _ hi (by rwa [htarget] at hq)
  have hv : ContDiffOn ℝ ∞ v (extChartAt I b).target :=
    (hu.comp_contMDiffOn (contMDiffOn_extChartAt_symm b)).contDiffOn
  have hl : ContDiffOn ℝ ∞ l (extChartAt I b).target :=
    (Complex.imCLM.contDiff.contDiffOn.inv (fun q hq => (hpos q hq).ne')).log
      (fun q hq => inv_ne_zero (hpos q hq).ne')
  have hf : ContDiffOn ℝ ∞ f (extChartAt I b).target := hv.add hl
  have hout' : ∀ k : Fin (n - 1), (extChartAt I b).symm z ∉ P.closedThinSeamCollar k := by
    rw [hpoint]; exact hout
  have hnear := P.gluedCurvatureBoundedInterior_outside_near b hz hout'
  have hmetric : ∀ᶠ q in 𝓝 z, ∀ a d,
      chartMetricInner metric b q a d = Real.exp (2 * f q) * (a.re * d.re + a.im * d.im) := by
    filter_upwards [hnear] with q hq
    intro a d
    rw [conformalRiemannianMetric_chartMetricInner,
      P.gluedCurvatureBoundedInterior_chartMetricInner_eq b hi hq.1
        (fun k h => hq.2 k (P.thinSeamCollar_subset_closedThinSeamCollar k h))]
    rw [show f q = v q + Real.log (q.im⁻¹) from rfl,
      exp_two_mul_add_log _ _ (inv_pos.mpr (hpos q hq.1))]
    simp only [v, Function.comp_apply, inv_pow]
    ring
  have hvz : v z = u b := by change u ((extChartAt I b).symm z) = _; rw [hpoint]
  have hK : P.gluedCurvatureBoundedGaussian b = -1 :=
    P.gluedCurvatureBoundedGaussian_eq_neg_one_of_outside b
      (fun k h => hout k (P.thinSeamCollar_subset_closedThinSeamCollar k h))
  have htwo : (2 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  have hlap : Laplacian.laplacian f z = Real.exp (2 * f z) := by
    rw [(hv.contDiffAt ((isOpen_extChartAt_target b).mem_nhds hz)).of_le htwo |>.laplacian_add
      ((hl.contDiffAt ((isOpen_extChartAt_target b).mem_nhds hz)).of_le htwo)]
    have hpde' : Laplacian.laplacian v z = z.im⁻¹ ^ 2 * (-1 + Real.exp (2 * v z)) := by
      rw [hvz]
      simpa only [v, hsymm, hcoord, hK] using hpde
    rw [hpde', poincareConformalLogFactor_laplacian (hpos z hz)]
    rw [show f z = v z + Real.log (z.im⁻¹) from rfl,
      exp_two_mul_add_log _ _ (inv_pos.mpr (hpos z hz))]
    ring
  have h := conformalEuclideanMetric_curvatureOperatorAt_eq_of_laplacian metric b f hf hz hmetric hlap
  rw [hpoint] at h
  exact h

/-- **Math.** Canonical seam selection on closed strips and the genuine
canonical atlas classification elsewhere exhaust the actual glued carrier.
The constructed conformal metric therefore has the desired intrinsic
curvature tensor globally from the literal classical scalar equation. -/
theorem gluedConformalMetric_curvature_eq
    (P : ExerciseGluingPreparation C g n genera X) (u : P.GluedCarrier → ℝ)
    (hu : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞ u)
    (hpde : P.GluedConformalClassicalPDE u) (b : P.GluedCarrier) :
    let metric := conformalRiemannianMetric P.gluedCurvatureBoundedSmoothRiemannianMetric u hu
    ∀ x y : TangentSpace (modelWithCornersSelf ℝ ℂ) b,
      metric.metricInner b x x * metric.metricInner b y y - (metric.metricInner b x y) ^ 2 =
        metric.metricInner b (metric.leviCivitaConnection.curvatureOperatorAt b x y y) x := by
  by_cases hc : ∃ k : Fin (n - 1), b ∈ P.closedThinSeamCollar k
  · obtain ⟨k, hk⟩ := hc
    obtain ⟨θ, hchart⟩ := P.gluedCurvatureBounded_chartAt_eq_seam_of_mem_closedThinSeamCollar b k hk
    have hother : ∀ l : Fin (n - 1), l ≠ k → b ∉ P.closedThinSeamCollar l :=
      fun l hl h => Set.disjoint_left.mp (P.closedThinSeamCollar_disjoint hl) h hk
    exact P.gluedConformalMetric_curvature_eq_of_seam_pde u hu b k θ hchart hother
      (hpde.1 b k θ hchart hother)
  · have hout : ∀ k : Fin (n - 1), b ∉ P.closedThinSeamCollar k :=
      fun k hk => hc ⟨k, hk⟩
    rcases P.gluedCurvatureBounded_chartAt_is_seam_or_interior b with hi | ⟨k, θ, hchart⟩
    · exact P.gluedConformalMetric_curvature_eq_of_interior_pde u hu b hi hout (hpde.2 b hi hout)
    · have hother : ∀ l : Fin (n - 1), l ≠ k → b ∉ P.closedThinSeamCollar l := fun l _ => hout l
      exact P.gluedConformalMetric_curvature_eq_of_seam_pde u hu b k θ hchart hother
        (hpde.1 b k θ hchart hother)

#print axioms gluedConformalMetric_curvature_eq_of_seam_pde
#print axioms gluedConformalMetric_curvature_eq_of_interior_pde
#print axioms gluedConformalMetric_curvature_eq

end

end SystolicGrowth.ExerciseGluingPreparation
