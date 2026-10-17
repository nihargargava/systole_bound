module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingWarpedGaussianCurvature
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Exponential.GaussLemma

@[expose] public section

/-!
# Actual exponential polar Gram tensor

The library Gauss lemma makes the radial differential of the exponential
map unit length and orthogonal to its angular differential. Consequently
the actual Gram tensor in exponential polar coordinates is
`dt² + J(θ,t)² dθ²`, where `J` is the angular differential length, and its
determinant-area density is precisely `J`. These local metric identities do
not presume a Jacobi equation or an embedded disk-area estimate.
-/

open Bundle Manifold Set Metric
open scoped Manifold ContDiff

namespace SystolicGrowth

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space (TangentBundle I M)]

/-- **Math.** Initial unit radial direction in an orthonormal two-frame. -/
def exponentialPolarUnit (e : Fin 2 → E) (θ : ℝ) : E :=
  Real.cos θ • e 0 + Real.sin θ • e 1

/-- **Math.** The angular derivative of the initial unit radial direction. -/
def exponentialPolarNormal (e : Fin 2 → E) (θ : ℝ) : E :=
  (-Real.sin θ) • e 0 + Real.cos θ • e 1

/-- **Math.** The actual fixed-chart reading of the exponential map at its base point. -/
def exponentialChartMap (g : Riemannian.RiemannianMetric I M) (p : M) (w : E) : E :=
  extChartAt I p (Riemannian.Exponential.expMap (I := I) g p (w : TangentSpace I p))

/-- **Math.** The literal exponential map in radial and real angular parameters. -/
def exponentialPolarChart (g : Riemannian.RiemannianMetric I M) (p : M)
    (e : Fin 2 → E) (q : ℝ × ℝ) : E :=
  exponentialChartMap g p (q.1 • exponentialPolarUnit e q.2)

/-- **Math.** The radial and angular images under the actual exponential differential. -/
def exponentialPolarFrame (g : Riemannian.RiemannianMetric I M) (p : M)
    (e : Fin 2 → E) (r θ : ℝ) (i : Fin 2) : E :=
  fderiv ℝ (exponentialChartMap g p) (r • exponentialPolarUnit e θ)
    (if i = 0 then exponentialPolarUnit e θ else r • exponentialPolarNormal e θ)

/-- **Math.** Gram matrix of the actual exponential radial and angular differentials,
evaluated in the actual metric at their exponential image. -/
def exponentialPolarGram (g : Riemannian.RiemannianMetric I M) (p : M)
    (e : Fin 2 → E) (r θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => Riemannian.chartMetricInner (I := I) g p
    (exponentialPolarChart g p e (r, θ))
    (exponentialPolarFrame g p e r θ i) (exponentialPolarFrame g p e r θ j)

/-- **Math.** The actual length of the angular exponential differential. Its Jacobi
equation is a separate geometric property, not part of this definition. -/
def exponentialPolarAngularLength (g : Riemannian.RiemannianMetric I M) (p : M)
    (e : Fin 2 → E) (θ r : ℝ) : ℝ :=
  Real.sqrt (exponentialPolarGram g p e r θ 1 1)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem exponentialPolarUnit_hasDerivAt (e : Fin 2 → E) (θ : ℝ) :
    HasDerivAt (exponentialPolarUnit e) (exponentialPolarNormal e θ) θ := by
  exact ((Real.hasDerivAt_cos θ).smul_const (e 0)).add
    ((Real.hasDerivAt_sin θ).smul_const (e 1))

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space (TangentBundle I M)] in
/-- **Math.** Rotation preserves orthonormality in the actual metric at the exponential
base point, without identifying it with the ambient model inner product. -/
theorem exponentialPolarDirections_chartMetric
    (g : Riemannian.RiemannianMetric I M) (p : M) (e : Fin 2 → E)
    (he : ∀ i j : Fin 2,
      Riemannian.chartMetricInner (I := I) g p (extChartAt I p p) (e i) (e j) =
        if i = j then 1 else 0) (θ : ℝ) :
    Riemannian.chartMetricInner (I := I) g p (extChartAt I p p)
        (exponentialPolarUnit e θ) (exponentialPolarUnit e θ) = 1 ∧
      Riemannian.chartMetricInner (I := I) g p (extChartAt I p p)
        (exponentialPolarUnit e θ) (exponentialPolarNormal e θ) = 0 ∧
      Riemannian.chartMetricInner (I := I) g p (extChartAt I p p)
        (exponentialPolarNormal e θ) (exponentialPolarNormal e θ) = 1 := by
  simp only [exponentialPolarUnit, exponentialPolarNormal,
    Riemannian.chartMetricInner_add_left, Riemannian.chartMetricInner_add_right,
    Riemannian.chartMetricInner_smul_left, Riemannian.chartMetricInner_smul_right, he]
  norm_num
  constructor
  · nlinarith [Real.sin_sq_add_cos_sq θ]
  · constructor
    · ring
    · nlinarith [Real.sin_sq_add_cos_sq θ]

omit [NeZero (Module.finrank ℝ E)] in
/-- **Math.** A genuine neighborhood of the exponential origin has the actual polar
differentials, the diagonal polar metric, and its angular-length area
density. The Gauss identities and differentiability are obtained internally
from the library exponential map, rather than supplied as hypotheses. -/
theorem exists_exponentialPolarMetric_ball
    (g : Riemannian.RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ w : E, ‖w‖ < ρ →
        (w : TangentSpace I p) ∈ Riemannian.Exponential.expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ρ →
        Riemannian.Exponential.expMap (I := I) g p (w : TangentSpace I p) ∈
          (chartAt H p).source) ∧
      (∀ (e : Fin 2 → E),
        (∀ i j : Fin 2,
          Riemannian.chartMetricInner (I := I) g p (extChartAt I p p) (e i) (e j) =
            if i = j then 1 else 0) →
        ∀ r θ : ℝ, 0 < r → ‖r • exponentialPolarUnit e θ‖ < ρ →
          HasDerivAt (fun t => exponentialPolarChart g p e (t, θ))
            (exponentialPolarFrame g p e r θ 0) r ∧
          HasDerivAt (fun a => exponentialPolarChart g p e (r, a))
            (exponentialPolarFrame g p e r θ 1) θ ∧
          exponentialPolarGram g p e r θ =
            gluingWarpedMetric (exponentialPolarAngularLength g p e θ) (r, θ) ∧
          (exponentialPolarGram g p e r θ).det =
            exponentialPolarGram g p e r θ 1 1 ∧
          Real.sqrt (exponentialPolarGram g p e r θ).det =
            exponentialPolarAngularLength g p e θ r) := by
  obtain ⟨ρG, hρG, hdom, hsrc, hgauss⟩ :=
    Riemannian.Exponential.exists_gauss_lemma_ball (I := I) g p
  obtain ⟨ρC, hρC, _, _, hC2⟩ :=
    Riemannian.Exponential.exists_contDiffOn_two_extChartAt_expMap_ball (I := I) g p
  refine ⟨min ρG ρC, lt_min hρG hρC,
    (fun w hw => hdom w (hw.trans_le (min_le_left _ _))),
    (fun w hw => hsrc w (hw.trans_le (min_le_left _ _))), ?_⟩
  intro e he r θ hr hv
  let U := exponentialPolarUnit e θ
  let N := exponentialPolarNormal e θ
  let f := exponentialChartMap g p
  have hvG : ‖r • U‖ < ρG := hv.trans_le (min_le_left _ _)
  have hvC : ‖r • U‖ < ρC := hv.trans_le (min_le_right _ _)
  have hdiff : DifferentiableAt ℝ f (r • U) :=
    (hC2.contDiffAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hvC))).differentiableAt
      (by norm_num)
  have hrad : HasDerivAt (fun t => exponentialPolarChart g p e (t, θ))
      (exponentialPolarFrame g p e r θ 0) r := by
    simpa [exponentialPolarChart, exponentialPolarFrame, U, f, Function.comp_def] using
      hdiff.hasFDerivAt.comp_hasDerivAt r ((hasDerivAt_id r).smul_const U)
  have hang : HasDerivAt (fun a => exponentialPolarChart g p e (r, a))
      (exponentialPolarFrame g p e r θ 1) θ := by
    simpa [exponentialPolarChart, exponentialPolarFrame, U, N, f, Function.comp_def] using
      hdiff.hasFDerivAt.comp_hasDerivAt θ
        ((exponentialPolarUnit_hasDerivAt e θ).const_smul r)
  have hrot := exponentialPolarDirections_chartMetric g p e he θ
  have h00 : exponentialPolarGram g p e r θ 0 0 = 1 := by
    have h := hgauss (r • U) U hvG
    change Riemannian.chartMetricInner (I := I) g p (f (r • U))
      (fderiv ℝ f (r • U) (r • U)) (fderiv ℝ f (r • U) U) = _ at h
    simp only [map_smul, Riemannian.chartMetricInner_smul_left] at h
    rw [show Riemannian.chartMetricInner (I := I) g p (extChartAt I p p) U U = 1
      from hrot.1, mul_one] at h
    have hcancel := mul_left_cancel₀ hr.ne' (h.trans (mul_one r).symm)
    change Riemannian.chartMetricInner (I := I) g p (f (r • U))
      (fderiv ℝ f (r • U) U) (fderiv ℝ f (r • U) U) = 1
    exact hcancel
  have h01 : exponentialPolarGram g p e r θ 0 1 = 0 := by
    have h := hgauss (r • U) (r • N) hvG
    change Riemannian.chartMetricInner (I := I) g p (f (r • U))
      (fderiv ℝ f (r • U) (r • U)) (fderiv ℝ f (r • U) (r • N)) = _ at h
    simp only [map_smul, Riemannian.chartMetricInner_smul_left,
      Riemannian.chartMetricInner_smul_right] at h
    rw [show Riemannian.chartMetricInner (I := I) g p (extChartAt I p p) U N = 0
      from hrot.2.1, mul_zero, mul_zero] at h
    change Riemannian.chartMetricInner (I := I) g p (f (r • U))
      (fderiv ℝ f (r • U) U) (fderiv ℝ f (r • U) (r • N)) = 0
    rw [map_smul, Riemannian.chartMetricInner_smul_right]
    exact (mul_eq_zero.mp h).resolve_left hr.ne'
  have h10 : exponentialPolarGram g p e r θ 1 0 = 0 := by
    rw [exponentialPolarGram, Riemannian.chartMetricInner_symm]
    exact h01
  have h11 : 0 ≤ exponentialPolarGram g p e r θ 1 1 := by
    change 0 ≤ Riemannian.chartMetricInner (I := I) g p
      (extChartAt I p (Riemannian.Exponential.expMap (I := I) g p
        ((r • U : E) : TangentSpace I p))) _ _
    rw [Riemannian.chartMetricInner_extChartAt_eq_metricInner (I := I) g p
      (hsrc (r • U) hvG)]
    exact g.metricInner_self_nonneg _ _
  have hmetric : exponentialPolarGram g p e r θ =
      gluingWarpedMetric (exponentialPolarAngularLength g p e θ) (r, θ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gluingWarpedMetric, exponentialPolarAngularLength, h00, h01, h10,
        Real.sq_sqrt h11]
  have hdet : (exponentialPolarGram g p e r θ).det =
      exponentialPolarGram g p e r θ 1 1 := by
    simp [Matrix.det_fin_two, h00, h01, h10]
  refine ⟨hrad, hang, hmetric, hdet, ?_⟩
  rw [hdet]
  rfl

#print axioms exponentialPolarDirections_chartMetric
#print axioms exists_exponentialPolarMetric_ball

end
end SystolicGrowth
