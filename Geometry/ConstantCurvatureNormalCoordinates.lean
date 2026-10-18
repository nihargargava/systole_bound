module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ExponentialGlobalAngularConstantCurvature
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Manifold.HadamardComplete
public import Vendored.DoCarmo.LeeLib.Ch02.Isometry
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

@[expose] public section

/-!
# Isometry from actual constant-curvature normal coordinates

The actual exponential differentials in two curvature-minus-one surfaces
have matching metric pullbacks under an initial tangent metric isometry.
The origin is treated by the actual identity exponential differential.
-/

open Set Bundle Manifold Riemannian
open scoped ContDiff Manifold Topology

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

namespace SystolicGrowth

local instance constantCurvatureNormalComplexFinrankNonzero : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by rw [Complex.finrank_real_complex]; norm_num⟩

variable {M N : Type*} [MetricSpace M] [MetricSpace N]
  [ChartedSpace ℂ M] [ChartedSpace ℂ N]
  [IsManifold (modelWithCornersSelf ℝ ℂ) ∞ M]
  [IsManifold (modelWithCornersSelf ℝ ℂ) ∞ N]
  [SigmaCompactSpace M] [SigmaCompactSpace N] [CompleteSpace M] [CompleteSpace N]

omit [SigmaCompactSpace M] [CompleteSpace M] in
private theorem exists_chartMetric_polar
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M) (p : M)
    (e : Fin 2 → ℂ)
    (he : ∀ i j : Fin 2,
      chartMetricInner g p (extChartAt (modelWithCornersSelf ℝ ℂ) p p) (e i) (e j) =
        if i = j then 1 else 0) (w : ℂ) (hw : w ≠ 0) :
    ∃ r θ : ℝ, 0 < r ∧ w = r • exponentialPolarUnit e θ := by
  let B := chartMetricInner g p (extChartAt (modelWithCornersSelf ℝ ℂ) p p)
  let z : ℂ := ⟨B w (e 0), B w (e 1)⟩
  have hexp : w = B w (e 0) • e 0 + B w (e 1) • e 1 := by
    simpa only [Fin.sum_univ_two] using
      Jacobi.frameExpansion g p (extChartAt (modelWithCornersSelf ℝ ℂ) p p) e
        (by simp [Complex.finrank_real_complex]) he w
  have hz : z ≠ 0 := by
    intro hzero
    have h0 : B w (e 0) = 0 := congrArg Complex.re hzero
    have h1 : B w (e 1) = 0 := congrArg Complex.im hzero
    apply hw
    rw [hexp, h0, h1, zero_smul, zero_smul, zero_add]
  refine ⟨‖z‖, z.arg, norm_pos_iff.mpr hz, ?_⟩
  rw [exponentialPolarUnit, smul_add, smul_smul, smul_smul,
    Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg]
  exact hexp

/-- **Math.** Actual exponential metric pullbacks at corresponding polar
points agree under the initial tangent metric isometry. Both all-vector
tensor formulas are derived from the actual curvature, not assumed. -/
theorem constantCurvature_exponential_metricInner_map_polar
    (gM : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M)
    (gN : RiemannianMetric (modelWithCornersSelf ℝ ℂ) N)
    (hgM : gM.IsRiemannianDist) (hgN : gN.IsRiemannianDist) (p : M) (q : N)
    (A : ℂ ≃L[ℝ] ℂ)
    (hA : ∀ u v : ℂ,
      chartMetricInner gN q (extChartAt (modelWithCornersSelf ℝ ℂ) q q) (A u) (A v) =
        chartMetricInner gM p (extChartAt (modelWithCornersSelf ℝ ℂ) p p) u v)
    (hKM : ∀ (a : M) (u v : TangentSpace (modelWithCornersSelf ℝ ℂ) a),
      gM.metricInner a u u * gM.metricInner a v v -
        gM.metricInner a u v * gM.metricInner a u v =
      gM.metricInner a (gM.leviCivitaConnection.curvatureOperatorAt a u v v) u)
    (hKN : ∀ (a : N) (u v : TangentSpace (modelWithCornersSelf ℝ ℂ) a),
      gN.metricInner a u u * gN.metricInner a v v -
        gN.metricInner a u v * gN.metricInner a u v =
      gN.metricInner a (gN.leviCivitaConnection.curvatureOperatorAt a u v v) u)
    (e : Fin 2 → ℂ)
    (he : ∀ i j : Fin 2,
      chartMetricInner gM p (extChartAt (modelWithCornersSelf ℝ ℂ) p p) (e i) (e j) =
        if i = j then 1 else 0) (r θ : ℝ) (hr : 0 < r)
    (ζM : M) (ζN : N)
    (hζM : Exponential.expMapGlobal gM hgM p (r • exponentialPolarUnit e θ) ∈
      (chartAt ℂ ζM).source)
    (hζN : Exponential.expMapGlobal gN hgN q (A (r • exponentialPolarUnit e θ)) ∈
      (chartAt ℂ ζN).source) (u v : ℂ) :
    chartMetricInner gN ζN
      (globalExponentialChartMap gN hgN q ζN (A (r • exponentialPolarUnit e θ)))
      (fderiv ℝ (globalExponentialChartMap gN hgN q ζN)
        (A (r • exponentialPolarUnit e θ)) (A u))
      (fderiv ℝ (globalExponentialChartMap gN hgN q ζN)
        (A (r • exponentialPolarUnit e θ)) (A v)) =
    chartMetricInner gM ζM
      (globalExponentialChartMap gM hgM p ζM (r • exponentialPolarUnit e θ))
      (fderiv ℝ (globalExponentialChartMap gM hgM p ζM)
        (r • exponentialPolarUnit e θ) u)
      (fderiv ℝ (globalExponentialChartMap gM hgM p ζM)
        (r • exponentialPolarUnit e θ) v) := by
  let f : Fin 2 → ℂ := fun i => A (e i)
  have hf : ∀ i j : Fin 2,
      chartMetricInner gN q (extChartAt (modelWithCornersSelf ℝ ℂ) q q) (f i) (f j) =
        if i = j then 1 else 0 := fun i j => (hA (e i) (e j)).trans (he i j)
  have hU : exponentialPolarUnit f θ = A (exponentialPolarUnit e θ) := by
    simp only [exponentialPolarUnit, f, map_add, map_smul]
  have hN : exponentialPolarNormal f θ = A (exponentialPolarNormal e θ) := by
    simp only [exponentialPolarNormal, f, map_add, map_smul]
  have hpoint : r • exponentialPolarUnit f θ = A (r • exponentialPolarUnit e θ) := by
    rw [hU, map_smul]
  have hNmetric := globalExponentialChartMap_metricInner_eq_hyperbolic gN hgN q ζN f θ r hr
    hf Complex.finrank_real_complex hKN (by simpa only [hpoint] using hζN) (A u) (A v)
  have hMmetric := globalExponentialChartMap_metricInner_eq_hyperbolic gM hgM p ζM e θ r hr
    he Complex.finrank_real_complex hKM hζM u v
  rw [hpoint, hU, hN, hA, hA, hA, hA] at hNmetric
  exact hNmetric.trans hMmetric.symm

/-- **Math.** Actual exponential metric pullbacks match at every initial
vector, including the origin. The polar frame is constructed from the
actual initial metric, and no tensor-preservation conclusion is assumed. -/
theorem constantCurvature_exponential_metricInner_map
    (gM : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M)
    (gN : RiemannianMetric (modelWithCornersSelf ℝ ℂ) N)
    (hgM : gM.IsRiemannianDist) (hgN : gN.IsRiemannianDist) (p : M) (q : N)
    (A : ℂ ≃L[ℝ] ℂ)
    (hA : ∀ u v : ℂ,
      chartMetricInner gN q (extChartAt (modelWithCornersSelf ℝ ℂ) q q) (A u) (A v) =
        chartMetricInner gM p (extChartAt (modelWithCornersSelf ℝ ℂ) p p) u v)
    (hKM : ∀ (a : M) (u v : TangentSpace (modelWithCornersSelf ℝ ℂ) a),
      gM.metricInner a u u * gM.metricInner a v v -
        gM.metricInner a u v * gM.metricInner a u v =
      gM.metricInner a (gM.leviCivitaConnection.curvatureOperatorAt a u v v) u)
    (hKN : ∀ (a : N) (u v : TangentSpace (modelWithCornersSelf ℝ ℂ) a),
      gN.metricInner a u u * gN.metricInner a v v -
        gN.metricInner a u v * gN.metricInner a u v =
      gN.metricInner a (gN.leviCivitaConnection.curvatureOperatorAt a u v v) u)
    (w u v : ℂ) :
    chartMetricInner gN (Exponential.expMapGlobal gN hgN q (A w))
      (globalExponentialChartMap gN hgN q (Exponential.expMapGlobal gN hgN q (A w)) (A w))
      (fderiv ℝ (globalExponentialChartMap gN hgN q
        (Exponential.expMapGlobal gN hgN q (A w))) (A w) (A u))
      (fderiv ℝ (globalExponentialChartMap gN hgN q
        (Exponential.expMapGlobal gN hgN q (A w))) (A w) (A v)) =
    chartMetricInner gM (Exponential.expMapGlobal gM hgM p w)
      (globalExponentialChartMap gM hgM p (Exponential.expMapGlobal gM hgM p w) w)
      (fderiv ℝ (globalExponentialChartMap gM hgM p
        (Exponential.expMapGlobal gM hgM p w)) w u)
      (fderiv ℝ (globalExponentialChartMap gM hgM p
        (Exponential.expMapGlobal gM hgM p w)) w v) := by
  by_cases hw : w = 0
  · subst w
    simp only [map_zero, Exponential.expMapGlobal_zero,
      globalExponentialChartMap_fderiv_zero, ContinuousLinearMap.id_apply,
      globalExponentialChartMap]
    exact hA u v
  · have hframe : ∃ e : Fin 2 → ℂ, ∀ i j : Fin 2,
        chartMetricInner gM p (extChartAt (modelWithCornersSelf ℝ ℂ) p p) (e i) (e j) =
          if i = j then 1 else 0 := by
      obtain ⟨e, he⟩ := Jacobi.exists_chartOrthonormalBasis_self gM p
      let f : Fin 2 ≃ Fin (Module.finrank ℝ ℂ) := (finCongr Complex.finrank_real_complex).symm
      refine ⟨fun i => e (f i), ?_⟩
      intro i j
      simpa only [f.apply_eq_iff_eq] using he (f i) (f j)
    obtain ⟨e, he⟩ := hframe
    obtain ⟨r, θ, hr, hpolar⟩ := exists_chartMetric_polar gM p e he w hw
    rw [hpolar]
    exact constantCurvature_exponential_metricInner_map_polar gM gN hgM hgN p q A hA hKM hKN
      e he r θ hr _ _ (mem_chart_source ℂ _) (mem_chart_source ℂ _) u v

private theorem mfderiv_expMapGlobal_eq_chart_fderiv
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M) (hg : g.IsRiemannianDist)
    (p : M) (w : ℂ) :
    mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      (fun z : ℂ => Exponential.expMapGlobal g hg p z) w =
      fderiv ℝ (globalExponentialChartMap g hg p (Exponential.expMapGlobal g hg p w)) w := by
  have hexp := (Exponential.contMDiff_expMapGlobal g hg p).mdifferentiable (by simp) w
  have hchart := mdifferentiableAt_extChartAt (I := modelWithCornersSelf ℝ ℂ)
    (mem_chart_source ℂ (Exponential.expMapGlobal g hg p w))
  have hcomp := mfderiv_comp w hchart hexp
  rw [mfderiv_extChartAt_self, ContinuousLinearMap.id_comp, mfderiv_eq_fderiv] at hcomp
  exact hcomp.symm

/-- **Math.** The equality of actual exponential metric pullbacks is
intrinsic, in the manifold differential, not just a terminal-chart formula. -/
theorem constantCurvature_exponential_metricInner_mfderiv_map
    (gM : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M)
    (gN : RiemannianMetric (modelWithCornersSelf ℝ ℂ) N)
    (hgM : gM.IsRiemannianDist) (hgN : gN.IsRiemannianDist) (p : M) (q : N)
    (A : ℂ ≃L[ℝ] ℂ)
    (hA : ∀ u v : ℂ,
      chartMetricInner gN q (extChartAt (modelWithCornersSelf ℝ ℂ) q q) (A u) (A v) =
        chartMetricInner gM p (extChartAt (modelWithCornersSelf ℝ ℂ) p p) u v)
    (hKM : ∀ (a : M) (u v : TangentSpace (modelWithCornersSelf ℝ ℂ) a),
      gM.metricInner a u u * gM.metricInner a v v -
        gM.metricInner a u v * gM.metricInner a u v =
      gM.metricInner a (gM.leviCivitaConnection.curvatureOperatorAt a u v v) u)
    (hKN : ∀ (a : N) (u v : TangentSpace (modelWithCornersSelf ℝ ℂ) a),
      gN.metricInner a u u * gN.metricInner a v v -
        gN.metricInner a u v * gN.metricInner a u v =
      gN.metricInner a (gN.leviCivitaConnection.curvatureOperatorAt a u v v) u)
    (w u v : ℂ) :
    gN.metricInner (Exponential.expMapGlobal gN hgN q (A w))
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
        (fun z : ℂ => Exponential.expMapGlobal gN hgN q z) (A w) (A u))
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
        (fun z : ℂ => Exponential.expMapGlobal gN hgN q z) (A w) (A v)) =
    gM.metricInner (Exponential.expMapGlobal gM hgM p w)
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
        (fun z : ℂ => Exponential.expMapGlobal gM hgM p z) w u)
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
        (fun z : ℂ => Exponential.expMapGlobal gM hgM p z) w v) := by
  have h := constantCurvature_exponential_metricInner_map gM gN hgM hgN p q A hA hKM hKN w u v
  unfold globalExponentialChartMap at h
  rw [chartMetricInner_extChartAt_eq_metricInner gN _ (mem_chart_source ℂ _),
    chartMetricInner_extChartAt_eq_metricInner gM _ (mem_chart_source ℂ _)] at h
  simp only [trivializationAt_symm_self] at h
  rw [mfderiv_expMapGlobal_eq_chart_fderiv, mfderiv_expMapGlobal_eq_chart_fderiv]
  exact h

section Hadamard

variable [ConnectedSpace M] [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]
  [ConnectedSpace N] [SimplyConnectedSpace N] [LocallyPathConnectedSpace N]

omit [CompleteSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
  [LocallyPathConnectedSpace M] in
theorem Internal.ConstantCurvatureNormalCoordinatesHelpers.constantCurvature_curvatureOperator_pair_nonneg
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M)
    (hK : ∀ (a : M) (u v : TangentSpace (modelWithCornersSelf ℝ ℂ) a),
      g.metricInner a u u * g.metricInner a v v -
        g.metricInner a u v * g.metricInner a u v =
      g.metricInner a (g.leviCivitaConnection.curvatureOperatorAt a u v v) u)
    (a : M) (u v : TangentSpace (modelWithCornersSelf ℝ ℂ) a) :
    0 ≤ g.metricInner a (g.leviCivitaConnection.curvatureOperatorAt a u v v) u := by
  rw [← hK a u v]
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : M → Type) :=
    ⟨g.toRiemannianMetric⟩
  exact sub_nonneg.mpr (real_inner_mul_inner_self_le u v)

/-- **Math.** The genuine Hadamard exponential diffeomorphism expressed on
the original complex model plane, with its original smooth structure. -/
def constantCurvatureExpDiffeomorph
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M) (hg : g.IsRiemannianDist) (p : M)
    (hK : ∀ (a : M) (u v : TangentSpace (modelWithCornersSelf ℝ ℂ) a),
      g.metricInner a u u * g.metricInner a v v -
        g.metricInner a u v * g.metricInner a u v =
      g.metricInner a (g.leviCivitaConnection.curvatureOperatorAt a u v v) u) :
    Diffeomorph (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ℂ M ∞ := by
  let H := Jacobi.hadamardDiffeomorphOfNonpos_complete g hg p
    (Internal.ConstantCurvatureNormalCoordinatesHelpers.constantCurvature_curvatureOperator_pair_nonneg g hK)
  have hto : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      (HadamardModel.toModel (E := ℂ)) := by
    intro v
    apply (contMDiffAt_extChartAt (I := modelWithCornersSelf ℝ ℂ) (x := v)).congr_of_eventuallyEq
    filter_upwards with y
    exact (HadamardModel.extChartAt_hadamard v y).symm
  exact
    { toEquiv := H.toEquiv
      contMDiff_toFun := by
        have hmap : (fun w : ℂ => H w) = fun w : ℂ => Exponential.expMapGlobal g hg p w := by
          funext w
          exact congrFun (Jacobi.hadamardDiffeomorphOfNonpos_complete_coe g hg p
            (Internal.ConstantCurvatureNormalCoordinatesHelpers.constantCurvature_curvatureOperator_pair_nonneg g hK))
            (w : HadamardModel ℂ)
        change ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞ (fun w : ℂ => H w)
        rw [hmap]
        exact Exponential.contMDiff_expMapGlobal g hg p
      contMDiff_invFun := hto.comp H.symm.contMDiff }

/-- **Math.** The normal-coordinate diffeomorphism is the actual composition
`exp_q ∘ A ∘ exp_p⁻¹` of genuine Hadamard exponentials. -/
def constantCurvatureNormalDiffeomorph
    (gM : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M)
    (gN : RiemannianMetric (modelWithCornersSelf ℝ ℂ) N)
    (hgM : gM.IsRiemannianDist) (hgN : gN.IsRiemannianDist) (p : M) (q : N)
    (hKM : ∀ (a : M) (u v : TangentSpace (modelWithCornersSelf ℝ ℂ) a),
      gM.metricInner a u u * gM.metricInner a v v -
        gM.metricInner a u v * gM.metricInner a u v =
      gM.metricInner a (gM.leviCivitaConnection.curvatureOperatorAt a u v v) u)
    (hKN : ∀ (a : N) (u v : TangentSpace (modelWithCornersSelf ℝ ℂ) a),
      gN.metricInner a u u * gN.metricInner a v v -
        gN.metricInner a u v * gN.metricInner a u v =
      gN.metricInner a (gN.leviCivitaConnection.curvatureOperatorAt a u v v) u)
    (A : ℂ ≃L[ℝ] ℂ) :
    Diffeomorph (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) M N ∞ :=
  (((constantCurvatureExpDiffeomorph gM hgM p hKM).symm).trans A.toDiffeomorph).trans
    (constantCurvatureExpDiffeomorph gN hgN q hKN)

/-- **Math.** The actual normal-coordinate diffeomorphism preserves the
full Riemannian tensor. Its only metric identification input is the initial
tangent isometry; actual constant curvature supplies the global conclusion. -/
theorem constantCurvatureNormalDiffeomorph_isIsometry
    (gM : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M)
    (gN : RiemannianMetric (modelWithCornersSelf ℝ ℂ) N)
    (hgM : gM.IsRiemannianDist) (hgN : gN.IsRiemannianDist) (p : M) (q : N)
    (hKM : ∀ (a : M) (u v : TangentSpace (modelWithCornersSelf ℝ ℂ) a),
      gM.metricInner a u u * gM.metricInner a v v -
        gM.metricInner a u v * gM.metricInner a u v =
      gM.metricInner a (gM.leviCivitaConnection.curvatureOperatorAt a u v v) u)
    (hKN : ∀ (a : N) (u v : TangentSpace (modelWithCornersSelf ℝ ℂ) a),
      gN.metricInner a u u * gN.metricInner a v v -
        gN.metricInner a u v * gN.metricInner a u v =
      gN.metricInner a (gN.leviCivitaConnection.curvatureOperatorAt a u v v) u)
    (A : ℂ ≃L[ℝ] ℂ)
    (hA : ∀ u v : ℂ,
      chartMetricInner gN q (extChartAt (modelWithCornersSelf ℝ ℂ) q q) (A u) (A v) =
        chartMetricInner gM p (extChartAt (modelWithCornersSelf ℝ ℂ) p p) u v) :
    LeeLib.Ch02.IsIsometry gM gN
      (constantCurvatureNormalDiffeomorph gM gN hgM hgN p q hKM hKN A) := by
  let I := modelWithCornersSelf ℝ ℂ
  let dM := constantCurvatureExpDiffeomorph gM hgM p hKM
  let dN := constantCurvatureExpDiffeomorph gN hgN q hKN
  let Φ := constantCurvatureNormalDiffeomorph gM gN hgM hgN p q hKM hKN A
  have hdM : (dM : ℂ → M) = fun z : ℂ => Exponential.expMapGlobal gM hgM p z := by
    funext z
    exact congrFun (Jacobi.hadamardDiffeomorphOfNonpos_complete_coe gM hgM p
      (Internal.ConstantCurvatureNormalCoordinatesHelpers.constantCurvature_curvatureOperator_pair_nonneg gM hKM))
      (z : HadamardModel ℂ)
  have hdN : (dN : ℂ → N) = fun z : ℂ => Exponential.expMapGlobal gN hgN q z := by
    funext z
    exact congrFun (Jacobi.hadamardDiffeomorphOfNonpos_complete_coe gN hgN q
      (Internal.ConstantCurvatureNormalCoordinatesHelpers.constantCurvature_curvatureOperator_pair_nonneg gN hKN))
      (z : HadamardModel ℂ)
  intro x
  ext u v
  rw [LeeLib.Ch02.pullbackForm_apply]
  let w : ℂ := dM.symm x
  have hw : dM w = x := dM.apply_symm_apply x
  have hΦ (z : M) : Φ z = dN (A (dM.symm z)) := rfl
  have hΦD (z : TangentSpace I x) :
      mfderiv I I (Φ : M → N) x z =
        mfderiv I I (dN : ℂ → N) (A w) (A (mfderiv I I (dM.symm : M → ℂ) x z)) := by
    have hfirst := mfderiv_comp_apply (I := I) (I' := I) (I'' := I) x
      (A.toDiffeomorph.mdifferentiable (by simp) (dM.symm x))
      (dM.symm.mdifferentiable (by simp) x) z
    have hsecond := mfderiv_comp_apply (I := I) (I' := I) (I'' := I) x
      (dN.mdifferentiable (by simp) (A (dM.symm x)))
      ((A.toDiffeomorph.contMDiff.comp dM.symm.contMDiff).mdifferentiable (by simp) x) z
    rw [hfirst, LeeLib.Ch02.mfderiv_toDiffeomorph] at hsecond
    exact hsecond
  have hundo (z : TangentSpace I x) :
      mfderiv I I (dM : ℂ → M) w (mfderiv I I (dM.symm : M → ℂ) x z) = z := by
    have hfun : (dM : ℂ → M) ∘ (dM.symm : M → ℂ) = id := funext dM.apply_symm_apply
    have hcomp := mfderiv_comp_apply (I := I) (I' := I) (I'' := I) x
      (dM.mdifferentiable (by simp) (dM.symm x))
      (dM.symm.mdifferentiable (by simp) x) z
    rw [hfun, mfderiv_id] at hcomp
    exact hcomp.symm
  have hmetric := constantCurvature_exponential_metricInner_mfderiv_map
    gM gN hgM hgN p q A hA hKM hKN w
      (mfderiv I I (dM.symm : M → ℂ) x u) (mfderiv I I (dM.symm : M → ℂ) x v)
  rw [← hdM, ← hdN] at hmetric
  rw [← congrFun hdM w, ← congrFun hdN (A w)] at hmetric
  change gN.metricInner (dN (A w))
      (mfderiv I I (dN : ℂ → N) (A w) (A (mfderiv I I (dM.symm : M → ℂ) x u)))
      (mfderiv I I (dN : ℂ → N) (A w) (A (mfderiv I I (dM.symm : M → ℂ) x v))) =
    gM.metricInner (dM w)
      (mfderiv I I (dM : ℂ → M) w (mfderiv I I (dM.symm : M → ℂ) x u))
      (mfderiv I I (dM : ℂ → M) w (mfderiv I I (dM.symm : M → ℂ) x v)) at hmetric
  erw [hundo u, hundo v, hw] at hmetric
  change gN.metricInner (Φ x) (mfderiv I I (Φ : M → N) x u)
    (mfderiv I I (Φ : M → N) x v) = gM.metricInner x u v
  erw [hΦ x, hΦD u, hΦD v]
  exact hmetric

/-- **Math.** Complete simply-connected smooth constant-curvature-minus-one
surfaces with the same complex model are genuinely isometric by their
actual normal coordinates. Tensor preservation and distance preservation
are proved, not supplied as premises. -/
def constantCurvatureNormalIsometryEquiv
    (gM : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M)
    (gN : RiemannianMetric (modelWithCornersSelf ℝ ℂ) N)
    (hgM : gM.IsRiemannianDist) (hgN : gN.IsRiemannianDist) (p : M) (q : N)
    (hKM : ∀ (a : M) (u v : TangentSpace (modelWithCornersSelf ℝ ℂ) a),
      gM.metricInner a u u * gM.metricInner a v v -
        gM.metricInner a u v * gM.metricInner a u v =
      gM.metricInner a (gM.leviCivitaConnection.curvatureOperatorAt a u v v) u)
    (hKN : ∀ (a : N) (u v : TangentSpace (modelWithCornersSelf ℝ ℂ) a),
      gN.metricInner a u u * gN.metricInner a v v -
        gN.metricInner a u v * gN.metricInner a u v =
      gN.metricInner a (gN.leviCivitaConnection.curvatureOperatorAt a u v v) u)
    (A : ℂ ≃L[ℝ] ℂ)
    (hA : ∀ u v : ℂ,
      chartMetricInner gN q (extChartAt (modelWithCornersSelf ℝ ℂ) q q) (A u) (A v) =
        chartMetricInner gM p (extChartAt (modelWithCornersSelf ℝ ℂ) p p) u v) :
    M ≃ᵢ N := by
  let Φ := constantCurvatureNormalDiffeomorph gM gN hgM hgN p q hKM hKN A
  have hΦ := constantCurvatureNormalDiffeomorph_isIsometry gM gN hgM hgN p q hKM hKN A hA
  refine { toEquiv := Φ.toEquiv, isometry_toFun := ?_ }
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : M → Type) :=
    ⟨gM.toRiemannianMetric⟩
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : N → Type) :=
    ⟨gN.toRiemannianMetric⟩
  intro x y
  rw [hgN.out, hgM.out]
  exact hΦ.riemannianEDist_comp x y

end Hadamard

#print axioms constantCurvature_exponential_metricInner_map_polar
#print axioms constantCurvature_exponential_metricInner_map
#print axioms constantCurvature_exponential_metricInner_mfderiv_map
#print axioms constantCurvatureExpDiffeomorph
#print axioms constantCurvatureNormalDiffeomorph_isIsometry
#print axioms constantCurvatureNormalIsometryEquiv

end SystolicGrowth

end
