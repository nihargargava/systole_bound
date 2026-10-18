module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.JacobiScaledComparison
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Jacobi.ChartCurvatureNaturality
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.HopfRinow.MetricBridge

@[expose] public section

/-!
# Intrinsic curvature bounds for the actual Jacobi coefficient

The chart Jacobi operator uses do Carmo's curvature convention, whereas
`chartCurvature` uses its opposite. The identities below retain that sign
when passing an intrinsic sectional bound to the normal scalar equation.
-/

open Set Bundle Manifold Riemannian Riemannian.Tensor
open scoped ContDiff Manifold Topology

noncomputable section

namespace SystolicGrowth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [CompleteSpace E] in
/-- **Math.** The coordinate curvature tensor and the actual Jacobi coefficient
tensor have opposite conventions. -/
theorem chartCurvature_basis_eq_neg_coef
    (g : RiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (i j k : Fin (Module.finrank ℝ E)) :
    Riemannian.Jacobi.chartCurvature g α y (Module.finBasis ℝ E i)
        (Module.finBasis ℝ E j) (Module.finBasis ℝ E k) =
      ∑ l, (-Riemannian.Jacobi.chartCurvatureCoef g α i j k l y) •
        Module.finBasis ℝ E l := by
  classical
  rw [Riemannian.Jacobi.chartCurvature_basis g α hy]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  unfold Riemannian.Jacobi.chartCurvatureCoef
  have hs :
      (∑ r, (chartChristoffel g α j k r y * chartChristoffel g α i r l y -
        chartChristoffel g α i k r y * chartChristoffel g α j r l y)) =
      -(∑ r, (chartChristoffel g α i k r y * chartChristoffel g α j r l y -
        chartChristoffel g α j k r y * chartChristoffel g α i r l y)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [hs]
  ring

/-- **Math.** The actual chart Jacobi operator is the negative of the chart-curvature
contraction; the sign is fixed by the vendored definitions. -/
theorem chartCurvatureOp_eq_neg_chartCurvature
    (g : RiemannianMetric I M) (α : M) (u : ℝ → E) (t : ℝ)
    (hy : u t ∈ interior (extChartAt I α).target) (w : E) :
    Riemannian.Jacobi.chartCurvatureOp g α u t w =
      -Riemannian.Jacobi.chartCurvature g α (u t) (deriv u t) w (deriv u t) := by
  classical
  rw [Riemannian.Jacobi.chartCurvatureOp_apply]
  conv_rhs =>
    rw [show deriv u t = ∑ i, Geodesic.chartCoord (E := E) i (deriv u t) •
      Module.finBasis ℝ E i from by simp [Geodesic.chartCoord_def, Module.Basis.sum_repr],
      show w = ∑ i, Geodesic.chartCoord (E := E) i w • Module.finBasis ℝ E i from
        by simp [Geodesic.chartCoord_def, Module.Basis.sum_repr]]
  rw [Riemannian.Jacobi.chartCurvature_sum₃]
  simp_rw [chartCurvature_basis_eq_neg_coef g α hy]
  apply (Module.finBasis ℝ E).ext_elem
  intro l₀
  simp only [map_neg, map_sum, map_smul, Module.Basis.repr_self,
    Finsupp.smul_single, Finsupp.smul_apply, smul_eq_mul, Finsupp.finsetSum_apply,
    Finsupp.neg_apply, Finsupp.single_apply]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Math.** Curvature annihilates its radial input; consequently the
Jacobi operator has zero radial column in a radial/normal frame. -/
theorem chartCurvatureOp_radial_eq_zero
    (g : RiemannianMetric I M) (α : M) (u : ℝ → E) (t : ℝ)
    (hy : u t ∈ interior (extChartAt I α).target) :
    Riemannian.Jacobi.chartCurvatureOp g α u t (deriv u t) = 0 := by
  rw [chartCurvatureOp_eq_neg_chartCurvature g α u t hy]
  simp [Riemannian.Jacobi.chartCurvature, Riemannian.Jacobi.christoffelCurvature]

/-- **Math.** The normal component of the actual two-component Jacobi
system satisfies the scalar equation for the normal diagonal coefficient.
Its decoupling is proved from curvature antisymmetry, not supplied as data. -/
theorem isScalarJacobiPairOn_normal_component_of_radial_smul
    (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    (e : Fin 2 → ℝ → E) (c : ℝ) {b : ℝ} {F V : ℝ → Fin 2 → ℝ}
    (hmem : ∀ t ∈ Icc 0 b, u t ∈ interior (extChartAt I α).target)
    (hradial : ∀ t ∈ Icc 0 b, e 0 t = c • deriv u t)
    (hFV : Riemannian.Jacobi.IsJacobiPairOn
      (Riemannian.Jacobi.jacobiCoefOp g α u
        (Riemannian.Jacobi.chartCurvatureOp g α u) e) 0 b F V) :
    Riemannian.Jacobi.IsJacobiPairOn
      (fun t => Riemannian.Jacobi.jacobiCoef g α u
        (Riemannian.Jacobi.chartCurvatureOp g α u) e 1 1 t •
          ContinuousLinearMap.id ℝ ℝ) 0 b (fun t => F t 1) (fun t => V t 1) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    have h := (ContinuousLinearMap.proj (1 : Fin 2)).hasFDerivAt.comp_hasDerivWithinAt
      t (hFV.1 t ht)
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using h
  · intro t ht
    have hzero : Riemannian.Jacobi.jacobiCoef g α u
        (Riemannian.Jacobi.chartCurvatureOp g α u) e 0 1 t = 0 := by
      rw [Riemannian.Jacobi.jacobiCoef, hradial t ht, map_smul,
        chartCurvatureOp_radial_eq_zero g α u t (hmem t ht)]
      simp [chartMetricInner_def]
    have h := (ContinuousLinearMap.proj (1 : Fin 2)).hasFDerivAt.comp_hasDerivWithinAt
      t (hFV.2 t ht)
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply, Pi.neg_apply,
      Riemannian.Jacobi.jacobiCoefOp_apply, Fin.sum_univ_two, hzero, zero_mul, zero_add,
      neg_apply, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul] using h

/-- **Math.** The unit-speed case of normal-component decoupling. -/
theorem isScalarJacobiPairOn_normal_component
    (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    (e : Fin 2 → ℝ → E) {b : ℝ} {F V : ℝ → Fin 2 → ℝ}
    (hmem : ∀ t ∈ Icc 0 b, u t ∈ interior (extChartAt I α).target)
    (hradial : ∀ t ∈ Icc 0 b, e 0 t = deriv u t)
    (hFV : Riemannian.Jacobi.IsJacobiPairOn
      (Riemannian.Jacobi.jacobiCoefOp g α u
        (Riemannian.Jacobi.chartCurvatureOp g α u) e) 0 b F V) :
    Riemannian.Jacobi.IsJacobiPairOn
      (fun t => Riemannian.Jacobi.jacobiCoef g α u
        (Riemannian.Jacobi.chartCurvatureOp g α u) e 1 1 t •
          ContinuousLinearMap.id ℝ ℝ) 0 b (fun t => F t 1) (fun t => V t 1) := by
  exact isScalarJacobiPairOn_normal_component_of_radial_smul g α u e 1 hmem
    (fun t ht => by simpa using hradial t ht) hFV

variable [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The actual Jacobi operator's chart pairing is the intrinsic curvature
form on the tangent readbacks of its velocity and test vectors. -/
theorem chartCurvatureOp_pairing_eq_curvatureFormAt
    (g : RiemannianMetric I M) (α : M) (u : ℝ → E) (t : ℝ)
    {p : M} (hp : p ∈ (chartAt H α).source) (hu : u t = extChartAt I α p)
    (w z : E) :
    chartMetricInner g α (u t) (Riemannian.Jacobi.chartCurvatureOp g α u t w) z =
      g.leviCivitaConnection.curvatureFormAt g p
        ((trivializationAt E (TangentSpace I) α).symm p (deriv u t))
        ((trivializationAt E (TangentSpace I) α).symm p w)
        ((trivializationAt E (TangentSpace I) α).symm p (deriv u t))
        ((trivializationAt E (TangentSpace I) α).symm p z) := by
  have hy : u t ∈ interior (extChartAt I α).target := by
    rw [hu, (isOpen_extChartAt_target (I := I) α).interior_eq]
    exact (extChartAt I α).map_source (by rwa [extChartAt_source])
  rw [chartCurvatureOp_eq_neg_chartCurvature g α u t hy w,
    Riemannian.Jacobi.chartMetricInner_neg_left]
  rw [Riemannian.trivializationAt_symm_eq_sum_chartBasisVecFiber α p _ hp,
    Riemannian.trivializationAt_symm_eq_sum_chartBasisVecFiber α p _ hp,
    Riemannian.trivializationAt_symm_eq_sum_chartBasisVecFiber α p _ hp,
    Riemannian.Jacobi.curvatureFormAt_chartFrame g hp]
  rw [hu]

/-- **Math.** An intrinsic sectional bound `K ≤ -1` makes the actual Jacobi
coefficient at most minus the radial speed squared, on a unit normal vector. -/
theorem jacobiCoef_self_le_neg_sq_of_intrinsic_bound
    {ι : Type*} (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    (e : ι → ℝ → E) (t : ℝ) (i : ι) (speed : ℝ)
    {p : M} (hp : p ∈ (chartAt H α).source) (hu : u t = extChartAt I α p)
    (hK : ∀ x y : TangentSpace I p,
      g.metricInner p x x * g.metricInner p y y -
        g.metricInner p x y * g.metricInner p x y ≤
      g.metricInner p (g.leviCivitaConnection.curvatureOperatorAt p x y y) x)
    (hspeed : chartMetricInner g α (u t) (deriv u t) (deriv u t) = speed ^ 2)
    (hnormal : chartMetricInner g α (u t) (e i t) (e i t) = 1)
    (horth : chartMetricInner g α (u t) (deriv u t) (e i t) = 0) :
    Riemannian.Jacobi.jacobiCoef g α u
      (Riemannian.Jacobi.chartCurvatureOp g α u) e i i t ≤ -(speed ^ 2) := by
  let X := (trivializationAt E (TangentSpace I) α).symm p (deriv u t)
  let Y := (trivializationAt E (TangentSpace I) α).symm p (e i t)
  have hX : g.metricInner p X X = speed ^ 2 := by
    change g.metricInner p
      ((trivializationAt E (TangentSpace I) α).symm p (deriv u t))
      ((trivializationAt E (TangentSpace I) α).symm p (deriv u t)) = speed ^ 2
    rw [← Riemannian.chartMetricInner_extChartAt_eq_metricInner g α hp, ← hu]
    exact hspeed
  have hY : g.metricInner p Y Y = 1 := by
    change g.metricInner p
      ((trivializationAt E (TangentSpace I) α).symm p (e i t))
      ((trivializationAt E (TangentSpace I) α).symm p (e i t)) = 1
    rw [← Riemannian.chartMetricInner_extChartAt_eq_metricInner g α hp, ← hu]
    exact hnormal
  have hXY : g.metricInner p X Y = 0 := by
    change g.metricInner p
      ((trivializationAt E (TangentSpace I) α).symm p (deriv u t))
      ((trivializationAt E (TangentSpace I) α).symm p (e i t)) = 0
    rw [← Riemannian.chartMetricInner_extChartAt_eq_metricInner g α hp, ← hu]
    exact horth
  have hreverse : speed ^ 2 ≤ g.leviCivitaConnection.curvatureFormAt g p X Y Y X := by
    have hbound := hK X Y
    rw [hX, hY, hXY] at hbound
    rw [Riemannian.Jacobi.curvatureFormAt_eq_metricInner]
    exact (by simpa only [mul_one, zero_mul, sub_zero] using hbound)
  letI : Bundle.RiemannianBundle (fun q : M => TangentSpace I q) :=
    ⟨g.toRiemannianMetric⟩
  have hLC := g.leviCivitaConnection.isLeviCivita_of_koszulDual g
    (fun U V W q => g.koszulDualSection_dual U V W q)
  have hB := g.leviCivitaConnection.isAlgCurvatureForm_curvatureFormAt g hLC p
  have hskew := hB.antisymm₃₄ X Y X Y
  unfold Riemannian.Jacobi.jacobiCoef
  rw [chartCurvatureOp_pairing_eq_curvatureFormAt g α u t hp hu]
  change g.leviCivitaConnection.curvatureFormAt g p X Y X Y ≤ -(speed ^ 2)
  linarith

/-- **Math.** The unit-speed curvature coefficient bound, as a specialization
of the squared-speed bound. -/
theorem jacobiCoef_self_le_neg_one_of_intrinsic_bound
    {ι : Type*} (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    (e : ι → ℝ → E) (t : ℝ) (i : ι)
    {p : M} (hp : p ∈ (chartAt H α).source) (hu : u t = extChartAt I α p)
    (hK : ∀ x y : TangentSpace I p,
      g.metricInner p x x * g.metricInner p y y -
        g.metricInner p x y * g.metricInner p x y ≤
      g.metricInner p (g.leviCivitaConnection.curvatureOperatorAt p x y y) x)
    (hunit : chartMetricInner g α (u t) (deriv u t) (deriv u t) = 1)
    (hnormal : chartMetricInner g α (u t) (e i t) (e i t) = 1)
    (horth : chartMetricInner g α (u t) (deriv u t) (e i t) = 0) :
    Riemannian.Jacobi.jacobiCoef g α u
      (Riemannian.Jacobi.chartCurvatureOp g α u) e i i t ≤ -1 := by
  simpa only [one_pow] using jacobiCoef_self_le_neg_sq_of_intrinsic_bound
    g α u e t i 1 hp hu hK (by simpa only [one_pow] using hunit) hnormal horth

/-- **Math.** Along a radial geodesic of positive speed, the normal component
of the actual Jacobi pair dominates `sinh(speed * t)`. The normal scalar
equation and curvature coefficient bound are derived from the actual
operator, intrinsic curvature, and orthonormal radial/normal frame. -/
theorem sinh_le_normalJacobi_of_intrinsic_bound_scaled
    (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    (e : Fin 2 → ℝ → E) {b speed : ℝ} {F V : ℝ → Fin 2 → ℝ}
    (hspeed : 0 < speed)
    (hmem : ∀ t ∈ Icc 0 b, u t ∈ interior (extChartAt I α).target)
    (hradial : ∀ t ∈ Icc 0 b, deriv u t = speed • e 0 t)
    (hframe : ∀ t ∈ Icc 0 b, ∀ i j,
      chartMetricInner g α (u t) (e i t) (e j t) = if i = j then (1 : ℝ) else 0)
    (hFV : Riemannian.Jacobi.IsJacobiPairOn
      (Riemannian.Jacobi.jacobiCoefOp g α u
        (Riemannian.Jacobi.chartCurvatureOp g α u) e) 0 b F V)
    (hK : ∀ (p : M) (x y : TangentSpace I p),
      g.metricInner p x x * g.metricInner p y y -
        g.metricInner p x y * g.metricInner p x y ≤
      g.metricInner p (g.leviCivitaConnection.curvatureOperatorAt p x y y) x)
    (hF0 : F 0 1 = 0) (hV0 : V 0 1 = speed)
    {t : ℝ} (ht : t ∈ Icc 0 b) :
    Real.sinh (speed * t) ≤ F t 1 := by
  have he0 : ∀ s ∈ Icc 0 b, e 0 s = speed⁻¹ • deriv u s := by
    intro s hs
    rw [hradial s hs, smul_smul, inv_mul_cancel₀ hspeed.ne', one_smul]
  apply sinh_le_scalarJacobi_of_curvature_le_neg_sq hspeed
    (isScalarJacobiPairOn_normal_component_of_radial_smul
      g α u e speed⁻¹ hmem he0 hFV) ?_ hF0 hV0 ht
  intro s hs
  let p := (extChartAt I α).symm (u s)
  have htarget : u s ∈ (extChartAt I α).target := interior_subset (hmem s hs)
  have hp : p ∈ (chartAt H α).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I α).map_target htarget
  have hu : u s = extChartAt I α p := ((extChartAt I α).right_inv htarget).symm
  apply jacobiCoef_self_le_neg_sq_of_intrinsic_bound g α u e s 1 speed hp hu (hK p)
  · rw [hradial s hs, chartMetricInner_smul_left, chartMetricInner_smul_right,
      hframe s hs 0 0]
    simp [pow_two]
  · simpa using hframe s hs 1 1
  · rw [hradial s hs, chartMetricInner_smul_left, hframe s hs 0 1]
    norm_num

/-- **Math.** The unit-speed case of the intrinsic normal Jacobi comparison. -/
theorem sinh_le_normalJacobi_of_intrinsic_bound
    (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    (e : Fin 2 → ℝ → E) {b : ℝ} {F V : ℝ → Fin 2 → ℝ}
    (hmem : ∀ t ∈ Icc 0 b, u t ∈ interior (extChartAt I α).target)
    (hradial : ∀ t ∈ Icc 0 b, e 0 t = deriv u t)
    (hframe : ∀ t ∈ Icc 0 b, ∀ i j,
      chartMetricInner g α (u t) (e i t) (e j t) = if i = j then (1 : ℝ) else 0)
    (hFV : Riemannian.Jacobi.IsJacobiPairOn
      (Riemannian.Jacobi.jacobiCoefOp g α u
        (Riemannian.Jacobi.chartCurvatureOp g α u) e) 0 b F V)
    (hK : ∀ (p : M) (x y : TangentSpace I p),
      g.metricInner p x x * g.metricInner p y y -
        g.metricInner p x y * g.metricInner p x y ≤
      g.metricInner p (g.leviCivitaConnection.curvatureOperatorAt p x y y) x)
    (hF0 : F 0 1 = 0) (hV0 : V 0 1 = 1)
    {t : ℝ} (ht : t ∈ Icc 0 b) :
    Real.sinh t ≤ F t 1 := by
  simpa only [one_mul] using sinh_le_normalJacobi_of_intrinsic_bound_scaled
    g α u e (speed := 1) zero_lt_one hmem
    (fun s hs => by simpa only [one_smul] using (hradial s hs).symm)
    hframe hFV hK hF0 hV0 ht

#print axioms chartCurvatureOp_eq_neg_chartCurvature
#print axioms isScalarJacobiPairOn_normal_component_of_radial_smul
#print axioms isScalarJacobiPairOn_normal_component
#print axioms chartCurvatureOp_pairing_eq_curvatureFormAt
#print axioms jacobiCoef_self_le_neg_one_of_intrinsic_bound
#print axioms jacobiCoef_self_le_neg_sq_of_intrinsic_bound
#print axioms sinh_le_normalJacobi_of_intrinsic_bound
#print axioms sinh_le_normalJacobi_of_intrinsic_bound_scaled

end SystolicGrowth

end
