module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCurvatureBoundedMetricSpace
public import Geometry.GluingChainBoundedCurvatureCurvature
public import Geometry.ExponentialPolarAreaTransfer
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.HopfRinow.MetricBridge

@[expose] public section

/-!
# Determinant area in the actual selected glued charts

The already constructed ODE area measure is identified locally with the
determinant of the actual smooth tensor in the chart selected by `chartAt`.
The neighborhoods are obtained from the concrete disjoint closed collars.
-/

open Set Bundle Manifold Riemannian MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

local instance (P : ExerciseGluingPreparation C g n genera X) :
    MetricSpace P.GluedCarrier := P.gluedCurvatureBoundedIntrinsicMetricSpace

local instance : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by rw [Complex.finrank_real_complex]; norm_num⟩

private theorem selected_chartMetricInner_eq
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedCarrier)
    {y : ℂ} (hy : y ∈ (chartAt ℂ q).target) (u v : ℂ) :
    chartMetricInner P.gluedCurvatureBoundedSmoothRiemannianMetric q y u v =
      P.gluedCurvatureBoundedSmoothRiemannianMetric.inner ((chartAt ℂ q).symm y)
        (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
          (achart ℂ q)).symmL ℝ ((chartAt ℂ q).symm y) u)
        (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
          (achart ℂ q)).symmL ℝ ((chartAt ℂ q).symm y) v) := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let p := (chartAt ℂ q).symm y
  let τ := trivializationAt ℂ (TangentSpace I) q
  have hp : p ∈ (chartAt ℂ q).source := (chartAt ℂ q).map_target hy
  have hpBase : p ∈ τ.baseSet := hp
  have hcoord : (extChartAt I q) p = y := by
    simpa only [extChartAt_coe, I, modelWithCornersSelf_coe,
      Function.comp_apply, id_eq] using (chartAt ℂ q).right_inv hy
  have hbridge := chartMetricInner_extChartAt_eq_metricInner
    (I := I) P.gluedCurvatureBoundedSmoothRiemannianMetric q hp u v
  rw [hcoord] at hbridge
  rw [hbridge, ← Bundle.Trivialization.symmL_apply (R := ℝ) τ hpBase u,
    ← Bundle.Trivialization.symmL_apply (R := ℝ) τ hpBase v]
  change P.gluedCurvatureBoundedSmoothRiemannianMetric.inner p
    (τ.symmL ℝ p u) (τ.symmL ℝ p v) = _
  simp only [τ, TangentBundle.trivializationAt_eq_localTriv]
  rfl

/-- **Math.** A selected seam chart has exactly the native complex chart Gram
matrix, irrespective of the arbitrary finite basis used by the connection API. -/
theorem gluedCurvatureBoundedSeamCoordinateMetric_eq_nativeComplexChartMetricGram
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedCarrier)
    (k : Fin (n - 1)) (θ : ℝ)
    (hchart : chartAt ℂ q = P.seamAngularComplexChart k θ)
    {y : ℂ} (hy : y ∈ (chartAt ℂ q).target) :
    P.gluedCurvatureBoundedSeamCoordinateMetric k θ (y.re, y.im) =
      nativeComplexChartMetricGram P.gluedCurvatureBoundedSmoothRiemannianMetric q y := by
  have hcoord : Complex.equivRealProdCLM.symm (y.re, y.im) = y := Complex.ext rfl rfl
  ext i j
  dsimp only [gluedCurvatureBoundedSeamCoordinateMetric, nativeComplexChartMetricGram]
  rw [hcoord]
  have h := (selected_chartMetricInner_eq P q hy
    (if i = 0 then 1 else Complex.I) (if j = 0 then 1 else Complex.I)).symm
  have hfoot : (chartAt ℂ q).symm y = (P.seamAngularComplexChart k θ).symm y := by
    rw [hchart]
  rw [hfoot] at h
  simpa only [achart, hchart] using h

/-- **Math.** The unchanged native interior tensor also agrees with the actual
selected complex chart Gram matrix. -/
theorem gluedCurvatureBoundedInteriorCoordinateMetric_eq_nativeComplexChartMetricGram
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedCarrier)
    (hi : P.IsGluedInteriorComplexChart (chartAt ℂ q))
    {y : ℂ} (hy : y ∈ (chartAt ℂ q).target) :
    P.gluedCurvatureBoundedInteriorCoordinateMetric (chartAt ℂ q) hi (y.re, y.im) =
      nativeComplexChartMetricGram P.gluedCurvatureBoundedSmoothRiemannianMetric q y := by
  have hcoord : Complex.equivRealProdCLM.symm (y.re, y.im) = y := Complex.ext rfl rfl
  ext i j
  dsimp only [gluedCurvatureBoundedInteriorCoordinateMetric, nativeComplexChartMetricGram]
  rw [hcoord]
  exact (selected_chartMetricInner_eq P q hy _ _).symm

private theorem exists_local_selected_area_regime
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedCarrier) :
    ∃ W : Set P.GluedCarrier, q ∈ W ∧ IsOpen W ∧ W ⊆ (chartAt ℂ q).source ∧
      ((∃ k : Fin (n - 1), ∃ θ : ℝ,
          chartAt ℂ q = P.seamAngularComplexChart k θ ∧
          ∀ c ∈ W, ∀ l : Fin (n - 1), l ≠ k → c ∉ P.thinSeamCollar l) ∨
        (P.IsGluedInteriorComplexChart (chartAt ℂ q) ∧
          ∀ c ∈ W, ∀ k : Fin (n - 1), c ∉ P.thinSeamCollar k)) := by
  classical
  by_cases hclosed : ∃ k : Fin (n - 1), q ∈ P.closedThinSeamCollar k
  · obtain ⟨k, hk⟩ := hclosed
    obtain ⟨θ, hchart⟩ :=
      P.gluedCurvatureBounded_chartAt_eq_seam_of_mem_closedThinSeamCollar q k hk
    let V : Set P.GluedCarrier := ⋃ l : Fin (n - 1),
      if l = k then ∅ else P.closedThinSeamCollar l
    have hV : IsClosed V := by
      apply isClosed_iUnion_of_finite
      intro l
      by_cases hl : l = k
      · simp [hl]
      · simpa only [if_neg hl] using (P.closedThinSeamCollar_isCompact l).isClosed
    have hqV : q ∉ V := by
      intro hqV
      rcases mem_iUnion.mp hqV with ⟨l, hlV⟩
      by_cases hl : l = k
      · simp [hl] at hlV
      · exact disjoint_left.mp (P.closedThinSeamCollar_disjoint hl)
          (by simpa only [if_neg hl] using hlV) hk
    let W : Set P.GluedCarrier := (chartAt ℂ q).source ∩ Vᶜ
    refine ⟨W, ⟨mem_chart_source ℂ q, hqV⟩,
      (chartAt ℂ q).open_source.inter hV.isOpen_compl, inter_subset_left,
      Or.inl ⟨k, θ, hchart, ?_⟩⟩
    intro c hc l hl hthin
    apply hc.2
    exact mem_iUnion.mpr ⟨l, by
      simpa only [if_neg hl] using P.thinSeamCollar_subset_closedThinSeamCollar l hthin⟩
  · have hnone : ∀ k : Fin (n - 1), q ∉ P.closedThinSeamCollar k := by
      simpa only [not_exists] using hclosed
    let V : Set P.GluedCarrier := ⋃ k : Fin (n - 1), P.closedThinSeamCollar k
    have hV : IsClosed V := isClosed_iUnion_of_finite fun k =>
      (P.closedThinSeamCollar_isCompact k).isClosed
    have hqV : q ∉ V := by
      intro hqV
      rcases mem_iUnion.mp hqV with ⟨k, hk⟩
      exact hnone k hk
    let W : Set P.GluedCarrier := (chartAt ℂ q).source ∩ Vᶜ
    have houtside : ∀ c ∈ W, ∀ k : Fin (n - 1), c ∉ P.thinSeamCollar k := by
      intro c hc k hk
      exact hc.2 (mem_iUnion.mpr
        ⟨k, P.thinSeamCollar_subset_closedThinSeamCollar k hk⟩)
    refine ⟨W, ⟨mem_chart_source ℂ q, hqV⟩,
      (chartAt ℂ q).open_source.inter hV.isOpen_compl, inter_subset_left, ?_⟩
    rcases P.gluedCurvatureBounded_chartAt_is_seam_or_interior q with hi | ⟨k, θ, hchart⟩
    · exact Or.inr ⟨hi, houtside⟩
    · exact Or.inl ⟨k, θ, hchart, fun c hc l _ => houtside c hc l⟩

/-- **Math.** Around every actual point, the constructed global ODE area measure
is precisely the native determinant-area measure of its selected chart. -/
theorem exists_local_gluedCurvatureBoundedArea_selected_chart
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedCarrier) :
    ∃ W : Set P.GluedCarrier, q ∈ W ∧ IsOpen W ∧ W ⊆ (chartAt ℂ q).source ∧
      ∀ s : Set ℂ, MeasurableSet s → s ⊆ (chartAt ℂ q) '' W →
        P.gluedCurvatureBoundedAreaMeasure ((chartAt ℂ q).symm '' s) =
          nativeComplexChartMetricArea P.gluedCurvatureBoundedSmoothRiemannianMetric q s := by
  obtain ⟨W, hqW, hW, hWsource, hregime⟩ := exists_local_selected_area_regime P q
  refine ⟨W, hqW, hW, hWsource, ?_⟩
  intro s hs hsub
  have ht : s ⊆ (chartAt ℂ q).target := by
    rintro y hy
    rcases hsub hy with ⟨c, hc, rfl⟩
    exact (chartAt ℂ q).map_source (hWsource hc)
  rw [nativeComplexChartMetricArea, withDensity_apply _ hs]
  rcases hregime with ⟨k, θ, hchart, hother⟩ | ⟨hi, houtside⟩
  · have hother' : ∀ y ∈ s, ∀ l : Fin (n - 1), l ≠ k →
        (P.seamAngularComplexChart k θ).symm y ∉ P.thinSeamCollar l := by
      intro y hy l hl
      rcases hsub hy with ⟨c, hc, rfl⟩
      rw [← hchart, (chartAt ℂ q).left_inv (hWsource hc)]
      exact hother c hc l hl
    have harea := P.gluedCurvatureBoundedAreaMeasure_isolated_seam_chart_image
      k θ hs (by simpa only [← hchart] using ht) hother'
    rw [← hchart] at harea
    rw [harea]
    apply setLIntegral_congr_fun hs
    intro y hy
    dsimp only
    rw [P.gluedCurvatureBoundedSeamCoordinateMetric_eq_nativeComplexChartMetricGram
      q k θ hchart (ht hy)]
  · have houtside' : ∀ y ∈ s, ∀ k : Fin (n - 1),
        (chartAt ℂ q).symm y ∉ P.thinSeamCollar k := by
      intro y hy k
      rcases hsub hy with ⟨c, hc, rfl⟩
      rw [(chartAt ℂ q).left_inv (hWsource hc)]
      exact houtside c hc k
    rw [P.gluedCurvatureBoundedAreaMeasure_exteriorInteriorComplexChart_image
      (chartAt ℂ q) hi hs ht houtside']
    apply setLIntegral_congr_fun hs
    intro y hy
    dsimp only
    rw [P.gluedCurvatureBoundedInteriorCoordinateMetric_eq_nativeComplexChartMetricGram
      q hi (ht hy)]

/-- **Math.** Integral form of the actual selected-chart area identity, with no
assumed Riemannian-area compatibility premise. -/
theorem exists_local_gluedCurvatureBoundedArea_selected_chart_integral
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedCarrier) :
    ∃ W : Set P.GluedCarrier, q ∈ W ∧ IsOpen W ∧ W ⊆ (chartAt ℂ q).source ∧
      ∀ s : Set ℂ, MeasurableSet s → s ⊆ (chartAt ℂ q) '' W →
        P.gluedCurvatureBoundedAreaMeasure ((chartAt ℂ q).symm '' s) =
          ∫⁻ y : ℂ in s, ENNReal.ofReal
            (Real.sqrt (nativeComplexChartMetricGram
              P.gluedCurvatureBoundedSmoothRiemannianMetric q y).det) := by
  obtain ⟨W, hqW, hW, hWsource, harea⟩ :=
    P.exists_local_gluedCurvatureBoundedArea_selected_chart q
  refine ⟨W, hqW, hW, hWsource, fun s hs hsub => ?_⟩
  rw [harea s hs hsub, nativeComplexChartMetricArea, withDensity_apply _ hs]

#print axioms gluedCurvatureBoundedSeamCoordinateMetric_eq_nativeComplexChartMetricGram
#print axioms gluedCurvatureBoundedInteriorCoordinateMetric_eq_nativeComplexChartMetricGram
#print axioms exists_local_gluedCurvatureBoundedArea_selected_chart
#print axioms exists_local_gluedCurvatureBoundedArea_selected_chart_integral

end
end SystolicGrowth.ExerciseGluingPreparation
