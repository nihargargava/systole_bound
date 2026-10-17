module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingInteriorDistance
public import Geometry.GluingCollarModelBounds

@[expose] public section

/-!
# Actual seam charts locally preserve the warped collar distance

Both distances are genuine native C¹-path infima. Chart and inverse-chart
curves have identical lengths in the actual tangent forms. Short-path
barriers in the original carrier and the model force near-minimizers to
remain in the actual chart, giving both local distance inequalities.
-/

open Set Filter Metric MeasureTheory Bundle Manifold
open scoped Manifold Topology Bundle ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The actual native length in a seam chart is precisely the native
warped-model length of its coordinate curve, including signed-radius zero. -/
theorem gluedCurve_seam_pathELength_eq_model
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {γ : ℝ → P.GluedCarrier} {a b : ℝ}
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1 γ (Icc a b))
    (hmap : MapsTo γ (Icc a b) (P.seamAngularComplexChart k θ).source) :
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
      ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
    pathELength (modelWithCornersSelf ℝ ℂ) γ a b =
      gluingCollarModelPathELength P.radius_pos (P.seamAngularComplexChart k θ ∘ γ) a b := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  rw [P.gluedCurve_pathELength_in_chart _ (Or.inr ⟨k, θ, rfl⟩) hγ hmap,
    gluingCollarModelPathELength_eq_lintegral]
  simp only [P.gluingChartTangentForm_seam, Function.comp_apply]

/-- Inverse-chart lifts retain the actual warped-model native length.
The equality of ordinary derivatives is used only at interior times. -/
theorem gluedSeamChart_lift_pathELength
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {α : ℝ → ℂ} {a b : ℝ} (hα : ContDiffOn ℝ 1 α (Icc a b))
    (hmap : MapsTo α (Icc a b) (P.seamAngularComplexChart k θ).target) :
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
      ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
    pathELength (modelWithCornersSelf ℝ ℂ) ((P.seamAngularComplexChart k θ).symm ∘ α) a b =
      gluingCollarModelPathELength P.radius_pos α a b := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  let e := P.seamAngularComplexChart k θ
  have he : e ∈ P.gluedComplexAtlas := Or.inr ⟨k, θ, rfl⟩
  have hγ := P.gluedChart_lift_contMDiffOn e he hα hmap
  have hs : MapsTo (e.symm ∘ α) (Icc a b) e.source :=
    fun t ht => e.map_target (hmap ht)
  rw [P.gluedCurve_seam_pathELength_eq_model k θ hγ hs]
  simp_rw [gluingCollarModelPathELength_eq_lintegral, ← restrict_Ioo_eq_restrict_Icc]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have heq : (e ∘ (e.symm ∘ α)) =ᶠ[𝓝 t] α := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with u hu
    exact e.right_inv (hmap hu)
  change ENNReal.ofReal (Real.sqrt (gluingComplexCollarTangentForm (gluingRadius C g)
    (e (e.symm (α t))) (deriv (e ∘ (e.symm ∘ α)) t)
      (deriv (e ∘ (e.symm ∘ α)) t))) =
    ENNReal.ofReal (Real.sqrt (gluingComplexCollarTangentForm (gluingRadius C g)
      (α t) (deriv α t) (deriv α t)))
  rw [heq.deriv_eq, e.right_inv (hmap ⟨ht.1.le, ht.2.le⟩)]

/-- Actual chart-contained native curves pay for genuine model distance. -/
theorem gluedCurve_seam_modelEDist_le_pathELength
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {γ : ℝ → P.GluedCarrier} {a b : ℝ}
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1 γ (Icc a b))
    (hmap : MapsTo γ (Icc a b) (P.seamAngularComplexChart k θ).source) (hab : a ≤ b) :
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
      ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
    gluingCollarModelEDist P.radius_pos
      (P.seamAngularComplexChart k θ (γ a)) (P.seamAngularComplexChart k θ (γ b)) ≤
      pathELength (modelWithCornersSelf ℝ ℂ) γ a b := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  rw [P.gluedCurve_seam_pathELength_eq_model k θ hγ hmap]
  exact gluingCollarModelEDist_le_pathELength P.radius_pos
    (P.gluedCurve_chart_contDiffOn _ (Or.inr ⟨k, θ, rfl⟩) hγ hmap).contMDiffOn hab

/-- Genuine model distance is locally bounded by native intrinsic distance,
with near-minimizer containment supplied by the actual native chart barrier. -/
theorem gluedIntrinsicMetric_seam_model_dist_locally_le
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (x : P.GluedCarrier) (hx : x ∈ (P.seamAngularComplexChart k θ).source) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    letI := gluingCollarModelMetricSpace P.radius_pos
    letI := (gluingCollarModelMetricSpace P.radius_pos).toPseudoMetricSpace
    ∃ ρ > 0, ball x ρ ⊆ (P.seamAngularComplexChart k θ).source ∧
      ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ,
        dist (P.seamAngularComplexChart k θ y) (P.seamAngularComplexChart k θ z) ≤
          dist y z := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  letI : MetricSpace ℂ := gluingCollarModelMetricSpace P.radius_pos
  letI : PseudoMetricSpace ℂ := (gluingCollarModelMetricSpace P.radius_pos).toPseudoMetricSpace
  let e := P.seamAngularComplexChart k θ
  obtain ⟨R, hR, hsource, hbarrier⟩ := P.gluedChart_exists_short_path_barrier e x hx
  have hball : ball x (R / 8) ⊆ e.source := by
    intro y hy
    apply hsource
    simp only [Metric.mem_ball] at hy ⊢
    linarith
  refine ⟨R / 8, by linarith, hball, ?_⟩
  intro y hy z hz
  have hxy : dist x y < R / 8 := by simpa only [Metric.mem_ball, dist_comm] using hy
  have hxz : dist x z < R / 8 := by simpa only [Metric.mem_ball, dist_comm] using hz
  have hd : dist y z < R / 4 := by
    have := dist_triangle y x z
    rw [dist_comm y x] at this
    linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := min ε (R / 4)
  have hδ : 0 < δ := lt_min hε (by linarith)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδR : δ ≤ R / 4 := min_le_right _ _
  have hdist : 0 ≤ dist y z := dist_nonneg
  have hr : riemannianEDist (modelWithCornersSelf ℝ ℂ) y z <
      ENNReal.ofReal (dist y z + δ) := by
    change edist y z < ENNReal.ofReal (dist y z + δ)
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff (by linarith)]
    linarith
  obtain ⟨γ, hγ0, hγ1, hγ, hlen, _, _⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hr (show (0 : ℝ) < 1 by norm_num)
  have hlenR : pathELength (modelWithCornersSelf ℝ ℂ) γ 0 1 <
      ENNReal.ofReal (3 * R / 4) :=
    hlen.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  have hstart : dist x (γ 0) < R / 4 := by rw [hγ0]; linarith
  have hmap := hbarrier γ hγ.contMDiffOn hstart hlenR
  have hmodel := (P.gluedCurve_seam_modelEDist_le_pathELength k θ
    hγ.contMDiffOn hmap zero_le_one).trans hlen.le
  change edist (e (γ 0)) (e (γ 1)) ≤ ENNReal.ofReal (dist y z + δ) at hmodel
  rw [hγ0, hγ1, edist_dist] at hmodel
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by linarith : 0 ≤ dist y z + δ)).1 hmodel
  linarith

/-- The original chart topology gives arbitrary small genuine model-
metric coordinate neighborhoods in the actual intrinsic carrier. -/
private theorem gluedSeamChart_exists_coordinate_ball
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (x : P.GluedCarrier) (hx : x ∈ (P.seamAngularComplexChart k θ).source)
    {ε : ℝ} (hε : 0 < ε) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    letI := gluingCollarModelMetricSpace P.radius_pos
    letI := (gluingCollarModelMetricSpace P.radius_pos).toPseudoMetricSpace
    ∃ ρ > 0, ball x ρ ⊆ (P.seamAngularComplexChart k θ).source ∧
      ∀ y ∈ ball x ρ,
        dist (P.seamAngularComplexChart k θ x) (P.seamAngularComplexChart k θ y) < ε := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  letI : MetricSpace ℂ := gluingCollarModelMetricSpace P.radius_pos
  letI : PseudoMetricSpace ℂ := (gluingCollarModelMetricSpace P.radius_pos).toPseudoMetricSpace
  let e := P.seamAngularComplexChart k θ
  have htarget : ball (e x) ε ∈ 𝓝 (e x) := Metric.ball_mem_nhds _ hε
  have hn : e ⁻¹' ball (e x) ε ∩ e.source ∈ 𝓝 x :=
    inter_mem ((e.continuousAt hx).preimage_mem_nhds htarget) (e.open_source.mem_nhds hx)
  obtain ⟨ρ, hρ, hsmall⟩ := Metric.mem_nhds_iff.1 hn
  refine ⟨ρ, hρ, fun y hy => (hsmall hy).2, ?_⟩
  intro y hy
  simpa only [mem_preimage, Metric.mem_ball, dist_comm] using (hsmall hy).1

/-- Every actual seam chart locally identifies the genuine intrinsic metric
with the full warped collar model metric. Both containment arguments use
proved native short-path barriers, including at signed-radius zero. -/
theorem gluedIntrinsicMetric_seam_locally_isometric
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (x : P.GluedCarrier) (hx : x ∈ (P.seamAngularComplexChart k θ).source) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    letI := gluingCollarModelMetricSpace P.radius_pos
    letI := (gluingCollarModelMetricSpace P.radius_pos).toPseudoMetricSpace
    ∃ ρ > 0, ball x ρ ⊆ (P.seamAngularComplexChart k θ).source ∧
      ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ,
        dist (P.seamAngularComplexChart k θ y) (P.seamAngularComplexChart k θ z) =
          dist y z := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  letI := gluingCollarModelRiemannianBundle P.radius_pos
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  letI : MetricSpace ℂ := gluingCollarModelMetricSpace P.radius_pos
  letI : PseudoMetricSpace ℂ := (gluingCollarModelMetricSpace P.radius_pos).toPseudoMetricSpace
  let e := P.seamAngularComplexChart k θ
  have he : e ∈ P.gluedComplexAtlas := Or.inr ⟨k, θ, rfl⟩
  obtain ⟨ρ₁, hρ₁, hball₁, hlower⟩ :=
    P.gluedIntrinsicMetric_seam_model_dist_locally_le k θ x hx
  obtain ⟨R, hR, _hmodelball, hbarrier⟩ :=
    gluingCollarModel_exists_short_path_barrier P.radius_pos e.open_target (e x) (e.map_source hx)
  obtain ⟨ρ₂, hρ₂, _hball₂, hcoord⟩ :=
    P.gluedSeamChart_exists_coordinate_ball k θ x hx (show 0 < R / 8 by linarith)
  let ρ := min ρ₁ ρ₂
  have hρ : 0 < ρ := lt_min hρ₁ hρ₂
  have hsmall₁ : ball x ρ ⊆ ball x ρ₁ := ball_subset_ball (min_le_left _ _)
  have hsmall₂ : ball x ρ ⊆ ball x ρ₂ := ball_subset_ball (min_le_right _ _)
  have hball : ball x ρ ⊆ e.source := hsmall₁.trans hball₁
  refine ⟨ρ, hρ, hball, ?_⟩
  intro y hy z hz
  apply le_antisymm (hlower y (hsmall₁ hy) z (hsmall₁ hz))
  have hxy : dist (e x) (e y) < R / 8 := hcoord y (hsmall₂ hy)
  have hxz : dist (e x) (e z) < R / 8 := hcoord z (hsmall₂ hz)
  have hd : dist (e y) (e z) < R / 4 := by
    have := dist_triangle (e y) (e x) (e z)
    rw [dist_comm (e y) (e x)] at this
    linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := min ε (R / 4)
  have hδ : 0 < δ := lt_min hε (by linarith)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδR : δ ≤ R / 4 := min_le_right _ _
  have hdist : 0 ≤ dist (e y) (e z) := dist_nonneg
  have hr : riemannianEDist (modelWithCornersSelf ℝ ℂ) (e y) (e z) <
      ENNReal.ofReal (dist (e y) (e z) + δ) := by
    change edist (e y) (e z) < ENNReal.ofReal (dist (e y) (e z) + δ)
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff (by linarith)]
    linarith
  obtain ⟨α, hα0, hα1, hα, hlen, _, _⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hr (show (0 : ℝ) < 1 by norm_num)
  have hlenModel : gluingCollarModelPathELength P.radius_pos α 0 1 <
      ENNReal.ofReal (dist (e y) (e z) + δ) := hlen
  have hlenR : gluingCollarModelPathELength P.radius_pos α 0 1 <
      ENNReal.ofReal (3 * R / 4) :=
    hlenModel.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  have hstart : dist (e x) (α 0) < R / 4 := by rw [hα0]; linarith
  have hmap := hbarrier α hα.contDiff.contDiffOn hstart hlenR
  have hγ := P.gluedChart_lift_contMDiffOn e he hα.contDiff.contDiffOn hmap
  have hupper := P.gluedIntrinsicEDist_le_pathELength hγ zero_le_one
  change edist ((e.symm ∘ α) 0) ((e.symm ∘ α) 1) ≤
    pathELength (modelWithCornersSelf ℝ ℂ) (e.symm ∘ α) 0 1 at hupper
  have h0 : (e.symm ∘ α) 0 = y := by
    change e.symm (α 0) = y
    rw [hα0]
    exact e.left_inv (hball hy)
  have h1 : (e.symm ∘ α) 1 = z := by
    change e.symm (α 1) = z
    rw [hα1]
    exact e.left_inv (hball hz)
  rw [h0, h1, P.gluedSeamChart_lift_pathELength k θ hα.contDiff.contDiffOn hmap] at hupper
  have hbound := hupper.trans hlenModel.le
  rw [edist_dist] at hbound
  have hreal := (ENNReal.ofReal_le_ofReal_iff
    (by linarith : 0 ≤ dist (e y) (e z) + δ)).1 hbound
  linarith

#print axioms gluedCurve_seam_pathELength_eq_model
#print axioms gluedSeamChart_lift_pathELength
#print axioms gluedCurve_seam_modelEDist_le_pathELength
#print axioms gluedIntrinsicMetric_seam_model_dist_locally_le
#print axioms gluedIntrinsicMetric_seam_locally_isometric

end SystolicGrowth.ExerciseGluingPreparation
