module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingLocalMetric
public import Geometry.HyperbolicCurveLength
public import Geometry.HyperbolicMetricSegments
public import Geometry.GluingSeamNeighborhoods

@[expose] public section

/-!
# Hyperbolic length and distance in actual glued interior charts

The inverse of an actual interior chart transports smooth model curves
to the original glued carrier. Its native length is the literal Poincare
speed integral; no ambient chord-distance substitution is made.
-/

open Set Filter Metric MeasureTheory Bundle Manifold
open scoped UpperHalfPlane Manifold Topology Bundle ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- An actual interior coordinate is a point of the genuine upper half-plane. -/
noncomputable def gluedInteriorChartPoint (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    (x : P.GluedCarrier) (hx : x ∈ e.source) : ℍ :=
  ⟨e x, P.gluedInteriorComplexChart_target_im_pos e he (e.map_source hx)⟩

@[simp] theorem gluedInteriorChartPoint_coe
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    (x : P.GluedCarrier) (hx : x ∈ e.source) :
    (P.gluedInteriorChartPoint e he x hx : ℂ) = e x := rfl

/-- Within-C¹ model curves lift through the actual inverse native chart. -/
theorem gluedChart_lift_contMDiffOn
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    {α : ℝ → ℂ} {s : Set ℝ} (hα : ContDiffOn ℝ 1 α s)
    (hmap : MapsTo α s e.target) :
    ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1
      (e.symm ∘ α) s :=
  (contMDiffOn_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas he)).comp hα.contMDiffOn hmap

/-- Lifting a model curve has exactly its Poincare speed integral as native
length. Only containment in the actual target and within-C¹ regularity are used. -/
theorem gluedInteriorChart_lift_pathELength
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    {α : ℝ → ℂ} {a b : ℝ} (hα : ContDiffOn ℝ 1 α (Icc a b))
    (hmap : MapsTo α (Icc a b) e.target) :
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
      ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
    pathELength (modelWithCornersSelf ℝ ℂ) (e.symm ∘ α) a b =
      ∫⁻ t in Icc a b, ENNReal.ofReal (‖deriv α t‖ / (α t).im) := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  have hγ := P.gluedChart_lift_contMDiffOn e (Or.inl he) hα hmap
  have hs : MapsTo (e.symm ∘ α) (Icc a b) e.source :=
    fun t ht => e.map_target (hmap ht)
  rw [P.gluedCurve_pathELength_interior e he hγ hs]
  simp_rw [← restrict_Ioo_eq_restrict_Icc]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have heq : (e ∘ (e.symm ∘ α)) =ᶠ[𝓝 t] α := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with u hu
    exact e.right_inv (hmap hu)
  change ENNReal.ofReal (‖deriv (e ∘ (e.symm ∘ α)) t‖ / (e (e.symm (α t))).im) =
    ENNReal.ofReal (‖deriv α t‖ / (α t).im)
  rw [heq.deriv_eq]
  simp only [e.right_inv (hmap ⟨ht.1.le, ht.2.le⟩)]

/-- Arbitrarily small genuine hyperbolic coordinate balls have native
intrinsic neighborhoods, by the preserved original chart topology. -/
private theorem gluedInteriorChart_exists_coordinate_ball
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    (x : P.GluedCarrier) (hx : x ∈ e.source) {ε : ℝ} (hε : 0 < ε) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ ρ > 0, ∃ hball : ball x ρ ⊆ e.source,
      ∀ (y : P.GluedCarrier) (hy : y ∈ ball x ρ),
        dist (P.gluedInteriorChartPoint e he x hx)
          (P.gluedInteriorChartPoint e he y (hball hy)) < ε := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  let q := P.gluedInteriorChartPoint e he x hx
  let U : Set ℂ := ((↑) : ℍ → ℂ) '' ball q ε
  have hU : IsOpen U := UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ Metric.isOpen_ball
  have hxU : e x ∈ U := ⟨q, by simpa only [Metric.mem_ball, dist_self] using hε, rfl⟩
  have hn : e ⁻¹' U ∩ e.source ∈ 𝓝 x :=
    inter_mem ((e.continuousAt hx).preimage_mem_nhds (hU.mem_nhds hxU))
      (e.open_source.mem_nhds hx)
  obtain ⟨ρ, hρ, hsmall⟩ := Metric.mem_nhds_iff.1 hn
  have hball : ball x ρ ⊆ e.source := fun y hy => (hsmall hy).2
  refine ⟨ρ, hρ, hball, ?_⟩
  intro y hy
  obtain ⟨w, hw, hew⟩ := (hsmall hy).1
  have hcoord : P.gluedInteriorChartPoint e he y (hball hy) = w := by
    apply UpperHalfPlane.ext
    exact hew.symm
  rw [hcoord]
  simpa only [Metric.mem_ball, dist_comm] using hw

/-- A genuine native curve in an actual interior chart pays for the
hyperbolic distance of its coordinates. -/
theorem gluedCurve_interior_hyperbolic_edist_le_pathELength
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    {γ : ℝ → P.GluedCarrier} {a b : ℝ}
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1 γ (Icc a b))
    (hmap : MapsTo γ (Icc a b) e.source) (hab : a ≤ b) :
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
      ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
    edist (P.gluedInteriorChartPoint e he (γ a) (hmap ⟨le_rfl, hab⟩))
      (P.gluedInteriorChartPoint e he (γ b) (hmap ⟨hab, le_rfl⟩)) ≤
      pathELength (modelWithCornersSelf ℝ ℂ) γ a b := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  rw [P.gluedCurve_pathELength_interior e he hγ hmap, edist_dist]
  exact hyperbolic_dist_le_poincare_lintegral
    (P.gluedCurve_chart_contDiffOn e (Or.inl he) hγ hmap) hab
    (fun t ht => P.gluedInteriorComplexChart_target_im_pos e he (e.map_source (hmap ht)))

/-- On a constructed small intrinsic ball, genuine hyperbolic coordinate
distance is bounded by actual intrinsic distance. Near-minimizer containment
comes from the proved short-path barrier, not a new hypothesis. -/
theorem gluedIntrinsicMetric_interior_hyperbolic_dist_locally_le
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    (x : P.GluedCarrier) (hx : x ∈ e.source) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ ρ > 0, ∃ hball : ball x ρ ⊆ e.source,
      ∀ (y : P.GluedCarrier) (hy : y ∈ ball x ρ)
        (z : P.GluedCarrier) (hz : z ∈ ball x ρ),
        dist (P.gluedInteriorChartPoint e he y (hball hy))
          (P.gluedInteriorChartPoint e he z (hball hz)) ≤ dist y z := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
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
  have hmodel := (P.gluedCurve_interior_hyperbolic_edist_le_pathELength e he
    hγ.contMDiffOn hmap zero_le_one).trans hlen.le
  have h0 : P.gluedInteriorChartPoint e he (γ 0) (hmap ⟨le_rfl, zero_le_one⟩) =
      P.gluedInteriorChartPoint e he y (hball hy) := by
    apply UpperHalfPlane.ext
    simp only [gluedInteriorChartPoint_coe, hγ0]
  have h1 : P.gluedInteriorChartPoint e he (γ 1) (hmap ⟨zero_le_one, le_rfl⟩) =
      P.gluedInteriorChartPoint e he z (hball hz) := by
    apply UpperHalfPlane.ext
    simp only [gluedInteriorChartPoint_coe, hγ1]
  rw [h0, h1, edist_dist] at hmodel
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by linarith : 0 ≤ dist y z + δ)).1 hmodel
  linarith

/-- Each actual interior chart is a hyperbolic metric isometry on a
constructed small intrinsic ball. Smooth hyperbolic segments provide the
upper bound; the native short-path barrier provides the lower bound. -/
theorem gluedIntrinsicMetric_interior_locally_isometric
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    (x : P.GluedCarrier) (hx : x ∈ e.source) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ ρ > 0, ∃ hball : ball x ρ ⊆ e.source,
      ∀ (y : P.GluedCarrier) (hy : y ∈ ball x ρ)
        (z : P.GluedCarrier) (hz : z ∈ ball x ρ),
        dist (P.gluedInteriorChartPoint e he y (hball hy))
          (P.gluedInteriorChartPoint e he z (hball hz)) = dist y z := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  obtain ⟨ρ₁, hρ₁, hball₁, hlower⟩ :=
    P.gluedIntrinsicMetric_interior_hyperbolic_dist_locally_le e he x hx
  let q := P.gluedInteriorChartPoint e he x hx
  have htarget : ((↑) : ℍ → ℂ) ⁻¹' e.target ∈ 𝓝 q :=
    (e.open_target.preimage UpperHalfPlane.continuous_coe).mem_nhds (e.map_source hx)
  obtain ⟨δ, hδ, hmodelball⟩ := Metric.mem_nhds_iff.1 htarget
  obtain ⟨ρ₂, hρ₂, hball₂, hcoord⟩ :=
    P.gluedInteriorChart_exists_coordinate_ball e he x hx (show 0 < δ / 4 by linarith)
  let ρ := min ρ₁ ρ₂
  have hρ : 0 < ρ := lt_min hρ₁ hρ₂
  have hsmall₁ : ball x ρ ⊆ ball x ρ₁ := ball_subset_ball (min_le_left _ _)
  have hsmall₂ : ball x ρ ⊆ ball x ρ₂ := ball_subset_ball (min_le_right _ _)
  have hball : ball x ρ ⊆ e.source := hsmall₁.trans hball₁
  refine ⟨ρ, hρ, hball, ?_⟩
  intro y hy z hz
  apply le_antisymm (hlower y (hsmall₁ hy) z (hsmall₁ hz))
  let qy := P.gluedInteriorChartPoint e he y (hball hy)
  let qz := P.gluedInteriorChartPoint e he z (hball hz)
  have hxy : dist q qy < δ / 4 := hcoord y (hsmall₂ hy)
  have hxz : dist q qz < δ / 4 := hcoord z (hsmall₂ hz)
  have hyz : dist qy qz < δ / 2 := by
    have := dist_triangle qy q qz
    rw [dist_comm qy q] at this
    linarith
  obtain ⟨α, hα, him, hα0, hα1, hlen, hpoints⟩ :=
    exists_hyperbolic_length_realizing_segment qy qz
  have hmap : MapsTo α (Icc 0 1) e.target := by
    intro t ht
    have hstep : dist qy (UpperHalfPlane.ofComplex (α t)) ≤ dist qy qz := by
      rw [hpoints t ht]
      exact mul_le_of_le_one_left dist_nonneg ht.2
    have hinside : dist q (UpperHalfPlane.ofComplex (α t)) < δ := by
      have := dist_triangle q qy (UpperHalfPlane.ofComplex (α t))
      linarith
    have hmem := hmodelball
      (show UpperHalfPlane.ofComplex (α t) ∈ ball q δ by
        simpa only [Metric.mem_ball, dist_comm] using hinside)
    simpa only [mem_preimage, UpperHalfPlane.ofComplex_apply_of_im_pos (him t),
      UpperHalfPlane.coe_mk] using hmem
  have hγ := P.gluedChart_lift_contMDiffOn e (Or.inl he) hα.contDiffOn hmap
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
  rw [h0, h1, P.gluedInteriorChart_lift_pathELength e he hα.contDiffOn hmap, hlen] at hupper
  simp only [edist_dist] at hupper
  exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).1 hupper

#print axioms gluedChart_lift_contMDiffOn
#print axioms gluedInteriorChart_lift_pathELength
#print axioms gluedCurve_interior_hyperbolic_edist_le_pathELength
#print axioms gluedIntrinsicMetric_interior_hyperbolic_dist_locally_le
#print axioms gluedIntrinsicMetric_interior_locally_isometric

/-- The original orbit metric and native glued metric agree on a constructed
neighborhood of each actual component-interior point. -/
theorem gluedComponent_interior_locally_dist_eq
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (q : P.ChainComponent i) (hqint : q.1 ∈ P.componentInteriorSet i) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ ε > 0, ∀ a b : P.ChainComponent i,
      P.gluedMk ⟨i, a⟩ ∈ ball (P.gluedMk ⟨i, q⟩) ε →
      P.gluedMk ⟨i, b⟩ ∈ ball (P.gluedMk ⟨i, q⟩) ε →
      dist a.1 b.1 = dist (P.gluedMk ⟨i, a⟩) (P.gluedMk ⟨i, b⟩) := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  obtain ⟨z, ρ, hρ, h4, hz, hinside, hf⟩ :=
    P.exists_gluedComponentInterior_ball_chart i ⟨q.1, hqint⟩
  let e := P.gluedInteriorComplexChart i z ρ hρ hinside hf
  have he : P.IsGluedInteriorComplexChart e := ⟨i, z, ρ, hρ, h4, hinside, hf, rfl⟩
  have hq : P.gluedMk ⟨i, q⟩ ∈ e.source := by
    rw [P.gluedInteriorComplexChart_source]
    refine ⟨⟨z, by simpa using hρ⟩, ?_⟩
    apply congrArg P.gluedMk
    apply congrArg (Sigma.mk i)
    exact Subtype.ext hz
  obtain ⟨ε, hε, hball, hmetric⟩ :=
    P.gluedIntrinsicMetric_interior_locally_isometric e he (P.gluedMk ⟨i, q⟩) hq
  refine ⟨ε, hε, ?_⟩
  intro a b ha hb
  obtain ⟨wa, hwa⟩ := (P.gluedInteriorComplexChart_source i z ρ hρ hinside hf) ▸ hball ha
  obtain ⟨wb, hwb⟩ := (P.gluedInteriorComplexChart_source i z ρ hρ hinside hf) ▸ hball hb
  have haq : (Quotient.mk'' wa.1 : (X i).Carrier) = a.1 := by
    have hcomp := P.gluedMk_injective_component i hwa
    exact congrArg Subtype.val hcomp
  have hbq : (Quotient.mk'' wb.1 : (X i).Carrier) = b.1 := by
    have hcomp := P.gluedMk_injective_component i hwb
    exact congrArg Subtype.val hcomp
  have hca : P.gluedInteriorChartPoint e he (P.gluedMk ⟨i, a⟩) (hball ha) = wa.1 := by
    apply UpperHalfPlane.ext
    change e (P.gluedMk ⟨i, a⟩) = (wa.1 : ℂ)
    rw [← hwa]
    exact P.gluedInteriorComplexChart_apply i z ρ hρ hinside hf wa
  have hcb : P.gluedInteriorChartPoint e he (P.gluedMk ⟨i, b⟩) (hball hb) = wb.1 := by
    apply UpperHalfPlane.ext
    change e (P.gluedMk ⟨i, b⟩) = (wb.1 : ℂ)
    rw [← hwb]
    exact P.gluedInteriorComplexChart_apply i z ρ hρ hinside hf wb
  calc
    dist a.1 b.1 = dist wa.1 wb.1 := by
      rw [← haq, ← hbq]
      exact (X i).carrier_dist_mk_eq_of_mem_small_ball z ρ h4 wa.2 wb.2
    _ = dist (P.gluedMk ⟨i, a⟩) (P.gluedMk ⟨i, b⟩) := by
      simpa only [hca, hcb] using hmetric (P.gluedMk ⟨i, a⟩) ha (P.gluedMk ⟨i, b⟩) hb

/-- Every genuinely deleted incoming boundary circle maps into the actual seam set. -/
theorem gluedMk_mem_gluedSeamSet_of_mem_left_circle
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (hi : 0 < i.1)
    (q : P.ChainComponent i)
    (hq : q.1 ∈ (X i).punctureCircle (P.centers i).1 (gluingRadius C g)) :
    P.gluedMk ⟨i, q⟩ ∈ P.gluedSeamSet := by
  let k : Fin (n - 1) := ⟨i.1 - 1, by have := i.2; omega⟩
  have hki : gluingChainEdgeRight k = i := Fin.ext (by dsimp [k, gluingChainEdgeRight]; omega)
  obtain ⟨w, hw, hwq⟩ := hq
  let w' : sphere (P.centers (gluingChainEdgeRight k)).1 (gluingRadius C g) :=
    ⟨w, by simpa only [hki] using hw⟩
  let e := gluingBoundaryCircleIsometry (P.centers (gluingChainEdgeLeft k)).2
    (P.centers (gluingChainEdgeRight k)).1 (gluingRadius C g)
  let z := e.symm w'
  have hmk (j : Fin n) (hji : j = i)
      (hjw : w ∈ sphere (P.centers j).1 (gluingRadius C g)) :
      (⟨j, P.leftCirclePoint j ⟨w, hjw⟩⟩ : P.ChainPieces) = ⟨i, q⟩ := by
    subst j
    apply congrArg (Sigma.mk i)
    exact Subtype.ext hwq
  have htarget : P.seamTarget k z = ⟨i, q⟩ := by
    change (⟨gluingChainEdgeRight k, P.leftCirclePoint _ (e z)⟩ : P.ChainPieces) = _
    rw [show e z = w' from e.apply_symm_apply _]
    exact hmk (gluingChainEdgeRight k) hki w'.2
  rw [← htarget, ← P.gluedMk_seamSource_eq_seamTarget k z]
  exact Set.mem_iUnion.mpr ⟨k, z, rfl⟩

/-- Every genuinely deleted outgoing boundary circle maps into the actual seam set. -/
theorem gluedMk_mem_gluedSeamSet_of_mem_right_circle
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (hi : i.1 + 1 < n)
    (q : P.ChainComponent i)
    (hq : q.1 ∈ (X i).punctureCircle (P.centers i).2 (gluingRadius C g)) :
    P.gluedMk ⟨i, q⟩ ∈ P.gluedSeamSet := by
  let k : Fin (n - 1) := ⟨i.1, by omega⟩
  have hki : gluingChainEdgeLeft k = i := Fin.ext rfl
  obtain ⟨w, hw, hwq⟩ := hq
  let w' : sphere (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) :=
    ⟨w, by simpa only [hki] using hw⟩
  have hsource : P.seamSource k w' = ⟨i, q⟩ := by
    change (⟨gluingChainEdgeLeft k, P.rightCirclePoint _ w'⟩ : P.ChainPieces) = _
    change (⟨i, P.rightCirclePoint i _⟩ : P.ChainPieces) = _
    apply congrArg (Sigma.mk i)
    exact Subtype.ext hwq
  rw [← hsource]
  exact Set.mem_iUnion.mpr ⟨k, w', rfl⟩

/-- Avoidance of the actual seams forces a retained point into the original
surface interior; a mere collar-neighborhood alternative is insufficient. -/
theorem mem_componentInteriorSet_of_gluedMk_not_mem_gluedSeamSet
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (q : P.ChainComponent i)
    (havoid : P.gluedMk ⟨i, q⟩ ∉ P.gluedSeamSet) : q.1 ∈ P.componentInteriorSet i := by
  have hsmall : 2 * gluingRadius C g < (X i).systole := by
    linarith [P.radius_lt_embeddedRadius, P.twice_outer_lt_systole i]
  let S : Set (X i).Carrier :=
    (if 0 < i.1 then closedBall (Quotient.mk'' (P.centers i).1) (gluingRadius C g) else ∅) ∪
    (if i.1 + 1 < n then closedBall (Quotient.mk'' (P.centers i).2) (gluingRadius C g) else ∅)
  have hS : IsClosed S := by
    apply IsClosed.union
    · split_ifs <;> first | exact isClosed_closedBall | exact isClosed_empty
    · split_ifs <;> first | exact isClosed_closedBall | exact isClosed_empty
  have hsub : (X i).punctureDeletedSet (P.centers i).1 (P.centers i).2
      (gluingRadius C g) i ⊆ S := by
    apply Set.union_subset_union
    · split_ifs
      · rw [← (X i).carrier_ball_eq_orbitBall]
        exact ball_subset_closedBall
      · exact subset_rfl
    · split_ifs
      · rw [← (X i).carrier_ball_eq_orbitBall]
        exact ball_subset_closedBall
      · exact subset_rfl
  have hleft : 0 < i.1 → q.1 ∉ closedBall (Quotient.mk'' (P.centers i).1)
      (gluingRadius C g) := by
    intro hi hclosed
    have hnotball : q.1 ∉ ball (Quotient.mk'' (P.centers i).1) (gluingRadius C g) := by
      intro hball
      apply q.2
      apply Or.inl
      simpa only [if_pos hi, (X i).carrier_ball_eq_orbitBall] using hball
    have hsphere : q.1 ∈ sphere (Quotient.mk'' (P.centers i).1) (gluingRadius C g) := by
      rw [mem_sphere]
      exact le_antisymm hclosed (le_of_not_gt hnotball)
    have hcircle : q.1 ∈ (X i).punctureCircle (P.centers i).1 (gluingRadius C g) := by
      rw [ClosedHyperbolicSurface.punctureCircle,
        (X i).image_quotientMk_sphere_eq_carrier_sphere _ _ hsmall]
      exact hsphere
    exact havoid (P.gluedMk_mem_gluedSeamSet_of_mem_left_circle i hi q hcircle)
  have hright : i.1 + 1 < n → q.1 ∉ closedBall (Quotient.mk'' (P.centers i).2)
      (gluingRadius C g) := by
    intro hi hclosed
    have hnotball : q.1 ∉ ball (Quotient.mk'' (P.centers i).2) (gluingRadius C g) := by
      intro hball
      apply q.2
      apply Or.inr
      simpa only [if_pos hi, (X i).carrier_ball_eq_orbitBall] using hball
    have hsphere : q.1 ∈ sphere (Quotient.mk'' (P.centers i).2) (gluingRadius C g) := by
      rw [mem_sphere]
      exact le_antisymm hclosed (le_of_not_gt hnotball)
    have hcircle : q.1 ∈ (X i).punctureCircle (P.centers i).2 (gluingRadius C g) := by
      rw [ClosedHyperbolicSurface.punctureCircle,
        (X i).image_quotientMk_sphere_eq_carrier_sphere _ _ hsmall]
      exact hsphere
    exact havoid (P.gluedMk_mem_gluedSeamSet_of_mem_right_circle i hi q hcircle)
  have hq : q.1 ∈ Sᶜ := by
    rintro (hl | hr)
    · split_ifs at hl with hi
      · exact hleft hi hl
      · exact hl
    · split_ifs at hr with hi
      · exact hright hi hr
      · exact hr
  exact interior_maximal (Set.compl_subset_compl.mpr hsub) hS.isOpen_compl hq

/-- Around every seam-free parameter value, a continuous actual component
lift preserves native distances for every pair of nearby parameters. -/
theorem continuous_component_lift_locally_dist_eq
    (P : ExerciseGluingPreparation C g n genera X) {α : Type*}
    [MetricSpace α] (i : Fin n) (δ : α → P.ChainComponent i)
    (hδ : Continuous δ) (t : α) (havoid : P.gluedMk ⟨i, δ t⟩ ∉ P.gluedSeamSet) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ η > 0, ∀ u v : α, dist u t < η → dist v t < η →
      dist (δ u).1 (δ v).1 = dist (P.gluedMk ⟨i, δ u⟩) (P.gluedMk ⟨i, δ v⟩) := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  have hint := P.mem_componentInteriorSet_of_gluedMk_not_mem_gluedSeamSet i (δ t) havoid
  obtain ⟨ε, hε, hdist⟩ := P.gluedComponent_interior_locally_dist_eq i (δ t) hint
  let f : α → P.GluedCarrier := fun u => P.gluedMk ⟨i, δ u⟩
  have hf : Continuous f := P.gluedMk_continuous.comp (continuous_sigmaMk.comp hδ)
  have hpre : f ⁻¹' ball (f t) ε ∈ 𝓝 t :=
    hf.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds (by simpa using hε))
  obtain ⟨η, hη, hsub⟩ := Metric.mem_nhds_iff.mp hpre
  exact ⟨η, hη, fun u v hu hv => hdist (δ u) (δ v) (hsub hu) (hsub hv)⟩

/-- A seam-avoiding excursion has a continuous original-component lift whose
interior parameter neighborhoods preserve the two actual metrics exactly. -/
theorem exists_locally_isometric_component_lift_of_excursion
    (P : ExerciseGluingPreparation C g n genera X) {a b : ℝ} (hab : a < b)
    (γ : ℝ → P.GluedCarrier) (hγ : ContinuousOn γ (Icc a b))
    (havoid : MapsTo γ (Ioo a b) P.gluedSeamSetᶜ) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ (i : Fin n) (δ : Icc a b → P.ChainComponent i),
      Continuous δ ∧ (∀ t : Icc a b, γ t = P.gluedMk ⟨i, δ t⟩) ∧
      ∀ t : Icc a b, a < t.1 → t.1 < b → ∃ η > 0,
        ∀ u v : Icc a b, dist u t < η → dist v t < η →
          dist (δ u).1 (δ v).1 = dist (γ u) (γ v) := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  obtain ⟨i, δ, hδ, hlift⟩ := P.exists_continuous_component_lift_of_excursion hab γ hγ havoid
  refine ⟨i, δ, hδ, hlift, ?_⟩
  intro t hta htb
  have hnonseam : P.gluedMk ⟨i, δ t⟩ ∉ P.gluedSeamSet := by
    rw [← hlift t]
    exact havoid ⟨hta, htb⟩
  obtain ⟨η, hη, hdist⟩ := P.continuous_component_lift_locally_dist_eq i δ hδ t hnonseam
  refine ⟨η, hη, ?_⟩
  intro u v hu hv
  simpa only [hlift u, hlift v] using hdist u v hu hv

#print axioms SystolicGrowth.ExerciseGluingPreparation.gluedComponent_interior_locally_dist_eq
#print axioms SystolicGrowth.ExerciseGluingPreparation.mem_componentInteriorSet_of_gluedMk_not_mem_gluedSeamSet
#print axioms SystolicGrowth.ExerciseGluingPreparation.exists_locally_isometric_component_lift_of_excursion

end SystolicGrowth.ExerciseGluingPreparation
