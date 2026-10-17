module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainCollarAreaCharts
public import Geometry.GluingChainGaussBonnet
public import Geometry.GluingCollarLocalizedCurvatureMass
public import Geometry.GluingDisjointThinSeamCollars
public import Geometry.GluingChainCurvatureRadon
public import Geometry.GluingChainSmoothCurvature

@[expose] public section

/-!
# Exact Gauss--Bonnet mass for the actual localized smooth metrics

The native strip area is computed in genuine angular charts. Two half-turn
charts miss two meridians, whose actual area vanishes in other charts.
The exact signed smoothed strip mass then cancels the original strip area.
-/

open Set Filter MeasureTheory
open scoped ENNReal BigOperators

namespace SystolicGrowth

noncomputable section

def Internal.GluingChainSmoothGaussBonnetHelpers.collarStripRectangle (R : ℝ) (A : Set ℝ) : Set ℂ :=
  Complex.measurableEquivRealProd ⁻¹' (Ioo (-R) R ×ˢ A)

private theorem collarStripRectangle_measurable (R : ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) : MeasurableSet (Internal.GluingChainSmoothGaussBonnetHelpers.collarStripRectangle R A) :=
  (measurableSet_Ioo.prod hA).preimage Complex.measurableEquivRealProd.measurable

private theorem collarStripRectangle_area (r R : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    (∫⁻ z : ℂ in Internal.GluingChainSmoothGaussBonnetHelpers.collarStripRectangle R A, ENNReal.ofReal (gluingCollarWarp r z.re)) =
      (∫⁻ t : ℝ in Ioo (-R) R, ENNReal.ofReal (gluingCollarWarp r t)) * volume A := by
  have hf : Measurable (fun z : ℂ => ENNReal.ofReal (gluingCollarWarp r z.re)) :=
    ((gluingCollarWarp_continuous r).comp Complex.continuous_re).measurable.ennreal_ofReal
  rw [← Complex.volume_preserving_equiv_real_prod.symm.map_eq,
    setLIntegral_map (collarStripRectangle_measurable R hA) hf
      Complex.measurableEquivRealProd.symm.measurable]
  have hpre : Complex.measurableEquivRealProd.symm ⁻¹' Internal.GluingChainSmoothGaussBonnetHelpers.collarStripRectangle R A =
      Ioo (-R) R ×ˢ A := by
    ext p
    simp [Internal.GluingChainSmoothGaussBonnetHelpers.collarStripRectangle]
  rw [hpre]
  change (∫⁻ p : ℝ × ℝ in Ioo (-R) R ×ˢ A,
    ENNReal.ofReal (gluingCollarWarp r p.1) ∂volume.prod volume) = _
  have hpf : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (gluingCollarWarp r p.1)) :=
    ((gluingCollarWarp_continuous r).comp continuous_fst).measurable.ennreal_ofReal
  rw [setLIntegral_prod _ hpf.aemeasurable]
  simp only [lintegral_const, Measure.restrict_apply_univ]
  exact lintegral_mul_const _ (gluingCollarWarp_continuous r).measurable.ennreal_ofReal

local instance smoothGaussBonnetMeasurableSpaceCircle : MeasurableSpace Circle :=
  borel Circle
local instance smoothGaussBonnetBorelSpaceCircle : BorelSpace Circle := ⟨rfl⟩

/-- **Math.** Exact signed Gaussian mass of the actual localized thin-cylinder metric. -/
theorem gluingThinCylinderCurvature_univ (r : ℝ) {ε δ : ℝ}
    (hε : 0 < ε) (b : ContDiffBump (0 : ℝ)) (hδ : b.rOut ≤ δ) :
    gluingThinCylinderCurvature r ε b δ univ = -4 * Real.pi * Real.cosh (r + δ) := by
  have hI := gluingThinCylinderCurvatureDensity_integrable r hε b δ
  rw [gluingThinCylinderCurvature, withDensityᵥ_apply hI MeasurableSet.univ,
    Measure.restrict_univ, gluingThinCylinderCoordinateMeasure, integral_prod _ hI]
  simp only [gluingThinCylinderCurvatureDensity, integral_const, smul_eq_mul]
  rw [measureReal_def, gluingCircleAngularLengthMeasure_univ,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi),
    gluingThinRadialMeasure, integral_subtype_comap measurableSet_Ioo
      (fun t : ℝ => -deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) t),
    integral_neg, gluingCollarLocalizedSmoothWarp_second_deriv_integral_Ioo_eq r hε b hδ]
  ring

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

private theorem stripRectangle_subset_chart_target
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {A : Set ℝ} (hA : A ⊆ GluingAngularInterval θ) :
    Internal.GluingChainSmoothGaussBonnetHelpers.collarStripRectangle (gluingThinSeamWidth C g) A ⊆
      (P.seamAngularComplexChart k θ).target := by
  intro z hz
  change z.re ∈ Ioo (-gluingThinSeamWidth C g) (gluingThinSeamWidth C g) ∧ z.im ∈ A at hz
  apply (P.mem_seamAngularComplexChart_target k θ z).mpr
  exact ⟨⟨by linarith [hz.1.1, P.thinSeamWidth_lt_depth],
    by linarith [hz.1.2, P.thinSeamWidth_lt_depth]⟩, hA hz.2⟩

private theorem stripRectangle_inverse_subset_thin
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {A : Set ℝ} (hA : A ⊆ GluingAngularInterval θ) :
    (P.seamAngularComplexChart k θ).symm '' Internal.GluingChainSmoothGaussBonnetHelpers.collarStripRectangle (gluingThinSeamWidth C g) A ⊆
      P.thinSeamCollar k := by
  rintro _ ⟨z, hz, rfl⟩
  have ht := (P.mem_seamAngularComplexChart_target k θ z).mp
    (stripRectangle_subset_chart_target P k θ hA hz)
  let p : GluingSeamAngularDomain C g θ := (⟨z.re, ht.1⟩, ⟨z.im, ht.2⟩)
  have heq : gluingSeamAngularModel C g θ p = z := Complex.ext rfl rfl
  rw [← heq, P.seamAngularComplexChart_symm_apply]
  refine ⟨(Circle.exp p.2.1, p.1), ?_, rfl⟩
  exact abs_lt.mpr hz.1

private theorem stripRectangle_inverse_point
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {A : Set ℝ} (hA : A ⊆ GluingAngularInterval θ) {z : ℂ}
    (hz : z ∈ Internal.GluingChainSmoothGaussBonnetHelpers.collarStripRectangle (gluingThinSeamWidth C g) A) :
    (P.seamAngularComplexChart k θ).symm z =
      (P.seamCylinderHomeomorph k (Circle.exp z.im,
        ⟨z.re, ((P.mem_seamAngularComplexChart_target k θ z).mp
          (stripRectangle_subset_chart_target P k θ hA hz)).1⟩)).1 := by
  have ht := (P.mem_seamAngularComplexChart_target k θ z).mp
    (stripRectangle_subset_chart_target P k θ hA hz)
  let p : GluingSeamAngularDomain C g θ := (⟨z.re, ht.1⟩, ⟨z.im, ht.2⟩)
  have heq : gluingSeamAngularModel C g θ p = z := Complex.ext rfl rfl
  conv_lhs => rw [← heq, P.seamAngularComplexChart_symm_apply]
  rfl

/-- **Math.** Two half-turn charts and two genuine meridians partition
the actual native thin strip. -/
private theorem thinSeamCollar_eq_four_chart_pieces
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.thinSeamCollar k =
      ((P.seamAngularComplexChart k (-Real.pi / 2)).symm ''
        Internal.GluingChainSmoothGaussBonnetHelpers.collarStripRectangle (gluingThinSeamWidth C g) (Ioo (-Real.pi) 0) ∪
      (P.seamAngularComplexChart k (Real.pi / 2)).symm ''
        Internal.GluingChainSmoothGaussBonnetHelpers.collarStripRectangle (gluingThinSeamWidth C g) (Ioo 0 Real.pi)) ∪
      ((P.seamAngularComplexChart k 0).symm ''
        Internal.GluingChainSmoothGaussBonnetHelpers.collarStripRectangle (gluingThinSeamWidth C g) {0} ∪
      (P.seamAngularComplexChart k Real.pi).symm ''
        Internal.GluingChainSmoothGaussBonnetHelpers.collarStripRectangle (gluingThinSeamWidth C g) {Real.pi}) := by
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    let α := Complex.arg (p.1 : ℂ)
    have hαlo : -Real.pi < α := Complex.neg_pi_lt_arg _
    have hαhi : α ≤ Real.pi := Complex.arg_le_pi _
    by_cases hαn : α < 0
    · let q : GluingSeamAngularDomain C g (-Real.pi / 2) :=
        (p.2, ⟨α, by constructor <;> linarith⟩)
      refine Or.inl (Or.inl ⟨gluingSeamAngularModel C g (-Real.pi / 2) q,
        ⟨abs_lt.mp hp, hαlo, hαn⟩, ?_⟩)
      rw [P.seamAngularComplexChart_symm_apply]
      change (P.seamCylinderHomeomorph k (Circle.exp (Complex.arg (p.1 : ℂ)), p.2)).1 = _
      rw [Circle.exp_arg]
    · by_cases hα0 : α = 0
      · let q : GluingSeamAngularDomain C g 0 :=
          (p.2, ⟨0, by constructor <;> linarith [Real.pi_pos]⟩)
        refine Or.inr (Or.inl ⟨gluingSeamAngularModel C g 0 q, ⟨abs_lt.mp hp, rfl⟩, ?_⟩)
        rw [P.seamAngularComplexChart_symm_apply]
        change (P.seamCylinderHomeomorph k (Circle.exp 0, p.2)).1 = _
        rw [← hα0, Circle.exp_arg]
      · have hαp : 0 < α := lt_of_le_of_ne (le_of_not_gt hαn) (Ne.symm hα0)
        by_cases hα : α < Real.pi
        · let q : GluingSeamAngularDomain C g (Real.pi / 2) :=
            (p.2, ⟨α, by constructor <;> linarith⟩)
          refine Or.inl (Or.inr ⟨gluingSeamAngularModel C g (Real.pi / 2) q,
            ⟨abs_lt.mp hp, hαp, hα⟩, ?_⟩)
          rw [P.seamAngularComplexChart_symm_apply]
          change (P.seamCylinderHomeomorph k (Circle.exp (Complex.arg (p.1 : ℂ)), p.2)).1 = _
          rw [Circle.exp_arg]
        · have hαeq : α = Real.pi := le_antisymm hαhi (le_of_not_gt hα)
          let q : GluingSeamAngularDomain C g Real.pi :=
            (p.2, ⟨Real.pi, by constructor <;> linarith [Real.pi_pos]⟩)
          refine Or.inr (Or.inr ⟨gluingSeamAngularModel C g Real.pi q, ⟨abs_lt.mp hp, rfl⟩, ?_⟩)
          rw [P.seamAngularComplexChart_symm_apply]
          change (P.seamCylinderHomeomorph k (Circle.exp Real.pi, p.2)).1 = _
          rw [← hαeq, Circle.exp_arg]
  · refine union_subset (union_subset ?_ ?_) (union_subset ?_ ?_)
    · exact stripRectangle_inverse_subset_thin P k (-Real.pi / 2) (by
        intro a ha
        constructor <;> linarith [ha.1, ha.2])
    · exact stripRectangle_inverse_subset_thin P k (Real.pi / 2) (by
        intro a ha
        constructor <;> linarith [ha.1, ha.2])
    · exact stripRectangle_inverse_subset_thin P k 0 (by
        intro a ha
        rcases ha with rfl
        constructor <;> linarith [Real.pi_pos])
    · exact stripRectangle_inverse_subset_thin P k Real.pi (by
        intro a ha
        rcases ha with rfl
        constructor <;> linarith [Real.pi_pos])

private theorem stripRectangle_native_area
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {A : Set ℝ} (hA : MeasurableSet A) (hAθ : A ⊆ GluingAngularInterval θ) :
    P.gluedChainAreaMeasure ((P.seamAngularComplexChart k θ).symm ''
      Internal.GluingChainSmoothGaussBonnetHelpers.collarStripRectangle (gluingThinSeamWidth C g) A) =
      (∫⁻ t : ℝ in Ioo (-gluingThinSeamWidth C g) (gluingThinSeamWidth C g),
        ENNReal.ofReal (gluingCollarWarp (gluingRadius C g) t)) * volume A := by
  rw [P.gluedChainAreaMeasure_seamAngularComplexChart_image_integral k θ
    (collarStripRectangle_measurable _ hA) (stripRectangle_subset_chart_target P k θ hAθ)]
  exact collarStripRectangle_area _ _ hA

/-- **Math.** Exact original native area of one true thin smoothing strip. -/
theorem gluedChainAreaMeasure_thinSeamCollar
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedChainAreaMeasure (P.thinSeamCollar k) =
      ENNReal.ofReal (4 * Real.pi *
        (Real.cosh (gluingRadius C g + gluingThinSeamWidth C g) - Real.cosh (gluingRadius C g))) := by
  let Aneg := (P.seamAngularComplexChart k (-Real.pi / 2)).symm ''
    Internal.GluingChainSmoothGaussBonnetHelpers.collarStripRectangle (gluingThinSeamWidth C g) (Ioo (-Real.pi) 0)
  let Apos := (P.seamAngularComplexChart k (Real.pi / 2)).symm ''
    Internal.GluingChainSmoothGaussBonnetHelpers.collarStripRectangle (gluingThinSeamWidth C g) (Ioo 0 Real.pi)
  let A₀ := (P.seamAngularComplexChart k 0).symm ''
    Internal.GluingChainSmoothGaussBonnetHelpers.collarStripRectangle (gluingThinSeamWidth C g) {0}
  let Aπ := (P.seamAngularComplexChart k Real.pi).symm ''
    Internal.GluingChainSmoothGaussBonnetHelpers.collarStripRectangle (gluingThinSeamWidth C g) {Real.pi}
  have hn : Ioo (-Real.pi) 0 ⊆ GluingAngularInterval (-Real.pi / 2) := by
    intro a ha
    constructor <;> linarith [ha.1, ha.2]
  have hp : Ioo 0 Real.pi ⊆ GluingAngularInterval (Real.pi / 2) := by
    intro a ha
    constructor <;> linarith [ha.1, ha.2]
  have hzero (θ : ℝ) : P.gluedChainAreaMeasure ((P.seamAngularComplexChart k θ).symm ''
      Internal.GluingChainSmoothGaussBonnetHelpers.collarStripRectangle (gluingThinSeamWidth C g) {θ}) = 0 := by
    rw [stripRectangle_native_area P k θ (measurableSet_singleton _) (by
      intro a ha
      rcases ha with rfl
      constructor <;> linarith [Real.pi_pos]), measure_singleton, mul_zero]
  have hmer : P.gluedChainAreaMeasure (A₀ ∪ Aπ) = 0 :=
    measure_union_null (hzero 0) (hzero Real.pi)
  have hpiece : P.gluedChainAreaMeasure (P.thinSeamCollar k) = P.gluedChainAreaMeasure (Aneg ∪ Apos) := by
    rw [thinSeamCollar_eq_four_chart_pieces P k]
    apply le_antisymm
    · exact (measure_union_le (Aneg ∪ Apos) (A₀ ∪ Aπ)).trans (by rw [hmer, add_zero])
    · exact measure_mono subset_union_left
  have hd : Disjoint Aneg Apos := by
    apply disjoint_left.mpr
    rintro x ⟨z, hz, hzx⟩ ⟨w, hw, hwx⟩
    have heq := hzx.trans hwx.symm
    rw [stripRectangle_inverse_point P k _ hn hz,
      stripRectangle_inverse_point P k _ hp hw] at heq
    change z.re ∈ Ioo (-gluingThinSeamWidth C g) (gluingThinSeamWidth C g) ∧
      z.im ∈ Ioo (-Real.pi) 0 at hz
    change w.re ∈ Ioo (-gluingThinSeamWidth C g) (gluingThinSeamWidth C g) ∧
      w.im ∈ Ioo 0 Real.pi at hw
    have hcircle := congrArg Prod.fst ((P.seamCylinderHomeomorph k).injective (Subtype.ext heq))
    have hzw : z.im = w.im := Circle.exp_injOn_Ioc (by linarith :
        Real.pi - (-Real.pi) ≤ 2 * Real.pi)
      ⟨hz.2.1, by linarith [hz.2.2, Real.pi_pos]⟩
      ⟨by linarith [hw.2.1, Real.pi_pos], hw.2.2.le⟩ hcircle
    linarith [hz.2.2, hw.2.1]
  have hmp : MeasurableSet Apos := (collarStripRectangle_measurable _ measurableSet_Ioo)
    |>.image_of_continuousOn_injOn
      ((P.seamAngularComplexChart k (Real.pi / 2)).symm.continuousOn.mono
        (stripRectangle_subset_chart_target P k _ hp))
      ((P.seamAngularComplexChart k (Real.pi / 2)).symm.injOn.mono
        (stripRectangle_subset_chart_target P k _ hp))
  rw [hpiece, measure_union hd hmp,
    stripRectangle_native_area P k _ measurableSet_Ioo hn,
    stripRectangle_native_area P k _ measurableSet_Ioo hp, Real.volume_Ioo, Real.volume_Ioo]
  have hi : IntegrableOn (gluingCollarWarp (gluingRadius C g))
      (Ioo (-gluingThinSeamWidth C g) (gluingThinSeamWidth C g)) :=
    (gluingCollarWarp_continuous (gluingRadius C g)).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun t => (gluingCollarWarp_pos P.radius_pos t).le),
    ← integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show -gluingThinSeamWidth C g ≤ gluingThinSeamWidth C g by
      linarith [P.thinSeamWidth_pos]),
    gluingCollarWarp_integral_symmetric_window _ P.thinSeamWidth_pos]
  rw [← mul_add, ← ENNReal.ofReal_add (by linarith [Real.pi_pos] : 0 ≤ (0 : ℝ) - -Real.pi)
    (by linarith [Real.pi_pos] : 0 ≤ Real.pi - 0), mul_comm,
    ← ENNReal.ofReal_mul (by linarith [Real.pi_pos] : 0 ≤ ((0 : ℝ) - -Real.pi) + (Real.pi - 0))]
  congr 1
  ring

/-- **Math.** Exact native strip area as a real mass. -/
theorem gluedChainAreaMeasure_real_thinSeamCollar
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedChainAreaMeasure.real (P.thinSeamCollar k) =
      4 * Real.pi *
        (Real.cosh (gluingRadius C g + gluingThinSeamWidth C g) - Real.cosh (gluingRadius C g)) := by
  have hc : Real.cosh (gluingRadius C g) ≤
      Real.cosh (gluingRadius C g + gluingThinSeamWidth C g) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_pos P.radius_pos, abs_of_pos (add_pos P.radius_pos P.thinSeamWidth_pos)]
    linarith [P.thinSeamWidth_pos]
  rw [measureReal_def, P.gluedChainAreaMeasure_thinSeamCollar k,
    ENNReal.toReal_ofReal (mul_nonneg (by positivity) (sub_nonneg.mpr hc))]

/-- **Math.** Pushing a true cylinder through its native injective seam chart
does not change its exact signed Gaussian mass. -/
theorem gluedChainSmoothSeamCurvature_univ
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 < ε)
    (k : Fin (n - 1)) :
    P.gluedChainSmoothSeamCurvature ε k univ =
      -4 * Real.pi * Real.cosh (gluingRadius C g + gluingThinSeamWidth C g) := by
  rw [gluedChainSmoothSeamCurvature,
    VectorMeasure.map_apply _ (P.thinSeamCylinderMap_measurableEmbedding k).measurable
      MeasurableSet.univ, preimage_univ]
  exact gluingThinCylinderCurvature_univ _ hε _ le_rfl

/-- **Math.** The actual disjoint native thin strips give the unchanged outside-area mass. -/
theorem gluedChainSmoothOutsideArea_real_univ
    (P : ExerciseGluingPreparation C g n genera X) :
    P.gluedChainSmoothOutsideArea.real univ = P.gluedChainAreaMeasure.real univ -
      ((n - 1 : ℕ) : ℝ) * (4 * Real.pi *
        (Real.cosh (gluingRadius C g + gluingThinSeamWidth C g) - Real.cosh (gluingRadius C g))) := by
  have hmeas (k : Fin (n - 1)) : MeasurableSet (P.thinSeamCollar k) :=
    (P.thinSeamCollar_isOpen k).measurableSet
  have hdisj : Pairwise (fun k l => Disjoint (P.thinSeamCollar k) (P.thinSeamCollar l)) := by
    intro k l hkl
    exact (P.closedThinSeamCollar_disjoint hkl).mono
      (P.thinSeamCollar_subset_closedThinSeamCollar k)
      (P.thinSeamCollar_subset_closedThinSeamCollar l)
  have hmass := measureReal_iUnion_fintype (μ := P.gluedChainAreaMeasure) hdisj hmeas
  simp_rw [P.gluedChainAreaMeasure_real_thinSeamCollar] at hmass
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hmass
  have hsplit := measureReal_add_measureReal_compl
    (μ := P.gluedChainAreaMeasure) (MeasurableSet.iUnion hmeas)
  rw [hmass] at hsplit
  rw [measureReal_def, gluedChainSmoothOutsideArea, Measure.restrict_apply_univ]
  change P.gluedChainAreaMeasure.real (⋃ k : Fin (n - 1), P.thinSeamCollar k)ᶜ = _
  linarith

/-- **Math.** Exact Gauss--Bonnet total for the constructed genuine smooth
metrics, obtained by computing native strip areas and signed Gaussian masses. -/
theorem gluedChainSmoothCurvature_univ
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 < ε)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) :
    P.gluedChainSmoothCurvature ε univ = -4 * Real.pi * ((g : ℝ) - 1) := by
  rw [gluedChainSmoothCurvature, add_apply, neg_apply,
    Measure.toSignedMeasure_apply_measurable MeasurableSet.univ]
  simp only [FunLike.coe_sum, Finset.sum_apply]
  simp_rw [P.gluedChainSmoothSeamCurvature_univ hε]
  rw [P.gluedChainSmoothOutsideArea_real_univ, P.gluedChainAreaMeasure_real_univ hn hsum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **Math.** The actual Gaussian field of each smooth approximant has the
original genus's exact Gauss--Bonnet integral against its constructed metric area. -/
theorem gluedChainSmoothGaussian_integral
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 < ε)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) :
    (∫ p, P.gluedChainSmoothGaussian ε p ∂P.gluedChainSmoothAreaMeasure ε) =
      -4 * Real.pi * ((g : ℝ) - 1) := by
  have hmass := P.gluedChainSmoothCurvature_univ hε hn hsum
  rw [P.gluedChainSmoothCurvature_eq_area_withDensity_gaussian hε,
    withDensityᵥ_apply (P.gluedChainSmoothGaussian_integrable_area hε)
      MeasurableSet.univ, Measure.restrict_univ] at hmass
  exact hmass

#print axioms gluedChainAreaMeasure_thinSeamCollar
#print axioms gluingThinCylinderCurvature_univ
#print axioms gluedChainSmoothOutsideArea_real_univ
#print axioms gluedChainSmoothCurvature_univ
#print axioms gluedChainSmoothGaussian_integral

end ExerciseGluingPreparation
end
end SystolicGrowth
