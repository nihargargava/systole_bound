module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainSmoothCurvature
public import Geometry.GluingChainCurvatureLocalSheets
public import Geometry.HyperbolicConformalCurvature
public import Geometry.GluingChainSmoothAreaCharts
public import Geometry.GluingChainSmoothRegularity

@[expose] public section

/-!
# Actual determinant area in exterior native charts

Outside the genuine thin patches, all transported cylinder areas vanish.
The remaining original area is pulled through the literal hyperbolic
projection sheet and identified with the determinant of the actual tensor.
-/

open Set MeasureTheory UpperHalfPlane
open scoped ENNReal UpperHalfPlane Manifold

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The actual smoothed area restricts outside all thin patches to the
original native area: no cylinder contribution survives there. -/
theorem gluedChainSmoothAreaMeasure_restrict_outside_thinCollars
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) :
    (P.gluedChainSmoothAreaMeasure ε).restrict
        (⋃ k : Fin (n - 1), P.thinSeamCollar k)ᶜ =
      P.gluedChainAreaMeasure.restrict
        (⋃ k : Fin (n - 1), P.thinSeamCollar k)ᶜ := by
  classical
  let U : Set P.GluedCarrier := ⋃ k : Fin (n - 1), P.thinSeamCollar k
  have hU : MeasurableSet U :=
    MeasurableSet.iUnion (fun k => (P.thinSeamCollar_isOpen k).measurableSet)
  have hz (k : Fin (n - 1)) : (P.gluedChainSmoothSeamArea ε k).restrict Uᶜ = 0 := by
    rw [gluedChainSmoothSeamArea,
      (P.thinSeamCylinderMap_measurableEmbedding k).restrict_map]
    have hpre : P.thinSeamCylinderMap k ⁻¹' Uᶜ = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      apply hp
      apply mem_iUnion.mpr
      refine ⟨k, ?_⟩
      rw [← P.range_thinSeamCylinderMap k]
      exact mem_range_self p
    simp [hpre]
  have houtside : P.gluedChainSmoothOutsideArea.restrict Uᶜ =
      P.gluedChainAreaMeasure.restrict Uᶜ := by
    rw [gluedChainSmoothOutsideArea, Measure.restrict_restrict hU.compl, inter_self]
  apply Measure.ext
  intro s hs
  have hzval (k : Fin (n - 1)) : P.gluedChainSmoothSeamArea ε k (s ∩ Uᶜ) = 0 := by
    have h := congrArg (fun μ : Measure P.GluedCarrier => μ s) (hz k)
    simpa [Measure.restrict_apply hs] using h
  change (P.gluedChainSmoothAreaMeasure ε).restrict Uᶜ s =
    (P.gluedChainAreaMeasure.restrict Uᶜ) s
  rw [Measure.restrict_apply hs]
  simp only [gluedChainSmoothAreaMeasure, Measure.add_apply, Measure.finsetSum_apply,
    hzval, Finset.sum_const_zero, add_zero]
  have h := congrArg (fun μ : Measure P.GluedCarrier => μ s) houtside
  simpa only [Measure.restrict_apply hs] using h

/-- Original glued area in any of its actual interior charts is exactly
the genuine Poincaré area density in complex Lebesgue coordinates. -/
theorem gluedChainAreaMeasure_interiorComplexChart_image
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    {s : Set ℂ} (hs : MeasurableSet s) (ht : s ⊆ e.target) :
    P.gluedChainAreaMeasure (e.symm '' s) =
      ∫⁻ z : ℂ in s, ENNReal.ofReal ((z.im ^ 2)⁻¹) := by
  rcases he with ⟨i, o, R, hR, h4, hq, hf, rfl⟩
  let t : Set (Metric.ball o R) := (fun w => (w.1 : ℂ)) ⁻¹' s
  have htmeas : MeasurableSet t := hs.preimage
    (UpperHalfPlane.continuous_coe.comp continuous_subtype_val).measurable
  have hι := P.gluedInteriorProjectionSheet_measurableEmbedding i o R (by linarith) hq
  have himage : (P.gluedInteriorComplexChart i o R hR hq hf).symm '' s =
      (fun w : Metric.ball o R =>
        P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' w.1, hq w⟩)) '' t := by
    apply Subset.antisymm
    · rintro y ⟨z, hz, rfl⟩
      obtain ⟨w, rfl⟩ := (P.gluedInteriorComplexChart_target i o R hR hq hf) ▸ ht hz
      exact ⟨w, hz, P.gluedInteriorComplexChart_symm_apply i o R hR hq hf w |>.symm⟩
    · rintro y ⟨w, hw, rfl⟩
      exact ⟨(w.1 : ℂ), hw, P.gluedInteriorComplexChart_symm_apply i o R hR hq hf w⟩
  have harea := congrArg (fun μ : Measure (Metric.ball o R) => μ t)
    (P.gluedChainAreaMeasure_projectionSheet_comap i o R (by linarith) hq)
  rw [Measure.comap_apply _ hι.injective (fun _ hv => hι.measurableSet_image' hv) _ htmeas,
    comap_subtype_coe_apply measurableSet_ball] at harea
  rw [himage, harea]
  have hsubimage : Subtype.val '' t = UpperHalfPlane.coe ⁻¹' s := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hw
      obtain ⟨v, hv⟩ := (P.gluedInteriorComplexChart_target i o R hR hq hf) ▸ ht hw
      have hvw : v.1 = w := UpperHalfPlane.coe_injective hv
      exact ⟨v, by simpa [t, hvw] using hw, hvw⟩
  rw [hsubimage, UpperHalfPlane.volume_eq_lintegral]
  have hcoeimage : UpperHalfPlane.coe '' (UpperHalfPlane.coe ⁻¹' s) = s := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      have hpos : 0 < z.im := P.gluedInteriorComplexChart_target_im_pos
        (P.gluedInteriorComplexChart i o R hR hq hf)
        ⟨i, o, R, hR, h4, hq, hf, rfl⟩ (ht hz)
      exact ⟨⟨z, hpos⟩, hz, rfl⟩
  rw [hcoeimage]
  apply lintegral_congr
  intro z
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  simp [NNReal.coe_pow, NNReal.coe_inv, coe_nnnorm, Real.norm_eq_abs, one_div, sq_abs]

/-- In a literal exterior interior chart, patched area is exactly
original complex Lebesgue measure with Poincaré density. -/
theorem gluedChainSmoothAreaMeasure_exteriorInteriorComplexChart_image
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    {s : Set ℂ} (hs : MeasurableSet s) (ht : s ⊆ e.target)
    (houtside : ∀ z ∈ s, ∀ k : Fin (n - 1), e.symm z ∉ P.thinSeamCollar k) :
    P.gluedChainSmoothAreaMeasure ε (e.symm '' s) =
      ∫⁻ z : ℂ in s, ENNReal.ofReal ((z.im ^ 2)⁻¹) := by
  have hmeas : MeasurableSet (e.symm '' s) :=
    hs.image_of_continuousOn_injOn (e.symm.continuousOn.mono ht)
      (e.symm.injOn.mono ht)
  have hsub : e.symm '' s ⊆ (⋃ k : Fin (n - 1), P.thinSeamCollar k)ᶜ := by
    rintro q ⟨z, hz, rfl⟩ hq
    rcases mem_iUnion.mp hq with ⟨k, hk⟩
    exact houtside z hz k hk
  have h := congrArg (fun μ : Measure P.GluedCarrier => μ (e.symm '' s))
    (P.gluedChainSmoothAreaMeasure_restrict_outside_thinCollars ε)
  rw [Measure.restrict_apply hmeas, Measure.restrict_apply hmeas,
    inter_eq_left.mpr hsub] at h
  exact h.trans (P.gluedChainAreaMeasure_interiorComplexChart_image e he hs ht)

/-- Exterior area is the square-root determinant of the genuine global
smoothed tensor, expressed in the original native interior chart. -/
theorem gluedChainSmoothAreaMeasure_exteriorInteriorComplexChart_metric_image
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    {s : Set ℂ} (hs : MeasurableSet s) (ht : s ⊆ e.target)
    (houtside : ∀ z ∈ s, ∀ k : Fin (n - 1), e.symm z ∉ P.thinSeamCollar k) :
    P.gluedChainSmoothAreaMeasure ε (e.symm '' s) =
      ∫⁻ z : ℂ in s, ENNReal.ofReal
        (Real.sqrt (P.gluedSmoothInteriorCoordinateMetric ε e he (z.re, z.im)).det) := by
  rw [P.gluedChainSmoothAreaMeasure_exteriorInteriorComplexChart_image ε e he hs ht houtside]
  apply setLIntegral_congr_fun hs
  intro z hz
  change ENNReal.ofReal ((z.im ^ 2)⁻¹) = ENNReal.ofReal
    (Real.sqrt (P.gluedSmoothInteriorCoordinateMetric ε e he (z.re, z.im)).det)
  have hp : Complex.equivRealProdCLM.symm (z.re, z.im) = z := Complex.ext rfl rfl
  rw [P.gluedSmoothInteriorCoordinateMetric_eq_hyperbolic ε e he (p := (z.re, z.im))
    (by simpa only [hp] using ht hz) (by simpa only [hp] using houtside z hz),
    hyperbolicGaussianMetric_areaDensity]

/-- The actual inverse angular chart lies in its thin patch precisely
when its unchanged signed radial coordinate lies in the thin interval. -/
theorem seamAngularComplexChart_symm_mem_thinSeamCollar_iff
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {z : ℂ} (hz : z ∈ (P.seamAngularComplexChart k θ).target) :
    (P.seamAngularComplexChart k θ).symm z ∈ P.thinSeamCollar k ↔
      |z.re| < gluingThinSeamWidth C g := by
  have h := (P.mem_seamAngularComplexChart_target k θ z).mp hz
  let a : GluingSeamAngularDomain C g θ := (⟨z.re, h.1⟩, ⟨z.im, h.2⟩)
  have ha : gluingSeamAngularModel C g θ a = z := Complex.ext rfl rfl
  rw [← ha, P.seamAngularComplexChart_symm_apply]
  exact P.seamCylinderHomeomorph_mem_thinSeamCollar_iff k (Circle.exp a.2.1, a.1)

/-- On an isolated part of its genuine angular chart, the actual tensor
is the computed warped metric, including both thin-cutoff boundaries. -/
theorem gluedSmoothSeamCoordinateMetric_eq_warped_of_isolated
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (k : Fin (n - 1)) (θ : ℝ)
    {p : ℝ × ℝ} (hp : Complex.equivRealProdCLM.symm p ∈ (P.seamAngularComplexChart k θ).target)
    (hother : ∀ l : Fin (n - 1), l ≠ k →
      (P.seamAngularComplexChart k θ).symm (Complex.equivRealProdCLM.symm p) ∉
        P.thinSeamCollar l) :
    P.gluedSmoothSeamCoordinateMetric ε k θ p =
      gluingWarpedMetric (gluingCollarLocalizedSmoothWarp (gluingRadius C g) ε
        P.seamSmoothingCutoff) p := by
  ext a b
  dsimp only [gluedSmoothSeamCoordinateMetric]
  rw [P.gluedSmoothTangentInner_in_isolated_seam_chart ε k θ _
    ((P.seamAngularComplexChart k θ).map_target hp) hother,
    (P.seamAngularComplexChart k θ).right_inv hp]
  fin_cases a <;> fin_cases b <;> simp [gluingWarpedMetric]

/-- The true warped Gaussian formula agrees pointwise with the assembled
global field throughout an isolated chart, including cutoff boundaries. -/
theorem gluedChainSmoothGaussian_in_isolated_seam_chart
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 < ε)
    (k : Fin (n - 1)) (θ : ℝ) {p : ℝ × ℝ}
    (hp : Complex.equivRealProdCLM.symm p ∈ (P.seamAngularComplexChart k θ).target)
    (hother : ∀ l : Fin (n - 1), l ≠ k →
      (P.seamAngularComplexChart k θ).symm (Complex.equivRealProdCLM.symm p) ∉
        P.thinSeamCollar l) :
    P.gluedChainSmoothGaussian ε
        ((P.seamAngularComplexChart k θ).symm (Complex.equivRealProdCLM.symm p)) =
      gluingWarpedGaussianCurvature (gluingCollarLocalizedSmoothWarp (gluingRadius C g) ε
        P.seamSmoothingCutoff) p := by
  by_cases hthin : (P.seamAngularComplexChart k θ).symm (Complex.equivRealProdCLM.symm p) ∈
      P.thinSeamCollar k
  · exact P.gluedChainSmoothGaussian_in_thin_seam_chart hε k θ hp hthin
  · have hout : ∀ l : Fin (n - 1),
        (P.seamAngularComplexChart k θ).symm (Complex.equivRealProdCLM.symm p) ∉
          P.thinSeamCollar l := by
      intro l
      by_cases hl : l = k
      · simpa only [hl] using hthin
      · exact hother l hl
    have hrad : gluingThinSeamWidth C g ≤ |p.1| := by
      have h := (P.seamAngularComplexChart_symm_mem_thinSeamCollar_iff k θ hp).not.mp hthin
      simpa using le_of_not_gt h
    rw [P.gluedChainSmoothGaussian_eq_neg_one_of_outside ε hout,
      gluingCollarLocalizedGaussianCurvature_eq_neg_one_of_radius_ge P.radius_pos hε
        P.seamSmoothingCutoff p (by exact hrad)]

/-- In any isolated exterior part of a genuine seam chart, smooth area
has the native warp density, which is exactly its actual tensor determinant. -/
theorem gluedChainSmoothAreaMeasure_isolated_seam_chart_exterior_image
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 ≤ ε)
    (k : Fin (n - 1)) (θ : ℝ) {s : Set ℂ} (hs : MeasurableSet s)
    (ht : s ⊆ (P.seamAngularComplexChart k θ).target)
    (houtside : ∀ z ∈ s, ∀ l : Fin (n - 1),
      (P.seamAngularComplexChart k θ).symm z ∉ P.thinSeamCollar l) :
    P.gluedChainSmoothAreaMeasure ε ((P.seamAngularComplexChart k θ).symm '' s) =
      ∫⁻ z : ℂ in s, ENNReal.ofReal
        (Real.sqrt (P.gluedSmoothSeamCoordinateMetric ε k θ (z.re, z.im)).det) := by
  let e := P.seamAngularComplexChart k θ
  have hmeas : MeasurableSet (e.symm '' s) :=
    hs.image_of_continuousOn_injOn (e.symm.continuousOn.mono ht)
      (e.symm.injOn.mono ht)
  have hsub : e.symm '' s ⊆ (⋃ l : Fin (n - 1), P.thinSeamCollar l)ᶜ := by
    rintro q ⟨z, hz, rfl⟩ hq
    rcases mem_iUnion.mp hq with ⟨l, hl⟩
    exact houtside z hz l hl
  have h := congrArg (fun μ : Measure P.GluedCarrier => μ (e.symm '' s))
    (P.gluedChainSmoothAreaMeasure_restrict_outside_thinCollars ε)
  rw [Measure.restrict_apply hmeas, Measure.restrict_apply hmeas,
    inter_eq_left.mpr hsub] at h
  rw [h, P.gluedChainAreaMeasure_seamAngularComplexChart_image k θ hs ht,
    withDensity_apply _ hs]
  apply setLIntegral_congr_fun hs
  intro z hz
  change ENNReal.ofReal (gluingCollarWarp (gluingRadius C g) z.re) =
    ENNReal.ofReal (Real.sqrt (P.gluedSmoothSeamCoordinateMetric ε k θ (z.re, z.im)).det)
  have hcoord : Complex.equivRealProdCLM.symm (z.re, z.im) = z := Complex.ext rfl rfl
  have hrad : P.seamSmoothingCutoff.rOut ≤ |z.re| := by
    have hnot := (P.seamAngularComplexChart_symm_mem_thinSeamCollar_iff k θ (ht hz)).not.mp
      (houtside z hz k)
    exact le_of_not_gt hnot
  rw [P.gluedSmoothSeamCoordinateMetric_eq_warped_of_isolated ε k θ
    (p := (z.re, z.im)) (by simpa only [hcoord] using ht hz)
    (by simpa only [hcoord] using fun l (_ : l ≠ k) => houtside z hz l),
    gluingWarpedMetric_areaDensity (gluingCollarLocalizedSmoothWarp_pos P.radius_pos hε _ _),
    gluingCollarLocalizedSmoothWarp_eq_native _ _ _ hrad]

/-- Every measurable portion of an isolated genuine seam chart has the
determinant area of the actual smooth tensor, with no own-strip restriction.
The complement of the thin interval includes both cutoff boundaries. -/
theorem gluedChainSmoothAreaMeasure_isolated_seam_chart_image
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 ≤ ε)
    (k : Fin (n - 1)) (θ : ℝ) {s : Set ℂ} (hs : MeasurableSet s)
    (ht : s ⊆ (P.seamAngularComplexChart k θ).target)
    (hother : ∀ z ∈ s, ∀ l : Fin (n - 1), l ≠ k →
      (P.seamAngularComplexChart k θ).symm z ∉ P.thinSeamCollar l) :
    P.gluedChainSmoothAreaMeasure ε ((P.seamAngularComplexChart k θ).symm '' s) =
      ∫⁻ z : ℂ in s, ENNReal.ofReal
        (Real.sqrt (P.gluedSmoothSeamCoordinateMetric ε k θ (z.re, z.im)).det) := by
  let e := P.seamAngularComplexChart k θ
  let A : Set ℂ := {z | |z.re| < gluingThinSeamWidth C g}
  let si := s ∩ A
  let so := s \ A
  have hA : MeasurableSet A :=
    (isOpen_lt Complex.continuous_re.abs continuous_const).measurableSet
  have hi : MeasurableSet si := hs.inter hA
  have ho : MeasurableSet so := hs.diff hA
  have his : si ⊆ s := inter_subset_left
  have hos : so ⊆ s := sdiff_subset
  have hdisj : Disjoint si so := by
    exact disjoint_left.mpr fun z hz hw => hw.2 hz.2
  have hunion : si ∪ so = s := by
    exact inter_union_sdiff s A
  have himagedisj : Disjoint (e.symm '' si) (e.symm '' so) := by
    apply Set.disjoint_image_image
    intro z hz w hw heq
    have hzw := e.symm.injOn (ht (his hz)) (ht (hos hw)) heq
    exact disjoint_left.mp hdisj hz (hzw ▸ hw)
  have hmeaso : MeasurableSet (e.symm '' so) :=
    P.seamAngularComplexChart_symm_image_measurable k θ ho (hos.trans ht)
  have hinsub : si ⊆ range (gluingThinSeamAngularModel (gluingThinSeamWidth C g) θ) := by
    intro z hz
    rw [gluingThinSeamAngularModel_range]
    exact ⟨abs_lt.mp hz.2, ((P.mem_seamAngularComplexChart_target k θ z).mp
      (ht hz.1)).2⟩
  have hin := P.gluedChainSmoothAreaMeasure_thin_seam_chart_image hε k θ hi hinsub
  have hout := P.gluedChainSmoothAreaMeasure_isolated_seam_chart_exterior_image
    hε k θ ho (hos.trans ht) (by
      intro z hz l
      by_cases hl : l = k
      · subst l
        exact (P.seamAngularComplexChart_symm_mem_thinSeamCollar_iff k θ (ht hz.1)).not.mpr hz.2
      · exact hother z hz.1 l hl)
  rw [← hunion, image_union, measure_union himagedisj hmeaso,
    lintegral_union ho hdisj, hin, hout]

#print axioms seamAngularComplexChart_symm_mem_thinSeamCollar_iff
#print axioms gluedSmoothSeamCoordinateMetric_eq_warped_of_isolated
#print axioms gluedChainSmoothGaussian_in_isolated_seam_chart
#print axioms gluedChainSmoothAreaMeasure_isolated_seam_chart_exterior_image
#print axioms gluedChainSmoothAreaMeasure_isolated_seam_chart_image
#print axioms gluedChainSmoothAreaMeasure_restrict_outside_thinCollars
#print axioms gluedChainAreaMeasure_interiorComplexChart_image
#print axioms gluedChainSmoothAreaMeasure_exteriorInteriorComplexChart_image
#print axioms gluedChainSmoothAreaMeasure_exteriorInteriorComplexChart_metric_image

end

end SystolicGrowth.ExerciseGluingPreparation
