module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCurvatureBoundedConformalCharts
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

/-!
# Actual metric area in the smooth conformal charts

The existing global area measure is transported through the constructed
inverse seam coordinate. Its actual Jacobian and original warped density
multiply to the square of the same smooth conformal tensor coefficient.
-/

open Set Filter Bundle Manifold IsManifold MeasureTheory
open scoped Manifold Topology ContDiff ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** The genuine inverse-coordinate Jacobian equals the positive
conformal coefficient, not its square. -/
theorem gluedCurvatureBoundedSeamConformalInverseDerivative_det
    (P : ExerciseGluingPreparation C g n genera X) (z : ℂ) :
    LinearMap.det (P.gluedCurvatureBoundedSeamConformalInverseDerivative z).toLinearMap =
      P.gluedCurvatureBoundedSeamConformalFactor z := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, gluedCurvatureBoundedSeamConformalInverseDerivative,
    smoothWarpConformalInverseDerivative_apply, gluedCurvatureBoundedSeamConformalFactor]

/-- **Math.** Every measurable isolated seam-chart set has the actual
conformal area density `a²` for the SAME already constructed global measure. -/
theorem gluedCurvatureBoundedAreaMeasure_conformal_seam_chart_image
    (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (θ : ℝ) {s : Set ℂ} (hs : MeasurableSet s)
    (ht : s ⊆ (P.gluedCurvatureBoundedSeamConformalChart k θ).target)
    (hother : ∀ z ∈ s, ∀ l : Fin (n - 1), l ≠ k →
      (P.gluedCurvatureBoundedSeamConformalChart k θ).symm z ∉ P.thinSeamCollar l) :
    P.gluedCurvatureBoundedAreaMeasure
        ((P.gluedCurvatureBoundedSeamConformalChart k θ).symm '' s) =
      ∫⁻ z : ℂ in s, ENNReal.ofReal (P.gluedCurvatureBoundedSeamConformalFactor z ^ 2) := by
  let e := P.seamAngularComplexChart k θ
  let ψ := P.gluedCurvatureBoundedSeamConformalChange
  let D := P.gluedCurvatureBoundedSeamConformalInverseDerivative
  have hψ : s ⊆ ψ.target := fun z hz => (ht hz).1
  have hFD : ∀ z ∈ s, HasFDerivWithinAt ψ.symm (D z) s z := fun z hz =>
    (P.gluedCurvatureBoundedSeamConformalChange_symm_hasFDerivAt (hψ hz)).hasFDerivWithinAt
  have hinj : InjOn ψ.symm s := ψ.symm.injOn.mono hψ
  have hsold : MeasurableSet (ψ.symm '' s) :=
    measurable_image_of_fderivWithin hs hFD hinj
  have htold : ψ.symm '' s ⊆ e.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact (ht hz).2
  have hotherold : ∀ z ∈ ψ.symm '' s, ∀ l : Fin (n - 1), l ≠ k →
      e.symm z ∉ P.thinSeamCollar l := by
    rintro _ ⟨z, hz, rfl⟩ l hl
    exact hother z hz l hl
  have himage : e.symm '' (ψ.symm '' s) =
      (P.gluedCurvatureBoundedSeamConformalChart k θ).symm '' s := by
    rw [image_image]
    rfl
  have harea := P.gluedCurvatureBoundedAreaMeasure_isolated_seam_chart_image
    k θ hsold htold hotherold
  change P.gluedCurvatureBoundedAreaMeasure (e.symm '' (ψ.symm '' s)) = _ at harea
  rw [himage] at harea
  rw [harea, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hFD hinj]
  apply setLIntegral_congr_fun hs
  intro z hz
  have hzold : ψ.symm z ∈ e.target := (ht hz).2
  have hcoord : Complex.equivRealProdCLM.symm ((ψ.symm z).re, (ψ.symm z).im) =
      ψ.symm z := Complex.ext rfl rfl
  have hp : Complex.equivRealProdCLM.symm ((ψ.symm z).re, (ψ.symm z).im) ∈ e.target := by
    simpa only [hcoord] using hzold
  have hother' : ∀ l : Fin (n - 1), l ≠ k →
      e.symm (Complex.equivRealProdCLM.symm ((ψ.symm z).re, (ψ.symm z).im)) ∉
        P.thinSeamCollar l := by
    simpa only [hcoord] using hotherold (ψ.symm z) ⟨z, hz, rfl⟩
  change ENNReal.ofReal |LinearMap.det (D z).toLinearMap| *
      ENNReal.ofReal (Real.sqrt (P.gluedCurvatureBoundedSeamCoordinateMetric k θ
        ((ψ.symm z).re, (ψ.symm z).im)).det) = _
  rw [P.gluedCurvatureBoundedSeamCoordinateMetric_eq_warped_of_other k θ hp hother',
    gluingWarpedMetric_areaDensity (x := ((ψ.symm z).re, (ψ.symm z).im))
      (gluingCurvatureBoundedWarp_pos P.radius_pos P.thinSeamWidth_pos (ψ.symm z).re)]
  have hwarp : gluingCurvatureBoundedWarp (gluingRadius C g) (gluingThinSeamWidth C g)
      P.thinSeamWidth_pos (ψ.symm z).re = P.gluedCurvatureBoundedSeamConformalFactor z := by
    simp [ψ, gluedCurvatureBoundedSeamConformalChange, smoothWarpConformalChart_symm_apply,
      gluedCurvatureBoundedSeamConformalFactor, smoothWarpConformalFactor,
      gluedCurvatureBoundedConformalWarp]
  rw [hwarp, P.gluedCurvatureBoundedSeamConformalInverseDerivative_det,
    abs_of_pos (P.gluedCurvatureBoundedSeamConformalFactor_pos z),
    ← ENNReal.ofReal_mul (P.gluedCurvatureBoundedSeamConformalFactor_pos z).le]
  simp only [pow_two]

/-- **Math.** The unchanged original interior chart has the square of its
same Poincaré conformal coefficient as its actual global area density. -/
theorem gluedCurvatureBoundedAreaMeasure_conformal_interior_chart_image
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    {s : Set ℂ} (hs : MeasurableSet s) (ht : s ⊆ e.target)
    (houtside : ∀ z ∈ s, ∀ k : Fin (n - 1), e.symm z ∉ P.thinSeamCollar k) :
    P.gluedCurvatureBoundedAreaMeasure (e.symm '' s) =
      ∫⁻ z : ℂ in s, ENNReal.ofReal (z.im⁻¹ ^ 2) := by
  rw [P.gluedCurvatureBoundedAreaMeasure_exteriorInteriorComplexChart_image e he hs ht houtside]
  apply setLIntegral_congr_fun hs
  intro z hz
  have hcoord : Complex.equivRealProdCLM.symm (z.re, z.im) = z := Complex.ext rfl rfl
  have hp : Complex.equivRealProdCLM.symm (z.re, z.im) ∈ e.target := by
    simpa only [hcoord] using ht hz
  have houtside' : ∀ k : Fin (n - 1),
      e.symm (Complex.equivRealProdCLM.symm (z.re, z.im)) ∉ P.thinSeamCollar k := by
    simpa only [hcoord] using houtside z hz
  dsimp only
  rw [P.gluedCurvatureBoundedInteriorCoordinateMetric_eq_hyperbolic e he hp houtside',
    hyperbolicGaussianMetric_areaDensity, inv_pow]

/-- **Math.** Around every point, ONE smooth chart in the original maximal
atlas simultaneously gives the conformal tensor of the existing metric and
the square-factor density of its existing global area measure. -/
theorem exists_gluedCurvatureBounded_conformal_metric_area_chart
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier) :
    ∃ (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
      (ψ : OpenPartialHomeomorph ℂ ℂ) (a : ℂ → ℝ) (D : ℂ → ℂ →L[ℝ] ℂ)
      (U : Set P.GluedCarrier),
      b ∈ U ∧ IsOpen U ∧ U ⊆ (e.trans ψ).source ∧
      ψ.source = univ ∧ ContDiff ℝ ∞ (ψ : ℂ → ℂ) ∧
      e.trans ψ ∈ maximalAtlas (modelWithCornersSelf ℝ ℂ) ∞ P.GluedCarrier ∧
      ContDiffOn ℝ ∞ a (e.trans ψ).target ∧
      (∀ z ∈ (e.trans ψ).target, 0 < a z) ∧
      (∀ z ∈ ψ.target, HasFDerivAt ψ.symm (D z) z) ∧
      (∀ c ∈ U, ∀ v w : ℂ,
        P.gluedCurvatureBoundedSmoothRiemannianMetric.inner c
          (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
            (⟨e, he⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ c (D ((e.trans ψ) c) v))
          (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
            (⟨e, he⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ c (D ((e.trans ψ) c) w)) =
          a ((e.trans ψ) c) ^ 2 * (v.re * w.re + v.im * w.im)) ∧
      ∀ s : Set ℂ, MeasurableSet s → s ⊆ (e.trans ψ) '' U →
        P.gluedCurvatureBoundedAreaMeasure ((e.trans ψ).symm '' s) =
          ∫⁻ z : ℂ in s, ENNReal.ofReal (a z ^ 2) := by
  classical
  by_cases hc : ∃ k : Fin (n - 1), b ∈ P.closedThinSeamCollar k
  · obtain ⟨k, hk⟩ := hc
    have hb := P.closedThinSeamCollar_subset_original_collar k hk
    let θ := P.seamSmoothingAngle k ⟨b, hb⟩
    have hs : b ∈ (P.seamAngularComplexChart k θ).source :=
      P.mem_seamSmoothingAngle_chart k ⟨b, hb⟩
    have hother : ∀ᶠ c in 𝓝 b, ∀ l : Fin (n - 1), l ≠ k → c ∉ P.thinSeamCollar l := by
      rw [Filter.eventually_all]
      intro l
      by_cases hl : l = k
      · exact Filter.Eventually.of_forall (fun _ h => (h hl).elim)
      · have hn : b ∉ P.closedThinSeamCollar l := fun h =>
          Set.disjoint_left.mp (P.closedThinSeamCollar_disjoint hl) h hk
        filter_upwards [(P.closedThinSeamCollar_isCompact l).isClosed.isOpen_compl.mem_nhds hn]
          with c hcl _ hthin
        exact hcl (P.thinSeamCollar_subset_closedThinSeamCollar l hthin)
    have hnear : ∀ᶠ c in 𝓝 b, c ∈ (P.seamAngularComplexChart k θ).source ∧
        ∀ l : Fin (n - 1), l ≠ k → c ∉ P.thinSeamCollar l := by
      filter_upwards [(P.seamAngularComplexChart k θ).open_source.mem_nhds hs, hother]
        with c hcs hco
      exact ⟨hcs, hco⟩
    obtain ⟨U, hUsub, hU, hbU⟩ := mem_nhds_iff.mp hnear
    have hUsource : U ⊆ (P.gluedCurvatureBoundedSeamConformalChart k θ).source := by
      intro c hc
      simpa using (hUsub hc).1
    refine ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩,
      P.gluedCurvatureBoundedSeamConformalChange, P.gluedCurvatureBoundedSeamConformalFactor,
      P.gluedCurvatureBoundedSeamConformalInverseDerivative, U, hbU, hU, hUsource,
      P.gluedCurvatureBoundedSeamConformalChange_source,
      P.gluedCurvatureBoundedSeamConformalChange_contDiff,
      P.gluedCurvatureBoundedSeamConformalChart_mem_maximalAtlas k θ,
      P.gluedCurvatureBoundedSeamConformalFactor_contDiffOn.mono (fun _ hz => hz.1),
      fun z _ => P.gluedCurvatureBoundedSeamConformalFactor_pos z,
      fun z hz => P.gluedCurvatureBoundedSeamConformalChange_symm_hasFDerivAt hz,
      fun c hc v w => P.gluedCurvatureBoundedSmoothMetric_in_conformal_seam_chart
        k θ c (hUsub hc).1 (hUsub hc).2 v w, ?_⟩
    intro s hsm hsub
    apply P.gluedCurvatureBoundedAreaMeasure_conformal_seam_chart_image k θ hsm
    · rintro z hz
      obtain ⟨c, hc, rfl⟩ := hsub hz
      exact (P.gluedCurvatureBoundedSeamConformalChart k θ).map_source (hUsource hc)
    · intro z hz l hl
      obtain ⟨c, hc, rfl⟩ := hsub hz
      change (P.gluedCurvatureBoundedSeamConformalChart k θ).symm
        (P.gluedCurvatureBoundedSeamConformalChart k θ c) ∉ P.thinSeamCollar l
      rw [(P.gluedCurvatureBoundedSeamConformalChart k θ).left_inv (hUsource hc)]
      exact (hUsub hc).2 l hl
  · have hn : ∀ k : Fin (n - 1), b ∉ P.closedThinSeamCollar k := by
      simpa only [not_exists] using hc
    obtain ⟨e, he, hs⟩ := P.exists_interior_chart_of_outside_closedThinSeamCollars b hn
    have hout : ∀ᶠ c in 𝓝 b, ∀ k : Fin (n - 1), c ∉ P.thinSeamCollar k := by
      rw [Filter.eventually_all]
      intro k
      filter_upwards [(P.closedThinSeamCollar_isCompact k).isClosed.isOpen_compl.mem_nhds (hn k)]
        with c hck hthin
      exact hck (P.thinSeamCollar_subset_closedThinSeamCollar k hthin)
    have hnear : ∀ᶠ c in 𝓝 b, c ∈ e.source ∧
        ∀ k : Fin (n - 1), c ∉ P.thinSeamCollar k := by
      filter_upwards [e.open_source.mem_nhds hs, hout] with c hcs hco
      exact ⟨hcs, hco⟩
    obtain ⟨U, hUsub, hU, hbU⟩ := mem_nhds_iff.mp hnear
    have hUsource : U ⊆ e.source := fun c hc => (hUsub hc).1
    refine ⟨e, Or.inl he, OpenPartialHomeomorph.refl ℂ, fun z => z.im⁻¹,
      fun _ => ContinuousLinearMap.id ℝ ℂ, U, hbU, hU, ?_, rfl, contDiff_id,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using hUsource
    · have heMax : e ∈ maximalAtlas (modelWithCornersSelf ℝ ℂ) ∞ P.GluedCarrier :=
        subset_maximalAtlas (I := modelWithCornersSelf ℝ ℂ) (n := ∞)
          (show e ∈ atlas ℂ P.GluedCarrier from Or.inl he)
      simpa using heMax
    · simp only [OpenPartialHomeomorph.trans_refl]
      convert! Complex.imCLM.contDiff.contDiffOn.inv
        (fun z hz => (P.gluedInteriorComplexChart_target_im_pos e he hz).ne') using 1
    · intro z hz
      exact inv_pos.mpr (P.gluedInteriorComplexChart_target_im_pos e he (by simpa using hz))
    · intro z _
      exact hasFDerivAt_id z
    · intro c hc v w
      simpa using P.gluedCurvatureBoundedSmoothMetric_in_conformal_interior_chart
        e he c (hUsub hc).1 (hUsub hc).2 v w
    · simp only [OpenPartialHomeomorph.trans_refl]
      intro s hsm hsub
      apply P.gluedCurvatureBoundedAreaMeasure_conformal_interior_chart_image e he hsm
      · rintro z hz
        obtain ⟨c, hc, rfl⟩ := hsub hz
        exact e.map_source (hUsource hc)
      · intro z hz k
        obtain ⟨c, hc, rfl⟩ := hsub hz
        rw [e.left_inv (hUsource hc)]
        exact (hUsub hc).2 k

#print axioms gluedCurvatureBoundedSeamConformalInverseDerivative_det
#print axioms gluedCurvatureBoundedAreaMeasure_conformal_seam_chart_image
#print axioms gluedCurvatureBoundedAreaMeasure_conformal_interior_chart_image
#print axioms exists_gluedCurvatureBounded_conformal_metric_area_chart

end

end SystolicGrowth.ExerciseGluingPreparation
