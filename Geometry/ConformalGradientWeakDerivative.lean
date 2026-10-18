module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ConformalGradientGraph
public import Geometry.ConformalChartAdjointTests

@[expose] public section

/-!
# Genuine weak derivatives in the completed conformal gradient graph

The explicit compact-chart integration-by-parts identity is a continuous
`L²` pairing. It therefore survives closure of the actual smooth gradient
graph. No distributional-derivative premise is imposed on graph elements.
-/

open Set Filter Manifold IsManifold MeasureTheory
open scoped ContDiff RealInnerProductSpace

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  (μ : Measure M) [IsFiniteMeasure μ]

/-- **Math.** Pairing an actual `L²` function with a smooth function is
the ordinary integral of the chosen representative against that function. -/
theorem L2_inner_smoothFunctionToL2
    (u : Lp ℝ 2 μ) (f : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) :
    inner ℝ u (smoothFunctionToL2 μ f) = ∫ x, u x * f x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [smoothFunctionToL2_coeFn μ f] with x hx
  simp only [Real.inner_apply, hx]

/-- **Math.** Smooth `L²` pairings use the original pointwise functions. -/
theorem smoothFunctionToL2_inner
    (f g : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) :
    inner ℝ (smoothFunctionToL2 μ f) (smoothFunctionToL2 μ g) =
      ∫ x, f x * g x ∂μ := by
  rw [L2_inner_smoothFunctionToL2]
  apply integral_congr_ae
  filter_upwards [smoothFunctionToL2_coeFn μ f] with x hx
  simp only [hx]

variable [T2Space M] {ι : Type*} [Fintype ι]

/-- **Math.** Every completed graph component satisfies the exact
distributional identity of the literal weighted coordinate derivative.
The adjoint is an explicitly differentiated, smooth, compact chart test. -/
theorem conformalH1Gradient_integral_adjoint
    (A : ConformalGradientAtlas M ι) (i : ι) (j : Fin 2)
    (U : Set M) (hU : IsOpen U) (hUs : U ⊆ (A.chart i).source)
    (hτ : tsupport (A.weight i) ⊆ U)
    (harea : ∀ s : Set ℂ, MeasurableSet s → s ⊆ A.chart i '' U →
      μ ((A.chart i).symm '' s) =
        ∫⁻ z : ℂ in s, ENNReal.ofReal (A.coefficient i z ^ 2))
    (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηsub : tsupport η ⊆ A.chart i '' U)
    (u : ConformalGradientH1 μ A) :
    (∫ x, (conformalH1Gradient μ A u (i, j)) x *
      conformalChartTestPullback (A.chart i) η x ∂μ) =
      -(∫ x, (conformalH1Value μ A u) x *
        conformalChartTestPullback (A.chart i)
          (weightedChartAdjointCoordinate (A.chart i) (A.coefficient i) (A.weight i)
            (if j = 0 then 1 else Complex.I) η) x ∂μ) := by
  let e := A.chart i
  let a := A.coefficient i
  let τ := A.weight i
  let v : ℂ := if j = 0 then 1 else Complex.I
  have hηt : tsupport η ⊆ e.target := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hηsub hz
    exact e.map_source (hUs hx)
  let T : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯ :=
    ⟨conformalChartTestPullback e η,
      conformalChartTestPullback_contMDiff e (A.chart_mem i) η hη hηc hηt⟩
  let Q : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯ :=
    ⟨conformalChartTestPullback e (weightedChartAdjointCoordinate e a τ v η),
      weightedChartAdjointTest_contMDiff e (A.chart_mem i) a
        (A.coefficient_smooth i) (A.coefficient_pos i) τ v η hη hηc hηt⟩
  let t := smoothFunctionToL2 μ T
  let q := smoothFunctionToL2 μ Q
  have hsmooth : ∀ f : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯,
      inner ℝ (conformalGradientComponent μ A i j f) t =
        -inner ℝ (smoothFunctionToL2 μ f) q := by
    intro f
    rw [show t = smoothFunctionToL2 μ T from rfl,
      show q = smoothFunctionToL2 μ Q from rfl,
      L2_inner_smoothFunctionToL2, smoothFunctionToL2_inner]
    have hpair := weightedChartDerivative_integral_adjoint μ e (A.chart_mem i)
      U hU hUs a (A.coefficient_smooth i) (A.coefficient_pos i) harea
      τ hτ f v η hη hηc hηsub
    apply Eq.trans ?_ hpair
    apply integral_congr_ae
    filter_upwards [conformalGradientComponent_coeFn μ A f i j] with x hx
    rw [hx]
    rfl
  have hlinear : ∀ f : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯,
      (-(innerSL ℝ q)) (smoothFunctionToL2 μ f) =
        ((innerSL ℝ t).comp
          (PiLp.proj 2 (fun _ : ι × Fin 2 => Lp ℝ 2 μ) (i, j)))
          (conformalSmoothGradient μ A f) := by
    intro f
    change -inner ℝ q (smoothFunctionToL2 μ f) =
      inner ℝ t (conformalGradientComponent μ A i j f)
    rw [real_inner_comm (smoothFunctionToL2 μ f) q,
      real_inner_comm (conformalGradientComponent μ A i j f) t]
    exact (hsmooth f).symm
  have hc := closedGradientGraph_weak_identity (smoothFunctionToL2 μ)
    (conformalSmoothGradient μ A) (-(innerSL ℝ q))
    ((innerSL ℝ t).comp
      (PiLp.proj 2 (fun _ : ι × Fin 2 => Lp ℝ 2 μ) (i, j))) hlinear u
  change -inner ℝ q (conformalH1Value μ A u) =
    inner ℝ t (conformalH1Gradient μ A u (i, j)) at hc
  rw [real_inner_comm (conformalH1Value μ A u) q,
    real_inner_comm (conformalH1Gradient μ A u (i, j)) t] at hc
  rw [show q = smoothFunctionToL2 μ Q from rfl,
    show t = smoothFunctionToL2 μ T from rfl,
    L2_inner_smoothFunctionToL2, L2_inner_smoothFunctionToL2] at hc
  exact hc.symm

/-- **Math.** The completed component has the literal coordinate weak
derivative identity, with the original area density `a²` on the left and
the differentiated coefficient `τ a` on the right. -/
theorem conformalH1Gradient_coordinate_integral_adjoint
    (A : ConformalGradientAtlas M ι) (i : ι) (j : Fin 2)
    (U : Set M) (hU : IsOpen U) (hUs : U ⊆ (A.chart i).source)
    (hτ : tsupport (A.weight i) ⊆ U)
    (harea : ∀ s : Set ℂ, MeasurableSet s → s ⊆ A.chart i '' U →
      μ ((A.chart i).symm '' s) =
        ∫⁻ z : ℂ in s, ENNReal.ofReal (A.coefficient i z ^ 2))
    (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηsub : tsupport η ⊆ A.chart i '' U)
    (u : ConformalGradientH1 μ A) :
    (∫ z : ℂ, A.coefficient i z ^ 2 *
      ((conformalH1Gradient μ A u (i, j)) ((A.chart i).symm z) * η z)) =
      -(∫ z : ℂ, (conformalH1Value μ A u) ((A.chart i).symm z) *
        fderiv ℝ (fun w => A.weight i ((A.chart i).symm w) * A.coefficient i w * η w)
          z (if j = 0 then 1 else Complex.I)) := by
  have hΩt : A.chart i '' U ⊆ (A.chart i).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (A.chart i).map_source (hUs hx)
  have h := conformalH1Gradient_integral_adjoint μ A i j U hU hUs hτ harea
    η hη hηc hηsub u
  rw [conformalChartTestPullback_integral μ (A.chart i) U hU hUs
    (A.coefficient i) (A.coefficient_smooth i).continuousOn harea η hηsub] at h
  rw [conformalChartTestPullback_integral μ (A.chart i) U hU hUs
    (A.coefficient i) (A.coefficient_smooth i).continuousOn harea _
    ((weightedChartAdjointCoordinate_tsupport_subset _ _ _ _ _).trans hηsub)] at h
  apply h.trans
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    dsimp only [weightedChartAdjointCoordinate]
    by_cases hzt : z ∈ (A.chart i).target
    · field_simp [(A.coefficient_pos i z hzt).ne']
    · have hd : fderiv ℝ
          (fun w => A.weight i ((A.chart i).symm w) * A.coefficient i w * η w)
          z (if j = 0 then 1 else Complex.I) = 0 := by
        apply image_eq_zero_of_notMem_tsupport (f := fun z => fderiv ℝ
          (fun w => A.weight i ((A.chart i).symm w) * A.coefficient i w * η w)
          z (if j = 0 then 1 else Complex.I))
        intro hz
        exact hzt (hΩt (hηsub (tsupport_mul_subset_right
          (tsupport_fderiv_apply_subset ℝ _ hz))))
      simp [hd])

/-- **Math.** On every open coordinate region where the partition weight
does not vanish, the function component has actual distributional partial
derivative `a / τ` times the completed gradient component. -/
theorem conformalH1Gradient_coordinate_weakDerivative
    (A : ConformalGradientAtlas M ι) (i : ι) (j : Fin 2)
    (U : Set M) (hU : IsOpen U) (hUs : U ⊆ (A.chart i).source)
    (hτ : tsupport (A.weight i) ⊆ U)
    (harea : ∀ s : Set ℂ, MeasurableSet s → s ⊆ A.chart i '' U →
      μ ((A.chart i).symm '' s) =
        ∫⁻ z : ℂ in s, ENNReal.ofReal (A.coefficient i z ^ 2))
    (V : Set ℂ) (hV : IsOpen V) (hVU : V ⊆ A.chart i '' U)
    (hτnz : ∀ z ∈ V, A.weight i ((A.chart i).symm z) ≠ 0)
    (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηV : tsupport η ⊆ V)
    (u : ConformalGradientH1 μ A) :
    (∫ z : ℂ, (A.coefficient i z / A.weight i ((A.chart i).symm z) *
      (conformalH1Gradient μ A u (i, j)) ((A.chart i).symm z)) * η z) =
      -(∫ z : ℂ, (conformalH1Value μ A u) ((A.chart i).symm z) *
        fderiv ℝ η z (if j = 0 then 1 else Complex.I)) := by
  let e := A.chart i
  let a := A.coefficient i
  let τ := A.weight i
  have hVt : V ⊆ e.target := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hVU hz
    exact e.map_source (hUs hx)
  let ξ : ℂ → ℝ := fun z => (τ (e.symm z) * a z)⁻¹ * η z
  have hξ : ContDiff ℝ ∞ ξ := contDiff_coordinate_mul_supported hV
    ((((smoothFunction_contDiffOn_chart_inverse e (A.chart_mem i) τ).mul
      (A.coefficient_smooth i)).mono hVt).inv
        (fun z hz => mul_ne_zero (hτnz z hz) (A.coefficient_pos i z (hVt hz)).ne'))
    hη hηV
  have hξc : HasCompactSupport ξ := hηc.mul_left
  have hξU : tsupport ξ ⊆ e '' U := tsupport_mul_subset_right.trans (hηV.trans hVU)
  have hcancel : (fun z => τ (e.symm z) * a z * ξ z) = η := by
    funext z
    by_cases hz : η z = 0
    · simp [ξ, hz]
    · have hzV : z ∈ V := hηV (subset_closure hz)
      dsimp only [ξ]
      have hτz : τ (e.symm z) ≠ 0 := hτnz z hzV
      have haz : a z ≠ 0 := (A.coefficient_pos i z (hVt hzV)).ne'
      field_simp [hτz, haz]
  have h := conformalH1Gradient_coordinate_integral_adjoint μ A i j U hU hUs
    hτ harea ξ hξ hξc hξU u
  change (∫ z : ℂ, a z ^ 2 *
      ((conformalH1Gradient μ A u (i, j)) (e.symm z) * ξ z)) =
    -(∫ z : ℂ, (conformalH1Value μ A u) (e.symm z) *
      fderiv ℝ (fun w => τ (e.symm w) * a w * ξ w) z
        (if j = 0 then 1 else Complex.I)) at h
  rw [hcancel] at h
  apply Eq.trans ?_ h
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    change (a z / τ (e.symm z) *
      (conformalH1Gradient μ A u (i, j)) (e.symm z)) * η z =
        a z ^ 2 * ((conformalH1Gradient μ A u (i, j)) (e.symm z) *
          ((τ (e.symm z) * a z)⁻¹ * η z))
    by_cases hz : η z = 0
    · simp [hz]
    · have hzV : z ∈ V := hηV (subset_closure hz)
      have hτz : τ (e.symm z) ≠ 0 := hτnz z hzV
      have haz : a z ≠ 0 := (A.coefficient_pos i z (hVt hzV)).ne'
      field_simp [hτz, haz])

#print axioms L2_inner_smoothFunctionToL2
#print axioms conformalH1Gradient_integral_adjoint
#print axioms conformalH1Gradient_coordinate_integral_adjoint
#print axioms conformalH1Gradient_coordinate_weakDerivative

end

end SystolicGrowth
