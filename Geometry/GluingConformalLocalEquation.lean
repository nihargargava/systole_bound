module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingConformalWeakPDE
public import Geometry.ConformalGradientLocalH1

@[expose] public section

/-!
# A common local weak equation for the actual solution and its forcing

The same nonvanishing partition weight supplies local weak derivatives for
every graph element. In particular the constructed solution and its actual
nonlinear forcing have `H¹` representatives in common coordinates. This is
the input to the first two local Fourier elliptic gains.
-/

open Set Filter Manifold IsManifold MeasureTheory Riemannian
open scoped ContDiff Manifold RealInnerProductSpace

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** A common actual coordinate neighborhood supplies local
weak derivatives for every graph element, hence simultaneously for the
solution and the nonlinear forcing. The neighborhood is constructed
solely from the original finite square partition. -/
theorem gluedConformalGradient_common_coordinates
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier) :
    let A := P.gluedConformalGradientAtlas
    let μ := P.gluedCurvatureBoundedAreaMeasure
    ∃ (i : Fin P.gluedConformalGradientData.size) (V : Set ℂ),
      let Q := P.gluedConformalPatch (P.gluedConformalGradientData.center i)
      IsOpen V ∧ b ∈ Q.region ∧ A.chart i b ∈ V ∧ V ⊆ A.chart i '' Q.region ∧
      ∀ w : ConformalGradientH1 μ A,
        (∀ K : Set ℂ, IsCompact K → K ⊆ V →
          MemLp (fun z => (conformalH1Value μ A w) ((A.chart i).symm z)) 2
            (volume.restrict K) ∧
          ∀ j : Fin 2, MemLp (fun z =>
            A.coefficient i z / A.weight i ((A.chart i).symm z) *
              (conformalH1Gradient μ A w (i, j)) ((A.chart i).symm z)) 2
            (volume.restrict K)) ∧
        (∀ (j : Fin 2) (η : ℂ → ℝ), ContDiff ℝ ∞ η → HasCompactSupport η →
          tsupport η ⊆ V →
          (∫ z : ℂ, (A.coefficient i z / A.weight i ((A.chart i).symm z) *
            (conformalH1Gradient μ A w (i, j)) ((A.chart i).symm z)) * η z) =
            -(∫ z : ℂ, (conformalH1Value μ A w) ((A.chart i).symm z) *
              fderiv ℝ η z (if j = 0 then 1 else Complex.I))) := by
  let D := P.gluedConformalGradientData
  let A := P.gluedConformalGradientAtlas
  let U : Fin D.size → Set P.GluedCarrier :=
    fun i => (P.gluedConformalPatch (D.center i)).region
  have hU : ∀ i, IsOpen (U i) := fun i =>
    (P.gluedConformalPatch (D.center i)).region_open
  have hUs : ∀ i, U i ⊆ (A.chart i).source := fun i =>
    (P.gluedConformalPatch (D.center i)).region_subset
  have hτ : ∀ i, tsupport (A.weight i) ⊆ U i := D.weight_support
  have harea : ∀ i (s : Set ℂ), MeasurableSet s → s ⊆ A.chart i '' U i →
      P.gluedCurvatureBoundedAreaMeasure ((A.chart i).symm '' s) =
        ∫⁻ z : ℂ in s, ENNReal.ofReal (A.coefficient i z ^ 2) :=
    fun i => (P.gluedConformalPatch (D.center i)).area_eq
  obtain ⟨i, V, hV, hbU, hbV, hVU, hτnz⟩ :=
    A.exists_nonvanishing_chart_neighborhood U hU hUs hτ b
  refine ⟨i, V, hV, hbU, hbV, hVU, fun w => ⟨?_, ?_⟩⟩
  · intro K hK hKV
    exact conformalH1Coordinate_memLp_on_isCompact P.gluedCurvatureBoundedAreaMeasure
      A i (U i) (hUs i) (harea i) K hK (hKV.trans hVU)
      (fun z hz => hτnz z (hKV hz)) w
  · intro j η hη hηc hηV
    exact conformalH1Gradient_coordinate_weakDerivative P.gluedCurvatureBoundedAreaMeasure
      A i j (U i) (hU i) (hUs i) (hτ i) (harea i) V hV hVU hτnz
      η hη hηc hηV w

/-- **Math.** The actual nonlinear equation can be written using an
actual graph forcing, so both sides have the common local `H¹` witnesses
above. Its `L²` value remains exactly `K + Ψ_B(u)`. -/
theorem exists_gluedConformal_solution_forcing_graph
    (P : ExerciseGluingPreparation C g n genera X) :
    ∃ (B : ℝ) (hB : 1 < B),
      (∀ b, P.gluedCurvatureBoundedGaussian b ∈ Icc (-B) (-1 : ℝ)) ∧
      ∃ v F : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas,
        conformalH1Value _ _ F = P.gluedConformalGaussianL2 +
          conformalCurvatureNonlinearityLp P.gluedCurvatureBoundedAreaMeasure B hB
            (conformalH1Value _ _ v) ∧
        ∀ w : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas,
          inner ℝ (conformalH1Gradient _ _ v) (conformalH1Gradient _ _ w) =
            -inner ℝ (conformalH1Value _ _ F) (conformalH1Value _ _ w) := by
  obtain ⟨B, hB, hK, v, hv⟩ := P.exists_gluedConformalGradient_solution
  obtain ⟨F, hF⟩ := P.exists_gluedConformal_forcing_graph B hB v
  refine ⟨B, hB, hK, v, F, hF, ?_⟩
  intro w
  rw [hF]
  exact hv w

/-- **Math.** The local scalar equation has the actual graph forcing
as its representative. This form directly feeds local Sobolev gain,
without first transferring an a.e. nonlinear identity between charts. -/
theorem gluedConformalGradient_forcing_weak_laplacian
    (P : ExerciseGluingPreparation C g n genera X)
    (v F : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas)
    (hweak : ∀ w : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas,
      inner ℝ (conformalH1Gradient _ _ v) (conformalH1Gradient _ _ w) =
        -inner ℝ (conformalH1Value _ _ F) (conformalH1Value _ _ w))
    (Q : GluedConformalPatch P)
    (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηsub : tsupport η ⊆ (Q.original.trans Q.change) '' Q.region) :
    let e := Q.original.trans Q.change
    let A := P.gluedConformalGradientAtlas
    let μ := P.gluedCurvatureBoundedAreaMeasure
    (∫ z : ℂ, (conformalH1Value μ A v) (e.symm z) * Laplacian.laplacian η z) =
      ∫ z : ℂ, Q.coefficient z ^ 2 * ((conformalH1Value μ A F) (e.symm z) * η z) := by
  let μ := P.gluedCurvatureBoundedAreaMeasure
  let A := P.gluedConformalGradientAtlas
  have henergy (f h : C^∞⟮𝓘(ℝ, ℂ), P.GluedCarrier; ℝ⟯) :
      inner ℝ (conformalSmoothGradient μ A f) (conformalSmoothGradient μ A h) =
        ∫ x, smoothDirichletDensity P.gluedCurvatureBoundedSmoothRiemannianMetric f h x ∂μ := by
    rw [conformalSmoothGradient_inner_eq_integral_components]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (P.gluedConformalGradient_sum_pair_eq f h)
  exact conformalH1Gradient_weak_laplacian μ A P.gluedCurvatureBoundedSmoothRiemannianMetric
    henergy (Q.original.trans Q.change) Q.chart_mem Q.region Q.region_open Q.region_subset
    Q.coefficient Q.coefficient_smooth Q.coefficient_pos
    (fun b hb => Q.metric_in_inverseTangent P b hb (Q.region_subset hb)) Q.area_eq v
    (conformalH1Value μ A F) (conformalH1Value μ A F) Filter.EventuallyEq.rfl
    hweak η hη hηc hηsub

#print axioms gluedConformalGradient_common_coordinates
#print axioms exists_gluedConformal_solution_forcing_graph
#print axioms gluedConformalGradient_forcing_weak_laplacian

end

end SystolicGrowth.ExerciseGluingPreparation
