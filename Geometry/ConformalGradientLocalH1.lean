module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ConformalGradientWeakDerivative
public import Geometry.ConformalChartLocalL2
public import Geometry.GluingConformalGradientGraph

@[expose] public section

/-!
# Actual local `H¹` representatives of the glued gradient graph

The finite square partition gives a nonvanishing weight near each point.
On that genuine chart neighborhood the actual graph value and its explicit
weak derivatives belong to Euclidean `L²` on compact subsets. The closing
theorem applies to the original glued carrier and its constructed area
measure, without a local Sobolev-space premise.
-/

open Set Filter Manifold IsManifold MeasureTheory
open scoped ContDiff Topology ENNReal RealInnerProductSpace

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

section Cover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  {ι : Type*} [Fintype ι]

/-- **Math.** A square partition supplies genuine chart neighborhoods
covering the carrier on which one weight can be inverted. -/
theorem ConformalGradientAtlas.exists_nonvanishing_chart_neighborhood
    (A : ConformalGradientAtlas M ι)
    (U : ι → Set M) (hU : ∀ i, IsOpen (U i))
    (hUs : ∀ i, U i ⊆ (A.chart i).source)
    (hτ : ∀ i, tsupport (A.weight i) ⊆ U i) (x : M) :
    ∃ (i : ι) (V : Set ℂ), IsOpen V ∧ x ∈ U i ∧ A.chart i x ∈ V ∧
      V ⊆ A.chart i '' U i ∧
      ∀ z ∈ V, A.weight i ((A.chart i).symm z) ≠ 0 := by
  classical
  have hex : ∃ i, A.weight i x ≠ 0 := by
    by_contra hn
    have hall : ∀ i, A.weight i x = 0 := by simpa only [not_exists, not_not] using hn
    have hs := A.weight_sum_sq x
    simp [hall] at hs
  obtain ⟨i, hi⟩ := hex
  let W : Set M := U i ∩ {y | A.weight i y ≠ 0}
  have hW : IsOpen W := (hU i).inter
    ((isOpen_ne : IsOpen {r : ℝ | r ≠ 0}).preimage (A.weight i).contMDiff.continuous)
  have hWs : W ⊆ (A.chart i).source := fun y hy => hUs i hy.1
  have hxU : x ∈ U i := hτ i (subset_closure hi)
  refine ⟨i, A.chart i '' W, (A.chart i).isOpen_image_of_subset_source hW hWs,
    hxU, ⟨x, ⟨hxU, hi⟩, rfl⟩, image_mono (inter_subset_left), ?_⟩
  rintro z ⟨y, hy, rfl⟩
  rw [(A.chart i).left_inv (hWs hy)]
  exact hy.2

end Cover

section LocalL2

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [T2Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {ι : Type*} [Fintype ι]
  (μ : Measure M) [IsFiniteMeasure μ]

/-- **Math.** Both the value and the explicitly unweighted graph
derivatives are ordinary Euclidean `L²` on each compact chart subset. -/
theorem conformalH1Coordinate_memLp_on_isCompact
    (A : ConformalGradientAtlas M ι) (i : ι)
    (U : Set M) (hUs : U ⊆ (A.chart i).source)
    (harea : ∀ s : Set ℂ, MeasurableSet s → s ⊆ A.chart i '' U →
      μ ((A.chart i).symm '' s) =
        ∫⁻ z : ℂ in s, ENNReal.ofReal (A.coefficient i z ^ 2))
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ A.chart i '' U)
    (hτnz : ∀ z ∈ K, A.weight i ((A.chart i).symm z) ≠ 0)
    (u : ConformalGradientH1 μ A) :
    MemLp (fun z => (conformalH1Value μ A u) ((A.chart i).symm z)) 2
        (volume.restrict K) ∧
      ∀ j : Fin 2, MemLp (fun z =>
        A.coefficient i z / A.weight i ((A.chart i).symm z) *
          (conformalH1Gradient μ A u (i, j)) ((A.chart i).symm z)) 2
        (volume.restrict K) := by
  have hKt : K ⊆ (A.chart i).target := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hKU hz
    exact (A.chart i).map_source (hUs hx)
  constructor
  · exact conformalChart_memLp_on_isCompact μ (A.chart i) U hUs
      (A.coefficient i) (A.coefficient_smooth i).continuousOn (A.coefficient_pos i)
      harea (Lp.memLp (conformalH1Value μ A u)) K hK hKU
  · intro j
    apply conformalChart_memLp_on_isCompact_mul μ (A.chart i) U hUs
      (A.coefficient i) (A.coefficient_smooth i).continuousOn (A.coefficient_pos i)
      harea (Lp.memLp (conformalH1Gradient μ A u (i, j))) K hK hKU
    exact ((A.coefficient_smooth i).continuousOn.mono hKt).div
      ((smoothFunction_contDiffOn_chart_inverse (A.chart i) (A.chart_mem i)
        (A.weight i)).continuousOn.mono hKt) hτnz

end LocalL2

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** Every element of the actual glued surface's completed
gradient graph has genuine local `H¹` coordinate representatives around
every carrier point, for the original area measure and smooth structure. -/
theorem gluedConformalH1_has_local_weak_derivatives
    (P : ExerciseGluingPreparation C g n genera X)
    (u : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure
      P.gluedConformalGradientAtlas) (b : P.GluedCarrier) :
    let A := P.gluedConformalGradientAtlas
    let μ := P.gluedCurvatureBoundedAreaMeasure
    ∃ (i : Fin P.gluedConformalGradientData.size) (V : Set ℂ),
      IsOpen V ∧ b ∈ (A.chart i).source ∧ A.chart i b ∈ V ∧ V ⊆ (A.chart i).target ∧
      (∀ K : Set ℂ, IsCompact K → K ⊆ V →
        MemLp (fun z => (conformalH1Value μ A u) ((A.chart i).symm z)) 2
          (volume.restrict K) ∧
        ∀ j : Fin 2, MemLp (fun z =>
          A.coefficient i z / A.weight i ((A.chart i).symm z) *
            (conformalH1Gradient μ A u (i, j)) ((A.chart i).symm z)) 2
          (volume.restrict K)) ∧
      (∀ (j : Fin 2) (η : ℂ → ℝ), ContDiff ℝ ∞ η → HasCompactSupport η →
        tsupport η ⊆ V →
        (∫ z : ℂ, (A.coefficient i z / A.weight i ((A.chart i).symm z) *
          (conformalH1Gradient μ A u (i, j)) ((A.chart i).symm z)) * η z) =
        -(∫ z : ℂ, (conformalH1Value μ A u) ((A.chart i).symm z) *
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
  have hVt : V ⊆ (A.chart i).target := by
    rintro z hz
    obtain ⟨x, hx, rfl⟩ := hVU hz
    exact (A.chart i).map_source (hUs i hx)
  refine ⟨i, V, hV, hUs i hbU, hbV, hVt, ?_, ?_⟩
  · intro K hK hKV
    exact conformalH1Coordinate_memLp_on_isCompact P.gluedCurvatureBoundedAreaMeasure
      A i (U i) (hUs i) (harea i) K hK (hKV.trans hVU)
      (fun z hz => hτnz z (hKV hz)) u
  · intro j η hη hηc hηV
    exact conformalH1Gradient_coordinate_weakDerivative P.gluedCurvatureBoundedAreaMeasure
      A i j (U i) (hU i) (hUs i) (hτ i) (harea i) V hV hVU hτnz
      η hη hηc hηV u

#print axioms gluedConformalH1_has_local_weak_derivatives

end ExerciseGluingPreparation

#print axioms ConformalGradientAtlas.exists_nonvanishing_chart_neighborhood
#print axioms conformalH1Coordinate_memLp_on_isCompact

end

end SystolicGrowth
