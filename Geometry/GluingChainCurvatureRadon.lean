module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainCurvatureLocalSheets
public import Geometry.GluingChainSeamCurvatureCharts
public import Geometry.GluingChartEvaluations
public import Geometry.GluingIntrinsicMetric
public import Mathlib.MeasureTheory.Measure.Regular

@[expose] public section

/-!
# The actual native curvature candidate is a finite Radon measure

The unchanged quotient measurable space is proved to be the native Borel
space using its genuine measurable interior and seam sheets. The original
compact metric topology then gives regularity of the constructed area,
seam and curvature measures. Intrinsic identification remains separate.
-/

open Set MeasureTheory UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth

theorem Internal.GluingChainCurvatureRadonHelpers.borel_inter_range_of_measurable_sheet
    {A M : Type*} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace M] [MeasurableSpace M] {f : A → M}
    (hf : Topology.IsOpenEmbedding f) (hm : Measurable f)
    {s : Set M} (hs : MeasurableSet s) :
    @MeasurableSet M (borel M) (s ∩ range f) := by
  have hp : MeasurableSet (f ⁻¹' s) := hm hs
  have hi : @MeasurableSet M (borel M) (f '' (f ⁻¹' s)) := by
    letI : MeasurableSpace M := borel M
    letI : BorelSpace M := ⟨rfl⟩
    exact hf.measurableEmbedding.measurableSet_image.mpr hp
  convert hi using 1
  ext x
  constructor
  · rintro ⟨hx, a, rfl⟩
    exact ⟨a, hx, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha, ⟨a, rfl⟩⟩

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The original quotient sigma algebra equals the native Borel sigma
algebra. No replacement measurable-space instance is imposed. -/
instance gluedCarrierBorelSpace
    (P : ExerciseGluingPreparation C g n genera X) : BorelSpace P.GluedCarrier where
  measurable_eq := by
    classical
    apply le_antisymm
    · intro s hs
      have hlocal (e : ↥P.gluedComplexAtlas) :
          @MeasurableSet P.GluedCarrier (borel P.GluedCarrier) (s ∩ e.1.source) := by
        rcases e.2 with hi | ⟨k, θ, he⟩
        · obtain ⟨i, o, R, hR, hsys, hq, hf, he⟩ := hi
          rw [he, P.gluedInteriorComplexChart_source]
          exact Internal.GluingChainCurvatureRadonHelpers.borel_inter_range_of_measurable_sheet hf
            (P.gluedInteriorProjectionSheet_measurableEmbedding i o R (by linarith) hq).measurable hs
        · rw [he, P.seamAngularComplexChart_source]
          exact Internal.GluingChainCurvatureRadonHelpers.borel_inter_range_of_measurable_sheet
            (P.seamAngularPoint_isOpenEmbedding k θ)
            (P.seamAngularPoint_measurable k θ) hs
      have hcover : univ ⊆ ⋃ e : ↥P.gluedComplexAtlas, e.1.source := by
        intro x _
        obtain ⟨e, he, hx⟩ := P.exists_gluedComplexAtlas_chart x
        exact mem_iUnion.mpr ⟨⟨e, he⟩, hx⟩
      obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
        (fun e : ↥P.gluedComplexAtlas => e.1.source) (fun e => e.1.open_source) hcover
      have heq : s = ⋃ e ∈ t, s ∩ e.1.source := by
        ext x
        constructor
        · intro hx
          obtain ⟨e, he, hxsource⟩ := mem_iUnion₂.mp (ht (mem_univ x))
          exact mem_iUnion₂.mpr ⟨e, he, hx, hxsource⟩
        · intro hx
          obtain ⟨_, _, hx, _⟩ := mem_iUnion₂.mp hx
          exact hx
      rw [heq]
      exact t.measurableSet_biUnion (fun e _ => hlocal e)
    · apply MeasurableSpace.generateFrom_le
      intro s hs
      exact P.gluedCarrier_isOpen_measurable hs

instance gluedChainAreaMeasure_regular
    (P : ExerciseGluingPreparation C g n genera X) : Measure.Regular P.gluedChainAreaMeasure := by
  letI := P.gluedCarrierIntrinsicMetricSpace
  infer_instance

instance gluedChainCurvatureMagnitude_regular
    (P : ExerciseGluingPreparation C g n genera X) :
    Measure.Regular P.gluedChainCurvatureMagnitude := by
  letI := P.gluedCarrierIntrinsicMetricSpace
  infer_instance

/-- Finite total variation of the original signed candidate is a genuine
regular measure on the actual surface, not only in model coordinates. -/
theorem gluedChainNegativeCurvatureMeasure_totalVariation_regular
    (P : ExerciseGluingPreparation C g n genera X) :
    Measure.Regular P.gluedChainNegativeCurvatureMeasure.totalVariation := by
  rw [P.gluedChainNegativeCurvatureMeasure_totalVariation]
  infer_instance

/-- The original global candidate has curvature at most negative native
area as an inequality of genuine finite signed measures, seam included. -/
theorem gluedChainNegativeCurvatureMeasure_le_neg_area
    (P : ExerciseGluingPreparation C g n genera X) :
    P.gluedChainNegativeCurvatureMeasure ≤ -P.gluedChainAreaMeasure.toSignedMeasure := by
  have harea : P.gluedChainAreaMeasure ≤ P.gluedChainCurvatureMagnitude := by
    rw [gluedChainCurvatureMagnitude]
    exact Measure.le_iff.mpr fun s _ => by
      rw [Measure.add_apply]
      exact le_add_right le_rfl
  have hsigned := (Measure.toSignedMeasure_le_toSignedMeasure_iff _ _).mpr harea
  apply VectorMeasure.le_iff.mpr
  intro s hs
  rw [gluedChainNegativeCurvatureMeasure, neg_apply, neg_apply]
  exact neg_le_neg (VectorMeasure.le_iff.mp hsigned s hs)

#print axioms gluedCarrierBorelSpace
#print axioms gluedChainCurvatureMagnitude_regular
#print axioms gluedChainNegativeCurvatureMeasure_totalVariation_regular
#print axioms gluedChainNegativeCurvatureMeasure_le_neg_area

end ExerciseGluingPreparation
end SystolicGrowth
