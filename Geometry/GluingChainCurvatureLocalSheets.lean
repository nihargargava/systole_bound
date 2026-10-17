module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainCurvatureMeasure
public import Geometry.QuotientAreaLocalIsometry
public import Geometry.GluingInteriorCharts

@[expose] public section

/-!
# Actual area on original component-interior projection sheets

The original quotient sigma algebra and the genuine seam-free singleton
fibers make native interior images measurable. The sum of the actual
retained-component area measures therefore restricts on a component
interior to that component alone. Original hyperbolic projection balls
then give literal pullback identities, with no assumed local area density.
-/

open Set MeasureTheory UpperHalfPlane
open scoped ENNReal UpperHalfPlane

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

theorem componentInclude_injective (P : ExerciseGluingPreparation C g n genera X)
    (i : Fin n) : Function.Injective (P.componentInclude i) :=
  P.gluedMk_injective_component i

/-- An actual component-interior fiber has no representative in a distinct
retained component. -/
theorem componentInclude_preimage_image_interior_of_ne
    (P : ExerciseGluingPreparation C g n genera X) (i j : Fin n) (hji : j ≠ i)
    {s : Set (P.ChainComponent i)}
    (hinterior : ∀ q ∈ s, q.1 ∈ P.componentInteriorSet i) :
    (P.componentInclude j) ⁻¹' (P.componentInclude i '' s) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro q hq
  obtain ⟨p, hp, hpq⟩ := hq
  have hseam : (⟨i, p⟩ : P.ChainPieces) ∉ P.chainSeamSet :=
    P.componentInteriorPoint_not_mem_chainSeamSet i ⟨p.1, hinterior p hp⟩
  have heq : (⟨i, p⟩ : P.ChainPieces) = ⟨j, q⟩ :=
    P.gluedMk_eq_of_not_mem_chainSeamSet hseam hpq
  exact hji (congrArg Sigma.fst heq).symm

/-- Measurability uses the unchanged quotient sigma algebra and the
actual singleton fibers, not a new Borel-space instance. -/
theorem componentInclude_image_measurable_of_interior
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {s : Set (P.ChainComponent i)} (hs : MeasurableSet s)
    (hinterior : ∀ q ∈ s, q.1 ∈ P.componentInteriorSet i) :
    MeasurableSet (P.componentInclude i '' s) := by
  apply measurableSet_quotient.mpr
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro j
  change MeasurableSet ((P.componentInclude j) ⁻¹' (P.componentInclude i '' s))
  by_cases hji : j = i
  · subst j
    rwa [(P.componentInclude_injective i).preimage_image]
  · rw [P.componentInclude_preimage_image_interior_of_ne i j hji hinterior]
    exact MeasurableSet.empty

/-- On an actual interior image all other component contributions are
zero, so the native sum area equals the retained original component area. -/
theorem gluedChainAreaMeasure_componentInclude_image_of_interior
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {s : Set (P.ChainComponent i)} (hs : MeasurableSet s)
    (hinterior : ∀ q ∈ s, q.1 ∈ P.componentInteriorSet i) :
    P.gluedChainAreaMeasure (P.componentInclude i '' s) =
      P.retainedComponentAreaMeasure i s := by
  have hm := P.componentInclude_image_measurable_of_interior i hs hinterior
  simp only [gluedChainAreaMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · rw [gluedComponentAreaMeasure, Measure.map_apply (P.componentInclude_measurable i) hm,
      (P.componentInclude_injective i).preimage_image]
  · intro j _ hji
    rw [gluedComponentAreaMeasure, Measure.map_apply (P.componentInclude_measurable j) hm,
      P.componentInclude_preimage_image_interior_of_ne i j hji hinterior, measure_empty]
  · simp

/-- The original upstairs ball maps measurably and injectively into the
literal retained component whenever its projection lies in the real interior. -/
theorem retainedInteriorProjectionSheet_measurableEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (o : ℍ) (R : ℝ)
    (hR : 2 * R ≤ (X i).systole)
    (hq : ∀ z : Metric.ball o R,
      (Quotient.mk'' z.1 : (X i).Carrier) ∈ P.componentInteriorSet i) :
    MeasurableEmbedding (fun z : Metric.ball o R =>
      (⟨Quotient.mk'' z.1, interior_subset (hq z)⟩ : P.ChainComponent i)) := by
  have hπ := (X i).quotientBall_measurableEmbedding_of_two_mul_le o R hR
  have hsub := MeasurableEmbedding.subtype_coe (P.componentRetainedSet_measurable i)
  refine ⟨?_, ?_, ?_⟩
  · intro z w h
    apply hπ.injective
    exact congrArg Subtype.val h
  · exact hπ.measurable.subtype_mk
  · intro s hs
    apply hsub.measurableSet_image.mp
    have himage : Subtype.val '' ((fun z : Metric.ball o R =>
        (⟨Quotient.mk'' z.1, interior_subset (hq z)⟩ : P.ChainComponent i)) '' s) =
        (fun z : Metric.ball o R => Quotient.mk (MulAction.orbitRel (X i).deckGroup ℍ) z.1) '' s := by
      rw [← image_comp]
      rfl
    rw [himage]
    exact hπ.measurableSet_image' hs

/-- The actual retained hyperbolic area pulls back to original upstairs
hyperbolic volume on the same genuine projection-ball subtype. -/
theorem retainedComponentAreaMeasure_projectionSheet_comap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (o : ℍ) (R : ℝ)
    (hR : 2 * R ≤ (X i).systole)
    (hq : ∀ z : Metric.ball o R,
      (Quotient.mk'' z.1 : (X i).Carrier) ∈ P.componentInteriorSet i) :
    (P.retainedComponentAreaMeasure i).comap (fun z : Metric.ball o R =>
      (⟨Quotient.mk'' z.1, interior_subset (hq z)⟩ : P.ChainComponent i)) =
        volume.comap (Subtype.val : Metric.ball o R → ℍ) := by
  have hf := P.retainedInteriorProjectionSheet_measurableEmbedding i o R hR hq
  have hsub := MeasurableEmbedding.subtype_coe (P.componentRetainedSet_measurable i)
  rw [retainedComponentAreaMeasure,
    Measure.comap_comap (fun _ hs => hf.measurableSet_image' hs) hsub.injective
      (fun _ hs => hsub.measurableSet_image' hs)]
  exact (X i).quotientAreaMeasure_comap_ball (P.centers i).1 o R hR

/-- The genuine native component-interior sheet is a measurable embedding
for the original glued quotient sigma algebra. -/
theorem gluedInteriorProjectionSheet_measurableEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (o : ℍ) (R : ℝ)
    (hR : 2 * R ≤ (X i).systole)
    (hq : ∀ z : Metric.ball o R,
      (Quotient.mk'' z.1 : (X i).Carrier) ∈ P.componentInteriorSet i) :
    MeasurableEmbedding (fun z : Metric.ball o R =>
      P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' z.1, hq z⟩)) := by
  have hf := P.retainedInteriorProjectionSheet_measurableEmbedding i o R hR hq
  refine ⟨?_, ?_, ?_⟩
  · exact (P.componentInclude_injective i).comp hf.injective
  · exact (P.componentInclude_measurable i).comp hf.measurable
  · intro s hs
    change MeasurableSet ((P.componentInclude i ∘
      (fun z : Metric.ball o R => (⟨Quotient.mk'' z.1, interior_subset (hq z)⟩ :
        P.ChainComponent i))) '' s)
    rw [image_comp]
    apply P.componentInclude_image_measurable_of_interior i (hf.measurableSet_image' hs)
    rintro q ⟨z, _, rfl⟩
    exact hq z

/-- The actual global glued area pulls back on a genuine component-interior
projection sheet to original hyperbolic volume. Both the native sum and
the original measure definitions are used, with no local-density premise. -/
theorem gluedChainAreaMeasure_projectionSheet_comap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (o : ℍ) (R : ℝ)
    (hR : 2 * R ≤ (X i).systole)
    (hq : ∀ z : Metric.ball o R,
      (Quotient.mk'' z.1 : (X i).Carrier) ∈ P.componentInteriorSet i) :
    P.gluedChainAreaMeasure.comap (fun z : Metric.ball o R =>
      P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' z.1, hq z⟩)) =
        volume.comap (Subtype.val : Metric.ball o R → ℍ) := by
  let f : Metric.ball o R → P.ChainComponent i :=
    fun z => ⟨Quotient.mk'' z.1, interior_subset (hq z)⟩
  have hf := P.retainedInteriorProjectionSheet_measurableEmbedding i o R hR hq
  have hι := P.gluedInteriorProjectionSheet_measurableEmbedding i o R hR hq
  apply Measure.ext
  intro s hs
  rw [Measure.comap_apply _ hι.injective (fun _ ht => hι.measurableSet_image' ht) _ hs]
  have himage : (fun z : Metric.ball o R =>
      P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' z.1, hq z⟩)) '' s =
      P.componentInclude i '' (f '' s) := by
    rw [← image_comp]
    rfl
  rw [himage, P.gluedChainAreaMeasure_componentInclude_image_of_interior i
    (hf.measurableSet_image' hs) (by rintro q ⟨z, _, rfl⟩; exact hq z)]
  have heq := congrArg (fun μ : Measure (Metric.ball o R) => μ s)
    (P.retainedComponentAreaMeasure_projectionSheet_comap i o R hR hq)
  rw [Measure.comap_apply _ hf.injective (fun _ ht => hf.measurableSet_image' ht) _ hs] at heq
  exact heq

/-- Every actual component-interior point avoids each original identified
seam circle, by the proved singleton fiber description. -/
theorem componentInclude_not_mem_seamCircle_of_interior
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (q : P.ChainComponent i) (hq : q.1 ∈ P.componentInteriorSet i)
    (k : Fin (n - 1)) : P.componentInclude i q ∉ P.gluedSeamCircle k := by
  rintro ⟨z, hz⟩
  have hseam : (⟨i, q⟩ : P.ChainPieces) ∉ P.chainSeamSet :=
    P.componentInteriorPoint_not_mem_chainSeamSet i ⟨q.1, hq⟩
  have heq : (⟨i, q⟩ : P.ChainPieces) = P.seamSource k z :=
    P.gluedMk_eq_of_not_mem_chainSeamSet hseam hz.symm
  have hsource : P.seamSource k z ∈ P.chainSeamSet :=
    ⟨P.seamTarget k z, Or.inl ⟨k, z, rfl, rfl⟩⟩
  exact hseam (heq.symm ▸ hsource)

/-- The genuinely defined total native seam arclength has zero mass on
every real component-interior image. -/
theorem gluedChainTotalSeamLengthMeasure_componentInclude_image_of_interior
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {s : Set (P.ChainComponent i)}
    (hinterior : ∀ q ∈ s, q.1 ∈ P.componentInteriorSet i) :
    P.gluedChainTotalSeamLengthMeasure (P.componentInclude i '' s) = 0 := by
  simp only [gluedChainTotalSeamLengthMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro k _
  apply le_antisymm _ zero_le
  calc
    P.gluedChainSeamLengthMeasure k (P.componentInclude i '' s) ≤
        P.gluedChainSeamLengthMeasure k (P.gluedSeamCircle k)ᶜ := by
      apply measure_mono
      rintro q ⟨p, hp, rfl⟩
      exact P.componentInclude_not_mem_seamCircle_of_interior i p (hinterior p hp) k
    _ = 0 := P.gluedChainSeamLengthMeasure_compl_seam k

/-- Away from the actual seams, the finite native curvature magnitude
really is native area; the seam contribution is proved zero. -/
theorem gluedChainCurvatureMagnitude_componentInclude_image_of_interior
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {s : Set (P.ChainComponent i)}
    (hinterior : ∀ q ∈ s, q.1 ∈ P.componentInteriorSet i) :
    P.gluedChainCurvatureMagnitude (P.componentInclude i '' s) =
      P.gluedChainAreaMeasure (P.componentInclude i '' s) := by
  rw [gluedChainCurvatureMagnitude, Measure.add_apply, Measure.smul_apply,
    P.gluedChainTotalSeamLengthMeasure_componentInclude_image_of_interior i hinterior]
  simp

/-- The actual finite curvature magnitude and native area have identical
restrictions to any genuine component-interior image. -/
theorem gluedChainCurvatureMagnitude_restrict_componentInclude_image_of_interior
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {s : Set (P.ChainComponent i)}
    (hinterior : ∀ q ∈ s, q.1 ∈ P.componentInteriorSet i) :
    P.gluedChainCurvatureMagnitude.restrict (P.componentInclude i '' s) =
      P.gluedChainAreaMeasure.restrict (P.componentInclude i '' s) := by
  have hzero : P.gluedChainTotalSeamLengthMeasure.restrict (P.componentInclude i '' s) = 0 :=
    Measure.restrict_eq_zero.mpr
      (P.gluedChainTotalSeamLengthMeasure_componentInclude_image_of_interior i hinterior)
  rw [gluedChainCurvatureMagnitude, Measure.restrict_add, Measure.restrict_smul, hzero]
  simp

/-- The actual negative native curvature candidate restricts on genuine
component interiors to negative original native area, not merely to a
measure with matching total variation. -/
theorem gluedChainNegativeCurvatureMeasure_restrict_componentInclude_image_of_interior
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {s : Set (P.ChainComponent i)} (hs : MeasurableSet s)
    (hinterior : ∀ q ∈ s, q.1 ∈ P.componentInteriorSet i) :
    P.gluedChainNegativeCurvatureMeasure.restrict (P.componentInclude i '' s) =
      -(P.gluedChainAreaMeasure.restrict (P.componentInclude i '' s)).toSignedMeasure := by
  have hm := P.componentInclude_image_measurable_of_interior i hs hinterior
  have heq := Measure.toSignedMeasure_congr
    (P.gluedChainCurvatureMagnitude_restrict_componentInclude_image_of_interior i hinterior)
  rw [gluedChainNegativeCurvatureMeasure, VectorMeasure.restrict_neg,
    VectorMeasure.restrict_toSignedMeasure hm, heq]

/-- The actual finite native curvature magnitude pulls back on a genuine
component-interior projection sheet to original hyperbolic area. -/
theorem gluedChainCurvatureMagnitude_projectionSheet_comap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (o : ℍ) (R : ℝ)
    (hR : 2 * R ≤ (X i).systole)
    (hq : ∀ z : Metric.ball o R,
      (Quotient.mk'' z.1 : (X i).Carrier) ∈ P.componentInteriorSet i) :
    P.gluedChainCurvatureMagnitude.comap (fun z : Metric.ball o R =>
      P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' z.1, hq z⟩)) =
        volume.comap (Subtype.val : Metric.ball o R → ℍ) := by
  let f : Metric.ball o R → P.ChainComponent i :=
    fun z => ⟨Quotient.mk'' z.1, interior_subset (hq z)⟩
  have hι := P.gluedInteriorProjectionSheet_measurableEmbedding i o R hR hq
  apply Measure.ext
  intro s hs
  have harea := congrArg (fun μ : Measure (Metric.ball o R) => μ s)
    (P.gluedChainAreaMeasure_projectionSheet_comap i o R hR hq)
  rw [Measure.comap_apply _ hι.injective (fun _ ht => hι.measurableSet_image' ht) _ hs] at harea ⊢
  have himage : (fun z : Metric.ball o R =>
      P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' z.1, hq z⟩)) '' s =
      P.componentInclude i '' (f '' s) := by
    rw [← image_comp]
    rfl
  rw [himage, P.gluedChainCurvatureMagnitude_componentInclude_image_of_interior i
    (by rintro q ⟨z, _, rfl⟩; exact hq z), ← himage]
  exact harea

/-- The variation of the actual negative native curvature candidate has
the proved original hyperbolic area pullback on every real interior sheet. -/
theorem gluedChainNegativeCurvatureMeasure_totalVariation_projectionSheet_comap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (o : ℍ) (R : ℝ)
    (hR : 2 * R ≤ (X i).systole)
    (hq : ∀ z : Metric.ball o R,
      (Quotient.mk'' z.1 : (X i).Carrier) ∈ P.componentInteriorSet i) :
    P.gluedChainNegativeCurvatureMeasure.totalVariation.comap (fun z : Metric.ball o R =>
      P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' z.1, hq z⟩)) =
        volume.comap (Subtype.val : Metric.ball o R → ℍ) := by
  rw [P.gluedChainNegativeCurvatureMeasure_totalVariation]
  exact P.gluedChainCurvatureMagnitude_projectionSheet_comap i o R hR hq

#print axioms gluedChainAreaMeasure_componentInclude_image_of_interior
#print axioms retainedComponentAreaMeasure_projectionSheet_comap
#print axioms gluedChainAreaMeasure_projectionSheet_comap
#print axioms gluedChainCurvatureMagnitude_projectionSheet_comap
#print axioms gluedChainNegativeCurvatureMeasure_totalVariation_projectionSheet_comap
#print axioms gluedChainNegativeCurvatureMeasure_restrict_componentInclude_image_of_interior

end
end SystolicGrowth.ExerciseGluingPreparation
