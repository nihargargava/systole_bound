module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainCurvatureLocalSheets
public import Geometry.GluingChainSeamCurvatureCharts
public import Geometry.GluingSeamOverlap
public import Geometry.GluingPolarArea
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

/-!
# Native area in the actual signed collar charts

The negative and positive signed branches project to the genuine original
outgoing and incoming component interiors. Native area reduces there to
original upstairs hyperbolic area. Actual chart injectivity supplies the
polar-sheet injectivity used by the change-of-variables theorem.
-/

open Set MeasureTheory UpperHalfPlane
open scoped ENNReal UpperHalfPlane

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Native area of any genuine retained interior projection image equals
original hyperbolic volume; the sum and retained-subtype definitions are
both used rather than a local area-density premise. -/
theorem gluedChainAreaMeasure_componentInterior_projection_image
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (o : ℍ) (R : ℝ)
    (hR : 2 * R ≤ (X i).systole) {s : Set ℍ} (hs : MeasurableSet s)
    (hsball : s ⊆ Metric.ball o R)
    (hq : ∀ z ∈ s, (Quotient.mk'' z : (X i).Carrier) ∈ P.componentInteriorSet i) :
    P.gluedChainAreaMeasure (P.componentInclude i ''
      (Subtype.val ⁻¹' ((Quotient.mk (MulAction.orbitRel (X i).deckGroup ℍ)) '' s))) = volume s := by
  let t : Set (P.ChainComponent i) :=
    Subtype.val ⁻¹' ((Quotient.mk (MulAction.orbitRel (X i).deckGroup ℍ)) '' s)
  have ht : MeasurableSet t :=
    ((X i).measurableSet_quotientMk_image hs).preimage measurable_subtype_coe
  have hinterior : ∀ q ∈ t, q.1 ∈ P.componentInteriorSet i := by
    rintro q ⟨z, hz, heq⟩
    exact heq ▸ hq z hz
  have himage : Subtype.val '' t =
      (Quotient.mk (MulAction.orbitRel (X i).deckGroup ℍ)) '' s := by
    apply Subset.antisymm
    · rintro q ⟨p, hp, rfl⟩
      exact hp
    · rintro q ⟨z, hz, rfl⟩
      exact ⟨⟨Quotient.mk'' z, interior_subset (hq z hz)⟩, ⟨z, hz, rfl⟩, rfl⟩
  change P.gluedChainAreaMeasure (P.componentInclude i '' t) = _
  rw [P.gluedChainAreaMeasure_componentInclude_image_of_interior i ht hinterior,
    retainedComponentAreaMeasure, comap_subtype_coe_apply (P.componentRetainedSet_measurable i),
    himage]
  exact (X i).quotientAreaMeasure_image_of_subset_ball (P.centers i).1 o R hR hs hsball

theorem Internal.GluingChainCollarAreaChartsHelpers.outgoing_chart_radius_bounds
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {z : ℂ} (hz : z ∈ (P.seamAngularComplexChart k θ).target) (hn : z.re < 0) :
    gluingRadius C g < gluingRadius C g - z.re ∧
      gluingRadius C g - z.re < gluingEmbeddedRadius C g := by
  have h := (P.mem_seamAngularComplexChart_target k θ z).mp hz
  constructor
  · linarith
  · change gluingRadius C g - z.re < gluingRadius C g + gluingDepth C g
    linarith [h.1.1]

theorem Internal.GluingChainCollarAreaChartsHelpers.incoming_chart_radius_bounds
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {z : ℂ} (hz : z ∈ (P.seamAngularComplexChart k θ).target) (hn : 0 < z.re) :
    gluingRadius C g < gluingRadius C g + z.re ∧
      gluingRadius C g + z.re < gluingEmbeddedRadius C g := by
  have h := (P.mem_seamAngularComplexChart_target k θ z).mp hz
  constructor
  · linarith
  · change gluingRadius C g + z.re < gluingRadius C g + gluingDepth C g
    linarith [h.1.2]

/-- The literal inverse native chart at a negative signed radius is the
actual original outgoing polar projection, with its real interior witness. -/
theorem seamAngularComplexChart_symm_negative
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {z : ℂ} (hz : z ∈ (P.seamAngularComplexChart k θ).target) (hn : z.re < 0) :
    (P.seamAngularComplexChart k θ).symm z =
      P.componentInclude (gluingChainEdgeLeft k)
        ⟨Quotient.mk'' (gluingPolarPoint (P.centers (gluingChainEdgeLeft k)).2
          (Circle.exp z.im) (gluingRadius C g - z.re)), interior_subset
          (P.outgoing_polarPoint_mem_componentInteriorSet _ _
            (Internal.GluingChainCollarAreaChartsHelpers.outgoing_chart_radius_bounds P k θ hz hn).1
            (Internal.GluingChainCollarAreaChartsHelpers.outgoing_chart_radius_bounds P k θ hz hn).2)⟩ := by
  have h := (P.mem_seamAngularComplexChart_target k θ z).mp hz
  let p : GluingSeamAngularDomain C g θ := (⟨z.re, h.1⟩, ⟨z.im, h.2⟩)
  have hp : gluingSeamAngularModel C g θ p = z := Complex.ext rfl rfl
  conv_lhs =>
    rw [← hp, P.seamAngularComplexChart_symm_apply,
      P.seamAngularPoint_of_nonpos k θ p hn.le]
  rfl

/-- The positive inverse branch is the original incoming polar projection
with the prescribed reflected angle, not a different polar parametrization. -/
theorem seamAngularComplexChart_symm_positive
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {z : ℂ} (hz : z ∈ (P.seamAngularComplexChart k θ).target) (hn : 0 < z.re) :
    (P.seamAngularComplexChart k θ).symm z =
      P.componentInclude (gluingChainEdgeRight k)
        ⟨Quotient.mk'' (gluingPolarPoint (P.centers (gluingChainEdgeRight k)).1
          (Circle.exp (-z.im)) (gluingRadius C g + z.re)), interior_subset
          (P.incoming_polarPoint_mem_componentInteriorSet _ _
            (Internal.GluingChainCollarAreaChartsHelpers.incoming_chart_radius_bounds P k θ hz hn).1
            (Internal.GluingChainCollarAreaChartsHelpers.incoming_chart_radius_bounds P k θ hz hn).2)⟩ := by
  have h := (P.mem_seamAngularComplexChart_target k θ z).mp hz
  let p : GluingSeamAngularDomain C g θ := (⟨z.re, h.1⟩, ⟨z.im, h.2⟩)
  have hp : gluingSeamAngularModel C g θ p = z := Complex.ext rfl rfl
  conv_lhs =>
    rw [← hp, P.seamAngularComplexChart_symm_apply,
      P.seamAngularPoint_of_nonneg k θ p hn.le]
  apply congrArg P.gluedMk
  unfold seamIncomingPolarPoint
  apply congrArg (Sigma.mk (gluingChainEdgeRight k))
  apply Subtype.ext
  change (Quotient.mk'' (gluingPolarPoint (P.centers (gluingChainEdgeRight k)).1
    (Circle.exp z.im)⁻¹ (gluingRadius C g + z.re)) : (X (gluingChainEdgeRight k)).Carrier) = _
  rw [Circle.exp_neg]

/-- Genuine negative-branch polar injectivity is a consequence of the
literal native chart's inverse injectivity. -/
theorem seamAngularComplexChart_outgoing_polar_injOn
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {s : Set ℂ} (ht : s ⊆ (P.seamAngularComplexChart k θ).target)
    (hn : ∀ z ∈ s, z.re < 0) :
    InjOn (fun z : ℂ => gluingPolarPoint (P.centers (gluingChainEdgeLeft k)).2
      (Circle.exp z.im) (gluingRadius C g - z.re)) s := by
  intro z hz w hw h
  apply (P.seamAngularComplexChart k θ).symm.injOn (ht hz) (ht hw)
  rw [P.seamAngularComplexChart_symm_negative k θ (ht hz) (hn z hz),
    P.seamAngularComplexChart_symm_negative k θ (ht hw) (hn w hw)]
  apply congrArg (P.componentInclude (gluingChainEdgeLeft k))
  apply Subtype.ext
  exact congrArg (Quotient.mk (MulAction.orbitRel (X (gluingChainEdgeLeft k)).deckGroup ℍ)) h

theorem seamAngularComplexChart_incoming_polar_injOn
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {s : Set ℂ} (ht : s ⊆ (P.seamAngularComplexChart k θ).target)
    (hn : ∀ z ∈ s, 0 < z.re) :
    InjOn (fun z : ℂ => gluingPolarPoint (P.centers (gluingChainEdgeRight k)).1
      (Circle.exp (-z.im)) (gluingRadius C g + z.re)) s := by
  intro z hz w hw h
  apply (P.seamAngularComplexChart k θ).symm.injOn (ht hz) (ht hw)
  rw [P.seamAngularComplexChart_symm_positive k θ (ht hz) (hn z hz),
    P.seamAngularComplexChart_symm_positive k θ (ht hw) (hn w hw)]
  apply congrArg (P.componentInclude (gluingChainEdgeRight k))
  apply Subtype.ext
  exact congrArg (Quotient.mk (MulAction.orbitRel (X (gluingChainEdgeRight k)).deckGroup ℍ)) h

/-- The negative signed branch has exactly the area of its actual
upstairs outgoing polar image in the original component. -/
theorem gluedChainAreaMeasure_seamAngularComplexChart_negative_image
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {s : Set ℂ} (hs : MeasurableSet s)
    (ht : s ⊆ (P.seamAngularComplexChart k θ).target) (hn : ∀ z ∈ s, z.re < 0) :
    P.gluedChainAreaMeasure ((P.seamAngularComplexChart k θ).symm '' s) =
      ∫⁻ z : ℂ in s, ENNReal.ofReal (Real.sinh (gluingRadius C g - z.re)) := by
  let i := gluingChainEdgeLeft k
  let o := (P.centers i).2
  let f : ℂ → ℍ := fun z => gluingPolarPoint o (Circle.exp z.im) (gluingRadius C g - z.re)
  have ha : Continuous (fun z : ℂ => Circle.exp z.im) :=
    Circle.exp.continuous.comp Complex.continuous_im
  have hr : Continuous (fun z : ℂ => gluingRadius C g - z.re) :=
    continuous_const.sub Complex.continuous_re
  have hf : Continuous f := by
    change Continuous ((fun p : Circle × ℝ => gluingPolarPoint o p.1 p.2) ∘
      (fun z : ℂ => (Circle.exp z.im, gluingRadius C g - z.re)))
    exact (gluingPolarPoint_continuous o).comp (ha.prodMk hr)
  have hinj : InjOn f s := P.seamAngularComplexChart_outgoing_polar_injOn k θ ht hn
  have hfs : MeasurableSet (f '' s) := hs.image_of_continuousOn_injOn hf.continuousOn hinj
  have hball : f '' s ⊆ Metric.ball o (gluingEmbeddedRadius C g) := by
    rintro v ⟨z, hz, rfl⟩
    rw [Metric.mem_ball, dist_comm, dist_gluingPolarPoint o _
      (P.radius_pos.le.trans (Internal.GluingChainCollarAreaChartsHelpers.outgoing_chart_radius_bounds P k θ (ht hz) (hn z hz)).1.le)]
    exact (Internal.GluingChainCollarAreaChartsHelpers.outgoing_chart_radius_bounds P k θ (ht hz) (hn z hz)).2
  have hq : ∀ v ∈ f '' s, (Quotient.mk'' v : (X i).Carrier) ∈ P.componentInteriorSet i := by
    rintro v ⟨z, hz, rfl⟩
    exact P.outgoing_polarPoint_mem_componentInteriorSet i _
      (Internal.GluingChainCollarAreaChartsHelpers.outgoing_chart_radius_bounds P k θ (ht hz) (hn z hz)).1
      (Internal.GluingChainCollarAreaChartsHelpers.outgoing_chart_radius_bounds P k θ (ht hz) (hn z hz)).2
  have himage : (P.seamAngularComplexChart k θ).symm '' s =
      P.componentInclude i '' (Subtype.val ⁻¹'
        ((Quotient.mk (MulAction.orbitRel (X i).deckGroup ℍ)) '' (f '' s))) := by
    apply Subset.antisymm
    · rintro y ⟨z, hz, rfl⟩
      refine ⟨⟨Quotient.mk'' (f z), interior_subset (hq (f z) ⟨z, hz, rfl⟩)⟩,
        ⟨f z, ⟨z, hz, rfl⟩, rfl⟩, ?_⟩
      exact (P.seamAngularComplexChart_symm_negative k θ (ht hz) (hn z hz)).symm
    · rintro y ⟨q, ⟨v, ⟨z, hz, rfl⟩, hvq⟩, rfl⟩
      refine ⟨z, hz, ?_⟩
      rw [P.seamAngularComplexChart_symm_negative k θ (ht hz) (hn z hz)]
      apply congrArg (P.componentInclude i)
      apply Subtype.ext
      exact hvq
  rw [himage, P.gluedChainAreaMeasure_componentInterior_projection_image i o
    (gluingEmbeddedRadius C g) (P.twice_outer_lt_systole i).le hfs hball hq]
  apply volume_image_gluingOutgoingPolarPoint o (gluingRadius C g) hs
  · intro z hz
    linarith [(Internal.GluingChainCollarAreaChartsHelpers.outgoing_chart_radius_bounds P k θ (ht hz) (hn z hz)).1, P.radius_pos]
  · intro z hz w hw h
    apply hinj hz hw
    apply UpperHalfPlane.ext
    exact h

/-- The reflected positive signed branch has the original incoming
hyperbolic polar area, with its actual angular reflection. -/
theorem gluedChainAreaMeasure_seamAngularComplexChart_positive_image
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {s : Set ℂ} (hs : MeasurableSet s)
    (ht : s ⊆ (P.seamAngularComplexChart k θ).target) (hn : ∀ z ∈ s, 0 < z.re) :
    P.gluedChainAreaMeasure ((P.seamAngularComplexChart k θ).symm '' s) =
      ∫⁻ z : ℂ in s, ENNReal.ofReal (Real.sinh (gluingRadius C g + z.re)) := by
  let i := gluingChainEdgeRight k
  let o := (P.centers i).1
  let f : ℂ → ℍ := fun z => gluingPolarPoint o (Circle.exp (-z.im)) (gluingRadius C g + z.re)
  have ha : Continuous (fun z : ℂ => Circle.exp (-z.im)) :=
    Circle.exp.continuous.comp Complex.continuous_im.neg
  have hr : Continuous (fun z : ℂ => gluingRadius C g + z.re) :=
    continuous_const.add Complex.continuous_re
  have hf : Continuous f := by
    change Continuous ((fun p : Circle × ℝ => gluingPolarPoint o p.1 p.2) ∘
      (fun z : ℂ => (Circle.exp (-z.im), gluingRadius C g + z.re)))
    exact (gluingPolarPoint_continuous o).comp (ha.prodMk hr)
  have hinj : InjOn f s := P.seamAngularComplexChart_incoming_polar_injOn k θ ht hn
  have hfs : MeasurableSet (f '' s) := hs.image_of_continuousOn_injOn hf.continuousOn hinj
  have hball : f '' s ⊆ Metric.ball o (gluingEmbeddedRadius C g) := by
    rintro v ⟨z, hz, rfl⟩
    rw [Metric.mem_ball, dist_comm, dist_gluingPolarPoint o _
      (P.radius_pos.le.trans (Internal.GluingChainCollarAreaChartsHelpers.incoming_chart_radius_bounds P k θ (ht hz) (hn z hz)).1.le)]
    exact (Internal.GluingChainCollarAreaChartsHelpers.incoming_chart_radius_bounds P k θ (ht hz) (hn z hz)).2
  have hq : ∀ v ∈ f '' s, (Quotient.mk'' v : (X i).Carrier) ∈ P.componentInteriorSet i := by
    rintro v ⟨z, hz, rfl⟩
    exact P.incoming_polarPoint_mem_componentInteriorSet i _
      (Internal.GluingChainCollarAreaChartsHelpers.incoming_chart_radius_bounds P k θ (ht hz) (hn z hz)).1
      (Internal.GluingChainCollarAreaChartsHelpers.incoming_chart_radius_bounds P k θ (ht hz) (hn z hz)).2
  have himage : (P.seamAngularComplexChart k θ).symm '' s =
      P.componentInclude i '' (Subtype.val ⁻¹'
        ((Quotient.mk (MulAction.orbitRel (X i).deckGroup ℍ)) '' (f '' s))) := by
    apply Subset.antisymm
    · rintro y ⟨z, hz, rfl⟩
      refine ⟨⟨Quotient.mk'' (f z), interior_subset (hq (f z) ⟨z, hz, rfl⟩)⟩,
        ⟨f z, ⟨z, hz, rfl⟩, rfl⟩, ?_⟩
      exact (P.seamAngularComplexChart_symm_positive k θ (ht hz) (hn z hz)).symm
    · rintro y ⟨q, ⟨v, ⟨z, hz, rfl⟩, hvq⟩, rfl⟩
      refine ⟨z, hz, ?_⟩
      rw [P.seamAngularComplexChart_symm_positive k θ (ht hz) (hn z hz)]
      apply congrArg (P.componentInclude i)
      apply Subtype.ext
      exact hvq
  rw [himage, P.gluedChainAreaMeasure_componentInterior_projection_image i o
    (gluingEmbeddedRadius C g) (P.twice_outer_lt_systole i).le hfs hball hq]
  apply volume_image_gluingIncomingPolarPoint o (gluingRadius C g) hs
  · intro z hz
    linarith [(Internal.GluingChainCollarAreaChartsHelpers.incoming_chart_radius_bounds P k θ (ht hz) (hn z hz)).1, P.radius_pos]
  · intro z hz w hw h
    apply hinj hz hw
    apply UpperHalfPlane.ext
    exact h

/-- Both original puncture circles are null for the natural quotient area.
This uses their actual embedded upstairs sphere, not a null-seam premise. -/
theorem quotientAreaMeasure_punctureCircle_eq_zero
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (o : ℍ) :
    (X i).quotientAreaMeasure (P.centers i).1
      ((X i).punctureCircle o (gluingRadius C g)) = 0 := by
  change (X i).quotientAreaMeasure (P.centers i).1
    ((Quotient.mk (MulAction.orbitRel (X i).deckGroup ℍ)) ''
      Metric.sphere o (gluingRadius C g)) = 0
  rw [(X i).quotientAreaMeasure_image_of_subset_ball (P.centers i).1 o
    (gluingEmbeddedRadius C g) (P.twice_outer_lt_systole i).le
    (Metric.isClosed_sphere.measurableSet) (by
      intro z hz
      rw [Metric.mem_ball, Metric.mem_sphere.mp hz]
      exact P.radius_lt_embeddedRadius), volume_hyperbolic_sphere_eq_zero]

theorem retainedComponentAreaMeasure_leftCirclePoint_range_eq_zero
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    P.retainedComponentAreaMeasure i (range (P.leftCirclePoint i)) = 0 := by
  rw [retainedComponentAreaMeasure,
    comap_subtype_coe_apply (P.componentRetainedSet_measurable i)]
  apply le_antisymm _ zero_le
  calc
    (X i).quotientAreaMeasure (P.centers i).1
        (Subtype.val '' range (P.leftCirclePoint i)) ≤
      (X i).quotientAreaMeasure (P.centers i).1
        ((X i).punctureCircle (P.centers i).1 (gluingRadius C g)) := by
          apply measure_mono
          rintro q ⟨p, ⟨z, rfl⟩, rfl⟩
          exact ⟨z.1, z.2, rfl⟩
    _ = 0 := P.quotientAreaMeasure_punctureCircle_eq_zero i _

theorem retainedComponentAreaMeasure_rightCirclePoint_range_eq_zero
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    P.retainedComponentAreaMeasure i (range (P.rightCirclePoint i)) = 0 := by
  rw [retainedComponentAreaMeasure,
    comap_subtype_coe_apply (P.componentRetainedSet_measurable i)]
  apply le_antisymm _ zero_le
  calc
    (X i).quotientAreaMeasure (P.centers i).1
        (Subtype.val '' range (P.rightCirclePoint i)) ≤
      (X i).quotientAreaMeasure (P.centers i).1
        ((X i).punctureCircle (P.centers i).2 (gluingRadius C g)) := by
          apply measure_mono
          rintro q ⟨p, ⟨z, rfl⟩, rfl⟩
          exact ⟨z.1, z.2, rfl⟩
    _ = 0 := P.quotientAreaMeasure_punctureCircle_eq_zero i _

private theorem componentInclude_preimage_gluedSeamCircle_subset
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (k : Fin (n - 1)) :
    P.componentInclude i ⁻¹' P.gluedSeamCircle k ⊆
      range (P.leftCirclePoint i) ∪ range (P.rightCirclePoint i) := by
  rintro q ⟨z, hz⟩
  have heq : P.gluedMk ⟨i, q⟩ = P.gluedMk (P.seamSource k z) := hz.symm
  have hseam : (⟨i, q⟩ : P.ChainPieces) ∈ P.chainSeamSet := by
    rcases (P.gluedMk_eq_iff _ _).mp heq with h | h | h
    · rw [h]
      exact ⟨P.seamTarget k z, Or.inl ⟨k, z, rfl, rfl⟩⟩
    · exact ⟨_, Or.inl h⟩
    · exact ⟨_, Or.inr h⟩
  rcases hseam with ⟨p, h | h⟩
  · exact Or.inr (P.chainRelation_source_mem_rightCircle
      (a := ⟨i, q⟩) (b := p) h)
  · exact Or.inl (P.chainRelation_target_mem_leftCircle
      (a := p) (b := ⟨i, q⟩) h)

/-- The real seam in the glued carrier has zero original hyperbolic area. -/
theorem gluedChainAreaMeasure_gluedSeamCircle_eq_zero
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedChainAreaMeasure (P.gluedSeamCircle k) = 0 := by
  have hs : MeasurableSet (P.gluedSeamCircle k) := by
    exact (P.gluedCarrier_isOpen_measurable (P.gluedSeamCircle_isClosed k).isOpen_compl).of_compl
  simp only [gluedChainAreaMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [gluedComponentAreaMeasure,
    Measure.map_apply (P.componentInclude_measurable i) hs]
  apply le_antisymm _ zero_le
  calc
    P.retainedComponentAreaMeasure i (P.componentInclude i ⁻¹' P.gluedSeamCircle k) ≤
      P.retainedComponentAreaMeasure i
        (range (P.leftCirclePoint i) ∪ range (P.rightCirclePoint i)) :=
          measure_mono (componentInclude_preimage_gluedSeamCircle_subset P i k)
    _ ≤ P.retainedComponentAreaMeasure i (range (P.leftCirclePoint i)) +
        P.retainedComponentAreaMeasure i (range (P.rightCirclePoint i)) := measure_union_le _ _
    _ = 0 := by rw [P.retainedComponentAreaMeasure_leftCirclePoint_range_eq_zero,
      P.retainedComponentAreaMeasure_rightCirclePoint_range_eq_zero, add_zero]

/-- Measurable complex pieces of the genuine chart have measurable native
images for the original quotient sigma algebra. -/
theorem seamAngularComplexChart_symm_image_measurable
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {s : Set ℂ} (hs : MeasurableSet s)
    (ht : s ⊆ (P.seamAngularComplexChart k θ).target) :
    MeasurableSet ((P.seamAngularComplexChart k θ).symm '' s) := by
  have hle : borel P.GluedCarrier ≤ (inferInstance : MeasurableSpace P.GluedCarrier) := by
    apply MeasurableSpace.generateFrom_le
    intro u hu
    exact P.gluedCarrier_isOpen_measurable hu
  have hB : @MeasurableSet P.GluedCarrier (borel P.GluedCarrier)
      ((P.seamAngularComplexChart k θ).symm '' s) := by
    letI : MeasurableSpace P.GluedCarrier := borel P.GluedCarrier
    letI : BorelSpace P.GluedCarrier := ⟨rfl⟩
    exact hs.image_of_continuousOn_injOn
      ((P.seamAngularComplexChart k θ).symm.continuousOn.mono ht)
      ((P.seamAngularComplexChart k θ).symm.injOn.mono ht)
  exact hle _ hB

/-- The literal zero-radius slice of this native collar is area-null. -/
theorem gluedChainAreaMeasure_seamAngularComplexChart_zero_image
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {s : Set ℂ} (ht : s ⊆ (P.seamAngularComplexChart k θ).target)
    (hz : ∀ z ∈ s, z.re = 0) :
    P.gluedChainAreaMeasure ((P.seamAngularComplexChart k θ).symm '' s) = 0 := by
  apply le_antisymm _ zero_le
  calc
    P.gluedChainAreaMeasure ((P.seamAngularComplexChart k θ).symm '' s) ≤
        P.gluedChainAreaMeasure (P.gluedSeamCircle k) := by
      apply measure_mono
      rintro y ⟨z, hs, rfl⟩
      have h := (P.mem_seamAngularComplexChart_target k θ z).mp (ht hs)
      let p : GluingSeamAngularDomain C g θ := (⟨z.re, h.1⟩, ⟨z.im, h.2⟩)
      have hp : gluingSeamAngularModel C g θ p = z := Complex.ext rfl rfl
      rw [← hp, P.seamAngularComplexChart_symm_apply,
        P.seamAngularPoint_of_zero k θ p (hz z hs)]
      exact ⟨_, rfl⟩
    _ = 0 := P.gluedChainAreaMeasure_gluedSeamCircle_eq_zero k

private theorem complex_volume_zero_real_part :
    (volume : Measure ℂ) {z : ℂ | z.re = 0} = 0 := by
  have heq : {z : ℂ | z.re = 0} = Complex.measurableEquivRealProd ⁻¹'
      (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) := by
    ext z
    simp
  rw [heq, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv,
    Measure.volume_eq_prod, Measure.prod_prod]
  simp

private theorem collar_area_integral_zero_real_part
    (r : ℝ) {s : Set ℂ} (hs : ∀ z ∈ s, z.re = 0) :
    (∫⁻ z : ℂ in s, ENNReal.ofReal (gluingCollarWarp r z.re)) = 0 := by
  apply setLIntegral_measure_zero
  apply le_antisymm _ zero_le
  exact (measure_mono (show s ⊆ {z : ℂ | z.re = 0} from fun z hz => hs z hz)).trans_eq
    complex_volume_zero_real_part

/-- The entire genuine signed collar chart carries exactly the original
warped hyperbolic area, including its zero-area seam. -/
theorem gluedChainAreaMeasure_seamAngularComplexChart_image
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {s : Set ℂ} (hs : MeasurableSet s)
    (ht : s ⊆ (P.seamAngularComplexChart k θ).target) :
    P.gluedChainAreaMeasure ((P.seamAngularComplexChart k θ).symm '' s) =
      ((volume : Measure ℂ).withDensity
        (fun z => ENNReal.ofReal (gluingCollarWarp (gluingRadius C g) z.re))) s := by
  let e := P.seamAngularComplexChart k θ
  let μ : Measure ℂ := volume.withDensity
    (fun z => ENNReal.ofReal (gluingCollarWarp (gluingRadius C g) z.re))
  let sn : Set ℂ := s ∩ {z | z.re < 0}
  let sp : Set ℂ := s ∩ {z | 0 < z.re}
  let sz : Set ℂ := s ∩ {z | z.re = 0}
  have hn : MeasurableSet sn := hs.inter (isOpen_lt Complex.continuous_re continuous_const).measurableSet
  have hp : MeasurableSet sp := hs.inter (isOpen_lt continuous_const Complex.continuous_re).measurableSet
  have hz : MeasurableSet sz := hs.inter (isClosed_eq Complex.continuous_re continuous_const).measurableSet
  have hns : sn ⊆ s := inter_subset_left
  have hps : sp ⊆ s := inter_subset_left
  have hzs : sz ⊆ s := inter_subset_left
  have hnp : Disjoint sn sp := by
    apply Set.disjoint_left.mpr
    intro z hn hp
    have hn' : z.re < 0 := hn.2
    have hp' : 0 < z.re := hp.2
    linarith
  have hnz : Disjoint (sn ∪ sp) sz := by
    apply Set.disjoint_left.mpr
    rintro z (hn | hp) hz
    · exact (ne_of_lt hn.2) hz.2
    · exact (ne_of_gt hp.2) hz.2
  have hunion : sn ∪ sp ∪ sz = s := by
    ext z
    constructor
    · rintro ((hn | hp) | hz)
      · exact hn.1
      · exact hp.1
      · exact hz.1
    · intro hz
      rcases lt_trichotomy z.re 0 with hn | he | hp
      · exact Or.inl (Or.inl ⟨hz, hn⟩)
      · exact Or.inr ⟨hz, he⟩
      · exact Or.inl (Or.inr ⟨hz, hp⟩)
  have himdisj : ∀ u v : Set ℂ, u ⊆ s → v ⊆ s → Disjoint u v →
      Disjoint (e.symm '' u) (e.symm '' v) := by
    intro u v hu hv hd
    apply Set.disjoint_image_image
    intro z hz w hw heq
    have hzw := e.symm.injOn (ht (hu hz)) (ht (hv hw)) heq
    exact Set.disjoint_left.mp hd hz (hzw ▸ hw)
  have hpimage : MeasurableSet (e.symm '' sp) :=
    P.seamAngularComplexChart_symm_image_measurable k θ hp (hps.trans ht)
  have hzimage : MeasurableSet (e.symm '' sz) :=
    P.seamAngularComplexChart_symm_image_measurable k θ hz (hzs.trans ht)
  have hnegative : P.gluedChainAreaMeasure (e.symm '' sn) = μ sn := by
    rw [P.gluedChainAreaMeasure_seamAngularComplexChart_negative_image k θ hn
      (hns.trans ht) (fun z hz => hz.2), withDensity_apply _ hn]
    apply setLIntegral_congr_fun hn
    intro z hz
    dsimp only
    rw [gluingCollarWarp_eq_of_nonpos _ hz.2.le]
  have hpositive : P.gluedChainAreaMeasure (e.symm '' sp) = μ sp := by
    rw [P.gluedChainAreaMeasure_seamAngularComplexChart_positive_image k θ hp
      (hps.trans ht) (fun z hz => hz.2), withDensity_apply _ hp]
    apply setLIntegral_congr_fun hp
    intro z hz
    dsimp only
    rw [gluingCollarWarp_eq_of_nonneg _ hz.2.le]
  have hzero : P.gluedChainAreaMeasure (e.symm '' sz) = μ sz := by
    rw [P.gluedChainAreaMeasure_seamAngularComplexChart_zero_image k θ
      (hzs.trans ht) (fun z hz => hz.2), withDensity_apply _ hz,
      collar_area_integral_zero_real_part _ (fun z hz => hz.2)]
  change P.gluedChainAreaMeasure (e.symm '' s) = μ s
  rw [← hunion, image_union,
    measure_union (himdisj (sn ∪ sp) sz (union_subset hns hps) hzs hnz) hzimage,
    image_union, measure_union (himdisj sn sp hns hps hnp) hpimage]
  rw [hnegative, hpositive, hzero, measure_union hnz hz, measure_union hnp hp]

theorem gluedChainAreaMeasure_seamAngularComplexChart_image_integral
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {s : Set ℂ} (hs : MeasurableSet s)
    (ht : s ⊆ (P.seamAngularComplexChart k θ).target) :
    P.gluedChainAreaMeasure ((P.seamAngularComplexChart k θ).symm '' s) =
      ∫⁻ z : ℂ in s, ENNReal.ofReal (gluingCollarWarp (gluingRadius C g) z.re) := by
  rw [P.gluedChainAreaMeasure_seamAngularComplexChart_image k θ hs ht,
    withDensity_apply _ hs]

/-- Pulling back actual native area through the literal two-dimensional
seam parametrization gives the genuine complex collar density. -/
theorem gluedChainAreaMeasure_comap_seamAngularPoint
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) :
    P.gluedChainAreaMeasure.comap (P.seamAngularPoint k θ) =
      ((volume : Measure ℂ).withDensity
        (fun z => ENNReal.ofReal (gluingCollarWarp (gluingRadius C g) z.re))).comap
          (gluingSeamAngularModel C g θ) := by
  have hmodel : MeasurableEmbedding (gluingSeamAngularModel C g θ) :=
    (gluingSeamAngularModel_isOpenEmbedding C g θ).measurableEmbedding
  apply Measure.ext
  intro s hs
  rw [(P.seamAngularPoint_measurableEmbedding k θ).comap_apply, hmodel.comap_apply]
  have ht : gluingSeamAngularModel C g θ '' s ⊆
      (P.seamAngularComplexChart k θ).target := by
    rintro z ⟨p, hp, rfl⟩
    exact (P.mem_seamAngularComplexChart_target k θ _).mpr ⟨p.1.2, p.2.2⟩
  have himage : P.seamAngularPoint k θ '' s =
      (P.seamAngularComplexChart k θ).symm '' (gluingSeamAngularModel C g θ '' s) := by
    rw [← image_comp]
    congr 1
    funext p
    exact (P.seamAngularComplexChart_symm_apply k θ p).symm
  rw [himage]
  exact P.gluedChainAreaMeasure_seamAngularComplexChart_image k θ
    (hmodel.measurableSet_image' hs) ht

#print axioms gluedChainAreaMeasure_comap_seamAngularPoint
#print axioms gluedChainAreaMeasure_seamAngularComplexChart_image
#print axioms seamAngularComplexChart_symm_image_measurable
#print axioms gluedChainAreaMeasure_seamAngularComplexChart_zero_image
#print axioms gluedChainAreaMeasure_gluedSeamCircle_eq_zero
#print axioms gluedChainAreaMeasure_componentInterior_projection_image
#print axioms seamAngularComplexChart_outgoing_polar_injOn
#print axioms seamAngularComplexChart_incoming_polar_injOn
#print axioms gluedChainAreaMeasure_seamAngularComplexChart_negative_image
#print axioms gluedChainAreaMeasure_seamAngularComplexChart_positive_image

end
end SystolicGrowth.ExerciseGluingPreparation
