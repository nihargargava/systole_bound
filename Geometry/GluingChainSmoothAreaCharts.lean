module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainSmoothCurvature
public import Geometry.GluingChainCollarAreaCharts
public import Geometry.GluingCircleAngularMeasure

@[expose] public section

/-!
# Coordinate area of the actual global smooth metrics

The patched positive measure is identified with the determinant density of
the actual smooth tangent tensor in native charts, rather than merely given
the name of metric area. Thin strips use genuine circle/angular coordinates;
outside the strips the unchanged original hyperbolic area remains in place.
-/

open Set Filter MeasureTheory
open scoped ENNReal BigOperators Manifold

namespace SystolicGrowth

noncomputable section

local instance gluingSmoothAreaCircleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance gluingSmoothAreaCircleBorelSpace : BorelSpace Circle := ⟨rfl⟩

/-- Literal complex coordinates on a thin radial/angular chart. -/
def gluingThinSeamAngularModel (δ θ : ℝ)
    (p : Ioo (-δ) δ × GluingAngularInterval θ) : ℂ :=
  Complex.equivRealProdCLM.symm (p.1.1, p.2.1)

theorem gluingThinSeamAngularModel_measurableEmbedding (δ θ : ℝ) :
    MeasurableEmbedding (gluingThinSeamAngularModel δ θ) :=
  Complex.measurableEquivRealProd.symm.measurableEmbedding.comp
    ((MeasurableEmbedding.subtype_coe measurableSet_Ioo).prodMap
      (MeasurableEmbedding.subtype_coe measurableSet_Ioo))

theorem gluingThinSeamAngularModel_range (δ θ : ℝ) :
    range (gluingThinSeamAngularModel δ θ) =
      {z : ℂ | z.re ∈ Ioo (-δ) δ ∧ z.im ∈ GluingAngularInterval θ} := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1.2, p.2.2⟩
  · intro hz
    refine ⟨(⟨z.re, hz.1⟩, ⟨z.im, hz.2⟩), ?_⟩
    exact Complex.ext rfl rfl

/-- Original complex Lebesgue area pulls back to the actual product of
the original radial and angular subtype Lebesgue measures. -/
theorem gluingThinSeamAngularModel_comap_volume (δ θ : ℝ) :
    (volume : Measure ℂ).comap (gluingThinSeamAngularModel δ θ) =
      ((volume : Measure ℝ).comap (Subtype.val : Ioo (-δ) δ → ℝ)).prod
        ((volume : Measure ℝ).comap (Subtype.val : GluingAngularInterval θ → ℝ)) := by
  let μ := (volume : Measure ℝ).comap (Subtype.val : Ioo (-δ) δ → ℝ)
  let ν := (volume : Measure ℝ).comap (Subtype.val : GluingAngularInterval θ → ℝ)
  letI : IsFiniteMeasure μ := inferInstanceAs (IsFiniteMeasure (gluingThinRadialMeasure δ))
  letI : IsFiniteMeasure ν := by
    change IsFiniteMeasure ((volume : Measure ℝ).comap
      (Subtype.val : GluingAngularInterval θ → ℝ))
    rw [← gluingCircleAngularLengthMeasure_comap_angularInterval θ]
    infer_instance
  let F : Ioo (-δ) δ × GluingAngularInterval θ → ℝ × ℝ := Prod.map Subtype.val Subtype.val
  let e := Complex.measurableEquivRealProd.symm
  let D : Set (ℝ × ℝ) := Ioo (-δ) δ ×ˢ GluingAngularInterval θ
  have hF : Measurable F := measurable_subtype_coe.prodMap measurable_subtype_coe
  have hreal : (μ.prod ν).map F = (volume : Measure (ℝ × ℝ)).restrict D := by
    rw [← Measure.map_prod_map μ ν measurable_subtype_coe measurable_subtype_coe,
      map_comap_subtype_coe measurableSet_Ioo, map_comap_subtype_coe measurableSet_Ioo,
      Measure.prod_restrict, Measure.volume_eq_prod]
  have hmodel : gluingThinSeamAngularModel δ θ = e ∘ F := rfl
  have hrange : range (gluingThinSeamAngularModel δ θ) = e '' D := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨F p, ⟨p.1.2, p.2.2⟩, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩), rfl⟩
  have hpush : (μ.prod ν).map (gluingThinSeamAngularModel δ θ) =
      (volume : Measure ℂ).restrict (range (gluingThinSeamAngularModel δ θ)) := by
    rw [hrange, hmodel, ← Measure.map_map e.measurable hF, hreal]
    have h := e.measurableEmbedding.restrict_map (volume : Measure (ℝ × ℝ)) (e '' D)
    rw [e.injective.preimage_image] at h
    rw [← h, Complex.volume_preserving_equiv_real_prod.symm.map_eq]
  have hf := gluingThinSeamAngularModel_measurableEmbedding δ θ
  have h := hf.restrict_comap (volume : Measure ℂ) univ
  simp only [Measure.restrict_univ, image_univ] at h
  rw [h, ← hpush, hf.comap_map]

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

theorem gluedChainSmoothSeamArea_restrict_own_thinCollar
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (k : Fin (n - 1)) :
    (P.gluedChainSmoothSeamArea ε k).restrict (P.thinSeamCollar k) =
      P.gluedChainSmoothSeamArea ε k := by
  rw [gluedChainSmoothSeamArea,
    Measure.restrict_map (P.thinSeamCylinderMap_measurableEmbedding k).measurable
      (P.thinSeamCollar_isOpen k).measurableSet]
  have hpre : P.thinSeamCylinderMap k ⁻¹' P.thinSeamCollar k = univ := by
    rw [← P.range_thinSeamCylinderMap k, preimage_range]
  rw [hpre, Measure.restrict_univ]

theorem gluedChainSmoothSeamArea_restrict_distinct_thinCollar
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ)
    {k l : Fin (n - 1)} (hkl : k ≠ l) :
    (P.gluedChainSmoothSeamArea ε k).restrict (P.thinSeamCollar l) = 0 := by
  rw [gluedChainSmoothSeamArea,
    Measure.restrict_map (P.thinSeamCylinderMap_measurableEmbedding k).measurable
      (P.thinSeamCollar_isOpen l).measurableSet]
  have hpre : P.thinSeamCylinderMap k ⁻¹' P.thinSeamCollar l = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hk : P.thinSeamCylinderMap k p ∈ P.thinSeamCollar k := by
      rw [← P.range_thinSeamCylinderMap k]
      exact ⟨p, rfl⟩
    exact disjoint_left.mp (P.closedThinSeamCollar_disjoint hkl)
      (P.thinSeamCollar_subset_closedThinSeamCollar k hk)
      (P.thinSeamCollar_subset_closedThinSeamCollar l hp)
  simp [hpre]

/-- Actual separation makes the full smooth area on a thin strip exactly
its own transported determinant density. -/
theorem gluedChainSmoothAreaMeasure_restrict_thinCollar
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (k : Fin (n - 1)) :
    (P.gluedChainSmoothAreaMeasure ε).restrict (P.thinSeamCollar k) =
      P.gluedChainSmoothSeamArea ε k := by
  classical
  rw [gluedChainSmoothAreaMeasure, Measure.restrict_add,
    P.gluedChainSmoothOutsideArea_restrict_thinCollar k, zero_add]
  have hsum := map_sum (Measure.restrictₗ (P.thinSeamCollar k))
    (fun l : Fin (n - 1) => P.gluedChainSmoothSeamArea ε l) Finset.univ
  simp only [Measure.restrictₗ_apply] at hsum
  rw [hsum, Finset.sum_eq_single k]
  · exact P.gluedChainSmoothSeamArea_restrict_own_thinCollar ε k
  · intro l _ hlk
    exact P.gluedChainSmoothSeamArea_restrict_distinct_thinCollar ε hlk
  · simp

/-- Pullback through the literal cylinder recovers its actual positive
warped determinant density; every other patch vanishes by separation. -/
theorem gluedChainSmoothAreaMeasure_comap_thinSeamCylinderMap
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (k : Fin (n - 1)) :
    (P.gluedChainSmoothAreaMeasure ε).comap (P.thinSeamCylinderMap k) =
      gluingThinCylinderArea (gluingRadius C g) ε P.seamSmoothingCutoff
        (gluingThinSeamWidth C g) := by
  have hf := P.thinSeamCylinderMap_measurableEmbedding k
  have h := congrArg (fun μ : Measure P.GluedCarrier => μ.comap (P.thinSeamCylinderMap k))
    (P.gluedChainSmoothAreaMeasure_restrict_thinCollar ε k)
  rw [hf.comap_restrict, ← P.range_thinSeamCylinderMap k, preimage_range,
    Measure.restrict_univ, gluedChainSmoothSeamArea, hf.comap_map] at h
  exact h

/-- The true native coordinate matrix supplies the positive area density
used in the transported cylinder measure. -/
theorem gluedSmoothSeamCoordinateMetric_areaDensity
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 ≤ ε)
    (k : Fin (n - 1)) (θ : ℝ) {p : ℝ × ℝ}
    (hp : Complex.equivRealProdCLM.symm p ∈ (P.seamAngularComplexChart k θ).target)
    (hthin : (P.seamAngularComplexChart k θ).symm (Complex.equivRealProdCLM.symm p) ∈
      P.thinSeamCollar k) :
    Real.sqrt (P.gluedSmoothSeamCoordinateMetric ε k θ p).det =
      gluingCollarLocalizedSmoothWarp (gluingRadius C g) ε P.seamSmoothingCutoff p.1 := by
  rw [P.gluedSmoothSeamCoordinateMetric_eq_warped ε k θ hp hthin]
  exact gluingWarpedMetric_areaDensity
    (gluingCollarLocalizedSmoothWarp_pos P.radius_pos hε _ p.1)

/-- The genuine angular seam parametrization restricted to the disjoint
thin interval; the surface, angle and radial coordinates are unchanged. -/
def thinSeamAngularPoint (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (θ : ℝ)
    (p : Ioo (-gluingThinSeamWidth C g) (gluingThinSeamWidth C g) ×
      GluingAngularInterval θ) : P.GluedCarrier :=
  P.seamAngularPoint k θ (P.thinRadialInclusion p.1, p.2)

theorem thinSeamAngularPoint_measurableEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) :
    MeasurableEmbedding (P.thinSeamAngularPoint k θ) := by
  have hi : Topology.IsOpenEmbedding P.thinRadialInclusion :=
    Topology.IsOpenEmbedding.inclusion P.thinRadialInterval_subset_original
      (isOpen_Ioo.preimage continuous_subtype_val)
  exact (P.seamAngularPoint_measurableEmbedding k θ).comp
    (hi.prodMap (Topology.IsOpenEmbedding.id (X := GluingAngularInterval θ))).measurableEmbedding

theorem thinSeamAngularPoint_eq_chart_symm
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (p : Ioo (-gluingThinSeamWidth C g) (gluingThinSeamWidth C g) ×
      GluingAngularInterval θ) :
    P.thinSeamAngularPoint k θ p =
      (P.seamAngularComplexChart k θ).symm
        (gluingThinSeamAngularModel (gluingThinSeamWidth C g) θ p) :=
  (P.seamAngularComplexChart_symm_apply k θ (P.thinRadialInclusion p.1, p.2)).symm

theorem thinSeamAngularPoint_mem_thinCollar
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (p : Ioo (-gluingThinSeamWidth C g) (gluingThinSeamWidth C g) ×
      GluingAngularInterval θ) : P.thinSeamAngularPoint k θ p ∈ P.thinSeamCollar k := by
  rw [← P.range_thinSeamCylinderMap k]
  exact ⟨(gluingAngularIntervalMap θ p.2, p.1), rfl⟩

theorem gluingThinSeamAngularModel_mem_chart_target
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (p : Ioo (-gluingThinSeamWidth C g) (gluingThinSeamWidth C g) ×
      GluingAngularInterval θ) :
    gluingThinSeamAngularModel (gluingThinSeamWidth C g) θ p ∈
      (P.seamAngularComplexChart k θ).target := by
  exact (P.mem_seamAngularComplexChart_target k θ _).mpr
    ⟨(P.thinRadialInclusion p.1).2, p.2.2⟩

/-- The determinant of the actual global metric, evaluated through its
literal thin native chart, is exactly the transported positive warp. -/
theorem gluedSmoothSeamCoordinateMetric_areaDensity_thinAngular
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 ≤ ε)
    (k : Fin (n - 1)) (θ : ℝ)
    (p : Ioo (-gluingThinSeamWidth C g) (gluingThinSeamWidth C g) ×
      GluingAngularInterval θ) :
    Real.sqrt (P.gluedSmoothSeamCoordinateMetric ε k θ (p.1.1, p.2.1)).det =
      gluingCollarLocalizedSmoothWarp (gluingRadius C g) ε P.seamSmoothingCutoff p.1.1 := by
  apply P.gluedSmoothSeamCoordinateMetric_areaDensity hε k θ
    (P.gluingThinSeamAngularModel_mem_chart_target k θ p)
  change (P.seamAngularComplexChart k θ).symm
    (gluingThinSeamAngularModel (gluingThinSeamWidth C g) θ p) ∈ P.thinSeamCollar k
  rw [← P.thinSeamAngularPoint_eq_chart_symm k θ p]
  exact P.thinSeamAngularPoint_mem_thinCollar k θ p

/-- Actual global area in every genuine thin angular chart is the
localized warp density against ordinary complex Lebesgue area. -/
theorem gluedChainSmoothAreaMeasure_comap_thinSeamAngularPoint
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (k : Fin (n - 1)) (θ : ℝ) :
    (P.gluedChainSmoothAreaMeasure ε).comap (P.thinSeamAngularPoint k θ) =
      ((volume : Measure ℂ).withDensity (fun z => ENNReal.ofReal
        (gluingCollarLocalizedSmoothWarp (gluingRadius C g) ε P.seamSmoothingCutoff z.re))).comap
          (gluingThinSeamAngularModel (gluingThinSeamWidth C g) θ) := by
  have hangular := gluingThinAngularCylinderMap_measurableEmbedding
    (gluingThinSeamWidth C g) θ
  have hcylinder := P.thinSeamCylinderMap_measurableEmbedding k
  have hcomp : P.thinSeamAngularPoint k θ =
      P.thinSeamCylinderMap k ∘ gluingThinAngularCylinderMap (gluingThinSeamWidth C g) θ := rfl
  rw [hcomp, ← Measure.comap_comap hangular.measurableSet_image' hcylinder.injective
    hcylinder.measurableSet_image', P.gluedChainSmoothAreaMeasure_comap_thinSeamCylinderMap ε k,
    gluingThinCylinderArea_comap_angular,
    gluingMeasure_comap_withDensity
      (gluingThinSeamAngularModel_measurableEmbedding (gluingThinSeamWidth C g) θ),
    gluingThinSeamAngularModel_comap_volume]
  rfl

/-- The full patched area is the determinant area of the actual global
smooth metric, pulled back through its literal native chart. -/
theorem gluedChainSmoothAreaMeasure_comap_thinSeamAngularPoint_eq_metricArea
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 ≤ ε)
    (k : Fin (n - 1)) (θ : ℝ) :
    (P.gluedChainSmoothAreaMeasure ε).comap (P.thinSeamAngularPoint k θ) =
      ((volume : Measure ℂ).withDensity (fun z => ENNReal.ofReal
        (Real.sqrt (P.gluedSmoothSeamCoordinateMetric ε k θ (z.re, z.im)).det))).comap
          (gluingThinSeamAngularModel (gluingThinSeamWidth C g) θ) := by
  rw [P.gluedChainSmoothAreaMeasure_comap_thinSeamAngularPoint ε k θ,
    gluingMeasure_comap_withDensity
      (gluingThinSeamAngularModel_measurableEmbedding (gluingThinSeamWidth C g) θ),
    gluingMeasure_comap_withDensity
      (gluingThinSeamAngularModel_measurableEmbedding (gluingThinSeamWidth C g) θ)]
  congr 1
  funext p
  dsimp only [Function.comp_apply, gluingThinSeamAngularModel]
  change ENNReal.ofReal
    (gluingCollarLocalizedSmoothWarp (gluingRadius C g) ε P.seamSmoothingCutoff p.1.1) =
    ENNReal.ofReal (Real.sqrt (P.gluedSmoothSeamCoordinateMetric ε k θ (p.1.1, p.2.1)).det)
  rw [P.gluedSmoothSeamCoordinateMetric_areaDensity_thinAngular hε k θ p]

/-- Every measurable set within the genuine thin seam chart has exactly
the area integral of the actual metric's Gram determinant. -/
theorem gluedChainSmoothAreaMeasure_thin_seam_chart_image
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 ≤ ε)
    (k : Fin (n - 1)) (θ : ℝ) {s : Set ℂ} (hs : MeasurableSet s)
    (hsub : s ⊆ range (gluingThinSeamAngularModel (gluingThinSeamWidth C g) θ)) :
    P.gluedChainSmoothAreaMeasure ε ((P.seamAngularComplexChart k θ).symm '' s) =
      ∫⁻ z : ℂ in s, ENNReal.ofReal
        (Real.sqrt (P.gluedSmoothSeamCoordinateMetric ε k θ (z.re, z.im)).det) := by
  let f := gluingThinSeamAngularModel (gluingThinSeamWidth C g) θ
  let t := f ⁻¹' s
  have himage : f '' t = s := image_preimage_eq_of_subset hsub
  have hpoint : P.thinSeamAngularPoint k θ '' t =
      (P.seamAngularComplexChart k θ).symm '' s := by
    rw [← himage, ← image_comp]
    congr 1
    funext p
    exact P.thinSeamAngularPoint_eq_chart_symm k θ p
  have h := congrArg (fun μ : Measure (Ioo (-gluingThinSeamWidth C g)
      (gluingThinSeamWidth C g) × GluingAngularInterval θ) => μ t)
    (P.gluedChainSmoothAreaMeasure_comap_thinSeamAngularPoint_eq_metricArea hε k θ)
  rw [(P.thinSeamAngularPoint_measurableEmbedding k θ).comap_apply,
    (gluingThinSeamAngularModel_measurableEmbedding (gluingThinSeamWidth C g) θ).comap_apply,
    hpoint, himage, withDensity_apply _ hs] at h
  exact h

#print axioms gluedChainSmoothAreaMeasure_comap_thinSeamCylinderMap
#print axioms gluedSmoothSeamCoordinateMetric_areaDensity
#print axioms gluingThinSeamAngularModel_comap_volume
#print axioms gluedSmoothSeamCoordinateMetric_areaDensity_thinAngular
#print axioms gluedChainSmoothAreaMeasure_comap_thinSeamAngularPoint_eq_metricArea
#print axioms gluedChainSmoothAreaMeasure_thin_seam_chart_image

end ExerciseGluingPreparation
end
end SystolicGrowth
