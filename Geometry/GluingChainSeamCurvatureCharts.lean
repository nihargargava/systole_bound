module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainCurvatureMeasure
public import Geometry.GluingChartEvaluations
public import Geometry.GluingChainTopology
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

@[expose] public section

/-!
# Native seam measure in literal angular charts

The original quotient seam measure is locally the pushforward of `sinh r`
times angular Lebesgue measure through the actual collar parametrization.
The proof retains the quotient sigma algebra and the reflected native seam.
-/

open MeasureTheory Set UpperHalfPlane
open scoped ENNReal UpperHalfPlane

namespace SystolicGrowth

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

private theorem circle_exp_turn_map (a : ℝ) :
    (volume.restrict (Ioc a (a + 2 * Real.pi))).map Circle.exp =
      (volume : Measure (AddCircle (2 * Real.pi))).map AddCircle.homeomorphCircle' := by
  rw [← (AddCircle.measurePreserving_mk (2 * Real.pi) a).map_eq,
    Measure.map_map AddCircle.homeomorphCircle'.continuous.measurable
      (AddCircle.measurePreserving_mk (2 * Real.pi) a).measurable]
  rfl

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

theorem gluedChainSeamCircleMap_continuous
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Continuous (P.gluedChainSeamCircleMap k) := by
  have h : P.gluedChainSeamCircleMap k =
      Subtype.val ∘ P.gluedSeamCircleInclusion k := by
    funext θ
    exact P.gluedChainSeamCircleMap_eq_inclusion k θ
  rw [h]
  exact continuous_subtype_val.comp (P.gluedSeamCircleInclusion k).continuous

theorem gluedChainSeamCircleMap_injective
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Function.Injective (P.gluedChainSeamCircleMap k) := by
  intro θ φ h
  have hi : P.gluedSeamCircleInclusion k θ = P.gluedSeamCircleInclusion k φ := by
    apply Subtype.ext
    simpa only [P.gluedChainSeamCircleMap_eq_inclusion] using h
  have hh := congrArg (P.gluedSeamCircleRetraction k) hi
  simpa only [P.gluedSeamCircleRetraction_inclusion] using hh

/-- Images of Borel arcs are measurable for the original quotient sigma algebra. -/
theorem gluedChainSeamCircleMap_measurableEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    MeasurableEmbedding (P.gluedChainSeamCircleMap k) := by
  have hc := (P.gluedChainSeamCircleMap_continuous k).isClosedEmbedding
    (P.gluedChainSeamCircleMap_injective k)
  refine ⟨hc.injective, P.gluedChainSeamCircleMap_measurable k, ?_⟩
  intro s hs
  have hb : @MeasurableSet P.GluedCarrier (borel P.GluedCarrier)
      (P.gluedChainSeamCircleMap k '' s) := by
    letI : MeasurableSpace P.GluedCarrier := borel P.GluedCarrier
    letI : BorelSpace P.GluedCarrier := ⟨rfl⟩
    exact hc.measurableEmbedding.measurableSet_image.mpr hs
  have hle : borel P.GluedCarrier ≤ (inferInstance : MeasurableSpace P.GluedCarrier) := by
    apply MeasurableSpace.generateFrom_le
    intro t ht
    exact P.gluedCarrier_isOpen_measurable ht
  exact hle _ hb

/-- The same literal seam measure can use any complete positive angular turn. -/
theorem gluedChainSeamLengthMeasure_eq_turn
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (a : ℝ) :
    P.gluedChainSeamLengthMeasure k =
      ENNReal.ofReal (Real.sinh (gluingRadius C g)) •
        (volume.restrict (Ioc a (a + 2 * Real.pi))).map
          (P.gluedChainSeamAngularMap k) := by
  unfold gluedChainSeamLengthMeasure gluedChainSeamAngularMap
  rw [← Measure.map_map (P.gluedChainSeamCircleMap_measurable k)
      Circle.exp.continuous.measurable,
    ← Measure.map_map (P.gluedChainSeamCircleMap_measurable k)
      Circle.exp.continuous.measurable]
  congr 2
  simpa only [zero_add] using (circle_exp_turn_map 0).trans (circle_exp_turn_map a).symm

/-- The seam at signed radius zero in the actual angular chart. -/
def gluedChainSeamAngularChartMap
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) :
    GluingAngularInterval θ → P.GluedCarrier :=
  fun a => P.gluedChainSeamAngularMap k a.1

theorem gluedChainSeamAngularChartMap_measurableEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) :
    MeasurableEmbedding (P.gluedChainSeamAngularChartMap k θ) :=
  (P.gluedChainSeamCircleMap_measurableEmbedding k).comp
    (gluingAngularIntervalMap_isOpenEmbedding θ).measurableEmbedding

theorem gluedChainSeamAngularMap_image_window_measurable
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) :
    MeasurableSet (P.gluedChainSeamAngularMap k '' GluingAngularInterval θ) := by
  have h : P.gluedChainSeamAngularMap k '' GluingAngularInterval θ =
      range (P.gluedChainSeamAngularChartMap k θ) := by
    ext y
    simp only [mem_image, mem_range, gluedChainSeamAngularChartMap]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a.1, a.2, rfl⟩
  rw [h]
  exact (P.gluedChainSeamAngularChartMap_measurableEmbedding k θ).measurableSet_range

/-- Restriction to a genuine seam angular chart has exactly the native angular density. -/
theorem gluedChainSeamLengthMeasure_restrict_angular_window
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) :
    (P.gluedChainSeamLengthMeasure k).restrict
        (P.gluedChainSeamAngularMap k '' GluingAngularInterval θ) =
      ENNReal.ofReal (Real.sinh (gluingRadius C g)) •
        (volume.restrict (GluingAngularInterval θ)).map
          (P.gluedChainSeamAngularMap k) := by
  let a := θ - Real.pi / 2
  have hsub : GluingAngularInterval θ ⊆ Ioc a (a + 2 * Real.pi) := by
    intro x hx
    exact ⟨hx.1, by dsimp [a]; linarith [hx.2, Real.pi_pos]⟩
  have hinj : InjOn (P.gluedChainSeamAngularMap k) (Ioc a (a + 2 * Real.pi)) := by
    intro x hx y hy hxy
    apply Circle.exp_injOn_Ioc (by linarith) hx hy
    exact P.gluedChainSeamCircleMap_injective k hxy
  have hpre : (P.gluedChainSeamAngularMap k ⁻¹'
      (P.gluedChainSeamAngularMap k '' GluingAngularInterval θ)) ∩
        Ioc a (a + 2 * Real.pi) = GluingAngularInterval θ := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, hxy⟩, hx⟩
      have heq := hinj (hsub hy) hx hxy
      simpa only [← heq] using hy
    · intro hx
      exact ⟨⟨x, hx, rfl⟩, hsub hx⟩
  rw [P.gluedChainSeamLengthMeasure_eq_turn k a, Measure.restrict_smul,
    Measure.restrict_map (P.gluedChainSeamAngularMap_measurable k)
      (P.gluedChainSeamAngularMap_image_window_measurable k θ),
    Measure.restrict_restrict
      ((P.gluedChainSeamAngularMap_measurable k)
        (P.gluedChainSeamAngularMap_image_window_measurable k θ)), hpre]

/-- Exact pullback through the literal one-dimensional seam chart. -/
theorem gluedChainSeamLengthMeasure_comap_angularChart
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) :
    (P.gluedChainSeamLengthMeasure k).comap (P.gluedChainSeamAngularChartMap k θ) =
      ENNReal.ofReal (Real.sinh (gluingRadius C g)) •
        (volume : Measure ℝ).comap (Subtype.val : GluingAngularInterval θ → ℝ) := by
  let ν := (volume : Measure ℝ).comap (Subtype.val : GluingAngularInterval θ → ℝ)
  have hpush : ν.map (P.gluedChainSeamAngularChartMap k θ) =
      (volume.restrict (GluingAngularInterval θ)).map
        (P.gluedChainSeamAngularMap k) := by
    change ν.map (P.gluedChainSeamAngularMap k ∘ Subtype.val) = _
    rw [← Measure.map_map (P.gluedChainSeamAngularMap_measurable k) measurable_subtype_coe]
    rw [map_comap_subtype_coe measurableSet_Ioo]
  have hrange : range (P.gluedChainSeamAngularChartMap k θ) =
      P.gluedChainSeamAngularMap k '' GluingAngularInterval θ := by
    ext y
    simp only [mem_range, mem_image, gluedChainSeamAngularChartMap]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.1, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hrestrict := (P.gluedChainSeamAngularChartMap_measurableEmbedding k θ).restrict_comap
    (P.gluedChainSeamLengthMeasure k) univ
  simp only [Measure.restrict_univ, image_univ, hrange] at hrestrict
  rw [hrestrict, P.gluedChainSeamLengthMeasure_restrict_angular_window k θ,
    ← hpush, Measure.comap_smul,
    (P.gluedChainSeamAngularChartMap_measurableEmbedding k θ).comap_map]

/-- The pullback parameter is the original two-dimensional chart at signed radius zero. -/
theorem gluedChainSeamAngularChartMap_eq_seamAngularPoint
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (a : GluingAngularInterval θ) :
    P.gluedChainSeamAngularChartMap k θ a =
      P.seamAngularPoint k θ (⟨0, neg_lt_zero.mpr P.depth_pos, P.depth_pos⟩, a) := by
  change P.gluedChainSeamCircleMap k (Circle.exp a.1) = _
  rw [P.gluedChainSeamCircleMap_eq_inclusion]
  rfl

theorem seamAngularComplexChart_seamAngularChartMap
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (a : GluingAngularInterval θ) :
    P.seamAngularComplexChart k θ (P.gluedChainSeamAngularChartMap k θ a) =
      (a.1 : ℂ) * Complex.I := by
  rw [P.gluedChainSeamAngularChartMap_eq_seamAngularPoint,
    P.seamAngularComplexChart_apply]
  apply Complex.ext <;> simp [gluingSeamAngularModel]

/-- The same seam point is the incoming native polar point with reflected angle. -/
theorem gluedChainSeamAngularChartMap_eq_reflected_incoming
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (a : GluingAngularInterval θ) :
    P.gluedChainSeamAngularChartMap k θ a =
      P.gluedMk (P.seamIncomingPolarPoint k
        (Circle.exp (-a.1), ⟨gluingRadius C g, le_rfl, P.radius_lt_embeddedRadius⟩)) := by
  rw [P.gluedChainSeamAngularChartMap_eq_seamAngularPoint]
  have h := P.seamAngularPoint_of_nonneg k θ
    (⟨0, neg_lt_zero.mpr P.depth_pos, P.depth_pos⟩, a) le_rfl
  simpa only [add_zero, Circle.exp_neg] using h

set_option backward.isDefEq.respectTransparency false in
theorem seamAngularPoint_measurable
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) :
    Measurable (P.seamAngularPoint k θ) := by
  let out : GluingSeamAngularDomain C g θ → P.GluedCarrier := fun p =>
    P.gluedMk (P.seamOutgoingPolarPoint k (Circle.exp p.2.1,
      ⟨gluingRadius C g + max (-p.1.1) 0, by
        constructor
        · linarith [le_max_right (-p.1.1) 0]
        · change gluingRadius C g + max (-p.1.1) 0 <
            gluingRadius C g + gluingDepth C g
          have h : -p.1.1 < gluingDepth C g := by linarith [p.1.2.1]
          linarith [max_lt h P.depth_pos]⟩))
  let inc : GluingSeamAngularDomain C g θ → P.GluedCarrier := fun p =>
    P.gluedMk (P.seamIncomingPolarPoint k ((Circle.exp p.2.1)⁻¹,
      ⟨gluingRadius C g + max p.1.1 0, by
        constructor
        · linarith [le_max_right p.1.1 0]
        · change gluingRadius C g + max p.1.1 0 <
            gluingRadius C g + gluingDepth C g
          linarith [max_lt p.1.2.2 P.depth_pos]⟩))
  have hout : Measurable out := by
    apply (P.componentInclude_measurable (gluingChainEdgeLeft k)).comp
    apply Measurable.subtype_mk
    apply measurable_quotient_mk''.comp
    exact ((gluingPolarPoint_continuous (P.centers (gluingChainEdgeLeft k)).2).comp
      ((Circle.exp.continuous.comp (continuous_subtype_val.comp continuous_snd)).prodMk
        (continuous_const.add
          (((continuous_subtype_val.comp continuous_fst).neg).max continuous_const)))).measurable
  have hinc : Measurable inc := by
    apply (P.componentInclude_measurable (gluingChainEdgeRight k)).comp
    apply Measurable.subtype_mk
    apply measurable_quotient_mk''.comp
    exact ((gluingPolarPoint_continuous (P.centers (gluingChainEdgeRight k)).1).comp
      (((Circle.exp.continuous.comp (continuous_subtype_val.comp continuous_snd)).inv).prodMk
        (continuous_const.add
          ((continuous_subtype_val.comp continuous_fst).max continuous_const)))).measurable
  have h : P.seamAngularPoint k θ = fun p => if p.1.1 ≤ 0 then out p else inc p := by
    funext p
    unfold seamAngularPoint
    rw [P.seamCylinderHomeomorph_apply]
    unfold seamCylinderMap
    split_ifs <;> rfl
  rw [h]
  exact hout.ite (measurableSet_le (measurable_subtype_coe.comp measurable_fst)
    measurable_const) hinc

/-- The literal two-dimensional collar parametrization is measurable for the native sigma algebra. -/
theorem seamAngularPoint_measurableEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) :
    MeasurableEmbedding (P.seamAngularPoint k θ) := by
  have hc := P.seamAngularPoint_isOpenEmbedding k θ
  refine ⟨hc.injective, P.seamAngularPoint_measurable k θ, ?_⟩
  intro s hs
  have hb : @MeasurableSet P.GluedCarrier (borel P.GluedCarrier)
      (P.seamAngularPoint k θ '' s) := by
    letI : MeasurableSpace P.GluedCarrier := borel P.GluedCarrier
    letI : BorelSpace P.GluedCarrier := ⟨rfl⟩
    exact hc.measurableEmbedding.measurableSet_image.mpr hs
  have hle : borel P.GluedCarrier ≤ (inferInstance : MeasurableSpace P.GluedCarrier) := by
    apply MeasurableSpace.generateFrom_le
    intro t ht
    exact P.gluedCarrier_isOpen_measurable ht
  exact hle _ hb

theorem seamAngularPoint_mem_gluedSeamCircle_iff
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (p : GluingSeamAngularDomain C g θ) :
    P.seamAngularPoint k θ p ∈ P.gluedSeamCircle k ↔ p.1.1 = 0 := by
  constructor
  · intro hp
    rw [← P.range_gluedSeamCircleInclusion k] at hp
    obtain ⟨φ, hφ⟩ := hp
    have hi : P.gluedSeamCircleInclusion k φ =
        P.seamCylinderHomeomorph k (Circle.exp p.2.1, p.1) := Subtype.ext hφ
    have hh := (P.seamCylinderHomeomorph k).injective hi
    exact (congrArg (fun q : GluingSeamCylinder C g => q.2.1) hh).symm
  · intro hp
    have hrad : p.1 = ⟨0, neg_lt_zero.mpr P.depth_pos, P.depth_pos⟩ := Subtype.ext hp
    change (P.seamCylinderHomeomorph k (Circle.exp p.2.1, p.1)).1 ∈ _
    rw [hrad]
    exact P.gluedSeamCircleInclusion_mem k (Circle.exp p.2.1)

/-- In the actual two-dimensional collar chart the seam density is radial Dirac times angular
Lebesgue measure, with its original hyperbolic arclength factor. -/
theorem gluedChainSeamLengthMeasure_comap_seamAngularPoint
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) :
    (P.gluedChainSeamLengthMeasure k).comap (P.seamAngularPoint k θ) =
      ENNReal.ofReal (Real.sinh (gluingRadius C g)) •
        (Measure.dirac (⟨0, neg_lt_zero.mpr P.depth_pos, P.depth_pos⟩ :
          Ioo (-gluingDepth C g) (gluingDepth C g))).prod
          ((volume : Measure ℝ).comap (Subtype.val : GluingAngularInterval θ → ℝ)) := by
  let zero : Ioo (-gluingDepth C g) (gluingDepth C g) :=
    ⟨0, neg_lt_zero.mpr P.depth_pos, P.depth_pos⟩
  let ν := (volume : Measure ℝ).comap (Subtype.val : GluingAngularInterval θ → ℝ)
  letI : IsFiniteMeasure ν := ⟨by
    change ((volume : Measure ℝ).comap
      (Subtype.val : GluingAngularInterval θ → ℝ)) univ < ∞
    rw [comap_subtype_coe_apply measurableSet_Ioo]
    simp only [image_univ, Subtype.range_coe, Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top⟩
  have hpush : ν.map (P.gluedChainSeamAngularChartMap k θ) =
      (volume.restrict (GluingAngularInterval θ)).map
        (P.gluedChainSeamAngularMap k) := by
    change ν.map (P.gluedChainSeamAngularMap k ∘ Subtype.val) = _
    rw [← Measure.map_map (P.gluedChainSeamAngularMap_measurable k) measurable_subtype_coe]
    rw [map_comap_subtype_coe measurableSet_Ioo]
  have hinter : range (P.seamAngularPoint k θ) ∩ P.gluedSeamCircle k =
      P.gluedChainSeamAngularMap k '' GluingAngularInterval θ := by
    ext y
    constructor
    · rintro ⟨⟨p, rfl⟩, hp⟩
      have hzero := (P.seamAngularPoint_mem_gluedSeamCircle_iff k θ p).mp hp
      refine ⟨p.2.1, p.2.2, ?_⟩
      change P.gluedChainSeamAngularChartMap k θ p.2 = _
      rw [P.gluedChainSeamAngularChartMap_eq_seamAngularPoint]
      congr 2
      exact (Subtype.ext hzero).symm
    · rintro ⟨a, ha, rfl⟩
      have heq := P.gluedChainSeamAngularChartMap_eq_seamAngularPoint k θ ⟨a, ha⟩
      refine ⟨⟨(zero, ⟨a, ha⟩), heq.symm⟩, ?_⟩
      change P.gluedChainSeamCircleMap k (Circle.exp a) ∈ _
      rw [P.gluedChainSeamCircleMap_eq_inclusion]
      exact P.gluedSeamCircleInclusion_mem k (Circle.exp a)
  have hconcentrated : (P.gluedChainSeamLengthMeasure k).restrict (P.gluedSeamCircle k) =
      P.gluedChainSeamLengthMeasure k := by
    apply Measure.restrict_eq_self_of_ae_mem
    exact mem_ae_iff.mpr (P.gluedChainSeamLengthMeasure_compl_seam k)
  have hsource : (P.gluedChainSeamLengthMeasure k).restrict
      (range (P.seamAngularPoint k θ)) =
        (P.gluedChainSeamLengthMeasure k).restrict
          (P.gluedChainSeamAngularMap k '' GluingAngularInterval θ) := by
    nth_rw 1 [← hconcentrated]
    rw [Measure.restrict_restrict
      (P.seamAngularPoint_measurableEmbedding k θ).measurableSet_range, hinter]
  have hrestrict := (P.seamAngularPoint_measurableEmbedding k θ).restrict_comap
    (P.gluedChainSeamLengthMeasure k) univ
  simp only [Measure.restrict_univ, image_univ] at hrestrict
  rw [hrestrict, hsource, P.gluedChainSeamLengthMeasure_restrict_angular_window k θ,
    ← hpush, Measure.comap_smul]
  have hcomp : P.gluedChainSeamAngularChartMap k θ =
      P.seamAngularPoint k θ ∘ Prod.mk zero := by
    funext a
    exact P.gluedChainSeamAngularChartMap_eq_seamAngularPoint k θ a
  rw [hcomp, ← Measure.map_map (P.seamAngularPoint_measurable k θ)
      measurable_prodMk_left,
    (P.seamAngularPoint_measurableEmbedding k θ).comap_map,
    ← Measure.dirac_prod]

theorem seamAngularPoint_not_mem_other_gluedSeamCircle
    (P : ExerciseGluingPreparation C g n genera X) {k l : Fin (n - 1)}
    (hkl : k ≠ l) (θ : ℝ) (p : GluingSeamAngularDomain C g θ) :
    P.seamAngularPoint k θ p ∉ P.gluedSeamCircle l := by
  rintro ⟨z, hz⟩
  have hmem : P.seamAngularPoint k θ p ∈ P.gluedMk '' P.seamNeighborhood k :=
    (P.seamCylinderHomeomorph k (Circle.exp p.2.1, p.1)).2
  rw [← hz] at hmem
  have hpre : P.seamSource l z ∈
      P.gluedMk ⁻¹' (P.gluedMk '' P.seamNeighborhood k) := hmem
  rw [P.preimage_gluedMk_image_seamNeighborhood k] at hpre
  exact hkl ((P.seamSource_mem_seamNeighborhood_iff k l z).mp hpre).symm

theorem gluedChainSeamLengthMeasure_comap_seamAngularPoint_of_ne
    (P : ExerciseGluingPreparation C g n genera X) {k l : Fin (n - 1)}
    (hkl : k ≠ l) (θ : ℝ) :
    (P.gluedChainSeamLengthMeasure l).comap (P.seamAngularPoint k θ) = 0 := by
  ext s _hs
  rw [(P.seamAngularPoint_measurableEmbedding k θ).comap_apply]
  apply le_antisymm _ bot_le
  have hsub : P.seamAngularPoint k θ '' s ⊆ (P.gluedSeamCircle l)ᶜ := by
    rintro y ⟨p, _hp, rfl⟩
    exact P.seamAngularPoint_not_mem_other_gluedSeamCircle hkl θ p
  exact (measure_mono hsub).trans_eq (P.gluedChainSeamLengthMeasure_compl_seam l)

/-- No other native seam contributes to this collar: the complete seam measure has the exact
same radial Dirac density on the literal chart. -/
theorem gluedChainTotalSeamLengthMeasure_comap_seamAngularPoint
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) :
    P.gluedChainTotalSeamLengthMeasure.comap (P.seamAngularPoint k θ) =
      ENNReal.ofReal (Real.sinh (gluingRadius C g)) •
        (Measure.dirac (⟨0, neg_lt_zero.mpr P.depth_pos, P.depth_pos⟩ :
          Ioo (-gluingDepth C g) (gluingDepth C g))).prod
          ((volume : Measure ℝ).comap (Subtype.val : GluingAngularInterval θ → ℝ)) := by
  rw [← P.gluedChainSeamLengthMeasure_comap_seamAngularPoint k θ]
  ext s _hs
  rw [(P.seamAngularPoint_measurableEmbedding k θ).comap_apply,
    (P.seamAngularPoint_measurableEmbedding k θ).comap_apply]
  simp only [gluedChainTotalSeamLengthMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_single k
  · intro l _hl hlk
    have hzero := congrArg (fun μ : Measure (GluingSeamAngularDomain C g θ) => μ s)
      (P.gluedChainSeamLengthMeasure_comap_seamAngularPoint_of_ne hlk.symm θ)
    simpa only [(P.seamAngularPoint_measurableEmbedding k θ).comap_apply,
      Measure.coe_zero, Pi.zero_apply] using hzero
  · simp

#print axioms gluedChainSeamLengthMeasure_eq_turn
#print axioms gluedChainSeamLengthMeasure_comap_angularChart
#print axioms gluedChainSeamAngularChartMap_eq_reflected_incoming
#print axioms seamAngularPoint_measurableEmbedding
#print axioms gluedChainSeamLengthMeasure_comap_seamAngularPoint
#print axioms gluedChainTotalSeamLengthMeasure_comap_seamAngularPoint

end ExerciseGluingPreparation
end
end SystolicGrowth
