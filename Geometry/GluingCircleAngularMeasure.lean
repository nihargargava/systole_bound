module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainSmoothCurvature
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

@[expose] public section

/-!
# Actual circle arclength in local angular coordinates

The one-turn measure used by the native smooth-curvature construction is
the standard length measure on the additive circle, transported by its
genuine homeomorphism to `Circle`.  On every angular interval shorter than
one turn, its pullback is actual Lebesgue measure, with no density premise.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SystolicGrowth

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Every complete positive turn pushes Lebesgue measure to the actual
standard angular length measure. -/
theorem gluingCircleAngularLengthMeasure_eq_turn (a : ℝ) :
    gluingCircleAngularLengthMeasure =
      (volume.restrict (Ioc a (a + 2 * Real.pi))).map Circle.exp := by
  have h (t : ℝ) :
      (volume.restrict (Ioc t (t + 2 * Real.pi))).map Circle.exp =
        (volume : Measure (AddCircle (2 * Real.pi))).map AddCircle.homeomorphCircle' := by
    rw [← (AddCircle.measurePreserving_mk (2 * Real.pi) t).map_eq,
      Measure.map_map AddCircle.homeomorphCircle'.continuous.measurable
        (AddCircle.measurePreserving_mk (2 * Real.pi) t).measurable]
    rfl
  simpa only [gluingCircleAngularLengthMeasure, zero_add] using (h 0).trans (h a).symm

/-- The measure is transported standard circle length, not a chosen
normalization having only the correct total mass. -/
theorem gluingCircleAngularLengthMeasure_eq_addCircle :
    gluingCircleAngularLengthMeasure =
      (volume : Measure (AddCircle (2 * Real.pi))).map AddCircle.homeomorphCircle' := by
  rw [gluingCircleAngularLengthMeasure_eq_turn 0,
    ← (AddCircle.measurePreserving_mk (2 * Real.pi) 0).map_eq,
    Measure.map_map AddCircle.homeomorphCircle'.continuous.measurable
      (AddCircle.measurePreserving_mk (2 * Real.pi) 0).measurable]
  rfl

/-- The genuine angular exponential on an interval shorter than one turn. -/
def gluingCircleIntervalMap (a b : ℝ) (x : Ioo a b) : Circle := Circle.exp x.1

theorem gluingCircleIntervalMap_isOpenEmbedding {a b : ℝ}
    (hwidth : b - a < 2 * Real.pi) :
    Topology.IsOpenEmbedding (gluingCircleIntervalMap a b) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact isLocalHomeomorph_circleExp.continuous.comp continuous_subtype_val
  · intro x y hxy
    exact Subtype.ext (Circle.exp_injOn_Icc hwidth
      (Ioo_subset_Icc_self x.2) (Ioo_subset_Icc_self y.2) hxy)
  · exact isLocalHomeomorph_circleExp.isOpenMap.comp
      isOpen_Ioo.isOpenEmbedding_subtypeVal.isOpenMap

theorem gluingCircleIntervalMap_measurableEmbedding {a b : ℝ}
    (hwidth : b - a < 2 * Real.pi) :
    MeasurableEmbedding (gluingCircleIntervalMap a b) :=
  (gluingCircleIntervalMap_isOpenEmbedding hwidth).measurableEmbedding

theorem gluingCircleIntervalMap_range (a b : ℝ) :
    range (gluingCircleIntervalMap a b) = Circle.exp '' Ioo a b := by
  ext z
  simp only [mem_range, mem_image, gluingCircleIntervalMap]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem gluingCircleAngularLengthMeasure_exp_Ioo_measurable {a b : ℝ}
    (hwidth : b - a < 2 * Real.pi) : MeasurableSet (Circle.exp '' Ioo a b) := by
  rw [← gluingCircleIntervalMap_range]
  exact (gluingCircleIntervalMap_measurableEmbedding hwidth).measurableSet_range

/-- Exact restriction to the real angular window, obtained by using a
complete turn beginning at its left endpoint and genuine exponential
injectivity on that turn. -/
theorem gluingCircleAngularLengthMeasure_restrict_exp_Ioo {a b : ℝ}
    (hwidth : b - a < 2 * Real.pi) :
    gluingCircleAngularLengthMeasure.restrict (Circle.exp '' Ioo a b) =
      (volume.restrict (Ioo a b)).map Circle.exp := by
  have hsub : Ioo a b ⊆ Ioc a (a + 2 * Real.pi) := by
    intro x hx
    exact ⟨hx.1, by linarith [hx.2]⟩
  have hinj : InjOn Circle.exp (Ioc a (a + 2 * Real.pi)) :=
    Circle.exp_injOn_Ioc (by linarith)
  have hpre : (Circle.exp ⁻¹' (Circle.exp '' Ioo a b)) ∩
      Ioc a (a + 2 * Real.pi) = Ioo a b := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, hxy⟩, hx⟩
      have heq := hinj (hsub hy) hx hxy
      simpa only [← heq] using hy
    · intro hx
      exact ⟨⟨x, hx, rfl⟩, hsub hx⟩
  have hs := gluingCircleAngularLengthMeasure_exp_Ioo_measurable hwidth
  rw [gluingCircleAngularLengthMeasure_eq_turn a,
    Measure.restrict_map Circle.exp.continuous.measurable hs,
    Measure.restrict_restrict (Circle.exp.continuous.measurable hs), hpre]

/-- Pullback of actual circle arclength by the true local angular chart
is precisely the original subtype Lebesgue measure. -/
theorem gluingCircleAngularLengthMeasure_comap_interval {a b : ℝ}
    (hwidth : b - a < 2 * Real.pi) :
    gluingCircleAngularLengthMeasure.comap (gluingCircleIntervalMap a b) =
      (volume : Measure ℝ).comap (Subtype.val : Ioo a b → ℝ) := by
  let ν := (volume : Measure ℝ).comap (Subtype.val : Ioo a b → ℝ)
  have hpush : ν.map (gluingCircleIntervalMap a b) =
      (volume.restrict (Ioo a b)).map Circle.exp := by
    change ν.map (Circle.exp ∘ Subtype.val) = _
    rw [← Measure.map_map Circle.exp.continuous.measurable measurable_subtype_coe,
      map_comap_subtype_coe measurableSet_Ioo]
  have hf := gluingCircleIntervalMap_measurableEmbedding hwidth
  have hrestrict := hf.restrict_comap gluingCircleAngularLengthMeasure univ
  simp only [Measure.restrict_univ, image_univ, gluingCircleIntervalMap_range] at hrestrict
  rw [hrestrict, gluingCircleAngularLengthMeasure_restrict_exp_Ioo hwidth,
    ← hpush, hf.comap_map]

theorem gluingCircleAngularLengthMeasure_exp_image_measurable {a b : ℝ}
    (hwidth : b - a < 2 * Real.pi) {s : Set ℝ} (hs : MeasurableSet s)
    (hsub : s ⊆ Ioo a b) : MeasurableSet (Circle.exp '' s) := by
  have himage : gluingCircleIntervalMap a b '' (Subtype.val ⁻¹' s) = Circle.exp '' s := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.1, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hsub hx⟩, hx, rfl⟩
  rw [← himage]
  exact (gluingCircleIntervalMap_measurableEmbedding hwidth).measurableSet_image.mpr
    (measurable_subtype_coe hs)

/-- Every subset of a true local angular interval has exactly its ordinary
real Lebesgue length, not only the whole interval's length. -/
theorem gluingCircleAngularLengthMeasure_exp_image {a b : ℝ}
    (hwidth : b - a < 2 * Real.pi) {s : Set ℝ}
    (hsub : s ⊆ Ioo a b) :
    gluingCircleAngularLengthMeasure (Circle.exp '' s) = volume s := by
  let t : Set (Ioo a b) := Subtype.val ⁻¹' s
  have himage : gluingCircleIntervalMap a b '' t = Circle.exp '' s := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.1, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hsub hx⟩, hx, rfl⟩
  have hreal : Subtype.val '' t = s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hsub hx⟩, hx, rfl⟩
  rw [← himage, ← (gluingCircleIntervalMap_measurableEmbedding hwidth).comap_apply
    gluingCircleAngularLengthMeasure t,
    gluingCircleAngularLengthMeasure_comap_interval hwidth,
    comap_subtype_coe_apply measurableSet_Ioo volume t, hreal]

/-- The original native collar angular chart has literal arclength
Lebesgue measure on its unchanged width-`π` interval. -/
theorem gluingCircleAngularLengthMeasure_comap_angularInterval (θ : ℝ) :
    gluingCircleAngularLengthMeasure.comap (gluingAngularIntervalMap θ) =
      (volume : Measure ℝ).comap (Subtype.val : GluingAngularInterval θ → ℝ) := by
  exact gluingCircleAngularLengthMeasure_comap_interval (by linarith [Real.pi_pos])

/-- Product pullbacks through genuine measurable embeddings are the product
of the pullbacks. The sigma-finiteness hypotheses concern the actual
restricted measures, rather than any asserted measure identity. -/
theorem gluingMeasure_comap_prodMap {α β γ κ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace κ]
    {f : α → β} {g : γ → κ} (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g)
    (μ : Measure β) (ν : Measure κ) [SFinite μ] [SFinite ν]
    [SigmaFinite (μ.comap f)] [SigmaFinite (ν.comap g)] :
    (μ.prod ν).comap (Prod.map f g) = (μ.comap f).prod (ν.comap g) := by
  symm
  apply Measure.prod_eq
  intro s t hs ht
  rw [(hf.prodMap hg).comap_apply, Set.prodMap_image_prod, Measure.prod_prod,
    hf.comap_apply, hg.comap_apply]

/-- A density pulls back by composition under an actual measurable
embedding. This statement does not require measurability of the density. -/
theorem gluingMeasure_comap_withDensity {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {f : α → β}
    (hf : MeasurableEmbedding f) (μ : Measure β) (w : β → ℝ≥0∞) :
    (μ.withDensity w).comap f = (μ.comap f).withDensity (w ∘ f) := by
  ext s hs
  rw [hf.comap_apply, withDensity_apply _ (hf.measurableSet_image.mpr hs),
    withDensity_apply _ hs, hf.restrict_comap]
  change (∫⁻ a in f '' s, w a ∂μ) =
    ∫⁻ a, w (f a) ∂(μ.restrict (f '' s)).comap f
  rw [← hf.lintegral_map w,
    hf.map_comap, Measure.restrict_restrict hf.measurableSet_range,
    inter_eq_right.mpr (image_subset_range f s)]

/-- The unchanged real seam angular coordinates restricted to a thin
radial window. The angular and radial coordinates are swapped only to match
the native cylinder's `Circle × radius` ordering. -/
def gluingThinAngularCylinderMap (δ θ : ℝ)
    (p : Ioo (-δ) δ × GluingAngularInterval θ) : Circle × Ioo (-δ) δ :=
  (gluingAngularIntervalMap θ p.2, p.1)

theorem gluingThinAngularCylinderMap_isOpenEmbedding (δ θ : ℝ) :
    Topology.IsOpenEmbedding (gluingThinAngularCylinderMap δ θ) := by
  exact ((gluingAngularIntervalMap_isOpenEmbedding θ).prodMap
    (Topology.IsOpenEmbedding.id (X := Ioo (-δ) δ))).comp
      (Homeomorph.prodComm _ _).isOpenEmbedding

theorem gluingThinAngularCylinderMap_measurableEmbedding (δ θ : ℝ) :
    MeasurableEmbedding (gluingThinAngularCylinderMap δ θ) :=
  (gluingThinAngularCylinderMap_isOpenEmbedding δ θ).measurableEmbedding

/-- Actual cylinder coordinates pull back to radial and angular Lebesgue
measure on the original two subtype intervals. -/
theorem gluingThinCylinderCoordinateMeasure_comap_angular (δ θ : ℝ) :
    (gluingThinCylinderCoordinateMeasure δ).comap (gluingThinAngularCylinderMap δ θ) =
      ((volume : Measure ℝ).comap (Subtype.val : Ioo (-δ) δ → ℝ)).prod
        ((volume : Measure ℝ).comap (Subtype.val : GluingAngularInterval θ → ℝ)) := by
  letI : IsFiniteMeasure
      ((volume : Measure ℝ).comap (Subtype.val : GluingAngularInterval θ → ℝ)) := by
    rw [← gluingCircleAngularLengthMeasure_comap_angularInterval θ]
    infer_instance
  letI : IsFiniteMeasure ((volume : Measure ℝ).comap
      (Subtype.val : Ioo (-δ) δ → ℝ)) :=
    inferInstanceAs (IsFiniteMeasure (gluingThinRadialMeasure δ))
  have hswap : MeasurableEmbedding
      (Prod.swap : Ioo (-δ) δ × GluingAngularInterval θ →
        GluingAngularInterval θ × Ioo (-δ) δ) :=
    (Homeomorph.prodComm _ _).measurableEmbedding
  have hid : MeasurableEmbedding (fun x : Ioo (-δ) δ => x) :=
    MeasurableEmbedding.id
  have hmap : MeasurableEmbedding
      (Prod.map (gluingAngularIntervalMap θ) (fun x : Ioo (-δ) δ => x)) :=
    (gluingAngularIntervalMap_isOpenEmbedding θ).measurableEmbedding.prodMap hid
  change (gluingCircleAngularLengthMeasure.prod (gluingThinRadialMeasure δ)).comap
    ((Prod.map (gluingAngularIntervalMap θ) (fun x => x)) ∘ Prod.swap) = _
  rw [← Measure.comap_comap hswap.measurableSet_image' hmap.injective
    hmap.measurableSet_image',
    gluingMeasure_comap_prodMap
      (gluingAngularIntervalMap_isOpenEmbedding θ).measurableEmbedding
      hid,
    gluingCircleAngularLengthMeasure_comap_angularInterval, Measure.comap_id,
    Measure.comap_swap, Measure.prod_swap]
  rfl

/-- The actual smooth cylinder area has precisely the localized warped
metric determinant density in the original radial/angular chart. -/
theorem gluingThinCylinderArea_comap_angular (r ε : ℝ) (b : ContDiffBump (0 : ℝ))
    (δ θ : ℝ) :
    (gluingThinCylinderArea r ε b δ).comap (gluingThinAngularCylinderMap δ θ) =
      ((((volume : Measure ℝ).comap (Subtype.val : Ioo (-δ) δ → ℝ)).prod
        ((volume : Measure ℝ).comap (Subtype.val : GluingAngularInterval θ → ℝ))).withDensity
        (fun p => ENNReal.ofReal (gluingCollarLocalizedSmoothWarp r ε b p.1.1))) := by
  rw [gluingThinCylinderArea,
    gluingMeasure_comap_withDensity (gluingThinAngularCylinderMap_measurableEmbedding δ θ),
    gluingThinCylinderCoordinateMeasure_comap_angular]
  rfl

#print axioms gluingCircleAngularLengthMeasure_eq_addCircle
#print axioms gluingCircleAngularLengthMeasure_restrict_exp_Ioo
#print axioms gluingCircleAngularLengthMeasure_comap_interval
#print axioms gluingCircleAngularLengthMeasure_exp_image
#print axioms gluingCircleAngularLengthMeasure_comap_angularInterval
#print axioms gluingMeasure_comap_prodMap
#print axioms gluingMeasure_comap_withDensity
#print axioms gluingThinAngularCylinderMap_isOpenEmbedding
#print axioms gluingThinCylinderCoordinateMeasure_comap_angular
#print axioms gluingThinCylinderArea_comap_angular

end
end SystolicGrowth
