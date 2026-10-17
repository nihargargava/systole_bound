module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.NormedPunctureRadialRetraction
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

@[expose] public section

/-!
# Retraction outside an embedded coordinate disk

An open coordinate chart containing the closed unit ball lets the normed
radial push extend by the identity to the ambient space. Properness makes the
region on which the formula can change compact, so this extension is
continuous even when the chart image is not closed.
-/

open Set
open scoped unitInterval ContinuousMap

namespace SystolicGrowth

noncomputable section

/-- Actual homotopy tracks transport path connectivity across a homotopy
equivalence, without assuming either map is surjective. -/
theorem pathConnectedSpace_of_homotopyEquiv {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [PathConnectedSpace B]
    (e : A ≃ₕ B) : PathConnectedSpace A := by
  obtain ⟨H⟩ := e.left_inv
  refine ⟨⟨e.invFun (Classical.choice (PathConnectedSpace.nonempty : Nonempty B))⟩,
    fun x y => ?_⟩
  exact ⟨(H.evalAt x).symm.trans
    (((PathConnectedSpace.somePath (e x) (e y)).map e.invFun.continuous).trans
      (H.evalAt y))⟩

variable {α E : Type*} [TopologicalSpace α] [T2Space α]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  {U : Set E}
  (hball : Metric.closedBall (0 : E) 1 ⊆ U)
  (f : C(U, α)) (hf : Topology.IsOpenEmbedding (f : U → α))

/-- The origin as a point of the chart domain. -/
def embeddedCoordinatePunctureOrigin : U := ⟨0, hball (by simp)⟩

/-- The center removed from the ambient space. -/
def embeddedCoordinatePunctureCenter : α := f (embeddedCoordinatePunctureOrigin hball)

/-- The open coordinate disk deleted by the puncture construction. -/
def embeddedCoordinatePunctureDisk : Set α :=
  f '' {x : U | ‖(x : E)‖ < 1}

/-- The compact image of the closed coordinate unit disk. -/
def embeddedCoordinatePunctureClosedDisk : Set α :=
  (fun x : Metric.closedBall (0 : E) 1 => f ⟨x.1, hball x.2⟩) '' Set.univ

omit [T2Space α] [NormedSpace ℝ E] in
theorem embeddedCoordinatePunctureClosedDisk_isCompact :
    IsCompact (embeddedCoordinatePunctureClosedDisk hball f) := by
  letI : CompactSpace (Metric.closedBall (0 : E) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E) 1)
  exact isCompact_univ.image (f.continuous.comp <|
    continuous_subtype_val.subtype_mk (fun x => hball x.2))

omit [T2Space α] [NormedSpace ℝ E] [ProperSpace E] in
theorem embeddedCoordinatePunctureClosedDisk_subset_range :
    embeddedCoordinatePunctureClosedDisk hball f ⊆ Set.range (f : U → α) := by
  rintro y ⟨x, -, rfl⟩
  exact ⟨⟨x.1, hball x.2⟩, rfl⟩

omit [T2Space α] [NormedSpace ℝ E] [ProperSpace E] in
theorem embeddedCoordinatePunctureDisk_subset_closedDisk :
    embeddedCoordinatePunctureDisk f ⊆ embeddedCoordinatePunctureClosedDisk hball f := by
  rintro y ⟨x, hx, rfl⟩
  refine ⟨⟨x.1, ?_⟩, Set.mem_univ _, ?_⟩
  · exact Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using le_of_lt hx)
  rfl

noncomputable def Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureChartHomeomorph (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) : U ≃ₜ Set.range (f : U → α) :=
  hf.isEmbedding.toHomeomorph

omit [T2Space α] [NormedSpace ℝ E] [ProperSpace E] in
private theorem embeddedCoordinatePuncture_chart_apply (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) (x : U) :
    Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureChartHomeomorph f hf x = ⟨f x, ⟨x, rfl⟩⟩ := by
  rfl

omit [T2Space α] [NormedSpace ℝ E] [ProperSpace E] in
private theorem embeddedCoordinatePuncture_chart_symm_apply (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) (y : Set.range (f : U → α)) :
    f ((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureChartHomeomorph f hf).symm y) = y.1 := by
  exact congrArg Subtype.val
    ((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureChartHomeomorph f hf).apply_symm_apply y)

omit [T2Space α] [NormedSpace ℝ E] [ProperSpace E] in
private theorem embeddedCoordinatePuncture_chart_coord_mem_closedBall
    (y : Set.range (f : U → α))
    (hy : y.1 ∉ embeddedCoordinatePunctureClosedDisk hball f) :
    1 < ‖((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureChartHomeomorph f hf).symm y : E)‖ := by
  by_contra hlt
  have hle : ‖((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureChartHomeomorph f hf).symm y : E)‖ ≤ 1 :=
    le_of_not_gt hlt
  have hmem : ((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureChartHomeomorph f hf).symm y).1 ∈
      Metric.closedBall (0 : E) 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hle
  apply hy
  refine ⟨⟨((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureChartHomeomorph f hf).symm y).1,
    hmem⟩, Set.mem_univ _, ?_⟩
  change f ⟨((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureChartHomeomorph f hf).symm y).1,
    hball hmem⟩ = y.1
  have hx : (⟨((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureChartHomeomorph f hf).symm y).1,
      hball hmem⟩ : U) = (Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureChartHomeomorph f hf).symm y :=
    Subtype.ext rfl
  rw [hx]
  exact embeddedCoordinatePuncture_chart_symm_apply f hf y

omit [ProperSpace E] in
theorem Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncture_radial_mem_domain
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (t : I) (x : U)
    (hx : (x : E) ≠ 0) : normPunctureRadialPush t (x : E) ∈ U := by
  by_cases hnorm : ‖(x : E)‖ ≤ 1
  · apply hball
    simpa [Metric.mem_closedBall, dist_eq_norm] using
      normPunctureRadialPush_norm_le_one t hx hnorm
  · rw [normPunctureRadialPush_fixed t (le_of_not_ge hnorm)]
    exact x.2

/-- The outward radial point in the same actual chart domain. -/
def embeddedCoordinatePunctureRadialPoint
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (t : I) (x : U)
    (hx : (x : E) ≠ 0) : U :=
  ⟨normPunctureRadialPush t (x : E),
    Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncture_radial_mem_domain hball t x hx⟩

abbrev Internal.EmbeddedCoordinatePunctureRetractionHelpers.EmbeddedCoordinatePuncturePoint
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α)) :=
  {y : {y : α // y ≠ embeddedCoordinatePunctureCenter hball f} //
    y.1 ∈ Set.range (f : U → α)}

omit [T2Space α] [NormedSpace ℝ E] [ProperSpace E] in
theorem Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncture_localCoord_ne_zero
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α))
    (y : Internal.EmbeddedCoordinatePunctureRetractionHelpers.EmbeddedCoordinatePuncturePoint hball f) :
    (((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureChartHomeomorph f hf).symm
      ⟨y.1.1, y.2⟩ : U) : E) ≠ 0 := by
  intro hz
  apply y.1.2
  have hchart := embeddedCoordinatePuncture_chart_symm_apply f hf ⟨y.1.1, y.2⟩
  calc
    y.1.1 = f ((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureChartHomeomorph f hf).symm
        ⟨y.1.1, y.2⟩) := hchart.symm
    _ = f (embeddedCoordinatePunctureOrigin hball) :=
      congrArg f (Subtype.ext hz)
    _ = embeddedCoordinatePunctureCenter hball f := rfl

def Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalPointToRange
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (y : Internal.EmbeddedCoordinatePunctureRetractionHelpers.EmbeddedCoordinatePuncturePoint hball f) : Set.range (f : U → α) :=
  ⟨y.1.1, y.2⟩

omit [T2Space α] [NormedSpace ℝ E] [ProperSpace E] in
private theorem embeddedCoordinatePunctureLocalPointToRange_continuous :
    Continuous (Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalPointToRange hball f) := by
  change Continuous (fun y : Internal.EmbeddedCoordinatePunctureRetractionHelpers.EmbeddedCoordinatePuncturePoint hball f =>
    (⟨y.1.1, y.2⟩ : Set.range (f : U → α)))
  have hval : Continuous (fun y : Internal.EmbeddedCoordinatePunctureRetractionHelpers.EmbeddedCoordinatePuncturePoint hball f => y.1.1) :=
    continuous_subtype_val.comp continuous_subtype_val
  exact hval.subtype_mk (fun y => y.2)

def Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α))
    (y : Internal.EmbeddedCoordinatePunctureRetractionHelpers.EmbeddedCoordinatePuncturePoint hball f) : {x : U // (x : E) ≠ 0} :=
  ⟨(Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureChartHomeomorph f hf).symm
      (Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalPointToRange hball f y),
    Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncture_localCoord_ne_zero hball f hf y⟩

omit [T2Space α] [NormedSpace ℝ E] [ProperSpace E] in
theorem Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate_continuous :
    Continuous (Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf) := by
  exact ((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureChartHomeomorph f hf).symm.continuous.comp
    (embeddedCoordinatePunctureLocalPointToRange_continuous hball f)).subtype_mk _

def Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalPush
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) :
    C(I × Internal.EmbeddedCoordinatePunctureRetractionHelpers.EmbeddedCoordinatePuncturePoint hball f, α) where
  toFun p := f ⟨normPunctureRadialPush p.1
    ((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf p.2).1 : E),
    Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncture_radial_mem_domain hball p.1
      (Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf p.2).1
      (Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf p.2).2⟩
  continuous_toFun := by
    let hcoord : Continuous (fun p : I × Internal.EmbeddedCoordinatePunctureRetractionHelpers.EmbeddedCoordinatePuncturePoint hball f =>
        (p.1, (⟨((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf p.2).1 : E),
          (Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf p.2).2⟩ :
            {x : E // x ≠ 0}))) := by
      let hcoordU : Continuous (fun p : I × Internal.EmbeddedCoordinatePunctureRetractionHelpers.EmbeddedCoordinatePuncturePoint hball f =>
          Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf p.2) :=
        (Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate_continuous hball f hf).comp continuous_snd
      let hval : Continuous (fun p : I × Internal.EmbeddedCoordinatePunctureRetractionHelpers.EmbeddedCoordinatePuncturePoint hball f =>
          ((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf p.2).1 : E)) :=
        continuous_subtype_val.comp (continuous_subtype_val.comp hcoordU)
      let hpunct : Continuous (fun p : I × Internal.EmbeddedCoordinatePunctureRetractionHelpers.EmbeddedCoordinatePuncturePoint hball f =>
          (⟨((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf p.2).1 : E),
            (Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf p.2).2⟩ :
              {x : E // x ≠ 0})) := hval.subtype_mk _
      exact continuous_fst.prodMk hpunct
    let hradial : Continuous (fun p : I × Internal.EmbeddedCoordinatePunctureRetractionHelpers.EmbeddedCoordinatePuncturePoint hball f =>
        normPunctureRadialPush p.1
          ((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf p.2).1 : E)) :=
      normPunctureRadialPush_continuous.comp hcoord
    exact f.continuous.comp <| hradial.subtype_mk (fun p =>
      Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncture_radial_mem_domain hball p.1
        (Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf p.2).1
        (Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf p.2).2)

omit [T2Space α] [ProperSpace E] in
private theorem embeddedCoordinatePunctureLocalPush_fixed
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) (t : I)
    (y : Internal.EmbeddedCoordinatePunctureRetractionHelpers.EmbeddedCoordinatePuncturePoint hball f)
    (hnorm : 1 ≤ ‖((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf y).1 : E)‖) :
    Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalPush hball f hf (t, y) =
      f (Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf y).1 := by
  change f ⟨normPunctureRadialPush t
      ((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf y).1 : E), _⟩ = _
  have hu : (⟨normPunctureRadialPush t
      ((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf y).1 : E),
      Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncture_radial_mem_domain hball t
        (Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf y).1
        (Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf y).2⟩ : U) =
      (Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf y).1 := by
    apply Subtype.ext
    exact normPunctureRadialPush_fixed t hnorm
  rw [hu]

omit [T2Space α] [ProperSpace E] in
private theorem embeddedCoordinatePunctureLocalPush_zero
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α))
    (y : Internal.EmbeddedCoordinatePunctureRetractionHelpers.EmbeddedCoordinatePuncturePoint hball f) :
    Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalPush hball f hf (0, y) =
      f (Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf y).1 := by
  change f ⟨normPunctureRadialPush 0
      ((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf y).1 : E), _⟩ = _
  have hu : (⟨normPunctureRadialPush 0
      ((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf y).1 : E),
      Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncture_radial_mem_domain hball 0
        (Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf y).1
        (Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf y).2⟩ : U) =
      (Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf y).1 := by
    apply Subtype.ext
    exact normPunctureRadialPush_zero _
  rw [hu]

/-- The ambient push, defined by the chart formula on its open range and by
the identity off that range. -/
noncomputable def embeddedCoordinatePuncturePushValue
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) (t : I)
    (y : {y : α // y ≠ embeddedCoordinatePunctureCenter hball f}) : α := by
  classical
  exact if hy : y.1 ∈ Set.range (f : U → α) then
      Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalPush hball f hf (t, ⟨y, hy⟩)
    else y.1

omit [T2Space α] [ProperSpace E] in
/-- On the actual chart, the ambient extension is the literal radial
coordinate formula. This permits restriction to smaller-disk exteriors. -/
theorem embeddedCoordinatePuncturePushValue_chart
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) (t : I)
    (y : {y : α // y ≠ embeddedCoordinatePunctureCenter hball f})
    (z : U) (hz : (z : E) ≠ 0) (hy : y.1 = f z) :
    embeddedCoordinatePuncturePushValue hball f hf t y =
      f (embeddedCoordinatePunctureRadialPoint hball t z hz) := by
  classical
  have hrange : y.1 ∈ Set.range (f : U → α) := ⟨z, hy.symm⟩
  let p : Internal.EmbeddedCoordinatePunctureRetractionHelpers.EmbeddedCoordinatePuncturePoint hball f := ⟨y, hrange⟩
  have hcoord : (Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf p).1 = z := by
    apply hf.injective
    exact (embeddedCoordinatePuncture_chart_symm_apply f hf ⟨y.1, hrange⟩).trans hy
  rw [embeddedCoordinatePuncturePushValue, dif_pos hrange]
  change f ⟨normPunctureRadialPush t
    ((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf p).1 : E), _⟩ = _
  apply congrArg f
  apply Subtype.ext
  exact congrArg (normPunctureRadialPush t) (congrArg Subtype.val hcoord)

omit [T2Space α] [ProperSpace E] in
/-- The ambient radial push preserves the complement of every smaller
closed coordinate disk. Thus it restricts to the genuine open exterior
member of the two-puncture cover. -/
theorem embeddedCoordinatePuncturePushValue_preserves_closedDiskExterior
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) (a : ℝ) (t : I)
    (y : {y : α // y ≠ embeddedCoordinatePunctureCenter hball f})
    (hy : y.1 ∉ f '' {z : U | ‖(z : E)‖ ≤ a}) :
    embeddedCoordinatePuncturePushValue hball f hf t y ∉
      f '' {z : U | ‖(z : E)‖ ≤ a} := by
  classical
  by_cases hrange : y.1 ∈ Set.range (f : U → α)
  · obtain ⟨z, hz⟩ := hrange
    have hz0 : (z : E) ≠ 0 := by
      intro hz0
      apply y.2
      rw [← hz]
      exact congrArg f (Subtype.ext hz0)
    have haz : a < ‖(z : E)‖ := by
      by_contra hnot
      exact hy ⟨z, le_of_not_gt hnot, hz⟩
    rw [embeddedCoordinatePuncturePushValue_chart hball f hf t y z hz0 hz.symm]
    rintro ⟨w, hw, hweq⟩
    have hwz := hf.injective hweq
    change ‖(w : E)‖ ≤ a at hw
    rw [hwz] at hw
    exact (not_lt_of_ge hw)
      (haz.trans_le (norm_le_normPunctureRadialPush t hz0))
  · rw [embeddedCoordinatePuncturePushValue, dif_neg hrange]
    exact hy

omit [T2Space α] [ProperSpace E] in
theorem Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncturePushValue_ne_center
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) (t : I)
    (y : {y : α // y ≠ embeddedCoordinatePunctureCenter hball f}) :
    embeddedCoordinatePuncturePushValue hball f hf t y ≠
      embeddedCoordinatePunctureCenter hball f := by
  classical
  by_cases hy : y.1 ∈ Set.range (f : U → α)
  · let z : Internal.EmbeddedCoordinatePunctureRetractionHelpers.EmbeddedCoordinatePuncturePoint hball f := ⟨y, hy⟩
    simp only [embeddedCoordinatePuncturePushValue, dif_pos hy,
      Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalPush]
    change f ⟨normPunctureRadialPush t
      ((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf z).1 : E), _⟩ ≠
      f (embeddedCoordinatePunctureOrigin hball)
    intro heq
    have hradial := normPunctureRadialPush_ne_zero t
      (Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncture_localCoord_ne_zero hball f hf z)
    have heqval := congrArg (fun x : U => (x : E)) (hf.injective heq)
    have hz : normPunctureRadialPush t
        ((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf z).1 : E) = 0 := by
      simpa [embeddedCoordinatePunctureOrigin] using heqval
    exact hradial hz
  · simpa only [embeddedCoordinatePuncturePushValue, dif_neg hy] using y.2

omit [T2Space α] [ProperSpace E] in
theorem Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncturePushValue_fixed_of_not_disk
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) (t : I)
    (y : {y : α // y ≠ embeddedCoordinatePunctureCenter hball f})
    (hy : y.1 ∉ embeddedCoordinatePunctureDisk f) :
    embeddedCoordinatePuncturePushValue hball f hf t y = y.1 := by
  classical
  by_cases hrange : y.1 ∈ Set.range (f : U → α)
  · let z : Set.range (f : U → α) := ⟨y.1, hrange⟩
    let p : Internal.EmbeddedCoordinatePunctureRetractionHelpers.EmbeddedCoordinatePuncturePoint hball f := ⟨y, hrange⟩
    have hnorm : 1 ≤ ‖((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf p).1 : E)‖ := by
      by_contra hn
      have hlt : ‖((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf p).1 : E)‖ < 1 :=
        lt_of_not_ge hn
      apply hy
      refine ⟨(Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf p).1, hlt, ?_⟩
      simpa [p, Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate,
        Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalPointToRange] using
        embeddedCoordinatePuncture_chart_symm_apply f hf z
    rw [embeddedCoordinatePuncturePushValue, dif_pos hrange]
    rw [embeddedCoordinatePunctureLocalPush_fixed hball f hf t p hnorm]
    exact embeddedCoordinatePuncture_chart_symm_apply f hf z
  · simp [embeddedCoordinatePuncturePushValue, hrange]

omit [T2Space α] [ProperSpace E] in
theorem Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncturePushValue_zero
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α))
    (y : {y : α // y ≠ embeddedCoordinatePunctureCenter hball f}) :
    embeddedCoordinatePuncturePushValue hball f hf 0 y = y.1 := by
  classical
  by_cases hrange : y.1 ∈ Set.range (f : U → α)
  · let z : Set.range (f : U → α) := ⟨y.1, hrange⟩
    let p : Internal.EmbeddedCoordinatePunctureRetractionHelpers.EmbeddedCoordinatePuncturePoint hball f := ⟨y, hrange⟩
    rw [embeddedCoordinatePuncturePushValue, dif_pos hrange,
      embeddedCoordinatePunctureLocalPush_zero]
    exact embeddedCoordinatePuncture_chart_symm_apply f hf z
  · simp [embeddedCoordinatePuncturePushValue, hrange]

omit [T2Space α] [ProperSpace E] in
theorem Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncturePushValue_one_avoids_disk
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α))
    (y : {y : α // y ≠ embeddedCoordinatePunctureCenter hball f}) :
    embeddedCoordinatePuncturePushValue hball f hf 1 y ∉
      embeddedCoordinatePunctureDisk f := by
  classical
  by_cases hrange : y.1 ∈ Set.range (f : U → α)
  · let p : Internal.EmbeddedCoordinatePunctureRetractionHelpers.EmbeddedCoordinatePuncturePoint hball f := ⟨y, hrange⟩
    have hnorm := one_le_normPunctureRadialPush_one
      (Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncture_localCoord_ne_zero hball f hf p)
    intro hmem
    rw [embeddedCoordinatePuncturePushValue, dif_pos hrange] at hmem
    rcases hmem with ⟨x, hx, hfx⟩
    change ‖(x : E)‖ < 1 at hx
    change f x = f ⟨normPunctureRadialPush 1
      ((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf p).1 : E), _⟩ at hfx
    have hxEq := hf.injective hfx
    have hnormlt : ‖normPunctureRadialPush 1
        ((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalCoordinate hball f hf p).1 : E)‖ < 1 := by
      simpa only [hxEq] using hx
    exact (not_lt_of_ge hnorm) hnormlt
  · intro hmem
    rw [embeddedCoordinatePuncturePushValue, dif_neg hrange] at hmem
    rcases hmem with ⟨x, _, hfx⟩
    exact hrange ⟨x, hfx⟩

theorem Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncturePushValue_continuous
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) :
    Continuous (fun p : I × {y : α // y ≠ embeddedCoordinatePunctureCenter hball f} =>
      embeddedCoordinatePuncturePushValue hball f hf p.1 p.2) := by
  classical
  let D := I × {y : α // y ≠ embeddedCoordinatePunctureCenter hball f}
  let g : D → α := fun p => embeddedCoordinatePuncturePushValue hball f hf p.1 p.2
  let S : Set D := {p | p.2.1 ∈ Set.range (f : U → α)}
  let T : Set D := {p | p.2.1 ∉ embeddedCoordinatePunctureClosedDisk hball f}
  have hproj : Continuous (fun p : D => p.2.1) :=
    continuous_subtype_val.comp continuous_snd
  have hS : IsOpen S := by
    exact hf.isOpen_range.preimage hproj
  have hclosed : IsClosed (embeddedCoordinatePunctureClosedDisk hball f) :=
    (embeddedCoordinatePunctureClosedDisk_isCompact hball f).isClosed
  have hT : IsOpen T := hclosed.isOpen_compl.preimage hproj
  have hcover : S ∪ T = Set.univ := by
    ext p
    constructor
    · intro _
      simp
    · intro _
      by_cases hp : p.2.1 ∈ embeddedCoordinatePunctureClosedDisk hball f
      · left
        exact embeddedCoordinatePunctureClosedDisk_subset_range hball f hp
      · exact Or.inr hp
  have hScont : ContinuousOn g S := by
    rw [continuousOn_iff_continuous_restrict]
    let hfirst : Continuous (fun p : S => p.1.1) :=
      continuous_fst.comp continuous_subtype_val
    let hcarrier : Continuous (fun p : S => p.1.2) :=
      continuous_snd.comp continuous_subtype_val
    let hpoint : Continuous (fun p : S =>
        (⟨p.1.2, p.2⟩ : Internal.EmbeddedCoordinatePunctureRetractionHelpers.EmbeddedCoordinatePuncturePoint hball f)) :=
      hcarrier.subtype_mk (fun p => p.2)
    let φ : S → I × Internal.EmbeddedCoordinatePunctureRetractionHelpers.EmbeddedCoordinatePuncturePoint hball f := fun p =>
      (p.1.1, ⟨p.1.2, p.2⟩)
    have hmap : Continuous φ := hfirst.prodMk hpoint
    have hlocal : Continuous (fun p : S =>
        Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalPush hball f hf (φ p)) :=
      (Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalPush hball f hf).continuous.comp hmap
    apply hlocal.congr
    intro p
    have hp : p.1.2.1 ∈ Set.range (f : U → α) := p.2
    change Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureLocalPush hball f hf (φ p) = g p.1
    simp only [g, embeddedCoordinatePuncturePushValue, dif_pos hp, φ]
  have hTcont : ContinuousOn g T := by
    apply hproj.continuousOn.congr
    intro p hp
    dsimp [g, T]
    exact Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncturePushValue_fixed_of_not_disk hball f hf p.1 p.2
      (fun hd => hp (embeddedCoordinatePunctureDisk_subset_closedDisk hball f hd))
  have hglobal : ContinuousOn g (S ∪ T) := hScont.union_of_isOpen hTcont hS hT
  rw [hcover] at hglobal
  exact continuousOn_univ.mp hglobal

/-- The ambient radial homotopy as an actual continuous map into the
punctured space. -/
def embeddedCoordinatePuncturePushMap
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) :
    C(I × {y : α // y ≠ embeddedCoordinatePunctureCenter hball f},
      {y : α // y ≠ embeddedCoordinatePunctureCenter hball f}) where
  toFun p := ⟨embeddedCoordinatePuncturePushValue hball f hf p.1 p.2,
    Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncturePushValue_ne_center hball f hf p.1 p.2⟩
  continuous_toFun :=
    (Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncturePushValue_continuous hball f hf).subtype_mk _

/-- The open coordinate disk as an ambient subset of the chart. -/
abbrev embeddedCoordinatePunctureExterior (f : C(U, α)) :=
  {y : α // y ∉ embeddedCoordinatePunctureDisk f}

omit [T2Space α] [NormedSpace ℝ E] [ProperSpace E] in
theorem Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureCenter_mem_disk
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α)) :
    embeddedCoordinatePunctureCenter hball f ∈ embeddedCoordinatePunctureDisk f := by
  refine ⟨embeddedCoordinatePunctureOrigin hball, ?_, rfl⟩
  simp [embeddedCoordinatePunctureOrigin]

/-- Inclusion of the complement of the open coordinate disk into the
center-punctured ambient space. -/
def embeddedCoordinatePunctureInclusion
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α)) :
    C(embeddedCoordinatePunctureExterior f,
      {y : α // y ≠ embeddedCoordinatePunctureCenter hball f}) where
  toFun y := ⟨y.1, fun hy => y.2 (hy ▸ Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePunctureCenter_mem_disk hball f)⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Retraction onto the complement of the open coordinate disk, obtained by
the terminal ambient push. -/
def embeddedCoordinatePunctureRetraction
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) :
    C({y : α // y ≠ embeddedCoordinatePunctureCenter hball f},
      embeddedCoordinatePunctureExterior f) where
  toFun y := ⟨embeddedCoordinatePuncturePushValue hball f hf 1 y,
    Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncturePushValue_one_avoids_disk hball f hf y⟩
  continuous_toFun :=
    ((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncturePushValue_continuous hball f hf).comp
      (continuous_const.prodMk continuous_id)).subtype_mk _

@[simp]
theorem embeddedCoordinatePunctureRetraction_inclusion
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α))
    (y : embeddedCoordinatePunctureExterior f) :
    embeddedCoordinatePunctureRetraction hball f hf
      (embeddedCoordinatePunctureInclusion hball f y) = y := by
  apply Subtype.ext
  exact Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncturePushValue_fixed_of_not_disk hball f hf 1
    (embeddedCoordinatePunctureInclusion hball f y) y.2

/-- The coordinate deformation fixes every exterior point at every time; in
particular, every loop carried by the exterior is fixed pointwise. -/
theorem embeddedCoordinatePuncturePushMap_fixedOn_exterior
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) (t : I)
    (y : embeddedCoordinatePunctureExterior f) :
    embeddedCoordinatePuncturePushMap hball f hf
      (t, embeddedCoordinatePunctureInclusion hball f y) =
      embeddedCoordinatePunctureInclusion hball f y := by
  apply Subtype.ext
  exact Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncturePushValue_fixed_of_not_disk hball f hf t
    (embeddedCoordinatePunctureInclusion hball f y) y.2

/-- A genuine strong deformation retraction, relative to the complete
exterior of the embedded open disk. -/
def embeddedCoordinatePunctureDeformationRetraction
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) :
    (ContinuousMap.id {y : α // y ≠ embeddedCoordinatePunctureCenter hball f}).HomotopyRel
      ((embeddedCoordinatePunctureInclusion hball f).comp
        (embeddedCoordinatePunctureRetraction hball f hf))
      {y | y.1 ∉ embeddedCoordinatePunctureDisk f} where
  toHomotopy :=
    { toContinuousMap := embeddedCoordinatePuncturePushMap hball f hf
      map_zero_left := fun y => by
        apply Subtype.ext
        exact Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncturePushValue_zero hball f hf y
      map_one_left := fun _ => rfl }
  prop' := fun t y hy => by
    apply Subtype.ext
    exact Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncturePushValue_fixed_of_not_disk hball f hf t y hy

/-- The literal disk exterior and center-punctured ambient space are
homotopy equivalent through the constructed inclusion and radial push. -/
def embeddedCoordinatePunctureHomotopyEquiv
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) :
    embeddedCoordinatePunctureExterior f ≃ₕ
      {y : α // y ≠ embeddedCoordinatePunctureCenter hball f} where
  toFun := embeddedCoordinatePunctureInclusion hball f
  invFun := embeddedCoordinatePunctureRetraction hball f hf
  left_inv := by
    have h : (embeddedCoordinatePunctureRetraction hball f hf).comp
        (embeddedCoordinatePunctureInclusion hball f) =
          ContinuousMap.id (embeddedCoordinatePunctureExterior f) := by
      apply ContinuousMap.ext
      intro y
      exact embeddedCoordinatePunctureRetraction_inclusion hball f hf y
    rw [h]
  right_inv := ⟨(embeddedCoordinatePunctureDeformationRetraction hball f hf).toHomotopy.symm⟩

/-- At each unchanged exterior basepoint, the actual inclusion induces a
genuine fundamental-group equivalence. -/
def embeddedCoordinatePunctureFundamentalGroupEquiv
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α))
    (q : embeddedCoordinatePunctureExterior f) :
    FundamentalGroup (embeddedCoordinatePunctureExterior f) q ≃*
      FundamentalGroup {y : α // y ≠ embeddedCoordinatePunctureCenter hball f}
        (embeddedCoordinatePunctureInclusion hball f q) := by
  let e := FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (embeddedCoordinatePunctureHomotopyEquiv hball f hf)
  exact MulEquiv.ofBijective (FundamentalGroup.map
    (embeddedCoordinatePunctureInclusion hball f) q)
      (e.fullyFaithfulFunctor.map_bijective (FundamentalGroupoid.mk q)
        (FundamentalGroupoid.mk q))

/-- Representative exterior loops are sent through the literal inclusion;
no path-dependent change of basepoint is inserted. -/
@[simp]
theorem embeddedCoordinatePunctureFundamentalGroupEquiv_loop
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α))
    (q : embeddedCoordinatePunctureExterior f) (p : Path q q) :
    embeddedCoordinatePunctureFundamentalGroupEquiv hball f hf q ⟦p⟧ =
      ⟦p.map (embeddedCoordinatePunctureInclusion hball f).continuous⟧ := rfl

/-- The open exterior of a closed coordinate disk. -/
abbrev embeddedCoordinateClosedDiskExterior (f : C(U, α)) (a : ℝ) :=
  {y : α // y ∉ f '' {z : U | ‖(z : E)‖ ≤ a}}

/-- A point outside the smaller closed disk is in the actual center-punctured
ambient space. -/
def embeddedCoordinateClosedDiskExteriorToPuncture
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (a : ℝ) (ha : 0 ≤ a) :
    C(embeddedCoordinateClosedDiskExterior f a,
      {y : α // y ≠ embeddedCoordinatePunctureCenter hball f}) := by
  have hne (y : embeddedCoordinateClosedDiskExterior f a) :
      y.1 ≠ embeddedCoordinatePunctureCenter hball f := by
    intro hy
    apply y.2
    refine ⟨embeddedCoordinatePunctureOrigin hball, ?_, hy.symm⟩
    simpa [embeddedCoordinatePunctureOrigin] using ha
  exact ⟨fun y => ⟨y.1, hne y⟩, continuous_subtype_val.subtype_mk hne⟩

/-- The unit-disk exterior lies in every strictly smaller closed-disk
exterior by its literal identity inclusion. -/
def embeddedCoordinateClosedDiskExteriorInclusion (f : C(U, α))
    (a : ℝ) (ha1 : a < 1) :
    C(embeddedCoordinatePunctureExterior f, embeddedCoordinateClosedDiskExterior f a) := by
  have hmem (y : embeddedCoordinatePunctureExterior f) :
      y.1 ∉ f '' {z : U | ‖(z : E)‖ ≤ a} := by
    rintro ⟨z, hz, heq⟩
    apply y.2
    exact ⟨z, lt_of_le_of_lt hz ha1, heq⟩
  exact ⟨fun y => ⟨y.1, hmem y⟩, continuous_subtype_val.subtype_mk hmem⟩

/-- The same actual terminal push retracts the smaller closed-disk exterior
onto the unit open-disk exterior. -/
def embeddedCoordinateClosedDiskExteriorRetraction
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) (a : ℝ) (ha : 0 ≤ a) :
    C(embeddedCoordinateClosedDiskExterior f a, embeddedCoordinatePunctureExterior f) :=
  (embeddedCoordinatePunctureRetraction hball f hf).comp
    (embeddedCoordinateClosedDiskExteriorToPuncture hball f a ha)

@[simp]
theorem embeddedCoordinateClosedDiskExteriorRetraction_inclusion
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (y : embeddedCoordinatePunctureExterior f) :
    embeddedCoordinateClosedDiskExteriorRetraction hball f hf a ha
      (embeddedCoordinateClosedDiskExteriorInclusion f a ha1 y) = y := by
  apply Subtype.ext
  exact Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncturePushValue_fixed_of_not_disk hball f hf 1
    (embeddedCoordinateClosedDiskExteriorToPuncture hball f a ha
      (embeddedCoordinateClosedDiskExteriorInclusion f a ha1 y)) y.2

/-- The radial homotopy really stays in the smaller closed-disk exterior,
and fixes the entire unit-disk exterior throughout. -/
def embeddedCoordinateClosedDiskExteriorDeformationRetraction
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) :
    (ContinuousMap.id (embeddedCoordinateClosedDiskExterior f a)).HomotopyRel
      ((embeddedCoordinateClosedDiskExteriorInclusion f a ha1).comp
        (embeddedCoordinateClosedDiskExteriorRetraction hball f hf a ha))
      {y | y.1 ∉ embeddedCoordinatePunctureDisk f} where
  toHomotopy :=
    { toFun p := ⟨embeddedCoordinatePuncturePushValue hball f hf p.1
          (embeddedCoordinateClosedDiskExteriorToPuncture hball f a ha p.2),
        embeddedCoordinatePuncturePushValue_preserves_closedDiskExterior
          hball f hf a p.1
          (embeddedCoordinateClosedDiskExteriorToPuncture hball f a ha p.2) p.2.2⟩
      continuous_toFun :=
        ((Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncturePushValue_continuous hball f hf).comp
          (continuous_fst.prodMk
            ((embeddedCoordinateClosedDiskExteriorToPuncture hball f a ha).continuous.comp
              continuous_snd))).subtype_mk _
      map_zero_left y := by
        apply Subtype.ext
        exact Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncturePushValue_zero hball f hf _
      map_one_left _ := rfl }
  prop' t y hy := by
    apply Subtype.ext
    exact Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncturePushValue_fixed_of_not_disk hball f hf t _ hy

/-- The genuine open exterior in the local-disk cover has the same topology
up to homotopy as the unit-disk exterior, through the literal inclusion. -/
def embeddedCoordinateClosedDiskExteriorHomotopyEquiv
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) :
    embeddedCoordinateClosedDiskExterior f a ≃ₕ embeddedCoordinatePunctureExterior f where
  toFun := embeddedCoordinateClosedDiskExteriorRetraction hball f hf a ha
  invFun := embeddedCoordinateClosedDiskExteriorInclusion f a ha1
  left_inv :=
    ⟨(embeddedCoordinateClosedDiskExteriorDeformationRetraction hball f hf a ha ha1).toHomotopy.symm⟩
  right_inv := by
    have h : (embeddedCoordinateClosedDiskExteriorRetraction hball f hf a ha).comp
        (embeddedCoordinateClosedDiskExteriorInclusion f a ha1) =
          ContinuousMap.id (embeddedCoordinatePunctureExterior f) := by
      apply ContinuousMap.ext
      intro y
      exact embeddedCoordinateClosedDiskExteriorRetraction_inclusion hball f hf a ha ha1 y
    rw [h]

/-- The open exterior's literal radial retraction induces its actual based
group equivalence with the unit-disk exterior. -/
def embeddedCoordinateClosedDiskExteriorFundamentalGroupEquiv
    (hball : Metric.closedBall (0 : E) 1 ⊆ U) (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (q : embeddedCoordinateClosedDiskExterior f a) :
    FundamentalGroup (embeddedCoordinateClosedDiskExterior f a) q ≃*
      FundamentalGroup (embeddedCoordinatePunctureExterior f)
        (embeddedCoordinateClosedDiskExteriorRetraction hball f hf a ha q) := by
  let e := FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (embeddedCoordinateClosedDiskExteriorHomotopyEquiv hball f hf a ha ha1)
  exact MulEquiv.ofBijective (FundamentalGroup.map
    (embeddedCoordinateClosedDiskExteriorRetraction hball f hf a ha) q)
    (e.fullyFaithfulFunctor.map_bijective (FundamentalGroupoid.mk q)
      (FundamentalGroupoid.mk q))

#print axioms Internal.EmbeddedCoordinatePunctureRetractionHelpers.embeddedCoordinatePuncturePushValue_continuous
#print axioms embeddedCoordinatePunctureDeformationRetraction
#print axioms embeddedCoordinatePunctureRetraction_inclusion
#print axioms embeddedCoordinatePunctureFundamentalGroupEquiv
#print axioms embeddedCoordinateClosedDiskExteriorHomotopyEquiv
#print axioms embeddedCoordinateClosedDiskExteriorFundamentalGroupEquiv
