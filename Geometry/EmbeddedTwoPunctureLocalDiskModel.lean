module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.EmbeddedTwoPunctureDiskOpenCover
public import Geometry.TwoPuncturedDiskVanKampen
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

/-!
# The actual local disk as a standard twice-punctured disk

An open embedding identifies its actual local image, with the two actual
centers deleted, with the corresponding coordinate disk. Positive scaling
then identifies that disk with the unit disk while preserving which puncture
is lower and which is upper.
-/

open Set

namespace SystolicGrowth

noncomputable section

variable {α : Type*} [TopologicalSpace α] [T2Space α] {U : Set ℂ}

/-- Coordinate points in the radius-`r` disk with the two actual chart
centers removed. -/
def embeddedTwoPunctureCoordinateDisk (p q : U) (r : ℝ) : Set ℂ :=
  {z | ‖z‖ < r ∧ z ≠ (p : ℂ) ∧ z ≠ (q : ℂ)}

/-- The same punctured coordinate disk represented inside the chart domain. -/
def embeddedTwoPunctureLocalDiskDomain (p q : U) (r : ℝ) : Set U :=
  {z | ‖(z : ℂ)‖ < r ∧ z ≠ p ∧ z ≠ q}

/-- The two original centers' normalized imaginary coordinates, sorted in
increasing order for the standard lower/upper disk cover. -/
def embeddedTwoPunctureLowerParameter (p q : U) (r : ℝ) : ℝ :=
  min ((p : ℂ).im / r) ((q : ℂ).im / r)

/-- The larger normalized imaginary coordinate. -/
def embeddedTwoPunctureUpperParameter (p q : U) (r : ℝ) : ℝ :=
  max ((p : ℂ).im / r) ((q : ℂ).im / r)

/-- The actual normalized unit-disk coordinates of the two punctures before
sorting them into lower and upper order. -/
def embeddedTwoPunctureNormalizedUnitDisk (p q : U) (r : ℝ) : Set ℂ :=
  {z | ‖z‖ < 1 ∧ z ≠ (r⁻¹ : ℝ) • (p : ℂ) ∧
    z ≠ (r⁻¹ : ℝ) • (q : ℂ)}

omit [T2Space α] in
theorem embeddedTwoPunctureLocalDisk_eq_image_domain (f : C(U, α))
    (hf : Function.Injective (f : U → α)) (p q : U) (r : ℝ) :
    embeddedTwoPunctureLocalDisk f p q r =
      f '' embeddedTwoPunctureLocalDiskDomain p q r := by
  ext x
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, hpunct⟩
    refine ⟨z, ⟨hz, ?_, ?_⟩, rfl⟩
    · intro hp
      exact hpunct.1 (congrArg f hp)
    · intro hq
      exact hpunct.2 (congrArg f hq)
  · rintro ⟨z, ⟨hz, hp, hq⟩, rfl⟩
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    exact ⟨fun h => hp (hf h), fun h => hq (hf h)⟩

/-- Forgetting the chart-domain subtype identifies its punctured radius disk
with the same coordinates in `ℂ`. -/
def embeddedTwoPunctureLocalDiskDomainHomeomorph (p q : U) (r : ℝ)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) :
    {z : U // z ∈ embeddedTwoPunctureLocalDiskDomain p q r} ≃ₜ
      {z : ℂ // z ∈ embeddedTwoPunctureCoordinateDisk p q r} where
  toFun z := ⟨z.1, ⟨z.2.1,
    (fun hp => z.2.2.1 (Subtype.ext hp)),
    (fun hq => z.2.2.2 (Subtype.ext hq))⟩⟩
  invFun z := ⟨⟨z.1, hrU (Metric.mem_closedBall.mpr (by
      simpa [dist_zero_right] using z.2.1.le))⟩,
    ⟨z.2.1,
      (fun hp => z.2.2.1 (congrArg Subtype.val hp)),
      (fun hq => z.2.2.2 (congrArg Subtype.val hq))⟩⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The actual local image of an embedded chart disk is homeomorphic to its
literal coordinate disk with the chart-center coordinates removed. -/
def embeddedTwoPunctureLocalDiskCoordinateHomeomorph (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) (p q : U) (r : ℝ)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) :
    ↥(embeddedTwoPunctureLocalDisk f p q r) ≃ₜ
      {z : ℂ // z ∈ embeddedTwoPunctureCoordinateDisk p q r} := by
  let s := embeddedTwoPunctureLocalDiskDomain p q r
  have himage : embeddedTwoPunctureLocalDisk f p q r =
      f '' embeddedTwoPunctureLocalDiskDomain p q r :=
    embeddedTwoPunctureLocalDisk_eq_image_domain f hf.isEmbedding.injective p q r
  let hlocal : {z : U // z ∈ s} ≃ₜ
      ↥(embeddedTwoPunctureLocalDisk f p q r) :=
    (hf.isEmbedding.homeomorphImage s).trans
      (Homeomorph.setCongr himage.symm)
  exact hlocal.symm.trans
    (embeddedTwoPunctureLocalDiskDomainHomeomorph p q r hrU)

omit [T2Space α] in
/-- On an actual chart image point, the local-disk coordinate homeomorphism
returns exactly the original chart coordinate. -/
theorem embeddedTwoPunctureLocalDiskCoordinateHomeomorph_chartPoint
    (f : C(U, α)) (hf : Topology.IsOpenEmbedding (f : U → α)) (p q : U)
    (r : ℝ) (hrU : Metric.closedBall (0 : ℂ) r ⊆ U)
    (z : {z : U // z ∈ embeddedTwoPunctureLocalDiskDomain p q r}) :
    embeddedTwoPunctureLocalDiskCoordinateHomeomorph f hf p q r hrU
      ⟨f z.1, (embeddedTwoPunctureLocalDisk_eq_image_domain f
        hf.isEmbedding.injective p q r).symm ▸ ⟨z.1, z.2, rfl⟩⟩ =
      embeddedTwoPunctureLocalDiskDomainHomeomorph p q r hrU z := by
  let s := embeddedTwoPunctureLocalDiskDomain p q r
  have himage : embeddedTwoPunctureLocalDisk f p q r = f '' s :=
    embeddedTwoPunctureLocalDisk_eq_image_domain f hf.isEmbedding.injective p q r
  let hlocal : {z : U // z ∈ s} ≃ₜ
      ↥(embeddedTwoPunctureLocalDisk f p q r) :=
    (hf.isEmbedding.homeomorphImage s).trans (Homeomorph.setCongr himage.symm)
  let x : ↥(embeddedTwoPunctureLocalDisk f p q r) :=
    ⟨f z.1, himage.symm ▸ ⟨z.1, z.2, rfl⟩⟩
  have hmap : hlocal z = x := by
    apply Subtype.ext
    rfl
  have hrec : hlocal.symm x = z := by
    apply hlocal.injective
    calc
      hlocal (hlocal.symm x) = x := hlocal.apply_symm_apply x
      _ = hlocal z := hmap.symm
  change (embeddedTwoPunctureLocalDiskDomainHomeomorph p q r hrU)
      (hlocal.symm x) =
    (embeddedTwoPunctureLocalDiskDomainHomeomorph p q r hrU) z
  rw [hrec]

/-- Scaling a positive-radius coordinate disk by `1/r` gives the unit disk
with its two correspondingly scaled punctures removed. -/
def embeddedTwoPunctureCoordinateScalingHomeomorph (p q : U) (r : ℝ)
    (hr : 0 < r) :
    {z : ℂ // z ∈ embeddedTwoPunctureCoordinateDisk p q r} ≃ₜ
      {z : ℂ // z ∈ embeddedTwoPunctureNormalizedUnitDisk p q r} where
  toFun z := ⟨(r⁻¹ : ℝ) • z.1, by
    refine ⟨?_, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      calc
        r⁻¹ * ‖z.1‖ = ‖z.1‖ / r := by rw [div_eq_mul_inv]; ring
        _ < 1 := (div_lt_one hr).2 z.2.1
    · intro h
      have hmul := congrArg (fun w : ℂ => (r : ℝ) • w) h
      have hz : z.1 = (p : ℂ) := by
        simpa [smul_smul, hr.ne'] using hmul
      exact z.2.2.1 hz
    · intro h
      have hmul := congrArg (fun w : ℂ => (r : ℝ) • w) h
      have hz : z.1 = (q : ℂ) := by
        simpa [smul_smul, hr.ne'] using hmul
      exact z.2.2.2 hz⟩
  invFun z := ⟨(r : ℝ) • z.1, by
    refine ⟨?_, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      exact (mul_lt_mul_of_pos_left z.2.1 hr).trans_eq (by ring)
    · intro h
      have hmul := congrArg (fun w : ℂ => (r⁻¹ : ℝ) • w) h
      have hz : z.1 = (r⁻¹ : ℝ) • (p : ℂ) := by
        simpa [smul_smul, hr.ne'] using hmul
      exact z.2.2.1 hz
    · intro h
      have hmul := congrArg (fun w : ℂ => (r⁻¹ : ℝ) • w) h
      have hz : z.1 = (r⁻¹ : ℝ) • (q : ℂ) := by
        simpa [smul_smul, hr.ne'] using hmul
      exact z.2.2.2 hz⟩
  left_inv z := by
    apply Subtype.ext
    simp [hr.ne']
  right_inv z := by
    apply Subtype.ext
    simp [hr.ne']
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
theorem embeddedTwoPunctureCoordinateScalingHomeomorph_apply (p q : U) (r : ℝ)
    (hr : 0 < r) (z : {z : ℂ // z ∈ embeddedTwoPunctureCoordinateDisk p q r}) :
    (embeddedTwoPunctureCoordinateScalingHomeomorph p q r hr z : ℂ) =
      z.1 / (r : ℂ) := by
  change (r⁻¹ : ℝ) • z.1 = z.1 / (r : ℂ)
  rw [Complex.real_smul, div_eq_mul_inv, ← Complex.ofReal_inv]
  ring

theorem embeddedTwoPunctureNormalizedCenter_eq_left (p : U) (r : ℝ)
    (hpre : (p : ℂ).re = 0) :
    (r⁻¹ : ℝ) • (p : ℂ) =
      twoPuncturedDiskLeftCenter ((p : ℂ).im / r) := by
  apply Complex.ext
  · simp [twoPuncturedDiskLeftCenter, hpre]
  · simp [twoPuncturedDiskLeftCenter, div_eq_mul_inv, mul_comm]

theorem embeddedTwoPunctureNormalizedCenter_eq_right (q : U) (r : ℝ)
    (hqre : (q : ℂ).re = 0) :
    (r⁻¹ : ℝ) • (q : ℂ) =
      twoPuncturedDiskRightCenter ((q : ℂ).im / r) := by
  apply Complex.ext
  · simp [twoPuncturedDiskRightCenter, hqre]
  · simp [twoPuncturedDiskRightCenter, div_eq_mul_inv, mul_comm]

/-- Sorting the scaled centers identifies the normalized puncture set with
the standard lower/upper twice-punctured unit disk. -/
theorem embeddedTwoPunctureNormalizedUnitDisk_eq_standard (p q : U) (r : ℝ)
    (hpre : (p : ℂ).re = 0) (hqre : (q : ℂ).re = 0) :
    embeddedTwoPunctureNormalizedUnitDisk p q r =
      twoPuncturedUnitDisk (embeddedTwoPunctureLowerParameter p q r)
        (embeddedTwoPunctureUpperParameter p q r) := by
  by_cases h : (p : ℂ).im / r ≤ (q : ℂ).im / r
  · ext z
    simp [embeddedTwoPunctureNormalizedUnitDisk, twoPuncturedUnitDisk,
      embeddedTwoPunctureLowerParameter, embeddedTwoPunctureUpperParameter,
      min_eq_left h, max_eq_right h,
      embeddedTwoPunctureNormalizedCenter_eq_left p r hpre,
      embeddedTwoPunctureNormalizedCenter_eq_right q r hqre,
      Metric.mem_ball, dist_zero_right]
  · have h' : (q : ℂ).im / r ≤ (p : ℂ).im / r := le_of_not_ge h
    ext z
    simp [embeddedTwoPunctureNormalizedUnitDisk, twoPuncturedUnitDisk,
      embeddedTwoPunctureLowerParameter, embeddedTwoPunctureUpperParameter,
      min_eq_right h', max_eq_left h',
      embeddedTwoPunctureNormalizedCenter_eq_left q r hqre,
      embeddedTwoPunctureNormalizedCenter_eq_right p r hpre,
      Metric.mem_ball, dist_zero_right, and_comm]

theorem embeddedTwoPunctureLowerParameter_lt_upper (p q : U) (r : ℝ)
    (hr : 0 < r) (hpq : p ≠ q)
    (hpre : (p : ℂ).re = 0) (hqre : (q : ℂ).re = 0) :
    embeddedTwoPunctureLowerParameter p q r <
      embeddedTwoPunctureUpperParameter p q r := by
  change min ((p : ℂ).im / r) ((q : ℂ).im / r) <
    max ((p : ℂ).im / r) ((q : ℂ).im / r)
  apply min_lt_max.mpr
  intro hdiv
  have him : (p : ℂ).im = (q : ℂ).im := by
    have h := hdiv
    field_simp at h
    exact h
  have hpqval : (p : ℂ) = (q : ℂ) := by
    apply Complex.ext
    · exact hpre.trans hqre.symm
    · exact him
  exact hpq (Subtype.ext hpqval)

/-- If the first original center has smaller imaginary coordinate, sorting
retains it as the lower puncture and the second as the upper one. -/
theorem embeddedTwoPunctureParameters_p_lower (p q : U) (r : ℝ)
    (horder : (p : ℂ).im / r < (q : ℂ).im / r) :
    embeddedTwoPunctureLowerParameter p q r = (p : ℂ).im / r ∧
      embeddedTwoPunctureUpperParameter p q r = (q : ℂ).im / r := by
  simp [embeddedTwoPunctureLowerParameter, embeddedTwoPunctureUpperParameter,
    min_eq_left horder.le, max_eq_right horder.le]

/-- If the second original center has smaller imaginary coordinate, sorting
retains the reversed original-center assignment. -/
theorem embeddedTwoPunctureParameters_q_lower (p q : U) (r : ℝ)
    (horder : (q : ℂ).im / r < (p : ℂ).im / r) :
    embeddedTwoPunctureLowerParameter p q r = (q : ℂ).im / r ∧
      embeddedTwoPunctureUpperParameter p q r = (p : ℂ).im / r := by
  simp [embeddedTwoPunctureLowerParameter, embeddedTwoPunctureUpperParameter,
    min_eq_right horder.le, max_eq_left horder.le]

/-- The sorted parameters lie strictly inside the unit interval whenever the
two original chart centers lie inside the radius-`r` disk. -/
theorem embeddedTwoPunctureParameters_bounds (p q : U) (r : ℝ)
    (hr : 0 < r) (hp : ‖(p : ℂ)‖ < r) (hq : ‖(q : ℂ)‖ < r) :
    -1 < embeddedTwoPunctureLowerParameter p q r ∧
      embeddedTwoPunctureLowerParameter p q r < 1 ∧
      -1 < embeddedTwoPunctureUpperParameter p q r ∧
      embeddedTwoPunctureUpperParameter p q r < 1 := by
  have hpabs : |(p : ℂ).im| < r :=
    (Complex.abs_im_le_norm (p : ℂ)).trans_lt hp
  have hqabs : |(q : ℂ).im| < r :=
    (Complex.abs_im_le_norm (q : ℂ)).trans_lt hq
  have hpcoord : -1 < (p : ℂ).im / r ∧ (p : ℂ).im / r < 1 := by
    rw [← abs_lt, abs_div, abs_of_pos hr]
    exact (div_lt_one hr).2 hpabs
  have hqcoord : -1 < (q : ℂ).im / r ∧ (q : ℂ).im / r < 1 := by
    rw [← abs_lt, abs_div, abs_of_pos hr]
    exact (div_lt_one hr).2 hqabs
  dsimp [embeddedTwoPunctureLowerParameter, embeddedTwoPunctureUpperParameter]
  exact ⟨lt_min hpcoord.1 hqcoord.1,
    lt_of_le_of_lt (min_le_left _ _) hpcoord.2,
    lt_of_lt_of_le hpcoord.1 (le_max_left _ _),
    max_lt hpcoord.2 hqcoord.2⟩

/-- The first original puncture is literally the lower normalized puncture
when its imaginary coordinate is smaller. -/
theorem embeddedTwoPunctureNormalized_p_is_left (p q : U) (r : ℝ)
    (hpre : (p : ℂ).re = 0)
    (horder : (p : ℂ).im / r < (q : ℂ).im / r) :
    (r⁻¹ : ℝ) • (p : ℂ) =
      twoPuncturedDiskLeftCenter (embeddedTwoPunctureLowerParameter p q r) := by
  rw [(embeddedTwoPunctureParameters_p_lower p q r horder).1]
  exact embeddedTwoPunctureNormalizedCenter_eq_left p r hpre

/-- The second original puncture is literally the upper normalized puncture
when the first has smaller imaginary coordinate. -/
theorem embeddedTwoPunctureNormalized_q_is_right (p q : U) (r : ℝ)
    (hqre : (q : ℂ).re = 0)
    (horder : (p : ℂ).im / r < (q : ℂ).im / r) :
    (r⁻¹ : ℝ) • (q : ℂ) =
      twoPuncturedDiskRightCenter (embeddedTwoPunctureUpperParameter p q r) := by
  rw [(embeddedTwoPunctureParameters_p_lower p q r horder).2]
  exact embeddedTwoPunctureNormalizedCenter_eq_right q r hqre

/-- Under the opposite order, the second original center is the literal
lower normalized puncture. -/
theorem embeddedTwoPunctureNormalized_q_is_left (p q : U) (r : ℝ)
    (hqre : (q : ℂ).re = 0)
    (horder : (q : ℂ).im / r < (p : ℂ).im / r) :
    (r⁻¹ : ℝ) • (q : ℂ) =
      twoPuncturedDiskLeftCenter (embeddedTwoPunctureLowerParameter p q r) := by
  rw [(embeddedTwoPunctureParameters_q_lower p q r horder).1]
  exact embeddedTwoPunctureNormalizedCenter_eq_left q r hqre

/-- Under the opposite order, the first original center is the literal
upper normalized puncture. -/
theorem embeddedTwoPunctureNormalized_p_is_right (p q : U) (r : ℝ)
    (hpre : (p : ℂ).re = 0)
    (horder : (q : ℂ).im / r < (p : ℂ).im / r) :
    (r⁻¹ : ℝ) • (p : ℂ) =
      twoPuncturedDiskRightCenter (embeddedTwoPunctureUpperParameter p q r) := by
  rw [(embeddedTwoPunctureParameters_q_lower p q r horder).2]
  exact embeddedTwoPunctureNormalizedCenter_eq_right p r hpre

/-- The actual embedded local disk, mapped by its literal chart coordinate
and positive scaling, is the standard twice-punctured unit disk. -/
def embeddedTwoPunctureLocalDiskUnitHomeomorph (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) (p q : U) (r : ℝ)
    (hr : 0 < r) (hrU : Metric.closedBall (0 : ℂ) r ⊆ U)
    (hpre : (p : ℂ).re = 0) (hqre : (q : ℂ).re = 0) :
    ↥(embeddedTwoPunctureLocalDisk f p q r) ≃ₜ
      twoPuncturedUnitDiskPoint (embeddedTwoPunctureLowerParameter p q r)
        (embeddedTwoPunctureUpperParameter p q r) :=
  (embeddedTwoPunctureLocalDiskCoordinateHomeomorph f hf p q r hrU).trans
    ((embeddedTwoPunctureCoordinateScalingHomeomorph p q r hr).trans
      (Homeomorph.setCongr
        (embeddedTwoPunctureNormalizedUnitDisk_eq_standard p q r hpre hqre)))

omit [T2Space α] in
@[simp]
theorem embeddedTwoPunctureLocalDiskUnitHomeomorph_apply (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) (p q : U) (r : ℝ)
    (hr : 0 < r) (hrU : Metric.closedBall (0 : ℂ) r ⊆ U)
    (hpre : (p : ℂ).re = 0) (hqre : (q : ℂ).re = 0)
    (x : ↥(embeddedTwoPunctureLocalDisk f p q r)) :
    (embeddedTwoPunctureLocalDiskUnitHomeomorph f hf p q r hr hrU hpre hqre x : ℂ) =
      (r⁻¹ : ℝ) •
        (embeddedTwoPunctureLocalDiskCoordinateHomeomorph f hf p q r hrU x : ℂ) := rfl

/-- The standard twice-punctured unit disk is path connected by the actual
lower/upper open cover and its nonempty strip overlap. -/
theorem twoPuncturedUnitDiskPoint_pathConnected {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hβ : -1 < β) (hβ1 : β < 1)
    (hαβ : α < β) : PathConnectedSpace (twoPuncturedUnitDiskPoint α β) := by
  let L := twoPuncturedDiskLowerRelativeSide α β
  let R := twoPuncturedDiskUpperRelativeSide α β
  have hL : IsPathConnected L :=
    twoPuncturedDiskLowerRelativeSide_isPathConnected hα hα1 hαβ
  have hR : IsPathConnected R :=
    twoPuncturedDiskUpperRelativeSide_isPathConnected hβ hβ1 hαβ
  letI : PathConnectedSpace
      {z : twoPuncturedUnitDiskPoint α β // z ∈ twoPuncturedDiskRelativeOverlap α β} :=
    twoPuncturedDiskRelativeOverlap_pathConnected hα hα1 hβ hβ1 hαβ
  have hLR : (L ∩ R).Nonempty := by
    obtain ⟨z⟩ := (inferInstance : Nonempty
      {z : twoPuncturedUnitDiskPoint α β //
        z ∈ twoPuncturedDiskRelativeOverlap α β})
    exact ⟨z.1, z.2⟩
  have hunion : IsPathConnected (Set.univ : Set (twoPuncturedUnitDiskPoint α β)) := by
    rw [← twoPuncturedDisk_relativeCover hαβ]
    exact hL.union hR hLR
  letI : PathConnectedSpace
      ↥(Set.univ : Set (twoPuncturedUnitDiskPoint α β)) :=
    (isPathConnected_iff_pathConnectedSpace).mp hunion
  exact Function.Surjective.pathConnectedSpace
    (Homeomorph.Set.univ (twoPuncturedUnitDiskPoint α β)).surjective
    (Homeomorph.Set.univ (twoPuncturedUnitDiskPoint α β)).continuous

omit [T2Space α] in
/-- The actual embedded twice-punctured local disk is path connected, via
its literal coordinate/scaling homeomorphism and the standard open cover. -/
theorem embeddedTwoPunctureLocalDisk_pathConnected (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) (p q : U) (r : ℝ)
    (hr : 0 < r) (hrU : Metric.closedBall (0 : ℂ) r ⊆ U)
    (hpre : (p : ℂ).re = 0) (hqre : (q : ℂ).re = 0) (hpq : p ≠ q)
    (hp : ‖(p : ℂ)‖ < r) (hq : ‖(q : ℂ)‖ < r) :
    PathConnectedSpace ↥(embeddedTwoPunctureLocalDisk f p q r) := by
  have hαβ := embeddedTwoPunctureLowerParameter_lt_upper p q r hr hpq hpre hqre
  obtain ⟨hα, hα1, hβ, hβ1⟩ := embeddedTwoPunctureParameters_bounds p q r hr hp hq
  letI : PathConnectedSpace
      (twoPuncturedUnitDiskPoint (embeddedTwoPunctureLowerParameter p q r)
        (embeddedTwoPunctureUpperParameter p q r)) :=
    twoPuncturedUnitDiskPoint_pathConnected hα hα1 hβ hβ1 hαβ
  exact Function.Surjective.pathConnectedSpace
    (embeddedTwoPunctureLocalDiskUnitHomeomorph f hf p q r hr hrU hpre hqre).symm.surjective
    (embeddedTwoPunctureLocalDiskUnitHomeomorph f hf p q r hr hrU hpre hqre).symm.continuous

end

end SystolicGrowth
