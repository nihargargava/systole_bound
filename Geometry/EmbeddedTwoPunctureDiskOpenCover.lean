module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Homeomorph.Lemmas
public import Geometry.ComplexAnnulusCircle

@[expose] public section

/-!
# An open cover around two punctures in an embedded disk

For an actual open embedding of a coordinate neighborhood, the complement of
two points in a compactly contained coordinate disk is covered by the exterior
of a smaller closed disk and the image of a larger open disk. Their overlap is
exactly the image of the intervening coordinate annulus.
-/

open Set

namespace SystolicGrowth

noncomputable section

variable {α : Type*} [TopologicalSpace α] [T2Space α] {U : Set ℂ}

/-- The ambient space with the two embedded punctures removed. -/
def embeddedTwoPunctureAmbient (f : C(U, α)) (p q : U) : Set α :=
  {x | x ≠ f p ∧ x ≠ f q}

/-- The compact image of a closed coordinate disk, using its actual chart-domain
inclusion. -/
def embeddedTwoPunctureClosedDiskImage (f : C(U, α)) (r : ℝ)
    (hr : Metric.closedBall (0 : ℂ) r ⊆ U) : Set α :=
  (fun z : Metric.closedBall (0 : ℂ) r => f ⟨z.1, hr z.2⟩) '' Set.univ

/-- Exterior of the embedded closed disk, restricted to the two-punctured
ambient space. -/
def embeddedTwoPunctureExterior (f : C(U, α)) (p q : U) (r : ℝ)
    (hr : Metric.closedBall (0 : ℂ) r ⊆ U) : Set α :=
  (embeddedTwoPunctureClosedDiskImage f r hr)ᶜ ∩ embeddedTwoPunctureAmbient f p q

/-- The larger coordinate disk's image, with both punctures removed. -/
def embeddedTwoPunctureLocalDisk (f : C(U, α)) (p q : U) (r : ℝ) : Set α :=
  f '' {z : U | ‖(z : ℂ)‖ < r} ∩ embeddedTwoPunctureAmbient f p q

/-- The literal intervening annulus in the original complex coordinates. -/
abbrev embeddedTwoPunctureCoordinateAnnulus (a b : ℝ) : Set ℂ :=
  complexAnnulus a b

/-- Include an entire coordinate annulus in the actual chart domain. -/
def embeddedTwoPunctureAnnulusToU (a b : ℝ)
    (hbU : Metric.closedBall (0 : ℂ) b ⊆ U) :
    embeddedTwoPunctureCoordinateAnnulus a b → U := fun z =>
  ⟨z.1, hbU (Metric.mem_closedBall.mpr (by
    simpa [dist_zero_right] using z.2.2.le))⟩

/-- The actual image in `α` of a complex-coordinate annulus. -/
def embeddedTwoPunctureAnnulusImage (f : C(U, α)) (a b : ℝ)
    (hbU : Metric.closedBall (0 : ℂ) b ⊆ U) : Set α :=
  Set.range (fun z : embeddedTwoPunctureCoordinateAnnulus a b =>
    f (embeddedTwoPunctureAnnulusToU a b hbU z))

omit [T2Space α] in
theorem embeddedTwoPunctureClosedDiskImage_isCompact
    (f : C(U, α)) (r : ℝ) (hr : Metric.closedBall (0 : ℂ) r ⊆ U) :
    IsCompact (embeddedTwoPunctureClosedDiskImage f r hr) := by
  letI : CompactSpace (Metric.closedBall (0 : ℂ) r) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) r)
  exact isCompact_univ.image (f.continuous.comp <|
    continuous_subtype_val.subtype_mk (fun z => hr z.2))

omit [T2Space α] in
theorem embeddedTwoPunctureClosedDiskImage_mem_iff
    (f : C(U, α)) (r : ℝ) (hr : Metric.closedBall (0 : ℂ) r ⊆ U) (x : α) :
    x ∈ embeddedTwoPunctureClosedDiskImage f r hr ↔
      ∃ z : U, ‖(z : ℂ)‖ ≤ r ∧ f z = x := by
  constructor
  · rintro ⟨z, -, hzx⟩
    refine ⟨⟨z.1, hr z.2⟩, ?_, hzx⟩
    have hzmem : (z.1 : ℂ) ∈ Metric.closedBall (0 : ℂ) r := z.2
    have hzdist : dist (z.1 : ℂ) 0 ≤ r := Metric.mem_closedBall.mp hzmem
    simpa [dist_zero_right] using hzdist
  · rintro ⟨z, hz, rfl⟩
    have hzmem : (z : ℂ) ∈ Metric.closedBall (0 : ℂ) r := by
      apply Metric.mem_closedBall.mpr
      simpa [dist_zero_right] using hz
    refine ⟨⟨z.1, hzmem⟩, Set.mem_univ _, ?_⟩
    rfl

theorem embeddedTwoPunctureAmbient_isOpen
    (f : C(U, α)) (p q : U) :
    IsOpen (embeddedTwoPunctureAmbient f p q) := by
  change IsOpen ({f p}ᶜ ∩ {f q}ᶜ)
  exact isClosed_singleton.isOpen_compl.inter isClosed_singleton.isOpen_compl

theorem embeddedTwoPunctureExterior_isOpen
    (f : C(U, α))
    (p q : U) (r : ℝ)
    (hr : Metric.closedBall (0 : ℂ) r ⊆ U) :
    IsOpen (embeddedTwoPunctureExterior f p q r hr) := by
  exact (embeddedTwoPunctureClosedDiskImage_isCompact f r hr).isClosed.isOpen_compl
    |>.inter (embeddedTwoPunctureAmbient_isOpen f p q)

theorem embeddedTwoPunctureLocalDisk_isOpen
    (f : C(U, α)) (hf : Topology.IsOpenEmbedding (f : U → α))
    (p q : U) (r : ℝ) :
    IsOpen (embeddedTwoPunctureLocalDisk f p q r) := by
  have hcoord : IsOpen {z : U | ‖(z : ℂ)‖ < r} := by
    have hball : IsOpen (Metric.ball (0 : ℂ) r) := Metric.isOpen_ball
    have h := hball.preimage
      (continuous_subtype_val : Continuous (fun z : U => (z : ℂ)))
    have hset : {z : U | ‖(z : ℂ)‖ < r} =
        (Subtype.val : U → ℂ) ⁻¹' Metric.ball (0 : ℂ) r := by
      ext z
      simp [Metric.mem_ball, dist_zero_right]
    rw [hset]
    exact h
  exact (hf.isOpenMap _ hcoord).inter (embeddedTwoPunctureAmbient_isOpen f p q)

omit [T2Space α] in
theorem embeddedTwoPuncture_exterior_union_local_eq_ambient
    (f : C(U, α)) (p q : U) {a r : ℝ} (har : a < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U) :
    embeddedTwoPunctureAmbient f p q =
      embeddedTwoPunctureExterior f p q a haU ∪
        embeddedTwoPunctureLocalDisk f p q r := by
  ext x
  constructor
  · intro hx
    by_cases hK : x ∈ embeddedTwoPunctureClosedDiskImage f a haU
    · right
      refine ⟨?_, hx⟩
      obtain ⟨z, hz, rfl⟩ :=
        (embeddedTwoPunctureClosedDiskImage_mem_iff f a haU x).mp hK
      refine ⟨z, ?_, rfl⟩
      exact lt_of_le_of_lt hz har
    · left
      exact ⟨hK, hx⟩
  · rintro (hx | hx)
    · exact hx.2
    · exact hx.2

omit [T2Space α] in
theorem embeddedTwoPuncture_exterior_inter_local_eq_annulus_image
    (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) (p q : U)
    {a r : ℝ} (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) :
    embeddedTwoPunctureExterior f p q a haU ∩
      embeddedTwoPunctureLocalDisk f p q r =
        embeddedTwoPunctureAnnulusImage f a r hrU := by
  ext x
  constructor
  · rintro ⟨⟨hxK, _hxD⟩, hxlocal⟩
    obtain ⟨zU, hzr, rfl⟩ := hxlocal.1
    have haz : a < ‖(zU : ℂ)‖ := by
      by_contra hnot
      have hle : ‖(zU : ℂ)‖ ≤ a := le_of_not_gt hnot
      apply hxK
      exact (embeddedTwoPunctureClosedDiskImage_mem_iff f a haU (f zU)).mpr
        ⟨zU, hle, rfl⟩
    let z : embeddedTwoPunctureCoordinateAnnulus a r := ⟨zU, ⟨haz, hzr⟩⟩
    have hinc : embeddedTwoPunctureAnnulusToU a r hrU z = zU := by
      apply Subtype.ext
      rfl
    refine ⟨z, ?_⟩
    change f (embeddedTwoPunctureAnnulusToU a r hrU z) = f zU
    rw [hinc]
  · rintro ⟨z, hxrange⟩
    let zU := embeddedTwoPunctureAnnulusToU a r hrU z
    have hzr : ‖(zU : ℂ)‖ < r := z.2.2
    have haz : a < ‖(zU : ℂ)‖ := z.2.1
    have hxD : f zU ≠ f p ∧ f zU ≠ f q := by
      constructor
      · intro h
        have hzp : zU = p := hf.injective h
        have hpbound : ‖(p : ℂ)‖ < a := lt_of_le_of_lt
          (le_max_left _ _) ha
        have hznorm : ‖(zU : ℂ)‖ < a := by
          rw [congrArg (fun w : U => ‖(w : ℂ)‖) hzp]
          exact hpbound
        exact (not_lt_of_ge hznorm.le) haz
      · intro h
        have hzq : zU = q := hf.injective h
        have hqbound : ‖(q : ℂ)‖ < a := lt_of_le_of_lt
          (le_max_right _ _) ha
        have hznorm : ‖(zU : ℂ)‖ < a := by
          rw [congrArg (fun w : U => ‖(w : ℂ)‖) hzq]
          exact hqbound
        exact (not_lt_of_ge hznorm.le) haz
    have hxK : f zU ∉ embeddedTwoPunctureClosedDiskImage f a haU := by
      intro hxK
      obtain ⟨w, hw, hwz⟩ :=
        (embeddedTwoPunctureClosedDiskImage_mem_iff f a haU (f zU)).mp hxK
      have hw_eq : w = zU := hf.injective hwz
      have hnormeq : ‖(w : ℂ)‖ = ‖(zU : ℂ)‖ :=
        congrArg (fun v : U => ‖(v : ℂ)‖) hw_eq
      have hnorm : ‖(zU : ℂ)‖ ≤ a := by rw [← hnormeq]; exact hw
      exact (not_lt_of_ge hnorm) haz
    rw [← hxrange]
    exact ⟨⟨hxK, hxD⟩,
      ⟨⟨zU, hzr, rfl⟩, hxD⟩⟩

/-- The overlap inherits the literal topology of the chart-coordinate
annulus. -/
noncomputable def embeddedTwoPunctureAnnulusHomeomorph
    (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) (p q : U)
    {a r : ℝ} (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) :
    embeddedTwoPunctureCoordinateAnnulus a r ≃ₜ
      ↥(embeddedTwoPunctureExterior f p q a haU ∩
        embeddedTwoPunctureLocalDisk f p q r) := by
  let H := embeddedTwoPuncture_exterior_inter_local_eq_annulus_image
    f hf p q ha haU hrU
  let m : embeddedTwoPunctureCoordinateAnnulus a r →
      ↥(embeddedTwoPunctureExterior f p q a haU ∩
        embeddedTwoPunctureLocalDisk f p q r) :=
    fun z => ⟨f (embeddedTwoPunctureAnnulusToU a r hrU z), by
      rw [H]
      exact ⟨z, rfl⟩⟩
  have hballU : Metric.ball (0 : ℂ) r ⊆ U := fun z hz =>
    hrU (Metric.ball_subset_closedBall hz)
  have hanball : embeddedTwoPunctureCoordinateAnnulus a r ⊆ Metric.ball (0 : ℂ) r := by
    intro z hz
    change dist (z : ℂ) 0 < r
    simpa [dist_zero_right] using hz.2
  have hinc : Topology.IsEmbedding (embeddedTwoPunctureAnnulusToU a r hrU) := by
    have he1 : Topology.IsEmbedding (inclusion hballU) :=
      Topology.IsEmbedding.inclusion hballU
    have he2 : Topology.IsEmbedding (inclusion hanball) :=
      Topology.IsEmbedding.inclusion hanball
    have hcomp : Topology.IsEmbedding (fun z : embeddedTwoPunctureCoordinateAnnulus a r =>
        inclusion hballU (inclusion hanball z)) := he1.comp he2
    convert hcomp using 1
    funext z
    apply Subtype.ext
    rfl
  have hem' : Topology.IsEmbedding
      (fun z : embeddedTwoPunctureCoordinateAnnulus a r =>
        f (embeddedTwoPunctureAnnulusToU a r hrU z)) :=
    hf.isEmbedding.comp hinc
  have hem : Topology.IsEmbedding m := hem'.codRestrict _ _
  have hsurj : Function.Surjective m := by
    intro x
    have hxrange : x.1 ∈ embeddedTwoPunctureAnnulusImage f a r hrU := H ▸ x.2
    change x.1 ∈ Set.range _ at hxrange
    obtain ⟨z, hx⟩ := hxrange
    exact ⟨z, Subtype.ext hx⟩
  exact hem.toHomeomorphOfSurjective hsurj

/-- Choose nested radii around two distinct points of the unit disk and obtain
the actual exterior/local open cover and its annular overlap. -/
theorem exists_embeddedTwoPunctureDiskOpenCover
    (hU : IsOpen U) (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (f : C(U, α)) (hf : Topology.IsOpenEmbedding (f : U → α))
    (p q : U) (hpq : p ≠ q)
    (hp : ‖(p : ℂ)‖ < 1) (hq : ‖(q : ℂ)‖ < 1) :
    ∃ (a r : ℝ) (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
      (hrU : Metric.closedBall (0 : ℂ) r ⊆ U),
      max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a ∧ a < 1 ∧ 1 < r ∧
      f p ≠ f q ∧ IsOpen (embeddedTwoPunctureExterior f p q a haU) ∧
      IsOpen (embeddedTwoPunctureLocalDisk f p q r) ∧
      embeddedTwoPunctureAmbient f p q =
        embeddedTwoPunctureExterior f p q a haU ∪
          embeddedTwoPunctureLocalDisk f p q r ∧
      embeddedTwoPunctureExterior f p q a haU ∩
        embeddedTwoPunctureLocalDisk f p q r =
          embeddedTwoPunctureAnnulusImage f a r hrU ∧
      Nonempty (embeddedTwoPunctureCoordinateAnnulus a r ≃ₜ
        ↥(embeddedTwoPunctureExterior f p q a haU ∩
          embeddedTwoPunctureLocalDisk f p q r)) := by
  have hmax : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < 1 := max_lt_iff.mpr ⟨hp, hq⟩
  obtain ⟨a, hamax, ha1⟩ := exists_between hmax
  have hcompact : IsCompact (Metric.closedBall (0 : ℂ) 1) :=
    isCompact_closedBall _ _
  obtain ⟨δ, hδ, hthick⟩ :=
    hcompact.exists_cthickening_subset_open hU hball
  let r := 1 + δ
  have hr1 : 1 < r := by dsimp [r]; linarith
  have hrball : Metric.closedBall (0 : ℂ) r ⊆ U := by
    have hrewrite : Metric.cthickening δ (Metric.closedBall (0 : ℂ) 1) =
        Metric.closedBall (0 : ℂ) r := by
      rw [cthickening_closedBall hδ.le (by norm_num : 0 ≤ (1 : ℝ)) (0 : ℂ)]
      simp [r, add_comm]
    rw [← hrewrite]
    exact hthick
  let haU : Metric.closedBall (0 : ℂ) a ⊆ U :=
    (Metric.closedBall_subset_closedBall ha1.le).trans hball
  have hfpq : f p ≠ f q := by
    intro heq
    exact hpq (hf.injective heq)
  refine ⟨a, r, haU, hrball, hamax, ha1, hr1, hfpq, ?_, ?_, ?_, ?_, ?_⟩
  · exact embeddedTwoPunctureExterior_isOpen f p q a haU
  · exact embeddedTwoPunctureLocalDisk_isOpen f hf p q r
  · exact embeddedTwoPuncture_exterior_union_local_eq_ambient f p q
      (lt_trans ha1 hr1) haU
  · exact embeddedTwoPuncture_exterior_inter_local_eq_annulus_image f hf p q
      hamax haU hrball
  · exact ⟨embeddedTwoPunctureAnnulusHomeomorph f hf p q hamax
      haU hrball⟩

#print axioms embeddedTwoPunctureClosedDiskImage_isCompact
#print axioms embeddedTwoPunctureExterior_isOpen
#print axioms embeddedTwoPunctureLocalDisk_isOpen
#print axioms embeddedTwoPuncture_exterior_union_local_eq_ambient
#print axioms embeddedTwoPuncture_exterior_inter_local_eq_annulus_image
#print axioms embeddedTwoPunctureAnnulusHomeomorph
#print axioms exists_embeddedTwoPunctureDiskOpenCover

end

end SystolicGrowth
