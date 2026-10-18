module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.EmbeddedTwoPunctureDiskVanKampen

@[expose] public section

/-!
# Actual connector paths inside the local annulus overlap

The normalized overlap is convex.  Pulling its literal straight segment back
through the actual local-disk homeomorphism gives connector paths in the
original relative local-disk carrier, with their endpoints and side
membership preserved.
-/

open Set
open scoped ContinuousMap unitInterval

namespace SystolicGrowth

noncomputable section

def Internal.SurfaceTwoCenterAnnulusConnectorPathsHelpers.pathIntoSubtype {Y : Type*} [TopologicalSpace Y] {A : Set Y}
    {x y : Y} (p : Path x y) (hmem : ∀ t : unitInterval, p t ∈ A) :
    Path (⟨x, p.source ▸ hmem 0⟩ : {z : Y // z ∈ A})
      (⟨y, p.target ▸ hmem 1⟩ : {z : Y // z ∈ A}) where
  toFun t := ⟨p t, hmem t⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

/-- The straight segment between two actual points of the normalized
relative overlap, regarded as a path in that overlap subtype. -/
def twoPuncturedDiskRelativeOverlapSegmentPath {α β : ℝ} (hαβ : α < β)
    (q₀ q₁ : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β}) : Path q₀ q₁ := by
  let E := twoPuncturedDiskOverlapHomeomorph hαβ
  let x₀ := E q₀
  let x₁ := E q₁
  have hsegment : ∀ t : unitInterval,
      Path.segment x₀.1 x₁.1 t ∈ twoPuncturedDiskOverlap α β := by
    intro t
    have ht : Path.segment x₀.1 x₁.1 t ∈ Set.range (Path.segment x₀.1 x₁.1) :=
      ⟨t, rfl⟩
    rw [Path.range_segment] at ht
    exact (twoPuncturedDiskOverlap_convex α β).segment_subset x₀.2 x₁.2 ht
  let γ := Internal.SurfaceTwoCenterAnnulusConnectorPathsHelpers.pathIntoSubtype (Path.segment x₀.1 x₁.1) hsegment
  change Path (E.symm x₀) (E.symm x₁)
  simpa only [E.symm_apply_apply] using γ.map E.symm.continuous

/-- Pull the literal normalized overlap segment back to the actual relative
local-disk carrier.  The pulled-back path remains in the actual coordinate
overlap at every parameter value. -/
theorem embeddedTwoPunctureRelativeLocalDiskOverlapConnector
    {g : ℕ} {X : ClosedHyperbolicSurface g} {U : Set ℂ}
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (r : ℝ) (hr : 0 < r)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U)
    (hpre : (p : ℂ).re = 0) (hqre : (q : ℂ).re = 0)
    (hαβ : embeddedTwoPunctureLowerParameter p q r <
      embeddedTwoPunctureUpperParameter p q r)
    (x y : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r})
    (hx : (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q r hr hrU hpre hqre x : twoPuncturedUnitDiskPoint
        (embeddedTwoPunctureLowerParameter p q r)
        (embeddedTwoPunctureUpperParameter p q r)) ∈
        twoPuncturedDiskRelativeOverlap
          (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r))
    (hy : (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q r hr hrU hpre hqre y : twoPuncturedUnitDiskPoint
        (embeddedTwoPunctureLowerParameter p q r)
        (embeddedTwoPunctureUpperParameter p q r)) ∈
        twoPuncturedDiskRelativeOverlap
          (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r)) :
    ∃ η : Path x y, ∀ t : unitInterval,
      (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
        f hf p q r hr hrU hpre hqre (η t) : twoPuncturedUnitDiskPoint
          (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r)) ∈
          twoPuncturedDiskRelativeOverlap
            (embeddedTwoPunctureLowerParameter p q r)
            (embeddedTwoPunctureUpperParameter p q r) := by
  let α := embeddedTwoPunctureLowerParameter p q r
  let β := embeddedTwoPunctureUpperParameter p q r
  let E := embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
    f hf p q r hr hrU hpre hqre
  let qx : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β} := ⟨E x, hx⟩
  let qy : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β} := ⟨E y, hy⟩
  let γ := twoPuncturedDiskRelativeOverlapSegmentPath hαβ qx qy
  let F : C({z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β},
      {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r}) :=
    ⟨fun z => E.symm z.1, E.symm.continuous.comp continuous_subtype_val⟩
  have hstart : x = E.symm qx := by
    simp [qx]
  have htarget : y = E.symm qy := by
    simp [qy]
  have hstart' : x = F qx := by simpa [F] using hstart
  have htarget' : y = F qy := by simpa [F] using htarget
  let η : Path x y := (γ.map F.continuous).cast hstart' htarget'
  refine ⟨η, ?_⟩
  intro t
  change (E (η t) : twoPuncturedUnitDiskPoint α β) ∈
    twoPuncturedDiskRelativeOverlap α β
  have hval : E (η t) = (γ t).1 := by
    change E (F (γ t)) = (γ t).1
    simp [F]
  rw [hval]
  exact (γ t).2

/-- The pulled-back overlap connector lies in both actual local sides, not
merely in the ambient local-disk carrier. -/
theorem embeddedTwoPunctureRelativeLocalDiskOverlapConnector_mem_sides
    {g : ℕ} {X : ClosedHyperbolicSurface g} {U : Set ℂ}
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (r : ℝ) (hr : 0 < r)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U)
    (hpre : (p : ℂ).re = 0) (hqre : (q : ℂ).re = 0)
    (hαβ : embeddedTwoPunctureLowerParameter p q r <
      embeddedTwoPunctureUpperParameter p q r)
    (x y : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r})
    (hx : (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q r hr hrU hpre hqre x : twoPuncturedUnitDiskPoint
        (embeddedTwoPunctureLowerParameter p q r)
        (embeddedTwoPunctureUpperParameter p q r)) ∈
        twoPuncturedDiskRelativeOverlap
          (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r))
    (hy : (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q r hr hrU hpre hqre y : twoPuncturedUnitDiskPoint
        (embeddedTwoPunctureLowerParameter p q r)
        (embeddedTwoPunctureUpperParameter p q r)) ∈
        twoPuncturedDiskRelativeOverlap
          (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r)) :
    ∃ η : Path x y,
      (∀ t : unitInterval,
        (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q r hr hrU hpre hqre (η t) : ℂ) ∈
            twoPuncturedDiskLowerSide
              (embeddedTwoPunctureLowerParameter p q r)
              (embeddedTwoPunctureUpperParameter p q r)) ∧
      (∀ t : unitInterval,
        (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q r hr hrU hpre hqre (η t) : ℂ) ∈
            twoPuncturedDiskUpperSide
              (embeddedTwoPunctureLowerParameter p q r)
              (embeddedTwoPunctureUpperParameter p q r)) := by
  obtain ⟨η, hη⟩ := embeddedTwoPunctureRelativeLocalDiskOverlapConnector
    f hf p q r hr hrU hpre hqre hαβ x y hx hy
  refine ⟨η, ?_, ?_⟩ <;> intro t
  · have h := hη t
    change ((embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q r hr hrU hpre hqre (η t)).1 ∈
        twoPuncturedDiskLowerSide
          (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r)) ∧ _ at h
    exact h.1
  · have h := hη t
    change _ ∧ ((embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q r hr hrU hpre hqre (η t)).1 ∈
        twoPuncturedDiskUpperSide
          (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r)) at h
    exact h.2

/-- Connect any actual local midpoint in the coordinate overlap to the
literal right crossing of the exterior/local annulus.  The connector remains
inside both local sides, so it can be concatenated with either native half
path at the annulus van-Kampen basepoint. -/
theorem exists_embeddedTwoPunctureAnnulusLocalConnector
    {g : ℕ} {X : ClosedHyperbolicSurface g} {U : Set ℂ}
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (a r : ℝ)
    (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a) (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U)
    (hpq : p ≠ q) (hpre : (p : ℂ).re = 0) (hqre : (q : ℂ).re = 0)
    (mid : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r})
    (hmid : (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q r (zero_lt_one.trans hr1) hrU hpre hqre mid :
        twoPuncturedUnitDiskPoint (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r)) ∈
        twoPuncturedDiskRelativeOverlap
          (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r)) :
    let hαβ := embeddedTwoPunctureLowerParameter_lt_upper p q r
      (zero_lt_one.trans hr1) hpq hpre hqre
    let hnorms := embeddedTwoPunctureParameters_abs_lt_inv p q
      (zero_lt_one.trans hr1)
      (((le_max_left _ _).trans_lt ha).trans ha1)
      (((le_max_right _ _).trans_lt ha).trans ha1)
    let hR := (inv_lt_one₀ (zero_lt_one.trans hr1)).mpr hr1
    let θ := twoPuncturedDiskOuterRightDirection hαβ hnorms.1 hnorms.2 hR
    ∃ η : Path mid
      (twoOpenCoverAmalgamOverlapRight
        (embeddedTwoPunctureExteriorRelativeSide f p q a haU)
        (embeddedTwoPunctureLocalDiskRelativeSide f p q r)
        (embeddedTwoPunctureRelativeBoundaryCircle
          f hf p q a r ha ha1 hr1 haU hrU θ)),
      (∀ t : unitInterval,
        (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q r (zero_lt_one.trans hr1) hrU hpre hqre (η t) : ℂ) ∈
            twoPuncturedDiskLowerSide
              (embeddedTwoPunctureLowerParameter p q r)
              (embeddedTwoPunctureUpperParameter p q r)) ∧
      (∀ t : unitInterval,
        (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q r (zero_lt_one.trans hr1) hrU hpre hqre (η t) : ℂ) ∈
            twoPuncturedDiskUpperSide
              (embeddedTwoPunctureLowerParameter p q r)
              (embeddedTwoPunctureUpperParameter p q r)) := by
  dsimp only
  let hαβ := embeddedTwoPunctureLowerParameter_lt_upper p q r
    (zero_lt_one.trans hr1) hpq hpre hqre
  let hnorms := embeddedTwoPunctureParameters_abs_lt_inv p q
    (zero_lt_one.trans hr1)
    (((le_max_left _ _).trans_lt ha).trans ha1)
    (((le_max_right _ _).trans_lt ha).trans ha1)
  let hR := (inv_lt_one₀ (zero_lt_one.trans hr1)).mpr hr1
  let θ := twoPuncturedDiskOuterRightDirection hαβ hnorms.1 hnorms.2 hR
  let qR := twoOpenCoverAmalgamOverlapRight
    (embeddedTwoPunctureExteriorRelativeSide f p q a haU)
    (embeddedTwoPunctureLocalDiskRelativeSide f p q r)
    (embeddedTwoPunctureRelativeBoundaryCircle
      f hf p q a r ha ha1 hr1 haU hrU θ)
  have hqR : (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q r (zero_lt_one.trans hr1) hrU hpre hqre qR :
        twoPuncturedUnitDiskPoint (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r)) ∈
        twoPuncturedDiskRelativeOverlap
          (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r) := by
    exact embeddedTwoPunctureRelativeBoundaryCircle_right_mem_localOverlap
      f hf p q a r ha ha1 hr1 haU hrU hpq hpre hqre
  exact embeddedTwoPunctureRelativeLocalDiskOverlapConnector_mem_sides
    f hf p q r (zero_lt_one.trans hr1) hrU hpre hqre hαβ mid qR hmid hqR

/-- Turn a local lower-side half-path into a path based at the actual
annulus point by following the common overlap connector backwards. -/
def embeddedTwoPunctureAnnulusLeftConnector
    {g : ℕ} {X : ClosedHyperbolicSurface g} {U : Set ℂ}
    (f : C(U, X.Carrier)) (p q : U) (r : ℝ)
    {leftEndpoint mid : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r}}
    (leftHalf : Path leftEndpoint mid)
    {annulusPoint : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r}}
    (η : Path mid annulusPoint) :=
  (leftHalf.trans η).symm

/-- Turn a local right-side half-path into a path based at the actual
annulus point by first following the common overlap connector backwards. -/
def embeddedTwoPunctureAnnulusRightConnector
    {g : ℕ} {X : ClosedHyperbolicSurface g} {U : Set ℂ}
    (f : C(U, X.Carrier)) (p q : U) (r : ℝ)
    {mid : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r}}
    {annulusPoint : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r}}
    (η : Path mid annulusPoint)
    {rightEndpoint : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r}}
    (rightHalf : Path mid rightEndpoint) :=
  η.symm.trans rightHalf

private theorem path_mem_trans {Y : Type*} [TopologicalSpace Y]
    {x y z : Y} (p : Path x y) (q : Path y z) {Z : Type*}
    (F : Y → Z) (S : Set Z)
    (hp : ∀ t : unitInterval, F (p t) ∈ S)
    (hq : ∀ t : unitInterval, F (q t) ∈ S) :
    ∀ t : unitInterval, F ((p.trans q) t) ∈ S := by
  intro t
  have ht : (p.trans q) t ∈ Set.range (p.trans q) := ⟨t, rfl⟩
  rw [Path.trans_range] at ht
  rcases ht with ht | ht
  · obtain ⟨s, hs⟩ := ht
    rw [← hs]
    exact hp s
  · obtain ⟨s, hs⟩ := ht
    rw [← hs]
    exact hq s

private theorem path_mem_symm {Y : Type*} [TopologicalSpace Y]
    {x y : Y} (p : Path x y) {Z : Type*} (F : Y → Z) (S : Set Z)
    (hp : ∀ t : unitInterval, F (p t) ∈ S) :
    ∀ t : unitInterval, F (p.symm t) ∈ S := by
  intro t
  have ht : p.symm t ∈ Set.range p := by
    rw [← Path.symm_range p]
    exact ⟨t, rfl⟩
  obtain ⟨s, hs⟩ := ht
  rw [← hs]
  exact hp s

/-- Rebase the two genuine local connector halves at the literal annulus
right-crossing.  The shared connector lies in both sides, so either vertical
ordering gives the matching lower/upper based paths.  When the two based paths
are joined, the common connector cancels up to endpoint-fixed path homotopy;
the result is the original cut-preserving pair of halves. -/
theorem embeddedTwoPunctureAnnulusConnectorPair
    {g : ℕ} {X : ClosedHyperbolicSurface g} {U : Set ℂ}
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (r : ℝ) (hr : 0 < r)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U)
    (hpre : (p : ℂ).re = 0) (hqre : (q : ℂ).re = 0)
    {leftEndpoint mid rightEndpoint annulusPoint :
      {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r}}
    (leftHalf : Path leftEndpoint mid)
    (rightHalf : Path mid rightEndpoint)
    (η : Path mid annulusPoint)
    (horder :
      ((∀ t : unitInterval,
        (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q r hr hrU hpre hqre (leftHalf t) : ℂ) ∈
          twoPuncturedDiskLowerSide
            (embeddedTwoPunctureLowerParameter p q r)
            (embeddedTwoPunctureUpperParameter p q r)) ∧
       (∀ t : unitInterval,
        (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q r hr hrU hpre hqre (rightHalf t) : ℂ) ∈
          twoPuncturedDiskUpperSide
            (embeddedTwoPunctureLowerParameter p q r)
            (embeddedTwoPunctureUpperParameter p q r))) ∨
      ((∀ t : unitInterval,
        (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q r hr hrU hpre hqre (leftHalf t) : ℂ) ∈
          twoPuncturedDiskUpperSide
            (embeddedTwoPunctureLowerParameter p q r)
            (embeddedTwoPunctureUpperParameter p q r)) ∧
       (∀ t : unitInterval,
        (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q r hr hrU hpre hqre (rightHalf t) : ℂ) ∈
          twoPuncturedDiskLowerSide
            (embeddedTwoPunctureLowerParameter p q r)
            (embeddedTwoPunctureUpperParameter p q r))))
    (hηLower : ∀ t : unitInterval,
      (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
        f hf p q r hr hrU hpre hqre (η t) : ℂ) ∈
        twoPuncturedDiskLowerSide
          (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r))
    (hηUpper : ∀ t : unitInterval,
      (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
        f hf p q r hr hrU hpre hqre (η t) : ℂ) ∈
        twoPuncturedDiskUpperSide
          (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r)) :
    (((∀ t : unitInterval,
        (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q r hr hrU hpre hqre
            (embeddedTwoPunctureAnnulusLeftConnector f p q r leftHalf η t) : ℂ) ∈
          twoPuncturedDiskLowerSide
            (embeddedTwoPunctureLowerParameter p q r)
            (embeddedTwoPunctureUpperParameter p q r)) ∧
       (∀ t : unitInterval,
        (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q r hr hrU hpre hqre
            (embeddedTwoPunctureAnnulusRightConnector f p q r η rightHalf t) : ℂ) ∈
          twoPuncturedDiskUpperSide
            (embeddedTwoPunctureLowerParameter p q r)
            (embeddedTwoPunctureUpperParameter p q r))) ∨
      ((∀ t : unitInterval,
        (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q r hr hrU hpre hqre
            (embeddedTwoPunctureAnnulusLeftConnector f p q r leftHalf η t) : ℂ) ∈
          twoPuncturedDiskUpperSide
            (embeddedTwoPunctureLowerParameter p q r)
            (embeddedTwoPunctureUpperParameter p q r)) ∧
       (∀ t : unitInterval,
        (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q r hr hrU hpre hqre
            (embeddedTwoPunctureAnnulusRightConnector f p q r η rightHalf t) : ℂ) ∈
          twoPuncturedDiskLowerSide
            (embeddedTwoPunctureLowerParameter p q r)
            (embeddedTwoPunctureUpperParameter p q r)))) ∧
    ((embeddedTwoPunctureAnnulusLeftConnector f p q r leftHalf η).symm.trans
      (embeddedTwoPunctureAnnulusRightConnector f p q r η rightHalf)).Homotopic
        (leftHalf.trans rightHalf) := by
  let E : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r} → ℂ :=
    fun y => (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q r hr hrU hpre hqre y : ℂ)
  let α := embeddedTwoPunctureLowerParameter p q r
  let β := embeddedTwoPunctureUpperParameter p q r
  let cLeft := embeddedTwoPunctureAnnulusLeftConnector f p q r leftHalf η
  let cRight := embeddedTwoPunctureAnnulusRightConnector f p q r η rightHalf
  constructor
  · rcases horder with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
    · left
      constructor
      · intro t
        exact path_mem_symm (leftHalf.trans η) E
          (twoPuncturedDiskLowerSide α β)
          (path_mem_trans leftHalf η E (twoPuncturedDiskLowerSide α β)
            hleft hηLower) t
      · intro t
        exact path_mem_trans η.symm rightHalf E
          (twoPuncturedDiskUpperSide α β)
          (path_mem_symm η E (twoPuncturedDiskUpperSide α β) hηUpper)
          hright t
    · right
      constructor
      · intro t
        exact path_mem_symm (leftHalf.trans η) E
          (twoPuncturedDiskUpperSide α β)
          (path_mem_trans leftHalf η E (twoPuncturedDiskUpperSide α β)
            hleft hηUpper) t
      · intro t
        exact path_mem_trans η.symm rightHalf E
          (twoPuncturedDiskLowerSide α β)
          (path_mem_symm η E (twoPuncturedDiskLowerSide α β) hηLower)
          hright t
  · have hpaths : cLeft.symm.trans cRight =
        (leftHalf.trans η).trans (η.symm.trans rightHalf) := by
      simp [cLeft, cRight, embeddedTwoPunctureAnnulusLeftConnector,
        embeddedTwoPunctureAnnulusRightConnector]
    rw [hpaths]
    apply Path.Homotopic.Quotient.exact
    simp only [Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_symm]
    rw [Path.Homotopic.Quotient.trans_assoc
      (Path.Homotopic.Quotient.mk leftHalf)
      (Path.Homotopic.Quotient.mk η)
      (Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk η))
        (Path.Homotopic.Quotient.mk rightHalf)),
      ← Path.Homotopic.Quotient.trans_assoc
      (Path.Homotopic.Quotient.mk η)
      (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk η))
      (Path.Homotopic.Quotient.mk rightHalf),
      Path.Homotopic.Quotient.trans_symm,
      Path.Homotopic.Quotient.refl_trans]

end

end SystolicGrowth

#print axioms SystolicGrowth.twoPuncturedDiskRelativeOverlapSegmentPath
#print axioms SystolicGrowth.embeddedTwoPunctureRelativeLocalDiskOverlapConnector
#print axioms SystolicGrowth.embeddedTwoPunctureRelativeLocalDiskOverlapConnector_mem_sides
#print axioms SystolicGrowth.exists_embeddedTwoPunctureAnnulusLocalConnector
#print axioms SystolicGrowth.embeddedTwoPunctureAnnulusConnectorPair
