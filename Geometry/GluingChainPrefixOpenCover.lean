module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainCollarRetraction
public import Geometry.GluingChainVanKampen
public import Geometry.GluingChainCoverConnected

@[expose] public section

/-!
# The retained prefix open-cover diagram

Restrict the already-constructed two-sided cover at seam `j` to an actual
closed prefix ending after component `k`. When `j < k`, both retained sides
of the original seam neighborhood lie in that prefix, so the overlap is the
same literal seam-image subtype, with its original basepoint.
-/

open Set
open scoped ContinuousMap

namespace SystolicGrowth
namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Literal subtype inclusion of the actual closed prefix into the original
glued carrier. -/
def gluedChainPrefixCarrierInclusion
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    C(↥(P.gluedChainPrefix k), P.GluedCarrier) where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val

/-- Pull back one of the already constructed full-carrier seam-cover sides
along the literal inclusion of the retained prefix. The definition does not
need an ordering hypothesis. -/
def gluedChainPrefixCoverSide
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (b : Bool) : Set ↥(P.gluedChainPrefix k) :=
  (P.gluedChainPrefixCarrierInclusion k) ⁻¹' P.gluedChainCoverSide j b

/-- The actual overlap of the two pulled-back sides. -/
def gluedChainPrefixCoverOverlap
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) : Set ↥(P.gluedChainPrefix k) :=
  P.gluedChainPrefixCoverSide k j true ∩ P.gluedChainPrefixCoverSide k j false

/-- Each full-carrier side is open, and its pullback to the actual prefix is
open in the prefix subspace topology. -/
theorem gluedChainPrefixCoverSide_isOpen
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (b : Bool) :
    IsOpen (P.gluedChainPrefixCoverSide k j b) := by
  cases b
  · simpa [gluedChainPrefixCoverSide, gluedChainCoverSide] using
      (P.gluedChainSuffixNeighborhood_isOpen j).preimage
        (P.gluedChainPrefixCarrierInclusion k).continuous
  · simpa [gluedChainPrefixCoverSide, gluedChainCoverSide] using
      (P.gluedChainPrefixNeighborhood_isOpen j).preimage
        (P.gluedChainPrefixCarrierInclusion k).continuous

/-- The restricted sides still cover every point of the actual prefix. -/
theorem gluedChainPrefixCoverSide_union
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) :
    P.gluedChainPrefixCoverSide k j true ∪
      P.gluedChainPrefixCoverSide k j false = Set.univ := by
  ext x
  change (x.1 ∈ P.gluedChainCoverSide j true ∨
    x.1 ∈ P.gluedChainCoverSide j false) ↔ True
  constructor
  · intro _
    trivial
  · intro _
    have hu := P.gluedChainPrefixNeighborhood_union_suffix j
    have hx : x.1 ∈ P.gluedChainPrefixNeighborhood j ∪
        P.gluedChainSuffixNeighborhood j := by
      rw [hu]
      exact Set.mem_univ _
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx

/-- The overlap is exactly the pullback of the original full two-sided seam
neighborhood; no puncture disk or collar is truncated at the prefix end. -/
theorem gluedChainPrefixCoverOverlap_eq_preimage_seamNeighborhood
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) :
    P.gluedChainPrefixCoverOverlap k j =
      (P.gluedChainPrefixCarrierInclusion k) ⁻¹'
        (P.gluedMk '' P.seamNeighborhood j) := by
  ext x
  change (x.1 ∈ P.gluedChainCoverSide j true ∧
      x.1 ∈ P.gluedChainCoverSide j false) ↔
    x.1 ∈ P.gluedMk '' P.seamNeighborhood j
  rw [← P.gluedChainPrefixNeighborhood_inter_suffix j]
  simp only [gluedChainCoverSide, if_pos, mem_inter_iff]
  simp

theorem gluedChainPrefixCoverOverlap_val_mem_seamNeighborhood
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (x : ↥(P.gluedChainPrefix k))
    (hx : x ∈ P.gluedChainPrefixCoverOverlap k j) :
    x.1 ∈ P.gluedMk '' P.seamNeighborhood j := by
  have hx' : x ∈ P.gluedChainPrefixCoverSide k j true ∧
      x ∈ P.gluedChainPrefixCoverSide k j false := hx
  have hleft : x.1 ∈ P.gluedChainPrefixNeighborhood j := by
    simpa [gluedChainPrefixCoverSide, gluedChainCoverSide,
      gluedChainPrefixCarrierInclusion] using hx'.1
  have hright : x.1 ∈ P.gluedChainSuffixNeighborhood j := by
    simpa [gluedChainPrefixCoverSide, gluedChainCoverSide,
      gluedChainPrefixCarrierInclusion] using hx'.2
  rw [← P.gluedChainPrefixNeighborhood_inter_suffix j]
  exact ⟨hleft, hright⟩

/-- The pulled-back overlap is homeomorphic to the original seam-image
subtype by the literal ambient-value identity. -/
def gluedChainPrefixCoverOverlapHomeomorph
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val) :
    ↥(P.gluedMk '' P.seamNeighborhood j) ≃ₜ
      ↥(P.gluedChainPrefixCoverOverlap k j) where
  toFun x := ⟨⟨x.1, P.gluedMk_image_seamNeighborhood_subset_prefix_of_lt j k hjk x.2⟩, by
    rw [P.gluedChainPrefixCoverOverlap_eq_preimage_seamNeighborhood]
    exact x.2⟩
  invFun y := ⟨y.1.1,
    P.gluedChainPrefixCoverOverlap_val_mem_seamNeighborhood k j y.1 y.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk
    (fun x => P.gluedMk_image_seamNeighborhood_subset_prefix_of_lt j k hjk x.2)).subtype_mk
      (fun x => by
        rw [P.gluedChainPrefixCoverOverlap_eq_preimage_seamNeighborhood]
        exact x.2)
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
    (fun y => P.gluedChainPrefixCoverOverlap_val_mem_seamNeighborhood k j y.1 y.2)

/-- When the cut `j` precedes the retained endpoint `k`, the entire original
left cover side survives in the retained prefix. This homeomorphism is the
literal inclusion, with inverse given by the same ambient value. -/
def gluedChainPrefixLeftCoverSideHomeomorph
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val) :
    ↥(P.gluedChainPrefixNeighborhood j) ≃ₜ
      ↥(P.gluedChainPrefixCoverSide k j true) where
  toFun x := ⟨⟨x.1,
      P.gluedChainPrefixNeighborhood_subset_laterPrefix j k hjk x.2⟩, by
    change (P.gluedChainPrefixCarrierInclusion k)
      ⟨x.1, P.gluedChainPrefixNeighborhood_subset_laterPrefix j k hjk x.2⟩ ∈
        P.gluedChainCoverSide j true
    exact x.2⟩
  invFun y := ⟨y.1.1, by
    simpa [gluedChainPrefixCoverSide, gluedChainPrefixCarrierInclusion,
      gluedChainCoverSide] using y.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk
    (fun x => P.gluedChainPrefixNeighborhood_subset_laterPrefix j k hjk x.2)).subtype_mk
      (fun x => by
        exact x.2)
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
    (fun y => by
      have hy : y.1.1 ∈ P.gluedChainPrefixNeighborhood j := by
        simpa [gluedChainPrefixCoverSide, gluedChainPrefixCarrierInclusion,
          gluedChainCoverSide] using y.2
      exact hy)

/-- The retained left cover side is path connected because it is homeomorphic
to the full original prefix neighborhood, not a truncated collar. -/
theorem gluedChainPrefixLeftCoverSidePathConnectedSpace
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val) :
    PathConnectedSpace ↥(P.gluedChainPrefixCoverSide k j true) := by
  letI : PathConnectedSpace ↥(P.gluedChainPrefixNeighborhood j) :=
    P.gluedChainPrefixNeighborhoodPathConnectedSpace j
  exact Function.Surjective.pathConnectedSpace
    (P.gluedChainPrefixLeftCoverSideHomeomorph k j hjk).surjective
    (P.gluedChainPrefixLeftCoverSideHomeomorph k j hjk).continuous

/-- The actual prefix-cover overlap is path connected: under its literal
homeomorphism it is the original full seam neighborhood. -/
theorem gluedChainPrefixCoverOverlapPathConnectedSpace
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val) :
    PathConnectedSpace ↥(P.gluedChainPrefixCoverOverlap k j) := by
  letI : PathConnectedSpace ↥(P.gluedMk '' P.seamNeighborhood j) :=
    isPathConnected_iff_pathConnectedSpace.mp (P.gluedSeamNeighborhood_isPathConnected j)
  exact Function.Surjective.pathConnectedSpace
    (P.gluedChainPrefixCoverOverlapHomeomorph k j hjk).surjective
    (P.gluedChainPrefixCoverOverlapHomeomorph k j hjk).continuous

/-- The overlap homeomorphism preserves the original seam-circle basepoint
as an ambient point, so paths and based groups use no new basepoint choice. -/
theorem gluedChainPrefixCoverOverlapHomeomorph_apply_circlePoint
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val) (θ : Circle) :
    ((P.gluedChainPrefixCoverOverlapHomeomorph k j hjk
      (P.gluedSeamCircleInclusion j θ)).1).1 =
      (P.gluedSeamCircleInclusion j θ).1 := rfl

#print axioms gluedChainPrefixCarrierInclusion
#print axioms gluedChainPrefixCoverSide_isOpen
#print axioms gluedChainPrefixCoverSide_union
#print axioms gluedChainPrefixCoverOverlap_eq_preimage_seamNeighborhood
#print axioms gluedChainPrefixCoverOverlapHomeomorph
#print axioms gluedChainPrefixCoverOverlapHomeomorph_apply_circlePoint
#print axioms gluedChainPrefixLeftCoverSideHomeomorph
#print axioms gluedChainPrefixLeftCoverSidePathConnectedSpace
#print axioms gluedChainPrefixCoverOverlapPathConnectedSpace

end ExerciseGluingPreparation
end SystolicGrowth
