module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainPrefixOpenCover
public import Geometry.GluingChainCoverConnected
public import Geometry.GluingChainTopology
public import Geometry.SurfaceTwoCenterBoundarySpine

@[expose] public section

/-!
# The actual suffix collar restricted to a retained prefix

Restrict the full suffix-side collar homotopy at an earlier cut to the
pullback cover side in a later actual prefix. Its endpoint is the literal
intersection of the retained prefix and suffix; at adjacent cuts this is
exactly the intervening original component image.
-/

open Set
open scoped ContinuousMap unitInterval

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

theorem gluedChainPrefixRightCoverSide_mem_suffixNeighborhood
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (x : ↥(P.gluedChainPrefixCoverSide k j false)) :
    x.1.1 ∈ P.gluedChainSuffixNeighborhood j := by
  have hx := x.2
  change (P.gluedChainPrefixCarrierInclusion k x.1) ∈
    P.gluedChainCoverSide j false at hx
  simpa [gluedChainPrefixCarrierInclusion, gluedChainCoverSide] using hx

def gluedChainPrefixRightCoverSideToSuffixNeighborhood
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) :
    C(↥(P.gluedChainPrefixCoverSide k j false),
      ↥(P.gluedChainSuffixNeighborhood j)) where
  toFun x := ⟨x.1.1,
    P.gluedChainPrefixRightCoverSide_mem_suffixNeighborhood k j x⟩
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- Include the actual closed intersection into the pulled-back right side
of the original cover. -/
def gluedChainPrefixRightCoverSideInclusion
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) :
    C(↥(P.gluedChainPrefix k ∩ P.gluedChainSuffix j),
      ↥(P.gluedChainPrefixCoverSide k j false)) where
  toFun x := ⟨⟨x.1, x.2.1⟩, by
    change x.1 ∈ P.gluedChainSuffixNeighborhood j
    exact Or.inl x.2.2⟩
  continuous_toFun :=
    (continuous_subtype_val.subtype_mk (fun x => x.2.1)).subtype_mk (fun x => by
      change x.1 ∈ P.gluedChainSuffixNeighborhood j
      exact Or.inl x.2.2)

/-- Restrict the actual global suffix retraction. The preservation theorem
keeps its image in the later prefix throughout the native collar motion. -/
def gluedChainPrefixRightCoverSideRetraction
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val) :
    C(↥(P.gluedChainPrefixCoverSide k j false),
      ↥(P.gluedChainPrefix k ∩ P.gluedChainSuffix j)) := by
  let h := P.gluedChainPrefixRightCoverSideToSuffixNeighborhood k j
  let r : C(↥(P.gluedChainPrefixCoverSide k j false), P.GluedCarrier) := {
    toFun x := (P.gluedChainSuffixRetraction j (h x)).1
    continuous_toFun :=
      ((P.gluedChainSuffixRetraction j).continuous.comp h.continuous).subtype_val }
  have hm (x : ↥(P.gluedChainPrefixCoverSide k j false)) :
      r x ∈ P.gluedChainPrefix k ∩ P.gluedChainSuffix j := by
    constructor
    · dsimp [r]
      change ((P.gluedChainSuffixDeformationRetraction j).toHomotopy
        (1, h x)).1 ∈ P.gluedChainPrefix k
      exact P.gluedChainSuffixDeformationRetraction_preserves_laterPrefix
        j k hjk 1 (h x) x.1.2
    · dsimp [r]
      exact (P.gluedChainSuffixRetraction j (h x)).2
  exact ⟨fun x => ⟨r x, hm x⟩, r.continuous.subtype_mk hm⟩

/-- The restricted inclusion and retraction compose to the identity on the
actual closed prefix/suffix intersection. -/
@[simp] theorem gluedChainPrefixRightCoverSideRetraction_inclusion
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val)
    (x : ↥(P.gluedChainPrefix k ∩ P.gluedChainSuffix j)) :
    P.gluedChainPrefixRightCoverSideRetraction k j hjk
      (P.gluedChainPrefixRightCoverSideInclusion k j x) = x := by
  apply Subtype.ext
  change (P.gluedChainSuffixRetraction j
    (P.gluedChainPrefixRightCoverSideToSuffixNeighborhood k j
      (P.gluedChainPrefixRightCoverSideInclusion k j x))).1 = x.1
  have hy : P.gluedChainPrefixRightCoverSideToSuffixNeighborhood k j
      (P.gluedChainPrefixRightCoverSideInclusion k j x) =
      P.gluedChainSuffixInclusion j ⟨x.1, x.2.2⟩ := by
    apply Subtype.ext
    rfl
  rw [hy, P.gluedChainSuffixRetraction_inclusion]

/-- Restrict the entire strong deformation retraction, not only its endpoint,
to the actual prefix preimage of the full suffix neighborhood. -/
def gluedChainPrefixRightCoverSideDeformationRetraction
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val) :
    (ContinuousMap.id ↥(P.gluedChainPrefixCoverSide k j false)).HomotopyRel
      ((P.gluedChainPrefixRightCoverSideInclusion k j).comp
        (P.gluedChainPrefixRightCoverSideRetraction k j hjk))
      {x | x.1.1 ∈ P.gluedChainSuffix j} where
  toHomotopy := by
    let H := (P.gluedChainSuffixDeformationRetraction j).toHomotopy
    let ρ := P.gluedChainPrefixRightCoverSideToSuffixNeighborhood k j
    let w : C(I × ↥(P.gluedChainPrefixCoverSide k j false), P.GluedCarrier) := {
      toFun p := (H (p.1, ρ p.2)).1
      continuous_toFun := (H.continuous.comp
        (continuous_fst.prodMk (ρ.continuous.comp continuous_snd))).subtype_val }
    have hpref (p : I × ↥(P.gluedChainPrefixCoverSide k j false)) :
        w p ∈ P.gluedChainPrefix k := by
      change (H (p.1, ρ p.2)).1 ∈ P.gluedChainPrefix k
      exact P.gluedChainSuffixDeformationRetraction_preserves_laterPrefix
        j k hjk p.1 (ρ p.2) p.2.1.2
    have hside (p : I × ↥(P.gluedChainPrefixCoverSide k j false)) :
        ⟨w p, hpref p⟩ ∈ P.gluedChainPrefixCoverSide k j false := by
      change w p ∈ P.gluedChainSuffixNeighborhood j
      exact (H (p.1, ρ p.2)).2
    refine {
      toContinuousMap := {
        toFun p := ⟨⟨w p, hpref p⟩, hside p⟩
        continuous_toFun :=
          (w.continuous.subtype_mk hpref).subtype_mk hside }
      map_zero_left := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        have hz := congrArg Subtype.val (H.map_zero_left (ρ x))
        change (H (0, ρ x)).1 = (ρ x).1 at hz
        change (H (0, ρ x)).1 = x.1.1
        exact hz
      map_one_left := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        rfl }
  prop' := by
    intro t x hx
    apply Subtype.ext
    apply Subtype.ext
    let ρ := P.gluedChainPrefixRightCoverSideToSuffixNeighborhood k j
    have hfix :=
      (P.gluedChainSuffixDeformationRetraction j).prop' t (ρ x) hx
    change ((P.gluedChainSuffixDeformationRetraction j).toHomotopy
      (t, ρ x)).1 = x.1.1
    simpa [ρ, gluedChainPrefixRightCoverSideToSuffixNeighborhood] using
      congrArg Subtype.val hfix

/-- The actual restricted open side and closed intersection are homotopy
equivalent through the suffix retraction; the deformation fixes the entire
closed target pointwise, hence is based at every target point. -/
def gluedChainPrefixRightCoverSideHomotopyEquiv
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val) :
    ↥(P.gluedChainPrefixCoverSide k j false) ≃ₕ
      ↥(P.gluedChainPrefix k ∩ P.gluedChainSuffix j) where
  toFun := P.gluedChainPrefixRightCoverSideRetraction k j hjk
  invFun := P.gluedChainPrefixRightCoverSideInclusion k j
  left_inv := ⟨
    (P.gluedChainPrefixRightCoverSideDeformationRetraction k j hjk).toHomotopy.symm⟩
  right_inv := by
    have h : (P.gluedChainPrefixRightCoverSideRetraction k j hjk).comp
        (P.gluedChainPrefixRightCoverSideInclusion k j) =
          ContinuousMap.id ↥(P.gluedChainPrefix k ∩ P.gluedChainSuffix j) := by
      apply ContinuousMap.ext
      intro x
      exact P.gluedChainPrefixRightCoverSideRetraction_inclusion k j hjk x
    rw [h]

/-- A retained component is path connected: the actual center-punctured
component retracts continuously onto it, and the punctured component is
path connected by the proved two-center spine argument. -/
theorem chainComponentPathConnectedSpace
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    PathConnectedSpace (P.ChainComponent i) := by
  letI : PathConnectedSpace (P.CenterPuncturedChainComponent i) :=
    P.componentCenterPuncturedPathConnectedSpace i
  have hsurj : Function.Surjective (P.componentPunctureRetraction i) := by
    intro x
    exact ⟨P.componentPunctureInclusion i x,
      P.componentPunctureRetraction_inclusion i x⟩
  exact hsurj.pathConnectedSpace (P.componentPunctureRetraction i).continuous

/-- The adjacent closed intersection is the original retained component,
identified by the actual quotient embedding. -/
noncomputable def gluedChainPrefixSuffixComponentHomeomorph
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val) :
    P.ChainComponent (gluingChainEdgeLeft k) ≃ₜ
      ↥(P.gluedChainPrefix k ∩ P.gluedChainSuffix j) :=
  (P.gluedComponentHomeomorph (gluingChainEdgeLeft k)).trans
    (Homeomorph.setCongr
      (P.gluedChainPrefix_inter_suffix_eq_componentImage j k hjk).symm)

/-- The actual closed target is path connected for adjacent cuts. -/
theorem gluedChainPrefixSuffixIntersectionPathConnectedSpace
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val) :
    PathConnectedSpace ↥(P.gluedChainPrefix k ∩ P.gluedChainSuffix j) := by
  let e := P.gluedChainPrefixSuffixComponentHomeomorph k j hjk
  letI : PathConnectedSpace (P.ChainComponent (gluingChainEdgeLeft k)) :=
    P.chainComponentPathConnectedSpace (gluingChainEdgeLeft k)
  exact e.surjective.pathConnectedSpace e.continuous

/-- The pulled-back right side of the actual prefix cover is path connected
at adjacent cuts, using its restricted native strong deformation retraction. -/
theorem gluedChainPrefixRightCoverSidePathConnectedSpace
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val) :
    PathConnectedSpace ↥(P.gluedChainPrefixCoverSide k j false) := by
  letI : PathConnectedSpace ↥(P.gluedChainPrefix k ∩ P.gluedChainSuffix j) :=
    P.gluedChainPrefixSuffixIntersectionPathConnectedSpace k j hjk
  let i := P.gluedChainPrefixRightCoverSideInclusion k j
  let r := P.gluedChainPrefixRightCoverSideRetraction k j (by omega)
  let H := P.gluedChainPrefixRightCoverSideDeformationRetraction k j (by omega)
  let track (x : ↥(P.gluedChainPrefixCoverSide k j false)) :
      Path x (i (r x)) := {
    toFun := fun t => H.toHomotopy (t, x)
    continuous_toFun := H.toHomotopy.continuous.comp
      (continuous_id.prodMk continuous_const)
    source' := H.toHomotopy.map_zero_left x
    target' := H.toHomotopy.map_one_left x }
  constructor
  · exact ⟨i (Classical.choice inferInstance)⟩
  · intro x y
    exact ⟨(track x).trans
      (((PathConnectedSpace.somePath (r x) (r y)).map i.continuous).trans
        (track y).symm)⟩

#print axioms gluedChainPrefixRightCoverSideInclusion
#print axioms gluedChainPrefixRightCoverSideRetraction
#print axioms gluedChainPrefixRightCoverSideRetraction_inclusion
#print axioms gluedChainPrefixRightCoverSideDeformationRetraction
#print axioms gluedChainPrefixRightCoverSideHomotopyEquiv
#print axioms chainComponentPathConnectedSpace
#print axioms gluedChainPrefixSuffixComponentHomeomorph
#print axioms gluedChainPrefixSuffixIntersectionPathConnectedSpace
#print axioms gluedChainPrefixRightCoverSidePathConnectedSpace

end

end ExerciseGluingPreparation
end SystolicGrowth
