module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainPrefixBaseCases
public import Geometry.GluingChainPrefixOpenCover
public import Geometry.SurfaceRetainedPolarBoundary
public import Geometry.TwoPuncturedDiskFreePresentation

@[expose] public section

/-!
# The unchanged outgoing polar boundary of a retained prefix

The recursive marking is based at the actual outgoing polar circle, not an
arbitrary point. At the first prefix its based group and positive boundary
class are transported literally from the first original retained component.
-/

open Set

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Math. Include the final component of a prefix in that original prefix. -/
def gluedChainPrefixLastComponentInclusion
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    C(P.ChainComponent (gluingChainEdgeLeft k), ↥(P.gluedChainPrefix k)) where
  toFun x := ⟨P.gluedMk ⟨gluingChainEdgeLeft k, x⟩,
    ⟨⟨gluingChainEdgeLeft k, x⟩, by change k.val ≤ k.val; exact le_rfl, rfl⟩⟩
  continuous_toFun := (P.gluedMk_continuous.comp continuous_sigmaMk).subtype_mk _

/-- Math. The retained outgoing circle of the original prefix. -/
def gluedChainPrefixRightPolarBoundaryMap
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    C(Circle, ↥(P.gluedChainPrefix k)) :=
  (P.gluedChainPrefixLastComponentInclusion k).comp
    (P.componentRetainedRightPolarBoundaryMap (gluingChainEdgeLeft k))

/-- Math. Its literal positive one-turn loop at angle one. -/
def gluedChainPrefixRightPolarBoundaryLoop
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Path (P.gluedChainPrefixRightPolarBoundaryMap k 1)
      (P.gluedChainPrefixRightPolarBoundaryMap k 1) :=
  (circleOneTurnLoop 1).map (P.gluedChainPrefixRightPolarBoundaryMap k).continuous

/-- Math. The prefix boundary loop is the included original component loop. -/
theorem gluedChainPrefixRightPolarBoundaryLoop_eq_map
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedChainPrefixRightPolarBoundaryLoop k =
      (P.componentRetainedRightPolarBoundaryLoop (gluingChainEdgeLeft k)).map
        (P.gluedChainPrefixLastComponentInclusion k).continuous := by
  apply Path.ext
  rfl

/-- Math. The actual prefix boundary point is the original outgoing seam point. -/
theorem gluedChainPrefixRightPolarBoundaryMap_val_eq_seam
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : Circle) :
    (P.gluedChainPrefixRightPolarBoundaryMap k θ).val =
      (P.gluedSeamCircleInclusion k θ).val := by
  rw [P.gluedSeamCircleInclusion_eq_outgoing k θ]
  rfl

/-- Math. Include an earlier original retained prefix in a later one. -/
def gluedChainPrefixInclusionOfLE
    (P : ExerciseGluingPreparation C g n genera X) (j k : Fin (n - 1))
    (hjk : j.val ≤ k.val) :
    C(↥(P.gluedChainPrefix j), ↥(P.gluedChainPrefix k)) where
  toFun x := ⟨x.1, P.gluedChainPrefix_subset_of_le j k hjk x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Math. View the original earlier seam circle in a later retained prefix. -/
def gluedChainPrefixSeamCircleMap
    (P : ExerciseGluingPreparation C g n genera X) (k j : Fin (n - 1))
    (hjk : j.val < k.val) : C(Circle, ↥(P.gluedChainPrefix k)) where
  toFun θ := ⟨(P.gluedSeamCircleInclusion j θ).val,
    P.gluedMk_image_seamNeighborhood_subset_prefix_of_lt j k hjk
      (P.gluedSeamCircleInclusion j θ).property⟩
  continuous_toFun :=
    (continuous_subtype_val.comp (P.gluedSeamCircleInclusion j).continuous).subtype_mk _

/-- Math. The overlap circle is literally the earlier prefix's outgoing circle. -/
theorem gluedChainPrefixSeamCircleMap_eq_included_boundary
    (P : ExerciseGluingPreparation C g n genera X) (k j : Fin (n - 1))
    (hjk : j.val < k.val) :
    P.gluedChainPrefixSeamCircleMap k j hjk =
      (P.gluedChainPrefixInclusionOfLE j k hjk.le).comp
        (P.gluedChainPrefixRightPolarBoundaryMap j) := by
  apply ContinuousMap.ext
  intro θ
  apply Subtype.ext
  exact (P.gluedChainPrefixRightPolarBoundaryMap_val_eq_seam j θ).symm

/-- Math. The literal one-turn overlap path is the included earlier boundary path. -/
theorem gluedChainPrefixSeamCircleMap_oneTurn_eq_included_boundary
    (P : ExerciseGluingPreparation C g n genera X) (k j : Fin (n - 1))
    (hjk : j.val < k.val) :
    ((circleOneTurnLoop 1).map (P.gluedChainPrefixSeamCircleMap k j hjk).continuous).cast
      (by rw [P.gluedChainPrefixSeamCircleMap_eq_included_boundary k j hjk]; rfl)
      (by rw [P.gluedChainPrefixSeamCircleMap_eq_included_boundary k j hjk]; rfl) =
        (P.gluedChainPrefixRightPolarBoundaryLoop j).map
          (P.gluedChainPrefixInclusionOfLE j k hjk.le).continuous := by
  apply Path.ext
  funext t
  exact congrArg (fun f : C(Circle, ↥(P.gluedChainPrefix k)) => f (circleOneTurnLoop 1 t))
    (P.gluedChainPrefixSeamCircleMap_eq_included_boundary k j hjk)

/-- Math. The first-prefix based group is the original retained component group. -/
def gluedChainPrefixZeroPolarFundamentalGroupEquiv
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (hk : k.val = 0) :
    FundamentalGroup ↥(P.gluedChainPrefix k)
        (P.gluedChainPrefixRightPolarBoundaryMap k 1) ≃*
      FundamentalGroup (P.ChainComponent (gluingChainEdgeLeft k))
        (P.componentRetainedRightPolarBoundaryMap (gluingChainEdgeLeft k) 1) :=
  (fundamentalGroupHomeomorphEquiv (P.gluedChainPrefixZeroHomeomorph k hk)
    (P.componentRetainedRightPolarBoundaryMap (gluingChainEdgeLeft k) 1)).symm

set_option backward.isDefEq.respectTransparency false in
/-- Math. The first-prefix equivalence preserves the actual positive boundary class. -/
theorem gluedChainPrefixZeroPolarFundamentalGroupEquiv_boundary
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (hk : k.val = 0) :
    P.gluedChainPrefixZeroPolarFundamentalGroupEquiv k hk
      ⟦P.gluedChainPrefixRightPolarBoundaryLoop k⟧ =
        ⟦P.componentRetainedRightPolarBoundaryLoop (gluingChainEdgeLeft k)⟧ := by
  apply (fundamentalGroupHomeomorphEquiv (P.gluedChainPrefixZeroHomeomorph k hk)
    (P.componentRetainedRightPolarBoundaryMap (gluingChainEdgeLeft k) 1)).injective
  change (fundamentalGroupHomeomorphEquiv (P.gluedChainPrefixZeroHomeomorph k hk)
    (P.componentRetainedRightPolarBoundaryMap (gluingChainEdgeLeft k) 1))
    ((fundamentalGroupHomeomorphEquiv (P.gluedChainPrefixZeroHomeomorph k hk)
      (P.componentRetainedRightPolarBoundaryMap (gluingChainEdgeLeft k) 1)).symm
      ⟦P.gluedChainPrefixRightPolarBoundaryLoop k⟧) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- Math. Include the first retained component of a suffix in that suffix. -/
def gluedChainSuffixFirstComponentInclusion
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    C(P.ChainComponent (gluingChainEdgeRight k), ↥(P.gluedChainSuffix k)) where
  toFun x := ⟨P.gluedMk ⟨gluingChainEdgeRight k, x⟩,
    ⟨⟨gluingChainEdgeRight k, x⟩, by change k.val < k.val + 1; omega, rfl⟩⟩
  continuous_toFun := (P.gluedMk_continuous.comp continuous_sigmaMk).subtype_mk _

/-- Math. The actual incoming polar circle of a retained suffix. -/
def gluedChainSuffixLeftPolarBoundaryMap
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    C(Circle, ↥(P.gluedChainSuffix k)) :=
  (P.gluedChainSuffixFirstComponentInclusion k).comp
    (P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeRight k))

/-- Math. The actual positive incoming boundary loop in a retained suffix. -/
def gluedChainSuffixLeftPolarBoundaryLoop
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Path (P.gluedChainSuffixLeftPolarBoundaryMap k 1)
      (P.gluedChainSuffixLeftPolarBoundaryMap k 1) :=
  (circleOneTurnLoop 1).map (P.gluedChainSuffixLeftPolarBoundaryMap k).continuous

/-- Math. The last-suffix based group is the original retained endpoint group. -/
def gluedChainSuffixLastPolarFundamentalGroupEquiv
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (hk : k.val + 2 = n) :
    FundamentalGroup ↥(P.gluedChainSuffix k)
        (P.gluedChainSuffixLeftPolarBoundaryMap k 1) ≃*
      FundamentalGroup (P.ChainComponent (gluingChainEdgeRight k))
        (P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeRight k) 1) :=
  (fundamentalGroupHomeomorphEquiv (P.gluedChainSuffixLastHomeomorph k hk)
    (P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeRight k) 1)).symm

set_option backward.isDefEq.respectTransparency false in
/-- Math. The last-suffix equivalence preserves the positive incoming class. -/
theorem gluedChainSuffixLastPolarFundamentalGroupEquiv_boundary
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (hk : k.val + 2 = n) :
    P.gluedChainSuffixLastPolarFundamentalGroupEquiv k hk
      ⟦P.gluedChainSuffixLeftPolarBoundaryLoop k⟧ =
        ⟦P.componentRetainedLeftPolarBoundaryLoop (gluingChainEdgeRight k)⟧ := by
  apply (fundamentalGroupHomeomorphEquiv (P.gluedChainSuffixLastHomeomorph k hk)
    (P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeRight k) 1)).injective
  change (fundamentalGroupHomeomorphEquiv (P.gluedChainSuffixLastHomeomorph k hk)
    (P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeRight k) 1))
    ((fundamentalGroupHomeomorphEquiv (P.gluedChainSuffixLastHomeomorph k hk)
      (P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeRight k) 1)).symm
      ⟦P.gluedChainSuffixLeftPolarBoundaryLoop k⟧) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

#print axioms gluedChainPrefixRightPolarBoundaryMap_val_eq_seam
#print axioms gluedChainPrefixSeamCircleMap_eq_included_boundary
#print axioms gluedChainPrefixSeamCircleMap_oneTurn_eq_included_boundary
#print axioms gluedChainPrefixZeroPolarFundamentalGroupEquiv
#print axioms gluedChainPrefixZeroPolarFundamentalGroupEquiv_boundary
#print axioms gluedChainSuffixLastPolarFundamentalGroupEquiv
#print axioms gluedChainSuffixLastPolarFundamentalGroupEquiv_boundary

end

end SystolicGrowth.ExerciseGluingPreparation
