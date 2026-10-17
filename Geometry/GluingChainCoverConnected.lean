module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainOpenCover
public import Geometry.GluingConnected
public import Geometry.GluingLocalContractibility
public import Geometry.GluingSeamFundamentalGroup
public import Mathlib.Data.Fin.SuccPredOrder

@[expose] public section

/-!
# Connectedness of the actual chain-cover pieces

The closed prefix and suffix are connected unions of the original retained
component images. Consecutive images meet at genuine identified seam points.
Thickening either side by the original seam neighborhood preserves connectedness;
native local path connectedness then makes these actual open sides path connected.
No component, seam, or cover connectedness is added as a hypothesis.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Each original retained component has connected image in the original quotient. -/
theorem gluedComponentImage_isConnected
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    IsConnected (Set.range (fun a : P.ChainComponent i => P.gluedMk ⟨i, a⟩)) :=
  isConnected_range (P.gluedMk_continuous.comp continuous_sigmaMk)

private theorem gluedComponentImage_inter_orderSucc_nonempty
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    (Set.range (fun a : P.ChainComponent i => P.gluedMk ⟨i, a⟩) ∩
      Set.range (fun a : P.ChainComponent (Order.succ i) =>
        P.gluedMk ⟨Order.succ i, a⟩)).Nonempty := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ m =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.orderSucc_last]
      exact (P.gluedComponentImage_isConnected (Fin.last m)).nonempty.mono
        (fun _ h => ⟨h, h⟩)
    · rw [Fin.orderSucc_castSucc]
      let k : Fin ((m + 1) - 1) := ⟨j.val, by have := j.isLt; omega⟩
      let z : sphere (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) :=
        ⟨gluingPolarPoint (P.centers (gluingChainEdgeLeft k)).2 1 (gluingRadius C g), by
          simpa only [mem_sphere, dist_comm] using
            dist_gluingPolarPoint (P.centers (gluingChainEdgeLeft k)).2 1 P.radius_pos.le⟩
      have hleft : gluingChainEdgeLeft k = j.castSucc := Fin.ext rfl
      have hright : gluingChainEdgeRight k = j.succ := Fin.ext rfl
      refine ⟨P.gluedMk (P.seamSource k z), ?_, ?_⟩
      · rw [← hleft]
        exact ⟨P.rightCirclePoint _ z, rfl⟩
      · rw [P.gluedMk_seamSource_eq_seamTarget k z, ← hright]
        exact ⟨P.leftCirclePoint _ (gluingBoundaryCircleIsometry _ _ _ z), rfl⟩

private theorem gluedMk_image_indexSet_eq_biUnion
    (P : ExerciseGluingPreparation C g n genera X) (t : Set (Fin n)) :
    P.gluedMk '' {a | a.1 ∈ t} =
      ⋃ i ∈ t, Set.range (fun a : P.ChainComponent i => P.gluedMk ⟨i, a⟩) := by
  ext q
  constructor
  · rintro ⟨⟨i, a⟩, hi, rfl⟩
    exact mem_iUnion₂.mpr ⟨i, hi, a, rfl⟩
  · intro hq
    obtain ⟨i, hi, a, rfl⟩ := mem_iUnion₂.mp hq
    exact ⟨⟨i, a⟩, hi, rfl⟩

/-- The actual closed prefix is connected, using each original intervening seam. -/
theorem gluedChainPrefix_isConnected
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    IsConnected (P.gluedChainPrefix k) := by
  change IsConnected (P.gluedMk '' {a | a.1 ∈ Iic (gluingChainEdgeLeft k)})
  rw [P.gluedMk_image_indexSet_eq_biUnion]
  exact IsConnected.biUnion_of_chain
    ⟨gluingChainEdgeLeft k, by change gluingChainEdgeLeft k ≤ gluingChainEdgeLeft k; rfl⟩
    ordConnected_Iic
    (fun i _ => P.gluedComponentImage_isConnected i)
    (fun i _ _ => P.gluedComponentImage_inter_orderSucc_nonempty i)

/-- The actual closed suffix is connected with its original chain incidence. -/
theorem gluedChainSuffix_isConnected
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    IsConnected (P.gluedChainSuffix k) := by
  change IsConnected (P.gluedMk '' {a | a.1 ∈ Ioi (gluingChainEdgeLeft k)})
  rw [P.gluedMk_image_indexSet_eq_biUnion]
  exact IsConnected.biUnion_of_chain
    ⟨gluingChainEdgeRight k, by change k.val < k.val + 1; omega⟩ ordConnected_Ioi
    (fun i _ => P.gluedComponentImage_isConnected i)
    (fun i _ _ => P.gluedComponentImage_inter_orderSucc_nonempty i)

/-- Connectedness of the native closed prefix subtype is constructed, not assumed. -/
instance gluedChainPrefixConnectedSpace
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    ConnectedSpace (P.gluedChainPrefix k) :=
  isConnected_iff_connectedSpace.mp (P.gluedChainPrefix_isConnected k)

/-- Connectedness of the native closed suffix subtype is also constructed. -/
instance gluedChainSuffixConnectedSpace
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    ConnectedSpace (P.gluedChainSuffix k) :=
  isConnected_iff_connectedSpace.mp (P.gluedChainSuffix_isConnected k)

private theorem closedChainSides_inter_seamNeighborhood_nonempty
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    ((P.gluedChainPrefix k ∩ P.gluedChainSuffix k) ∩
      P.gluedMk '' P.seamNeighborhood k).Nonempty := by
  let q := P.gluedSeamCircleInclusion k 1
  have hq : q.1 ∈ P.gluedChainPrefix k ∩ P.gluedChainSuffix k := by
    rw [P.gluedChainPrefix_inter_suffix k]
    exact P.gluedSeamCircleInclusion_mem k 1
  exact ⟨q.1, hq, q.2⟩

/-- Thickening the genuine closed prefix by its seam neighborhood preserves connectedness. -/
theorem gluedChainPrefixNeighborhood_isConnected
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    IsConnected (P.gluedChainPrefixNeighborhood k) := by
  obtain ⟨q, hq, hN⟩ := P.closedChainSides_inter_seamNeighborhood_nonempty k
  exact IsConnected.union ⟨q, hq.1, hN⟩ (P.gluedChainPrefix_isConnected k)
    (P.gluedSeamNeighborhood_isPathConnected k).isConnected

/-- The genuine thickened suffix is connected for the same actual seam point. -/
theorem gluedChainSuffixNeighborhood_isConnected
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    IsConnected (P.gluedChainSuffixNeighborhood k) := by
  obtain ⟨q, hq, hN⟩ := P.closedChainSides_inter_seamNeighborhood_nonempty k
  exact IsConnected.union ⟨q, hq.2, hN⟩ (P.gluedChainSuffix_isConnected k)
    (P.gluedSeamNeighborhood_isPathConnected k).isConnected

/-- Native local path connectedness upgrades the actual open prefix side. -/
theorem gluedChainPrefixNeighborhood_isPathConnected
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    IsPathConnected (P.gluedChainPrefixNeighborhood k) :=
  (P.gluedChainPrefixNeighborhood_isOpen k).isConnected_iff_isPathConnected.mp
    (P.gluedChainPrefixNeighborhood_isConnected k)

/-- The actual open suffix side is path connected in the unchanged quotient topology. -/
theorem gluedChainSuffixNeighborhood_isPathConnected
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    IsPathConnected (P.gluedChainSuffixNeighborhood k) :=
  (P.gluedChainSuffixNeighborhood_isOpen k).isConnected_iff_isPathConnected.mp
    (P.gluedChainSuffixNeighborhood_isConnected k)

/-- The original prefix open-cover subtype supplies the native van Kampen instance. -/
instance gluedChainPrefixNeighborhoodPathConnectedSpace
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    PathConnectedSpace (P.gluedChainPrefixNeighborhood k) :=
  isPathConnected_iff_pathConnectedSpace.mp (P.gluedChainPrefixNeighborhood_isPathConnected k)

/-- The original suffix open-cover subtype supplies its van Kampen instance. -/
instance gluedChainSuffixNeighborhoodPathConnectedSpace
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    PathConnectedSpace (P.gluedChainSuffixNeighborhood k) :=
  isPathConnected_iff_pathConnectedSpace.mp (P.gluedChainSuffixNeighborhood_isPathConnected k)

#print axioms gluedComponentImage_isConnected
#print axioms gluedChainPrefix_isConnected
#print axioms gluedChainSuffix_isConnected
#print axioms gluedChainPrefixConnectedSpace
#print axioms gluedChainSuffixConnectedSpace
#print axioms gluedChainPrefixNeighborhood_isConnected
#print axioms gluedChainSuffixNeighborhood_isConnected
#print axioms gluedChainPrefixNeighborhood_isPathConnected
#print axioms gluedChainSuffixNeighborhood_isPathConnected
#print axioms gluedChainPrefixNeighborhoodPathConnectedSpace
#print axioms gluedChainSuffixNeighborhoodPathConnectedSpace

end SystolicGrowth.ExerciseGluingPreparation
