module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingInteriorCharts
public import Geometry.GluingSeamNeighborhoods

@[expose] public section

/-!
# Coverage by actual interior charts and seam neighborhoods

A retained point outside its genuinely deleted-disk collars lies in the
original surface interior: the complement of the two closed inner balls
gives an actual open neighborhood. Every actual collar belongs to the
corresponding path-edge neighborhood. Thus these interiors and the proved
two-sided seam neighborhoods cover the prescribed glued quotient.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- A retained point avoiding its genuinely deleted-disk collars is an
interior point in the original surface topology. -/
theorem mem_componentInteriorSet_of_not_mem_collars
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (q : P.ChainComponent i)
    (hl : 0 < i.1 → q ∉ P.incomingCollar i)
    (hr : i.1 + 1 < n → q ∉ P.outgoingCollar i) :
    q.1 ∈ P.componentInteriorSet i := by
  let U : Set (X i).Carrier :=
    (if 0 < i.1 then
      (Metric.closedBall (Quotient.mk'' (P.centers i).1) (gluingRadius C g))ᶜ else univ) ∩
    (if i.1 + 1 < n then
      (Metric.closedBall (Quotient.mk'' (P.centers i).2) (gluingRadius C g))ᶜ else univ)
  have hU : IsOpen U := by
    apply IsOpen.inter
    · split_ifs
      · exact Metric.isClosed_closedBall.isOpen_compl
      · exact isOpen_univ
    · split_ifs
      · exact Metric.isClosed_closedBall.isOpen_compl
      · exact isOpen_univ
  have hsub : U ⊆ (X i).puncturedComponentSet (P.centers i).1 (P.centers i).2
      (gluingRadius C g) i := by
    rintro a ⟨hal, har⟩
    change a ∉ (X i).punctureDeletedSet _ _ _ i
    have hleft : a ∉ (if 0 < i.1 then
        (X i).orbitBall (P.centers i).1 (gluingRadius C g) else ∅) := by
      split_ifs with hi
      · have hnot : a ∉ Metric.closedBall (Quotient.mk'' (P.centers i).1)
            (gluingRadius C g) := by simpa only [hi, if_pos, Set.mem_compl_iff] using hal
        intro ha
        have hb : a ∈ Metric.ball (Quotient.mk'' (P.centers i).1) (gluingRadius C g) := by
          simpa only [(X i).carrier_ball_eq_orbitBall] using ha
        exact hnot (Metric.ball_subset_closedBall hb)
      · exact Set.notMem_empty _
    have hright : a ∉ (if i.1 + 1 < n then
        (X i).orbitBall (P.centers i).2 (gluingRadius C g) else ∅) := by
      split_ifs with hi
      · have hnot : a ∉ Metric.closedBall (Quotient.mk'' (P.centers i).2)
            (gluingRadius C g) := by simpa only [hi, if_pos, Set.mem_compl_iff] using har
        intro ha
        have hb : a ∈ Metric.ball (Quotient.mk'' (P.centers i).2) (gluingRadius C g) := by
          simpa only [(X i).carrier_ball_eq_orbitBall] using ha
        exact hnot (Metric.ball_subset_closedBall hb)
      · exact Set.notMem_empty _
    rintro (ha | ha)
    · exact hleft ha
    · exact hright ha
  have hqU : q.1 ∈ U := by
    constructor
    · split_ifs with hi
      · have hnot : q.1 ∉ Metric.ball (Quotient.mk'' (P.centers i).1)
            (gluingEmbeddedRadius C g) := by
          intro ha
          apply hl hi
          rw [P.incomingCollar_eq_outerBall i hi]
          simpa only [Set.mem_preimage, (X i).carrier_ball_eq_orbitBall] using ha
        have hdist : gluingEmbeddedRadius C g ≤ dist q.1 (Quotient.mk'' (P.centers i).1) :=
          le_of_not_gt hnot
        exact not_le_of_gt (P.radius_lt_embeddedRadius.trans_le hdist)
      · exact Set.mem_univ _
    · split_ifs with hi
      · have hnot : q.1 ∉ Metric.ball (Quotient.mk'' (P.centers i).2)
            (gluingEmbeddedRadius C g) := by
          intro ha
          apply hr hi
          rw [P.outgoingCollar_eq_outerBall i hi]
          simpa only [Set.mem_preimage, (X i).carrier_ball_eq_orbitBall] using ha
        have hdist : gluingEmbeddedRadius C g ≤ dist q.1 (Quotient.mk'' (P.centers i).2) :=
          le_of_not_gt hnot
        exact not_le_of_gt (P.radius_lt_embeddedRadius.trans_le hdist)
      · exact Set.mem_univ _
  exact interior_maximal hsub hU hqU

/-- Every genuine incoming collar has its actual preceding path edge. -/
theorem exists_seamNeighborhood_of_mem_incomingCollar
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (hi : 0 < i.1)
    {q : P.ChainComponent i} (hq : q ∈ P.incomingCollar i) :
    ∃ k : Fin (n - 1), (⟨i, q⟩ : P.ChainPieces) ∈ P.seamNeighborhood k := by
  let k : Fin (n - 1) := ⟨i.1 - 1, by have := i.2; omega⟩
  have hki : gluingChainEdgeRight k = i := Fin.ext (by dsimp [k, gluingChainEdgeRight]; omega)
  refine ⟨k, Or.inr ?_⟩
  rw [hki]
  exact ⟨q, hq, rfl⟩

/-- Every genuine outgoing collar has its actual following path edge. -/
theorem exists_seamNeighborhood_of_mem_outgoingCollar
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (hi : i.1 + 1 < n)
    {q : P.ChainComponent i} (hq : q ∈ P.outgoingCollar i) :
    ∃ k : Fin (n - 1), (⟨i, q⟩ : P.ChainPieces) ∈ P.seamNeighborhood k := by
  let k : Fin (n - 1) := ⟨i.1, by omega⟩
  have hki : gluingChainEdgeLeft k = i := Fin.ext rfl
  refine ⟨k, Or.inl ?_⟩
  rw [hki]
  exact ⟨q, hq, rfl⟩

/-- Every point of the actual pieces is already in an original component
interior or in one of the actual two-sided seam neighborhoods. -/
theorem chainPoint_mem_interior_or_seamNeighborhood
    (P : ExerciseGluingPreparation C g n genera X) (a : P.ChainPieces) :
    (∃ (i : Fin n) (q : P.componentInteriorSet i), a = P.componentInteriorPoint i q) ∨
      ∃ k : Fin (n - 1), a ∈ P.seamNeighborhood k := by
  obtain ⟨i, q⟩ := a
  by_cases hl : ∃ h : 0 < i.1, q ∈ P.incomingCollar i
  · obtain ⟨hi, hq⟩ := hl
    exact Or.inr (P.exists_seamNeighborhood_of_mem_incomingCollar i hi hq)
  by_cases hr : ∃ h : i.1 + 1 < n, q ∈ P.outgoingCollar i
  · obtain ⟨hi, hq⟩ := hr
    exact Or.inr (P.exists_seamNeighborhood_of_mem_outgoingCollar i hi hq)
  have hq := P.mem_componentInteriorSet_of_not_mem_collars i q
    (fun hi hmem => hl ⟨hi, hmem⟩) (fun hi hmem => hr ⟨hi, hmem⟩)
  exact Or.inl ⟨i, ⟨q.1, hq⟩, rfl⟩

/-- Genuine interior charts and actual open seam neighborhoods cover every
point of the prescribed quotient, without an assumed atlas-coverage field. -/
theorem gluedPoint_mem_interior_or_seamNeighborhood
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedCarrier) :
    (∃ (i : Fin n) (p : P.componentInteriorSet i),
      q = P.gluedMk (P.componentInteriorPoint i p)) ∨
      ∃ k : Fin (n - 1), q ∈ P.gluedMk '' P.seamNeighborhood k := by
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective q
  rcases P.chainPoint_mem_interior_or_seamNeighborhood a with ⟨i, p, rfl⟩ | ⟨k, hk⟩
  · exact Or.inl ⟨i, p, rfl⟩
  · exact Or.inr ⟨k, a, hk, rfl⟩

#print axioms mem_componentInteriorSet_of_not_mem_collars
#print axioms chainPoint_mem_interior_or_seamNeighborhood
#print axioms gluedPoint_mem_interior_or_seamNeighborhood

end SystolicGrowth.ExerciseGluingPreparation
