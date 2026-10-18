module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarCoordinates
public import Geometry.GluingSeamNeighborhoods

@[expose] public section

/-!
# Signed polar coordinates on the actual seam neighborhoods

The signed cylinder uses the actual outgoing collar at negative signed
radius and the incoming collar at positive signed radius. The incoming
angle is inverted by the prescribed reflected attachment. At zero the
two branch maps agree by that genuine seam identification. All quotient
maps here are restrictions of the original chain quotient.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth

/-- The signed cylinder with the original global collar depth. -/
abbrev GluingSeamCylinder (C : ℝ) (g : ℕ) :=
  Circle × Ioo (-gluingDepth C g) (gluingDepth C g)

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The actual quotient projection restricted to the proved seam domain. -/
def seamNeighborhoodProjection (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (a : P.seamNeighborhood k) :
    ↥(P.gluedMk '' P.seamNeighborhood k) :=
  ⟨P.gluedMk a.1, ⟨a.1, a.2, rfl⟩⟩

/-- Restricting the original quotient to this saturated open domain gives
its actual quotient topology, not a replacement cylinder quotient. -/
theorem seamNeighborhoodProjection_isQuotientMap
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Topology.IsQuotientMap (P.seamNeighborhoodProjection k) := by
  let e : ↥(P.seamNeighborhood k) ≃ₜ
      ↥(P.gluedMk ⁻¹' (P.gluedMk '' P.seamNeighborhood k)) :=
    Homeomorph.setCongr (P.preimage_gluedMk_image_seamNeighborhood k).symm
  have hq : Topology.IsQuotientMap
      ((P.gluedMk '' P.seamNeighborhood k).restrictPreimage P.gluedMk) :=
    isQuotientMap_quotient_mk'.restrictPreimage_isOpen (P.gluedSeamNeighborhood_isOpen k)
  exact hq.comp e.isQuotientMap

/-- The genuine outgoing polar point in the original disjoint union. -/
noncomputable def seamOutgoingPolarPoint
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (p : Circle × Ico (gluingRadius C g) (gluingEmbeddedRadius C g)) : P.ChainPieces :=
  ⟨gluingChainEdgeLeft k, ((P.outgoingCollarPolarHomeomorph _).symm p).1⟩

/-- The genuine incoming polar point in the original disjoint union. -/
noncomputable def seamIncomingPolarPoint
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (p : Circle × Ico (gluingRadius C g) (gluingEmbeddedRadius C g)) : P.ChainPieces :=
  ⟨gluingChainEdgeRight k, ((P.incomingCollarPolarHomeomorph _).symm p).1⟩

theorem seamOutgoingPolarPoint_mem
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (p : Circle × Ico (gluingRadius C g) (gluingEmbeddedRadius C g)) :
    seamOutgoingPolarPoint P k p ∈ P.seamNeighborhood k :=
  Or.inl ⟨_, ((P.outgoingCollarPolarHomeomorph _).symm p).2, rfl⟩

theorem seamIncomingPolarPoint_mem
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (p : Circle × Ico (gluingRadius C g) (gluingEmbeddedRadius C g)) :
    seamIncomingPolarPoint P k p ∈ P.seamNeighborhood k :=
  Or.inr ⟨_, ((P.incomingCollarPolarHomeomorph _).symm p).2, rfl⟩

theorem seamOutgoingPolarPoint_continuous
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Continuous (seamOutgoingPolarPoint P k) :=
  continuous_sigmaMk.comp (continuous_subtype_val.comp
    (P.outgoingCollarPolarHomeomorph _).symm.continuous)

theorem seamIncomingPolarPoint_continuous
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Continuous (seamIncomingPolarPoint P k) :=
  continuous_sigmaMk.comp (continuous_subtype_val.comp
    (P.incomingCollarPolarHomeomorph _).symm.continuous)

/-- The polar branch values on the actual inner circles agree by precisely
the prescribed reflected seam equality. -/
theorem seamPolarBoundary_eq (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (u : Circle) :
    P.gluedMk (seamOutgoingPolarPoint P k
      (u, ⟨gluingRadius C g, le_rfl, P.radius_lt_embeddedRadius⟩)) =
    P.gluedMk (seamIncomingPolarPoint P k
      (u⁻¹, ⟨gluingRadius C g, le_rfl, P.radius_lt_embeddedRadius⟩)) := by
  let z : sphere (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) :=
    ⟨gluingPolarPoint (P.centers (gluingChainEdgeLeft k)).2 u (gluingRadius C g), by
      rw [mem_sphere, dist_comm, dist_gluingPolarPoint _ u P.radius_pos.le]⟩
  have hs : seamOutgoingPolarPoint P k
      (u, ⟨gluingRadius C g, le_rfl, P.radius_lt_embeddedRadius⟩) = P.seamSource k z := by
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Subtype.ext
    rfl
  have ht : seamIncomingPolarPoint P k
      (u⁻¹, ⟨gluingRadius C g, le_rfl, P.radius_lt_embeddedRadius⟩) = P.seamTarget k z := by
    unfold seamIncomingPolarPoint seamTarget
    apply congrArg (Sigma.mk (gluingChainEdgeRight k))
    apply Subtype.ext
    change (Quotient.mk'' (gluingPolarPoint (P.centers (gluingChainEdgeRight k)).1
      u⁻¹ (gluingRadius C g)) : (X (gluingChainEdgeRight k)).Carrier) =
      Quotient.mk'' (gluingCircleMap (P.centers (gluingChainEdgeLeft k)).2
        (P.centers (gluingChainEdgeRight k)).1
        (gluingPolarPoint (P.centers (gluingChainEdgeLeft k)).2 u (gluingRadius C g)))
    rw [gluingCircleMap_gluingPolarPoint]
  rw [hs, ht]
  exact P.gluedMk_seamSource_eq_seamTarget k z

noncomputable def Internal.GluingSeamChartsHelpers.seamSourceCoordinates
    (P : ExerciseGluingPreparation C g n genera X) (p : GluingSeamCylinder C g) :
    Circle × Ico (gluingRadius C g) (gluingEmbeddedRadius C g) :=
  (p.1, ⟨gluingRadius C g + max (-p.2.1) 0, by
    constructor
    · exact le_add_of_nonneg_right (le_max_right _ _)
    · change gluingRadius C g + max (-p.2.1) 0 < gluingRadius C g + gluingDepth C g
      have h : max (-p.2.1) 0 < gluingDepth C g :=
        max_lt (by linarith [p.2.2.1]) P.depth_pos
      linarith⟩)

noncomputable def Internal.GluingSeamChartsHelpers.seamTargetCoordinates
    (P : ExerciseGluingPreparation C g n genera X) (p : GluingSeamCylinder C g) :
    Circle × Ico (gluingRadius C g) (gluingEmbeddedRadius C g) :=
  (p.1⁻¹, ⟨gluingRadius C g + max p.2.1 0, by
    constructor
    · exact le_add_of_nonneg_right (le_max_right _ _)
    · change gluingRadius C g + max p.2.1 0 < gluingRadius C g + gluingDepth C g
      have h := max_lt p.2.2.2 P.depth_pos
      linarith⟩)

private theorem seamSourceCoordinates_continuous
    (P : ExerciseGluingPreparation C g n genera X) : Continuous (Internal.GluingSeamChartsHelpers.seamSourceCoordinates P) :=
  continuous_fst.prodMk ((continuous_const.add
    (((continuous_subtype_val.comp continuous_snd).neg).max continuous_const)).subtype_mk _)

private theorem seamTargetCoordinates_continuous
    (P : ExerciseGluingPreparation C g n genera X) : Continuous (Internal.GluingSeamChartsHelpers.seamTargetCoordinates P) :=
  continuous_fst.inv.prodMk ((continuous_const.add
    ((continuous_subtype_val.comp continuous_snd).max continuous_const)).subtype_mk _)

noncomputable def Internal.GluingSeamChartsHelpers.seamSourceBranch
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (p : GluingSeamCylinder C g) : ↥(P.gluedMk '' P.seamNeighborhood k) :=
  ⟨P.gluedMk (seamOutgoingPolarPoint P k (Internal.GluingSeamChartsHelpers.seamSourceCoordinates P p)),
    ⟨_, seamOutgoingPolarPoint_mem P k _, rfl⟩⟩

noncomputable def Internal.GluingSeamChartsHelpers.seamTargetBranch
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (p : GluingSeamCylinder C g) : ↥(P.gluedMk '' P.seamNeighborhood k) :=
  ⟨P.gluedMk (seamIncomingPolarPoint P k (Internal.GluingSeamChartsHelpers.seamTargetCoordinates P p)),
    ⟨_, seamIncomingPolarPoint_mem P k _, rfl⟩⟩

private theorem seamSourceBranch_continuous
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Continuous (Internal.GluingSeamChartsHelpers.seamSourceBranch P k) :=
  (P.gluedMk_continuous.comp ((seamOutgoingPolarPoint_continuous P k).comp
    (seamSourceCoordinates_continuous P))).subtype_mk _

private theorem seamTargetBranch_continuous
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Continuous (Internal.GluingSeamChartsHelpers.seamTargetBranch P k) :=
  (P.gluedMk_continuous.comp ((seamIncomingPolarPoint_continuous P k).comp
    (seamTargetCoordinates_continuous P))).subtype_mk _

/-- The actual signed polar map: negative signed radius uses the source
collar; positive signed radius uses the target with angular inversion. -/
noncomputable def seamCylinderMap (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (p : GluingSeamCylinder C g) :
    ↥(P.gluedMk '' P.seamNeighborhood k) :=
  if p.2.1 ≤ 0 then Internal.GluingSeamChartsHelpers.seamSourceBranch P k p else Internal.GluingSeamChartsHelpers.seamTargetBranch P k p

private theorem seamCylinderMap_of_nonpos
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (p : GluingSeamCylinder C g) (hp : p.2.1 ≤ 0) :
    P.seamCylinderMap k p = Internal.GluingSeamChartsHelpers.seamSourceBranch P k p := by
  unfold seamCylinderMap
  rw [if_pos hp]

private theorem seamCylinderMap_of_pos
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (p : GluingSeamCylinder C g) (hp : 0 < p.2.1) :
    P.seamCylinderMap k p = Internal.GluingSeamChartsHelpers.seamTargetBranch P k p := by
  unfold seamCylinderMap
  rw [if_neg (not_le.mpr hp)]

/-- The only branch gluing at zero is the actual reflected inner-circle
identification; the signed map is continuous across that seam. -/
theorem seamCylinderMap_continuous
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Continuous (P.seamCylinderMap k) := by
  apply (seamSourceBranch_continuous P k).if_le (seamTargetBranch_continuous P k)
    (continuous_subtype_val.comp continuous_snd) continuous_const
  intro p hp
  change p.2.1 = 0 at hp
  apply Subtype.ext
  change P.gluedMk (seamOutgoingPolarPoint P k (Internal.GluingSeamChartsHelpers.seamSourceCoordinates P p)) =
    P.gluedMk (seamIncomingPolarPoint P k (Internal.GluingSeamChartsHelpers.seamTargetCoordinates P p))
  have hs : Internal.GluingSeamChartsHelpers.seamSourceCoordinates P p =
      (p.1, ⟨gluingRadius C g, le_rfl, P.radius_lt_embeddedRadius⟩) := by
    unfold Internal.GluingSeamChartsHelpers.seamSourceCoordinates
    apply Prod.ext
    · rfl
    apply Subtype.ext
    simp only [hp, neg_zero, max_self, add_zero]
  have ht : Internal.GluingSeamChartsHelpers.seamTargetCoordinates P p =
      (p.1⁻¹, ⟨gluingRadius C g, le_rfl, P.radius_lt_embeddedRadius⟩) := by
    unfold Internal.GluingSeamChartsHelpers.seamTargetCoordinates
    apply Prod.ext
    · rfl
    apply Subtype.ext
    simp only [hp, max_self, add_zero]
  rw [hs, ht]
  exact P.seamPolarBoundary_eq k p.1

noncomputable def Internal.GluingSeamChartsHelpers.seamPolarPiecesToNeighborhood
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    (Circle × Ico (gluingRadius C g) (gluingEmbeddedRadius C g)) ⊕
      (Circle × Ico (gluingRadius C g) (gluingEmbeddedRadius C g)) →
      ↥(P.seamNeighborhood k) :=
  Sum.elim
    (fun p => ⟨seamOutgoingPolarPoint P k p, seamOutgoingPolarPoint_mem P k p⟩)
    (fun p => ⟨seamIncomingPolarPoint P k p, seamIncomingPolarPoint_mem P k p⟩)

private theorem seamPolarPiecesToNeighborhood_isQuotientMap
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Topology.IsQuotientMap (Internal.GluingSeamChartsHelpers.seamPolarPiecesToNeighborhood P k) := by
  have hout : Topology.IsOpenEmbedding (fun p =>
      ⟨seamOutgoingPolarPoint P k p, seamOutgoingPolarPoint_mem P k p⟩ :
      Circle × Ico (gluingRadius C g) (gluingEmbeddedRadius C g) →
        ↥(P.seamNeighborhood k)) := by
    have hc := (P.outgoingCollar_isOpen (gluingChainEdgeLeft k) (by
      change k.1 + 1 < n
      have := k.2
      omega)).isOpenEmbedding_subtypeVal
    have he := (Topology.IsOpenEmbedding.sigmaMk.comp hc).comp
      (P.outgoingCollarPolarHomeomorph _).symm.isOpenEmbedding
    exact Topology.IsOpenEmbedding.of_isEmbedding_isOpenMap
      (he.isEmbedding.codRestrict _ _) (he.isOpenMap.codRestrict _)
  have hin : Topology.IsOpenEmbedding (fun p =>
      ⟨seamIncomingPolarPoint P k p, seamIncomingPolarPoint_mem P k p⟩ :
      Circle × Ico (gluingRadius C g) (gluingEmbeddedRadius C g) →
        ↥(P.seamNeighborhood k)) := by
    have hc := (P.incomingCollar_isOpen (gluingChainEdgeRight k) (by
      change 0 < k.1 + 1
      omega)).isOpenEmbedding_subtypeVal
    have he := (Topology.IsOpenEmbedding.sigmaMk.comp hc).comp
      (P.incomingCollarPolarHomeomorph _).symm.isOpenEmbedding
    exact Topology.IsOpenEmbedding.of_isEmbedding_isOpenMap
      (he.isEmbedding.codRestrict _ _) (he.isOpenMap.codRestrict _)
  apply (hout.isOpenMap.sumElim hin.isOpenMap).isQuotientMap
    (hout.continuous.sumElim hin.continuous)
  rintro ⟨a, ⟨x, hx, hxa⟩ | ⟨x, hx, hxa⟩⟩
  · refine ⟨Sum.inl ((P.outgoingCollarPolarHomeomorph _) ⟨x, hx⟩), ?_⟩
    apply Subtype.ext
    change Sigma.mk (gluingChainEdgeLeft k)
      (((P.outgoingCollarPolarHomeomorph _).symm
        ((P.outgoingCollarPolarHomeomorph _) ⟨x, hx⟩)).1) = a
    rw [(P.outgoingCollarPolarHomeomorph _).symm_apply_apply]
    exact hxa
  · refine ⟨Sum.inr ((P.incomingCollarPolarHomeomorph _) ⟨x, hx⟩), ?_⟩
    apply Subtype.ext
    change Sigma.mk (gluingChainEdgeRight k)
      (((P.incomingCollarPolarHomeomorph _).symm
        ((P.incomingCollarPolarHomeomorph _) ⟨x, hx⟩)).1) = a
    rw [(P.incomingCollarPolarHomeomorph _).symm_apply_apply]
    exact hxa

noncomputable def Internal.GluingSeamChartsHelpers.seamPolarPiecesSignedCoordinates
    (_P : ExerciseGluingPreparation C g n genera X) :
    (Circle × Ico (gluingRadius C g) (gluingEmbeddedRadius C g)) ⊕
      (Circle × Ico (gluingRadius C g) (gluingEmbeddedRadius C g)) →
      GluingSeamCylinder C g :=
  Sum.elim
    (fun p => (p.1, ⟨gluingRadius C g - p.2.1, by
      have hu := p.2.2.2
      change p.2.1 < gluingRadius C g + gluingDepth C g at hu
      constructor <;> linarith [p.2.2.1, _P.depth_pos]⟩))
    (fun p => (p.1⁻¹, ⟨p.2.1 - gluingRadius C g, by
      have hu := p.2.2.2
      change p.2.1 < gluingRadius C g + gluingDepth C g at hu
      constructor <;> linarith [p.2.2.1, _P.depth_pos]⟩))

private theorem seamPolarPiecesSignedCoordinates_continuous
    (P : ExerciseGluingPreparation C g n genera X) :
    Continuous (Internal.GluingSeamChartsHelpers.seamPolarPiecesSignedCoordinates P) :=
  (continuous_fst.prodMk ((continuous_const.sub
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _)).sumElim
    (continuous_fst.inv.prodMk (((continuous_subtype_val.comp continuous_snd).sub
      continuous_const).subtype_mk _))

private theorem seamCylinderMap_comp_signedCoordinates
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.seamCylinderMap k ∘ Internal.GluingSeamChartsHelpers.seamPolarPiecesSignedCoordinates P =
      P.seamNeighborhoodProjection k ∘ Internal.GluingSeamChartsHelpers.seamPolarPiecesToNeighborhood P k := by
  funext p
  cases p with
  | inl p =>
    have ht : gluingRadius C g - p.2.1 ≤ 0 := by linarith [p.2.2.1]
    have hs : Internal.GluingSeamChartsHelpers.seamSourceCoordinates P
        (Internal.GluingSeamChartsHelpers.seamPolarPiecesSignedCoordinates P (Sum.inl p)) = p := by
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        change gluingRadius C g + max (-(gluingRadius C g - p.2.1)) 0 = p.2.1
        rw [max_eq_left (by linarith [p.2.2.1])]
        ring
    apply Subtype.ext
    simp only [Function.comp_apply]
    rw [seamCylinderMap_of_nonpos P k _ (by exact ht)]
    change P.gluedMk (seamOutgoingPolarPoint P k
      (Internal.GluingSeamChartsHelpers.seamSourceCoordinates P (Internal.GluingSeamChartsHelpers.seamPolarPiecesSignedCoordinates P (Sum.inl p)))) =
      P.gluedMk (seamOutgoingPolarPoint P k p)
    rw [hs]
  | inr p =>
    have ht : 0 ≤ p.2.1 - gluingRadius C g := by linarith [p.2.2.1]
    by_cases hzero : p.2.1 - gluingRadius C g = 0
    · have hs : Internal.GluingSeamChartsHelpers.seamSourceCoordinates P
          (Internal.GluingSeamChartsHelpers.seamPolarPiecesSignedCoordinates P (Sum.inr p)) =
          (p.1⁻¹, ⟨gluingRadius C g, le_rfl, P.radius_lt_embeddedRadius⟩) := by
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          change gluingRadius C g + max (-(p.2.1 - gluingRadius C g)) 0 = gluingRadius C g
          rw [hzero, neg_zero, max_self, add_zero]
      have hp : p = (p.1, ⟨gluingRadius C g, le_rfl, P.radius_lt_embeddedRadius⟩) := by
        apply Prod.ext
        · rfl
        apply Subtype.ext
        linarith
      apply Subtype.ext
      simp only [Function.comp_apply]
      rw [seamCylinderMap_of_nonpos P k _ (by exact hzero.le)]
      change P.gluedMk (seamOutgoingPolarPoint P k
        (Internal.GluingSeamChartsHelpers.seamSourceCoordinates P (Internal.GluingSeamChartsHelpers.seamPolarPiecesSignedCoordinates P (Sum.inr p)))) =
        P.gluedMk (seamIncomingPolarPoint P k p)
      rw [hs, hp]
      simpa only [inv_inv] using P.seamPolarBoundary_eq k p.1⁻¹
    · have hpos : 0 < p.2.1 - gluingRadius C g := lt_of_le_of_ne ht (Ne.symm hzero)
      have hs : Internal.GluingSeamChartsHelpers.seamTargetCoordinates P
          (Internal.GluingSeamChartsHelpers.seamPolarPiecesSignedCoordinates P (Sum.inr p)) = p := by
        apply Prod.ext
        · exact inv_inv _
        · apply Subtype.ext
          change gluingRadius C g + max (p.2.1 - gluingRadius C g) 0 = p.2.1
          rw [max_eq_left ht]
          ring
      apply Subtype.ext
      simp only [Function.comp_apply]
      rw [seamCylinderMap_of_pos P k _ (by exact hpos)]
      change P.gluedMk (seamIncomingPolarPoint P k
        (Internal.GluingSeamChartsHelpers.seamTargetCoordinates P (Internal.GluingSeamChartsHelpers.seamPolarPiecesSignedCoordinates P (Sum.inr p)))) =
        P.gluedMk (seamIncomingPolarPoint P k p)
      rw [hs]

/-- The signed map has the quotient topology of the actual seam domain,
by factoring the original quotient projection through the genuine collars. -/
theorem seamCylinderMap_isQuotientMap
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Topology.IsQuotientMap (P.seamCylinderMap k) := by
  apply Topology.IsQuotientMap.of_comp (seamPolarPiecesSignedCoordinates_continuous P)
    (P.seamCylinderMap_continuous k)
  rw [seamCylinderMap_comp_signedCoordinates P k]
  exact (P.seamNeighborhoodProjection_isQuotientMap k).comp
    (seamPolarPiecesToNeighborhood_isQuotientMap P k)

private theorem seamOutgoingPolar_quotient_injective
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Function.Injective (fun p => P.gluedMk (seamOutgoingPolarPoint P k p)) := by
  intro p q h
  have hc : ((P.outgoingCollarPolarHomeomorph (gluingChainEdgeLeft k)).symm p).1 =
      ((P.outgoingCollarPolarHomeomorph (gluingChainEdgeLeft k)).symm q).1 :=
    P.gluedMk_injective_component (gluingChainEdgeLeft k) h
  exact (P.outgoingCollarPolarHomeomorph _).symm.injective (Subtype.ext hc)

private theorem seamIncomingPolar_quotient_injective
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Function.Injective (fun p => P.gluedMk (seamIncomingPolarPoint P k p)) := by
  intro p q h
  have hc : ((P.incomingCollarPolarHomeomorph (gluingChainEdgeRight k)).symm p).1 =
      ((P.incomingCollarPolarHomeomorph (gluingChainEdgeRight k)).symm q).1 :=
    P.gluedMk_injective_component (gluingChainEdgeRight k) h
  exact (P.incomingCollarPolarHomeomorph _).symm.injective (Subtype.ext hc)

private theorem incomingPolar_radial_of_mem_circle
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (p : Circle × Ico (gluingRadius C g) (gluingEmbeddedRadius C g))
    (hp : ((P.incomingCollarPolarHomeomorph i).symm p).1 ∈
      Set.range (P.leftCirclePoint i)) : p.2.1 = gluingRadius C g := by
  obtain ⟨z, hz⟩ := hp
  have hq := congrArg Subtype.val hz
  change (Quotient.mk'' z.1 : (X i).Carrier) =
    Quotient.mk'' (gluingPolarPoint (P.centers i).1 p.1 p.2.1) at hq
  have hzR : z.1 ∈ ball (P.centers i).1 (gluingEmbeddedRadius C g) :=
    Metric.sphere_subset_ball P.radius_lt_embeddedRadius z.2
  have hpR : gluingPolarPoint (P.centers i).1 p.1 p.2.1 ∈
      ball (P.centers i).1 (gluingEmbeddedRadius C g) := by
    rw [mem_ball, dist_comm,
      dist_gluingPolarPoint _ p.1 (P.radius_pos.trans_le p.2.2.1).le]
    exact p.2.2.2
  have hup := P.quotient_injOn_outer_ball i (P.centers i).1 hzR hpR hq
  have hd : dist (P.centers i).1 z.1 = gluingRadius C g := by
    simpa only [mem_sphere, dist_comm] using z.2
  rw [hup, dist_gluingPolarPoint _ p.1 (P.radius_pos.trans_le p.2.2.1).le] at hd
  exact hd

/-- Cross-component equality of actual polar collar points forces the
incoming point onto its inner circle. Positive signed radii cannot acquire
an extra identification with the outgoing branch. -/
private theorem seamIncomingPolar_radial_of_quotient_eq
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (p q : Circle × Ico (gluingRadius C g) (gluingEmbeddedRadius C g))
    (h : P.gluedMk (seamOutgoingPolarPoint P k p) =
      P.gluedMk (seamIncomingPolarPoint P k q)) : q.2.1 = gluingRadius C g := by
  rcases (P.gluedMk_eq_iff _ _).mp h with heq | hrel | hrev
  · have hv := congrArg (fun a : P.ChainPieces => a.1.1) heq
    change k.1 = k.1 + 1 at hv
    omega
  · apply incomingPolar_radial_of_mem_circle P (gluingChainEdgeRight k) q
    exact P.chainRelation_target_mem_leftCircle
      (a := seamOutgoingPolarPoint P k p) (b := seamIncomingPolarPoint P k q) hrel
  · obtain ⟨l, z, hs, ht⟩ := hrev
    have hleft := congrArg (fun a : P.ChainPieces => a.1.1) hs
    have hright := congrArg (fun a : P.ChainPieces => a.1.1) ht
    change k.1 + 1 = l.1 at hleft
    change k.1 = l.1 + 1 at hright
    omega

/-- The signed polar map is injective in the actual quotient. Equal points
on one side are equal by the component embedding; opposite signed sides
can meet only on the original inner-circle seam. -/
theorem seamCylinderMap_injective
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Function.Injective (P.seamCylinderMap k) := by
  intro p q h
  by_cases hp : p.2.1 ≤ 0
  · rw [seamCylinderMap_of_nonpos P k p hp] at h
    by_cases hq : q.2.1 ≤ 0
    · rw [seamCylinderMap_of_nonpos P k q hq] at h
      have heq : Internal.GluingSeamChartsHelpers.seamSourceCoordinates P p = Internal.GluingSeamChartsHelpers.seamSourceCoordinates P q :=
        seamOutgoingPolar_quotient_injective P k (congrArg Subtype.val h)
      apply Prod.ext
      · exact congrArg (fun a : Circle × Ico (gluingRadius C g)
          (gluingEmbeddedRadius C g) => a.1) heq
      · apply Subtype.ext
        have hr := congrArg (fun a : Circle × Ico (gluingRadius C g)
          (gluingEmbeddedRadius C g) => a.2.1) heq
        change gluingRadius C g + max (-p.2.1) 0 =
          gluingRadius C g + max (-q.2.1) 0 at hr
        rw [max_eq_left (by linarith : 0 ≤ -p.2.1),
          max_eq_left (by linarith : 0 ≤ -q.2.1)] at hr
        linarith
    · have hqpos : 0 < q.2.1 := lt_of_not_ge hq
      rw [seamCylinderMap_of_pos P k q hqpos] at h
      have hr := seamIncomingPolar_radial_of_quotient_eq P k
        (Internal.GluingSeamChartsHelpers.seamSourceCoordinates P p) (Internal.GluingSeamChartsHelpers.seamTargetCoordinates P q) (congrArg Subtype.val h)
      change gluingRadius C g + max q.2.1 0 = gluingRadius C g at hr
      rw [max_eq_left hqpos.le] at hr
      linarith
  · have hppos : 0 < p.2.1 := lt_of_not_ge hp
    rw [seamCylinderMap_of_pos P k p hppos] at h
    by_cases hq : q.2.1 ≤ 0
    · rw [seamCylinderMap_of_nonpos P k q hq] at h
      have hr := seamIncomingPolar_radial_of_quotient_eq P k
        (Internal.GluingSeamChartsHelpers.seamSourceCoordinates P q) (Internal.GluingSeamChartsHelpers.seamTargetCoordinates P p) (congrArg Subtype.val h.symm)
      change gluingRadius C g + max p.2.1 0 = gluingRadius C g at hr
      rw [max_eq_left hppos.le] at hr
      linarith
    · have hqpos : 0 < q.2.1 := lt_of_not_ge hq
      rw [seamCylinderMap_of_pos P k q hqpos] at h
      have heq : Internal.GluingSeamChartsHelpers.seamTargetCoordinates P p = Internal.GluingSeamChartsHelpers.seamTargetCoordinates P q :=
        seamIncomingPolar_quotient_injective P k (congrArg Subtype.val h)
      apply Prod.ext
      · exact inv_injective (congrArg (fun a : Circle × Ico (gluingRadius C g)
          (gluingEmbeddedRadius C g) => a.1) heq)
      · apply Subtype.ext
        have hr := congrArg (fun a : Circle × Ico (gluingRadius C g)
          (gluingEmbeddedRadius C g) => a.2.1) heq
        change gluingRadius C g + max p.2.1 0 =
          gluingRadius C g + max q.2.1 0 at hr
        rw [max_eq_left hppos.le, max_eq_left hqpos.le] at hr
        linarith

/-- The actual signed polar cylinder is homeomorphic to the actual open
image of the prescribed seam neighborhood in the original glued carrier. -/
noncomputable def seamCylinderHomeomorph
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    GluingSeamCylinder C g ≃ₜ ↥(P.gluedMk '' P.seamNeighborhood k) :=
  ((isHomeomorph_iff_isQuotientMap_injective).mpr
    ⟨P.seamCylinderMap_isQuotientMap k, P.seamCylinderMap_injective k⟩).homeomorph
      (P.seamCylinderMap k)

@[simp] theorem seamCylinderHomeomorph_apply
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (p : GluingSeamCylinder C g) : P.seamCylinderHomeomorph k p = P.seamCylinderMap k p := rfl

/-- The inverse chart on the actual outgoing collar has its original
angle and signed coordinate `r - radius`, including the seam at zero. -/
theorem seamCylinderHomeomorph_symm_outgoing
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (p : Circle × Ico (gluingRadius C g) (gluingEmbeddedRadius C g)) :
    (P.seamCylinderHomeomorph k).symm
      (P.seamNeighborhoodProjection k
        ⟨P.seamOutgoingPolarPoint k p, P.seamOutgoingPolarPoint_mem k p⟩) =
      (p.1, ⟨gluingRadius C g - p.2.1, by
        have hu := p.2.2.2
        change p.2.1 < gluingRadius C g + gluingDepth C g at hu
        constructor <;> linarith [p.2.2.1, P.depth_pos]⟩) := by
  apply (P.seamCylinderHomeomorph k).injective
  simp only [Homeomorph.apply_symm_apply, seamCylinderHomeomorph_apply]
  exact (congrFun (seamCylinderMap_comp_signedCoordinates P k) (Sum.inl p)).symm

/-- The inverse chart on the actual incoming collar inverts the original
angle and uses signed coordinate `radius - r`; the formulas agree at zero
by the actual reflected attachment. -/
theorem seamCylinderHomeomorph_symm_incoming
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (p : Circle × Ico (gluingRadius C g) (gluingEmbeddedRadius C g)) :
    (P.seamCylinderHomeomorph k).symm
      (P.seamNeighborhoodProjection k
        ⟨P.seamIncomingPolarPoint k p, P.seamIncomingPolarPoint_mem k p⟩) =
      (p.1⁻¹, ⟨p.2.1 - gluingRadius C g, by
        have hu := p.2.2.2
        change p.2.1 < gluingRadius C g + gluingDepth C g at hu
        constructor <;> linarith [p.2.2.1, P.depth_pos]⟩) := by
  apply (P.seamCylinderHomeomorph k).injective
  simp only [Homeomorph.apply_symm_apply, seamCylinderHomeomorph_apply]
  exact (congrFun (seamCylinderMap_comp_signedCoordinates P k) (Sum.inr p)).symm

end ExerciseGluingPreparation

#print axioms ExerciseGluingPreparation.seamNeighborhoodProjection_isQuotientMap
#print axioms ExerciseGluingPreparation.seamPolarBoundary_eq
#print axioms ExerciseGluingPreparation.seamCylinderMap_continuous
#print axioms ExerciseGluingPreparation.seamCylinderMap_isQuotientMap
#print axioms ExerciseGluingPreparation.seamCylinderMap_injective
#print axioms ExerciseGluingPreparation.seamCylinderHomeomorph
#print axioms ExerciseGluingPreparation.seamCylinderHomeomorph_symm_outgoing
#print axioms ExerciseGluingPreparation.seamCylinderHomeomorph_symm_incoming

end SystolicGrowth
