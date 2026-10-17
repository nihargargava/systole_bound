module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingSeamIncidence
public import Mathlib.Topology.Maps.Proper.Basic

@[expose] public section

/-!
# Hausdorff topology of the actual chain gluing

Each seam-pair image is compact, so the finite actual seam relation is
closed. The proved one-step description of its equivalence closure makes
the actual setoid closed as well. Compact saturation then makes the
quotient map proper. Its product map detects the closed quotient diagonal,
proving Hausdorffness without replacing the prescribed quotient carrier.
The already proved component injections are consequently closed embeddings
and homeomorphisms onto their actual images.
-/

open Metric Set UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth
namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

theorem seamSource_continuous (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) : Continuous (P.seamSource k) :=
  continuous_sigmaMk.comp (P.rightCirclePoint_isEmbedding (gluingChainEdgeLeft k)).continuous

theorem seamTarget_continuous (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) : Continuous (P.seamTarget k) :=
  continuous_sigmaMk.comp
    ((P.leftCirclePoint_isEmbedding (gluingChainEdgeRight k)).continuous.comp
      (gluingBoundaryCircleIsometry (P.centers (gluingChainEdgeLeft k)).2
        (P.centers (gluingChainEdgeRight k)).1 (gluingRadius C g)).continuous)

/-- The generating seam relation is a finite union of actual compact
circle-pair images in the disjoint union of retained components. -/
theorem chainRelation_isClosed (P : ExerciseGluingPreparation C g n genera X) :
    IsClosed {p : P.ChainPieces × P.ChainPieces | P.chainRelation p.1 p.2} := by
  have hclosed (k : Fin (n - 1)) :
      IsClosed (Set.range (fun z => (P.seamSource k z, P.seamTarget k z))) := by
    letI : CompactSpace (sphere (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g)) :=
      isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
    exact (isCompact_range ((P.seamSource_continuous k).prodMk
      (P.seamTarget_continuous k))).isClosed
  convert isClosed_iUnion_of_finite hclosed using 1
  ext p
  constructor
  · rintro ⟨k, z, ha, hb⟩
    exact Set.mem_iUnion.mpr ⟨k, z, Prod.ext ha.symm hb.symm⟩
  · intro hp
    obtain ⟨k, z, hz⟩ := Set.mem_iUnion.mp hp
    exact ⟨k, z, (congrArg Prod.fst hz).symm, (congrArg Prod.snd hz).symm⟩

/-- The genuine equivalence closure is closed: its classes contain only
equality and one of the two orientations of a single actual seam pair. -/
theorem chainSetoid_isClosed (P : ExerciseGluingPreparation C g n genera X) :
    IsClosed {p : P.ChainPieces × P.ChainPieces | P.chainSetoid.r p.1 p.2} := by
  have hclosed := (isClosed_diagonal (X := P.ChainPieces)).union
    (P.chainRelation_isClosed.union (P.chainRelation_isClosed.preimage continuous_swap))
  convert hclosed using 1
  ext p
  change Relation.EqvGen P.chainRelation p.1 p.2 ↔ _
  simpa only [Set.mem_union, Set.mem_diagonal_iff, Set.mem_setOf_eq, Set.mem_preimage,
    Prod.fst_swap, Prod.snd_swap]
    using P.eqvGen_chainRelation_iff p.1 p.2

/-- Saturating a closed subset of the actual compact pieces is closed;
therefore the prescribed quotient projection is a closed map. -/
theorem gluedMk_isClosedMap (P : ExerciseGluingPreparation C g n genera X) :
    IsClosedMap P.gluedMk := by
  intro K hK
  apply isQuotientMap_quotient_mk'.isClosed_preimage.mp
  change IsClosed (P.gluedMk ⁻¹' (P.gluedMk '' K))
  have hsaturation : P.gluedMk ⁻¹' (P.gluedMk '' K) =
      Prod.fst '' ({p : P.ChainPieces × P.ChainPieces | P.chainSetoid.r p.1 p.2} ∩
        Prod.snd ⁻¹' K) := by
    ext a
    constructor
    · rintro ⟨b, hb, hba⟩
      exact ⟨(a, b), ⟨Quotient.exact hba.symm, hb⟩, rfl⟩
    · rintro ⟨⟨a', b⟩, ⟨hrel, hb⟩, ha⟩
      dsimp only at ha
      subst a'
      exact ⟨b, hb, (Quotient.sound hrel).symm⟩
  rw [hsaturation]
  exact isClosedMap_fst_of_compactSpace _
    (P.chainSetoid_isClosed.inter (hK.preimage continuous_snd))

/-- Fibers of the actual quotient map are compact closed subsets of the
compact disjoint union; together with closedness this proves properness. -/
theorem gluedMk_isProperMap (P : ExerciseGluingPreparation C g n genera X) :
    IsProperMap P.gluedMk := by
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨P.gluedMk_continuous, P.gluedMk_isClosedMap, ?_⟩
  intro q
  obtain ⟨a, rfl⟩ := Quotient.exists_rep q
  change IsCompact (P.gluedMk ⁻¹' {P.gluedMk a})
  have hfiber : P.gluedMk ⁻¹' {P.gluedMk a} =
      (fun b : P.ChainPieces => (b, a)) ⁻¹'
        {p : P.ChainPieces × P.ChainPieces | P.chainSetoid.r p.1 p.2} := by
    ext b
    exact ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩
  rw [hfiber]
  exact (P.chainSetoid_isClosed.preimage (continuous_id.prodMk continuous_const)).isCompact

/-- The actual compact chain quotient is Hausdorff: its diagonal is detected
by the closed proper product of the actual quotient projections. -/
instance gluedCarrierT2Space (P : ExerciseGluingPreparation C g n genera X) :
    T2Space P.GluedCarrier := by
  apply t2_iff_isClosed_diagonal.mpr
  have hproper := P.gluedMk_isProperMap.prodMap P.gluedMk_isProperMap
  have hsurj : Function.Surjective (Prod.map P.gluedMk P.gluedMk) := by
    rintro ⟨a, b⟩
    obtain ⟨x, rfl⟩ := Quotient.exists_rep a
    obtain ⟨y, rfl⟩ := Quotient.exists_rep b
    exact ⟨(x, y), rfl⟩
  apply (hproper.isClosedMap.isQuotientMap hproper.continuous hsurj).isClosed_preimage.mp
  convert P.chainSetoid_isClosed using 1
  ext p
  change P.gluedMk p.1 = P.gluedMk p.2 ↔ P.chainSetoid.r p.1 p.2
  exact ⟨Quotient.exact, Quotient.sound⟩

/-- Each concrete retained component is a closed embedded subset of the
actual glued carrier, using its proved injection and compactness. -/
theorem gluedComponent_isClosedEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Topology.IsClosedEmbedding (fun x : P.ChainComponent i => P.gluedMk ⟨i, x⟩) :=
  (P.gluedMk_continuous.comp continuous_sigmaMk).isClosedEmbedding
    (P.gluedMk_injective_component i)

/-- The original punctured carrier is homeomorphic to its actual component
image in the quotient, not to an abstract replacement copy. -/
noncomputable def gluedComponentHomeomorph
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    P.ChainComponent i ≃ₜ Set.range (fun x : P.ChainComponent i => P.gluedMk ⟨i, x⟩) :=
  (P.gluedComponent_isClosedEmbedding i).isEmbedding.toHomeomorph

end ExerciseGluingPreparation

#print axioms ExerciseGluingPreparation.chainRelation_isClosed
#print axioms ExerciseGluingPreparation.chainSetoid_isClosed
#print axioms ExerciseGluingPreparation.gluedMk_isProperMap
#print axioms ExerciseGluingPreparation.gluedCarrierT2Space
#print axioms ExerciseGluingPreparation.gluedComponent_isClosedEmbedding
#print axioms ExerciseGluingPreparation.gluedComponentHomeomorph

end SystolicGrowth
