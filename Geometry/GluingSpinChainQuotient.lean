module

public import Geometry.GluingSpinBoundaryCharts
public import Geometry.GluingChainQuotient

@[expose] public section

open UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Restrict the actual component spin directions to the retained piece. -/
abbrev SpinChainComponent (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :=
  {q : (X i).SpinCarrier // (X i).spinBase q ∈
    (X i).puncturedComponentSet (P.centers i).1 (P.centers i).2 (gluingRadius C g) i}

/-- Restrict the actual component tangent directions to that same piece. -/
abbrev TangentChainComponent (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :=
  {q : (X i).TangentFrameCarrier // (X i).tangentFrameBase q ∈
    (X i).puncturedComponentSet (P.centers i).1 (P.centers i).2 (gluingRadius C g) i}

abbrev SpinChainPieces (P : ExerciseGluingPreparation C g n genera X) :=
  Σ i : Fin n, P.SpinChainComponent i

abbrev TangentChainPieces (P : ExerciseGluingPreparation C g n genera X) :=
  Σ i : Fin n, P.TangentChainComponent i

/-- The unchanged actual base point of each retained spin direction. -/
def spinChainComponentBase (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (q : P.SpinChainComponent i) : P.ChainComponent i := ⟨(X i).spinBase q.1, q.2⟩

def tangentChainComponentBase (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (q : P.TangentChainComponent i) : P.ChainComponent i :=
  ⟨(X i).tangentFrameBase q.1, q.2⟩

def spinChainComponentSquare (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (q : P.SpinChainComponent i) : P.TangentChainComponent i :=
  ⟨(X i).spinSquare q.1, by simpa using q.2⟩

theorem continuous_spinChainComponentSquare
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Continuous (P.spinChainComponentSquare i) :=
  ((X i).continuous_spinSquare.comp continuous_subtype_val).subtype_mk _

theorem spinChainComponentSquare_surjective
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Function.Surjective (P.spinChainComponentSquare i) := by
  intro q
  obtain ⟨r, hr⟩ := (X i).spinSquare_surjective q.1
  refine ⟨⟨r, ?_⟩, Subtype.ext hr⟩
  simpa [← hr] using q.2

private theorem polarBoundary_subset_punctureCircle
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (o : ℍ) :
    (X i).polarBoundary o (gluingRadius C g) ⊆
      (X i).punctureCircle o (gluingRadius C g) := by
  rintro _ ⟨u, rfl⟩
  refine ⟨gluingPolarPoint o u (gluingRadius C g), ?_, rfl⟩
  simpa [Metric.mem_sphere, dist_comm] using
    dist_gluingPolarPoint o u P.radius_pos.le

theorem polarLeftBoundary_retained
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    (X i).polarBoundary (P.centers i).1 (gluingRadius C g) ⊆
      (X i).puncturedComponentSet (P.centers i).1 (P.centers i).2 (gluingRadius C g) i :=
  (P.polarBoundary_subset_punctureCircle i _).trans
    ((X i).punctureCircle_left_subset_puncturedComponentSet _ _ _ _ i
      P.radius_lt_embeddedRadius (P.twice_outer_lt_systole i)
      (P.separated_outer_add_inner i))

theorem polarRightBoundary_retained
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    (X i).polarBoundary (P.centers i).2 (gluingRadius C g) ⊆
      (X i).puncturedComponentSet (P.centers i).1 (P.centers i).2 (gluingRadius C g) i :=
  (P.polarBoundary_subset_punctureCircle i _).trans
    ((X i).punctureCircle_right_subset_puncturedComponentSet _ _ _ _ i
      P.radius_lt_embeddedRadius (P.twice_outer_lt_systole i)
      (P.separated_outer_add_inner i))

def spinLeftBoundaryInclusion (P : ExerciseGluingPreparation C g n genera X)
    (i : Fin n) (q : (X i).SpinBoundaryCarrier (P.centers i).1 (gluingRadius C g)) :
    P.SpinChainComponent i := ⟨q.1, P.polarLeftBoundary_retained i q.2⟩

def spinRightBoundaryInclusion (P : ExerciseGluingPreparation C g n genera X)
    (i : Fin n) (q : (X i).SpinBoundaryCarrier (P.centers i).2 (gluingRadius C g)) :
    P.SpinChainComponent i := ⟨q.1, P.polarRightBoundary_retained i q.2⟩

def tangentLeftBoundaryInclusion (P : ExerciseGluingPreparation C g n genera X)
    (i : Fin n) (q : (X i).TangentBoundaryCarrier (P.centers i).1 (gluingRadius C g)) :
    P.TangentChainComponent i := ⟨q.1, P.polarLeftBoundary_retained i q.2⟩

def tangentRightBoundaryInclusion (P : ExerciseGluingPreparation C g n genera X)
    (i : Fin n) (q : (X i).TangentBoundaryCarrier (P.centers i).2 (gluingRadius C g)) :
    P.TangentChainComponent i := ⟨q.1, P.polarRightBoundary_retained i q.2⟩

/-- The actual prepared edge uses the previously constructed literal Fermi
square root, with all embeddedness bounds supplied by the preparation. -/
def seamSpinHomeomorph (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) :
    (X (gluingChainEdgeLeft k)).SpinBoundaryCarrier
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) ≃ₜ
        (X (gluingChainEdgeRight k)).SpinBoundaryCarrier
          (P.centers (gluingChainEdgeRight k)).1 (gluingRadius C g) :=
  ClosedHyperbolicSurface.fermiSpinBoundaryHomeomorph
    (X (gluingChainEdgeRight k)) (X (gluingChainEdgeLeft k))
    (P.centers (gluingChainEdgeRight k)).1 (P.centers (gluingChainEdgeLeft k)).2
    P.radius_pos P.radius_lt_embeddedRadius P.radius_lt_embeddedRadius
    (P.twice_outer_lt_systole _) (P.twice_outer_lt_systole _)

def seamTangentHomeomorph (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) :
    (X (gluingChainEdgeLeft k)).TangentBoundaryCarrier
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) ≃ₜ
        (X (gluingChainEdgeRight k)).TangentBoundaryCarrier
          (P.centers (gluingChainEdgeRight k)).1 (gluingRadius C g) :=
  ClosedHyperbolicSurface.fermiTangentBoundaryHomeomorph
    (X (gluingChainEdgeRight k)) (X (gluingChainEdgeLeft k))
    (P.centers (gluingChainEdgeRight k)).1 (P.centers (gluingChainEdgeLeft k)).2
    P.radius_pos P.radius_lt_embeddedRadius P.radius_lt_embeddedRadius
    (P.twice_outer_lt_systole _) (P.twice_outer_lt_systole _)

theorem seamSpinHomeomorph_square
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (q : (X (gluingChainEdgeLeft k)).SpinBoundaryCarrier
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g)) :
    (X (gluingChainEdgeRight k)).spinBoundarySquare
      (P.centers (gluingChainEdgeRight k)).1 (gluingRadius C g)
        (P.seamSpinHomeomorph k q) =
          P.seamTangentHomeomorph k
            ((X (gluingChainEdgeLeft k)).spinBoundarySquare
              (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) q) :=
  ClosedHyperbolicSurface.fermiSpinBoundaryHomeomorph_square _ _ _ _ _ _ _ _ _ q

def spinSeamSource (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1))
    (q : (X (gluingChainEdgeLeft k)).SpinBoundaryCarrier
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g)) : P.SpinChainPieces :=
  ⟨gluingChainEdgeLeft k, P.spinRightBoundaryInclusion _ q⟩

def spinSeamTarget (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1))
    (q : (X (gluingChainEdgeLeft k)).SpinBoundaryCarrier
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g)) : P.SpinChainPieces :=
  ⟨gluingChainEdgeRight k, P.spinLeftBoundaryInclusion _ (P.seamSpinHomeomorph k q)⟩

def tangentSeamSource (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1))
    (q : (X (gluingChainEdgeLeft k)).TangentBoundaryCarrier
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g)) : P.TangentChainPieces :=
  ⟨gluingChainEdgeLeft k, P.tangentRightBoundaryInclusion _ q⟩

def tangentSeamTarget (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1))
    (q : (X (gluingChainEdgeLeft k)).TangentBoundaryCarrier
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g)) : P.TangentChainPieces :=
  ⟨gluingChainEdgeRight k, P.tangentLeftBoundaryInclusion _ (P.seamTangentHomeomorph k q)⟩

def spinChainRelation (P : ExerciseGluingPreparation C g n genera X)
    (a b : P.SpinChainPieces) : Prop :=
  ∃ k : Fin (n - 1), ∃ q, a = P.spinSeamSource k q ∧ b = P.spinSeamTarget k q

def tangentChainRelation (P : ExerciseGluingPreparation C g n genera X)
    (a b : P.TangentChainPieces) : Prop :=
  ∃ k : Fin (n - 1), ∃ q, a = P.tangentSeamSource k q ∧ b = P.tangentSeamTarget k q

def spinChainSetoid (P : ExerciseGluingPreparation C g n genera X) :
    Setoid P.SpinChainPieces := Relation.EqvGen.setoid P.spinChainRelation

def tangentChainSetoid (P : ExerciseGluingPreparation C g n genera X) :
    Setoid P.TangentChainPieces := Relation.EqvGen.setoid P.tangentChainRelation

/-- The actual spin-boundary-clutched quotient of the retained components. -/
abbrev GluedSpinCarrier (P : ExerciseGluingPreparation C g n genera X) :=
  Quotient P.spinChainSetoid

/-- The corresponding actual clutched oriented-direction carrier. -/
abbrev GluedTangentCarrier (P : ExerciseGluingPreparation C g n genera X) :=
  Quotient P.tangentChainSetoid

def spinChainPieceBase (P : ExerciseGluingPreparation C g n genera X)
    (a : P.SpinChainPieces) : P.ChainPieces := ⟨a.1, P.spinChainComponentBase a.1 a.2⟩

def tangentChainPieceBase (P : ExerciseGluingPreparation C g n genera X)
    (a : P.TangentChainPieces) : P.ChainPieces :=
  ⟨a.1, P.tangentChainComponentBase a.1 a.2⟩

def spinChainPieceSquare (P : ExerciseGluingPreparation C g n genera X)
    (a : P.SpinChainPieces) : P.TangentChainPieces :=
  ⟨a.1, P.spinChainComponentSquare a.1 a.2⟩

theorem continuous_spinChainPieceBase (P : ExerciseGluingPreparation C g n genera X) :
    Continuous P.spinChainPieceBase := by
  change Continuous (Sigma.map id P.spinChainComponentBase)
  apply continuous_sigma_map.mpr
  intro i
  exact ((X i).continuous_spinBase.comp continuous_subtype_val).subtype_mk _

theorem continuous_tangentChainPieceBase
    (P : ExerciseGluingPreparation C g n genera X) :
    Continuous P.tangentChainPieceBase := by
  change Continuous (Sigma.map id P.tangentChainComponentBase)
  apply continuous_sigma_map.mpr
  intro i
  exact ((X i).continuous_tangentFrameBase.comp continuous_subtype_val).subtype_mk _

theorem continuous_spinChainPieceSquare
    (P : ExerciseGluingPreparation C g n genera X) :
    Continuous P.spinChainPieceSquare :=
  Continuous.sigma_map P.continuous_spinChainComponentSquare

/-- Actual prepared spin seam endpoints project to the prescribed base seam. -/
theorem gluedMk_spinSeamBase_eq (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1))
    (q : (X (gluingChainEdgeLeft k)).SpinBoundaryCarrier
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g)) :
    P.gluedMk (P.spinChainPieceBase (P.spinSeamSource k q)) =
      P.gluedMk (P.spinChainPieceBase (P.spinSeamTarget k q)) := by
  obtain ⟨p, rfl⟩ := (X (gluingChainEdgeLeft k)).spinBoundaryParam_surjective
    (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) q
  let z : Metric.sphere (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) :=
    ⟨gluingPolarPoint (P.centers (gluingChainEdgeLeft k)).2 p.1 (gluingRadius C g), by
      simpa [Metric.mem_sphere, dist_comm] using
        dist_gluingPolarPoint _ p.1 P.radius_pos.le⟩
  have hs : P.spinChainPieceBase (P.spinSeamSource k
      ((X (gluingChainEdgeLeft k)).spinBoundaryParam
        (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) p)) =
      P.seamSource k z := rfl
  have ht : P.spinChainPieceBase (P.spinSeamTarget k
      ((X (gluingChainEdgeLeft k)).spinBoundaryParam
        (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) p)) =
      P.seamTarget k z := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact ClosedHyperbolicSurface.fermiSpinBoundaryHomeomorph_base
        (X (gluingChainEdgeRight k)) (X (gluingChainEdgeLeft k))
        (P.centers (gluingChainEdgeRight k)).1 (P.centers (gluingChainEdgeLeft k)).2
        P.radius_pos P.radius_lt_embeddedRadius P.radius_lt_embeddedRadius
        (P.twice_outer_lt_systole _) (P.twice_outer_lt_systole _) p
  rw [hs, ht]
  exact P.gluedMk_seamSource_eq_seamTarget k z

theorem gluedMk_tangentSeamBase_eq (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1))
    (q : (X (gluingChainEdgeLeft k)).TangentBoundaryCarrier
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g)) :
    P.gluedMk (P.tangentChainPieceBase (P.tangentSeamSource k q)) =
      P.gluedMk (P.tangentChainPieceBase (P.tangentSeamTarget k q)) := by
  obtain ⟨r, hr⟩ := (X (gluingChainEdgeLeft k)).spinSquare_surjective q.1
  let r' : (X (gluingChainEdgeLeft k)).SpinBoundaryCarrier
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) :=
    ⟨r, by simpa [← hr] using q.2⟩
  have he : (X (gluingChainEdgeLeft k)).spinBoundarySquare
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) r' = q := Subtype.ext hr
  rw [← he]
  have hs : P.tangentChainPieceBase (P.tangentSeamSource k
      ((X (gluingChainEdgeLeft k)).spinBoundarySquare
        (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) r')) =
      P.spinChainPieceBase (P.spinSeamSource k r') := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact (X (gluingChainEdgeLeft k)).tangentFrameBase_spinSquare r'.1
  have ht : P.tangentChainPieceBase (P.tangentSeamTarget k
      ((X (gluingChainEdgeLeft k)).spinBoundarySquare
        (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) r')) =
      P.spinChainPieceBase (P.spinSeamTarget k r') := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      change (X (gluingChainEdgeRight k)).tangentFrameBase
        (P.seamTangentHomeomorph k
          ((X (gluingChainEdgeLeft k)).spinBoundarySquare
            (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) r')).1 = _
      rw [← P.seamSpinHomeomorph_square]
      exact (X (gluingChainEdgeRight k)).tangentFrameBase_spinSquare
        (P.seamSpinHomeomorph k r').1
  rw [hs, ht]
  exact P.gluedMk_spinSeamBase_eq k r'

/-- The genuine spin quotient projects to the unchanged actual glued surface. -/
def gluedSpinBase (P : ExerciseGluingPreparation C g n genera X) :
    P.GluedSpinCarrier → P.GluedCarrier :=
  Quotient.lift (fun a => P.gluedMk (P.spinChainPieceBase a)) fun a b h => by
    change Relation.EqvGen P.spinChainRelation a b at h
    induction h with
    | rel a b h =>
      obtain ⟨k, q, rfl, rfl⟩ := h
      exact P.gluedMk_spinSeamBase_eq k q
    | refl a => rfl
    | symm a b h ih => exact ih.symm
    | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc

def gluedTangentBase (P : ExerciseGluingPreparation C g n genera X) :
    P.GluedTangentCarrier → P.GluedCarrier :=
  Quotient.lift (fun a => P.gluedMk (P.tangentChainPieceBase a)) fun a b h => by
    change Relation.EqvGen P.tangentChainRelation a b at h
    induction h with
    | rel a b h =>
      obtain ⟨k, q, rfl, rfl⟩ := h
      exact P.gluedMk_tangentSeamBase_eq k q
    | refl a => rfl
    | symm a b h ih => exact ih.symm
    | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc

@[simp] theorem spinChainPieceSquare_seamSource
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (q : (X (gluingChainEdgeLeft k)).SpinBoundaryCarrier
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g)) :
    P.spinChainPieceSquare (P.spinSeamSource k q) = P.tangentSeamSource k
      ((X (gluingChainEdgeLeft k)).spinBoundarySquare
        (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) q) := rfl

@[simp] theorem spinChainPieceSquare_seamTarget
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (q : (X (gluingChainEdgeLeft k)).SpinBoundaryCarrier
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g)) :
    P.spinChainPieceSquare (P.spinSeamTarget k q) = P.tangentSeamTarget k
      ((X (gluingChainEdgeLeft k)).spinBoundarySquare
        (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) q) := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    change (X (gluingChainEdgeRight k)).spinSquare (P.seamSpinHomeomorph k q).1 =
      (P.seamTangentHomeomorph k
        ((X (gluingChainEdgeLeft k)).spinBoundarySquare
          (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) q)).1
    exact congrArg Subtype.val (P.seamSpinHomeomorph_square k q)

/-- The genuine component double maps descend through literal seam clutching. -/
def gluedSpinSquare (P : ExerciseGluingPreparation C g n genera X) :
    P.GluedSpinCarrier → P.GluedTangentCarrier :=
  Quotient.map P.spinChainPieceSquare fun a b h => by
    change Relation.EqvGen P.spinChainRelation a b at h
    change Relation.EqvGen P.tangentChainRelation _ _
    induction h with
    | rel a b h =>
      obtain ⟨k, q, rfl, rfl⟩ := h
      rw [P.spinChainPieceSquare_seamSource, P.spinChainPieceSquare_seamTarget]
      exact Relation.EqvGen.rel _ _ ⟨k, _, rfl, rfl⟩
    | refl a => exact Relation.EqvGen.refl _
    | symm a b h ih => exact ih.symm
    | trans a b c hab hbc ihab ihbc => exact Relation.EqvGen.trans _ _ _ ihab ihbc

/-- Squaring preserves the unchanged actual glued surface point. -/
@[simp] theorem gluedTangentBase_gluedSpinSquare
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedSpinCarrier) :
    P.gluedTangentBase (P.gluedSpinSquare q) = P.gluedSpinBase q := by
  induction q using Quotient.inductionOn with
  | h q =>
    apply congrArg P.gluedMk
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact (X q.1).tangentFrameBase_spinSquare q.2.1

theorem continuous_gluedSpinBase (P : ExerciseGluingPreparation C g n genera X) :
    Continuous P.gluedSpinBase :=
  (P.gluedMk_continuous.comp P.continuous_spinChainPieceBase).quotient_lift _

theorem continuous_gluedTangentBase (P : ExerciseGluingPreparation C g n genera X) :
    Continuous P.gluedTangentBase :=
  (P.gluedMk_continuous.comp P.continuous_tangentChainPieceBase).quotient_lift _

theorem continuous_gluedSpinSquare (P : ExerciseGluingPreparation C g n genera X) :
    Continuous P.gluedSpinSquare :=
  (continuous_quotient_mk'.comp P.continuous_spinChainPieceSquare).quotient_lift _

/-- Surjectivity survives the genuine finite seam quotient. -/
theorem gluedSpinSquare_surjective (P : ExerciseGluingPreparation C g n genera X) :
    Function.Surjective P.gluedSpinSquare := by
  intro q
  induction q using Quotient.inductionOn with
  | h q =>
    obtain ⟨r, hr⟩ := P.spinChainComponentSquare_surjective q.1 q.2
    refine ⟨Quotient.mk _ ⟨q.1, r⟩, ?_⟩
    change Quotient.mk _ (P.spinChainPieceSquare ⟨q.1, r⟩) = Quotient.mk _ q
    apply congrArg (Quotient.mk _)
    apply Sigma.ext
    · rfl
    · exact heq_of_eq hr

end ExerciseGluingPreparation

#print axioms ExerciseGluingPreparation.seamSpinHomeomorph_square
#print axioms ExerciseGluingPreparation.gluedMk_spinSeamBase_eq
#print axioms ExerciseGluingPreparation.gluedMk_tangentSeamBase_eq
#print axioms ExerciseGluingPreparation.gluedSpinBase
#print axioms ExerciseGluingPreparation.gluedSpinSquare
#print axioms ExerciseGluingPreparation.gluedTangentBase_gluedSpinSquare
#print axioms ExerciseGluingPreparation.continuous_gluedSpinSquare
#print axioms ExerciseGluingPreparation.gluedSpinSquare_surjective

end
end SystolicGrowth
