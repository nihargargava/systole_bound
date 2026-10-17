module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainTopology

@[expose] public section

/-!
# Actual relative-open neighborhoods of the gluing circles

The collars are the existing quotient images of the upstairs half-annuli,
viewed in the retained component carriers. At a genuinely deleted disk they
are exactly the retained part of the open outer orbit ball, hence relatively
open. Restriction of the actual embedded outer-ball chart gives their
homeomorphisms. Full-orbit separation excludes the other boundary circle;
no disjointness of the two outer balls or assumed polar chart is used.
-/

open Metric Set UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth
namespace ClosedHyperbolicSurface

/-- Restriction of the genuine outer-ball quotient chart embeds the upstairs
half-annulus, including its inner circle. -/
theorem quotientHalfAnnulus_isEmbedding {k : ℕ} (Y : ClosedHyperbolicSurface k)
    (o : ℍ) (r R : ℝ) (hR : 2 * R < Y.systole) :
    Topology.IsEmbedding
      (fun z : ↥(ball o R \ ball o r) => (Quotient.mk'' z.1 : Y.Carrier)) :=
  (Y.quotientBall_isOpenEmbedding o R hR).isEmbedding.comp
    (Topology.IsEmbedding.inclusion Set.sdiff_subset)

/-- Full-orbit separation excludes even the other inner boundary circle
from the open outer ball, with strictness supplied by that outer ball. -/
theorem orbitBall_disjoint_punctureCircle_of_orbit_separated {k : ℕ}
    (Y : ClosedHyperbolicSurface k) (left right : ℍ) (R r : ℝ)
    (hsep : ∀ γ : Y.deckGroup, R + r ≤ dist left (γ • right)) :
    Disjoint (Y.orbitBall left R) (Y.punctureCircle right r) := by
  apply Set.disjoint_left.mpr
  rintro q ⟨z, hz, hzq⟩ ⟨w, hw, hwq⟩
  have hrel : MulAction.orbitRel Y.deckGroup ℍ z w :=
    Quotient.exact (hzq.trans hwq.symm)
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hrel)
  have hzd : dist left z < R := by simpa only [Metric.mem_ball, dist_comm] using hz
  have hwd : dist z (γ • right) = r := by
    rw [← hγ, dist_smul]
    exact hw
  have hlt : dist left (γ • right) < R + r :=
    lt_of_le_of_lt (dist_triangle left z (γ • right)) (by linarith)
  exact (not_lt_of_ge (hsep γ)) hlt

end ClosedHyperbolicSurface

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The actual incoming half-annulus image in the retained component. -/
def incomingCollar (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Set (P.ChainComponent i) :=
  Subtype.val ⁻¹' (X i).punctureCollar (P.centers i).1
    (gluingRadius C g) (gluingEmbeddedRadius C g)

/-- The actual outgoing half-annulus image in the same retained component. -/
def outgoingCollar (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Set (P.ChainComponent i) :=
  Subtype.val ⁻¹' (X i).punctureCollar (P.centers i).2
    (gluingRadius C g) (gluingEmbeddedRadius C g)

/-- Where the incoming disk is genuinely deleted, the collar is precisely
the retained portion of the open outer orbit ball. -/
theorem incomingCollar_eq_outerBall (P : ExerciseGluingPreparation C g n genera X)
    (i : Fin n) (hi : 0 < i.1) :
    P.incomingCollar i = Subtype.val ⁻¹'
      (X i).orbitBall (P.centers i).1 (gluingEmbeddedRadius C g) := by
  ext q
  change q.1 ∈ (X i).punctureCollar _ _ _ ↔ q.1 ∈ (X i).orbitBall _ _
  constructor
  · intro hq
    exact (X i).punctureCollar_subset_orbitBall _ _ _ hq
  · rintro ⟨z, hz, hzq⟩
    have hnot : q.1 ∉ (X i).orbitBall (P.centers i).1 (gluingRadius C g) := by
      intro hq
      apply q.2
      simp only [ClosedHyperbolicSurface.punctureDeletedSet, if_pos hi, Set.mem_union]
      exact Or.inl hq
    refine ⟨z, ⟨hz, ?_⟩, hzq⟩
    intro hzr
    exact hnot ⟨z, hzr, hzq⟩

/-- The same precise relative-open description holds at an actual outgoing
deleted disk, including the first component of a nontrivial chain. -/
theorem outgoingCollar_eq_outerBall (P : ExerciseGluingPreparation C g n genera X)
    (i : Fin n) (hi : i.1 + 1 < n) :
    P.outgoingCollar i = Subtype.val ⁻¹'
      (X i).orbitBall (P.centers i).2 (gluingEmbeddedRadius C g) := by
  ext q
  change q.1 ∈ (X i).punctureCollar _ _ _ ↔ q.1 ∈ (X i).orbitBall _ _
  constructor
  · intro hq
    exact (X i).punctureCollar_subset_orbitBall _ _ _ hq
  · rintro ⟨z, hz, hzq⟩
    have hnot : q.1 ∉ (X i).orbitBall (P.centers i).2 (gluingRadius C g) := by
      intro hq
      apply q.2
      simp only [ClosedHyperbolicSurface.punctureDeletedSet, if_pos hi, Set.mem_union]
      exact Or.inr hq
    refine ⟨z, ⟨hz, ?_⟩, hzq⟩
    intro hzr
    exact hnot ⟨z, hzr, hzq⟩

theorem incomingCollar_isOpen (P : ExerciseGluingPreparation C g n genera X)
    (i : Fin n) (hi : 0 < i.1) : IsOpen (P.incomingCollar i) := by
  rw [P.incomingCollar_eq_outerBall i hi]
  exact ((X i).isOpen_orbitBall _ _).preimage continuous_subtype_val

theorem outgoingCollar_isOpen (P : ExerciseGluingPreparation C g n genera X)
    (i : Fin n) (hi : i.1 + 1 < n) : IsOpen (P.outgoingCollar i) := by
  rw [P.outgoingCollar_eq_outerBall i hi]
  exact ((X i).isOpen_orbitBall _ _).preimage continuous_subtype_val

/-- The actual quotient half-annulus map into the incoming retained collar. -/
noncomputable def incomingCollarPoint (P : ExerciseGluingPreparation C g n genera X)
    (i : Fin n)
    (z : ↥(ball (P.centers i).1 (gluingEmbeddedRadius C g) \
      ball (P.centers i).1 (gluingRadius C g))) : P.ChainComponent i :=
  ⟨Quotient.mk'' z.1,
    (X i).punctureCollar_left_subset_puncturedComponentSet _ _ _ _ i
      P.radius_lt_embeddedRadius (P.twice_outer_lt_systole i)
      (P.separated_outer_add_inner i) ⟨z.1, z.2, rfl⟩⟩

/-- The symmetric outgoing half-annulus map uses the same actual quotient. -/
noncomputable def outgoingCollarPoint (P : ExerciseGluingPreparation C g n genera X)
    (i : Fin n)
    (z : ↥(ball (P.centers i).2 (gluingEmbeddedRadius C g) \
      ball (P.centers i).2 (gluingRadius C g))) : P.ChainComponent i :=
  ⟨Quotient.mk'' z.1,
    (X i).punctureCollar_right_subset_puncturedComponentSet _ _ _ _ i
      P.radius_lt_embeddedRadius (P.twice_outer_lt_systole i)
      (P.separated_outer_add_inner i) ⟨z.1, z.2, rfl⟩⟩

theorem incomingCollarPoint_isEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Topology.IsEmbedding (P.incomingCollarPoint i) :=
  ((X i).quotientHalfAnnulus_isEmbedding _ _ _ (P.twice_outer_lt_systole i)).codRestrict
    ((X i).puncturedComponentSet (P.centers i).1 (P.centers i).2 (gluingRadius C g) i) _

theorem outgoingCollarPoint_isEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Topology.IsEmbedding (P.outgoingCollarPoint i) :=
  ((X i).quotientHalfAnnulus_isEmbedding _ _ _ (P.twice_outer_lt_systole i)).codRestrict
    ((X i).puncturedComponentSet (P.centers i).1 (P.centers i).2 (gluingRadius C g) i) _

theorem incomingCollarPoint_range (P : ExerciseGluingPreparation C g n genera X)
    (i : Fin n) : Set.range (P.incomingCollarPoint i) = P.incomingCollar i := by
  ext q
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z.1, z.2, rfl⟩
  · rintro ⟨z, hz, hzq⟩
    exact ⟨⟨z, hz⟩, Subtype.ext hzq⟩

theorem outgoingCollarPoint_range (P : ExerciseGluingPreparation C g n genera X)
    (i : Fin n) : Set.range (P.outgoingCollarPoint i) = P.outgoingCollar i := by
  ext q
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z.1, z.2, rfl⟩
  · rintro ⟨z, hz, hzq⟩
    exact ⟨⟨z, hz⟩, Subtype.ext hzq⟩

theorem incomingCollarPoint_isOpenEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (hi : 0 < i.1) :
    Topology.IsOpenEmbedding (P.incomingCollarPoint i) := by
  refine ⟨P.incomingCollarPoint_isEmbedding i, ?_⟩
  rw [P.incomingCollarPoint_range i]
  exact P.incomingCollar_isOpen i hi

theorem outgoingCollarPoint_isOpenEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (hi : i.1 + 1 < n) :
    Topology.IsOpenEmbedding (P.outgoingCollarPoint i) := by
  refine ⟨P.outgoingCollarPoint_isEmbedding i, ?_⟩
  rw [P.outgoingCollarPoint_range i]
  exact P.outgoingCollar_isOpen i hi

/-- The actual incoming collar is homeomorphic to its genuine upstairs
half-annulus, without an assumed collar or polar-coordinate field. -/
noncomputable def incomingCollarHomeomorph
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    ↥(ball (P.centers i).1 (gluingEmbeddedRadius C g) \
      ball (P.centers i).1 (gluingRadius C g)) ≃ₜ P.incomingCollar i :=
  (P.incomingCollarPoint_isEmbedding i).toHomeomorph.trans
    (Homeomorph.setCongr (P.incomingCollarPoint_range i))

noncomputable def outgoingCollarHomeomorph
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    ↥(ball (P.centers i).2 (gluingEmbeddedRadius C g) \
      ball (P.centers i).2 (gluingRadius C g)) ≃ₜ P.outgoingCollar i :=
  (P.outgoingCollarPoint_isEmbedding i).toHomeomorph.trans
    (Homeomorph.setCongr (P.outgoingCollarPoint_range i))

theorem leftCirclePoint_mem_incomingCollar
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (z : sphere (P.centers i).1 (gluingRadius C g)) :
    P.leftCirclePoint i z ∈ P.incomingCollar i :=
  (X i).punctureCircle_subset_collar _ _ _ P.radius_lt_embeddedRadius ⟨z.1, z.2, rfl⟩

theorem rightCirclePoint_mem_outgoingCollar
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (z : sphere (P.centers i).2 (gluingRadius C g)) :
    P.rightCirclePoint i z ∈ P.outgoingCollar i :=
  (X i).punctureCircle_subset_collar _ _ _ P.radius_lt_embeddedRadius ⟨z.1, z.2, rfl⟩

/-- The incoming collar avoids the entire other actual circle, even when
the outer quotient balls overlap. -/
theorem incomingCollar_disjoint_outgoingCircle
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Disjoint (P.incomingCollar i) (Set.range (P.rightCirclePoint i)) := by
  apply Set.disjoint_left.mpr
  rintro q hq ⟨z, hzq⟩
  have hball := (X i).punctureCollar_subset_orbitBall _ _ _ hq
  have hcircle : q.1 ∈ (X i).punctureCircle (P.centers i).2 (gluingRadius C g) :=
    ⟨z.1, z.2, congrArg Subtype.val hzq⟩
  exact Set.disjoint_left.mp
    ((X i).orbitBall_disjoint_punctureCircle_of_orbit_separated _ _ _ _
      (P.separated_outer_add_inner i)) hball hcircle

/-- The outgoing collar similarly avoids the incoming boundary circle. -/
theorem outgoingCollar_disjoint_incomingCircle
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Disjoint (P.outgoingCollar i) (Set.range (P.leftCirclePoint i)) := by
  apply Set.disjoint_left.mpr
  rintro q hq ⟨z, hzq⟩
  have hball := (X i).punctureCollar_subset_orbitBall _ _ _ hq
  have hcircle : q.1 ∈ (X i).punctureCircle (P.centers i).1 (gluingRadius C g) :=
    ⟨z.1, z.2, congrArg Subtype.val hzq⟩
  exact Set.disjoint_left.mp
    ((X i).orbitBall_disjoint_punctureCircle_of_orbit_separated _ _ _ _
      ((X i).orbit_separation_symm _ _ _ (P.separated_outer_add_inner i))) hball hcircle

end ExerciseGluingPreparation

#print axioms ExerciseGluingPreparation.incomingCollar_isOpen
#print axioms ExerciseGluingPreparation.outgoingCollar_isOpen
#print axioms ExerciseGluingPreparation.incomingCollarPoint_isOpenEmbedding
#print axioms ExerciseGluingPreparation.outgoingCollarPoint_isOpenEmbedding
#print axioms ExerciseGluingPreparation.incomingCollarHomeomorph
#print axioms ExerciseGluingPreparation.incomingCollar_disjoint_outgoingCircle
#print axioms ExerciseGluingPreparation.outgoingCollar_disjoint_incomingCircle

end SystolicGrowth
