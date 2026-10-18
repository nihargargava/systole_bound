module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainQuotient

@[expose] public section

/-!
# Actual seam incidence and absence of extra chain identifications

The incoming and outgoing circles in one punctured component are disjoint
by the actual full-orbit separation. The concrete seam relation is therefore
a partial matching, with each partner uniquely determined by the retained
circle embeddings and the reflected circle isometry. Its equivalence closure
contains only equality and the two orientations of one genuine seam pair.
-/

open Metric Set UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth
namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The two actual quotient radius-r circles are disjoint: slightly larger
open orbit balls still have sum of radii exactly `R + r`. -/
theorem punctureCircles_disjoint (P : ExerciseGluingPreparation C g n genera X)
    (i : Fin n) :
    Disjoint ((X i).punctureCircle (P.centers i).1 (gluingRadius C g))
      ((X i).punctureCircle (P.centers i).2 (gluingRadius C g)) := by
  let a := (gluingEmbeddedRadius C g + gluingRadius C g) / 2
  have hra : gluingRadius C g < a := by
    dsimp [a]
    linarith [P.radius_lt_embeddedRadius]
  have hdis := (X i).disjoint_orbitBalls_of_orbit_separated
    (P.centers i).1 (P.centers i).2 a a (by
      intro γ
      have h := P.separated_outer_add_inner i γ
      dsimp [a]
      linarith)
  exact hdis.mono (Set.image_mono (Metric.sphere_subset_ball hra))
    (Set.image_mono (Metric.sphere_subset_ball hra))

/-- Incoming and outgoing circle points cannot coincide in their actual
retained component carrier. -/
theorem leftCirclePoint_ne_rightCirclePoint
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (z : sphere (P.centers i).1 (gluingRadius C g))
    (w : sphere (P.centers i).2 (gluingRadius C g)) :
    P.leftCirclePoint i z ≠ P.rightCirclePoint i w := by
  intro h
  have hq := congrArg Subtype.val h
  change (Quotient.mk'' z.1 : (X i).Carrier) = Quotient.mk'' w.1 at hq
  have hz : (Quotient.mk'' z.1 : (X i).Carrier) ∈
      (X i).punctureCircle (P.centers i).1 (gluingRadius C g) := ⟨z.1, z.2, rfl⟩
  have hw : (Quotient.mk'' z.1 : (X i).Carrier) ∈
      (X i).punctureCircle (P.centers i).2 (gluingRadius C g) := by
    rw [hq]
    exact ⟨w.1, w.2, rfl⟩
  exact Set.disjoint_left.mp (P.punctureCircles_disjoint i) hz hw

/-- The actual two seam-map ranges within a component are disjoint. -/
theorem circlePoint_ranges_disjoint (P : ExerciseGluingPreparation C g n genera X)
    (i : Fin n) : Disjoint (Set.range (P.leftCirclePoint i))
      (Set.range (P.rightCirclePoint i)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨z, rfl⟩ ⟨w, hw⟩
  exact P.leftCirclePoint_ne_rightCirclePoint i z w hw.symm

theorem chainRelation_source_mem_rightCircle
    (P : ExerciseGluingPreparation C g n genera X) {a b : P.ChainPieces}
    (hab : P.chainRelation a b) : a.2 ∈ Set.range (P.rightCirclePoint a.1) := by
  obtain ⟨k, z, rfl, rfl⟩ := hab
  exact ⟨z, rfl⟩

theorem chainRelation_target_mem_leftCircle
    (P : ExerciseGluingPreparation C g n genera X) {a b : P.ChainPieces}
    (hab : P.chainRelation a b) : b.2 ∈ Set.range (P.leftCirclePoint b.1) := by
  obtain ⟨k, z, rfl, rfl⟩ := hab
  exact ⟨_, rfl⟩

/-- No point can be both the target of one actual seam and the source of
another: that would belong to the two disjoint circles in its component. -/
theorem chainRelation_no_two_step (P : ExerciseGluingPreparation C g n genera X)
    {a b c : P.ChainPieces} (hab : P.chainRelation a b) (hbc : P.chainRelation b c) :
    False :=
  Set.disjoint_left.mp (P.circlePoint_ranges_disjoint b.1)
    (P.chainRelation_target_mem_leftCircle hab) (P.chainRelation_source_mem_rightCircle hbc)

/-- The actual outgoing embedding determines the unique partner of a source
point; its component index determines the path edge. -/
theorem chainRelation_right_unique (P : ExerciseGluingPreparation C g n genera X)
    {a b c : P.ChainPieces} (hab : P.chainRelation a b) (hac : P.chainRelation a c) :
    b = c := by
  obtain ⟨k, z, hak, hbk⟩ := hab
  obtain ⟨l, w, hal, hcl⟩ := hac
  have hs : P.seamSource k z = P.seamSource l w := hak.symm.trans hal
  have hv := congrArg (fun s : P.ChainPieces => s.1.1) hs
  change k.1 = l.1 at hv
  have hkl : k = l := Fin.ext hv
  subst l
  have hcirc : P.rightCirclePoint (gluingChainEdgeLeft k) z =
      P.rightCirclePoint (gluingChainEdgeLeft k) w :=
    eq_of_heq (Sigma.mk.inj_iff.mp hs).2
  have hzw := (P.rightCirclePoint_isEmbedding (gluingChainEdgeLeft k)).injective hcirc
  subst w
  exact hbk.trans hcl.symm

/-- The incoming embedding and the actual reflected isometry also determine
the unique source of a target point. -/
theorem chainRelation_left_unique (P : ExerciseGluingPreparation C g n genera X)
    {a b c : P.ChainPieces} (hab : P.chainRelation a b) (hcb : P.chainRelation c b) :
    a = c := by
  obtain ⟨k, z, hak, hbk⟩ := hab
  obtain ⟨l, w, hcl, hbl⟩ := hcb
  have ht : P.seamTarget k z = P.seamTarget l w := hbk.symm.trans hbl
  have hv := congrArg (fun s : P.ChainPieces => s.1.1) ht
  change k.1 + 1 = l.1 + 1 at hv
  have hkl : k = l := Fin.ext (by omega)
  subst l
  have hcirc := eq_of_heq (Sigma.mk.inj_iff.mp ht).2
  have htransport :=
    (P.leftCirclePoint_isEmbedding (gluingChainEdgeRight k)).injective hcirc
  have hzw :=
    (gluingBoundaryCircleIsometry (P.centers (gluingChainEdgeLeft k)).2
      (P.centers (gluingChainEdgeRight k)).1 (gluingRadius C g)).injective htransport
  subst w
  exact hak.trans hcl.symm

/-- The generated equivalence relation makes no hidden extra identifications:
two points are equivalent only if they coincide or form one actual seam pair. -/
theorem eqvGen_chainRelation_iff (P : ExerciseGluingPreparation C g n genera X)
    (a b : P.ChainPieces) :
    Relation.EqvGen P.chainRelation a b ↔
      a = b ∨ P.chainRelation a b ∨ P.chainRelation b a := by
  constructor
  · intro h
    induction h with
    | rel a b hab => exact Or.inr (Or.inl hab)
    | refl a => exact Or.inl rfl
    | symm a b hab ih =>
      rcases ih with heq | hab | hba
      · exact Or.inl heq.symm
      · exact Or.inr (Or.inr hab)
      · exact Or.inr (Or.inl hba)
    | trans a b c hab hbc ihab ihbc =>
      rcases ihab with heq | hab | hba
      · subst b
        exact ihbc
      · rcases ihbc with heq | hbc | hcb
        · subst c
          exact Or.inr (Or.inl hab)
        · exact (P.chainRelation_no_two_step hab hbc).elim
        · exact Or.inl (P.chainRelation_left_unique hab hcb)
      · rcases ihbc with heq | hbc | hcb
        · subst c
          exact Or.inr (Or.inr hba)
        · exact Or.inl (P.chainRelation_right_unique hba hbc)
        · exact (P.chainRelation_no_two_step hcb hba).elim
  · rintro (heq | hab | hba)
    · subst b
      exact Relation.EqvGen.refl a
    · exact Relation.EqvGen.rel a b hab
    · exact Relation.EqvGen.symm b a (Relation.EqvGen.rel b a hba)

/-- Exact equality in the actual glued quotient is already decided by the
one-step seam matching, not by an assumed equivalence-class description. -/
theorem gluedMk_eq_iff (P : ExerciseGluingPreparation C g n genera X)
    (a b : P.ChainPieces) :
    P.gluedMk a = P.gluedMk b ↔ a = b ∨ P.chainRelation a b ∨ P.chainRelation b a := by
  constructor
  · intro h
    exact (P.eqvGen_chainRelation_iff a b).mp (Quotient.exact h)
  · intro h
    exact Quotient.sound ((P.eqvGen_chainRelation_iff a b).mpr h)

/-- An actual punctured component injects into the glued carrier: the seam
equivalence closure cannot identify two different points of that component. -/
theorem gluedMk_injective_component (P : ExerciseGluingPreparation C g n genera X)
    (i : Fin n) :
    Function.Injective (fun x : P.ChainComponent i => P.gluedMk ⟨i, x⟩) := by
  intro x y h
  rcases (P.gluedMk_eq_iff ⟨i, x⟩ ⟨i, y⟩).mp h with hxy | hrel | hrev
  · exact eq_of_heq (Sigma.mk.inj_iff.mp hxy).2
  · exact (P.chainRelation_components_ne hrel rfl).elim
  · exact (P.chainRelation_components_ne hrev rfl).elim

end ExerciseGluingPreparation

#print axioms ExerciseGluingPreparation.circlePoint_ranges_disjoint
#print axioms ExerciseGluingPreparation.chainRelation_right_unique
#print axioms ExerciseGluingPreparation.chainRelation_left_unique
#print axioms ExerciseGluingPreparation.eqvGen_chainRelation_iff
#print axioms ExerciseGluingPreparation.gluedMk_injective_component

end SystolicGrowth
