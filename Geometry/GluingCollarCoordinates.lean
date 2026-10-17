module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingPolarCollar
public import Geometry.GluingCollarNeighborhoods

@[expose] public section

/-!
# Polar coordinates on the actual retained collars

The positive-radius open polar chart restricts to the retained half-annulus,
including its inner circle. This gives actual incoming and outgoing collar
homeomorphisms with `Circle × Ico r R`, not merely coordinates on the
complement of the seam. No C¹ transition-map or metric-tensor assertion is
made here.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth

def Internal.GluingCollarCoordinatesHelpers.halfAnnulusInPolarAnnulus (o : ℍ) (r R : ℝ) (hr : 0 < r)
    (z : ↥(ball o R \ ball o r)) : GluingPolarAnnulus o (r / 2) R :=
  ⟨z.1, by
    have hl : r ≤ dist o z.1 := by
      apply le_of_not_gt
      intro h
      exact z.2.2 (by simpa only [mem_ball, dist_comm] using h)
    have hu : dist o z.1 < R := by simpa only [mem_ball, dist_comm] using z.2.1
    exact ⟨by linarith, hu⟩⟩

noncomputable def Internal.GluingCollarCoordinatesHelpers.halfAnnulusPolarForward (o : ℍ) (r R : ℝ) (hr : 0 < r)
    (z : ↥(ball o R \ ball o r)) : Circle × Ico r R :=
  ((gluingPolarCollarHomeomorph o (r / 2) R (by linarith)
    (Internal.GluingCollarCoordinatesHelpers.halfAnnulusInPolarAnnulus o r R hr z)).1,
    ⟨dist o z.1, by
      constructor
      · apply le_of_not_gt
        intro h
        exact z.2.2 (by simpa only [mem_ball, dist_comm] using h)
      · simpa only [mem_ball, dist_comm] using z.2.1⟩)

noncomputable def Internal.GluingCollarCoordinatesHelpers.halfAnnulusPolarBackward (o : ℍ) (r R : ℝ) (hr : 0 < r)
    (p : Circle × Ico r R) : ↥(ball o R \ ball o r) :=
  ⟨gluingPolarPoint o p.1 p.2.1, by
    have ht : 0 ≤ (p.2 : ℝ) := (hr.trans_le p.2.2.1).le
    constructor
    · simpa only [mem_ball, dist_comm, dist_gluingPolarPoint o p.1 ht] using p.2.2.2
    · simpa only [mem_ball, dist_comm, dist_gluingPolarPoint o p.1 ht, not_lt]
        using p.2.2.1⟩

theorem Internal.GluingCollarCoordinatesHelpers.halfAnnulusPolarForward_continuous
    (o : ℍ) (r R : ℝ) (hr : 0 < r) :
    Continuous (Internal.GluingCollarCoordinatesHelpers.halfAnnulusPolarForward o r R hr) := by
  have hsub : Continuous (Internal.GluingCollarCoordinatesHelpers.halfAnnulusInPolarAnnulus o r R hr) :=
    continuous_subtype_val.subtype_mk _
  have hangle :=
    ((gluingPolarCollarHomeomorph o (r / 2) R (by linarith)).continuous.comp hsub).fst
  exact hangle.prodMk ((continuous_const.dist continuous_subtype_val).subtype_mk _)

theorem Internal.GluingCollarCoordinatesHelpers.halfAnnulusPolarBackward_continuous
    (o : ℍ) (r R : ℝ) (hr : 0 < r) :
    Continuous (Internal.GluingCollarCoordinatesHelpers.halfAnnulusPolarBackward o r R hr) := by
  have hproj : Continuous (fun p : Circle × Ico r R => (p.1, (p.2 : ℝ))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  exact ((gluingPolarPoint_continuous o).comp hproj).subtype_mk _

/-- The actual retained half-annulus, including the inner seam, has the
concrete polar product coordinates. -/
noncomputable def gluingHalfAnnulusPolarHomeomorph
    (o : ℍ) (r R : ℝ) (hr : 0 < r) :
    ↥(ball o R \ ball o r) ≃ₜ Circle × Ico r R where
  toFun := Internal.GluingCollarCoordinatesHelpers.halfAnnulusPolarForward o r R hr
  invFun := Internal.GluingCollarCoordinatesHelpers.halfAnnulusPolarBackward o r R hr
  left_inv z := by
    apply Subtype.ext
    have h := congrArg Subtype.val
      ((gluingPolarCollarHomeomorph o (r / 2) R (by linarith)).left_inv
        (Internal.GluingCollarCoordinatesHelpers.halfAnnulusInPolarAnnulus o r R hr z))
    exact h
  right_inv p := by
    let p' : Circle × Ioo (r / 2) R :=
      (p.1, ⟨p.2.1, ⟨by linarith [p.2.2.1], p.2.2.2⟩⟩)
    have h := (gluingPolarCollarHomeomorph o (r / 2) R (by linarith)).right_inv p'
    apply Prod.ext
    · have hangle := congrArg (fun a : Circle × Ioo (r / 2) R => a.1) h
      exact hangle
    · apply Subtype.ext
      exact dist_gluingPolarPoint o p.1 (hr.trans_le p.2.2.1).le
  continuous_toFun := Internal.GluingCollarCoordinatesHelpers.halfAnnulusPolarForward_continuous o r R hr
  continuous_invFun := Internal.GluingCollarCoordinatesHelpers.halfAnnulusPolarBackward_continuous o r R hr

@[simp] theorem gluingHalfAnnulusPolarHomeomorph_radial
    (o : ℍ) (r R : ℝ) (hr : 0 < r) (z : ↥(ball o R \ ball o r)) :
    ((gluingHalfAnnulusPolarHomeomorph o r R hr z).2 : ℝ) = dist o z.1 := rfl

@[simp] theorem gluingHalfAnnulusPolarHomeomorph_symm_apply
    (o : ℍ) (r R : ℝ) (hr : 0 < r) (p : Circle × Ico r R) :
    ((gluingHalfAnnulusPolarHomeomorph o r R hr).symm p).1 =
      gluingPolarPoint o p.1 p.2.1 := rfl

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Actual incoming collar coordinates, including the retained inner circle. -/
noncomputable def incomingCollarPolarHomeomorph
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    P.incomingCollar i ≃ₜ Circle × Ico (gluingRadius C g) (gluingEmbeddedRadius C g) :=
  (P.incomingCollarHomeomorph i).symm.trans
    (gluingHalfAnnulusPolarHomeomorph _ _ _ P.radius_pos)

/-- Actual outgoing collar coordinates, with the same global radial cutoffs. -/
noncomputable def outgoingCollarPolarHomeomorph
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    P.outgoingCollar i ≃ₜ Circle × Ico (gluingRadius C g) (gluingEmbeddedRadius C g) :=
  (P.outgoingCollarHomeomorph i).symm.trans
    (gluingHalfAnnulusPolarHomeomorph _ _ _ P.radius_pos)

end ExerciseGluingPreparation

#print axioms gluingHalfAnnulusPolarHomeomorph
#print axioms ExerciseGluingPreparation.incomingCollarPolarHomeomorph
#print axioms ExerciseGluingPreparation.outgoingCollarPolarHomeomorph

end SystolicGrowth
