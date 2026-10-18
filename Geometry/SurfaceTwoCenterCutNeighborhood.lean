module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceTwoCenterCutSpine
public import Geometry.SurfaceDeckCompactTube
public import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

/-!
# A uniformly separated tubular neighborhood of the actual lifted cut

The compact lift of the embedded two-center cut has positive separation from
all of its nonidentity deck translates. Proper discontinuity reduces the
uniform estimate to finitely many translates; freeness and injectivity of the
actual quotient cut rule out intersections for those finitely many translates.
Consequently a positive metric neighborhood descends injectively to the
surface quotient. This file constructs the actual neighborhood and does not
postulate a regular-neighborhood record.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane unitInterval

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The literal lift of the actual truncated center-to-center cut. -/
def componentTwoCenterLiftedCutPoint
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (t : I) : ℍ :=
  Vendored.RiemannDynamics.geodInterp (P.centers i).1
    (P.componentCenterClosestDeck i • (P.centers i).2)
    (P.componentTwoCenterCutCoordinate i t)

/-- The compact set traced out by the actual lifted cut. -/
def componentTwoCenterLiftedCutSet
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) : Set ℍ :=
  range (P.componentTwoCenterLiftedCutPoint i)

theorem componentTwoCenterLiftedCutPoint_continuous
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Continuous (P.componentTwoCenterLiftedCutPoint i) := by
  change Continuous (fun t : I => Vendored.RiemannDynamics.geodInterp
    (P.centers i).1 (P.componentCenterClosestDeck i • (P.centers i).2)
    (P.componentTwoCenterCutCoordinate i t))
  have hcoord : Continuous (P.componentTwoCenterCutCoordinate i) := by
    apply Continuous.subtype_mk
    fun_prop
  exact Vendored.RiemannDynamics.continuous_geodInterp.comp
    (continuous_const.prodMk
      (continuous_const.prodMk (continuous_subtype_val.comp hcoord)))

@[simp]
theorem componentTwoCenterLiftedCutPoint_project
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (t : I) :
    Quotient.mk'' (P.componentTwoCenterLiftedCutPoint i t) =
      P.componentTwoCenterCutPoint i t := rfl

theorem componentTwoCenterLiftedCutSet_isCompact
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    IsCompact (P.componentTwoCenterLiftedCutSet i) := by
  letI : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  exact isCompact_range (P.componentTwoCenterLiftedCutPoint_continuous i)

theorem componentTwoCenterLiftedCutSet_nonempty
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    (P.componentTwoCenterLiftedCutSet i).Nonempty :=
  ⟨P.componentTwoCenterLiftedCutPoint i 0, ⟨0, rfl⟩⟩

private theorem componentTwoCenterLiftedCutSet_smul_disjoint
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (γ : (X i).deckGroup) (hγ : γ ≠ 1) :
    Disjoint (P.componentTwoCenterLiftedCutSet i)
      ((fun z : ℍ => γ • z) '' P.componentTwoCenterLiftedCutSet i) := by
  rw [Set.disjoint_left]
  intro z hzK hzγK
  change z ∈ range (P.componentTwoCenterLiftedCutPoint i) at hzK
  change z ∈ ((fun z : ℍ => γ • z) '' range (P.componentTwoCenterLiftedCutPoint i)) at hzγK
  obtain ⟨s, hsz⟩ := hzK
  obtain ⟨w, hwK, hzw⟩ := hzγK
  obtain ⟨t, hwt⟩ := hwK
  rw [← hsz] at hzw
  rw [← hwt] at hzw
  have hquot : P.componentTwoCenterCutPoint i s = P.componentTwoCenterCutPoint i t := by
    apply Quotient.sound
    exact MulAction.orbitRel_apply.mpr ⟨γ, hzw⟩
  have hst := P.componentTwoCenterCutPoint_injective i hquot
  have hfix : γ • P.componentTwoCenterLiftedCutPoint i t =
      P.componentTwoCenterLiftedCutPoint i t := by
    rw [hst] at hzw
    exact hzw
  exact hγ ((X i).free γ _ hfix)


/-- The metric neighborhood of radius `ε` about the actual lifted cut. -/
def componentTwoCenterLiftedCutTube
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (ε : ℝ) : Set ℍ :=
  {z | Metric.infDist z (P.componentTwoCenterLiftedCutSet i) < ε}

/-- A positive-width neighborhood of the actual lifted cut is disjoint from all
nonidentity deck translates, so it descends injectively to the quotient. -/
theorem exists_componentTwoCenterLiftedCutTube_disjoint_translates
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ γ : (X i).deckGroup, γ ≠ 1 →
      Disjoint ((fun z : ℍ => γ • z) '' P.componentTwoCenterLiftedCutTube i ε)
        (P.componentTwoCenterLiftedCutTube i ε) := by
  exact (X i).exists_compact_deck_tube_disjoint_translates
    (P.componentTwoCenterLiftedCutSet i) (P.componentTwoCenterLiftedCutSet_isCompact i)
    (P.componentTwoCenterLiftedCutSet_nonempty i)
    (P.componentTwoCenterLiftedCutSet_smul_disjoint i)

#print axioms componentTwoCenterLiftedCutSet_isCompact
#print axioms exists_componentTwoCenterLiftedCutTube_disjoint_translates

end

end SystolicGrowth.ExerciseGluingPreparation
