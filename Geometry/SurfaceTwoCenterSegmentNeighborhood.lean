module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceTwoCenterCutSpine
public import Geometry.SurfaceDeckCompactTube

@[expose] public section

/-!
# An embedded neighborhood containing both actual puncture centers

The full minimizing center segment, not only the retained cut, has injective
projection. Compact deck separation therefore gives an actual open surface
neighborhood containing both centers. It supports the local twice-punctured
disk route to the original component's peripheral presentation.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane unitInterval

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The literal lift of the entire minimizing center segment. -/
def componentLiftedCenterGeodPoint
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (t : I) : ℍ :=
  Vendored.RiemannDynamics.geodInterp (P.centers i).1
    (P.componentCenterClosestDeck i • (P.centers i).2) t

/-- The actual compact lifted segment, including both centers. -/
def componentLiftedCenterGeodSet
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) : Set ℍ :=
  range (P.componentLiftedCenterGeodPoint i)

@[simp]
theorem componentLiftedCenterGeodPoint_project
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (t : I) :
    (X i).orbitProjection (P.componentLiftedCenterGeodPoint i t) =
      P.componentCenterGeodPoint i t := rfl

theorem componentLiftedCenterGeodPoint_continuous
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Continuous (P.componentLiftedCenterGeodPoint i) :=
  Vendored.RiemannDynamics.continuous_geodInterp.comp
    (continuous_const.prodMk (continuous_const.prodMk continuous_subtype_val))

theorem componentLiftedCenterGeodSet_isCompact
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    IsCompact (P.componentLiftedCenterGeodSet i) := by
  letI : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  exact isCompact_range (P.componentLiftedCenterGeodPoint_continuous i)

theorem componentLiftedCenterGeodSet_nonempty
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    (P.componentLiftedCenterGeodSet i).Nonempty :=
  ⟨P.componentLiftedCenterGeodPoint i 0, ⟨0, rfl⟩⟩

/-- Exact quotient subsegment distances make the entire center segment injective. -/
theorem componentCenterGeodPoint_injective
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Function.Injective (P.componentCenterGeodPoint i) := by
  intro s t hst
  have hdpos : 0 < dist
      (Quotient.mk'' (P.centers i).1 : (X i).Carrier) (Quotient.mk'' (P.centers i).2) := by
    linarith [P.carrier_centers_outer_add_inner_le_dist i, P.radius_pos,
      P.radius_lt_embeddedRadius]
  have hdist := P.componentCenterGeodPoint_dist i s t
  rw [hst, dist_self] at hdist
  have habs : |(s : ℝ) - t| = 0 :=
    (mul_eq_zero.mp hdist.symm).resolve_right hdpos.ne'
  exact Subtype.ext (sub_eq_zero.mp (abs_eq_zero.mp habs))

/-- No nontrivial deck translate meets the full lifted center segment. -/
theorem componentLiftedCenterGeodSet_smul_disjoint
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (γ : (X i).deckGroup) (hγ : γ ≠ 1) :
    Disjoint (P.componentLiftedCenterGeodSet i)
      ((fun z : ℍ => γ • z) '' P.componentLiftedCenterGeodSet i) := by
  rw [Set.disjoint_left]
  intro z hzK hzγK
  obtain ⟨s, hsz⟩ := hzK
  obtain ⟨w, hwK, hzw⟩ := hzγK
  obtain ⟨t, hwt⟩ := hwK
  rw [← hsz, ← hwt] at hzw
  have hquot : P.componentCenterGeodPoint i s = P.componentCenterGeodPoint i t := by
    apply Quotient.sound
    exact MulAction.orbitRel_apply.mpr ⟨γ, hzw⟩
  have hst := P.componentCenterGeodPoint_injective i hquot
  have hfix : γ • P.componentLiftedCenterGeodPoint i t =
      P.componentLiftedCenterGeodPoint i t := by
    rw [hst] at hzw
    exact hzw
  exact hγ ((X i).free γ _ hfix)

/-- The metric neighborhood of the entire actual lifted center segment. -/
def componentLiftedCenterGeodTube
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (ε : ℝ) : Set ℍ :=
  {z | Metric.infDist z (P.componentLiftedCenterGeodSet i) < ε}

/-- A full center-segment tube is uniformly disjoint from its nontrivial translates. -/
theorem exists_componentLiftedCenterGeodTube_disjoint_translates
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ γ : (X i).deckGroup, γ ≠ 1 →
      Disjoint ((fun z : ℍ => γ • z) '' P.componentLiftedCenterGeodTube i ε)
        (P.componentLiftedCenterGeodTube i ε) :=
  (X i).exists_compact_deck_tube_disjoint_translates
    (P.componentLiftedCenterGeodSet i) (P.componentLiftedCenterGeodSet_isCompact i)
    (P.componentLiftedCenterGeodSet_nonempty i)
    (P.componentLiftedCenterGeodSet_smul_disjoint i)

/-- The original quotient map restricted to the entire center-segment tube. -/
def componentLiftedCenterGeodTubeProjection
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (ε : ℝ) :
    P.componentLiftedCenterGeodTube i ε → (X i).Carrier :=
  fun z => (X i).orbitProjection z.1

theorem componentLiftedCenterGeodTubeProjection_isOpenEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (ε : ℝ)
    (hdisj : ∀ γ : (X i).deckGroup, γ ≠ 1 →
      Disjoint ((fun z : ℍ => γ • z) '' P.componentLiftedCenterGeodTube i ε)
        (P.componentLiftedCenterGeodTube i ε)) :
    Topology.IsOpenEmbedding (P.componentLiftedCenterGeodTubeProjection i ε) := by
  apply (X i).orbitProjection_restrict_isOpenEmbedding _ _ hdisj
  exact isOpen_Iio.preimage (Metric.continuous_infDist_pt _)

/-- Every point of the full physical segment lies in the projected positive tube. -/
theorem componentCenterGeodPoint_mem_liftedCenterGeodTubeProjection_range
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (ε : ℝ)
    (hε : 0 < ε) (t : I) :
    P.componentCenterGeodPoint i t ∈
      range (P.componentLiftedCenterGeodTubeProjection i ε) := by
  refine ⟨⟨P.componentLiftedCenterGeodPoint i t, ?_⟩, rfl⟩
  change Metric.infDist _ (P.componentLiftedCenterGeodSet i) < ε
  rw [Metric.infDist_zero_of_mem (show P.componentLiftedCenterGeodPoint i t ∈
    P.componentLiftedCenterGeodSet i from ⟨t, rfl⟩)]
  exact hε

/-- Both actual puncture centers belong to the same genuine open tube image. -/
theorem componentCenters_mem_liftedCenterGeodTubeProjection_range
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (ε : ℝ)
    (hε : 0 < ε) :
    (Quotient.mk'' (P.centers i).1 : (X i).Carrier) ∈
        range (P.componentLiftedCenterGeodTubeProjection i ε) ∧
      (Quotient.mk'' (P.centers i).2 : (X i).Carrier) ∈
        range (P.componentLiftedCenterGeodTubeProjection i ε) := by
  simpa only [P.componentCenterGeodPoint_zero, P.componentCenterGeodPoint_one] using
    And.intro
      (P.componentCenterGeodPoint_mem_liftedCenterGeodTubeProjection_range i ε hε 0)
      (P.componentCenterGeodPoint_mem_liftedCenterGeodTubeProjection_range i ε hε 1)

#print axioms componentCenterGeodPoint_injective
#print axioms exists_componentLiftedCenterGeodTube_disjoint_translates
#print axioms componentLiftedCenterGeodTubeProjection_isOpenEmbedding
#print axioms componentCenters_mem_liftedCenterGeodTubeProjection_range

end

end SystolicGrowth.ExerciseGluingPreparation
