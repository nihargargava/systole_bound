module

public import Geometry.QuotientAreaMeasure

@[expose] public section

/-!
# Orbit balls and separated centers on a closed quotient

The orbit ball is the actual image of an upstairs metric ball. Dirichlet
minimization proves its quotient area is at most that upstairs ball's area.
If this is smaller than the covolume, a complementary quotient point gives a
lift whose entire orbit stays outside the ball.
-/

open MeasureTheory UpperHalfPlane
open scoped ENNReal MatrixGroups Pointwise UpperHalfPlane

namespace SystolicGrowth

namespace ClosedHyperbolicSurface

/-- The quotient image of the actual upstairs ball, not a postulated
downstairs distance or area function. -/
def orbitBall {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) (D : ℝ) :
    Set X.Carrier :=
  (Quotient.mk (MulAction.orbitRel X.deckGroup ℍ)) '' Metric.ball o D

/-- A lifted point lies in the orbit ball exactly when one of its translates
lies in the original upstairs ball. -/
theorem mem_orbitBall_mk_iff {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o z : ℍ) (D : ℝ) :
    Quotient.mk (MulAction.orbitRel X.deckGroup ℍ) z ∈ X.orbitBall o D ↔
      ∃ γ : X.deckGroup, γ • z ∈ Metric.ball o D := by
  constructor
  · rintro ⟨v, hv, hvz⟩
    have hrel : MulAction.orbitRel X.deckGroup ℍ v z := Quotient.exact hvz
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hrel)
    exact ⟨γ, hγ ▸ hv⟩
  · rintro ⟨γ, hγ⟩
    refine ⟨γ • z, hγ, ?_⟩
    exact Quotient.sound (MulAction.orbitRel_apply.mpr
      (MulAction.mem_orbit_iff.mpr ⟨γ, rfl⟩))

/-- The saturated upstairs preimage is the union of translated ball preimages. -/
theorem orbitBall_preimage {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) (D : ℝ) :
    (Quotient.mk (MulAction.orbitRel X.deckGroup ℍ)) ⁻¹' X.orbitBall o D =
      ⋃ γ : X.deckGroup, (fun z : ℍ => γ • z) ⁻¹' Metric.ball o D := by
  ext z
  simpa only [Set.mem_preimage, Set.mem_iUnion] using X.mem_orbitBall_mk_iff o z D

/-- Orbit balls are measurable for the actual quotient measurable space. -/
theorem measurableSet_orbitBall {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (D : ℝ) : MeasurableSet (X.orbitBall o D) := by
  apply measurableSet_quotient.mpr
  change MeasurableSet
    ((Quotient.mk (MulAction.orbitRel X.deckGroup ℍ)) ⁻¹' X.orbitBall o D)
  rw [X.orbitBall_preimage]
  apply IsOpen.measurableSet
  exact isOpen_iUnion fun γ => Metric.isOpen_ball.preimage (continuous_const_smul γ)

/-- A representative chosen in the center's Dirichlet domain is no farther
from the center than any of its translates. -/
theorem dirichlet_mem_orbitBall_implies_mem_ball {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o z : ℍ) (D : ℝ)
    (hz : z ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)
    (hball : Quotient.mk (MulAction.orbitRel X.deckGroup ℍ) z ∈ X.orbitBall o D) :
    z ∈ Metric.ball o D := by
  obtain ⟨γ, hγ⟩ := (X.mem_orbitBall_mk_iff o z D).mp hball
  have hdir := (Vendored.RiemannDynamics.mem_dirichletDomain.mp hz) γ⁻¹
  have hrewrite : dist z ((γ⁻¹ : X.deckGroup) • o) = dist (γ • z) o := by
    rw [← dist_smul γ z ((γ⁻¹ : X.deckGroup) • o)]
    simp
  rw [hrewrite] at hdir
  exact lt_of_le_of_lt hdir hγ

/-- The quotient orbit ball has area at most the genuine upstairs ball,
regardless of which center represents the quotient area measure. -/
theorem quotientAreaMeasure_orbitBall_le {g : ℕ} (X : ClosedHyperbolicSurface g)
    (measureCenter o : ℍ) (D : ℝ) :
    X.quotientAreaMeasure measureCenter (X.orbitBall o D) ≤ volume (Metric.ball o D) := by
  rw [X.quotientAreaMeasure_center_independent measureCenter o]
  unfold quotientAreaMeasure
  letI : Setoid ℍ := MulAction.orbitRel X.deckGroup ℍ
  change ((volume.restrict (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)).map
    (Quotient.mk' : ℍ → X.Carrier)) (X.orbitBall o D) ≤ _
  rw [Measure.map_apply (measurable_quotient_mk' (s := MulAction.orbitRel X.deckGroup ℍ))
    (X.measurableSet_orbitBall o D)]
  rw [Measure.restrict_apply
    ((measurable_quotient_mk' (s := MulAction.orbitRel X.deckGroup ℍ))
      (X.measurableSet_orbitBall o D))]
  apply measure_mono
  intro z hz
  exact X.dirichlet_mem_orbitBall_implies_mem_ball o z D hz.2 hz.1

/-- When an upstairs ball has smaller area than the quotient, the quotient
contains an actual point outside its orbit image. -/
theorem exists_not_mem_orbitBall_of_volume_lt_covolume {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) (D : ℝ)
    (hvolume : volume (Metric.ball o D) < covolume X.deckGroup ℍ volume) :
    ∃ q : X.Carrier, q ∉ X.orbitBall o D := by
  have hlt : X.quotientAreaMeasure o (X.orbitBall o D) <
      X.quotientAreaMeasure o Set.univ := by
    rw [X.quotientAreaMeasure_univ_eq_covolume]
    exact lt_of_le_of_lt (X.quotientAreaMeasure_orbitBall_le o o D) hvolume
  by_contra hnone
  have hall : ∀ q : X.Carrier, q ∈ X.orbitBall o D := by
    simpa only [not_exists, not_not] using hnone
  have heq : X.orbitBall o D = Set.univ := Set.eq_univ_iff_forall.mpr hall
  rw [heq] at hlt
  exact (lt_irrefl _) hlt

/-- Strict area comparison produces a lifted second center whose entire deck
orbit is at least `D` from the first center. No quotient distance is assumed. -/
theorem exists_orbit_separated_center_of_volume_lt_covolume {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) (D : ℝ)
    (hvolume : volume (Metric.ball o D) < covolume X.deckGroup ℍ volume) :
    ∃ z : ℍ, ∀ γ : X.deckGroup, D ≤ dist o (γ • z) := by
  obtain ⟨q, hq⟩ := X.exists_not_mem_orbitBall_of_volume_lt_covolume o D hvolume
  obtain ⟨z, rfl⟩ := Quotient.exists_rep q
  refine ⟨z, ?_⟩
  intro γ
  by_contra hdist
  apply hq
  apply (X.mem_orbitBall_mk_iff o z D).mpr
  refine ⟨γ, ?_⟩
  simpa only [Metric.mem_ball, dist_comm] using (not_le.mp hdist)

end ClosedHyperbolicSurface

#print axioms ClosedHyperbolicSurface.measurableSet_orbitBall
#print axioms ClosedHyperbolicSurface.quotientAreaMeasure_orbitBall_le
#print axioms ClosedHyperbolicSurface.exists_orbit_separated_center_of_volume_lt_covolume

end SystolicGrowth
