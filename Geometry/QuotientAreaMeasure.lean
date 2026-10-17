module

public import Geometry.RiemannDynamicsBridge
public import Geometry.HyperbolicBallVolume

@[expose] public section

/-!
# Hyperbolic area on a closed-surface quotient

The area measure downstairs is obtained by restricting hyperbolic area to a
Dirichlet domain and projecting to the orbit quotient. The choice of center
does not affect this measure. Its total mass is the deck-group covolume; the
remaining genus-dependent Gauss--Bonnet formula is not asserted here.
-/

open MeasureTheory UpperHalfPlane
open scoped ENNReal MatrixGroups Pointwise UpperHalfPlane

namespace SystolicGrowth

namespace ClosedHyperbolicSurface

/-- Area on the orbit quotient, represented using a Dirichlet domain centered
at `o`. -/
noncomputable def quotientAreaMeasure {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) : Measure X.Carrier :=
  (volume.restrict (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)).map
    (Quotient.mk (MulAction.orbitRel X.deckGroup ℍ))

/-- The quotient area does not depend on the Dirichlet center. -/
theorem quotientAreaMeasure_center_independent {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o₁ o₂ : ℍ) :
    X.quotientAreaMeasure o₁ = X.quotientAreaMeasure o₂ := by
  letI : Countable (SurfaceGroup g) := by
    change Countable (Quotient (QuotientGroup.leftRel
      (Subgroup.normalClosure ({surfaceRelator g} : Set (FreeGroup (SurfaceGenerator g))))))
    infer_instance
  letI : Countable X.deckGroup :=
    (Equiv.countable_iff X.marking.toEquiv).mpr inferInstance
  letI : SMulInvariantMeasure X.deckGroup ℍ volume :=
    ⟨fun γ s hs => SMulInvariantMeasure.measure_preimage_smul
      (M := GL (Fin 2) ℝ)
      (Matrix.SpecialLinearGroup.mapGL ℝ
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)) hs⟩
  exact (X.dirichletDomain_isFundamentalDomain o₁).quotientMeasure_eq volume
    (X.dirichletDomain_isFundamentalDomain o₂)

/-- The total area of the quotient equals the hyperbolic covolume of its deck
group. -/
theorem quotientAreaMeasure_univ_eq_covolume {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) :
    X.quotientAreaMeasure o Set.univ = covolume X.deckGroup ℍ volume := by
  rw [X.covolume_eq_dirichletDomain_volume o]
  unfold quotientAreaMeasure
  letI : Setoid ℍ := MulAction.orbitRel X.deckGroup ℍ
  change ((volume.restrict
    (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)).map
      (Quotient.mk' : ℍ → X.Carrier)) Set.univ = _
  rw [Measure.map_apply (measurable_quotient_mk' (s := MulAction.orbitRel X.deckGroup ℍ))
    MeasurableSet.univ]
  simp

/-- In particular, the quotient area measure is finite. -/
theorem quotientAreaMeasure_univ_ne_top {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) :
    X.quotientAreaMeasure o Set.univ ≠ ∞ := by
  rw [X.quotientAreaMeasure_univ_eq_covolume]
  exact X.covolume_ne_top

/-- The deck-group covolume is nonzero: an almost-everywhere fundamental
domain cannot be null in the nonzero hyperbolic area measure. -/
theorem covolume_ne_zero {g : ℕ} (X : ClosedHyperbolicSurface g) :
    covolume X.deckGroup ℍ volume ≠ 0 := by
  letI : Countable (SurfaceGroup g) := by
    change Countable (Quotient (QuotientGroup.leftRel
      (Subgroup.normalClosure ({surfaceRelator g} : Set (FreeGroup (SurfaceGenerator g))))))
    infer_instance
  letI : Countable X.deckGroup :=
    (Equiv.countable_iff X.marking.toEquiv).mpr inferInstance
  letI : SMulInvariantMeasure X.deckGroup ℍ volume :=
    ⟨fun γ s hs => SMulInvariantMeasure.measure_preimage_smul
      (M := GL (Fin 2) ℝ)
      (Matrix.SpecialLinearGroup.mapGL ℝ
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)) hs⟩
  rw [X.covolume_eq_dirichletDomain_volume (I : ℍ)]
  apply (X.dirichletDomain_isFundamentalDomain I).measure_ne_zero
  intro hzero
  have hlog : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    exact h
  have hball : (0 : ℝ≥0∞) < volume (Metric.ball (I : ℍ) 1) := by
    have hbound := ofReal_exp_div_sixteen_le_volume_ball (I : ℍ) hlog
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) hbound
  have huniv : volume (Set.univ : Set ℍ) ≠ 0 := by
    exact ne_of_gt (hball.trans_le (measure_mono (Set.subset_univ _)))
  exact huniv (by simp [hzero])

/-- The quotient carries a finite measure of strictly positive total mass. -/
theorem quotientAreaMeasure_univ_pos {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) :
    0 < X.quotientAreaMeasure o Set.univ := by
  rw [X.quotientAreaMeasure_univ_eq_covolume]
  exact pos_iff_ne_zero.mpr X.covolume_ne_zero

end ClosedHyperbolicSurface

end SystolicGrowth
