module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainCurvatureMeasure
public import Geometry.HyperbolicBallExactVolume
public import Geometry.QuotientAreaLocalIsometry
public import Geometry.ExerciseGeometryFoundation

@[expose] public section

/-!
# Exact total area and candidate curvature of the original retained chain

Every deleted set is the prescribed original orbit ball. Natural quotient
area on its actual embedded projection sheet equals hyperbolic ball area.
Full-orbit separation makes the left and right deletions disjoint. The
original endpoint predicates then count exactly two deletions per actual
chain edge. Combining this computation with the proved original genus area
formula gives the native negative-area/negative-seam candidate its exact
Gauss--Bonnet total. Intrinsic bounded integral curvature identification is
not asserted by this arithmetic conclusion.
-/

open MeasureTheory Set Metric UpperHalfPlane
open scoped ENNReal UpperHalfPlane

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

local instance componentQuotientArea_isFinite
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    IsFiniteMeasure ((X i).quotientAreaMeasure (P.centers i).1) :=
  ⟨lt_top_iff_ne_top.mpr ((X i).quotientAreaMeasure_univ_ne_top _)⟩

/-- **Math.** Each prescribed deleted orbit ball has its exact original hyperbolic area. -/
theorem componentOrbitBall_area
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (o : ℍ) :
    (X i).quotientAreaMeasure (P.centers i).1 ((X i).orbitBall o (gluingRadius C g)) =
      ENNReal.ofReal (2 * Real.pi * (Real.cosh (gluingRadius C g) - 1)) := by
  have hsmall : 2 * gluingRadius C g ≤ (X i).systole := by
    linarith [P.twice_outer_lt_systole i, P.radius_lt_embeddedRadius]
  rw [ClosedHyperbolicSurface.orbitBall,
    (X i).quotientAreaMeasure_image_of_subset_ball (P.centers i).1 o (gluingRadius C g)
      hsmall measurableSet_ball subset_rfl,
    volume_hyperbolic_ball_exact o P.radius_pos]

theorem componentOrbitBall_area_real
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (o : ℍ) :
    ((X i).quotientAreaMeasure (P.centers i).1).real
      ((X i).orbitBall o (gluingRadius C g)) =
        2 * Real.pi * (Real.cosh (gluingRadius C g) - 1) := by
  rw [measureReal_def, P.componentOrbitBall_area i o, ENNReal.toReal_ofReal]
  exact mul_nonneg Real.two_pi_pos.le (sub_nonneg.mpr (Real.one_le_cosh _))

/-- **Math.** The two actual orbit disks, rather than merely their selected lifts, are disjoint. -/
theorem componentInnerOrbitBalls_disjoint
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Disjoint ((X i).orbitBall (P.centers i).1 (gluingRadius C g))
      ((X i).orbitBall (P.centers i).2 (gluingRadius C g)) :=
  (X i).disjoint_innerOrbitBalls _ _ _ _ P.radius_lt_embeddedRadius
    (P.separated_outer_add_inner i)

/-- **Math.** Exact original deleted area retains the literal first/last index predicates. -/
theorem componentDeletedArea_real
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    ((X i).quotientAreaMeasure (P.centers i).1).real
      ((X i).punctureDeletedSet (P.centers i).1 (P.centers i).2 (gluingRadius C g) i) =
      (if 0 < i.val then 2 * Real.pi * (Real.cosh (gluingRadius C g) - 1) else 0) +
        (if i.val + 1 < n then 2 * Real.pi * (Real.cosh (gluingRadius C g) - 1) else 0) := by
  unfold ClosedHyperbolicSurface.punctureDeletedSet
  split_ifs with hleft hright
  · rw [measureReal_union (P.componentInnerOrbitBalls_disjoint i)
      ((X i).measurableSet_orbitBall _ _),
      P.componentOrbitBall_area_real i _, P.componentOrbitBall_area_real i _]
  · simp only [union_empty, P.componentOrbitBall_area_real, add_zero]
  · simp only [empty_union, P.componentOrbitBall_area_real, zero_add]
  · simp

/-- **Math.** The retained area is original closed-surface area minus the actual
disjoint deletions, with no removed-area input assumed. -/
theorem retainedComponentAreaMeasure_real_univ
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    (P.retainedComponentAreaMeasure i).real univ =
      4 * Real.pi * ((genera i : ℝ) - 1) -
        ((if 0 < i.val then 2 * Real.pi * (Real.cosh (gluingRadius C g) - 1) else 0) +
          (if i.val + 1 < n then 2 * Real.pi * (Real.cosh (gluingRadius C g) - 1) else 0)) := by
  have hdeleted : MeasurableSet ((X i).punctureDeletedSet
      (P.centers i).1 (P.centers i).2 (gluingRadius C g) i) := by
    simpa only [ClosedHyperbolicSurface.puncturedComponentSet, compl_compl] using
      (P.componentRetainedSet_measurable i).compl
  have hsplit := measureReal_add_measureReal_compl
    (μ := (X i).quotientAreaMeasure (P.centers i).1) hdeleted
  have htotal : ((X i).quotientAreaMeasure (P.centers i).1).real univ =
      4 * Real.pi * ((genera i : ℝ) - 1) := by
    rw [measureReal_def, (X i).quotientAreaMeasure_univ_eq_covolume,
      exercise_covolume_eq_genus_area (P.component_genus i), ENNReal.toReal_ofReal]
    have hi : (2 : ℝ) ≤ genera i := by exact_mod_cast P.component_genus i
    exact mul_nonneg (by positivity) (by linarith)
  rw [P.componentDeletedArea_real i, htotal] at hsplit
  rw [measureReal_def, P.retainedComponentAreaMeasure_univ i]
  change ((X i).quotientAreaMeasure (P.centers i).1).real
    ((X i).punctureDeletedSet (P.centers i).1 (P.centers i).2 (gluingRadius C g) i)ᶜ = _
  linarith

theorem gluedComponentAreaMeasure_real_univ
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    (P.gluedComponentAreaMeasure i).real univ =
      4 * Real.pi * ((genera i : ℝ) - 1) -
        ((if 0 < i.val then 2 * Real.pi * (Real.cosh (gluingRadius C g) - 1) else 0) +
          (if i.val + 1 < n then 2 * Real.pi * (Real.cosh (gluingRadius C g) - 1) else 0)) := by
  rw [measureReal_def, gluedComponentAreaMeasure,
    Measure.map_apply (P.componentInclude_measurable i) MeasurableSet.univ, preimage_univ]
  exact P.retainedComponentAreaMeasure_real_univ i

private theorem sum_incoming_deleted_area (n : ℕ) (A : ℝ) :
    (∑ i : Fin n, if 0 < i.val then A else 0) = ((n - 1 : ℕ) : ℝ) * A := by
  cases n with
  | zero => simp
  | succ m =>
    rw [Fin.sum_univ_succ]
    simp

private theorem sum_outgoing_deleted_area (n : ℕ) (A : ℝ) :
    (∑ i : Fin n, if i.val + 1 < n then A else 0) = ((n - 1 : ℕ) : ℝ) * A := by
  cases n with
  | zero => simp
  | succ m =>
    have hi (i : Fin m) : i.val + 1 < m + 1 := Nat.succ_lt_succ i.isLt
    rw [Fin.sum_univ_castSucc]
    simp [hi]

/-- **Math.** Exact native retained area after the original endpoint/interior deletion
bookkeeping. The unchanged sum-genus equation is the only genus-sum input. -/
theorem gluedChainAreaMeasure_real_univ
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (hsum : (∑ i, genera i) = g) :
    P.gluedChainAreaMeasure.real univ =
      4 * Real.pi * ((g : ℝ) - 1) -
        4 * Real.pi * ((n - 1 : ℕ) : ℝ) * Real.cosh (gluingRadius C g) := by
  have hcast : (∑ i : Fin n, (genera i : ℝ)) = (g : ℝ) := by exact_mod_cast hsum
  have hsurfaces : (∑ i : Fin n, 4 * Real.pi * ((genera i : ℝ) - 1)) =
      4 * Real.pi * ((g : ℝ) - n) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hcast]
    simp
  have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  rw [measureReal_def, gluedChainAreaMeasure]
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  rw [ENNReal.toReal_sum (fun i _ => measure_ne_top (P.gluedComponentAreaMeasure i) univ)]
  change (∑ i : Fin n, (P.gluedComponentAreaMeasure i).real univ) = _
  simp_rw [P.gluedComponentAreaMeasure_real_univ]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hsurfaces,
    sum_incoming_deleted_area, sum_outgoing_deleted_area, hsub]
  ring

/-- **Math.** Exact retained mass also as an extended nonnegative-real measure value. -/
theorem gluedChainAreaMeasure_univ
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (hsum : (∑ i, genera i) = g) :
    P.gluedChainAreaMeasure univ =
      ENNReal.ofReal (4 * Real.pi * ((g : ℝ) - 1) -
        4 * Real.pi * ((n - 1 : ℕ) : ℝ) * Real.cosh (gluingRadius C g)) := by
  rw [← P.gluedChainAreaMeasure_real_univ hn hsum, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- **Math.** Actual removed disk areas and actual seam masses cancel exactly in the
constructed native magnitude; there is no area-cancellation hypothesis. -/
theorem gluedChainCurvatureMagnitude_real_univ
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (hsum : (∑ i, genera i) = g) :
    P.gluedChainCurvatureMagnitude.real univ = 4 * Real.pi * ((g : ℝ) - 1) := by
  rw [measureReal_def, P.gluedChainCurvatureMagnitude_univ,
    ENNReal.toReal_add (measure_ne_top _ _) (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (show 0 ≤ 4 * Real.pi * Real.cosh (gluingRadius C g) by positivity)]
  change P.gluedChainAreaMeasure.real univ +
    ((n - 1 : ℕ) : ℝ) * (4 * Real.pi * Real.cosh (gluingRadius C g)) = _
  rw [P.gluedChainAreaMeasure_real_univ hn hsum]
  ring

theorem gluedChainCurvatureMagnitude_univ_eq_genus_area
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (hsum : (∑ i, genera i) = g) :
    P.gluedChainCurvatureMagnitude univ = ENNReal.ofReal (4 * Real.pi * ((g : ℝ) - 1)) := by
  rw [← P.gluedChainCurvatureMagnitude_real_univ hn hsum, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- **Math.** The constructed nonpositive native candidate has the exact signed
Gauss--Bonnet total for the original marked chain genus. -/
theorem gluedChainNegativeCurvatureMeasure_univ
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (hsum : (∑ i, genera i) = g) :
    P.gluedChainNegativeCurvatureMeasure univ = -4 * Real.pi * ((g : ℝ) - 1) := by
  rw [gluedChainNegativeCurvatureMeasure, neg_apply,
    Measure.toSignedMeasure_apply_measurable MeasurableSet.univ,
    P.gluedChainCurvatureMagnitude_real_univ hn hsum]
  ring

/-- **Math.** Exact total variation is now the genus area, on the original carrier. -/
theorem gluedChainNegativeCurvatureMeasure_totalVariation_univ
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (hsum : (∑ i, genera i) = g) :
    P.gluedChainNegativeCurvatureMeasure.totalVariation univ =
      ENNReal.ofReal (4 * Real.pi * ((g : ℝ) - 1)) := by
  rw [P.gluedChainNegativeCurvatureMeasure_totalVariation]
  exact P.gluedChainCurvatureMagnitude_univ_eq_genus_area hn hsum

#print axioms componentOrbitBall_area
#print axioms retainedComponentAreaMeasure_real_univ
#print axioms gluedChainAreaMeasure_real_univ
#print axioms gluedChainNegativeCurvatureMeasure_univ
#print axioms gluedChainNegativeCurvatureMeasure_totalVariation_univ

end

end SystolicGrowth.ExerciseGluingPreparation
