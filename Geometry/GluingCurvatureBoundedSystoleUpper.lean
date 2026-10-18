module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCurvatureBoundedSystole
public import Geometry.GluingChainBoundedCurvatureCurvature
public import Geometry.SystoleDiskAreaBound
public import Geometry.GluingCurvatureBoundedDiskArea

@[expose] public section

/-!
# Finite systole of the actual curvature-bounded glued metric

The actual global area budget and actual half-systole disk comparison give
the uniform systolic upper bound. Finiteness of the extended-valued fiber
infimum is a consequence, not an additional geometric assumption.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

private theorem two_le_total_genus
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (hsum : (∑ i, genera i) = g) : 2 ≤ g := by
  let i : Fin n := ⟨0, by omega⟩
  calc
    2 ≤ genera i := P.component_genus i
    _ ≤ ∑ j, genera j := Finset.single_le_sum (fun j _ => Nat.zero_le (genera j))
      (Finset.mem_univ i)
    _ = g := hsum

/-- **Math.** The total actual ODE area has the extended-real genus budget;
the conversion from real area uses the constructed finite area measure. -/
theorem gluedCurvatureBoundedAreaMeasure_univ_le
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (hsum : (∑ i, genera i) = g) :
    P.gluedCurvatureBoundedAreaMeasure univ ≤
      ENNReal.ofReal (4 * Real.pi * ((g : ℝ) - 1)) := by
  calc
    P.gluedCurvatureBoundedAreaMeasure univ =
        ENNReal.ofReal (P.gluedCurvatureBoundedAreaMeasure.real univ) := by
      exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (4 * Real.pi * ((g : ℝ) - 1)) :=
      ENNReal.ofReal_le_ofReal (P.gluedCurvatureBoundedAreaMeasure_real_univ_le hn hsum)

/-- **Math.** The actual extended-valued fiber systole has the uniform genus
upper bound. The disk estimate is instantiated at every finite test length
below the actual infimum, so finiteness is not assumed along the way. -/
theorem gluedCurvatureBoundedFiberSystole_le_arcosh
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) :
    P.gluedCurvatureBoundedFiberSystole x ≤
      ENNReal.ofReal (2 * Real.arcosh (2 * (g : ℝ) - 1)) := by
  have hg := two_le_total_genus P hn hsum
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hbudget0 : 0 ≤ 4 * Real.pi * ((g : ℝ) - 1) :=
    mul_nonneg (by positivity) (by linarith)
  obtain ⟨q, _⟩ := P.gluedUniversalCoverProjection_surjective x x
  apply systoleENNReal_le_arcosh_of_open_disk_area_bounds hg
  intro L _hL hL r hr0 hrL
  have hgap := (P.le_gluedCurvatureBoundedFiberSystole_iff x L).mp hL
  have hball := P.gluedCurvatureBounded_ball_area_lower_bound_of_fiber_gap
    x q r L hr0.le hgap (by linarith)
  have htotal := hball.trans (measure_mono (subset_univ _))
  have harea := htotal.trans (P.gluedCurvatureBoundedAreaMeasure_univ_le hn hsum)
  exact (ENNReal.ofReal_le_ofReal_iff hbudget0).mp harea

/-- **Math.** The actual smooth fiber systole is finite as a consequence of
the constructed disk-area comparison and genus budget. -/
theorem gluedCurvatureBoundedFiberSystole_lt_top
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) :
    P.gluedCurvatureBoundedFiberSystole x < ⊤ :=
  (P.gluedCurvatureBoundedFiberSystole_le_arcosh x hn hsum).trans_lt ENNReal.ofReal_lt_top

/-- **Math.** The now genuinely finite systole has the same exact real
upper bound used for the hyperbolic replacement argument. -/
theorem gluedCurvatureBoundedFiberSystole_toReal_le_arcosh
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) :
    (P.gluedCurvatureBoundedFiberSystole x).toReal ≤
      2 * Real.arcosh (2 * (g : ℝ) - 1) := by
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast two_le_total_genus P hn hsum
  have hupper0 : 0 ≤ 2 * Real.arcosh (2 * (g : ℝ) - 1) :=
    mul_nonneg (by norm_num) (Real.arcosh_nonneg (by linarith))
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (P.gluedCurvatureBoundedFiberSystole_le_arcosh x hn hsum)
  simpa only [ENNReal.toReal_ofReal hupper0] using h

/-- **Math.** The prescribed target remains a lower bound for the actual
real systole; the finite upper bound justifies conversion from `ENNReal`. -/
theorem target_le_gluedCurvatureBoundedFiberSystole_toReal
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) :
    targetSystole C g ≤ (P.gluedCurvatureBoundedFiberSystole x).toReal := by
  have h := ENNReal.toReal_mono
    (P.gluedCurvatureBoundedFiberSystole_lt_top x hn hsum).ne
    (P.target_le_gluedCurvatureBoundedFiberSystole x)
  simpa only [ENNReal.toReal_ofReal P.target_pos.le] using h

#print axioms gluedCurvatureBoundedAreaMeasure_univ_le
#print axioms gluedCurvatureBoundedFiberSystole_le_arcosh
#print axioms gluedCurvatureBoundedFiberSystole_lt_top
#print axioms gluedCurvatureBoundedFiberSystole_toReal_le_arcosh
#print axioms target_le_gluedCurvatureBoundedFiberSystole_toReal

end
end SystolicGrowth.ExerciseGluingPreparation
