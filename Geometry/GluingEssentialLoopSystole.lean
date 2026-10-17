module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingEssentialLoopPeriodic

@[expose] public section

/-!
# The native systole bound for every continuous essential loop

Infinite variation already pays the target. For finite variation, native
local contractibility gives positive length and the actual rectifiable
arclength normalization preserves essentiality and variation. The proved
Lipschitz-loop bound therefore applies without a regularity premise on the
original continuous loop.
-/

open Set
open scoped Topology unitInterval NNReal ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Every continuous essential loop on the original glued carrier has
native variation at least the unchanged target systole. -/
theorem targetSystole_le_variation_of_essential_closedLoop
    (P : ExerciseGluingPreparation C g n genera X)
    (f : closedLoopMapSet P.GluedCarrier)
    (hessential : ¬(closedLoopPath f).Homotopic (Path.refl (f.1 0))) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ENNReal.ofReal (targetSystole C g) ≤ eVariationOn f.1 univ := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  by_cases hfinite : eVariationOn f.1 univ ≠ ⊤
  · obtain ⟨r, hr, hnull⟩ := P.exists_nullhomotopy_radius
    have hrle : ENNReal.ofReal r ≤ eVariationOn f.1 univ := by
      apply le_of_not_gt
      exact fun hsmall => hessential (hnull (f.1 0) (closedLoopPath f) hsmall)
    have hpos : 0 < eVariationOn f.1 univ :=
      (ENNReal.ofReal_pos.mpr hr).trans_le hrle
    have hrealpos : 0 < (eVariationOn f.1 univ).toReal :=
      ENNReal.toReal_pos hpos.ne' hfinite
    obtain ⟨a, hbase, haLip, haVariation, haHom⟩ :=
      exists_rectifiable_arclength_closedLoop f hfinite hrealpos
    have haEssential : ¬(closedLoopPath a).Homotopic (Path.refl (a.1 0)) := by
      intro haNull
      have hcast := haNull.pathCast hbase hbase
      have hrefl : (Path.refl (a.1 0)).cast hbase hbase = Path.refl (f.1 0) := by
        apply Path.ext
        funext t
        exact hbase.symm
      rw [hrefl] at hcast
      exact hessential (haHom.trans hcast)
    exact (P.targetSystole_le_variation_of_essential_lipschitz_loop
      (NNReal.mk (eVariationOn f.1 univ).toReal ENNReal.toReal_nonneg)
      a haLip haEssential).trans_eq haVariation
  · rw [not_ne_iff.mp hfinite]
    exact le_top

/-- The same native systole bound in the based-path form needed by covering
and displacement comparisons, at every actual basepoint. -/
theorem targetSystole_le_variation_of_essential_path
    (P : ExerciseGluingPreparation C g n genera X) {y : P.GluedCarrier}
    (β : Path y y) (hessential : ¬β.Homotopic (Path.refl y)) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ENNReal.ofReal (targetSystole C g) ≤ eVariationOn β univ := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  let f : closedLoopMapSet P.GluedCarrier :=
    ⟨β.toContinuousMap, by change β 0 = β 1; rw [β.source, β.target]⟩
  have hfEssential : ¬(closedLoopPath f).Homotopic (Path.refl (f.1 0)) := by
    intro hnull
    have hcast := hnull.pathCast β.source.symm β.source.symm
    have hpath : (closedLoopPath f).cast β.source.symm β.source.symm = β := by
      apply Path.ext
      funext t
      rfl
    have hrefl : (Path.refl (f.1 0)).cast β.source.symm β.source.symm = Path.refl y := by
      apply Path.ext
      funext t
      exact β.source
    rw [hpath, hrefl] at hcast
    exact hessential hcast
  exact P.targetSystole_le_variation_of_essential_closedLoop f hfEssential

end SystolicGrowth.ExerciseGluingPreparation
