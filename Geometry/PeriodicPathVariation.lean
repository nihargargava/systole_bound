module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Algebra.Order.Interval.Set.Monoid
public import Mathlib.Algebra.Ring.Periodic

@[expose] public section

/-!
# Variation over a full period

Splitting a period at the new starting point and translating the first part
to the end preserves the full variation. The identity also holds for
infinite variation and requires no continuity assumption.
-/

open Set

namespace SystolicGrowth

/-- Moving the initial point within one period does not change the metric
variation over a full period. -/
theorem eVariationOn_Icc_eq_of_periodic_of_mem_period
    {E : Type*} [PseudoEMetricSpace E] (f : ℝ → E) {T A s : ℝ}
    (_hT : 0 < T) (hperiod : Function.Periodic f T)
    (hAs : A ≤ s) (hsT : s ≤ A + T) :
    eVariationOn f (Icc s (s + T)) = eVariationOn f (Icc A (A + T)) := by
  have hsplitA : eVariationOn f (Icc A s) + eVariationOn f (Icc s (A + T)) =
      eVariationOn f (Icc A (A + T)) := by
    simpa only [univ_inter] using
      eVariationOn.Icc_add_Icc f hAs hsT (mem_univ s)
  have hsplitS : eVariationOn f (Icc s (A + T)) +
      eVariationOn f (Icc (A + T) (s + T)) = eVariationOn f (Icc s (s + T)) := by
    simpa only [univ_inter] using
      eVariationOn.Icc_add_Icc f hsT
        (show A + T ≤ s + T by simpa only [add_comm] using add_le_add_right hAs T)
        (mem_univ (A + T))
  have hperiodEq : f ∘ (fun t : ℝ => t + T) = f := funext hperiod
  have hshift : eVariationOn f (Icc A s) = eVariationOn f (Icc (A + T) (s + T)) := by
    simpa only [hperiodEq, image_add_const_Icc] using
      eVariationOn.comp_eq_of_monotoneOn f (t := Icc A s)
        (fun t : ℝ => t + T) (fun _ _ _ _ h => by
          simpa only [add_comm] using add_le_add_right h T)
  calc
    eVariationOn f (Icc s (s + T)) =
        eVariationOn f (Icc s (A + T)) + eVariationOn f (Icc (A + T) (s + T)) :=
      hsplitS.symm
    _ = eVariationOn f (Icc s (A + T)) + eVariationOn f (Icc A s) := by rw [← hshift]
    _ = eVariationOn f (Icc A s) + eVariationOn f (Icc s (A + T)) := add_comm _ _
    _ = eVariationOn f (Icc A (A + T)) := hsplitA

#print axioms eVariationOn_Icc_eq_of_periodic_of_mem_period

end SystolicGrowth
