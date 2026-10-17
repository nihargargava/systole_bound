module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingLoopNullhomotopyOpenness
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.EMetricSpace.BoundedVariation

@[expose] public section

/-!
# Continuous periodic extension of an actual closed loop

Mathlib's additive-circle lift identifies the two equal endpoint values and
provides a continuous period-one extension to the real parameter line. Its
full-period variation is exactly the original unit-interval variation.
-/

open Set

namespace SystolicGrowth

instance Internal.ClosedLoopPeriodicExtensionHelpers.unitPeriodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

noncomputable def Internal.ClosedLoopPeriodicExtensionHelpers.closedLoopClampedMap
    {M : Type*} [TopologicalSpace M] (f : closedLoopMapSet M) : ℝ → M :=
  fun t => f.1 (projIcc 0 1 zero_le_one t)

private theorem closedLoopClampedMap_apply
    {M : Type*} [TopologicalSpace M] (f : closedLoopMapSet M) (t : unitInterval) :
    Internal.ClosedLoopPeriodicExtensionHelpers.closedLoopClampedMap f t = f.1 t := by
  dsimp [Internal.ClosedLoopPeriodicExtensionHelpers.closedLoopClampedMap]
  rw [projIcc_val]

private theorem closedLoopClampedMap_endpoints
    {M : Type*} [TopologicalSpace M] (f : closedLoopMapSet M) :
    Internal.ClosedLoopPeriodicExtensionHelpers.closedLoopClampedMap f 0 = Internal.ClosedLoopPeriodicExtensionHelpers.closedLoopClampedMap f 1 := by
  exact (closedLoopClampedMap_apply f 0).trans
    (f.2.trans (closedLoopClampedMap_apply f 1).symm)

/-- The genuine continuous real period-one extension of a native closed loop. -/
noncomputable def closedLoopPeriodicExtension
    {M : Type*} [TopologicalSpace M] (f : closedLoopMapSet M) : ℝ → M :=
  fun t => AddCircle.liftIco (1 : ℝ) 0 (Internal.ClosedLoopPeriodicExtensionHelpers.closedLoopClampedMap f) (t : AddCircle (1 : ℝ))

/-- Continuity includes the identified closing join. -/
theorem closedLoopPeriodicExtension_continuous
    {M : Type*} [TopologicalSpace M] (f : closedLoopMapSet M) :
    Continuous (closedLoopPeriodicExtension f) :=
  (AddCircle.liftIco_zero_continuous (closedLoopClampedMap_endpoints f)
    (f.1.continuous.comp continuous_projIcc).continuousOn).comp
      (AddCircle.continuous_mk' (1 : ℝ))

/-- Periodicity is inherited from the actual additive-circle quotient. -/
theorem closedLoopPeriodicExtension_periodic
    {M : Type*} [TopologicalSpace M] (f : closedLoopMapSet M) :
    Function.Periodic (closedLoopPeriodicExtension f) 1 := by
  intro t
  dsimp [closedLoopPeriodicExtension]
  simp only [AddCircle.coe_period, add_zero]

/-- The real periodic extension agrees with the original closed loop on
the whole closed unit interval, including both endpoint representatives. -/
theorem closedLoopPeriodicExtension_apply
    {M : Type*} [TopologicalSpace M] (f : closedLoopMapSet M) (t : unitInterval) :
    closedLoopPeriodicExtension f t = f.1 t := by
  by_cases ht : (t : ℝ) < 1
  · rw [closedLoopPeriodicExtension, AddCircle.liftIco_zero_coe_apply ⟨t.property.1, ht⟩]
    exact closedLoopClampedMap_apply f t
  · have ht1 : t = 1 := Subtype.ext (le_antisymm t.property.2 (not_lt.mp ht))
    rw [ht1]
    change AddCircle.liftIco (1 : ℝ) 0 (Internal.ClosedLoopPeriodicExtensionHelpers.closedLoopClampedMap f)
      ((1 : ℝ) : AddCircle (1 : ℝ)) = f.1 1
    rw [AddCircle.coe_period, ← AddCircle.coe_zero,
      AddCircle.liftIco_zero_coe_apply (by constructor <;> norm_num : (0 : ℝ) ∈ Ico 0 1)]
    exact (closedLoopClampedMap_apply f 0).trans f.2

/-- Extension preserves the exact native full-period metric variation,
including infinite variation. -/
theorem closedLoopPeriodicExtension_eVariationOn
    {M : Type*} [PseudoEMetricSpace M] (f : closedLoopMapSet M) :
    eVariationOn (closedLoopPeriodicExtension f) (Icc (0 : ℝ) 1) =
      eVariationOn f.1 univ := by
  have heq : closedLoopPeriodicExtension f ∘ (fun t : unitInterval => (t : ℝ)) = f.1 :=
    funext (closedLoopPeriodicExtension_apply f)
  have hc := eVariationOn.comp_eq_of_monotoneOn (closedLoopPeriodicExtension f)
    (t := univ) (fun t : unitInterval => (t : ℝ)) (fun _ _ _ _ h => h)
  simpa only [heq, image_univ, Subtype.range_coe_subtype, setOf_mem_eq] using hc.symm

end SystolicGrowth
