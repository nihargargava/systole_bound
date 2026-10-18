module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.UnitInterval

@[expose] public section

/-!
# Compact families of bounded-speed closed loops

Arzelà--Ascoli gives compactness for a common Lipschitz bound and a compact
target. The native variation functional is lower semicontinuous by Mathlib's
pointwise variation theorem. Essentiality remains a separate topological
condition; neither compactness nor its stability is assumed here.
-/

open Set Filter
open scoped Topology NNReal ENNReal

namespace SystolicGrowth

/-- Unit-time closed loops with a common Lipschitz bound, allowing the
basepoint to vary. -/
def metricClosedLipschitzLoopSet (M : Type*) [MetricSpace M] (K : ℝ≥0) :
    Set C(unitInterval, M) :=
  {f | f 0 = f 1 ∧ LipschitzWith K f}

/-- Closed loops with a common speed bound form a compact continuous-map
family when the target metric space is compact. -/
theorem isCompact_metricClosedLipschitzLoopSet
    (M : Type*) [MetricSpace M] [CompactSpace M] (K : ℝ≥0) :
    IsCompact (metricClosedLipschitzLoopSet M K) := by
  let S : Set (unitInterval → M) := {f | f 0 = f 1 ∧ LipschitzWith K f}
  have hSclosed : IsClosed S :=
    (isClosed_eq (continuous_apply 0) (continuous_apply 1)).inter
      (isClosed_setOf_lipschitzWith K)
  have hScompact : IsCompact S := hSclosed.isCompact
  have himage : ContinuousMap.toFun '' metricClosedLipschitzLoopSet M K = S := by
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hf
      exact ⟨⟨f, hf.2.continuous⟩, hf, rfl⟩
  apply ArzelaAscoli.isCompact_of_equicontinuous
  · rw [himage]
    exact hScompact
  · apply Metric.equicontinuous_of_continuity_modulus (fun d : ℝ => K * d)
      (by
        have hmod : Continuous (fun d : ℝ => (K : ℝ) * d) := by fun_prop
        simpa only [mul_zero] using hmod.tendsto 0)
    intro u v f
    exact f.property.2.dist_le_mul u v

/-- Mathlib's pointwise lower semicontinuity of variation applies directly
to the topology of continuous maps, whose evaluations are continuous. -/
theorem lowerSemicontinuous_eVariationOn_continuousMap
    {A M : Type*} [LinearOrder A] [TopologicalSpace A] [PseudoEMetricSpace M]
    (s : Set A) :
    LowerSemicontinuous (fun f : C(A, M) => eVariationOn f s) := by
  intro f v hv
  apply eVariationOn.lowerSemicontinuous_aux (p := 𝓝 f) (F := fun g : C(A, M) => g) _ hv
  intro x _
  exact (continuous_eval_const x).tendsto f

/-- A unit-time curve with Lipschitz constant `K` has variation at most `K`,
without any closed-loop or target compactness hypothesis. -/
theorem eVariationOn_unitInterval_le_of_lipschitz
    {M : Type*} [MetricSpace M] (f : C(unitInterval, M)) {K : ℝ≥0}
    (hf : LipschitzWith K f) : eVariationOn f univ ≤ (K : ℝ≥0∞) := by
  have hmono : MonotoneOn (fun t : unitInterval => (t : ℝ)) univ :=
    fun _ _ _ _ h => h
  have hid : eVariationOn (id : unitInterval → unitInterval) univ ≤ 1 := by
    change eVariationOn (fun t : unitInterval => (t : ℝ)) univ ≤ 1
    simpa only [univ_inter, ← unitInterval.univ_eq_Icc, Set.Icc.coe_zero,
      Set.Icc.coe_one, sub_zero, ENNReal.ofReal_one] using
      hmono.eVariationOn_le (a := 0) (b := 1) (mem_univ _) (mem_univ _)
  have hbound := hf.lipschitzOnWith.comp_eVariationOn_le
    (g := id) (s := univ) (mapsTo_univ id univ)
  change eVariationOn f univ ≤
    (K : ℝ≥0∞) * eVariationOn (id : unitInterval → unitInterval) univ at hbound
  exact hbound.trans (by simpa only [mul_one] using mul_le_mul_right hid (K : ℝ≥0∞))

#print axioms eVariationOn_unitInterval_le_of_lipschitz

end SystolicGrowth
