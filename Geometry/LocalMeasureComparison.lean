module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Compactness.Lindelof

@[expose] public section

/-!
# Local-to-global measure comparison

Local domination on open neighborhoods globalizes through a countable
subcover and its disjoint measurable partition. No regularity, local
finiteness, or sigma-finiteness assumption is required.
-/

open Set MeasureTheory
open scoped Topology ENNReal

namespace SystolicGrowth

private theorem measure_restrict_iUnion_le_of_restrict_le
    {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    (U : ℕ → Set α) (hU : ∀ i, MeasurableSet (U i))
    (hle : ∀ i, μ.restrict (U i) ≤ ν.restrict (U i)) :
    μ.restrict (⋃ i, U i) ≤ ν.restrict (⋃ i, U i) := by
  let D := disjointed U
  have hD : ∀ i, MeasurableSet (D i) := fun i => MeasurableSet.disjointed hU i
  have hDle (i : ℕ) : μ.restrict (D i) ≤ ν.restrict (D i) := by
    have h := Measure.restrict_mono (Subset.rfl : D i ⊆ D i) (hle i)
    rw [Measure.restrict_restrict_of_subset (disjointed_subset U i),
      Measure.restrict_restrict_of_subset (disjointed_subset U i)] at h
    exact h
  have hcover : (⋃ i, D i) = ⋃ i, U i := iUnion_disjointed
  apply Measure.le_iff.mpr
  intro s hs
  rw [← hcover,
    Measure.restrict_iUnion_apply (disjoint_disjointed U) hD hs,
    Measure.restrict_iUnion_apply (disjoint_disjointed U) hD hs]
  exact ENNReal.tsum_le_tsum fun i => Measure.le_iff'.mp (hDle i) s

/-- **Math.** On a fixed measurable set, domination on every sufficiently small
open neighborhood implies domination of the restricted measures. -/
theorem measure_restrict_le_of_locally_le
    {α : Type*} [TopologicalSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [OpensMeasurableSpace α]
    (μ ν : Measure α) {S : Set α} (hS : MeasurableSet S)
    (hlocal : ∀ x ∈ S, ∃ U : Set α, IsOpen U ∧ x ∈ U ∧
      ∀ s : Set α, MeasurableSet s → s ⊆ S ∩ U → μ s ≤ ν s) :
    μ.restrict S ≤ ν.restrict S := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hnonempty
  · simp
  letI : Nonempty S := hnonempty.to_subtype
  choose U hUopen hxU hUle using fun x : S => hlocal x x.2
  have hcover : S ⊆ ⋃ x : S, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  obtain ⟨f, hf⟩ := (HereditarilyLindelofSpace.isLindelof S).indexed_countable_subcover
    U hUopen hcover
  let V : ℕ → Set α := fun i => S ∩ U (f i)
  have hV : ∀ i, MeasurableSet (V i) := fun i => hS.inter (hUopen (f i)).measurableSet
  have hVle : ∀ i, μ.restrict (V i) ≤ ν.restrict (V i) := by
    intro i
    apply Measure.le_iff.mpr
    intro s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
    exact hUle (f i) (s ∩ V i) (hs.inter (hV i)) inter_subset_right
  have hVcover : (⋃ i, V i) = S := by
    apply Subset.antisymm
    · exact iUnion_subset fun _ => inter_subset_left
    · intro x hx
      rcases mem_iUnion.mp (hf hx) with ⟨i, hi⟩
      exact mem_iUnion.mpr ⟨i, hx, hi⟩
  rw [← hVcover]
  exact measure_restrict_iUnion_le_of_restrict_le μ ν V hV hVle

/-- **Math.** Local measurable-set domination on open neighborhoods is global
measure domination on a second-countable space. -/
theorem measure_le_of_locally_le
    {α : Type*} [TopologicalSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [OpensMeasurableSpace α]
    (μ ν : Measure α)
    (hlocal : ∀ x, ∃ U : Set α, IsOpen U ∧ x ∈ U ∧
      ∀ s : Set α, MeasurableSet s → s ⊆ U → μ s ≤ ν s) :
    μ ≤ ν := by
  have h := measure_restrict_le_of_locally_le μ ν MeasurableSet.univ (by
    intro x _
    obtain ⟨U, hU, hx, hle⟩ := hlocal x
    exact ⟨U, hU, hx, fun s hs hsub => hle s hs (hsub.trans inter_subset_right)⟩)
  simpa only [Measure.restrict_univ] using h

/-- **Math.** Local domination of restrictions is enough to compare the whole
measures; no additional setwise compatibility premise is needed. -/
theorem measure_le_of_locally_restrict_le
    {α : Type*} [TopologicalSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [OpensMeasurableSpace α]
    (μ ν : Measure α)
    (hlocal : ∀ x, ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ μ.restrict U ≤ ν.restrict U) :
    μ ≤ ν := by
  apply measure_le_of_locally_le μ ν
  intro x
  obtain ⟨U, hU, hx, hle⟩ := hlocal x
  refine ⟨U, hU, hx, fun s hs hsub => ?_⟩
  have h := Measure.le_iff'.mp hle s
  simpa only [Measure.restrict_apply hs, inter_eq_left.mpr hsub] using h

#print axioms measure_restrict_le_of_locally_le
#print axioms measure_le_of_locally_le
#print axioms measure_le_of_locally_restrict_le

end SystolicGrowth
