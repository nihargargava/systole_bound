module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.MetricSegmentCompactness
public import Geometry.MetricSegmentUniqueness
public import Geometry.GluingGeodesics
public import Mathlib.Topology.Homeomorph.Defs

@[expose] public section

/-!
# Continuous interpolation by genuine metric segments

The compact family of actual constant-speed metric segments has a continuous
endpoint map. Proved existence and uniqueness make that map a homeomorphism.
Its inverse therefore chooses the segment continuously in both endpoints;
continuous evaluation includes the time parameter. Continuity is derived,
not included among the comparison hypotheses.
-/

open Set

namespace SystolicGrowth

/-- Compact all-test midpoint comparison constructs a jointly continuous
actual metric interpolation, including coincident endpoints. -/
theorem exists_continuous_metric_interpolation_of_midpoint_cosh_all_test
    {M : Type*} [MetricSpace M] [CompactSpace M]
    (hmid : ∀ x y : M, ∃ m : M,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : M, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y)) :
    ∃ G : C((M × M) × unitInterval, M),
      (∀ x y, G ((x, y), 0) = x) ∧ (∀ x y, G ((x, y), 1) = y) ∧
      ∀ x y (s t : unitInterval),
        dist (G ((x, y), s)) (G ((x, y), t)) = dist x y * |(s : ℝ) - (t : ℝ)| := by
  classical
  let S := metricUnitSegmentSet M
  letI : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_metricUnitSegmentSet M)
  let endpoint : S → M × M := fun f => (f.1 0, f.1 1)
  have hendpoint : Continuous endpoint :=
    ((continuous_eval_const 0).comp continuous_subtype_val).prodMk
      ((continuous_eval_const 1).comp continuous_subtype_val)
  have hinjective : Function.Injective endpoint := by
    intro f g h
    have h₀ : f.1 0 = g.1 0 := congrArg Prod.fst h
    have h₁ : f.1 1 = g.1 1 := congrArg Prod.snd h
    let α : Path (f.1 0) (f.1 1) :=
      { toFun := f.1, continuous_toFun := f.1.continuous, source' := rfl, target' := rfl }
    let β : Path (f.1 0) (f.1 1) :=
      { toFun := g.1, continuous_toFun := g.1.continuous,
        source' := h₀.symm, target' := h₁.symm }
    have hα : ∀ s t : unitInterval,
        dist (α s) (α t) = dist (f.1 0) (f.1 1) * |(s : ℝ) - (t : ℝ)| := f.2
    have hβ : ∀ s t : unitInterval,
        dist (β s) (β t) = dist (f.1 0) (f.1 1) * |(s : ℝ) - (t : ℝ)| := by
      intro s t
      change dist (g.1 s) (g.1 t) = dist (f.1 0) (f.1 1) * |(s : ℝ) - (t : ℝ)|
      rw [h₀, h₁]
      exact g.2 s t
    have heq := metric_path_unique_of_midpoint_cosh_all_test hmid α β hα hβ
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    exact congrArg (fun p : Path (f.1 0) (f.1 1) => p t) heq
  have hsurjective : Function.Surjective endpoint := by
    rintro ⟨x, y⟩
    let m : M → M → M := fun a b => (hmid a b).choose
    have hm : ∀ a b : M, dist a (m a b) = dist a b / 2 ∧ dist (m a b) b = dist a b / 2 :=
      fun a b => ⟨(hmid a b).choose_spec.1, (hmid a b).choose_spec.2.1⟩
    obtain ⟨γ, hγ⟩ := exists_midpoint_metric_path m hm x y
    have hmem : (γ : C(unitInterval, M)) ∈ S := by
      intro s t
      change dist (γ s) (γ t) = dist (γ 0) (γ 1) * |(s : ℝ) - (t : ℝ)|
      rw [γ.source, γ.target]
      exact hγ s t
    exact ⟨⟨γ, hmem⟩, Prod.ext γ.source γ.target⟩
  let e : S ≃ M × M := Equiv.ofBijective endpoint ⟨hinjective, hsurjective⟩
  have he : Continuous e := hendpoint
  let H : S ≃ₜ M × M := e.toHomeomorphOfContinuousClosed he he.isClosedMap
  have hend (p : M × M) : endpoint (H.symm p) = p := H.apply_symm_apply p
  let G : C((M × M) × unitInterval, M) :=
    { toFun := fun p => (H.symm p.1).1 p.2
      continuous_toFun := continuous_eval.comp
        ((continuous_subtype_val.comp (H.symm.continuous.comp continuous_fst)).prodMk
          continuous_snd) }
  have hzero (x y : M) : G ((x, y), 0) = x := congrArg Prod.fst (hend (x, y))
  have hone (x y : M) : G ((x, y), 1) = y := congrArg Prod.snd (hend (x, y))
  refine ⟨G, hzero, hone, ?_⟩
  intro x y s t
  have hlaw := (H.symm (x, y)).2 s t
  change dist (G ((x, y), s)) (G ((x, y), t)) =
    dist (G ((x, y), 0)) (G ((x, y), 1)) * |(s : ℝ) - (t : ℝ)| at hlaw
  simpa only [hzero, hone] using hlaw

#print axioms exists_continuous_metric_interpolation_of_midpoint_cosh_all_test

end SystolicGrowth
