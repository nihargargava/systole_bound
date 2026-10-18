module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Topology.MetricSpace.Gluing
public import Mathlib.Topology.MetricSpace.Isometry
public import Geometry.MetricTriangleBoundaryReparameterization

@[expose] public section

/-!
# Symmetry of the actual metric gluing

Swapping the two labelled summands descends to an isometry of the original
separation quotient. This transports comparison with left-copy test points
to the already proved right-copy case without choosing another metric.
-/

namespace SystolicGrowth

variable {A B S : Type*} [MetricSpace A] [MetricSpace B] [MetricSpace S] [Nonempty S]
  {Φ : S → A} {Ψ : S → B}

noncomputable def metricGlueSwap (hΦ : Isometry Φ) (hΨ : Isometry Ψ) :
    Metric.GlueSpace hΦ hΨ → Metric.GlueSpace hΨ hΦ := by
  exact @SeparationQuotient.map (A ⊕ B) (B ⊕ A)
    (Metric.gluePremetric hΦ hΨ).toUniformSpace
    (Metric.gluePremetric hΨ hΦ).toUniformSpace Sum.swap

private theorem metricGlueSwap_mk (hΦ : Isometry Φ) (hΨ : Isometry Ψ) (x : A ⊕ B) :
    metricGlueSwap hΦ hΨ (Quotient.mk'' x) = Quotient.mk'' x.swap := by
  letI := Metric.gluePremetric hΦ hΨ
  letI := Metric.gluePremetric hΨ hΦ
  have hswap : Isometry (Sum.swap : A ⊕ B → B ⊕ A) :=
    Isometry.of_dist_eq (Metric.glueDist_swap Φ Ψ 0)
  exact @SeparationQuotient.map_mk (A ⊕ B) (B ⊕ A)
    (Metric.gluePremetric hΦ hΨ).toUniformSpace
    (Metric.gluePremetric hΨ hΦ).toUniformSpace
    Sum.swap hswap.uniformContinuous x

@[simp] theorem metricGlueSwap_left (hΦ : Isometry Φ) (hΨ : Isometry Ψ) (x : A) :
    metricGlueSwap hΦ hΨ (Metric.toGlueL hΦ hΨ x) = Metric.toGlueR hΨ hΦ x :=
  metricGlueSwap_mk hΦ hΨ (.inl x)

@[simp] theorem metricGlueSwap_right (hΦ : Isometry Φ) (hΨ : Isometry Ψ) (y : B) :
    metricGlueSwap hΦ hΨ (Metric.toGlueR hΦ hΨ y) = Metric.toGlueL hΨ hΦ y :=
  metricGlueSwap_mk hΦ hΨ (.inr y)

theorem metricGlueSwap_isometry (hΦ : Isometry Φ) (hΨ : Isometry Ψ) :
    Isometry (metricGlueSwap hΦ hΨ) := by
  apply Isometry.of_dist_eq
  intro x y
  obtain ⟨a, rfl⟩ := Quotient.exists_rep x
  obtain ⟨b, rfl⟩ := Quotient.exists_rep y
  rw [metricGlueSwap_mk, metricGlueSwap_mk]
  exact Metric.glueDist_swap Φ Ψ 0 a b

@[simp] theorem metricGlueSwap_swap (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
    (x : Metric.GlueSpace hΦ hΨ) :
    metricGlueSwap hΨ hΦ (metricGlueSwap hΦ hΨ x) = x := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep x
  rw [metricGlueSwap_mk, metricGlueSwap_mk, Sum.swap_swap]

/-- Swapping the copies and reversing the two original legs retains exactly
the same native side, with reversed unit time. No glued midpoint uniqueness
is assumed. -/
theorem metricGlueSwap_reversedTwoLeg (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
    (q : S) (x : A) (y : B)
    (α : Set.Icc (0 : ℝ) (dist x (Φ q)) → A)
    (β : Set.Icc (0 : ℝ) (dist (Ψ q) y) → B)
    (hjoin : Metric.toGlueL hΦ hΨ (α ⟨dist x (Φ q), ⟨dist_nonneg, le_rfl⟩⟩) =
      Metric.toGlueR hΦ hΨ (β ⟨0, ⟨le_rfl, dist_nonneg⟩⟩))
    (t : Set.Icc (0 : ℝ) 1) :
    metricGlueSwap hΨ hΦ
      (metricTwoLegUnitPoint dist_nonneg dist_nonneg
        (Metric.toGlueL hΨ hΦ ∘ metricReverseDistanceInterval β)
        (Metric.toGlueR hΨ hΦ ∘ metricReverseDistanceInterval α) t) =
      metricTwoLegUnitPoint dist_nonneg dist_nonneg
        (Metric.toGlueL hΦ hΨ ∘ α) (Metric.toGlueR hΦ hΨ ∘ β)
        (metricBoundaryReverseUnit t) := by
  rw [metricTwoLegUnitPoint_map (metricGlueSwap hΨ hΦ)]
  have hr := metricTwoLegUnitPoint_reverse dist_nonneg dist_nonneg
    (Metric.toGlueL hΦ hΨ ∘ α) (Metric.toGlueR hΦ hΨ ∘ β) hjoin t
  simpa only [metricTwoLegUnitPoint, metricReverseDistanceInterval,
    metricBoundaryReverseInterval, Function.comp_def,
    metricGlueSwap_left, metricGlueSwap_right, dist_comm y (Ψ q), dist_comm (Φ q) x]
    using hr

#print axioms metricGlueSwap_isometry
#print axioms metricGlueSwap_reversedTwoLeg

end SystolicGrowth
