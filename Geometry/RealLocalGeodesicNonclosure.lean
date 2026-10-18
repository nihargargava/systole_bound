module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.HyperbolicLocalGeodesicConvexity

@[expose] public section

/-!
# Positive-speed real local segments do not close

The exponential vertical geodesic embeds the real line isometrically in the
hyperbolic plane. Its proved local-to-global cosh inequality rules out equal
endpoint values, without an assumed orientation or monotonicity of the curve.
-/

open Set

namespace SystolicGrowth

/-- A continuous real curve with a positive-speed local metric segment law
has distinct endpoints on every nondegenerate compact interval. -/
theorem real_locally_metric_segment_endpoints_ne
    {a b speed : ℝ} (hab : a < b) (hs : 0 < speed)
    (α : Icc a b → ℝ) (hα : Continuous α)
    (hlocal : ∀ t : Icc a b, a < t.1 → t.1 < b →
      ∃ η > 0, ∀ u v : Icc a b,
        dist u t < η → dist v t < η →
          dist (α u) (α v) = speed * |(u : ℝ) - (v : ℝ)|) :
    α ⟨a, le_rfl, hab.le⟩ ≠ α ⟨b, hab.le, le_rfl⟩ := by
  let e : ℝ → UpperHalfPlane := hyperbolicVerticalSegmentPoint 0 0 1
  have he : Isometry e := by
    apply Isometry.of_dist_eq
    intro u v
    simp only [e, hyperbolicVerticalSegmentPoint_dist, sub_zero, abs_one, mul_one,
      Real.dist_eq]
  let β : Icc a b → UpperHalfPlane := e ∘ α
  have hβ : Continuous β := he.continuous.comp hα
  have hβlocal : ∀ t : Icc a b, a < t.1 → t.1 < b →
      ∃ η > 0, ∀ u v : Icc a b,
        dist u t < η → dist v t < η →
          dist (β u) (β v) = speed * |(u : ℝ) - (v : ℝ)| := by
    intro t hta htb
    obtain ⟨η, hη, hm⟩ := hlocal t hta htb
    refine ⟨η, hη, ?_⟩
    intro u v hu hv
    rw [show dist (β u) (β v) = dist (α u) (α v) from he.dist_eq _ _]
    exact hm u v hu hv
  intro heq
  let t₀ : Icc a b := ⟨a, le_rfl, hab.le⟩
  let t₁ : Icc a b := ⟨b, hab.le, le_rfl⟩
  have heqβ : β t₀ = β t₁ := congrArg e heq
  have hc := hyperbolic_locally_metric_segment_midpoint_cosh_le
    hab hs β hβ hβlocal (β t₀)
  change 2 * Real.cosh (speed * (b - a) / 2) *
      Real.cosh (dist (β t₀) (β ⟨(a + b) / 2, by constructor <;> linarith⟩)) ≤
    Real.cosh (dist (β t₀) (β t₀)) + Real.cosh (dist (β t₀) (β t₁)) at hc
  rw [← heqβ, dist_self, Real.cosh_zero] at hc
  have hD : 0 < speed * (b - a) / 2 :=
    div_pos (mul_pos hs (sub_pos.mpr hab)) (by norm_num)
  have hcosh : 1 < Real.cosh (speed * (b - a) / 2) := Real.one_lt_cosh.mpr hD.ne'
  have hmid := Real.one_le_cosh
    (dist (β t₀) (β ⟨(a + b) / 2, by constructor <;> linarith⟩))
  nlinarith

end SystolicGrowth
