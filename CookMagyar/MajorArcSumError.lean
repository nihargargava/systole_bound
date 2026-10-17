module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.MajorArcIntegralError

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SystolicGrowth.CookMagyarArcs

/-! # Summing errors over disjoint rational arcs

Once the major arcs are separated, a model and error bound on each rational
arc give a bound for the complete major-arc integral. This leaves the
arithmetic-progression estimate and the integral of each model to be proved.
-/

/-- Local pointwise errors sum over the finitely many disjoint major arcs. -/
theorem norm_cubicMajorArcIntegral_sub_sum_models_le
    (n N T Q : ℕ) (hscale : 2 * Q ^ 3 ≤ N ^ 3)
    (model : ℕ × ℕ → ℝ → ℂ) (E : ℕ × ℕ → ℝ)
    (hmodel : ∀ aq ∈ (majorArcCenters_finite Q).toFinset,
      IntegrableOn (model aq) (majorArcAt N Q aq.1 aq.2))
    (hpoint : ∀ aq ∈ (majorArcCenters_finite Q).toFinset,
      ∀ alpha ∈ majorArcAt N Q aq.1 aq.2,
        ‖cubicIntegrand n N T alpha - model aq alpha‖ ≤ E aq) :
    ‖cubicMajorArcIntegral n N T Q -
        ∑ aq ∈ (majorArcCenters_finite Q).toFinset,
          ∫ alpha in majorArcAt N Q aq.1 aq.2, model aq alpha‖ ≤
      ∑ aq ∈ (majorArcCenters_finite Q).toFinset,
        E aq * volume.real (majorArcAt N Q aq.1 aq.2) := by
  classical
  let F := (majorArcCenters_finite Q).toFinset
  have hlocal : ∀ aq ∈ F,
      ‖(∫ alpha in majorArcAt N Q aq.1 aq.2,
          cubicIntegrand n N T alpha) -
        ∫ alpha in majorArcAt N Q aq.1 aq.2,
          model aq alpha‖ ≤
        E aq * volume.real (majorArcAt N Q aq.1 aq.2) := by
    intro aq haq
    have hfin : volume (majorArcAt N Q aq.1 aq.2) < ∞ := by
      calc
        volume (majorArcAt N Q aq.1 aq.2) ≤
            volume (Set.Icc (0 : ℝ) 1) :=
          measure_mono (majorArcAt_subset_Icc N Q aq.1 aq.2)
        _ < ∞ := by simp
    have hnorm :
        ‖∫ alpha in majorArcAt N Q aq.1 aq.2,
            (cubicIntegrand n N T alpha - model aq alpha)‖ ≤
          E aq * volume.real (majorArcAt N Q aq.1 aq.2) :=
      norm_setIntegral_le_of_norm_le_const hfin (hpoint aq haq)
    rw [integral_sub (cubicIntegrand_integrableOn_majorArcAt
      n N T Q aq.1 aq.2) (hmodel aq haq)] at hnorm
    exact hnorm
  rw [cubicMajorArcIntegral_eq_sum_individual n N T Q hscale]
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ aq ∈ F,
        ((∫ alpha in majorArcAt N Q aq.1 aq.2,
            cubicIntegrand n N T alpha) -
          ∫ alpha in majorArcAt N Q aq.1 aq.2,
            model aq alpha)‖ ≤
      ∑ aq ∈ F,
        ‖(∫ alpha in majorArcAt N Q aq.1 aq.2,
            cubicIntegrand n N T alpha) -
          ∫ alpha in majorArcAt N Q aq.1 aq.2,
            model aq alpha‖ := norm_sum_le _ _
    _ ≤ ∑ aq ∈ F,
        E aq * volume.real (majorArcAt N Q aq.1 aq.2) := by
      apply Finset.sum_le_sum
      intro aq haq
      exact hlocal aq haq

end SystolicGrowth.CookMagyarArcs
