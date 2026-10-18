module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.Assembly
public import CookMagyar.LogCutoff
public import CookMagyar.MainTerm
public import CookMagyar.PrimePowerAsymptotic

@[expose] public section

open Filter

namespace SystolicGrowth
namespace CookMagyarCircle

open CookMagyarArcs

/-! # Target-uniform asymptotic estimates

This module records the quantifier order that is easy to obscure in a paper
statement.  For a fixed number of variables `n`, each analytic estimate is
eventual in the scale `N`, and *inside* that eventual quantifier it holds for
every admissible moving target `T`.  The four eventual estimates are combined
into one threshold before any target is chosen.
-/

/-- Targets which have the necessary congruence and lie in the fixed compact
normalized window at scale `N`. -/
def IsAdmissibleTarget (n N T : ℕ) : Prop :=
  24 ∣ T ∧ CookMagyarWindow n N T

/-- The separated analytic conclusions used in the specialization.

The main coefficient may depend on the fixed arity `n`, but is positive.
The arc errors are at most one quarter of that coefficient times `N^(n-3)`.
The discarded-prime-power estimate is *derived* from `hua`; it is not a
separate assumption.  The constants and eventual thresholds may depend on
`n`; critically, they do not depend on the target `T` inside the compact
window. -/
structure SeparatedCubicEstimates where
  minSummands : ℕ
  minSummands_ge_thirtyThree : 33 ≤ minSummands
  cutoff : ℕ → ℕ → ℕ
  mainCoefficient : ℕ → ℝ
  mainCoefficient_pos : ∀ n, minSummands ≤ n → 0 < mainCoefficient n
  main_lower : ∀ n, minSummands ≤ n →
    ∀ᶠ N : ℕ in atTop, ∀ T, IsAdmissibleTarget n N T →
      mainCoefficient n * cubicMainScale n N ≤
        cubicSingularMainTerm n N T
  major_error : ∀ n, minSummands ≤ n →
    ∀ᶠ N : ℕ in atTop, ∀ T, IsAdmissibleTarget n N T →
      ‖cubicMajorArcIntegral n N T (cutoff n N) -
          (cubicSingularMainTerm n N T : ℂ)‖ ≤
        (mainCoefficient n / 4) * cubicMainScale n N
  minor_error : ∀ n, minSummands ≤ n →
    ∀ᶠ N : ℕ in atTop, ∀ T, IsAdmissibleTarget n N T →
      ‖cubicMinorArcIntegral n N T (cutoff n N)‖ ≤
        (mainCoefficient n / 4) * cubicMainScale n N
  /-- A target-free cubic Hua estimate.  The exact Fourier and Chebyshev
  arguments in `PrimePowerAsymptotic` turn this into the required discarded
  error uniformly in `T`. -/
  hua : CubicHuaEstimate

/-- All four estimates, together with positivity of the scale, hold beyond
one target-independent threshold. -/
theorem SeparatedCubicEstimates.eventually_all
    (a : SeparatedCubicEstimates) {n : ℕ} (hn : a.minSummands ≤ n) :
    ∀ᶠ N : ℕ in atTop,
      0 < N ∧
      ∀ T, IsAdmissibleTarget n N T →
        a.mainCoefficient n * cubicMainScale n N ≤
          cubicSingularMainTerm n N T ∧
        ‖cubicMajorArcIntegral n N T (a.cutoff n N) -
            (cubicSingularMainTerm n N T : ℂ)‖ ≤
          (a.mainCoefficient n / 4) * cubicMainScale n N ∧
        ‖cubicMinorArcIntegral n N T (a.cutoff n N)‖ ≤
          (a.mainCoefficient n / 4) * cubicMainScale n N ∧
        cubicDiscardedRepresentation n N T ≤
          (a.mainCoefficient n / 4) * cubicMainScale n N := by
  have hn9 : 9 ≤ n := (by norm_num : 9 ≤ 33).trans
    (a.minSummands_ge_thirtyThree.trans hn)
  have hc : 0 < a.mainCoefficient n / 4 :=
    div_pos (a.mainCoefficient_pos n hn) (by norm_num)
  have hdiscard :
      ∀ᶠ N : ℕ in atTop, ∀ T : ℕ,
        cubicDiscardedRepresentation n N T ≤
          (a.mainCoefficient n / 4) * cubicMainScale n N := by
    simpa only [cubicMainScale] using
      eventually_discarded_le_mul_cubicMainScale a.hua hn9 hc
  filter_upwards [eventually_gt_atTop (0 : ℕ), a.main_lower n hn,
      a.major_error n hn, a.minor_error n hn, hdiscard] with
      N hN hmain hmajor hminor hdiscard
  refine ⟨hN, fun T hT ↦ ⟨hmain T hT, hmajor T hT, hminor T hT,
    hdiscard T⟩⟩

/-- Choose a single scale threshold for each arity.  Below the minimum arity
the value is irrelevant. -/
noncomputable def SeparatedCubicEstimates.scaleThreshold
    (a : SeparatedCubicEstimates) (n : ℕ) : ℕ :=
  if hn : a.minSummands ≤ n then
    Classical.choose (eventually_atTop.1 (a.eventually_all hn))
  else 0

theorem SeparatedCubicEstimates.all_of_scaleThreshold
    (a : SeparatedCubicEstimates) {n N : ℕ}
    (hn : a.minSummands ≤ n) (hN : a.scaleThreshold n ≤ N) :
    0 < N ∧
    ∀ T, IsAdmissibleTarget n N T →
      a.mainCoefficient n * cubicMainScale n N ≤
        cubicSingularMainTerm n N T ∧
      ‖cubicMajorArcIntegral n N T (a.cutoff n N) -
          (cubicSingularMainTerm n N T : ℂ)‖ ≤
        (a.mainCoefficient n / 4) * cubicMainScale n N ∧
      ‖cubicMinorArcIntegral n N T (a.cutoff n N)‖ ≤
        (a.mainCoefficient n / 4) * cubicMainScale n N ∧
      cubicDiscardedRepresentation n N T ≤
        (a.mainCoefficient n / 4) * cubicMainScale n N := by
  have hchosen := Classical.choose_spec
    (eventually_atTop.1 (a.eventually_all hn))
  exact hchosen N (by simpa [SeparatedCubicEstimates.scaleThreshold, hn] using hN)

/-- The separated, target-uniform estimates assemble into the quantitative
bound family consumed by the prime-representation theorem. -/
noncomputable def SeparatedCubicEstimates.toUniformCubicCircleBounds
    (a : SeparatedCubicEstimates) : UniformCubicCircleBounds where
  minSummands := a.minSummands
  minSummands_ge_thirtyThree := a.minSummands_ge_thirtyThree
  scaleThreshold := a.scaleThreshold
  bounds := by
    intro n N T hn hN hdvd hwindow
    have hall := a.all_of_scaleThreshold hn hN
    have hT : IsAdmissibleTarget n N T := ⟨hdvd, hwindow⟩
    rcases hall.2 T hT with ⟨hmain, hmajor, hminor, hdiscard⟩
    let error := (a.mainCoefficient n / 4) * cubicMainScale n N
    refine
      { cutoff := a.cutoff n N
        mainTerm := cubicSingularMainTerm n N T
        majorError := error
        minorError := error
        discardedError := error
        major_bound := hmajor
        minor_bound := hminor
        discarded_bound := hdiscard
        dominates := ?_ }
    have hc : 0 < a.mainCoefficient n := a.mainCoefficient_pos n hn
    have hs : 0 < cubicMainScale n N := cubicMainScale_pos hall.1
    dsimp [error]
    nlinarith

end CookMagyarCircle
end SystolicGrowth
