module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.CubicMajorArcPoweredModel
public import CookMagyar.ArcPhasePeriodicity
public import Mathlib.MeasureTheory.Function.Floor

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SystolicGrowth.CookMagyarMajorArc

open CookMagyarArcs CookMagyarCircle CookMagyarFiniteFourier

/-! # A measurable model on wrapped major arcs

The nearest-integer representative gives a canonical displacement on the
circle. This turns the existential local major-arc approximation into a
single model function suitable for integration.
-/

/-- The canonical displacement from a rational center on the unit circle. -/
noncomputable def wrappedMajorArcDisplacement (a q : ℕ) (alpha : ℝ) : ℝ :=
  alpha - rationalCenter a q -
    (round (alpha - rationalCenter a q) : ℝ)

theorem measurable_wrappedMajorArcDisplacement (a q : ℕ) :
    Measurable (wrappedMajorArcDisplacement a q) := by
  change Measurable (fun alpha : ℝ =>
    alpha - rationalCenter a q -
      (round (alpha - rationalCenter a q) : ℝ))
  exact CookMagyarArcs.measurable_wrappedDisplacement (rationalCenter a q)

/-- The nearest-integer displacement is invariant under integer shifts. -/
theorem wrappedMajorArcDisplacement_add_int
    (a q : ℕ) (alpha : ℝ) (z : ℤ) :
    wrappedMajorArcDisplacement a q (alpha + z) =
      wrappedMajorArcDisplacement a q alpha := by
  unfold wrappedMajorArcDisplacement
  rw [show alpha + (z : ℝ) - rationalCenter a q =
      (alpha - rationalCenter a q) + z by ring,
    round_add_intCast]
  push_cast
  ring

/-- The normalized continuous approximation, evaluated at the canonical
small displacement even for an arc crossing the endpoint of `[0,1]`. -/
noncomputable def wrappedMajorArcModel
    (q a N n T : ℕ) [NeZero q] (alpha : ℝ) : ℂ :=
  (unitCubicExponentialSum (a : ZMod q) *
    ((Nat.totient q : ℂ)⁻¹ *
      ∫ t in Set.Icc (0 : ℝ) N,
        cubicAbelWeight (wrappedMajorArcDisplacement a q alpha) t)) ^ n *
    negAddChar (rationalCenter a q +
      wrappedMajorArcDisplacement a q alpha) T

/-- The canonical wrapped model is period one, so a clipped arc crossing an
endpoint can be unfolded without changing its integrand. -/
theorem wrappedMajorArcModel_add_int
    (q a N n T : ℕ) [NeZero q] (alpha : ℝ) (z : ℤ) :
    wrappedMajorArcModel q a N n T (alpha + z) =
      wrappedMajorArcModel q a N n T alpha := by
  simp only [wrappedMajorArcModel, wrappedMajorArcDisplacement_add_int]

/-- The canonical wrapped model is measurable as a function of the arc point. -/
theorem measurable_wrappedMajorArcModel
    (q a N n T : ℕ) [NeZero q] :
    Measurable (wrappedMajorArcModel q a N n T) := by
  let J : ℝ → ℂ := fun beta =>
    ∫ t in Set.Icc (0 : ℝ) N, cubicAbelWeight beta t
  have hJ : Continuous J := by
    dsimp [J]
    apply continuous_parametric_integral_of_continuous
    · exact (by fun_prop [cubicAbelWeight, cubicAbelRealPhase] : Continuous
        (fun p : ℝ × ℝ => cubicAbelWeight p.1 p.2))
    · exact isCompact_Icc
  have hdisp := measurable_wrappedMajorArcDisplacement a q
  have hA : Measurable (fun alpha : ℝ =>
      unitCubicExponentialSum (a : ZMod q) *
        ((Nat.totient q : ℂ)⁻¹ * J (wrappedMajorArcDisplacement a q alpha))) :=
    measurable_const.mul (measurable_const.mul (hJ.measurable.comp hdisp))
  have hphase : Measurable (fun beta : ℝ =>
      negAddChar (rationalCenter a q + beta) T) := by
    exact (by fun_prop [negAddChar] : Continuous
      (fun beta : ℝ => negAddChar (rationalCenter a q + beta) T)).measurable
  have hP := hphase.comp hdisp
  change Measurable (fun alpha : ℝ =>
    (unitCubicExponentialSum (a : ZMod q) *
      ((Nat.totient q : ℂ)⁻¹ * J (wrappedMajorArcDisplacement a q alpha))) ^ n *
      negAddChar (rationalCenter a q +
        wrappedMajorArcDisplacement a q alpha) T)
  exact hA.pow_const n |>.mul hP

/-- The wrapped model is integrable on its finite-measure major arc. -/
theorem wrappedMajorArcModel_integrableOn
    (q a N Q n T : ℕ) [NeZero q] :
    IntegrableOn (wrappedMajorArcModel q a N n T) (majorArcAt N Q a q) := by
  have hfin : volume (majorArcAt N Q a q) ≠ ∞ := by
    apply ne_of_lt
    calc
      volume (majorArcAt N Q a q) ≤ volume (Set.Icc (0 : ℝ) 1) :=
        measure_mono (majorArcAt_subset_Icc N Q a q)
      _ < ∞ := by simp
  have hbound : ∀ alpha : ℝ,
      ‖wrappedMajorArcModel q a N n T alpha‖ ≤ (N : ℝ) ^ n := by
    intro alpha
    rw [wrappedMajorArcModel, norm_mul, norm_pow, norm_negAddChar, mul_one]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_normalizedCubicIntegralModel_le q (a : ZMod q)
        (wrappedMajorArcDisplacement a q alpha) N) n
  exact volume.integrableOn_of_bounded hfin
    (measurable_wrappedMajorArcModel q a N n T).aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

/-- On a major arc, the canonical measurable model retains the pointwise
quantitative error from the Abel/AP bridge. -/
theorem norm_cubicIntegrand_sub_wrappedMajorArcModel_le
    (q a N Q n T : ℕ) [NeZero q] {alpha Delta : ℝ}
    (hN : 0 < N) (hDelta : 0 ≤ Delta)
    (halpha : alpha ∈ majorArcAt N Q a q)
    (hAP : ∀ r : ZMod q, ∀ m ≤ N,
      ‖cubicResiduePartialSum q r m -
        (m + 1 : ℕ) *
          (if IsUnit r then (Nat.totient q : ℂ)⁻¹ else 0)‖ ≤ Delta) :
    ‖cubicIntegrand n N T alpha -
      wrappedMajorArcModel q a N n T alpha‖ ≤
      (n : ℝ) * ((Real.log 4 + 4) * (N : ℝ)) ^ (n - 1) *
        (((q : ℝ) * Delta + 1) * (1 + 8 * Real.pi * (Q : ℝ))) := by
  let beta := wrappedMajorArcDisplacement a q alpha
  have hbeta : |beta| < cubicArcRadius N Q := by
    simpa [beta, wrappedMajorArcDisplacement,
      CookMagyarArcs.periodicDistance_eq_abs_sub_round] using halpha.2
  have hdecomp : alpha = rationalCenter a q + beta +
      (round (alpha - rationalCenter a q) : ℤ) := by
    dsimp [beta, wrappedMajorArcDisplacement]
    ring
  have hperiod : cubicIntegrand n N T alpha =
      cubicIntegrand n N T (rationalCenter a q + beta) := by
    rw [hdecomp, CookMagyarArcs.cubicIntegrand_add_int]
  rw [hperiod]
  change ‖cubicIntegrand n N T (rationalCenter a q + beta) -
      (unitCubicExponentialSum (a : ZMod q) *
        ((Nat.totient q : ℂ)⁻¹ *
          ∫ t in Set.Icc (0 : ℝ) N, cubicAbelWeight beta t)) ^ n *
        negAddChar (rationalCenter a q + beta) T‖ ≤ _
  exact norm_cubicIntegrand_sub_normalizedIntegralModel_le_on_arc
    q a N Q n T hN hDelta (le_of_lt hbeta) hAP

end SystolicGrowth.CookMagyarMajorArc
