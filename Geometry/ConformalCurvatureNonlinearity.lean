module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# The smooth nonlinearity for conformal curvature replacement

An actual smooth cutoff and its two primitives extend `exp (2 * t)` from
`[0, log B / 2]`. The extension has a positive globally bounded derivative;
this is the scalar input to the coercive-resolvent contraction argument.
No elliptic solvability or replacement metric is assumed here.
-/

open Set MeasureTheory
open scoped Topology ContDiff

namespace SystolicGrowth

noncomputable section

/-- Two literal smooth steps cut off the interval `[0,b]`. -/
def conformalCurvatureCutoff (b δ t : ℝ) : ℝ :=
  Real.smoothTransition ((t + δ) / δ) *
    Real.smoothTransition ((b + δ - t) / δ)

theorem conformalCurvatureCutoff_contDiff (b δ : ℝ) :
    ContDiff ℝ ∞ (conformalCurvatureCutoff b δ) := by
  unfold conformalCurvatureCutoff
  exact (Real.smoothTransition.contDiff.comp
    ((contDiff_id.add contDiff_const).div_const δ)).mul
      (Real.smoothTransition.contDiff.comp
        ((contDiff_const.sub contDiff_id).div_const δ))

theorem conformalCurvatureCutoff_mem_Icc (b δ t : ℝ) :
    conformalCurvatureCutoff b δ t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · exact mul_le_one₀ (Real.smoothTransition.le_one _)
      (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)

theorem conformalCurvatureCutoff_eq_one {b δ t : ℝ} (hδ : 0 < δ)
    (ht : t ∈ Icc (0 : ℝ) b) : conformalCurvatureCutoff b δ t = 1 := by
  unfold conformalCurvatureCutoff
  rw [Real.smoothTransition.one_of_one_le
    ((le_div_iff₀ hδ).2 (by linarith [ht.1])),
    Real.smoothTransition.one_of_one_le
      ((le_div_iff₀ hδ).2 (by linarith [ht.2]))]
  norm_num

theorem conformalCurvatureCutoff_eq_zero_left {b δ t : ℝ} (hδ : 0 < δ)
    (ht : t ≤ -δ) : conformalCurvatureCutoff b δ t = 0 := by
  unfold conformalCurvatureCutoff
  rw [show Real.smoothTransition ((t + δ) / δ) = 0 from
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le), zero_mul]

theorem conformalCurvatureCutoff_eq_zero_right {b δ t : ℝ} (hδ : 0 < δ)
    (ht : b + δ ≤ t) : conformalCurvatureCutoff b δ t = 0 := by
  unfold conformalCurvatureCutoff
  rw [show Real.smoothTransition ((b + δ - t) / δ) = 0 from
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le), mul_zero]

/-- The smooth primitive has bounded range, despite its unbounded domain. -/
def conformalCurvatureCutoffPrimitive (b δ t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, conformalCurvatureCutoff b δ s

theorem conformalCurvatureCutoffPrimitive_hasDerivAt (b δ t : ℝ) :
    HasDerivAt (conformalCurvatureCutoffPrimitive b δ)
      (conformalCurvatureCutoff b δ t) t :=
  ((conformalCurvatureCutoff_contDiff b δ).continuous.integral_hasStrictDerivAt 0 t).hasDerivAt

theorem conformalCurvatureCutoffPrimitive_contDiff (b δ : ℝ) :
    ContDiff ℝ ∞ (conformalCurvatureCutoffPrimitive b δ) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (conformalCurvatureCutoffPrimitive_hasDerivAt b δ t).differentiableAt, ?_⟩
  have hd : deriv (conformalCurvatureCutoffPrimitive b δ) = conformalCurvatureCutoff b δ := by
    funext t
    exact (conformalCurvatureCutoffPrimitive_hasDerivAt b δ t).deriv
  rw [hd]
  exact conformalCurvatureCutoff_contDiff b δ

theorem conformalCurvatureCutoffPrimitive_eq_self {b δ t : ℝ} (hδ : 0 < δ)
    (ht : t ∈ Icc (0 : ℝ) b) : conformalCurvatureCutoffPrimitive b δ t = t := by
  unfold conformalCurvatureCutoffPrimitive
  calc
    (∫ s in (0 : ℝ)..t, conformalCurvatureCutoff b δ s) = ∫ _ in (0 : ℝ)..t, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le ht.1]
      intro s hs
      exact conformalCurvatureCutoff_eq_one hδ ⟨hs.1, hs.2.trans ht.2⟩
    _ = t := by simp

private theorem conformalCurvatureCutoffPrimitive_eq_left {b δ t : ℝ} (hδ : 0 < δ)
    (ht : t ≤ -δ) :
    conformalCurvatureCutoffPrimitive b δ t = conformalCurvatureCutoffPrimitive b δ (-δ) := by
  have hzero : (∫ s in -δ..t, conformalCurvatureCutoff b δ s) = 0 := by
    calc
      _ = ∫ _ in -δ..t, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_ge ht]
        intro s hs
        exact conformalCurvatureCutoff_eq_zero_left hδ hs.2
      _ = 0 := by simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    ((conformalCurvatureCutoff_contDiff b δ).continuous.intervalIntegrable (μ := volume) 0 (-δ))
    ((conformalCurvatureCutoff_contDiff b δ).continuous.intervalIntegrable (μ := volume) (-δ) t)
  simpa only [conformalCurvatureCutoffPrimitive, hzero, add_zero] using hadd.symm

private theorem conformalCurvatureCutoffPrimitive_eq_right {b δ t : ℝ} (hδ : 0 < δ)
    (ht : b + δ ≤ t) :
    conformalCurvatureCutoffPrimitive b δ t = conformalCurvatureCutoffPrimitive b δ (b + δ) := by
  have hzero : (∫ s in (b + δ)..t, conformalCurvatureCutoff b δ s) = 0 := by
    calc
      _ = ∫ _ in (b + δ)..t, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le ht]
        intro s hs
        exact conformalCurvatureCutoff_eq_zero_right hδ hs.1
      _ = 0 := by simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    ((conformalCurvatureCutoff_contDiff b δ).continuous.intervalIntegrable (μ := volume) 0 (b + δ))
    ((conformalCurvatureCutoff_contDiff b δ).continuous.intervalIntegrable (μ := volume) (b + δ) t)
  simpa only [conformalCurvatureCutoffPrimitive, hzero, add_zero] using hadd.symm

theorem conformalCurvatureCutoffPrimitive_mem_Icc {b δ : ℝ} (hb : 0 ≤ b) (hδ : 0 < δ)
    (t : ℝ) : conformalCurvatureCutoffPrimitive b δ t ∈ Icc (-δ) (b + δ) := by
  have hcont := (conformalCurvatureCutoff_contDiff b δ).continuous
  have hnonneg (s : ℝ) := (conformalCurvatureCutoff_mem_Icc b δ s).1
  have hle (s : ℝ) := (conformalCurvatureCutoff_mem_Icc b δ s).2
  have hposbound (s : ℝ) (hs : 0 ≤ s) :
      0 ≤ conformalCurvatureCutoffPrimitive b δ s ∧ conformalCurvatureCutoffPrimitive b δ s ≤ s := by
    constructor
    · exact intervalIntegral.integral_nonneg_of_forall (μ := volume) hs hnonneg
    · simpa only [conformalCurvatureCutoffPrimitive, intervalIntegral.integral_const,
        sub_zero, smul_eq_mul, mul_one] using
        intervalIntegral.integral_mono hs (hcont.intervalIntegrable (μ := volume) 0 s)
          (continuous_const.intervalIntegrable (μ := volume) 0 s) hle
  have hnegbound (s : ℝ) (hs : s ≤ 0) :
      s ≤ conformalCurvatureCutoffPrimitive b δ s ∧ conformalCurvatureCutoffPrimitive b δ s ≤ 0 := by
    unfold conformalCurvatureCutoffPrimitive
    rw [intervalIntegral.integral_symm]
    have hn := intervalIntegral.integral_nonneg_of_forall (μ := volume) hs hnonneg
    have hu : (∫ u in s..(0 : ℝ), conformalCurvatureCutoff b δ u) ≤ -s := by
      simpa only [intervalIntegral.integral_const, zero_sub, smul_eq_mul, mul_one] using
        intervalIntegral.integral_mono hs (hcont.intervalIntegrable (μ := volume) s 0)
          (continuous_const.intervalIntegrable (μ := volume) s 0) hle
    constructor <;> linarith
  by_cases htleft : t ≤ -δ
  · rw [conformalCurvatureCutoffPrimitive_eq_left hδ htleft]
    have h := hnegbound (-δ) (by linarith)
    exact ⟨h.1, h.2.trans (by linarith)⟩
  by_cases htright : b + δ ≤ t
  · rw [conformalCurvatureCutoffPrimitive_eq_right hδ htright]
    have h := hposbound (b + δ) (by linarith)
    exact ⟨(by linarith [h.1]), h.2⟩
  by_cases ht : 0 ≤ t
  · have h := hposbound t ht
    exact ⟨(by linarith [h.1]), (by linarith [h.2])⟩
  · have h := hnegbound t (le_of_not_ge ht)
    exact ⟨(by linarith [h.1]), h.2.trans (by linarith)⟩

/-- The explicit extension is allowed linear growth; it has bounded slope. -/
def conformalCurvatureNonlinearity (B t : ℝ) : ℝ :=
  1 + ∫ s in (0 : ℝ)..t,
    2 * Real.exp (2 * conformalCurvatureCutoffPrimitive (Real.log B / 2) (Real.log 2 / 2) s)

theorem conformalCurvatureNonlinearity_hasDerivAt (B t : ℝ) :
    HasDerivAt (conformalCurvatureNonlinearity B)
      (2 * Real.exp (2 * conformalCurvatureCutoffPrimitive (Real.log B / 2) (Real.log 2 / 2) t)) t := by
  have hc : Continuous (fun s => 2 * Real.exp
      (2 * conformalCurvatureCutoffPrimitive (Real.log B / 2) (Real.log 2 / 2) s)) :=
    continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul (conformalCurvatureCutoffPrimitive_contDiff _ _).continuous))
  exact (hc.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add 1

theorem conformalCurvatureNonlinearity_contDiff (B : ℝ) :
    ContDiff ℝ ∞ (conformalCurvatureNonlinearity B) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (conformalCurvatureNonlinearity_hasDerivAt B t).differentiableAt, ?_⟩
  have hc : ContDiff ℝ ∞ (fun s => 2 * Real.exp
      (2 * conformalCurvatureCutoffPrimitive (Real.log B / 2) (Real.log 2 / 2) s)) :=
    contDiff_const.mul (Real.contDiff_exp.comp
      (contDiff_const.mul (conformalCurvatureCutoffPrimitive_contDiff _ _)))
  have hd : deriv (conformalCurvatureNonlinearity B) = (fun s => 2 * Real.exp
      (2 * conformalCurvatureCutoffPrimitive (Real.log B / 2) (Real.log 2 / 2) s)) := by
    funext t
    exact (conformalCurvatureNonlinearity_hasDerivAt B t).deriv
  rw [hd]
  exact hc

@[simp] theorem conformalCurvatureNonlinearity_zero (B : ℝ) :
    conformalCurvatureNonlinearity B 0 = 1 := by
  simp [conformalCurvatureNonlinearity]

theorem conformalCurvatureNonlinearity_eq_exp {B t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.log B / 2)) :
    conformalCurvatureNonlinearity B t = Real.exp (2 * t) := by
  have hδ : 0 < Real.log 2 / 2 := by positivity
  have heq : (∫ s in (0 : ℝ)..t, 2 * Real.exp (2 *
      conformalCurvatureCutoffPrimitive (Real.log B / 2) (Real.log 2 / 2) s)) =
      ∫ s in (0 : ℝ)..t, 2 * Real.exp (2 * s) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le ht.1]
    intro s hs
    dsimp only
    rw [conformalCurvatureCutoffPrimitive_eq_self hδ ⟨hs.1, hs.2.trans ht.2⟩]
  have hint : (∫ s in (0 : ℝ)..t, 2 * Real.exp (2 * s)) = Real.exp (2 * t) - 1 := by
    have hd (s : ℝ) : HasDerivAt (fun x : ℝ => Real.exp (2 * x))
        (2 * Real.exp (2 * s)) s := by
      simpa only [Function.comp_def, mul_one, one_mul, mul_comm] using
        (Real.hasDerivAt_exp (2 * s)).comp s ((hasDerivAt_id s).const_mul 2)
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hd s) ((continuous_const.mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 t)
  unfold conformalCurvatureNonlinearity
  rw [heq, hint]
  ring

theorem conformalCurvatureNonlinearity_deriv_mem_Icc {B : ℝ} (hB : 1 < B) (t : ℝ) :
    deriv (conformalCurvatureNonlinearity B) t ∈ Icc (1 : ℝ) (4 * B) := by
  rw [(conformalCurvatureNonlinearity_hasDerivAt B t).deriv]
  have hσ := conformalCurvatureCutoffPrimitive_mem_Icc
    (show 0 ≤ Real.log B / 2 from div_nonneg (Real.log_pos hB).le (by norm_num))
    (show 0 < Real.log 2 / 2 by positivity) t
  have hlo := Real.exp_le_exp.mpr (show -(Real.log 2) ≤ 2 *
      conformalCurvatureCutoffPrimitive (Real.log B / 2) (Real.log 2 / 2) t by linarith [hσ.1])
  have hhi := Real.exp_le_exp.mpr (show 2 *
      conformalCurvatureCutoffPrimitive (Real.log B / 2) (Real.log 2 / 2) t ≤
        Real.log B + Real.log 2 by linarith [hσ.2])
  rw [Real.exp_neg, Real.exp_log (by norm_num)] at hlo
  rw [Real.exp_add, Real.exp_log (by linarith : 0 < B), Real.exp_log (by norm_num)] at hhi
  constructor <;> nlinarith

theorem conformalCurvatureNonlinearity_lipschitz {B : ℝ} (hB : 1 < B) :
    LipschitzWith ⟨4 * B, by linarith⟩ (conformalCurvatureNonlinearity B) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    ((conformalCurvatureNonlinearity_contDiff B).differentiable (by simp))
  intro t
  exact_mod_cast (show ‖deriv (conformalCurvatureNonlinearity B) t‖ ≤ 4 * B by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [(conformalCurvatureNonlinearity_deriv_mem_Icc hB t).1])]
    exact (conformalCurvatureNonlinearity_deriv_mem_Icc hB t).2)

theorem conformalCurvatureNonlinearity_deriv_hasDerivAt (B t : ℝ) :
    HasDerivAt (deriv (conformalCurvatureNonlinearity B))
      (2 * conformalCurvatureCutoff (Real.log B / 2) (Real.log 2 / 2) t *
        deriv (conformalCurvatureNonlinearity B) t) t := by
  have hd : deriv (conformalCurvatureNonlinearity B) = (fun s => 2 * Real.exp
      (2 * conformalCurvatureCutoffPrimitive (Real.log B / 2) (Real.log 2 / 2) s)) := by
    funext s
    exact (conformalCurvatureNonlinearity_hasDerivAt B s).deriv
  rw [hd]
  exact (((Real.hasDerivAt_exp _).comp t
    ((conformalCurvatureCutoffPrimitive_hasDerivAt _ _ t).const_mul 2)).const_mul 2).congr_deriv
      (by dsimp only; ring)

/-- The second derivative needed for the local Sobolev chain rule is
globally bounded as well; the value of the nonlinearity need not be bounded. -/
theorem conformalCurvatureNonlinearity_second_deriv_mem_Icc {B : ℝ} (hB : 1 < B) (t : ℝ) :
    deriv (deriv (conformalCurvatureNonlinearity B)) t ∈ Icc (0 : ℝ) (8 * B) := by
  rw [(conformalCurvatureNonlinearity_deriv_hasDerivAt B t).deriv]
  have hc := conformalCurvatureCutoff_mem_Icc (Real.log B / 2) (Real.log 2 / 2) t
  have hd := conformalCurvatureNonlinearity_deriv_mem_Icc hB t
  constructor
  · exact mul_nonneg (mul_nonneg (by norm_num) hc.1) (by linarith [hd.1])
  · calc
      2 * conformalCurvatureCutoff (Real.log B / 2) (Real.log 2 / 2) t *
          deriv (conformalCurvatureNonlinearity B) t ≤
          2 * deriv (conformalCurvatureNonlinearity B) t := by
        nlinarith [mul_nonneg
          (show 0 ≤ deriv (conformalCurvatureNonlinearity B) t by linarith [hd.1])
          (show 0 ≤ 1 - conformalCurvatureCutoff (Real.log B / 2) (Real.log 2 / 2) t by linarith [hc.2])]
      _ ≤ 8 * B := by linarith [hd.2]

theorem conformalCurvatureNonlinearity_strictMono {B : ℝ} (hB : 1 < B) :
    StrictMono (conformalCurvatureNonlinearity B) := by
  apply strictMono_of_hasDerivAt_pos (conformalCurvatureNonlinearity_hasDerivAt B)
  intro t
  have h := (conformalCurvatureNonlinearity_deriv_mem_Icc hB t).1
  rw [(conformalCurvatureNonlinearity_hasDerivAt B t).deriv] at h
  linarith

/-- Center the damped nonlinearity at zero so that Lipschitz composition
acts directly on `Lp`, even before adding the finite-volume constant. -/
def conformalCurvatureDampedNonlinearity (B lam t : ℝ) : ℝ :=
  lam * t - conformalCurvatureNonlinearity B t + 1

@[simp] theorem conformalCurvatureDampedNonlinearity_zero (B lam : ℝ) :
    conformalCurvatureDampedNonlinearity B lam 0 = 0 := by
  simp [conformalCurvatureDampedNonlinearity]

theorem conformalCurvatureDampedNonlinearity_hasDerivAt (B lam t : ℝ) :
    HasDerivAt (conformalCurvatureDampedNonlinearity B lam)
      (lam - deriv (conformalCurvatureNonlinearity B) t) t := by
  exact ((((hasDerivAt_id t).const_mul lam).sub
    (conformalCurvatureNonlinearity_hasDerivAt B t)).add_const 1).congr_deriv
      (by rw [(conformalCurvatureNonlinearity_hasDerivAt B t).deriv]; ring)

/-- The derivative bounds of the constructed extension give the actual
`λ - 1` slope bound used by the resolvent, not just the larger triangle bound. -/
theorem conformalCurvatureDampedNonlinearity_lipschitz {B lam : ℝ}
    (hB : 1 < B) (hlam : 4 * B ≤ lam) :
    LipschitzWith ⟨lam - 1, by linarith⟩ (conformalCurvatureDampedNonlinearity B lam) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t => (conformalCurvatureDampedNonlinearity_hasDerivAt B lam t).differentiableAt)
  intro t
  rw [(conformalCurvatureDampedNonlinearity_hasDerivAt B lam t).deriv]
  have hd := conformalCurvatureNonlinearity_deriv_mem_Icc hB t
  exact_mod_cast (show ‖lam - deriv (conformalCurvatureNonlinearity B) t‖ ≤ lam - 1 by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hd.2])]
    linarith [hd.1])

#print axioms conformalCurvatureNonlinearity_eq_exp
#print axioms conformalCurvatureNonlinearity_contDiff
#print axioms conformalCurvatureNonlinearity_deriv_mem_Icc
#print axioms conformalCurvatureNonlinearity_lipschitz
#print axioms conformalCurvatureNonlinearity_second_deriv_mem_Icc
#print axioms conformalCurvatureNonlinearity_strictMono
#print axioms conformalCurvatureDampedNonlinearity_lipschitz

end

end SystolicGrowth
