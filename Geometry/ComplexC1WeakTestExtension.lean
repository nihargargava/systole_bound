module

public import Geometry.ComplexC1CompactMollification
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# Extending weak derivatives to compactly supported `C¹` tests

Normalized convolution approximates both a compact `C¹` test and its
classical derivative. The support remains inside one fixed compact set;
this permits dominated convergence against an arbitrary `L²` weak field.
-/

open Set Function Filter MeasureTheory TemperedDistribution ContinuousLinearMap
open scoped ContDiff Topology Convolution LineDeriv SchwartzMap Pointwise

namespace SystolicGrowth

noncomputable section

/-- Dominated convergence against a genuine global `L²` field when
approximating multipliers are uniformly bounded and share a compact
support. This is the analytic limit step in the `C¹`-test extension. -/
theorem complex_tendsto_integral_mul_L2_of_uniform_compact
    (g : Lp ℂ 2 (volume : Measure ℂ)) (K : Set ℂ) (hK : IsCompact K)
    (ψ : ℕ → ℂ → ℂ) (hψcont : ∀ n, Continuous (ψ n))
    (hψsupp : ∀ n, support (ψ n) ⊆ K)
    (C : ℝ) (hψbound : ∀ n z, ‖ψ n z‖ ≤ C)
    (ψlim : ℂ → ℂ) (hψlim : ∀ z, Tendsto (fun n => ψ n z) atTop (𝓝 (ψlim z))) :
    Tendsto (fun n => ∫ z, ψ n z * g z) atTop
      (𝓝 (∫ z, ψlim z * g z)) := by
  letI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by simpa using hK.measure_lt_top (μ := (volume : Measure ℂ))⟩
  have hgInt : Integrable (fun z => g z) (volume.restrict K) :=
    ((Lp.memLp g).restrict K).integrable (by norm_num)
  have hboundInt : Integrable (K.indicator (fun z => C * ‖g z‖)) volume :=
    (integrable_indicator_iff hK.measurableSet).mpr (hgInt.norm.const_mul C)
  apply tendsto_integral_of_dominated_convergence
    (bound := K.indicator (fun z => C * ‖g z‖))
  · intro n
    exact (hψcont n).aestronglyMeasurable.mul (Lp.memLp g).aestronglyMeasurable
  · exact hboundInt
  · intro n
    apply Filter.Eventually.of_forall
    intro z
    by_cases hz : z ∈ K
    · rw [Set.indicator_of_mem hz, norm_mul]
      exact mul_le_mul_of_nonneg_right (hψbound n z) (norm_nonneg _)
    · have hzero : ψ n z = 0 := by
        by_contra hh
        exact hz (hψsupp n hh)
      simp [Set.indicator_of_notMem hz, hzero]
  · apply Filter.Eventually.of_forall
    intro z
    exact (hψlim z).mul tendsto_const_nhds

/-- A common compact support for every mollification of a given compact
test. The fixed unit ball contains every shrinking bump support. -/
def complexMollifyCommonSupport (f : ℂ → ℂ) : Set ℂ :=
  tsupport f + Metric.closedBall 0 1

theorem complexMollifyCommonSupport_isCompact (f : ℂ → ℂ)
    (hf : HasCompactSupport f) :
    IsCompact (complexMollifyCommonSupport f) := by
  exact hf.isCompact.add (isCompact_closedBall 0 1)

theorem complexMollify_tsupport_subset_common (f : ℂ → ℂ)
    (hf : HasCompactSupport f) (n : ℕ) :
    tsupport (complexMollify n f) ⊆ complexMollifyCommonSupport f := by
  have hrad : (2 : ℝ) / ((n : ℝ) + 2) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).2
    norm_num
  have hb : tsupport ((complexShrinkingBump n).normed volume) ⊆
      Metric.closedBall (0 : ℂ) 1 := by
    rw [(complexShrinkingBump n).tsupport_normed_eq]
    intro x hx
    exact Metric.closedBall_subset_closedBall
      (by simpa only [complexShrinkingBump] using hrad) hx
  have hsub : support (complexMollify n f) ⊆ complexMollifyCommonSupport f := by
    exact (support_convolution_subset_swap (lsmul ℝ ℝ)).trans
      (Set.add_subset_add (subset_tsupport f)
        ((subset_tsupport ((complexShrinkingBump n).normed volume)).trans hb))
  exact closure_minimal hsub (complexMollifyCommonSupport_isCompact f hf).isClosed

theorem complexMollify_fderiv_eq_convolution
    (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (n : ℕ) (x : ℂ) :
    fderiv ℝ (complexMollify n f) x =
      ((complexShrinkingBump n).normed volume ⋆[
        lsmul ℝ ℝ, volume] fderiv ℝ f) x := by
  have h := (complexMollify_hasFDerivAt f hf hfc n x).fderiv
  convert h using 1
  simp only [MeasureTheory.convolution]
  congr 1

/-- The classical derivatives of every mollification are uniformly bounded
by the bound of the original derivative. -/
theorem complexMollify_fderiv_norm_le
    (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (C : ℝ) (hC : ∀ x, ‖fderiv ℝ f x‖ ≤ C) (n : ℕ) (x : ℂ) :
    ‖fderiv ℝ (complexMollify n f) x‖ ≤ 3 * C := by
  have hD : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hdist (y : ℂ) (_ : y ∈ Metric.ball x (complexShrinkingBump n).rOut) :
      dist (fderiv ℝ f y) (fderiv ℝ f x) ≤ 2 * C := by
    calc
      dist (fderiv ℝ f y) (fderiv ℝ f x) =
          ‖fderiv ℝ f y - fderiv ℝ f x‖ := dist_eq_norm _ _
      _ ≤ ‖fderiv ℝ f y‖ + ‖fderiv ℝ f x‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (hC y) (hC x)
      _ = 2 * C := by ring
  have hd := (complexShrinkingBump n).dist_normed_convolution_le
    (μ := volume) hD.aestronglyMeasurable hdist
  rw [← complexMollify_fderiv_eq_convolution f hf hfc n x] at hd
  calc
    ‖fderiv ℝ (complexMollify n f) x‖ ≤
        dist (fderiv ℝ (complexMollify n f) x) (fderiv ℝ f x) +
          ‖fderiv ℝ f x‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using
        norm_add_le (fderiv ℝ (complexMollify n f) x - fderiv ℝ f x)
          (fderiv ℝ f x)
    _ ≤ 2 * C + C := add_le_add hd (hC x)
    _ = 3 * C := by ring

theorem complexMollify_deriv_tsupport_subset_common
    (f : ℂ → ℂ) (hfc : HasCompactSupport f)
    (n : ℕ) (v : ℂ) :
    tsupport (fun z => fderiv ℝ (complexMollify n f) z v) ⊆
      complexMollifyCommonSupport f :=
  (tsupport_fderiv_apply_subset ℝ v).trans
    (complexMollify_tsupport_subset_common f hfc n)

private theorem complex_compact_contDiff_one_exists_bound
    (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) :
    ∃ C : ℝ, (∀ x, ‖f x‖ ≤ C) ∧
      (∀ x, ‖fderiv ℝ f x‖ ≤ C) := by
  obtain ⟨x₀, hx₀⟩ := hf.continuous.norm.exists_forall_ge_of_hasCompactSupport hfc.norm
  obtain ⟨x₁, hx₁⟩ :=
    (hf.continuous_fderiv (by norm_num)).norm.exists_forall_ge_of_hasCompactSupport
      (hfc.fderiv ℝ).norm
  refine ⟨max ‖f x₀‖ ‖fderiv ℝ f x₁‖, ?_, ?_⟩
  · intro x
    exact (hx₀ x).trans (le_max_left _ _)
  · intro x
    exact (hx₁ x).trans (le_max_right _ _)

/-- A global `L²` weak derivative identity, established on smooth compact
tests, holds for every compactly supported `C¹` test. The proof mollifies
the test, preserves one compact support and uniform bounds, and passes both
integrals by dominated convergence. -/
theorem complex_L2_weak_lineDeriv_test_contDiff_one
    (F G : Lp ℂ 2 (volume : Measure ℂ)) (v : ℂ)
    (hweak : ∀ φ : ℂ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ z, φ z * G z) = -(∫ z, fderiv ℝ φ z v * F z))
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) :
    (∫ z, ψ z * G z) = -(∫ z, fderiv ℝ ψ z v * F z) := by
  obtain ⟨C, hCvalue, hCderiv⟩ :=
    complex_compact_contDiff_one_exists_bound ψ hψ hψc
  let K := complexMollifyCommonSupport ψ
  have hK : IsCompact K := complexMollifyCommonSupport_isCompact ψ hψc
  have hL : Tendsto (fun n => ∫ z, complexMollify n ψ z * G z) atTop
      (𝓝 (∫ z, ψ z * G z)) := by
    apply complex_tendsto_integral_mul_L2_of_uniform_compact G K hK
      (fun n => complexMollify n ψ)
      (C := 3 * C) (ψlim := ψ)
    · intro n
      exact (complexMollify_smooth ψ hψ.continuous.locallyIntegrable n).continuous
    · intro n
      exact (subset_tsupport _).trans
        (complexMollify_tsupport_subset_common ψ hψc n)
    · intro n z
      exact complexMollify_norm_le ψ hψ.continuous C hCvalue n z
    · intro z
      exact complexMollify_tendsto ψ hψ.continuous z
  have hDcont (n : ℕ) :
      Continuous (fun z => fderiv ℝ (complexMollify n ψ) z v) :=
    ((complexMollify_smooth ψ hψ.continuous.locallyIntegrable n).fderiv_right
      (show (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) by simp)).clm_apply contDiff_const |>.continuous
  have hR : Tendsto (fun n => ∫ z,
      fderiv ℝ (complexMollify n ψ) z v * F z) atTop
      (𝓝 (∫ z, fderiv ℝ ψ z v * F z)) := by
    apply complex_tendsto_integral_mul_L2_of_uniform_compact F K hK
      (fun n z => fderiv ℝ (complexMollify n ψ) z v)
      (C := 3 * C * ‖v‖) (ψlim := fun z => fderiv ℝ ψ z v)
    · exact hDcont
    · intro n
      exact (subset_tsupport _).trans
        (complexMollify_deriv_tsupport_subset_common ψ hψc n v)
    · intro n z
      calc
        ‖fderiv ℝ (complexMollify n ψ) z v‖ ≤
            ‖fderiv ℝ (complexMollify n ψ) z‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ 3 * C * ‖v‖ :=
          mul_le_mul_of_nonneg_right
            (complexMollify_fderiv_norm_le ψ hψ hψc C hCderiv n z)
            (norm_nonneg _)
    · intro z
      exact ((continuous_eval_const v).tendsto (fderiv ℝ ψ z)).comp
        (complexMollify_fderiv_tendsto ψ hψ hψc z)
  have hL' : Tendsto (fun n => -(∫ z,
      fderiv ℝ (complexMollify n ψ) z v * F z)) atTop
      (𝓝 (∫ z, ψ z * G z)) := by
    apply hL.congr'
    apply Filter.Eventually.of_forall
    intro n
    exact hweak (complexMollify n ψ)
      (complexMollify_smooth ψ hψ.continuous.locallyIntegrable n)
      (complexMollify_compact ψ hψc n)
  exact tendsto_nhds_unique hL' hR.neg

/-- The distributional derivative identity itself supplies the smooth-test
premise of the `C¹` extension. -/
theorem complex_L2_lineDeriv_test_contDiff_one
    (F G : Lp ℂ 2 (volume : Measure ℂ)) (v : ℂ)
    (hderiv : ∂_{v} (F : 𝓢'(ℂ, ℂ)) = (G : 𝓢'(ℂ, ℂ)))
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) :
    (∫ z, ψ z * G z) = -(∫ z, fderiv ℝ ψ z v * F z) := by
  apply complex_L2_weak_lineDeriv_test_contDiff_one F G v ?_ ψ hψ hψc
  intro φ hφ hφc
  let s : 𝓢(ℂ, ℂ) := hφc.toSchwartzMap hφ
  have h := congrArg (fun T : 𝓢'(ℂ, ℂ) => T s) hderiv
  rw [TemperedDistribution.lineDerivOp_apply_apply,
    Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply] at h
  have hs : (s : ℂ → ℂ) = φ := rfl
  simpa only [neg_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    hs, neg_mul, integral_neg, smul_eq_mul] using h.symm

#print axioms complex_tendsto_integral_mul_L2_of_uniform_compact
#print axioms complexMollify_tsupport_subset_common
#print axioms complexMollify_fderiv_eq_convolution
#print axioms complexMollify_fderiv_norm_le
#print axioms complex_L2_weak_lineDeriv_test_contDiff_one
#print axioms complex_L2_lineDeriv_test_contDiff_one

end

end SystolicGrowth
