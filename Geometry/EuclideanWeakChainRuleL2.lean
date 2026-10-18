module

public import Geometry.BoundedCoefficientL2Convergence

@[expose] public section

/-!
# Real `L²` limit steps for the first weak chain rule

The conformal gradient graph is real-valued. These lemmas transport the
proved complex-valued dominated convergence argument to its real function
and derivative components.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace SystolicGrowth

noncomputable section

private theorem eLpNorm_two_complex_ofReal_eq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) :
    eLpNorm (fun x => (f x : ℂ)) 2 μ = eLpNorm f 2 μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · apply eLpNorm_congr_enorm_ae
      (Complex.ofRealCLM.continuous.comp_aestronglyMeasurable hf) hf
    filter_upwards with x
    exact enorm_eq_iff_norm_eq.mpr (Complex.norm_real (f x))
  · have hc : ¬ AEStronglyMeasurable (fun x => (f x : ℂ)) μ := by
      intro hc
      apply hf
      simpa only [Function.comp_def, Complex.ofReal_re] using
        Complex.continuous_re.comp_aestronglyMeasurable hc
    rw [eLpNorm_of_not_aestronglyMeasurable hf,
      eLpNorm_of_not_aestronglyMeasurable hc]

/-- Real bounded coefficients converging a.e. converge strongly after
pairing with a fixed real `L²` function. -/
theorem tendsto_eLpNorm_two_bounded_coeff_mul_real
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (a : ℕ → α → ℝ) (b g : α → ℝ) (C : ℝ)
    (ha : ∀ n, AEStronglyMeasurable (a n) μ)
    (hb : AEStronglyMeasurable b μ)
    (hg : MemLp g 2 μ)
    (hC : 0 ≤ C)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖a n x - b x‖ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => a n x) atTop (𝓝 (b x))) :
    Tendsto (fun n => eLpNorm (fun x => (a n x - b x) * g x) 2 μ)
      atTop (𝓝 0) := by
  let F : ℕ → α → ℝ := fun n x => (a n x - b x) * g x
  let G : α → ℝ := fun x => C * g x
  have hF (n : ℕ) : AEStronglyMeasurable (fun x => (F n x : ℂ)) μ :=
    Complex.ofRealCLM.continuous.comp_aestronglyMeasurable
      (((ha n).sub hb).mul hg.aestronglyMeasurable)
  have hG : MemLp (fun x => (G x : ℂ)) 2 μ := (hg.const_mul C).ofReal
  have hdom (n : ℕ) : ∀ᵐ x ∂μ, ‖(F n x : ℂ)‖ ≤ ‖(G x : ℂ)‖ := by
    filter_upwards [hbound n] with x hx
    simpa only [F, G, Complex.norm_real, norm_mul, Real.norm_of_nonneg hC] using
      mul_le_mul_of_nonneg_right hx (norm_nonneg (g x))
  have hpoint : ∀ᵐ x ∂μ,
      Tendsto (fun n => (F n x : ℂ)) atTop (𝓝 0) := by
    filter_upwards [hlim] with x hx
    have hsub : Tendsto (fun n => a n x - b x) atTop (𝓝 0) := by
      simpa using hx.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => b x) atTop (𝓝 (b x)))
    have hmul : Tendsto (fun n => F n x) atTop (𝓝 0) := by
      simpa [F] using hsub.mul_const (g x)
    simpa only [Function.comp_def, Complex.ofRealCLM_apply, map_zero] using
      (Complex.ofRealCLM.continuous.tendsto 0).comp hmul
  have hcomplex := tendsto_eLpNorm_two_zero_of_ae_tendsto_dominated μ
    (fun n x => (F n x : ℂ)) (fun x => (G x : ℂ)) hF hG hdom hpoint
  simpa only [eLpNorm_two_complex_ofReal_eq, F] using hcomplex

/-- A globally Lipschitz scalar composition preserves strong `L²`
convergence, after subtracting the common constant value if necessary.
The measurability witnesses are explicit because the current `eLpNorm`
assigns infinity to nonmeasurable functions; the graph consumer uses actual `Lp` values. -/
theorem tendsto_eLpNorm_two_lipschitz_comp_sub
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (ψ : ℝ → ℝ) (f : ℕ → α → ℝ) (u : α → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hψ : ∀ x y, ‖ψ x - ψ y‖ ≤ C * ‖x - y‖)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hu : AEStronglyMeasurable u μ)
    (hlim : Tendsto (fun n => eLpNorm (fun x => f n x - u x) 2 μ)
      atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => ψ (f n x) - ψ (u x)) 2 μ)
      atTop (𝓝 0) := by
  have hψcont : Continuous ψ := by
    apply LipschitzWith.continuous (K := C.toNNReal)
    rw [lipschitzWith_iff_norm_sub_le]
    simpa only [Real.coe_toNNReal _ hC] using hψ
  have hbound (n : ℕ) :
      eLpNorm (fun x => ψ (f n x) - ψ (u x)) 2 μ ≤
        ENNReal.ofReal C * eLpNorm (fun x => f n x - u x) 2 μ := by
    calc
      _ ≤ eLpNorm (fun x => C * (f n x - u x)) 2 μ := by
        apply eLpNorm_mono (f := fun x => ψ (f n x) - ψ (u x)) (by
          simpa only [Pi.sub_def] using
            (hψcont.comp_aestronglyMeasurable (hf n)).sub
              (hψcont.comp_aestronglyMeasurable hu))
        intro x
        simpa only [norm_mul, Real.norm_of_nonneg hC] using hψ (f n x) (u x)
      _ = ENNReal.ofReal C * eLpNorm (fun x => f n x - u x) 2 μ := by
        change eLpNorm (C • (fun x : α => f n x - u x)) 2 μ = _
        rw [eLpNorm_const_smul]
        congr 1
        exact (ofReal_norm C).symm.trans (by rw [Real.norm_of_nonneg hC])
  have hR : Tendsto
      (fun n => ENNReal.ofReal C * eLpNorm (fun x => f n x - u x) 2 μ)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.ofReal_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hR
    (fun n => bot_le) hbound

/-- The full first-order product limit: both a bounded coefficient and its
`L²` factor may vary, with the coefficient converging a.e. and the factor
converging strongly in `L²`. -/
theorem tendsto_eLpNorm_two_bounded_coeff_varying_mul_real
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (a : ℕ → α → ℝ) (b : α → ℝ)
    (g : ℕ → α → ℝ) (h : α → ℝ) (C : ℝ)
    (ha : ∀ n, AEStronglyMeasurable (a n) μ)
    (hb : AEStronglyMeasurable b μ)
    (hg : ∀ n, AEStronglyMeasurable (g n) μ)
    (hh : MemLp h 2 μ)
    (hC : 0 ≤ C)
    (haC : ∀ n, ∀ᵐ x ∂μ, ‖a n x‖ ≤ C)
    (hbC : ∀ᵐ x ∂μ, ‖b x‖ ≤ C)
    (halim : ∀ᵐ x ∂μ, Tendsto (fun n => a n x) atTop (𝓝 (b x)))
    (hglim : Tendsto (fun n => eLpNorm (fun x => g n x - h x) 2 μ)
      atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => a n x * g n x - b x * h x) 2 μ)
      atTop (𝓝 0) := by
  have hdiff (n : ℕ) : ∀ᵐ x ∂μ, ‖a n x - b x‖ ≤ 2 * C := by
    filter_upwards [haC n, hbC] with x hax hbx
    calc
      ‖a n x - b x‖ ≤ ‖a n x‖ + ‖b x‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add hax hbx
      _ = 2 * C := by ring
  have hsecond := tendsto_eLpNorm_two_bounded_coeff_mul_real μ a b h
    (2 * C) ha hb hh (by positivity) hdiff halim
  have hfirst : Tendsto
      (fun n => ENNReal.ofReal C * eLpNorm (fun x => g n x - h x) 2 μ)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hglim (Or.inr ENNReal.ofReal_ne_top)
  have hsum : Tendsto
      (fun n => ENNReal.ofReal C * eLpNorm (fun x => g n x - h x) 2 μ +
        eLpNorm (fun x => (a n x - b x) * h x) 2 μ)
      atTop (𝓝 0) := by
    simpa using hfirst.add hsecond
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun n => bot_le)
  intro n
  have hfirstBd : eLpNorm (fun x => a n x * (g n x - h x)) 2 μ ≤
      ENNReal.ofReal C * eLpNorm (fun x => g n x - h x) 2 μ := by
    calc
      _ ≤ eLpNorm (fun x => C * (g n x - h x)) 2 μ := by
        apply eLpNorm_mono_ae (f := fun x => a n x * (g n x - h x)) (by
          simpa only [Pi.mul_def, Pi.sub_def] using
            (ha n).mul ((hg n).sub hh.aestronglyMeasurable))
        filter_upwards [haC n] with x hx
        simpa only [norm_mul, Real.norm_of_nonneg hC] using
          mul_le_mul_of_nonneg_right hx (norm_nonneg (g n x - h x))
      _ = _ := by
        change eLpNorm (C • (fun x : α => g n x - h x)) 2 μ = _
        rw [eLpNorm_const_smul]
        congr 1
        exact (ofReal_norm C).symm.trans (by rw [Real.norm_of_nonneg hC])
  calc
    eLpNorm (fun x => a n x * g n x - b x * h x) 2 μ =
        eLpNorm (fun x => a n x * (g n x - h x) + (a n x - b x) * h x) 2 μ := by
          congr 1
          funext x
          ring
    _ ≤ eLpNorm (fun x => a n x * (g n x - h x)) 2 μ +
        eLpNorm (fun x => (a n x - b x) * h x) 2 μ := by
          simpa only [Pi.add_def] using
            eLpNorm_add_le (μ := μ) (p := 2)
              (f := fun x => a n x * (g n x - h x))
              (g := fun x => (a n x - b x) * h x) (by norm_num)
    _ ≤ _ := add_le_add_left hfirstBd _

#print axioms tendsto_eLpNorm_two_bounded_coeff_mul_real
#print axioms tendsto_eLpNorm_two_lipschitz_comp_sub
#print axioms tendsto_eLpNorm_two_bounded_coeff_varying_mul_real

end

end SystolicGrowth
