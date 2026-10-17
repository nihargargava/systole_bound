module

public import Geometry.ConformalGradientGraph
public import Geometry.ClosedGradientGraphRealChainRule

@[expose] public section

/-!
# First scalar chain rule in the conformal gradient graph

The rule is obtained from literal smooth weighted-coordinate derivatives,
strong `L²` approximation, an a.e.-convergent subsequence, and closure of
the original graph.
-/

open MeasureTheory Filter Set Manifold IsManifold
open scoped ContDiff Topology RealInnerProductSpace

namespace SystolicGrowth

noncomputable section

variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Fintype ι]
  (μ : Measure M) [IsFiniteMeasure μ]

def Internal.ConformalGradientFirstChainRuleHelpers.smoothScalarComp
    (f : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯ :=
  ⟨fun x => φ (f x), hφ.comp_contMDiff f.contMDiff⟩

private theorem smoothScalarComp_gradient_ae
    (A : ConformalGradientAtlas M ι)
    (f : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (i : ι) (j : Fin 2) :
    conformalSmoothGradient μ A (Internal.ConformalGradientFirstChainRuleHelpers.smoothScalarComp f φ hφ) (i, j) =ᵐ[μ]
      fun x => deriv φ ((smoothFunctionToL2 μ f) x) *
        (conformalSmoothGradient μ A f (i, j)) x := by
  have hf := smoothFunctionToL2_coeFn μ f
  have hdf := conformalGradientComponent_coeFn μ A f i j
  have hdc := conformalGradientComponent_coeFn μ A (Internal.ConformalGradientFirstChainRuleHelpers.smoothScalarComp f φ hφ) i j
  filter_upwards [hf, hdf, hdc] with x hx hdx hdcx
  change (conformalGradientComponent μ A i j (Internal.ConformalGradientFirstChainRuleHelpers.smoothScalarComp f φ hφ)) x = _ at hdcx
  change (conformalGradientComponent μ A i j f) x = _ at hdx
  change (conformalGradientComponent μ A i j (Internal.ConformalGradientFirstChainRuleHelpers.smoothScalarComp f φ hφ)) x = _
  rw [hdcx, hx]
  change weightedChartDerivative (A.chart i) (A.coefficient i) (A.weight i)
    (if j = 0 then 1 else Complex.I) (Internal.ConformalGradientFirstChainRuleHelpers.smoothScalarComp f φ hφ) x =
    deriv φ (f x) * (conformalGradientComponent μ A i j f) x
  rw [hdx]
  exact weightedChartDerivative_comp_scalar (A.chart i) (A.chart_mem i)
    (A.coefficient i) (A.weight i) (A.weight_support i)
    (if j = 0 then 1 else Complex.I) f φ hφ x

omit [TopologicalSpace M] [ChartedSpace ℂ M] [BorelSpace M]
  [CompactSpace M] [IsFiniteMeasure μ] in
private theorem smoothScalarComp_memLp
    (u : Lp ℝ 2 μ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hφ0 : φ 0 = 0) (C : ℝ)
    (hLip : ∀ x y, ‖φ x - φ y‖ ≤ C * ‖x - y‖) :
    MemLp (fun x => φ (u x)) 2 μ := by
  refine (Lp.memLp u).of_le_mul (c := C)
    (hφ.continuous.comp_aestronglyMeasurable (Lp.memLp u).aestronglyMeasurable) ?_
  apply Filter.Eventually.of_forall
  intro x
  simpa only [hφ0, sub_zero] using hLip (u x) 0

omit [TopologicalSpace M] [ChartedSpace ℂ M] [BorelSpace M]
  [CompactSpace M] [IsFiniteMeasure μ] in
private theorem smoothScalarDerivMul_memLp
    (u g : Lp ℝ 2 μ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (C : ℝ) (hderiv : ∀ t, ‖deriv φ t‖ ≤ C) :
    MemLp (fun x => deriv φ (u x) * g x) 2 μ := by
  have hc : AEStronglyMeasurable (fun x => deriv φ (u x)) μ :=
    (hφ.continuous_deriv (by simp)).comp_aestronglyMeasurable
      (Lp.memLp u).aestronglyMeasurable
  refine (Lp.memLp g).of_le_mul (c := C)
    (hc.mul (Lp.memLp g).aestronglyMeasurable) ?_
  apply Filter.Eventually.of_forall
  intro x
  simpa only [norm_mul] using
    mul_le_mul_of_nonneg_right (hderiv (u x)) (norm_nonneg (g x))

private theorem smoothScalarComp_value_tendsto
    (f : ℕ → C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (u : Lp ℝ 2 μ)
    (hu : Tendsto (fun n => smoothFunctionToL2 μ (f n)) atTop (𝓝 u))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hφ0 : φ 0 = 0) (C : ℝ) (hC : 0 ≤ C)
    (hLip : ∀ x y, ‖φ x - φ y‖ ≤ C * ‖x - y‖) :
    Tendsto (fun n => smoothFunctionToL2 μ (Internal.ConformalGradientFirstChainRuleHelpers.smoothScalarComp (f n) φ hφ))
      atTop (𝓝 ((smoothScalarComp_memLp μ u φ hφ hφ0 C hLip).toLp
        (fun x => φ (u x)))) := by
  let hU := smoothScalarComp_memLp μ u φ hφ hφ0 C hLip
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm _ _ hU).2
  have hdiff : Tendsto
      (fun n => eLpNorm (fun x => (smoothFunctionToL2 μ (f n)) x - u x) 2 μ)
      atTop (𝓝 0) := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ u).1 hu
  have hcomp := tendsto_eLpNorm_two_lipschitz_comp_sub μ φ
    (fun n x => (smoothFunctionToL2 μ (f n)) x) (fun x => u x)
    C hC hLip (fun n => (Lp.memLp (smoothFunctionToL2 μ (f n))).aestronglyMeasurable)
    (Lp.memLp u).aestronglyMeasurable hdiff
  convert hcomp using 1
  funext n
  apply eLpNorm_congr_ae
  filter_upwards [smoothFunctionToL2_coeFn μ (f n),
    smoothFunctionToL2_coeFn μ (Internal.ConformalGradientFirstChainRuleHelpers.smoothScalarComp (f n) φ hφ)] with x hfx hcx
  simp only [Pi.sub_apply]
  rw [hcx, hfx]
  rfl

private theorem smoothScalarComp_gradient_component_tendsto
    (A : ConformalGradientAtlas M ι)
    (f : ℕ → C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯)
    (u : Lp ℝ 2 μ)
    (du : PiLp 2 (fun _ : ι × Fin 2 => Lp ℝ 2 μ))
    (hvalueAE : ∀ᵐ x ∂μ,
      Tendsto (fun n => (smoothFunctionToL2 μ (f n)) x) atTop (𝓝 (u x)))
    (hgrad : Tendsto (fun n => conformalSmoothGradient μ A (f n))
      atTop (𝓝 du))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀ t, ‖deriv φ t‖ ≤ C) (i : ι) (j : Fin 2) :
    Tendsto (fun n => conformalSmoothGradient μ A
      (Internal.ConformalGradientFirstChainRuleHelpers.smoothScalarComp (f n) φ hφ) (i, j)) atTop
      (𝓝 ((smoothScalarDerivMul_memLp μ u (du (i, j)) φ hφ C hderiv).toLp
        (fun x => deriv φ (u x) * (du (i, j)) x))) := by
  let hD := smoothScalarDerivMul_memLp μ u (du (i, j)) φ hφ C hderiv
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm _ _ hD).2
  have ha (n : ℕ) : AEStronglyMeasurable
      (fun x => deriv φ ((smoothFunctionToL2 μ (f n)) x)) μ :=
    (hφ.continuous_deriv (by simp)).comp_aestronglyMeasurable
      (Lp.memLp (smoothFunctionToL2 μ (f n))).aestronglyMeasurable
  have hb : AEStronglyMeasurable (fun x => deriv φ (u x)) μ :=
    (hφ.continuous_deriv (by simp)).comp_aestronglyMeasurable
      (Lp.memLp u).aestronglyMeasurable
  have hg (n : ℕ) : AEStronglyMeasurable
      (fun x => (conformalSmoothGradient μ A (f n) (i, j)) x) μ :=
    (Lp.memLp _).aestronglyMeasurable
  have haC (n : ℕ) : ∀ᵐ x ∂μ,
      ‖deriv φ ((smoothFunctionToL2 μ (f n)) x)‖ ≤ C :=
    Filter.Eventually.of_forall fun x => hderiv _
  have hbC : ∀ᵐ x ∂μ, ‖deriv φ (u x)‖ ≤ C :=
    Filter.Eventually.of_forall fun x => hderiv _
  have halim : ∀ᵐ x ∂μ,
      Tendsto (fun n => deriv φ ((smoothFunctionToL2 μ (f n)) x))
        atTop (𝓝 (deriv φ (u x))) := by
    filter_upwards [hvalueAE] with x hx
    exact ((hφ.continuous_deriv (by simp)).tendsto (u x)).comp hx
  have hgLp : Tendsto
      (fun n => conformalSmoothGradient μ A (f n) (i, j))
      atTop (𝓝 (du (i, j))) :=
    ((PiLp.continuous_apply (p := 2) (β := fun _ : ι × Fin 2 => Lp ℝ 2 μ)
      (i, j)).tendsto du).comp hgrad
  have hglim : Tendsto
      (fun n => eLpNorm (fun x =>
        (conformalSmoothGradient μ A (f n) (i, j)) x - (du (i, j)) x) 2 μ)
      atTop (𝓝 0) := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 hgLp
  have hlim := tendsto_eLpNorm_two_bounded_coeff_varying_mul_real μ
    (fun n x => deriv φ ((smoothFunctionToL2 μ (f n)) x))
    (fun x => deriv φ (u x))
    (fun n x => (conformalSmoothGradient μ A (f n) (i, j)) x)
    (fun x => (du (i, j)) x) C ha hb hg (Lp.memLp _) hC haC hbC halim hglim
  convert hlim using 1
  funext n
  apply eLpNorm_congr_ae
  filter_upwards [smoothScalarComp_gradient_ae μ A (f n) φ hφ i j] with x hx
  simp only [Pi.sub_apply]
  rw [hx]

/-- The first scalar chain rule for the actual completed weighted-coordinate
gradient graph. Both the composed value and its coordinate derivatives are
identified as `L²` functions; no weak-chain-rule or regularity conclusion is
assumed. The Lipschitz bound is an ordinary scalar calculus hypothesis. -/
theorem conformalGradientH1_comp_smooth_bounded_deriv
    (A : ConformalGradientAtlas M ι) (v : ConformalGradientH1 μ A)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφ0 : φ 0 = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hLip : ∀ x y, ‖φ x - φ y‖ ≤ C * ‖x - y‖)
    (hderiv : ∀ t, ‖deriv φ t‖ ≤ C) :
    ∃ w : ConformalGradientH1 μ A,
      conformalH1Value μ A w =ᵐ[μ]
        (fun x => φ ((conformalH1Value μ A v) x)) ∧
      ∀ i : ι, ∀ j : Fin 2,
        conformalH1Gradient μ A w (i, j) =ᵐ[μ]
          (fun x => deriv φ ((conformalH1Value μ A v) x) *
            (conformalH1Gradient μ A v (i, j)) x) := by
  let u : Lp ℝ 2 μ := conformalH1Value μ A v
  let du : PiLp 2 (fun _ : ι × Fin 2 => Lp ℝ 2 μ) :=
    conformalH1Gradient μ A v
  obtain ⟨f, hfvalue, hfgrad⟩ :=
    closedGradientGraph_exists_smooth_approximation
      (smoothFunctionToL2 μ) (conformalSmoothGradient μ A) v
  change Tendsto (fun n => smoothFunctionToL2 μ (f n)) atTop (𝓝 u) at hfvalue
  change Tendsto (fun n => conformalSmoothGradient μ A (f n)) atTop (𝓝 du) at hfgrad
  obtain ⟨ns, -, hae, hvalue, hgrad⟩ :=
    lp_two_ae_subsequence_preserves_graph_limit μ
      (fun n => smoothFunctionToL2 μ (f n)) u
      (fun n => conformalSmoothGradient μ A (f n)) du hfvalue hfgrad
  let fs : ℕ → C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯ := fun n => f (ns n)
  have hvalue' : Tendsto (fun n => smoothFunctionToL2 μ (fs n)) atTop (𝓝 u) := hvalue
  have hgrad' : Tendsto (fun n => conformalSmoothGradient μ A (fs n))
      atTop (𝓝 du) := hgrad
  have hae' : ∀ᵐ x ∂μ,
      Tendsto (fun n => (smoothFunctionToL2 μ (fs n)) x) atTop (𝓝 (u x)) := hae
  let U : Lp ℝ 2 μ :=
    (smoothScalarComp_memLp μ u φ hφ hφ0 C hLip).toLp (fun x => φ (u x))
  let Dfun : ι × Fin 2 → Lp ℝ 2 μ := fun ij =>
    (smoothScalarDerivMul_memLp μ u (du ij) φ hφ C hderiv).toLp
      (fun x => deriv φ (u x) * (du ij) x)
  let D : PiLp 2 (fun _ : ι × Fin 2 => Lp ℝ 2 μ) := WithLp.toLp 2 Dfun
  have hcompvalue : Tendsto
      (fun n => smoothFunctionToL2 μ (Internal.ConformalGradientFirstChainRuleHelpers.smoothScalarComp (fs n) φ hφ))
      atTop (𝓝 U) :=
    smoothScalarComp_value_tendsto μ fs u hvalue' φ hφ hφ0 C hC hLip
  have hpoint : Tendsto
      (fun n : ℕ => fun ij : ι × Fin 2 =>
        conformalSmoothGradient μ A (Internal.ConformalGradientFirstChainRuleHelpers.smoothScalarComp (fs n) φ hφ) ij)
      atTop (𝓝 Dfun) := by
    apply tendsto_pi_nhds.mpr
    rintro ⟨i, j⟩
    exact smoothScalarComp_gradient_component_tendsto μ A fs u du hae' hgrad'
      φ hφ C hC hderiv i j
  have hcompgrad : Tendsto
      (fun n => conformalSmoothGradient μ A (Internal.ConformalGradientFirstChainRuleHelpers.smoothScalarComp (fs n) φ hφ))
      atTop (𝓝 D) := by
    have ht := ((PiLp.continuous_toLp 2
      (fun _ : ι × Fin 2 => Lp ℝ 2 μ)).tendsto Dfun).comp hpoint
    have heq :
        (fun n => WithLp.toLp 2 (fun ij : ι × Fin 2 =>
          conformalSmoothGradient μ A (Internal.ConformalGradientFirstChainRuleHelpers.smoothScalarComp (fs n) φ hφ) ij)) =
        (fun n => conformalSmoothGradient μ A (Internal.ConformalGradientFirstChainRuleHelpers.smoothScalarComp (fs n) φ hφ)) := by
      funext n
      change WithLp.toLp 2
        ((conformalSmoothGradient μ A (Internal.ConformalGradientFirstChainRuleHelpers.smoothScalarComp (fs n) φ hφ)).ofLp) = _
      exact WithLp.toLp_ofLp 2 _
    change Tendsto (fun n => WithLp.toLp 2 (fun ij : ι × Fin 2 =>
      conformalSmoothGradient μ A (Internal.ConformalGradientFirstChainRuleHelpers.smoothScalarComp (fs n) φ hφ) ij))
      atTop (𝓝 D) at ht
    rw [heq] at ht
    exact ht
  obtain ⟨w, hwvalue, hwgrad⟩ :=
    closedGradientGraph_exists_of_smooth_tendsto
      (smoothFunctionToL2 μ) (conformalSmoothGradient μ A)
      (fun n => Internal.ConformalGradientFirstChainRuleHelpers.smoothScalarComp (fs n) φ hφ) U D hcompvalue hcompgrad
  refine ⟨w, ?_, ?_⟩
  · change (conformalH1Value μ A w) =ᵐ[μ] (fun x => φ (u x))
    rw [show conformalH1Value μ A w = U from hwvalue]
    exact (smoothScalarComp_memLp μ u φ hφ hφ0 C hLip).coeFn_toLp
  · intro i j
    change (conformalH1Gradient μ A w (i, j)) =ᵐ[μ]
      (fun x => deriv φ (u x) * (du (i, j)) x)
    rw [show conformalH1Gradient μ A w = D from hwgrad]
    exact (smoothScalarDerivMul_memLp μ u (du (i, j)) φ hφ C hderiv).coeFn_toLp

#print axioms smoothScalarComp_gradient_ae
#print axioms smoothScalarComp_memLp
#print axioms smoothScalarDerivMul_memLp
#print axioms conformalGradientH1_comp_smooth_bounded_deriv

end

end SystolicGrowth
