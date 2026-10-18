module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

/-!
# The actual weighted derivative in a smooth surface chart

A smooth weight supported inside a genuine chart makes the coordinate
derivative a globally smooth function, even though the coordinate inverse
is only smooth on its target. Dividing by the positive conformal coefficient
gives one orthonormal component of the gradient. The construction is linear
in the original smooth function; no global tangent frame is needed.
-/

open Set Manifold IsManifold
open scoped ContDiff

namespace SystolicGrowth

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

theorem smoothFunction_contDiffOn_chart_inverse
    (e : OpenPartialHomeomorph M ℂ)
    (he : e ∈ maximalAtlas 𝓘(ℝ, ℂ) ∞ M)
    (f : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) :
    ContDiffOn ℝ ∞ (fun z => f (e.symm z)) e.target :=
  (f.contMDiff.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas he)).contDiffOn

/-- The literal weighted coordinate derivative, defined on the original carrier. -/
def weightedChartDerivative (e : OpenPartialHomeomorph M ℂ)
    (a : ℂ → ℝ) (τ : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (v : ℂ)
    (f : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (x : M) : ℝ :=
  τ x * ((a (e x))⁻¹ * (fderiv ℝ (fun z => f (e.symm z)) (e x)) v)

/-- Support containment is sufficient for smooth zero-extension of the
weighted derivative across the boundary of its coordinate chart. -/
theorem weightedChartDerivative_contMDiff
    (e : OpenPartialHomeomorph M ℂ)
    (he : e ∈ maximalAtlas 𝓘(ℝ, ℂ) ∞ M)
    (a : ℂ → ℝ) (ha : ContDiffOn ℝ ∞ a e.target)
    (hapos : ∀ z ∈ e.target, 0 < a z)
    (τ : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (hτ : tsupport τ ⊆ e.source)
    (v : ℂ) (f : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (weightedChartDerivative e a τ v f) := by
  apply contMDiff_of_tsupport
  intro x hx
  have hxτ : x ∈ tsupport τ := tsupport_mul_subset_left hx
  have hxe : x ∈ e.source := hτ hxτ
  have htarget := e.map_source hxe
  have hchart := contMDiffAt_of_mem_maximalAtlas he hxe
  have hfa := smoothFunction_contDiffOn_chart_inverse e he f
  have hderiv := hfa.fderiv_of_isOpen e.open_target (show ∞ + 1 ≤ ∞ by simp)
  have hderivAt := hderiv.contDiffAt (e.open_target.mem_nhds htarget)
  have hcoordinate := hderivAt.comp_contMDiffAt hchart
  have happly := hcoordinate.clm_apply (contMDiffAt_const (c := v))
  have hac := (ha.contDiffAt (e.open_target.mem_nhds htarget)).comp_contMDiffAt hchart
  exact (τ.contMDiff x).mul ((hac.inv₀ (hapos _ htarget).ne').mul happly)

theorem weightedChartDerivative_add
    (e : OpenPartialHomeomorph M ℂ)
    (he : e ∈ maximalAtlas 𝓘(ℝ, ℂ) ∞ M)
    (a : ℂ → ℝ) (τ : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (hτ : tsupport τ ⊆ e.source)
    (v : ℂ) (f g : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (x : M) :
    weightedChartDerivative e a τ v (f + g) x =
      weightedChartDerivative e a τ v f x + weightedChartDerivative e a τ v g x := by
  by_cases hx : x ∈ e.source
  · have hf := ((smoothFunction_contDiffOn_chart_inverse e he f).contDiffAt
      (e.open_target.mem_nhds (e.map_source hx))).differentiableAt (by simp)
    have hg := ((smoothFunction_contDiffOn_chart_inverse e he g).contDiffAt
      (e.open_target.mem_nhds (e.map_source hx))).differentiableAt (by simp)
    change τ x * ((a (e x))⁻¹ * (fderiv ℝ
      ((fun z => f (e.symm z)) + (fun z => g (e.symm z))) (e x)) v) = _
    rw [fderiv_add hf hg]
    simp only [weightedChartDerivative, add_apply]
    ring
  · have hz : τ x = 0 := by
      by_contra hn
      exact hx (hτ (subset_closure hn))
    simp [weightedChartDerivative, hz]

theorem weightedChartDerivative_smul
    (e : OpenPartialHomeomorph M ℂ)
    (he : e ∈ maximalAtlas 𝓘(ℝ, ℂ) ∞ M)
    (a : ℂ → ℝ) (τ : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (hτ : tsupport τ ⊆ e.source)
    (v : ℂ) (r : ℝ) (f : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (x : M) :
    weightedChartDerivative e a τ v (r • f) x =
      r * weightedChartDerivative e a τ v f x := by
  by_cases hx : x ∈ e.source
  · have hf := ((smoothFunction_contDiffOn_chart_inverse e he f).contDiffAt
      (e.open_target.mem_nhds (e.map_source hx))).differentiableAt (by simp)
    change τ x * ((a (e x))⁻¹ * (fderiv ℝ
      (r • (fun z => f (e.symm z))) (e x)) v) = _
    rw [fderiv_const_smul hf]
    simp only [weightedChartDerivative, smul_apply, smul_eq_mul]
    ring
  · have hz : τ x = 0 := by
      by_contra hn
      exact hx (hτ (subset_closure hn))
    simp [weightedChartDerivative, hz]

/-- The actual linear smooth-function gradient component in a supported chart. -/
def weightedChartDerivativeLinear
    (e : OpenPartialHomeomorph M ℂ)
    (he : e ∈ maximalAtlas 𝓘(ℝ, ℂ) ∞ M)
    (a : ℂ → ℝ) (ha : ContDiffOn ℝ ∞ a e.target)
    (hapos : ∀ z ∈ e.target, 0 < a z)
    (τ : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (hτ : tsupport τ ⊆ e.source) (v : ℂ) :
    C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯ where
  toFun f := ⟨weightedChartDerivative e a τ v f,
    weightedChartDerivative_contMDiff e he a ha hapos τ hτ v f⟩
  map_add' f g := by
    ext x
    exact weightedChartDerivative_add e he a τ hτ v f g x
  map_smul' r f := by
    ext x
    exact weightedChartDerivative_smul e he a τ hτ v r f x

/-- The literal chain rule for the supported conformal gradient component.
It is valid also outside the chart because the weight vanishes there. -/
theorem weightedChartDerivative_comp_scalar
    (e : OpenPartialHomeomorph M ℂ)
    (he : e ∈ maximalAtlas 𝓘(ℝ, ℂ) ∞ M)
    (a : ℂ → ℝ) (τ : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (hτ : tsupport τ ⊆ e.source)
    (v : ℂ) (f : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (x : M) :
    weightedChartDerivative e a τ v
      ⟨fun y => φ (f y), hφ.comp_contMDiff f.contMDiff⟩ x =
        deriv φ (f x) * weightedChartDerivative e a τ v f x := by
  by_cases hx : x ∈ e.source
  · have hf := ((smoothFunction_contDiffOn_chart_inverse e he f).contDiffAt
      (e.open_target.mem_nhds (e.map_source hx))).differentiableAt (by simp)
    have hp := ((hφ.differentiable (by simp)) (f (e.symm (e x)))).hasDerivAt
    have hc := hp.comp_hasFDerivAt (e x) hf.hasFDerivAt
    simp only [Function.comp_def] at hc
    change τ x * ((a (e x))⁻¹ *
      (fderiv ℝ (fun z => φ (f (e.symm z))) (e x)) v) = _
    rw [hc.fderiv]
    simp only [smul_apply, smul_eq_mul, weightedChartDerivative, e.left_inv hx]
    ring
  · have hz : τ x = 0 := by
      by_contra hn
      exact hx (hτ (subset_closure hn))
    simp [weightedChartDerivative, hz]

#print axioms weightedChartDerivative_contMDiff
#print axioms weightedChartDerivative_add
#print axioms weightedChartDerivative_smul
#print axioms weightedChartDerivativeLinear
#print axioms weightedChartDerivative_comp_scalar

end

end SystolicGrowth
