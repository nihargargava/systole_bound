module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ConformalCurvatureNonlinearity
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# The genuine maximum principle for the conformal equation

The Euclidean Laplacian sign is derived from actual second derivatives at
a local extremum. Compactness supplies attained extrema; the pointwise
coordinate equation then bounds the solution and removes the globally
extended nonlinearity. No Laplacian-sign conclusion is an input.
-/

open Set Filter
open scoped Topology ContDiff

namespace SystolicGrowth

theorem conformalLocalMin_second_deriv_nonneg {f : ℝ → ℝ} {x : ℝ}
    (hmin : IsLocalMin f x) (hc : ContinuousAt f x) : 0 ≤ deriv (deriv f) x := by
  by_contra h
  have hneg : deriv (deriv f) x < 0 := lt_of_not_ge h
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [hmin, hmax] with y hymin hymax
    exact le_antisymm hymax hymin
  have hz : deriv (deriv f) x = 0 := by
    simpa only [deriv_const', deriv_const] using heq.deriv.deriv_eq
  linarith

theorem conformalLocalMax_second_deriv_nonpos {f : ℝ → ℝ} {x : ℝ}
    (hmax : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  have h := conformalLocalMin_second_deriv_nonneg hmax.neg hc.neg
  change 0 ≤ deriv (deriv (-f)) x at h
  rw [deriv.neg', deriv.fun_neg] at h
  exact neg_nonneg.mp h

/-- Restrict to a literal affine line and use the genuine second-order
chain rule to derive the Hessian sign, rather than postulating it. -/
theorem conformalLocalMin_hessian_diagonal_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hmin : IsLocalMin f x) (hf : ContDiffAt ℝ 2 f x) (d : E) :
    0 ≤ iteratedFDeriv ℝ 2 f x (fun _ => d) := by
  let line : ℝ → E := fun t => x + t • d
  have hline : ContDiff ℝ 2 line := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hline0 : line 0 = x := by simp [line]
  have hderiv (t : ℝ) : HasDerivAt line d t := by
    simpa only [line, id_eq, one_smul] using ((hasDerivAt_id t).smul_const d).const_add x
  have hd : deriv line = fun _ => d := funext fun t => (hderiv t).deriv
  have hlmin : IsLocalMin (f ∘ line) 0 := by
    apply IsLocalMin.comp_continuous (by simpa only [hline0] using hmin)
    exact hline.continuous.continuousAt
  have hnonneg := conformalLocalMin_second_deriv_nonneg hlmin
    ((show ContinuousAt f (line 0) by simpa only [hline0] using hf.continuousAt).comp
      hline.continuous.continuousAt)
  have hchain := iteratedDeriv_vcomp_two (f := line) (g := f) (x := 0)
    (by simpa only [hline0] using hf) hline.contDiffAt
  have hsecond : deriv (deriv (f ∘ line)) 0 = iteratedFDeriv ℝ 2 f x (fun _ => d) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, hline0, hd,
      deriv_const, map_zero, add_zero] using hchain
  rwa [hsecond] at hnonneg

theorem conformalLocalMin_laplacian_nonneg {f : ℂ → ℝ} {z : ℂ}
    (hmin : IsLocalMin f z) (hf : ContDiffAt ℝ 2 f z) :
    0 ≤ Laplacian.laplacian f z := by
  have h1 := conformalLocalMin_hessian_diagonal_nonneg hmin hf (1 : ℂ)
  have hI := conformalLocalMin_hessian_diagonal_nonneg hmin hf Complex.I
  have hv (d : ℂ) : (![d, d] : Fin 2 → ℂ) = fun _ => d := by
    funext i
    fin_cases i <;> rfl
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  dsimp only
  rw [hv, hv]
  exact add_nonneg h1 hI

theorem conformalLocalMax_laplacian_nonpos {f : ℂ → ℝ} {z : ℂ}
    (hmax : IsLocalMax f z) (hf : ContDiffAt ℝ 2 f z) :
    Laplacian.laplacian f z ≤ 0 := by
  have h := conformalLocalMin_laplacian_nonneg hmax.neg hf.neg
  change 0 ≤ Laplacian.laplacian (-f) z at h
  rw [InnerProductSpace.laplacian_neg] at h
  exact neg_nonneg.mp h

/-- **Math.** A classical solution of the actual local conformal equation
on a compact carrier stays in the interval where the constructed `Ψ`
equals `exp (2 * u)`. Charts are actual open partial homeomorphisms,
and the `C²` and PDE statements concern their literal coordinate functions. -/
theorem conformalCurvatureMaximumPrinciple
    {M : Type*} [TopologicalSpace M] [CompactSpace M]
    (u K : M → ℝ) (hu : Continuous u) (B : ℝ) (hB : 1 < B)
    (hK : ∀ x, K x ∈ Icc (-B) (-1 : ℝ))
    (hcharts : ∀ x : M, ∃ e : OpenPartialHomeomorph M ℂ,
      x ∈ e.source ∧ ContDiffAt ℝ 2 (u ∘ e.symm) (e x) ∧
      ∃ a : ℝ, 0 < a ∧ Laplacian.laplacian (u ∘ e.symm) (e x) =
        a ^ 2 * (K x + conformalCurvatureNonlinearity B (u x))) :
    ∀ x, u x ∈ Icc (0 : ℝ) (Real.log B / 2) := by
  intro x
  obtain ⟨xmin, _, hmin⟩ := isCompact_univ.exists_isMinOn ⟨x, mem_univ x⟩ hu.continuousOn
  obtain ⟨xmax, _, hmax⟩ := isCompact_univ.exists_isMaxOn ⟨x, mem_univ x⟩ hu.continuousOn
  have hminbound : 0 ≤ u xmin := by
    obtain ⟨e, he, hcd, a, ha, hpde⟩ := hcharts xmin
    have hcmin : IsLocalMin (u ∘ e.symm) (e xmin) := by
      apply IsLocalMin.comp_continuous
        (by simpa only [e.left_inv he] using hmin.isLocalMin (Filter.univ_mem))
      exact e.symm.continuousAt (e.map_source he)
    have hlap := conformalLocalMin_laplacian_nonneg hcmin hcd
    by_contra h
    have hneg : u xmin < 0 := lt_of_not_ge h
    have hpsi := (conformalCurvatureNonlinearity_strictMono hB) hneg
    rw [conformalCurvatureNonlinearity_zero] at hpsi
    have hsum : K xmin + conformalCurvatureNonlinearity B (u xmin) < 0 := by
      linarith [(hK xmin).2]
    have hbad := mul_neg_of_pos_of_neg (sq_pos_of_pos ha) hsum
    rw [← hpde] at hbad
    linarith
  have hmaxbound : u xmax ≤ Real.log B / 2 := by
    obtain ⟨e, he, hcd, a, ha, hpde⟩ := hcharts xmax
    have hcmax : IsLocalMax (u ∘ e.symm) (e xmax) := by
      apply IsLocalMax.comp_continuous
        (by simpa only [e.left_inv he] using hmax.isLocalMax (Filter.univ_mem))
      exact e.symm.continuousAt (e.map_source he)
    have hlap := conformalLocalMax_laplacian_nonpos hcmax hcd
    by_contra h
    have hgt : Real.log B / 2 < u xmax := lt_of_not_ge h
    have hpsi := (conformalCurvatureNonlinearity_strictMono hB) hgt
    have hb : 0 ≤ Real.log B / 2 := div_nonneg (Real.log_pos hB).le (by norm_num)
    rw [conformalCurvatureNonlinearity_eq_exp ⟨hb, le_rfl⟩,
      show 2 * (Real.log B / 2) = Real.log B by ring,
      Real.exp_log (by linarith : 0 < B)] at hpsi
    have hsum : 0 < K xmax + conformalCurvatureNonlinearity B (u xmax) := by
      linarith [(hK xmax).1]
    have hbad := mul_pos (sq_pos_of_pos ha) hsum
    rw [← hpde] at hbad
    linarith
  exact ⟨hminbound.trans (hmin (mem_univ x)), (hmax (mem_univ x)).trans hmaxbound⟩

#print axioms conformalLocalMin_hessian_diagonal_nonneg
#print axioms conformalLocalMin_laplacian_nonneg
#print axioms conformalCurvatureMaximumPrinciple

end SystolicGrowth
