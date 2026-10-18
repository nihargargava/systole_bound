module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.PerronLogDerivativeResidues
public import CookMagyar.PerronResidueJump
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

/-!
# A genuine local simple-zero Perron contour

At an explicitly given simple zero `β ≠ 0` of a nonprincipal L-function,
divide out the zero using `dslope`. The resulting entire factor is nonzero
near `β`; it provides an analytic numerator for the actual weighted
logarithmic derivative. Cauchy's formula then gives the exact local circle
integral `2πi * (-x^β/β)`.

The zero and simplicity are local premises, not assumed conclusions of a
global zero-free-region theorem. The factor `1/β` is retained exactly.
On a positive-abscissa rectangle, Cauchy--Goursat also gives the full finite
boundary identity, with either no zero or one simple real exceptional zero.
-/

open Filter Metric Set MeasureTheory intervalIntegral
open scoped Topology Interval Real

namespace SystolicGrowth.CookMagyarCircle

/-- The L-function's zero-divided entire factor; at its center it equals `L'`. -/
noncomputable def perronLFunctionZeroFactor (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (β : ℂ) : ℂ → ℂ :=
  dslope (DirichletCharacter.LFunction χ) β

/-- Nonprincipal L-functions give entire zero-divided factors. -/
theorem differentiable_perronLFunctionZeroFactor
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (β : ℂ) :
    Differentiable ℂ (perronLFunctionZeroFactor q χ β) := by
  apply differentiableOn_univ.mp
  exact (Complex.differentiableOn_dslope (s := Set.univ) (c := β) (by simp)).2
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn

/-- Dividing out an actual zero gives a global exact L-function factorization. -/
theorem sub_mul_perronLFunctionZeroFactor_eq_LFunction
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (β : ℂ)
    (hzero : DirichletCharacter.LFunction χ β = 0) (s : ℂ) :
    (s - β) * perronLFunctionZeroFactor q χ β s =
      DirichletCharacter.LFunction χ s := by
  simpa only [perronLFunctionZeroFactor, smul_eq_mul] using
    sub_smul_dslope_of_zero hzero s

/-- Differentiating the exact zero factorization gives the numerator of `L'/L`. -/
theorem deriv_LFunction_eq_zeroFactor_add_mul_deriv
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (β : ℂ)
    (hzero : DirichletCharacter.LFunction χ β = 0) (s : ℂ) :
    deriv (DirichletCharacter.LFunction χ) s =
      perronLFunctionZeroFactor q χ β s +
        (s - β) * deriv (perronLFunctionZeroFactor q χ β) s := by
  have hfactor : (fun z : ℂ => (z - β) * perronLFunctionZeroFactor q χ β z) =
      DirichletCharacter.LFunction χ := by
    funext z
    exact sub_mul_perronLFunctionZeroFactor_eq_LFunction q χ β hzero z
  rw [← hfactor]
  have hsub : DifferentiableAt ℂ (fun z : ℂ => z - β) s := by fun_prop
  rw [deriv_fun_mul hsub
    (differentiable_perronLFunctionZeroFactor q χ hχ β s),
    deriv_sub_const, deriv_id'', one_mul]

/-- The analytic extension of `(s-β)` times the actual Perron integrand. -/
noncomputable def perronSimpleZeroNumerator (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (x : ℝ) (β s : ℂ) : ℂ :=
  -((perronLFunctionZeroFactor q χ β s +
      (s - β) * deriv (perronLFunctionZeroFactor q χ β) s) /
        perronLFunctionZeroFactor q χ β s) * ((x : ℂ) ^ s / s)

/-- Simplicity ensures that the zero-divided factor is nonzero near the zero. -/
theorem eventually_perronLFunctionZeroFactor_ne_zero
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (β : ℂ)
    (hsimple : deriv (DirichletCharacter.LFunction χ) β ≠ 0) :
    ∀ᶠ s : ℂ in 𝓝 β, perronLFunctionZeroFactor q χ β s ≠ 0 := by
  have hβfactor : perronLFunctionZeroFactor q χ β β ≠ 0 := by
    simpa only [perronLFunctionZeroFactor, dslope_same] using hsimple
  exact (differentiable_perronLFunctionZeroFactor q χ hχ β).continuous.continuousAt
    |>.eventually_ne hβfactor

/-- The actual weighted numerator is analytic at any explicitly simple nonzero zero. -/
theorem analyticAt_perronSimpleZeroNumerator
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (x : ℝ) (hx : 0 < x) (β : ℂ) (hβ : β ≠ 0)
    (hsimple : deriv (DirichletCharacter.LFunction χ) β ≠ 0) :
    AnalyticAt ℂ (perronSimpleZeroNumerator q χ x β) β := by
  have hG := (differentiable_perronLFunctionZeroFactor q χ hχ β).analyticAt β
  have hGβ : perronLFunctionZeroFactor q χ β β ≠ 0 := by
    simpa only [perronLFunctionZeroFactor, dslope_same] using hsimple
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hweight : DifferentiableOn ℂ (fun s : ℂ => (x : ℂ) ^ s / s)
      ({0}ᶜ : Set ℂ) := by
    intro s hs
    have hs' : s ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hs
    have hnum : DifferentiableAt ℂ (fun z : ℂ => (x : ℂ) ^ z) s :=
      differentiableAt_id.const_cpow (.inl hxC)
    exact (hnum.div differentiableAt_id hs').differentiableWithinAt
  have hweightA := hweight.analyticAt (isOpen_compl_singleton.mem_nhds hβ)
  unfold perronSimpleZeroNumerator
  exact ((hG.fun_add ((analyticAt_id.fun_sub analyticAt_const).fun_mul hG.deriv)).div
    hG hGβ).neg.fun_mul hweightA

/-- The numerator's value at the zero is the exact weighted residue. -/
theorem perronSimpleZeroNumerator_apply_center
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) (β : ℂ)
    (hsimple : deriv (DirichletCharacter.LFunction χ) β ≠ 0) :
    perronSimpleZeroNumerator q χ x β β = -(x : ℂ) ^ β / β := by
  have hGβ : perronLFunctionZeroFactor q χ β β ≠ 0 := by
    simpa only [perronLFunctionZeroFactor, dslope_same] using hsimple
  simp only [perronSimpleZeroNumerator, sub_self, zero_mul, add_zero,
    div_self hGβ, neg_one_mul, neg_div]

/-- Away from the zero, the actual integrand is its analytic numerator divided by `s-β`. -/
theorem perronLogDerivativeIntegrand_eq_simpleZeroNumerator_div
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (x : ℝ) (β : ℂ) (hzero : DirichletCharacter.LFunction χ β = 0)
    (s : ℂ) (hsβ : s ≠ β) (hGs : perronLFunctionZeroFactor q χ β s ≠ 0) :
    perronLogDerivativeIntegrand q χ x s =
      (s - β)⁻¹ * perronSimpleZeroNumerator q χ x β s := by
  unfold perronLogDerivativeIntegrand
  rw [deriv_LFunction_eq_zeroFactor_add_mul_deriv q χ hχ β hzero s,
    ← sub_mul_perronLFunctionZeroFactor_eq_LFunction q χ β hzero s]
  unfold perronSimpleZeroNumerator
  field_simp [sub_ne_zero.mpr hsβ, hGs]

/-- The actual weighted pole subtraction extends analytically through the simple zero. -/
theorem analyticAt_dslope_perronSimpleZeroNumerator
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (x : ℝ) (hx : 0 < x) (β : ℂ) (hβ : β ≠ 0)
    (hsimple : deriv (DirichletCharacter.LFunction χ) β ≠ 0) :
    AnalyticAt ℂ (dslope (perronSimpleZeroNumerator q χ x β) β) β := by
  have hnum := analyticAt_perronSimpleZeroNumerator q χ hχ x hx β hβ hsimple
  obtain ⟨U, hU, hA⟩ := hnum.exists_mem_nhds_analyticOnNhd
  exact ((Complex.differentiableOn_dslope hU).2 hA.differentiableOn).analyticAt hU

/-- An explicitly simple zero is the only L-function zero in some punctured
neighborhood; no quantitative zero-free region is assumed. -/
theorem eventually_LFunction_ne_zero_of_simple_zero
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (β : ℂ)
    (hzero : DirichletCharacter.LFunction χ β = 0)
    (hsimple : deriv (DirichletCharacter.LFunction χ) β ≠ 0) :
    ∀ᶠ s : ℂ in 𝓝[≠] β, DirichletCharacter.LFunction χ s ≠ 0 := by
  have hGsEvent := eventually_perronLFunctionZeroFactor_ne_zero q χ hχ β hsimple
  filter_upwards [hGsEvent.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with s hGs hs
  have hs' : s ≠ β := hs
  rw [← sub_mul_perronLFunctionZeroFactor_eq_LFunction q χ β hzero s]
  exact mul_ne_zero (sub_ne_zero.mpr hs') hGs

/-- The actual simple-zero Perron integrand is locally its exact pole plus
an analytic regular part, with the residue's `1/β` factor preserved. -/
theorem simpleZero_perronLogDerivativeIntegrand_local_pole_decomposition
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (x : ℝ) (hx : 0 < x) (β : ℂ) (hβ : β ≠ 0)
    (hzero : DirichletCharacter.LFunction χ β = 0)
    (hsimple : deriv (DirichletCharacter.LFunction χ) β ≠ 0) :
    AnalyticAt ℂ (dslope (perronSimpleZeroNumerator q χ x β) β) β ∧
      ∀ᶠ s : ℂ in 𝓝[≠] β,
        perronLogDerivativeIntegrand q χ x s =
          (-(x : ℂ) ^ β / β) / (s - β) +
            dslope (perronSimpleZeroNumerator q χ x β) β s := by
  refine ⟨analyticAt_dslope_perronSimpleZeroNumerator q χ hχ x hx β hβ hsimple, ?_⟩
  have hGsEvent := eventually_perronLFunctionZeroFactor_ne_zero q χ hχ β hsimple
  filter_upwards [hGsEvent.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with s hGs hs
  have hs' : s ≠ β := hs
  rw [perronLogDerivativeIntegrand_eq_simpleZeroNumerator_div q χ hχ x β hzero s hs' hGs,
    dslope_of_ne _ hs', slope_def_field, perronSimpleZeroNumerator_apply_center q χ x β hsimple]
  field_simp [sub_ne_zero.mpr hs']
  ring

/-- Every sufficiently small circle around an explicitly simple nonprincipal
zero has exact weighted Perron integral `2πi * (-x^β/β)`. -/
theorem exists_nonprincipal_perronLogDerivativeIntegrand_simple_zero_circleIntegral_eq
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (x : ℝ) (hx : 0 < x) (β : ℂ) (hβ : β ≠ 0)
    (hzero : DirichletCharacter.LFunction χ β = 0)
    (hsimple : deriv (DirichletCharacter.LFunction χ) β ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ R : ℝ, 0 < R → R < r →
      (∮ s in C(β, R), perronLogDerivativeIntegrand q χ x s) =
        (2 * Real.pi * Complex.I : ℂ) * (-(x : ℂ) ^ β / β) := by
  have hnum := analyticAt_perronSimpleZeroNumerator q χ hχ x hx β hβ hsimple
  have hlocal : {s : ℂ | AnalyticAt ℂ (perronSimpleZeroNumerator q χ x β) s ∧
      perronLFunctionZeroFactor q χ β s ≠ 0} ∈ 𝓝 β :=
    hnum.eventually_analyticAt.and (eventually_perronLFunctionZeroFactor_ne_zero
      q χ hχ β hsimple)
  obtain ⟨r, hr, hsubset⟩ := nhds_basis_closedBall.mem_iff.mp hlocal
  refine ⟨r, hr, ?_⟩
  intro R hR hRr
  have hRsubset : closedBall β R ⊆ closedBall β r := closedBall_subset_closedBall hRr.le
  have hdiff : DifferentiableOn ℂ (perronSimpleZeroNumerator q χ x β) (closedBall β R) := by
    intro s hs
    exact ((hsubset (hRsubset hs)).1.differentiableAt).differentiableWithinAt
  have hcongr : Set.EqOn (perronLogDerivativeIntegrand q χ x)
      (fun s : ℂ => (s - β)⁻¹ • perronSimpleZeroNumerator q χ x β s) (sphere β R) := by
    intro s hs
    have hs' : s ≠ β := by
      intro h
      subst s
      simp only [mem_sphere, dist_self] at hs
      linarith
    simpa only [smul_eq_mul] using
      perronLogDerivativeIntegrand_eq_simpleZeroNumerator_div q χ hχ x β hzero s hs'
        (hsubset (hRsubset (sphere_subset_closedBall hs))).2
  calc
    _ = ∮ s in C(β, R), (s - β)⁻¹ • perronSimpleZeroNumerator q χ x β s :=
      circleIntegral.integral_congr hR.le hcongr
    _ = (2 * Real.pi * Complex.I : ℂ) • perronSimpleZeroNumerator q χ x β β :=
      hdiff.circleIntegral_sub_inv_smul (mem_ball_self hR)
    _ = _ := by rw [perronSimpleZeroNumerator_apply_center q χ x β hsimple, smul_eq_mul]

/-- Counterclockwise boundary integral: bottom minus top, then right minus left. -/
noncomputable def perronRectangleBoundaryIntegral (f : ℂ → ℂ) (σL σR H : ℝ) : ℂ :=
  (∫ u in σL..σR, f ((u : ℂ) + (-H : ℂ) * Complex.I)) -
    (∫ u in σL..σR, f ((u : ℂ) + (H : ℂ) * Complex.I)) +
    Complex.I * (∫ t in -H..H, f ((σR : ℂ) + (t : ℂ) * Complex.I)) -
    Complex.I * (∫ t in -H..H, f ((σL : ℂ) + (t : ℂ) * Complex.I))

/-- The actual weighted L-function logarithmic derivative on a finite rectangle. -/
noncomputable def perronLogDerivativeRectangleBoundary
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ)
    (σL σR H : ℝ) : ℂ :=
  perronRectangleBoundaryIntegral (perronLogDerivativeIntegrand q χ x) σL σR H

/-- The reciprocal kernel boundary integral for an explicitly located pole. -/
noncomputable def perronReciprocalRectangleBoundary (β : ℂ) (σL σR H : ℝ) : ℂ :=
  perronRectangleBoundaryIntegral (fun z => (z - β)⁻¹) σL σR H

private theorem perronRectangleBoundaryIntegral_add_const_mul
    (f k : ℂ → ℂ) (A : ℂ) (σL σR H : ℝ)
    (hfB : IntervalIntegrable (fun u => f ((u : ℂ) + (-H : ℂ) * Complex.I)) volume σL σR)
    (hkB : IntervalIntegrable (fun u => k ((u : ℂ) + (-H : ℂ) * Complex.I)) volume σL σR)
    (hfT : IntervalIntegrable (fun u => f ((u : ℂ) + (H : ℂ) * Complex.I)) volume σL σR)
    (hkT : IntervalIntegrable (fun u => k ((u : ℂ) + (H : ℂ) * Complex.I)) volume σL σR)
    (hfR : IntervalIntegrable (fun t => f ((σR : ℂ) + (t : ℂ) * Complex.I)) volume (-H) H)
    (hkR : IntervalIntegrable (fun t => k ((σR : ℂ) + (t : ℂ) * Complex.I)) volume (-H) H)
    (hfL : IntervalIntegrable (fun t => f ((σL : ℂ) + (t : ℂ) * Complex.I)) volume (-H) H)
    (hkL : IntervalIntegrable (fun t => k ((σL : ℂ) + (t : ℂ) * Complex.I)) volume (-H) H) :
    perronRectangleBoundaryIntegral (fun z => A * k z + f z) σL σR H =
      A * perronRectangleBoundaryIntegral k σL σR H + perronRectangleBoundaryIntegral f σL σR H := by
  unfold perronRectangleBoundaryIntegral
  rw [intervalIntegral.integral_add (hkB.const_mul A) hfB,
    intervalIntegral.integral_const_mul A,
    intervalIntegral.integral_add (hkT.const_mul A) hfT,
    intervalIntegral.integral_const_mul A,
    intervalIntegral.integral_add (hkR.const_mul A) hfR,
    intervalIntegral.integral_const_mul A,
    intervalIntegral.integral_add (hkL.const_mul A) hfL,
    intervalIntegral.integral_const_mul A]
  ring

private theorem perronSimpleZeroNumerator_analyticAt_on_rect
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (x : ℝ) (hx : 0 < x) (β : ℂ)
    (R : Set ℂ) (hG : ∀ z ∈ R,
      perronLFunctionZeroFactor q χ β z ≠ 0)
    (h0 : ∀ z ∈ R, z ≠ 0) (z : ℂ) (hz : z ∈ R) :
    AnalyticAt ℂ (perronSimpleZeroNumerator q χ x β) z := by
  let G : ℂ → ℂ := perronLFunctionZeroFactor q χ β
  have hGanalytic : ∀ w : ℂ, AnalyticAt ℂ G w := by
    intro w
    exact (differentiable_perronLFunctionZeroFactor q χ hχ β).analyticAt w
  have hGderiv : ∀ w : ℂ, AnalyticAt ℂ (deriv G) w := by
    intro w
    exact (hGanalytic w).deriv
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hweightDiff : DifferentiableOn ℂ (fun w : ℂ => (x : ℂ) ^ w / w)
      ({0}ᶜ : Set ℂ) := by
    intro w hw
    have hw0 : w ≠ 0 := by simpa using hw
    have hpow : DifferentiableAt ℂ (fun v : ℂ => (x : ℂ) ^ v) w :=
      differentiableAt_id.const_cpow (.inl hxC)
    exact (hpow.div differentiableAt_id hw0).differentiableWithinAt
  have hU : ({0}ᶜ : Set ℂ) ∈ 𝓝 z :=
    isOpen_compl_singleton.mem_nhds (h0 z hz)
  have hweight : AnalyticAt ℂ (fun w : ℂ => (x : ℂ) ^ w / w) z :=
    hweightDiff.analyticAt hU
  unfold perronSimpleZeroNumerator
  exact (((hGanalytic z).fun_add
    ((analyticAt_id.fun_sub analyticAt_const).fun_mul (hGderiv z))).div
      (hGanalytic z) (hG z hz)).neg.fun_mul hweight

/-- Cauchy--Goursat annihilates the globally regularized Perron remainder
on the actual rectangle, once the zero-divided factor is nonzero there. -/
theorem dslope_perronSimpleZeroNumerator_rect_boundary_eq_zero
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (x : ℝ) (hx : 0 < x) (β : ℂ) (σL σR H : ℝ)
    (hσL : 0 < σL) (hσlr : σL < σR) (hH : 0 < H)
    (hβinside : σL < β.re ∧ β.re < σR ∧ -H < β.im ∧ β.im < H)
    (hG : ∀ z : ℂ, z ∈ ([[σL, σR]] ×ℂ [[-H, H]] : Set ℂ) →
      perronLFunctionZeroFactor q χ β z ≠ 0) :
    perronRectangleBoundaryIntegral (dslope (perronSimpleZeroNumerator q χ x β) β)
      σL σR H = 0 := by
  let R : Set ℂ := [[σL, σR]] ×ℂ [[-H, H]]
  let U : Set ℂ := Ioo σL σR ×ℂ Ioo (-H) H
  let z : ℂ := (σL : ℂ) + (-H : ℂ) * Complex.I
  let w : ℂ := (σR : ℂ) + (H : ℂ) * Complex.I
  let N : ℂ → ℂ := perronSimpleZeroNumerator q χ x β
  let F : ℂ → ℂ := dslope N β
  have hβU : β ∈ U := by
    change β.re ∈ Ioo σL σR ∧ β.im ∈ Ioo (-H) H
    exact ⟨⟨hβinside.1, hβinside.2.1⟩,
      ⟨hβinside.2.2.1, hβinside.2.2.2⟩⟩
  have hRnhds : R ∈ 𝓝 β :=
    Filter.mem_of_superset
      ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hβU) (by
        intro v hv
        have hv' : v.re ∈ Ioo σL σR ∧ v.im ∈ Ioo (-H) H := by
          simpa only [Complex.mem_reProdIm] using hv
        have hvR : v.re ∈ Icc σL σR := ⟨le_of_lt hv'.1.1, le_of_lt hv'.1.2⟩
        have hvI : v.im ∈ Icc (-H) H := ⟨le_of_lt hv'.2.1, le_of_lt hv'.2.2⟩
        simpa [R, uIcc_of_le hσlr.le,
          uIcc_of_le (show -H ≤ H by linarith)] using
          (Complex.mem_reProdIm.mpr ⟨hvR, hvI⟩))
  have h0 : ∀ v : ℂ, v ∈ R → v ≠ 0 := by
    intro v hv hv0
    have hv' : v.re ∈ Icc σL σR ∧ v.im ∈ Icc (-H) H := by
      simpa [R, uIcc_of_le hσlr.le,
        uIcc_of_le (show -H ≤ H by linarith), Complex.mem_reProdIm] using hv
    have hvre : v.re ∈ Icc σL σR := hv'.1
    have hvre0 : v.re = 0 := by rw [hv0]; simp
    linarith [hvre.1]
  have hN : DifferentiableOn ℂ N R := by
    intro v hv
    exact (perronSimpleZeroNumerator_analyticAt_on_rect q χ hχ x hx β
      R hG h0 v hv).differentiableAt.differentiableWithinAt
  have hF : DifferentiableOn ℂ F R :=
    (Complex.differentiableOn_dslope (s := R) (c := β) hRnhds).2 hN
  have hFopen : DifferentiableOn ℂ F U := hF.mono (by
    intro v hv
    have hv' : v.re ∈ Ioo σL σR ∧ v.im ∈ Ioo (-H) H := by
      simpa [U, Complex.mem_reProdIm] using hv
    have hvR : v.re ∈ Icc σL σR := ⟨le_of_lt hv'.1.1, le_of_lt hv'.1.2⟩
    have hvI : v.im ∈ Icc (-H) H := ⟨le_of_lt hv'.2.1, le_of_lt hv'.2.2⟩
    simpa [R, uIcc_of_le hσlr.le,
      uIcc_of_le (show -H ≤ H by linarith)] using
      (Complex.mem_reProdIm.mpr ⟨hvR, hvI⟩))
  have hRcorner : ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) = R := by
    ext v
    simp [R, z, w]
  have hUcorner :
      (Ioo (min z.re w.re) (max z.re w.re) ×ℂ
        Ioo (min z.im w.im) (max z.im w.im)) = U := by
    ext v
    simp [U, z, w, min_eq_left hσlr.le, max_eq_right hσlr.le,
      min_eq_left (show -H ≤ H by linarith), max_eq_right (show -H ≤ H by linarith)]
  have hFcont : ContinuousOn F ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
    rw [hRcorner]
    exact hF.continuousOn
  have hFopenCorner : DifferentiableOn ℂ F
      (Ioo (min z.re w.re) (max z.re w.re) ×ℂ
        Ioo (min z.im w.im) (max z.im w.im)) := by
    rw [hUcorner]
    exact hFopen
  have hboundary := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    F z w hFcont hFopenCorner
  simpa [perronRectangleBoundaryIntegral, F, z, w] using hboundary

/-- In a zero-free closed rectangle, the actual weighted nonprincipal
logarithmic derivative is holomorphic, so its CCW boundary integral vanishes. -/
theorem perronLogDerivative_zeroFree_rectangle_boundary_eq_zero
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (x : ℝ) (hx : 0 < x) (σL σR H : ℝ)
    (hσL : 0 < σL) (hσlr : σL < σR) (hH : 0 < H)
    (hzeroFree : ∀ z : ℂ, z ∈ ([[σL, σR]] ×ℂ [[-H, H]] : Set ℂ) →
      DirichletCharacter.LFunction χ z ≠ 0) :
    perronLogDerivativeRectangleBoundary q χ x σL σR H = 0 := by
  let R : Set ℂ := [[σL, σR]] ×ℂ [[-H, H]]
  let U : Set ℂ := Ioo σL σR ×ℂ Ioo (-H) H
  let z : ℂ := (σL : ℂ) + (-H : ℂ) * Complex.I
  let w : ℂ := (σR : ℂ) + (H : ℂ) * Complex.I
  let F : ℂ → ℂ := perronLogDerivativeIntegrand q χ x
  have h0 : ∀ v : ℂ, v ∈ R → v ≠ 0 := by
    intro v hv hv0
    have hv' : v.re ∈ Icc σL σR ∧ v.im ∈ Icc (-H) H := by
      simpa [R, uIcc_of_le hσlr.le,
        uIcc_of_le (show -H ≤ H by linarith), Complex.mem_reProdIm] using hv
    have hvre0 : v.re = 0 := by rw [hv0]; simp
    linarith [hv'.1.1]
  have hFanalytic : ∀ v : ℂ, v ∈ R → AnalyticAt ℂ F v := by
    intro v hv
    have hLanalytic : AnalyticAt ℂ (DirichletCharacter.LFunction χ) v :=
      (DirichletCharacter.differentiable_LFunction hχ).analyticAt v
    have hLderiv : AnalyticAt ℂ (deriv (DirichletCharacter.LFunction χ)) v :=
      hLanalytic.deriv
    have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have hpowDiff : DifferentiableOn ℂ (fun u : ℂ => (x : ℂ) ^ u) Set.univ := by
      intro u hu
      exact (differentiableAt_id.const_cpow (.inl hxC)).differentiableWithinAt
    have hpow : AnalyticAt ℂ (fun u : ℂ => (x : ℂ) ^ u) v :=
      hpowDiff.analyticAt (isOpen_univ.mem_nhds (Set.mem_univ v))
    have hLne : DirichletCharacter.LFunction χ v ≠ 0 := hzeroFree v hv
    have hactual : AnalyticAt ℂ
        (fun u => (-(deriv (DirichletCharacter.LFunction χ) u /
          DirichletCharacter.LFunction χ u) * (x : ℂ) ^ u) / u) v :=
      (((hLderiv.div hLanalytic hLne).neg.fun_mul hpow).div
        analyticAt_id (h0 v hv))
    change AnalyticAt ℂ (perronLogDerivativeIntegrand q χ x) v
    unfold perronLogDerivativeIntegrand
    have hform :
        (fun u : ℂ => -deriv (DirichletCharacter.LFunction χ) u /
          DirichletCharacter.LFunction χ u * (x : ℂ) ^ u / u) =
        (fun u : ℂ => (-(deriv (DirichletCharacter.LFunction χ) u /
          DirichletCharacter.LFunction χ u) * (x : ℂ) ^ u) / u) := by
      funext u
      ring
    rw [hform]
    exact hactual
  have hFdiff : DifferentiableOn ℂ F R := by
    intro v hv
    exact (hFanalytic v hv).differentiableAt.differentiableWithinAt
  have hFopen : DifferentiableOn ℂ F U := hFdiff.mono (by
    intro v hv
    have hv' : v.re ∈ Ioo σL σR ∧ v.im ∈ Ioo (-H) H := by
      simpa [U, Complex.mem_reProdIm] using hv
    have hvR : v.re ∈ Icc σL σR := ⟨le_of_lt hv'.1.1, le_of_lt hv'.1.2⟩
    have hvI : v.im ∈ Icc (-H) H := ⟨le_of_lt hv'.2.1, le_of_lt hv'.2.2⟩
    simpa [R, uIcc_of_le hσlr.le,
      uIcc_of_le (show -H ≤ H by linarith)] using
      (Complex.mem_reProdIm.mpr ⟨hvR, hvI⟩))
  have hRcorner : ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) = R := by
    ext v
    simp [R, z, w]
  have hUcorner :
      (Ioo (min z.re w.re) (max z.re w.re) ×ℂ
        Ioo (min z.im w.im) (max z.im w.im)) = U := by
    ext v
    simp [U, z, w, min_eq_left hσlr.le, max_eq_right hσlr.le,
      min_eq_left (show -H ≤ H by linarith), max_eq_right (show -H ≤ H by linarith)]
  have hFcont : ContinuousOn F ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
    rw [hRcorner]
    exact hFdiff.continuousOn
  have hFopenCorner : DifferentiableOn ℂ F
      (Ioo (min z.re w.re) (max z.re w.re) ×ℂ
        Ioo (min z.im w.im) (max z.im w.im)) := by
    rw [hUcorner]
    exact hFopen
  have hboundary := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    F z w hFcont hFopenCorner
  simpa [perronLogDerivativeRectangleBoundary, perronRectangleBoundaryIntegral, F, z, w] using hboundary

private theorem perronLogDerivativeIntegrand_eq_residue_add_dslope_rect
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (x : ℝ) (_hx : 0 < x) (β : ℂ) (hβ : β ≠ 0)
    (hzero : DirichletCharacter.LFunction χ β = 0)
    (hsimple : deriv (DirichletCharacter.LFunction χ) β ≠ 0)
    (z : ℂ) (hzβ : z ≠ β) (hG : perronLFunctionZeroFactor q χ β z ≠ 0) :
    perronLogDerivativeIntegrand q χ x z =
      (-(x : ℂ) ^ β / β) / (z - β) +
        dslope (perronSimpleZeroNumerator q χ x β) β z := by
  rw [perronLogDerivativeIntegrand_eq_simpleZeroNumerator_div
    q χ hχ x β hzero z hzβ hG,
    dslope_of_ne _ hzβ, slope_def_field,
    perronSimpleZeroNumerator_apply_center q χ x β hsimple]
  field_simp [sub_ne_zero.mpr hzβ]
  ring

/-- Four-edge Perron contour transfer across one simple zero, retaining the
exact reciprocal-kernel boundary integral. -/
theorem perronLogDerivative_rectangle_boundary_eq_residue_mul_kernel
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (x : ℝ) (hx : 0 < x) (σL σR H : ℝ)
    (hσL : 0 < σL) (hσlr : σL < σR) (hH : 0 < H)
    (β : ℂ) (hβ : β ≠ 0)
    (hβinside : σL < β.re ∧ β.re < σR ∧ -H < β.im ∧ β.im < H)
    (hzero : DirichletCharacter.LFunction χ β = 0)
    (hsimple : deriv (DirichletCharacter.LFunction χ) β ≠ 0)
    (hG : ∀ z : ℂ, z ∈ ([[σL, σR]] ×ℂ [[-H, H]] : Set ℂ) →
      perronLFunctionZeroFactor q χ β z ≠ 0) :
    perronLogDerivativeRectangleBoundary q χ x σL σR H =
      (-(x : ℂ) ^ β / β) * perronReciprocalRectangleBoundary β σL σR H := by
  let R : Set ℂ := [[σL, σR]] ×ℂ [[-H, H]]
  let U : Set ℂ := Ioo σL σR ×ℂ Ioo (-H) H
  let N : ℂ → ℂ := perronSimpleZeroNumerator q χ x β
  let F : ℂ → ℂ := dslope N β
  let K : ℂ → ℂ := fun z => (z - β)⁻¹
  let A : ℂ := -(x : ℂ) ^ β / β
  let pB : ℝ → ℂ := fun u => (u : ℂ) + (-H : ℂ) * Complex.I
  let pT : ℝ → ℂ := fun u => (u : ℂ) + (H : ℂ) * Complex.I
  let pR : ℝ → ℂ := fun t => (σR : ℂ) + (t : ℂ) * Complex.I
  let pL : ℝ → ℂ := fun t => (σL : ℂ) + (t : ℂ) * Complex.I
  have hβU : β ∈ U := by
    change β.re ∈ Ioo σL σR ∧ β.im ∈ Ioo (-H) H
    exact ⟨⟨hβinside.1, hβinside.2.1⟩,
      ⟨hβinside.2.2.1, hβinside.2.2.2⟩⟩
  have hRnhds : R ∈ 𝓝 β :=
    Filter.mem_of_superset
      ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hβU) (by
        intro v hv
        have hv' : v.re ∈ Ioo σL σR ∧ v.im ∈ Ioo (-H) H := by
          simpa only [Complex.mem_reProdIm] using hv
        have hvR : v.re ∈ Icc σL σR := ⟨le_of_lt hv'.1.1, le_of_lt hv'.1.2⟩
        have hvI : v.im ∈ Icc (-H) H := ⟨le_of_lt hv'.2.1, le_of_lt hv'.2.2⟩
        simpa [R, uIcc_of_le hσlr.le,
          uIcc_of_le (show -H ≤ H by linarith)] using
          (Complex.mem_reProdIm.mpr ⟨hvR, hvI⟩))
  have h0 : ∀ v : ℂ, v ∈ R → v ≠ 0 := by
    intro v hv hv0
    have hv' : v.re ∈ Icc σL σR ∧ v.im ∈ Icc (-H) H := by
      simpa [R, uIcc_of_le hσlr.le,
        uIcc_of_le (show -H ≤ H by linarith), Complex.mem_reProdIm] using hv
    have hvre0 : v.re = 0 := by rw [hv0]; simp
    linarith [hv'.1.1]
  have hN : DifferentiableOn ℂ N R := by
    intro v hv
    exact (perronSimpleZeroNumerator_analyticAt_on_rect q χ hχ x hx β
      R hG h0 v hv).differentiableAt.differentiableWithinAt
  have hFdiff : DifferentiableOn ℂ F R :=
    (Complex.differentiableOn_dslope (s := R) (c := β) hRnhds).2 hN
  have hFcont : ContinuousOn F R := hFdiff.continuousOn
  have hFboundary : perronRectangleBoundaryIntegral F σL σR H = 0 :=
    dslope_perronSimpleZeroNumerator_rect_boundary_eq_zero q χ hχ x hx β
      σL σR H hσL hσlr hH hβinside hG
  have hBmap : ∀ u : ℝ, u ∈ [[σL, σR]] → pB u ∈ R ∧ pB u ≠ β := by
    intro u hu
    have hu' : u ∈ Icc σL σR := by simpa [uIcc_of_le hσlr.le] using hu
    have hmem : pB u ∈ R := by
      change (pB u).re ∈ [[σL, σR]] ∧ (pB u).im ∈ [[-H, H]]
      constructor
      · simp [pB, Icc_subset_uIcc hu']
      · simp [pB, (left_mem_uIcc : -H ∈ [[-H, H]])]
    refine ⟨hmem, ?_⟩
    intro heq
    have him := congrArg Complex.im heq
    simp [pB] at him
    linarith [hβinside.2.2.1]
  have hTmap : ∀ u : ℝ, u ∈ [[σL, σR]] → pT u ∈ R ∧ pT u ≠ β := by
    intro u hu
    have hu' : u ∈ Icc σL σR := by simpa [uIcc_of_le hσlr.le] using hu
    have hmem : pT u ∈ R := by
      change (pT u).re ∈ [[σL, σR]] ∧ (pT u).im ∈ [[-H, H]]
      constructor
      · simp [pT, Icc_subset_uIcc hu']
      · simp [pT, (right_mem_uIcc : H ∈ [[-H, H]])]
    refine ⟨hmem, ?_⟩
    intro heq
    have him := congrArg Complex.im heq
    simp [pT] at him
    linarith [hβinside.2.2.2]
  have hRmap : ∀ t : ℝ, t ∈ [[-H, H]] → pR t ∈ R ∧ pR t ≠ β := by
    intro t ht
    have ht' : t ∈ Icc (-H) H := by
      simpa [uIcc_of_le (show -H ≤ H by linarith)] using ht
    have hmem : pR t ∈ R := by
      change (pR t).re ∈ [[σL, σR]] ∧ (pR t).im ∈ [[-H, H]]
      constructor
      · simp [pR, (right_mem_uIcc : σR ∈ [[σL, σR]])]
      · simp [pR, Icc_subset_uIcc ht']
    refine ⟨hmem, ?_⟩
    intro heq
    have hre := congrArg Complex.re heq
    simp [pR] at hre
    linarith [hβinside.2.1]
  have hLmap : ∀ t : ℝ, t ∈ [[-H, H]] → pL t ∈ R ∧ pL t ≠ β := by
    intro t ht
    have ht' : t ∈ Icc (-H) H := by
      simpa [uIcc_of_le (show -H ≤ H by linarith)] using ht
    have hmem : pL t ∈ R := by
      change (pL t).re ∈ [[σL, σR]] ∧ (pL t).im ∈ [[-H, H]]
      constructor
      · simp [pL, (left_mem_uIcc : σL ∈ [[σL, σR]])]
      · simp [pL, Icc_subset_uIcc ht']
    refine ⟨hmem, ?_⟩
    intro heq
    have hre := congrArg Complex.re heq
    simp [pL] at hre
    linarith [hβinside.1]
  have hdecomp (v : ℂ) (hv : v ∈ R) (hvβ : v ≠ β) :
      perronLogDerivativeIntegrand q χ x v = A * K v + F v := by
    simpa [A, K, F, div_eq_mul_inv] using
      perronLogDerivativeIntegrand_eq_residue_add_dslope_rect q χ hχ x hx β hβ
        hzero hsimple v hvβ (hG v hv)
  have hbottom : ∫ u in σL..σR, perronLogDerivativeIntegrand q χ x (pB u) =
      ∫ u in σL..σR, A * K (pB u) + F (pB u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    exact hdecomp (pB u) (hBmap u hu).1 (hBmap u hu).2
  have htop : ∫ u in σL..σR, perronLogDerivativeIntegrand q χ x (pT u) =
      ∫ u in σL..σR, A * K (pT u) + F (pT u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    exact hdecomp (pT u) (hTmap u hu).1 (hTmap u hu).2
  have hright : ∫ t in -H..H, perronLogDerivativeIntegrand q χ x (pR t) =
      ∫ t in -H..H, A * K (pR t) + F (pR t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hdecomp (pR t) (hRmap t ht).1 (hRmap t ht).2
  have hleft : ∫ t in -H..H, perronLogDerivativeIntegrand q χ x (pL t) =
      ∫ t in -H..H, A * K (pL t) + F (pL t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hdecomp (pL t) (hLmap t ht).1 (hLmap t ht).2
  have hFB : ContinuousOn (fun u => F (pB u)) [[σL, σR]] :=
    hFcont.comp (by fun_prop) (fun u hu => (hBmap u hu).1)
  have hFT : ContinuousOn (fun u => F (pT u)) [[σL, σR]] :=
    hFcont.comp (by fun_prop) (fun u hu => (hTmap u hu).1)
  have hFR : ContinuousOn (fun t => F (pR t)) [[-H, H]] :=
    hFcont.comp (by fun_prop) (fun t ht => (hRmap t ht).1)
  have hFL : ContinuousOn (fun t => F (pL t)) [[-H, H]] :=
    hFcont.comp (by fun_prop) (fun t ht => (hLmap t ht).1)
  have hKB : ContinuousOn (fun u => K (pB u)) [[σL, σR]] := by
    change ContinuousOn (fun u => (pB u - β)⁻¹) [[σL, σR]]
    apply continuousOn_inv₀.comp (by fun_prop)
    intro u hu
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact sub_ne_zero.mpr (hBmap u hu).2
  have hKT : ContinuousOn (fun u => K (pT u)) [[σL, σR]] := by
    change ContinuousOn (fun u => (pT u - β)⁻¹) [[σL, σR]]
    apply continuousOn_inv₀.comp (by fun_prop)
    intro u hu
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact sub_ne_zero.mpr (hTmap u hu).2
  have hKR : ContinuousOn (fun t => K (pR t)) [[-H, H]] := by
    change ContinuousOn (fun t => (pR t - β)⁻¹) [[-H, H]]
    apply continuousOn_inv₀.comp (by fun_prop)
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact sub_ne_zero.mpr (hRmap t ht).2
  have hKL : ContinuousOn (fun t => K (pL t)) [[-H, H]] := by
    change ContinuousOn (fun t => (pL t - β)⁻¹) [[-H, H]]
    apply continuousOn_inv₀.comp (by fun_prop)
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact sub_ne_zero.mpr (hLmap t ht).2
  have hrewrite : perronLogDerivativeRectangleBoundary q χ x σL σR H =
      perronRectangleBoundaryIntegral (fun v => A * K v + F v) σL σR H := by
    unfold perronLogDerivativeRectangleBoundary perronRectangleBoundaryIntegral
    rw [hbottom, htop, hright, hleft]
  have hlinear := perronRectangleBoundaryIntegral_add_const_mul F K A σL σR H
    hFB.intervalIntegrable hKB.intervalIntegrable
    hFT.intervalIntegrable hKT.intervalIntegrable
    hFR.intervalIntegrable hKR.intervalIntegrable
    hFL.intervalIntegrable hKL.intervalIntegrable
  calc
    perronLogDerivativeRectangleBoundary q χ x σL σR H =
        perronRectangleBoundaryIntegral (fun v => A * K v + F v) σL σR H := hrewrite
    _ = A * perronRectangleBoundaryIntegral K σL σR H + perronRectangleBoundaryIntegral F σL σR H := hlinear
    _ = A * perronReciprocalRectangleBoundary β σL σR H := by
      dsimp [perronReciprocalRectangleBoundary, K]
      rw [hFboundary]
      ring

/-- A simple zero is removed without introducing any additional zeros in the
zero-divided factor, when it is the only zero on the closed rectangle. -/
theorem perronLFunctionZeroFactor_ne_zero_on_rect_of_unique_zero
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (β : ℂ) (hzero : DirichletCharacter.LFunction χ β = 0)
    (hsimple : deriv (DirichletCharacter.LFunction χ) β ≠ 0)
    (σL σR H : ℝ)
    (honly : ∀ z : ℂ, z ∈ ([[σL, σR]] ×ℂ [[-H, H]] : Set ℂ) →
      DirichletCharacter.LFunction χ z = 0 → z = β) :
    ∀ z : ℂ, z ∈ ([[σL, σR]] ×ℂ [[-H, H]] : Set ℂ) →
      perronLFunctionZeroFactor q χ β z ≠ 0 := by
  intro z hz
  by_cases hzb : z = β
  · subst z
    simpa only [perronLFunctionZeroFactor, dslope_same] using hsimple
  · intro hGzero
    have hLzero : DirichletCharacter.LFunction χ z = 0 := by
      calc
        _ = (z - β) * perronLFunctionZeroFactor q χ β z :=
          (sub_mul_perronLFunctionZeroFactor_eq_LFunction q χ β hzero z).symm
        _ = 0 := by simp [hGzero]
    exact hzb (honly z hz hLzero)

/-- With a real exceptional zero, the proved exact reciprocal rectangle
formula evaluates the retained kernel to `2πi`, giving the exact normalized
exceptional Perron residue. -/
theorem perronLogDerivative_real_exceptional_rectangle_residue
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (x : ℝ) (hx : 0 < x) (σL σR H β : ℝ)
    (hσL : 0 < σL) (hσlr : σL < σR) (hH : 0 < H)
    (hleft : σL < β) (hright : β < σR) (hβ : β ≠ 0)
    (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0)
    (hsimple : deriv (DirichletCharacter.LFunction χ) (β : ℂ) ≠ 0)
    (honly : ∀ z : ℂ, z ∈ ([[σL, σR]] ×ℂ [[-H, H]] : Set ℂ) →
      DirichletCharacter.LFunction χ z = 0 → z = (β : ℂ)) :
    perronLogDerivativeRectangleBoundary q χ x σL σR H /
      (2 * Real.pi * Complex.I : ℂ) =
      -(x : ℂ) ^ (β : ℂ) / (β : ℂ) := by
  have hβC : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  have hinside : σL < (β : ℂ).re ∧ (β : ℂ).re < σR ∧
      -H < (β : ℂ).im ∧ (β : ℂ).im < H := by
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨hleft, hright, by linarith, by linarith⟩
  have hG := perronLFunctionZeroFactor_ne_zero_on_rect_of_unique_zero
    q χ (β : ℂ) hzero hsimple σL σR H honly
  have htransfer := perronLogDerivative_rectangle_boundary_eq_residue_mul_kernel
    q χ hχ x hx σL σR H hσL hσlr hH (β : ℂ) hβC hinside hzero hsimple hG
  have hkernel : perronReciprocalRectangleBoundary (β : ℂ) σL σR H =
      (2 * Real.pi * Complex.I : ℂ) := by
    unfold perronReciprocalRectangleBoundary perronRectangleBoundaryIntegral
    simpa only [smul_eq_mul] using
      perronReciprocal_realPole_rectangle σL σR β H hleft hright hH
  have hboundary : perronLogDerivativeRectangleBoundary q χ x σL σR H =
      (-(x : ℂ) ^ (β : ℂ) / (β : ℂ)) *
        (2 * Real.pi * Complex.I : ℂ) := by
    rw [htransfer, hkernel]
  have hden : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast (mul_ne_zero two_ne_zero Real.pi_ne_zero)
    · exact Complex.I_ne_zero
  rw [hboundary]
  field_simp [hden]

#print axioms dslope_perronSimpleZeroNumerator_rect_boundary_eq_zero
#print axioms perronLFunctionZeroFactor_ne_zero_on_rect_of_unique_zero
#print axioms perronLogDerivative_rectangle_boundary_eq_residue_mul_kernel
#print axioms perronLogDerivative_real_exceptional_rectangle_residue
#print axioms perronLogDerivative_zeroFree_rectangle_boundary_eq_zero

/-- The normalized right edge differs from the normalized boundary by just
the left edge and the two horizontal edges. -/
theorem norm_perronRectangle_right_sub_boundary_le
    (f : ℂ → ℂ) (σL σR H : ℝ) :
    ‖(2 * Real.pi : ℂ)⁻¹ *
        (∫ t in -H..H, f ((σR : ℂ) + (t : ℂ) * Complex.I)) -
      perronRectangleBoundaryIntegral f σL σR H /
        (2 * Real.pi * Complex.I : ℂ)‖ ≤
      (2 * Real.pi)⁻¹ *
        (‖∫ t in -H..H, f ((σL : ℂ) + (t : ℂ) * Complex.I)‖ +
          ‖∫ u in σL..σR, f ((u : ℂ) + (-H : ℂ) * Complex.I)‖ +
          ‖∫ u in σL..σR, f ((u : ℂ) + (H : ℂ) * Complex.I)‖) := by
  let B : ℂ := ∫ u in σL..σR, f ((u : ℂ) + (-H : ℂ) * Complex.I)
  let T : ℂ := ∫ u in σL..σR, f ((u : ℂ) + (H : ℂ) * Complex.I)
  let R : ℂ := ∫ t in -H..H, f ((σR : ℂ) + (t : ℂ) * Complex.I)
  let L : ℂ := ∫ t in -H..H, f ((σL : ℂ) + (t : ℂ) * Complex.I)
  have ha : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hform : (2 * Real.pi : ℂ)⁻¹ * R -
      (B - T + Complex.I * R - Complex.I * L) /
        (2 * Real.pi * Complex.I : ℂ) =
      (2 * Real.pi : ℂ)⁻¹ * (L + Complex.I * B - Complex.I * T) := by
    field_simp [ha, Complex.I_ne_zero]
    ring_nf
    simp [Complex.I_sq, sub_eq_add_neg]
  change ‖(2 * Real.pi : ℂ)⁻¹ * R -
      (B - T + Complex.I * R - Complex.I * L) /
        (2 * Real.pi * Complex.I : ℂ)‖ ≤
      (2 * Real.pi)⁻¹ * (‖L‖ + ‖B‖ + ‖T‖)
  rw [hform, norm_mul]
  have hfactor : ‖(2 * Real.pi : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    simp [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hfactor]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ‖L + Complex.I * B - Complex.I * T‖ ≤
        ‖L + Complex.I * B‖ + ‖Complex.I * T‖ := norm_sub_le _ _
    _ ≤ (‖L‖ + ‖Complex.I * B‖) + ‖Complex.I * T‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ = ‖L‖ + ‖B‖ + ‖T‖ := by simp

#print axioms norm_perronRectangle_right_sub_boundary_le

end SystolicGrowth.CookMagyarCircle

#print axioms SystolicGrowth.CookMagyarCircle.deriv_LFunction_eq_zeroFactor_add_mul_deriv
#print axioms SystolicGrowth.CookMagyarCircle.analyticAt_perronSimpleZeroNumerator
#print axioms SystolicGrowth.CookMagyarCircle.analyticAt_dslope_perronSimpleZeroNumerator
#print axioms SystolicGrowth.CookMagyarCircle.simpleZero_perronLogDerivativeIntegrand_local_pole_decomposition
#print axioms SystolicGrowth.CookMagyarCircle.eventually_LFunction_ne_zero_of_simple_zero
#print axioms SystolicGrowth.CookMagyarCircle.exists_nonprincipal_perronLogDerivativeIntegrand_simple_zero_circleIntegral_eq
