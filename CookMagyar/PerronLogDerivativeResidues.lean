module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# Local logarithmic-derivative residues for Perron contours

For the principal character, the negative logarithmic derivative has pole
`1 / (s - 1)` and an analytic remainder near `1`. Weighting by `x^s / s`
gives residue `x`. At a simple zero `β ≠ 0` of a nonprincipal L-function,
the weighted residue is `-x^β / β`.

These are local residue calculations, not a zero-free-region theorem or a
proof that the possible exceptional zero is simple. In particular, the
exact exceptional contribution includes the factor `1 / β`; an error
allowance of only `x^β` needs a separate estimate for the excess.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace SystolicGrowth.CookMagyarCircle

/-- The analytic part of the principal-character negative logarithmic
derivative after subtracting its pole at `1`. -/
noncomputable def principalLogDerivRegularRemainder (q : ℕ) [NeZero q]
    (s : ℂ) : ℂ :=
  -deriv (DirichletCharacter.LFunctionTrivChar₁ q) s /
    DirichletCharacter.LFunctionTrivChar₁ q s

/-- The principal-character logarithmic derivative decomposes into its
universal simple pole and the regularized analytic term. -/
theorem principal_negative_logDeriv_eq_pole_add_remainder
    (q : ℕ) [NeZero q] (s : ℂ) (hs : s ≠ 1)
    (hLs : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s ≠ 0) :
    -deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s /
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s =
      (s - 1)⁻¹ + principalLogDerivRegularRemainder q s := by
  have hF : DirichletCharacter.LFunctionTrivChar₁ q s =
      (s - 1) * DirichletCharacter.LFunctionTrivChar q s := by
    exact Function.update_of_ne hs _ _
  unfold principalLogDerivRegularRemainder
  rw [DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one q hs, hF]
  change -deriv (DirichletCharacter.LFunctionTrivChar q) s /
      DirichletCharacter.LFunctionTrivChar q s = _
  field_simp [sub_ne_zero_of_ne hs, hLs]
  ring

/-- The pole-subtracted principal logarithmic derivative is analytic at `1`. -/
theorem analyticAt_principalLogDerivRegularRemainder_one
    (q : ℕ) [NeZero q] :
    AnalyticAt ℂ (principalLogDerivRegularRemainder q) 1 := by
  have hF := (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).analyticAt 1
  exact hF.deriv.neg.div hF (DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q)

/-- In particular, the pole-subtracted term is continuous at `1`. -/
theorem continuousAt_principalLogDerivRegularRemainder_one
    (q : ℕ) [NeZero q] :
    ContinuousAt (principalLogDerivRegularRemainder q) 1 :=
  (analyticAt_principalLogDerivRegularRemainder_one q).continuousAt

/-- The principal L-function has no zeros in a punctured neighborhood of `1`,
as a consequence of its nonzero regularized value there. -/
theorem eventually_principal_LFunction_ne_zero_at_one
    (q : ℕ) [NeZero q] :
    ∀ᶠ s : ℂ in 𝓝[≠] 1,
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s ≠ 0 := by
  have hF : ∀ᶠ s : ℂ in 𝓝 1,
      DirichletCharacter.LFunctionTrivChar₁ q s ≠ 0 :=
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).continuous.continuousAt
      |>.eventually_ne (DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q)
  filter_upwards [hF.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hFs hs
  have hs' : s ≠ 1 := hs
  rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs'] at hFs
  exact (mul_ne_zero_iff.mp hFs).2

/-- The negative logarithmic derivative has residue `1` at the principal pole. -/
theorem tendsto_principal_negative_logDeriv_residue_one
    (q : ℕ) [NeZero q] :
    Tendsto (fun s : ℂ => (s - 1) *
      (-deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s /
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s))
      (𝓝[≠] 1) (𝓝 1) := by
  have hsub : Tendsto (fun s : ℂ => s - 1) (𝓝[≠] 1) (𝓝 0) := by
    simpa only [id_eq, sub_self] using
      ((tendsto_id : Tendsto (fun s : ℂ => s) (𝓝 1) (𝓝 1)).sub_const 1)
        |>.mono_left nhdsWithin_le_nhds
  have hrem : Tendsto (principalLogDerivRegularRemainder q)
      (𝓝[≠] 1) (𝓝 (principalLogDerivRegularRemainder q 1)) :=
    (continuousAt_principalLogDerivRegularRemainder_one q).tendsto
      |>.mono_left nhdsWithin_le_nhds
  have htarget : Tendsto (fun s : ℂ => 1 + (s - 1) *
      principalLogDerivRegularRemainder q s) (𝓝[≠] 1) (𝓝 1) := by
    simpa only [zero_mul, add_zero] using tendsto_const_nhds.add (hsub.mul hrem)
  refine htarget.congr' ?_
  filter_upwards [eventually_principal_LFunction_ne_zero_at_one q,
    self_mem_nhdsWithin] with s hLs hs
  have hs' : s ≠ 1 := hs
  rw [principal_negative_logDeriv_eq_pole_add_remainder q s hs' hLs]
  simp only [mul_add, mul_inv_cancel₀ (sub_ne_zero_of_ne hs')]

/-- The actual `x^s / s`-weighted logarithmic derivative in the Perron integral. -/
noncomputable def perronLogDerivativeIntegrand (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (x : ℝ) (s : ℂ) : ℂ :=
  (-deriv (DirichletCharacter.LFunction χ) s /
    DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s

/- TASK-SLOT PERRON-WEIGHTED-POLE-SUBTRACTION:
P13 principal_perronLogDerivativeIntegrand_eq_pole_add_dslope
(COMPLETE). The exact identity is proved below. No contour shift or
zero-free-region claim is made by this constituent. -/

/-- Subtract the actual weighted principal pole `x / (s - 1)`; the remaining
divided difference is extended through `1` by `dslope`. -/
theorem principal_perronLogDerivativeIntegrand_eq_pole_add_dslope
    (q : ℕ) [NeZero q] (x : ℝ) (s : ℂ) (hs : s ≠ 1)
    (hLs : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s ≠ 0) :
    perronLogDerivativeIntegrand q (1 : DirichletCharacter ℂ q) x s =
      (x : ℂ) / (s - 1) +
        dslope (fun z : ℂ => (x : ℂ) ^ z / z) 1 s +
        principalLogDerivRegularRemainder q s * ((x : ℂ) ^ s / s) := by
  unfold perronLogDerivativeIntegrand
  rw [principal_negative_logDeriv_eq_pole_add_remainder q s hs hLs]
  rw [dslope_of_ne _ hs, slope_def_field]
  simp only [Complex.cpow_one, div_one]
  field_simp [sub_ne_zero.mpr hs]
  ring

/- TASK-SLOT PERRON-WEIGHTED-REGULAR-HOLOMORPHY:
P14 analyticAt_principal_perronLogDerivativeIntegrand_regular_part_one
(COMPLETE). The actual P13 remainder is analytic at `1`, without a
quantitative zero-free-region or a global contour claim. -/

/-- P13's actual weighted pole-subtracted principal integrand is analytic
at `1`; the weight's separate pole at `0` is excluded in the intermediate domain. -/
theorem analyticAt_principal_perronLogDerivativeIntegrand_regular_part_one
    (q : ℕ) [NeZero q] (x : ℝ) (hx : 0 < x) :
    AnalyticAt ℂ (fun s : ℂ =>
      dslope (fun z : ℂ => (x : ℂ) ^ z / z) 1 s +
        principalLogDerivRegularRemainder q s * ((x : ℂ) ^ s / s)) 1 := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hU : ({0}ᶜ : Set ℂ) ∈ 𝓝 (1 : ℂ) :=
    isOpen_compl_singleton.mem_nhds (by simp)
  have hweight : DifferentiableOn ℂ (fun z : ℂ => (x : ℂ) ^ z / z)
      ({0}ᶜ : Set ℂ) := by
    intro z hz
    have hz' : z ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
    have hnum : DifferentiableAt ℂ (fun t : ℂ => (x : ℂ) ^ t) z :=
      differentiableAt_id.const_cpow (.inl hxC)
    exact (hnum.div differentiableAt_id hz').differentiableWithinAt
  have hdiff : DifferentiableOn ℂ
      (dslope (fun z : ℂ => (x : ℂ) ^ z / z) 1) ({0}ᶜ : Set ℂ) :=
    (Complex.differentiableOn_dslope hU).2 hweight
  exact (hdiff.analyticAt hU).fun_add
    ((analyticAt_principalLogDerivRegularRemainder_one q).fun_mul (hweight.analyticAt hU))

/-- On a punctured neighborhood of `1`, the actual principal Perron integrand
equals its principal pole plus P14's analytic remainder. -/
theorem eventually_principal_perronLogDerivativeIntegrand_eq_pole_add_regular_part
    (q : ℕ) [NeZero q] (x : ℝ) (_hx : 0 < x) :
    ∀ᶠ s : ℂ in 𝓝[≠] 1,
      perronLogDerivativeIntegrand q (1 : DirichletCharacter ℂ q) x s =
        (x : ℂ) / (s - 1) +
          (dslope (fun z : ℂ => (x : ℂ) ^ z / z) 1 s +
            principalLogDerivRegularRemainder q s * ((x : ℂ) ^ s / s)) := by
  filter_upwards [eventually_principal_LFunction_ne_zero_at_one q,
    self_mem_nhdsWithin] with s hLs hs
  have hs' : s ≠ 1 := hs
  simpa only [add_assoc] using
    principal_perronLogDerivativeIntegrand_eq_pole_add_dslope q x s hs' hLs

/-- The principal-character weighted Perron integrand has exact residue `x`. -/
theorem tendsto_principal_perronLogDerivativeIntegrand_residue_one
    (q : ℕ) [NeZero q] (x : ℝ) (hx : 0 < x) :
    Tendsto (fun s : ℂ => (s - 1) *
      perronLogDerivativeIntegrand q (1 : DirichletCharacter ℂ q) x s)
      (𝓝[≠] 1) (𝓝 (x : ℂ)) := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hweight : ContinuousAt (fun s : ℂ => (x : ℂ) ^ s / s) 1 :=
    (continuousAt_const_cpow hxC).div continuousAt_id one_ne_zero
  simpa only [perronLogDerivativeIntegrand, Complex.cpow_one, div_one,
    one_mul, mul_div_assoc, mul_assoc] using
    (tendsto_principal_negative_logDeriv_residue_one q).mul
      (hweight.tendsto.mono_left nhdsWithin_le_nhds)

/-- A simple zero of a nonprincipal L-function contributes the negative
weighted residue `-x^β / β`. Simplicity is an explicit local premise only. -/
theorem tendsto_nonprincipal_perronLogDerivativeIntegrand_simple_zero_residue
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (x : ℝ) (hx : 0 < x) (β : ℂ) (hβ : β ≠ 0)
    (hzero : DirichletCharacter.LFunction χ β = 0)
    (hsimple : deriv (DirichletCharacter.LFunction χ) β ≠ 0) :
    Tendsto (fun s : ℂ => (s - β) * perronLogDerivativeIntegrand q χ x s)
      (𝓝[≠] β) (𝓝 (-(x : ℂ) ^ β / β)) := by
  have hL := (DirichletCharacter.differentiable_LFunction hχ).analyticAt β
  have hlog := (hL.tendsto_mul_logDeriv_simple_zero hzero hsimple).neg
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hweight : ContinuousAt (fun s : ℂ => (x : ℂ) ^ s / s) β :=
    (continuousAt_const_cpow hxC).div continuousAt_id hβ
  simpa only [perronLogDerivativeIntegrand, logDeriv_apply, neg_div, mul_neg,
    neg_mul, neg_one_mul, one_mul, mul_div_assoc, mul_assoc] using
    hlog.mul (hweight.tendsto.mono_left nhdsWithin_le_nhds)

/-- Real exceptional-zero specialization, retaining the exact `1 / β` factor. -/
theorem tendsto_nonprincipal_perronLogDerivativeIntegrand_real_simple_zero_residue
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (x : ℝ) (hx : 0 < x) (β : ℝ) (hβ : β ≠ 0)
    (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0)
    (hsimple : deriv (DirichletCharacter.LFunction χ) (β : ℂ) ≠ 0) :
    Tendsto (fun s : ℂ => (s - (β : ℂ)) * perronLogDerivativeIntegrand q χ x s)
      (𝓝[≠] (β : ℂ)) (𝓝 ((-(x ^ β) / β : ℝ) : ℂ)) := by
  have hβC : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  simpa only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_cpow hx.le] using
    tendsto_nonprincipal_perronLogDerivativeIntegrand_simple_zero_residue
      q χ hχ x hx (β : ℂ) hβC hzero hsimple

/-- The magnitude of the real-zero weighted residue is exactly `x^β / β`. -/
theorem norm_perron_real_zero_residue (x β : ℝ) (hx : 0 < x) (hβ : 0 < β) :
    ‖-(x : ℂ) ^ (β : ℂ) / (β : ℂ)‖ = x ^ β / β := by
  rw [norm_div, norm_neg, ← Complex.ofReal_cpow hx.le]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hx.le β), abs_of_pos hβ]

/-- A zero to the right of `1/2` has residue magnitude at most `2*x^β`.
This does not imply a bound by only `x^β`. -/
theorem norm_perron_real_zero_residue_le_two_rpow
    (x β : ℝ) (hx : 0 < x) (hβ : 1 / 2 < β) :
    ‖-(x : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ 2 * x ^ β := by
  have hβpos : 0 < β := by linarith
  rw [norm_perron_real_zero_residue x β hx hβpos]
  apply (div_le_iff₀ hβpos).mpr
  nlinarith [Real.rpow_nonneg hx.le β]

/-- The amount by which the exact zero residue exceeds the source allowance
`x^β` is explicitly `x^β * (1 - β) / β`. -/
theorem norm_perron_real_zero_residue_eq_rpow_add_excess
    (x β : ℝ) (hx : 0 < x) (hβ : 0 < β) :
    ‖-(x : ℂ) ^ (β : ℂ) / (β : ℂ)‖ =
      x ^ β + x ^ β * (1 - β) / β := by
  rw [norm_perron_real_zero_residue x β hx hβ]
  field_simp [hβ.ne']
  ring

/-- For `1/2 ≤ β ≤ 1`, the excess is nonnegative and at most `x^β`.
Making it exponentially small still requires the quantified Siegel estimate. -/
theorem perron_real_zero_residue_excess_nonneg_le_rpow
    (x β : ℝ) (hx : 0 < x) (hβ : 1 / 2 ≤ β) (hβone : β ≤ 1) :
    0 ≤ x ^ β * (1 - β) / β ∧ x ^ β * (1 - β) / β ≤ x ^ β := by
  have hβpos : 0 < β := by linarith
  constructor
  · exact div_nonneg
      (mul_nonneg (Real.rpow_nonneg hx.le β) (sub_nonneg.mpr hβone)) hβpos.le
  · apply (div_le_iff₀ hβpos).mpr
    nlinarith [Real.rpow_nonneg hx.le β]

private theorem intervalIntegral_abs_add_one_inv (H : ℝ) (hH : 0 ≤ H) :
    ∫ t in -H..H, 1 / (|t| + 1) = 2 * Real.log (H + 1) := by
  let f : ℝ → ℝ := fun t => 1 / (|t| + 1)
  have hden (t : ℝ) : |t| + 1 ≠ 0 := by positivity
  have hdencont : Continuous (fun t : ℝ => |t| + 1) := by fun_prop
  have hfcont : Continuous f := by
    dsimp [f]
    exact continuous_const.div hdencont hden
  have hfi (a b : ℝ) : IntervalIntegrable f volume a b :=
    Continuous.intervalIntegrable (μ := volume) hfcont a b
  have hneg : (∫ t in -H..0, f t) = ∫ t in 0..H, f t := by
    calc
      (∫ t in -H..0, f t) = ∫ t in 0..H, f (-t) := by
        simpa only [neg_zero] using
          (intervalIntegral.integral_comp_neg (f := f) (a := 0) (b := H)).symm
      _ = ∫ t in 0..H, f t := by
        apply intervalIntegral.integral_congr
        intro t _
        simp [f]
  have hpos : (∫ t in 0..H, f t) = Real.log (H + 1) := by
    have hcongr : (∫ t in 0..H, f t) = ∫ t in 0..H, 1 / (t + 1) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : 0 ≤ t := by
        have ht'' : t ∈ Set.uIcc (0 : ℝ) H := ht
        rw [uIcc_of_le hH] at ht''
        exact ht''.1
      simp [f, abs_of_nonneg ht']
    rw [hcongr, intervalIntegral.integral_comp_add_right (fun u : ℝ => 1 / u) 1]
    simp only [zero_add]
    rw [integral_one_div_of_pos (by norm_num : (0 : ℝ) < 1)
      (by linarith : (0 : ℝ) < H + 1)]
    simp
  calc
    (∫ t in -H..H, f t) =
        (∫ t in -H..0, f t) + ∫ t in 0..H, f t := by
          symm
          exact intervalIntegral.integral_add_adjacent_intervals (hfi _ _) (hfi _ _)
    _ = 2 * Real.log (H + 1) := by rw [hneg, hpos]; ring

/-- The unnormalized vertical integral has an explicit logarithmic bound from
the actual logarithmic-derivative supremum on the segment. -/
theorem norm_integral_perronLogDerivativeIntegrand_vertical_le
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (_hχ : χ ≠ 1)
    (x H σ M : ℝ) (hx : 0 < x) (hH : 0 ≤ H) (hσ : 1 / 2 ≤ σ) (hM : 0 ≤ M)
    (hbound : ∀ t : ℝ, |t| ≤ H →
      DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 ∧
      ‖logDeriv (DirichletCharacter.LFunction χ)
        ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M) :
    ‖∫ t in -H..H, perronLogDerivativeIntegrand q χ x
      ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        6 * M * x ^ σ * Real.log (H + 1) := by
  let f : ℝ → ℂ := fun t => perronLogDerivativeIntegrand q χ x
    ((σ : ℂ) + (t : ℂ) * Complex.I)
  let g : ℝ → ℝ := fun t => 3 * M * x ^ σ / (|t| + 1)
  have hpoint : ∀ t ∈ Set.Ioc (-H) H, ‖f t‖ ≤ g t := by
    intro t ht
    have htabs : |t| ≤ H := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
    have hsre : s.re = σ := by simp [s]
    have hsim : s.im = t := by simp [s]
    have hlognorm := (hbound t htabs).2
    have hnorm_id : ‖perronLogDerivativeIntegrand q χ x s‖ =
        ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ σ / ‖s‖ := by
      unfold perronLogDerivativeIntegrand
      simp only [logDeriv_apply, norm_div, norm_mul, norm_neg,
        Complex.norm_cpow_eq_rpow_re_of_pos hx, hsre]
    have hsre_le : σ ≤ ‖s‖ := by
      rw [← hsre]
      exact le_trans (le_abs_self _) (Complex.abs_re_le_norm s)
    have hsim_le : |t| ≤ ‖s‖ := by
      rw [← hsim]
      exact Complex.abs_im_le_norm s
    have hsgeHalf : 1 / 2 ≤ ‖s‖ := le_trans hσ hsre_le
    have hspos : 0 < ‖s‖ := lt_of_lt_of_le (by norm_num) hsgeHalf
    have hdenpos : 0 < |t| + 1 := by positivity
    have hrecip : 1 / ‖s‖ ≤ 3 / (|t| + 1) := by
      apply (div_le_div_iff₀ hspos hdenpos).2
      nlinarith [hsgeHalf, hsim_le]
    have hrpow : 0 ≤ x ^ σ := Real.rpow_nonneg hx.le σ
    calc
      ‖f t‖ = ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ σ / ‖s‖ := by
        simpa [f] using hnorm_id
      _ ≤ M * x ^ σ / ‖s‖ := by
        apply div_le_div_of_nonneg_right ?_ hspos.le
        exact mul_le_mul_of_nonneg_right hlognorm hrpow
      _ = M * x ^ σ * (1 / ‖s‖) := by ring
      _ ≤ M * x ^ σ * (3 / (|t| + 1)) :=
        mul_le_mul_of_nonneg_left hrecip (mul_nonneg hM hrpow)
      _ = g t := by dsimp [g]; ring
  have hpointAE : ∀ᵐ t ∂volume, t ∈ Set.Ioc (-H) H → ‖f t‖ ≤ g t :=
    Filter.Eventually.of_forall fun t ht => hpoint t ht
  have hgden : ∀ t : ℝ, |t| + 1 ≠ 0 := fun t => by positivity
  have hgdencont : Continuous (fun t : ℝ => |t| + 1) := by fun_prop
  have hgcont : Continuous g := by
    dsimp [g]
    exact continuous_const.div hgdencont hgden
  have hgi : IntervalIntegrable g volume (-H) H :=
    Continuous.intervalIntegrable (μ := volume) hgcont (-H) H
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le
    (by linarith : -H ≤ H) hpointAE hgi
  calc
    ‖∫ t in -H..H, perronLogDerivativeIntegrand q χ x
        ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ ∫ t in -H..H, g t := by
      simpa [f] using hnorm
    _ = 3 * M * x ^ σ * (2 * Real.log (H + 1)) := by
      have hgEq : g = fun t : ℝ => (3 * M * x ^ σ) * (1 / (|t| + 1)) := by
        funext t
        dsimp [g]
        ring
      rw [hgEq, intervalIntegral.integral_const_mul,
        intervalIntegral_abs_add_one_inv H hH]
    _ = 6 * M * x ^ σ * Real.log (H + 1) := by ring

#print axioms norm_integral_perronLogDerivativeIntegrand_vertical_le

/-- The unnormalized horizontal Perron integral is bounded by the actual
logarithmic-derivative supremum along that edge. -/
theorem norm_integral_perronLogDerivativeIntegrand_horizontal_le
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (_hχ : χ ≠ 1)
    (x σL σR τ M : ℝ) (hx : 1 ≤ x) (hσ : σL ≤ σR)
    (hτ : τ ≠ 0) (hM : 0 ≤ M)
    (hbound : ∀ u ∈ Set.Icc σL σR,
      DirichletCharacter.LFunction χ ((u : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 ∧
      ‖logDeriv (DirichletCharacter.LFunction χ)
        ((u : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ M) :
    ‖∫ u in σL..σR, perronLogDerivativeIntegrand q χ x
      ((u : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
        (σR - σL) * M * x ^ σR / |τ| := by
  let f : ℝ → ℂ := fun u => perronLogDerivativeIntegrand q χ x
    ((u : ℂ) + (τ : ℂ) * Complex.I)
  let C : ℝ := M * x ^ σR / |τ|
  have hτpos : 0 < |τ| := abs_pos.mpr hτ
  have hpoint : ∀ u ∈ Set.Icc σL σR, ‖f u‖ ≤ C := by
    intro u hu
    let s : ℂ := (u : ℂ) + (τ : ℂ) * Complex.I
    have hsre : s.re = u := by simp [s]
    have hsim : s.im = τ := by simp [s]
    have hlognorm := (hbound u hu).2
    have huRpow : x ^ u ≤ x ^ σR :=
      Real.rpow_le_rpow_of_exponent_le hx hu.2
    have hrpow : 0 ≤ x ^ u := Real.rpow_nonneg (by linarith : 0 ≤ x) u
    have hnorm_id : ‖perronLogDerivativeIntegrand q χ x s‖ =
        ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ u / ‖s‖ := by
      unfold perronLogDerivativeIntegrand
      simp only [logDeriv_apply, norm_div, norm_mul, norm_neg,
        Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < x), hsre]
    have hsimle : |τ| ≤ ‖s‖ := by
      rw [← hsim]
      exact Complex.abs_im_le_norm s
    have hnormpos : 0 < ‖s‖ := lt_of_lt_of_le hτpos hsimle
    have hrecip : 1 / ‖s‖ ≤ 1 / |τ| := by
      apply (div_le_div_iff₀ hnormpos hτpos).2
      nlinarith [hsimle]
    calc
      ‖f u‖ = ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ u / ‖s‖ := by
        simpa [f] using hnorm_id
      _ ≤ M * x ^ u / ‖s‖ := by
        apply div_le_div_of_nonneg_right ?_ hnormpos.le
        exact mul_le_mul_of_nonneg_right hlognorm hrpow
      _ = M * x ^ u * (1 / ‖s‖) := by ring
      _ ≤ M * x ^ u * (1 / |τ|) :=
        mul_le_mul_of_nonneg_left hrecip (mul_nonneg hM hrpow)
      _ ≤ M * x ^ σR * (1 / |τ|) := by
        apply mul_le_mul_of_nonneg_right ?_ (by positivity : 0 ≤ 1 / |τ|)
        exact mul_le_mul_of_nonneg_left huRpow hM
      _ = C := by dsimp [C]; ring
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := σL) (b := σR) (C := C) (f := f) (by
      intro u hu
      have hu' : u ∈ Set.Icc σL σR := by
        rw [uIoc_of_le hσ] at hu
        exact ⟨hu.1.le, hu.2⟩
      exact hpoint u hu')
  calc
    ‖∫ u in σL..σR, perronLogDerivativeIntegrand q χ x
        ((u : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ C * |σR - σL| := by
      simpa [f] using hnorm
    _ = (σR - σL) * M * x ^ σR / |τ| := by
      rw [abs_of_nonneg (sub_nonneg.mpr hσ)]
      dsimp [C]
      ring

#print axioms norm_integral_perronLogDerivativeIntegrand_horizontal_le

end SystolicGrowth.CookMagyarCircle

#print axioms SystolicGrowth.CookMagyarCircle.principal_negative_logDeriv_eq_pole_add_remainder
#print axioms SystolicGrowth.CookMagyarCircle.analyticAt_principalLogDerivRegularRemainder_one
#print axioms SystolicGrowth.CookMagyarCircle.principal_perronLogDerivativeIntegrand_eq_pole_add_dslope
#print axioms SystolicGrowth.CookMagyarCircle.analyticAt_principal_perronLogDerivativeIntegrand_regular_part_one
#print axioms SystolicGrowth.CookMagyarCircle.eventually_principal_perronLogDerivativeIntegrand_eq_pole_add_regular_part
#print axioms SystolicGrowth.CookMagyarCircle.tendsto_principal_perronLogDerivativeIntegrand_residue_one
#print axioms SystolicGrowth.CookMagyarCircle.tendsto_nonprincipal_perronLogDerivativeIntegrand_simple_zero_residue
#print axioms SystolicGrowth.CookMagyarCircle.tendsto_nonprincipal_perronLogDerivativeIntegrand_real_simple_zero_residue
#print axioms SystolicGrowth.CookMagyarCircle.norm_perron_real_zero_residue_le_two_rpow
#print axioms SystolicGrowth.CookMagyarCircle.perron_real_zero_residue_excess_nonneg_le_rpow
