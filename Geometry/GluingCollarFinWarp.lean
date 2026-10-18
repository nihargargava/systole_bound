module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarFinScalar
public import Geometry.GluingCollarWarpRegularity
public import Geometry.LipschitzCoordinateCalculus
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# Uniform fin-boundary estimate for the actual collar warp

On any bounded signed-radius interval, the actual collar warp and its smooth
derivative satisfy the scalar AB04 boundary criterion at one explicit scale.
This is a scalar input to the fin construction, not a metric curvature result.
-/

open Filter MeasureTheory Set
open scoped NNReal Topology

namespace SystolicGrowth

private theorem complex_band_speed_perturbation (a d p q : ℝ) :
    ‖((a * d : ℝ) : ℂ) + Complex.I * ((p + q * d : ℝ) : ℂ)‖ ≤
      ‖((d : ℝ) : ℂ) + Complex.I * ((p : ℝ) : ℂ)‖ +
        (|a - 1| + |q|) * |d| := by
  have hsplit :
      ((a * d : ℝ) : ℂ) + Complex.I * ((p + q * d : ℝ) : ℂ) =
        (((d : ℝ) : ℂ) + Complex.I * ((p : ℝ) : ℂ)) +
          ((((a - 1) * d : ℝ) : ℂ) +
            Complex.I * ((q * d : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [hsplit]
  have herr :
      ‖((((a - 1) * d : ℝ) : ℂ) +
          Complex.I * ((q * d : ℝ) : ℂ))‖ ≤
        (|a - 1| + |q|) * |d| := by
    have hreal : ‖(((a - 1) * d : ℝ) : ℂ)‖ = |a - 1| * |d| := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have himag : ‖Complex.I * ((q * d : ℝ) : ℂ)‖ = |q| * |d| := by
      rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      ring
    calc
      _ ≤ ‖(((a - 1) * d : ℝ) : ℂ)‖ +
          ‖Complex.I * ((q * d : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = |a - 1| * |d| + |q| * |d| := by rw [hreal, himag]
      _ = _ := by ring
  exact (norm_add_le _ _).trans (add_le_add le_rfl herr)

private theorem complex_band_speed_horizontal_scale_mono (c x y : ℝ)
    (hc : 1 ≤ c) :
    ‖((x : ℝ) : ℂ) + Complex.I * ((y : ℝ) : ℂ)‖ ≤
      ‖((c * x : ℝ) : ℂ) + Complex.I * ((y : ℝ) : ℂ)‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  apply Real.sqrt_le_sqrt
  simp only [Complex.normSq_apply, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, add_zero, Complex.add_im,
    Complex.mul_im]
  nlinarith [sq_nonneg x, mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg x)]

/-- The pointwise speed comparison for an AB04 band coordinate map. If
`u=f*s` and `u'=f*y' + s*f'*t'`, then replacing the original collar speed
`|(t', f*y')|` by the `cs_k` speed `|(cosh(λu)t', u')|` costs at most the
explicit multiplicative-warp and band-shear error times `|t'|`. This is the
local estimate to integrate along target curves in the distance-limit proof. -/
theorem gluingCollarFinBand_pointwise_speed_bound
    {lam ε M₀ M₁ f f' s t' y' : ℝ}
    (hlam : 0 ≤ lam) (hε : 0 ≤ ε) (hM₀ : 0 ≤ M₀)
    (hs : |s| ≤ ε) (hf : |f| ≤ M₀) (hf' : |f'| ≤ M₁) :
    ‖((Real.cosh (lam * (f * s)) * t' : ℝ) : ℂ) +
        Complex.I * ((f * y' + s * f' * t' : ℝ) : ℂ)‖ ≤
      ‖((t' : ℝ) : ℂ) + Complex.I * ((f * y' : ℝ) : ℂ)‖ +
        (Real.cosh (lam * (ε * M₀)) - 1 + ε * M₁) * |t'| := by
  have hfs : |f * s| ≤ M₀ * ε := by
    calc
      |f * s| = |f| * |s| := abs_mul f s
      _ ≤ M₀ * ε := mul_le_mul hf hs (abs_nonneg s) hM₀
  have hA : 0 ≤ lam * (ε * M₀) := by positivity
  have harg : |lam * (f * s)| ≤ lam * (ε * M₀) := by
    rw [abs_mul, abs_of_nonneg hlam]
    calc
      lam * |f * s| ≤ lam * (M₀ * ε) :=
        mul_le_mul_of_nonneg_left hfs hlam
      _ = lam * (ε * M₀) := by ring
  have hcosh : Real.cosh (lam * (f * s)) ≤ Real.cosh (lam * (ε * M₀)) :=
    Real.cosh_le_cosh.mpr (harg.trans_eq (abs_of_nonneg hA).symm)
  have hcoshOne : 1 ≤ Real.cosh (lam * (f * s)) := Real.one_le_cosh _
  have hmul : |s * f'| ≤ ε * M₁ := by
    calc
      |s * f'| = |s| * |f'| := abs_mul s f'
      _ ≤ ε * M₁ := mul_le_mul hs hf' (abs_nonneg f') hε
  have herror : |Real.cosh (lam * (f * s)) - 1| + |s * f'| ≤
      Real.cosh (lam * (ε * M₀)) - 1 + ε * M₁ := by
    rw [abs_of_nonneg (sub_nonneg.mpr hcoshOne)]
    linarith
  have h := complex_band_speed_perturbation
    (Real.cosh (lam * (f * s))) t' (f * y') (s * f')
  calc
    _ ≤ ‖((t' : ℝ) : ℂ) + Complex.I * ((f * y' : ℝ) : ℂ)‖ +
        (|Real.cosh (lam * (f * s)) - 1| + |s * f'|) * |t'| := by
          simpa [mul_add, add_assoc, add_left_comm, add_comm] using h
    _ ≤ _ := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_right herror (abs_nonneg t'))

/-- Multiplicative form of the forward AB04 band speed comparison. The source
speed controls the radial component `|t'|`, so the additive shear estimate is
also a relative estimate, uniformly over the band. -/
theorem gluingCollarFinBand_forward_speed_distortion
    {lam ε M₀ M₁ f f' s t' y' : ℝ}
    (hlam : 0 ≤ lam) (hε : 0 ≤ ε) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hs : |s| ≤ ε) (hf : |f| ≤ M₀) (hf' : |f'| ≤ M₁) :
    ‖((Real.cosh (lam * (f * s)) * t' : ℝ) : ℂ) +
        Complex.I * ((f * y' + s * f' * t' : ℝ) : ℂ)‖ ≤
      (1 + (Real.cosh (lam * (ε * M₀)) - 1 + ε * M₁)) *
        ‖((t' : ℝ) : ℂ) + Complex.I * ((f * y' : ℝ) : ℂ)‖ := by
  have hpoint := gluingCollarFinBand_pointwise_speed_bound
    (t' := t') (y' := y') hlam hε hM₀ hs hf hf'
  have hradial : |t'| ≤
      ‖((t' : ℝ) : ℂ) + Complex.I * ((f * y' : ℝ) : ℂ)‖ := by
    simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero, abs_of_nonneg (abs_nonneg t')] using
        (Complex.abs_re_le_norm
          (((t' : ℝ) : ℂ) + Complex.I * ((f * y' : ℝ) : ℂ)))
  have hδ : 0 ≤ Real.cosh (lam * (ε * M₀)) - 1 + ε * M₁ := by
    exact add_nonneg (sub_nonneg.mpr (Real.one_le_cosh _))
      (mul_nonneg hε hM₁)
  calc
    _ ≤ ‖((t' : ℝ) : ℂ) + Complex.I * ((f * y' : ℝ) : ℂ)‖ +
        (Real.cosh (lam * (ε * M₀)) - 1 + ε * M₁) * |t'| := hpoint
    _ ≤ ‖((t' : ℝ) : ℂ) + Complex.I * ((f * y' : ℝ) : ℂ)‖ +
        (Real.cosh (lam * (ε * M₀)) - 1 + ε * M₁) *
          ‖((t' : ℝ) : ℂ) + Complex.I * ((f * y' : ℝ) : ℂ)‖ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hradial hδ)
    _ = _ := by ring

/-- Reverse pointwise speed comparison for the AB04 band map. The vertical
shear `s*f'*t'` costs at most `ε*M₁` times the finite-curvature target speed;
the target's horizontal coefficient `cosh(λ*f*s) ≥ 1` controls `|t'|`.
Together with `gluingCollarFinBand_pointwise_speed_bound`, this gives the two
pointwise inequalities needed before integrating lengths for distance
convergence. -/
theorem gluingCollarFinBand_inverse_pointwise_speed_bound
    {lam ε M₁ f f' s t' u' : ℝ}
    (hε : 0 ≤ ε) (hM₁ : 0 ≤ M₁)
    (hs : |s| ≤ ε) (hf' : |f'| ≤ M₁) :
    ‖((t' : ℝ) : ℂ) + Complex.I * ((u' - s * f' * t' : ℝ) : ℂ)‖ ≤
      (1 + ε * M₁) *
        ‖((Real.cosh (lam * (f * s)) * t' : ℝ) : ℂ) +
          Complex.I * ((u' : ℝ) : ℂ)‖ := by
  have hcosh : 1 ≤ Real.cosh (lam * (f * s)) := Real.one_le_cosh _
  have hbase := complex_band_speed_horizontal_scale_mono
    (Real.cosh (lam * (f * s))) t' u' hcosh
  have hshear : |s * f'| ≤ ε * M₁ := by
    calc
      |s * f'| = |s| * |f'| := abs_mul s f'
      _ ≤ ε * M₁ := mul_le_mul hs hf' (abs_nonneg f') hε
  have hperturb := complex_band_speed_perturbation
    1 t' u' (-s * f')
  have htarget_horizontal : |t'| ≤
      ‖((Real.cosh (lam * (f * s)) * t' : ℝ) : ℂ) +
        Complex.I * ((u' : ℝ) : ℂ)‖ := by
    have hcoord : |Real.cosh (lam * (f * s)) * t'| ≤
        ‖((Real.cosh (lam * (f * s)) * t' : ℝ) : ℂ) +
          Complex.I * ((u' : ℝ) : ℂ)‖ := by
      simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        sub_zero, add_zero] using
          (Complex.abs_re_le_norm
            (((Real.cosh (lam * (f * s)) * t' : ℝ) : ℂ) +
              Complex.I * ((u' : ℝ) : ℂ)))
    have hcosh_nonneg : 0 ≤ Real.cosh (lam * (f * s)) :=
      (le_trans (by norm_num) hcosh)
    rw [abs_mul, abs_of_nonneg hcosh_nonneg] at hcoord
    nlinarith [mul_nonneg (sub_nonneg.mpr hcosh) (abs_nonneg t')]
  calc
    _ ≤ ‖((t' : ℝ) : ℂ) + Complex.I * ((u' : ℝ) : ℂ)‖ +
        |s * f'| * |t'| := by
          simpa [mul_add, add_assoc, add_left_comm, add_comm,
            abs_neg, sub_eq_add_neg, mul_assoc] using hperturb
    _ ≤ ‖((Real.cosh (lam * (f * s)) * t' : ℝ) : ℂ) +
          Complex.I * ((u' : ℝ) : ℂ)‖ +
        (ε * M₁) * ‖((Real.cosh (lam * (f * s)) * t' : ℝ) : ℂ) +
          Complex.I * ((u' : ℝ) : ℂ)‖ := by
          exact add_le_add hbase
            (mul_le_mul hshear htarget_horizontal (abs_nonneg t') (by positivity))
    _ = _ := by ring

/-- The scalar fin-boundary estimate holds uniformly on a bounded interval for
the actual collar warp, with an explicit scale depending only on the interval
and its derivative bounds. -/
theorem gluingCollarFinWarp_uniform_boundary_estimate
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧
      ∀ t ∈ Icc (-R) R, t ≠ 0 →
        (1 - ε) *
          (Real.cosh (Real.sqrt (1 - ε) * ε * gluingCollarWarp r t) *
              Real.sinh (Real.sqrt (1 - ε) * ε * gluingCollarWarp r t) /
                (Real.sqrt (1 - ε) * ε * gluingCollarWarp r t) +
            2 * ε ^ 2 * (deriv (gluingCollarWarp r) t) ^ 2 *
              Real.tanh (Real.sqrt (1 - ε) * ε * gluingCollarWarp r t) /
                (Real.sqrt (1 - ε) * ε * gluingCollarWarp r t)) ≤ 1 := by
  let M : ℝ := Real.sinh (r + R)
  let D : ℝ := Real.cosh (r + R)
  let A : ℝ := M ^ 2 * Real.cosh M ^ 2 + 2 * D ^ 2
  let ε : ℝ := 1 / (A + 2)
  have hM : 0 < M := by
    dsimp [M]
    exact Real.sinh_pos_iff.mpr (by linarith)
  have hD : 0 ≤ D := by
    dsimp [D]
    exact (Real.cosh_pos _).le
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hden : 0 < A + 2 := by linarith
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hε' : ε < 1 / 2 := by
    have hden' : 2 < A + 2 := by linarith
    change 1 / (A + 2) < 1 / 2
    exact one_div_lt_one_div_of_lt (by norm_num) hden'
  have hsmall : ε * A ≤ 1 := by
    calc
      ε * A = A / (A + 2) := by dsimp [ε]; ring
      _ ≤ 1 := (div_le_iff₀ hden).2 (by linarith)
  have hDexpr : D = Real.cosh (|r| + R) := by
    dsimp [D]
    rw [abs_of_pos hr]
  refine ⟨ε, hε, hε', ?_⟩
  intro t ht ht0
  let F : ℝ := gluingCollarWarp r t
  let p : ℝ := deriv (gluingCollarWarp r) t
  have hF : 0 < F := by
    dsimp [F]
    exact gluingCollarWarp_pos hr t
  have hFle : F ≤ M := by
    dsimp [F, M]
    have htabs : |t| ≤ R := abs_le.mpr ht
    rw [gluingCollarWarp]
    exact Real.sinh_le_sinh.mpr (by nlinarith)
  have hp : |p| ≤ D := by
    dsimp [p]
    rw [hDexpr]
    exact gluingCollarWarp_deriv_abs_le r hR ht ht0
  have hsmall' : ε *
      (M ^ 2 * Real.cosh M ^ 2 + 2 * D ^ 2) ≤ 1 := by
    simpa [A] using hsmall
  have h := gluingCollarFinScalar_boundary_estimate hε hε' hF hFle hM hp hD hsmall'
  simpa [F, p] using h

/-- Convert the scalar AB04 boundary criterion at a fixed positive scale into
the geodesic-graph acceleration inequality. The scale need not be the
particular explicit one chosen by
`gluingCollarFinWarp_uniform_boundary_acceleration`; this form is what lets a
dyadic approximating sequence reuse the same comparison argument. -/
theorem gluingCollarFinWarp_boundary_estimate_implies_acceleration
    {r R ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (hε' : ε < 1 / 2)
    (hboundary : ∀ t ∈ Icc (-R) R, t ≠ 0 →
      (1 - ε) *
        (Real.cosh (Real.sqrt (1 - ε) * ε * gluingCollarWarp r t) *
            Real.sinh (Real.sqrt (1 - ε) * ε * gluingCollarWarp r t) /
              (Real.sqrt (1 - ε) * ε * gluingCollarWarp r t) +
          2 * ε ^ 2 * (deriv (gluingCollarWarp r) t) ^ 2 *
            Real.tanh (Real.sqrt (1 - ε) * ε * gluingCollarWarp r t) /
              (Real.sqrt (1 - ε) * ε * gluingCollarWarp r t)) ≤ 1) :
    ∀ t ∈ Icc (-R) R, t ≠ 0 →
      let α := Real.sqrt (1 - ε)
      α * Real.cosh (α * ε * gluingCollarWarp r t) *
          Real.sinh (α * ε * gluingCollarWarp r t) +
        2 * α * ε ^ 2 * (deriv (gluingCollarWarp r) t) ^ 2 *
          Real.tanh (α * ε * gluingCollarWarp r t) ≤
        ε * gluingCollarWarp r t := by
  intro t ht ht0
  let α : ℝ := Real.sqrt (1 - ε)
  let F : ℝ := gluingCollarWarp r t
  let p : ℝ := deriv (gluingCollarWarp r) t
  let x : ℝ := α * ε * F
  have hα : 0 < α := by
    dsimp [α]
    exact Real.sqrt_pos.2 (by linarith)
  have hF : 0 < F := by
    dsimp [F]
    exact gluingCollarWarp_pos hr t
  have hx : 0 < x := by dsimp [x]; positivity
  have hαsq : α ^ 2 = 1 - ε := by
    dsimp [α]
    exact Real.sq_sqrt (by linarith)
  have hb := hboundary t ht ht0
  have hb' : (1 - ε) *
      (Real.cosh x * Real.sinh x / x +
        2 * ε ^ 2 * p ^ 2 * Real.tanh x / x) ≤ 1 := by
    simpa [α, F, p, x] using hb
  have hmul := mul_le_mul_of_nonneg_right hb' hx.le
  have hmul' : α ^ 2 *
        (Real.cosh x * Real.sinh x +
          2 * ε ^ 2 * p ^ 2 * Real.tanh x) ≤ α * ε * F := by
    calc
      _ = (1 - ε) *
          (Real.cosh x * Real.sinh x +
            2 * ε ^ 2 * p ^ 2 * Real.tanh x) := by rw [hαsq]
      _ = (1 - ε) *
          (Real.cosh x * Real.sinh x / x +
            2 * ε ^ 2 * p ^ 2 * Real.tanh x / x) * x := by
        field_simp [hx.ne']
      _ ≤ x := by simpa [mul_comm] using hmul
      _ = α * ε * F := by simp [x, mul_assoc]
  have hcancel : α *
        (α * (Real.cosh x * Real.sinh x +
          2 * ε ^ 2 * p ^ 2 * Real.tanh x)) ≤ α * (ε * F) := by
    convert hmul' using 1 <;> ring
  have hfinal : α * (Real.cosh x * Real.sinh x +
      2 * ε ^ 2 * p ^ 2 * Real.tanh x) ≤ ε * F :=
    (mul_le_mul_iff_right₀ hα).mp hcancel
  calc
    _ = α * (Real.cosh x * Real.sinh x +
        2 * ε ^ 2 * p ^ 2 * Real.tanh x) := by ring
    _ ≤ ε * F := hfinal
    _ = _ := by rfl

/-- On every bounded window, the scaled fin graph satisfies the direct
geodesic-graph acceleration inequality corresponding to its nonnegative
geodesic curvature. This is the scalar ODE barrier input for convexity. -/
theorem gluingCollarFinWarp_uniform_boundary_acceleration
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧
      ∀ t ∈ Icc (-R) R, t ≠ 0 →
        let α := Real.sqrt (1 - ε)
        α * Real.cosh (α * ε * gluingCollarWarp r t) *
            Real.sinh (α * ε * gluingCollarWarp r t) +
          2 * α * ε ^ 2 * (deriv (gluingCollarWarp r) t) ^ 2 *
            Real.tanh (α * ε * gluingCollarWarp r t) ≤
          ε * gluingCollarWarp r t := by
  obtain ⟨ε, hε, hε', hboundary⟩ :=
    gluingCollarFinWarp_uniform_boundary_estimate hr hR
  refine ⟨ε, hε, hε', ?_⟩
  intro t ht ht0
  let α : ℝ := Real.sqrt (1 - ε)
  let F : ℝ := gluingCollarWarp r t
  let p : ℝ := deriv (gluingCollarWarp r) t
  let x : ℝ := α * ε * F
  have hα : 0 < α := by
    dsimp [α]
    exact Real.sqrt_pos.2 (by linarith)
  have hF : 0 < F := by
    dsimp [F]
    exact gluingCollarWarp_pos hr t
  have hx : 0 < x := by dsimp [x]; positivity
  have hαsq : α ^ 2 = 1 - ε := by
    dsimp [α]
    exact Real.sq_sqrt (by linarith)
  have hb := hboundary t ht ht0
  have hb' : (1 - ε) *
      (Real.cosh x * Real.sinh x / x +
        2 * ε ^ 2 * p ^ 2 * Real.tanh x / x) ≤ 1 := by
    simpa [α, F, p, x] using hb
  have hmul := mul_le_mul_of_nonneg_right hb' hx.le
  have hmul' : α ^ 2 *
        (Real.cosh x * Real.sinh x +
          2 * ε ^ 2 * p ^ 2 * Real.tanh x) ≤ α * ε * F := by
    calc
      _ = (1 - ε) *
          (Real.cosh x * Real.sinh x +
            2 * ε ^ 2 * p ^ 2 * Real.tanh x) := by rw [hαsq]
      _ = (1 - ε) *
          (Real.cosh x * Real.sinh x / x +
            2 * ε ^ 2 * p ^ 2 * Real.tanh x / x) * x := by
        field_simp [hx.ne']
      _ ≤ x := by simpa [mul_comm] using hmul
      _ = α * ε * F := by simp [x, mul_assoc]
  have hcancel : α *
        (α * (Real.cosh x * Real.sinh x +
          2 * ε ^ 2 * p ^ 2 * Real.tanh x)) ≤ α * (ε * F) := by
    convert hmul' using 1 <;> ring
  have hfinal : α * (Real.cosh x * Real.sinh x +
      2 * ε ^ 2 * p ^ 2 * Real.tanh x) ≤ ε * F :=
    (mul_le_mul_iff_right₀ hα).mp hcancel
  calc
    _ = α * (Real.cosh x * Real.sinh x +
        2 * ε ^ 2 * p ^ 2 * Real.tanh x) := by ring
    _ ≤ ε * F := hfinal
    _ = _ := by rfl

/-- On a fixed bounded window, every sufficiently fine dyadic AB04 scale
`εₙ = 2⁻ⁿ` satisfies the actual collar's scalar fin-boundary criterion.
The proof uses the explicit window majorant, so the threshold may depend on
`r` and `R` but is uniform in `t` and all later dyadic indices. -/
theorem gluingCollarFinWarp_dyadic_boundary_estimate_eventually
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ t ∈ Icc (-R) R, t ≠ 0 →
        (1 - (1 / 2 : ℝ) ^ n) *
          (Real.cosh (Real.sqrt (1 - (1 / 2 : ℝ) ^ n) *
                (1 / 2 : ℝ) ^ n * gluingCollarWarp r t) *
              Real.sinh (Real.sqrt (1 - (1 / 2 : ℝ) ^ n) *
                (1 / 2 : ℝ) ^ n * gluingCollarWarp r t) /
                (Real.sqrt (1 - (1 / 2 : ℝ) ^ n) *
                  (1 / 2 : ℝ) ^ n * gluingCollarWarp r t) +
            2 * ((1 / 2 : ℝ) ^ n) ^ 2 *
              (deriv (gluingCollarWarp r) t) ^ 2 *
              Real.tanh (Real.sqrt (1 - (1 / 2 : ℝ) ^ n) *
                (1 / 2 : ℝ) ^ n * gluingCollarWarp r t) /
                (Real.sqrt (1 - (1 / 2 : ℝ) ^ n) *
                  (1 / 2 : ℝ) ^ n * gluingCollarWarp r t)) ≤ 1 := by
  let M : ℝ := Real.sinh (r + R)
  let D : ℝ := Real.cosh (r + R)
  let A : ℝ := M ^ 2 * Real.cosh M ^ 2 + 2 * D ^ 2
  have hM : 0 < M := by
    dsimp [M]
    exact Real.sinh_pos_iff.mpr (by linarith)
  have hD : 0 ≤ D := by
    dsimp [D]
    exact (Real.cosh_pos _).le
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hden : 0 < A + 2 := by linarith
  let δ : ℝ := 1 / (A + 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδhalf : δ < 1 / 2 := by
    dsimp [δ]
    apply one_div_lt_one_div_of_lt (by norm_num)
    linarith
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ
    (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨N, fun n hn t ht ht0 => ?_⟩
  let ε : ℝ := (1 / 2 : ℝ) ^ n
  have hpow : ε ≤ (1 / 2 : ℝ) ^ N := by
    dsimp [ε]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have hεδ : ε < δ := by
    dsimp [δ] at hN ⊢
    exact hpow.trans_lt hN
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hε' : ε < 1 / 2 := hεδ.trans hδhalf
  have hεA : ε * A ≤ 1 := by
    have hεA' : ε * A ≤ δ * A := mul_le_mul_of_nonneg_right hεδ.le hA.le
    have hδA : δ * A ≤ 1 := by
      dsimp [δ]
      calc
        _ = A / (A + 2) := by rw [div_eq_mul_inv]; ring
        _ ≤ 1 := (div_le_one hden).2 (by linarith)
    exact hεA'.trans hδA
  have hDexpr : D = Real.cosh (|r| + R) := by
    dsimp [D]
    rw [abs_of_pos hr]
  let F : ℝ := gluingCollarWarp r t
  let p : ℝ := deriv (gluingCollarWarp r) t
  have hF : 0 < F := by
    dsimp [F]
    exact gluingCollarWarp_pos hr t
  have hFle : F ≤ M := by
    dsimp [F, M]
    have htabs : |t| ≤ R := abs_le.mpr ht
    rw [gluingCollarWarp]
    exact Real.sinh_le_sinh.mpr (by nlinarith)
  have hp : |p| ≤ D := by
    dsimp [p]
    rw [hDexpr]
    exact gluingCollarWarp_deriv_abs_le r hR ht ht0
  have hsmall : ε *
      (M ^ 2 * Real.cosh M ^ 2 + 2 * D ^ 2) ≤ 1 := by
    simpa only [A] using hεA
  have h := gluingCollarFinScalar_boundary_estimate hε hε' hF hFle hM hp hD hsmall
  simpa only [F, p, ε] using h

/-- The actual one-sided derivative jump at the seam is positive. -/
theorem gluingCollarFinWarp_seam_jump_pos (r : ℝ) :
    0 < derivWithin (gluingCollarWarp r) (Ici 0) 0 -
      derivWithin (gluingCollarWarp r) (Iic 0) 0 :=
  gluingCollarWarp_deriv_jump_pos r

/-- Away from the seam, the actual collar warp is exactly `F_{-1}`-affine:
its ordinary second derivative equals itself. The seam is handled by the
separate positive one-sided slope jump, not by this smooth identity. -/
theorem gluingCollarFinWarp_second_deriv_eq (r : ℝ) {t : ℝ} (ht : t ≠ 0) :
    deriv (deriv (gluingCollarWarp r)) t = gluingCollarWarp r t :=
  (gluingCollarWarp_hasDerivAt_deriv r ht).deriv

/-- Scaling the actual fin profile by a constant scales its classical second
derivative on each smooth side of the seam. -/
theorem gluingCollarFinWarp_scaled_second_deriv_eq
    (ε r : ℝ) {t : ℝ} (ht : t ≠ 0) :
    deriv (deriv (fun s => ε * gluingCollarWarp r s)) t =
      ε * gluingCollarWarp r t := by
  have hinner : deriv (fun s : ℝ => ε * gluingCollarWarp r s) =
      fun s => ε * deriv (gluingCollarWarp r) s := by
    funext s
    exact deriv_const_mul_field ε
  rw [hinner, deriv_const_mul_field,
    gluingCollarFinWarp_second_deriv_eq r ht]

/-- Scaling the actual collar profile by the AB04 fin width scales its weak
`F_{-1}` second derivative, including the positive atom at the seam. This is
the distributional curvature input for the actual fin boundary; it is not a
metric convexity claim. -/
theorem gluingCollarFinWarp_scaled_integral_second_deriv_sub
    (ε r : ℝ) {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφa : φ a = 0) (hφb : φ b = 0)
    (hφ'a : deriv φ a = 0) (hφ'b : deriv φ b = 0) :
    (∫ t in a..b, (ε * gluingCollarWarp r t) *
        (deriv (deriv φ) t - φ t)) = ε * (2 * Real.cosh r * φ 0) := by
  calc
    _ = ∫ t in a..b, ε *
        (gluingCollarWarp r t * (deriv (deriv φ) t - φ t)) := by
      congr 1
      funext t
      ring
    _ = ε * (∫ t in a..b, gluingCollarWarp r t *
        (deriv (deriv φ) t - φ t)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = ε * (2 * Real.cosh r * φ 0) := by
      rw [gluingCollarWarp_integral_second_deriv_sub r ha hb hφ hφa hφb hφ'a hφ'b]

/-- A nonnegative fin width preserves the collar profile's weak
`F_{-1}`-convexity on every interval crossing the seam. The seam mass is
explicitly `2 * ε * cosh r * φ(0)`. -/
theorem gluingCollarFinWarp_scaled_distributional_FMinusOneConvex
    {ε r : ℝ} (hε : 0 ≤ ε) {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφa : φ a = 0) (hφb : φ b = 0)
    (hφ'a : deriv φ a = 0) (hφ'b : deriv φ b = 0)
    (hφnonneg : ∀ t ∈ Icc a b, 0 ≤ φ t) :
    0 ≤ ∫ t in a..b, (ε * gluingCollarWarp r t) *
      (deriv (deriv φ) t - φ t) := by
  rw [gluingCollarFinWarp_scaled_integral_second_deriv_sub ε r ha hb hφ
    hφa hφb hφ'a hφ'b]
  exact mul_nonneg hε (mul_nonneg (mul_nonneg (by norm_num) (Real.cosh_pos r).le)
    (hφnonneg 0 ⟨ha.le, hb.le⟩))

/-- The fixed-band angular output has the expected a.e. derivative, including
times when the radial coordinate lies on the seam. At the seam, the radial
curve and its warped image both have derivative zero almost everywhere on
their level sets, so no null-preimage assumption is needed. The range bound
keeps the warp Lipschitz on the interval containing the radial path. -/
theorem gluingCollarFinBand_product_deriv_ae
    {a b r R c : ℝ} {u v : ℝ → ℝ} {Ku Kv : ℝ≥0}
    (hab : a ≤ b) (hR : 0 ≤ R)
    (hu : LipschitzOnWith Ku u (Icc a b))
    (hv : LipschitzOnWith Kv v (Icc a b))
    (hrange : ∀ t ∈ Icc a b, u t ∈ Icc (-R) R) :
    ∀ᵐ t ∂volume.restrict (Icc a b),
      deriv (fun s => gluingCollarWarp r (u s) * (v s - c)) t =
        (deriv (gluingCollarWarp r) (u t) * deriv u t) * (v t - c) +
          gluingCollarWarp r (u t) * deriv v t := by
  let q : ℝ → ℝ := fun t => gluingCollarWarp r (u t)
  have hwarp := gluingCollarWarp_lipschitzOnWith r hR
  have hq : LipschitzOnWith
      (⟨Real.cosh (|r| + R), (Real.cosh_pos _).le⟩ * Ku) q (Icc a b) := by
    change LipschitzOnWith _ (fun t => gluingCollarWarp r (u t)) (Icc a b)
    exact hwarp.comp hu (by
      intro t ht
      exact hrange t ht)
  have huIcc : LipschitzOnWith Ku u (uIcc a b) := by
    simpa only [uIcc_of_le hab] using hu
  have hvIcc : LipschitzOnWith Kv v (uIcc a b) := by
    simpa only [uIcc_of_le hab] using hv
  have hqIcc : LipschitzOnWith
      (⟨Real.cosh (|r| + R), (Real.cosh_pos _).le⟩ * Ku) q (uIcc a b) := by
    simpa only [uIcc_of_le hab] using hq
  have huAC := huIcc.absolutelyContinuousOnInterval
  have hvAC := hvIcc.absolutelyContinuousOnInterval
  have hqAC := hqIcc.absolutelyContinuousOnInterval
  have huZero := deriv_eq_zero_ae_on_level_set u 0
  have hqZero := deriv_eq_zero_ae_on_level_set q (gluingCollarWarp r 0)
  filter_upwards
      [ae_restrict_of_ae huAC.ae_differentiableAt,
        ae_restrict_of_ae hvAC.ae_differentiableAt,
        ae_restrict_of_ae hqAC.ae_differentiableAt,
        ae_restrict_of_ae huZero,
        ae_restrict_of_ae hqZero,
        ae_restrict_mem measurableSet_Icc] with t hdu hdv hdq hUz hqz ht
  have htI : t ∈ uIcc a b := by
    simpa only [uIcc_of_le hab] using ht
  have hdu' := hdu htI
  have hdv' := hdv htI
  have hdq' := hdq htI
  change deriv (fun s => q s * (v s - c)) t = _
  by_cases hu0 : u t = 0
  · have hq0 : q t = gluingCollarWarp r 0 := by simp [q, hu0]
    have hp := hdq'.hasDerivAt.mul (hdv'.hasDerivAt.sub_const c)
    change deriv (q * (fun s => v s - c)) t = _
    rw [hp.deriv, hqz hq0, hUz hu0, hq0, hu0]
    ring
  · have hwarp' := gluingCollarWarp_hasDerivAt_of_ne r hu0
    have hq' : HasDerivAt q
        (deriv (gluingCollarWarp r) (u t) * deriv u t) t := by
      simpa only [q, Function.comp_def] using hwarp'.comp t hdu'.hasDerivAt
    have hp := hq'.mul (hdv'.hasDerivAt.sub_const c)
    exact hp.deriv

/-- Source speed of a collar-coordinate curve, represented as a complex norm
so it can be compared directly with the two real Fermi-coordinate
components. -/
noncomputable def gluingCollarFinBandSourceSpeed
    (r : ℝ) (u v : ℝ → ℝ) (t : ℝ) : ℝ :=
  ‖((deriv u t : ℝ) : ℂ) + Complex.I *
    ((gluingCollarWarp r (u t) * deriv v t : ℝ) : ℂ)‖

/-- Finite-curvature target speed of the image of a fixed-band curve, in the
Fermi metric `du² + cosh(λu)² dt²`. -/
noncomputable def gluingCollarFinBandTargetSpeed
    (r lam c : ℝ) (u v : ℝ → ℝ) (t : ℝ) : ℝ :=
  ‖((Real.cosh (lam * (gluingCollarWarp r (u t) * (v t - c))) *
      deriv u t : ℝ) : ℂ) + Complex.I *
    ((deriv (fun s => gluingCollarWarp r (u s) * (v s - c)) t : ℝ) : ℂ)‖

/-- On a fixed AB04 band over a bounded radial window, the map from collar
coordinates to the finite-curvature Fermi strip distorts speed by the explicit
AB04 factor. The derivative identity handles the radial seam and all values
on the closed band boundary; neither preimage is discarded. -/
theorem gluingCollarFinBand_forward_speed_le_ae
    {a b r R c lam ε M₀ M₁ : ℝ} {u v : ℝ → ℝ} {Ku Kv : ℝ≥0}
    (hab : a ≤ b) (hR : 0 ≤ R)
    (hu : LipschitzOnWith Ku u (Icc a b))
    (hv : LipschitzOnWith Kv v (Icc a b))
    (hrange : ∀ t ∈ Icc a b, u t ∈ Icc (-R) R)
    (hlam : 0 ≤ lam) (hε : 0 ≤ ε) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hband : ∀ t ∈ Icc a b, |v t - c| ≤ ε)
    (hprofile : ∀ t ∈ Icc a b, |gluingCollarWarp r (u t)| ≤ M₀)
    (hslope : ∀ t ∈ Icc a b,
      |deriv (gluingCollarWarp r) (u t)| ≤ M₁) :
    ∀ᵐ t ∂volume.restrict (Icc a b),
      gluingCollarFinBandTargetSpeed r lam c u v t ≤
        (1 + (Real.cosh (lam * (ε * M₀)) - 1 + ε * M₁)) *
          gluingCollarFinBandSourceSpeed r u v t := by
  have hderiv := gluingCollarFinBand_product_deriv_ae
    (r := r) hab hR hu hv hrange (c := c)
  filter_upwards [hderiv, ae_restrict_mem measurableSet_Icc] with t hdt ht
  change ‖((Real.cosh (lam * (gluingCollarWarp r (u t) * (v t - c))) *
      deriv u t : ℝ) : ℂ) + Complex.I *
    ((deriv (fun s => gluingCollarWarp r (u s) * (v s - c)) t : ℝ) : ℂ)‖ ≤
    (1 + (Real.cosh (lam * (ε * M₀)) - 1 + ε * M₁)) *
      ‖((deriv u t : ℝ) : ℂ) + Complex.I *
        ((gluingCollarWarp r (u t) * deriv v t : ℝ) : ℂ)‖
  have hdt' :
      deriv (fun s => gluingCollarWarp r (u s) * (v s - c)) t =
        gluingCollarWarp r (u t) * deriv v t +
          (v t - c) * deriv (gluingCollarWarp r) (u t) * deriv u t := by
    rw [hdt]
    ring
  rw [hdt']
  exact gluingCollarFinBand_forward_speed_distortion
    (f := gluingCollarWarp r (u t))
    (f' := deriv (gluingCollarWarp r) (u t))
    (s := v t - c) (t' := deriv u t) (y' := deriv v t)
    hlam hε hM₀ hM₁ (hband t ht) (hprofile t ht) (hslope t ht)

/-- Integrating the a.e. fixed-band speed comparison gives the corresponding
weighted-length bound. No differentiability at interval endpoints or at the
radial seam is required. -/
theorem gluingCollarFinBand_forward_length_le
    {a b r R c lam ε M₀ M₁ : ℝ} {u v : ℝ → ℝ} {Ku Kv : ℝ≥0}
    (hab : a ≤ b) (hR : 0 ≤ R)
    (hu : LipschitzOnWith Ku u (Icc a b))
    (hv : LipschitzOnWith Kv v (Icc a b))
    (hrange : ∀ t ∈ Icc a b, u t ∈ Icc (-R) R)
    (hlam : 0 ≤ lam) (hε : 0 ≤ ε) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hband : ∀ t ∈ Icc a b, |v t - c| ≤ ε)
    (hprofile : ∀ t ∈ Icc a b, |gluingCollarWarp r (u t)| ≤ M₀)
    (hslope : ∀ t ∈ Icc a b,
      |deriv (gluingCollarWarp r) (u t)| ≤ M₁) :
    ∫⁻ t in Icc a b, ENNReal.ofReal (gluingCollarFinBandTargetSpeed r lam c u v t) ≤
      ∫⁻ t in Icc a b, ENNReal.ofReal
        ((1 + (Real.cosh (lam * (ε * M₀)) - 1 + ε * M₁)) *
          gluingCollarFinBandSourceSpeed r u v t) := by
  apply lintegral_mono_ae
  filter_upwards [gluingCollarFinBand_forward_speed_le_ae
    hab hR hu hv hrange hlam hε hM₀ hM₁ hband hprofile hslope] with t ht
  exact ENNReal.ofReal_le_ofReal ht

/-- The inverse differential of a fixed-band map also distorts speed by an
explicit factor. This inequality is stated on the same source path as the
forward estimate, using the product derivative to recover the inverse
vertical component `f*v' = U' - (v-c)*f'*u'`. -/
theorem gluingCollarFinBand_inverse_speed_le_ae
    {a b r R c lam ε M₁ : ℝ} {u v : ℝ → ℝ} {Ku Kv : ℝ≥0}
    (hab : a ≤ b) (hR : 0 ≤ R)
    (hu : LipschitzOnWith Ku u (Icc a b))
    (hv : LipschitzOnWith Kv v (Icc a b))
    (hrange : ∀ t ∈ Icc a b, u t ∈ Icc (-R) R)
    (hε : 0 ≤ ε) (hM₁ : 0 ≤ M₁)
    (hband : ∀ t ∈ Icc a b, |v t - c| ≤ ε)
    (hslope : ∀ t ∈ Icc a b,
      |deriv (gluingCollarWarp r) (u t)| ≤ M₁) :
    ∀ᵐ t ∂volume.restrict (Icc a b),
      gluingCollarFinBandSourceSpeed r u v t ≤
        (1 + ε * M₁) * gluingCollarFinBandTargetSpeed r lam c u v t := by
  have hderiv := gluingCollarFinBand_product_deriv_ae
    (r := r) hab hR hu hv hrange (c := c)
  filter_upwards [hderiv, ae_restrict_mem measurableSet_Icc] with t hdt ht
  change ‖((deriv u t : ℝ) : ℂ) + Complex.I *
      ((gluingCollarWarp r (u t) * deriv v t : ℝ) : ℂ)‖ ≤
    (1 + ε * M₁) *
      ‖((Real.cosh (lam * (gluingCollarWarp r (u t) * (v t - c))) *
          deriv u t : ℝ) : ℂ) + Complex.I *
        ((deriv (fun s => gluingCollarWarp r (u s) * (v s - c)) t : ℝ) : ℂ)‖
  have hvertical :
      gluingCollarWarp r (u t) * deriv v t =
        deriv (fun s => gluingCollarWarp r (u s) * (v s - c)) t -
          (v t - c) * deriv (gluingCollarWarp r) (u t) * deriv u t := by
    rw [hdt]
    ring
  rw [hvertical]
  exact gluingCollarFinBand_inverse_pointwise_speed_bound
    (lam := lam) (f := gluingCollarWarp r (u t))
    (f' := deriv (gluingCollarWarp r) (u t)) (s := v t - c)
    (t' := deriv u t)
    (u' := deriv (fun s => gluingCollarWarp r (u s) * (v s - c)) t)
    hε hM₁ (hband t ht) (hslope t ht)

/-- Integrating the inverse fixed-band speed comparison gives the reverse
weighted-length bound, again across seam and band-boundary times. -/
theorem gluingCollarFinBand_inverse_length_le
    {a b r R c lam ε M₁ : ℝ} {u v : ℝ → ℝ} {Ku Kv : ℝ≥0}
    (hab : a ≤ b) (hR : 0 ≤ R)
    (hu : LipschitzOnWith Ku u (Icc a b))
    (hv : LipschitzOnWith Kv v (Icc a b))
    (hrange : ∀ t ∈ Icc a b, u t ∈ Icc (-R) R)
    (hε : 0 ≤ ε) (hM₁ : 0 ≤ M₁)
    (hband : ∀ t ∈ Icc a b, |v t - c| ≤ ε)
    (hslope : ∀ t ∈ Icc a b,
      |deriv (gluingCollarWarp r) (u t)| ≤ M₁) :
    ∫⁻ t in Icc a b, ENNReal.ofReal (gluingCollarFinBandSourceSpeed r u v t) ≤
      ∫⁻ t in Icc a b, ENNReal.ofReal
        ((1 + ε * M₁) * gluingCollarFinBandTargetSpeed r lam c u v t) := by
  apply lintegral_mono_ae
  filter_upwards [gluingCollarFinBand_inverse_speed_le_ae
    hab hR hu hv hrange hε hM₁ hband hslope] with t ht
  exact ENNReal.ofReal_le_ofReal ht

/-- The forward fixed-band length estimate with all warp bounds discharged
from the actual closed radial window. -/
theorem gluingCollarFinBand_forward_length_le_window
    {a b r R c lam ε : ℝ} {u v : ℝ → ℝ} {Ku Kv : ℝ≥0}
    (hr : 0 < r) (hab : a ≤ b) (hR : 0 ≤ R)
    (hu : LipschitzOnWith Ku u (Icc a b))
    (hv : LipschitzOnWith Kv v (Icc a b))
    (hrange : ∀ t ∈ Icc a b, u t ∈ Icc (-R) R)
    (hlam : 0 ≤ lam) (hε : 0 ≤ ε)
    (hband : ∀ t ∈ Icc a b, |v t - c| ≤ ε) :
    ∫⁻ t in Icc a b, ENNReal.ofReal
      (gluingCollarFinBandTargetSpeed r lam c u v t) ≤
    ∫⁻ t in Icc a b, ENNReal.ofReal
      ((1 + (Real.cosh (lam * (ε * Real.sinh (r + R))) - 1 +
        ε * Real.cosh (|r| + R))) *
        gluingCollarFinBandSourceSpeed r u v t) := by
  have hM₀ : 0 ≤ Real.sinh (r + R) :=
    Real.sinh_nonneg_iff.mpr (by linarith)
  exact gluingCollarFinBand_forward_length_le hab hR hu hv hrange
    hlam hε hM₀ (Real.cosh_pos _).le hband
    (fun t ht => gluingCollarWarp_abs_le_window hr (hrange t ht))
    (fun t ht => gluingCollarWarp_deriv_abs_le_all r hR (hrange t ht))

/-- The reverse fixed-band length estimate with the seam derivative covered
by the same uniform window bound. -/
theorem gluingCollarFinBand_inverse_length_le_window
    {a b r R c lam ε : ℝ} {u v : ℝ → ℝ} {Ku Kv : ℝ≥0}
    (hab : a ≤ b) (hR : 0 ≤ R)
    (hu : LipschitzOnWith Ku u (Icc a b))
    (hv : LipschitzOnWith Kv v (Icc a b))
    (hrange : ∀ t ∈ Icc a b, u t ∈ Icc (-R) R)
    (hε : 0 ≤ ε)
    (hband : ∀ t ∈ Icc a b, |v t - c| ≤ ε) :
    ∫⁻ t in Icc a b, ENNReal.ofReal
      (gluingCollarFinBandSourceSpeed r u v t) ≤
    ∫⁻ t in Icc a b, ENNReal.ofReal
      ((1 + ε * Real.cosh (|r| + R)) *
        gluingCollarFinBandTargetSpeed r lam c u v t) := by
  exact gluingCollarFinBand_inverse_length_le hab hR hu hv hrange hε
    (Real.cosh_pos _).le hband
    (fun t ht => gluingCollarWarp_deriv_abs_le_all r hR (hrange t ht))

/-- The fixed-band forward length distortion factors outside the integral,
so it can be passed through the ensuing path infimum. -/
theorem gluingCollarFinBand_forward_length_le_mul
    {a b r R c lam ε : ℝ} {u v : ℝ → ℝ} {Ku Kv : ℝ≥0}
    (hr : 0 < r) (hab : a ≤ b) (hR : 0 ≤ R)
    (hu : LipschitzOnWith Ku u (Icc a b))
    (hv : LipschitzOnWith Kv v (Icc a b))
    (hrange : ∀ t ∈ Icc a b, u t ∈ Icc (-R) R)
    (hlam : 0 ≤ lam) (hε : 0 ≤ ε)
    (hband : ∀ t ∈ Icc a b, |v t - c| ≤ ε) :
    ∫⁻ t in Icc a b, ENNReal.ofReal
      (gluingCollarFinBandTargetSpeed r lam c u v t) ≤
    ENNReal.ofReal (1 + (Real.cosh (lam * (ε * Real.sinh (r + R))) - 1 +
      ε * Real.cosh (|r| + R))) *
      ∫⁻ t in Icc a b, ENNReal.ofReal
        (gluingCollarFinBandSourceSpeed r u v t) := by
  let D : ℝ := 1 + (Real.cosh (lam * (ε * Real.sinh (r + R))) - 1 +
    ε * Real.cosh (|r| + R))
  have hD : 0 ≤ D := by
    dsimp [D]
    nlinarith [Real.one_le_cosh (lam * (ε * Real.sinh (r + R))),
      mul_nonneg hε (Real.cosh_pos (|r| + R)).le]
  calc
    _ ≤ ∫⁻ t in Icc a b, ENNReal.ofReal
        (D * gluingCollarFinBandSourceSpeed r u v t) := by
          exact gluingCollarFinBand_forward_length_le_window
            hr hab hR hu hv hrange hlam hε hband
    _ = ∫⁻ t in Icc a b, ENNReal.ofReal D *
        ENNReal.ofReal (gluingCollarFinBandSourceSpeed r u v t) := by
          congr 1
          funext t
          exact ENNReal.ofReal_mul hD
    _ = _ := by
          exact lintegral_const_mul' _ _ (by simp)

/-- The reverse fixed-band length distortion also factors outside the
integral, with a constant depending only on the window and band width. -/
theorem gluingCollarFinBand_inverse_length_le_mul
    {a b r R c lam ε : ℝ} {u v : ℝ → ℝ} {Ku Kv : ℝ≥0}
    (hab : a ≤ b) (hR : 0 ≤ R)
    (hu : LipschitzOnWith Ku u (Icc a b))
    (hv : LipschitzOnWith Kv v (Icc a b))
    (hrange : ∀ t ∈ Icc a b, u t ∈ Icc (-R) R)
    (hε : 0 ≤ ε)
    (hband : ∀ t ∈ Icc a b, |v t - c| ≤ ε) :
    ∫⁻ t in Icc a b, ENNReal.ofReal
      (gluingCollarFinBandSourceSpeed r u v t) ≤
    ENNReal.ofReal (1 + ε * Real.cosh (|r| + R)) *
      ∫⁻ t in Icc a b, ENNReal.ofReal
        (gluingCollarFinBandTargetSpeed r lam c u v t) := by
  have hD : 0 ≤ 1 + ε * Real.cosh (|r| + R) := by positivity
  calc
    _ ≤ ∫⁻ t in Icc a b, ENNReal.ofReal
        ((1 + ε * Real.cosh (|r| + R)) *
          gluingCollarFinBandTargetSpeed r lam c u v t) :=
            gluingCollarFinBand_inverse_length_le_window
              hab hR hu hv hrange hε hband
    _ = ∫⁻ t in Icc a b, ENNReal.ofReal
        (1 + ε * Real.cosh (|r| + R)) *
          ENNReal.ofReal (gluingCollarFinBandTargetSpeed r lam c u v t) := by
          congr 1
          funext t
          exact ENNReal.ofReal_mul hD
    _ = _ := by
          exact lintegral_const_mul' _ _ (by simp)

/-- A path confined to one AB04 band has an admissible ordinary-Lipschitz
image in the finite Fermi strip. This is the regularity input needed to use
the fixed-band length comparison in a path-infimum distance. -/
theorem gluingCollarFinBand_image_lipschitz
    {a b r R c ε M₀ : ℝ} {u v : ℝ → ℝ} {Ku Kv : ℝ≥0}
    (hR : 0 ≤ R)
    (hu : LipschitzOnWith Ku u (Icc a b))
    (hv : LipschitzOnWith Kv v (Icc a b))
    (hrange : ∀ t ∈ Icc a b, u t ∈ Icc (-R) R)
    (hε : 0 ≤ ε) (hM₀ : 0 ≤ M₀)
    (hband : ∀ t ∈ Icc a b, |v t - c| ≤ ε)
    (hprofile : ∀ t ∈ Icc a b, |gluingCollarWarp r (u t)| ≤ M₀) :
    ∃ K : ℝ≥0, LipschitzOnWith K
      (fun t => ((u t : ℝ) : ℂ) + Complex.I *
        ((gluingCollarWarp r (u t) * (v t - c) : ℝ) : ℂ)) (Icc a b) := by
  let C : ℝ≥0 := ⟨Real.cosh (|r| + R), (Real.cosh_pos _).le⟩
  let K : ℝ≥0 := ⟨M₀ * (Kv : ℝ) + ε * ((C * Ku : ℝ≥0) : ℝ), by positivity⟩
  have hq : LipschitzOnWith (C * Ku)
      (fun t => gluingCollarWarp r (u t)) (Icc a b) := by
    exact (gluingCollarWarp_lipschitzOnWith r hR).comp hu hrange
  have hw : LipschitzOnWith K
      (fun t => gluingCollarWarp r (u t) * (v t - c)) (Icc a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hqxy := hq.dist_le_mul x hx y hy
    have hvxy := hv.dist_le_mul x hx y hy
    rw [Real.dist_eq] at hqxy hvxy
    change |gluingCollarWarp r (u x) * (v x - c) -
      gluingCollarWarp r (u y) * (v y - c)| ≤ (K : ℝ) * dist x y
    have hsplit : gluingCollarWarp r (u x) * (v x - c) -
        gluingCollarWarp r (u y) * (v y - c) =
        gluingCollarWarp r (u x) * (v x - v y) +
          (gluingCollarWarp r (u x) - gluingCollarWarp r (u y)) *
            (v y - c) := by ring
    rw [hsplit]
    calc
      _ ≤ |gluingCollarWarp r (u x) * (v x - v y)| +
          |(gluingCollarWarp r (u x) - gluingCollarWarp r (u y)) *
            (v y - c)| := abs_add_le _ _
      _ = |gluingCollarWarp r (u x)| * |v x - v y| +
          |gluingCollarWarp r (u x) - gluingCollarWarp r (u y)| *
            |v y - c| := by rw [abs_mul, abs_mul]
      _ ≤ M₀ * ((Kv : ℝ) * dist x y) +
          ((C * Ku : ℝ≥0) : ℝ) * dist x y * ε := by
            gcongr
            · exact hprofile x hx
            · exact hband y hy
      _ = (K : ℝ) * dist x y := by
            change M₀ * ((Kv : ℝ) * dist x y) +
              ((C * Ku : ℝ≥0) : ℝ) * dist x y * ε =
                (M₀ * (Kv : ℝ) + ε * ((C * Ku : ℝ≥0) : ℝ)) * dist x y
            ring
  refine ⟨Ku + K, ?_⟩
  simpa only [mul_comm (Complex.I : ℂ)] using
    (lipschitzCoordinate_pair hu hw)

private theorem gluingCollarFinBand_inverse_quotient_bound
    {m ε fx fy wx wy : ℝ} (hm : 0 < m) (hfx : m ≤ fx) (hfy : m ≤ fy)
    (hε : 0 ≤ ε) (hwy : |wy| ≤ ε * fy) :
    |wx / fx - wy / fy| ≤ (|wx - wy| + ε * |fx - fy|) / m := by
  have hfx0 : 0 < fx := lt_of_lt_of_le hm hfx
  have hfy0 : 0 < fy := lt_of_lt_of_le hm hfy
  have hratio : |wy / fy| ≤ ε := by
    rw [abs_div, abs_of_pos hfy0]
    exact (div_le_iff₀ hfy0).2 hwy
  have hid : wx / fx - wy / fy =
      ((wx - wy) + (fy - fx) * (wy / fy)) / fx := by
    field_simp
    ring
  have hnum : |(wx - wy) + (fy - fx) * (wy / fy)| ≤
      |wx - wy| + ε * |fx - fy| := by
    calc
      _ ≤ |wx - wy| + |(fy - fx) * (wy / fy)| := abs_add_le _ _
      _ = |wx - wy| + |fx - fy| * |wy / fy| := by
        rw [abs_mul, abs_sub_comm fy fx]
      _ ≤ |wx - wy| + |fx - fy| * ε := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hratio (abs_nonneg _))
      _ = _ := by ring
  have hnonneg : 0 ≤ |wx - wy| + ε * |fx - fy| := by positivity
  rw [hid, abs_div, abs_of_pos hfx0]
  exact (div_le_div_of_nonneg_right hnum hfx0.le).trans
    (div_le_div_of_nonneg_left hnonneg hm hfx)

/-- A finite Fermi-strip path pulls back to an ordinary-Lipschitz collar
coordinate path. The strip condition supplies the relative vertical bound;
the positive minimum `sinh r` prevents division by a vanishing warp. -/
theorem gluingCollarFinBand_inverse_image_lipschitz
    {a b r R c ε : ℝ} {u w : ℝ → ℝ} {Ku Kw : ℝ≥0}
    (hr : 0 < r) (hR : 0 ≤ R)
    (hu : LipschitzOnWith Ku u (Icc a b))
    (hw : LipschitzOnWith Kw w (Icc a b))
    (hrange : ∀ t ∈ Icc a b, u t ∈ Icc (-R) R)
    (hε : 0 ≤ ε)
    (hstrip : ∀ t ∈ Icc a b,
      |w t| ≤ ε * gluingCollarWarp r (u t)) :
    ∃ K : ℝ≥0, LipschitzOnWith K
      (fun t => ((u t : ℝ) : ℂ) + Complex.I *
        (((w t / gluingCollarWarp r (u t) + c) : ℝ) : ℂ)) (Icc a b) := by
  let m := Real.sinh r
  have hm : 0 < m := Real.sinh_pos_iff.mpr hr
  let C : ℝ≥0 := ⟨Real.cosh (|r| + R), (Real.cosh_pos _).le⟩
  let K : ℝ≥0 :=
    ⟨((Kw : ℝ) + ε * ((C * Ku : ℝ≥0) : ℝ)) / m, by positivity⟩
  have hq : LipschitzOnWith (C * Ku)
      (fun t => gluingCollarWarp r (u t)) (Icc a b) := by
    exact (gluingCollarWarp_lipschitzOnWith r hR).comp hu hrange
  have hv : LipschitzOnWith K
      (fun t => w t / gluingCollarWarp r (u t)) (Icc a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hqxy := hq.dist_le_mul x hx y hy
    have hwxy := hw.dist_le_mul x hx y hy
    rw [Real.dist_eq] at hqxy hwxy
    change |w x / gluingCollarWarp r (u x) -
      w y / gluingCollarWarp r (u y)| ≤ (K : ℝ) * dist x y
    calc
      _ ≤ (|w x - w y| + ε *
          |gluingCollarWarp r (u x) - gluingCollarWarp r (u y)|) / m :=
            gluingCollarFinBand_inverse_quotient_bound hm
              (gluingCollarWarp_lower_bound r (u x))
              (gluingCollarWarp_lower_bound r (u y)) hε (hstrip y hy)
      _ ≤ (((Kw : ℝ) * dist x y) + ε *
          (((C * Ku : ℝ≥0) : ℝ) * dist x y)) / m := by
            apply div_le_div_of_nonneg_right ?_ hm.le
            exact add_le_add hwxy
              (mul_le_mul_of_nonneg_left hqxy hε)
      _ = (K : ℝ) * dist x y := by
            change (((Kw : ℝ) * dist x y) + ε *
              (((C * Ku : ℝ≥0) : ℝ) * dist x y)) / m =
                (((Kw : ℝ) + ε * ((C * Ku : ℝ≥0) : ℝ)) / m) * dist x y
            ring
  have hvc : LipschitzOnWith K
      (fun t => w t / gluingCollarWarp r (u t) + c) (Icc a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa [Real.dist_eq] using hv.dist_le_mul x hx y hy
  refine ⟨Ku + K, ?_⟩
  simpa only [mul_comm (Complex.I : ℂ)] using
    (lipschitzCoordinate_pair hu hvc)

/-- Coordinate map from one collar band to its finite Fermi strip. -/
noncomputable def gluingCollarFinBandForward (r c : ℝ) (z : ℂ) : ℂ :=
  (z.re : ℂ) + Complex.I *
    ((gluingCollarWarp r z.re * (z.im - c) : ℝ) : ℂ)

/-- The inverse coordinate map on the finite strip. -/
noncomputable def gluingCollarFinBandInverse (r c : ℝ) (z : ℂ) : ℂ :=
  (z.re : ℂ) + Complex.I *
    ((z.im / gluingCollarWarp r z.re + c : ℝ) : ℂ)

@[simp] theorem gluingCollarFinBandForward_re (r c : ℝ) (z : ℂ) :
    (gluingCollarFinBandForward r c z).re = z.re := by
  simp [gluingCollarFinBandForward]

@[simp] theorem gluingCollarFinBandForward_im (r c : ℝ) (z : ℂ) :
    (gluingCollarFinBandForward r c z).im =
      gluingCollarWarp r z.re * (z.im - c) := by
  simp [gluingCollarFinBandForward]

@[simp] theorem gluingCollarFinBandInverse_re (r c : ℝ) (z : ℂ) :
    (gluingCollarFinBandInverse r c z).re = z.re := by
  simp [gluingCollarFinBandInverse]

@[simp] theorem gluingCollarFinBandInverse_im (r c : ℝ) (z : ℂ) :
    (gluingCollarFinBandInverse r c z).im =
      z.im / gluingCollarWarp r z.re + c := by
  simp [gluingCollarFinBandInverse]

/-- The coordinate maps are genuine inverses, including at the radial seam. -/
theorem gluingCollarFinBandInverse_forward {r : ℝ} (hr : 0 < r) (c : ℝ) (z : ℂ) :
    gluingCollarFinBandInverse r c (gluingCollarFinBandForward r c z) = z := by
  apply Complex.ext
  · simp
  · simp only [gluingCollarFinBandInverse_im, gluingCollarFinBandForward_re,
      gluingCollarFinBandForward_im]
    have hf := (gluingCollarWarp_pos hr z.re).ne'
    field_simp
    ring

theorem gluingCollarFinBandForward_inverse {r : ℝ} (hr : 0 < r) (c : ℝ) (z : ℂ) :
    gluingCollarFinBandForward r c (gluingCollarFinBandInverse r c z) = z := by
  apply Complex.ext
  · simp
  · simp only [gluingCollarFinBandForward_im, gluingCollarFinBandInverse_re,
      gluingCollarFinBandInverse_im]
    have hf := (gluingCollarWarp_pos hr z.re).ne'
    field_simp
    ring

/-- A closed collar band maps into its variable-width Fermi strip. -/
theorem gluingCollarFinBandForward_mem_strip {r ε : ℝ} (hr : 0 < r)
    (c : ℝ) (z : ℂ) (hz : |z.im - c| ≤ ε) :
    |(gluingCollarFinBandForward r c z).im| ≤
      ε * gluingCollarWarp r z.re := by
  rw [gluingCollarFinBandForward_im, abs_mul,
    abs_of_pos (gluingCollarWarp_pos hr z.re)]
  simpa only [mul_comm] using
    (mul_le_mul_of_nonneg_left hz (gluingCollarWarp_pos hr z.re).le)

/-- A point of the variable-width strip pulls back into the closed band. -/
theorem gluingCollarFinBandInverse_mem_band {r ε : ℝ} (hr : 0 < r)
    (c : ℝ) (z : ℂ)
    (hz : |z.im| ≤ ε * gluingCollarWarp r z.re) :
    |(gluingCollarFinBandInverse r c z).im - c| ≤ ε := by
  rw [gluingCollarFinBandInverse_im, add_sub_cancel_right,
    abs_div, abs_of_pos (gluingCollarWarp_pos hr z.re)]
  exact (div_le_iff₀ (gluingCollarWarp_pos hr z.re)).2 hz

/-- The actual complex forward map sends every admissible band path to an
ordinary-Lipschitz target path on the same parameter interval. -/
theorem gluingCollarFinBandForward_path_lipschitz
    {a b r R c ε : ℝ} {α : ℝ → ℂ} {K : ℝ≥0}
    (hr : 0 < r) (hR : 0 ≤ R)
    (hα : LipschitzOnWith K α (Icc a b))
    (hrange : ∀ t ∈ Icc a b, (α t).re ∈ Icc (-R) R)
    (hε : 0 ≤ ε)
    (hband : ∀ t ∈ Icc a b, |(α t).im - c| ≤ ε) :
    ∃ K' : ℝ≥0, LipschitzOnWith K'
      (fun t => gluingCollarFinBandForward r c (α t)) (Icc a b) := by
  have hu : LipschitzOnWith K (fun t => (α t).re) (Icc a b) := by
    simpa [Function.comp_def] using
      (RCLike.lipschitzWith_re (K := ℂ)).comp_lipschitzOnWith hα
  have hv : LipschitzOnWith K (fun t => (α t).im) (Icc a b) := by
    simpa [Function.comp_def] using
      (RCLike.lipschitzWith_im (K := ℂ)).comp_lipschitzOnWith hα
  have hM₀ : 0 ≤ Real.sinh (r + R) :=
    Real.sinh_nonneg_iff.mpr (by linarith)
  simpa only [gluingCollarFinBandForward] using
    (gluingCollarFinBand_image_lipschitz hR hu hv hrange hε hM₀ hband
      (fun t ht => gluingCollarWarp_abs_le_window hr (hrange t ht)))

/-- The actual complex inverse map sends every admissible strip path to an
ordinary-Lipschitz collar path on the same parameter interval. -/
theorem gluingCollarFinBandInverse_path_lipschitz
    {a b r R c ε : ℝ} {β : ℝ → ℂ} {K : ℝ≥0}
    (hr : 0 < r) (hR : 0 ≤ R)
    (hβ : LipschitzOnWith K β (Icc a b))
    (hrange : ∀ t ∈ Icc a b, (β t).re ∈ Icc (-R) R)
    (hε : 0 ≤ ε)
    (hstrip : ∀ t ∈ Icc a b,
      |(β t).im| ≤ ε * gluingCollarWarp r (β t).re) :
    ∃ K' : ℝ≥0, LipschitzOnWith K'
      (fun t => gluingCollarFinBandInverse r c (β t)) (Icc a b) := by
  have hu : LipschitzOnWith K (fun t => (β t).re) (Icc a b) := by
    simpa [Function.comp_def] using
      (RCLike.lipschitzWith_re (K := ℂ)).comp_lipschitzOnWith hβ
  have hw : LipschitzOnWith K (fun t => (β t).im) (Icc a b) := by
    simpa [Function.comp_def] using
      (RCLike.lipschitzWith_im (K := ℂ)).comp_lipschitzOnWith hβ
  simpa only [gluingCollarFinBandInverse] using
    (gluingCollarFinBand_inverse_image_lipschitz hr hR hu hw hrange hε hstrip
      (c := c))

#print axioms gluingCollarFinWarp_uniform_boundary_estimate
#print axioms gluingCollarFinBand_pointwise_speed_bound
#print axioms gluingCollarFinBand_forward_speed_distortion
#print axioms gluingCollarFinBand_inverse_pointwise_speed_bound
#print axioms gluingCollarFinWarp_boundary_estimate_implies_acceleration
#print axioms gluingCollarFinWarp_uniform_boundary_acceleration
#print axioms gluingCollarFinWarp_dyadic_boundary_estimate_eventually
#print axioms gluingCollarFinWarp_seam_jump_pos
#print axioms gluingCollarFinWarp_second_deriv_eq
#print axioms gluingCollarFinWarp_scaled_second_deriv_eq
#print axioms gluingCollarFinWarp_scaled_integral_second_deriv_sub
#print axioms gluingCollarFinWarp_scaled_distributional_FMinusOneConvex
#print axioms gluingCollarFinBand_product_deriv_ae
#print axioms gluingCollarFinBand_forward_speed_le_ae
#print axioms gluingCollarFinBand_forward_length_le
#print axioms gluingCollarFinBand_inverse_speed_le_ae
#print axioms gluingCollarFinBand_inverse_length_le
#print axioms gluingCollarFinBand_forward_length_le_window
#print axioms gluingCollarFinBand_inverse_length_le_window
#print axioms gluingCollarFinBand_forward_length_le_mul
#print axioms gluingCollarFinBand_inverse_length_le_mul
#print axioms gluingCollarFinBand_image_lipschitz
#print axioms gluingCollarFinBand_inverse_image_lipschitz
#print axioms gluingCollarFinBandInverse_forward
#print axioms gluingCollarFinBandForward_inverse
#print axioms gluingCollarFinBandForward_mem_strip
#print axioms gluingCollarFinBandInverse_mem_band
#print axioms gluingCollarFinBandForward_path_lipschitz
#print axioms gluingCollarFinBandInverse_path_lipschitz

end SystolicGrowth
