module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.PerronKernelLeaf
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Topology.MetricSpace.Cauchy

@[expose] public section

/-!
# Oscillatory prerequisites for the scalar Perron kernel

The positive real base in `perronScalarKernel` has an explicit exponential
phase. Its numerator has a finite-interval oscillatory bound, and integration
by parts exposes one factor of `1 / log (x / k)` in the full scalar kernel.
These are prerequisites for, not substitutes for, the integrated far- and
near-range estimates in Montgomery--Vaughan, *Multiplicative Number Theory I*,
Section 5.1, formula (5.9).
-/

namespace SystolicGrowth.CookMagyarCircle

open MeasureTheory

/-- The positive-base complex power is a real amplitude times a unit-norm
oscillatory phase. -/
theorem perronCpow_phase {y : ℝ} (hy : 0 < y) (σ t : ℝ) :
    (y : ℂ) ^ ((σ : ℂ) + Complex.I * (t : ℂ)) =
      ((y ^ σ : ℝ) : ℂ) *
        Complex.exp ((Complex.I * (Real.log y : ℂ)) * (t : ℂ)) := by
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  rw [Complex.cpow_add _ _ hyC, ← Complex.ofReal_cpow hy.le,
    Complex.cpow_def_of_ne_zero hyC, ← Complex.ofReal_log hy.le]
  congr 1
  ring_nf

/-- The phase-amplitude form of the scalar Perron integrand. -/
theorem perronScalarKernel_phase (x σ t : ℝ) (k : ℕ)
    (hx : 0 < x) (hk : 0 < k) :
    perronScalarKernel x k σ t =
      (((x / (k : ℝ)) ^ σ : ℝ) : ℂ) *
          Complex.exp ((Complex.I * (Real.log (x / (k : ℝ)) : ℂ)) * (t : ℂ)) /
        ((σ : ℂ) + Complex.I * (t : ℂ)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hy : 0 < x / (k : ℝ) := div_pos hx hkR
  unfold perronScalarKernel
  rw [perronCpow_phase hy]

/-- For a half-integer endpoint, the logarithmic frequency is nonzero at
every positive integer index. -/
theorem perronHalfInteger_log_ne_zero (m k : ℕ) (hk : 0 < k) :
    Real.log (((m : ℝ) + 1 / 2) / (k : ℝ)) ≠ 0 := by
  have hx : (0 : ℝ) < (m : ℝ) + 1 / 2 := by positivity
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hy : (0 : ℝ) < ((m : ℝ) + 1 / 2) / (k : ℝ) := div_pos hx hkR
  intro hlog
  rcases Real.log_eq_zero.mp hlog with h0 | h1 | hneg
  · linarith
  · have hmk : (m : ℝ) + 1 / 2 = (k : ℝ) :=
      (div_eq_one_iff_eq hkR.ne').mp h1
    have hgap := perronHalfInteger_gap m k
    rw [hmk, sub_self, abs_zero] at hgap
    norm_num at hgap
  · linarith

/-- Exact cancellation in the positive-base numerator over a finite vertical
interval. The denominator of the Perron kernel is not included here. -/
theorem integral_perronNumerator_eq (y σ a b : ℝ) (hy : 0 < y)
    (hlog : Real.log y ≠ 0) :
    (∫ t in a..b, (y : ℂ) ^ ((σ : ℂ) + Complex.I * (t : ℂ))) =
      ((y ^ σ : ℝ) : ℂ) *
        ((Complex.exp ((Complex.I * (Real.log y : ℂ)) * (b : ℂ)) -
          Complex.exp ((Complex.I * (Real.log y : ℂ)) * (a : ℂ))) /
          (Complex.I * (Real.log y : ℂ))) := by
  have hc : Complex.I * (Real.log y : ℂ) ≠ 0 := by
    exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hlog)
  simp_rw [perronCpow_phase hy σ]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hc]

/-- A finite-interval oscillatory numerator bound, uniform in the interval
length. The gain is the reciprocal of the nonzero logarithmic frequency. -/
theorem norm_integral_perronNumerator_le (y σ a b : ℝ) (hy : 0 < y)
    (hlog : Real.log y ≠ 0) :
    ‖∫ t in a..b, (y : ℂ) ^ ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
      (2 * y ^ σ) / |Real.log y| := by
  let c : ℂ := Complex.I * (Real.log y : ℂ)
  have hc (t : ℝ) : ‖Complex.exp (c * (t : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp [c]
  have hnum : ‖Complex.exp (c * (b : ℂ)) - Complex.exp (c * (a : ℂ))‖ ≤ 2 := by
    calc
      _ ≤ ‖Complex.exp (c * (b : ℂ))‖ + ‖Complex.exp (c * (a : ℂ))‖ := norm_sub_le _ _
      _ = 2 := by rw [hc, hc]; norm_num
  have hden : ‖c‖ = |Real.log y| := by simp [c]
  have hcoef : ‖((y ^ σ : ℝ) : ℂ)‖ = y ^ σ := by
    simpa using (Real.norm_eq_abs (y ^ σ)).trans (abs_of_nonneg (Real.rpow_nonneg hy.le σ))
  have hpos : 0 < |Real.log y| := abs_pos.mpr hlog
  calc
    ‖∫ t in a..b, (y : ℂ) ^ ((σ : ℂ) + Complex.I * (t : ℂ))‖
        = (y ^ σ) * (‖Complex.exp (c * (b : ℂ)) - Complex.exp (c * (a : ℂ))‖ /
            |Real.log y|) := by
              rw [integral_perronNumerator_eq y σ a b hy hlog, norm_mul, norm_div,
                hcoef, hden]
    _ ≤ (y ^ σ) * (2 / |Real.log y|) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hy.le σ)
      exact (div_le_div_iff_of_pos_right hpos).mpr hnum
    _ = (2 * y ^ σ) / |Real.log y| := by ring

/-- One integration-by-parts step for the full oscillatory scalar kernel.
The identity makes the endpoint terms and the squared-denominator remainder
explicit. It is not yet a far- or near-range bound for the symmetric contour. -/
theorem perronPhaseKernel_integrationByParts (σ L a b : ℝ)
    (hσ : 0 < σ) (hL : L ≠ 0) :
    (∫ t in a..b,
      (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹) *
        Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ))) =
      (((σ : ℂ) + Complex.I * (b : ℂ))⁻¹) *
          (Complex.exp ((Complex.I * (L : ℂ)) * (b : ℂ)) /
            (Complex.I * (L : ℂ))) -
      (((σ : ℂ) + Complex.I * (a : ℂ))⁻¹) *
          (Complex.exp ((Complex.I * (L : ℂ)) * (a : ℂ)) /
            (Complex.I * (L : ℂ))) -
      (∫ t in a..b,
        (-Complex.I / (((σ : ℂ) + Complex.I * (t : ℂ)) ^ 2)) *
          (Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ)) /
            (Complex.I * (L : ℂ)))) := by
  let c : ℂ := Complex.I * (L : ℂ)
  have hc : c ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hL)
  have hden (t : ℝ) : (σ : ℂ) + Complex.I * (t : ℂ) ≠ 0 := by
    apply Complex.ne_zero_of_re_pos
    simpa using hσ
  have hs (t : ℝ) : HasDerivAt
      (fun u : ℝ => (σ : ℂ) + Complex.I * (u : ℂ)) Complex.I t := by
    convert (((hasDerivAt_id (t : ℂ)).const_mul Complex.I).const_add (σ : ℂ)).comp_ofReal
      using 1 <;> simp
  have hu (t : ℝ) : HasDerivAt
      (fun u : ℝ => ((σ : ℂ) + Complex.I * (u : ℂ))⁻¹)
      (-Complex.I / (((σ : ℂ) + Complex.I * (t : ℂ)) ^ 2)) t :=
    (hs t).inv (hden t)
  have hv (t : ℝ) : HasDerivAt
      (fun u : ℝ => Complex.exp (c * (u : ℂ)) / c)
      (Complex.exp (c * (t : ℂ))) t := by
    have hlin : HasDerivAt (fun u : ℝ => c * (u : ℂ)) c t := by
      simpa only [mul_one] using! ((hasDerivAt_id (t : ℂ)).const_mul c).comp_ofReal
    have hd := ((Complex.hasDerivAt_exp _).comp t hlin).div_const c
    simpa [Function.comp_def, hc] using hd
  have hu'cont : Continuous (fun t : ℝ =>
      -Complex.I / (((σ : ℂ) + Complex.I * (t : ℂ)) ^ 2)) := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro t
      exact pow_ne_zero _ (hden t)
  have hv'cont : Continuous (fun t : ℝ => Complex.exp (c * (t : ℂ))) := by
    fun_prop
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => ((σ : ℂ) + Complex.I * (t : ℂ))⁻¹)
    (v := fun t : ℝ => Complex.exp (c * (t : ℂ)) / c)
    (u' := fun t : ℝ => -Complex.I / (((σ : ℂ) + Complex.I * (t : ℂ)) ^ 2))
    (v' := fun t : ℝ => Complex.exp (c * (t : ℂ)))
    (fun t _ => hu t) (fun t _ => hv t)
    (hu'cont.intervalIntegrable a b) (hv'cont.intervalIntegrable a b)

/-- A subinterval of one positive dyadic shell gains both the frequency
`1/|L|` and the shell's inverse height. -/
theorem norm_integral_perronPhaseKernel_short_interval_le
    (σ L H b : ℝ) (hσ : 0 < σ) (hL : L ≠ 0) (hH : 0 < H)
    (hHb : H ≤ b) (hb : b ≤ 2 * H) :
    ‖∫ t in H..b,
      (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹) *
        Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ))‖ ≤
      3 / (H * |L|) := by
  let den (t : ℝ) : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  let wave (t : ℝ) : ℂ :=
    Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ))
  have him (t : ℝ) : (den t).im = t := by simp [den]
  have hden_lower (t : ℝ) (ht : H ≤ t) : H ≤ ‖den t‖ := by
    have h := Complex.abs_im_le_norm (den t)
    rw [him, abs_of_nonneg (le_trans hH.le ht)] at h
    exact ht.trans h
  have hfreq : 0 < |L| := abs_pos.mpr hL
  have hfreq_norm : ‖Complex.I * (L : ℂ)‖ = |L| := by simp
  have hwave (t : ℝ) : ‖wave t‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hendpoint (t : ℝ) (ht : H ≤ t) :
      ‖(den t)⁻¹ * (wave t / (Complex.I * (L : ℂ)))‖ ≤
        1 / (H * |L|) := by
    have hdt := hden_lower t ht
    have hdtpos : 0 < ‖den t‖ := lt_of_lt_of_le hH hdt
    have hinv : (‖den t‖)⁻¹ ≤ H⁻¹ :=
      (inv_le_inv₀ hdtpos hH).2 hdt
    calc
      ‖(den t)⁻¹ * (wave t / (Complex.I * (L : ℂ)))‖ =
          (‖den t‖)⁻¹ / |L| := by
        rw [norm_mul, norm_inv, norm_div, hwave t, hfreq_norm]
        ring
      _ ≤ H⁻¹ / |L| :=
        div_le_div_of_nonneg_right hinv hfreq.le
      _ = 1 / (H * |L|) := by
        field_simp [ne_of_gt hH, ne_of_gt hfreq]
  have hrem_point (t : ℝ) (ht : t ∈ Set.uIoc H b) :
      ‖(-Complex.I / (den t ^ 2)) *
        (wave t / (Complex.I * (L : ℂ)))‖ ≤
          1 / (H ^ 2 * |L|) := by
    have ht' : t ∈ Set.Ioc H b := by
      simpa [Set.uIoc_of_le hHb] using ht
    have hleft : H ≤ t := le_of_lt ht'.1
    have hdt := hden_lower t hleft
    have hpow : H ^ 2 ≤ ‖den t‖ ^ 2 := by
      exact (sq_le_sq₀ hH.le (norm_nonneg _)).2 hdt
    have hpow' : H ^ 2 ≤ ‖den t ^ 2‖ := by
      simpa only [norm_pow] using hpow
    calc
      ‖(-Complex.I / (den t ^ 2)) *
          (wave t / (Complex.I * (L : ℂ)))‖ =
          (‖den t ^ 2‖)⁻¹ / |L| := by
        simp [hwave t]
        ring
      _ ≤ (H ^ 2)⁻¹ / |L| := by
        apply div_le_div_of_nonneg_right _ hfreq.le
        have hdtpos : 0 < ‖den t‖ := lt_of_lt_of_le hH hdt
        have hdenpowpos : 0 < ‖den t ^ 2‖ := by
          simpa only [norm_pow] using pow_pos hdtpos 2
        exact (inv_le_inv₀ hdenpowpos (pow_pos hH 2)).2 hpow'
      _ = 1 / (H ^ 2 * |L|) := by
        field_simp [ne_of_gt (pow_pos hH 2), ne_of_gt hfreq]
  have hrem :
      ‖∫ t in H..b,
        (-Complex.I / (den t ^ 2)) *
          (wave t / (Complex.I * (L : ℂ)))‖ ≤
        1 / (H * |L|) := by
    have hconst := intervalIntegral.norm_integral_le_of_norm_le_const hrem_point
    have hlength : |b - H| ≤ H := by
      rw [abs_of_nonneg (sub_nonneg.mpr hHb)]
      linarith
    calc
      _ ≤ (1 / (H ^ 2 * |L|)) * |b - H| := hconst
      _ ≤ (1 / (H ^ 2 * |L|)) * H :=
        mul_le_mul_of_nonneg_left hlength (by positivity)
      _ = 1 / (H * |L|) := by
        field_simp [ne_of_gt hH, ne_of_gt hfreq]
  have hformula := perronPhaseKernel_integrationByParts σ L H b
    hσ hL
  calc
    _ ≤
        ‖(den b)⁻¹ * (wave b / (Complex.I * (L : ℂ))) -
          (den H)⁻¹ * (wave H / (Complex.I * (L : ℂ)))‖ +
        ‖∫ t in H..b,
          (-Complex.I / (den t ^ 2)) *
            (wave t / (Complex.I * (L : ℂ)))‖ := by
      rw [show (∫ t in H..b,
          (den t)⁻¹ * wave t) =
            (den b)⁻¹ * (wave b / (Complex.I * (L : ℂ))) -
              (den H)⁻¹ * (wave H / (Complex.I * (L : ℂ))) -
              ∫ t in H..b,
                (-Complex.I / (den t ^ 2)) *
                  (wave t / (Complex.I * (L : ℂ))) by
          simpa [den, wave] using hformula]
      exact norm_sub_le _ _
    _ ≤
        (1 / (H * |L|) + 1 / (H * |L|)) + 1 / (H * |L|) := by
      apply add_le_add
      · exact norm_sub_le _ _ |>.trans (add_le_add
          (hendpoint b hHb) (hendpoint H le_rfl))
      · exact hrem
    _ = 3 / (H * |L|) := by ring

/-- A full positive dyadic shell is a special case of the short-interval
bound. -/
theorem norm_integral_perronPhaseKernel_dyadic_le
    (σ L H : ℝ) (hσ : 0 < σ) (hL : L ≠ 0) (hH : 0 < H) :
    ‖∫ t in H..2 * H,
      (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹) *
        Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ))‖ ≤
      3 / (H * |L|) :=
  norm_integral_perronPhaseKernel_short_interval_le σ L H (2 * H)
    hσ hL hH (by linarith) (by linarith)

/-- The reciprocal-height factors on finitely many successive dyadic shells
sum to less than two. -/
private theorem sum_inv_two_pow_range_le_two (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), ((2 : ℝ) ^ j)⁻¹ ≤ 2 := by
  have hsum (n : ℕ) :
      ∑ j ∈ Finset.range (n + 1), ((2 : ℝ) ^ j)⁻¹ =
        2 - ((2 : ℝ) ^ n)⁻¹ := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hp : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      have hq : (2 : ℝ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp [hp, hq]
      ring
  rw [hsum]
  have hpos : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  have hinv : 0 < ((2 : ℝ) ^ n)⁻¹ := inv_pos.mpr hpos
  linarith

/-- Summing the positive dyadic shells above height `H` costs at most twice
the first-shell scale, uniformly in the number of shells. This is the
finite tail bound needed before passing to the infinite Perron contour. -/
theorem norm_sum_perronPhaseKernel_dyadic_le
    (σ L H : ℝ) (hσ : 0 < σ) (hL : L ≠ 0) (hH : 0 < H) (n : ℕ) :
    ‖∑ j ∈ Finset.range (n + 1),
      ∫ t in ((2 : ℝ) ^ j * H)..(2 * ((2 : ℝ) ^ j * H)),
        (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹) *
          Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ))‖ ≤
      6 / (H * |L|) := by
  have hfreq : 0 < |L| := abs_pos.mpr hL
  have hterm (j : ℕ) :
      ‖∫ t in ((2 : ℝ) ^ j * H)..(2 * ((2 : ℝ) ^ j * H)),
        (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹) *
          Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ))‖ ≤
        (3 / (H * |L|)) * ((2 : ℝ) ^ j)⁻¹ := by
    have hscale : 0 < (2 : ℝ) ^ j * H := mul_pos (by positivity) hH
    have hbound := norm_integral_perronPhaseKernel_dyadic_le σ L
      ((2 : ℝ) ^ j * H) hσ hL hscale
    calc
      _ ≤ 3 / (((2 : ℝ) ^ j * H) * |L|) := hbound
      _ = (3 / (H * |L|)) * ((2 : ℝ) ^ j)⁻¹ := by
        field_simp [ne_of_gt hH, ne_of_gt hfreq,
          pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)]
  have hsum := Finset.sum_le_sum (s := Finset.range (n + 1))
    (fun j _ => hterm j)
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1),
        ‖∫ t in ((2 : ℝ) ^ j * H)..(2 * ((2 : ℝ) ^ j * H)),
          (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹) *
            Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (n + 1),
        (3 / (H * |L|)) * ((2 : ℝ) ^ j)⁻¹ := hsum
    _ = (3 / (H * |L|)) *
        (∑ j ∈ Finset.range (n + 1), ((2 : ℝ) ^ j)⁻¹) := by
      rw [Finset.mul_sum]
    _ ≤ (3 / (H * |L|)) * 2 := by
      exact mul_le_mul_of_nonneg_left (sum_inv_two_pow_range_le_two n)
        (by positivity)
    _ = 6 / (H * |L|) := by ring

/-- The full positive tail from `H` to any finite endpoint has the same
`1/(H|L|)` decay, after decomposing it into full dyadic shells and one
partial final shell. The hypotheses place `T` in shell `n`. -/
theorem norm_integral_perronPhaseKernel_finite_tail_le
    (σ L H T : ℝ) (hσ : 0 < σ) (hL : L ≠ 0) (hH : 0 < H)
    (n : ℕ) (hlo : (2 : ℝ) ^ n * H ≤ T)
    (hhi : T ≤ (2 : ℝ) ^ (n + 1) * H) :
    ‖∫ t in H..T,
      (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹) *
        Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ))‖ ≤
      9 / (H * |L|) := by
  let f (t : ℝ) : ℂ :=
    (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹) *
      Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ))
  let a (j : ℕ) : ℝ := (2 : ℝ) ^ j * H
  have hfcont : Continuous f := by
    have hden (t : ℝ) : (σ : ℂ) + Complex.I * (t : ℂ) ≠ 0 := by
      apply Complex.ne_zero_of_re_pos
      simpa using hσ
    have hlinear : Continuous (fun t : ℝ =>
        (σ : ℂ) + Complex.I * (t : ℂ)) := by fun_prop
    have hinv := hlinear.inv₀ hden
    have hwave : Continuous (fun t : ℝ =>
        Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ))) := by fun_prop
    change Continuous (fun t : ℝ =>
      (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹) *
        Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ)))
    exact hinv.mul hwave
  have hfint (x y : ℝ) : IntervalIntegrable f volume x y :=
    hfcont.intervalIntegrable x y
  have hsum_integral :
      ∑ j ∈ Finset.range n, ∫ t in a j..(2 * a j), f t =
        ∫ t in H..a n, f t := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (f := f) (μ := volume) (a := a) (n := n)
      (fun _ _ => hfint _ _)
    simpa [a, f, pow_succ, mul_assoc, mul_left_comm, mul_comm] using h
  have hfullsum :
      ‖∑ j ∈ Finset.range n, ∫ t in a j..(2 * a j), f t‖ ≤
        6 / (H * |L|) := by
    cases n with
    | zero =>
      simp
      positivity
    | succ m =>
      simpa [a, f, Nat.succ_eq_add_one] using
        norm_sum_perronPhaseKernel_dyadic_le σ L H hσ hL hH m
  have ha0 : 0 < a n := mul_pos (by positivity) hH
  have hlower : a n ≤ T := by simpa [a] using hlo
  have hupper : T ≤ 2 * a n := by
    simpa [a, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hhi
  have hpartial := norm_integral_perronPhaseKernel_short_interval_le
    σ L (a n) T hσ hL ha0 hlower hupper
  have hdecomp :
      ∫ t in H..T, f t =
        (∑ j ∈ Finset.range n, ∫ t in a j..(2 * a j), f t) +
          ∫ t in a n..T, f t := by
    rw [hsum_integral]
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hfint H (a n)) (hfint (a n) T)).symm
  have hscale : H ≤ a n := by
    dsimp [a]
    simpa using mul_le_mul_of_nonneg_right
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := n)) hH.le
  calc
    ‖∫ t in H..T, f t‖ =
        ‖(∑ j ∈ Finset.range n, ∫ t in a j..(2 * a j), f t) +
          ∫ t in a n..T, f t‖ := by rw [hdecomp]
    _ ≤ ‖∑ j ∈ Finset.range n, ∫ t in a j..(2 * a j), f t‖ +
        ‖∫ t in a n..T, f t‖ := norm_add_le _ _
    _ ≤ 6 / (H * |L|) + 3 / (a n * |L|) :=
      add_le_add hfullsum hpartial
    _ ≤ 6 / (H * |L|) + 3 / (H * |L|) := by
      gcongr
    _ = 9 / (H * |L|) := by ring

/-- The phase kernel at negative height is the complex conjugate of its
value at the corresponding positive height. -/
private theorem perronPhaseKernel_neg_eq_conj (σ L t : ℝ) :
    (((σ : ℂ) + Complex.I * (-t : ℂ))⁻¹) *
        Complex.exp ((Complex.I * (L : ℂ)) * (-t : ℂ)) =
      star ((((σ : ℂ) + Complex.I * (t : ℂ))⁻¹) *
        Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ))) := by
  have hdenneg :
      (σ : ℂ) + Complex.I * (-t : ℂ) =
        star ((σ : ℂ) + Complex.I * (t : ℂ)) := by simp
  have hphase :
      (Complex.I * (L : ℂ)) * (-t : ℂ) =
        star ((Complex.I * (L : ℂ)) * (t : ℂ)) := by simp
  have hexp (z : ℂ) : Complex.exp (star z) = star (Complex.exp z) := by simp
  rw [hdenneg, hphase, ← star_inv₀, hexp]
  calc
    star ((((σ : ℂ) + Complex.I * (t : ℂ))⁻¹)) *
        star (Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ))) =
      star (Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ))) *
        star ((((σ : ℂ) + Complex.I * (t : ℂ))⁻¹)) := mul_comm _ _
    _ = star (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹ *
        Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ))) :=
      (star_mul ((((σ : ℂ) + Complex.I * (t : ℂ))⁻¹))
        (Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ)))).symm

/-- The negative tail has the same uniform bound as the positive tail, by
complex-conjugate symmetry of the real vertical line. -/
theorem norm_integral_perronPhaseKernel_negative_tail_le
    (σ L H T : ℝ) (hσ : 0 < σ) (hL : L ≠ 0) (hH : 0 < H)
    (n : ℕ) (hlo : (2 : ℝ) ^ n * H ≤ T)
    (hhi : T ≤ (2 : ℝ) ^ (n + 1) * H) :
    ‖∫ t in -T..-H,
      (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹) *
        Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ))‖ ≤
      9 / (H * |L|) := by
  let f (t : ℝ) : ℂ :=
    (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹) *
      Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ))
  have hreflection :
      (∫ t in -T..-H, f t) = ∫ t in H..T, f (-t) := by
    simp [intervalIntegral.integral_comp_neg]
  have hconj :
      (∫ t in H..T, f (-t)) = star (∫ t in H..T, f t) := by
    rw [show (fun t : ℝ => f (-t)) = fun t => star (f t) by
      funext t
      simpa [f] using perronPhaseKernel_neg_eq_conj σ L t]
    have hHT : H ≤ T := by
      have hpow : 1 ≤ (2 : ℝ) ^ n :=
        one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      simpa only [one_mul] using (mul_le_mul_of_nonneg_right hpow hH.le).trans hlo
    have hset :
        (∫ t in Set.uIoc H T, star (f t)) =
          star (∫ t in Set.uIoc H T, f t) := integral_conj
    simpa [intervalIntegral.intervalIntegral_eq_integral_uIoc, hHT] using hset
  rw [show (∫ t in -T..-H, f t) = star (∫ t in H..T, f t) by
    rw [hreflection, hconj]]
  simpa [f] using norm_integral_perronPhaseKernel_finite_tail_le
    σ L H T hσ hL hH n hlo hhi

/-- The two finite tails of the symmetric vertical contour are bounded by
the sum of their one-sided dyadic estimates. -/
theorem norm_integral_perronPhaseKernel_two_tails_le
    (σ L H T : ℝ) (hσ : 0 < σ) (hL : L ≠ 0) (hH : 0 < H)
    (n : ℕ) (hlo : (2 : ℝ) ^ n * H ≤ T)
    (hhi : T ≤ (2 : ℝ) ^ (n + 1) * H) :
    ‖∫ t in -T..-H,
      (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹) *
        Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ))‖ +
    ‖∫ t in H..T,
      (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹) *
        Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ))‖ ≤
      18 / (H * |L|) := by
  calc
    _ ≤ 9 / (H * |L|) + 9 / (H * |L|) := add_le_add
      (norm_integral_perronPhaseKernel_negative_tail_le σ L H T hσ hL hH n hlo hhi)
      (norm_integral_perronPhaseKernel_finite_tail_le σ L H T hσ hL hH n hlo hhi)
    _ = 18 / (H * |L|) := by ring

/-- Every positive-height interval endpoint belongs to a dyadic shell. -/
private theorem exists_perron_dyadic_shell {H T : ℝ} (hH : 0 < H) (hHT : H ≤ T) :
    ∃ n : ℕ, (2 : ℝ) ^ n * H ≤ T ∧ T ≤ (2 : ℝ) ^ (n + 1) * H := by
  have hratio : 1 ≤ T / H := (le_div_iff₀ hH).2 (by simpa using hHT)
  obtain ⟨n, hlo, hhi⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  exact ⟨n, (le_div_iff₀ hH).1 hlo, ((div_lt_iff₀ hH).1 hhi).le⟩

/-- Uniform positive-tail bound with no dyadic-shell hypothesis on `T`. -/
theorem norm_integral_perronPhaseKernel_positive_tail_le
    (σ L H T : ℝ) (hσ : 0 < σ) (hL : L ≠ 0) (hH : 0 < H) (hHT : H ≤ T) :
    ‖∫ t in H..T,
      (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹) *
        Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ))‖ ≤
      9 / (H * |L|) := by
  obtain ⟨n, hlo, hhi⟩ := exists_perron_dyadic_shell hH hHT
  exact norm_integral_perronPhaseKernel_finite_tail_le σ L H T hσ hL hH n hlo hhi

/-- Finite-height symmetric phase integral in the Perron contour. -/
noncomputable def perronPhaseTruncation (σ L H : ℝ) : ℂ :=
  ∫ t in -H..H,
    (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹) *
      Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ))

/-- The integrand is continuous on a positive real vertical line. -/
theorem continuous_perronPhaseKernel (σ L : ℝ) (hσ : 0 < σ) :
    Continuous (fun t : ℝ =>
      (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹) *
        Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ))) := by
  have hden (t : ℝ) : (σ : ℂ) + Complex.I * (t : ℂ) ≠ 0 := by
    apply Complex.ne_zero_of_re_pos
    simpa using hσ
  have hlinear : Continuous (fun t : ℝ => (σ : ℂ) + Complex.I * (t : ℂ)) := by
    fun_prop
  exact (hlinear.inv₀ hden).mul (by fun_prop)

/-- Increasing the symmetric contour height adds two controlled tails. -/
theorem norm_perronPhaseTruncation_sub_le
    (σ L H T : ℝ) (hσ : 0 < σ) (hL : L ≠ 0) (hH : 0 < H) (hHT : H ≤ T) :
    ‖perronPhaseTruncation σ L T - perronPhaseTruncation σ L H‖ ≤
      18 / (H * |L|) := by
  let f (t : ℝ) : ℂ :=
    (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹) *
      Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ))
  have hfint (a b : ℝ) : IntervalIntegrable f volume a b :=
    (continuous_perronPhaseKernel σ L hσ).intervalIntegrable a b
  have hdecomp : perronPhaseTruncation σ L T - perronPhaseTruncation σ L H =
      (∫ t in -T..-H, f t) + ∫ t in H..T, f t := by
    unfold perronPhaseTruncation
    change (∫ t in -T..T, f t) - (∫ t in -H..H, f t) = _
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hfint (-T) (-H)) (hfint (-H) T),
      ← intervalIntegral.integral_add_adjacent_intervals
        (hfint (-H) H) (hfint H T)]
    abel
  obtain ⟨n, hlo, hhi⟩ := exists_perron_dyadic_shell hH hHT
  rw [hdecomp]
  exact (norm_add_le _ _).trans
    (norm_integral_perronPhaseKernel_two_tails_le σ L H T hσ hL hH n hlo hhi)

/-- The symmetric Perron contour is Cauchy as its height tends to infinity.
The nonzero frequency supplies the uniform inverse-height tail estimate. -/
theorem cauchySeq_perronPhaseTruncation (σ L : ℝ) (hσ : 0 < σ) (hL : L ≠ 0) :
    CauchySeq (perronPhaseTruncation σ L) := by
  apply Metric.cauchySeq_iff'.2
  intro ε hε
  have hfreq : 0 < |L| := abs_pos.mpr hL
  let H : ℝ := 18 / (ε * |L|) + 1
  have hH : 0 < H := by dsimp [H]; positivity
  have hsmall : 18 / (H * |L|) < ε := by
    apply (div_lt_iff₀ (mul_pos hH hfreq)).2
    have hcancel : 18 / (ε * |L|) * (ε * |L|) = (18 : ℝ) :=
      div_mul_cancel₀ _ (ne_of_gt (mul_pos hε hfreq))
    dsimp [H]
    nlinarith [mul_pos hε hfreq]
  refine ⟨H, fun T hHT => ?_⟩
  rw [dist_eq_norm]
  exact (norm_perronPhaseTruncation_sub_le σ L H T hσ hL hH hHT).trans_lt hsmall

/-- The infinite-height symmetric phase contour, whose convergence is
proved for positive abscissa and nonzero frequency below. -/
noncomputable def perronPhaseContourLimit (σ L : ℝ) : ℂ :=
  Filter.limUnder Filter.atTop (perronPhaseTruncation σ L)

/-- Existence of the infinite-height symmetric phase contour. -/
theorem tendsto_perronPhaseTruncation (σ L : ℝ) (hσ : 0 < σ) (hL : L ≠ 0) :
    Filter.Tendsto (perronPhaseTruncation σ L) Filter.atTop
      (nhds (perronPhaseContourLimit σ L)) :=
  (cauchySeq_perronPhaseTruncation σ L hσ hL).tendsto_limUnder

/-- Quantitative truncation error after passing to infinite contour height. -/
theorem norm_perronPhaseContourLimit_sub_truncation_le
    (σ L H : ℝ) (hσ : 0 < σ) (hL : L ≠ 0) (hH : 0 < H) :
    ‖perronPhaseContourLimit σ L - perronPhaseTruncation σ L H‖ ≤
      18 / (H * |L|) := by
  apply le_of_tendsto
    ((tendsto_perronPhaseTruncation σ L hσ hL).sub_const
      (perronPhaseTruncation σ L H)).norm
  filter_upwards [Filter.eventually_ge_atTop H] with T hHT
  exact norm_perronPhaseTruncation_sub_le σ L H T hσ hL hH hHT

/-- The finite scalar Perron integral has the same real amplitude as its
infinite-height phase contour. -/
theorem integral_perronScalarKernel_eq_phaseTruncation
    (x σ H : ℝ) (k : ℕ) (hx : 0 < x) (hk : 0 < k) :
    (∫ t in -H..H, perronScalarKernel x k σ t) =
      (((x / (k : ℝ)) ^ σ : ℝ) : ℂ) *
        perronPhaseTruncation σ (Real.log (x / (k : ℝ))) H := by
  have hpoint (t : ℝ) : perronScalarKernel x k σ t =
      (((x / (k : ℝ)) ^ σ : ℝ) : ℂ) *
        ((((σ : ℂ) + Complex.I * (t : ℂ))⁻¹) *
          Complex.exp ((Complex.I * (Real.log (x / (k : ℝ)) : ℂ)) * (t : ℂ))) := by
    rw [perronScalarKernel_phase x σ t k hx hk, div_eq_mul_inv]
    ring
  simp_rw [hpoint]
  exact intervalIntegral.integral_const_mul _ _

/-- Scalar-kernel convergence to its amplitude times the phase-contour
limit, before the latter is identified with the Perron indicator. -/
theorem tendsto_integral_perronScalarKernel
    (x σ : ℝ) (k : ℕ) (hx : 0 < x) (hk : 0 < k) (hσ : 0 < σ)
    (hlog : Real.log (x / (k : ℝ)) ≠ 0) :
    Filter.Tendsto (fun H : ℝ => ∫ t in -H..H, perronScalarKernel x k σ t)
      Filter.atTop (nhds ((((x / (k : ℝ)) ^ σ : ℝ) : ℂ) *
        perronPhaseContourLimit σ (Real.log (x / (k : ℝ))))) := by
  simp_rw [integral_perronScalarKernel_eq_phaseTruncation x σ _ k hx hk]
  exact (tendsto_perronPhaseTruncation σ (Real.log (x / (k : ℝ))) hσ hlog).const_mul _

/-- Integrated scalar-kernel truncation error with nonzero logarithmic
frequency. Evaluating the displayed limit is a separate contour theorem. -/
theorem norm_perronScalarKernel_limit_sub_integral_le
    (x σ H : ℝ) (k : ℕ) (hx : 0 < x) (hk : 0 < k) (hσ : 0 < σ)
    (hH : 0 < H) (hlog : Real.log (x / (k : ℝ)) ≠ 0) :
    ‖(((x / (k : ℝ)) ^ σ : ℝ) : ℂ) *
        perronPhaseContourLimit σ (Real.log (x / (k : ℝ))) -
      ∫ t in -H..H, perronScalarKernel x k σ t‖ ≤
      18 * (x / (k : ℝ)) ^ σ / (H * |Real.log (x / (k : ℝ))|) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hamp : 0 ≤ (x / (k : ℝ)) ^ σ := Real.rpow_nonneg (div_pos hx hkpos).le σ
  rw [integral_perronScalarKernel_eq_phaseTruncation x σ H k hx hk, ← mul_sub,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hamp]
  calc
    _ ≤ (x / (k : ℝ)) ^ σ * (18 / (H * |Real.log (x / (k : ℝ))|)) :=
      mul_le_mul_of_nonneg_left
        (norm_perronPhaseContourLimit_sub_truncation_le σ (Real.log (x / (k : ℝ)))
          H hσ hlog hH) hamp
    _ = _ := by ring

end SystolicGrowth.CookMagyarCircle

#print axioms SystolicGrowth.CookMagyarCircle.perronCpow_phase
#print axioms SystolicGrowth.CookMagyarCircle.perronScalarKernel_phase
#print axioms SystolicGrowth.CookMagyarCircle.perronHalfInteger_log_ne_zero
#print axioms SystolicGrowth.CookMagyarCircle.integral_perronNumerator_eq
#print axioms SystolicGrowth.CookMagyarCircle.norm_integral_perronNumerator_le
#print axioms SystolicGrowth.CookMagyarCircle.perronPhaseKernel_integrationByParts
#print axioms SystolicGrowth.CookMagyarCircle.norm_integral_perronPhaseKernel_short_interval_le
#print axioms SystolicGrowth.CookMagyarCircle.norm_integral_perronPhaseKernel_dyadic_le
#print axioms SystolicGrowth.CookMagyarCircle.norm_sum_perronPhaseKernel_dyadic_le
#print axioms SystolicGrowth.CookMagyarCircle.norm_integral_perronPhaseKernel_finite_tail_le
#print axioms SystolicGrowth.CookMagyarCircle.norm_integral_perronPhaseKernel_negative_tail_le
#print axioms SystolicGrowth.CookMagyarCircle.norm_integral_perronPhaseKernel_two_tails_le
#print axioms SystolicGrowth.CookMagyarCircle.norm_integral_perronPhaseKernel_positive_tail_le
#print axioms SystolicGrowth.CookMagyarCircle.cauchySeq_perronPhaseTruncation
#print axioms SystolicGrowth.CookMagyarCircle.tendsto_perronPhaseTruncation
#print axioms SystolicGrowth.CookMagyarCircle.norm_perronPhaseContourLimit_sub_truncation_le
#print axioms SystolicGrowth.CookMagyarCircle.tendsto_integral_perronScalarKernel
#print axioms SystolicGrowth.CookMagyarCircle.norm_perronScalarKernel_limit_sub_integral_le
