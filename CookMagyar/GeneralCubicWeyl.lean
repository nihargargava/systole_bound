module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.OrdinaryWeylPairs
public import CookMagyar.LogCutoff
public import CookMagyar.CubicAbelPhase
public import CookMagyar.AuxiliaryPowerCutoff

@[expose] public section

open scoped BigOperators ComplexConjugate
open Filter

namespace SystolicGrowth
namespace CookMagyarCircle

open CookMagyarArcs

/-! # Differencing for cubic phases with arbitrary lower coefficients

Hua's rational-leading estimate is uniform in the quadratic and linear
coefficients.  The two positive shifts eliminate these coefficients, so the
same spacing argument used for `x^3 - x` applies to every real cubic
polynomial. -/

/-- The real polynomial value whose leading coefficient is used in Hua's
rational approximation. -/
noncomputable def generalCubicPolynomial (a b c d : ℝ) (m : ℕ) : ℝ :=
  a * (m : ℝ) ^ 3 + b * (m : ℝ) ^ 2 + c * m + d

/-- The exponential phase of a real cubic polynomial with arbitrary
quadratic, linear, and constant coefficients. -/
noncomputable def generalCubicPhase (a b c d : ℝ) (m : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * generalCubicPolynomial a b c d m : ℝ) : ℂ) * Complex.I)

/-- The finite exponential sum of a real cubic polynomial with arbitrary
quadratic, linear, and constant coefficients. -/
noncomputable def generalCubicExpSum (a b c d : ℝ) (N : ℕ) : ℂ :=
  ∑ m ∈ Finset.range (N + 1), generalCubicPhase a b c d m

/-- Positive-shift autocorrelation of a finite unit-modulus sequence. -/
noncomputable def unitSequenceFixedShiftSum (u : ℕ → ℂ) (N h : ℕ) : ℂ :=
  ∑ m ∈ Finset.range (N + 1 - h), u (m + h) * conj (u m)

/-- Sum of all positive second differences of a finite unit-modulus
sequence, with the natural triangular ranges. -/
noncomputable def unitSequenceSecondDifferenceSum (u : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 N,
    ∑ km ∈ positiveCubicShiftPairs (N - h),
      u (km.2 + km.1 + h) * conj (u (km.2 + km.1)) *
        conj (u (km.2 + h)) * u km.2

/-- The first positive-shift sum of a sequence. -/
noncomputable def unitSequenceFirstDifferenceSum (u : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ hm ∈ positiveCubicShiftPairs N,
    u (hm.2 + hm.1) * conj (u hm.2)

@[simp] theorem norm_generalCubicPhase (a b c d : ℝ) (m : ℕ) :
    ‖generalCubicPhase a b c d m‖ = 1 := by
  unfold generalCubicPhase
  exact Complex.norm_exp_ofReal_mul_I _

private theorem conj_exp_real_mul_I (x : ℝ) :
    conj (Complex.exp ((x : ℂ) * Complex.I)) =
      Complex.exp (((-x : ℝ) : ℂ) * Complex.I) := by
  calc
    conj (Complex.exp ((x : ℂ) * Complex.I)) =
        Complex.exp (conj ((x : ℂ) * Complex.I)) := by
          rw [← Complex.exp_conj]
    _ = Complex.exp (((-x : ℝ) : ℂ) * Complex.I) := by
      congr 1
      simp [map_mul]

/-- Two positive shifts remove all lower-degree terms from a cubic phase.
The remaining linear frequency is six times the leading coefficient times
the product of the shifts; quadratic and linear coefficients contribute
only a shift-dependent unit factor (the linear coefficient cancels). -/
theorem generalCubicPhase_secondDifference (a b c d : ℝ) (h k m : ℕ) :
    generalCubicPhase a b c d (m + h + k) *
        conj (generalCubicPhase a b c d (m + k)) *
        conj (generalCubicPhase a b c d (m + h)) *
        generalCubicPhase a b c d m =
      Complex.exp
          (((2 * Real.pi *
            (a * (6 * h * k * m + 3 * h * k * (h + k)) +
              b * (2 * h * k) : ℝ)) : ℂ) * Complex.I) := by
  unfold generalCubicPhase generalCubicPolynomial
  rw [conj_exp_real_mul_I, conj_exp_real_mul_I]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The same second difference factors into a unit prefactor and a linear
additive character, ready for the spacing estimate. -/
theorem generalCubicPhase_secondDifference_eq_unit_mul_addChar
    (a b c d : ℝ) (h k m : ℕ) :
    generalCubicPhase a b c d (m + h + k) *
        conj (generalCubicPhase a b c d (m + k)) *
        conj (generalCubicPhase a b c d (m + h)) *
        generalCubicPhase a b c d m =
      Complex.exp
          (((2 * Real.pi * (3 * a * h * k * (h + k) + 2 * b * h * k : ℝ)) : ℂ) *
            Complex.I) * addChar (6 * a * h * k) m := by
  rw [generalCubicPhase_secondDifference]
  have hsplit :
      a * (6 * h * k * m + 3 * h * k * (h + k)) + b * (2 * h * k) =
        (3 * a * h * k * (h + k) + 2 * b * h * k) + (6 * a * h * k) * m := by
    ring
  rw [hsplit]
  unfold addChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact affine reparameterization of a cubic polynomial. This is the
polynomial identity needed to pass from a progression variable to the
ordinary interval variable in Hua's Type-I lemma. -/
theorem generalCubicPolynomial_affineChange
    (a b c d : ℝ) (r s m : ℕ) :
    generalCubicPolynomial a b c d (r + s * m) =
      generalCubicPolynomial
        (a * (s : ℝ) ^ 3)
        (3 * a * r * (s : ℝ) ^ 2 + b * (s : ℝ) ^ 2)
        (3 * a * (r : ℝ) ^ 2 * s + 2 * b * r * s + c * s)
        (a * (r : ℝ) ^ 3 + b * (r : ℝ) ^ 2 + c * r + d) m := by
  unfold generalCubicPolynomial
  push_cast
  ring

/-- The phase and finite sum obey the same exact affine
reparameterization, with no approximation or endpoint loss. -/
theorem generalCubicPhase_affineChange
    (a b c d : ℝ) (r s m : ℕ) :
    generalCubicPhase a b c d (r + s * m) =
      generalCubicPhase
        (a * (s : ℝ) ^ 3)
        (3 * a * r * (s : ℝ) ^ 2 + b * (s : ℝ) ^ 2)
        (3 * a * (r : ℝ) ^ 2 * s + 2 * b * r * s + c * s)
        (a * (r : ℝ) ^ 3 + b * (r : ℝ) ^ 2 + c * r + d) m := by
  unfold generalCubicPhase
  rw [generalCubicPolynomial_affineChange]

/-- The displaced additive character `e(theta*(k^3-k))` is a general cubic
phase with the same leading coefficient and the exact linear correction. -/
theorem addChar_primeCubic_eq_generalCubicPhase (theta : ℝ) (k : ℕ) :
    addChar theta (primeCubic k) =
      generalCubicPhase theta 0 (-theta) 0 k := by
  unfold addChar generalCubicPhase generalCubicPolynomial primeCubic
  rw [Nat.cast_sub (Nat.le_pow (by norm_num : 0 < 3))]
  push_cast
  congr 1
  ring

/-- Exact progression form of the rational cubic character. The smooth
beta factor is handled separately by affine Abel summation. -/
theorem addChar_primeCubic_affine_eq_generalCubicPhase
    (theta : ℝ) (base step m : ℕ) :
    addChar theta (primeCubic (base + step * m)) =
      generalCubicPhase
        (theta * (step : ℝ) ^ 3)
        (3 * theta * (base : ℝ) * (step : ℝ) ^ 2)
        (3 * theta * (base : ℝ) ^ 2 * (step : ℝ) - theta * (step : ℝ))
        (theta * (base : ℝ) ^ 3 - theta * (base : ℝ)) m := by
  rw [addChar_primeCubic_eq_generalCubicPhase]
  rw [generalCubicPhase_affineChange]
  congr 1 <;> ring

/-- Compose an endpoint-uniform general-cubic estimate with the affine smooth
beta Abel transfer. `hphase` is the exact phase identification; callers may
use `addChar_primeCubic_affine_eq_generalCubicPhase` and reduce its leading
coefficient to the denominator used by the rational Weyl estimate. -/
theorem norm_sum_affineCubicAbelWeight_mul_addChar_le_of_generalCubicPartialSums
    (beta alpha theta : ℝ) (b c d : ℝ) (base step P M : ℕ) {Delta : ℝ}
    (hM : 0 < M) (hDelta : 0 ≤ Delta)
    (hbase : 0 < base) (hstep : 0 < step)
    (hcover : base + step * M ≤ P)
    (hscaled : (P : ℝ) ^ 3 * |beta| ≤ 1)
    (hphase : ∀ m : ℕ,
      addChar alpha (primeCubic (base + step * m)) =
        generalCubicPhase theta b c d m)
    (hpartial : ∀ n : ℕ, n ≤ M →
      ‖generalCubicExpSum theta b c d n‖ ≤ Delta) :
    ‖∑ m ∈ Finset.Icc 0 M,
      CookMagyarMajorArc.cubicAbelWeight beta
          ((base : ℝ) + (step : ℝ) * m) *
        addChar alpha (primeCubic (base + step * m))‖ ≤
      Delta * (1 + 8 * Real.pi) := by
  let phase : ℕ → ℂ := fun m =>
    addChar alpha (primeCubic (base + step * m))
  have hphasePartial : ∀ t ∈ Set.Ioc (0 : ℝ) M,
      ‖∑ m ∈ Finset.Icc 0 ⌊t⌋₊, phase m‖ ≤ Delta := by
    intro t ht
    let n := ⌊t⌋₊
    have hn : n ≤ M := by
      have hfloor : (n : ℝ) ≤ t := by
        exact_mod_cast Nat.floor_le ht.1.le
      exact_mod_cast hfloor.trans ht.2
    have hsum : (∑ m ∈ Finset.Icc 0 n, phase m) =
        generalCubicExpSum theta b c d n := by
      unfold phase generalCubicExpSum
      rw [← Nat.range_succ_eq_Icc_zero]
      apply Finset.sum_congr rfl
      intro m hm
      exact hphase m
    rw [hsum]
    exact hpartial n hn
  exact CookMagyarMajorArc.norm_sum_affineCubicAbelWeight_mul_le_partialSumBound_of_scaledError
    phase beta base step P M hM hDelta hbase hstep hcover hscaled
    hphasePartial

/-- Prefix form of the affine Abel transfer. The zero prefix is handled
directly using the unit modulus of the smooth factor; positive prefixes use
the usual integral Abel estimate. -/
theorem norm_sum_affineCubicAbelWeight_mul_addChar_prefix_le_of_generalCubicPartialSums
    (beta alpha theta : ℝ) (b c d : ℝ) (base step P n : ℕ) {Delta : ℝ}
    (hDelta : 0 ≤ Delta) (hbase : 0 < base) (hstep : 0 < step)
    (hcover : base + step * n ≤ P)
    (hscaled : (P : ℝ) ^ 3 * |beta| ≤ 1)
    (hphase : ∀ m : ℕ,
      addChar alpha (primeCubic (base + step * m)) =
        generalCubicPhase theta b c d m)
    (hpartial : ∀ k : ℕ, k ≤ n →
      ‖generalCubicExpSum theta b c d k‖ ≤ Delta) :
    ‖∑ m ∈ Finset.Icc 0 n,
      CookMagyarMajorArc.cubicAbelWeight beta
          ((base : ℝ) + (step : ℝ) * m) *
        addChar alpha (primeCubic (base + step * m))‖ ≤
      Delta * (1 + 8 * Real.pi) := by
  by_cases hn : n = 0
  · subst n
    have hbasephase :
        addChar alpha (primeCubic base) = generalCubicPhase theta b c d 0 := by
      simpa using hphase 0
    have hsum :
        (∑ m ∈ Finset.Icc (0 : ℕ) 0,
          CookMagyarMajorArc.cubicAbelWeight beta
              ((base : ℝ) + (step : ℝ) * m) *
            addChar alpha (primeCubic (base + step * m))) =
          CookMagyarMajorArc.cubicAbelWeight beta (base : ℝ) *
            generalCubicExpSum theta b c d 0 := by
      simp only [Finset.Icc_self, Finset.sum_singleton]
      simp only [Nat.cast_zero, mul_zero, add_zero]
      rw [hbasephase]
      simp [generalCubicExpSum]
    rw [hsum, norm_mul, CookMagyarMajorArc.cubicAbelWeight_norm]
    simp only [one_mul]
    have hsmall : ‖generalCubicExpSum theta b c d 0‖ ≤ Delta :=
      hpartial 0 (by omega)
    calc
      ‖generalCubicExpSum theta b c d 0‖ ≤ Delta := hsmall
      _ ≤ Delta * (1 + 8 * Real.pi) := by
        nlinarith [mul_nonneg hDelta
          (show 0 ≤ 8 * Real.pi by positivity)]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let phase : ℕ → ℂ := fun m =>
      addChar alpha (primeCubic (base + step * m))
    have hphasePartial : ∀ t ∈ Set.Ioc (0 : ℝ) n,
        ‖∑ m ∈ Finset.Icc 0 ⌊t⌋₊, phase m‖ ≤ Delta := by
      intro t ht
      let k := ⌊t⌋₊
      have hk : k ≤ n := by
        have hfloor : (k : ℝ) ≤ t := by
          exact_mod_cast Nat.floor_le ht.1.le
        exact_mod_cast hfloor.trans ht.2
      have hsum : (∑ m ∈ Finset.Icc 0 k, phase m) =
          generalCubicExpSum theta b c d k := by
        unfold phase generalCubicExpSum
        rw [← Nat.range_succ_eq_Icc_zero]
        apply Finset.sum_congr rfl
        intro m hm
        exact hphase m
      rw [hsum]
      exact hpartial k hk
    exact norm_sum_affineCubicAbelWeight_mul_addChar_le_of_generalCubicPartialSums
      beta alpha theta b c d base step P n hnpos hDelta hbase hstep hcover
      hscaled hphase (by
        intro k hk
        exact hpartial k hk)

/-- Convert a bound for every natural-number prefix into the real-floor
hypothesis of logarithmic Abel summation. This is the coefficient shape of
Vaughan's first Type-I block, where the summand at index `k` has weight
`log (k+1)`. -/
theorem norm_sum_log_mul_le_of_natPrefixBound
    (c : ℕ → ℂ) (M : ℕ) {Delta : ℝ}
    (hM : 0 < M) (hDelta : 0 ≤ Delta)
    (hpartial : ∀ n : ℕ, n ≤ M →
      ‖∑ k ∈ Finset.Icc 0 n, c k‖ ≤ Delta) :
    ‖∑ k ∈ Finset.Icc 0 M,
        (Real.log ((k : ℝ) + 1) : ℂ) * c k‖ ≤
      2 * Delta * Real.log ((M : ℝ) + 1) := by
  apply CookMagyarMajorArc.norm_sum_log_mul_le_of_partialSumBound
    c M hM hDelta
  intro t ht
  let n : ℕ := ⌊t⌋₊
  have hfloor : (n : ℝ) ≤ t := by
    dsimp [n]
    exact_mod_cast Nat.floor_le ht.1.le
  have hn : n ≤ M := by
    exact_mod_cast hfloor.trans ht.2
  exact hpartial n hn

theorem sum_generalCubicPhase_affineChange
    (a b c d : ℝ) (r s X : ℕ) :
    (∑ m ∈ Finset.range X, generalCubicPhase a b c d (r + s * m)) =
      ∑ m ∈ Finset.range X,
        generalCubicPhase
          (a * (s : ℝ) ^ 3)
          (3 * a * r * (s : ℝ) ^ 2 + b * (s : ℝ) ^ 2)
          (3 * a * (r : ℝ) ^ 2 * s + 2 * b * r * s + c * s)
          (a * (r : ℝ) ^ 3 + b * (r : ℝ) ^ 2 + c * r + d) m := by
  apply Finset.sum_congr rfl
  intro m hm
  exact generalCubicPhase_affineChange a b c d r s m

/-- Scaling the progression variable cubes the leading coefficient and its
rational approximation numerator, while scaling the approximation error by
the same cubic factor. The denominator still needs reduction before applying
the coprime spacing theorem. -/
theorem generalCubicLeadingCoeff_affineApprox
    (theta beta : ℝ) (a q s : ℕ) (hq : 0 < q)
    (happrox : theta = rationalCenter a q + beta) :
    theta * (s : ℝ) ^ 3 =
      rationalCenter (a * s ^ 3) q + beta * (s : ℝ) ^ 3 := by
  rw [happrox]
  unfold rationalCenter
  push_cast
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  field_simp

/-- Cancelling the common factor from the scaled rational leading
coefficient preserves its rational center exactly. -/
theorem generalCubicLeadingCoeff_reducedCenter
    (a q s : ℕ) (hq : 0 < q) :
    rationalCenter (a * s ^ 3) q =
      rationalCenter ((a * s ^ 3) / Nat.gcd q (a * s ^ 3))
        (q / Nat.gcd q (a * s ^ 3)) := by
  let g := Nat.gcd q (a * s ^ 3)
  have hgq : g ∣ q := Nat.gcd_dvd_left q (a * s ^ 3)
  have hgnum : g ∣ a * s ^ 3 := Nat.gcd_dvd_right q (a * s ^ 3)
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left (a * s ^ 3) hq
  have hnumNat : ((a * s ^ 3) / g) * g = a * s ^ 3 :=
    Nat.div_mul_cancel hgnum
  have hqNat : (q / g) * g = q := Nat.div_mul_cancel hgq
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hgpos)
  have hnumR : (a * s ^ 3 : ℝ) = (g : ℝ) * (((a * s ^ 3) / g : ℕ) : ℝ) := by
    exact_mod_cast (by simpa [Nat.mul_comm] using hnumNat.symm)
  have hqR : (q : ℝ) = (g : ℝ) * (q / g : ℕ) := by
    exact_mod_cast (by simpa [Nat.mul_comm] using hqNat.symm)
  simp only [CookMagyarArcs.rationalCenter]
  rw [Nat.cast_div_charZero hgnum, Nat.cast_div_charZero hgq]
  have hqRne : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  field_simp [hgR, hqRne]

/-- After multiplying the rational `x^3-x` phase by an affine progression,
the leading coefficient is exactly the reduced rational center used in
`eventually_hua_cubic_progression_partial_weyl_norm_bound`. -/
theorem addChar_rationalPrimeCubic_affine_eq_reducedGeneralCubicPhase
    (a q base step m : ℕ) (hq : 0 < q) :
    addChar (rationalCenter a q) (primeCubic (base + step * m)) =
      generalCubicPhase
        (rationalCenter ((a * step ^ 3) / Nat.gcd q (a * step ^ 3))
          (q / Nat.gcd q (a * step ^ 3)))
        (3 * rationalCenter a q * (base : ℝ) * (step : ℝ) ^ 2)
        (3 * rationalCenter a q * (base : ℝ) ^ 2 * (step : ℝ) -
          rationalCenter a q * (step : ℝ))
        (rationalCenter a q * (base : ℝ) ^ 3 -
          rationalCenter a q * (base : ℝ)) m := by
  have hscale : rationalCenter a q * (step : ℝ) ^ 3 =
      rationalCenter (a * step ^ 3) q := by
    simpa using
      (generalCubicLeadingCoeff_affineApprox
        (rationalCenter a q) 0 a q step hq (by ring))
  rw [addChar_primeCubic_affine_eq_generalCubicPhase, hscale,
    generalCubicLeadingCoeff_reducedCenter a q step hq]

/-- The reduced scaled numerator and denominator are coprime. -/
theorem generalCubicLeadingCoeff_reduced_coprime
    (a q s : ℕ) (hq : 0 < q) :
    Nat.Coprime ((a * s ^ 3) / Nat.gcd q (a * s ^ 3))
      (q / Nat.gcd q (a * s ^ 3)) := by
  have hred :=
    Nat.gcd_div_gcd_div_gcd_of_pos_right (m := q) (n := a * s ^ 3) hq
  simpa [Nat.Coprime, Nat.gcd_comm] using hred

/-- Coprimality of the original leading numerator with `q` forces the
factor cancelled after progression scaling to divide `s^3`. Consequently
the reduced denominator stays between `q / s^3` and `q`. -/
theorem generalCubicLeadingCoeff_reduced_denominator_bounds
    (a q s : ℕ) (hq : 0 < q) (hs : 0 < s)
    (hac : Nat.Coprime a q) :
    q / s ^ 3 ≤ q / Nat.gcd q (a * s ^ 3) ∧
      q / Nat.gcd q (a * s ^ 3) ≤ q ∧
      0 < q / Nat.gcd q (a * s ^ 3) := by
  let g := Nat.gcd q (a * s ^ 3)
  have hgq : g ∣ q := Nat.gcd_dvd_left q (a * s ^ 3)
  have hgnum : g ∣ a * s ^ 3 := Nat.gcd_dvd_right q (a * s ^ 3)
  have hga : Nat.Coprime g a := (hac.of_dvd_right hgq).symm
  have hgs : g ∣ s ^ 3 := hga.dvd_mul_left.mp hgnum
  have hgle : g ≤ s ^ 3 := Nat.le_of_dvd (by positivity : 0 < s ^ 3) hgs
  have hfactor : q = (q / g) * g := (Nat.div_mul_cancel hgq).symm
  have hprod : q ≤ (q / g) * s ^ 3 := by
    calc
      q = (q / g) * g := hfactor
      _ ≤ (q / g) * s ^ 3 := Nat.mul_le_mul_left (q / g) hgle
  have hdenpos : 0 < q / g :=
    Nat.div_pos (Nat.le_of_dvd hq hgq) (Nat.gcd_pos_of_pos_left (a * s ^ 3) hq)
  constructor
  · exact Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using hprod)
  constructor
  · exact Nat.div_le_self q g
  · exact hdenpos

/-- If the original denominator dominates the cube of the progression step
times one more than a cutoff, then cancellation still leaves a denominator
strictly above that cutoff. -/
theorem generalCubicLeadingCoeff_reduced_denominator_gt_of_scaled_lower_bound
    (a q s cutoff : ℕ) (hq : 0 < q) (hs : 0 < s)
    (hac : Nat.Coprime a q)
    (hlarge : s ^ 3 * (cutoff + 1) ≤ q) :
    cutoff < q / Nat.gcd q (a * s ^ 3) := by
  have hbounds := generalCubicLeadingCoeff_reduced_denominator_bounds
    a q s hq hs hac
  have hs3 : 0 < s ^ 3 := by positivity
  have hquot : cutoff + 1 ≤ q / s ^ 3 := by
    apply (Nat.le_div_iff_mul_le hs3).2
    simpa [Nat.mul_comm] using hlarge
  omega

/-- In Hua's congruence progression, the cubic phase is evaluated at
`ell*x`; its total affine scale is `ell * (Q / gcd(Q,ell))`, at most
`ell*Q`. This packages the resulting denominator loss in the source
parameters. -/
theorem generalCubicLeadingCoeff_reduced_denominator_gt_of_ell_Q_bound
    (a q ell Q cutoff : ℕ) (hQ : 0 < Q) (hell : 0 < ell)
    (hac : Nat.Coprime a q)
    (hlarge : (ell * Q) ^ 3 * (cutoff + 1) ≤ q) :
    cutoff < q / Nat.gcd q (a * (ell * (Q / Nat.gcd Q ell)) ^ 3) := by
  have hgpos : 0 < Nat.gcd Q ell := Nat.gcd_pos_of_pos_left ell hQ
  have hstep_pos : 0 < Q / Nat.gcd Q ell := by
    exact Nat.div_pos (Nat.le_of_dvd hQ (Nat.gcd_dvd_left Q ell)) hgpos
  have hstep_le : Q / Nat.gcd Q ell ≤ Q := Nat.div_le_self Q (Nat.gcd Q ell)
  have hscale : ell * (Q / Nat.gcd Q ell) ≤ ell * Q :=
    Nat.mul_le_mul_left ell hstep_le
  have hscale_pos : 0 < ell * (Q / Nat.gcd Q ell) :=
    Nat.mul_pos hell hstep_pos
  have hscale_cube :
      (ell * (Q / Nat.gcd Q ell)) ^ 3 ≤ (ell * Q) ^ 3 := by
    gcongr
  have hlarge' :
      (ell * (Q / Nat.gcd Q ell)) ^ 3 * (cutoff + 1) ≤ q := by
    calc
      (ell * (Q / Nat.gcd Q ell)) ^ 3 * (cutoff + 1) ≤
          (ell * Q) ^ 3 * (cutoff + 1) :=
        Nat.mul_le_mul_right (cutoff + 1) hscale_cube
      _ ≤ q := hlarge
  have hq : 0 < q := by
    have hs3 : 0 < (ell * (Q / Nat.gcd Q ell)) ^ 3 := by positivity
    have hnext : 0 < cutoff + 1 := by omega
    exact lt_of_lt_of_le (Nat.mul_pos hs3 hnext) hlarge'
  have hcut := generalCubicLeadingCoeff_reduced_denominator_gt_of_scaled_lower_bound
    a q (ell * (Q / Nat.gcd Q ell)) cutoff hq hscale_pos hac hlarge'
  exact hcut

/-- Pure natural-number power bookkeeping for the denominator range: if the
scale and target cutoff are bounded by powers of a base `B≥2`, then an
original denominator above the corresponding larger power dominates their
product. -/
theorem cubic_scaled_denominator_lower_bound_of_power_bounds
    (B ell Q cutoff q eEll eQ eCut eQden : ℕ) (hB : 2 ≤ B)
    (hell : ell ≤ B ^ eEll) (hQ : Q ≤ B ^ eQ)
    (hcut : cutoff ≤ B ^ eCut)
    (hbudget : 3 * (eEll + eQ) + (eCut + 1) ≤ eQden)
    (hq : B ^ eQden < q) :
    (ell * Q) ^ 3 * (cutoff + 1) ≤ q := by
  have hscale : ell * Q ≤ B ^ (eEll + eQ) := by
    calc
      ell * Q ≤ B ^ eEll * B ^ eQ := Nat.mul_le_mul hell hQ
      _ = B ^ (eEll + eQ) := by rw [← pow_add]
  have hscale_cube : (ell * Q) ^ 3 ≤ B ^ (3 * (eEll + eQ)) := by
    calc
      (ell * Q) ^ 3 ≤ (B ^ (eEll + eQ)) ^ 3 := by gcongr
      _ = B ^ ((eEll + eQ) * 3) := by rw [← pow_mul]
      _ = B ^ (3 * (eEll + eQ)) := by congr 1; omega
  have hcut_plus : cutoff + 1 ≤ B ^ (eCut + 1) := by
    have hpowpos : 0 < B ^ eCut := by positivity
    calc
      cutoff + 1 ≤ B ^ eCut + 1 := Nat.add_le_add_right hcut 1
      _ ≤ 2 * B ^ eCut := by omega
      _ ≤ B * B ^ eCut := Nat.mul_le_mul_right (B ^ eCut) hB
      _ = B ^ eCut * B := Nat.mul_comm _ _
      _ = B ^ (eCut + 1) := by rw [Nat.pow_succ]
  have hprod :
      (ell * Q) ^ 3 * (cutoff + 1) ≤ B ^ (3 * (eEll + eQ) + (eCut + 1)) := by
    calc
      (ell * Q) ^ 3 * (cutoff + 1) ≤
          B ^ (3 * (eEll + eQ)) * B ^ (eCut + 1) :=
        Nat.mul_le_mul hscale_cube hcut_plus
      _ = B ^ (3 * (eEll + eQ) + (eCut + 1)) := by rw [← pow_add]
  have hbudget_pow :
      B ^ (3 * (eEll + eQ) + (eCut + 1)) ≤ B ^ eQden := by
    have hB1 : 1 ≤ B := by omega
    gcongr
  exact (hprod.trans hbudget_pow).trans (Nat.le_of_lt hq)

/-- Upper-denominator range transfer for a scaled progression. If the
original summation cutoff is at most `scale * (M+2)`, the scale is at most
`B^eScale`, and `q * B^eDen ≤ P^3`, then the reduced denominator is at most
the cubic Weyl upper window for the progression length, with the lost scale
power made explicit. -/
theorem cubic_scaled_denominator_upper_bound_of_power_bounds
    (B scale M P q q' eScale eDen : ℕ)
    (hB : 1 ≤ B) (hbudget : 3 * eScale ≤ eDen)
    (hscale : scale ≤ B ^ eScale)
    (hlen : P ≤ scale * (M + 2))
    (hqUpper : q * B ^ eDen ≤ P ^ 3)
    (hq'reduced : q' ≤ q) :
    q' * B ^ (eDen - 3 * eScale) ≤ (M + 2) ^ 3 := by
  have hscaleCube : scale ^ 3 ≤ B ^ (3 * eScale) := by
    calc
      scale ^ 3 ≤ (B ^ eScale) ^ 3 := by gcongr
      _ = B ^ (eScale * 3) := by rw [← pow_mul]
      _ = B ^ (3 * eScale) := by rw [Nat.mul_comm]
  have hlen' : P ≤ B ^ eScale * (M + 2) := by
    calc
      P ≤ scale * (M + 2) := hlen
      _ ≤ B ^ eScale * (M + 2) := Nat.mul_le_mul_right _ hscale
  have hPcube : P ^ 3 ≤ B ^ (3 * eScale) * (M + 2) ^ 3 := by
    calc
      P ^ 3 ≤ (B ^ eScale * (M + 2)) ^ 3 := by gcongr
      _ = (B ^ eScale) ^ 3 * (M + 2) ^ 3 := by rw [mul_pow]
      _ = B ^ (eScale * 3) * (M + 2) ^ 3 := by rw [← pow_mul]
      _ = B ^ (3 * eScale) * (M + 2) ^ 3 := by
        rw [Nat.mul_comm eScale 3]
  have hpow : B ^ eDen = B ^ (eDen - 3 * eScale) * B ^ (3 * eScale) := by
    calc
      B ^ eDen = B ^ (eDen - 3 * eScale + 3 * eScale) := by
        congr 1
        exact (Nat.sub_add_cancel hbudget).symm
      _ = B ^ (eDen - 3 * eScale) * B ^ (3 * eScale) := by rw [Nat.pow_add]
  have hmul :
      (q' * B ^ (eDen - 3 * eScale)) * B ^ (3 * eScale) ≤
        ((M + 2) ^ 3) * B ^ (3 * eScale) := by
    calc
      (q' * B ^ (eDen - 3 * eScale)) * B ^ (3 * eScale) =
          q' * B ^ eDen := by rw [hpow]; ac_rfl
      _ ≤ q * B ^ eDen := Nat.mul_le_mul_right _ hq'reduced
      _ ≤ P ^ 3 := hqUpper
      _ ≤ B ^ (3 * eScale) * (M + 2) ^ 3 := hPcube
      _ = ((M + 2) ^ 3) * B ^ (3 * eScale) := by ac_rfl
  have hcancel : 0 < B ^ (3 * eScale) := by positivity
  exact Nat.le_of_mul_le_mul_right hmul hcancel

/-- Convert a source real-log upper range to the natural-power ceiling used
by the transformed progression estimate. -/
theorem nat_denominator_upper_of_real_log_bound
    (L : ℝ) (B q P sigma : ℕ)
    (hL : 0 < L) (hB : (B : ℝ) ≤ L)
    (hq : (q : ℝ) ≤ (P : ℝ) ^ 3 / L ^ sigma) :
    q * B ^ sigma ≤ P ^ 3 := by
  have hpow : (B : ℝ) ^ sigma ≤ L ^ sigma := by gcongr
  have hqL : (q : ℝ) * L ^ sigma ≤ (P : ℝ) ^ 3 :=
    (le_div_iff₀ (by positivity : 0 < L ^ sigma)).mp hq
  have hreal : (q : ℝ) * (B : ℝ) ^ sigma ≤ (P : ℝ) ^ 3 := by
    calc
      (q : ℝ) * (B : ℝ) ^ sigma ≤ (q : ℝ) * L ^ sigma :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ (P : ℝ) ^ 3 := hqL
  exact_mod_cast hreal

/-- Hua's cubic Type-I parameter budget supplies the transformed upper
denominator window from the source bounds on `ell` and `Q`, once the exact
progression-length inequality is provided. -/
theorem hua_cubic_typeI_upper_window_of_natural_ranges
    (B ell Q q q' M P sigma sigma0 sigma3 sigma4 : ℕ)
    (hB : 1 ≤ B)
    (hell : ell ≤ B ^ (sigma3 + 1))
    (hQ : Q ≤ B ^ (sigma4 + 1))
    (hlen : P ≤ (ell * (Q / Nat.gcd Q ell)) * (M + 2))
    (hqUpper : q * B ^ sigma ≤ P ^ 3)
    (hq'reduced : q' ≤ q)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma) :
    q' * B ^ (sigma - 3 * (sigma3 + sigma4 + 2)) ≤ (M + 2) ^ 3 := by
  have hscaleStep : Q / Nat.gcd Q ell ≤ Q := Nat.div_le_self Q _
  have hscale : ell * (Q / Nat.gcd Q ell) ≤ B ^ (sigma3 + sigma4 + 2) := by
    calc
      ell * (Q / Nat.gcd Q ell) ≤ ell * Q := Nat.mul_le_mul_left ell hscaleStep
      _ ≤ B ^ (sigma3 + 1) * B ^ (sigma4 + 1) := Nat.mul_le_mul hell hQ
      _ = B ^ ((sigma3 + 1) + (sigma4 + 1)) := by rw [← pow_add]
      _ = B ^ (sigma3 + sigma4 + 2) := by congr 1; omega
  have hbudget' : 3 * (sigma3 + sigma4 + 2) ≤ sigma := by omega
  exact cubic_scaled_denominator_upper_bound_of_power_bounds
    B (ell * (Q / Nat.gcd Q ell)) M P q q'
      (sigma3 + sigma4 + 2) sigma hB hbudget' hscale hlen hqUpper hq'reduced

/-- Hua's exponent budget supports the threshold choice `T = B^4` with a
residual `B⁻¹` saving, provided the source cutoff exponent is at least five.
The first inequality controls the leading `T/q` term from the spacing
envelope; the second leaves room for `log q ≤ B` in its large-denominator
term; the third absorbs the seventh-log divisor-moment tail. This is exponent
bookkeeping only: the real-valued spacing estimate still has to be normalized
and assembled into the Type-I sum. -/
theorem hua_cubic_typeI_threshold_exponents
    (sigma sigma0 sigma3 sigma4 : ℕ)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma)
    (hsigma0 : 5 ≤ sigma0) :
    4 + 1 ≤ sigma0 ∧
      4 + 1 + 1 ≤ sigma - 3 * (sigma3 + sigma4 + 2) ∧
      1 + 7 ≤ 2 * 4 := by
  have hrho : 6 ≤ sigma - 3 * (sigma3 + sigma4 + 2) := by omega
  omega

/-- The stronger lower-denominator cutoff needed to absorb the progression
scale `s^3≤B^(3e)` into the thresholded spacing estimate. The first output
margin gives `B^5 s^3≤q'`; the Hua budget supplies the upper-window margin
`B^6 s^3≤B^(sigma-3e)`. -/
theorem hua_cubic_typeI_scaled_threshold_exponents
    (sigma sigma0 sigma3 sigma4 : ℕ)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma)
    (hcutoff : 3 * (sigma3 + sigma4 + 2) + 5 ≤ sigma0) :
    3 * (sigma3 + sigma4 + 2) + 5 ≤ sigma0 ∧
      3 * (sigma3 + sigma4 + 2) + 6 ≤
        sigma - 3 * (sigma3 + sigma4 + 2) := by
  omega

/-- Cubing a progression-step power bound gives the exact natural-power
bound on the error constant `K=s^3` used by the scaled spacing envelope. -/
theorem progressionStep_cube_le_log_power
    (step B e : ℕ) (hstep : step ≤ B ^ e) :
    step ^ 3 ≤ B ^ (3 * e) := by
  calc
    step ^ 3 ≤ (B ^ e) ^ 3 := by gcongr
    _ = B ^ (3 * e) := by
      rw [← pow_mul]
      congr 1
      omega

/-- A progression whose step is bounded by a fixed power of the floor-log
scale still has length exceeding any prescribed floor-log power, eventually.
The endpoint condition is the exact one supplied by
`progression_quotient_length_covers_endpoint`; this lemma does not posit an
independent lower bound on the progression length. -/
theorem eventually_progression_length_dominates_logarithmic_power
    (e K : ℕ) :
    ∀ᶠ P : ℕ in atTop,
      ∀ (step M : ℕ),
        step ≤ (Nat.floor (Real.log ((P : ℝ) + 2))) ^ e →
        P ≤ step * (M + 2) →
        (Nat.floor (Real.log ((P : ℝ) + 2))) ^ K ≤ M + 2 := by
  filter_upwards
    [tendsto_logarithmicDenominatorCutoff 1 (by omega) |>.eventually_ge_atTop 1,
      eventually_logarithmicDenominatorCutoff_pow_le_rpow 1 (e + K)
        (by norm_num : (0 : ℝ) < 1)] with P hBpos hscale
  intro step M hstep hlen
  let B : ℕ := Nat.floor (Real.log ((P : ℝ) + 2))
  have hB : 1 ≤ Nat.floor (Real.log ((P : ℝ) + 2)) := by
    have h := hBpos
    simpa [logarithmicDenominatorCutoff, Nat.pow_one] using h
  have hscaleReal :
      ((Nat.floor (Real.log ((P : ℝ) + 2)) : ℕ) : ℝ) ^ (e + K) ≤
        (P : ℝ) := by
    simpa [logarithmicDenominatorCutoff, Nat.pow_one, Real.rpow_one] using hscale
  have hscaleNat : B ^ (e + K) ≤ P := by
    dsimp [B]
    exact_mod_cast hscaleReal
  have hlen' : P ≤ B ^ e * (M + 2) := by
    calc
      P ≤ step * (M + 2) := hlen
      _ ≤ B ^ e * (M + 2) := Nat.mul_le_mul_right _ hstep
  have hmul : B ^ e * B ^ K ≤ B ^ e * (M + 2) := by
    calc
      B ^ e * B ^ K = B ^ (e + K) := by rw [Nat.pow_add]
      _ ≤ P := hscaleNat
      _ ≤ B ^ e * (M + 2) := hlen'
  have hBpos' : 0 < B := by omega
  apply Nat.le_of_mul_le_mul_left (c := B ^ e) ?_ (Nat.pow_pos hBpos')
  exact hmul

/-- Hua's cubic Type-I exponent budget dominates the denominator loss from
the progression phase, once its real-log bounds have been converted to the
displayed natural-power bounds. The `+1` in `eQ` absorbs the fixed implied
constant in `Q ≪ L^σ₄`. -/
theorem hua_cubic_typeI_budget_gives_reduced_denominator_range
    (a B ell Q cutoff q sigma sigma0 sigma3 sigma4 : ℕ)
    (hB : 2 ≤ B) (hQpos : 0 < Q) (hellpos : 0 < ell)
    (hac : Nat.Coprime a q)
    (hell : ell ≤ B ^ (sigma3 + 1))
    (hQ : Q ≤ B ^ (sigma4 + 1))
    (hcut : cutoff ≤ B ^ (sigma0 + 1))
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma)
    (hq : B ^ sigma < q) :
    cutoff < q / Nat.gcd q (a * (ell * (Q / Nat.gcd Q ell)) ^ 3) := by
  have hexp :
      3 * ((sigma3 + 1) + (sigma4 + 1)) + ((sigma0 + 1) + 1) ≤ sigma := by
    omega
  have hlarge := cubic_scaled_denominator_lower_bound_of_power_bounds
    B ell Q cutoff q (sigma3 + 1) (sigma4 + 1) (sigma0 + 1) sigma
    hB hell hQ hcut hexp hq
  exact generalCubicLeadingCoeff_reduced_denominator_gt_of_ell_Q_bound
    a q ell Q cutoff hQpos hellpos hac hlarge

/-- Eventual conversion of Hua's logarithmic source ranges to the natural
power hypotheses used by the progression-denominator argument. The fixed
constant in `Q ≤ cQ * L^sigma4` is absorbed by one spare floor power; the
source lower bound `L^sigma < q` passes to `floor(L)^sigma < q` by monotonicity.
This is only the parameter conversion, not a Type-I exponential-sum estimate. -/
theorem eventually_hua_cubic_log_ranges_give_reduced_denominator_range
    (a : ℕ) (cQ : ℝ) (hcQ : 0 ≤ cQ)
    (sigma sigma0 sigma3 sigma4 : ℕ)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma) :
    ∀ᶠ L : ℝ in atTop,
      ∀ ell Q cutoff q : ℕ,
        0 < Q → 0 < ell → Nat.Coprime a q →
        (ell : ℝ) ≤ L ^ sigma3 →
        (Q : ℝ) ≤ cQ * L ^ sigma4 →
        (cutoff : ℝ) ≤ L ^ sigma0 →
        L ^ sigma < (q : ℝ) →
        cutoff < q / Nat.gcd q (a * (ell * (Q / Nat.gcd Q ell)) ^ 3) := by
  filter_upwards
    [eventually_const_mul_pow_le_natFloor_pow_succ 1 (by norm_num) sigma3,
      eventually_const_mul_pow_le_natFloor_pow_succ cQ hcQ sigma4,
      eventually_const_mul_pow_le_natFloor_pow_succ 1 (by norm_num) sigma0,
      eventually_ge_atTop (3 : ℝ)] with
    L hellPow hQPow hcutPow hL
  intro ell Q cutoff q hQpos hellpos hac hell hQ hcut hq
  let B : ℕ := Nat.floor L
  have hBfloor : 2 ≤ Nat.floor L :=
    Nat.le_floor (by linarith : (2 : ℝ) ≤ L)
  have hB : 2 ≤ B := by
    dsimp [B]
    exact hBfloor
  have hEllReal : (ell : ℝ) ≤ (B : ℝ) ^ (sigma3 + 1) := by
    exact hell.trans (by simpa [B] using hellPow)
  have hEllNat : ell ≤ B ^ (sigma3 + 1) := by exact_mod_cast hEllReal
  have hQReal : (Q : ℝ) ≤ (B : ℝ) ^ (sigma4 + 1) :=
    hQ.trans (by simpa [B] using hQPow)
  have hQNat : Q ≤ B ^ (sigma4 + 1) := by exact_mod_cast hQReal
  have hcutReal : (cutoff : ℝ) ≤ (B : ℝ) ^ (sigma0 + 1) :=
    hcut.trans (by simpa [B] using hcutPow)
  have hcutNat : cutoff ≤ B ^ (sigma0 + 1) := by exact_mod_cast hcutReal
  have hfloorPow : (B : ℝ) ^ sigma ≤ L ^ sigma := by
    simpa [B] using natFloor_pow_le_of_nonneg L (by linarith) sigma
  have hqReal : (B : ℝ) ^ sigma < (q : ℝ) := hfloorPow.trans_lt hq
  have hqNat : B ^ sigma < q := by exact_mod_cast hqReal
  exact hua_cubic_typeI_budget_gives_reduced_denominator_range
    a B ell Q cutoff q sigma sigma0 sigma3 sigma4 hB hQpos hellpos hac
    hEllNat hQNat hcutNat hbudget hqNat

/-- Uniform-numerator version of the source-range conversion. The eventual
threshold depends only on the logarithmic scale and Hua's exponent budget,
not on the numerator in the reduced rational approximation. -/
theorem eventually_hua_cubic_log_ranges_give_reduced_denominator_range_uniform_a
    (cQ : ℝ) (hcQ : 0 ≤ cQ)
    (sigma sigma0 sigma3 sigma4 : ℕ)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma) :
    ∀ᶠ L : ℝ in atTop,
      ∀ a ell Q cutoff q : ℕ,
        0 < Q → 0 < ell → Nat.Coprime a q →
        (ell : ℝ) ≤ L ^ sigma3 →
        (Q : ℝ) ≤ cQ * L ^ sigma4 →
        (cutoff : ℝ) ≤ L ^ sigma0 →
        L ^ sigma < (q : ℝ) →
        cutoff < q / Nat.gcd q (a * (ell * (Q / Nat.gcd Q ell)) ^ 3) := by
  filter_upwards
    [eventually_const_mul_pow_le_natFloor_pow_succ 1 (by norm_num) sigma3,
      eventually_const_mul_pow_le_natFloor_pow_succ cQ hcQ sigma4,
      eventually_const_mul_pow_le_natFloor_pow_succ 1 (by norm_num) sigma0,
      eventually_ge_atTop (3 : ℝ)] with
    L hellPow hQPow hcutPow hL
  intro a ell Q cutoff q hQpos hellpos hac hell hQ hcut hq
  let B : ℕ := Nat.floor L
  have hBfloor : 2 ≤ Nat.floor L :=
    Nat.le_floor (by linarith : (2 : ℝ) ≤ L)
  have hB : 2 ≤ B := by
    dsimp [B]
    exact hBfloor
  have hEllReal : (ell : ℝ) ≤ (B : ℝ) ^ (sigma3 + 1) := by
    exact hell.trans (by simpa [B] using hellPow)
  have hEllNat : ell ≤ B ^ (sigma3 + 1) := by exact_mod_cast hEllReal
  have hQReal : (Q : ℝ) ≤ (B : ℝ) ^ (sigma4 + 1) :=
    hQ.trans (by simpa [B] using hQPow)
  have hQNat : Q ≤ B ^ (sigma4 + 1) := by exact_mod_cast hQReal
  have hcutReal : (cutoff : ℝ) ≤ (B : ℝ) ^ (sigma0 + 1) :=
    hcut.trans (by simpa [B] using hcutPow)
  have hcutNat : cutoff ≤ B ^ (sigma0 + 1) := by exact_mod_cast hcutReal
  have hfloorPow : (B : ℝ) ^ sigma ≤ L ^ sigma := by
    simpa [B] using natFloor_pow_le_of_nonneg L (by linarith) sigma
  have hqReal : (B : ℝ) ^ sigma < (q : ℝ) := hfloorPow.trans_lt hq
  have hqNat : B ^ sigma < q := by exact_mod_cast hqReal
  exact hua_cubic_typeI_budget_gives_reduced_denominator_range
    a B ell Q cutoff q sigma sigma0 sigma3 sigma4 hB hQpos hellpos hac
    hEllNat hQNat hcutNat hbudget hqNat

/-- Specialize the eventual logarithmic range conversion to the project's
natural scale `N`, with Hua's `L = log(N+2)`. The additive shift keeps the log
positive even at the initial endpoint and does not affect its divergence. -/
theorem eventually_hua_cubic_log_ranges_give_reduced_denominator_range_at_scale
    (a : ℕ) (cQ : ℝ) (hcQ : 0 ≤ cQ)
    (sigma sigma0 sigma3 sigma4 : ℕ)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma) :
    ∀ᶠ N : ℕ in atTop,
      ∀ ell Q cutoff q : ℕ,
        0 < Q → 0 < ell → Nat.Coprime a q →
        (ell : ℝ) ≤ Real.log ((N : ℝ) + 2) ^ sigma3 →
        (Q : ℝ) ≤ cQ * Real.log ((N : ℝ) + 2) ^ sigma4 →
        (cutoff : ℝ) ≤ Real.log ((N : ℝ) + 2) ^ sigma0 →
        Real.log ((N : ℝ) + 2) ^ sigma < (q : ℝ) →
        cutoff < q / Nat.gcd q (a * (ell * (Q / Nat.gcd Q ell)) ^ 3) := by
  have harg : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop := by
    convert tendsto_atTop_add_const_right _ (2 : ℝ)
      tendsto_natCast_atTop_atTop using 1
  have hlog : Tendsto
      (fun N : ℕ => Real.log ((N : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp harg
  exact hlog.eventually
    (eventually_hua_cubic_log_ranges_give_reduced_denominator_range
      a cQ hcQ sigma sigma0 sigma3 sigma4 hbudget)

/-- The same reduced-denominator conversion at `L=log(P+2)`, with one
eventual threshold valid simultaneously for every leading numerator `a`. -/
theorem eventually_hua_cubic_log_ranges_give_reduced_denominator_range_at_scale_uniform_a
    (cQ : ℝ) (hcQ : 0 ≤ cQ)
    (sigma sigma0 sigma3 sigma4 : ℕ)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma) :
    ∀ᶠ P : ℕ in atTop,
      ∀ a ell Q cutoff q : ℕ,
        0 < Q → 0 < ell → Nat.Coprime a q →
        (ell : ℝ) ≤ Real.log ((P : ℝ) + 2) ^ sigma3 →
        (Q : ℝ) ≤ cQ * Real.log ((P : ℝ) + 2) ^ sigma4 →
        (cutoff : ℝ) ≤ Real.log ((P : ℝ) + 2) ^ sigma0 →
        Real.log ((P : ℝ) + 2) ^ sigma < (q : ℝ) →
        cutoff < q / Nat.gcd q (a * (ell * (Q / Nat.gcd Q ell)) ^ 3) := by
  have harg : Tendsto (fun P : ℕ => (P : ℝ) + 2) atTop atTop := by
    convert tendsto_atTop_add_const_right _ (2 : ℝ)
      tendsto_natCast_atTop_atTop using 1
  have hlog : Tendsto
      (fun P : ℕ => Real.log ((P : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp harg
  exact hlog.eventually
    (eventually_hua_cubic_log_ranges_give_reduced_denominator_range_uniform_a
      cQ hcQ sigma sigma0 sigma3 sigma4 hbudget)

/-- The preceding source-range adapter also applies directly to the project's
floor-log cutoff, as soon as its exponent `A` does not exceed Hua's allowed
cutoff exponent `sigma0`. -/
theorem eventually_hua_cubic_logarithmicCutoff_gives_reduced_denominator_range
    (a : ℕ) (cQ : ℝ) (hcQ : 0 ≤ cQ)
    (A sigma sigma0 sigma3 sigma4 : ℕ) (hA : A ≤ sigma0)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma) :
    ∀ᶠ N : ℕ in atTop,
      ∀ ell Q q : ℕ,
        0 < Q → 0 < ell → Nat.Coprime a q →
        (ell : ℝ) ≤ Real.log ((N : ℝ) + 2) ^ sigma3 →
        (Q : ℝ) ≤ cQ * Real.log ((N : ℝ) + 2) ^ sigma4 →
        Real.log ((N : ℝ) + 2) ^ sigma < (q : ℝ) →
        logarithmicDenominatorCutoff A N <
          q / Nat.gcd q (a * (ell * (Q / Nat.gcd Q ell)) ^ 3) := by
  filter_upwards
    [eventually_logarithmicDenominatorCutoff_le_log_pow A sigma0 hA,
      eventually_hua_cubic_log_ranges_give_reduced_denominator_range_at_scale
        a cQ hcQ sigma sigma0 sigma3 sigma4 hbudget] with
    N hcut hrange
  intro ell Q q hQpos hellpos hac hell hQ hq
  exact hrange ell Q (logarithmicDenominatorCutoff A N) q
    hQpos hellpos hac hell hQ hcut hq

/-- The quotient coordinate for the progression cutoff is long enough that
the original endpoint is covered by `step * (coordinate + 2)`. The spare two
steps account for the initial representative and final division remainder. -/
theorem progression_quotient_length_covers_endpoint
    (base step P : ℕ) (hstep : 0 < step)
    (hbaseStep : base ≤ step) (hbaseP : base ≤ P) :
    P ≤ step * ((P - base) / step + 2) := by
  have hrem : (P - base) % step < step := Nat.mod_lt _ hstep
  have hremLe : (P - base) % step ≤ step := Nat.le_of_lt hrem
  have hdecomp : (P - base) % step + step * ((P - base) / step) = P - base :=
    Nat.mod_add_div _ _
  have hbaseRem : base + (P - base) % step ≤ step + step :=
    Nat.add_le_add hbaseStep hremLe
  calc
    P = base + (P - base) := (Nat.add_sub_of_le hbaseP).symm
    _ = base + ((P - base) % step + step * ((P - base) / step)) := by
      rw [hdecomp]
    _ = base + (P - base) % step + step * ((P - base) / step) := by ac_rfl
    _ ≤ (step + step) + step * ((P - base) / step) :=
      Nat.add_le_add_right hbaseRem _
    _ = step * ((P - base) / step + 2) := by
      rw [Nat.mul_add, Nat.mul_two]
      omega

/-- Assemble Hua's real-log source ranges into both sides of the reduced
denominator window for a Type-I progression. Its exact length relation is
derived from the canonical representative and quotient cutoff; it supplies
range data, not the Weyl saving. -/
theorem eventually_hua_cubic_log_ranges_give_transformed_denominator_window
    (a : ℕ) (cQ : ℝ) (hcQ : 0 ≤ cQ)
    (sigma sigma0 sigma3 sigma4 : ℕ)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma) :
    ∀ᶠ P : ℕ in atTop,
      ∀ ell Q q r : ℕ,
        0 < Q → 0 < ell → 0 < r →
        r ≤ Q / Nat.gcd Q ell → ell * r ≤ P → Nat.Coprime a q →
        (ell : ℝ) ≤ Real.log ((P : ℝ) + 2) ^ sigma3 →
        (Q : ℝ) ≤ cQ * Real.log ((P : ℝ) + 2) ^ sigma4 →
        Real.log ((P : ℝ) + 2) ^ sigma < (q : ℝ) →
        (q : ℝ) ≤ (P : ℝ) ^ 3 / Real.log ((P : ℝ) + 2) ^ sigma →
        (Nat.floor (Real.log ((P : ℝ) + 2))) ^ sigma0 <
            q / Nat.gcd q (a * (ell * (Q / Nat.gcd Q ell)) ^ 3) ∧
          (q / Nat.gcd q (a * (ell * (Q / Nat.gcd Q ell)) ^ 3)) *
              (Nat.floor (Real.log ((P : ℝ) + 2))) ^
                (sigma - 3 * (sigma3 + sigma4 + 2)) ≤
            ((P - ell * r) / (ell * (Q / Nat.gcd Q ell)) + 2) ^ 3 := by
  have harg : Tendsto (fun P : ℕ => (P : ℝ) + 2) atTop atTop := by
    convert tendsto_atTop_add_const_right _ (2 : ℝ)
      tendsto_natCast_atTop_atTop using 1
  have hlog : Tendsto
      (fun P : ℕ => Real.log ((P : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp harg
  filter_upwards
    [eventually_hua_cubic_log_ranges_give_reduced_denominator_range_at_scale
        a cQ hcQ sigma sigma0 sigma3 sigma4 hbudget,
      hlog.eventually
        (eventually_const_mul_pow_le_natFloor_pow_succ
          1 (by norm_num) sigma3),
      hlog.eventually
        (eventually_const_mul_pow_le_natFloor_pow_succ cQ hcQ sigma4),
      hlog.eventually (eventually_ge_atTop (3 : ℝ))] with
    P hlower hellPow hQPow hL
  intro ell Q q r hQpos hellpos hrpos hrle hbase hac hell hQ hqLower hqUpper
  let L : ℝ := Real.log ((P : ℝ) + 2)
  let B : ℕ := Nat.floor L
  have hLlarge : (3 : ℝ) ≤ L := by simpa [L] using hL
  have hLpos : 0 < L := by linarith
  have hBtwo : 2 ≤ B := Nat.le_floor (by
    exact_mod_cast (show (2 : ℝ) ≤ L by linarith))
  have hB : 1 ≤ B := by omega
  have hBcast : (B : ℝ) ≤ L := by
    dsimp [B]
    exact Nat.floor_le hLpos.le
  have hEllBound : ell ≤ B ^ (sigma3 + 1) := by
    have hreal : (ell : ℝ) ≤ (B : ℝ) ^ (sigma3 + 1) :=
      hell.trans (by simpa [L, B] using hellPow)
    exact_mod_cast hreal
  have hQBound : Q ≤ B ^ (sigma4 + 1) := by
    have hreal : (Q : ℝ) ≤ (B : ℝ) ^ (sigma4 + 1) :=
      hQ.trans (by simpa [L, B] using hQPow)
    exact_mod_cast hreal
  have hqUpperNat := nat_denominator_upper_of_real_log_bound
    L B q P sigma hLpos hBcast (by simpa [L] using hqUpper)
  have hlower' := hlower ell Q (B ^ sigma0) q
    hQpos hellpos hac hell hQ
  have hcutoff : ((B ^ sigma0 : ℕ) : ℝ) ≤ L ^ sigma0 := by
    have hp := natFloor_pow_le_of_nonneg L (by linarith) sigma0
    simpa [B] using hp
  have hqLower' : L ^ sigma < (q : ℝ) := by simpa [L] using hqLower
  have hlow := hlower' hcutoff hqLower'
  have hgpos : 0 < Nat.gcd Q ell := Nat.gcd_pos_of_pos_left ell hQpos
  have hstep : 0 < Q / Nat.gcd Q ell :=
    Nat.div_pos (Nat.le_of_dvd hQpos (Nat.gcd_dvd_left Q ell)) hgpos
  have hscale : 0 < ell * (Q / Nat.gcd Q ell) := Nat.mul_pos hellpos hstep
  have hbaseStep : ell * r ≤ ell * (Q / Nat.gcd Q ell) :=
    Nat.mul_le_mul_left ell hrle
  let M := (P - ell * r) / (ell * (Q / Nat.gcd Q ell))
  have hlen : P ≤ (ell * (Q / Nat.gcd Q ell)) * (M + 2) := by
    exact progression_quotient_length_covers_endpoint
      (ell * r) (ell * (Q / Nat.gcd Q ell)) P hscale hbaseStep hbase
  have hhigh := hua_cubic_typeI_upper_window_of_natural_ranges
    B ell Q q
      (q / Nat.gcd q (a * (ell * (Q / Nat.gcd Q ell)) ^ 3))
      M P sigma sigma0 sigma3 sigma4 hB hEllBound hQBound hlen hqUpperNat
      (Nat.div_le_self q _) hbudget
  simpa [M] using And.intro hlow hhigh

/-- Hua's transformed denominator window with a single endpoint threshold
for every numerator `a`. This removes witness-dependence from the eventual
quantifier when the rational approximant is selected separately at each
minor-arc point. -/
theorem eventually_hua_cubic_log_ranges_give_transformed_denominator_window_uniform_a
    (cQ : ℝ) (hcQ : 0 ≤ cQ)
    (sigma sigma0 sigma3 sigma4 : ℕ)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma) :
    ∀ᶠ P : ℕ in atTop,
      ∀ a ell Q q r : ℕ,
        0 < Q → 0 < ell → 0 < r →
        r ≤ Q / Nat.gcd Q ell → ell * r ≤ P → Nat.Coprime a q →
        (ell : ℝ) ≤ Real.log ((P : ℝ) + 2) ^ sigma3 →
        (Q : ℝ) ≤ cQ * Real.log ((P : ℝ) + 2) ^ sigma4 →
        Real.log ((P : ℝ) + 2) ^ sigma < (q : ℝ) →
        (q : ℝ) ≤ (P : ℝ) ^ 3 / Real.log ((P : ℝ) + 2) ^ sigma →
        (Nat.floor (Real.log ((P : ℝ) + 2))) ^ sigma0 <
            q / Nat.gcd q (a * (ell * (Q / Nat.gcd Q ell)) ^ 3) ∧
          (q / Nat.gcd q (a * (ell * (Q / Nat.gcd Q ell)) ^ 3)) *
              (Nat.floor (Real.log ((P : ℝ) + 2))) ^
                (sigma - 3 * (sigma3 + sigma4 + 2)) ≤
            ((P - ell * r) / (ell * (Q / Nat.gcd Q ell)) + 2) ^ 3 := by
  have harg : Tendsto (fun P : ℕ => (P : ℝ) + 2) atTop atTop := by
    convert tendsto_atTop_add_const_right _ (2 : ℝ)
      tendsto_natCast_atTop_atTop using 1
  have hlog : Tendsto
      (fun P : ℕ => Real.log ((P : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp harg
  filter_upwards
    [eventually_hua_cubic_log_ranges_give_reduced_denominator_range_at_scale_uniform_a
        cQ hcQ sigma sigma0 sigma3 sigma4 hbudget,
      hlog.eventually
        (eventually_const_mul_pow_le_natFloor_pow_succ
          1 (by norm_num) sigma3),
      hlog.eventually
        (eventually_const_mul_pow_le_natFloor_pow_succ cQ hcQ sigma4),
      hlog.eventually (eventually_ge_atTop (3 : ℝ))] with
    P hlower hellPow hQPow hL
  intro a ell Q q r hQpos hellpos hrpos hrle hbase hac hell hQ hqLower hqUpper
  let L : ℝ := Real.log ((P : ℝ) + 2)
  let B : ℕ := Nat.floor L
  have hLlarge : (3 : ℝ) ≤ L := by simpa [L] using hL
  have hLpos : 0 < L := by linarith
  have hBtwo : 2 ≤ B := Nat.le_floor (by
    exact_mod_cast (show (2 : ℝ) ≤ L by linarith))
  have hB : 1 ≤ B := by omega
  have hBcast : (B : ℝ) ≤ L := by
    dsimp [B]
    exact Nat.floor_le hLpos.le
  have hEllBound : ell ≤ B ^ (sigma3 + 1) := by
    have hreal : (ell : ℝ) ≤ (B : ℝ) ^ (sigma3 + 1) :=
      hell.trans (by simpa [L, B] using hellPow)
    exact_mod_cast hreal
  have hQBound : Q ≤ B ^ (sigma4 + 1) := by
    have hreal : (Q : ℝ) ≤ (B : ℝ) ^ (sigma4 + 1) :=
      hQ.trans (by simpa [L, B] using hQPow)
    exact_mod_cast hreal
  have hqUpperNat := nat_denominator_upper_of_real_log_bound
    L B q P sigma hLpos hBcast (by simpa [L] using hqUpper)
  have hlower' := hlower a ell Q (B ^ sigma0) q
    hQpos hellpos hac hell hQ
  have hcutoff : ((B ^ sigma0 : ℕ) : ℝ) ≤ L ^ sigma0 := by
    have hp := natFloor_pow_le_of_nonneg L (by linarith) sigma0
    simpa [B] using hp
  have hqLower' : L ^ sigma < (q : ℝ) := by simpa [L] using hqLower
  have hlow := hlower' hcutoff hqLower'
  have hgpos : 0 < Nat.gcd Q ell := Nat.gcd_pos_of_pos_left ell hQpos
  have hstep : 0 < Q / Nat.gcd Q ell :=
    Nat.div_pos (Nat.le_of_dvd hQpos (Nat.gcd_dvd_left Q ell)) hgpos
  have hscale : 0 < ell * (Q / Nat.gcd Q ell) := Nat.mul_pos hellpos hstep
  have hbaseStep : ell * r ≤ ell * (Q / Nat.gcd Q ell) :=
    Nat.mul_le_mul_left ell hrle
  let M := (P - ell * r) / (ell * (Q / Nat.gcd Q ell))
  have hlen : P ≤ (ell * (Q / Nat.gcd Q ell)) * (M + 2) := by
    exact progression_quotient_length_covers_endpoint
      (ell * r) (ell * (Q / Nat.gcd Q ell)) P hscale hbaseStep hbase
  have hhigh := hua_cubic_typeI_upper_window_of_natural_ranges
    B ell Q q
      (q / Nat.gcd q (a * (ell * (Q / Nat.gcd Q ell)) ^ 3))
      M P sigma sigma0 sigma3 sigma4 hB hEllBound hQBound hlen hqUpperNat
      (Nat.div_le_self q _) hbudget
  simpa [M] using And.intro hlow hhigh

/-- Hua's polylogarithmic bounds on `ell` and `Q` leave an arbitrarily large
fixed power of the floor-log scale inside each congruence progression,
eventually. The progression length is the exact quotient interval attached
to the canonical representative `ell*r`; the conclusion follows from its
endpoint coverage, not from an assumed lower bound on `M`. -/
theorem eventually_hua_cubic_progression_length_dominates_log_power
    (cQ : ℝ) (hcQ : 0 ≤ cQ) (sigma3 sigma4 K : ℕ) :
    ∀ᶠ P : ℕ in atTop,
      ∀ ell Q r : ℕ,
        0 < Q → 0 < ell → 0 < r →
        r ≤ Q / Nat.gcd Q ell → ell * r ≤ P →
        (ell : ℝ) ≤ Real.log ((P : ℝ) + 2) ^ sigma3 →
        (Q : ℝ) ≤ cQ * Real.log ((P : ℝ) + 2) ^ sigma4 →
        (Nat.floor (Real.log ((P : ℝ) + 2))) ^ K ≤
          (P - ell * r) / (ell * (Q / Nat.gcd Q ell)) + 2 := by
  have harg : Tendsto (fun P : ℕ => (P : ℝ) + 2) atTop atTop := by
    convert tendsto_atTop_add_const_right _ (2 : ℝ)
      tendsto_natCast_atTop_atTop using 1
  have hlog : Tendsto
      (fun P : ℕ => Real.log ((P : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp harg
  filter_upwards
    [hlog.eventually_ge_atTop (3 : ℝ),
      hlog.eventually
        (eventually_const_mul_pow_le_natFloor_pow_succ
          1 (by norm_num) sigma3),
      hlog.eventually
        (eventually_const_mul_pow_le_natFloor_pow_succ cQ hcQ sigma4),
      eventually_progression_length_dominates_logarithmic_power
        (sigma3 + sigma4 + 2) K] with P hL hellPow hQPow hlong
  intro ell Q r hQpos hellpos hrpos hrle hbase hell hQ
  let L : ℝ := Real.log ((P : ℝ) + 2)
  let B : ℕ := Nat.floor L
  have hLlarge : (3 : ℝ) ≤ L := by simpa [L] using hL
  have hLpos : 0 < L := by linarith
  have hB : 1 ≤ B := by
    dsimp [B]
    exact Nat.le_floor (by exact_mod_cast (show (1 : ℝ) ≤ L by linarith))
  have hBcast : (B : ℝ) ≤ L := by
    dsimp [B]
    exact Nat.floor_le hLpos.le
  have hellNat : ell ≤ B ^ (sigma3 + 1) := by
    have hreal : (ell : ℝ) ≤ (B : ℝ) ^ (sigma3 + 1) :=
      hell.trans (by simpa [L, B] using hellPow)
    exact_mod_cast hreal
  have hQNat : Q ≤ B ^ (sigma4 + 1) := by
    have hreal : (Q : ℝ) ≤ (B : ℝ) ^ (sigma4 + 1) :=
      hQ.trans (by simpa [L, B] using hQPow)
    exact_mod_cast hreal
  let step := ell * (Q / Nat.gcd Q ell)
  have hgpos : 0 < Nat.gcd Q ell := Nat.gcd_pos_of_pos_left ell hQpos
  have hstepPos : 0 < step := by
    dsimp [step]
    exact Nat.mul_pos hellpos (Nat.div_pos
      (Nat.le_of_dvd hQpos (Nat.gcd_dvd_left Q ell)) hgpos)
  have hstepLe : step ≤ B ^ (sigma3 + sigma4 + 2) := by
    dsimp [step]
    calc
      ell * (Q / Nat.gcd Q ell) ≤ ell * Q :=
        Nat.mul_le_mul_left ell (Nat.div_le_self Q _)
      _ ≤ B ^ (sigma3 + 1) * B ^ (sigma4 + 1) :=
        Nat.mul_le_mul hellNat hQNat
      _ = B ^ (sigma3 + sigma4 + 2) := by
        rw [← pow_add]
        congr 1
        omega
  let M := (P - ell * r) / step
  have hbaseStep : ell * r ≤ step :=
    Nat.mul_le_mul_left ell hrle
  have hlen : P ≤ step * (M + 2) := by
    exact progression_quotient_length_covers_endpoint
      (ell * r) step P hstepPos hbaseStep hbase
  have hlong' := hlong step M hstepLe hlen
  simpa [L, B, M, step] using hlong'

/-- Combine Hua's real-log source ranges, the exact quotient progression, and
the scaled divisor-threshold estimate into a logarithmically saving bound for
the progression's positive product-pair envelope, centered at the exactly
reduced rational leading coefficient. This remains a Weyl coefficient bound,
not the prime Type-I sum: Vaughan's coefficients have not yet been summed. -/
theorem eventually_hua_cubic_progression_pair_envelope
    (a : ℕ) (cQ : ℝ) (hcQ : 0 ≤ cQ)
    (sigma sigma0 sigma3 sigma4 : ℕ)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma)
    (hcutoff : 3 * (sigma3 + sigma4 + 2) + 5 ≤ sigma0) :
    ∀ᶠ P : ℕ in atTop,
      ∀ ell Q q r : ℕ,
        0 < Q → 0 < ell → 0 < r →
        r ≤ Q / Nat.gcd Q ell → ell * r ≤ P → Nat.Coprime a q →
        (ell : ℝ) ≤ Real.log ((P : ℝ) + 2) ^ sigma3 →
        (Q : ℝ) ≤ cQ * Real.log ((P : ℝ) + 2) ^ sigma4 →
        Real.log ((P : ℝ) + 2) ^ sigma < (q : ℝ) →
        (q : ℝ) ≤ (P : ℝ) ^ 3 / Real.log ((P : ℝ) + 2) ^ sigma →
        let B := Nat.floor (Real.log ((P : ℝ) + 2))
        let step := ell * (Q / Nat.gcd Q ell)
        let M := (P - ell * r) / step
        let q' := q / Nat.gcd q (a * step ^ 3)
        let anum := (a * step ^ 3) / Nat.gcd q (a * step ^ 3)
        (∑ hk ∈ (Finset.Icc 1 (M + 1)).product (Finset.Icc 1 (M + 1)),
          linearDistanceEnvelope (M + 2 : ℝ)
            (6 * rationalCenter anum q' * (hk.1 * hk.2 : ℕ))) ≤
          79301 * (M + 2 : ℝ) ^ 3 / (B : ℝ) := by
  let e := sigma3 + sigma4 + 2
  have harg : Tendsto (fun P : ℕ => (P : ℝ) + 2) atTop atTop := by
    convert tendsto_atTop_add_const_right _ (2 : ℝ)
      tendsto_natCast_atTop_atTop using 1
  have hlog : Tendsto
      (fun P : ℕ => Real.log ((P : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp harg
  filter_upwards
    [hlog.eventually_ge_atTop (4 : ℝ),
      hlog.eventually
        (eventually_const_mul_pow_le_natFloor_pow_succ
          1 (by norm_num) sigma3),
      hlog.eventually
        (eventually_const_mul_pow_le_natFloor_pow_succ cQ hcQ sigma4),
      eventually_hua_cubic_log_ranges_give_transformed_denominator_window
        a cQ hcQ sigma sigma0 sigma3 sigma4 hbudget,
      eventually_hua_cubic_progression_length_dominates_log_power
        cQ hcQ sigma3 sigma4 (3 * e + 6)] with
    P hlogLarge hellPow hQPow hwindow hlength
  intro ell Q q r hQpos hellpos hrpos hrle hbase hac hell hQ hqLower hqUpper
  let L : ℝ := Real.log ((P : ℝ) + 2)
  let B : ℕ := Nat.floor L
  let step : ℕ := ell * (Q / Nat.gcd Q ell)
  let M : ℕ := (P - ell * r) / step
  let q' : ℕ := q / Nat.gcd q (a * step ^ 3)
  let anum : ℕ := (a * step ^ 3) / Nat.gcd q (a * step ^ 3)
  have hB : 3 ≤ B := by
    dsimp [B, L]
    have hfloor : 4 ≤ Nat.floor (Real.log ((P : ℝ) + 2)) :=
      Nat.le_floor (by simpa [L] using hlogLarge)
    omega
  have hBpos : 1 ≤ B := by omega
  have hBtwo : 2 ≤ B := by omega
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hBcast : (B : ℝ) ≤ L := by
    dsimp [B]
    exact Nat.floor_le hLpos.le
  have hellNat : ell ≤ B ^ (sigma3 + 1) := by
    have hreal : (ell : ℝ) ≤ (B : ℝ) ^ (sigma3 + 1) :=
      hell.trans (by simpa [B, L] using hellPow)
    exact_mod_cast hreal
  have hQNat : Q ≤ B ^ (sigma4 + 1) := by
    have hreal : (Q : ℝ) ≤ (B : ℝ) ^ (sigma4 + 1) :=
      hQ.trans (by simpa [B, L] using hQPow)
    exact_mod_cast hreal
  have hstepPos : 0 < step := by
    dsimp [step]
    exact Nat.mul_pos hellpos (Nat.div_pos
      (Nat.le_of_dvd hQpos (Nat.gcd_dvd_left Q ell))
      (Nat.gcd_pos_of_pos_left ell hQpos))
  have hstepBound : step ≤ B ^ e := by
    dsimp [step, e]
    calc
      ell * (Q / Nat.gcd Q ell) ≤ ell * Q :=
        Nat.mul_le_mul_left ell (Nat.div_le_self Q _)
      _ ≤ B ^ (sigma3 + 1) * B ^ (sigma4 + 1) :=
        Nat.mul_le_mul hellNat hQNat
      _ = B ^ (sigma3 + sigma4 + 2) := by rw [← pow_add]; congr 1; omega
  have hMleP : M ≤ P := by
    dsimp [M, step]
    exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hlen : B ^ (3 * e + 6) ≤ M + 2 := by
    have h := hlength ell Q r hQpos hellpos hrpos hrle hbase hell hQ
    simpa [L, B, M, step, e] using h
  have hwindow' := hwindow ell Q q r hQpos hellpos hrpos hrle hbase hac
    hell hQ hqLower hqUpper
  have hexp := hua_cubic_typeI_scaled_threshold_exponents
    sigma sigma0 sigma3 sigma4 hbudget hcutoff
  let rho := sigma - 3 * e
  have hrho : 3 * e + 6 ≤ rho := by
    dsimp [rho, e]
    exact hexp.2
  have hqpos : 0 < q := by
    have hqreal : (0 : ℝ) < (q : ℝ) :=
      lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ L ^ sigma) hqLower
    exact_mod_cast hqreal
  have hnumcop : Nat.Coprime anum q' := by
    dsimp [anum, q']
    exact generalCubicLeadingCoeff_reduced_coprime a q step hqpos
  have hpair :=
    sum_positiveProductPairs_sixMul_envelope_le_logSaving_of_progression_power_ranges_source_size
      P M step anum q' rho e sigma0 hB hMleP hstepPos hstepBound hcutoff
      hwindow'.1 hlen (by simpa [rho, e, B, M, step, q'] using hwindow'.2)
      hrho hnumcop
  simpa [L, B, step, M, q', anum, e] using hpair

/-- Arbitrarily high fixed logarithmic savings for the Hua progression pair
envelope. Increasing the cutoff exponent by `5*delta` and the available
progression/rho margins by `6*delta`/`7*delta` lets the fixed-scale argument
run at `B^delta`. -/
theorem eventually_hua_cubic_progression_pair_envelope_order
    (a : ℕ) (cQ : ℝ) (hcQ : 0 ≤ cQ)
    (sigma sigma0 sigma3 sigma4 delta : ℕ)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma)
    (hdelta : 1 ≤ delta)
    (hcutoff : 3 * (sigma3 + sigma4 + 2) + 5 * delta ≤ sigma0) :
    ∀ᶠ P : ℕ in atTop,
      ∀ ell Q q r : ℕ,
        0 < Q → 0 < ell → 0 < r →
        r ≤ Q / Nat.gcd Q ell → ell * r ≤ P → Nat.Coprime a q →
        (ell : ℝ) ≤ Real.log ((P : ℝ) + 2) ^ sigma3 →
        (Q : ℝ) ≤ cQ * Real.log ((P : ℝ) + 2) ^ sigma4 →
        Real.log ((P : ℝ) + 2) ^ sigma < (q : ℝ) →
        (q : ℝ) ≤ (P : ℝ) ^ 3 / Real.log ((P : ℝ) + 2) ^ sigma →
        let B := Nat.floor (Real.log ((P : ℝ) + 2))
        let step := ell * (Q / Nat.gcd Q ell)
        let M := (P - ell * r) / step
        let q' := q / Nat.gcd q (a * step ^ 3)
        let anum := (a * step ^ 3) / Nat.gcd q (a * step ^ 3)
        (∑ hk ∈ (Finset.Icc 1 (M + 1)).product (Finset.Icc 1 (M + 1)),
          linearDistanceEnvelope (M + 2 : ℝ)
            (6 * rationalCenter anum q' * (hk.1 * hk.2 : ℕ))) ≤
          79301 * (M + 2 : ℝ) ^ 3 / (B : ℝ) ^ delta := by
  let e := sigma3 + sigma4 + 2
  have harg : Tendsto (fun P : ℕ => (P : ℝ) + 2) atTop atTop := by
    convert tendsto_atTop_add_const_right _ (2 : ℝ)
      tendsto_natCast_atTop_atTop using 1
  have hlog : Tendsto
      (fun P : ℕ => Real.log ((P : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp harg
  filter_upwards
    [hlog.eventually_ge_atTop (4 : ℝ),
      hlog.eventually
        (eventually_const_mul_pow_le_natFloor_pow_succ
          1 (by norm_num) sigma3),
      hlog.eventually
        (eventually_const_mul_pow_le_natFloor_pow_succ cQ hcQ sigma4),
      eventually_hua_cubic_log_ranges_give_transformed_denominator_window
        a cQ hcQ sigma sigma0 sigma3 sigma4 hbudget,
      eventually_hua_cubic_progression_length_dominates_log_power
        cQ hcQ sigma3 sigma4 (3 * e + 6 * delta)] with
    P hlogLarge hellPow hQPow hwindow hlength
  intro ell Q q r hQpos hellpos hrpos hrle hbase hac hell hQ hqLower hqUpper
  let L : ℝ := Real.log ((P : ℝ) + 2)
  let B : ℕ := Nat.floor L
  let step : ℕ := ell * (Q / Nat.gcd Q ell)
  let M : ℕ := (P - ell * r) / step
  let q' : ℕ := q / Nat.gcd q (a * step ^ 3)
  let anum : ℕ := (a * step ^ 3) / Nat.gcd q (a * step ^ 3)
  have hB : 3 ≤ B := by
    dsimp [B, L]
    have hfloor : 4 ≤ Nat.floor (Real.log ((P : ℝ) + 2)) :=
      Nat.le_floor (by simpa [L] using hlogLarge)
    omega
  have hBpos : 1 ≤ B := by omega
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hellNat : ell ≤ B ^ (sigma3 + 1) := by
    have hreal : (ell : ℝ) ≤ (B : ℝ) ^ (sigma3 + 1) :=
      hell.trans (by simpa [B, L] using hellPow)
    exact_mod_cast hreal
  have hQNat : Q ≤ B ^ (sigma4 + 1) := by
    have hreal : (Q : ℝ) ≤ (B : ℝ) ^ (sigma4 + 1) :=
      hQ.trans (by simpa [B, L] using hQPow)
    exact_mod_cast hreal
  have hstepPos : 0 < step := by
    dsimp [step]
    exact Nat.mul_pos hellpos (Nat.div_pos
      (Nat.le_of_dvd hQpos (Nat.gcd_dvd_left Q ell))
      (Nat.gcd_pos_of_pos_left ell hQpos))
  have hstepBound : step ≤ B ^ e := by
    dsimp [step, e]
    calc
      ell * (Q / Nat.gcd Q ell) ≤ ell * Q :=
        Nat.mul_le_mul_left ell (Nat.div_le_self Q _)
      _ ≤ B ^ (sigma3 + 1) * B ^ (sigma4 + 1) :=
        Nat.mul_le_mul hellNat hQNat
      _ = B ^ (sigma3 + sigma4 + 2) := by rw [← pow_add]; congr 1; omega
  have hMleP : M ≤ P := by
    dsimp [M, step]
    exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hlen : B ^ (3 * e + 6 * delta) ≤ M + 2 := by
    have h := hlength ell Q r hQpos hellpos hrpos hrle hbase hell hQ
    simpa [L, B, M, step, e] using h
  have hwindow' := hwindow ell Q q r hQpos hellpos hrpos hrle hbase hac
    hell hQ hqLower hqUpper
  have hrho : 3 * e + 7 * delta ≤ sigma - 3 * e := by
    dsimp [e]
    omega
  have hqpos : 0 < q := by
    have hqreal : (0 : ℝ) < (q : ℝ) :=
      lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ L ^ sigma) hqLower
    exact_mod_cast hqreal
  have hnumcop : Nat.Coprime anum q' := by
    dsimp [anum, q']
    exact generalCubicLeadingCoeff_reduced_coprime a q step hqpos
  have hpair :=
    sum_positiveProductPairs_sixMul_envelope_le_logSaving_of_progression_power_ranges_source_size_order
      P M step anum q' (sigma - 3 * e) e sigma0 delta hB hMleP
      hstepPos hstepBound hdelta hcutoff hwindow'.1 hlen
      (by simpa [e, B, M, step, q'] using hwindow'.2) hrho hnumcop
  simpa [L, B, step, M, q', anum, e] using hpair

/-- A `q^-2` approximation remains controlled after progression scaling by
the explicit factor `s^3`, even when written with the reduced denominator. -/
theorem generalCubicLeadingCoeff_affineError_le_reduced
    (beta : ℝ) (a q s : ℕ) (hq : 0 < q) (hs : 0 < s)
    (hac : Nat.Coprime a q)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) :
    |beta| * (s : ℝ) ^ 3 ≤
      (s : ℝ) ^ 3 /
        ((q / Nat.gcd q (a * s ^ 3) : ℕ) : ℝ) ^ 2 := by
  obtain ⟨_, hq'reduced, hq'pos⟩ :=
    generalCubicLeadingCoeff_reduced_denominator_bounds a q s hq hs hac
  have hq'leq :
      ((q / Nat.gcd q (a * s ^ 3) : ℕ) : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hq'reduced
  have hq'posR :
      (0 : ℝ) < ((q / Nat.gcd q (a * s ^ 3) : ℕ) : ℝ) := by
    exact_mod_cast hq'pos
  have hreciprocal :
      (q : ℝ)⁻¹ ≤ ((q / Nat.gcd q (a * s ^ 3) : ℕ) : ℝ)⁻¹ :=
    by simpa [one_div] using one_div_le_one_div_of_le hq'posR hq'leq
  have hreciprocal_sq :
      (q : ℝ)⁻¹ ^ 2 ≤
        ((q / Nat.gcd q (a * s ^ 3) : ℕ) : ℝ)⁻¹ ^ 2 := by
    have hqinv : 0 ≤ (q : ℝ)⁻¹ := by positivity
    have hq'inv : 0 ≤ ((q / Nat.gcd q (a * s ^ 3) : ℕ) : ℝ)⁻¹ := by
      positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hreciprocal)
      (add_nonneg hqinv hq'inv)]
  have hbeta' : |beta| ≤ (q : ℝ)⁻¹ ^ 2 := by
    simpa [one_div] using hbeta
  calc
    |beta| * (s : ℝ) ^ 3 ≤ (q : ℝ)⁻¹ ^ 2 * (s : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_right hbeta' (by positivity)
    _ ≤ ((q / Nat.gcd q (a * s ^ 3) : ℕ) : ℝ)⁻¹ ^ 2 * (s : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_right hreciprocal_sq (by positivity)
    _ = (s : ℝ) ^ 3 /
        ((q / Nat.gcd q (a * s ^ 3) : ℕ) : ℝ) ^ 2 := by
      field_simp [ne_of_gt hq'posR]

/-- The rational approximation to the leading coefficient remains exact
after scaling the progression variable and reducing its denominator. -/
theorem generalCubicLeadingCoeff_affineApprox_reduced
    (theta beta : ℝ) (a q s : ℕ) (hq : 0 < q)
    (happrox : theta = rationalCenter a q + beta) :
    theta * (s : ℝ) ^ 3 =
      rationalCenter ((a * s ^ 3) / Nat.gcd q (a * s ^ 3))
        (q / Nat.gcd q (a * s ^ 3)) + beta * (s : ℝ) ^ 3 := by
  rw [generalCubicLeadingCoeff_affineApprox theta beta a q s hq happrox]
  rw [generalCubicLeadingCoeff_reducedCenter a q s hq]

/-- Multiplication by `ell` identifies congruence modulo `Q` with
congruence modulo the reduced progression step `Q / gcd Q ell`. This is the
exact cancellation needed after fixing one solution to Hua's congruence. -/
theorem mul_modEq_iff_modEq_div_gcd
    (ell Q x y : ℕ) (hQ : 0 < Q) :
    ell * x ≡ ell * y [MOD Q] ↔
      x ≡ y [MOD Q / Nat.gcd Q ell] := by
  constructor
  · intro hxy
    exact Nat.ModEq.cancel_right_div_gcd hQ (by simpa [Nat.mul_comm] using hxy)
  · intro hxy
    have hmultiple : Q ∣ ell * (Q / Nat.gcd Q ell) := by
      have hmul :=
        Nat.mul_dvd_mul_right (Nat.gcd_dvd_right Q ell) (Q / Nat.gcd Q ell)
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left Q ell)] at hmul
      exact hmul
    exact (hxy.mul_left' ell).of_dvd hmultiple

/-- Once `r` is one solution to `ell * x = t (mod Q)`, all solutions are
exactly its residue class modulo `Q / gcd(Q, ell)`. -/
theorem mul_modEq_iff_root_modEq_div_gcd
    (ell Q t r x : ℕ) (hQ : 0 < Q)
    (hr : ell * r ≡ t [MOD Q]) :
    ell * x ≡ t [MOD Q] ↔
      x ≡ r [MOD Q / Nat.gcd Q ell] := by
  constructor
  · intro hx
    apply (mul_modEq_iff_modEq_div_gcd ell Q x r hQ).mp
    exact hx.trans hr.symm
  · intro hx
    have hxr := (mul_modEq_iff_modEq_div_gcd ell Q x r hQ).mpr hx
    exact hxr.trans hr

/-- The linear congruence `ell * x = t (mod Q)` is solvable in natural
numbers exactly when the common divisor of its coefficient and modulus
divides `t`. The converse reduces by the gcd and uses a Bézout inverse for
the resulting coprime coefficient. -/
theorem exists_mul_modEq_iff_gcd_dvd
    (ell Q t : ℕ) (hQ : 0 < Q) :
    (∃ x : ℕ, ell * x ≡ t [MOD Q]) ↔ Nat.gcd Q ell ∣ t := by
  constructor
  · rintro ⟨x, hx⟩
    have hgQ : Nat.gcd Q ell ∣ Q := Nat.gcd_dvd_left Q ell
    have hge : Nat.gcd Q ell ∣ ell := Nat.gcd_dvd_right Q ell
    exact (hx.dvd_iff hgQ).mp (dvd_mul_of_dvd_left hge x)
  · intro hgt
    let g := Nat.gcd Q ell
    let a := ell / g
    let q := Q / g
    let c := t / g
    have hgQ : g ∣ Q := by exact Nat.gcd_dvd_left Q ell
    have hge : g ∣ ell := by exact Nat.gcd_dvd_right Q ell
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left ell hQ
    have hcop : Nat.Coprime a q := by
      dsimp [a, q, g]
      rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_div
        (Nat.gcd_dvd_right Q ell) (Nat.gcd_dvd_left Q ell), Nat.gcd_comm]
      exact Nat.div_self hgpos
    have hqpos : 0 < q := by
      dsimp [q, g]
      exact Nat.div_pos (Nat.le_of_dvd hQ (Nat.gcd_dvd_left Q ell)) hgpos
    obtain ⟨y, hy⟩ := Int.mod_coprime hcop
    obtain ⟨x, hxlt, hx⟩ :=
      Int.existsUnique_equiv_nat (y * (c : ℤ)) (b := (q : ℤ)) (by exact_mod_cast hqpos)
    have hprod : (a : ℤ) * (y * (c : ℤ)) ≡ (c : ℤ) [ZMOD (q : ℤ)] := by
      simpa [mul_assoc] using hy.mul_right (c : ℤ)
    have hredInt : (a : ℤ) * (x : ℤ) ≡ (c : ℤ) [ZMOD (q : ℤ)] :=
      (hx.mul_left (a : ℤ)).trans hprod
    have hred : a * x ≡ c [MOD q] := by
      exact Int.natCast_modEq_iff.mp (by simpa using hredInt)
    have hscaled : g * (a * x) ≡ g * c [MOD g * q] := hred.mul_left' g
    have hgeq : g * a = ell := by
      dsimp [a, g]
      exact Nat.mul_div_cancel' (Nat.gcd_dvd_right Q ell)
    have hQeq : g * q = Q := by
      dsimp [q, g]
      exact Nat.mul_div_cancel' (Nat.gcd_dvd_left Q ell)
    have hteq : g * c = t := by
      dsimp [c, g]
      exact Nat.mul_div_cancel' hgt
    have hleft : g * (a * x) = ell * x := by
      calc
        g * (a * x) = (g * a) * x := by ring
        _ = ell * x := by rw [hgeq]
    refine ⟨x, ?_⟩
    rw [← hleft, ← hteq, ← hQeq]
    exact hscaled

/-- Every solvable linear congruence has a canonical positive representative
in the first progression block. The zero residue is represented by the
positive endpoint `Q / gcd(Q, ell)`. -/
theorem exists_pos_mul_modEq_root_le_div_gcd_iff
    (ell Q t : ℕ) (hQ : 0 < Q) :
    (∃ r : ℕ, 0 < r ∧ r ≤ Q / Nat.gcd Q ell ∧ ell * r ≡ t [MOD Q]) ↔
      Nat.gcd Q ell ∣ t := by
  constructor
  · rintro ⟨r, hrpos, hrle, hroot⟩
    exact (exists_mul_modEq_iff_gcd_dvd ell Q t hQ).mp ⟨r, hroot⟩
  · intro hgt
    obtain ⟨x, hx⟩ := (exists_mul_modEq_iff_gcd_dvd ell Q t hQ).mpr hgt
    let step := Q / Nat.gcd Q ell
    let x₀ := x % step
    have hgpos : 0 < Nat.gcd Q ell := Nat.gcd_pos_of_pos_left ell hQ
    have hstep : 0 < step := by
      dsimp [step]
      exact Nat.div_pos (Nat.le_of_dvd hQ (Nat.gcd_dvd_left Q ell)) hgpos
    have hx₀lt : x₀ < step := by
      dsimp [x₀]
      exact Nat.mod_lt x hstep
    have hx₀root : ell * x₀ ≡ t [MOD Q] :=
      (mul_modEq_iff_root_modEq_div_gcd ell Q t x x₀ hQ hx).mpr
        (Nat.mod_modEq x step)
    let r := if x₀ = 0 then step else x₀
    have hrpos : 0 < r := by
      dsimp [r]
      split_ifs with hzero
      · exact hstep
      · exact Nat.pos_of_ne_zero hzero
    have hrle : r ≤ step := by
      dsimp [r]
      split_ifs with hzero
      · exact le_rfl
      · exact Nat.le_of_lt hx₀lt
    have hrclass : r ≡ x₀ [MOD step] := by
      by_cases hzero : x₀ = 0
      · simp [r, hzero]
      · simpa [r, hzero] using (Nat.ModEq.rfl : x₀ ≡ x₀ [MOD step])
    have hroot : ell * r ≡ t [MOD Q] :=
      (mul_modEq_iff_root_modEq_div_gcd ell Q t x₀ r hQ hx₀root).mpr hrclass
    refine ⟨r, hrpos, ?_, hroot⟩
    simpa [step] using hrle

/-- A congruent index lying to the right of a base point has a
nonnegative progression coordinate. The lower-bound premise makes the
subtraction in the divisibility characterization exact. -/
theorem nat_modEq_iff_exists_add_mul_of_le
    (r x step : ℕ) (hrx : r ≤ x) :
    r ≡ x [MOD step] ↔ ∃ y : ℕ, x = r + step * y := by
  rw [Nat.modEq_iff_dvd' hrx]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    omega
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    simp

/-- For a positive index, a positive representative no larger than one
period is the least positive member of its congruence class. -/
theorem le_of_pos_modEq_of_le_step
    (r x step : ℕ) (hrpos : 0 < r) (hrs : r ≤ step)
    (hxpos : 0 < x) (hclass : r ≡ x [MOD step]) : r ≤ x := by
  by_contra hnot
  have hxr : x < r := Nat.lt_of_not_ge hnot
  by_cases hrslt : r < step
  · have hxeq := hclass.eq_of_lt_of_lt hrslt (lt_trans hxr hrslt)
    omega
  · have hre : r = step := by omega
    subst r
    have hxzeroMod : 0 ≡ x [MOD step] := by
      calc
        0 ≡ step [MOD step] := Nat.modulus_modEq_zero.symm
        _ ≡ x [MOD step] := hclass
    have hxdiv : step ∣ x := Nat.modEq_zero_iff_dvd.mp hxzeroMod.symm
    have hxlt : x < step := by omega
    have hxzero : x = 0 := Nat.eq_zero_of_dvd_of_lt hxdiv hxlt
    omega

/-- Positive solutions of a linear congruence form exactly one arithmetic
progression, starting at its canonical positive representative. -/
theorem pos_mul_modEq_iff_exists_progression
    (ell Q t r x : ℕ) (hQ : 0 < Q) (hrpos : 0 < r)
    (hrle : r ≤ Q / Nat.gcd Q ell)
    (hroot : ell * r ≡ t [MOD Q]) :
    (0 < x ∧ ell * x ≡ t [MOD Q]) ↔
      ∃ y : ℕ, x = r + (Q / Nat.gcd Q ell) * y := by
  let step := Q / Nat.gcd Q ell
  have hgpos : 0 < Nat.gcd Q ell := Nat.gcd_pos_of_pos_left ell hQ
  have hstep : 0 < step := by
    dsimp [step]
    exact Nat.div_pos (Nat.le_of_dvd hQ (Nat.gcd_dvd_left Q ell)) hgpos
  have hrle' : r ≤ step := by simpa [step] using hrle
  constructor
  · rintro ⟨hxpos, hxroot⟩
    have hclass : x ≡ r [MOD step] :=
      (mul_modEq_iff_root_modEq_div_gcd ell Q t r x hQ hroot).mp hxroot
    have hrx := le_of_pos_modEq_of_le_step r x step hrpos hrle' hxpos hclass.symm
    simpa [step] using
      (nat_modEq_iff_exists_add_mul_of_le r x step hrx).mp hclass.symm
  · rintro ⟨y, hy⟩
    have hxpos : 0 < x := by rw [hy]; positivity
    have hrx : r ≤ x := by rw [hy]; exact Nat.le_add_right _ _
    have hclass : r ≡ x [MOD step] := by
      exact (nat_modEq_iff_exists_add_mul_of_le r x step hrx).mpr ⟨y, by simpa [step] using hy⟩
    refine ⟨hxpos, ?_⟩
    exact (mul_modEq_iff_root_modEq_div_gcd ell Q t r x hQ hroot).mpr hclass.symm

/-- Exact natural-number cutoff for the progression coordinate. This keeps
the floor/end-point convention explicit instead of silently replacing the
source's real-valued progression length by an integer. -/
theorem nat_add_mul_le_iff_le_div
    (base step y P : ℕ) (hbase : base ≤ P) (hstep : 0 < step) :
    base + step * y ≤ P ↔ y ≤ (P - base) / step := by
  constructor
  · intro h
    have hsum : step * y + base ≤ P := by
      simpa [Nat.add_comm] using h
    have hsub : step * y ≤ P - base := (Nat.le_sub_iff_add_le hbase).2 hsum
    exact (Nat.le_div_iff_mul_le hstep).2 (by simpa [Nat.mul_comm] using hsub)
  · intro h
    have hmul : y * step ≤ P - base := (Nat.le_div_iff_mul_le hstep).1 h
    have hsum : y * step + base ≤ P := (Nat.le_sub_iff_add_le hbase).1 hmul
    simpa [Nat.add_comm, Nat.mul_comm] using hsum

/-- Multiplying the progression index by `ell` converts the cutoff to the
exact quotient bound on its natural-number coordinate. -/
theorem nat_mul_progression_cutoff_iff_le_div
    (ell r step y P : ℕ) (hbase : ell * r ≤ P) (hstep : 0 < ell * step) :
    ell * (r + step * y) ≤ P ↔
      y ≤ (P - ell * r) / (ell * step) := by
  rw [Nat.mul_add, ← Nat.mul_assoc]
  exact nat_add_mul_le_iff_le_div (ell * r) (ell * step) y P hbase hstep

/-- Hua's congruence and product cutoff are equivalent to a bounded natural
progression coordinate, provided the least positive solution lies below the
cutoff. -/
theorem pos_mul_modEq_mul_le_iff_progression_cutoff
    (ell Q t r x P : ℕ) (hQ : 0 < Q) (hell : 0 < ell)
    (hrpos : 0 < r) (hrle : r ≤ Q / Nat.gcd Q ell)
    (hroot : ell * r ≡ t [MOD Q]) (hbase : ell * r ≤ P) :
    (0 < x ∧ ell * x ≤ P ∧ ell * x ≡ t [MOD Q]) ↔
      ∃ y : ℕ, x = r + (Q / Nat.gcd Q ell) * y ∧
        y ≤ (P - ell * r) / (ell * (Q / Nat.gcd Q ell)) := by
  let step := Q / Nat.gcd Q ell
  have hgpos : 0 < Nat.gcd Q ell := Nat.gcd_pos_of_pos_left ell hQ
  have hstep : 0 < step := by
    dsimp [step]
    exact Nat.div_pos (Nat.le_of_dvd hQ (Nat.gcd_dvd_left Q ell)) hgpos
  have hden : 0 < ell * step := Nat.mul_pos hell hstep
  have hrle' : r ≤ step := by simpa [step] using hrle
  constructor
  · rintro ⟨hxpos, hle, hxroot⟩
    obtain ⟨y, hy⟩ :=
      (pos_mul_modEq_iff_exists_progression ell Q t r x hQ hrpos hrle hroot).mp
        ⟨hxpos, hxroot⟩
    have hybound : y ≤ (P - ell * r) / (ell * step) := by
      apply (nat_mul_progression_cutoff_iff_le_div ell r step y P hbase hden).mp
      simpa [hy] using hle
    exact ⟨y, by simpa [step] using hy, by simpa [step] using hybound⟩
  · rintro ⟨y, hy, hybound⟩
    have hxpos : 0 < x := by rw [hy]; positivity
    have hle : ell * x ≤ P := by
      rw [hy]
      exact (nat_mul_progression_cutoff_iff_le_div ell r step y P hbase hden).mpr
        (by simpa [step] using hybound)
    have hxroot :=
      (pos_mul_modEq_iff_exists_progression ell Q t r x hQ hrpos hrle hroot).mpr
        ⟨y, hy⟩
    exact ⟨hxpos, hle, hxroot.2⟩

/-- Complete cutoff membership criterion: if the least positive solution is
already beyond `P / ell`, there are no admissible indices; otherwise the
admissible indices are exactly the bounded progression coordinates. -/
theorem pos_mul_modEq_mul_le_iff_progression_cutoff_unconditional
    (ell Q t r x P : ℕ) (hQ : 0 < Q) (hell : 0 < ell)
    (hrpos : 0 < r) (hrle : r ≤ Q / Nat.gcd Q ell)
    (hroot : ell * r ≡ t [MOD Q]) :
    (0 < x ∧ ell * x ≤ P ∧ ell * x ≡ t [MOD Q]) ↔
      (ell * r ≤ P ∧ ∃ y : ℕ,
        x = r + (Q / Nat.gcd Q ell) * y ∧
          y ≤ (P - ell * r) / (ell * (Q / Nat.gcd Q ell))) := by
  let step := Q / Nat.gcd Q ell
  have hgpos : 0 < Nat.gcd Q ell := Nat.gcd_pos_of_pos_left ell hQ
  have hstep : 0 < step := by
    dsimp [step]
    exact Nat.div_pos (Nat.le_of_dvd hQ (Nat.gcd_dvd_left Q ell)) hgpos
  have hden : 0 < ell * step := Nat.mul_pos hell hstep
  constructor
  · rintro ⟨hxpos, hle, hxroot⟩
    obtain ⟨y, hy⟩ :=
      (pos_mul_modEq_iff_exists_progression ell Q t r x hQ hrpos hrle hroot).mp
        ⟨hxpos, hxroot⟩
    have hrx : r ≤ x := by rw [hy]; exact Nat.le_add_right _ _
    have hbase : ell * r ≤ P :=
      le_trans (Nat.mul_le_mul_left ell hrx) hle
    have hybound : y ≤ (P - ell * r) / (ell * step) := by
      apply (nat_mul_progression_cutoff_iff_le_div ell r step y P hbase hden).mp
      simpa [hy] using hle
    exact ⟨hbase, ⟨y, by simpa [step] using hy, by simpa [step] using hybound⟩⟩
  · rintro ⟨hbase, ⟨y, hy, hybound⟩⟩
    exact (pos_mul_modEq_mul_le_iff_progression_cutoff
      ell Q t r x P hQ hell hrpos hrle hroot hbase).mpr ⟨y, hy, hybound⟩

/-- Indices for Hua's progression sum, using the natural endpoint convention
`1 ≤ x ≤ P / ell` and retaining the original congruence predicate. -/
def linearCongruenceProgressionIndexSet (ell Q t P : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (P / ell)).filter fun x => ell * x ≡ t [MOD Q]

/-- Reindex the finite sum over `ell*x ≤ P` in one congruence class by its
exact arithmetic progression. The right endpoint is the exact quotient for
the progression coordinate, not a rounded real bound. -/
theorem sum_linearCongruence_eq_sum_progression
    (ell Q t r P : ℕ) (hQ : 0 < Q) (hell : 0 < ell)
    (hrpos : 0 < r) (hrle : r ≤ Q / Nat.gcd Q ell)
    (hroot : ell * r ≡ t [MOD Q]) (hbase : ell * r ≤ P)
    (f : ℕ → ℂ) :
    (∑ x ∈ linearCongruenceProgressionIndexSet ell Q t P, f (ell * x)) =
      ∑ y ∈ Finset.range
          ((P - ell * r) / (ell * (Q / Nat.gcd Q ell)) + 1),
        f (ell * (r + (Q / Nat.gcd Q ell) * y)) := by
  classical
  let step := Q / Nat.gcd Q ell
  let last := (P - ell * r) / (ell * step)
  have hgpos : 0 < Nat.gcd Q ell := Nat.gcd_pos_of_pos_left ell hQ
  have hstep : 0 < step := by
    dsimp [step]
    exact Nat.div_pos (Nat.le_of_dvd hQ (Nat.gcd_dvd_left Q ell)) hgpos
  have hden : 0 < ell * step := Nat.mul_pos hell hstep
  have hrle' : r ≤ step := by simpa [step] using hrle
  change (∑ x ∈ (Finset.Icc 1 (P / ell)).filter
      (fun x => ell * x ≡ t [MOD Q]), f (ell * x)) = _
  symm
  change (∑ y ∈ Finset.range (last + 1), f (ell * (r + step * y))) = _
  refine Finset.sum_bij (fun y _ => r + step * y) ?_ ?_ ?_ ?_
  · intro y hy
    have hybound : y ≤ last := by
      have := Finset.mem_range.mp hy
      omega
    have hcut : ell * (r + step * y) ≤ P := by
      apply (nat_mul_progression_cutoff_iff_le_div ell r step y P hbase hden).mpr
      simpa [last] using hybound
    have hupper : r + step * y ≤ P / ell := by
      apply (Nat.le_div_iff_mul_le hell).2
      simpa [Nat.mul_comm] using hcut
    have hcong :=
      (pos_mul_modEq_iff_exists_progression ell Q t r (r + step * y)
        hQ hrpos hrle hroot).mpr ⟨y, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      constructor <;> omega
    · exact hcong.2
  · intro y hy z hz heq
    have hmul : step * y = step * z := Nat.add_left_cancel heq
    exact Nat.mul_left_cancel hstep hmul
  · intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxIcc, hxcong⟩
    have hxpos : 0 < x := by
      have := Finset.mem_Icc.mp hxIcc
      omega
    have hxupper : x ≤ P / ell := (Finset.mem_Icc.mp hxIcc).2
    have hxprod : x * ell ≤ P := (Nat.le_div_iff_mul_le hell).1 hxupper
    have hcut : ell * x ≤ P := by simpa [Nat.mul_comm] using hxprod
    obtain ⟨y, hxy⟩ :=
      (pos_mul_modEq_iff_exists_progression ell Q t r x hQ hrpos hrle hroot).mp
        ⟨hxpos, hxcong⟩
    have hybound : y ≤ last := by
      apply (nat_mul_progression_cutoff_iff_le_div ell r step y P hbase hden).mp
      simpa [hxy] using hcut
    refine ⟨y, Finset.mem_range.mpr ?_, ?_⟩
    · dsimp [last]
      omega
    · simpa [step] using hxy.symm
  · intro y hy
    rfl

/-- After solving the congruence and parameterizing its solutions, the
general cubic phase becomes an ordinary cubic phase with explicitly changed
coefficients. This is the phase-level adapter for Hua's Type-I progression. -/
theorem sum_linearCongruence_generalCubicPhase_eq_progression
    (a b c d : ℝ) (ell Q t r P : ℕ) (hQ : 0 < Q) (hell : 0 < ell)
    (hrpos : 0 < r) (hrle : r ≤ Q / Nat.gcd Q ell)
    (hroot : ell * r ≡ t [MOD Q]) (hbase : ell * r ≤ P) :
    (∑ x ∈ linearCongruenceProgressionIndexSet ell Q t P,
      generalCubicPhase a b c d (ell * x)) =
      ∑ y ∈ Finset.range
          ((P - ell * r) / (ell * (Q / Nat.gcd Q ell)) + 1),
        generalCubicPhase
          (a * ((ell * (Q / Nat.gcd Q ell) : ℕ) : ℝ) ^ 3)
          (3 * a * ((ell * r : ℕ) : ℝ) *
              ((ell * (Q / Nat.gcd Q ell) : ℕ) : ℝ) ^ 2 +
            b * ((ell * (Q / Nat.gcd Q ell) : ℕ) : ℝ) ^ 2)
          (3 * a * ((ell * r : ℕ) : ℝ) ^ 2 *
              ((ell * (Q / Nat.gcd Q ell) : ℕ) : ℝ) +
            2 * b * ((ell * r : ℕ) : ℝ) *
              ((ell * (Q / Nat.gcd Q ell) : ℕ) : ℝ) +
            c * ((ell * (Q / Nat.gcd Q ell) : ℕ) : ℝ))
          (a * ((ell * r : ℕ) : ℝ) ^ 3 + b * ((ell * r : ℕ) : ℝ) ^ 2 +
            c * ((ell * r : ℕ) : ℝ) + d) y := by
  rw [sum_linearCongruence_eq_sum_progression ell Q t r P hQ hell
    hrpos hrle hroot hbase (generalCubicPhase a b c d)]
  apply Finset.sum_congr rfl
  intro y hy
  have hindex :
      ell * (r + (Q / Nat.gcd Q ell) * y) =
        ell * r + (ell * (Q / Nat.gcd Q ell)) * y := by ring
  rw [hindex]
  exact generalCubicPhase_affineChange a b c d
    (ell * r) (ell * (Q / Nat.gcd Q ell)) y

/-- Hua's main application has progression modulus one. In that case the
congruence restriction disappears and the sum over multiples of `ell` is an
ordinary cubic phase sum beginning at `ell`. -/
theorem sum_multiples_generalCubicPhase_eq_progression
    (a b c d : ℝ) (ell P : ℕ) (hell : 0 < ell) (hellP : ell ≤ P) :
    (∑ x ∈ Finset.Icc 1 (P / ell),
      generalCubicPhase a b c d (ell * x)) =
      ∑ y ∈ Finset.range ((P - ell) / ell + 1),
        generalCubicPhase
          (a * (ell : ℝ) ^ 3)
          (3 * a * ell * (ell : ℝ) ^ 2 + b * (ell : ℝ) ^ 2)
          (3 * a * (ell : ℝ) ^ 2 * ell + 2 * b * ell * ell + c * ell)
          (a * (ell : ℝ) ^ 3 + b * (ell : ℝ) ^ 2 + c * ell + d) y := by
  have hset : linearCongruenceProgressionIndexSet ell 1 0 P =
      Finset.Icc 1 (P / ell) := by
    ext x
    simp [linearCongruenceProgressionIndexSet, Nat.ModEq, Nat.mod_one]
  have hsum := sum_linearCongruence_generalCubicPhase_eq_progression
    a b c d ell 1 0 1 P (by norm_num) hell (by norm_num) (by norm_num)
    (by simp [Nat.ModEq, Nat.mod_one]) (by simpa [Nat.mul_one] using hellP)
  simpa [hset, Nat.gcd_one_left] using hsum

/-- Every inner second-difference sum is a unit multiple of a linear
character sum; its length is at most `N+1`. -/
theorem norm_generalCubicSecondDifferenceInner_le_envelope
    (theta b c d : ℝ) (N h k : ℕ) (hh : h ≤ N)
    (hk : k ≤ N - h) :
    ‖∑ m ∈ Finset.range (N - h + 1 - k),
        generalCubicPhase theta b c d (m + h + k) *
          conj (generalCubicPhase theta b c d (m + k)) *
          conj (generalCubicPhase theta b c d (m + h)) *
          generalCubicPhase theta b c d m‖ ≤
      linearDistanceEnvelope (N + 1 : ℝ) (6 * theta * (h * k : ℕ)) := by
  let X := N - h + 1 - k
  let slope := 6 * theta * (h * k : ℕ)
  let c₀ := Complex.exp
    (((2 * Real.pi * (3 * theta * h * k * (h + k) + 2 * b * h * k : ℝ)) : ℂ) *
      Complex.I)
  have hc₀ : ‖c₀‖ = 1 := by
    dsimp [c₀]
    rw [show (2 * (Real.pi : ℂ) *
          ((3 * theta * h * k * (h + k) + 2 * b * h * k : ℝ) : ℂ)) * Complex.I =
        (((2 * Real.pi *
          (3 * theta * h * k * (h + k) + 2 * b * h * k : ℝ) : ℝ) : ℂ) * Complex.I) by
          push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hsum :
      (∑ m ∈ Finset.range X,
        generalCubicPhase theta b c d (m + h + k) *
          conj (generalCubicPhase theta b c d (m + k)) *
          conj (generalCubicPhase theta b c d (m + h)) *
          generalCubicPhase theta b c d m) =
      ∑ m ∈ Finset.range X, c₀ * addChar slope m := by
    apply Finset.sum_congr rfl
    intro m hm
    simpa [X, slope, c₀, mul_assoc, mul_left_comm, mul_comm] using
      generalCubicPhase_secondDifference_eq_unit_mul_addChar
        theta b c d h k m
  have hlinear := norm_unitPhase_shiftedLinearAddCharSum_le_distanceEnvelope
    slope 0 X c₀ hc₀
  have hlinear' :
      ‖∑ m ∈ Finset.range X, c₀ * addChar slope m‖ ≤
        linearDistanceEnvelope (X : ℝ) slope := by
    simpa [linearDistanceEnvelope,
      CookMagyarArcs.periodicDistance_eq_abs_sub_round] using hlinear
  have hXle : X ≤ N + 1 := by dsimp [X]; omega
  have hmono := linearDistanceEnvelope_mono
    (Y₁ := (X : ℝ)) (Y₂ := (N + 1 : ℝ)) (theta := slope)
    (by exact_mod_cast hXle)
  have hfreq : slope = 6 * theta * (h * k : ℕ) := rfl
  calc
    _ = ‖∑ m ∈ Finset.range X, c₀ * addChar slope m‖ := by
      simpa [X] using congrArg (fun z : ℂ => ‖z‖) hsum
    _ ≤ linearDistanceEnvelope (X : ℝ) slope := hlinear'
    _ ≤ linearDistanceEnvelope (N + 1 : ℝ) slope := hmono
    _ = linearDistanceEnvelope (N + 1 : ℝ) (6 * theta * (h * k : ℕ)) := by
      rw [hfreq]

/-- The cubic second-difference norm is bounded by its positive product-pair
envelope. The one-term padding in both the range and envelope height is
intentional: it lets the Hua progression adapter retain the exact quotient
endpoint without a separate off-by-one case. -/
theorem norm_generalCubicSecondDifferenceSum_le_paddedPairEnvelope
    (theta b c d : ℝ) (N : ℕ) :
    ‖unitSequenceSecondDifferenceSum (generalCubicPhase theta b c d) N‖ ≤
      ∑ hk ∈ (Finset.Icc 1 (N + 1)).product (Finset.Icc 1 (N + 1)),
        linearDistanceEnvelope (N + 2 : ℝ)
          (6 * theta * (hk.1 * hk.2 : ℕ)) := by
  let u := generalCubicPhase theta b c d
  have hdecomp :
      unitSequenceSecondDifferenceSum u N =
        ∑ h ∈ Finset.Icc 1 N,
          ∑ k ∈ Finset.Icc 1 (N - h),
            ∑ m ∈ Finset.range (N - h + 1 - k),
              u (m + h + k) * conj (u (m + k)) *
                conj (u (m + h)) * u m := by
    unfold unitSequenceSecondDifferenceSum
    apply Finset.sum_congr rfl
    intro h hh
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      sum_positiveCubicShiftPairs_eq_sum_by_shift (N - h)
        (fun k m => u (m + h + k) * conj (u (m + k)) *
          conj (u (m + h)) * u m)
  have hsub :
      (Finset.Icc 1 N).product (Finset.Icc 1 N) ⊆
        (Finset.Icc 1 (N + 1)).product (Finset.Icc 1 (N + 1)) :=
    Finset.product_subset_product
      (Finset.Icc_subset_Icc_right (by omega))
      (Finset.Icc_subset_Icc_right (by omega))
  rw [hdecomp]
  calc
    _ ≤ ∑ h ∈ Finset.Icc 1 N,
        ‖∑ k ∈ Finset.Icc 1 (N - h),
          ∑ m ∈ Finset.range (N - h + 1 - k),
            u (m + h + k) * conj (u (m + k)) *
              conj (u (m + h)) * u m‖ := norm_sum_le _ _
    _ ≤ ∑ h ∈ Finset.Icc 1 N,
        ∑ k ∈ Finset.Icc 1 (N - h),
          ‖∑ m ∈ Finset.range (N - h + 1 - k),
            u (m + h + k) * conj (u (m + k)) *
              conj (u (m + h)) * u m‖ := by
      apply Finset.sum_le_sum
      intro h hh
      exact norm_sum_le _ _
    _ ≤ ∑ h ∈ Finset.Icc 1 N,
        ∑ k ∈ Finset.Icc 1 (N - h),
          linearDistanceEnvelope (N + 1 : ℝ) (6 * theta * (h * k : ℕ)) := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum
      intro k hk
      exact norm_generalCubicSecondDifferenceInner_le_envelope
        theta b c d N h k (Finset.mem_Icc.mp hh).2 (Finset.mem_Icc.mp hk).2
    _ ≤ ∑ h ∈ Finset.Icc 1 N,
        ∑ k ∈ Finset.Icc 1 N,
          linearDistanceEnvelope (N + 1 : ℝ) (6 * theta * (h * k : ℕ)) := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_right (by omega))
      intro k hk hnot
      exact linearDistanceEnvelope_nonneg (by positivity)
    _ = ∑ hk ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
          linearDistanceEnvelope (N + 1 : ℝ)
            (6 * theta * (hk.1 * hk.2 : ℕ)) := by
      symm
      exact Finset.sum_product (Finset.Icc 1 N) (Finset.Icc 1 N)
        (fun hk => linearDistanceEnvelope (N + 1 : ℝ)
          (6 * theta * (hk.1 * hk.2 : ℕ)))
    _ ≤ ∑ hk ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
          linearDistanceEnvelope (N + 2 : ℝ)
            (6 * theta * (hk.1 * hk.2 : ℕ)) := by
      apply Finset.sum_le_sum
      intro hk hhk
      exact linearDistanceEnvelope_mono (by exact_mod_cast (by omega))
    _ ≤ ∑ hk ∈ (Finset.Icc 1 (N + 1)).product (Finset.Icc 1 (N + 1)),
          linearDistanceEnvelope (N + 2 : ℝ)
            (6 * theta * (hk.1 * hk.2 : ℕ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro hk hhk hnot
        exact linearDistanceEnvelope_nonneg (by positivity))

/-- Hua's leading-coefficient uniformity is visible at the second-difference
level: arbitrary lower coefficients do not affect the spacing envelope. -/
theorem exists_uniform_norm_generalCubicSecondDifferenceSum_le_spacing
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (theta b c d : ℝ) (N a q : ℕ) (beta : ℝ),
      0 < q → Nat.Coprime a q → theta = rationalCenter a q + beta →
      |beta| ≤ 1 / (q : ℝ) ^ 2 →
      ‖unitSequenceSecondDifferenceSum
        (generalCubicPhase theta b c d) N‖ ≤
        C * Real.rpow ((N * N : ℕ) : ℝ) ε *
          sixMulSpacingEnvelopeBound N q (N + 1 : ℝ) := by
  obtain ⟨C, hC, hpair⟩ :=
    exists_uniform_sum_positiveProductPairs_sixMul_envelope_le hε
  refine ⟨C, hC, fun theta b c d N a q beta hq hac halpha hbeta => ?_⟩
  have hpair' := hpair N a q theta beta (N + 1 : ℝ)
    hq hac halpha hbeta (by positivity)
  let u := generalCubicPhase theta b c d
  have hdecomp :
      unitSequenceSecondDifferenceSum u N =
        ∑ h ∈ Finset.Icc 1 N,
          ∑ k ∈ Finset.Icc 1 (N - h),
            ∑ m ∈ Finset.range (N - h + 1 - k),
              u (m + h + k) * conj (u (m + k)) *
                conj (u (m + h)) * u m := by
    unfold unitSequenceSecondDifferenceSum
    apply Finset.sum_congr rfl
    intro h hh
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      sum_positiveCubicShiftPairs_eq_sum_by_shift (N - h)
        (fun k m => u (m + h + k) * conj (u (m + k)) *
          conj (u (m + h)) * u m)
  rw [hdecomp]
  calc
    _ ≤ ∑ h ∈ Finset.Icc 1 N,
        ‖∑ k ∈ Finset.Icc 1 (N - h),
          ∑ m ∈ Finset.range (N - h + 1 - k),
            u (m + h + k) * conj (u (m + k)) *
              conj (u (m + h)) * u m‖ := norm_sum_le _ _
    _ ≤ ∑ h ∈ Finset.Icc 1 N,
        ∑ k ∈ Finset.Icc 1 (N - h),
          ‖∑ m ∈ Finset.range (N - h + 1 - k),
            u (m + h + k) * conj (u (m + k)) *
              conj (u (m + h)) * u m‖ := by
      apply Finset.sum_le_sum
      intro h hh
      exact norm_sum_le _ _
    _ ≤ ∑ h ∈ Finset.Icc 1 N,
        ∑ k ∈ Finset.Icc 1 (N - h),
          linearDistanceEnvelope (N + 1 : ℝ) (6 * theta * (h * k : ℕ)) := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum
      intro k hk
      exact norm_generalCubicSecondDifferenceInner_le_envelope
        theta b c d N h k ((Finset.mem_Icc.mp hh).2)
          ((Finset.mem_Icc.mp hk).2)
    _ ≤ ∑ h ∈ Finset.Icc 1 N,
        ∑ k ∈ Finset.Icc 1 N,
          linearDistanceEnvelope (N + 1 : ℝ) (6 * theta * (h * k : ℕ)) := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_right (by omega))
      intro k hk hnot
      exact linearDistanceEnvelope_nonneg (by positivity)
    _ = ∑ hk ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
          linearDistanceEnvelope (N + 1 : ℝ)
            (6 * theta * (hk.1 * hk.2 : ℕ)) := by
      symm
      exact Finset.sum_product (Finset.Icc 1 N) (Finset.Icc 1 N)
        (fun hk => linearDistanceEnvelope (N + 1 : ℝ)
          (6 * theta * (hk.1 * hk.2 : ℕ)))
    _ ≤ C * Real.rpow ((N * N : ℕ) : ℝ) ε *
        sixMulSpacingEnvelopeBound N q (N + 1 : ℝ) := hpair'

/-- Thresholded divisor-moment version of the cubic second-difference bound.
It retains the arbitrary lower coefficients and replaces the pointwise
subpower divisor loss by the explicit small-count/rich-tail tradeoff. -/
theorem norm_generalCubicSecondDifferenceSum_le_divisorThreshold
    (theta b c d : ℝ) (N a q : ℕ) (beta T : ℝ)
    (hq : 0 < q) (hac : Nat.Coprime a q)
    (halpha : theta = rationalCenter a q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hT : 0 < T) :
    ‖unitSequenceSecondDifferenceSum (generalCubicPhase theta b c d) N‖ ≤
      T * sixMulSpacingEnvelopeBound N q (N + 1 : ℝ) +
        (N + 1 : ℝ) * (((N * N : ℕ) : ℝ) *
          (1 + Real.log ((N * N : ℕ) : ℝ)) ^ 7) / T ^ 2 := by
  let u := generalCubicPhase theta b c d
  have hdecomp :
      unitSequenceSecondDifferenceSum u N =
        ∑ h ∈ Finset.Icc 1 N,
          ∑ k ∈ Finset.Icc 1 (N - h),
            ∑ m ∈ Finset.range (N - h + 1 - k),
              u (m + h + k) * conj (u (m + k)) *
                conj (u (m + h)) * u m := by
    unfold unitSequenceSecondDifferenceSum
    apply Finset.sum_congr rfl
    intro h hh
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      sum_positiveCubicShiftPairs_eq_sum_by_shift (N - h)
        (fun k m => u (m + h + k) * conj (u (m + k)) *
          conj (u (m + h)) * u m)
  rw [hdecomp]
  calc
    _ ≤ ∑ h ∈ Finset.Icc 1 N,
        ‖∑ k ∈ Finset.Icc 1 (N - h),
          ∑ m ∈ Finset.range (N - h + 1 - k),
            u (m + h + k) * conj (u (m + k)) *
              conj (u (m + h)) * u m‖ := norm_sum_le _ _
    _ ≤ ∑ h ∈ Finset.Icc 1 N,
        ∑ k ∈ Finset.Icc 1 (N - h),
          ‖∑ m ∈ Finset.range (N - h + 1 - k),
            u (m + h + k) * conj (u (m + k)) *
              conj (u (m + h)) * u m‖ := by
      apply Finset.sum_le_sum
      intro h hh
      exact norm_sum_le _ _
    _ ≤ ∑ h ∈ Finset.Icc 1 N,
        ∑ k ∈ Finset.Icc 1 (N - h),
          linearDistanceEnvelope (N + 1 : ℝ) (6 * theta * (h * k : ℕ)) := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum
      intro k hk
      exact norm_generalCubicSecondDifferenceInner_le_envelope
        theta b c d N h k ((Finset.mem_Icc.mp hh).2)
          ((Finset.mem_Icc.mp hk).2)
    _ ≤ ∑ h ∈ Finset.Icc 1 N,
        ∑ k ∈ Finset.Icc 1 N,
          linearDistanceEnvelope (N + 1 : ℝ) (6 * theta * (h * k : ℕ)) := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_right (by omega))
      intro k hk hnot
      exact linearDistanceEnvelope_nonneg (by positivity)
    _ = ∑ hk ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
          linearDistanceEnvelope (N + 1 : ℝ)
            (6 * theta * (hk.1 * hk.2 : ℕ)) := by
      symm
      exact Finset.sum_product (Finset.Icc 1 N) (Finset.Icc 1 N)
        (fun hk => linearDistanceEnvelope (N + 1 : ℝ)
          (6 * theta * (hk.1 * hk.2 : ℕ)))
    _ ≤ T * sixMulSpacingEnvelopeBound N q (N + 1 : ℝ) +
          (N + 1 : ℝ) * (((N * N : ℕ) : ℝ) *
            (1 + Real.log ((N * N : ℕ) : ℝ)) ^ 7) / T ^ 2 := by
      exact sum_positiveProductPairs_sixMul_envelope_le_divisorThreshold
        N a q theta beta (N + 1 : ℝ) T hq hac halpha hbeta
        (by positivity) hT

/-- Squaring one fixed-shift autocorrelation gives its diagonal plus its
positive second differences. -/
theorem unitSequenceFixedShift_norm_sq_eq
    (u : ℕ → ℂ) (N h : ℕ) (hh : h ≤ N)
    (hunit : ∀ m, ‖u m‖ = 1) :
    ‖unitSequenceFixedShiftSum u N h‖ ^ 2 =
      ((N + 1 - h : ℕ) : ℝ) +
        2 * (∑ km ∈ positiveCubicShiftPairs (N - h),
          u (km.2 + km.1 + h) * conj (u (km.2 + km.1)) *
            conj (u (km.2 + h)) * u km.2).re := by
  let v : ℕ → ℂ := fun m => u (m + h) * conj (u m)
  have hlen : N + 1 - h = (N - h) + 1 := by omega
  have hdiag (m : ℕ) : ‖v m‖ ^ 2 = (1 : ℝ) := by
    dsimp [v]
    simp [hunit]
  have hpairs :
      (∑ i ∈ Finset.range ((N - h) + 1),
        ∑ j ∈ Finset.range i, v i * conj (v j)) =
      ∑ km ∈ positiveCubicShiftPairs (N - h),
        v (km.2 + km.1) * conj (v km.2) := by
    rw [sum_triangle_eq_strictCubicIndexPairs]
    exact sum_strictCubicIndexPairs_eq_positiveShiftPairs (N - h)
      (fun i j => v i * conj (v j))
  have hpairs' :
      (∑ km ∈ positiveCubicShiftPairs (N - h),
        v (km.2 + km.1) * conj (v km.2)) =
      ∑ km ∈ positiveCubicShiftPairs (N - h),
        u (km.2 + km.1 + h) * conj (u (km.2 + km.1)) *
          conj (u (km.2 + h)) * u km.2 := by
    apply Finset.sum_congr rfl
    intro km hkm
    simp [v]
    ring
  have hnorm := norm_sum_range_sq_eq_diagonal_add_pairs v ((N - h) + 1)
  simp_rw [hdiag] at hnorm
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hnorm
  rw [hpairs, hpairs'] at hnorm
  simpa [unitSequenceFixedShiftSum, v, hlen] using hnorm

/-- The first differencing identity for a unit-modulus sequence. -/
theorem norm_unitSequence_sum_sq_eq_firstDifferenceSum
    (u : ℕ → ℂ) (N : ℕ) (hunit : ∀ m, ‖u m‖ = 1) :
    ‖∑ m ∈ Finset.range (N + 1), u m‖ ^ 2 =
      (N + 1 : ℝ) + 2 * (unitSequenceFirstDifferenceSum u N).re := by
  have hpairs :
      (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range i,
        u i * conj (u j)) = unitSequenceFirstDifferenceSum u N := by
    rw [sum_triangle_eq_strictCubicIndexPairs]
    exact sum_strictCubicIndexPairs_eq_positiveShiftPairs N
      (fun i j => u i * conj (u j))
  have hnorm := norm_sum_range_sq_eq_diagonal_add_pairs u (N + 1)
  simp_rw [hunit] at hnorm
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hnorm
  rw [hpairs] at hnorm
  norm_num at hnorm
  simpa only [unitSequenceFirstDifferenceSum] using hnorm

/-- Exact second-shift identity for an arbitrary unit-modulus sequence. -/
theorem sum_unitSequenceFixedShift_norm_sq_eq_secondDifferenceSum
    (u : ℕ → ℂ) (N : ℕ) (hunit : ∀ m, ‖u m‖ = 1) :
    (∑ h ∈ Finset.Icc 1 N, ‖unitSequenceFixedShiftSum u N h‖ ^ 2) =
      (N : ℝ) * (N + 1) / 2 +
        2 * (unitSequenceSecondDifferenceSum u N).re := by
  have hsum :
      (∑ h ∈ Finset.Icc 1 N, ‖unitSequenceFixedShiftSum u N h‖ ^ 2) =
        ∑ h ∈ Finset.Icc 1 N,
          (((N + 1 - h : ℕ) : ℝ) +
            2 * (∑ km ∈ positiveCubicShiftPairs (N - h),
              u (km.2 + km.1 + h) * conj (u (km.2 + km.1)) *
                conj (u (km.2 + h)) * u km.2).re) := by
    apply Finset.sum_congr rfl
    intro h hh
    exact unitSequenceFixedShift_norm_sq_eq u N h
      ((Finset.mem_Icc.mp hh).2) hunit
  rw [hsum, Finset.sum_add_distrib, cubicShiftDiagonalSum]
  simp only [unitSequenceSecondDifferenceSum, Complex.re_sum]
  rw [← Finset.mul_sum]

/-- Van der Corput's fourth-power inequality for any unit-modulus finite
sequence, with its exact positive second-difference sum. -/
theorem norm_unitSequence_sum_four_le_secondDifference
    (u : ℕ → ℂ) (N : ℕ) (hunit : ∀ m, ‖u m‖ = 1) :
    ‖∑ m ∈ Finset.range (N + 1), u m‖ ^ 4 ≤
      6 * (N + 1 : ℝ) ^ 3 +
        16 * (N + 1 : ℝ) * ‖unitSequenceSecondDifferenceSum u N‖ := by
  let S : ℂ := ∑ h ∈ Finset.Icc 1 N, unitSequenceFixedShiftSum u N h
  let D : ℂ := unitSequenceSecondDifferenceSum u N
  let X : ℝ := N + 1
  have hshift : unitSequenceFirstDifferenceSum u N = S := by
    unfold unitSequenceFirstDifferenceSum S unitSequenceFixedShiftSum
    exact sum_positiveCubicShiftPairs_eq_sum_by_shift N
      (fun h m => u (m + h) * conj (u m))
  have hfirst : ‖∑ m ∈ Finset.range (N + 1), u m‖ ^ 2 = X + 2 * S.re := by
    rw [norm_unitSequence_sum_sq_eq_firstDifferenceSum u N hunit, hshift]
  have hre2 : S.re ^ 2 ≤ ‖S‖ ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg S.re) (norm_nonneg S)).2
      (Complex.abs_re_le_norm S)
    simpa only [sq_abs] using h
  have hfour : ‖∑ m ∈ Finset.range (N + 1), u m‖ ^ 4 ≤
      2 * X ^ 2 + 8 * ‖S‖ ^ 2 := by
    calc
      _ = (X + 2 * S.re) ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hfirst]
      _ ≤ 2 * X ^ 2 + 8 * S.re ^ 2 := by
        nlinarith [sq_nonneg (X - 2 * S.re)]
      _ ≤ 2 * X ^ 2 + 8 * ‖S‖ ^ 2 := by gcongr
  have hcs : ‖S‖ ^ 2 ≤ (N : ℝ) *
      ∑ h ∈ Finset.Icc 1 N, ‖unitSequenceFixedShiftSum u N h‖ ^ 2 := by
    have hnorm : ‖S‖ ≤
        ∑ h ∈ Finset.Icc 1 N, ‖unitSequenceFixedShiftSum u N h‖ := by
      exact norm_sum_le _ _
    have hcs' := sq_sum_le_card_mul_sum_sq
      (s := Finset.Icc 1 N)
      (f := fun h => ‖unitSequenceFixedShiftSum u N h‖)
    dsimp [S]
    calc
      _ ≤ (∑ h ∈ Finset.Icc 1 N,
          ‖unitSequenceFixedShiftSum u N h‖) ^ 2 := by gcongr
      _ ≤ ((Finset.Icc 1 N).card : ℝ) *
          ∑ h ∈ Finset.Icc 1 N, ‖unitSequenceFixedShiftSum u N h‖ ^ 2 := hcs'
      _ = _ := by simp [Nat.card_Icc]
  have hsecond := sum_unitSequenceFixedShift_norm_sq_eq_secondDifferenceSum
    u N hunit
  have hre : D.re ≤ ‖D‖ := Complex.re_le_norm D
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hX : 1 ≤ X := by dsimp [X]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  have hnX : (N : ℝ) ≤ X := by dsimp [X]; linarith
  have hpower : (N : ℝ) ^ 2 * X ≤ X ^ 3 := by
    have hsq : (N : ℝ) ^ 2 ≤ X ^ 2 := by gcongr
    calc
      (N : ℝ) ^ 2 * X ≤ X ^ 2 * X := by gcongr
      _ = X ^ 3 := by ring
  have hXpower : X ^ 2 ≤ X ^ 3 := by
    calc
      X ^ 2 = X ^ 2 * 1 := by ring
      _ ≤ X ^ 2 * X := by gcongr
      _ = X ^ 3 := by ring
  calc
    _ ≤ 2 * X ^ 2 + 8 * ‖S‖ ^ 2 := hfour
    _ ≤ 2 * X ^ 2 + 8 * (N : ℝ) *
        (∑ h ∈ Finset.Icc 1 N,
          ‖unitSequenceFixedShiftSum u N h‖ ^ 2) := by nlinarith [hcs]
    _ = 2 * X ^ 2 + 8 * (N : ℝ) *
        ((N : ℝ) * (N + 1) / 2 + 2 * D.re) := by
          rw [hsecond]
    _ ≤ 2 * X ^ 2 + 8 * (N : ℝ) *
        ((N : ℝ) * (N + 1) / 2 + 2 * ‖D‖) := by gcongr
    _ ≤ 6 * X ^ 3 + 16 * X * ‖D‖ := by
      nlinarith [hpower, hXpower, mul_nonneg (sub_nonneg.mpr hnX) (norm_nonneg D)]
    _ = _ := rfl

/-- The generic sequence inequality specializes to cubic polynomials with
arbitrary real lower coefficients. -/
theorem norm_generalCubicExpSum_four_le_secondDifference
    (a b c d : ℝ) (N : ℕ) :
    ‖generalCubicExpSum a b c d N‖ ^ 4 ≤
      6 * (N + 1 : ℝ) ^ 3 +
        16 * (N + 1 : ℝ) *
          ‖unitSequenceSecondDifferenceSum (generalCubicPhase a b c d) N‖ := by
  simpa [generalCubicExpSum] using
    norm_unitSequence_sum_four_le_secondDifference
      (generalCubicPhase a b c d) N (by intro m; simp)

/-- Turn any padded positive product-pair envelope bound into a fourth-power
bound for the corresponding cubic Weyl sum. This is the direct interface from
the source-range spacing theorem to a progression-restricted Weyl estimate. -/
theorem norm_generalCubicExpSum_four_le_of_paddedPairEnvelope
    (theta b c d : ℝ) (N : ℕ) (S : ℝ)
    (hpair :
      (∑ hk ∈ (Finset.Icc 1 (N + 1)).product (Finset.Icc 1 (N + 1)),
        linearDistanceEnvelope (N + 2 : ℝ)
          (6 * theta * (hk.1 * hk.2 : ℕ))) ≤ S) :
    ‖generalCubicExpSum theta b c d N‖ ^ 4 ≤
      6 * (N + 1 : ℝ) ^ 3 + 16 * (N + 1 : ℝ) * S := by
  have hsecond := norm_generalCubicSecondDifferenceSum_le_paddedPairEnvelope
    theta b c d N
  have hsecond' := hsecond.trans hpair
  have hcoef : 0 ≤ (16 : ℝ) * ((N : ℝ) + 1) := by positivity
  calc
    ‖generalCubicExpSum theta b c d N‖ ^ 4 ≤
        6 * (N + 1 : ℝ) ^ 3 + 16 * (N + 1 : ℝ) *
          ‖unitSequenceSecondDifferenceSum (generalCubicPhase theta b c d) N‖ :=
      norm_generalCubicExpSum_four_le_secondDifference theta b c d N
    _ ≤ 6 * (N + 1 : ℝ) ^ 3 + 16 * (N + 1 : ℝ) * S := by
      have hmul := mul_le_mul_of_nonneg_left hsecond' hcoef
      nlinarith

/-- Turn a pair-envelope saving for a prefix of length `N` into a linear-norm
bound normalized by a larger ambient length `M`. The length hypothesis lets
the trivial differencing diagonal be absorbed even for short prefixes. -/
theorem norm_generalCubicExpSum_le_of_paddedPairEnvelope_logSaving
    (theta b c d : ℝ) (N M B saving : ℕ)
    (hB : 3 ≤ B) (hNM : N ≤ M)
    (hLength : B ^ (4 * saving) ≤ M + 2)
    (hpair :
      (∑ hk ∈ (Finset.Icc 1 (N + 1)).product (Finset.Icc 1 (N + 1)),
        linearDistanceEnvelope (N + 2 : ℝ)
          (6 * theta * (hk.1 * hk.2 : ℕ))) ≤
        79301 * (N + 2 : ℝ) ^ 3 / (B : ℝ) ^ (4 * saving)) :
    ‖generalCubicExpSum theta b c d N‖ ≤
      1268822 * (M + 2 : ℝ) / (B : ℝ) ^ saving := by
  have hBpos : 0 < B := by omega
  have hdenpos : (0 : ℝ) < (B : ℝ) ^ (4 * saving) := by positivity
  have hLengthReal : (B : ℝ) ^ (4 * saving) ≤ (M + 2 : ℝ) := by
    exact_mod_cast hLength
  have hNle : (N + 2 : ℝ) ≤ (M + 2 : ℝ) := by
    exact_mod_cast Nat.add_le_add_right hNM 2
  have hN1le : (N + 1 : ℝ) ≤ (M + 2 : ℝ) := by
    exact_mod_cast (Nat.add_le_add_right hNM 1).trans (Nat.le_succ (M + 1))
  have hfour := norm_generalCubicExpSum_four_le_of_paddedPairEnvelope
    theta b c d N (79301 * (N + 2 : ℝ) ^ 3 / (B : ℝ) ^ (4 * saving)) hpair
  have hfirst :
      6 * (N + 1 : ℝ) ^ 3 ≤
        6 * (M + 2 : ℝ) ^ 4 / (B : ℝ) ^ (4 * saving) := by
    apply (le_div_iff₀ hdenpos).2
    calc
      6 * (N + 1 : ℝ) ^ 3 * (B : ℝ) ^ (4 * saving) ≤
          6 * (N + 1 : ℝ) ^ 3 * (M + 2 : ℝ) := by gcongr
      _ ≤ 6 * (M + 2 : ℝ) ^ 4 := by
        calc
          6 * (N + 1 : ℝ) ^ 3 * (M + 2 : ℝ) ≤
              6 * (M + 2 : ℝ) ^ 3 * (M + 2 : ℝ) := by gcongr
          _ = 6 * (M + 2 : ℝ) ^ 4 := by ring
  have hnumSecond :
      16 * (N + 1 : ℝ) * 79301 * (N + 2 : ℝ) ^ 3 ≤
        (16 * 79301 : ℝ) * (M + 2 : ℝ) ^ 4 := by
    calc
      16 * (N + 1 : ℝ) * 79301 * (N + 2 : ℝ) ^ 3 ≤
          16 * (M + 2 : ℝ) * 79301 * (M + 2 : ℝ) ^ 3 := by gcongr
      _ = (16 * 79301 : ℝ) * (M + 2 : ℝ) ^ 4 := by ring
  have hsecond :
      16 * (N + 1 : ℝ) *
          (79301 * (N + 2 : ℝ) ^ 3 / (B : ℝ) ^ (4 * saving)) ≤
        (16 * 79301 : ℝ) * (M + 2 : ℝ) ^ 4 /
          (B : ℝ) ^ (4 * saving) := by
    calc
      _ = (16 * (N + 1 : ℝ) * 79301 * (N + 2 : ℝ) ^ 3) /
          (B : ℝ) ^ (4 * saving) := by ring
      _ ≤ (16 * 79301 : ℝ) * (M + 2 : ℝ) ^ 4 /
          (B : ℝ) ^ (4 * saving) :=
        div_le_div_of_nonneg_right hnumSecond hdenpos.le
  have hbound :
      ‖generalCubicExpSum theta b c d N‖ ^ 4 ≤
        (1268822 : ℝ) * (M + 2 : ℝ) ^ 4 /
          (B : ℝ) ^ (4 * saving) := by
    calc
      _ ≤ 6 * (N + 1 : ℝ) ^ 3 +
          16 * (N + 1 : ℝ) *
            (79301 * (N + 2 : ℝ) ^ 3 / (B : ℝ) ^ (4 * saving)) := hfour
      _ ≤ 6 * (M + 2 : ℝ) ^ 4 / (B : ℝ) ^ (4 * saving) +
          (16 * 79301 : ℝ) * (M + 2 : ℝ) ^ 4 /
            (B : ℝ) ^ (4 * saving) := add_le_add hfirst hsecond
      _ = (1268822 : ℝ) * (M + 2 : ℝ) ^ 4 /
            (B : ℝ) ^ (4 * saving) := by ring
  have hscalePow : (B : ℝ) ^ (4 * saving) = ((B : ℝ) ^ saving) ^ 4 := by
    rw [show 4 * saving = saving * 4 by omega, ← pow_mul]
  have hquotientPow :
      ((M + 2 : ℝ) / (B : ℝ) ^ saving) ^ 4 =
        (M + 2 : ℝ) ^ 4 / (B : ℝ) ^ (4 * saving) := by
    rw [div_pow, hscalePow]
  have htarget :
      ‖generalCubicExpSum theta b c d N‖ ^ 4 ≤
        (1268822 * ((M + 2 : ℝ) / (B : ℝ) ^ saving)) ^ 4 := by
    calc
      _ ≤ (1268822 : ℝ) * (M + 2 : ℝ) ^ 4 /
          (B : ℝ) ^ (4 * saving) := hbound
      _ = (1268822 : ℝ) *
          ((M + 2 : ℝ) ^ 4 / (B : ℝ) ^ (4 * saving)) := by ring
      _ ≤ (1268822 : ℝ) ^ 4 *
          ((M + 2 : ℝ) ^ 4 / (B : ℝ) ^ (4 * saving)) := by
        exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = (1268822 * ((M + 2 : ℝ) / (B : ℝ) ^ saving)) ^ 4 := by
        rw [mul_pow, hquotientPow]
  have hrootNonneg :
      0 ≤ 1268822 * ((M + 2 : ℝ) / (B : ℝ) ^ saving) := by positivity
  have hroot := le_of_pow_le_pow_left₀ (by norm_num : 4 ≠ 0)
    hrootNonneg htarget
  calc
    _ ≤ 1268822 * ((M + 2 : ℝ) / (B : ℝ) ^ saving) := hroot
    _ = 1268822 * (M + 2 : ℝ) / (B : ℝ) ^ saving := by ring

/-- Hua's source ranges imply a logarithmically saving fourth-power Weyl bound
on the exact congruence progression, uniformly in all lower coefficients.
The smooth minor-arc beta twist is intentionally not included; it is handled
separately by Abel summation. -/
theorem eventually_hua_cubic_progression_weyl_fourth_power_bound
    (a : ℕ) (b c d : ℝ) (cQ : ℝ) (hcQ : 0 ≤ cQ)
    (sigma sigma0 sigma3 sigma4 : ℕ)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma)
    (hcutoff : 3 * (sigma3 + sigma4 + 2) + 5 ≤ sigma0) :
    ∀ᶠ P : ℕ in atTop,
      ∀ ell Q q r : ℕ,
        0 < Q → 0 < ell → 0 < r →
        r ≤ Q / Nat.gcd Q ell → ell * r ≤ P → Nat.Coprime a q →
        (ell : ℝ) ≤ Real.log ((P : ℝ) + 2) ^ sigma3 →
        (Q : ℝ) ≤ cQ * Real.log ((P : ℝ) + 2) ^ sigma4 →
        Real.log ((P : ℝ) + 2) ^ sigma < (q : ℝ) →
        (q : ℝ) ≤ (P : ℝ) ^ 3 / Real.log ((P : ℝ) + 2) ^ sigma →
        let B := Nat.floor (Real.log ((P : ℝ) + 2))
        let step := ell * (Q / Nat.gcd Q ell)
        let M := (P - ell * r) / step
        let q' := q / Nat.gcd q (a * step ^ 3)
        let anum := (a * step ^ 3) / Nat.gcd q (a * step ^ 3)
        ‖generalCubicExpSum (rationalCenter anum q') b c d M‖ ^ 4 ≤
          6 * (M + 1 : ℝ) ^ 3 +
            16 * (M + 1 : ℝ) * (79301 * (M + 2 : ℝ) ^ 3 / (B : ℝ)) := by
  filter_upwards
    [eventually_hua_cubic_progression_pair_envelope a cQ hcQ
      sigma sigma0 sigma3 sigma4 hbudget hcutoff] with P hpair
  intro ell Q q r hQpos hellpos hrpos hrle hbase hac hell hQ hqLower hqUpper
  let B := Nat.floor (Real.log ((P : ℝ) + 2))
  let step := ell * (Q / Nat.gcd Q ell)
  let M := (P - ell * r) / step
  let q' := q / Nat.gcd q (a * step ^ 3)
  let anum := (a * step ^ 3) / Nat.gcd q (a * step ^ 3)
  have hpair' := hpair ell Q q r hQpos hellpos hrpos hrle hbase hac
    hell hQ hqLower hqUpper
  exact norm_generalCubicExpSum_four_le_of_paddedPairEnvelope
    (rationalCenter anum q') b c d M
    (79301 * (M + 2 : ℝ) ^ 3 / (B : ℝ))
    (by simpa [B, step, M, q', anum] using hpair')

/-- Any fixed logarithmic saving power for the unweighted progression Weyl
sum, provided Hua's source cutoff and transformed progression windows have
the corresponding exponent margins. This is still a per-sum estimate; it
does not perform Vaughan coefficient summation or the beta Abel transfer. -/
theorem eventually_hua_cubic_progression_weyl_fourth_power_bound_order
    (a : ℕ) (b c d : ℝ) (cQ : ℝ) (hcQ : 0 ≤ cQ)
    (sigma sigma0 sigma3 sigma4 delta : ℕ)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma)
    (hdelta : 1 ≤ delta)
    (hcutoff : 3 * (sigma3 + sigma4 + 2) + 5 * delta ≤ sigma0) :
    ∀ᶠ P : ℕ in atTop,
      ∀ ell Q q r : ℕ,
        0 < Q → 0 < ell → 0 < r →
        r ≤ Q / Nat.gcd Q ell → ell * r ≤ P → Nat.Coprime a q →
        (ell : ℝ) ≤ Real.log ((P : ℝ) + 2) ^ sigma3 →
        (Q : ℝ) ≤ cQ * Real.log ((P : ℝ) + 2) ^ sigma4 →
        Real.log ((P : ℝ) + 2) ^ sigma < (q : ℝ) →
        (q : ℝ) ≤ (P : ℝ) ^ 3 / Real.log ((P : ℝ) + 2) ^ sigma →
        let B := Nat.floor (Real.log ((P : ℝ) + 2))
        let step := ell * (Q / Nat.gcd Q ell)
        let M := (P - ell * r) / step
        let q' := q / Nat.gcd q (a * step ^ 3)
        let anum := (a * step ^ 3) / Nat.gcd q (a * step ^ 3)
        ‖generalCubicExpSum (rationalCenter anum q') b c d M‖ ^ 4 ≤
          6 * (M + 1 : ℝ) ^ 3 +
            16 * (M + 1 : ℝ) *
              (79301 * (M + 2 : ℝ) ^ 3 / (B : ℝ) ^ delta) := by
  filter_upwards
    [eventually_hua_cubic_progression_pair_envelope_order a cQ hcQ
      sigma sigma0 sigma3 sigma4 delta hbudget hdelta hcutoff] with P hpair
  intro ell Q q r hQpos hellpos hrpos hrle hbase hac hell hQ hqLower hqUpper
  let B := Nat.floor (Real.log ((P : ℝ) + 2))
  let step := ell * (Q / Nat.gcd Q ell)
  let M := (P - ell * r) / step
  let q' := q / Nat.gcd q (a * step ^ 3)
  let anum := (a * step ^ 3) / Nat.gcd q (a * step ^ 3)
  have hpair' := hpair ell Q q r hQpos hellpos hrpos hrle hbase hac
    hell hQ hqLower hqUpper
  exact norm_generalCubicExpSum_four_le_of_paddedPairEnvelope
    (rationalCenter anum q') b c d M
    (79301 * (M + 2 : ℝ) ^ 3 / (B : ℝ) ^ delta)
    (by simpa [B, step, M, q', anum] using hpair')

/-- Convert the adjustable fourth-power Weyl estimate into a linear-norm
saving. Taking `delta = 4 * saving` makes the logarithmic denominator a
perfect fourth power; the independently proved progression-length lower
bound absorbs the residual `6(M+1)^3` term. -/
theorem eventually_hua_cubic_progression_weyl_norm_bound
    (a : ℕ) (b c d : ℝ) (cQ : ℝ) (hcQ : 0 ≤ cQ)
    (sigma sigma0 sigma3 sigma4 saving : ℕ)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma)
    (hsaving : 1 ≤ saving)
    (hcutoff : 3 * (sigma3 + sigma4 + 2) + 20 * saving ≤ sigma0) :
    ∀ᶠ P : ℕ in atTop,
      ∀ ell Q q r : ℕ,
        0 < Q → 0 < ell → 0 < r →
        r ≤ Q / Nat.gcd Q ell → ell * r ≤ P → Nat.Coprime a q →
        (ell : ℝ) ≤ Real.log ((P : ℝ) + 2) ^ sigma3 →
        (Q : ℝ) ≤ cQ * Real.log ((P : ℝ) + 2) ^ sigma4 →
        Real.log ((P : ℝ) + 2) ^ sigma < (q : ℝ) →
        (q : ℝ) ≤ (P : ℝ) ^ 3 / Real.log ((P : ℝ) + 2) ^ sigma →
        let B := Nat.floor (Real.log ((P : ℝ) + 2))
        let step := ell * (Q / Nat.gcd Q ell)
        let M := (P - ell * r) / step
        let q' := q / Nat.gcd q (a * step ^ 3)
        let anum := (a * step ^ 3) / Nat.gcd q (a * step ^ 3)
        ‖generalCubicExpSum (rationalCenter anum q') b c d M‖ ≤
          1268822 * (M + 2 : ℝ) / (B : ℝ) ^ saving := by
  have harg : Tendsto (fun P : ℕ => (P : ℝ) + 2) atTop atTop := by
    convert tendsto_atTop_add_const_right _ (2 : ℝ)
      tendsto_natCast_atTop_atTop using 1
  have hlog : Tendsto
      (fun P : ℕ => Real.log ((P : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp harg
  filter_upwards
    [eventually_hua_cubic_progression_weyl_fourth_power_bound_order
      a b c d cQ hcQ sigma sigma0 sigma3 sigma4 (4 * saving) hbudget
      (by omega) (by omega),
      eventually_hua_cubic_progression_length_dominates_log_power
        cQ hcQ sigma3 sigma4 (4 * saving),
      hlog.eventually_ge_atTop (4 : ℝ)] with P hfour hlength hlogLarge
  intro ell Q q r hQpos hellpos hrpos hrle hbase hac hell hQ hqLower hqUpper
  let B := Nat.floor (Real.log ((P : ℝ) + 2))
  let step := ell * (Q / Nat.gcd Q ell)
  let M := (P - ell * r) / step
  let q' := q / Nat.gcd q (a * step ^ 3)
  let anum := (a * step ^ 3) / Nat.gcd q (a * step ^ 3)
  have hB : 3 ≤ B := by
    dsimp [B]
    have hfloor : 4 ≤ Nat.floor (Real.log ((P : ℝ) + 2)) := by
      exact Nat.le_floor hlogLarge
    omega
  have hlength' := hlength ell Q r hQpos hellpos hrpos hrle hbase hell hQ
  have hlengthNat : B ^ (4 * saving) ≤ M + 2 := by
    simpa [B, M, step] using hlength'
  have hlengthReal : (B : ℝ) ^ (4 * saving) ≤ (M + 2 : ℝ) := by
    exact_mod_cast hlengthNat
  have hdenpos : (0 : ℝ) < (B : ℝ) ^ (4 * saving) := by
    positivity
  have hscalePow : (B : ℝ) ^ (4 * saving) = ((B : ℝ) ^ saving) ^ 4 := by
    rw [show 4 * saving = saving * 4 by omega, ← pow_mul]
  have hquotientPow :
      ((M + 2 : ℝ) / (B : ℝ) ^ saving) ^ 4 =
        (M + 2 : ℝ) ^ 4 / (B : ℝ) ^ (4 * saving) := by
    rw [div_pow, hscalePow]
  have hMpos : (0 : ℝ) ≤ (M + 1 : ℝ) := by positivity
  have hMle : (M + 1 : ℝ) ≤ (M + 2 : ℝ) := by exact_mod_cast Nat.le_succ (M + 1)
  have hfirst :
      6 * (M + 1 : ℝ) ^ 3 ≤
        6 * (M + 2 : ℝ) ^ 4 / (B : ℝ) ^ (4 * saving) := by
    apply (le_div_iff₀ hdenpos).2
    calc
      6 * (M + 1 : ℝ) ^ 3 * (B : ℝ) ^ (4 * saving) ≤
          6 * (M + 1 : ℝ) ^ 3 * (M + 2 : ℝ) := by
        gcongr
      _ ≤ 6 * (M + 2 : ℝ) ^ 4 := by
        calc
          6 * (M + 1 : ℝ) ^ 3 * (M + 2 : ℝ) ≤
              6 * (M + 2 : ℝ) ^ 3 * (M + 2 : ℝ) := by gcongr
          _ = 6 * (M + 2 : ℝ) ^ 4 := by ring
  have hnumSecond :
      16 * (M + 1 : ℝ) * 79301 * (M + 2 : ℝ) ^ 3 ≤
        (16 * 79301 : ℝ) * (M + 2 : ℝ) ^ 4 := by
    calc
      16 * (M + 1 : ℝ) * 79301 * (M + 2 : ℝ) ^ 3 ≤
          16 * (M + 2 : ℝ) * 79301 * (M + 2 : ℝ) ^ 3 := by gcongr
      _ = (16 * 79301 : ℝ) * (M + 2 : ℝ) ^ 4 := by ring
  have hsecond :
      16 * (M + 1 : ℝ) *
          (79301 * (M + 2 : ℝ) ^ 3 / (B : ℝ) ^ (4 * saving)) ≤
        (16 * 79301 : ℝ) * (M + 2 : ℝ) ^ 4 /
          (B : ℝ) ^ (4 * saving) := by
    calc
      _ = (16 * (M + 1 : ℝ) * 79301 * (M + 2 : ℝ) ^ 3) /
          (B : ℝ) ^ (4 * saving) := by ring
      _ ≤ (16 * 79301 : ℝ) * (M + 2 : ℝ) ^ 4 /
          (B : ℝ) ^ (4 * saving) :=
        div_le_div_of_nonneg_right hnumSecond hdenpos.le
  have hfour' := hfour ell Q q r hQpos hellpos hrpos hrle hbase hac
    hell hQ hqLower hqUpper
  have hbound :
      ‖generalCubicExpSum (rationalCenter anum q') b c d M‖ ^ 4 ≤
        (1268822 : ℝ) * (M + 2 : ℝ) ^ 4 /
          (B : ℝ) ^ (4 * saving) := by
    calc
      _ ≤ 6 * (M + 1 : ℝ) ^ 3 +
          16 * (M + 1 : ℝ) *
            (79301 * (M + 2 : ℝ) ^ 3 / (B : ℝ) ^ (4 * saving)) := by
        simpa [B, step, M, q', anum] using hfour'
      _ ≤ 6 * (M + 2 : ℝ) ^ 4 / (B : ℝ) ^ (4 * saving) +
          (16 * 79301 : ℝ) * (M + 2 : ℝ) ^ 4 /
            (B : ℝ) ^ (4 * saving) := add_le_add hfirst hsecond
      _ = (1268822 : ℝ) * (M + 2 : ℝ) ^ 4 /
            (B : ℝ) ^ (4 * saving) := by ring
  have hC : (1 : ℝ) ≤ 1268822 := by norm_num
  have hratioNonneg : 0 ≤ (M + 2 : ℝ) ^ 4 /
      (B : ℝ) ^ (4 * saving) := by positivity
  have htarget :
      ‖generalCubicExpSum (rationalCenter anum q') b c d M‖ ^ 4 ≤
        (1268822 * ((M + 2 : ℝ) / (B : ℝ) ^ saving)) ^ 4 := by
    calc
      _ ≤ (1268822 : ℝ) * (M + 2 : ℝ) ^ 4 /
          (B : ℝ) ^ (4 * saving) := hbound
      _ = (1268822 : ℝ) *
          ((M + 2 : ℝ) ^ 4 / (B : ℝ) ^ (4 * saving)) := by ring
      _ ≤ (1268822 : ℝ) ^ 4 *
          ((M + 2 : ℝ) ^ 4 / (B : ℝ) ^ (4 * saving)) := by
        exact mul_le_mul_of_nonneg_right (by norm_num)
          (by positivity)
      _ = (1268822 * ((M + 2 : ℝ) / (B : ℝ) ^ saving)) ^ 4 := by
        rw [mul_pow, hquotientPow]
  have htargetNonneg :
      0 ≤ 1268822 * ((M + 2 : ℝ) / (B : ℝ) ^ saving) := by positivity
  have hroot := le_of_pow_le_pow_left₀ (by norm_num : 4 ≠ 0)
    htargetNonneg htarget
  have hroot' :
      ‖generalCubicExpSum (rationalCenter anum q') b c d M‖ ≤
        1268822 * ((M + 2 : ℝ) / (B : ℝ) ^ saving) := hroot
  calc
    _ ≤ 1268822 * ((M + 2 : ℝ) / (B : ℝ) ^ saving) := hroot'
    _ = 1268822 * (M + 2 : ℝ) / (B : ℝ) ^ saving := by ring

/-- Endpoint-uniform form of the Hua progression Weyl estimate. Very short
prefixes are bounded trivially; for longer prefixes, the ambient denominator
upper window is weakened by three powers per lost logarithmic scale and the
pair-envelope estimate is reapplied at that prefix length. This is the
partial-sum interface needed by Abel summation. -/
theorem eventually_hua_cubic_progression_partial_weyl_norm_bound_uniform_coefficients_uniform_a
    (cQ : ℝ) (hcQ : 0 ≤ cQ)
    (sigma sigma0 sigma3 sigma4 saving : ℕ)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma)
    (hsaving : 1 ≤ saving)
    (hcutoff : 3 * (sigma3 + sigma4 + 2) + 20 * saving ≤ sigma0) :
    ∀ᶠ P : ℕ in atTop,
      ∀ a : ℕ, ∀ b c d : ℝ, ∀ ell Q q r : ℕ,
        0 < Q → 0 < ell → 0 < r →
        r ≤ Q / Nat.gcd Q ell → ell * r ≤ P → Nat.Coprime a q →
        (ell : ℝ) ≤ Real.log ((P : ℝ) + 2) ^ sigma3 →
        (Q : ℝ) ≤ cQ * Real.log ((P : ℝ) + 2) ^ sigma4 →
        Real.log ((P : ℝ) + 2) ^ sigma < (q : ℝ) →
        (q : ℝ) ≤ (P : ℝ) ^ 3 / Real.log ((P : ℝ) + 2) ^ sigma →
        let B := Nat.floor (Real.log ((P : ℝ) + 2))
        let step := ell * (Q / Nat.gcd Q ell)
        let M := (P - ell * r) / step
        let q' := q / Nat.gcd q (a * step ^ 3)
        let anum := (a * step ^ 3) / Nat.gcd q (a * step ^ 3)
        ∀ N : ℕ, N ≤ M →
          ‖generalCubicExpSum (rationalCenter anum q') b c d N‖ ≤
            1268822 * (M + 2 : ℝ) / (B : ℝ) ^ saving := by
  let e := sigma3 + sigma4 + 2
  have harg : Tendsto (fun P : ℕ => (P : ℝ) + 2) atTop atTop := by
    convert tendsto_atTop_add_const_right _ (2 : ℝ)
      tendsto_natCast_atTop_atTop using 1
  have hlog : Tendsto
      (fun P : ℕ => Real.log ((P : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp harg
  filter_upwards
    [hlog.eventually_ge_atTop (4 : ℝ),
      hlog.eventually
        (eventually_const_mul_pow_le_natFloor_pow_succ
          1 (by norm_num) sigma3),
      hlog.eventually
        (eventually_const_mul_pow_le_natFloor_pow_succ cQ hcQ sigma4),
      eventually_hua_cubic_log_ranges_give_transformed_denominator_window_uniform_a
        cQ hcQ sigma sigma0 sigma3 sigma4 hbudget,
      eventually_hua_cubic_progression_length_dominates_log_power
        cQ hcQ sigma3 sigma4 (3 * e + 25 * saving)] with
    P hlogLarge hellPow hQPow hwindow hlength
  intro a b c d ell Q q r hQpos hellpos hrpos hrle hbase hac hell hQ hqLower hqUpper
  let L : ℝ := Real.log ((P : ℝ) + 2)
  let B : ℕ := Nat.floor L
  let step : ℕ := ell * (Q / Nat.gcd Q ell)
  let M : ℕ := (P - ell * r) / step
  let q' : ℕ := q / Nat.gcd q (a * step ^ 3)
  let anum : ℕ := (a * step ^ 3) / Nat.gcd q (a * step ^ 3)
  have hB : 3 ≤ B := by
    dsimp [B, L]
    have hfloor : 4 ≤ Nat.floor (Real.log ((P : ℝ) + 2)) :=
      Nat.le_floor (by simpa [L] using hlogLarge)
    omega
  have hBpos : 0 < B := by omega
  have hellNat : ell ≤ B ^ (sigma3 + 1) := by
    have hreal : (ell : ℝ) ≤ (B : ℝ) ^ (sigma3 + 1) :=
      hell.trans (by simpa [B, L] using hellPow)
    exact_mod_cast hreal
  have hQNat : Q ≤ B ^ (sigma4 + 1) := by
    have hreal : (Q : ℝ) ≤ (B : ℝ) ^ (sigma4 + 1) :=
      hQ.trans (by simpa [B, L] using hQPow)
    exact_mod_cast hreal
  have hstepPos : 0 < step := by
    dsimp [step]
    exact Nat.mul_pos hellpos (Nat.div_pos
      (Nat.le_of_dvd hQpos (Nat.gcd_dvd_left Q ell))
      (Nat.gcd_pos_of_pos_left ell hQpos))
  have hstepBound : step ≤ B ^ e := by
    dsimp [step, e]
    calc
      ell * (Q / Nat.gcd Q ell) ≤ ell * Q :=
        Nat.mul_le_mul_left ell (Nat.div_le_self Q _)
      _ ≤ B ^ (sigma3 + 1) * B ^ (sigma4 + 1) :=
        Nat.mul_le_mul hellNat hQNat
      _ = B ^ (sigma3 + sigma4 + 2) := by
        rw [← pow_add]
        congr 1
        omega
  have hMleP : M ≤ P := by
    dsimp [M, step]
    exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hMlength : B ^ (3 * e + 25 * saving) ≤ M + 2 := by
    have h := hlength ell Q r hQpos hellpos hrpos hrle hbase hell hQ
    simpa [L, B, M, step, e] using h
  have hwindow' := hwindow a ell Q q r hQpos hellpos hrpos hrle hbase hac
    hell hQ hqLower hqUpper
  have hqpos : 0 < q := by
    have hqreal : (0 : ℝ) < (q : ℝ) :=
      lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ L ^ sigma) hqLower
    exact_mod_cast hqreal
  have hnumcop : Nat.Coprime anum q' := by
    dsimp [anum, q']
    exact generalCubicLeadingCoeff_reduced_coprime a q step hqpos
  have hMlenSaving : B ^ (4 * saving) ≤ M + 2 := by
    calc
      B ^ (4 * saving) ≤ B ^ (3 * e + 25 * saving) := by
        gcongr
        omega
      _ ≤ M + 2 := hMlength
  change ∀ n : ℕ, n ≤ M →
    ‖generalCubicExpSum (rationalCenter anum q') b c d n‖ ≤
      1268822 * (M + 2 : ℝ) / (B : ℝ) ^ saving
  intro n hnm
  have hnleP : n ≤ P := hnm.trans hMleP
  by_cases hlarge : M + 2 ≤ B ^ saving * (n + 2)
  · let rhoShort := sigma - 3 * e - 3 * saving
    have hrhoGap : 3 * e + 31 * saving ≤ sigma := by
      dsimp [e]
      omega
    have hrhoShort : 3 * e + 28 * saving ≤ rhoShort := by
      dsimp [rhoShort, e]
      omega
    have hsplit : rhoShort + 3 * saving = sigma - 3 * e := by
      dsimp [rhoShort]
      omega
    have hpowSplit : B ^ (sigma - 3 * e) =
        B ^ rhoShort * B ^ (3 * saving) := by
      rw [← hsplit, Nat.pow_add]
    have hlenMul : B ^ saving * B ^ (3 * e + 24 * saving) ≤
        B ^ saving * (n + 2) := by
      calc
        B ^ saving * B ^ (3 * e + 24 * saving) =
            B ^ (3 * e + 25 * saving) := by
          rw [← Nat.pow_add]
          congr 1
          omega
        _ ≤ M + 2 := hMlength
        _ ≤ B ^ saving * (n + 2) := hlarge
    have hlenPrefix : B ^ (3 * e + 24 * saving) ≤ n + 2 :=
      Nat.le_of_mul_le_mul_left hlenMul (Nat.pow_pos hBpos)
    have hupperMul :
        (q' * B ^ rhoShort) * B ^ (3 * saving) ≤
          (n + 2) ^ 3 * B ^ (3 * saving) := by
      calc
        (q' * B ^ rhoShort) * B ^ (3 * saving) =
            q' * B ^ (sigma - 3 * e) := by rw [hpowSplit]; ac_rfl
        _ ≤ (M + 2) ^ 3 := hwindow'.2
        _ ≤ (B ^ saving * (n + 2)) ^ 3 := Nat.pow_le_pow_left hlarge 3
        _ = (n + 2) ^ 3 * B ^ (3 * saving) := by
          rw [Nat.mul_pow, ← pow_mul]
          ac_rfl
    have hupperPrefix : q' * B ^ rhoShort ≤ (n + 2) ^ 3 :=
      Nat.le_of_mul_le_mul_right hupperMul (Nat.pow_pos hBpos)
    have hlenPrefixAdapter : B ^ (3 * e + 6 * (4 * saving)) ≤ n + 2 := by
      convert hlenPrefix using 1
      congr 1
      omega
    have hpair :=
      sum_positiveProductPairs_sixMul_envelope_le_logSaving_of_progression_power_ranges_source_size_order
        P n step anum q' rhoShort e sigma0 (4 * saving) hB hnleP
        hstepPos hstepBound (by omega) (by omega) hwindow'.1 hlenPrefixAdapter
        hupperPrefix (by omega) hnumcop
    exact norm_generalCubicExpSum_le_of_paddedPairEnvelope_logSaving
      (rationalCenter anum q') b c d n M B saving hB hnm hMlenSaving hpair
  · have hsmall : B ^ saving * (n + 2) < M + 2 := by omega
    have htrivial :
        ‖generalCubicExpSum (rationalCenter anum q') b c d n‖ ≤
          (n + 1 : ℝ) := by
      unfold generalCubicExpSum
      calc
        _ ≤ ∑ m ∈ Finset.range (n + 1),
            ‖generalCubicPhase (rationalCenter anum q') b c d m‖ := norm_sum_le _ _
        _ = (n + 1 : ℝ) := by simp
    have hsmallReal :
        (n + 2 : ℝ) ≤ (M + 2 : ℝ) / (B : ℝ) ^ saving := by
      apply (le_div_iff₀ (by positivity)).2
      exact_mod_cast (show (n + 2) * B ^ saving ≤ M + 2 by
        simpa [Nat.mul_comm] using hsmall.le)
    calc
      _ ≤ (n + 1 : ℝ) := htrivial
      _ ≤ (n + 2 : ℝ) := by exact_mod_cast Nat.le_succ (n + 1)
      _ ≤ 1268822 * ((M + 2 : ℝ) / (B : ℝ) ^ saving) := by
        calc
          (n + 2 : ℝ) ≤ (M + 2 : ℝ) / (B : ℝ) ^ saving := hsmallReal
          _ ≤ 1268822 * ((M + 2 : ℝ) / (B : ℝ) ^ saving) := by
            nlinarith [mul_nonneg (by positivity :
              0 ≤ (M + 2 : ℝ) / (B : ℝ) ^ saving) (by norm_num :
              0 ≤ (1268822 : ℝ) - 1)]
      _ = 1268822 * (M + 2 : ℝ) / (B : ℝ) ^ saving := by ring

/-- Compatibility interface with a fixed leading numerator. Its proof uses
the stronger endpoint threshold uniform in every numerator. -/
theorem eventually_hua_cubic_progression_partial_weyl_norm_bound_uniform_coefficients
    (a : ℕ) (cQ : ℝ) (hcQ : 0 ≤ cQ)
    (sigma sigma0 sigma3 sigma4 saving : ℕ)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma)
    (hsaving : 1 ≤ saving)
    (hcutoff : 3 * (sigma3 + sigma4 + 2) + 20 * saving ≤ sigma0) :
    ∀ᶠ P : ℕ in atTop,
      ∀ b c d : ℝ, ∀ ell Q q r : ℕ,
        0 < Q → 0 < ell → 0 < r →
        r ≤ Q / Nat.gcd Q ell → ell * r ≤ P → Nat.Coprime a q →
        (ell : ℝ) ≤ Real.log ((P : ℝ) + 2) ^ sigma3 →
        (Q : ℝ) ≤ cQ * Real.log ((P : ℝ) + 2) ^ sigma4 →
        Real.log ((P : ℝ) + 2) ^ sigma < (q : ℝ) →
        (q : ℝ) ≤ (P : ℝ) ^ 3 / Real.log ((P : ℝ) + 2) ^ sigma →
        let B := Nat.floor (Real.log ((P : ℝ) + 2))
        let step := ell * (Q / Nat.gcd Q ell)
        let M := (P - ell * r) / step
        let q' := q / Nat.gcd q (a * step ^ 3)
        let anum := (a * step ^ 3) / Nat.gcd q (a * step ^ 3)
        ∀ N : ℕ, N ≤ M →
          ‖generalCubicExpSum (rationalCenter anum q') b c d N‖ ≤
            1268822 * (M + 2 : ℝ) / (B : ℝ) ^ saving := by
  filter_upwards
    [eventually_hua_cubic_progression_partial_weyl_norm_bound_uniform_coefficients_uniform_a
      cQ hcQ sigma sigma0 sigma3 sigma4 saving hbudget hsaving hcutoff]
    with P hP
  intro b c d ell Q q r hQ hEll hR hRle hbase hac hell hQbound hqLower hqUpper
  exact hP a b c d ell Q q r hQ hEll hR hRle hbase hac hell hQbound
    hqLower hqUpper

/-- Fixed-lower-coefficient form retained for callers of the original
endpoint-uniform Weyl interface. -/
theorem eventually_hua_cubic_progression_partial_weyl_norm_bound
    (a : ℕ) (b c d : ℝ) (cQ : ℝ) (hcQ : 0 ≤ cQ)
    (sigma sigma0 sigma3 sigma4 saving : ℕ)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma)
    (hsaving : 1 ≤ saving)
    (hcutoff : 3 * (sigma3 + sigma4 + 2) + 20 * saving ≤ sigma0) :
    ∀ᶠ P : ℕ in atTop,
      ∀ ell Q q r : ℕ,
        0 < Q → 0 < ell → 0 < r →
        r ≤ Q / Nat.gcd Q ell → ell * r ≤ P → Nat.Coprime a q →
        (ell : ℝ) ≤ Real.log ((P : ℝ) + 2) ^ sigma3 →
        (Q : ℝ) ≤ cQ * Real.log ((P : ℝ) + 2) ^ sigma4 →
        Real.log ((P : ℝ) + 2) ^ sigma < (q : ℝ) →
        (q : ℝ) ≤ (P : ℝ) ^ 3 / Real.log ((P : ℝ) + 2) ^ sigma →
        let B := Nat.floor (Real.log ((P : ℝ) + 2))
        let step := ell * (Q / Nat.gcd Q ell)
        let M := (P - ell * r) / step
        let q' := q / Nat.gcd q (a * step ^ 3)
        let anum := (a * step ^ 3) / Nat.gcd q (a * step ^ 3)
        ∀ N : ℕ, N ≤ M →
          ‖generalCubicExpSum (rationalCenter anum q') b c d N‖ ≤
            1268822 * (M + 2 : ℝ) / (B : ℝ) ^ saving := by
  filter_upwards
    [eventually_hua_cubic_progression_partial_weyl_norm_bound_uniform_coefficients
      a cQ hcQ sigma sigma0 sigma3 sigma4 saving hbudget hsaving hcutoff]
    with P hP
  exact hP b c d

/-- Every prefix of Hua's rational-leading progression estimate survives
the smooth beta displacement. The endpoint-uniform bound is the input needed
to transfer logarithmic Vaughan weights by Abel summation. -/
theorem eventually_hua_cubic_progression_smooth_rational_char_prefix_bound_uniform_a
    (cQ : ℝ) (hcQ : 0 ≤ cQ)
    (sigma sigma0 sigma3 sigma4 saving : ℕ)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma)
    (hsaving : 1 ≤ saving)
    (hcutoff : 3 * (sigma3 + sigma4 + 2) + 20 * saving ≤ sigma0) :
    ∀ᶠ P : ℕ in atTop,
      ∀ a ell Q q r : ℕ,
        0 < Q → 0 < ell → 0 < r →
        r ≤ Q / Nat.gcd Q ell → ell * r ≤ P → Nat.Coprime a q →
        (ell : ℝ) ≤ Real.log ((P : ℝ) + 2) ^ sigma3 →
        (Q : ℝ) ≤ cQ * Real.log ((P : ℝ) + 2) ^ sigma4 →
        Real.log ((P : ℝ) + 2) ^ sigma < (q : ℝ) →
        (q : ℝ) ≤ (P : ℝ) ^ 3 / Real.log ((P : ℝ) + 2) ^ sigma →
        ∀ beta : ℝ, (P : ℝ) ^ 3 * |beta| ≤ 1 →
          let B := Nat.floor (Real.log ((P : ℝ) + 2))
          let step := ell * (Q / Nat.gcd Q ell)
          let M := (P - ell * r) / step
          ∀ n : ℕ, n ≤ M →
            ‖∑ m ∈ Finset.Icc 0 n,
              CookMagyarMajorArc.cubicAbelWeight beta
                  ((ell * r : ℝ) + (step : ℝ) * m) *
                addChar (rationalCenter a q)
                  (primeCubic (ell * r + step * m))‖ ≤
              (1268822 * (M + 2 : ℝ) / (B : ℝ) ^ saving) *
                (1 + 8 * Real.pi) := by
  let e := sigma3 + sigma4 + 2
  have harg : Tendsto (fun P : ℕ => (P : ℝ) + 2) atTop atTop := by
    convert tendsto_atTop_add_const_right _ (2 : ℝ)
      tendsto_natCast_atTop_atTop using 1
  have hlog : Tendsto
      (fun P : ℕ => Real.log ((P : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp harg
  filter_upwards
    [eventually_hua_cubic_progression_partial_weyl_norm_bound_uniform_coefficients_uniform_a
        cQ hcQ sigma sigma0 sigma3 sigma4 saving hbudget hsaving hcutoff,
      hlog.eventually_ge_atTop (4 : ℝ),
      eventually_hua_cubic_progression_length_dominates_log_power
        cQ hcQ sigma3 sigma4 (3 * e + 25 * saving)] with
    P hweyl hlogLarge hlength
  intro a ell Q q r hQpos hellpos hrpos hrle hbase hac hell hQ hqLower hqUpper
    beta hscaled
  dsimp only
  intro n hn
  let L : ℝ := Real.log ((P : ℝ) + 2)
  let B : ℕ := Nat.floor L
  let base : ℕ := ell * r
  let step : ℕ := ell * (Q / Nat.gcd Q ell)
  let M : ℕ := (P - base) / step
  let q' : ℕ := q / Nat.gcd q (a * step ^ 3)
  let anum : ℕ := (a * step ^ 3) / Nat.gcd q (a * step ^ 3)
  let Delta : ℝ := 1268822 * (M + 2 : ℝ) / (B : ℝ) ^ saving
  let alpha : ℝ := rationalCenter a q
  let theta : ℝ := rationalCenter anum q'
  let b' : ℝ := 3 * alpha * (base : ℝ) * (step : ℝ) ^ 2
  let c' : ℝ := 3 * alpha * (base : ℝ) ^ 2 * (step : ℝ) -
    alpha * (step : ℝ)
  let d' : ℝ := alpha * (base : ℝ) ^ 3 - alpha * (base : ℝ)
  have hB : 3 ≤ B := by
    dsimp [B, L]
    have hfloor : 4 ≤ Nat.floor (Real.log ((P : ℝ) + 2)) :=
      Nat.le_floor (by simpa [L] using hlogLarge)
    omega
  have hbasePos : 0 < base := by
    dsimp [base]
    exact Nat.mul_pos hellpos hrpos
  have hbasele : base ≤ P := by simpa [base] using hbase
  have hstepPos : 0 < step := by
    dsimp [step]
    exact Nat.mul_pos hellpos (Nat.div_pos
      (Nat.le_of_dvd hQpos (Nat.gcd_dvd_left Q ell))
      (Nat.gcd_pos_of_pos_left ell hQpos))
  have hMlength : B ^ (3 * e + 25 * saving) ≤ M + 2 := by
    have h := hlength ell Q r hQpos hellpos hrpos hrle hbase hell hQ
    simpa [L, B, base, M, step, e] using h
  have hMpos : 0 < M := by
    have hexp : 0 < 3 * e + 25 * saving := by omega
    have hpow : 3 ≤ B ^ (3 * e + 25 * saving) := by
      calc
        3 ≤ B := hB
        _ ≤ B ^ (3 * e + 25 * saving) := by
          exact Nat.le_pow (by omega)
    omega
  have hrem : (P - base) % step + step * M = P - base := by
    dsimp [M]
    exact Nat.mod_add_div (P - base) step
  have hstepM : step * M ≤ P - base := by
    have hle : step * M ≤ (P - base) % step + step * M :=
      Nat.le_add_left _ _
    rw [hrem] at hle
    exact hle
  have hcover : base + step * M ≤ P := by
    calc
      base + step * M ≤ base + (P - base) := Nat.add_le_add_left hstepM base
      _ = P := Nat.add_sub_cancel' hbasele
  have hDelta : 0 ≤ Delta := by
    dsimp [Delta]
    positivity
  have hphase : ∀ m : ℕ,
      addChar alpha (primeCubic (base + step * m)) =
        generalCubicPhase theta b' c' d' m := by
    intro m
    simpa [alpha, theta, b', c', d'] using
      addChar_rationalPrimeCubic_affine_eq_reducedGeneralCubicPhase
        a q base step m (by
          have hqreal : (0 : ℝ) < (q : ℝ) :=
            lt_of_le_of_lt (by positivity) hqLower
          exact_mod_cast hqreal)
  have hpartial : ∀ n : ℕ, n ≤ M →
      ‖generalCubicExpSum theta b' c' d' n‖ ≤ Delta := by
    intro n hn
    have h := hweyl a b' c' d' ell Q q r hQpos hellpos hrpos hrle
      hbase hac hell hQ hqLower hqUpper n hn
    simpa [B, L, base, step, M, q', anum, Delta, theta] using h
  have hcoverN : base + step * n ≤ P := by
    calc
      base + step * n ≤ base + step * M := by
        exact Nat.add_le_add_left (Nat.mul_le_mul_left step hn) base
      _ ≤ P := hcover
  have hbound :=
    norm_sum_affineCubicAbelWeight_mul_addChar_prefix_le_of_generalCubicPartialSums
      beta alpha theta b' c' d' base step P n hDelta hbasePos hstepPos
      hcoverN hscaled hphase (by
        intro k hk
        exact hpartial k (hk.trans hn))
  simpa [base, step, M, q', anum, B, L, Delta, alpha, theta, b', c', d'] using
    hbound

/-- Full-interval compatibility wrapper for the endpoint-uniform
smooth-beta progression estimate. -/
theorem eventually_hua_cubic_progression_smooth_rational_char_bound_uniform_a
    (cQ : ℝ) (hcQ : 0 ≤ cQ)
    (sigma sigma0 sigma3 sigma4 saving : ℕ)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma)
    (hsaving : 1 ≤ saving)
    (hcutoff : 3 * (sigma3 + sigma4 + 2) + 20 * saving ≤ sigma0) :
    ∀ᶠ P : ℕ in atTop,
      ∀ a ell Q q r : ℕ,
        0 < Q → 0 < ell → 0 < r →
        r ≤ Q / Nat.gcd Q ell → ell * r ≤ P → Nat.Coprime a q →
        (ell : ℝ) ≤ Real.log ((P : ℝ) + 2) ^ sigma3 →
        (Q : ℝ) ≤ cQ * Real.log ((P : ℝ) + 2) ^ sigma4 →
        Real.log ((P : ℝ) + 2) ^ sigma < (q : ℝ) →
        (q : ℝ) ≤ (P : ℝ) ^ 3 / Real.log ((P : ℝ) + 2) ^ sigma →
        ∀ beta : ℝ, (P : ℝ) ^ 3 * |beta| ≤ 1 →
          let B := Nat.floor (Real.log ((P : ℝ) + 2))
          let step := ell * (Q / Nat.gcd Q ell)
          let M := (P - ell * r) / step
          ‖∑ m ∈ Finset.Icc 0 M,
            CookMagyarMajorArc.cubicAbelWeight beta
                ((ell * r : ℝ) + (step : ℝ) * m) *
              addChar (rationalCenter a q)
                (primeCubic (ell * r + step * m))‖ ≤
            (1268822 * (M + 2 : ℝ) / (B : ℝ) ^ saving) *
              (1 + 8 * Real.pi) := by
  filter_upwards
    [eventually_hua_cubic_progression_smooth_rational_char_prefix_bound_uniform_a
      cQ hcQ sigma sigma0 sigma3 sigma4 saving hbudget hsaving hcutoff]
    with P hP
  intro a ell Q q r hQpos hellpos hrpos hrle hbase hac hell hQ hqLower hqUpper
    beta hscaled
  exact hP a ell Q q r hQpos hellpos hrpos hrle hbase hac hell hQ hqLower
    hqUpper beta hscaled _ (Nat.le_refl _)

/-- Fixed-numerator compatibility wrapper for the smooth-beta character
bound. The eventual threshold now comes from the uniform-numerator theorem. -/
theorem eventually_hua_cubic_progression_smooth_rational_char_bound
    (a : ℕ) (cQ : ℝ) (hcQ : 0 ≤ cQ)
    (sigma sigma0 sigma3 sigma4 saving : ℕ)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma)
    (hsaving : 1 ≤ saving)
    (hcutoff : 3 * (sigma3 + sigma4 + 2) + 20 * saving ≤ sigma0) :
    ∀ᶠ P : ℕ in atTop,
      ∀ ell Q q r : ℕ,
        0 < Q → 0 < ell → 0 < r →
        r ≤ Q / Nat.gcd Q ell → ell * r ≤ P → Nat.Coprime a q →
        (ell : ℝ) ≤ Real.log ((P : ℝ) + 2) ^ sigma3 →
        (Q : ℝ) ≤ cQ * Real.log ((P : ℝ) + 2) ^ sigma4 →
        Real.log ((P : ℝ) + 2) ^ sigma < (q : ℝ) →
        (q : ℝ) ≤ (P : ℝ) ^ 3 / Real.log ((P : ℝ) + 2) ^ sigma →
        ∀ beta : ℝ, (P : ℝ) ^ 3 * |beta| ≤ 1 →
          let B := Nat.floor (Real.log ((P : ℝ) + 2))
          let step := ell * (Q / Nat.gcd Q ell)
          let M := (P - ell * r) / step
          ‖∑ m ∈ Finset.Icc 0 M,
            CookMagyarMajorArc.cubicAbelWeight beta
                ((ell * r : ℝ) + (step : ℝ) * m) *
              addChar (rationalCenter a q)
                (primeCubic (ell * r + step * m))‖ ≤
            (1268822 * (M + 2 : ℝ) / (B : ℝ) ^ saving) *
              (1 + 8 * Real.pi) := by
  filter_upwards
    [eventually_hua_cubic_progression_smooth_rational_char_bound_uniform_a
      cQ hcQ sigma sigma0 sigma3 sigma4 saving hbudget hsaving hcutoff]
    with P hP
  intro ell Q q r hQ hEll hR hRle hbase hac hEllBound hQBound hqLower hqUpper
    beta hscaled
  exact hP a ell Q q r hQ hEll hR hRle hbase hac hEllBound hQBound
    hqLower hqUpper beta hscaled

/-- Wrapped-arc form of the smooth-beta progression estimate. The integer
wrap is removed exactly by periodicity, so this is the character at the
original frequency `rationalCenter a q + beta + z`. -/
theorem eventually_hua_cubic_progression_wrapped_beta_char_prefix_bound_uniform_a
    (cQ : ℝ) (hcQ : 0 ≤ cQ)
    (sigma sigma0 sigma3 sigma4 saving : ℕ)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma)
    (hsaving : 1 ≤ saving)
    (hcutoff : 3 * (sigma3 + sigma4 + 2) + 20 * saving ≤ sigma0) :
    ∀ᶠ P : ℕ in atTop,
      ∀ a ell Q q r : ℕ,
        0 < Q → 0 < ell → 0 < r →
        r ≤ Q / Nat.gcd Q ell → ell * r ≤ P → Nat.Coprime a q →
        (ell : ℝ) ≤ Real.log ((P : ℝ) + 2) ^ sigma3 →
        (Q : ℝ) ≤ cQ * Real.log ((P : ℝ) + 2) ^ sigma4 →
        Real.log ((P : ℝ) + 2) ^ sigma < (q : ℝ) →
        (q : ℝ) ≤ (P : ℝ) ^ 3 / Real.log ((P : ℝ) + 2) ^ sigma →
        ∀ beta : ℝ, ∀ z : ℤ, (P : ℝ) ^ 3 * |beta| ≤ 1 →
          let B := Nat.floor (Real.log ((P : ℝ) + 2))
          let step := ell * (Q / Nat.gcd Q ell)
          let M := (P - ell * r) / step
          ∀ n : ℕ, n ≤ M →
            ‖∑ m ∈ Finset.Icc 0 n,
              addChar (rationalCenter a q + beta + z)
                (primeCubic (ell * r + step * m))‖ ≤
              (1268822 * (M + 2 : ℝ) / (B : ℝ) ^ saving) *
                (1 + 8 * Real.pi) := by
  filter_upwards
    [eventually_hua_cubic_progression_smooth_rational_char_prefix_bound_uniform_a
      cQ hcQ sigma sigma0 sigma3 sigma4 saving hbudget hsaving hcutoff]
    with P hsmooth
  intro a ell Q q r hQpos hellpos hrpos hrle hbase hac hell hQ hqLower hqUpper
    beta z hscaled
  dsimp only
  intro n hn
  let step : ℕ := ell * (Q / Nat.gcd Q ell)
  have hsum : (∑ m ∈ Finset.Icc 0 n,
      addChar (rationalCenter a q + beta + z)
        (primeCubic (ell * r + step * m))) =
      ∑ m ∈ Finset.Icc 0 n,
        CookMagyarMajorArc.cubicAbelWeight beta
            ((ell * r : ℝ) + (step : ℝ) * m) *
          addChar (rationalCenter a q) (primeCubic (ell * r + step * m)) := by
    apply Finset.sum_congr rfl
    intro m _hm
    simpa only [Nat.cast_add, Nat.cast_mul] using
      CookMagyarMajorArc.addChar_primeCubic_eq_cubicAbelWeight_mul_rational
        (alpha := rationalCenter a q + beta + z) (beta := beta)
        (a := a) (q := q) (z := z) (ell * r + step * m) rfl
  rw [hsum]
  exact hsmooth a ell Q q r hQpos hellpos hrpos hrle hbase hac hell hQ
    hqLower hqUpper beta hscaled n hn

/-- Full-interval compatibility wrapper for the endpoint-uniform
wrapped-beta character estimate. -/
theorem eventually_hua_cubic_progression_wrapped_beta_char_bound_uniform_a
    (cQ : ℝ) (hcQ : 0 ≤ cQ)
    (sigma sigma0 sigma3 sigma4 saving : ℕ)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma)
    (hsaving : 1 ≤ saving)
    (hcutoff : 3 * (sigma3 + sigma4 + 2) + 20 * saving ≤ sigma0) :
    ∀ᶠ P : ℕ in atTop,
      ∀ a ell Q q r : ℕ,
        0 < Q → 0 < ell → 0 < r →
        r ≤ Q / Nat.gcd Q ell → ell * r ≤ P → Nat.Coprime a q →
        (ell : ℝ) ≤ Real.log ((P : ℝ) + 2) ^ sigma3 →
        (Q : ℝ) ≤ cQ * Real.log ((P : ℝ) + 2) ^ sigma4 →
        Real.log ((P : ℝ) + 2) ^ sigma < (q : ℝ) →
        (q : ℝ) ≤ (P : ℝ) ^ 3 / Real.log ((P : ℝ) + 2) ^ sigma →
        ∀ beta : ℝ, ∀ z : ℤ, (P : ℝ) ^ 3 * |beta| ≤ 1 →
          let B := Nat.floor (Real.log ((P : ℝ) + 2))
          let step := ell * (Q / Nat.gcd Q ell)
          let M := (P - ell * r) / step
          ‖∑ m ∈ Finset.Icc 0 M,
            addChar (rationalCenter a q + beta + z)
              (primeCubic (ell * r + step * m))‖ ≤
            (1268822 * (M + 2 : ℝ) / (B : ℝ) ^ saving) *
              (1 + 8 * Real.pi) := by
  filter_upwards
    [eventually_hua_cubic_progression_wrapped_beta_char_prefix_bound_uniform_a
      cQ hcQ sigma sigma0 sigma3 sigma4 saving hbudget hsaving hcutoff]
    with P hP
  intro a ell Q q r hQpos hellpos hrpos hrle hbase hac hell hQ hqLower hqUpper
    beta z hscaled
  exact hP a ell Q q r hQpos hellpos hrpos hrle hbase hac hell hQ hqLower
    hqUpper beta z hscaled _ (Nat.le_refl _)

/-- Fixed-numerator compatibility wrapper for the wrapped-beta character
estimate. -/
theorem eventually_hua_cubic_progression_wrapped_beta_char_bound
    (a : ℕ) (cQ : ℝ) (hcQ : 0 ≤ cQ)
    (sigma sigma0 sigma3 sigma4 saving : ℕ)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma)
    (hsaving : 1 ≤ saving)
    (hcutoff : 3 * (sigma3 + sigma4 + 2) + 20 * saving ≤ sigma0) :
    ∀ᶠ P : ℕ in atTop,
      ∀ ell Q q r : ℕ,
        0 < Q → 0 < ell → 0 < r →
        r ≤ Q / Nat.gcd Q ell → ell * r ≤ P → Nat.Coprime a q →
        (ell : ℝ) ≤ Real.log ((P : ℝ) + 2) ^ sigma3 →
        (Q : ℝ) ≤ cQ * Real.log ((P : ℝ) + 2) ^ sigma4 →
        Real.log ((P : ℝ) + 2) ^ sigma < (q : ℝ) →
        (q : ℝ) ≤ (P : ℝ) ^ 3 / Real.log ((P : ℝ) + 2) ^ sigma →
        ∀ beta : ℝ, ∀ z : ℤ, (P : ℝ) ^ 3 * |beta| ≤ 1 →
          let B := Nat.floor (Real.log ((P : ℝ) + 2))
          let step := ell * (Q / Nat.gcd Q ell)
          let M := (P - ell * r) / step
          ‖∑ m ∈ Finset.Icc 0 M,
            addChar (rationalCenter a q + beta + z)
              (primeCubic (ell * r + step * m))‖ ≤
            (1268822 * (M + 2 : ℝ) / (B : ℝ) ^ saving) *
              (1 + 8 * Real.pi) := by
  filter_upwards
    [eventually_hua_cubic_progression_wrapped_beta_char_bound_uniform_a
      cQ hcQ sigma sigma0 sigma3 sigma4 saving hbudget hsaving hcutoff]
    with P hP
  intro ell Q q r hQ hEll hR hRle hbase hac hEllBound hQBound hqLower hqUpper
    beta z hscaled
  exact hP a ell Q q r hQ hEll hR hRle hbase hac hEllBound hQBound
    hqLower hqUpper beta z hscaled

/-- The one-power margin in Hua's Dirichlet denominator window absorbs the
height shift `(N+2)^3` and gives the denominator upper range at scale `N`. -/
theorem eventually_logarithmic_hua_denominator_upper_bound
    (sigma : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      ((N : ℝ) + 2) ^ 3 /
          (Real.log ((N : ℝ) + 2)) ^ (sigma + 1) ≤
        (N : ℝ) ^ 3 / (Real.log ((N : ℝ) + 2)) ^ sigma := by
  have harg : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop := by
    convert tendsto_atTop_add_const_right _ (2 : ℝ)
      tendsto_natCast_atTop_atTop using 1
  have hlog : Tendsto
      (fun N : ℕ => Real.log ((N : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp harg
  filter_upwards [hlog.eventually_ge_atTop (27 : ℝ),
    eventually_ge_atTop (1 : ℕ)] with N hL hN
  let L : ℝ := Real.log ((N : ℝ) + 2)
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hshift : (N : ℝ) + 2 ≤ 3 * (N : ℝ) := by
    linarith
  have hshiftCube : ((N : ℝ) + 2) ^ 3 ≤ 27 * (N : ℝ) ^ 3 := by
    calc
      ((N : ℝ) + 2) ^ 3 ≤ (3 * (N : ℝ)) ^ 3 := by gcongr
      _ = 27 * (N : ℝ) ^ 3 := by ring
  have hnum : ((N : ℝ) + 2) ^ 3 ≤ (N : ℝ) ^ 3 * L := by
    calc
      ((N : ℝ) + 2) ^ 3 ≤ 27 * (N : ℝ) ^ 3 := hshiftCube
      _ ≤ L * (N : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right hL (by positivity)
      _ = (N : ℝ) ^ 3 * L := by ring
  have hcross :
      ((N : ℝ) + 2) ^ 3 * L ^ sigma ≤
        (N : ℝ) ^ 3 * (L ^ sigma * L) := by
    calc
      ((N : ℝ) + 2) ^ 3 * L ^ sigma ≤
          ((N : ℝ) ^ 3 * L) * L ^ sigma :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
      _ = (N : ℝ) ^ 3 * (L ^ sigma * L) := by ring
  apply (div_le_div_iff₀
    (pow_pos hLpos (sigma + 1)) (pow_pos hLpos sigma)).2
  rw [show sigma + 1 = Nat.succ sigma by omega, pow_succ]
  exact hcross

/-- Compose Hua's minor-arc Dirichlet witness with the all-numerator wrapped
progression estimate. A stronger Dirichlet exponent supplies the extra
logarithmic margin needed to replace `(N+2)^3` by `N^3`; this proves an
unweighted character estimate on every admissible progression, not yet the
Vaughan-weighted prime sum. -/
theorem eventually_logarithmicPrimeMinorArc_wrapped_progression_character_bound
    (A sigma sigma0 sigma3 sigma4 saving : ℕ)
    (hA : 0 < A) (hSA : sigma + 2 < A)
    (cQ : ℝ) (hcQ : 0 ≤ cQ)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma)
    (hsaving : 1 ≤ saving)
    (hcutoff : 3 * (sigma3 + sigma4 + 2) + 20 * saving ≤ sigma0) :
    ∀ᶠ N : ℕ in atTop,
      ∀ alpha : ℝ,
        alpha ∈ minorArcs N
          (CookMagyarCircle.logarithmicDenominatorCutoff A N) →
          ∃ a q : ℕ, ∃ beta : ℝ, ∃ z : ℤ,
            Real.log ((N : ℝ) + 2) ^ (sigma + 1) < (q : ℝ) ∧
            (q : ℝ) ≤ ((N : ℝ) + 2) ^ 3 /
              Real.log ((N : ℝ) + 2) ^ (sigma + 1) ∧
            a < q ∧ Nat.Coprime a q ∧
            alpha = rationalCenter a q + beta + z ∧
            |beta| ≤ 1 / (q : ℝ) ^ 2 ∧
            (N : ℝ) ^ 3 * |beta| ≤
              (CookMagyarCircle.logarithmicDenominatorCutoff A N : ℝ) /
                (q : ℝ) ∧
            (N : ℝ) ^ 3 * |beta| ≤ 1 ∧
            (∀ ell Q r : ℕ,
              0 < Q → 0 < ell → 0 < r →
              r ≤ Q / Nat.gcd Q ell → ell * r ≤ N →
              (ell : ℝ) ≤ Real.log ((N : ℝ) + 2) ^ sigma3 →
              (Q : ℝ) ≤ cQ * Real.log ((N : ℝ) + 2) ^ sigma4 →
              ∀ n : ℕ,
                n ≤ (N - ell * r) / (ell * (Q / Nat.gcd Q ell)) →
                ‖∑ m ∈ Finset.Icc 0 n,
                  addChar (rationalCenter a q + beta + z)
                    (primeCubic
                      (ell * r + ell * (Q / Nat.gcd Q ell) * m))‖ ≤
                  (1268822 *
                      (((N - ell * r) /
                        (ell * (Q / Nat.gcd Q ell)) : ℕ) + 2 : ℝ) /
                      (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ saving) *
                    (1 + 8 * Real.pi)) := by
  have hData :=
    CookMagyarMajorArc.eventually_exists_logarithmicPrimeMinorArcWeylData_huaWindow
      A (sigma + 1) hA (by omega)
  have hWeyl :=
    eventually_hua_cubic_progression_wrapped_beta_char_prefix_bound_uniform_a
      cQ hcQ sigma sigma0 sigma3 sigma4 saving hbudget hsaving hcutoff
  have hUpper := eventually_logarithmic_hua_denominator_upper_bound sigma
  have harg : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop := by
    convert tendsto_atTop_add_const_right _ (2 : ℝ)
      tendsto_natCast_atTop_atTop using 1
  have hlog : Tendsto
      (fun N : ℕ => Real.log ((N : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp harg
  filter_upwards [hData, hWeyl, hUpper,
    hlog.eventually_ge_atTop (1 : ℝ)] with
    N hDataN hWeylN hUpperN hL
  intro alpha hminor
  obtain ⟨a, q, beta, z, hqLowerStrong, hqUpperStrong, ha, hac, halpha,
    hbeta, hscaledByCutoff, hscaledOne⟩ := hDataN alpha hminor
  let L : ℝ := Real.log ((N : ℝ) + 2)
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hqLower : L ^ sigma < (q : ℝ) := by
    have hpow : L ^ sigma ≤ L ^ (sigma + 1) := by
      rw [show sigma + 1 = Nat.succ sigma by omega, pow_succ]
      calc
        L ^ sigma = L ^ sigma * 1 := by ring
        _ ≤ L ^ sigma * L :=
          mul_le_mul_of_nonneg_left (by linarith : 1 ≤ L) (by positivity)
        _ = L ^ sigma * L := rfl
    exact hpow.trans_lt (by simpa [L] using hqLowerStrong)
  have hqUpperStrong' :
      (q : ℝ) ≤ ((N : ℝ) + 2) ^ 3 / L ^ (sigma + 1) := by
    simpa [L] using hqUpperStrong
  have hqUpperRange :
      ((N : ℝ) + 2) ^ 3 / L ^ (sigma + 1) ≤
        (N : ℝ) ^ 3 / L ^ sigma := by
    simpa [L] using hUpperN
  have hqUpper : (q : ℝ) ≤ (N : ℝ) ^ 3 / L ^ sigma :=
    hqUpperStrong'.trans hqUpperRange
  refine ⟨a, q, beta, z, hqLowerStrong, hqUpperStrong, ha, hac, halpha,
    hbeta, hscaledByCutoff, hscaledOne, ?_⟩
  intro ell Q r hQpos hellpos hrpos hrle hbase hell hQ n hn
  exact hWeylN a ell Q q r hQpos hellpos hrpos hrle hbase hac
    hell hQ hqLower hqUpper beta z hscaledOne n hn

set_option maxHeartbeats 800000 in
/-- Logarithmically weighted form of the minor-arc progression bound. The
weight `log(k+1)` is the Vaughan first-Type-I weight after writing the inner
variable as `m=k+1`. This controls one progression block; summation over the
outer truncated-Möbius variable is still separate. -/
theorem eventually_logarithmicPrimeMinorArc_logWeighted_wrapped_progression_bound
    (A sigma sigma0 sigma3 sigma4 saving : ℕ)
    (hA : 0 < A) (hSA : sigma + 2 < A)
    (cQ : ℝ) (hcQ : 0 ≤ cQ)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma)
    (hsaving : 1 ≤ saving)
    (hcutoff : 3 * (sigma3 + sigma4 + 2) + 20 * saving ≤ sigma0) :
    ∀ᶠ N : ℕ in atTop,
      ∀ alpha : ℝ,
        alpha ∈ minorArcs N
          (CookMagyarCircle.logarithmicDenominatorCutoff A N) →
          ∃ a q : ℕ, ∃ beta : ℝ, ∃ z : ℤ,
            Real.log ((N : ℝ) + 2) ^ (sigma + 1) < (q : ℝ) ∧
            (q : ℝ) ≤ ((N : ℝ) + 2) ^ 3 /
              Real.log ((N : ℝ) + 2) ^ (sigma + 1) ∧
            a < q ∧ Nat.Coprime a q ∧
            alpha = rationalCenter a q + beta + z ∧
            |beta| ≤ 1 / (q : ℝ) ^ 2 ∧
            (N : ℝ) ^ 3 * |beta| ≤
              (CookMagyarCircle.logarithmicDenominatorCutoff A N : ℝ) /
                (q : ℝ) ∧
            (N : ℝ) ^ 3 * |beta| ≤ 1 ∧
            (∀ ell Q r : ℕ,
              0 < Q → 0 < ell → 0 < r →
              r ≤ Q / Nat.gcd Q ell → ell * r ≤ N →
              (ell : ℝ) ≤ Real.log ((N : ℝ) + 2) ^ sigma3 →
              (Q : ℝ) ≤ cQ * Real.log ((N : ℝ) + 2) ^ sigma4 →
              let B := Nat.floor (Real.log ((N : ℝ) + 2))
              let step := ell * (Q / Nat.gcd Q ell)
              let M := (N - ell * r) / step
              0 < M →
              ‖∑ k ∈ Finset.Icc 0 M,
                (Real.log ((k : ℝ) + 1) : ℂ) *
                  addChar (rationalCenter a q + beta + z)
                    (primeCubic (ell * r + step * k))‖ ≤
                2 * (1268822 * (M + 2 : ℝ) / (B : ℝ) ^ saving) *
                  (1 + 8 * Real.pi) * Real.log ((M : ℝ) + 1)) := by
  have hBase := eventually_logarithmicPrimeMinorArc_wrapped_progression_character_bound
    A sigma sigma0 sigma3 sigma4 saving hA hSA cQ hcQ hbudget hsaving hcutoff
  filter_upwards [hBase] with N hN
  intro alpha hminor
  obtain ⟨a, q, beta, z, hqLower, hqUpper, ha, hac, halpha, hbeta,
    hscaled, hscaledOne, hprogressions⟩ := hN alpha hminor
  refine ⟨a, q, beta, z, hqLower, hqUpper, ha, hac, halpha, hbeta,
    hscaled, hscaledOne, ?_⟩
  intro ell Q r hQpos hellpos hrpos hrle hbase hell hQ
  dsimp only
  intro hM
  let step : ℕ := ell * (Q / Nat.gcd Q ell)
  let M : ℕ := (N - ell * r) / step
  let B : ℕ := Nat.floor (Real.log ((N : ℝ) + 2))
  let Delta : ℝ := 1268822 * (M + 2 : ℝ) / (B : ℝ) ^ saving *
    (1 + 8 * Real.pi)
  let c : ℕ → ℂ := fun k =>
    addChar (rationalCenter a q + beta + z)
      (primeCubic (ell * r + step * k))
  have hprefix : ∀ n : ℕ, n ≤ M →
      ‖∑ k ∈ Finset.Icc 0 n, c k‖ ≤ Delta := by
    intro n hn
    have h := hprogressions ell Q r hQpos hellpos hrpos hrle hbase hell hQ n hn
    simpa [step, M, B, Delta, c] using h
  have hDelta : 0 ≤ Delta := by
    dsimp [Delta]
    positivity
  have hweighted :=
    norm_sum_log_mul_le_of_natPrefixBound c M hM hDelta hprefix
  simpa [step, M, B, Delta, c, mul_assoc, mul_left_comm, mul_comm] using
    hweighted

/-- Fourth-power form of the thresholded divisor-moment Weyl estimate for a
cubic with arbitrary real lower coefficients. -/
theorem norm_generalCubicExpSum_four_le_divisorThreshold
    (theta b c d : ℝ) (N a q : ℕ) (beta T : ℝ)
    (hq : 0 < q) (hac : Nat.Coprime a q)
    (halpha : theta = rationalCenter a q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hT : 0 < T) :
    ‖generalCubicExpSum theta b c d N‖ ^ 4 ≤
      6 * (N + 1 : ℝ) ^ 3 +
        16 * (N + 1 : ℝ) *
          (T * sixMulSpacingEnvelopeBound N q (N + 1 : ℝ) +
            (N + 1 : ℝ) * (((N * N : ℕ) : ℝ) *
              (1 + Real.log ((N * N : ℕ) : ℝ)) ^ 7) / T ^ 2) := by
  have hsecond := norm_generalCubicSecondDifferenceSum_le_divisorThreshold
    theta b c d N a q beta T hq hac halpha hbeta hT
  have hbase := norm_generalCubicExpSum_four_le_secondDifference
    theta b c d N
  calc
    ‖generalCubicExpSum theta b c d N‖ ^ 4 ≤
        6 * (N + 1 : ℝ) ^ 3 +
          16 * (N + 1 : ℝ) *
            ‖unitSequenceSecondDifferenceSum
              (generalCubicPhase theta b c d) N‖ := hbase
    _ ≤ 6 * (N + 1 : ℝ) ^ 3 +
          16 * (N + 1 : ℝ) *
            (T * sixMulSpacingEnvelopeBound N q (N + 1 : ℝ) +
              (N + 1 : ℝ) * (((N * N : ℕ) : ℝ) *
                (1 + Real.log ((N * N : ℕ) : ℝ)) ^ 7) / T ^ 2) := by
      gcongr

/-- Exact-rational-leading specialization of the thresholded fourth-power
bound. This is the phase contract needed before transferring a smooth beta
twist by Abel summation. -/
theorem norm_generalCubicExpSum_four_le_divisorThreshold_rational
    (a : ℕ) (b c d : ℝ) (N q : ℕ) (T : ℝ)
    (hq : 0 < q) (hac : Nat.Coprime a q) (hT : 0 < T) :
    ‖generalCubicExpSum (rationalCenter a q) b c d N‖ ^ 4 ≤
      6 * (N + 1 : ℝ) ^ 3 +
        16 * (N + 1 : ℝ) *
          (T * sixMulSpacingEnvelopeBound N q (N + 1 : ℝ) +
            (N + 1 : ℝ) * (((N * N : ℕ) : ℝ) *
              (1 + Real.log ((N * N : ℕ) : ℝ)) ^ 7) / T ^ 2) := by
  apply norm_generalCubicExpSum_four_le_divisorThreshold
    (rationalCenter a q) b c d N a q 0 T hq hac ?_ ?_ hT
  · ring
  · simp

/-- Uniform cubic Weyl differencing with arbitrary quadratic and linear
coefficients. Only the rational approximation to the leading coefficient
enters the bound. -/
theorem exists_uniform_norm_generalCubicExpSum_four_le_spacing
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (theta b c d : ℝ) (N a q : ℕ) (beta : ℝ),
      0 < q → Nat.Coprime a q → theta = rationalCenter a q + beta →
      |beta| ≤ 1 / (q : ℝ) ^ 2 →
      ‖generalCubicExpSum theta b c d N‖ ^ 4 ≤
        6 * (N + 1 : ℝ) ^ 3 +
          16 * (N + 1 : ℝ) *
            (C * Real.rpow ((N * N : ℕ) : ℝ) ε *
              sixMulSpacingEnvelopeBound N q (N + 1 : ℝ)) := by
  obtain ⟨C, hC, hD⟩ :=
    exists_uniform_norm_generalCubicSecondDifferenceSum_le_spacing hε
  refine ⟨C, hC, fun theta b c d N a q beta hq hac halpha hbeta => ?_⟩
  have hD' := hD theta b c d N a q beta hq hac halpha hbeta
  calc
    ‖generalCubicExpSum theta b c d N‖ ^ 4 ≤
        6 * (N + 1 : ℝ) ^ 3 + 16 * (N + 1 : ℝ) *
          ‖unitSequenceSecondDifferenceSum (generalCubicPhase theta b c d) N‖ :=
      norm_generalCubicExpSum_four_le_secondDifference theta b c d N
    _ ≤ 6 * (N + 1 : ℝ) ^ 3 + 16 * (N + 1 : ℝ) *
          (C * Real.rpow ((N * N : ℕ) : ℝ) ε *
            sixMulSpacingEnvelopeBound N q (N + 1 : ℝ)) := by
      have hcoef : 0 ≤ 16 * (N + 1 : ℝ) := by positivity
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left (mul_le_mul_of_nonneg_left hD' hcoef)
          (6 * (N + 1 : ℝ) ^ 3)

#print axioms SystolicGrowth.CookMagyarCircle.norm_unitSequence_sum_four_le_secondDifference
#print axioms SystolicGrowth.CookMagyarCircle.generalCubicPhase_secondDifference
#print axioms SystolicGrowth.CookMagyarCircle.generalCubicPolynomial_affineChange
#print axioms SystolicGrowth.CookMagyarCircle.sum_generalCubicPhase_affineChange
#print axioms SystolicGrowth.CookMagyarCircle.addChar_primeCubic_eq_generalCubicPhase
#print axioms SystolicGrowth.CookMagyarCircle.addChar_primeCubic_affine_eq_generalCubicPhase
#print axioms SystolicGrowth.CookMagyarCircle.norm_sum_affineCubicAbelWeight_mul_addChar_le_of_generalCubicPartialSums
#print axioms SystolicGrowth.CookMagyarCircle.norm_sum_affineCubicAbelWeight_mul_addChar_prefix_le_of_generalCubicPartialSums
#print axioms SystolicGrowth.CookMagyarCircle.norm_sum_log_mul_le_of_natPrefixBound
#print axioms SystolicGrowth.CookMagyarCircle.generalCubicLeadingCoeff_affineApprox
#print axioms SystolicGrowth.CookMagyarCircle.generalCubicLeadingCoeff_reducedCenter
#print axioms SystolicGrowth.CookMagyarCircle.addChar_rationalPrimeCubic_affine_eq_reducedGeneralCubicPhase
#print axioms SystolicGrowth.CookMagyarCircle.generalCubicLeadingCoeff_reduced_coprime
#print axioms SystolicGrowth.CookMagyarCircle.generalCubicLeadingCoeff_reduced_denominator_bounds
#print axioms SystolicGrowth.CookMagyarCircle.generalCubicLeadingCoeff_reduced_denominator_gt_of_scaled_lower_bound
#print axioms SystolicGrowth.CookMagyarCircle.generalCubicLeadingCoeff_reduced_denominator_gt_of_ell_Q_bound
#print axioms SystolicGrowth.CookMagyarCircle.cubic_scaled_denominator_lower_bound_of_power_bounds
#print axioms SystolicGrowth.CookMagyarCircle.hua_cubic_typeI_budget_gives_reduced_denominator_range
#print axioms SystolicGrowth.CookMagyarCircle.hua_cubic_typeI_threshold_exponents
#print axioms SystolicGrowth.CookMagyarCircle.hua_cubic_typeI_scaled_threshold_exponents
#print axioms SystolicGrowth.CookMagyarCircle.progressionStep_cube_le_log_power
#print axioms SystolicGrowth.CookMagyarCircle.eventually_progression_length_dominates_logarithmic_power
#print axioms SystolicGrowth.CookMagyarCircle.eventually_hua_cubic_log_ranges_give_reduced_denominator_range
#print axioms SystolicGrowth.CookMagyarCircle.eventually_hua_cubic_log_ranges_give_reduced_denominator_range_uniform_a
#print axioms SystolicGrowth.CookMagyarCircle.eventually_hua_cubic_log_ranges_give_reduced_denominator_range_at_scale
#print axioms SystolicGrowth.CookMagyarCircle.eventually_hua_cubic_log_ranges_give_reduced_denominator_range_at_scale_uniform_a
#print axioms SystolicGrowth.CookMagyarCircle.eventually_hua_cubic_logarithmicCutoff_gives_reduced_denominator_range
#print axioms SystolicGrowth.CookMagyarCircle.generalCubicLeadingCoeff_affineError_le_reduced
#print axioms SystolicGrowth.CookMagyarCircle.generalCubicLeadingCoeff_affineApprox_reduced
#print axioms SystolicGrowth.CookMagyarCircle.mul_modEq_iff_modEq_div_gcd
#print axioms SystolicGrowth.CookMagyarCircle.mul_modEq_iff_root_modEq_div_gcd
#print axioms SystolicGrowth.CookMagyarCircle.exists_mul_modEq_iff_gcd_dvd
#print axioms SystolicGrowth.CookMagyarCircle.exists_pos_mul_modEq_root_le_div_gcd_iff
#print axioms SystolicGrowth.CookMagyarCircle.nat_modEq_iff_exists_add_mul_of_le
#print axioms SystolicGrowth.CookMagyarCircle.le_of_pos_modEq_of_le_step
#print axioms SystolicGrowth.CookMagyarCircle.pos_mul_modEq_iff_exists_progression
#print axioms SystolicGrowth.CookMagyarCircle.nat_add_mul_le_iff_le_div
#print axioms SystolicGrowth.CookMagyarCircle.nat_mul_progression_cutoff_iff_le_div
#print axioms SystolicGrowth.CookMagyarCircle.progression_quotient_length_covers_endpoint
#print axioms SystolicGrowth.CookMagyarCircle.pos_mul_modEq_mul_le_iff_progression_cutoff
#print axioms SystolicGrowth.CookMagyarCircle.pos_mul_modEq_mul_le_iff_progression_cutoff_unconditional
#print axioms SystolicGrowth.CookMagyarCircle.sum_linearCongruence_eq_sum_progression
#print axioms SystolicGrowth.CookMagyarCircle.sum_linearCongruence_generalCubicPhase_eq_progression
#print axioms SystolicGrowth.CookMagyarCircle.sum_multiples_generalCubicPhase_eq_progression
#print axioms SystolicGrowth.CookMagyarCircle.exists_uniform_norm_generalCubicExpSum_four_le_spacing
#print axioms SystolicGrowth.CookMagyarCircle.norm_generalCubicExpSum_four_le_divisorThreshold
#print axioms SystolicGrowth.CookMagyarCircle.norm_generalCubicExpSum_four_le_divisorThreshold_rational
#print axioms SystolicGrowth.CookMagyarCircle.cubic_scaled_denominator_upper_bound_of_power_bounds
#print axioms SystolicGrowth.CookMagyarCircle.nat_denominator_upper_of_real_log_bound
#print axioms SystolicGrowth.CookMagyarCircle.hua_cubic_typeI_upper_window_of_natural_ranges
#print axioms SystolicGrowth.CookMagyarCircle.eventually_hua_cubic_log_ranges_give_transformed_denominator_window
#print axioms SystolicGrowth.CookMagyarCircle.eventually_hua_cubic_log_ranges_give_transformed_denominator_window_uniform_a
#print axioms SystolicGrowth.CookMagyarCircle.eventually_hua_cubic_progression_length_dominates_log_power
#print axioms SystolicGrowth.CookMagyarCircle.eventually_hua_cubic_progression_pair_envelope
#print axioms SystolicGrowth.CookMagyarCircle.norm_generalCubicSecondDifferenceSum_le_paddedPairEnvelope
#print axioms SystolicGrowth.CookMagyarCircle.norm_generalCubicExpSum_four_le_of_paddedPairEnvelope
#print axioms SystolicGrowth.CookMagyarCircle.norm_generalCubicExpSum_le_of_paddedPairEnvelope_logSaving
#print axioms SystolicGrowth.CookMagyarCircle.eventually_hua_cubic_progression_weyl_fourth_power_bound
#print axioms SystolicGrowth.CookMagyarCircle.eventually_hua_cubic_progression_weyl_fourth_power_bound_order
#print axioms SystolicGrowth.CookMagyarCircle.eventually_hua_cubic_progression_weyl_norm_bound
#print axioms SystolicGrowth.CookMagyarCircle.eventually_hua_cubic_progression_partial_weyl_norm_bound
#print axioms SystolicGrowth.CookMagyarCircle.eventually_hua_cubic_progression_partial_weyl_norm_bound_uniform_coefficients
#print axioms SystolicGrowth.CookMagyarCircle.eventually_hua_cubic_progression_partial_weyl_norm_bound_uniform_coefficients_uniform_a
#print axioms SystolicGrowth.CookMagyarCircle.eventually_hua_cubic_progression_smooth_rational_char_bound
#print axioms SystolicGrowth.CookMagyarCircle.eventually_hua_cubic_progression_smooth_rational_char_bound_uniform_a
#print axioms SystolicGrowth.CookMagyarCircle.eventually_hua_cubic_progression_smooth_rational_char_prefix_bound_uniform_a
#print axioms SystolicGrowth.CookMagyarCircle.eventually_hua_cubic_progression_wrapped_beta_char_bound
#print axioms SystolicGrowth.CookMagyarCircle.eventually_hua_cubic_progression_wrapped_beta_char_bound_uniform_a
#print axioms SystolicGrowth.CookMagyarCircle.eventually_hua_cubic_progression_wrapped_beta_char_prefix_bound_uniform_a
#print axioms SystolicGrowth.CookMagyarCircle.eventually_logarithmic_hua_denominator_upper_bound
#print axioms SystolicGrowth.CookMagyarCircle.eventually_logarithmicPrimeMinorArc_wrapped_progression_character_bound
#print axioms SystolicGrowth.CookMagyarCircle.eventually_logarithmicPrimeMinorArc_logWeighted_wrapped_progression_bound

end CookMagyarCircle
end SystolicGrowth
