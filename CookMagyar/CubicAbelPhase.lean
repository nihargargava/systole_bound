module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.AbelError
public import CookMagyar.ArcPhasePeriodicity
public import CookMagyar.MajorArcArithmetic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

@[expose] public section

open Finset MeasureTheory

namespace SystolicGrowth
namespace CookMagyarMajorArc

open CookMagyarCircle

/-! # Smooth cubic phase for major-arc partial summation

The natural cubic here is `x^3 - x`, not `x^3 - 1`.  This real extension
agrees with the discrete character at every natural argument and has an
explicit derivative bound on the interval used by Abel summation.
-/

/-- The real phase occurring in the displaced cubic character. -/
noncomputable def cubicAbelRealPhase (beta t : ℝ) : ℝ :=
  2 * Real.pi * beta * (t ^ 3 - t)

/-- A smooth extension of `addChar beta (primeCubic k)`. -/
noncomputable def cubicAbelWeight (beta t : ℝ) : ℂ :=
  Complex.exp ((cubicAbelRealPhase beta t : ℂ) * Complex.I)

theorem cubicAbelRealPhase_hasDerivAt (beta t : ℝ) :
    HasDerivAt (cubicAbelRealPhase beta)
      (2 * Real.pi * beta * (3 * t ^ 2 - 1)) t := by
  have hpow : HasDerivAt (fun y : ℝ => y ^ 3) (3 * t ^ 2) t := by
    simpa using (hasDerivAt_pow 3 t)
  have hpoly : HasDerivAt (fun y : ℝ => y ^ 3 - y) (3 * t ^ 2 - 1) t :=
    hpow.sub (hasDerivAt_id t)
  convert hpoly.const_mul (2 * Real.pi * beta) using 1 <;> rfl

theorem cubicAbelWeight_hasDerivAt (beta t : ℝ) :
    HasDerivAt (cubicAbelWeight beta)
      (cubicAbelWeight beta t *
        ((2 * Real.pi * beta * (3 * t ^ 2 - 1) : ℝ) : ℂ) * Complex.I) t := by
  have h := (cubicAbelRealPhase_hasDerivAt beta t).ofReal_comp.mul_const Complex.I
  convert h.cexp using 1 <;> try rfl
  dsimp only [cubicAbelWeight]
  ring

theorem cubicAbelWeight_differentiable (beta : ℝ) :
    Differentiable ℝ (cubicAbelWeight beta) :=
  fun t => (cubicAbelWeight_hasDerivAt beta t).differentiableAt

theorem cubicAbelWeight_deriv (beta t : ℝ) :
    deriv (cubicAbelWeight beta) t =
      cubicAbelWeight beta t *
        ((2 * Real.pi * beta * (3 * t ^ 2 - 1) : ℝ) : ℂ) * Complex.I :=
  (cubicAbelWeight_hasDerivAt beta t).deriv

theorem cubicAbelWeight_norm (beta t : ℝ) :
    ‖cubicAbelWeight beta t‖ = 1 := by
  unfold cubicAbelWeight
  exact Complex.norm_exp_ofReal_mul_I _

theorem cubicAbelWeight_nat (beta : ℝ) (k : ℕ) :
    cubicAbelWeight beta k = addChar beta (primeCubic k) := by
  unfold cubicAbelWeight cubicAbelRealPhase addChar primeCubic
  rw [Nat.cast_sub (Nat.le_pow (by norm_num : 0 < 3))]
  push_cast
  congr 1
  ring

/-- A wrapped rational approximation of the frequency splits the cubic
character into Hua's rational-leading phase and the smooth displacement
`e(beta (x^3-x))`. The integer wrap contributes no phase. -/
theorem addChar_primeCubic_eq_cubicAbelWeight_mul_rational
    {alpha beta : ℝ} {a q : ℕ} {z : ℤ} (k : ℕ)
    (happrox : alpha = CookMagyarArcs.rationalCenter a q + beta + z) :
    addChar alpha (primeCubic k) =
      cubicAbelWeight beta k *
        addChar (CookMagyarArcs.rationalCenter a q) (primeCubic k) := by
  rw [happrox, CookMagyarArcs.addChar_add_int,
    CookMagyarMajorArc.addChar_add_real]
  rw [← cubicAbelWeight_nat beta k]
  ring

theorem cubicAbelWeight_deriv_integrableOn (beta : ℝ) (N : ℕ) :
    IntegrableOn (deriv (cubicAbelWeight beta)) (Set.Icc (0 : ℝ) N) := by
  have hcont : Continuous (fun t : ℝ =>
      cubicAbelWeight beta t *
        ((2 * Real.pi * beta * (3 * t ^ 2 - 1) : ℝ) : ℂ) * Complex.I) := by
    unfold cubicAbelWeight cubicAbelRealPhase
    fun_prop
  have hint : IntegrableOn (fun t : ℝ =>
      cubicAbelWeight beta t *
        ((2 * Real.pi * beta * (3 * t ^ 2 - 1) : ℝ) : ℂ) * Complex.I)
      (Set.Icc (0 : ℝ) N) := hcont.integrableOn_Icc
  change IntegrableOn (fun t : ℝ => deriv (cubicAbelWeight beta) t)
    (Set.Icc (0 : ℝ) N)
  rw [show (fun t : ℝ => deriv (cubicAbelWeight beta) t) =
      (fun t : ℝ => cubicAbelWeight beta t *
        ((2 * Real.pi * beta * (3 * t ^ 2 - 1) : ℝ) : ℂ) * Complex.I) by
      funext t
      exact cubicAbelWeight_deriv beta t]
  exact hint

theorem cubicAbelWeight_deriv_norm (beta t : ℝ) :
    ‖deriv (cubicAbelWeight beta) t‖ =
      |2 * Real.pi * beta * (3 * t ^ 2 - 1)| := by
  rw [cubicAbelWeight_deriv]
  simp only [norm_mul, cubicAbelWeight_norm, one_mul,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one, abs_mul]

/-- An explicit bound for the variation of the real cubic phase on `[0,N]`. -/
theorem cubicAbelWeight_deriv_bound (beta : ℝ) (N : ℕ)
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) N) :
    ‖deriv (cubicAbelWeight beta) t‖ ≤
      2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1) := by
  have ht0 : 0 ≤ t := ht.1.le
  have htN : t ≤ N := ht.2
  have ht2 : t ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ ht0 htN 2
  have hpoly : |3 * t ^ 2 - 1| ≤ 3 * (N : ℝ) ^ 2 + 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg t]
  have hcoeff : 0 ≤ 2 * Real.pi * |beta| := by positivity
  rw [cubicAbelWeight_deriv_norm, abs_mul, abs_mul]
  calc
    |2 * Real.pi| * |beta| * |3 * t ^ 2 - 1| =
        (2 * Real.pi * |beta|) * |3 * t ^ 2 - 1| := by
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    _ ≤ (2 * Real.pi * |beta|) * (3 * (N : ℝ) ^ 2 + 1) :=
      mul_le_mul_of_nonneg_left hpoly hcoeff

/-- The cubic character can be used directly as the smooth Abel weight.
Only the arithmetic partial-sum estimate remains as an input. -/
theorem norm_sum_addChar_primeCubic_le_partialSumBound
    (c : ℕ → ℂ) (beta : ℝ) (N : ℕ) {Delta : ℝ}
    (hN : 0 < N) (hDelta : 0 ≤ Delta)
    (hpartial : ∀ t ∈ Set.Ioc (0 : ℝ) N,
      ‖∑ k ∈ Icc 0 ⌊t⌋₊, c k‖ ≤ Delta) :
    ‖∑ k ∈ Icc 0 N, addChar beta (primeCubic k) * c k‖ ≤
      Delta * (1 + (N : ℝ) *
        (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1))) := by
  have h := norm_sum_mul_le_partialSumBound_mul_one_add_length_deriv
    c (f := cubicAbelWeight beta) N hN hDelta
    (fun t _ht => (cubicAbelWeight_differentiable beta).differentiableAt)
    (cubicAbelWeight_deriv_integrableOn beta N)
    (by rw [cubicAbelWeight_norm]) hpartial
    (fun t ht => cubicAbelWeight_deriv_bound beta N ht)
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro k _hk
  rw [cubicAbelWeight_nat]

/-- If the cubic displacement satisfies `N^3 |beta| ≤ 1`, the Abel weight
costs only an absolute factor. This is the analytic interface for the
logarithmic minor-arc Dirichlet approximation. -/
theorem norm_sum_addChar_primeCubic_le_partialSumBound_of_scaledError
    (c : ℕ → ℂ) (beta : ℝ) (N : ℕ) {Delta : ℝ}
    (hN : 0 < N) (hDelta : 0 ≤ Delta)
    (hscaled : (N : ℝ) ^ 3 * |beta| ≤ 1)
    (hpartial : ∀ t ∈ Set.Ioc (0 : ℝ) N,
      ‖∑ k ∈ Icc 0 ⌊t⌋₊, c k‖ ≤ Delta) :
    ‖∑ k ∈ Icc 0 N, addChar beta (primeCubic k) * c k‖ ≤
      Delta * (1 + 8 * Real.pi) := by
  have hbase := norm_sum_addChar_primeCubic_le_partialSumBound
    c beta N hN hDelta hpartial
  have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hN2 : 1 ≤ (N : ℝ) ^ 2 := by nlinarith
  have hpoly : 3 * (N : ℝ) ^ 2 + 1 ≤ 4 * (N : ℝ) ^ 2 := by nlinarith
  have hfactor :
      (N : ℝ) * (2 * Real.pi * |beta| *
        (3 * (N : ℝ) ^ 2 + 1)) ≤ 8 * Real.pi := by
    calc
      (N : ℝ) * (2 * Real.pi * |beta| *
          (3 * (N : ℝ) ^ 2 + 1)) ≤
        (N : ℝ) * (2 * Real.pi * |beta| *
          (4 * (N : ℝ) ^ 2)) := by
            apply mul_le_mul_of_nonneg_left
            · apply mul_le_mul_of_nonneg_left hpoly
              positivity
            · positivity
      _ = 8 * Real.pi * ((N : ℝ) ^ 3 * |beta|) := by ring
      _ ≤ 8 * Real.pi := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hscaled
            (by positivity : 0 ≤ 8 * Real.pi))
  calc
    ‖∑ k ∈ Icc 0 N, addChar beta (primeCubic k) * c k‖ ≤
        Delta * (1 + (N : ℝ) *
          (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1))) := hbase
    _ ≤ Delta * (1 + 8 * Real.pi) :=
      mul_le_mul_of_nonneg_left (by linarith) hDelta

/-- Chain-rule derivative for the smooth cubic displacement along an affine
progression `base + step*t`. -/
private theorem cubicAbelWeight_affine_hasDerivAt
    (beta base step t : ℝ) :
    HasDerivAt (fun x : ℝ => cubicAbelWeight beta (base + step * x))
      (cubicAbelWeight beta (base + step * t) *
        (((2 * Real.pi * beta * (3 * (base + step * t) ^ 2 - 1) : ℝ) : ℂ) *
          Complex.I) * (step : ℂ)) t := by
  have hinner : HasDerivAt (fun x : ℝ => base + step * x) step t := by
    simpa [add_comm] using ((hasDerivAt_id t).const_mul step).const_add base
  have houter := HasDerivAt.scomp t
    (cubicAbelWeight_hasDerivAt beta (base + step * t)) hinner
  simpa only [Function.comp_def, Complex.real_smul, mul_assoc, mul_comm,
    mul_left_comm] using houter

/-- Transfer an unweighted partial-sum estimate through the original smooth
minor-arc beta phase after restricting to an affine progression. If the
progression lies in `[0,P]` and `P^3 |beta|≤1`, the variation cost is the same
absolute factor `1+8π` as for the unscaled prime-cubic phase. -/
theorem norm_sum_affineCubicAbelWeight_mul_le_partialSumBound_of_scaledError
    (c : ℕ → ℂ) (beta : ℝ) (base step P M : ℕ) {Delta : ℝ}
    (hM : 0 < M) (hDelta : 0 ≤ Delta)
    (hbase : 0 < base) (hstep : 0 < step)
    (hcover : base + step * M ≤ P)
    (hscaled : (P : ℝ) ^ 3 * |beta| ≤ 1)
    (hpartial : ∀ t ∈ Set.Ioc (0 : ℝ) M,
      ‖∑ k ∈ Icc 0 ⌊t⌋₊, c k‖ ≤ Delta) :
    ‖∑ m ∈ Icc 0 M,
      cubicAbelWeight beta ((base : ℝ) + (step : ℝ) * m) * c m‖ ≤
        Delta * (1 + 8 * Real.pi) := by
  let f : ℝ → ℂ := fun t =>
    cubicAbelWeight beta ((base : ℝ) + (step : ℝ) * t)
  have hPpos : 0 < P := by omega
  have hPreal : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hPpos)
  have hbaseReal : (0 : ℝ) < (base : ℝ) := by exact_mod_cast hbase
  have hstepReal : (0 : ℝ) ≤ (step : ℝ) := by positivity
  have hstepM : step * M ≤ P := by
    have hmul : step * M ≤ base + step * M := by omega
    exact hmul.trans hcover
  have hstepMReal : (step : ℝ) * (M : ℝ) ≤ (P : ℝ) := by
    exact_mod_cast hstepM
  have hpoly :
      (P : ℝ) * (3 * (P : ℝ) ^ 2 + 1) ≤ 4 * (P : ℝ) ^ 3 := by
    nlinarith [sq_nonneg ((P : ℝ) - 1)]
  have hbetaP : |beta| * ((P : ℝ) ^ 3) ≤ 1 := by
    nlinarith [hscaled]
  have hvariation : (M : ℝ) *
      (2 * Real.pi * |beta| * (step : ℝ) *
        (3 * (P : ℝ) ^ 2 + 1)) ≤ 8 * Real.pi := by
    have hbaseVariation :
        |beta| * ((step : ℝ) * (M : ℝ)) *
          (3 * (P : ℝ) ^ 2 + 1) ≤ 4 := by
      calc
        |beta| * ((step : ℝ) * (M : ℝ)) *
            (3 * (P : ℝ) ^ 2 + 1) ≤
          |beta| * (P : ℝ) * (3 * (P : ℝ) ^ 2 + 1) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hstepMReal (abs_nonneg beta))
              (by positivity)
        _ ≤ |beta| * (4 * (P : ℝ) ^ 3) := by
          calc
            |beta| * (P : ℝ) * (3 * (P : ℝ) ^ 2 + 1) =
                |beta| * ((P : ℝ) * (3 * (P : ℝ) ^ 2 + 1)) := by ring
            _ ≤ |beta| * (4 * (P : ℝ) ^ 3) :=
              mul_le_mul_of_nonneg_left hpoly (abs_nonneg beta)
        _ ≤ 4 := by nlinarith [hbetaP]
    calc
      (M : ℝ) * (2 * Real.pi * |beta| * (step : ℝ) *
          (3 * (P : ℝ) ^ 2 + 1)) =
        2 * Real.pi * (|beta| * ((step : ℝ) * (M : ℝ)) *
          (3 * (P : ℝ) ^ 2 + 1)) := by ring
      _ ≤ 2 * Real.pi * 4 := by
        exact mul_le_mul_of_nonneg_left hbaseVariation (by positivity)
      _ = 8 * Real.pi := by ring
  have hfdiff : ∀ t ∈ Set.Icc (0 : ℝ) M, DifferentiableAt ℝ f t := by
    intro t _ht
    exact (cubicAbelWeight_affine_hasDerivAt beta (base : ℝ) (step : ℝ) t).differentiableAt
  have hderivFormula (t : ℝ) :
      deriv f t = cubicAbelWeight beta ((base : ℝ) + (step : ℝ) * t) *
        (((2 * Real.pi * beta *
          (3 * ((base : ℝ) + (step : ℝ) * t) ^ 2 - 1) : ℝ) : ℂ) *
            Complex.I) * (step : ℂ) := by
    exact (cubicAbelWeight_affine_hasDerivAt beta (base : ℝ) (step : ℝ) t).deriv
  have hfint : IntegrableOn (deriv f) (Set.Icc (0 : ℝ) M) := by
    have hcont : Continuous (fun t : ℝ =>
        cubicAbelWeight beta ((base : ℝ) + (step : ℝ) * t) *
          (((2 * Real.pi * beta *
            (3 * ((base : ℝ) + (step : ℝ) * t) ^ 2 - 1) : ℝ) : ℂ) *
              Complex.I) * (step : ℂ)) := by
      unfold cubicAbelWeight cubicAbelRealPhase
      fun_prop
    have hfcont : ContinuousOn (deriv f) (Set.Icc (0 : ℝ) M) := by
      apply hcont.continuousOn.congr
      intro t _ht
      exact hderivFormula t
    exact hfcont.integrableOn_Icc
  have hderiv : ∀ t ∈ Set.Ioc (0 : ℝ) M,
      ‖deriv f t‖ ≤
        2 * Real.pi * |beta| * (step : ℝ) *
          (3 * (P : ℝ) ^ 2 + 1) := by
    intro t ht
    let x := (base : ℝ) + (step : ℝ) * t
    have htM : t ≤ M := ht.2
    have hxpos : 0 < x := by
      have ht0 : 0 ≤ t := ht.1.le
      dsimp [x]
      nlinarith [hbaseReal, hstepReal, ht0]
    have hxle : x ≤ P := by
      dsimp [x]
      have htmul : (step : ℝ) * t ≤ (step : ℝ) * (M : ℝ) :=
        mul_le_mul_of_nonneg_left htM hstepReal
      have hbasex : (base : ℝ) + (step : ℝ) * t ≤
          (base : ℝ) + (step : ℝ) * (M : ℝ) := by
        nlinarith [htmul]
      have hcoverReal : (base : ℝ) + (step : ℝ) * (M : ℝ) ≤ P := by
        exact_mod_cast hcover
      exact hbasex.trans hcoverReal
    have hx : x ∈ Set.Ioc (0 : ℝ) P := ⟨hxpos, hxle⟩
    have hweight := cubicAbelWeight_deriv_bound beta P hx
    have hchain : deriv f t = deriv (cubicAbelWeight beta) x * (step : ℂ) := by
      rw [hderivFormula, cubicAbelWeight_deriv]
      ring
    have hvariationAtX :
        ‖deriv (cubicAbelWeight beta) x‖ * (step : ℝ) ≤
          (2 * Real.pi * |beta| * (3 * (P : ℝ) ^ 2 + 1)) * (step : ℝ) :=
      mul_le_mul_of_nonneg_right hweight hstepReal
    have hstepnorm : ‖(step : ℂ)‖ = (step : ℝ) := by
      norm_cast
    calc
      ‖deriv f t‖ = ‖deriv (cubicAbelWeight beta) x‖ * (step : ℝ) := by
        rw [hchain, norm_mul, hstepnorm]
      _ ≤ (2 * Real.pi * |beta| * (3 * (P : ℝ) ^ 2 + 1)) * (step : ℝ) :=
        hvariationAtX
      _ = 2 * Real.pi * |beta| * (step : ℝ) *
          (3 * (P : ℝ) ^ 2 + 1) := by ring
  have habel := norm_sum_mul_le_partialSumBound_mul_one_add_length_deriv
    c (f := f) M hM hDelta hfdiff hfint
    (by simp [f, cubicAbelWeight_norm]) hpartial hderiv
  have hfactor : 1 + (M : ℝ) *
      (2 * Real.pi * |beta| * (step : ℝ) *
        (3 * (P : ℝ) ^ 2 + 1)) ≤ 1 + 8 * Real.pi := by
    linarith [hvariation]
  exact habel.trans (mul_le_mul_of_nonneg_left hfactor hDelta)

/-- Transfer a uniform rational-phase partial-sum estimate to the wrapped
minor-arc frequency. This isolates the exact implication needed after Hua's
prime estimate: the source estimate is still supplied separately, while the
Dirichlet displacement is handled by bounded variation. -/
theorem norm_sum_addChar_wrapped_le_of_rationalPartialSums
    (c : ℕ → ℂ) (alpha beta : ℝ) (a q : ℕ) (z : ℤ) (N : ℕ)
    {Delta : ℝ} (hN : 0 < N) (hDelta : 0 ≤ Delta)
    (hscaled : (N : ℝ) ^ 3 * |beta| ≤ 1)
    (happrox : alpha = CookMagyarArcs.rationalCenter a q + beta + z)
    (hpartial : ∀ t ∈ Set.Ioc (0 : ℝ) N,
      ‖∑ k ∈ Icc 0 ⌊t⌋₊,
        addChar (CookMagyarArcs.rationalCenter a q)
          (primeCubic k) * c k‖ ≤ Delta) :
    ‖∑ k ∈ Icc 0 N, addChar alpha (primeCubic k) * c k‖ ≤
      Delta * (1 + 8 * Real.pi) := by
  let d : ℕ → ℂ := fun k =>
    addChar (CookMagyarArcs.rationalCenter a q) (primeCubic k) * c k
  have hdpartial : ∀ t ∈ Set.Ioc (0 : ℝ) N,
      ‖∑ k ∈ Icc 0 ⌊t⌋₊, d k‖ ≤ Delta := by
    intro t ht
    simpa only [d] using hpartial t ht
  have habel := norm_sum_addChar_primeCubic_le_partialSumBound_of_scaledError
    d beta N hN hDelta hscaled hdpartial
  have hsum :
      (∑ k ∈ Icc 0 N, addChar alpha (primeCubic k) * c k) =
        ∑ k ∈ Icc 0 N, addChar beta (primeCubic k) * d k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [addChar_primeCubic_eq_cubicAbelWeight_mul_rational k happrox,
      ← cubicAbelWeight_nat beta k]
    simp only [d]
    ring
  rw [hsum]
  exact habel

/-- The real logarithmic weight normalized to have endpoint value at most
one on `[0,N]`. The shift by one keeps the logarithm smooth at the origin,
while making the value at a positive integer `k` equal to `log k`. -/
noncomputable def normalizedPrimeLogWeightReal (N : ℕ) (t : ℝ) : ℝ :=
  Real.log (t + 1) / Real.log ((N : ℝ) + 1)

/-- Complex-valued version of `normalizedPrimeLogWeightReal`, used as a
smooth Abel weight. -/
noncomputable def normalizedPrimeLogWeight (N : ℕ) (t : ℝ) : ℂ :=
  (normalizedPrimeLogWeightReal N t : ℂ)

private theorem primeLogScale_pos {N : ℕ} (hN : 0 < N) :
    0 < Real.log ((N : ℝ) + 1) := by
  apply Real.log_pos
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.succ_le_iff.mpr hN)
  linarith

private theorem normalizedPrimeLogWeightReal_hasDerivAt
    (N : ℕ) (_hN : 0 < N) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (normalizedPrimeLogWeightReal N)
      ((1 / (t + 1)) / Real.log ((N : ℝ) + 1)) t := by
  have hshift : HasDerivAt (fun x : ℝ => x + 1) 1 t := by
    simpa using (hasDerivAt_id t).add_const (1 : ℝ)
  have hlog : HasDerivAt (fun x : ℝ => Real.log (x + 1))
      (1 / (t + 1)) t := by
    have hcomp :=
      (Real.hasDerivAt_log (x := t + 1) (by linarith)).comp t hshift
    convert hcomp using 1 <;> try rfl
    simp [div_eq_mul_inv]
  change HasDerivAt
    (fun x : ℝ => Real.log (x + 1) / Real.log ((N : ℝ) + 1)) _ t
  exact hlog.div_const (Real.log ((N : ℝ) + 1))

private theorem normalizedPrimeLogWeight_hasDerivAt
    (N : ℕ) (hN : 0 < N) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (normalizedPrimeLogWeight N)
      ((((1 / (t + 1)) / Real.log ((N : ℝ) + 1) : ℝ) : ℂ)) t := by
  change HasDerivAt (fun x => (normalizedPrimeLogWeightReal N x : ℂ)) _ t
  exact (normalizedPrimeLogWeightReal_hasDerivAt N hN t ht).ofReal_comp

/-- Abel summation converts a uniform bound for all partial sums into a
logarithmically weighted bound. The variation of the normalized log weight
is at most one, so the loss is at most `2 log(N+1)`. -/
theorem norm_sum_log_mul_le_of_partialSumBound
    (c : ℕ → ℂ) (N : ℕ) {Delta : ℝ}
    (hN : 0 < N) (hDelta : 0 ≤ Delta)
    (hpartial : ∀ t ∈ Set.Ioc (0 : ℝ) N,
      ‖∑ k ∈ Icc 0 ⌊t⌋₊, c k‖ ≤ Delta) :
    ‖∑ k ∈ Icc 0 N,
        (Real.log ((k : ℝ) + 1) : ℂ) * c k‖ ≤
      2 * Delta * Real.log ((N : ℝ) + 1) := by
  let D : ℝ := Real.log ((N : ℝ) + 1)
  have hD : 0 < D := by exact primeLogScale_pos hN
  have hN0 : (0 : ℝ) ≤ N := by exact_mod_cast (Nat.zero_le N)
  have hmono : MonotoneOn (normalizedPrimeLogWeightReal N)
      (Set.uIcc (0 : ℝ) N) := by
    intro x hx y hy hxy
    have hx' : 0 ≤ x ∧ x ≤ N := by
      simpa using hx
    have hy' : 0 ≤ y ∧ y ≤ N := by
      simpa using hy
    unfold normalizedPrimeLogWeightReal
    apply div_le_div_of_nonneg_right _ (le_of_lt hD)
    apply Real.log_le_log
    · linarith
    · linarith
  have hfdiff : ∀ t ∈ Set.Icc (0 : ℝ) N,
      DifferentiableAt ℝ (normalizedPrimeLogWeight N) t := by
    intro t ht
    exact (normalizedPrimeLogWeight_hasDerivAt N hN t ht.1).differentiableAt
  have hfint : IntegrableOn (deriv (normalizedPrimeLogWeight N))
      (Set.Icc (0 : ℝ) N) := by
    have hden : ContinuousOn (fun t : ℝ => t + 1) (Set.Icc 0 N) := by
      fun_prop
    have hden_ne : ∀ t ∈ Set.Icc (0 : ℝ) N, t + 1 ≠ 0 := by
      intro t ht
      rcases ht with ⟨ht0, _⟩
      linarith
    have hrecip : ContinuousOn (fun t : ℝ => 1 / (t + 1))
        (Set.Icc (0 : ℝ) N) := continuousOn_const.div hden hden_ne
    have hreal : ContinuousOn
        (fun t : ℝ => (1 / (t + 1)) / Real.log ((N : ℝ) + 1))
        (Set.Icc (0 : ℝ) N) := hrecip.div_const _
    have hcomplex : ContinuousOn
        (fun t : ℝ => (((1 / (t + 1)) / Real.log ((N : ℝ) + 1) : ℝ) : ℂ))
        (Set.Icc (0 : ℝ) N) := by
      simpa only [Function.comp_def] using
        Continuous.comp_continuousOn' Complex.continuous_ofReal hreal
    have hcontInt : IntegrableOn
        (fun t : ℝ => (((1 / (t + 1)) / Real.log ((N : ℝ) + 1) : ℝ) : ℂ))
        (Set.Icc (0 : ℝ) N) volume := hcomplex.integrableOn_Icc
    apply hcontInt.congr_fun
    · intro t ht
      exact (normalizedPrimeLogWeight_hasDerivAt N hN t ht.1).deriv.symm
    · exact measurableSet_Icc
  have hfN : ‖normalizedPrimeLogWeight N N‖ ≤ 1 := by
    rw [normalizedPrimeLogWeight, normalizedPrimeLogWeightReal]
    have hnum : Real.log ((N : ℝ) + 1) ≠ 0 := hD.ne'
    rw [div_self hnum]
    norm_num
  have hvariation :
      (∫ t in Set.Ioc (0 : ℝ) N,
        ‖deriv (normalizedPrimeLogWeight N) t‖) ≤ 1 := by
    have hderivEq (t : ℝ) (ht : 0 ≤ t) :
        deriv (normalizedPrimeLogWeight N) t =
          ((((1 / (t + 1)) / D : ℝ) : ℂ)) := by
      simpa [D] using (normalizedPrimeLogWeight_hasDerivAt N hN t ht).deriv
    have hnonneg : ∀ t ∈ Set.Ioc (0 : ℝ) N,
        0 ≤ deriv (normalizedPrimeLogWeightReal N) t := by
      intro t ht
      rw [(normalizedPrimeLogWeightReal_hasDerivAt N hN t ht.1.le).deriv]
      have htpos : 0 < t + 1 := by linarith [ht.1]
      positivity
    have hIntMem := MonotoneOn.intervalIntegral_deriv_mem_uIcc hmono
    have hDedge : normalizedPrimeLogWeightReal N N = 1 := by
      unfold normalizedPrimeLogWeightReal
      exact div_self hD.ne'
    have hF0 : 0 ≤ normalizedPrimeLogWeightReal N 0 := by
      unfold normalizedPrimeLogWeightReal
      apply div_nonneg
      · exact Real.log_nonneg (by norm_num)
      · exact le_of_lt hD
    have hIntLe :
        (∫ t in (0 : ℝ)..N, deriv (normalizedPrimeLogWeightReal N) t) ≤ 1 := by
      have hfdiff : 0 ≤ normalizedPrimeLogWeightReal N N -
          normalizedPrimeLogWeightReal N 0 := by
        apply sub_nonneg.mpr
        exact hmono (by simp) (by simp) hN0
      have hmem :
          (∫ t in (0 : ℝ)..N, deriv (normalizedPrimeLogWeightReal N) t) ∈
            Set.Icc 0 (normalizedPrimeLogWeightReal N N -
              normalizedPrimeLogWeightReal N 0) := by
        simpa [Set.uIcc_of_le hfdiff] using hIntMem
      rw [hDedge] at hmem
      exact (hmem.2.trans (by linarith :
        1 - normalizedPrimeLogWeightReal N 0 ≤ 1))
    have hfund :
        (∫ t in Set.Ioc (0 : ℝ) N,
          deriv (normalizedPrimeLogWeightReal N) t) =
            ∫ t in (0 : ℝ)..N,
              deriv (normalizedPrimeLogWeightReal N) t := by
      rw [← intervalIntegral.integral_of_le hN0]
    have hnorm : ∀ t ∈ Set.Ioc (0 : ℝ) N,
        ‖deriv (normalizedPrimeLogWeight N) t‖ =
          deriv (normalizedPrimeLogWeightReal N) t := by
      intro t ht
      rw [hderivEq t ht.1.le,
        (normalizedPrimeLogWeightReal_hasDerivAt N hN t ht.1.le).deriv]
      rw [Complex.norm_real, Real.norm_eq_abs]
      have hpos : 0 ≤ (1 / (t + 1)) / D := by
        apply div_nonneg
        · apply div_nonneg (by norm_num) (by linarith [ht.1])
        · exact le_of_lt hD
      rw [abs_of_nonneg hpos]
    calc
      (∫ t in Set.Ioc (0 : ℝ) N,
          ‖deriv (normalizedPrimeLogWeight N) t‖) =
          ∫ t in Set.Ioc (0 : ℝ) N,
            deriv (normalizedPrimeLogWeightReal N) t := by
              apply setIntegral_congr_fun
              · exact measurableSet_Ioc
              · exact hnorm
      _ = ∫ t in (0 : ℝ)..N,
            deriv (normalizedPrimeLogWeightReal N) t := hfund
      _ ≤ 1 := hIntLe
  have habel := norm_sum_mul_le_partialSumBound_mul_one_add_integral_norm_deriv
    c (f := normalizedPrimeLogWeight N) N hN hDelta hfdiff hfint hfN hpartial
  have hweighted :
      (∑ k ∈ Icc 0 N,
        (Real.log ((k : ℝ) + 1) : ℂ) * c k) =
          (D : ℂ) *
            ∑ k ∈ Icc 0 N, normalizedPrimeLogWeight N k * c k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    simp only [normalizedPrimeLogWeight, normalizedPrimeLogWeightReal]
    push_cast
    have hDne : D ≠ 0 := hD.ne'
    simp only [D]
    field_simp [D, hDne]
  rw [hweighted, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hD]
  calc
    D * ‖∑ k ∈ Icc 0 N,
        normalizedPrimeLogWeight N k * c k‖ ≤
        D * (Delta * (1 +
          ∫ t in Set.Ioc (0 : ℝ) N,
            ‖deriv (normalizedPrimeLogWeight N) t‖)) :=
          mul_le_mul_of_nonneg_left habel (le_of_lt hD)
    _ ≤ D * (Delta * 2) := by
      have hfactor :
          1 + (∫ t in Set.Ioc (0 : ℝ) N,
            ‖deriv (normalizedPrimeLogWeight N) t‖) ≤ 2 := by linarith
      have := mul_le_mul_of_nonneg_left hfactor hDelta
      nlinarith [mul_le_mul_of_nonneg_left this (le_of_lt hD)]
    _ = 2 * Delta * D := by ring

end CookMagyarMajorArc
end SystolicGrowth

#print axioms SystolicGrowth.CookMagyarMajorArc.norm_sum_addChar_primeCubic_le_partialSumBound_of_scaledError
#print axioms SystolicGrowth.CookMagyarMajorArc.addChar_primeCubic_eq_cubicAbelWeight_mul_rational
#print axioms SystolicGrowth.CookMagyarMajorArc.norm_sum_addChar_wrapped_le_of_rationalPartialSums
#print axioms SystolicGrowth.CookMagyarMajorArc.norm_sum_affineCubicAbelWeight_mul_le_partialSumBound_of_scaledError
#print axioms SystolicGrowth.CookMagyarMajorArc.norm_sum_log_mul_le_of_partialSumBound
