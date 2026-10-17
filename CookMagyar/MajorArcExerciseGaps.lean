module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.APCharacterBridge
public import CookMagyar.MajorArcConcreteError
public import CookMagyar.ArchimedeanFourierBridge
public import CookMagyar.MainLowerInterface
public import CookMagyar.PerronOscillatoryKernel
public import CookMagyar.PerronHalfIntegerHarmonic
public import CookMagyar.PerronScalarContour
public import CookMagyar.PerronCoefficientSeries
public import CookMagyar.PerronSeriesExchange
public import CookMagyar.PerronFarCoefficient
public import CookMagyar.PerronResidueJump
public import CookMagyar.PerronLogDerivativeResidues
public import CookMagyar.PerronPrincipalContour
public import CookMagyar.PerronSimpleZeroContour
public import CookMagyar.SiegelUniformLower
public import CookMagyar.DirichletLocalZeros
public import CookMagyar.DirichletZeroAvoidingHeight
public import CookMagyar.DirichletLocalFactorization
public import CookMagyar.DirichletLogDerivativePositivity
public import CookMagyar.ZetaLogDerivativeNearOne
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Vendored.PrimeNumberTheoremAnd.StrongPNT

@[expose] public section

/-!
# Major-arc exercises, in dependency order

MA01 is proved by the named finite-to-series helpers below. MA02 is proved by
the actual Estermann--Siegel argument and the real-zero derivative adapter.
MA03 is proved from the actual character zero-free regions, selected contour,
uniform edge payment and conductor transfer. MA05 onward assemble these
proved inputs into the all-residue AP and uniform major-arc estimates.
The local source is Montgomery--Vaughan, *Multiplicative Number Theory I*,
§11, especially Corollaries 11.15, 11.18, 11.19 (printed pp. 378--381; local
scan pp. 397--400). The precise contour choices are in
`PROOF_STRATEGY_REVIEW.md` §23. Ask for missing reference pages.

Do not make `A = 40` a proof assumption. The major-arc theorem below works
for **every fixed positive cutoff exponent**. With the coarse existing
center-count bound, the AP term loses at most `Q^5`; requesting an AP saving
`B = 5*A+2` suffices. A direct product estimate based on the weaker
`|sum| ≤ N*log(N+2)` would instead spend an additional `n-1` logarithms;
this file uses the already proved Chebyshev bound in `MajorArcConcreteError`
and therefore does not make that unnecessary loss.
-/

open Filter MeasureTheory Finset
open scoped BigOperators Topology Interval
open scoped Classical

namespace SystolicGrowth.CookMagyarCircle

open CookMagyarArcs CookMagyarMajorArc CookMagyarFiniteFourier CookMagyarReal

/-- The single logarithm used in all numerical budgets in this file. -/
noncomputable def exerciseMajorLog (N : ℕ) : ℝ := Real.log ((N : ℝ) + 2)

/-- Finite twisted von Mangoldt mass, with the repository's inclusive endpoint. -/
noncomputable def exerciseTwistedPsi (q : ℕ)
    (χ : DirichletCharacter ℂ q) (m : ℕ) : ℂ :=
  ∑ k ∈ Icc 0 m, χ k * (ArithmeticFunction.vonMangoldt k : ℂ)

/-- Half-integer endpoint: it counts exactly the integers in `Icc 0 m`. -/
noncomputable def exercisePerronEndpoint (m : ℕ) : ℝ := (m : ℝ) + 1 / 2

/-- The vertical line of absolute convergence for truncated Perron. -/
noncomputable def exercisePerronAbscissa (m : ℕ) : ℝ :=
  1 + (exerciseMajorLog m)⁻¹

/- TASK-SLOT PERRON-POSITIVE-SUM (COMPLETE): P09 is proved below. -/

/-- Remove the zero von Mangoldt coefficient while preserving the inclusive
upper endpoint of the twisted sum. -/
theorem exerciseTwistedPsi_eq_sum_positive
    (q : ℕ) (χ : DirichletCharacter ℂ q) (m : ℕ) :
    exerciseTwistedPsi q χ m =
      ∑ k ∈ Finset.range m,
        χ (k + 1) * (ArithmeticFunction.vonMangoldt (k + 1) : ℂ) := by
  unfold exerciseTwistedPsi
  rw [← Nat.range_succ_eq_Icc_zero m, Finset.sum_range_succ']
  simp only [ArithmeticFunction.map_zero, Complex.ofReal_zero, mul_zero, add_zero,
    Nat.cast_add, Nat.cast_one]

/-- The modulus-one principal-character sum is exactly Chebyshev's ψ. This
normalization bridge lets the imported strong PNT feed the principal lane of
MA03 without changing its finite-sum convention. -/
theorem exercisePrincipalTwistedPsi_eq_chebyshevPsi (m : ℕ) :
    exerciseTwistedPsi 1 (1 : DirichletCharacter ℂ 1) m =
      (_root_.ChebyshevPsi (m : ℝ) : ℂ) := by
  rw [exerciseTwistedPsi, _root_.ChebyshevPsi, Chebyshev.psi_eq_sum_Icc]
  rw [Nat.floor_natCast]
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [MulChar.one_apply (isUnit_of_subsingleton _), one_mul]

/-- The imported strong PNT supplies the required root-log error for the
modulus-one principal-character finite sum. -/
theorem exercise_principalTwistedPsi_strongPNT :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ᶠ m : ℕ in atTop,
        ‖exerciseTwistedPsi 1 (1 : DirichletCharacter ℂ 1) m - (m : ℂ)‖ ≤
          C * (m : ℝ) * Real.exp (-c * Real.sqrt (Real.log (m : ℝ))) := by
  obtain ⟨c, hc, hStrong⟩ := StrongPNT
  obtain ⟨C, hC⟩ := hStrong.bound
  have hNat := tendsto_natCast_atTop_atTop.eventually hC
  refine ⟨|C| + 1, c, by positivity, hc, ?_⟩
  filter_upwards [hNat, Filter.eventually_ge_atTop 2] with m hm hm2
  have hmPos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hReal :
      ‖_root_.ChebyshevPsi (m : ℝ) - (m : ℝ)‖ ≤
        C * ((m : ℝ) * Real.exp (-c * Real.sqrt (Real.log (m : ℝ)))) := by
    simpa [Pi.sub_apply, id_eq, Real.norm_eq_abs, Real.sqrt_eq_rpow,
      abs_of_nonneg (by positivity : 0 ≤ (m : ℝ) *
        Real.exp (-c * Real.sqrt (Real.log (m : ℝ))))] using hm
  calc
    ‖exerciseTwistedPsi 1 (1 : DirichletCharacter ℂ 1) m - (m : ℂ)‖ =
        ‖_root_.ChebyshevPsi (m : ℝ) - (m : ℝ)‖ := by
          rw [exercisePrincipalTwistedPsi_eq_chebyshevPsi]
          rw [show (m : ℂ) = ((m : ℝ) : ℂ) by norm_cast,
            ← Complex.ofReal_sub, Complex.norm_real]
    _ ≤ C * ((m : ℝ) * Real.exp (-c * Real.sqrt (Real.log (m : ℝ)))) := hReal
    _ ≤ (|C| + 1) * ((m : ℝ) * Real.exp (-c * Real.sqrt (Real.log (m : ℝ)))) :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) (by positivity)
    _ = _ := by ring


/-- The actual half-integer Perron contour lies in the quantitative
coefficient-series range for every endpoint used by MA01. -/
theorem exercisePerronAbscissa_bounds (m : ℕ) (hm : 2 ≤ m) :
    1 < exercisePerronAbscissa m ∧ exercisePerronAbscissa m ≤ 2 := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    exact h
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    have h : Real.log (2 * 2 : ℝ) = Real.log 2 + Real.log 2 :=
      Real.log_mul (by norm_num) (by norm_num)
    norm_num only at h
    linarith
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : 1 ≤ exerciseMajorLog m := by
    dsimp [exerciseMajorLog]
    exact hlog4.trans (Real.log_le_log (by norm_num) (by linarith))
  have hpos : 0 < exerciseMajorLog m := by linarith
  have hinv : 0 < (exerciseMajorLog m)⁻¹ := inv_pos.mpr hpos
  have hinv_le : (exerciseMajorLog m)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlog
  constructor <;> dsimp [exercisePerronAbscissa] <;> linarith

/-- On the absolute-convergence half-plane, the analytic `LFunction` has
the twisted von Mangoldt L-series as its negative logarithmic derivative. -/
theorem negative_logDeriv_LFunction_eq_twisted_LSeries
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 1 < s.re) :
    -deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s =
      LSeries (fun k : ℕ => χ k * (ArithmeticFunction.vonMangoldt k : ℂ)) s := by
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  simpa only [Pi.mul_def] using
    (DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs).symm

/-- An explicit vertical-line Perron integral, including its `1/(2π)` factor.
Its parameterization contributes `ds = i dt`, canceling Perron's `i`.
The principal pole and any exceptional zero are handled in MA02--MA04. -/
noncomputable def exercisePerronIntegral (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (m : ℕ) (H : ℝ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ *
    ∫ t in (-H)..H,
      let s : ℂ := (exercisePerronAbscissa m : ℂ) + Complex.I * (t : ℂ)
      (-deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) *
          (exercisePerronEndpoint m : ℂ) ^ s / s

/-- The explicit exercise integral uses exactly the weighted logarithmic
derivative whose local residues are proved in `PerronLogDerivativeResidues`. -/
theorem exercisePerronIntegral_eq_logDerivativeIntegrand
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (m : ℕ) (H : ℝ) :
    exercisePerronIntegral q χ m H =
      (2 * Real.pi : ℂ)⁻¹ *
        ∫ t in -H..H, perronLogDerivativeIntegrand q χ
          (exercisePerronEndpoint m)
          ((exercisePerronAbscissa m : ℂ) + Complex.I * (t : ℂ)) := rfl

/-- The exercise's analytic logarithmic-derivative integral expands into
the absolutely convergent coefficient-weighted scalar Perron integrals. -/
theorem exercisePerronIntegral_eq_tsum (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (m : ℕ) (H : ℝ)
    (hm : 2 ≤ m) (hH : 0 ≤ H) :
    exercisePerronIntegral q χ m H =
      (2 * Real.pi : ℂ)⁻¹ *
        ∑' k : ℕ, (χ (k + 1) * (ArithmeticFunction.vonMangoldt (k + 1) : ℂ)) *
          (∫ t in -H..H,
            perronScalarKernel (exercisePerronEndpoint m) (k + 1)
              (exercisePerronAbscissa m) t) := by
  obtain ⟨hσ, hσ₂⟩ := exercisePerronAbscissa_bounds m hm
  have hx : 0 < exercisePerronEndpoint m := by
    dsimp [exercisePerronEndpoint]
    positivity
  unfold exercisePerronIntegral
  congr 1
  have hpoint (t : ℝ) :
      -deriv (DirichletCharacter.LFunction χ)
          ((exercisePerronAbscissa m : ℂ) + Complex.I * (t : ℂ)) /
        DirichletCharacter.LFunction χ
          ((exercisePerronAbscissa m : ℂ) + Complex.I * (t : ℂ)) =
      LSeries (fun k : ℕ => χ k * (ArithmeticFunction.vonMangoldt k : ℂ))
        ((exercisePerronAbscissa m : ℂ) + Complex.I * (t : ℂ)) := by
    exact negative_logDeriv_LFunction_eq_twisted_LSeries q χ _ (by simpa using hσ)
  simp_rw [hpoint]
  exact integral_twisted_LSeries_perron_eq_tsum q χ
    (exercisePerronEndpoint m) (exercisePerronAbscissa m) H hx hσ hσ₂ hH

/- TASK-SLOT PERRON-WEIGHTED-ERROR (COMPLETE): P12 is proved below. -/

/-- Character weights and the Perron normalization preserve the universal
finite middle/far remainder budget. -/
theorem sum_twisted_normalized_perron_error_le
    (q : ℕ) (χ : DirichletCharacter ℂ q) (m : ℕ) (s : Finset ℕ) (σ H : ℝ)
    (hσ : 1 < σ) (hσ₂ : σ ≤ 2) (hH : 0 < H)
    (hkpos : ∀ k ∈ s, 0 < k) :
    (∑ k ∈ s, ‖(χ k * (ArithmeticFunction.vonMangoldt k : ℂ)) *
      ((if k ≤ m then (1 : ℂ) else 0) -
        (2 * Real.pi : ℂ)⁻¹ *
          (∫ t in -H..H, perronScalarKernel ((m : ℝ) + 1 / 2) k σ t))‖) ≤
      (2 * Real.pi)⁻¹ *
        (3456 * ((m : ℝ) + 1 / 2) * Real.log ((m : ℝ) + 2) ^ 2 / H +
          216 * ((m : ℝ) + 1 / 2) ^ σ / (H * (σ - 1) ^ 2)) := by
  have hpiR : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpiR.ne'
  have hnorm : ‖(2 * Real.pi : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    have hcast : (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast]
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpiR]
  have hpoint (k : ℕ) (hk : k ∈ s) :
      ‖(χ k * (ArithmeticFunction.vonMangoldt k : ℂ)) *
        ((if k ≤ m then (1 : ℂ) else 0) -
          (2 * Real.pi : ℂ)⁻¹ *
            (∫ t in -H..H, perronScalarKernel ((m : ℝ) + 1 / 2) k σ t))‖ ≤
        (2 * Real.pi)⁻¹ * (ArithmeticFunction.vonMangoldt k *
          ‖(((((m : ℝ) + 1 / 2) / (k : ℝ)) ^ σ : ℝ) : ℂ) *
              perronPhaseContourLimit σ (Real.log (((m : ℝ) + 1 / 2) / (k : ℝ))) -
            ∫ t in -H..H, perronScalarKernel ((m : ℝ) + 1 / 2) k σ t‖) := by
    let A : ℂ := (((((m : ℝ) + 1 / 2) / (k : ℝ)) ^ σ : ℝ) : ℂ) *
      perronPhaseContourLimit σ (Real.log (((m : ℝ) + 1 / 2) / (k : ℝ)))
    have hA : A = if k ≤ m then (2 * Real.pi : ℂ) else 0 :=
      perronHalfInteger_amplitude_mul_contourLimit m k σ (hkpos k hk) (by linarith)
    have hindicator : (if k ≤ m then (1 : ℂ) else 0) =
        (2 * Real.pi : ℂ)⁻¹ * A := by
      rw [hA]
      by_cases hkm : k ≤ m
      · simp only [if_pos hkm]
        exact (inv_mul_cancel₀ hpi).symm
      · simp only [if_neg hkm, mul_zero]
    have ha : ‖χ k * (ArithmeticFunction.vonMangoldt k : ℂ)‖ ≤
        ArithmeticFunction.vonMangoldt k := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (χ.norm_le_one k)
        (ArithmeticFunction.vonMangoldt_nonneg (n := k))
    have hbracket : ‖(2 * Real.pi : ℂ)⁻¹ * (A -
        ∫ t in -H..H, perronScalarKernel ((m : ℝ) + 1 / 2) k σ t)‖ =
        (2 * Real.pi)⁻¹ * ‖A -
          ∫ t in -H..H, perronScalarKernel ((m : ℝ) + 1 / 2) k σ t‖ := by
      rw [norm_mul, hnorm]
    rw [hindicator, ← mul_sub, norm_mul, hbracket]
    calc
      _ ≤ ArithmeticFunction.vonMangoldt k *
          ((2 * Real.pi)⁻¹ * ‖A -
            ∫ t in -H..H, perronScalarKernel ((m : ℝ) + 1 / 2) k σ t‖) :=
        mul_le_mul_of_nonneg_right ha (by positivity)
      _ = _ := by dsimp [A]; ring
  calc
    _ ≤ ∑ k ∈ s, (2 * Real.pi)⁻¹ * (ArithmeticFunction.vonMangoldt k *
      ‖(((((m : ℝ) + 1 / 2) / (k : ℝ)) ^ σ : ℝ) : ℂ) *
          perronPhaseContourLimit σ (Real.log (((m : ℝ) + 1 / 2) / (k : ℝ))) -
        ∫ t in -H..H, perronScalarKernel ((m : ℝ) + 1 / 2) k σ t‖) :=
      sum_le_sum hpoint
    _ = (2 * Real.pi)⁻¹ * ∑ k ∈ s, ArithmeticFunction.vonMangoldt k *
      ‖(((((m : ℝ) + 1 / 2) / (k : ℝ)) ^ σ : ℝ) : ℂ) *
          perronPhaseContourLimit σ (Real.log (((m : ℝ) + 1 / 2) / (k : ℝ))) -
        ∫ t in -H..H, perronScalarKernel ((m : ℝ) + 1 / 2) k σ t‖ :=
      (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_perronScalarKernel_truncation_error_le m s σ H hσ hσ₂ hH hkpos)
      (inv_nonneg.mpr hpiR.le)

/- TASK-SLOT PERRON-FINAL-ASSEMBLY: transparent positive-index terms and
proved numerical/finite-to-series helpers for MA01; see SMALL_LEMMA_TASKS.md. -/

/-- Convert the finite middle/far budget to a universal `m*log²(m+2)/H` bound. -/
theorem exercisePerron_budget_le (m : ℕ) (H : ℝ) (hm : 2 ≤ m) (hH : 0 < H) :
    (2 * Real.pi)⁻¹ *
        (3456 * exercisePerronEndpoint m * exerciseMajorLog m ^ 2 / H +
          216 * exercisePerronEndpoint m ^ (exercisePerronAbscissa m) /
            (H * (exercisePerronAbscissa m - 1) ^ 2)) ≤
      (2 * (3456 + 216 * Real.exp 1)) *
        ((m : ℝ) * exerciseMajorLog m ^ 2 / H) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hx : 0 < exercisePerronEndpoint m := by
    dsimp [exercisePerronEndpoint]
    positivity
  have hxy : exercisePerronEndpoint m ≤ (m : ℝ) + 2 := by
    dsimp [exercisePerronEndpoint]
    linarith
  have hy : (1 : ℝ) < (m : ℝ) + 2 := by linarith
  have hamp : exercisePerronEndpoint m ^ exercisePerronAbscissa m ≤
      Real.exp 1 * exercisePerronEndpoint m := by
    simpa only [exercisePerronAbscissa, exerciseMajorLog] using
      perron_rpow_one_add_inv_log_le (exercisePerronEndpoint m) ((m : ℝ) + 2)
        hx hxy hy
  have habscissa : exercisePerronAbscissa m - 1 = (exerciseMajorLog m)⁻¹ := by
    simp [exercisePerronAbscissa]
  have hden :
      216 * exercisePerronEndpoint m ^ exercisePerronAbscissa m /
          (H * (exercisePerronAbscissa m - 1) ^ 2) =
        216 * exercisePerronEndpoint m ^ exercisePerronAbscissa m *
          exerciseMajorLog m ^ 2 / H := by
    rw [habscissa]
    simp only [inv_pow, div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  rw [hden]
  have hinnerNonneg :
      0 ≤ 3456 * exercisePerronEndpoint m * exerciseMajorLog m ^ 2 / H +
        216 * exercisePerronEndpoint m ^ exercisePerronAbscissa m *
          exerciseMajorLog m ^ 2 / H := by positivity
  have hpi : (2 * Real.pi)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by have h := Real.one_le_pi_div_two; linarith)
  have hendpoint : exercisePerronEndpoint m ≤ 2 * (m : ℝ) := by
    dsimp [exercisePerronEndpoint]
    linarith
  calc
    _ ≤ 3456 * exercisePerronEndpoint m * exerciseMajorLog m ^ 2 / H +
        216 * exercisePerronEndpoint m ^ exercisePerronAbscissa m *
          exerciseMajorLog m ^ 2 / H := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hpi hinnerNonneg
    _ ≤ 3456 * exercisePerronEndpoint m * exerciseMajorLog m ^ 2 / H +
        216 * (Real.exp 1 * exercisePerronEndpoint m) *
          exerciseMajorLog m ^ 2 / H := by
      gcongr
    _ = (3456 + 216 * Real.exp 1) * exercisePerronEndpoint m *
        exerciseMajorLog m ^ 2 / H := by ring
    _ ≤ (3456 + 216 * Real.exp 1) * (2 * (m : ℝ)) *
        exerciseMajorLog m ^ 2 / H := by
      gcongr
    _ = _ := by ring

/-- The positive-index finite indicator part of the Perron remainder. -/
noncomputable def exercisePerronIndicatorTerm (q : ℕ)
    (χ : DirichletCharacter ℂ q) (m j : ℕ) : ℂ :=
  (χ (j + 1) * (ArithmeticFunction.vonMangoldt (j + 1) : ℂ)) *
    (if j + 1 ≤ m then 1 else 0)

/-- The positive-index coefficient-weighted, unnormalized scalar integral. -/
noncomputable def exercisePerronIntegralTerm (q : ℕ)
    (χ : DirichletCharacter ℂ q) (m : ℕ) (H : ℝ) (j : ℕ) : ℂ :=
  (χ (j + 1) * (ArithmeticFunction.vonMangoldt (j + 1) : ℂ)) *
    (∫ t in -H..H, perronScalarKernel (exercisePerronEndpoint m) (j + 1)
      (exercisePerronAbscissa m) t)

/-- The difference between the indicator term and the normalized integral term. -/
noncomputable def exercisePerronRemainderTerm (q : ℕ)
    (χ : DirichletCharacter ℂ q) (m : ℕ) (H : ℝ) (j : ℕ) : ℂ :=
  exercisePerronIndicatorTerm q χ m j -
    (2 * Real.pi : ℂ)⁻¹ * exercisePerronIntegralTerm q χ m H j

/-- The scalar finite error estimate transfers to arbitrary shifted index sets. -/
theorem sum_exercisePerron_remainder_norm_le
    (q : ℕ) (χ : DirichletCharacter ℂ q) (m : ℕ) (H : ℝ)
    (hm : 2 ≤ m) (hH : 0 < H) (u : Finset ℕ) :
    (∑ j ∈ u, ‖exercisePerronRemainderTerm q χ m H j‖) ≤
      (2 * Real.pi)⁻¹ *
        (3456 * exercisePerronEndpoint m * exerciseMajorLog m ^ 2 / H +
          216 * exercisePerronEndpoint m ^ exercisePerronAbscissa m /
            (H * (exercisePerronAbscissa m - 1) ^ 2)) := by
  classical
  obtain ⟨hσ, hσ₂⟩ := exercisePerronAbscissa_bounds m hm
  have hkpos : ∀ k ∈ u.image (fun j => j + 1), 0 < k := by
    intro k hk
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
    omega
  have h := sum_twisted_normalized_perron_error_le q χ m
    (u.image (fun j => j + 1)) (exercisePerronAbscissa m) H hσ hσ₂ hH hkpos
  rw [Finset.sum_image (by intro a _ b _ hab; dsimp only at hab; omega)] at h
  have hterm (j : ℕ) : exercisePerronRemainderTerm q χ m H j =
      (χ (j + 1) * (ArithmeticFunction.vonMangoldt (j + 1) : ℂ)) *
        ((if j + 1 ≤ m then (1 : ℂ) else 0) -
          (2 * Real.pi : ℂ)⁻¹ *
            (∫ t in -H..H, perronScalarKernel (exercisePerronEndpoint m) (j + 1)
              (exercisePerronAbscissa m) t)) := by
    dsimp [exercisePerronRemainderTerm, exercisePerronIndicatorTerm,
      exercisePerronIntegralTerm]
    ring
  simpa only [hterm, exerciseMajorLog, exercisePerronEndpoint,
    Nat.cast_add, Nat.cast_one] using h

/-- A uniform finite-set budget proves absolute convergence of the remainder. -/
theorem summable_norm_exercisePerron_remainder
    (q : ℕ) (χ : DirichletCharacter ℂ q) (m : ℕ) (H : ℝ)
    (hm : 2 ≤ m) (hH : 0 < H) :
    Summable (fun j : ℕ => ‖exercisePerronRemainderTerm q χ m H j‖) := by
  exact summable_of_sum_le (fun _ => norm_nonneg _)
    (sum_exercisePerron_remainder_norm_le q χ m H hm hH)

/-- The absolutely convergent remainder has the same finite middle/far budget. -/
theorem norm_tsum_exercisePerron_remainder_le
    (q : ℕ) (χ : DirichletCharacter ℂ q) (m : ℕ) (H : ℝ)
    (hm : 2 ≤ m) (hH : 0 < H) :
    ‖∑' j : ℕ, exercisePerronRemainderTerm q χ m H j‖ ≤
      (2 * Real.pi)⁻¹ *
        (3456 * exercisePerronEndpoint m * exerciseMajorLog m ^ 2 / H +
          216 * exercisePerronEndpoint m ^ exercisePerronAbscissa m /
            (H * (exercisePerronAbscissa m - 1) ^ 2)) := by
  exact (norm_tsum_le_tsum_norm
    (summable_norm_exercisePerron_remainder q χ m H hm hH)).trans
      (Real.tsum_le_of_sum_le (fun _ => norm_nonneg _)
        (sum_exercisePerron_remainder_norm_le q χ m H hm hH))

/-- The shifted indicator vanishes outside the prefix of length `m`. -/
theorem indicatorTerm_eq_zero_of_not_mem_range (q : ℕ)
    (χ : DirichletCharacter ℂ q) (m j : ℕ)
    (hj : j ∉ Finset.range m) :
    exercisePerronIndicatorTerm q χ m j = 0 := by
  have hnot : ¬ j + 1 ≤ m := by
    simp only [Finset.mem_range, not_lt] at hj
    omega
  simp [exercisePerronIndicatorTerm, hnot]

/-- Finite support makes the shifted indicator series summable. -/
theorem summable_indicatorTerm (q : ℕ)
    (χ : DirichletCharacter ℂ q) (m : ℕ) :
    Summable (exercisePerronIndicatorTerm q χ m) :=
  summable_of_ne_finset_zero (s := Finset.range m)
    (indicatorTerm_eq_zero_of_not_mem_range q χ m)

/-- The indicator series counts precisely the inclusive twisted sum through `m`. -/
theorem tsum_indicatorTerm_eq_twistedPsi (q : ℕ)
    (χ : DirichletCharacter ℂ q) (m : ℕ) :
    (∑' j : ℕ, exercisePerronIndicatorTerm q χ m j) =
      exerciseTwistedPsi q χ m := by
  rw [tsum_eq_sum (indicatorTerm_eq_zero_of_not_mem_range q χ m),
    exerciseTwistedPsi_eq_sum_positive]
  apply Finset.sum_congr rfl
  intro j hj
  have hle : j + 1 ≤ m := by
    exact Nat.succ_le_of_lt (Finset.mem_range.mp hj)
  simp [exercisePerronIndicatorTerm, hle]

/-- The absolute coefficient bound makes integrated scalar terms summable. -/
theorem summable_integralTerm (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (m : ℕ) (H : ℝ)
    (hm : 2 ≤ m) (hH : 0 ≤ H) :
    Summable (exercisePerronIntegralTerm q χ m H) := by
  obtain ⟨hσ, hσ₂⟩ := exercisePerronAbscissa_bounds m hm
  have hx : 0 < exercisePerronEndpoint m := by
    dsimp [exercisePerronEndpoint]
    positivity
  have ha : Summable (fun k : ℕ =>
      ‖χ ((k + 1 : ℕ) : ZMod q) *
        (ArithmeticFunction.vonMangoldt (k + 1) : ℂ)‖ /
        (((k + 1 : ℕ) : ℝ) ^ exercisePerronAbscissa m)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      summable_twisted_vonMangoldt_rpow_norm q χ
        (exercisePerronAbscissa m) hσ hσ₂
  change Summable (fun k : ℕ =>
    (χ (k + 1) * (ArithmeticFunction.vonMangoldt (k + 1) : ℂ)) *
      (∫ t in -H..H,
        perronScalarKernel (exercisePerronEndpoint m) (k + 1)
          (exercisePerronAbscissa m) t))
  simpa only [Nat.cast_add, Nat.cast_one] using
    summable_integral_perronScalarKernel
      (fun k : ℕ => χ k * (ArithmeticFunction.vonMangoldt k : ℂ))
      (exercisePerronEndpoint m) (exercisePerronAbscissa m) H hx
      (by linarith) hH ha

/-- The difference of the two summable Perron families is summable. -/
theorem summable_remainderTerm (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (m : ℕ) (H : ℝ)
    (hm : 2 ≤ m) (hH : 0 ≤ H) :
    Summable (exercisePerronRemainderTerm q χ m H) := by
  have hI := summable_indicatorTerm q χ m
  have hJ := summable_integralTerm q χ m H hm hH
  exact hI.sub (hJ.mul_left (2 * Real.pi : ℂ)⁻¹)

/-- The remainder series is the actual twisted-sum minus LFunction-integral error. -/
theorem tsum_remainder_eq_twistedPsi_sub_perronIntegral
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (m : ℕ) (H : ℝ) (hm : 2 ≤ m) (hH : 0 ≤ H) :
    (∑' j : ℕ, exercisePerronRemainderTerm q χ m H j) =
      exerciseTwistedPsi q χ m - exercisePerronIntegral q χ m H := by
  have hI := summable_indicatorTerm q χ m
  have hJ := summable_integralTerm q χ m H hm hH
  have hnormJ : Summable (fun j : ℕ =>
      (2 * Real.pi : ℂ)⁻¹ * exercisePerronIntegralTerm q χ m H j) :=
    hJ.mul_left _
  have hJtsum :
      (∑' j : ℕ, (2 * Real.pi : ℂ)⁻¹ *
        exercisePerronIntegralTerm q χ m H j) =
      exercisePerronIntegral q χ m H := by
    rw [(hJ.tsum_mul_left (2 * Real.pi : ℂ)⁻¹)]
    rw [exercisePerronIntegral_eq_tsum q χ m H hm hH]
    congr 1
  calc
    (∑' j : ℕ, exercisePerronRemainderTerm q χ m H j) =
        (∑' j : ℕ, exercisePerronIndicatorTerm q χ m j) -
          (∑' j : ℕ, (2 * Real.pi : ℂ)⁻¹ *
            exercisePerronIntegralTerm q χ m H j) := by
              exact hI.tsum_sub hnormJ
    _ = exerciseTwistedPsi q χ m - exercisePerronIntegral q χ m H := by
      rw [tsum_indicatorTerm_eq_twistedPsi, hJtsum]

/-- Truncated Perron with one explicit constant independent of the modulus
and character, proved from the positive-index remainder series. -/
theorem exercise_truncatedPerron_error_explicit
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (m : ℕ) (H : ℝ)
    (hm : 2 ≤ m) (hH : 0 < H) :
    ‖exerciseTwistedPsi q χ m - exercisePerronIntegral q χ m H‖ ≤
      (2 * (3456 + 216 * Real.exp 1)) *
        ((m : ℝ) * exerciseMajorLog m ^ 2 / H) := by
  rw [← tsum_remainder_eq_twistedPsi_sub_perronIntegral q χ m H hm hH.le]
  exact (norm_tsum_exercisePerron_remainder_le q χ m H hm hH).trans
    (exercisePerron_budget_le m H hm hH)

/-- Pole contribution at `s=1`, before the finite character average. -/
noncomputable def exerciseCharacterPole (q : ℕ)
    (χ : DirichletCharacter ℂ q) (m : ℕ) : ℂ := by
  classical
  exact if χ = 1 then (exercisePerronEndpoint m : ℂ) else 0

/-- MA01 (PROVED): truncated Perron with a half-integer endpoint.

The scalar contour values, weighted finite middle/far budgets, actual
LFunction exchange and absolutely convergent remainder series yield the
explicit universal constant `2*(3456+216*exp 1)`. The fixed contract retains
`H≤m` and its extra `log²(m+2)` allowance; the stronger preceding theorem
does not need either. -/
theorem exercise_truncatedPerron_error :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ (_hq : NeZero q),
      letI : NeZero q := _hq
      ∀ χ : DirichletCharacter ℂ q, ∀ m : ℕ, 2 ≤ m →
        ∀ H : ℝ, 2 ≤ H → H ≤ (m : ℝ) →
          ‖exerciseTwistedPsi q χ m - exercisePerronIntegral q χ m H‖ ≤
            C * ((m : ℝ) * exerciseMajorLog m ^ 2 / H +
              exerciseMajorLog m ^ 2) := by
  refine ⟨2 * (3456 + 216 * Real.exp 1), by positivity, ?_⟩
  intro q hq
  letI : NeZero q := hq
  intro χ m hm H hH _hHm
  have hHpos : 0 < H := by linarith
  calc
    _ ≤ (2 * (3456 + 216 * Real.exp 1)) *
        ((m : ℝ) * exerciseMajorLog m ^ 2 / H) :=
      exercise_truncatedPerron_error_explicit q χ m H hm hHpos
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (sq_nonneg _)) (by positivity)

/-- A precise real-character predicate for the exceptional-zero statements. -/
def exerciseRealCharacter (q : ℕ) (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ r : ZMod q, (χ r).im = 0

/-- Primitive `L`-value with its positive-conductor instance provided locally. -/
noncomputable def exercisePrimitiveLValue (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (β : ℝ) : ℂ := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  exact DirichletCharacter.LFunction χ.primitiveCharacter (β : ℂ)

/-- MA02 (PROVED): Siegel's ineffective lower bound, only for a
nonprincipal primitive real character and a real zero in `(1/2,1)`.

The proof constructs Estermann's positivity estimate, the actual
single-character and four-character products, Siegel's two-case uniform
value bound and the logarithmic-square derivative estimate near `1`. It does not infer a
quantitative rate from qualitative nonvanishing. The constant may depend
on `ε`, but not on the conductor or the zero. This statement is intentionally
separate so the exceptional-zero obligation cannot disappear inside MA03.
Its output plugs into the already proved
`eventually_exceptional_zero_term_le_of_siegel_bound` in
`APCharacterBridge.lean`, with `ε=1/(3*A')` and `A'=2*A+1` after the
`m>sqrt(N)` logarithmic-modulus conversion. -/
theorem exercise_siegel_real_zero_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ (_hq : NeZero q),
      letI : NeZero q := _hq
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
        exerciseRealCharacter q χ → ∀ β : ℝ, 1 / 2 < β → β < 1 →
          DirichletCharacter.LFunction χ (β : ℂ) = 0 →
            C * (q : ℝ) ^ (-ε) ≤ 1 - β := by
  obtain ⟨c, hc, hLower⟩ := exists_siegel_uniform_LFunction_one_lower
    (ε := ε / 2) (by positivity)
  let D : ℝ := 16 * Real.exp 1 * (1 + 2 / (ε / 2)) ^ 2
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨c / D, div_pos hc hD, ?_⟩
  intro q hq
  letI : NeZero q := hq
  intro χ hprim hχ hreal β _hβlo hβhi hzero
  have hvalue := hLower q hq χ hprim hχ hreal
  have h := siegel_real_zero_lower_of_one_norm_lower χ hχ
    (by positivity : 0 < ε / 2) hvalue hβhi hzero
  simpa only [show -2 * (ε / 2) = -ε by ring] using h

/-- Package the previously established horizontal zero-avoidance theorem at
the precise Perron height scale. The explicit room hypotheses are elementary
size conditions; the analytic separation is uniform across the whole fixed
strip and is for every actual zero, not just zeros in a local disk. -/
theorem exists_exercisePerron_zero_avoiding_height
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (m : ℕ) (hbase : 2 ≤ Real.exp (Real.sqrt (exerciseMajorLog m)))
    (hroom : Real.exp (Real.sqrt (exerciseMajorLog m)) + 1 / 4 ≤ (m : ℝ)) :
    ∃ H : ℝ,
      Real.exp (Real.sqrt (exerciseMajorLog m)) ≤ H ∧
      H ≤ 2 * Real.exp (Real.sqrt (exerciseMajorLog m)) ∧
      2 ≤ H ∧ H ≤ (m : ℝ) ∧
      ∀ σ ∈ Set.Icc (9 / 10 : ℝ) (11 / 10), ∀ z : ℂ,
        DirichletCharacter.LFunction χ z = 0 →
          1 / (24 * (Real.log (28 * (q : ℝ) *
            (Real.exp (Real.sqrt (exerciseMajorLog m)) + 2)) /
              Real.log (6 / 5 : ℝ) + 1)) ≤
                ‖((σ : ℂ) + (H : ℂ) * Complex.I) - z‖ := by
  let τ : ℝ := Real.exp (Real.sqrt (exerciseMajorLog m))
  obtain ⟨H, hH, hsep⟩ :=
    exists_dirichlet_zero_avoiding_horizontal_strip χ hχ τ
  refine ⟨H, ?_, ?_, ?_, ?_, ?_⟩
  · exact hH.1
  · have hτ : 0 ≤ τ := by dsimp [τ]; positivity
    have hbase' : 2 ≤ τ := hbase
    calc
      H ≤ τ + 1 / 4 := hH.2
      _ ≤ 2 * τ := by linarith
  · simpa [τ] using hbase.trans hH.1
  · simpa [τ] using hH.2.trans hroom
  · intro σ hσ z hz
    have hsep' := hsep σ hσ z hz
    have hτ : |τ| = τ := abs_of_nonneg (by dsimp [τ]; positivity)
    simpa [τ, hτ] using hsep'

/-- A large prefix has enough room for the safe Perron height, with a strict
additive margin. These are scalar consequences, not new MA03 hypotheses. -/
theorem exercise_perron_height_room (m : ℕ) (hm : 2 ≤ m)
    (hlog : 4 ≤ Real.log (m : ℝ)) :
    2 ≤ Real.exp (Real.sqrt (exerciseMajorLog m)) ∧
      Real.exp (Real.sqrt (exerciseMajorLog m)) + 1 / 4 ≤ (m : ℝ) := by
  let L : ℝ := exerciseMajorLog m
  let H : ℝ := Real.exp (Real.sqrt L)
  have hmTwo : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : 0 < (m : ℝ) := by linarith
  have hL : 0 ≤ L := by
    dsimp [L, exerciseMajorLog]
    exact Real.log_nonneg (by linarith)
  have hlogL : Real.log (m : ℝ) ≤ L := by
    dsimp [L, exerciseMajorLog]
    exact Real.log_le_log hmpos (by linarith)
  have hmsq : (m : ℝ) + 2 ≤ (m : ℝ) ^ 2 := by nlinarith
  have hLUpper : L ≤ 2 * Real.log (m : ℝ) := by
    have h := Real.log_le_log (by positivity : 0 < (m : ℝ) + 2) hmsq
    rw [Real.log_pow] at h
    simpa only [L, exerciseMajorLog, Nat.cast_ofNat] using h
  have hrootMargin : Real.sqrt L ≤ Real.log (m : ℝ) - 1 := by
    rw [Real.sqrt_le_iff]
    constructor <;> nlinarith
  have hHlower : 2 ≤ H := by
    have hroot : 1 ≤ Real.sqrt L := by
      nlinarith [Real.sq_sqrt hL, Real.sqrt_nonneg L]
    have h := Real.add_one_le_exp (Real.sqrt L)
    dsimp [H]
    linarith
  have hHcost : H * Real.exp 1 ≤ (m : ℝ) := by
    calc
      H * Real.exp 1 = Real.exp (Real.sqrt L + 1) := by
        dsimp [H]
        rw [Real.exp_add]
      _ ≤ Real.exp (Real.log (m : ℝ)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := Real.exp_log hmpos
  have hexpTwo : 2 ≤ Real.exp (1 : ℝ) := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  refine ⟨hHlower, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hexpTwo (by dsimp [H]; positivity : 0 ≤ H)
  change H + 1 / 4 ≤ (m : ℝ)
  nlinarith

/-- One ambient threshold supplies every numerical room condition for all
prefixes above its square root, before choosing the modulus or character. -/
theorem exercise_eventually_perron_prefix_room :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, Real.sqrt (N : ℝ) < (m : ℝ) →
      2 ≤ m ∧ 10 ≤ exerciseMajorLog m ∧
      2 ≤ Real.exp (Real.sqrt (exerciseMajorLog m)) ∧
      Real.exp (Real.sqrt (exerciseMajorLog m)) + 1 / 4 ≤ (m : ℝ) := by
  have harg : Tendsto (fun m : ℕ => (m : ℝ) + 2) atTop atTop := by
    exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hlog : Tendsto exerciseMajorLog atTop atTop :=
    Real.tendsto_log_atTop.comp harg
  have hlogNat : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hgood : ∀ᶠ m : ℕ in atTop,
      2 ≤ m ∧ 10 ≤ exerciseMajorLog m ∧
      2 ≤ Real.exp (Real.sqrt (exerciseMajorLog m)) ∧
      Real.exp (Real.sqrt (exerciseMajorLog m)) + 1 / 4 ≤ (m : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), hlog.eventually_ge_atTop 10,
      hlogNat.eventually_ge_atTop 4] with m hm hLm hlogm
    exact ⟨hm, hLm, exercise_perron_height_room m hm hlogm⟩
  obtain ⟨M, hM⟩ := eventually_atTop.1 hgood
  have hroot : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hroot.eventually_ge_atTop (M : ℝ)] with N hN
  intro m hm
  have hMm : M ≤ m := by exact_mod_cast hN.trans hm.le
  exact hM m hMm

#print axioms exercise_eventually_perron_prefix_room

/-- One height is safe for both nonprincipal horizontal edges. All room
conditions are discharged before the modulus, character and prefix are chosen. -/
theorem exercise_eventually_exists_perron_zero_avoiding_edges :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, ∀ (_hq : NeZero q),
      letI : NeZero q := _hq
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ m : ℕ,
        Real.sqrt (N : ℝ) < (m : ℝ) →
          ∃ H : ℝ,
            Real.exp (Real.sqrt (exerciseMajorLog m)) ≤ H ∧
            H ≤ 2 * Real.exp (Real.sqrt (exerciseMajorLog m)) ∧
            2 ≤ H ∧ H ≤ (m : ℝ) ∧
            ∀ σ ∈ Set.Icc (9 / 10 : ℝ) (11 / 10), ∀ z : ℂ,
              DirichletCharacter.LFunction χ z = 0 →
                1 / (48 * (Real.log (28 * (q : ℝ) *
                  (Real.exp (Real.sqrt (exerciseMajorLog m)) + 2)) /
                    Real.log (6 / 5 : ℝ) + 1)) ≤
                      ‖((σ : ℂ) + (H : ℂ) * Complex.I) - z‖ ∧
                1 / (48 * (Real.log (28 * (q : ℝ) *
                  (Real.exp (Real.sqrt (exerciseMajorLog m)) + 2)) /
                    Real.log (6 / 5 : ℝ) + 1)) ≤
                      ‖((σ : ℂ) - (H : ℂ) * Complex.I) - z‖ := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hgood : ∀ᶠ m : ℕ in atTop, 2 ≤ m ∧ 4 ≤ Real.log (m : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), hlog.eventually_ge_atTop 4]
      with m hm hlogm
    exact ⟨hm, hlogm⟩
  obtain ⟨M, hM⟩ := eventually_atTop.1 hgood
  have hroot : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hroot.eventually_ge_atTop (M : ℝ)] with N hN
  intro q hq
  letI : NeZero q := hq
  intro χ hχ m hm
  have hmM : M ≤ m := by exact_mod_cast hN.trans hm.le
  obtain ⟨hmTwo, hlogm⟩ := hM m hmM
  obtain ⟨hbase, hroom⟩ := exercise_perron_height_room m hmTwo hlogm
  obtain ⟨H, hH, hsep⟩ := exists_dirichlet_zero_avoiding_horizontal_edges χ hχ
    (Real.exp (Real.sqrt (exerciseMajorLog m)))
  refine ⟨H, hH.1, ?_, hbase.trans hH.1, hH.2.trans hroom, ?_⟩
  · linarith [hH.2]
  · intro σ hσ z hz
    simpa only [abs_of_pos (Real.exp_pos _)] using hsep σ hσ z hz

open Metric Set in
private theorem horizontal_strip_mem_closedBall
    (τ H σ : ℝ) (hδ : |H - τ| ≤ 1 / 4)
    (hσ : σ ∈ Icc (9 / 10 : ℝ) (11 / 10)) :
    (σ : ℂ) + (H : ℂ) * Complex.I ∈
      closedBall (2 + (τ : ℂ) * Complex.I) (6 / 5 : ℝ) := by
  rw [mem_closedBall, dist_eq_norm]
  let s : ℂ := (σ : ℂ) + (H : ℂ) * Complex.I -
    (2 + (τ : ℂ) * Complex.I)
  have hre : s.re = σ - 2 := by simp [s]
  have him : s.im = H - τ := by simp [s]
  have hresq : (σ - 2) ^ 2 ≤ (121 / 100 : ℝ) := by
    nlinarith [hσ.1, hσ.2]
  have himsq : (H - τ) ^ 2 ≤ (1 / 16 : ℝ) := by
    have hsq := (sq_le_sq₀ (abs_nonneg (H - τ)) (by norm_num : (0 : ℝ) ≤ 1 / 4)).mpr hδ
    norm_num [sq_abs] at hsq
    exact hsq
  have hnormsq : ‖s‖ ^ 2 ≤ (6 / 5 : ℝ) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
    nlinarith
  change ‖s‖ ≤ 6 / 5
  nlinarith [norm_nonneg s]


open Metric Set in
private theorem norm_local_logDeriv_le_of_divisor_norm_bound
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (τ : ℝ)
    {s : ℂ} (hs : s ∈ closedBall (2 + (τ : ℂ) * Complex.I) (6 / 5 : ℝ))
    (hsne : DirichletCharacter.LFunction χ s ≠ 0) {F : ℝ}
    (hF : ‖∑ᶠ u : ℂ,
      ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
        (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) u : ℤ) : ℂ) /
          (s - u)‖ ≤ F) :
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤
      F + (8760 * (1 + Real.log 5 / Real.log (6 / 5 : ℝ))) *
        (Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1) := by
  let S : ℂ := ∑ᶠ u : ℂ,
    ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
      (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) u : ℤ) : ℂ) / (s - u)
  have hrem := norm_dirichlet_LFunction_local_logDeriv_sub_divisor_sum_le χ hχ τ hs hsne
  calc
    _ = ‖(logDeriv (DirichletCharacter.LFunction χ) s - S) + S‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖logDeriv (DirichletCharacter.LFunction χ) s - S‖ + ‖S‖ := norm_add_le _ _
    _ ≤ (8760 * (1 + Real.log 5 / Real.log (6 / 5 : ℝ))) *
        (Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1) + F := add_le_add hrem hF
    _ = _ := add_comm _ _

open Metric Set in
/-- One actual height bounds the full L-function logarithmic derivative on
both horizontal edges throughout the strip. It retains nonvanishing and uses
the proved open-zero sum and quantitative remainder, not a zero-free premise. -/
theorem exists_dirichlet_logDeriv_bounded_horizontal_edges
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (τ : ℝ) :
    let J : ℝ := Real.log (28 * (q : ℝ) * (|τ| + 2)) / Real.log (6 / 5 : ℝ)
    let B : ℝ := 48 * J * (J + 1) +
      (8760 * (1 + Real.log 5 / Real.log (6 / 5 : ℝ))) *
        (Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1)
    ∃ H ∈ Icc τ (τ + 1 / 4), ∀ σ ∈ Icc (9 / 10 : ℝ) (11 / 10),
      (DirichletCharacter.LFunction χ ((σ : ℂ) + (H : ℂ) * Complex.I) ≠ 0 ∧
        ‖logDeriv (DirichletCharacter.LFunction χ)
          ((σ : ℂ) + (H : ℂ) * Complex.I)‖ ≤ B) ∧
      (DirichletCharacter.LFunction χ ((σ : ℂ) - (H : ℂ) * Complex.I) ≠ 0 ∧
        ‖logDeriv (DirichletCharacter.LFunction χ)
          ((σ : ℂ) - (H : ℂ) * Complex.I)‖ ≤ B) := by
  let J : ℝ := Real.log (28 * (q : ℝ) * (|τ| + 2)) / Real.log (6 / 5 : ℝ)
  have hJ : 0 ≤ J := (Nat.cast_nonneg _).trans (dirichletLocalZeros_card_le χ hχ τ)
  have hδ : 0 < 1 / (48 * (J + 1)) := by positivity
  obtain ⟨H, hH, hsum, havoid⟩ := exists_dirichlet_open_divisor_edge_height_bound χ hχ τ
  have hgap : |H - τ| ≤ 1 / 4 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hH.1)]
    linarith [hH.2]
  refine ⟨H, hH, ?_⟩
  intro σ hσ
  have hplus : DirichletCharacter.LFunction χ ((σ : ℂ) + (H : ℂ) * Complex.I) ≠ 0 := by
    intro hz
    have hsep := (havoid σ hσ ((σ : ℂ) + (H : ℂ) * Complex.I) hz).1
    simp only [sub_self, norm_zero] at hsep
    change 1 / (48 * (J + 1)) ≤ 0 at hsep
    linarith
  have hminus : DirichletCharacter.LFunction χ ((σ : ℂ) - (H : ℂ) * Complex.I) ≠ 0 := by
    intro hz
    have hsep := (havoid σ hσ ((σ : ℂ) - (H : ℂ) * Complex.I) hz).2
    simp only [sub_self, norm_zero] at hsep
    change 1 / (48 * (J + 1)) ≤ 0 at hsep
    linarith
  have hplusBound := norm_local_logDeriv_le_of_divisor_norm_bound χ hχ τ
    (horizontal_strip_mem_closedBall τ H σ hgap hσ) hplus (hsum σ hσ).1
  have hminusGap : |-H - -τ| ≤ 1 / 4 := by
    simpa only [neg_sub_neg, abs_sub_comm] using hgap
  have hminus' : DirichletCharacter.LFunction χ
      ((σ : ℂ) + ((-H : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using hminus
  have hminusBound := norm_local_logDeriv_le_of_divisor_norm_bound χ hχ (-τ)
    (horizontal_strip_mem_closedBall (-τ) (-H) σ hminusGap hσ) hminus' (hsum σ hσ).2
  refine ⟨⟨hplus, hplusBound⟩, hminus, ?_⟩
  simpa only [abs_neg, Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using hminusBound

#print axioms exists_dirichlet_logDeriv_bounded_horizontal_edges

open Metric Set in
/-- Select a left edge with the actual logarithmic-derivative bound, and
evaluate the rectangle as either zero or its unique actual real simple-zero
residue. -/
theorem exists_selected_perron_contour_with_real_exception :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1 / 100 ∧ 0 < C ∧
      ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
        ∀ H : ℝ, 2 ≤ H →
        let ellH : ℝ := Real.log (28 * (q : ℝ) * (H + 4)) + 1
        ∀ x : ℝ, 0 < x → ∀ σR : ℝ, 1 < σR →
        ∃ σ ∈ Icc (1 - c / ellH) (1 - c / (2 * ellH)),
          1 / 2 < σ ∧
          (∀ τ : ℝ, |τ| ≤ H →
            DirichletCharacter.LFunction χ ((σ : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 ∧
            ‖logDeriv (DirichletCharacter.LFunction χ)
              ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ C * ellH ^ 2) ∧
          (perronLogDerivativeRectangleBoundary q χ x σ σR H = 0 ∨
            ∃ β : ℝ, 1 / 2 < β ∧ β < 1 ∧ σ < β ∧
              (∀ r : ZMod q, (χ r).im = 0) ∧
              DirichletCharacter.LFunction χ (β : ℂ) = 0 ∧
              deriv (DirichletCharacter.LFunction χ) (β : ℂ) ≠ 0 ∧
              perronLogDerivativeRectangleBoundary q χ x σ σR H /
                (2 * Real.pi * Complex.I : ℂ) =
                  -(x : ℂ) ^ (β : ℂ) / (β : ℂ)) := by
  obtain ⟨c, C, hc, hcsmall, hC, hedge⟩ :=
    exists_dirichlet_LFunction_bounded_left_vertical_edge
  refine ⟨c, C, hc, hcsmall, hC, ?_⟩
  intro q hq χ hχ H hH ellH x hx σR hσRgt
  have hqge : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have harg : 1 ≤ 28 * (q : ℝ) * (H + 4) := by
    have hprod := mul_le_mul hqge (show (6 : ℝ) ≤ H + 4 by linarith)
      (by norm_num : (0 : ℝ) ≤ 6) (by exact_mod_cast (NeZero.pos q).le)
    nlinarith
  have hell : 1 ≤ ellH := by
    dsimp [ellH]
    linarith [Real.log_nonneg harg]
  have hellpos : 0 < ellH := lt_of_lt_of_le zero_lt_one hell
  obtain ⟨σ, hσI, hEdge, hZeroCert⟩ := hedge χ hχ H hH
  have hσlt1 : σ < 1 := by
    have hpos : 0 < c / (2 * ellH) := by positivity
    exact lt_of_le_of_lt hσI.2 (by linarith)
  have hσhalf : 1 / 2 < σ := by
    have hratio : c / ellH ≤ 1 / 100 :=
      (div_le_self (le_of_lt hc) hell).trans hcsmall
    linarith [hσI.1]
  have hσpos : 0 < σ := by linarith
  have hσR : σ < σR := lt_trans hσlt1 hσRgt
  have hHpos : 0 < H := by linarith
  have hRectRe (z : ℂ)
      (hz : z ∈ ([[σ, σR]] ×ℂ [[-H, H]] : Set ℂ)) : z.re ∈ Icc σ σR := by
    have hz' : z.re ∈ Icc σ σR ∧ z.im ∈ Icc (-H) H := by
      simpa [uIcc_of_le hσR.le,
        uIcc_of_le (show -H ≤ H by linarith), Complex.mem_reProdIm] using hz
    exact hz'.1
  have hRectIm (z : ℂ)
      (hz : z ∈ ([[σ, σR]] ×ℂ [[-H, H]] : Set ℂ)) : z.im ∈ Icc (-H) H := by
    have hz' : z.re ∈ Icc σ σR ∧ z.im ∈ Icc (-H) H := by
      simpa [uIcc_of_le hσR.le,
        uIcc_of_le (show -H ≤ H by linarith), Complex.mem_reProdIm] using hz
    exact hz'.2
  by_cases hex : ∃ z : ℂ,
      z ∈ ([[σ, σR]] ×ℂ [[-H, H]] : Set ℂ) ∧
        DirichletCharacter.LFunction χ z = 0
  · obtain ⟨z, hzRect, hzero⟩ := hex
    have himBound : |z.im| ≤ H := by
      rcases hRectIm z hzRect with ⟨hlo, hhi⟩
      exact abs_le.mpr ⟨by linarith, hhi⟩
    have hreBound : σ ≤ z.re := (hRectRe z hzRect).1
    obtain ⟨hχreal, him, hzlt1, hsimple, hunique⟩ :=
      hZeroCert z hzero himBound hreBound
    let β : ℝ := z.re
    have hzReal : z = (β : ℂ) := by
      apply Complex.ext
      · simp [β]
      · simp [β, him]
    have hβgt : σ < β := by
      have hβge : σ ≤ β := hreBound
      by_contra hnot
      have heq : β = σ := by linarith
      have hleftzero :
          DirichletCharacter.LFunction χ ((σ : ℂ) + (0 : ℂ) * Complex.I) = 0 := by
        simpa [hzReal, β, heq] using hzero
      exact (hEdge 0 (by simp; linarith)).1 hleftzero
    have hβone : β < 1 := by simpa [β] using hzlt1
    have hβhalf : 1 / 2 < β := lt_trans hσhalf hβgt
    have hsimpleβ : deriv (DirichletCharacter.LFunction χ) (β : ℂ) ≠ 0 := by
      simpa [hzReal] using hsimple
    have honly : ∀ w : ℂ,
        w ∈ ([[σ, σR]] ×ℂ [[-H, H]] : Set ℂ) →
          DirichletCharacter.LFunction χ w = 0 → w = (β : ℂ) := by
      intro w hw hwzero
      have hwHeight : |w.im| ≤ H := by
        rcases hRectIm w hw with ⟨hlo, hhi⟩
        exact abs_le.mpr ⟨by linarith, hhi⟩
      have hwRe : σ ≤ w.re := (hRectRe w hw).1
      exact (hunique w hwzero hwHeight hwRe).trans hzReal
    have hres := perronLogDerivative_real_exceptional_rectangle_residue
      q χ hχ x hx σ σR H β hσpos hσR hHpos hβgt
      (by linarith) (by exact_mod_cast (ne_of_gt (by linarith : 0 < β)))
      (by simpa [hzReal] using hzero) hsimpleβ honly
    refine ⟨σ, hσI, hσhalf, hEdge, Or.inr ?_⟩
    exact ⟨β, hβhalf, hβone, hβgt, hχreal, by simpa [hzReal] using hzero,
      hsimpleβ, hres⟩
  · have hzeroFree : ∀ z : ℂ,
        z ∈ ([[σ, σR]] ×ℂ [[-H, H]] : Set ℂ) →
          DirichletCharacter.LFunction χ z ≠ 0 := by
      intro z hz hLzero
      exact hex ⟨z, hz, hLzero⟩
    have hboundary := perronLogDerivative_zeroFree_rectangle_boundary_eq_zero
      q χ hχ x hx σ σR H hσpos hσR hHpos hzeroFree
    exact ⟨σ, hσI, hσhalf, hEdge, Or.inl hboundary⟩

#print axioms exists_selected_perron_contour_with_real_exception

open Metric Set intervalIntegral in
open scoped Real in
set_option maxHeartbeats 1000000 in
/-- At one actual safe height, the truncated Perron integral differs from its
actual rectangle residue by the sum of the three proved edge budgets. -/
theorem exists_nonprincipal_pointwise_shiftedPerron_error :
    ∃ c K : ℝ, 0 < c ∧ c ≤ 1 / 100 ∧ 0 < K ∧
      ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
        ∀ m : ℕ, 2 ≤ m → 10 ≤ exerciseMajorLog m →
          let τ : ℝ := Real.exp (Real.sqrt (exerciseMajorLog m))
          2 ≤ τ → τ + 1 / 4 ≤ (m : ℝ) →
          ∃ H : ℝ, τ ≤ H ∧ H ≤ τ + 1 / 4 ∧
          ∃ σ ∈ Icc
              (1 - c / (Real.log (28 * (q : ℝ) * (H + 4)) + 1))
              (1 - c / (2 * (Real.log (28 * (q : ℝ) * (H + 4)) + 1))),
            ∃ R : ℂ,
              (R = 0 ∨ ∃ β : ℝ,
                1 / 2 < β ∧ β < 1 ∧ σ < β ∧
                (∀ r : ZMod q, (χ r).im = 0) ∧
                DirichletCharacter.LFunction χ (β : ℂ) = 0 ∧
                deriv (DirichletCharacter.LFunction χ) (β : ℂ) ≠ 0 ∧
                R = -(exercisePerronEndpoint m : ℂ) ^ (β : ℂ) / (β : ℂ)) ∧
              ‖exercisePerronIntegral q χ m H - R‖ ≤
                6 * K * (Real.log (28 * (q : ℝ) * (H + 4)) + 1) ^ 2 *
                    (exercisePerronEndpoint m) ^ σ * Real.log (H + 1) +
                  4 * Real.exp 1 * K *
                    (Real.log (28 * (q : ℝ) * (H + 4)) + 1) ^ 2 *
                    (m : ℝ) / H := by
  obtain ⟨c, C, hc, hcsmall, hC, hSelected⟩ :=
    exists_selected_perron_contour_with_real_exception
  let d : ℝ := Real.log (6 / 5 : ℝ)
  let Khor : ℝ := 48 * (1 / d) * (1 / d + 1) +
    8760 * (1 + Real.log 5 / d)
  let K : ℝ := max C Khor
  have hd : 0 < d := by dsimp [d]; exact Real.log_pos (by norm_num)
  have hK : 0 < K := by dsimp [K, Khor, d]; positivity
  refine ⟨c, K, hc, hcsmall, hK, ?_⟩
  intro q hq χ hχ m hm hLm τ hτ hroom
  let x : ℝ := exercisePerronEndpoint m
  let σR : ℝ := exercisePerronAbscissa m
  let ellH (H : ℝ) : ℝ := Real.log (28 * (q : ℝ) * (H + 4)) + 1
  have hmReal : 2 ≤ (m : ℝ) := by exact_mod_cast hm
  have hτpos : 0 < τ := by positivity
  have hτabs : |τ| = τ := abs_of_nonneg hτpos.le
  obtain ⟨H, hHrange, hHorizontal⟩ :=
    exists_dirichlet_logDeriv_bounded_horizontal_edges χ hχ τ
  have hHlower : τ ≤ H := hHrange.1
  have hHupper : H ≤ τ + 1 / 4 := hHrange.2
  have hHtwo : 2 ≤ H := le_trans hτ hHlower
  have hHpos : 0 < H := by linarith
  have hHm : H ≤ (m : ℝ) := hHupper.trans hroom
  have hqge : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hEll (Y : ℝ) (hY : 2 ≤ Y) : 1 ≤ ellH Y := by
    dsimp [ellH]
    have harg : 1 ≤ 28 * (q : ℝ) * (Y + 4) := by
      nlinarith only [hqge, hY]
    linarith [Real.log_nonneg harg]
  have hell : 1 ≤ ellH H := hEll H hHtwo
  obtain ⟨σ, hσI, hσhalf, hLeft, hResidue⟩ :=
    hSelected χ hχ H hHtwo x (by dsimp [x, exercisePerronEndpoint]; positivity)
      σR (by
        have hb := exercisePerronAbscissa_bounds m hm
        dsimp [σR]
        linarith [hb.1])
  have hσlt1 : σ < 1 := by
    have hpos : 0 < c / (2 * ellH H) := by positivity
    linarith only [hσI.2, hpos]
  have hcdiv : c / ellH H ≤ 1 / 100 :=
    (div_le_self (le_of_lt hc) hell).trans hcsmall
  have hσge09 : (9 / 10 : ℝ) ≤ σ := by linarith only [hσI.1, hcdiv]
  have habscissa := exercisePerronAbscissa_bounds m hm
  have hσRgt : 1 < σR := by simpa [σR] using habscissa.1
  have hσRle : σR ≤ 11 / 10 := by
    dsimp [σR, exercisePerronAbscissa]
    have hL : 0 < exerciseMajorLog m := by linarith
    have hinv : (exerciseMajorLog m)⁻¹ ≤ 1 / 10 := by
      have hrecip := one_div_le_one_div_of_le
        (by norm_num : (0 : ℝ) < 10) hLm
      simpa only [inv_eq_one_div] using hrecip
    linarith only [hinv]
  have hσleR : σ ≤ σR := le_of_lt (lt_trans hσlt1 hσRgt)
  have hwidth : σR - σ ≤ 1 := by linarith only [hσRle, hσge09]
  have hx : 1 ≤ x := by dsimp [x, exercisePerronEndpoint]; nlinarith
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hxle : x ≤ 2 * (m : ℝ) := by
    dsimp [x, exercisePerronEndpoint]
    nlinarith only [hmReal]
  have hxPow : x ^ σR ≤ Real.exp 1 * x := by
    dsimp [x, σR]
    have hxarg : exercisePerronEndpoint m ≤ (m : ℝ) + 2 := by
      dsimp [exercisePerronEndpoint]
      linarith
    have hmarg : (1 : ℝ) < (m : ℝ) + 2 := by linarith
    simpa only [exercisePerronAbscissa, exerciseMajorLog] using
      perron_rpow_one_add_inv_log_le (exercisePerronEndpoint m) ((m : ℝ) + 2)
        (by dsimp [exercisePerronEndpoint]; positivity) hxarg hmarg
  have hlogArgle :
      Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1 ≤ ellH H := by
    have hargle : 28 * (q : ℝ) * (|τ| + 2) ≤ 28 * (q : ℝ) * (H + 4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [hτabs]
      linarith [hHlower]
    exact add_le_add (Real.log_le_log (by positivity) hargle) le_rfl
  have hLτarg : 1 ≤ 28 * (q : ℝ) * (|τ| + 2) := by
    rw [hτabs]
    nlinarith only [hqge, hτ]
  have hLτnonneg : 0 ≤ Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1 := by
    linarith [Real.log_nonneg hLτarg]
  have hJle :
      Real.log (28 * (q : ℝ) * (|τ| + 2)) / d ≤ ellH H / d :=
    div_le_div_of_nonneg_right (by linarith [hlogArgle]) hd.le
  have hJplus :
      Real.log (28 * (q : ℝ) * (|τ| + 2)) / d + 1 ≤
        ellH H * (1 / d + 1) := by
    calc
      _ ≤ ellH H / d + ellH H := add_le_add hJle hell
      _ = ellH H * (1 / d + 1) := by ring
  have hlogτnonneg : 0 ≤ Real.log (28 * (q : ℝ) * (|τ| + 2)) :=
    Real.log_nonneg hLτarg
  let Lτ : ℝ := Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1
  let Bτ : ℝ :=
    48 * (Real.log (28 * (q : ℝ) * (|τ| + 2)) / d) *
        (Real.log (28 * (q : ℝ) * (|τ| + 2)) / d + 1) +
      8760 * (1 + Real.log 5 / d) * Lτ
  have hBτ : Bτ ≤ Khor * (ellH H) ^ 2 := by
    dsimp [Bτ, Khor, Lτ]
    have hJnonneg : 0 ≤ Real.log (28 * (q : ℝ) * (|τ| + 2)) / d :=
      div_nonneg hlogτnonneg hd.le
    have hJplusnonneg :
        0 ≤ Real.log (28 * (q : ℝ) * (|τ| + 2)) / d + 1 :=
      add_nonneg hJnonneg zero_le_one
    have hfirst := mul_le_mul hJle hJplus hJplusnonneg
      (div_nonneg (le_trans zero_le_one hell) hd.le)
    have hsecond := mul_le_mul_of_nonneg_left hlogArgle
      (by positivity : (0 : ℝ) ≤ 8760 * (1 + Real.log 5 / d))
    have hfirst' := mul_le_mul_of_nonneg_left hfirst (by norm_num : (0 : ℝ) ≤ 48)
    have hcoef : 0 ≤ 8760 * (1 + Real.log 5 / d) := by positivity
    have hellsq : ellH H ≤ (ellH H) ^ 2 := by
      calc
        ellH H = ellH H * 1 := by ring
        _ ≤ ellH H * ellH H := mul_le_mul_of_nonneg_left hell (by positivity)
        _ = (ellH H) ^ 2 := by ring
    have hsecond' := mul_le_mul_of_nonneg_left hellsq hcoef
    calc
      _ = 48 * ((Real.log (28 * (q : ℝ) * (|τ| + 2)) / d) *
          (Real.log (28 * (q : ℝ) * (|τ| + 2)) / d + 1)) +
          8760 * (1 + Real.log 5 / d) * Lτ := by ring
      _ ≤ 48 * ((ellH H / d) * (ellH H * (1 / d + 1))) +
          8760 * (1 + Real.log 5 / d) * (ellH H) ^ 2 :=
        add_le_add hfirst' (hsecond.trans hsecond')
      _ = Khor * (ellH H) ^ 2 := by dsimp [Khor]; ring
  have hB : Bτ ≤ K * (ellH H) ^ 2 :=
    hBτ.trans (mul_le_mul_of_nonneg_right (le_max_right C Khor) (sq_nonneg _))
  have hHorizontalBound (u : ℝ) (hu : u ∈ Icc (9 / 10 : ℝ) (11 / 10)) :
      (DirichletCharacter.LFunction χ ((u : ℂ) + (H : ℂ) * Complex.I) ≠ 0 ∧
        ‖logDeriv (DirichletCharacter.LFunction χ)
          ((u : ℂ) + (H : ℂ) * Complex.I)‖ ≤ K * (ellH H) ^ 2) ∧
      (DirichletCharacter.LFunction χ ((u : ℂ) + ((-H : ℝ) : ℂ) * Complex.I) ≠ 0 ∧
        ‖logDeriv (DirichletCharacter.LFunction χ)
          ((u : ℂ) + ((-H : ℝ) : ℂ) * Complex.I)‖ ≤ K * (ellH H) ^ 2) := by
    rcases hHorizontal u hu with ⟨⟨hplus, hplusB⟩, hminus, hminusB⟩
    refine ⟨⟨hplus, hplusB.trans hB⟩, ?_, ?_⟩
    · simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using hminus
    · simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using
        (hminusB.trans hB)
  have hσin : σ ∈ Icc (9 / 10 : ℝ) (11 / 10) := ⟨hσge09, by linarith⟩
  have hσRin : σR ∈ Icc (9 / 10 : ℝ) (11 / 10) := ⟨by linarith, hσRle⟩
  have hbetween (u : ℝ) (hu : u ∈ Icc σ σR) :
      u ∈ Icc (9 / 10 : ℝ) (11 / 10) := ⟨le_trans hσge09 hu.1, le_trans hu.2 hσRle⟩
  have hLeftBound (t : ℝ) (ht : |t| ≤ H) :
      DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 ∧
      ‖logDeriv (DirichletCharacter.LFunction χ)
        ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ K * (ellH H) ^ 2 := by
    rcases hLeft t ht with ⟨hne, hnorm⟩
    exact ⟨hne, hnorm.trans (mul_le_mul_of_nonneg_right
      (le_max_left C Khor) (sq_nonneg _))⟩
  have hvertical := norm_integral_perronLogDerivativeIntegrand_vertical_le
    χ hχ x H σ (K * (ellH H) ^ 2) hxpos (by linarith) (by linarith)
    (by positivity) hLeftBound
  have hbottom := norm_integral_perronLogDerivativeIntegrand_horizontal_le
    χ hχ x σ σR (-H) (K * (ellH H) ^ 2) hx hσleR (by linarith) (by positivity)
    (fun u hu => (hHorizontalBound u (hbetween u hu)).2)
  have htop := norm_integral_perronLogDerivativeIntegrand_horizontal_le
    χ hχ x σ σR H (K * (ellH H) ^ 2) hx hσleR (by linarith) (by positivity)
    (fun u hu => (hHorizontalBound u (hbetween u hu)).1)
  have hbottomBound :
      ‖∫ u in σ..σR, perronLogDerivativeIntegrand q χ x
        ((u : ℂ) + (-H : ℂ) * Complex.I)‖ ≤
        K * (ellH H) ^ 2 * x ^ σR / H := by
    have habs : |-H| = H := by rw [abs_neg, abs_of_nonneg hHpos.le]
    have hbase :
        ‖∫ u in σ..σR, perronLogDerivativeIntegrand q χ x
          ((u : ℂ) + (-H : ℂ) * Complex.I)‖ ≤
          (σR - σ) * (K * (ellH H) ^ 2) * x ^ σR / H := by
      simpa [habs, Complex.ofReal_neg] using hbottom
    calc
      _ ≤ (σR - σ) * (K * (ellH H) ^ 2) * x ^ σR / H := hbase
      _ = (σR - σ) * (K * (ellH H) ^ 2 * x ^ σR / H) := by ring
      _ ≤ 1 * (K * (ellH H) ^ 2 * x ^ σR / H) :=
        mul_le_mul_of_nonneg_right hwidth (by positivity)
      _ = _ := by ring
  have htopBound :
      ‖∫ u in σ..σR, perronLogDerivativeIntegrand q χ x
        ((u : ℂ) + (H : ℂ) * Complex.I)‖ ≤
        K * (ellH H) ^ 2 * x ^ σR / H := by
    have habs : |H| = H := abs_of_nonneg hHpos.le
    have hbase :
        ‖∫ u in σ..σR, perronLogDerivativeIntegrand q χ x
          ((u : ℂ) + (H : ℂ) * Complex.I)‖ ≤
          (σR - σ) * (K * (ellH H) ^ 2) * x ^ σR / H := by
      simpa [habs] using htop
    calc
      _ ≤ (σR - σ) * (K * (ellH H) ^ 2) * x ^ σR / H := hbase
      _ = (σR - σ) * (K * (ellH H) ^ 2 * x ^ σR / H) := by ring
      _ ≤ 1 * (K * (ellH H) ^ 2 * x ^ σR / H) :=
        mul_le_mul_of_nonneg_right hwidth (by positivity)
      _ = _ := by ring
  have hverticalBound :
      ‖∫ t in -H..H, perronLogDerivativeIntegrand q χ x
        ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        6 * K * (ellH H) ^ 2 * x ^ σ * Real.log (H + 1) := by
    calc
      _ ≤ 6 * (K * (ellH H) ^ 2) * x ^ σ * Real.log (H + 1) := hvertical
      _ = _ := by ring
  have hnormEdges :
      ‖∫ t in -H..H, perronLogDerivativeIntegrand q χ x
          ((σ : ℂ) + (t : ℂ) * Complex.I)‖ +
        ‖∫ u in σ..σR, perronLogDerivativeIntegrand q χ x
          ((u : ℂ) + (-H : ℂ) * Complex.I)‖ +
        ‖∫ u in σ..σR, perronLogDerivativeIntegrand q χ x
          ((u : ℂ) + (H : ℂ) * Complex.I)‖ ≤
        6 * K * (ellH H) ^ 2 * x ^ σ * Real.log (H + 1) +
          4 * Real.exp 1 * K * (ellH H) ^ 2 * (m : ℝ) / H := by
    have hxupper : x ^ σR ≤ Real.exp 1 * x := hxPow
    have hxhor :
        ‖∫ u in σ..σR, perronLogDerivativeIntegrand q χ x
            ((u : ℂ) + (-H : ℂ) * Complex.I)‖ +
          ‖∫ u in σ..σR, perronLogDerivativeIntegrand q χ x
            ((u : ℂ) + (H : ℂ) * Complex.I)‖ ≤
          4 * Real.exp 1 * K * (ellH H) ^ 2 * (m : ℝ) / H := by
      calc
        _ ≤ 2 * (K * (ellH H) ^ 2 * x ^ σR / H) := by
          calc
            _ ≤ (K * (ellH H) ^ 2 * x ^ σR / H) +
                (K * (ellH H) ^ 2 * x ^ σR / H) := add_le_add hbottomBound htopBound
            _ = _ := by ring
        _ ≤ 2 * (K * (ellH H) ^ 2 * (Real.exp 1 * x) / H) := by gcongr
        _ ≤ 4 * Real.exp 1 * K * (ellH H) ^ 2 * (m : ℝ) / H := by
          have hcoef : 0 ≤ 2 * K * (ellH H) ^ 2 * Real.exp 1 / H := by positivity
          calc
            _ = (2 * K * (ellH H) ^ 2 * Real.exp 1 / H) * x := by ring
            _ ≤ (2 * K * (ellH H) ^ 2 * Real.exp 1 / H) * (2 * (m : ℝ)) :=
              mul_le_mul_of_nonneg_left hxle hcoef
            _ = _ := by ring
    calc
      _ = ‖∫ t in -H..H, perronLogDerivativeIntegrand q χ x
            ((σ : ℂ) + (t : ℂ) * Complex.I)‖ +
          (‖∫ u in σ..σR, perronLogDerivativeIntegrand q χ x
              ((u : ℂ) + (-H : ℂ) * Complex.I)‖ +
            ‖∫ u in σ..σR, perronLogDerivativeIntegrand q χ x
              ((u : ℂ) + (H : ℂ) * Complex.I)‖) := by ring
      _ ≤ 6 * K * (ellH H) ^ 2 * x ^ σ * Real.log (H + 1) +
          4 * Real.exp 1 * K * (ellH H) ^ 2 * (m : ℝ) / H :=
        add_le_add hverticalBound hxhor
  have hcompare := norm_perronRectangle_right_sub_boundary_le
    (perronLogDerivativeIntegrand q χ x) σ σR H
  have hIeq : exercisePerronIntegral q χ m H =
      (2 * Real.pi : ℂ)⁻¹ *
        ∫ t in -H..H, perronLogDerivativeIntegrand q χ x
          ((σR : ℂ) + (t : ℂ) * Complex.I) := by
    rw [exercisePerronIntegral_eq_logDerivativeIntegrand]
    dsimp [x]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    change perronLogDerivativeIntegrand q χ (exercisePerronEndpoint m)
        ((exercisePerronAbscissa m : ℂ) + Complex.I * (t : ℂ)) =
      perronLogDerivativeIntegrand q χ (exercisePerronEndpoint m)
        ((σR : ℂ) + (t : ℂ) * Complex.I)
    have hparam :
        (exercisePerronAbscissa m : ℂ) + Complex.I * (t : ℂ) =
          (σR : ℂ) + (t : ℂ) * Complex.I := by
      change (exercisePerronAbscissa m : ℂ) + Complex.I * (t : ℂ) =
        (exercisePerronAbscissa m : ℂ) + (t : ℂ) * Complex.I
      rw [mul_comm]
    rw [hparam]
  have hboundaryEq : perronRectangleBoundaryIntegral
      (perronLogDerivativeIntegrand q χ x) σ σR H =
        perronLogDerivativeRectangleBoundary q χ x σ σR H := rfl
  rcases hResidue with hzero | hex
  · let R : ℂ := 0
    have hresidue : perronLogDerivativeRectangleBoundary q χ x σ σR H /
        (2 * Real.pi * Complex.I : ℂ) = R := by simpa [R] using hzero
    have hcompare' := hcompare
    rw [← hIeq, hboundaryEq, hresidue] at hcompare'
    have hpi : (2 * Real.pi : ℝ)⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀
      linarith only [Real.pi_gt_three]
    have hfinal : ‖exercisePerronIntegral q χ m H - R‖ ≤
        6 * K * (ellH H) ^ 2 * x ^ σ * Real.log (H + 1) +
          4 * Real.exp 1 * K * (ellH H) ^ 2 * (m : ℝ) / H := by
      calc
        _ ≤ (2 * Real.pi)⁻¹ * _ := hcompare'
        _ ≤ 1 * _ := mul_le_mul_of_nonneg_right hpi (by positivity)
        _ = _ := by norm_num
        _ ≤ _ := hnormEdges
    refine ⟨H, hHlower, hHupper, σ, ?_, R, Or.inl rfl, ?_⟩
    · simpa [ellH] using hσI
    · simpa [x, ellH] using hfinal
  · obtain ⟨β, hβhalf, hβone, hβgt, hreal, hzero, hsimple, hvalue⟩ := hex
    let R : ℂ := -(x : ℂ) ^ (β : ℂ) / (β : ℂ)
    have hresidue : perronLogDerivativeRectangleBoundary q χ x σ σR H /
        (2 * Real.pi * Complex.I : ℂ) = R := by simpa [R] using hvalue
    have hcompare' := hcompare
    rw [← hIeq, hboundaryEq, hresidue] at hcompare'
    have hpi : (2 * Real.pi : ℝ)⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀
      linarith only [Real.pi_gt_three]
    have hfinal : ‖exercisePerronIntegral q χ m H - R‖ ≤
        6 * K * (ellH H) ^ 2 * x ^ σ * Real.log (H + 1) +
          4 * Real.exp 1 * K * (ellH H) ^ 2 * (m : ℝ) / H := by
      calc
        _ ≤ (2 * Real.pi)⁻¹ * _ := hcompare'
        _ ≤ 1 * _ := mul_le_mul_of_nonneg_right hpi (by positivity)
        _ = _ := by norm_num
        _ ≤ _ := hnormEdges
    refine ⟨H, hHlower, hHupper, σ, ?_, R,
      Or.inr ⟨β, hβhalf, hβone, hβgt, hreal, hzero, hsimple, rfl⟩, ?_⟩
    · simpa [ellH] using hσI
    · simpa [x, ellH] using hfinal

#print axioms exists_nonprincipal_pointwise_shiftedPerron_error

/-- MA04 (PROVED, using MA02): absorb every possible exceptional
zero contribution uniformly above `sqrt(N)`.

Use `χ.primitiveCharacter_isPrimitive`, `χ.conductor_ne_zero`, and
`χ.conductor_dvd_level` to apply MA02 at the conductor. The proof uses the
positive real exponent `A+1`, which handles `A=0` without a separate case.
Uniformly over `m>sqrt(N)`, `log(m+1/2)≥log(N+2)/4`; hence the Siegel gap
gives decay of order `exp(-C*(log N)^(2/3))`. A spare half of that decay
absorbs the factor `(m+1/2)/N≤2`. MA02 and this consumer now audit with
standard logical axioms only. -/
theorem exercise_exceptionalTerm_absorbed (A : ℕ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, ∀ (_hq : NeZero q),
        letI : NeZero q := _hq
        q ≤ logarithmicDenominatorCutoff A N →
        ∀ χ : DirichletCharacter ℂ q, ∀ m : ℕ, m ≤ N →
          Real.sqrt (N : ℝ) < (m : ℝ) → ∀ β : ℝ,
            1 / 2 < β → β < 1 → χ.primitiveCharacter ≠ 1 →
              exerciseRealCharacter χ.conductor χ.primitiveCharacter →
              exercisePrimitiveLValue q χ β = 0 →
                exercisePerronEndpoint m ^ β ≤
                  (N : ℝ) *
                    Real.exp (-c * Real.sqrt (exerciseMajorLog N)) := by
  let R : ℝ := (A : ℝ) + 1
  let ε : ℝ := 1 / (3 * R)
  have hR : 0 < R := by dsimp [R]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C, hC, hSiegel⟩ := exercise_siegel_real_zero_lower hε
  let c : ℝ := C / 8
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  have hlog : Tendsto exerciseMajorLog atTop atTop := by
    have harg : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop := by
      convert tendsto_atTop_add_const_right _ (2 : ℝ)
        tendsto_natCast_atTop_atTop using 1
    exact Real.tendsto_log_atTop.comp harg
  have hroot : Tendsto (fun N : ℕ => Real.sqrt (exerciseMajorLog N))
      atTop atTop := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hlog
  filter_upwards [hlog.eventually_ge_atTop (1 : ℝ),
    hroot.eventually_ge_atTop (8 * Real.log 2 / C),
    eventually_ge_atTop (2 : ℕ)] with N hLone hrootLarge hN2
  intro q hq hqcut χ m hm hmsqrt β hβhalf hβone hχprim hχreal hzero
  letI : NeZero q := hq
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  let L : ℝ := exerciseMajorLog N
  let x : ℝ := exercisePerronEndpoint m
  let y : ℝ := Real.log x
  have hL1 : 1 ≤ L := hLone
  have hL : 0 < L := by linarith
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hx : 0 < x := by
    dsimp [x, exercisePerronEndpoint]
    positivity
  have hxUpper : x ≤ 2 * (N : ℝ) := by
    dsimp [x, exercisePerronEndpoint]
    have hmreal : (m : ℝ) ≤ N := by exact_mod_cast hm
    linarith
  have hconductor : χ.conductor ≤ q :=
    Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
  have hconductorPos : (0 : ℝ) < χ.conductor := by
    exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hcut : (χ.conductor : ℝ) ≤ L ^ R := by
    have hqcutReal : (χ.conductor : ℝ) ≤
        (logarithmicDenominatorCutoff A N : ℝ) := by
      exact_mod_cast hconductor.trans hqcut
    have hcutLog := logarithmicDenominatorCutoff_le_log_pow A N
    have hpow : L ^ A ≤ L ^ (A + 1) :=
      pow_le_pow_right₀ hL1 (by omega)
    calc
      (χ.conductor : ℝ) ≤
          (logarithmicDenominatorCutoff A N : ℝ) := hqcutReal
      _ ≤ L ^ A := by simpa only [L, exerciseMajorLog] using hcutLog
      _ ≤ L ^ (A + 1) := hpow
      _ = L ^ R := by
        have hRcast : R = ((A + 1 : ℕ) : ℝ) := by dsimp [R]; norm_num
        rw [hRcast, Real.rpow_natCast]
  have hneg : -ε ≤ 0 := neg_nonpos.mpr hε.le
  have hpowid : (L ^ R) ^ (-ε) = L ^ (-1 / 3 : ℝ) := by
    rw [← Real.rpow_mul hL.le]
    congr 1
    dsimp [ε, R]
    field_simp
  have hconductorPow : L ^ (-1 / 3 : ℝ) ≤
      (χ.conductor : ℝ) ^ (-ε) := by
    rw [← hpowid]
    exact Real.rpow_le_rpow_of_nonpos hconductorPos hcut hneg
  have hzero' : DirichletCharacter.LFunction χ.primitiveCharacter (β : ℂ) = 0 := by
    simpa only [exercisePrimitiveLValue] using hzero
  have hSiegelCond : C * (χ.conductor : ℝ) ^ (-ε) ≤ 1 - β :=
    hSiegel χ.conductor inferInstance χ.primitiveCharacter
      χ.primitiveCharacter_isPrimitive hχprim hχreal β hβhalf hβone hzero'
  have hgap : C * L ^ (-1 / 3 : ℝ) ≤ 1 - β :=
    (mul_le_mul_of_nonneg_left hconductorPow hC.le).trans hSiegelCond
  have hNplusSq : (N : ℝ) + 2 ≤ (N : ℝ) ^ 2 := by nlinarith
  have hLlogN : L ≤ 2 * Real.log (N : ℝ) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (N : ℝ) + 2)
      hNplusSq
    rw [Real.log_pow] at h
    simpa only [L, exerciseMajorLog, Nat.cast_ofNat] using h
  have hlogRoot : Real.log (Real.sqrt (N : ℝ)) =
      Real.log (N : ℝ) / 2 := Real.log_sqrt (by positivity)
  have hrootNpos : 0 < Real.sqrt (N : ℝ) := by positivity
  have hrootEnd : Real.sqrt (N : ℝ) ≤ x := by
    dsimp [x, exercisePerronEndpoint]
    linarith
  have hlogEnd : L / 4 ≤ y := by
    have hlogMono := Real.log_le_log hrootNpos hrootEnd
    rw [hlogRoot] at hlogMono
    dsimp [y]
    linarith
  have hy : 0 < y := by linarith
  have hprod : L ^ (-1 / 3 : ℝ) * L = L ^ (2 / 3 : ℝ) := by
    calc
      L ^ (-1 / 3 : ℝ) * L =
          L ^ (-1 / 3 : ℝ) * L ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = L ^ ((-1 / 3 : ℝ) + 1) := by rw [← Real.rpow_add hL]
      _ = L ^ (2 / 3 : ℝ) := by congr 1; ring
  have hgapLog : C / 4 * L ^ (2 / 3 : ℝ) ≤ (1 - β) * y := by
    calc
      C / 4 * L ^ (2 / 3 : ℝ) =
          C / 4 * (L ^ (-1 / 3 : ℝ) * L) := by rw [hprod]
      _ = (C * L ^ (-1 / 3 : ℝ)) * (L / 4) := by ring
      _ ≤ (1 - β) * (L / 4) :=
        mul_le_mul_of_nonneg_right hgap (by positivity)
      _ ≤ (1 - β) * y :=
        mul_le_mul_of_nonneg_left hlogEnd (by linarith)
  have hrootPower : Real.sqrt L ≤ L ^ (2 / 3 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hlogTwo : Real.log 2 ≤ c * Real.sqrt L := by
    have h := (div_le_iff₀ hC).1 hrootLarge
    dsimp [c]
    nlinarith
  have hbudget : c * Real.sqrt L + Real.log 2 ≤
      C / 4 * L ^ (2 / 3 : ℝ) := by
    calc
      c * Real.sqrt L + Real.log 2 ≤
          2 * c * Real.sqrt L := by linarith
      _ = C / 4 * Real.sqrt L := by dsimp [c]; ring
      _ ≤ C / 4 * L ^ (2 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left hrootPower (by positivity)
  have hExpArg : β * y ≤ y - c * Real.sqrt L - Real.log 2 := by
    linarith [hgapLog, hbudget]
  have hExpTwo : Real.exp (-c * Real.sqrt L - Real.log 2) =
      Real.exp (-c * Real.sqrt L) / 2 := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg, Real.exp_log (by norm_num)]
    ring
  calc
    x ^ β = Real.exp (β * y) := by
      rw [Real.rpow_def_of_pos hx]
      simp [y, mul_comm]
    _ ≤ Real.exp (y - c * Real.sqrt L - Real.log 2) :=
      Real.exp_le_exp.mpr hExpArg
    _ = x * (Real.exp (-c * Real.sqrt L) / 2) := by
      rw [show y - c * Real.sqrt L - Real.log 2 =
        y + (-c * Real.sqrt L - Real.log 2) by ring,
        Real.exp_add, Real.exp_log hx, hExpTwo]
    _ ≤ (2 * (N : ℝ)) * (Real.exp (-c * Real.sqrt L) / 2) :=
      mul_le_mul_of_nonneg_right hxUpper (by positivity)
    _ = (N : ℝ) * Real.exp (-c * Real.sqrt L) := by ring

/-- The exact exceptional-zero residue fits MA03's fixed `x^β` allowance
after absorbing its `1/β` excess into the main error.

This is a proved normalization adapter, conditional on MA02 through MA04;
its axiom audit now uses standard logical axioms only. -/
theorem exercise_exceptionalResidue_le_term_add_absorbed (A : ℕ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, ∀ (_hq : NeZero q),
        letI : NeZero q := _hq
        q ≤ logarithmicDenominatorCutoff A N →
        ∀ χ : DirichletCharacter ℂ q, ∀ m : ℕ, m ≤ N →
          Real.sqrt (N : ℝ) < (m : ℝ) → ∀ β : ℝ,
            1 / 2 < β → β < 1 → χ.primitiveCharacter ≠ 1 →
              exerciseRealCharacter χ.conductor χ.primitiveCharacter →
              exercisePrimitiveLValue q χ β = 0 →
                ‖-(exercisePerronEndpoint m : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤
                  exercisePerronEndpoint m ^ β +
                    (N : ℝ) * Real.exp (-c * Real.sqrt (exerciseMajorLog N)) := by
  obtain ⟨c, hc, hbound⟩ := exercise_exceptionalTerm_absorbed A
  refine ⟨c, hc, ?_⟩
  filter_upwards [hbound] with N hN
  intro q hq hqcut χ m hm hmsqrt β hβhalf hβone hχprim hχreal hzero
  letI : NeZero q := hq
  have hx : 0 < exercisePerronEndpoint m := by
    dsimp [exercisePerronEndpoint]
    positivity
  have hβpos : 0 < β := by linarith
  have habsorbed := hN q hq hqcut χ m hm hmsqrt β hβhalf hβone hχprim hχreal hzero
  have hexcess := (perron_real_zero_residue_excess_nonneg_le_rpow
    (exercisePerronEndpoint m) β hx hβhalf.le hβone.le).2
  rw [norm_perron_real_zero_residue_eq_rpow_add_excess
    (exercisePerronEndpoint m) β hx hβpos]
  exact add_le_add le_rfl (hexcess.trans habsorbed)

/-- A fixed logarithmic power times square-root-log exponential decay tends
to zero. This scalar fact is used for each analytic error in MA05. -/
theorem exercise_eventually_majorLog_pow_exp_small (K : ℕ) {d r : ℝ}
    (hd : 0 < d) (hr : 0 < r) :
    ∀ᶠ N : ℕ in atTop,
      exerciseMajorLog N ^ K *
        Real.exp (-d * Real.sqrt (exerciseMajorLog N)) ≤ r := by
  have harg : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop := by
    convert tendsto_atTop_add_const_right _ (2 : ℝ)
      tendsto_natCast_atTop_atTop using 1
  have hlog : Tendsto exerciseMajorLog atTop atTop :=
    Real.tendsto_log_atTop.comp harg
  have hroot : Tendsto (fun N : ℕ => Real.sqrt (exerciseMajorLog N))
      atTop atTop := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hlog
  have hlimit : Tendsto
      (fun N : ℕ =>
        (Real.sqrt (exerciseMajorLog N)) ^ (2 * K) *
          Real.exp (-d * Real.sqrt (exerciseMajorLog N)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_natCast] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        ((2 * K : ℕ) : ℝ) d hd).comp hroot
  have hnorm (N : ℕ) :
      (Real.sqrt (exerciseMajorLog N)) ^ (2 * K) =
        exerciseMajorLog N ^ K := by
    rw [pow_mul, Real.sq_sqrt]
    dsimp [exerciseMajorLog]
    exact Real.log_nonneg (by
      have hNnonneg : (0 : ℝ) ≤ N := by positivity
      linarith)
  have hlimit' : Tendsto
      (fun N : ℕ => exerciseMajorLog N ^ K *
        Real.exp (-d * Real.sqrt (exerciseMajorLog N)))
      atTop (𝓝 0) := by
    simpa only [hnorm] using hlimit
  filter_upwards [hlimit'.eventually (Iio_mem_nhds hr)] with N hN
  exact hN.le

/-- The admissible modulus and height give an explicit square-root-log budget. -/
theorem perron_log_height_budget
    (L H : ℝ) (A q : ℕ) [NeZero q] (hL : 1 ≤ L)
    (hq : (q : ℝ) ≤ L ^ A) (hH : 2 ≤ H)
    (hHupper : H ≤ 2 * Real.exp (Real.sqrt L)) :
    Real.log (28 * (q : ℝ) * (H + 4)) + 1 ≤
      (2 * (A : ℝ) + 170) * Real.sqrt L := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hHpos : 0 < H + 4 := by linarith
  have hsqrt : 1 ≤ Real.sqrt L := by
    exact (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) hLpos.le).mpr (by simpa using hL)
  have hsqrtpos : 0 < Real.sqrt L := lt_of_lt_of_le zero_lt_one hsqrt
  have hexp : 1 ≤ Real.exp (Real.sqrt L) := Real.one_le_exp_iff.mpr (Real.sqrt_nonneg L)
  have hHfour : H + 4 ≤ 6 * Real.exp (Real.sqrt L) := by linarith
  have hlogq : Real.log (q : ℝ) ≤ (A : ℝ) * Real.log L := by
    have h := Real.log_le_log hqpos hq
    rwa [Real.log_pow] at h
  have hlogL : Real.log L ≤ 2 * Real.sqrt L := by
    have h := Real.log_le_sub_one_of_pos hsqrtpos
    rw [Real.log_sqrt hLpos.le] at h
    linarith
  have hAlog := mul_le_mul_of_nonneg_left hlogL (Nat.cast_nonneg A)
  have hlogH : Real.log (H + 4) ≤ Real.log 6 + Real.sqrt L := by
    have h := Real.log_le_log hHpos hHfour
    rwa [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h
  have hlog168 : Real.log 28 + Real.log 6 ≤ 167 := by
    rw [← Real.log_mul (by norm_num : (28 : ℝ) ≠ 0) (by norm_num : (6 : ℝ) ≠ 0)]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 168)
    norm_num at h ⊢
    exact h
  have hsplit : Real.log (28 * (q : ℝ) * (H + 4)) =
      Real.log 28 + Real.log (q : ℝ) + Real.log (H + 4) := by
    rw [Real.log_mul (mul_pos (by norm_num) hqpos).ne' hHpos.ne',
      Real.log_mul (by norm_num) hqpos.ne']
  rw [hsplit]
  nlinarith

#print axioms perron_log_height_budget

/-- A left edge inside the zero-free strip gives decay on the ambient prefix scale. -/
theorem perron_left_edge_endpoint_decay
    (c x N L ell B σ : ℝ) (hc : 0 < c) (hx : 1 ≤ x)
    (hlog : L / 4 ≤ Real.log x) (hxN : x ≤ 2 * N)
    (hell : 0 < ell) (hB : 0 < B) (hellUpper : ell ≤ B * Real.sqrt L)
    (hσ : σ ≤ 1 - c / (2 * ell)) :
    x ^ σ ≤ 2 * N * Real.exp (-(c / (8 * B)) * Real.sqrt L) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hsqrtpos : 0 < Real.sqrt L := by
    by_contra h
    have hzero : Real.sqrt L = 0 := le_antisymm (le_of_not_gt h) (Real.sqrt_nonneg L)
    rw [hzero, mul_zero] at hellUpper
    linarith
  have hLpos : 0 < L := Real.sqrt_pos.mp hsqrtpos
  have hscaled := mul_le_mul_of_nonneg_right hellUpper (Real.sqrt_nonneg L)
  have hratio : Real.sqrt L / B ≤ L / ell := by
    apply (div_le_div_iff₀ hB hell).mpr
    rw [mul_assoc, ← sq, Real.sq_sqrt hLpos.le] at hscaled
    nlinarith
  have hratioScaled := mul_le_mul_of_nonneg_left hratio (show 0 ≤ c / 8 by positivity)
  have hfirst : (c / (8 * B)) * Real.sqrt L ≤ (c / (2 * ell)) * (L / 4) := by
    have hleft : (c / 8) * (Real.sqrt L / B) = (c / (8 * B)) * Real.sqrt L := by ring
    have hright : (c / 8) * (L / ell) = (c / (2 * ell)) * (L / 4) := by ring
    rwa [hleft, hright] at hratioScaled
  have hdecay : (c / (8 * B)) * Real.sqrt L ≤ (c / (2 * ell)) * Real.log x :=
    hfirst.trans (mul_le_mul_of_nonneg_left hlog (by positivity))
  have hlogNonneg : 0 ≤ Real.log x := Real.log_nonneg hx
  have hpow : x ^ σ ≤ x * Real.exp (-(c / (2 * ell)) * Real.log x) := by
    rw [Real.rpow_def_of_pos hxpos]
    calc
      Real.exp (Real.log x * σ) ≤ Real.exp (Real.log x * (1 - c / (2 * ell))) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hσ hlogNonneg)
      _ = Real.exp (Real.log x + (-(c / (2 * ell)) * Real.log x)) := by congr 1; ring
      _ = x * Real.exp (-(c / (2 * ell)) * Real.log x) := by
        rw [Real.exp_add, Real.exp_log hxpos]
  calc
    x ^ σ ≤ x * Real.exp (-(c / (2 * ell)) * Real.log x) := hpow
    _ ≤ x * Real.exp (-(c / (8 * B)) * Real.sqrt L) := by
      apply mul_le_mul_of_nonneg_left _ hxpos.le
      apply Real.exp_le_exp.mpr
      nlinarith
    _ ≤ 2 * N * Real.exp (-(c / (8 * B)) * Real.sqrt L) :=
      mul_le_mul_of_nonneg_right hxN (Real.exp_pos _).le

#print axioms perron_left_edge_endpoint_decay

set_option maxHeartbeats 0 in

/-- The vertical and horizontal edge norm payments are absorbed uniformly over the
polylogarithmic moduli, prefixes, and allowed Perron heights. -/
theorem perron_scalar_edge_payment (A : ℕ) (c K : ℝ)
    (hc : 0 < c) (hK : 0 < K) :
    ∃ C d : ℝ, 0 < C ∧ 0 < d ∧
      ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, ∀ (_hq : NeZero q),
        letI : NeZero q := _hq
        q ≤ logarithmicDenominatorCutoff A N →
        ∀ m : ℕ, m ≤ N → Real.sqrt (N : ℝ) < (m : ℝ) →
        ∀ H σ : ℝ,
          Real.exp (Real.sqrt (exerciseMajorLog m)) ≤ H →
          H ≤ 2 * Real.exp (Real.sqrt (exerciseMajorLog m)) →
          2 ≤ H → σ ≤ 1 - c / (2 * (Real.log (28 * (q : ℝ) * (H + 4)) + 1)) →
          6 * K * (Real.log (28 * (q : ℝ) * (H + 4)) + 1) ^ 2 *
              exercisePerronEndpoint m ^ σ * Real.log (H + 1) +
            4 * Real.exp 1 * K *
              (Real.log (28 * (q : ℝ) * (H + 4)) + 1) ^ 2 * (m : ℝ) / H ≤
            C * (N : ℝ) * Real.exp (-d * Real.sqrt (exerciseMajorLog N)) := by
  let B : ℝ := 2 * (A : ℝ) + 170
  let d₀ : ℝ := min (c / (8 * B)) (1 / 2)
  have hB : 0 < B := by dsimp [B]; positivity
  have hd₀ : 0 < d₀ := by dsimp [d₀]; positivity
  refine ⟨(36 + 4 * Real.exp 1) * K * B ^ 2, d₀ / 2, ?_, by positivity, ?_⟩
  · positivity
  have hloglim : Tendsto exerciseMajorLog atTop atTop := by
    have harg : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop := by
      convert tendsto_atTop_add_const_right _ (2 : ℝ)
        tendsto_natCast_atTop_atTop using 1
    exact Real.tendsto_log_atTop.comp harg
  filter_upwards [exercise_eventually_majorLog_pow_exp_small 2
      (d := d₀ / 2) (r := 1) (by positivity) (by norm_num),
    eventually_ge_atTop (4 : ℕ), hloglim.eventually_ge_atTop 1] with N hpoly hN hLone
  intro q hq
  letI : NeZero q := hq
  intro hqcut m hm hmsqrt H σ hHlower hHupper hHtwo hσ
  let L : ℝ := exerciseMajorLog N
  let Lm : ℝ := exerciseMajorLog m
  let x : ℝ := exercisePerronEndpoint m
  let ell : ℝ := Real.log (28 * (q : ℝ) * (H + 4)) + 1
  have hNfour : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : 0 < (N : ℝ) := by linarith
  have hL : 1 ≤ L := by simpa [L] using hLone
  have hLnonneg : 0 ≤ L := le_trans (by norm_num) hL
  have hLmnonneg : 0 ≤ Lm := by
    dsimp [Lm, exerciseMajorLog]
    exact Real.log_nonneg (by
      have hmnonneg : (0 : ℝ) ≤ m := by positivity
      linarith)
  have hmN : (m : ℝ) ≤ N := by exact_mod_cast hm
  have hLmLe : Lm ≤ L := by
    dsimp [Lm, L, exerciseMajorLog]
    exact Real.log_le_log (by positivity) (by exact_mod_cast (show m + 2 ≤ N + 2 by omega))
  have hrootLmLe : Real.sqrt Lm ≤ Real.sqrt L := Real.sqrt_le_sqrt hLmLe
  have hHupperL : H ≤ 2 * Real.exp (Real.sqrt L) := by
    dsimp [L] at *
    exact hHupper.trans (by gcongr)
  have hqL : (q : ℝ) ≤ L ^ A := by
    have hqcutReal : (q : ℝ) ≤ logarithmicDenominatorCutoff A N := by exact_mod_cast hqcut
    exact hqcutReal.trans (by simpa [L, exerciseMajorLog] using logarithmicDenominatorCutoff_le_log_pow A N)
  have hbudget := perron_log_height_budget L H A q hL hqL hHtwo hHupperL
  have hellUpper : ell ≤ B * Real.sqrt L := by
    dsimp [ell, B]
    exact hbudget
  have hellpos : 0 < ell := by
    dsimp [ell]
    have hqpos : 0 < (q : ℝ) := by exact_mod_cast NeZero.pos q
    have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
    have harg : 1 ≤ 28 * (q : ℝ) * (H + 4) := by nlinarith [hqone, hHtwo]
    have hlog : 0 ≤ Real.log (28 * (q : ℝ) * (H + 4)) := Real.log_nonneg harg
    linarith
  have hx : 1 ≤ x := by
    dsimp [x, exercisePerronEndpoint]
    have hrootTwo : (2 : ℝ) ≤ Real.sqrt (N : ℝ) := by
      have hsq := Real.sq_sqrt hNpos.le
      nlinarith [Real.sqrt_nonneg (N : ℝ)]
    have hmTwo : (2 : ℝ) ≤ m := by linarith
    nlinarith
  have hxN : x ≤ 2 * N := by
    dsimp [x, exercisePerronEndpoint]
    nlinarith
  have hlogPrefix : Real.log (N : ℝ) / 2 ≤ Real.log (m : ℝ) := by
    have h := Real.log_le_log (Real.sqrt_pos.mpr hNpos) hmsqrt.le
    rw [Real.log_sqrt hNpos.le] at h
    exact h
  have hLlogN : L ≤ 2 * Real.log (N : ℝ) := by
    have hNsq : (N : ℝ) + 2 ≤ (N : ℝ) ^ 2 := by nlinarith [hNfour]
    have h := Real.log_le_log (by positivity : 0 < (N : ℝ) + 2) hNsq
    rw [Real.log_pow] at h
    simpa only [L, exerciseMajorLog, Nat.cast_ofNat] using h
  have hlogx : L / 4 ≤ Real.log x := by
    have hmpos : 0 < (m : ℝ) := lt_of_le_of_lt (Real.sqrt_nonneg _) hmsqrt
    have hlogmLm : Real.log (m : ℝ) ≤ Lm := by
      dsimp [Lm, exerciseMajorLog]
      exact Real.log_le_log hmpos (by linarith)
    have hlogm_le_x : Real.log (m : ℝ) ≤ Real.log x := by
      apply Real.log_le_log hmpos
      dsimp [x, exercisePerronEndpoint]
      linarith
    dsimp [L]
    linarith
  have hendpoint := perron_left_edge_endpoint_decay c x N L ell B σ hc hx
    hlogx hxN hellpos hB hellUpper hσ
  have hsqrtL : 1 ≤ Real.sqrt L := (Real.one_le_sqrt).2 hL
  have hlogH : Real.log (H + 1) ≤ 3 * Real.sqrt L := by
    have hExp : 1 ≤ Real.exp (Real.sqrt L) := Real.one_le_exp_iff.mpr (Real.sqrt_nonneg L)
    have hHplus : H + 1 ≤ 3 * Real.exp (Real.sqrt L) := by
      have h := hHupperL
      have hexp := Real.exp_pos (Real.sqrt L)
      linarith
    have hlog := Real.log_le_log (by linarith : 0 < H + 1) hHplus
    have hlog3 : Real.log 3 ≤ 2 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at hlog
    linarith
  have hLmLower : L / 4 ≤ Lm := by
    have hmpos : 0 < (m : ℝ) := lt_of_le_of_lt (Real.sqrt_nonneg _) hmsqrt
    have hlogm : Real.log (m : ℝ) ≤ Lm := by
      dsimp [Lm, exerciseMajorLog]
      exact Real.log_le_log hmpos (by linarith)
    have hlogmLow : L / 4 ≤ Real.log (m : ℝ) := by
      linarith [hlogPrefix, hLlogN]
    exact hlogmLow.trans hlogm
  have hsqrtLower : Real.sqrt L / 2 ≤ Real.sqrt Lm := by
    nlinarith [Real.sq_sqrt hLnonneg, Real.sq_sqrt hLmnonneg,
      Real.sqrt_nonneg L, Real.sqrt_nonneg Lm]
  have hHlower' : Real.exp (Real.sqrt L / 2) ≤ H := by
    exact (Real.exp_le_exp.mpr hsqrtLower).trans hHlower
  have hmOverH : (m : ℝ) / H ≤ (N : ℝ) * Real.exp (-(1 / 2 : ℝ) * Real.sqrt L) := by
    have hrecip : H⁻¹ ≤ Real.exp (-(1 / 2 : ℝ) * Real.sqrt L) := by
      have h := one_div_le_one_div_of_le (Real.exp_pos _) hHlower'
      simpa [one_div, ← Real.exp_neg, div_eq_mul_inv, mul_comm] using h
    rw [div_eq_mul_inv]
    calc
      (m : ℝ) * H⁻¹ ≤ (N : ℝ) * H⁻¹ := mul_le_mul_of_nonneg_right hmN (inv_nonneg.mpr (le_of_lt (by linarith : 0 < H)))
      _ ≤ (N : ℝ) * Real.exp (-(1 / 2 : ℝ) * Real.sqrt L) := mul_le_mul_of_nonneg_left hrecip hNpos.le
  have hd0a : d₀ ≤ c / (8 * B) := by dsimp [d₀]; exact min_le_left _ _
  have hd0b : d₀ ≤ 1 / 2 := by dsimp [d₀]; exact min_le_right _ _
  have hdecayA : Real.exp (-(c / (8 * B)) * Real.sqrt L) ≤ Real.exp (-d₀ * Real.sqrt L) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hd0a (Real.sqrt_nonneg L)]
  have hdecayB : Real.exp (-(1 / 2 : ℝ) * Real.sqrt L) ≤ Real.exp (-d₀ * Real.sqrt L) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hd0b (Real.sqrt_nonneg L)]
  have hellsq : ell ^ 2 ≤ B ^ 2 * L := by
    have h := mul_le_mul_of_nonneg_left hellUpper (le_of_lt hB)
    nlinarith [Real.sq_sqrt hLnonneg]
  have hLleLtwo : L ≤ L ^ 2 := by nlinarith [hL]
  have hsqrtleL : Real.sqrt L ≤ L := by
    have hsq := Real.sq_sqrt hLnonneg
    nlinarith [hsqrtL]
  have hLSqrt : L * Real.sqrt L ≤ L ^ 2 := by
    calc
      L * Real.sqrt L ≤ L * L := mul_le_mul_of_nonneg_left hsqrtleL hLnonneg
      _ = L ^ 2 := by ring
  have hlogHnonneg : 0 ≤ Real.log (H + 1) :=
    Real.log_nonneg (by linarith : (1 : ℝ) ≤ H + 1)
  have hfirst : 6 * K * ell ^ 2 * x ^ σ * Real.log (H + 1) ≤
      36 * K * B ^ 2 * (N : ℝ) * L ^ 2 * Real.exp (-d₀ * Real.sqrt L) := by
    calc
      _ ≤ 6 * K * (B ^ 2 * L) * (2 * N * Real.exp (-(c / (8 * B)) * Real.sqrt L)) * (3 * Real.sqrt L) := by
        gcongr
      _ ≤ 36 * K * B ^ 2 * (N : ℝ) * L ^ 2 * Real.exp (-d₀ * Real.sqrt L) := by
        rw [show 6 * K * (B ^ 2 * L) * (2 * N * Real.exp (-(c / (8 * B)) * Real.sqrt L)) * (3 * Real.sqrt L) =
          36 * K * B ^ 2 * (N : ℝ) * (L * Real.sqrt L) * Real.exp (-(c / (8 * B)) * Real.sqrt L) by ring]
        gcongr
  have hsecond : 4 * Real.exp 1 * K * ell ^ 2 * (m : ℝ) / H ≤
      4 * Real.exp 1 * K * B ^ 2 * (N : ℝ) * L ^ 2 * Real.exp (-d₀ * Real.sqrt L) := by
    calc
      _ ≤ 4 * Real.exp 1 * K * (B ^ 2 * L) *
          ((N : ℝ) * Real.exp (-(1 / 2 : ℝ) * Real.sqrt L)) := by
        rw [show 4 * Real.exp 1 * K * ell ^ 2 * (m : ℝ) / H =
          4 * Real.exp 1 * K * ell ^ 2 * ((m : ℝ) / H) by ring]
        gcongr
      _ ≤ _ := by
        rw [show 4 * Real.exp 1 * K * (B ^ 2 * L) *
          ((N : ℝ) * Real.exp (-(1 / 2 : ℝ) * Real.sqrt L)) =
          4 * Real.exp 1 * K * B ^ 2 * (N : ℝ) * L *
            Real.exp (-(1 / 2 : ℝ) * Real.sqrt L) by ring]
        gcongr
  have hsum :
      6 * K * ell ^ 2 * x ^ σ * Real.log (H + 1) +
        4 * Real.exp 1 * K * ell ^ 2 * (m : ℝ) / H ≤
      ((36 + 4 * Real.exp 1) * K * B ^ 2) * (N : ℝ) *
        (L ^ 2 * Real.exp (-d₀ * Real.sqrt L)) := by
    nlinarith [hfirst, hsecond]
  have hsmall : L ^ 2 * Real.exp (-d₀ * Real.sqrt L) ≤
      Real.exp (-(d₀ / 2) * Real.sqrt L) := by
    have h := hpoly
    have h' : L ^ 2 * Real.exp (-(d₀ / 2) * Real.sqrt L) ≤ 1 := by
      simpa [L, exerciseMajorLog, div_eq_mul_inv, mul_assoc] using h
    calc
      L ^ 2 * Real.exp (-d₀ * Real.sqrt L) =
          (L ^ 2 * Real.exp (-(d₀ / 2) * Real.sqrt L)) *
            Real.exp (-(d₀ / 2) * Real.sqrt L) := by
          have hexp : Real.exp (-d₀ * Real.sqrt L) =
              Real.exp (-(d₀ / 2) * Real.sqrt L) *
                Real.exp (-(d₀ / 2) * Real.sqrt L) := by
            calc
              _ = Real.exp (-(d₀ / 2) * Real.sqrt L + -(d₀ / 2) * Real.sqrt L) := by
                congr 1
                ring
              _ = _ := Real.exp_add _ _
          rw [hexp]
          ring
      _ ≤ 1 * Real.exp (-(d₀ / 2) * Real.sqrt L) := by gcongr
      _ = _ := by ring
  have hfinal := hsum.trans (by
    apply mul_le_mul_of_nonneg_left hsmall
    positivity)
  simpa [L, x, ell, B] using hfinal

#print axioms perron_scalar_edge_payment

/-- The principal modulus-one Perron contour inherits a root-log saving from
the imported strong PNT and the explicit finite Perron error. -/
theorem exercise_principalPerron_integral_strongPNT :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ᶠ m : ℕ in atTop,
        ‖exercisePerronIntegral 1 (1 : DirichletCharacter ℂ 1) m
              (Real.exp (Real.sqrt (exerciseMajorLog m))) -
            exerciseCharacterPole 1 (1 : DirichletCharacter ℂ 1) m‖ ≤
          C * (m : ℝ) * Real.exp (-c * Real.sqrt (Real.log (m : ℝ))) := by
  obtain ⟨CP, cP, hCP, hcP, hPNT⟩ := exercise_principalTwistedPsi_strongPNT
  let c : ℝ := min cP (1 / 2)
  let K : ℝ := 2 * (3456 + 216 * Real.exp 1)
  let C : ℝ := CP + K + 1
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min hcP (by norm_num)
  have hC : 0 < C := by dsimp [C, K]; positivity
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨C, c, hC, hc, ?_⟩
  filter_upwards [hPNT,
    exercise_eventually_majorLog_pow_exp_small 2 (d := 1 / 2) (r := 1)
      (by norm_num) (by norm_num),
    hlog.eventually_ge_atTop 4, Filter.eventually_ge_atTop 2]
    with m hPNT hpoly hlog4 hm
  let L : ℝ := exerciseMajorLog m
  let H : ℝ := Real.exp (Real.sqrt L)
  have hmPos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hlogPos : 0 < Real.log (m : ℝ) := by linarith
  have hLnonneg : 0 ≤ L := by
    dsimp [L, exerciseMajorLog]
    apply Real.log_nonneg
    have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hlogLe : Real.log (m : ℝ) ≤ L := by
    dsimp [L, exerciseMajorLog]
    apply Real.log_le_log hmPos
    linarith
  have hrootLe : Real.sqrt (Real.log (m : ℝ)) ≤ Real.sqrt L :=
    Real.sqrt_le_sqrt hlogLe
  have hcHalf : c ≤ 1 / 2 := by dsimp [c]; exact min_le_right _ _
  have hhalfExp :
      Real.exp (-(1 / 2 : ℝ) * Real.sqrt L) ≤
        Real.exp (-c * Real.sqrt (Real.log (m : ℝ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hrootLe (show 0 ≤ c by exact hc.le),
      mul_le_mul_of_nonneg_right hcHalf (Real.sqrt_nonneg (Real.log (m : ℝ)))]
  have hpoly' : L ^ 2 * Real.exp (-(1 / 2 : ℝ) * Real.sqrt L) ≤ 1 := by
    simpa [L, exerciseMajorLog, Real.sqrt_eq_rpow] using hpoly
  have hfactor : L ^ 2 * Real.exp (-Real.sqrt L) ≤
      Real.exp (-c * Real.sqrt (Real.log (m : ℝ))) := by
    rw [show -Real.sqrt L =
      -(1 / 2 : ℝ) * Real.sqrt L + -(1 / 2 : ℝ) * Real.sqrt L by ring,
      Real.exp_add]
    calc
      L ^ 2 * (Real.exp (-(1 / 2 : ℝ) * Real.sqrt L) *
          Real.exp (-(1 / 2 : ℝ) * Real.sqrt L)) =
          (L ^ 2 * Real.exp (-(1 / 2 : ℝ) * Real.sqrt L)) *
            Real.exp (-(1 / 2 : ℝ) * Real.sqrt L) := by ring
      _ ≤ 1 * Real.exp (-(1 / 2 : ℝ) * Real.sqrt L) :=
        mul_le_mul_of_nonneg_right hpoly' (by positivity)
      _ ≤ Real.exp (-c * Real.sqrt (Real.log (m : ℝ))) := by
        simpa using hhalfExp
  have hbudget :
      (m : ℝ) * L ^ 2 / H ≤
        (m : ℝ) * Real.exp (-c * Real.sqrt (Real.log (m : ℝ))) := by
    dsimp [H]
    rw [div_eq_mul_inv, ← Real.exp_neg]
    calc
      (m : ℝ) * L ^ 2 * Real.exp (-Real.sqrt L) =
          (m : ℝ) * (L ^ 2 * Real.exp (-Real.sqrt L)) := by ring
      _ ≤ (m : ℝ) * Real.exp (-c * Real.sqrt (Real.log (m : ℝ))) :=
        mul_le_mul_of_nonneg_left hfactor hmPos.le
  have hMA01 := exercise_truncatedPerron_error_explicit 1
    (1 : DirichletCharacter ℂ 1) m H (by omega : 2 ≤ m) (by positivity)
  have htrunc :
      ‖exerciseTwistedPsi 1 (1 : DirichletCharacter ℂ 1) m -
          exercisePerronIntegral 1 (1 : DirichletCharacter ℂ 1) m H‖ ≤
        K * (m : ℝ) * Real.exp (-c * Real.sqrt (Real.log (m : ℝ))) := by
    have hMA01' : ‖exerciseTwistedPsi 1 (1 : DirichletCharacter ℂ 1) m -
        exercisePerronIntegral 1 (1 : DirichletCharacter ℂ 1) m H‖ ≤
          K * ((m : ℝ) * L ^ 2 / H) := by
      simpa [K, L, H, exerciseMajorLog] using hMA01
    calc
      _ ≤ K * ((m : ℝ) * L ^ 2 / H) := hMA01'
      _ ≤ K * ((m : ℝ) * Real.exp (-c * Real.sqrt (Real.log (m : ℝ)))) :=
        mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ = K * (m : ℝ) * Real.exp (-c * Real.sqrt (Real.log (m : ℝ))) := by ring
  have hPNT' :
      ‖exerciseTwistedPsi 1 (1 : DirichletCharacter ℂ 1) m - (m : ℂ)‖ ≤
        CP * (m : ℝ) * Real.exp (-c * Real.sqrt (Real.log (m : ℝ))) := by
    have hcLe : c ≤ cP := by dsimp [c]; exact min_le_left _ _
    calc
      _ ≤ CP * (m : ℝ) *
          Real.exp (-cP * Real.sqrt (Real.log (m : ℝ))) := hPNT
      _ ≤ CP * (m : ℝ) *
          Real.exp (-c * Real.sqrt (Real.log (m : ℝ))) := by
        gcongr
  have hrootBound : Real.sqrt (Real.log (m : ℝ)) ≤ Real.log (m : ℝ) / 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [hlog4]
  have hgapExp : 0 ≤ Real.log (m : ℝ) -
      c * Real.sqrt (Real.log (m : ℝ)) := by
    have hcroot := mul_le_mul_of_nonneg_left hrootBound (show 0 ≤ c by exact hc.le)
    nlinarith [hcHalf]
  have hgap : (1 / 2 : ℝ) ≤
      (m : ℝ) * Real.exp (-c * Real.sqrt (Real.log (m : ℝ))) := by
    have hone : 1 ≤ Real.exp
        (Real.log (m : ℝ) - c * Real.sqrt (Real.log (m : ℝ))) :=
      Real.one_le_exp_iff.mpr hgapExp
    have hid : Real.exp
        (Real.log (m : ℝ) - c * Real.sqrt (Real.log (m : ℝ))) =
          (m : ℝ) * Real.exp (-c * Real.sqrt (Real.log (m : ℝ))) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hmPos]
      congr 2
      ring
    rw [hid] at hone
    linarith
  have hdecomp :
      exercisePerronIntegral 1 (1 : DirichletCharacter ℂ 1) m H -
          exerciseCharacterPole 1 (1 : DirichletCharacter ℂ 1) m =
        (exercisePerronIntegral 1 (1 : DirichletCharacter ℂ 1) m H -
          exerciseTwistedPsi 1 (1 : DirichletCharacter ℂ 1) m) +
        (exerciseTwistedPsi 1 (1 : DirichletCharacter ℂ 1) m - (m : ℂ)) +
        ((m : ℂ) - exerciseCharacterPole 1 (1 : DirichletCharacter ℂ 1) m) := by
    ring
  have hPole : ‖(m : ℂ) -
      exerciseCharacterPole 1 (1 : DirichletCharacter ℂ 1) m‖ = 1 / 2 := by
    simp [exerciseCharacterPole, exercisePerronEndpoint]
  have htruncRev :
      ‖exercisePerronIntegral 1 (1 : DirichletCharacter ℂ 1) m H -
          exerciseTwistedPsi 1 (1 : DirichletCharacter ℂ 1) m‖ ≤
        K * ((m : ℝ) * Real.exp (-c * Real.sqrt (Real.log (m : ℝ)))) := by
    calc
      _ = ‖exerciseTwistedPsi 1 (1 : DirichletCharacter ℂ 1) m -
          exercisePerronIntegral 1 (1 : DirichletCharacter ℂ 1) m H‖ := by
        rw [show exercisePerronIntegral 1 (1 : DirichletCharacter ℂ 1) m H -
            exerciseTwistedPsi 1 (1 : DirichletCharacter ℂ 1) m =
              -(exerciseTwistedPsi 1 (1 : DirichletCharacter ℂ 1) m -
                exercisePerronIntegral 1 (1 : DirichletCharacter ℂ 1) m H) by ring,
          norm_neg]
      _ ≤ K * (m : ℝ) * Real.exp (-c * Real.sqrt (Real.log (m : ℝ))) := htrunc
      _ = K * ((m : ℝ) * Real.exp (-c * Real.sqrt (Real.log (m : ℝ)))) := by ring
  have hPNT'' :
      ‖exerciseTwistedPsi 1 (1 : DirichletCharacter ℂ 1) m - (m : ℂ)‖ ≤
        CP * ((m : ℝ) * Real.exp (-c * Real.sqrt (Real.log (m : ℝ)))) := by
    calc
      _ ≤ CP * (m : ℝ) * Real.exp (-c * Real.sqrt (Real.log (m : ℝ))) := hPNT'
      _ = CP * ((m : ℝ) * Real.exp (-c * Real.sqrt (Real.log (m : ℝ)))) := by ring
  have hsum :
      ‖exercisePerronIntegral 1 (1 : DirichletCharacter ℂ 1) m H -
          exerciseTwistedPsi 1 (1 : DirichletCharacter ℂ 1) m‖ +
        ‖exerciseTwistedPsi 1 (1 : DirichletCharacter ℂ 1) m - (m : ℂ)‖ +
        1 / 2 ≤ (CP + K + 1) *
          ((m : ℝ) * Real.exp (-c * Real.sqrt (Real.log (m : ℝ)))) := by
    calc
      _ ≤ K * ((m : ℝ) * Real.exp (-c * Real.sqrt (Real.log (m : ℝ)))) +
          CP * ((m : ℝ) * Real.exp (-c * Real.sqrt (Real.log (m : ℝ)))) +
          (m : ℝ) * Real.exp (-c * Real.sqrt (Real.log (m : ℝ))) := by
        exact add_le_add (add_le_add htruncRev hPNT'') hgap
      _ = _ := by ring
  rw [hdecomp]
  calc
    _ ≤ ‖exercisePerronIntegral 1 (1 : DirichletCharacter ℂ 1) m H -
          exerciseTwistedPsi 1 (1 : DirichletCharacter ℂ 1) m‖ +
        ‖exerciseTwistedPsi 1 (1 : DirichletCharacter ℂ 1) m - (m : ℂ)‖ +
        ‖(m : ℂ) - exerciseCharacterPole 1 (1 : DirichletCharacter ℂ 1) m‖ := by
      calc
        _ ≤ ‖(exercisePerronIntegral 1 (1 : DirichletCharacter ℂ 1) m H -
              exerciseTwistedPsi 1 (1 : DirichletCharacter ℂ 1) m) +
              (exerciseTwistedPsi 1 (1 : DirichletCharacter ℂ 1) m - (m : ℂ))‖ +
            ‖(m : ℂ) - exerciseCharacterPole 1 (1 : DirichletCharacter ℂ 1) m‖ :=
              norm_add_le _ _
        _ ≤ _ := add_le_add (norm_add_le _ _) le_rfl
    _ = ‖exercisePerronIntegral 1 (1 : DirichletCharacter ℂ 1) m H -
          exerciseTwistedPsi 1 (1 : DirichletCharacter ℂ 1) m‖ +
        ‖exerciseTwistedPsi 1 (1 : DirichletCharacter ℂ 1) m - (m : ℂ)‖ +
        1 / 2 := by rw [hPole]
    _ ≤ (CP + K + 1) *
        ((m : ℝ) * Real.exp (-c * Real.sqrt (Real.log (m : ℝ)))) := hsum
    _ = C * (m : ℝ) * Real.exp (-c * Real.sqrt (Real.log (m : ℝ))) := by
      dsimp [C]
      ring

/-- The conductor-one principal lane satisfies MA03's uniform ambient-scale
bound, including every prescribed height-range condition. The threshold is
chosen before the prefix `m`, rather than separately for each prefix. -/
theorem exercise_shiftedPerron_principal_modulus_one :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, m ≤ N →
        Real.sqrt (N : ℝ) < (m : ℝ) →
          ∃ H : ℝ,
            Real.exp (Real.sqrt (exerciseMajorLog m)) ≤ H ∧
            H ≤ 2 * Real.exp (Real.sqrt (exerciseMajorLog m)) ∧
            2 ≤ H ∧ H ≤ (m : ℝ) ∧
            ‖exercisePerronIntegral 1 (1 : DirichletCharacter ℂ 1) m H -
              exerciseCharacterPole 1 (1 : DirichletCharacter ℂ 1) m‖ ≤
                C * (N : ℝ) * Real.exp (-c * Real.sqrt (exerciseMajorLog N)) := by
  obtain ⟨C, c, hC, hc, hprincipal⟩ := exercise_principalPerron_integral_strongPNT
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hgood : ∀ᶠ m : ℕ in atTop,
      ‖exercisePerronIntegral 1 (1 : DirichletCharacter ℂ 1) m
          (Real.exp (Real.sqrt (exerciseMajorLog m))) -
        exerciseCharacterPole 1 (1 : DirichletCharacter ℂ 1) m‖ ≤
          C * (m : ℝ) * Real.exp (-c * Real.sqrt (Real.log (m : ℝ))) ∧
      4 ≤ Real.log (m : ℝ) ∧ 2 ≤ m := by
    filter_upwards [hprincipal, hlog.eventually_ge_atTop 4,
      eventually_ge_atTop (2 : ℕ)] with m hp hl hm
    exact ⟨hp, hl, hm⟩
  obtain ⟨M, hM⟩ := eventually_atTop.1 hgood
  have hroot : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨C, c / 2, hC, by positivity, ?_⟩
  filter_upwards [hroot.eventually_ge_atTop (M : ℝ),
    eventually_ge_atTop (4 : ℕ)] with N hNM hN
  intro m hm hmsqrt
  have hmM : M ≤ m := by exact_mod_cast hNM.trans hmsqrt.le
  obtain ⟨hbound, hlogm, hmTwo⟩ := hM m hmM
  have hmPos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hNfour : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : 0 < (N : ℝ) := by linarith
  have hmN : (m : ℝ) ≤ N := by exact_mod_cast hm
  let L : ℝ := exerciseMajorLog N
  let Lm : ℝ := exerciseMajorLog m
  let H : ℝ := Real.exp (Real.sqrt Lm)
  have hLnonneg : 0 ≤ L := by
    dsimp [L, exerciseMajorLog]
    exact Real.log_nonneg (by linarith)
  have hLmnonneg : 0 ≤ Lm := by
    dsimp [Lm, exerciseMajorLog]
    exact Real.log_nonneg (by linarith)
  have hlogmLm : Real.log (m : ℝ) ≤ Lm := by
    dsimp [Lm, exerciseMajorLog]
    exact Real.log_le_log hmPos (by linarith)
  have hmsq : (m : ℝ) + 2 ≤ (m : ℝ) ^ 2 := by
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hmTwo
    nlinarith
  have hLmUpper : Lm ≤ 2 * Real.log (m : ℝ) := by
    have h := Real.log_le_log (by positivity : 0 < (m : ℝ) + 2) hmsq
    rw [Real.log_pow] at h
    simpa only [Lm, exerciseMajorLog, Nat.cast_ofNat] using h
  have hheightUpper : H ≤ (m : ℝ) := by
    have hsqrt : Real.sqrt Lm ≤ Real.log (m : ℝ) := by
      rw [Real.sqrt_le_iff]
      constructor
      · linarith
      · nlinarith
    exact (Real.exp_le_exp.mpr hsqrt).trans_eq (Real.exp_log hmPos)
  have hheightLower : 2 ≤ H := by
    have hsq := Real.sq_sqrt hLmnonneg
    have hrootpos := Real.sqrt_nonneg Lm
    have hone : 1 ≤ Real.sqrt Lm := by nlinarith
    have hexp := Real.add_one_le_exp (Real.sqrt Lm)
    dsimp [H]
    linarith
  have hNsq : (N : ℝ) + 2 ≤ (N : ℝ) ^ 2 := by nlinarith
  have hLUpper : L ≤ 2 * Real.log (N : ℝ) := by
    have h := Real.log_le_log (by positivity : 0 < (N : ℝ) + 2) hNsq
    rw [Real.log_pow] at h
    simpa only [L, exerciseMajorLog, Nat.cast_ofNat] using h
  have hlogPrefix : Real.log (N : ℝ) / 2 ≤ Real.log (m : ℝ) := by
    have h := Real.log_le_log (Real.sqrt_pos.mpr hNpos) hmsqrt.le
    rw [Real.log_sqrt hNpos.le] at h
    exact h
  have hlogLower : L / 4 ≤ Real.log (m : ℝ) := by linarith
  have hsqrtLower : Real.sqrt L / 2 ≤ Real.sqrt (Real.log (m : ℝ)) := by
    have hsqL := Real.sq_sqrt hLnonneg
    have hsqm := Real.sq_sqrt (by linarith : 0 ≤ Real.log (m : ℝ))
    have hnL := Real.sqrt_nonneg L
    have hnm := Real.sqrt_nonneg (Real.log (m : ℝ))
    nlinarith
  have hexpCompare : Real.exp (-c * Real.sqrt (Real.log (m : ℝ))) ≤
      Real.exp (-(c / 2) * Real.sqrt L) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hsqrtLower hc.le]
  refine ⟨H, le_rfl, ?_, hheightLower, hheightUpper, ?_⟩
  · dsimp [H, Lm]
    nlinarith [Real.exp_pos (Real.sqrt (exerciseMajorLog m))]
  · calc
      _ ≤ C * (m : ℝ) *
          Real.exp (-c * Real.sqrt (Real.log (m : ℝ))) := hbound
      _ ≤ C * (N : ℝ) * Real.exp (-(c / 2) * Real.sqrt L) := by
        gcongr

/-- The MA01 error has a uniform root-log saving at every allowed Perron
height. This estimate is independent of the character and modulus. -/
theorem exercise_truncatedPerron_error_uniform_rootLog :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, ∀ (_hq : NeZero q),
      letI : NeZero q := _hq
      ∀ χ : DirichletCharacter ℂ q, ∀ m : ℕ, m ≤ N →
        Real.sqrt (N : ℝ) < (m : ℝ) → ∀ H : ℝ,
          Real.exp (Real.sqrt (exerciseMajorLog m)) ≤ H →
            ‖exerciseTwistedPsi q χ m - exercisePerronIntegral q χ m H‖ ≤
              (2 * (3456 + 216 * Real.exp 1)) * (N : ℝ) *
                Real.exp (-(1 / 4 : ℝ) * Real.sqrt (exerciseMajorLog N)) := by
  filter_upwards [exercise_eventually_majorLog_pow_exp_small 2
    (d := 1 / 4) (r := 1) (by norm_num) (by norm_num),
    eventually_ge_atTop (4 : ℕ)] with N hpoly hN
  intro q hq
  letI : NeZero q := hq
  intro χ m hm hmsqrt H hH
  let L : ℝ := exerciseMajorLog N
  let Lm : ℝ := exerciseMajorLog m
  have hNfour : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : 0 < (N : ℝ) := by linarith
  have hL : 0 ≤ L := by
    dsimp [L, exerciseMajorLog]
    exact Real.log_nonneg (by linarith)
  have hLm : 0 ≤ Lm := by
    dsimp [Lm, exerciseMajorLog]
    exact Real.log_nonneg (by
      have hmnonneg : (0 : ℝ) ≤ m := by positivity
      linarith)
  have hLmLe : Lm ≤ L := by
    dsimp [Lm, L, exerciseMajorLog]
    exact Real.log_le_log (by positivity) (by exact_mod_cast (show m + 2 ≤ N + 2 by omega))
  have hrootTwo : 2 ≤ Real.sqrt (N : ℝ) := by
    nlinarith [Real.sq_sqrt hNpos.le, Real.sqrt_nonneg (N : ℝ)]
  have hmTwo : 2 ≤ m := by exact_mod_cast hrootTwo.trans hmsqrt.le
  have hNplusSq : (N : ℝ) + 2 ≤ (N : ℝ) ^ 2 := by nlinarith
  have hLlogN : L ≤ 2 * Real.log (N : ℝ) := by
    have h := Real.log_le_log (by positivity : 0 < (N : ℝ) + 2) hNplusSq
    rw [Real.log_pow] at h
    simpa only [L, exerciseMajorLog, Nat.cast_ofNat] using h
  have hLmLower : L / 4 ≤ Lm := by
    have h := Real.log_le_log (Real.sqrt_pos.mpr hNpos)
      (show Real.sqrt (N : ℝ) ≤ (m : ℝ) + 2 by linarith)
    rw [Real.log_sqrt hNpos.le] at h
    dsimp [Lm, exerciseMajorLog]
    linarith
  have hrootLm : Real.sqrt L / 2 ≤ Real.sqrt Lm := by
    nlinarith [Real.sq_sqrt hL, Real.sq_sqrt hLm,
      Real.sqrt_nonneg L, Real.sqrt_nonneg Lm]
  have hheight : Real.exp (Real.sqrt L / 2) ≤ H :=
    (Real.exp_le_exp.mpr hrootLm).trans hH
  have hHpos : 0 < H := (Real.exp_pos _).trans_le hH
  have hrecip : H⁻¹ ≤ Real.exp (-(1 / 2 : ℝ) * Real.sqrt L) := by
    have h := one_div_le_one_div_of_le (Real.exp_pos _) hheight
    simpa only [one_div, ← Real.exp_neg,
      show -(Real.sqrt L / 2) = -(1 / 2 : ℝ) * Real.sqrt L by ring] using h
  have hbase : (m : ℝ) * Lm ^ 2 / H ≤
      (N : ℝ) * L ^ 2 * Real.exp (-(1 / 2 : ℝ) * Real.sqrt L) := by
    rw [div_eq_mul_inv]
    gcongr
  have hfactor : L ^ 2 * Real.exp (-(1 / 2 : ℝ) * Real.sqrt L) ≤
      Real.exp (-(1 / 4 : ℝ) * Real.sqrt L) := by
    rw [show -(1 / 2 : ℝ) * Real.sqrt L =
      -(1 / 4 : ℝ) * Real.sqrt L + -(1 / 4 : ℝ) * Real.sqrt L by ring,
      Real.exp_add, ← mul_assoc]
    exact (mul_le_mul_of_nonneg_right hpoly (by positivity)).trans_eq (one_mul _)
  have hbudget : (m : ℝ) * Lm ^ 2 / H ≤
      (N : ℝ) * Real.exp (-(1 / 4 : ℝ) * Real.sqrt L) := by
    calc
      _ ≤ (N : ℝ) * L ^ 2 * Real.exp (-(1 / 2 : ℝ) * Real.sqrt L) := hbase
      _ = (N : ℝ) * (L ^ 2 * Real.exp (-(1 / 2 : ℝ) * Real.sqrt L)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfactor hNpos.le
  exact (exercise_truncatedPerron_error_explicit q χ m H hmTwo hHpos).trans
    (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hbudget (by positivity : 0 ≤ 2 * (3456 + 216 * Real.exp 1)))

/-- Fixed logarithmic losses can be paid at any positive root-log error rate.
This will absorb the finite principal-character prime-power correction. -/
theorem exercise_eventually_majorLog_pow_le_rootLog_budget (K : ℕ) (c : ℝ) :
    ∀ᶠ N : ℕ in atTop, exerciseMajorLog N ^ K ≤
      (N : ℝ) * Real.exp (-c * Real.sqrt (exerciseMajorLog N)) := by
  have harg : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop := by
    convert tendsto_atTop_add_const_right _ (2 : ℝ)
      tendsto_natCast_atTop_atTop using 1
  have hlog : Tendsto exerciseMajorLog atTop atTop := Real.tendsto_log_atTop.comp harg
  have hroot : Tendsto (fun N : ℕ => Real.sqrt (exerciseMajorLog N)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hlog
  filter_upwards [exercise_eventually_majorLog_pow_exp_small K
    (d := 1) (r := 1) (by norm_num) (by norm_num),
    hroot.eventually_ge_atTop (2 * (c + 1)),
    eventually_ge_atTop (4 : ℕ)] with N hpoly hrootN hN
  let L : ℝ := exerciseMajorLog N
  have hNfour : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : 0 < (N : ℝ) := by linarith
  have hL : 0 ≤ L := by
    dsimp [L, exerciseMajorLog]
    exact Real.log_nonneg (by linarith)
  have hNsq : (N : ℝ) + 2 ≤ (N : ℝ) ^ 2 := by nlinarith
  have hLUpper : L ≤ 2 * Real.log (N : ℝ) := by
    have h := Real.log_le_log (by positivity : 0 < (N : ℝ) + 2) hNsq
    rw [Real.log_pow] at h
    simpa only [L, exerciseMajorLog, Nat.cast_ofNat] using h
  have hexponent : (c + 1) * Real.sqrt L ≤ Real.log (N : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hrootN (Real.sqrt_nonneg L)
    nlinarith [Real.sq_sqrt hL]
  have hpow : L ^ K ≤ Real.exp (Real.sqrt L) := by
    have h := mul_le_mul_of_nonneg_right hpoly (Real.exp_pos (Real.sqrt L)).le
    simpa only [L, neg_mul, one_mul, mul_assoc, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero, mul_one, one_mul] using h
  have hexp : Real.exp (Real.sqrt L) ≤
      (N : ℝ) * Real.exp (-c * Real.sqrt L) := by
    calc
      Real.exp (Real.sqrt L) =
          Real.exp ((c + 1) * Real.sqrt L) * Real.exp (-c * Real.sqrt L) := by
            rw [← Real.exp_add]
            congr 1
            ring
      _ ≤ Real.exp (Real.log (N : ℝ)) * Real.exp (-c * Real.sqrt L) := by gcongr
      _ = _ := by rw [Real.exp_log hNpos]
  exact hpow.trans hexp

/-- The finite prime-power loss for a principal character is uniformly paid
by the root-log budget, before choosing the modulus or prefix. -/
theorem exercise_eventually_principal_primePowerCorrection_absorbed (A : ℕ) (c : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, 0 < q →
      q ≤ logarithmicDenominatorCutoff A N → ∀ m : ℕ, 0 < m → m ≤ N →
        (Nat.log 2 m : ℝ) * Real.log (q : ℝ) ≤
          (Real.log 2)⁻¹ * (N : ℝ) *
            Real.exp (-c * Real.sqrt (exerciseMajorLog N)) := by
  filter_upwards [exercise_eventually_majorLog_pow_le_rootLog_budget (A + 1) c]
    with N hbudget
  intro q hq hqcut m hm hmN
  let L : ℝ := exerciseMajorLog N
  have hL : 0 ≤ L := by
    dsimp [L, exerciseMajorLog]
    exact Real.log_nonneg (by
      have hNnonneg : (0 : ℝ) ≤ N := by positivity
      linarith)
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (2 : ℝ) ^ Nat.log 2 m ≤ (m : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (Nat.ne_of_gt hm)
  have hlogPow := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ Nat.log 2 m) hpow
  rw [Real.log_pow] at hlogPow
  have hlogm : Real.log (m : ℝ) ≤ L := by
    dsimp [L, exerciseMajorLog]
    have hmNreal : (m : ℝ) ≤ N := by exact_mod_cast hmN
    exact Real.log_le_log hmpos (by linarith)
  have hnatLog : (Nat.log 2 m : ℝ) ≤ L / Real.log 2 :=
    (le_div_iff₀ hlogTwo).2 (hlogPow.trans hlogm)
  have hqL : (q : ℝ) ≤ L ^ A := by
    have hqcutReal : (q : ℝ) ≤ logarithmicDenominatorCutoff A N := by exact_mod_cast hqcut
    exact hqcutReal.trans (logarithmicDenominatorCutoff_le_log_pow A N)
  have hlogq : Real.log (q : ℝ) ≤ L ^ A := by
    have h := Real.log_le_sub_one_of_pos hqpos
    linarith
  have hlogqNonneg : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqone
  calc
    (Nat.log 2 m : ℝ) * Real.log (q : ℝ) ≤ (L / Real.log 2) * L ^ A := by gcongr
    _ = (Real.log 2)⁻¹ * L ^ (A + 1) := by rw [pow_succ]; ring
    _ ≤ (Real.log 2)⁻¹ * ((N : ℝ) * Real.exp (-c * Real.sqrt L)) :=
      mul_le_mul_of_nonneg_left hbudget (inv_nonneg.mpr hlogTwo.le)
    _ = _ := by ring

/-- Every conductor-to-modulus finite twisted-sum correction is paid by
the root-log budget, uniformly before choosing either level or character.
This transfers a primitive prefix estimate without a contour Euler-factor
loss. -/
theorem exercise_eventually_changeLevel_twistedPsi_sub_absorbed (A : ℕ) (c : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, ∀ (_hq : NeZero q),
      letI : NeZero q := _hq
      q ≤ logarithmicDenominatorCutoff A N → ∀ d : ℕ, ∀ hd : d ∣ q,
        ∀ χ : DirichletCharacter ℂ d, ∀ m : ℕ, 0 < m → m ≤ N →
          ‖exerciseTwistedPsi q (DirichletCharacter.changeLevel hd χ) m -
            exerciseTwistedPsi d χ m‖ ≤
              (Real.log 2)⁻¹ * (N : ℝ) *
                Real.exp (-c * Real.sqrt (exerciseMajorLog N)) := by
  filter_upwards [exercise_eventually_principal_primePowerCorrection_absorbed A c]
    with N hbudget
  intro q hq
  letI : NeZero q := hq
  intro hqcut d hd χ m hm hmN
  have hfinite := norm_changeLevel_twistedPsi_sub_le hd χ m
  have hfloor : ⌊Real.log (m : ℝ) / Real.log 2⌋₊ = Nat.log 2 m := by
    simpa only [Real.logb, Nat.cast_ofNat] using Real.natFloor_logb_natCast 2 m
  rw [hfloor] at hfinite
  exact hfinite.trans (hbudget q (NeZero.pos q) hqcut m hm hmN)

/-- Conductor-to-modulus transfer for the actual Perron integrals at every
allowed height. Two uniform MA01 errors and the finite twisted-sum correction
give the root-log saving; no integrated Euler-factor estimate is needed. -/
theorem exercise_eventually_changeLevel_perronIntegral_sub_absorbed (A : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, ∀ (_hq : NeZero q),
      letI : NeZero q := _hq
      q ≤ logarithmicDenominatorCutoff A N → ∀ d : ℕ, ∀ hd : d ∣ q,
        letI : NeZero d := ⟨Nat.ne_of_gt (Nat.pos_of_dvd_of_pos hd (NeZero.pos q))⟩
        ∀ χ : DirichletCharacter ℂ d, ∀ m : ℕ, m ≤ N →
          Real.sqrt (N : ℝ) < (m : ℝ) → ∀ H : ℝ,
            Real.exp (Real.sqrt (exerciseMajorLog m)) ≤ H →
              ‖exercisePerronIntegral q (DirichletCharacter.changeLevel hd χ) m H -
                exercisePerronIntegral d χ m H‖ ≤
                  (4 * (3456 + 216 * Real.exp 1) + (Real.log 2)⁻¹) * (N : ℝ) *
                    Real.exp (-(1 / 4 : ℝ) * Real.sqrt (exerciseMajorLog N)) := by
  filter_upwards [exercise_truncatedPerron_error_uniform_rootLog,
    exercise_eventually_changeLevel_twistedPsi_sub_absorbed A (1 / 4)]
    with N hperron hfinite
  intro q hq
  letI : NeZero q := hq
  intro hqcut d hd χ m hm hmroot H hH
  letI : NeZero d := ⟨Nat.ne_of_gt (Nat.pos_of_dvd_of_pos hd (NeZero.pos q))⟩
  have hmpos : 0 < m := by
    have : (0 : ℝ) < m := (Real.sqrt_nonneg (N : ℝ)).trans_lt hmroot
    exact_mod_cast this
  have hqerr := hperron q inferInstance (DirichletCharacter.changeLevel hd χ)
    m hm hmroot H hH
  have hderr := hperron d inferInstance χ m hm hmroot H hH
  have hmass := hfinite q inferInstance hqcut d hd χ m hmpos hm
  rw [norm_sub_rev] at hqerr
  calc
    _ = ‖(exercisePerronIntegral q (DirichletCharacter.changeLevel hd χ) m H -
          exerciseTwistedPsi q (DirichletCharacter.changeLevel hd χ) m) +
        (exerciseTwistedPsi q (DirichletCharacter.changeLevel hd χ) m -
          exerciseTwistedPsi d χ m) +
        (exerciseTwistedPsi d χ m - exercisePerronIntegral d χ m H)‖ := by
      congr 1
      ring
    _ ≤ ‖exercisePerronIntegral q (DirichletCharacter.changeLevel hd χ) m H -
          exerciseTwistedPsi q (DirichletCharacter.changeLevel hd χ) m‖ +
        ‖exerciseTwistedPsi q (DirichletCharacter.changeLevel hd χ) m -
          exerciseTwistedPsi d χ m‖ +
        ‖exerciseTwistedPsi d χ m - exercisePerronIntegral d χ m H‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by nlinarith [hqerr, hmass, hderr]

/-- The principal-character branch of MA03 for every modulus under the
original cutoff. Finite omitted prime powers transfer the conductor-one
strong PNT estimate without integrating a coarse Euler-factor error. -/
theorem exercise_shiftedPerron_principal (A : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, ∀ (_hq : NeZero q),
        letI : NeZero q := _hq
        q ≤ logarithmicDenominatorCutoff A N → ∀ m : ℕ, m ≤ N →
          Real.sqrt (N : ℝ) < (m : ℝ) →
            ∃ H : ℝ,
              Real.exp (Real.sqrt (exerciseMajorLog m)) ≤ H ∧
              H ≤ 2 * Real.exp (Real.sqrt (exerciseMajorLog m)) ∧
              2 ≤ H ∧ H ≤ (m : ℝ) ∧
              ‖exercisePerronIntegral q (1 : DirichletCharacter ℂ q) m H -
                exerciseCharacterPole q (1 : DirichletCharacter ℂ q) m‖ ≤
                  C * (N : ℝ) * Real.exp (-c * Real.sqrt (exerciseMajorLog N)) := by
  obtain ⟨C₁, c₁, hC₁, hc₁, hprincipal⟩ := exercise_shiftedPerron_principal_modulus_one
  let c : ℝ := min c₁ (1 / 4)
  let K : ℝ := 2 * (3456 + 216 * Real.exp 1)
  let D : ℝ := (Real.log 2)⁻¹
  let C : ℝ := C₁ + 2 * K + D
  have hc : 0 < c := lt_min hc₁ (by norm_num)
  have hD : 0 < D := inv_pos.mpr (Real.log_pos (by norm_num))
  have hC : 0 < C := by dsimp [C, K]; positivity
  refine ⟨C, c, hC, hc, ?_⟩
  filter_upwards [hprincipal, exercise_truncatedPerron_error_uniform_rootLog,
    exercise_eventually_principal_primePowerCorrection_absorbed A c]
    with N hprincipalN hPerronN hcorrectionN
  intro q hq
  letI : NeZero q := hq
  intro hqcut m hm hmsqrt
  obtain ⟨H, hHlow, hHhigh, hHTwo, hHm, hprincipalBound⟩ := hprincipalN m hm hmsqrt
  let L : ℝ := exerciseMajorLog N
  let B : ℝ := (N : ℝ) * Real.exp (-c * Real.sqrt L)
  let ψq : ℂ := exerciseTwistedPsi q (1 : DirichletCharacter ℂ q) m
  let ψ₁ : ℂ := exerciseTwistedPsi 1 (1 : DirichletCharacter ℂ 1) m
  let Iq : ℂ := exercisePerronIntegral q (1 : DirichletCharacter ℂ q) m H
  let I₁ : ℂ := exercisePerronIntegral 1 (1 : DirichletCharacter ℂ 1) m H
  let pole : ℂ := exerciseCharacterPole 1 (1 : DirichletCharacter ℂ 1) m
  have hmpos : 0 < m := by
    exact_mod_cast (Real.sqrt_nonneg (N : ℝ)).trans_lt hmsqrt
  have hrate (a : ℝ) (hca : c ≤ a) :
      Real.exp (-a * Real.sqrt L) ≤ Real.exp (-c * Real.sqrt L) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hca (Real.sqrt_nonneg L)]
  have hprincipalSmall : ‖I₁ - pole‖ ≤ C₁ * B := by
    calc
      _ ≤ C₁ * (N : ℝ) * Real.exp (-c₁ * Real.sqrt L) := hprincipalBound
      _ ≤ C₁ * (N : ℝ) * Real.exp (-c * Real.sqrt L) :=
        mul_le_mul_of_nonneg_left (hrate c₁ (min_le_left _ _)) (by positivity)
      _ = _ := by dsimp [B]; ring
  have htruncOne : ‖ψ₁ - I₁‖ ≤ K * B := by
    calc
      _ ≤ K * (N : ℝ) * Real.exp (-(1 / 4 : ℝ) * Real.sqrt L) :=
        hPerronN 1 inferInstance (1 : DirichletCharacter ℂ 1) m hm hmsqrt H hHlow
      _ ≤ K * (N : ℝ) * Real.exp (-c * Real.sqrt L) :=
        mul_le_mul_of_nonneg_left (hrate (1 / 4) (min_le_right _ _)) (by positivity)
      _ = _ := by dsimp [B]; ring
  have htruncQ : ‖Iq - ψq‖ ≤ K * B := by
    calc
      _ = ‖ψq - Iq‖ := norm_sub_rev _ _
      _ ≤ K * (N : ℝ) * Real.exp (-(1 / 4 : ℝ) * Real.sqrt L) :=
        hPerronN q hq (1 : DirichletCharacter ℂ q) m hm hmsqrt H hHlow
      _ ≤ K * (N : ℝ) * Real.exp (-c * Real.sqrt L) :=
        mul_le_mul_of_nonneg_left (hrate (1 / 4) (min_le_right _ _)) (by positivity)
      _ = _ := by dsimp [B]; ring
  have hfloor : Nat.floor (Real.log (m : ℝ) / Real.log 2) = Nat.log 2 m := by
    simpa only [Real.logb, Nat.cast_ofNat] using Real.natFloor_logb_natCast 2 m
  have hfinite : ‖ψq - ψ₁‖ ≤ (Nat.log 2 m : ℝ) * Real.log (q : ℝ) := by
    dsimp only [ψq, ψ₁]
    rw [exercisePrincipalTwistedPsi_eq_chebyshevPsi]
    simpa only [exerciseTwistedPsi, hfloor] using
      norm_principal_twistedPsi_sub_chebyshevPsi_le q m
  have hcorrection : ‖ψq - ψ₁‖ ≤ D * B := by
    calc
      _ ≤ (Nat.log 2 m : ℝ) * Real.log (q : ℝ) := hfinite
      _ ≤ (Real.log 2)⁻¹ * (N : ℝ) * Real.exp (-c * Real.sqrt L) :=
        hcorrectionN q (Nat.pos_of_ne_zero hq.out) hqcut m hmpos hm
      _ = _ := by dsimp [D, B]; ring
  have hpole : exerciseCharacterPole q (1 : DirichletCharacter ℂ q) m = pole := by
    simp [exerciseCharacterPole, pole]
  refine ⟨H, hHlow, hHhigh, hHTwo, hHm, ?_⟩
  rw [hpole]
  calc
    ‖Iq - pole‖ = ‖(Iq - ψq) + (ψq - ψ₁) + (ψ₁ - I₁) + (I₁ - pole)‖ := by
      congr 1
      ring
    _ ≤ ‖(Iq - ψq) + (ψq - ψ₁) + (ψ₁ - I₁)‖ + ‖I₁ - pole‖ := norm_add_le _ _
    _ ≤ (‖(Iq - ψq) + (ψq - ψ₁)‖ + ‖ψ₁ - I₁‖) + ‖I₁ - pole‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (‖Iq - ψq‖ + ‖ψq - ψ₁‖ + ‖ψ₁ - I₁‖) + ‖I₁ - pole‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (K * B + D * B + K * B) + C₁ * B := by gcongr
    _ = C * (N : ℝ) * Real.exp (-c * Real.sqrt L) := by dsimp [C, B]; ring

set_option maxHeartbeats 0 in
/-- The full shifted-Perron source estimate, assembled from the actual
primitive contour, uniform scalar payment, and conductor transfer. -/
theorem exercise_shiftedPerron_with_exception (A : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, ∀ (_hq : NeZero q),
        letI : NeZero q := _hq
        q ≤ logarithmicDenominatorCutoff A N →
        ∀ χ : DirichletCharacter ℂ q, ∀ m : ℕ, m ≤ N →
          Real.sqrt (N : ℝ) < (m : ℝ) →
          ∃ H : ℝ,
            Real.exp (Real.sqrt (exerciseMajorLog m)) ≤ H ∧
            H ≤ 2 * Real.exp (Real.sqrt (exerciseMajorLog m)) ∧
            2 ≤ H ∧ H ≤ (m : ℝ) ∧
            ∃ E : ℝ, 0 ≤ E ∧
              (E = 0 ∨ ∃ β : ℝ,
                1 / 2 < β ∧ β < 1 ∧
                χ.primitiveCharacter ≠ 1 ∧
                exerciseRealCharacter χ.conductor χ.primitiveCharacter ∧
                exercisePrimitiveLValue q χ β = 0 ∧
                E = exercisePerronEndpoint m ^ β) ∧
              ‖exercisePerronIntegral q χ m H -
                exerciseCharacterPole q χ m‖ ≤
                  C * (N : ℝ) *
                    Real.exp (-c * Real.sqrt (exerciseMajorLog N)) + E := by
  obtain ⟨c₀, K, hc₀, _hc₀small, hK, hpointwise⟩ :=
    exists_nonprincipal_pointwise_shiftedPerron_error
  obtain ⟨Cedge, dedge, hCedge, hdedge, hscalar⟩ :=
    perron_scalar_edge_payment A c₀ K hc₀ hK
  obtain ⟨cE, hcE, hresidue⟩ :=
    exercise_exceptionalResidue_le_term_add_absorbed A
  obtain ⟨CP, cP, hCP, hcP, hprincipal⟩ :=
    exercise_shiftedPerron_principal A
  let T : ℝ := 4 * (3456 + 216 * Real.exp 1) + (Real.log 2)⁻¹
  let c : ℝ := min dedge (min cE (min (1 / 4) cP))
  let C : ℝ := Cedge + T + 1 + CP
  have hT : 0 < T := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [T]
    positivity
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min hdedge (lt_min hcE (lt_min (by norm_num) hcP))
  have hC : 0 < C := by dsimp [C]; positivity
  have hcdedge : c ≤ dedge := min_le_left _ _
  have hccE : c ≤ cE := (min_le_right _ _).trans (min_le_left _ _)
  have hcquarter : c ≤ (1 / 4 : ℝ) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hccP : c ≤ cP :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hCPle : CP ≤ C := by dsimp [C]; linarith
  have hCedgeTle : Cedge + T + 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C, c, hC, hc, ?_⟩
  filter_upwards [hscalar, hresidue, hprincipal,
    exercise_eventually_changeLevel_perronIntegral_sub_absorbed A,
    exercise_eventually_perron_prefix_room] with
    N hscalarN hresidueN hprincipalN htransferN hroomN
  intro q hq
  letI : NeZero q := hq
  intro hqcut χ m hm hmsqrt
  let L : ℝ := exerciseMajorLog N
  let B : ℝ := (N : ℝ) * Real.exp (-c * Real.sqrt L)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hrate (a : ℝ) (hca : c ≤ a) :
      Real.exp (-a * Real.sqrt L) ≤ Real.exp (-c * Real.sqrt L) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hca (Real.sqrt_nonneg L)]
  by_cases hχ : χ = 1
  · subst χ
    obtain ⟨H, hHlow, hHhigh, hHtwo, hHm, hnorm⟩ :=
      hprincipalN q hq hqcut m hm hmsqrt
    refine ⟨H, hHlow, hHhigh, hHtwo, hHm, 0, le_rfl, Or.inl rfl, ?_⟩
    calc
      _ ≤ CP * (N : ℝ) * Real.exp (-cP * Real.sqrt L) := hnorm
      _ ≤ CP * (N : ℝ) * Real.exp (-c * Real.sqrt L) :=
        mul_le_mul_of_nonneg_left (hrate cP hccP) (by positivity)
      _ = CP * B := by dsimp [B]; ring
      _ ≤ C * B := mul_le_mul_of_nonneg_right hCPle hB
      _ = _ := by dsimp [B, L]; ring
  · letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hprim : χ.primitiveCharacter ≠ 1 := by
      intro h
      have heq := χ.changeLevel_primitiveCharacter
      rw [h, DirichletCharacter.changeLevel_one] at heq
      exact hχ heq.symm
    have hconductorCut : χ.conductor ≤ logarithmicDenominatorCutoff A N :=
      (Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level).trans hqcut
    obtain ⟨hmTwo, hLm, hτTwo, hτroom⟩ := hroomN m hmsqrt
    obtain ⟨H, hHlow, hHquarter, σ, hσI, R, hR, hpointwiseBound⟩ :=
      hpointwise χ.primitiveCharacter hprim m hmTwo hLm hτTwo hτroom
    have hHhigh : H ≤ 2 * Real.exp (Real.sqrt (exerciseMajorLog m)) := by
      linarith
    have hHtwo : 2 ≤ H := hτTwo.trans hHlow
    have hHm : H ≤ (m : ℝ) := hHquarter.trans hτroom
    have hscalarBound := hscalarN χ.conductor inferInstance hconductorCut m hm
      hmsqrt H σ hHlow hHhigh hHtwo hσI.2
    have hprimitiveSmall : ‖exercisePerronIntegral χ.conductor
        χ.primitiveCharacter m H - R‖ ≤ Cedge * B := by
      calc
        _ ≤ Cedge * (N : ℝ) * Real.exp (-dedge * Real.sqrt L) :=
          hpointwiseBound.trans hscalarBound
        _ ≤ Cedge * (N : ℝ) * Real.exp (-c * Real.sqrt L) :=
          mul_le_mul_of_nonneg_left (hrate dedge hcdedge) (by positivity)
        _ = _ := by dsimp [B]; ring
    have htransferBound := htransferN q hq hqcut χ.conductor
      χ.conductor_dvd_level χ.primitiveCharacter m hm hmsqrt H hHlow
    have htransferSmall : ‖exercisePerronIntegral q χ m H -
        exercisePerronIntegral χ.conductor χ.primitiveCharacter m H‖ ≤ T * B := by
      calc
        _ ≤ T * (N : ℝ) * Real.exp (-(1 / 4 : ℝ) * Real.sqrt L) := by
          simpa only [DirichletCharacter.changeLevel_primitiveCharacter] using htransferBound
        _ ≤ T * (N : ℝ) * Real.exp (-c * Real.sqrt L) :=
          mul_le_mul_of_nonneg_left (hrate (1 / 4) hcquarter) (by positivity)
        _ = _ := by dsimp [B]; ring
    obtain ⟨E, hE, hErecord, hRsmall⟩ : ∃ E : ℝ, 0 ≤ E ∧
        (E = 0 ∨ ∃ β : ℝ,
          1 / 2 < β ∧ β < 1 ∧ χ.primitiveCharacter ≠ 1 ∧
          exerciseRealCharacter χ.conductor χ.primitiveCharacter ∧
          exercisePrimitiveLValue q χ β = 0 ∧
          E = exercisePerronEndpoint m ^ β) ∧ ‖R‖ ≤ E + B := by
      rcases hR with hRzero | ⟨β, hβhalf, hβone, _hσβ, hreal, hzero, _hsimple, hRvalue⟩
      · refine ⟨0, le_rfl, Or.inl rfl, ?_⟩
        simpa only [hRzero, norm_zero, zero_add] using hB
      · have hreal' : exerciseRealCharacter χ.conductor χ.primitiveCharacter := hreal
        have hzero' : exercisePrimitiveLValue q χ β = 0 := by
          change DirichletCharacter.LFunction χ.primitiveCharacter (β : ℂ) = 0
          exact hzero
        have hresidueBound := hresidueN q hq hqcut χ m hm hmsqrt β
          hβhalf hβone hprim hreal' hzero'
        refine ⟨exercisePerronEndpoint m ^ β, Real.rpow_nonneg (by
          dsimp [exercisePerronEndpoint]; positivity) _,
          Or.inr ⟨β, hβhalf, hβone, hprim, hreal', hzero', rfl⟩, ?_⟩
        calc
          ‖R‖ = ‖-(exercisePerronEndpoint m : ℂ) ^ (β : ℂ) / (β : ℂ)‖ := by
            rw [hRvalue]
          _ ≤ exercisePerronEndpoint m ^ β +
              (N : ℝ) * Real.exp (-cE * Real.sqrt L) := hresidueBound
          _ ≤ exercisePerronEndpoint m ^ β + B := by
            apply add_le_add_right
            exact mul_le_mul_of_nonneg_left (hrate cE hccE) (by positivity)
    refine ⟨H, hHlow, hHhigh, hHtwo, hHm, E, hE, hErecord, ?_⟩
    have hpole : exerciseCharacterPole q χ m = 0 := by
      simp only [exerciseCharacterPole, if_neg hχ]
    rw [hpole, sub_zero]
    calc
      ‖exercisePerronIntegral q χ m H‖ =
          ‖(exercisePerronIntegral q χ m H -
              exercisePerronIntegral χ.conductor χ.primitiveCharacter m H) +
            (exercisePerronIntegral χ.conductor χ.primitiveCharacter m H - R) + R‖ := by
        congr 1
        ring
      _ ≤ ‖exercisePerronIntegral q χ m H -
              exercisePerronIntegral χ.conductor χ.primitiveCharacter m H‖ +
          ‖exercisePerronIntegral χ.conductor χ.primitiveCharacter m H - R‖ + ‖R‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ T * B + Cedge * B + (E + B) :=
        add_le_add (add_le_add htransferSmall hprimitiveSmall) hRsmall
      _ = (Cedge + T + 1) * B + E := by ring
      _ ≤ C * B + E := add_le_add_left
        (mul_le_mul_of_nonneg_right hCedgeTle hB) E
      _ = _ := by dsimp [B, L]; ring

#print axioms exercise_shiftedPerron_with_exception

/-- Every fixed logarithmic power is eventually at most the ambient
integer scale; this absorbs Perron's additive `log²` term. -/
theorem exercise_eventually_majorLog_pow_le_nat (K : ℕ) :
    ∀ᶠ N : ℕ in atTop, exerciseMajorLog N ^ K ≤ (N : ℝ) := by
  have harg : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop := by
    convert tendsto_atTop_add_const_right _ (2 : ℝ)
      tendsto_natCast_atTop_atTop using 1
  have hlo : (fun N : ℕ => exerciseMajorLog N ^ K) =o[atTop]
      (fun N : ℕ => (N : ℝ) + 2) := by
    simpa only [exerciseMajorLog, Function.comp_def, Real.rpow_natCast,
      Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ)) (K : ℝ)
        (by norm_num)).comp_tendsto harg
  filter_upwards [hlo.bound (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop (2 : ℕ)] with N hbound hN
  have hlognonneg : 0 ≤ exerciseMajorLog N := by
    dsimp [exerciseMajorLog]
    exact Real.log_nonneg (by
      have hNnonneg : (0 : ℝ) ≤ N := by positivity
      linarith)
  have hpow : 0 ≤ exerciseMajorLog N ^ K := by positivity
  have hargnonneg : 0 ≤ (N : ℝ) + 2 := by positivity
  have hbound' : exerciseMajorLog N ^ K ≤
      (1 / 2 : ℝ) * ((N : ℝ) + 2) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hpow,
      abs_of_nonneg hargnonneg] using hbound
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

/-- MA05 (PROVED, using MA01--MA04): combine the Perron, contour,
and exceptional estimates and convert their errors into an arbitrary
logarithmic saving.

The eventual threshold stays outside every character and endpoint
quantifier, using the scalar lemmas above for the three exponential terms
and the additive Perron term.

Take the height supplied by MA03; invoke the uniform MA01 root-log estimate.
Use `norm_sub_le` to add the two errors. For the principal character, change
`m+1/2` to `m`; its cost is `1/2`. For a nonprincipal character both pole
terms are zero. Finally prove for each fixed `B` and positive `c` that
`log(N+2)^B * exp(-c*sqrt(log(N+2))) → 0`; substitute `y=sqrt(log(N+2))`
and use that exponential dominates the polynomial `y^(2*B)`.
The constant `C` is chosen before `N,q,χ,m` and can depend on `A,B` only.
Do not use a fixed-character asymptotic whose threshold depends on `χ`. -/
theorem exercise_characterPsi_logSaving (A B : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, ∀ (_hq : NeZero q),
        letI : NeZero q := _hq
        q ≤ logarithmicDenominatorCutoff A N →
        ∀ χ : DirichletCharacter ℂ q, ∀ m : ℕ, m ≤ N →
          Real.sqrt (N : ℝ) < (m : ℝ) →
            ‖exerciseTwistedPsi q χ m -
              (if χ = 1 then (m : ℂ) else 0)‖ ≤
                C * (N : ℝ) / exerciseMajorLog N ^ B := by
  let CP : ℝ := 2 * (3456 + 216 * Real.exp 1)
  have hCP : 0 < CP := by dsimp [CP]; positivity
  obtain ⟨CS, cS, hCS, hcS, hShift⟩ :=
    exercise_shiftedPerron_with_exception A
  obtain ⟨cE, hcE, hExceptional⟩ := exercise_exceptionalTerm_absorbed A
  let C : ℝ := 2 * CP + CS + 2
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hShift, hExceptional,
    exercise_truncatedPerron_error_uniform_rootLog,
    exercise_eventually_majorLog_pow_exp_small B
      (d := 1 / 4) (r := 1) (by norm_num) (by norm_num),
    exercise_eventually_majorLog_pow_exp_small B hcS
      (by norm_num : (0 : ℝ) < 1),
    exercise_eventually_majorLog_pow_exp_small B hcE
      (by norm_num : (0 : ℝ) < 1),
    exercise_eventually_majorLog_pow_le_nat (B + 2),
    eventually_ge_atTop (4 : ℕ)] with
    N hShiftN hExceptionalN hPerronN hPexp hSexp hEexp hPoly hN4
  intro q hq hqcut χ m hm hmsqrt
  letI : NeZero q := hq
  let L : ℝ := exerciseMajorLog N
  let D : ℝ := (N : ℝ) / L ^ B
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNrFour : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hL : 0 < L := by
    dsimp [L, exerciseMajorLog]
    apply Real.log_pos
    have hNnonneg : (0 : ℝ) ≤ N := by positivity
    linarith
  have hLone : 1 ≤ L := by
    dsimp [L, exerciseMajorLog]
    have harg : Real.exp 1 ≤ (N : ℝ) + 2 := by
      linarith [Real.exp_one_lt_three]
    exact (Real.le_log_iff_exp_le (by positivity)).2 harg
  obtain ⟨H, hHlow, _hHhigh, _hHTwo, _hHm,
    E, hEnonneg, hEform, hContour⟩ :=
    hShiftN q hq hqcut χ m hm hmsqrt
  have hPerronBound := hPerronN q hq χ m hm hmsqrt H hHlow
  have hEbound : E ≤
      (N : ℝ) * Real.exp (-cE * Real.sqrt L) := by
    rcases hEform with hzero | ⟨β, hβhalf, hβone, hχprim, hχreal, hzero, hEq⟩
    · rw [hzero]
      positivity
    · rw [hEq]
      exact hExceptionalN q hq hqcut χ m hm hmsqrt β
        hβhalf hβone hχprim hχreal hzero
  have hD : 0 < D := by dsimp [D]; positivity
  have hPerronMain : (N : ℝ) * Real.exp (-(1 / 4 : ℝ) * Real.sqrt L) ≤ D := by
    apply (le_div_iff₀ (pow_pos hL B)).2
    calc
      (N : ℝ) * Real.exp (-(1 / 4 : ℝ) * Real.sqrt L) * L ^ B =
          (N : ℝ) * (L ^ B * Real.exp (-(1 / 4 : ℝ) * Real.sqrt L)) := by ring
      _ ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left hPexp hNr.le
      _ = (N : ℝ) := by ring
  have hShiftSmall : (N : ℝ) * Real.exp (-cS * Real.sqrt L) ≤ D := by
    apply (le_div_iff₀ (pow_pos hL B)).2
    calc
      (N : ℝ) * Real.exp (-cS * Real.sqrt L) * L ^ B =
          (N : ℝ) * (L ^ B * Real.exp (-cS * Real.sqrt L)) := by ring
      _ ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left hSexp hNr.le
      _ = (N : ℝ) := by ring
  have hExceptionalSmall : (N : ℝ) * Real.exp (-cE * Real.sqrt L) ≤ D := by
    apply (le_div_iff₀ (pow_pos hL B)).2
    calc
      (N : ℝ) * Real.exp (-cE * Real.sqrt L) * L ^ B =
          (N : ℝ) * (L ^ B * Real.exp (-cE * Real.sqrt L)) := by ring
      _ ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left hEexp hNr.le
      _ = (N : ℝ) := by ring
  have hOne : 1 ≤ D := by
    apply (le_div_iff₀ (pow_pos hL B)).2
    have hpowB : L ^ B ≤ L ^ (B + 2) :=
      pow_le_pow_right₀ hLone (by omega)
    simpa only [one_mul] using hpowB.trans hPoly
  have hPole :
      ‖exerciseCharacterPole q χ m -
        (if χ = 1 then (m : ℂ) else 0)‖ ≤ 1 / 2 := by
    by_cases hχ : χ = 1
    · simp [exerciseCharacterPole, exercisePerronEndpoint, hχ]
    · simp [exerciseCharacterPole, hχ]
  let ψ : ℂ := exerciseTwistedPsi q χ m
  let P : ℂ := exercisePerronIntegral q χ m H
  let pole : ℂ := exerciseCharacterPole q χ m
  let main : ℂ := if χ = 1 then (m : ℂ) else 0
  have htriangle : ‖ψ - main‖ ≤
      ‖ψ - P‖ + ‖P - pole‖ + ‖pole - main‖ := by
    calc
      ‖ψ - main‖ = ‖(ψ - P) + (P - pole) + (pole - main)‖ := by
        congr 1
        ring
      _ ≤ ‖(ψ - P) + (P - pole)‖ + ‖pole - main‖ := norm_add_le _ _
      _ ≤ ‖ψ - P‖ + ‖P - pole‖ + ‖pole - main‖ := by
        have h := norm_add_le (ψ - P) (P - pole)
        linarith
  have hPerronSmall : ‖ψ - P‖ ≤ CP * (D + D) := by
    calc
      ‖ψ - P‖ ≤ CP * (N : ℝ) *
          Real.exp (-(1 / 4 : ℝ) * Real.sqrt L) := hPerronBound
      _ = CP * ((N : ℝ) * Real.exp (-(1 / 4 : ℝ) * Real.sqrt L)) := by ring
      _ ≤ CP * D := mul_le_mul_of_nonneg_left hPerronMain hCP.le
      _ ≤ CP * (D + D) := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right hD.le) hCP.le
  have hContourSmall : ‖P - pole‖ ≤ CS * D + D := by
    calc
      ‖P - pole‖ ≤ CS * (N : ℝ) *
          Real.exp (-cS * Real.sqrt L) + E := hContour
      _ ≤ CS * D + (N : ℝ) * Real.exp (-cE * Real.sqrt L) := by
        have hterm : CS * (N : ℝ) * Real.exp (-cS * Real.sqrt L) ≤
            CS * D := by
          calc
            CS * (N : ℝ) * Real.exp (-cS * Real.sqrt L) =
                CS * ((N : ℝ) * Real.exp (-cS * Real.sqrt L)) := by ring
            _ ≤ CS * D := mul_le_mul_of_nonneg_left hShiftSmall hCS.le
        linarith [hEbound]
      _ ≤ CS * D + D := by linarith [hExceptionalSmall]
  calc
    ‖ψ - main‖ ≤ ‖ψ - P‖ + ‖P - pole‖ + ‖pole - main‖ := htriangle
    _ ≤ CP * (D + D) + (CS * D + D) + 1 / 2 := by
      dsimp [ψ, P, pole, main] at hPerronSmall hContourSmall hPole
      linarith
    _ ≤ C * D := by
      dsimp [C]
      linarith [hOne]
    _ = C * (N : ℝ) / L ^ B := by dsimp [D]; ring

/-- MA06 (FILLED, finite algebra): uniform individual character errors
survive the orthogonality average with no loss of a factor `φ(q)`.

Rewrite with `cubicResiduePartialSum_eq_character_average`; put the `m`
main term inside the sum (only `χ=1` survives). Use `χ(r⁻¹)` of norm one
for a unit `r`, `norm_sum_le`, then `sum_le_sum`. The resulting cardinal is
`φ(q)` by `DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity` and
`Nat.card_eq_fintype_card`. Finally cancel against `‖φ(q)⁻¹‖`; use
`Nat.totient_pos.mpr (NeZero.pos q)` before field simplification.
This is finite-dimensional algebra, not a further analytic assumption. -/
theorem exercise_unitAP_of_characterBound (q m : ℕ) [NeZero q]
    (r : ZMod q) (hr : IsUnit r) (E : ℝ)
    (hχ : ∀ χ : DirichletCharacter ℂ q,
      ‖exerciseTwistedPsi q χ m -
        (if χ = 1 then (m : ℂ) else 0)‖ ≤ E) :
    ‖cubicResiduePartialSum q r m -
      (m : ℕ) * (Nat.totient q : ℂ)⁻¹‖ ≤ E := by
  classical
  let c : ℂ := (Nat.totient q : ℂ)⁻¹
  have hrInv : IsUnit r⁻¹ := isUnit_of_dvd_one
    ⟨r, (ZMod.inv_mul_of_unit r hr).symm⟩
  have hmain : (∑ χ : DirichletCharacter ℂ q,
      χ r⁻¹ * (if χ = 1 then (m : ℂ) else 0)) = (m : ℂ) := by
    simp [MulChar.one_apply hrInv]
  have heq : cubicResiduePartialSum q r m - (m : ℕ) * c =
      c * ∑ χ : DirichletCharacter ℂ q,
        χ r⁻¹ * (exerciseTwistedPsi q χ m -
          (if χ = 1 then (m : ℂ) else 0)) := by
    rw [cubicResiduePartialSum_eq_character_average q m r hr]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hmain]
    dsimp [c, exerciseTwistedPsi]
    ring
  have hcard : Fintype.card (DirichletCharacter ℂ q) = Nat.totient q := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hsum :
      ‖∑ χ : DirichletCharacter ℂ q,
        χ r⁻¹ * (exerciseTwistedPsi q χ m -
          (if χ = 1 then (m : ℂ) else 0))‖ ≤
        (Nat.totient q : ℝ) * E := by
    calc
      _ ≤ ∑ χ : DirichletCharacter ℂ q,
          ‖χ r⁻¹ * (exerciseTwistedPsi q χ m -
            (if χ = 1 then (m : ℂ) else 0))‖ := norm_sum_le _ _
      _ ≤ ∑ _χ : DirichletCharacter ℂ q, E := by
        apply Finset.sum_le_sum
        intro χ _hχ
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right (χ.norm_le_one r⁻¹)
          (norm_nonneg _)).trans (by simpa using hχ χ)
      _ = (Nat.totient q : ℝ) * E := by simp [hcard]
  have ht : (Nat.totient q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  change ‖cubicResiduePartialSum q r m - (m : ℕ) * c‖ ≤ E
  rw [heq, norm_mul]
  calc
    _ ≤ ‖c‖ * ((Nat.totient q : ℝ) * E) :=
      mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = E := by
      simp only [c, norm_inv, Complex.norm_natCast]
      field_simp

/-- The all-residue discrepancy charged to each center. The last terms are
already proved small-endpoint and nonunit bounds, not analytic placeholders. -/
noncomputable def exerciseMajorAPEnvelope (A B N : ℕ) (C : ℝ) : ℝ :=
  C * (N : ℝ) / exerciseMajorLog N ^ B + 1 +
    (nonunitResidueAPConstant + (Real.log 4 + 6)) *
      (Real.sqrt (N : ℝ) + 1) +
    (Real.log 4 + 4) * logarithmicDenominatorCutoff A N

/-- Endpoint normalization and all nonunit/small-endpoint cases, using the
proved uniform character source theorem. -/
theorem exercise_eventually_allResidueAP (A B : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, ∀ (_hq0 : NeZero q),
        q ≤ logarithmicDenominatorCutoff A N →
        ∀ r : ZMod q, ∀ m ≤ N,
          ‖cubicResiduePartialSum q r m -
            (m + 1 : ℕ) *
              (if IsUnit r then (Nat.totient q : ℂ)⁻¹ else 0)‖ ≤
                exerciseMajorAPEnvelope A B N C := by
  obtain ⟨C, hC, hsource⟩ := exercise_characterPsi_logSaving A B
  refine ⟨C, hC, ?_⟩
  filter_upwards [hsource] with N hN q hq0 hq r m hm
  letI : NeZero q := hq0
  have hU : 0 ≤ C * (N : ℝ) / exerciseMajorLog N ^ B := by
    have hlog : 0 ≤ exerciseMajorLog N := by
      dsimp [exerciseMajorLog]
      exact Real.log_nonneg (by
        have hNnonneg : 0 ≤ (N : ℝ) := by positivity
        linarith)
    positivity
  apply norm_cubicResiduePartialSum_sub_density_le_of_unit_large
    q (logarithmicDenominatorCutoff A N) N m r
    (C * (N : ℝ) / exerciseMajorLog N ^ B + 1) hq hm (by linarith)
  intro hr hlarge
  exact norm_cubicResiduePartialSum_sub_endpointDensity_le q m r
    (C * (N : ℝ) / exerciseMajorLog N ^ B)
    (exercise_unitAP_of_characterBound q m r hr _
      (fun χ => hN q hq0 hq χ m hm hlarge))

/-- Exact complex-valued truncated main term in the existing model identity. -/
noncomputable def exerciseTruncatedMainTerm (n N T Q : ℕ) : ℂ :=
  (((N : ℝ) ^ n : ℂ) *
    (((N : ℝ) ^ 3)⁻¹ •
      truncatedSingularIntegral n ((T : ℝ) / (N : ℝ) ^ 3) Q)) *
    truncatedSingularSeries n T Q

/-- Exact coarse global error already proved in `MajorArcConcreteError`.
Keeping it named avoids asking a later model to rediscover its powers. -/
noncomputable def exerciseMajorModelError (n N Q : ℕ) (D : ℝ) : ℝ :=
  ((Q + 1 : ℕ) ^ 2 : ℝ) *
    ((n : ℝ) * ((Real.log 4 + 4) * (N : ℝ)) ^ (n - 1) *
      (((Q : ℝ) * D + 1) * (1 + 8 * Real.pi * (Q : ℝ)) +
        2 * Real.pi * Q / (N : ℝ)) *
      (2 * (Q : ℝ) / (N : ℝ) ^ 3))

/-- The coefficient of the AP discrepancy in the global model error. It is
independent of the discrepancy itself, which permits four separate limits. -/
noncomputable def exerciseMajorModelSlope (n N Q : ℕ) : ℝ :=
  ((Q + 1 : ℕ) ^ 2 : ℝ) *
    ((n : ℝ) * ((Real.log 4 + 4) * (N : ℝ)) ^ (n - 1) *
      ((Q : ℝ) * (1 + 8 * Real.pi * (Q : ℝ))) *
      (2 * (Q : ℝ) / (N : ℝ) ^ 3))

/-- MA07-0 (FILLED, algebra): decompose the exact AP envelope into four
summands. The identity also holds at `N=0`; no division cancellation is used. -/
theorem exerciseMajorModelError_split (A n N : ℕ) (C : ℝ) :
    exerciseMajorModelError n N (logarithmicDenominatorCutoff A N)
      (exerciseMajorAPEnvelope A (5 * A + 2) N C) =
    exerciseMajorModelSlope n N (logarithmicDenominatorCutoff A N) *
      (C * (N : ℝ) / exerciseMajorLog N ^ (5 * A + 2)) +
    exerciseMajorModelSlope n N (logarithmicDenominatorCutoff A N) *
      (1 + (nonunitResidueAPConstant + (Real.log 4 + 6)) *
        (Real.sqrt (N : ℝ) + 1)) +
    exerciseMajorModelSlope n N (logarithmicDenominatorCutoff A N) *
      ((Real.log 4 + 4) * logarithmicDenominatorCutoff A N) +
    exerciseMajorModelError n N (logarithmicDenominatorCutoff A N) 0 := by
  unfold exerciseMajorModelError exerciseMajorModelSlope exerciseMajorAPEnvelope
  ring

/-! MA07-1--MA07-3 use the common slope bound
`S(n,N,Q) ≤ H_n * Q^5 * N^(n-3) / N` for `N>0`, `Q≥1`, where
`H_n = 8*n*(log 4+4)^(n-1)*(1+8*pi)`. Use `(Q+1)^2≤4Q²`,
`1+8*pi*Q≤(1+8*pi)*Q`, and `n-1=(n-3)+2`. The named helper below
is proved separately so that each leaf has only one scalar limit. -/

/-- A positive constant for the common slope estimate in MA07-1--MA07-3. -/
noncomputable def exerciseMajorSlopeConstant (n : ℕ) : ℝ :=
  8 * (n : ℝ) * (Real.log 4 + 4) ^ (n - 1) * (1 + 8 * Real.pi)

/-- The model-error slope costs five powers of the denominator cutoff and
one inverse power of `N` relative to the main scale. -/
theorem exerciseMajorModelSlope_le (n N Q : ℕ) (hn : 3 ≤ n)
    (hN : 0 < N) (hQ : 1 ≤ Q) :
    exerciseMajorModelSlope n N Q ≤
      exerciseMajorSlopeConstant n * (Q : ℝ) ^ 5 * cubicMainScale n N / (N : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hL : 0 ≤ Real.log 4 + 4 := by
    have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hQsq : ((Q + 1 : ℕ) : ℝ) ^ 2 ≤ 4 * (Q : ℝ) ^ 2 := by
    push_cast
    nlinarith [sq_nonneg ((Q : ℝ) - 1)]
  have hQlin : 1 + 8 * Real.pi * (Q : ℝ) ≤
      (1 + 8 * Real.pi) * (Q : ℝ) := by
    nlinarith [Real.pi_pos]
  have hpre : exerciseMajorModelSlope n N Q ≤
      (4 * (Q : ℝ) ^ 2) *
        ((n : ℝ) * ((Real.log 4 + 4) * (N : ℝ)) ^ (n - 1) *
          ((Q : ℝ) * ((1 + 8 * Real.pi) * (Q : ℝ))) *
          (2 * (Q : ℝ) / (N : ℝ) ^ 3)) := by
    unfold exerciseMajorModelSlope
    gcongr
  calc
    exerciseMajorModelSlope n N Q ≤
        (4 * (Q : ℝ) ^ 2) *
          ((n : ℝ) * ((Real.log 4 + 4) * (N : ℝ)) ^ (n - 1) *
            ((Q : ℝ) * ((1 + 8 * Real.pi) * (Q : ℝ))) *
            (2 * (Q : ℝ) / (N : ℝ) ^ 3)) := hpre
    _ = exerciseMajorSlopeConstant n * (Q : ℝ) ^ 5 *
          cubicMainScale n N / (N : ℝ) := by
      unfold exerciseMajorSlopeConstant cubicMainScale
      rw [mul_pow, show n - 1 = (n - 3) + 2 by omega, pow_add]
      field_simp
      ring

/-- The logarithmic cutoff is eventually positive, including at exponent
zero, where it is identically one. -/
theorem exercise_eventually_logarithmicCutoff_pos (A : ℕ) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ logarithmicDenominatorCutoff A N := by
  by_cases hA : A = 0
  · filter_upwards [] with N
    simp [hA, logarithmicDenominatorCutoff]
  · exact (tendsto_logarithmicDenominatorCutoff A (by omega)).eventually_ge_atTop 1

/-- MA07-1 (FILLED, numeric): AP saving beats the five cutoff powers.
Use `Q≤log(N+2)^A` and `B=5*A+2`; the common slope bound reduces the
ratio to at most a fixed multiple of `1/log(N+2)^2`. Obtain its eventual
smallness from `Real.tendsto_log_atTop`. `C` is fixed before `N`. -/
theorem exercise_eventually_majorAPTerm_small (A n : ℕ) (hn : 33 ≤ n)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      exerciseMajorModelSlope n N (logarithmicDenominatorCutoff A N) *
        (C * (N : ℝ) / exerciseMajorLog N ^ (5 * A + 2)) ≤
          c * cubicMainScale n N := by
  have hlog : Tendsto exerciseMajorLog atTop atTop := by
    have harg : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop := by
      convert tendsto_atTop_add_const_right _ (2 : ℝ)
        tendsto_natCast_atTop_atTop using 1
    exact Real.tendsto_log_atTop.comp harg
  have hH : 0 ≤ exerciseMajorSlopeConstant n := by
    unfold exerciseMajorSlopeConstant
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  filter_upwards [hlog.eventually_ge_atTop
      (max 1 (exerciseMajorSlopeConstant n * C / c)),
    exercise_eventually_logarithmicCutoff_pos A,
    eventually_gt_atTop (0 : ℕ)] with N hlogN hQ hN
  let L := exerciseMajorLog N
  let Q := logarithmicDenominatorCutoff A N
  let H := exerciseMajorSlopeConstant n
  have hLone : 1 ≤ L := (le_max_left _ _).trans hlogN
  have hL : 0 < L := by linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hcut : (Q : ℝ) ≤ L ^ A := by
    simpa only [Q, L, exerciseMajorLog] using
      logarithmicDenominatorCutoff_le_log_pow A N
  have hQpow : (Q : ℝ) ^ 5 ≤ L ^ (5 * A) := by
    calc
      (Q : ℝ) ^ 5 ≤ (L ^ A) ^ 5 :=
        pow_le_pow_left₀ (by positivity) hcut 5
      _ = L ^ (5 * A) := by rw [← pow_mul]; congr 1; omega
  have hratio : (Q : ℝ) ^ 5 / L ^ (5 * A + 2) ≤ 1 / L ^ 2 := by
    apply (div_le_div_iff₀ (pow_pos hL _) (pow_pos hL _)).2
    rw [pow_add]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hQpow (pow_nonneg hL.le 2)
  have hHC : 0 ≤ H * C := mul_nonneg hH hC.le
  have hHCbound : H * C ≤ c * L ^ 2 := by
    have hquot : H * C / c ≤ L :=
      (le_max_right _ _).trans hlogN
    have hlinear : H * C ≤ c * L := by
      exact (div_le_iff₀ hc).1 hquot |>.trans_eq (mul_comm L c)
    have hLsq : L ≤ L ^ 2 := by nlinarith
    exact hlinear.trans (mul_le_mul_of_nonneg_left hLsq hc.le)
  have hsmall : H * C / L ^ 2 ≤ c :=
    (div_le_iff₀ (pow_pos hL 2)).2 hHCbound
  have hD : 0 ≤ C * (N : ℝ) / L ^ (5 * A + 2) := by positivity
  have hscale : 0 ≤ cubicMainScale n N := (cubicMainScale_pos hN).le
  have hslope := exerciseMajorModelSlope_le n N Q (by omega) hN hQ
  calc
    exerciseMajorModelSlope n N Q * (C * (N : ℝ) / L ^ (5 * A + 2)) ≤
        (H * (Q : ℝ) ^ 5 * cubicMainScale n N / (N : ℝ)) *
          (C * (N : ℝ) / L ^ (5 * A + 2)) :=
      mul_le_mul_of_nonneg_right hslope hD
    _ = (H * C * ((Q : ℝ) ^ 5 / L ^ (5 * A + 2))) *
          cubicMainScale n N := by field_simp
    _ ≤ (H * C / L ^ 2) * cubicMainScale n N := by
      apply mul_le_mul_of_nonneg_right _ hscale
      simpa only [div_eq_mul_inv, mul_assoc, one_mul] using
        mul_le_mul_of_nonneg_left hratio hHC
    _ ≤ c * cubicMainScale n N :=
      mul_le_mul_of_nonneg_right hsmall hscale

/-- MA07-2 (FILLED, numeric): the small-endpoint/nonunit terms cost
`Q^5*(sqrt N+1)/N`. Bound each by a fixed `N^(-1/4)` after using
`eventually_logarithmicDenominatorCutoff_pow_le_rpow` with sufficient slack.
Prove the coefficient `nonunitResidueAPConstant+log 4+6` nonnegative first. -/
theorem exercise_eventually_majorEndpointTerm_small (A n : ℕ) (hn : 33 ≤ n)
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      exerciseMajorModelSlope n N (logarithmicDenominatorCutoff A N) *
        (1 + (nonunitResidueAPConstant + (Real.log 4 + 6)) *
          (Real.sqrt (N : ℝ) + 1)) ≤ c * cubicMainScale n N := by
  let K : ℝ := nonunitResidueAPConstant + (Real.log 4 + 6)
  let H : ℝ := exerciseMajorSlopeConstant n
  let D : ℝ := 1 + 2 * K
  have hK : 0 ≤ K := by
    dsimp [K]
    have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hnonunit := nonunitResidueAPConstant_nonneg
    linarith
  have hH : 0 ≤ H := by
    dsimp [H, exerciseMajorSlopeConstant]
    have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hYt : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [exercise_eventually_logarithmicCutoff_pos A,
    eventually_logarithmicDenominatorCutoff_pow_le_rpow A 5
      (by norm_num : (0 : ℝ) < 1 / 4),
    hYt.eventually_ge_atTop (max 1 (H * D / c)),
    eventually_gt_atTop (0 : ℕ)] with N hQ hQpow hY hN
  let x : ℝ := N
  let y : ℝ := x ^ (1 / 4 : ℝ)
  let Q := logarithmicDenominatorCutoff A N
  let E : ℝ := 1 + K * (Real.sqrt x + 1)
  have hx : 0 < x := by dsimp [x]; exact_mod_cast hN
  have hy : 0 < y := by dsimp [y]; positivity
  have hyone : 1 ≤ y := (le_max_left _ _).trans hY
  have hy4 : y ^ 4 = x := by
    dsimp [y]
    rw [← Real.rpow_mul_natCast hx.le (1 / 4 : ℝ) 4]
    norm_num
  have hsqrt : Real.sqrt x = y ^ 2 := by
    rw [Real.sqrt_eq_rpow]
    dsimp [y]
    rw [← Real.rpow_mul_natCast hx.le (1 / 4 : ℝ) 2]
    norm_num
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hEle : E ≤ D * y ^ 2 := by
    dsimp [E, D]
    rw [hsqrt]
    have hy2 : 1 ≤ y ^ 2 := by nlinarith
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + K)
      (sub_nonneg.mpr hy2)]
  have hQreal : (Q : ℝ) ^ 5 ≤ y := by simpa only [Q, x, y] using hQpow
  have hQE : (Q : ℝ) ^ 5 * E ≤ D * y ^ 3 := by
    calc
      (Q : ℝ) ^ 5 * E ≤ y * E :=
        mul_le_mul_of_nonneg_right hQreal hE
      _ ≤ y * (D * y ^ 2) := mul_le_mul_of_nonneg_left hEle hy.le
      _ = D * y ^ 3 := by ring
  have htarget : H * D ≤ c * y := by
    have hquot : H * D / c ≤ y := (le_max_right _ _).trans hY
    nlinarith [(div_le_iff₀ hc).1 hquot]
  have hscalar : H * (Q : ℝ) ^ 5 * E / x ≤ c := by
    apply (div_le_iff₀ hx).2
    rw [← hy4]
    calc
      H * (Q : ℝ) ^ 5 * E ≤ H * (D * y ^ 3) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hQE hH
      _ = (H * D) * y ^ 3 := by ring
      _ ≤ (c * y) * y ^ 3 :=
        mul_le_mul_of_nonneg_right htarget (pow_nonneg hy.le 3)
      _ = c * y ^ 4 := by ring
  have hscale : 0 ≤ cubicMainScale n N := (cubicMainScale_pos hN).le
  calc
    exerciseMajorModelSlope n N Q * E ≤
        (H * (Q : ℝ) ^ 5 * cubicMainScale n N / x) * E :=
      mul_le_mul_of_nonneg_right
        (exerciseMajorModelSlope_le n N Q (by omega) hN hQ) hE
    _ = (H * (Q : ℝ) ^ 5 * E / x) * cubicMainScale n N := by ring
    _ ≤ c * cubicMainScale n N :=
      mul_le_mul_of_nonneg_right hscalar hscale

/-- MA07-3 (FILLED, numeric): the cutoff correction costs `Q^6/N`.
Apply the same eventual cutoff-power lemma directly at exponent six with
a power of `N` strictly below one; absorb the fixed `log 4+4` factor. -/
theorem exercise_eventually_majorCutoffTerm_small (A n : ℕ) (hn : 33 ≤ n)
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      exerciseMajorModelSlope n N (logarithmicDenominatorCutoff A N) *
        ((Real.log 4 + 4) * logarithmicDenominatorCutoff A N) ≤
          c * cubicMainScale n N := by
  let K : ℝ := Real.log 4 + 4
  let H : ℝ := exerciseMajorSlopeConstant n
  have hK : 0 ≤ K := by
    dsimp [K]
    have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hH : 0 ≤ H := by
    dsimp [H, exerciseMajorSlopeConstant]
    positivity
  have hYt : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [exercise_eventually_logarithmicCutoff_pos A,
    eventually_logarithmicDenominatorCutoff_pow_le_rpow A 6
      (by norm_num : (0 : ℝ) < 1 / 2),
    hYt.eventually_ge_atTop (H * K / c),
    eventually_gt_atTop (0 : ℕ)] with N hQ hQpow hY hN
  let x : ℝ := N
  let y : ℝ := x ^ (1 / 2 : ℝ)
  let Q := logarithmicDenominatorCutoff A N
  have hx : 0 < x := by dsimp [x]; exact_mod_cast hN
  have hy : 0 < y := by dsimp [y]; positivity
  have hy2 : y ^ 2 = x := by
    dsimp [y]
    rw [← Real.rpow_mul_natCast hx.le (1 / 2 : ℝ) 2]
    norm_num
  have hQreal : (Q : ℝ) ^ 6 ≤ y := by simpa only [Q, x, y] using hQpow
  have htarget : H * K ≤ c * y := by
    nlinarith [(div_le_iff₀ hc).1 hY]
  have hscalar : H * K * (Q : ℝ) ^ 6 / x ≤ c := by
    apply (div_le_iff₀ hx).2
    rw [← hy2]
    calc
      H * K * (Q : ℝ) ^ 6 ≤ (H * K) * y :=
        mul_le_mul_of_nonneg_left hQreal (mul_nonneg hH hK)
      _ ≤ (c * y) * y := mul_le_mul_of_nonneg_right htarget hy.le
      _ = c * y ^ 2 := by ring
  have hE : 0 ≤ K * (Q : ℝ) := by positivity
  have hscale : 0 ≤ cubicMainScale n N := (cubicMainScale_pos hN).le
  calc
    exerciseMajorModelSlope n N Q * (K * (Q : ℝ)) ≤
        (H * (Q : ℝ) ^ 5 * cubicMainScale n N / x) * (K * (Q : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (exerciseMajorModelSlope_le n N Q (by omega) hN hQ) hE
    _ = (H * K * (Q : ℝ) ^ 6 / x) * cubicMainScale n N := by ring
    _ ≤ c * cubicMainScale n N :=
      mul_le_mul_of_nonneg_right hscalar hscale

/-- MA07-4 (FILLED, numeric): the zero-discrepancy model costs
`Q^4/N + Q^4/N²` after factoring the main scale. The proof bounds these
terms together by a fixed multiple of `Q^4/N` and uses the cutoff's
square-root-scale bound. -/
theorem exercise_eventually_majorBaseTerm_small (A n : ℕ) (hn : 33 ≤ n)
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      exerciseMajorModelError n N (logarithmicDenominatorCutoff A N) 0 ≤
        c * cubicMainScale n N := by
  let H : ℝ := 8 * (n : ℝ) * (Real.log 4 + 4) ^ (n - 1) *
    (1 + 10 * Real.pi)
  have hH : 0 ≤ H := by
    dsimp [H]
    have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  have hYt : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [exercise_eventually_logarithmicCutoff_pos A,
    eventually_logarithmicDenominatorCutoff_pow_le_rpow A 4
      (by norm_num : (0 : ℝ) < 1 / 2),
    hYt.eventually_ge_atTop (H / c),
    eventually_gt_atTop (0 : ℕ)] with N hQ hQpow hY hN
  let x : ℝ := N
  let y : ℝ := x ^ (1 / 2 : ℝ)
  let Q := logarithmicDenominatorCutoff A N
  have hx : 0 < x := by dsimp [x]; exact_mod_cast hN
  have hxone : 1 ≤ x := by dsimp [x]; exact_mod_cast hN
  have hy : 0 < y := by dsimp [y]; positivity
  have hy2 : y ^ 2 = x := by
    dsimp [y]
    rw [← Real.rpow_mul_natCast hx.le (1 / 2 : ℝ) 2]
    norm_num
  have hQreal : (Q : ℝ) ^ 4 ≤ y := by simpa only [Q, x, y] using hQpow
  have hQone : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQsq : ((Q + 1 : ℕ) : ℝ) ^ 2 ≤ 4 * (Q : ℝ) ^ 2 := by
    push_cast
    nlinarith [sq_nonneg ((Q : ℝ) - 1)]
  have hB : (1 + 8 * Real.pi * (Q : ℝ)) +
      2 * Real.pi * (Q : ℝ) / x ≤
        (1 + 10 * Real.pi) * (Q : ℝ) := by
    have hterm : 2 * Real.pi * (Q : ℝ) / x ≤
        2 * Real.pi * (Q : ℝ) :=
      div_le_self (by positivity) hxone
    nlinarith [Real.pi_pos]
  have hpre : exerciseMajorModelError n N Q 0 ≤
      (4 * (Q : ℝ) ^ 2) *
        ((n : ℝ) * ((Real.log 4 + 4) * x) ^ (n - 1) *
          ((1 + 10 * Real.pi) * (Q : ℝ)) *
          (2 * (Q : ℝ) / x ^ 3)) := by
    unfold exerciseMajorModelError
    simp only [mul_zero, zero_add, one_mul]
    gcongr
  have hmodel : exerciseMajorModelError n N Q 0 ≤
      H * (Q : ℝ) ^ 4 * cubicMainScale n N / x := by
    calc
      _ ≤ (4 * (Q : ℝ) ^ 2) *
          ((n : ℝ) * ((Real.log 4 + 4) * x) ^ (n - 1) *
            ((1 + 10 * Real.pi) * (Q : ℝ)) *
            (2 * (Q : ℝ) / x ^ 3)) := hpre
      _ = H * (Q : ℝ) ^ 4 * cubicMainScale n N / x := by
        unfold H cubicMainScale
        rw [mul_pow, show n - 1 = (n - 3) + 2 by omega, pow_add]
        field_simp
        ring
  have htarget : H ≤ c * y := by
    nlinarith [(div_le_iff₀ hc).1 hY]
  have hscalar : H * (Q : ℝ) ^ 4 / x ≤ c := by
    apply (div_le_iff₀ hx).2
    rw [← hy2]
    calc
      H * (Q : ℝ) ^ 4 ≤ H * y :=
        mul_le_mul_of_nonneg_left hQreal hH
      _ ≤ (c * y) * y := mul_le_mul_of_nonneg_right htarget hy.le
      _ = c * y ^ 2 := by ring
  have hscale : 0 ≤ cubicMainScale n N := (cubicMainScale_pos hN).le
  calc
    exerciseMajorModelError n N Q 0 ≤
        H * (Q : ℝ) ^ 4 * cubicMainScale n N / x := hmodel
    _ = (H * (Q : ℝ) ^ 4 / x) * cubicMainScale n N := by ring
    _ ≤ c * cubicMainScale n N :=
      mul_le_mul_of_nonneg_right hscalar hscale

/-- MA07-5 (FILLED): recombine the four scalar budgets into the model error.
The scalar limits are precisely MA07-1--MA07-4; this wrapper adds no new
asymptotic reasoning or target dependence. -/
theorem exercise_eventually_modelError_small (A n : ℕ) (hn : 33 ≤ n)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      exerciseMajorModelError n N (logarithmicDenominatorCutoff A N)
        (exerciseMajorAPEnvelope A (5 * A + 2) N C) ≤
          c * cubicMainScale n N := by
  have hc4 : 0 < c / 4 := by linarith
  filter_upwards [exercise_eventually_majorAPTerm_small A n hn hC hc4,
    exercise_eventually_majorEndpointTerm_small A n hn hc4,
    exercise_eventually_majorCutoffTerm_small A n hn hc4,
    exercise_eventually_majorBaseTerm_small A n hn hc4] with
    N hAP hendpoint hcutoff hbase
  rw [exerciseMajorModelError_split A n N C]
  linarith

/-- Filled assembly from AP discrepancy to the truncated main term.
All remaining obligations occur in the named exercises above. -/
theorem exercise_eventually_majorArc_sub_truncated_small
    (A n : ℕ) (hn : 33 ≤ n) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ T : ℕ,
      ‖cubicMajorArcIntegral n N T (logarithmicDenominatorCutoff A N) -
        exerciseTruncatedMainTerm n N T (logarithmicDenominatorCutoff A N)‖ ≤
          c * cubicMainScale n N := by
  obtain ⟨C, hC, hAP⟩ := exercise_eventually_allResidueAP A (5 * A + 2)
  filter_upwards [hAP, exercise_eventually_modelError_small A n hn hC hc,
    eventually_two_mul_logarithmicCutoff_cube_le A,
    eventually_gt_atTop (0 : ℕ)] with N hAPN herr hscale hN T
  let Q := logarithmicDenominatorCutoff A N
  let D := exerciseMajorAPEnvelope A (5 * A + 2) N C
  have hD : 0 ≤ D := by
    dsimp [D, exerciseMajorAPEnvelope]
    have hlog : 0 ≤ exerciseMajorLog N := by
      dsimp [exerciseMajorLog]
      exact Real.log_nonneg (by
        have hNnonneg : 0 ≤ (N : ℝ) := by positivity
        linarith)
    have hK := nonunitResidueAPConstant_nonneg
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  have hscaleNat : 2 * Q ^ 3 ≤ N ^ 3 := by
    dsimp [Q]
    exact_mod_cast hscale
  have hbound := norm_cubicMajorArcIntegral_sub_truncatedMainTerm_le_global
    n N T Q hscaleNat (fun _ => D) D hN hD
    (fun _ _ => ⟨hD, le_rfl⟩) (by
      intro aq haq hqn
      letI : NeZero aq.2 := ⟨hqn⟩
      have hcenter : aq ∈ majorArcCenters Q := by
        simpa only [Set.Finite.mem_toFinset] using haq
      exact hAPN aq.2 inferInstance hcenter.1)
  exact hbound.trans herr

/-- A positive target-independent bound for the full singular series. -/
noncomputable def exerciseSeriesNormBudget (n : ℕ) : ℝ :=
  (∑' q : ℕ, singularSeriesTermNormMaximum n q) + 1

/-- A positive target-independent bound for the full singular integral. -/
noncomputable def exerciseIntegralNormBudget (n : ℕ) : ℝ :=
  (∫ tau : ℝ, ‖singularIntegrand n 0 tau‖) + 1

/-- MA08 (FILLED, sum norms): the maximum-coefficient envelope bounds the
full series for every target. Rewrite `singularSeries` as `tsum`, invoke
`norm_tsum_le_tsum_norm (summable_norm_singularSeriesTerm hn)`, then apply
`Summable.tsum_le_tsum` with `norm_singularSeriesTerm_le_maximum`.
The `q=0` case simplifies to zero; positive `q` is the existing theorem.
Nonnegativity of the envelope's terms proves strict positivity after `+1`.
Use `summable_singularSeriesTermNormMaximum hn` for the right-hand tsum. -/
theorem exercise_uniformSeriesNorm (n : ℕ) (hn : 33 ≤ n) :
    0 < exerciseSeriesNormBudget n ∧
      ∀ T : ℕ, ‖singularSeries n T‖ ≤ exerciseSeriesNormBudget n := by
  have hnonneg : 0 ≤ ∑' q : ℕ, singularSeriesTermNormMaximum n q :=
    tsum_nonneg (fun q => singularSeriesTermNormMaximum_nonneg n q)
  refine ⟨by dsimp [exerciseSeriesNormBudget]; linarith, ?_⟩
  intro T
  have hnorm := summable_norm_singularSeriesTerm (T := T) hn
  have hmax := summable_singularSeriesTermNormMaximum hn
  have hterm (q : ℕ) :
      ‖singularSeriesTerm n T q‖ ≤ singularSeriesTermNormMaximum n q := by
    by_cases hq : q = 0
    · simp [hq, singularSeriesTermNormMaximum]
    · exact norm_singularSeriesTerm_le_maximum n q T (Nat.pos_of_ne_zero hq)
  calc
    _ ≤ ∑' q : ℕ, ‖singularSeriesTerm n T q‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' q : ℕ, singularSeriesTermNormMaximum n q :=
      Summable.tsum_le_tsum hterm hnorm hmax
    _ ≤ exerciseSeriesNormBudget n := by dsimp [exerciseSeriesNormBudget]; linarith

/-- MA09 (FILLED, integral norms): remove the target phase of norm one.
Use `norm_integral_le_integral_norm` and
`singularIntegrand_integrable (by omega : 4≤n) mu`. Pointwise norms agree
with target `0` by `simp [singularIntegrand]`. The integral of a norm is
nonnegative, so adding `1` proves strict positivity. No compact-window
argument or additional Fourier estimate is needed. -/
theorem exercise_uniformIntegralNorm (n : ℕ) (hn : 33 ≤ n) :
    0 < exerciseIntegralNormBudget n ∧
      ∀ mu : ℝ, ‖singularIntegral n mu‖ ≤ exerciseIntegralNormBudget n := by
  have hnonneg : 0 ≤ ∫ tau : ℝ, ‖singularIntegrand n 0 tau‖ :=
    integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨by dsimp [exerciseIntegralNormBudget]; linarith, ?_⟩
  intro mu
  have h4 : 4 ≤ n := by omega
  have _hint := singularIntegrand_integrable h4 mu
  have heq : (fun tau => ‖singularIntegrand n mu tau‖) =
      (fun tau => ‖singularIntegrand n 0 tau‖) := by
    funext tau
    simp [singularIntegrand]
  calc
    _ ≤ ∫ tau : ℝ, ‖singularIntegrand n mu tau‖ := norm_integral_le_integral_norm _
    _ = ∫ tau : ℝ, ‖singularIntegrand n 0 tau‖ := by rw [heq]
    _ ≤ exerciseIntegralNormBudget n := by
      dsimp [exerciseIntegralNormBudget]
      linarith

/-- MA10 (FILLED, norm algebra): a two-error product estimate.
The exact identity to verify with `ring` is
`Iq*Sq-I*S = (Iq-I)*Sq + I*(Sq-S)`. Apply `norm_add_le`, `norm_mul`, then
`mul_le_mul` using the nonnegative constants. This statement is independent
of the circle method and can be solved first as a warm-up. -/
theorem exercise_productError_le (Iq I Sq S : ℂ) (ei es BI BS : ℝ)
    (hei : ‖Iq - I‖ ≤ ei) (hes : ‖Sq - S‖ ≤ es)
    (hI : ‖I‖ ≤ BI) (hSq : ‖Sq‖ ≤ BS) :
    ‖Iq * Sq - I * S‖ ≤ ei * BS + BI * es := by
  have heq : Iq * Sq - I * S = (Iq - I) * Sq + I * (Sq - S) := by ring
  rw [heq]
  calc
    _ ≤ ‖(Iq - I) * Sq‖ + ‖I * (Sq - S)‖ := norm_add_le _ _
    _ = ‖Iq - I‖ * ‖Sq‖ + ‖I‖ * ‖Sq - S‖ := by simp only [norm_mul]
    _ ≤ ei * BS + BI * es := add_le_add
      (mul_le_mul hei hSq (norm_nonneg _) ((norm_nonneg _).trans hei))
      (mul_le_mul hI hes (norm_nonneg _) ((norm_nonneg _).trans hI))

/-- MA11 (FILLED, routine tails): products of the two truncations converge
uniformly in **both** the real normalized target and the integer target.

Set `BI=exerciseIntegralNormBudget n`, `BS=exerciseSeriesNormBudget n+1`,
and choose `ε=min 1 (c/(2*(BI+BS)))`, with positivity proved first.
Compose `truncatedSingularIntegral_tendsto_uniform` with
`tendsto_logarithmicDenominatorCutoff A hA`. Combine it using `filter_upwards`
with `eventually_norm_singularSeries_sub_logarithmicTruncation_lt` at `ε`
and at `1`. The latter gives `‖Sq‖≤‖S‖+1≤BS` by `norm_sub_le`.
Apply MA10 and MA08--MA09. The two errors cost at most `ε*(BS+BI)≤c`.
Do not specialize the target before taking the eventual threshold. -/
theorem exercise_eventually_truncatedCoefficient_small
    (A n : ℕ) (hA : 0 < A) (hn : 33 ≤ n) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ mu : ℝ, ∀ T : ℕ,
      ‖truncatedSingularIntegral n mu (logarithmicDenominatorCutoff A N) *
          truncatedSingularSeries n T (logarithmicDenominatorCutoff A N) -
        singularIntegral n mu * singularSeries n T‖ ≤ c := by
  let BI := exerciseIntegralNormBudget n
  let BS := exerciseSeriesNormBudget n + 1
  have hBI : 0 < BI := (exercise_uniformIntegralNorm n hn).1
  have hBS : 0 < BS := by
    dsimp [BS]
    linarith [(exercise_uniformSeriesNorm n hn).1]
  let ε := c / (BI + BS)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hcutoff := tendsto_logarithmicDenominatorCutoff A hA
  have hItail := hcutoff.eventually
    (truncatedSingularIntegral_tendsto_uniform (n := n) (by omega : 4 ≤ n) hε)
  have hStail := eventually_norm_singularSeries_sub_logarithmicTruncation_lt
    hn A hA hε
  have hStailOne := eventually_norm_singularSeries_sub_logarithmicTruncation_lt
    hn A hA (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hItail, hStail, hStailOne] with N hI hS hSone mu T
  let Iq := truncatedSingularIntegral n mu (logarithmicDenominatorCutoff A N)
  let I := singularIntegral n mu
  let Sq := truncatedSingularSeries n T (logarithmicDenominatorCutoff A N)
  let S := singularSeries n T
  have hSq : ‖Sq‖ ≤ BS := by
    have hnorm : ‖Sq‖ ≤ ‖Sq - S‖ + ‖S‖ := by
      calc
        ‖Sq‖ = ‖(Sq - S) + S‖ := by congr 1; ring
        _ ≤ ‖Sq - S‖ + ‖S‖ := norm_add_le _ _
    have hseries : ‖S‖ ≤ exerciseSeriesNormBudget n :=
      (exercise_uniformSeriesNorm n hn).2 T
    have herror : ‖Sq - S‖ < 1 := by
      simpa only [norm_sub_rev] using hSone T
    dsimp [BS]
    linarith
  have hprod : ‖Iq * Sq - I * S‖ ≤ ε * BS + BI * ε :=
    exercise_productError_le Iq I Sq S ε ε BI BS
      (le_of_lt (hI mu))
      (le_of_lt (by simpa only [norm_sub_rev] using hS T))
      ((exercise_uniformIntegralNorm n hn).2 mu) hSq
  calc
    ‖Iq * Sq - I * S‖ ≤ ε * BS + BI * ε := hprod
    _ = c := by
      dsimp [ε]
      field_simp
      ring

/-- MA12 (FILLED, scalar normalization): factor out exactly `N^(n-3)`.
Use `N>0`, `n≥33`, `n=(n-3)+3` from `omega`, `pow_add`, and
`field_simp` to prove `N^n / N³ = N^(n-3)`. Convert real scalar action on
`ℂ` to multiplication via `Complex.real_smul` (or `simp`), then `ring`.
This prevents a loss of three powers or a hidden division by zero. -/
theorem exercise_truncatedMainTerm_eq_scale (n N T Q : ℕ)
    (hn : 33 ≤ n) (hN : 0 < N) :
    exerciseTruncatedMainTerm n N T Q =
      (cubicMainScale n N : ℂ) *
        (truncatedSingularIntegral n (normalizedTarget N T) Q *
          truncatedSingularSeries n T Q) := by
  have hNzero : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hreal : (N : ℝ) ^ n * ((N : ℝ) ^ 3)⁻¹ = (N : ℝ) ^ (n - 3) := by
    calc
      _ = (N : ℝ) ^ ((n - 3) + 3) * ((N : ℝ) ^ 3)⁻¹ := by
        congr 2
        omega
      _ = _ := by rw [pow_add]; field_simp
  have hcomplex : (((N : ℝ) ^ n : ℂ) * (((N : ℝ) ^ 3)⁻¹ : ℂ)) =
      ((N : ℝ) ^ (n - 3) : ℂ) := by exact_mod_cast hreal
  dsimp [exerciseTruncatedMainTerm, cubicMainScale, normalizedTarget]
  simp only [Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_natCast]
  calc
    _ = (((N : ℝ) ^ n : ℂ) * (((N : ℝ) ^ 3)⁻¹ : ℂ)) *
        (truncatedSingularIntegral n ((T : ℝ) / (N : ℝ) ^ 3) Q *
          truncatedSingularSeries n T Q) := by
            simp only [Complex.ofReal_natCast]
            ring
    _ = _ := by
      rw [hcomplex]
      simp only [Complex.ofReal_natCast]

/-- MA13 (FILLED, real/complex conversion): the full analytic product is
real on admissible arithmetic targets.
Use `singularSeries_im_eq_zero_of_admissible hn hT` and
`singularIntegral_eq_ofReal_re`; a complex number with zero imaginary part
equals the cast of its real part. Expand `cubicSingularMainTerm` and
`cubicSingularCoefficient`, then finish by `Complex.ext`, `simp`, and `ring`.
Only the divisibility `24∣T` is needed; no normalized-window bound is used. -/
theorem exercise_fullMainTerm_eq_real (n N T : ℕ)
    (hn : 33 ≤ n) (hT : 24 ∣ T) :
    (cubicMainScale n N : ℂ) *
      (singularIntegral n (normalizedTarget N T) * singularSeries n T) =
        (cubicSingularMainTerm n N T : ℂ) := by
  have hI := singularIntegral_im_eq_zero n (normalizedTarget N T)
  have hS := singularSeries_im_eq_zero_of_admissible hn hT
  dsimp only [cubicSingularMainTerm, cubicSingularCoefficient]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, hI, hS] <;> ring

/-- Filled scaling adapter from uniform coefficient tails to the real main
term. It consumes the explicitly named MA11--MA13 exercises. -/
theorem exercise_eventually_truncatedMainTerm_small
    (A n : ℕ) (hA : 0 < A) (hn : 33 ≤ n) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ T : ℕ, 24 ∣ T →
      ‖exerciseTruncatedMainTerm n N T (logarithmicDenominatorCutoff A N) -
        (cubicSingularMainTerm n N T : ℂ)‖ ≤ c * cubicMainScale n N := by
  filter_upwards [exercise_eventually_truncatedCoefficient_small A n hA hn hc,
    eventually_gt_atTop (0 : ℕ)] with N htail hN T hT
  rw [exercise_truncatedMainTerm_eq_scale n N T _ hn hN,
    ← exercise_fullMainTerm_eq_real n N T hn hT, ← mul_sub, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (cubicMainScale_pos hN).le]
  calc
    _ ≤ cubicMainScale n N * c :=
      mul_le_mul_of_nonneg_left (htail (normalizedTarget N T) T)
        (cubicMainScale_pos hN).le
    _ = _ := mul_comm _ _

/-- MA14: final assembly is filled. For every fixed positive cutoff exponent,
the major-arc error is eventually smaller than any positive multiple of
the main scale, uniformly in every admissible moving target.

Dependency order: MA01--MA06 → all-residue AP → MA07 → truncated model;
MA08--MA13 → full main term; this theorem combines the two with budget `c/2`
each. The complete dependency cone uses only standard logical axioms. -/
theorem eventually_majorArc_error_small (A : ℕ) (hA : 0 < A)
    (n : ℕ) (hn : 33 ≤ n) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ T : ℕ, IsAdmissibleTarget n N T →
      ‖cubicMajorArcIntegral n N T (logarithmicDenominatorCutoff A N) -
        (cubicSingularMainTerm n N T : ℂ)‖ ≤ c * cubicMainScale n N := by
  have hc2 : 0 < c / 2 := by linarith
  filter_upwards [exercise_eventually_majorArc_sub_truncated_small A n hn hc2,
    exercise_eventually_truncatedMainTerm_small A n hA hn hc2] with
    N hmodel htail T hT
  have hsum := norm_add_le
    (cubicMajorArcIntegral n N T (logarithmicDenominatorCutoff A N) -
      exerciseTruncatedMainTerm n N T (logarithmicDenominatorCutoff A N))
    (exerciseTruncatedMainTerm n N T (logarithmicDenominatorCutoff A N) -
      (cubicSingularMainTerm n N T : ℂ))
  have heq :
      cubicMajorArcIntegral n N T (logarithmicDenominatorCutoff A N) -
        (cubicSingularMainTerm n N T : ℂ) =
      (cubicMajorArcIntegral n N T (logarithmicDenominatorCutoff A N) -
        exerciseTruncatedMainTerm n N T (logarithmicDenominatorCutoff A N)) +
      (exerciseTruncatedMainTerm n N T (logarithmicDenominatorCutoff A N) -
        (cubicSingularMainTerm n N T : ℂ)) := by ring
  rw [heq]
  exact hsum.trans (by
    have h1 := hmodel T
    have h2 := htail T hT.1
    linarith)

/-- Public adapter used by the aggregate constructor, with all analytic
source estimates proved above. -/
theorem exercise_eventually_major_error_logarithmic_cutoff
    (A n : ℕ) (hA : 0 < A) (hn : 33 ≤ n) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ T : ℕ, IsAdmissibleTarget n N T →
      ‖cubicMajorArcIntegral n N T (logarithmicDenominatorCutoff A N) -
        (cubicSingularMainTerm n N T : ℂ)‖ ≤ c * cubicMainScale n N :=
  eventually_majorArc_error_small A hA n hn hc

end SystolicGrowth.CookMagyarCircle

-- The analytic source and its consumers must use only standard logical axioms.
#print axioms SystolicGrowth.CookMagyarCircle.eventually_majorArc_error_small
#print axioms SystolicGrowth.CookMagyarCircle.exerciseMajorModelSlope_le
#print axioms SystolicGrowth.CookMagyarCircle.exercise_eventually_modelError_small
#print axioms SystolicGrowth.CookMagyarCircle.exercise_eventually_truncatedCoefficient_small
#print axioms SystolicGrowth.CookMagyarCircle.exercise_exceptionalTerm_absorbed
#print axioms SystolicGrowth.CookMagyarCircle.exercise_siegel_real_zero_lower
#print axioms SystolicGrowth.CookMagyarCircle.exercise_exceptionalResidue_le_term_add_absorbed
#print axioms SystolicGrowth.CookMagyarCircle.exercise_characterPsi_logSaving
#print axioms SystolicGrowth.CookMagyarCircle.negative_logDeriv_LFunction_eq_twisted_LSeries
#print axioms SystolicGrowth.CookMagyarCircle.exercisePerronAbscissa_bounds
#print axioms SystolicGrowth.CookMagyarCircle.exercisePerronIntegral_eq_tsum
#print axioms SystolicGrowth.CookMagyarCircle.exercisePerronIntegral_eq_logDerivativeIntegrand
#print axioms SystolicGrowth.CookMagyarCircle.exerciseTwistedPsi_eq_sum_positive
#print axioms SystolicGrowth.CookMagyarCircle.exercisePrincipalTwistedPsi_eq_chebyshevPsi
#print axioms SystolicGrowth.CookMagyarCircle.exercise_principalTwistedPsi_strongPNT
#print axioms SystolicGrowth.CookMagyarCircle.exercise_principalPerron_integral_strongPNT
#print axioms SystolicGrowth.CookMagyarCircle.exercise_shiftedPerron_principal_modulus_one
#print axioms SystolicGrowth.CookMagyarCircle.exercise_truncatedPerron_error_uniform_rootLog
#print axioms SystolicGrowth.CookMagyarCircle.exercise_eventually_majorLog_pow_le_rootLog_budget
#print axioms SystolicGrowth.CookMagyarCircle.exercise_eventually_principal_primePowerCorrection_absorbed
#print axioms SystolicGrowth.CookMagyarCircle.exercise_eventually_changeLevel_twistedPsi_sub_absorbed
#print axioms SystolicGrowth.CookMagyarCircle.exercise_eventually_changeLevel_perronIntegral_sub_absorbed
#print axioms SystolicGrowth.CookMagyarCircle.exercise_shiftedPerron_principal
#print axioms SystolicGrowth.CookMagyarCircle.sum_twisted_normalized_perron_error_le
#print axioms SystolicGrowth.CookMagyarCircle.exercisePerron_budget_le
#print axioms SystolicGrowth.CookMagyarCircle.sum_exercisePerron_remainder_norm_le
#print axioms SystolicGrowth.CookMagyarCircle.summable_norm_exercisePerron_remainder
#print axioms SystolicGrowth.CookMagyarCircle.norm_tsum_exercisePerron_remainder_le
#print axioms SystolicGrowth.CookMagyarCircle.tsum_indicatorTerm_eq_twistedPsi
#print axioms SystolicGrowth.CookMagyarCircle.summable_integralTerm
#print axioms SystolicGrowth.CookMagyarCircle.tsum_remainder_eq_twistedPsi_sub_perronIntegral
#print axioms SystolicGrowth.CookMagyarCircle.exercise_truncatedPerron_error_explicit
#print axioms SystolicGrowth.CookMagyarCircle.exercise_truncatedPerron_error
#print axioms SystolicGrowth.CookMagyarCircle.exists_exercisePerron_zero_avoiding_height
#print axioms SystolicGrowth.CookMagyarCircle.exercise_perron_height_room
#print axioms SystolicGrowth.CookMagyarCircle.exercise_eventually_exists_perron_zero_avoiding_edges
