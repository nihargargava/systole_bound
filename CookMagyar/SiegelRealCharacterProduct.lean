module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# Nonnegative coefficients of real-character products

The Dirichlet coefficients of `ζ L(χ)` and `ζ L(χ) L(ψ) L(χψ)`
are actual finite divisor convolutions. Real characters are quadratic;
the four-factor coefficients are nonnegative by their local prime-power
arithmetic. These are the positivity inputs in Estermann's argument.
-/

open scoped BigOperators ComplexOrder Topology

namespace SystolicGrowth.CookMagyarCircle

open ArithmeticFunction Filter

variable {q : ℕ}

/-- A real-valued complex Dirichlet character is quadratic. -/
theorem siegel_realCharacter_sq_eq_one [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : ∀ r : ZMod q, (χ r).im = 0) :
    χ ^ 2 = 1 := by
  have hstar : star χ = χ := by
    ext r
    apply Complex.ext <;> simp [hχ r]
  have hinv : χ⁻¹ = χ := by
    rw [← MulChar.star_eq_inv]
    exact hstar
  calc
    χ ^ 2 = χ⁻¹ * χ := by rw [hinv, pow_two]
    _ = 1 := inv_mul_cancel χ

/-- Changing the level preserves the source real-character predicate. -/
theorem siegel_realCharacter_changeLevel {Q : ℕ} [NeZero q] [NeZero Q]
    (χ : DirichletCharacter ℂ q) (hqQ : q ∣ Q)
    (hχ : ∀ r : ZMod q, (χ r).im = 0) :
    ∀ r : ZMod Q, (DirichletCharacter.changeLevel hqQ χ r).im = 0 := by
  have hquad : (DirichletCharacter.changeLevel hqQ χ) ^ 2 = 1 := by
    rw [← map_pow, siegel_realCharacter_sq_eq_one χ hχ, map_one]
  intro r
  rcases (MulChar.isQuadratic_iff_sq_eq_one.mpr hquad) r with h | h | h <;> simp [h]

/-- At a common level, the product of real characters with distinct
conductors is nonprincipal. This is the nonprincipal third `L`-factor
needed in the four-factor Estermann argument. -/
theorem siegel_changeLevel_product_ne_one_of_conductor_ne
    {m Q : ℕ} [NeZero q] [NeZero m] [NeZero Q]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ m)
    (hqQ : q ∣ Q) (hmQ : m ∣ Q)
    (hχ : ∀ r : ZMod q, (χ r).im = 0)
    (hne : χ.conductor ≠ ψ.conductor) :
    DirichletCharacter.changeLevel hqQ χ *
      DirichletCharacter.changeLevel hmQ ψ ≠ 1 := by
  intro heq
  have hquad := siegel_realCharacter_sq_eq_one (DirichletCharacter.changeLevel hqQ χ)
    (siegel_realCharacter_changeLevel χ hqQ hχ)
  have hinv := (MulChar.isQuadratic_iff_sq_eq_one.mpr hquad).inv
  have hchars : DirichletCharacter.changeLevel hmQ ψ =
      DirichletCharacter.changeLevel hqQ χ := by
    calc
      _ = (DirichletCharacter.changeLevel hqQ χ)⁻¹ *
          (DirichletCharacter.changeLevel hqQ χ *
            DirichletCharacter.changeLevel hmQ ψ) := by simp
      _ = _ := by rw [heq, mul_one, hinv]
  apply hne
  calc
    χ.conductor = (DirichletCharacter.changeLevel hqQ χ).conductor :=
      (χ.conductor_changeLevel hqQ).symm
    _ = (DirichletCharacter.changeLevel hmQ ψ).conductor :=
      congrArg DirichletCharacter.conductor hchars.symm
    _ = ψ.conductor := ψ.conductor_changeLevel hmQ

/-- The four-factor coefficients, with multiplication interpreted as
Dirichlet convolution rather than pointwise multiplication. -/
noncomputable def siegelRealCharacterProductCoefficients
    (χ ψ : DirichletCharacter ℂ q) : ArithmeticFunction ℂ :=
  χ.zetaMul * toArithmeticFunction (ψ ·) * toArithmeticFunction ((χ * ψ) ·)

private theorem primePower_mul_congr {p : ℕ} (hp : p.Prime)
    {f g f' g' : ArithmeticFunction ℂ}
    (hf : ∀ k, f (p ^ k) = f' (p ^ k))
    (hg : ∀ k, g (p ^ k) = g' (p ^ k)) (k : ℕ) :
    (f * g) (p ^ k) = (f' * g') (p ^ k) := by
  simp only [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro x hx
  have hxmul := (Nat.mem_divisorsAntidiagonal.mp hx).1
  have hx₁ : x.1 ∣ p ^ k := ⟨x.2, hxmul.symm⟩
  have hx₂ : x.2 ∣ p ^ k := ⟨x.1, by simpa only [mul_comm] using hxmul.symm⟩
  obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow hp).mp hx₁
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp hx₂
  rw [hi, hj, hf i, hg j]

private theorem character_primePower_congr {p : ℕ} (hp : p.Prime)
    {χ ψ : DirichletCharacter ℂ q} (h : χ p = ψ p) (k : ℕ) :
    toArithmeticFunction (χ ·) (p ^ k) = toArithmeticFunction (ψ ·) (p ^ k) := by
  simp only [toArithmeticFunction, ArithmeticFunction.coe_mk,
    pow_ne_zero _ hp.ne_zero, ite_false, Nat.cast_pow, map_pow, h]

private theorem character_primePower_zero {p : ℕ} (hp : p.Prime)
    {χ : DirichletCharacter ℂ q} (h : χ p = 0) (k : ℕ) :
    toArithmeticFunction (χ ·) (p ^ k) = (1 : ArithmeticFunction ℂ) (p ^ k) := by
  cases k with
  | zero => simp [toArithmeticFunction]
  | succ k =>
    have hk : p ^ (k + 1) ≠ 1 := ne_of_gt (one_lt_pow₀ hp.one_lt (by omega))
    rw [ArithmeticFunction.one_apply_ne hk]
    simp [toArithmeticFunction, map_pow, h]

private theorem character_primePower_one {p : ℕ} (hp : p.Prime)
    {χ : DirichletCharacter ℂ q} (h : χ p = 1) (k : ℕ) :
    toArithmeticFunction (χ ·) (p ^ k) = (ArithmeticFunction.zeta :
      ArithmeticFunction ℂ) (p ^ k) := by
  simp only [toArithmeticFunction, ArithmeticFunction.coe_mk, pow_ne_zero _ hp.ne_zero,
    ite_false, Nat.cast_pow, map_pow, h, one_pow,
    ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, Nat.cast_one]

private theorem convolution_nonneg (f g : ArithmeticFunction ℂ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (n : ℕ) :
    0 ≤ (f * g) n := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hf x.1) (hg x.2)

/-- The four-factor coefficient sequence is multiplicative. -/
theorem siegelRealCharacterProductCoefficients_isMultiplicative
    (χ ψ : DirichletCharacter ℂ q) :
    (siegelRealCharacterProductCoefficients χ ψ).IsMultiplicative :=
  (χ.isMultiplicative_zetaMul.mul ψ.isMultiplicative_toArithmeticFunction).mul
    (χ * ψ).isMultiplicative_toArithmeticFunction

/-- Its first Dirichlet coefficient is exactly one. -/
theorem siegelRealCharacterProductCoefficients_one
    (χ ψ : DirichletCharacter ℂ q) :
    siegelRealCharacterProductCoefficients χ ψ 1 = 1 :=
  (siegelRealCharacterProductCoefficients_isMultiplicative χ ψ).map_one

/-- The first coefficient of `ζ L(χ)` is exactly one. -/
theorem siegel_zetaMul_one (χ : DirichletCharacter ℂ q) : χ.zetaMul 1 = 1 :=
  χ.isMultiplicative_zetaMul.map_one

set_option maxHeartbeats 800000 in
private theorem product_primePower_nonneg
    {χ ψ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0 ≤ siegelRealCharacterProductCoefficients χ ψ (p ^ k) := by
  let Z : ArithmeticFunction ℂ := ArithmeticFunction.zeta
  let X := toArithmeticFunction (χ ·)
  let Y := toArithmeticFunction (ψ ·)
  let XY := toArithmeticFunction ((χ * ψ) ·)
  have hZ : ∀ j, Z (p ^ j) = Z (p ^ j) := fun _ => rfl
  have hX : ∀ j, X (p ^ j) = X (p ^ j) := fun _ => rfl
  have hY : ∀ j, Y (p ^ j) = Y (p ^ j) := fun _ => rfl
  have hχnonneg := DirichletCharacter.zetaMul_nonneg hχ
  have hψnonneg := DirichletCharacter.zetaMul_nonneg hψ
  change 0 ≤ (Z * X * Y * XY) (p ^ k)
  rcases (MulChar.isQuadratic_iff_sq_eq_one.mpr hχ) p with hχ₀ | hχ₁ | hχneg
  · have hXY₀ : (χ * ψ) p = 0 := by simp [MulChar.mul_apply, hχ₀]
    have hfirst := primePower_mul_congr hp hZ (character_primePower_zero hp hχ₀)
    have hsecond := primePower_mul_congr hp hfirst hY
    have hthird := primePower_mul_congr hp hsecond (character_primePower_zero hp hXY₀) k
    rw [hthird]
    simpa only [mul_one, Z, Y, DirichletCharacter.zetaMul] using hψnonneg (p ^ k)
  · have hXY : (χ * ψ) p = ψ p := by simp [MulChar.mul_apply, hχ₁]
    have hfirst := primePower_mul_congr hp hZ (character_primePower_one hp hχ₁)
    have hsecond := primePower_mul_congr hp hfirst hY
    have hthird := primePower_mul_congr hp hsecond (character_primePower_congr hp hXY) k
    rw [hthird]
    have heq : Z * Z * Y * Y = ψ.zetaMul * ψ.zetaMul := by
      simp only [DirichletCharacter.zetaMul, Z, Y]
      ac_rfl
    rw [heq]
    exact convolution_nonneg _ _ hψnonneg hψnonneg _
  · rcases (MulChar.isQuadratic_iff_sq_eq_one.mpr hψ) p with hψ₀ | hψ₁ | hψneg
    · have hXY₀ : (χ * ψ) p = 0 := by simp [MulChar.mul_apply, hψ₀]
      have hfirst := primePower_mul_congr hp (primePower_mul_congr hp hZ hX)
        (character_primePower_zero hp hψ₀)
      have hsecond := primePower_mul_congr hp hfirst (character_primePower_zero hp hXY₀) k
      rw [hsecond]
      simpa only [mul_one, Z, X, DirichletCharacter.zetaMul] using hχnonneg (p ^ k)
    · have hXY : (χ * ψ) p = χ p := by simp [MulChar.mul_apply, hψ₁]
      have hfirst := primePower_mul_congr hp (primePower_mul_congr hp hZ hX)
        (character_primePower_one hp hψ₁)
      have hsecond := primePower_mul_congr hp hfirst (character_primePower_congr hp hXY) k
      rw [hsecond]
      have heq : Z * X * Z * X = χ.zetaMul * χ.zetaMul := by
        simp only [DirichletCharacter.zetaMul, Z, X]
        ac_rfl
      rw [heq]
      exact convolution_nonneg _ _ hχnonneg hχnonneg _
    · have hXY₁ : (χ * ψ) p = 1 := by simp [MulChar.mul_apply, hχneg, hψneg]
      have hYX : ψ p = χ p := hψneg.trans hχneg.symm
      have hfirst := primePower_mul_congr hp (primePower_mul_congr hp hZ hX)
        (character_primePower_congr hp hYX)
      have hsecond := primePower_mul_congr hp hfirst (character_primePower_one hp hXY₁) k
      rw [hsecond]
      have heq : Z * X * X * Z = χ.zetaMul * χ.zetaMul := by
        simp only [DirichletCharacter.zetaMul, Z, X]
        ac_rfl
      rw [heq]
      exact convolution_nonneg _ _ hχnonneg hχnonneg _

/-- Every four-factor coefficient is nonnegative for real characters. -/
theorem siegelRealCharacterProductCoefficients_nonneg [NeZero q]
    (χ ψ : DirichletCharacter ℂ q)
    (hχ : ∀ r : ZMod q, (χ r).im = 0) (hψ : ∀ r : ZMod q, (ψ r).im = 0)
    (n : ℕ) : 0 ≤ siegelRealCharacterProductCoefficients χ ψ n := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  · have hmult := siegelRealCharacterProductCoefficients_isMultiplicative χ ψ
    simpa only [hmult.multiplicative_factorization _ hn] using!
      Finset.prod_nonneg (s := n.primeFactors) fun p hp => product_primePower_nonneg
        (siegel_realCharacter_sq_eq_one χ hχ) (siegel_realCharacter_sq_eq_one ψ hψ)
        (Nat.prime_of_mem_primeFactors hp) (n.factorization p)

/-- The two-factor coefficients are also nonnegative for a real character. -/
theorem siegel_zetaMul_coefficients_nonneg [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : ∀ r : ZMod q, (χ r).im = 0) (n : ℕ) :
    0 ≤ χ.zetaMul n :=
  DirichletCharacter.zetaMul_nonneg (siegel_realCharacter_sq_eq_one χ hχ) n

/-- Nonnegative four-factor coefficients are real, with nonnegative real part. -/
theorem siegelRealCharacterProductCoefficients_re_nonneg_im_zero [NeZero q]
    (χ ψ : DirichletCharacter ℂ q)
    (hχ : ∀ r : ZMod q, (χ r).im = 0) (hψ : ∀ r : ZMod q, (ψ r).im = 0)
    (n : ℕ) :
    0 ≤ (siegelRealCharacterProductCoefficients χ ψ n).re ∧
      (siegelRealCharacterProductCoefficients χ ψ n).im = 0 := by
  have h := Complex.nonneg_iff.mp
    (siegelRealCharacterProductCoefficients_nonneg χ ψ hχ hψ n)
  exact ⟨h.1, h.2.symm⟩

private theorem character_arithmetic_LSeriesSummable
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (toArithmeticFunction (χ ·)) s :=
  (LSeriesSummable_congr s χ.apply_eq_toArithmeticFunction_apply).mp
    (χ.LSeriesSummable_of_one_lt_re hs)

private theorem character_arithmetic_LSeries_eq [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (toArithmeticFunction (χ ·)) s = DirichletCharacter.LFunction χ s := by
  rw [← LSeries_congr χ.apply_eq_toArithmeticFunction_apply s,
    χ.LFunction_eq_LSeries hs]

/-- The exact analytic two-factor product on its half-plane of convergence. -/
theorem siegel_zetaMul_LSeries_eq [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries χ.zetaMul s = riemannZeta s * DirichletCharacter.LFunction χ s := by
  have hZ : LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s := by
    exact (LSeriesSummable_congr s (fun _ => ArithmeticFunction.natCoe_apply)).mpr
      (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs)
  have hZeq : LSeries (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s =
      riemannZeta s := by
    exact (LSeries_congr (fun _ => ArithmeticFunction.natCoe_apply) s).trans
      (ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs)
  change LSeries ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
    toArithmeticFunction (χ ·) : ArithmeticFunction ℂ) s = _
  rw [ArithmeticFunction.LSeries_mul' hZ (character_arithmetic_LSeriesSummable χ hs),
    hZeq, character_arithmetic_LSeries_eq χ hs]

/-- The actual four-factor Dirichlet series converges absolutely for `Re(s)>1`. -/
theorem siegelRealCharacterProductCoefficients_LSeriesSummable
    (χ ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (siegelRealCharacterProductCoefficients χ ψ) s :=
  ArithmeticFunction.LSeriesSummable_mul
    (ArithmeticFunction.LSeriesSummable_mul (χ.LSeriesSummable_zetaMul hs)
      (character_arithmetic_LSeriesSummable ψ hs))
    (character_arithmetic_LSeriesSummable (χ * ψ) hs)

/-- The exact analytic four-factor product on its half-plane of convergence. -/
theorem siegelRealCharacterProductCoefficients_LSeries_eq [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (siegelRealCharacterProductCoefficients χ ψ) s =
      riemannZeta s * DirichletCharacter.LFunction χ s *
        DirichletCharacter.LFunction ψ s * DirichletCharacter.LFunction (χ * ψ) s := by
  rw [siegelRealCharacterProductCoefficients,
    ArithmeticFunction.LSeries_mul'
      (ArithmeticFunction.LSeriesSummable_mul (χ.LSeriesSummable_zetaMul hs)
        (character_arithmetic_LSeriesSummable ψ hs))
      (character_arithmetic_LSeriesSummable (χ * ψ) hs),
    ArithmeticFunction.LSeries_mul' (χ.LSeriesSummable_zetaMul hs)
      (character_arithmetic_LSeriesSummable ψ hs),
    siegel_zetaMul_LSeries_eq χ hs, character_arithmetic_LSeries_eq ψ hs,
    character_arithmetic_LSeries_eq (χ * ψ) hs]

private theorem realCharacter_LFunction_pos_of_one_lt [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : ∀ r : ZMod q, (χ r).im = 0)
    {x : ℝ} (hx : 1 < x) : 0 < DirichletCharacter.LFunction χ (x : ℂ) := by
  have hxs : 1 < (x : ℂ).re := by simpa only [Complex.ofReal_re] using hx
  have hpos : 0 < LSeries χ.zetaMul (x : ℂ) := by
    exact (χ.LSeriesSummable_zetaMul hxs).tsum_pos
      (fun n => LSeries.term_nonneg (siegel_zetaMul_coefficients_nonneg χ hχ n) x) 1
      (LSeries.term_pos one_ne_zero (by rw [siegel_zetaMul_one]; exact zero_lt_one) x)
  rw [siegel_zetaMul_LSeries_eq χ hxs] at hpos
  obtain ⟨hZre, hZim⟩ := Complex.pos_iff.mp (riemannZeta_pos_of_one_lt hx)
  obtain ⟨hFre, hFim⟩ := Complex.pos_iff.mp hpos
  simp only [Complex.mul_re, hZim.symm, zero_mul, sub_zero] at hFre
  simp only [Complex.mul_im, hZim.symm, zero_mul, add_zero] at hFim
  have him : (DirichletCharacter.LFunction χ (x : ℂ)).im = 0 :=
    (mul_eq_zero.mp hFim.symm).resolve_left hZre.ne'
  exact Complex.pos_iff.mpr ⟨(mul_pos_iff_of_pos_left hZre).mp hFre, him.symm⟩

/-- A nonprincipal real character has a real, strictly positive `L`-value
on the real half-line `s≥1`. At `1`, continuity gives nonnegativity and
the established nonvanishing theorem makes it strict. -/
theorem siegel_realCharacter_LFunction_pos_of_one_le [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : ∀ r : ZMod q, (χ r).im = 0)
    (hne : χ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    0 < DirichletCharacter.LFunction χ (x : ℂ) := by
  obtain rfl | hxgt := eq_or_lt_of_le hx
  · have hseqReal : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hseq := hseqReal.ofReal
    have hlim := (χ.differentiableAt_LFunction 1 (Or.inr hne)).continuousAt.tendsto.comp hseq
    have hpos (n : ℕ) :
        0 < DirichletCharacter.LFunction χ ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) :=
      realCharacter_LFunction_pos_of_one_lt χ hχ (lt_add_of_pos_right 1 (by positivity))
    have hre : 0 ≤ (DirichletCharacter.LFunction χ 1).re :=
      ge_of_tendsto' (Complex.continuous_re.continuousAt.tendsto.comp hlim)
        (fun n => (Complex.pos_iff.mp (hpos n)).1.le)
    have hlimIm := Complex.continuous_im.continuousAt.tendsto.comp hlim
    have hconstIm : Tendsto
        (fun n : ℕ => (DirichletCharacter.LFunction χ
          ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)).im) atTop (𝓝 0) := by
      convert (tendsto_const_nhds (x := (0 : ℝ))) using 1
      ext n
      exact (Complex.pos_iff.mp (hpos n)).2.symm
    have him : (DirichletCharacter.LFunction χ 1).im = 0 :=
      tendsto_nhds_unique hlimIm hconstIm
    have hreNe : (DirichletCharacter.LFunction χ 1).re ≠ 0 := by
      intro hzero
      apply χ.LFunction_apply_one_ne_zero hne
      exact Complex.ext hzero him
    exact Complex.pos_iff.mpr ⟨lt_of_le_of_ne hre hreNe.symm, him.symm⟩
  · exact realCharacter_LFunction_pos_of_one_lt χ hχ hxgt

end SystolicGrowth.CookMagyarCircle
