module

public import CookMagyar.SiegelCharacterBounds
public import CookMagyar.SiegelEstermann
public import CookMagyar.SiegelRealCharacterProduct
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

@[expose] public section

/-!
# Actual character applications of Estermann's lemma

The universal analytic constants are applied to the actual two- and
four-factor Dirichlet series, with conductor bounds derived from character
partial sums. These are the two quantitative inputs in Siegel's case split.
-/

open scoped BigOperators ComplexOrder Topology

namespace SystolicGrowth.CookMagyarCircle

open Finset

/-- A zero-free real interval ending at `1` preserves the actual positive
sign at `1`. This supplies the first case of Siegel's alternative. -/
theorem siegel_realCharacter_LFunction_nonneg_of_zeroFree_interval
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : ∀ r : ZMod q, (χ r).im = 0) (hne : χ ≠ 1)
    {σ : ℝ} (hσ : 0 < σ) (hσ' : σ < 1)
    (hzeroFree : ∀ x ∈ Set.Ico σ 1, DirichletCharacter.LFunction χ (x : ℂ) ≠ 0) :
    0 ≤ DirichletCharacter.LFunction χ (σ : ℂ) := by
  have hreal := siegel_realCharacter_LFunction_im_eq_zero χ hχ hne hσ
  apply Complex.nonneg_iff.mpr ⟨?_, hreal.symm⟩
  have h1 := (Complex.pos_iff.mp
    (siegel_realCharacter_LFunction_pos_of_one_le χ hχ hne (x := 1) le_rfl)).1
  simp only [Complex.ofReal_one] at h1
  by_contra hneg
  have hcontinuous : ContinuousOn
      (fun x : ℝ => (DirichletCharacter.LFunction χ (x : ℂ)).re) (Set.Icc σ 1) :=
    (Complex.continuous_re.comp ((DirichletCharacter.differentiable_LFunction hne).continuous.comp
      Complex.continuous_ofReal)).continuousOn
  obtain ⟨x, hx, hxzero⟩ := intermediate_value_Icc hσ'.le hcontinuous
    ⟨(not_le.mp hneg).le, by simpa only [Complex.ofReal_one] using h1.le⟩
  have hzero : DirichletCharacter.LFunction χ (x : ℂ) = 0 :=
    Complex.ext hxzero (siegel_realCharacter_LFunction_im_eq_zero χ hχ hne (hσ.trans_le hx.1))
  by_cases hx1 : x = 1
  · subst x
    simp only [Complex.ofReal_one] at hxzero
    exact h1.ne' hxzero
  · exact hzeroFree x ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩ hzero

/-- A fixed modulus has a strictly positive minimum nonprincipal `L(1)`
norm. Finiteness and actual nonvanishing discharge the exceptional modulus
in Siegel's second case. No analytic lower bound is assumed. -/
theorem exists_siegel_LFunction_one_norm_lower_for_modulus
    (q : ℕ) [NeZero q] :
    ∃ c : ℝ, 0 < c ∧ ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      c ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
  classical
  let s : Finset ℝ := (univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).image
    (fun χ => ‖DirichletCharacter.LFunction χ 1‖)
  by_cases hs : s.Nonempty
  · refine ⟨s.min' hs, ?_, ?_⟩
    · obtain ⟨χ, hχ, heq⟩ := mem_image.mp (s.min'_mem hs)
      rw [← heq]
      exact norm_pos_iff.mpr (χ.LFunction_apply_one_ne_zero (mem_filter.mp hχ).2)
    · intro χ hχ
      apply s.min'_le
      exact mem_image.mpr ⟨χ, mem_filter.mpr ⟨mem_univ _, hχ⟩, rfl⟩
  · refine ⟨1, zero_lt_one, ?_⟩
    intro χ hχ
    exact (hs ⟨_, mem_image.mpr ⟨χ, mem_filter.mpr ⟨mem_univ _, hχ⟩, rfl⟩⟩).elim

/-- Adding only the fixed modulus `m` changes the value at `1` by at most
`2` for each prime divisor of `m`. Primes already dividing `q` contribute
exactly `1`, so the constant does not grow with the variable conductor. -/
theorem siegel_LFunction_changeLevel_mul_one_norm_le
    {q m : ℕ} [NeZero q] [NeZero m]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ‖DirichletCharacter.LFunction
      (DirichletCharacter.changeLevel (Nat.dvd_mul_right q m) χ) 1‖ ≤
      (2 : ℝ) ^ m.primeFactors.card * ‖DirichletCharacter.LFunction χ 1‖ := by
  have : NeZero (q * m) := ⟨mul_ne_zero (NeZero.ne q) (NeZero.ne m)⟩
  let f : ℕ → ℂ := fun p => 1 - χ (p : ZMod q) * (p : ℂ) ^ (-(1 : ℂ))
  have hprimeQ : m.primeFactors ⊆ (q * m).primeFactors := by
    rw [Nat.primeFactors_mul (NeZero.ne q) (NeZero.ne m)]
    exact subset_union_right
  have hfactor_one (p : ℕ) (hp : p ∈ (q * m).primeFactors)
      (hpm : p ∉ m.primeFactors) : f p = 1 := by
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpq : p ∈ q.primeFactors := by
      rw [Nat.primeFactors_mul (NeZero.ne q) (NeZero.ne m)] at hp
      exact (mem_union.mp hp).resolve_right hpm
    have hnonunit : ¬ IsUnit (p : ZMod q) := by
      rw [ZMod.isUnit_prime_iff_not_dvd hpp]
      exact not_not.mpr (Nat.dvd_of_mem_primeFactors hpq)
    simp [f, χ.map_nonunit hnonunit]
  have hprod : (∏ p ∈ (q * m).primeFactors, f p) = ∏ p ∈ m.primeFactors, f p :=
    (prod_subset hprimeQ hfactor_one).symm
  have hfactor (p : ℕ) (hp : p ∈ m.primeFactors) : ‖f p‖ ≤ 2 := by
    have hp0 : 0 < p := Nat.pos_of_mem_primeFactors hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
    have hpow : ‖(p : ℂ) ^ (-(1 : ℂ))‖ ≤ 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hp0]
      simp only [Complex.neg_re, Complex.one_re, Real.rpow_neg_one]
      exact inv_le_one_of_one_le₀ hp1
    calc
      ‖f p‖ ≤ ‖(1 : ℂ)‖ + ‖χ (p : ZMod q) * (p : ℂ) ^ (-(1 : ℂ))‖ :=
        norm_sub_le _ _
      _ ≤ 1 + 1 * 1 := by
        rw [norm_one, norm_mul]
        exact add_le_add le_rfl (mul_le_mul (χ.norm_le_one p) hpow (norm_nonneg _) zero_le_one)
      _ = 2 := by norm_num
  have hprodBound : ‖∏ p ∈ m.primeFactors, f p‖ ≤ (2 : ℝ) ^ m.primeFactors.card := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _p ∈ m.primeFactors, (2 : ℝ) :=
        prod_le_prod₀ (fun _ _ => norm_nonneg _) hfactor
      _ = _ := prod_const _
  rw [DirichletCharacter.LFunction_changeLevel (Nat.dvd_mul_right q m) χ (Or.inl hχ),
    show (∏ p ∈ (q * m).primeFactors, (1 - χ p * (p : ℂ) ^ (-(1 : ℂ)))) =
      ∏ p ∈ m.primeFactors, f p from hprod, norm_mul]
  exact (mul_le_mul_of_nonneg_left hprodBound (norm_nonneg _)).trans_eq (mul_comm _ _)

/-- One pair of universal Estermann constants controls both actual
character products used in the ineffective Siegel argument. -/
theorem exists_siegel_character_estermann_bounds :
    ∃ C η : ℝ, 1 ≤ C ∧ 0 < η ∧ η ≤ 1 / 20 ∧
      (∀ q : ℕ, ∀ (_hq : NeZero q),
        letI : NeZero q := _hq
        ∀ χ : DirichletCharacter ℂ q,
          (∀ r : ZMod q, (χ r).im = 0) → χ ≠ 1 →
          ∀ σ : ℝ, 1 - η ≤ σ → σ < 1 →
            0 ≤ DirichletCharacter.LFunction χ (σ : ℂ) →
            (1 / 4 : ℝ) * (1 - σ) *
              (C * (7 * (q : ℝ))) ^ (-3 * (1 - σ)) ≤
                (DirichletCharacter.LFunction χ 1).re) ∧
      (∀ q : ℕ, ∀ (_hq : NeZero q),
        letI : NeZero q := _hq
        ∀ χ ψ : DirichletCharacter ℂ q,
          (∀ r : ZMod q, (χ r).im = 0) →
          (∀ r : ZMod q, (ψ r).im = 0) →
          χ ≠ 1 → ψ ≠ 1 → χ * ψ ≠ 1 →
          ∀ σ : ℝ, 1 - η ≤ σ → σ < 1 →
            DirichletCharacter.LFunction ψ (σ : ℂ) = 0 →
            (1 / 4 : ℝ) * (1 - σ) *
              (C * (343 * (q : ℝ) ^ 3)) ^ (-3 * (1 - σ)) ≤
                (DirichletCharacter.LFunction χ 1).re * (2 + Real.log q) ^ 2) := by
  obtain ⟨C, η, hC, hη, hη20, hEstermann⟩ := exists_estermann_constants
  refine ⟨C, η, hC, hη, hη20, ?_, ?_⟩
  · intro q hq
    let : NeZero q := hq
    intro χ hχ hne σ hσ hσ' hvalue
    apply hEstermann (DirichletCharacter.LFunction χ) χ.zetaMul (7 * (q : ℝ)) σ
    · have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
      linarith
    · exact (DirichletCharacter.differentiable_LFunction hne).diffContOnCl
    · intro s hs
      exact siegel_LFunction_norm_le_estermann_disk χ hne hs
    · exact siegel_zetaMul_coefficients_nonneg χ hχ
    · exact siegel_zetaMul_one χ
    · intro s hs
      exact χ.LSeriesSummable_zetaMul hs
    · intro s hs
      exact (siegel_zetaMul_LSeries_eq χ hs).symm
    · exact hσ
    · exact hσ'
    · exact hvalue
  · intro q hq
    let : NeZero q := hq
    intro χ ψ hχ hψ hχne hψne hprodne σ hσ hσ' hzero
    let f : ℂ → ℂ := fun s => DirichletCharacter.LFunction χ s *
      DirichletCharacter.LFunction ψ s * DirichletCharacter.LFunction (χ * ψ) s
    have hprodreal (r : ZMod q) : ((χ * ψ) r).im = 0 := by
      simp [MulChar.mul_apply, Complex.mul_im, hχ, hψ]
    have hbound (s : ℂ) (hs : s ∈ Metric.closedBall (2 : ℂ) (3 / 2)) :
        ‖f s‖ ≤ 343 * (q : ℝ) ^ 3 := by
      dsimp only [f]
      rw [norm_mul, norm_mul]
      calc
        _ ≤ (7 * (q : ℝ)) * (7 * (q : ℝ)) * (7 * (q : ℝ)) := by
          gcongr
          · exact siegel_LFunction_norm_le_estermann_disk χ hχne hs
          · exact siegel_LFunction_norm_le_estermann_disk ψ hψne hs
          · exact siegel_LFunction_norm_le_estermann_disk (χ * ψ) hprodne hs
        _ = _ := by ring
    have hmain := hEstermann f (siegelRealCharacterProductCoefficients χ ψ)
      (343 * (q : ℝ) ^ 3) σ
      (by have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
          nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hq1 3])
      (((DirichletCharacter.differentiable_LFunction hχne).mul
        (DirichletCharacter.differentiable_LFunction hψne)).mul
        (DirichletCharacter.differentiable_LFunction hprodne)).diffContOnCl
      hbound (siegelRealCharacterProductCoefficients_nonneg χ ψ hχ hψ)
      (siegelRealCharacterProductCoefficients_one χ ψ)
      (fun s hs => siegelRealCharacterProductCoefficients_LSeriesSummable χ ψ hs)
      (fun s hs => by
        rw [siegelRealCharacterProductCoefficients_LSeries_eq χ ψ hs]
        dsimp only [f]
        ring)
      hσ hσ'
      (by dsimp only [f]; rw [hzero, mul_zero, zero_mul])
    apply hmain.trans
    have hχpos := Complex.pos_iff.mp
      (siegel_realCharacter_LFunction_pos_of_one_le χ hχ hχne (x := 1) le_rfl)
    have hψpos := Complex.pos_iff.mp
      (siegel_realCharacter_LFunction_pos_of_one_le ψ hψ hψne (x := 1) le_rfl)
    have hprodpos := Complex.pos_iff.mp
      (siegel_realCharacter_LFunction_pos_of_one_le (χ * ψ) hprodreal hprodne (x := 1) le_rfl)
    simp only [Complex.ofReal_one] at hχpos hψpos hprodpos
    have hψbound : (DirichletCharacter.LFunction ψ 1).re ≤ 2 + Real.log q :=
      (Complex.re_le_norm _).trans (siegel_LFunction_one_norm_le ψ hψne)
    have hprodbound : (DirichletCharacter.LFunction (χ * ψ) 1).re ≤ 2 + Real.log q :=
      (Complex.re_le_norm _).trans (siegel_LFunction_one_norm_le (χ * ψ) hprodne)
    dsimp only [f]
    simp only [Complex.mul_re, ← hχpos.2, ← hψpos.2, Complex.mul_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    have hA : 0 ≤ 2 + Real.log q := by linarith [Real.log_natCast_nonneg q]
    calc
      _ ≤ (DirichletCharacter.LFunction χ 1).re *
          (2 + Real.log q) * (2 + Real.log q) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hψbound hχpos.1.le)
          hprodbound hprodpos.1.le (mul_nonneg hχpos.1.le hA)
      _ = _ := by ring

#print axioms exists_siegel_character_estermann_bounds
#print axioms siegel_realCharacter_LFunction_nonneg_of_zeroFree_interval
#print axioms exists_siegel_LFunction_one_norm_lower_for_modulus
#print axioms siegel_LFunction_changeLevel_mul_one_norm_le

end SystolicGrowth.CookMagyarCircle
