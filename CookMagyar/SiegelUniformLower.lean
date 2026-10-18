module

public import CookMagyar.SiegelLowerBound
public import CookMagyar.SiegelRealZeroAdapter

@[expose] public section

/-!
# Uniform ineffective lower bound for real primitive characters

The two cases of Siegel's argument use the actual character applications
of Estermann's lemma. A single fixed real zero supplies the ineffective
constant in the second case; all modulus powers and logarithmic losses are
absorbed uniformly for every positive modulus.
-/

open scoped ComplexOrder

namespace SystolicGrowth.CookMagyarCircle

private theorem siegel_single_power_lower {q : ℕ} [NeZero q]
    {C d ε : ℝ} (hC : 0 < C) (hd : 0 < d) (hexp : 3 * d ≤ ε) :
    ((1 / 4 : ℝ) * d * (C * 7) ^ (-3 * d)) * (q : ℝ) ^ (-ε) ≤
      (1 / 4 : ℝ) * d * (C * (7 * (q : ℝ))) ^ (-3 * d) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hfactor : C * (7 * (q : ℝ)) = (C * 7) * q := by ring
  rw [hfactor, Real.mul_rpow (x := C * 7) (y := (q : ℝ)) (by positivity) (by positivity)]
  have hpow := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : -ε ≤ -3 * d)
  calc
    _ ≤ ((1 / 4 : ℝ) * d * (C * 7) ^ (-3 * d)) * (q : ℝ) ^ (-3 * d) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

private theorem siegel_product_power_lower {q m : ℕ} [NeZero q] [NeZero m]
    {C d ε : ℝ} (hC : 0 < C) (hd : 0 < d) (hexp : 9 * d ≤ ε / 2) :
    ((1 / 4 : ℝ) * d * (C * (343 * (m : ℝ) ^ 3)) ^ (-3 * d)) *
        (q : ℝ) ^ (-(ε / 2)) ≤
      (1 / 4 : ℝ) * d * (C * (343 * ((q * m : ℕ) : ℝ) ^ 3)) ^ (-3 * d) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hfactor : C * (343 * ((q * m : ℕ) : ℝ) ^ 3) =
      (C * (343 * (m : ℝ) ^ 3)) * (q : ℝ) ^ 3 := by
    push_cast
    ring
  have hqpow : ((q : ℝ) ^ 3) ^ (-3 * d) = (q : ℝ) ^ (-9 * d) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ q)]
    congr 1
    ring
  rw [hfactor, Real.mul_rpow (x := C * (343 * (m : ℝ) ^ 3))
    (y := (q : ℝ) ^ 3) (by positivity) (by positivity), hqpow]
  have hpow := Real.rpow_le_rpow_of_exponent_le hq1
    (by linarith : -(ε / 2) ≤ -9 * d)
  calc
    _ ≤ ((1 / 4 : ℝ) * d * (C * (343 * (m : ℝ) ^ 3)) ^ (-3 * d)) *
        (q : ℝ) ^ (-9 * d) := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

private theorem siegel_fixed_added_logSquare {q m : ℕ} [NeZero q] [NeZero m]
    {ε : ℝ} (hε : 0 < ε) :
    (2 + Real.log (q * m : ℕ)) ^ 2 ≤
      (4 * (1 + 4 / ε) ^ 2 * (m : ℝ) ^ (ε / 2)) * (q : ℝ) ^ (ε / 2) := by
  have hlog : 0 ≤ Real.log (q * m : ℕ) := Real.log_natCast_nonneg _
  have hbase : 2 + Real.log (q * m : ℕ) ≤ 2 * (1 + Real.log (q * m : ℕ)) :=
    by linarith
  have hbound := siegel_logSquare_le_modulus_rpow (q := q * m)
    (by positivity : 0 < ε / 2)
  have hquot : 2 / (ε / 2) = 4 / ε := by ring
  rw [hquot] at hbound
  calc
    _ ≤ (2 * (1 + Real.log (q * m : ℕ))) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hbase 2
    _ = 4 * (1 + Real.log (q * m : ℕ)) ^ 2 := by ring
    _ ≤ 4 * ((1 + 4 / ε) ^ 2 * ((q * m : ℕ) : ℝ) ^ (ε / 2)) := by
      gcongr
    _ = _ := by
      rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
      ring

private theorem siegel_absorb_product_loss {q : ℕ} [NeZero q]
    {a D K N ε : ℝ} (hD : 0 < D) (hK : 0 < K)
    (h : a * (q : ℝ) ^ (-(ε / 2)) ≤ D * N * K * (q : ℝ) ^ (ε / 2)) :
    (a / (D * K)) * (q : ℝ) ^ (-ε) ≤ N := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hweight : 0 < (D * K) * (q : ℝ) ^ (ε / 2) := by positivity
  apply le_of_mul_le_mul_right _ hweight
  calc
    _ = a * ((q : ℝ) ^ (-ε) * (q : ℝ) ^ (ε / 2)) := by
      calc
        _ = ((a / (D * K)) * (D * K)) *
            ((q : ℝ) ^ (-ε) * (q : ℝ) ^ (ε / 2)) := by ring
        _ = _ := by rw [div_mul_cancel₀ _ (mul_pos hD hK).ne']
    _ = a * (q : ℝ) ^ (-(ε / 2)) := by
      rw [← Real.rpow_add hq, show -ε + ε / 2 = -(ε / 2) by ring]
    _ ≤ D * N * K * (q : ℝ) ^ (ε / 2) := h
    _ = _ := by ring

/-- Siegel's ineffective lower bound for the actual value at `1`, uniform
over every positive modulus and primitive nonprincipal real character.
The positive constant is constructed by the two-case argument, not
supplied as a uniform analytic premise. -/
theorem exists_siegel_uniform_LFunction_one_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, ∀ (_hq : NeZero q),
      letI : NeZero q := _hq
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
        (∀ r : ZMod q, (χ r).im = 0) →
        c * (q : ℝ) ^ (-ε) ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
  classical
  obtain ⟨C, η, hC, hη, hη20, hsingle, hfour⟩ :=
    exists_siegel_character_estermann_bounds
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let d : ℝ := min η (ε / 18)
  have hd : 0 < d := lt_min hη (by positivity)
  have hdη : d ≤ η := min_le_left _ _
  have hdε : d ≤ ε / 18 := min_le_right _ _
  have hd20 : d ≤ 1 / 20 := hdη.trans hη20
  by_cases hz : ∃ m : ℕ, ∃ (_hm : NeZero m),
      letI : NeZero m := _hm
      ∃ ψ : DirichletCharacter ℂ m, ψ.IsPrimitive ∧ ψ ≠ 1 ∧
        (∀ r : ZMod m, (ψ r).im = 0) ∧
        ∃ σ : ℝ, 1 - d ≤ σ ∧ σ < 1 ∧
          DirichletCharacter.LFunction ψ (σ : ℂ) = 0
  · obtain ⟨m, hm, ψ, hψprim, hψne, hψreal, σ, hσlo, hσhi, hψzero⟩ := hz
    letI : NeZero m := hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
    have hδ : 0 < 1 - σ := by linarith
    have hδexp : 9 * (1 - σ) ≤ ε / 2 := by linarith
    let a : ℝ := (1 / 4 : ℝ) * (1 - σ) *
      (C * (343 * (m : ℝ) ^ 3)) ^ (-3 * (1 - σ))
    let D : ℝ := (2 : ℝ) ^ m.primeFactors.card
    let K : ℝ := 4 * (1 + 4 / ε) ^ 2 * (m : ℝ) ^ (ε / 2)
    have ha : 0 < a := by dsimp [a]; positivity
    have hD : 0 < D := by dsimp [D]; positivity
    have hK : 0 < K := by dsimp [K]; positivity
    obtain ⟨c₀, hc₀, hfinite⟩ := exists_siegel_LFunction_one_norm_lower_for_modulus m
    refine ⟨min c₀ (a / (D * K)), lt_min hc₀ (by positivity), ?_⟩
    intro q hq
    letI : NeZero q := hq
    intro χ hχprim hχne hχreal
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
    by_cases hqm : q = m
    · subst q
      have hpow : (m : ℝ) ^ (-ε) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hq1 (by linarith)
      calc
        _ ≤ c₀ * (m : ℝ) ^ (-ε) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
        _ ≤ c₀ * 1 := mul_le_mul_of_nonneg_left hpow hc₀.le
        _ = c₀ := mul_one _
        _ ≤ _ := hfinite χ hχne
    · haveI : NeZero (q * m) := ⟨mul_ne_zero (NeZero.ne q) (NeZero.ne m)⟩
      let χQ := DirichletCharacter.changeLevel (Nat.dvd_mul_right q m) χ
      let ψQ := DirichletCharacter.changeLevel (Nat.dvd_mul_left m q) ψ
      have hχQreal : ∀ r : ZMod (q * m), (χQ r).im = 0 :=
        siegel_realCharacter_changeLevel χ _ hχreal
      have hψQreal : ∀ r : ZMod (q * m), (ψQ r).im = 0 :=
        siegel_realCharacter_changeLevel ψ _ hψreal
      have hχQne : χQ ≠ 1 :=
        hχne ∘ (DirichletCharacter.changeLevel_eq_one_iff _).mp
      have hψQne : ψQ ≠ 1 :=
        hψne ∘ (DirichletCharacter.changeLevel_eq_one_iff _).mp
      have hconductorne : χ.conductor ≠ ψ.conductor := by
        change χ.conductor = q at hχprim
        change ψ.conductor = m at hψprim
        rw [hχprim, hψprim]
        exact hqm
      have hprodne : χQ * ψQ ≠ 1 :=
        siegel_changeLevel_product_ne_one_of_conductor_ne χ ψ _ _ hχreal hconductorne
      have hψQzero : DirichletCharacter.LFunction ψQ (σ : ℂ) = 0 := by
        dsimp [ψQ]
        rw [DirichletCharacter.LFunction_changeLevel _ ψ (Or.inl hψne), hψzero, zero_mul]
      have hmain := hfour (q * m) inferInstance χQ ψQ hχQreal hψQreal
        hχQne hψQne hprodne σ (by linarith) hσhi hψQzero
      have hlift : (DirichletCharacter.LFunction χQ 1).re ≤
          D * ‖DirichletCharacter.LFunction χ 1‖ :=
        (Complex.re_le_norm _).trans (siegel_LFunction_changeLevel_mul_one_norm_le χ hχne)
      have hlog : (2 + Real.log (q * m : ℕ)) ^ 2 ≤ K * (q : ℝ) ^ (ε / 2) :=
        siegel_fixed_added_logSquare hε
      have hscalar : a * (q : ℝ) ^ (-(ε / 2)) ≤
          D * ‖DirichletCharacter.LFunction χ 1‖ * K * (q : ℝ) ^ (ε / 2) := by
        calc
          _ ≤ (1 / 4 : ℝ) * (1 - σ) *
              (C * (343 * ((q * m : ℕ) : ℝ) ^ 3)) ^ (-3 * (1 - σ)) :=
            siegel_product_power_lower hCpos hδ hδexp
          _ ≤ (DirichletCharacter.LFunction χQ 1).re *
              (2 + Real.log (q * m : ℕ)) ^ 2 := hmain
          _ ≤ (D * ‖DirichletCharacter.LFunction χ 1‖) *
              (2 + Real.log (q * m : ℕ)) ^ 2 :=
            mul_le_mul_of_nonneg_right hlift (sq_nonneg _)
          _ ≤ (D * ‖DirichletCharacter.LFunction χ 1‖) *
              (K * (q : ℝ) ^ (ε / 2)) :=
            mul_le_mul_of_nonneg_left hlog (mul_nonneg hD.le (norm_nonneg _))
          _ = _ := by ring
      calc
        _ ≤ (a / (D * K)) * (q : ℝ) ^ (-ε) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
        _ ≤ _ := siegel_absorb_product_loss hD hK hscalar
  · let c : ℝ := (1 / 4 : ℝ) * d * (C * 7) ^ (-3 * d)
    have hc : 0 < c := by dsimp [c]; positivity
    refine ⟨c, hc, ?_⟩
    intro q hq
    letI : NeZero q := hq
    intro χ hχprim hχne hχreal
    have hσpos : 0 < 1 - d := by linarith
    have hσhi : 1 - d < 1 := by linarith
    have hzeroFree : ∀ x ∈ Set.Ico (1 - d) 1,
        DirichletCharacter.LFunction χ (x : ℂ) ≠ 0 := by
      intro x hx hzero
      exact hz ⟨q, hq, χ, hχprim, hχne, hχreal, x, hx.1, hx.2, hzero⟩
    have hvalue := siegel_realCharacter_LFunction_nonneg_of_zeroFree_interval
      χ hχreal hχne hσpos hσhi hzeroFree
    have hmain := hsingle q hq χ hχreal hχne (1 - d) (by linarith) hσhi hvalue
    rw [show 1 - (1 - d) = d by ring] at hmain
    calc
      _ ≤ (1 / 4 : ℝ) * d * (C * (7 * (q : ℝ))) ^ (-3 * d) :=
        siegel_single_power_lower hCpos hd (by linarith)
      _ ≤ (DirichletCharacter.LFunction χ 1).re := hmain
      _ ≤ _ := Complex.re_le_norm _

#print axioms exists_siegel_uniform_LFunction_one_lower

end SystolicGrowth.CookMagyarCircle
