module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

open Filter

namespace SystolicGrowth
namespace CookMagyarCircle

/-! # A polylogarithmic denominator cutoff

The exponent is left as a parameter so the arithmetic, minor-arc, and
singular-series estimates can later impose their combined lower bound on it.
-/

/-- The `A`th power of the integer part of `log (N+2)`. -/
noncomputable def logarithmicDenominatorCutoff (A N : ℕ) : ℕ :=
  Nat.floor (Real.log (N + 2 : ℝ)) ^ A

/-- The natural floor of a real variable tends to infinity with that
variable. This lets fixed constants be absorbed by one spare integer power of
the floor in logarithmic parameter estimates. -/
theorem tendsto_natFloor_real_atTop :
    Tendsto (fun x : ℝ => (Nat.floor x : ℝ)) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b + 1 : ℝ)] with x hx
  have hfloor : x - 1 < (Nat.floor x : ℝ) := by
    have h := Nat.lt_floor_add_one x
    linarith
  linarith

/-- A fixed multiplicative constant times a natural power of `x` is
eventually bounded by the next power of `floor x`. The spare power absorbs
both the floor-rounding factor and the fixed constant. -/
theorem eventually_const_mul_pow_le_natFloor_pow_succ
    (C : ℝ) (hC : 0 ≤ C) (m : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      C * x ^ m ≤ (Nat.floor x : ℝ) ^ (m + 1) := by
  filter_upwards
    [eventually_ge_atTop (2 : ℝ),
      tendsto_natFloor_real_atTop.eventually_ge_atTop
        (max 1 (C * (2 : ℝ) ^ m))] with x hx hfloor
  let b : ℝ := (Nat.floor x : ℝ)
  have hx0 : 0 ≤ x := by linarith
  have hb1 : 1 ≤ b := by
    dsimp [b]
    exact le_trans (le_max_left _ _) hfloor
  have hconst : C * (2 : ℝ) ^ m ≤ b := by
    dsimp [b]
    exact le_trans (le_max_right _ _) hfloor
  have hfloor_lt : x < b + 1 := by
    dsimp [b]
    exact Nat.lt_floor_add_one x
  have hx_le : x ≤ 2 * b := by linarith
  have hpow : x ^ m ≤ (2 * b) ^ m :=
    pow_le_pow_left₀ hx0 hx_le m
  calc
    C * x ^ m ≤ C * (2 * b) ^ m :=
      mul_le_mul_of_nonneg_left hpow hC
    _ = (C * (2 : ℝ) ^ m) * b ^ m := by rw [mul_pow]; ring
    _ ≤ b * b ^ m :=
      mul_le_mul_of_nonneg_right hconst (pow_nonneg (by positivity) m)
    _ = b ^ (m + 1) := by rw [pow_succ]; ring

/-- Flooring a nonnegative real base can only decrease its natural powers. -/
theorem natFloor_pow_le_of_nonneg (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    (Nat.floor x : ℝ) ^ m ≤ x ^ m := by
  have hfloor : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx
  have hfloor0 : 0 ≤ (Nat.floor x : ℝ) := by positivity
  exact pow_le_pow_left₀ hfloor0 hfloor m

private theorem tendsto_natFloor_log_succ_succ :
    Tendsto (fun N : ℕ => Nat.floor (Real.log (N + 2 : ℝ))) atTop atTop := by
  have harg : Tendsto (fun N : ℕ => (N + 2 : ℝ)) atTop atTop := by
    convert tendsto_atTop_add_const_right _ (2 : ℝ)
      tendsto_natCast_atTop_atTop using 1
  have hlog : Tendsto (fun N : ℕ => Real.log (N + 2 : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp harg
  apply Filter.tendsto_atTop.2
  intro b
  have hev : ∀ᶠ N : ℕ in atTop,
      (b : ℝ) ≤ Real.log (N + 2 : ℝ) :=
    hlog.eventually (eventually_ge_atTop (b : ℝ))
  filter_upwards [hev] with N hN
  exact Nat.le_floor hN

/-- Every positive integral power of this logarithmic cutoff tends to
infinity. -/
theorem tendsto_logarithmicDenominatorCutoff
    (A : ℕ) (hA : 0 < A) :
    Tendsto (fun N : ℕ => logarithmicDenominatorCutoff A N) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  have hbase := tendsto_natFloor_log_succ_succ.eventually_ge_atTop (max b 1)
  filter_upwards [hbase] with N hN
  have hb : b ≤ Nat.floor (Real.log (N + 2 : ℝ)) :=
    le_trans (Nat.le_max_left _ _) hN
  have hbaseOne : 1 ≤ Nat.floor (Real.log (N + 2 : ℝ)) :=
    le_trans (Nat.le_max_right _ _) hN
  exact hb.trans (Nat.le_pow (by omega))

/-- The natural cutoff is bounded by the corresponding real logarithmic
power. This is the polylogarithmic upper envelope used in scale estimates. -/
theorem logarithmicDenominatorCutoff_le_log_pow
    (A N : ℕ) :
    (logarithmicDenominatorCutoff A N : ℝ) ≤
      Real.log (N + 2 : ℝ) ^ A := by
  have harg : (1 : ℝ) ≤ (N : ℝ) + 2 := by
    exact_mod_cast (show 1 ≤ N + 2 by omega)
  have hlog : 0 ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg harg
  have hfloor :
      (Nat.floor (Real.log (N + 2 : ℝ)) : ℝ) ≤ Real.log (N + 2 : ℝ) :=
    Nat.floor_le hlog
  have hfloor_nonneg :
      0 ≤ (Nat.floor (Real.log (N + 2 : ℝ)) : ℝ) := by positivity
  have hpow := pow_le_pow_left₀ hfloor_nonneg hfloor A
  simpa [logarithmicDenominatorCutoff] using hpow

/-- Eventually, a cutoff with exponent `A` lies below the `K`th real log
power whenever `A ≤ K`. Unlike the exact `A`th-power estimate above, this
version allows increasing the exponent, which is needed to match Hua's
source cutoff parameter. -/
theorem eventually_logarithmicDenominatorCutoff_le_log_pow
    (A K : ℕ) (hAK : A ≤ K) :
    ∀ᶠ N : ℕ in atTop,
      (logarithmicDenominatorCutoff A N : ℝ) ≤
        Real.log ((N : ℝ) + 2) ^ K := by
  have hlog : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 2)) atTop atTop := by
    have harg : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop := by
      convert tendsto_atTop_add_const_right _ (2 : ℝ)
        tendsto_natCast_atTop_atTop using 1
    exact Real.tendsto_log_atTop.comp harg
  filter_upwards [hlog.eventually_ge_atTop (1 : ℝ)] with N hlogN
  have hcut := logarithmicDenominatorCutoff_le_log_pow A N
  have hpow : Real.log ((N : ℝ) + 2) ^ A ≤
      Real.log ((N : ℝ) + 2) ^ K :=
    pow_le_pow_right₀ hlogN hAK
  exact hcut.trans hpow

/-- If the cutoff exponent is at least twice `C`, then the integer cutoff
eventually dominates the `C`th real power of the logarithm. This lower
comparison is the denominator-floor adapter used by the prime minor-arc
argument. -/
theorem eventually_log_pow_le_logarithmicDenominatorCutoff
    (A C : ℕ) (hCA : C < A) :
    ∀ᶠ N : ℕ in atTop,
      Real.log ((N : ℝ) + 2) ^ C ≤
        (logarithmicDenominatorCutoff A N : ℝ) := by
  have hlog : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 2)) atTop atTop := by
    have harg : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop := by
      convert tendsto_atTop_add_const_right _ (2 : ℝ)
        tendsto_natCast_atTop_atTop using 1
    exact Real.tendsto_log_atTop.comp harg
  filter_upwards
    [hlog.eventually_ge_atTop (max 4 ((2 : ℝ) ^ A))] with N hN
  let y : ℝ := Real.log ((N : ℝ) + 2)
  let b : ℝ := (Nat.floor y : ℝ)
  have hy : 4 ≤ y := by
    dsimp [y]
    exact (le_max_left _ _).trans hN
  have hy2pow : (2 : ℝ) ^ A ≤ y := by
    dsimp [y]
    exact (le_max_right _ _).trans hN
  have hy0 : 0 ≤ y := by linarith
  have hb : y / 2 ≤ b := by
    have hfloor := Nat.lt_floor_add_one y
    dsimp [b]
    linarith
  have hAminus : 1 ≤ A - C := by omega
  have hyPow : y ^ 1 ≤ y ^ (A - C) :=
    pow_le_pow_right₀ (by linarith) hAminus
  have htwoPow : (2 : ℝ) ^ A ≤ y ^ (A - C) := by
    exact hy2pow.trans (by simpa only [pow_one] using hyPow)
  have hproduct : y ^ C * (2 : ℝ) ^ A ≤ y ^ A := by
    calc
      y ^ C * (2 : ℝ) ^ A ≤ y ^ C * y ^ (A - C) :=
        mul_le_mul_of_nonneg_left htwoPow (pow_nonneg hy0 C)
      _ = y ^ A := by
        rw [← pow_add]
        congr 1
        omega
  have hyPower : y ^ C ≤ (y / 2) ^ A := by
    have hdiv : y ^ C ≤ y ^ A / (2 : ℝ) ^ A :=
      (le_div_iff₀ (by positivity)).2 (by nlinarith [hproduct])
    calc
      y ^ C ≤ y ^ A / (2 : ℝ) ^ A := hdiv
      _ = (y / 2) ^ A := by rw [div_pow]
  have hpow : (y / 2) ^ A ≤ b ^ A :=
    pow_le_pow_left₀ (by positivity) hb A
  have htotal : y ^ C ≤ b ^ A := hyPower.trans hpow
  simpa [y, b, logarithmicDenominatorCutoff] using htotal

/-- With one extra logarithmic power in the cutoff, it eventually dominates
twice the requested power. This slack is useful when transferring a Dirichlet
height `ceil(N^3/Q)` into the source theorem's upper denominator range. -/
theorem eventually_two_mul_log_pow_le_logarithmicDenominatorCutoff
    (A C : ℕ) (hCA : C + 1 < A) :
    ∀ᶠ N : ℕ in atTop,
      2 * Real.log ((N : ℝ) + 2) ^ C ≤
        (logarithmicDenominatorCutoff A N : ℝ) := by
  have hlog : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 2)) atTop atTop := by
    have harg : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop := by
      convert tendsto_atTop_add_const_right _ (2 : ℝ)
        tendsto_natCast_atTop_atTop using 1
    exact Real.tendsto_log_atTop.comp harg
  filter_upwards
    [eventually_log_pow_le_logarithmicDenominatorCutoff A (C + 1) (by omega),
      hlog.eventually_ge_atTop (2 : ℝ)] with N hpower hlogN
  have hNlog : (2 : ℝ) ≤ Real.log ((N : ℝ) + 2) := hlogN
  have hmul : 2 * Real.log ((N : ℝ) + 2) ^ C ≤
      Real.log ((N : ℝ) + 2) ^ (C + 1) := by
    rw [pow_succ]
    nlinarith [mul_nonneg (by positivity :
      0 ≤ Real.log ((N : ℝ) + 2) ^ C)
      (sub_nonneg.mpr hNlog)]
  exact hmul.trans hpower

/-- With one spare logarithmic exponent, the floor-log cutoff eventually
dominates three times the requested power. The factor three is the loss in
the Dirichlet height bound `q ≤ 3N^3/cutoff`; this form removes that loss when
matching Hua's upper denominator range. -/
theorem eventually_three_mul_log_pow_le_logarithmicDenominatorCutoff
    (A C : ℕ) (hCA : C + 1 < A) :
    ∀ᶠ N : ℕ in atTop,
      3 * Real.log ((N : ℝ) + 2) ^ C ≤
        (logarithmicDenominatorCutoff A N : ℝ) := by
  have hlog : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 2)) atTop atTop := by
    have harg : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop := by
      convert tendsto_atTop_add_const_right _ (2 : ℝ)
        tendsto_natCast_atTop_atTop using 1
    exact Real.tendsto_log_atTop.comp harg
  filter_upwards
    [hlog.eventually_ge_atTop (3 : ℝ),
      eventually_log_pow_le_logarithmicDenominatorCutoff A (C + 1)
        (by omega)] with N hlogN hpower
  have hmul : 3 * Real.log ((N : ℝ) + 2) ^ C ≤
      Real.log ((N : ℝ) + 2) ^ (C + 1) := by
    rw [pow_succ]
    nlinarith [mul_nonneg (by positivity :
      0 ≤ Real.log ((N : ℝ) + 2) ^ C)
      (by linarith : 0 ≤ Real.log ((N : ℝ) + 2) - 3)]
  exact hmul.trans hpower

/-- Every fixed power of the logarithmic cutoff is eventually at most the
ambient scale `N+2`. This coarse power-saving envelope is enough to establish
the basic disjointness range for cubic major arcs. -/
theorem eventually_logarithmicDenominatorCutoff_pow_le_add_two
    (A K : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      (logarithmicDenominatorCutoff A N : ℝ) ^ K ≤ (N : ℝ) + 2 := by
  let R : ℕ := A * K
  have harg : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop := by
    convert tendsto_atTop_add_const_right _ (2 : ℝ)
      tendsto_natCast_atTop_atTop using 1
  have hloglittleO : (fun N : ℕ => Real.log ((N : ℝ) + 2) ^ R) =o[atTop]
      (fun N : ℕ => (N : ℝ) + 2) := by
    simpa only [Function.comp_def, Real.rpow_one, Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ)) (R : ℝ)
        (by norm_num)).comp_tendsto harg
  have hevent := hloglittleO.bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hevent] with N hN
  have hargpos : 0 ≤ (N : ℝ) + 2 := by positivity
  have hlognonneg : 0 ≤ Real.log ((N : ℝ) + 2) :=
    Real.log_nonneg (by linarith)
  have hpowernonneg : 0 ≤ Real.log ((N : ℝ) + 2) ^ R := by positivity
  have hlogbound : Real.log ((N : ℝ) + 2) ^ R ≤ (N : ℝ) + 2 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hpowernonneg,
      abs_of_nonneg hargpos, one_mul] using hN
  have hcut := logarithmicDenominatorCutoff_le_log_pow A N
  have hcutnonneg :
      0 ≤ (logarithmicDenominatorCutoff A N : ℝ) := by positivity
  calc
    (logarithmicDenominatorCutoff A N : ℝ) ^ K ≤
        (Real.log ((N : ℝ) + 2) ^ A) ^ K :=
      pow_le_pow_left₀ hcutnonneg hcut K
    _ = Real.log ((N : ℝ) + 2) ^ R := by
      rw [← pow_mul]
    _ ≤ (N : ℝ) + 2 := hlogbound

/-- The cubic logarithmic cutoff is eventually small enough for the standard
`2 Q^3 ≤ N^3` major-arc separation condition. -/
theorem eventually_two_mul_logarithmicCutoff_cube_le
    (A : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      2 * (logarithmicDenominatorCutoff A N : ℝ) ^ 3 ≤ (N : ℝ) ^ 3 := by
  filter_upwards
    [eventually_logarithmicDenominatorCutoff_pow_le_add_two A 3,
      eventually_ge_atTop (2 : ℕ)] with N hQ hN
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hpoly : 0 ≤ ((N : ℝ) - 2) *
      ((N : ℝ) ^ 2 + 2 * N + 2) :=
    mul_nonneg (by linarith) (by positivity)
  have hscale : (N : ℝ) + 2 ≤ (N : ℝ) ^ 3 / 2 := by
    nlinarith
  have hQhalf : (logarithmicDenominatorCutoff A N : ℝ) ^ 3 ≤
      (N : ℝ) ^ 3 / 2 := hQ.trans hscale
  nlinarith

/-- Every fixed power of the logarithmic cutoff is eventually dominated by
any positive power of the ambient scale. -/
theorem eventually_logarithmicDenominatorCutoff_pow_le_rpow
    (A K : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      (logarithmicDenominatorCutoff A N : ℝ) ^ K ≤ (N : ℝ) ^ δ := by
  let R : ℕ := A * K
  let s : ℝ := δ / 2
  have hs : 0 < s := by dsimp [s]; linarith
  have harg : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop := by
    convert tendsto_atTop_add_const_right _ (2 : ℝ)
      tendsto_natCast_atTop_atTop using 1
  have hlittleO : (fun N : ℕ => Real.log ((N : ℝ) + 2) ^ R) =o[atTop]
      (fun N : ℕ => ((N : ℝ) + 2) ^ s) := by
    simpa only [Function.comp_def, Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (s := s) (R : ℝ) hs).comp_tendsto harg
  have hbound := hlittleO.bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hbound, eventually_ge_atTop (2 : ℕ)] with N hbound hN
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hargpos : 0 ≤ (N : ℝ) + 2 := by positivity
  have hlognonneg : 0 ≤ Real.log ((N : ℝ) + 2) :=
    Real.log_nonneg (by linarith)
  have hlogpow_nonneg : 0 ≤ Real.log ((N : ℝ) + 2) ^ R := by positivity
  have hpowerbound : Real.log ((N : ℝ) + 2) ^ R ≤
      ((N : ℝ) + 2) ^ s := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlogpow_nonneg,
      Real.norm_eq_abs, abs_of_nonneg (by positivity :
        0 ≤ ((N : ℝ) + 2) ^ s), one_mul] using hbound
  have hcut := logarithmicDenominatorCutoff_le_log_pow A N
  have hcutnonneg :
      0 ≤ (logarithmicDenominatorCutoff A N : ℝ) := by positivity
  have hcutpow : (logarithmicDenominatorCutoff A N : ℝ) ^ K ≤
      Real.log ((N : ℝ) + 2) ^ R := by
    calc
      _ ≤ (Real.log ((N : ℝ) + 2) ^ A) ^ K :=
        pow_le_pow_left₀ hcutnonneg hcut K
      _ = Real.log ((N : ℝ) + 2) ^ R := by
        rw [← pow_mul]
  have hNplus : (N : ℝ) + 2 ≤ (N : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hNreal)
      (add_nonneg (by positivity : (0 : ℝ) ≤ N) (by norm_num : (0 : ℝ) ≤ 1))]
  have hscale : ((N : ℝ) + 2) ^ s ≤ (N : ℝ) ^ δ := by
    calc
      ((N : ℝ) + 2) ^ s ≤ ((N : ℝ) ^ 2) ^ s :=
        Real.rpow_le_rpow (by positivity) hNplus hs.le
      _ = (N : ℝ) ^ δ := by
        rw [← Real.rpow_natCast_mul (by positivity) 2 s]
        have hsδ : (2 : ℝ) * s = δ := by dsimp [s]; ring
        norm_num [hsδ]
  exact hcutpow.trans (hpowerbound.trans hscale)

end CookMagyarCircle
end SystolicGrowth

#print axioms SystolicGrowth.CookMagyarCircle.tendsto_logarithmicDenominatorCutoff
#print axioms SystolicGrowth.CookMagyarCircle.tendsto_natFloor_real_atTop
#print axioms SystolicGrowth.CookMagyarCircle.eventually_const_mul_pow_le_natFloor_pow_succ
#print axioms SystolicGrowth.CookMagyarCircle.natFloor_pow_le_of_nonneg
#print axioms SystolicGrowth.CookMagyarCircle.logarithmicDenominatorCutoff_le_log_pow
#print axioms SystolicGrowth.CookMagyarCircle.eventually_logarithmicDenominatorCutoff_le_log_pow
#print axioms SystolicGrowth.CookMagyarCircle.eventually_logarithmicDenominatorCutoff_pow_le_add_two
#print axioms SystolicGrowth.CookMagyarCircle.eventually_two_mul_logarithmicCutoff_cube_le
#print axioms SystolicGrowth.CookMagyarCircle.eventually_logarithmicDenominatorCutoff_pow_le_rpow
#print axioms SystolicGrowth.CookMagyarCircle.eventually_logarithmicDenominatorCutoff_pow_le_rpow
#print axioms SystolicGrowth.CookMagyarCircle.eventually_log_pow_le_logarithmicDenominatorCutoff
#print axioms SystolicGrowth.CookMagyarCircle.eventually_two_mul_log_pow_le_logarithmicDenominatorCutoff
#print axioms SystolicGrowth.CookMagyarCircle.eventually_three_mul_log_pow_le_logarithmicDenominatorCutoff
