module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.AuxiliaryPowerCutoff
public import CookMagyar.OrdinaryWeylPairs
public import CookMagyar.HuaOrthogonality
public import CookMagyar.CubicHighMoment
public import CookMagyar.ArchimedeanFourierBridge
public import CookMagyar.CubicMajorArcHomogeneousModel

@[expose] public section

namespace SystolicGrowth
namespace CookMagyarCircle

open MeasureTheory
open Filter
open scoped ENNReal
open CookMagyarMajorArc CookMagyarArcs CookMagyarFiniteFourier
open CookMagyarReal

/-- The nonnegative integrand whose full-line integral is the absolute cubic
frequency moment needed on the auxiliary major arcs. -/
noncomputable def Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 (tau : ℝ) : ℝ :=
  ‖oneDimensionalCubicIntegral tau‖ ^ 32

private theorem cubicFrequencyNormPow32_integrable :
    Integrable Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 := by
  change Integrable (fun tau : ℝ => ‖oneDimensionalCubicIntegral tau‖ ^ 32)
  have hv : Integrable (cubicFrequencyFactor 32) :=
    cubicFrequencyFactor_integrable (by omega)
  have hn := hv.norm
  change Integrable (fun tau : ℝ => ‖oneDimensionalCubicIntegral tau ^ 32‖) at hn
  simpa [cubicFrequencyFactor, norm_pow] using hn

private theorem cubicFrequencyNormPow32_nonneg (tau : ℝ) :
    0 ≤ Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau := by
  exact pow_nonneg (norm_nonneg _) _

/-- Scaling a finite displacement window by `N³` costs precisely the cubic
Jacobian; its absolute frequency moment is bounded by the full-line one. -/
private theorem integral_cubicFrequencyNormPow32_scaled_le
    (N Q : ℕ) (hN : 0 < N) :
    (∫ beta in Set.Icc (-((Q : ℝ) / (N : ℝ) ^ 3))
        ((Q : ℝ) / (N : ℝ) ^ 3),
        Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 (beta * (N : ℝ) ^ 3)) ≤
      ((N : ℝ) ^ 3)⁻¹ * ∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau := by
  let c : ℝ := (N : ℝ) ^ 3
  let r : ℝ := (Q : ℝ) / c
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hcn : c ≠ 0 := ne_of_gt hcpos
  have hrpos : 0 ≤ r := by dsimp [r]; positivity
  have hlow : -r * c = -(Q : ℝ) := by
    dsimp [r]
    field_simp [hcn]
  have hupp : r * c = (Q : ℝ) := by
    dsimp [r]
    field_simp [hcn]
  let f : ℝ → ℝ := Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32
  have hleft :
      (∫ beta in Set.Icc (-r) r, f (beta * c)) =
        ∫ beta in (-r)..r, f (beta * c) := by
    rw [intervalIntegral.integral_of_le (by linarith [hrpos]),
      ← integral_Icc_eq_integral_Ioc]
  have hright :
      (∫ tau in Set.Icc (-(Q : ℝ)) (Q : ℝ), f tau) =
        ∫ tau in (-(Q : ℝ))..(Q : ℝ), f tau := by
    have hQ : (-(Q : ℝ)) ≤ (Q : ℝ) := by
      have hQnonneg : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
      linarith
    rw [intervalIntegral.integral_of_le hQ,
      ← integral_Icc_eq_integral_Ioc]
  have hwindow :
      (∫ beta in Set.Icc (-r) r, f (beta * c)) =
        c⁻¹ • ∫ tau in Set.Icc (-(Q : ℝ)) (Q : ℝ), f tau := by
    calc
      (∫ beta in Set.Icc (-r) r, f (beta * c)) =
          ∫ beta in (-r)..r, f (beta * c) := hleft
      _ = c⁻¹ • ∫ tau in (-(Q : ℝ))..(Q : ℝ), f tau := by
        rw [intervalIntegral.integral_comp_mul_right f hcn, hlow, hupp]
      _ = c⁻¹ * ∫ tau in Set.Icc (-(Q : ℝ)) (Q : ℝ), f tau := by
        rw [hright]
        simp only [smul_eq_mul]
  have hwindow_le :
      (∫ tau in Set.Icc (-(Q : ℝ)) (Q : ℝ), f tau) ≤
        ∫ tau : ℝ, f tau := by
    exact setIntegral_le_integral cubicFrequencyNormPow32_integrable
      (Filter.Eventually.of_forall cubicFrequencyNormPow32_nonneg)
  have hcInv : 0 ≤ c⁻¹ := inv_nonneg.mpr hcpos.le
  calc
    (∫ beta in Set.Icc (-((Q : ℝ) / (N : ℝ) ^ 3))
        ((Q : ℝ) / (N : ℝ) ^ 3),
        Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 (beta * (N : ℝ) ^ 3)) =
      c⁻¹ * ∫ tau in Set.Icc (-(Q : ℝ)) (Q : ℝ), f tau := by
        simpa [c, r, f] using hwindow
    _ ≤ c⁻¹ * ∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau :=
      mul_le_mul_of_nonneg_left hwindow_le hcInv
    _ = ((N : ℝ) ^ 3)⁻¹ * ∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau := by
      simp [c]

/-- On the auxiliary minor arcs the three terms in the cubic Weyl factor
are bounded uniformly by the reciprocal cubic root. -/
theorem auxiliaryMinorWeylFactor_le
    {N q : ℕ} (hN : 8 ≤ N)
    (hqP : cubicAuxiliaryCutoff N < q)
    (hqBound : (q : ℝ) ≤
      3 * (N : ℝ) ^ 3 / (cubicAuxiliaryCutoff N : ℝ)) :
    1 / (q : ℝ) + 1 / (N : ℝ) + (q : ℝ) / (N : ℝ) ^ 3 ≤
      8 / Real.rpow (N : ℝ) ((3 : ℝ)⁻¹) := by
  let x : ℝ := N
  let p : ℝ := cubicAuxiliaryCutoff N
  let r : ℝ := Real.rpow x ((3 : ℝ)⁻¹)
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hxone : 1 ≤ x := by dsimp [x]; exact_mod_cast (by omega : 1 ≤ N)
  have hppos : 0 < p := by
    dsimp [p]
    exact_mod_cast cubicAuxiliaryCutoff_pos (by omega : 0 < N)
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrootlt : r < p + 1 := by
    dsimp [r, p, x]
    exact cubicAuxiliaryCutoff_lt_succ_realRoot N
  have hqPnat : cubicAuxiliaryCutoff N + 1 ≤ q := Nat.succ_le_of_lt hqP
  have hPq : p + 1 ≤ (q : ℝ) := by
    dsimp [p]
    exact_mod_cast hqPnat
  have hrootq : r < (q : ℝ) := hrootlt.trans_le hPq
  have hrootleN : r ≤ x := by
    dsimp [r]
    calc
      Real.rpow x ((3 : ℝ)⁻¹) ≤ Real.rpow x 1 :=
        Real.rpow_le_rpow_of_exponent_le hxone (by norm_num)
      _ = x := Real.rpow_one x
  have hrootle2p : r ≤ 2 * p := by
    dsimp [r, p, x]
    exact realRoot_le_two_cubicAuxiliaryCutoff hN
  have hterm1 : 1 / (q : ℝ) ≤ 1 / r := by
    exact one_div_le_one_div_of_le hrpos hrootq.le
  have hterm2 : 1 / (N : ℝ) ≤ 1 / r := by
    exact one_div_le_one_div_of_le hrpos hrootleN
  have hterm3 : (q : ℝ) / (N : ℝ) ^ 3 ≤ 6 / r := by
    have hqdiv : (q : ℝ) / x ^ 3 ≤ (3 * x ^ 3 / p) / x ^ 3 :=
      div_le_div_of_nonneg_right (by simpa [x, p] using hqBound) (by positivity)
    have hqdiv' : (q : ℝ) / x ^ 3 ≤ 3 / p := by
      calc
        (q : ℝ) / x ^ 3 ≤ (3 * x ^ 3 / p) / x ^ 3 := hqdiv
        _ = 3 / p := by field_simp [hxpos.ne', hppos.ne']
    have hfrac : 3 / p ≤ 6 / r := by
      apply (div_le_div_iff₀ hppos hrpos).2
      nlinarith
    have hqdiv'' : (q : ℝ) / x ^ 3 ≤ 6 / r := hqdiv'.trans hfrac
    simpa [x] using hqdiv''
  have hsum :
      1 / (q : ℝ) + 1 / (N : ℝ) + (q : ℝ) / (N : ℝ) ^ 3 ≤
        1 / r + 1 / r + 6 / r := by
    exact add_le_add (add_le_add hterm1 hterm2) hterm3
  calc
    1 / (q : ℝ) + 1 / (N : ℝ) + (q : ℝ) / (N : ℝ) ^ 3 ≤
        1 / r + 1 / r + 6 / r := hsum
    _ = 8 / Real.rpow (N : ℝ) ((3 : ℝ)⁻¹) := by
      dsimp [r, x]
      ring

set_option maxHeartbeats 800000 in
/-- The complete all-residue cubic sum is the rational-center ordinary
sum of length `q`. -/
theorem cubicUnweightedExpSum_rationalCenter_eq_allResidue
    (q a : ℕ) [NeZero q] (hq : 0 < q) :
    cubicUnweightedExpSum (rationalCenter a q) (q - 1) =
      allResidueCubicExponentialSum q (a : ZMod q) := by
  classical
  obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  rw [cubicUnweightedExpSum_eq_finSum]
  have hlen : (q' + 1) - 1 + 1 = q' + 1 := by omega
  rw [hlen]
  unfold allResidueCubicExponentialSum
  calc
    (∑ m : Fin (q' + 1), addChar (rationalCenter a (q' + 1)) (primeCubic m.val)) =
        ∑ m : Fin (q' + 1),
          standardAdditiveCharacter
            ((a : ZMod (q' + 1)) * cubicResidue (m.val : ZMod (q' + 1))) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [addChar_rationalCenter, cast_primeCubic_zmod]
    _ = ∑ r : ZMod (q' + 1),
          standardAdditiveCharacter ((a : ZMod (q' + 1)) * cubicResidue r) := by
      have hfin (m : Fin (q' + 1)) :
          (ZMod.finEquiv (q' + 1)) m = (m.val : ZMod (q' + 1)) := by
        change (m : ZMod (q' + 1)) = (m.val : ZMod (q' + 1))
        apply Fin.ext
        change m.val = m.val % (q' + 1)
        exact (Nat.mod_eq_of_lt m.isLt).symm
      exact Fintype.sum_equiv (ZMod.finEquiv (q' + 1)) _ _ (by
        intro m
        change standardAdditiveCharacter
            ((a : ZMod (q' + 1)) * cubicResidue (m.val : ZMod (q' + 1))) =
          standardAdditiveCharacter
            ((a : ZMod (q' + 1)) * cubicResidue ((ZMod.finEquiv (q' + 1)) m))
        rw [hfin])

/-- Uniform decay of the complete all-residue cubic sum. For `q≥9` this is
the ordinary Weyl estimate on one complete period; the finitely many smaller
moduli are absorbed by the trivial bound. -/
theorem exists_uniform_norm_allResidueCubicExponentialSum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (q a : ℕ) [NeZero q],
      0 < q → Nat.Coprime a q →
      ‖allResidueCubicExponentialSum q (a : ZMod q)‖ ≤
        C * Real.rpow (q : ℝ) (25 / 32 : ℝ) := by
  obtain ⟨K, hK, hweyl⟩ := exists_norm_cubicUnweightedExpSum_four_le_weyl
  let C : ℝ := 8 + 3 * K
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hCge8 : 8 ≤ C := by dsimp [C]; linarith
  have hCge3K : 3 * K ≤ C := by dsimp [C]; linarith
  have hCnonneg : 0 ≤ C := le_of_lt hCpos
  have hC2one : 1 ≤ C ^ 2 := by nlinarith [sq_nonneg (C - 1)]
  have hCfour : 3 * K ≤ C ^ 4 := by
    calc
      3 * K ≤ C := hCge3K
      _ ≤ C ^ 2 := by nlinarith [sq_nonneg (C - 1)]
      _ = C ^ 2 * 1 := by ring
      _ ≤ C ^ 2 * C ^ 2 :=
        mul_le_mul_of_nonneg_left hC2one (sq_nonneg C)
      _ = C ^ 4 := by ring
  refine ⟨C, hCpos, ?_⟩
  intro q a inst hq hac
  letI : NeZero q := inst
  by_cases hlarge : 9 ≤ q
  · have hN : 8 ≤ q - 1 := by omega
    have hxnat : 8 ≤ q - 1 := hN
    let x : ℝ := (q - 1 : ℕ)
    let y : ℝ := q
    have hxpos : 0 < x := by dsimp [x]; positivity
    have hypos : 0 < y := by dsimp [y]; exact_mod_cast hq
    have hyone : 1 ≤ y := by dsimp [y]; exact_mod_cast (by omega : 1 ≤ q)
    have hxge : 8 ≤ x := by dsimp [x]; exact_mod_cast hxnat
    have hyx : y = x + 1 := by
      dsimp [x, y]
      have hsub : q - 1 + 1 = q := Nat.sub_add_cancel (by omega)
      exact_mod_cast hsub.symm
    have hxle : x ≤ y := by linarith
    have hsecondPoly : 2 * y ≤ 3 * x := by linarith
    have hthirdPoly : 2 * y ^ 2 ≤ x ^ 3 := by
      have hxnonneg : 0 ≤ x := by linarith
      have hxSq : 0 ≤ x ^ 2 := sq_nonneg x
      have hxCubeLower : 8 * x ^ 2 ≤ x ^ 3 := by
        nlinarith [mul_le_mul_of_nonneg_right hxge hxSq]
      have hyUpper : y ≤ (9 / 8 : ℝ) * x := by nlinarith
      have hySq : y ^ 2 ≤ ((9 / 8 : ℝ) * x) ^ 2 := by
        nlinarith [mul_nonneg
          (show 0 ≤ (9 / 8 : ℝ) * x - y by linarith)
          (show 0 ≤ (9 / 8 : ℝ) * x + y by positivity)]
      nlinarith
    have hsecond : 1 / x ≤ 3 / (2 * y) := by
      rw [div_le_div_iff₀ hxpos (by positivity)]
      nlinarith [hsecondPoly]
    have hthird : y / x ^ 3 ≤ 1 / (2 * y) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hthirdPoly]
    have hfactor : 1 / y + 1 / x + y / x ^ 3 ≤ 3 / y := by
      calc
        1 / y + 1 / x + y / x ^ 3 ≤ 1 / y + 3 / (2 * y) + 1 / (2 * y) := by
          gcongr
        _ = 3 / y := by field_simp; ring
    have hqmaxR : y ≤ 3 * x ^ 3 := by
      have hxgeone : 1 ≤ x := by linarith
      have hxCube : x ≤ x ^ 3 := by nlinarith [sq_nonneg (x - 1)]
      linarith
    have hqmax : q ≤ 3 * (q - 1) ^ 3 := by
      dsimp [x, y] at hqmaxR
      exact_mod_cast hqmaxR
    have hfour := hweyl (rationalCenter a q) (q - 1) a q 0
      hN hq hqmax hac (by simp) (by norm_num)
    have hfour' :
        ‖cubicUnweightedExpSum (rationalCenter a q) (q - 1)‖ ^ 4 ≤
          K * Real.rpow x (4 + 1 / 12 : ℝ) *
            (1 / y + 1 / x + y / x ^ 3) := by
      simpa [x, y] using hfour
    have hpowbase :
        Real.rpow x (4 + 1 / 12 : ℝ) ≤
          Real.rpow y (4 + 1 / 12 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hxle (by norm_num)
    have hquotient :
        Real.rpow y (4 + 1 / 12 : ℝ) / y =
          Real.rpow y (37 / 12 : ℝ) := by
      calc
        _ = Real.rpow y (4 + 1 / 12 : ℝ) /
            Real.rpow y (1 : ℝ) := by
          congr 1
          exact (Real.rpow_one y).symm
        _ = Real.rpow y ((4 + 1 / 12 : ℝ) - 1) :=
          (Real.rpow_sub hypos _ _).symm
        _ = Real.rpow y (37 / 12 : ℝ) := by congr 1; norm_num
    have hfourBound :
        ‖cubicUnweightedExpSum (rationalCenter a q) (q - 1)‖ ^ 4 ≤
          3 * K * Real.rpow y (37 / 12 : ℝ) := by
      calc
        _ ≤ K * Real.rpow x (4 + 1 / 12 : ℝ) *
              (1 / y + 1 / x + y / x ^ 3) := hfour'
        _ = K * (Real.rpow x (4 + 1 / 12 : ℝ) *
              (1 / y + 1 / x + y / x ^ 3)) := by ring
        _ ≤ K * (Real.rpow y (4 + 1 / 12 : ℝ) * (3 / y)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hpowbase hfactor
              (by positivity : 0 ≤ 1 / y + 1 / x + y / x ^ 3)
              (Real.rpow_nonneg hypos.le _)) hK.le
        _ = 3 * K * Real.rpow y (37 / 12 : ℝ) := by
          rw [show Real.rpow y (4 + 1 / 12 : ℝ) * (3 / y) =
            3 * (Real.rpow y (4 + 1 / 12 : ℝ) / y) by ring, hquotient]
          ring
    have hexp : (37 / 12 : ℝ) ≤ 25 / 8 := by norm_num
    have hpowexp : Real.rpow y (37 / 12 : ℝ) ≤ Real.rpow y (25 / 8 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hyone hexp
    have htargetpow :
        (Real.rpow y (25 / 32 : ℝ)) ^ 4 = Real.rpow y (25 / 8 : ℝ) := by
      calc
        (Real.rpow y (25 / 32 : ℝ)) ^ 4 =
            Real.rpow y ((25 / 32 : ℝ) * 4) := by
          exact (Real.rpow_mul_natCast (by positivity) (25 / 32 : ℝ) 4).symm
        _ = Real.rpow y (25 / 8 : ℝ) := by congr 1; norm_num
    have hfourTarget :
        ‖cubicUnweightedExpSum (rationalCenter a q) (q - 1)‖ ^ 4 ≤
          (C * Real.rpow y (25 / 32 : ℝ)) ^ 4 := by
      rw [show (C * Real.rpow y (25 / 32 : ℝ)) ^ 4 =
        C ^ 4 * (Real.rpow y (25 / 32 : ℝ)) ^ 4 by ring, htargetpow]
      exact hfourBound.trans (mul_le_mul hCfour hpowexp
        (Real.rpow_nonneg (le_of_lt hypos) _)
        (pow_nonneg hCnonneg _))
    have hpoint :
        ‖cubicUnweightedExpSum (rationalCenter a q) (q - 1)‖ ≤
          C * Real.rpow y (25 / 32 : ℝ) := by
      by_contra hnot
      have hlt := lt_of_not_ge hnot
      have hnonneg : 0 ≤ C * Real.rpow y (25 / 32 : ℝ) :=
        mul_nonneg hCnonneg (Real.rpow_nonneg (le_of_lt hypos) _)
      have hnormpos :
          0 < ‖cubicUnweightedExpSum (rationalCenter a q) (q - 1)‖ :=
        lt_of_le_of_lt hnonneg hlt
      have hdiff : 0 <
          (‖cubicUnweightedExpSum (rationalCenter a q) (q - 1)‖ -
              C * Real.rpow y (25 / 32 : ℝ)) *
            (‖cubicUnweightedExpSum (rationalCenter a q) (q - 1)‖ +
              C * Real.rpow y (25 / 32 : ℝ)) *
            (‖cubicUnweightedExpSum (rationalCenter a q) (q - 1)‖ ^ 2 +
              (C * Real.rpow y (25 / 32 : ℝ)) ^ 2) := by
        apply mul_pos
        · exact mul_pos (sub_pos.mpr hlt) (by positivity)
        · exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hnormpos) (sq_nonneg _)
      have hfac :
          ‖cubicUnweightedExpSum (rationalCenter a q) (q - 1)‖ ^ 4 -
              (C * Real.rpow y (25 / 32 : ℝ)) ^ 4 =
            (‖cubicUnweightedExpSum (rationalCenter a q) (q - 1)‖ -
                C * Real.rpow y (25 / 32 : ℝ)) *
              (‖cubicUnweightedExpSum (rationalCenter a q) (q - 1)‖ +
                C * Real.rpow y (25 / 32 : ℝ)) *
              (‖cubicUnweightedExpSum (rationalCenter a q) (q - 1)‖ ^ 2 +
                (C * Real.rpow y (25 / 32 : ℝ)) ^ 2) := by ring
      nlinarith [hfourTarget, hdiff, hfac]
    rw [cubicUnweightedExpSum_rationalCenter_eq_allResidue q a hq] at hpoint
    simpa [y] using hpoint
  · have hqle8 : q ≤ 8 := by omega
    have hqreal : (q : ℝ) ≤ 8 := by exact_mod_cast hqle8
    have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
    have hpowone : 1 ≤ Real.rpow (q : ℝ) (25 / 32 : ℝ) := by
      calc
        1 = Real.rpow 1 (25 / 32 : ℝ) := by norm_num
        _ ≤ Real.rpow (q : ℝ) (25 / 32 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) hqone
            (by norm_num : (0 : ℝ) ≤ 25 / 32)
    calc
      ‖allResidueCubicExponentialSum q (a : ZMod q)‖ ≤ q :=
        norm_allResidueCubicExponentialSum_le q (a : ZMod q)
      _ ≤ 8 := hqreal
      _ ≤ C := hCge8
      _ ≤ C * Real.rpow (q : ℝ) (25 / 32 : ℝ) := by
        exact le_mul_of_one_le_right hCnonneg hpowone

/-- After dividing by the modulus, the complete-sum coefficient has enough
decay that its 32nd power is summable over all reduced centers. -/
theorem exists_uniform_norm_allResidueCoefficient_pow32_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (q a : ℕ) [NeZero q],
      0 < q → Nat.Coprime a q →
      ‖allResidueCubicExponentialSum q (a : ZMod q) *
          ((1 / (q : ℝ) : ℝ) : ℂ)‖ ^ 32 ≤ C ^ 32 / (q : ℝ) ^ 3 := by
  obtain ⟨C, hCpos, hsum⟩ :=
    exists_uniform_norm_allResidueCubicExponentialSum_le
  refine ⟨C, hCpos, ?_⟩
  intro q a inst hq hac
  letI : NeZero q := inst
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hsumq := hsum q a hq hac
  have hpowmono :
      Real.rpow (q : ℝ) (25 / 32 : ℝ) ≤
        Real.rpow (q : ℝ) (29 / 32 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hqone (by norm_num)
  have hquotient :
      Real.rpow (q : ℝ) (29 / 32 : ℝ) * (1 / (q : ℝ)) =
        Real.rpow (q : ℝ) (-3 / 32 : ℝ) := by
    calc
      _ = Real.rpow (q : ℝ) (29 / 32 : ℝ) / (q : ℝ) := by ring
      _ = Real.rpow (q : ℝ) (29 / 32 : ℝ) /
          Real.rpow (q : ℝ) (1 : ℝ) := by
        congr 1
        exact (Real.rpow_one (q : ℝ)).symm
      _ = Real.rpow (q : ℝ) ((29 / 32 : ℝ) - 1) :=
        (Real.rpow_sub hqreal _ _).symm
      _ = Real.rpow (q : ℝ) (-3 / 32 : ℝ) := by congr 1; norm_num
  have hcoefficient :
      ‖allResidueCubicExponentialSum q (a : ZMod q) *
          ((1 / (q : ℝ) : ℝ) : ℂ)‖ ≤
        C * Real.rpow (q : ℝ) (-3 / 32 : ℝ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (q : ℝ))]
    calc
      ‖allResidueCubicExponentialSum q (a : ZMod q)‖ * (1 / (q : ℝ)) ≤
          (C * Real.rpow (q : ℝ) (25 / 32 : ℝ)) * (1 / (q : ℝ)) :=
        mul_le_mul_of_nonneg_right hsumq (by positivity)
      _ = C * (Real.rpow (q : ℝ) (25 / 32 : ℝ) * (1 / (q : ℝ))) := by ring
      _ ≤ C * (Real.rpow (q : ℝ) (29 / 32 : ℝ) * (1 / (q : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hCpos.le
        exact mul_le_mul_of_nonneg_right hpowmono (by positivity)
      _ = C * Real.rpow (q : ℝ) (-3 / 32 : ℝ) := by rw [hquotient]
  have hpower :
      (Real.rpow (q : ℝ) (-3 / 32 : ℝ)) ^ 32 = 1 / (q : ℝ) ^ 3 := by
    calc
      (Real.rpow (q : ℝ) (-3 / 32 : ℝ)) ^ 32 =
          Real.rpow (q : ℝ) ((-3 / 32 : ℝ) * 32) := by
        exact (Real.rpow_mul_natCast (by positivity) (-3 / 32 : ℝ) 32).symm
      _ = Real.rpow (q : ℝ) (-3 : ℝ) := by congr 1; norm_num
      _ = (Real.rpow (q : ℝ) 3)⁻¹ := by
        exact Real.rpow_neg hqreal.le (3 : ℝ)
      _ = 1 / (q : ℝ) ^ 3 := by simp
  have hpow := pow_le_pow_left₀ (norm_nonneg _) hcoefficient 32
  calc
    _ ≤ (C * Real.rpow (q : ℝ) (-3 / 32 : ℝ)) ^ 32 := hpow
    _ = C ^ 32 * (Real.rpow (q : ℝ) (-3 / 32 : ℝ)) ^ 32 := by ring
    _ = C ^ 32 / (q : ℝ) ^ 3 := by rw [hpower]; ring

/-- The homogeneous all-residue model contributes at most `q⁻³ N²⁹` times
the absolute archimedean frequency moment on any power-cutoff arc window. -/
theorem exists_uniform_integral_norm_cubicAllResidueHomogeneousModel_pow32_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (q a N Q : ℕ) [NeZero q],
      0 < q → Nat.Coprime a q → 0 < N →
      (∫ beta in Set.Icc (-((Q : ℝ) / (N : ℝ) ^ 3))
          ((Q : ℝ) / (N : ℝ) ^ 3),
          ‖cubicAllResidueHomogeneousModel q (a : ZMod q) beta N‖ ^ 32) ≤
        C ^ 32 / (q : ℝ) ^ 3 * (N : ℝ) ^ 29 *
          ∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau := by
  obtain ⟨C, hCpos, hcoef⟩ := exists_uniform_norm_allResidueCoefficient_pow32_le
  refine ⟨C, hCpos, ?_⟩
  intro q a N Q inst hq hac hN
  letI : NeZero q := inst
  let B : ℝ := C ^ 32 / (q : ℝ) ^ 3
  let r : ℝ := (Q : ℝ) / (N : ℝ) ^ 3
  let M : ℝ → ℝ := fun beta =>
    ‖cubicAllResidueHomogeneousModel q (a : ZMod q) beta N‖ ^ 32
  let G : ℝ → ℝ := fun beta =>
    B * (N : ℝ) ^ 32 * Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 (beta * (N : ℝ) ^ 3)
  have hBnonneg : 0 ≤ B := by dsimp [B]; positivity
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hcoeff := hcoef q a hq hac
  have hmodelNorm (beta : ℝ) :
      ‖cubicAllResidueHomogeneousModel q (a : ZMod q) beta N‖ =
        ‖allResidueCubicExponentialSum q (a : ZMod q) *
            ((1 / (q : ℝ) : ℝ) : ℂ)‖ * (N : ℝ) *
          ‖oneDimensionalCubicIntegral (beta * (N : ℝ) ^ 3)‖ := by
    simp [cubicAllResidueHomogeneousModel]
    ring
  have hpoint (beta : ℝ) : M beta ≤ G beta := by
    dsimp [M, G, B]
    rw [hmodelNorm]
    calc
      (‖allResidueCubicExponentialSum q (a : ZMod q) *
            ((1 / (q : ℝ) : ℝ) : ℂ)‖ * (N : ℝ) *
          ‖oneDimensionalCubicIntegral (beta * (N : ℝ) ^ 3)‖) ^ 32 =
          ‖allResidueCubicExponentialSum q (a : ZMod q) *
              ((1 / (q : ℝ) : ℝ) : ℂ)‖ ^ 32 * (N : ℝ) ^ 32 *
            ‖oneDimensionalCubicIntegral (beta * (N : ℝ) ^ 3)‖ ^ 32 := by ring
      _ ≤ (C ^ 32 / (q : ℝ) ^ 3) * (N : ℝ) ^ 32 *
            ‖oneDimensionalCubicIntegral (beta * (N : ℝ) ^ 3)‖ ^ 32 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoeff (by positivity)) (by positivity)
      _ = G beta := by
        simp [G, B, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32]
  have hvcont : Continuous
      (fun beta : ℝ => oneDimensionalCubicIntegral (beta * (N : ℝ) ^ 3)) :=
    oneDimensionalCubicIntegral_continuous.comp
      (continuous_id.mul continuous_const)
  have hMmodel : Continuous
      (fun beta : ℝ => cubicAllResidueHomogeneousModel q (a : ZMod q) beta N) := by
    change Continuous (fun beta : ℝ =>
      (allResidueCubicExponentialSum q (a : ZMod q) *
          ((1 / (q : ℝ) : ℝ) : ℂ)) *
        ((N : ℝ) • oneDimensionalCubicIntegral (beta * (N : ℝ) ^ 3)))
    have hNcontinuous : Continuous (fun _ : ℝ => (N : ℝ)) :=
      continuous_const
    have hscaled : Continuous
        (fun beta : ℝ => (N : ℝ) •
          oneDimensionalCubicIntegral (beta * (N : ℝ) ^ 3)) :=
      hNcontinuous.smul hvcont
    have hcoefficient : Continuous (fun _ : ℝ =>
        allResidueCubicExponentialSum q (a : ZMod q) *
          ((1 / (q : ℝ) : ℝ) : ℂ)) := continuous_const
    exact hcoefficient.mul hscaled
  have hMcont : Continuous M := by
    dsimp [M]
    exact hMmodel.norm.pow 32
  have hfreqCont : Continuous
      (fun beta : ℝ => Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 (beta * (N : ℝ) ^ 3)) := by
    dsimp [Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32]
    exact (oneDimensionalCubicIntegral_continuous.comp
      (continuous_id.mul continuous_const)).norm.pow 32
  have hGcont : Continuous G := by
    change Continuous (fun beta : ℝ =>
      (B * (N : ℝ) ^ 32) *
        Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 (beta * (N : ℝ) ^ 3))
    have hconstant : Continuous (fun _ : ℝ => B * (N : ℝ) ^ 32) :=
      continuous_const
    exact hconstant.mul hfreqCont
  have hMint : IntegrableOn M (Set.Icc (-r) r) := by
    exact hMcont.integrableOn_Icc
  have hGint : IntegrableOn G (Set.Icc (-r) r) := by
    exact hGcont.integrableOn_Icc
  have hInt := setIntegral_mono_ae hMint hGint
    (Filter.Eventually.of_forall hpoint)
  have hscale := integral_cubicFrequencyNormPow32_scaled_le N Q hN
  calc
    (∫ beta in Set.Icc (-((Q : ℝ) / (N : ℝ) ^ 3))
        ((Q : ℝ) / (N : ℝ) ^ 3),
        ‖cubicAllResidueHomogeneousModel q (a : ZMod q) beta N‖ ^ 32) =
      ∫ beta in Set.Icc (-r) r, M beta := by simp [M, r]
    _ ≤ ∫ beta in Set.Icc (-r) r, G beta := hInt
    _ = B * (N : ℝ) ^ 32 *
        (∫ beta in Set.Icc (-r) r,
          Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 (beta * (N : ℝ) ^ 3)) := by
      simp only [G]
      rw [integral_const_mul]
    _ ≤ B * (N : ℝ) ^ 32 *
        (((N : ℝ) ^ 3)⁻¹ * ∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau) := by
      exact mul_le_mul_of_nonneg_left hscale
        (mul_nonneg hBnonneg (by positivity))
    _ = C ^ 32 / (q : ℝ) ^ 3 * (N : ℝ) ^ 29 *
          ∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau := by
      dsimp [B]
      field_simp [ne_of_gt hNreal]

/-- The all-residue homogeneous model evaluated at the canonical small
displacement from a rational center, including arcs crossing 0 or 1. -/
noncomputable def wrappedCubicAllResidueHomogeneousModel
    (q : ℕ) [NeZero q] (a : ZMod q) (N : ℕ) (alpha : ℝ) : ℂ :=
  cubicAllResidueHomogeneousModel q a
    (wrappedMajorArcDisplacement a.val q alpha) N

theorem wrappedCubicAllResidueHomogeneousModel_add_int
    (q : ℕ) [NeZero q] (a : ZMod q) (N : ℕ) (alpha : ℝ) (z : ℤ) :
    wrappedCubicAllResidueHomogeneousModel q a N (alpha + z) =
      wrappedCubicAllResidueHomogeneousModel q a N alpha := by
  simp [wrappedCubicAllResidueHomogeneousModel,
    wrappedMajorArcDisplacement_add_int]

/-- The local all-residue approximation holds uniformly on the wrapped
power-cutoff arc after reducing its frequency to the canonical displacement. -/
theorem norm_cubicUnweightedExpSum_sub_wrappedCubicAllResidueHomogeneousModel_le_auxCutoff
    (q a N P : ℕ) [NeZero q] (hq : 0 < q) (hN : 0 < N)
    (hqP : q ≤ P) (ha : a < q) {alpha : ℝ}
    (halpha : alpha ∈ majorArcAt N P a q) :
    ‖cubicUnweightedExpSum alpha N -
      wrappedCubicAllResidueHomogeneousModel q (a : ZMod q) N alpha‖ ≤
        64 * ((P : ℝ) + 1) ^ 2 := by
  let beta := wrappedMajorArcDisplacement a q alpha
  have hbeta : |beta| < cubicArcRadius N P := by
    simpa [beta, wrappedMajorArcDisplacement, rationalCenter,
      periodicDistance_eq_abs_sub_round] using halpha.2
  have hbetaScale : |beta| * (N : ℝ) ^ 3 ≤ (P : ℝ) := by
    have hNcube : 0 < (N : ℝ) ^ 3 := by positivity
    have hrad : cubicArcRadius N P * (N : ℝ) ^ 3 = (P : ℝ) := by
      unfold cubicArcRadius
      field_simp
    rw [← hrad]
    exact mul_le_mul_of_nonneg_right hbeta.le hNcube.le
  have hval : ((a : ZMod q).val) = a := by
    simp [Nat.mod_eq_of_lt ha]
  have hperiod : cubicUnweightedExpSum alpha N =
      cubicUnweightedExpSum (rationalCenter a q + beta) N := by
    have hdecomp : alpha = rationalCenter a q + beta +
        (round (alpha - rationalCenter a q) : ℤ) := by
      dsimp [beta, wrappedMajorArcDisplacement]
      ring
    rw [hdecomp, cubicUnweightedExpSum_add_int]
  have hmodel : wrappedCubicAllResidueHomogeneousModel q
      (a : ZMod q) N alpha =
        cubicAllResidueHomogeneousModel q (a : ZMod q) beta N := by
    simp [wrappedCubicAllResidueHomogeneousModel, beta,
      wrappedMajorArcDisplacement, hval]
  rw [hperiod, hmodel]
  exact norm_cubicUnweightedExpSum_sub_homogeneousModel_le_auxCutoff
    q a N P hq hN hqP beta hbetaScale

/-- On an interior clipped rational arc, transport an explicit uniform
real-window estimate to the wrapped all-residue model. -/
theorem integral_wrappedCubicAllResidueHomogeneousModel_pow32_le_of_interior
    (q a N Q : ℕ) [NeZero q] (C : ℝ)
    (hwindow :
      (∫ beta in Set.Icc (-((Q : ℝ) / (N : ℝ) ^ 3))
          ((Q : ℝ) / (N : ℝ) ^ 3),
          ‖cubicAllResidueHomogeneousModel q (a : ZMod q) beta N‖ ^ 32) ≤
        C ^ 32 / (q : ℝ) ^ 3 * (N : ℝ) ^ 29 *
          ∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau)
    (hN : 0 < N) (hq : 0 < q)
    (ha : a < q) (_hac : Nat.Coprime a q)
    (hright : cubicArcRadius N Q < rationalCenter a q)
    (hleft : cubicArcRadius N Q < 1 - rationalCenter a q) :
    (∫ alpha in majorArcAt N Q a q,
        ‖wrappedCubicAllResidueHomogeneousModel q (a : ZMod q) N alpha‖ ^ 32) ≤
        C ^ 32 / (q : ℝ) ^ 3 * (N : ℝ) ^ 29 *
          ∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau := by
  let c : ℝ := rationalCenter a q
  let r : ℝ := cubicArcRadius N Q
  let M : ℝ → ℝ := fun beta =>
    ‖cubicAllResidueHomogeneousModel q (a : ZMod q) beta N‖ ^ 32
  let F : ℝ → ℝ := fun alpha =>
    ‖wrappedCubicAllResidueHomogeneousModel q (a : ZMod q) N alpha‖ ^ 32
  have hval : (a : ZMod q).val = a := by
    simp [Nat.mod_eq_of_lt ha]
  have hrnonneg : 0 ≤ r := by dsimp [r, cubicArcRadius]; positivity
  have hlocalCont : Continuous
      (fun beta : ℝ => cubicAllResidueHomogeneousModel q (a : ZMod q) beta N) := by
    change Continuous (fun beta : ℝ =>
      (allResidueCubicExponentialSum q (a : ZMod q) *
        ((1 / (q : ℝ) : ℝ) : ℂ)) *
        ((N : ℝ) • oneDimensionalCubicIntegral (beta * (N : ℝ) ^ 3)))
    have hNcontinuous : Continuous (fun _ : ℝ => (N : ℝ)) := continuous_const
    have hv : Continuous
        (fun beta : ℝ => oneDimensionalCubicIntegral (beta * (N : ℝ) ^ 3)) :=
      oneDimensionalCubicIntegral_continuous.comp
        (continuous_id.mul continuous_const)
    have hscaled : Continuous
        (fun beta : ℝ => (N : ℝ) •
          oneDimensionalCubicIntegral (beta * (N : ℝ) ^ 3)) := hNcontinuous.smul hv
    have hcoefficient : Continuous (fun _ : ℝ =>
        allResidueCubicExponentialSum q (a : ZMod q) *
          ((1 / (q : ℝ) : ℝ) : ℂ)) := continuous_const
    exact hcoefficient.mul hscaled
  have hMcont : Continuous M := by
    dsimp [M]
    exact hlocalCont.norm.pow 32
  have hFmeas : Measurable F := by
    dsimp [F]
    change Measurable (fun alpha : ℝ =>
      M (wrappedMajorArcDisplacement (a : ZMod q).val q alpha))
    rw [hval]
    exact hMcont.measurable.comp
      (measurable_wrappedMajorArcDisplacement a q)
  have hcoeff : ‖allResidueCubicExponentialSum q (a : ZMod q) *
      ((1 / (q : ℝ) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (q : ℝ))]
    calc
      ‖allResidueCubicExponentialSum q (a : ZMod q)‖ * (1 / (q : ℝ)) ≤
          (q : ℝ) * (1 / (q : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (norm_allResidueCubicExponentialSum_le q (a : ZMod q)) (by positivity)
      _ = 1 := by field_simp
  have hmodelBound (beta : ℝ) :
      ‖cubicAllResidueHomogeneousModel q (a : ZMod q) beta N‖ ≤ N := by
    rw [cubicAllResidueHomogeneousModel, norm_mul, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ))]
    calc
      ‖allResidueCubicExponentialSum q (a : ZMod q) *
          ((1 / (q : ℝ) : ℝ) : ℂ)‖ * ((N : ℝ) *
            ‖oneDimensionalCubicIntegral (beta * (N : ℝ) ^ 3)‖) ≤
          1 * ((N : ℝ) * 1) := by
        exact mul_le_mul hcoeff
          (mul_le_mul_of_nonneg_left
            (norm_oneDimensionalCubicIntegral_le_one _) (by positivity))
          (by positivity) (by positivity)
      _ = N := by norm_num
  have hFbound (alpha : ℝ) : ‖F alpha‖ ≤ (N : ℝ) ^ 32 := by
    change ‖‖wrappedCubicAllResidueHomogeneousModel q (a : ZMod q) N alpha‖ ^ 32‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) 32)]
    change ‖cubicAllResidueHomogeneousModel q (a : ZMod q)
      (wrappedMajorArcDisplacement (a : ZMod q).val q alpha) N‖ ^ 32 ≤ _
    exact pow_le_pow_left₀ (norm_nonneg _)
      (hmodelBound (wrappedMajorArcDisplacement (a : ZMod q).val q alpha)) 32
  have hfinite : volume (majorArcAt N Q a q) ≠ ∞ := by
    apply ne_of_lt
    calc
      volume (majorArcAt N Q a q) ≤ volume (Set.Icc (0 : ℝ) 1) :=
        measure_mono (majorArcAt_subset_Icc N Q a q)
      _ < ∞ := by simp
  have hFint : IntegrableOn F (majorArcAt N Q a q) :=
    volume.integrableOn_of_bounded hfinite hFmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hFbound)
  have hset : majorArcAt N Q a q = Set.Ioo (c - r) (c + r) := by
    simpa [c, r] using
      (majorArcAt_eq_Ioo_of_interior_radius N Q a q hright hleft)
  have hpoint : ∀ alpha ∈ Set.Ioo (c - r) (c + r),
      F alpha = M (alpha - c) := by
    intro alpha halpha
    have harc : alpha ∈ majorArcAt N Q a q := by rw [hset]; exact halpha
    have hdisp := wrappedMajorArcDisplacement_eq_sub_of_interior
      harc.1 hright hleft harc.2
    change ‖cubicAllResidueHomogeneousModel q (a : ZMod q)
      (wrappedMajorArcDisplacement (a : ZMod q).val q alpha) N‖ ^ 32 =
      ‖cubicAllResidueHomogeneousModel q (a : ZMod q) (alpha - c) N‖ ^ 32
    rw [hval, wrappedMajorArcDisplacement, hdisp]
  have hwindowModel :
      (∫ beta in Set.Icc (-r) r, M beta) ≤
        C ^ 32 / (q : ℝ) ^ 3 * (N : ℝ) ^ 29 *
          ∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau := by
    simpa [M, r, cubicArcRadius] using hwindow
  calc
    (∫ alpha in majorArcAt N Q a q, F alpha) =
        ∫ alpha in Set.Ioo (c - r) (c + r), F alpha := by rw [hset]
    _ = ∫ alpha in Set.Ioo (c - r) (c + r), M (alpha - c) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      exact hpoint
    _ = ∫ alpha in Set.Icc (c - r) (c + r), M (alpha - c) := by
      rw [← integral_Icc_eq_integral_Ioo]
    _ = ∫ alpha in (c - r)..(c + r), M (alpha - c) := by
      rw [intervalIntegral.integral_of_le (by linarith [hrnonneg]),
        ← integral_Icc_eq_integral_Ioc]
    _ = ∫ beta in (-r)..r, M beta := by
      calc
        (∫ alpha in (c - r)..(c + r), M (alpha - c)) =
            ∫ alpha in (c - r)..(c + r), M (alpha + -c) := by congr 1
        _ = ∫ beta in (c - r + -c)..(c + r + -c), M beta :=
          intervalIntegral.integral_comp_add_right (f := M) (-c)
        _ = ∫ beta in (-r)..r, M beta := by congr 1 <;> ring
    _ = ∫ beta in Set.Icc (-r) r, M beta := by
      rw [intervalIntegral.integral_of_le (by linarith [hrnonneg]),
        ← integral_Icc_eq_integral_Ioc]
    _ ≤ C ^ 32 / (q : ℝ) ^ 3 * (N : ℝ) ^ 29 *
          ∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau := hwindowModel

/-- Existential interface for the interior wrapped model bound. The explicit
constant is retained in the companion theorem for finite center summation. -/
theorem exists_uniform_integral_wrappedCubicAllResidueHomogeneousModel_pow32_le_of_interior
    (q a N Q : ℕ) [NeZero q] (hN : 0 < N) (hq : 0 < q)
    (ha : a < q) (hac : Nat.Coprime a q)
    (hright : cubicArcRadius N Q < rationalCenter a q)
    (hleft : cubicArcRadius N Q < 1 - rationalCenter a q) :
    ∃ C : ℝ, 0 < C ∧
      (∫ alpha in majorArcAt N Q a q,
        ‖wrappedCubicAllResidueHomogeneousModel q (a : ZMod q) N alpha‖ ^ 32) ≤
        C ^ 32 / (q : ℝ) ^ 3 * (N : ℝ) ^ 29 *
          ∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau := by
  obtain ⟨C, hC, hwindowAll⟩ :=
    exists_uniform_integral_norm_cubicAllResidueHomogeneousModel_pow32_le
  refine ⟨C, hC, ?_⟩
  exact integral_wrappedCubicAllResidueHomogeneousModel_pow32_le_of_interior
    q a N Q C (hwindowAll q a N Q hq hac hN) hN hq ha hac hright hleft

/-- Under the auxiliary separation scale, every reduced center of denominator
greater than one is far enough from both endpoints for the interior transport. -/
theorem cubicAuxiliaryArc_interior_of_denominator_gt_one
    {N Q a q : ℕ} (hscale : 2 * Q ^ 3 ≤ N ^ 3)
    (hqQ : q ≤ Q) (hq : 0 < q) (hq1 : 1 < q)
    (ha : a < q) (hac : Nat.Coprime a q) :
    cubicArcRadius N Q < rationalCenter a q ∧
      cubicArcRadius N Q < 1 - rationalCenter a q := by
  have hQpos : 0 < Q := lt_of_lt_of_le hq hqQ
  have hQone : 1 ≤ Q := by omega
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQpos
  have hNcubeNat : 0 < N ^ 3 := by
    have hpos : 0 < 2 * Q ^ 3 := by positivity
    exact lt_of_lt_of_le hpos hscale
  have hNcube : (0 : ℝ) < (N : ℝ) ^ 3 := by
    exact_mod_cast hNcubeNat
  have hscaleReal : 2 * (Q : ℝ) ^ 3 ≤ (N : ℝ) ^ 3 := by
    exact_mod_cast hscale
  have hQsq : (Q : ℝ) ^ 2 < (N : ℝ) ^ 3 := by
    have hstrict : (Q : ℝ) ^ 2 < 2 * (Q : ℝ) ^ 3 := by
      have hQtwo : (2 : ℝ) ≤ Q := by exact_mod_cast (show 2 ≤ Q by omega)
      nlinarith [hQreal, hQtwo]
    exact hstrict.trans_le hscaleReal
  have hradius : cubicArcRadius N Q < 1 / (Q : ℝ) := by
    unfold cubicArcRadius
    apply (div_lt_div_iff₀ hNcube hQreal).2
    nlinarith [hQsq]
  have ha0 : 0 < a := by
    by_contra hnot
    have haeq : a = 0 := by omega
    subst a
    simp at hac
    omega
  have hcenterLower : 1 / (q : ℝ) ≤ rationalCenter a q := by
    unfold rationalCenter
    apply (div_le_div_iff_of_pos_right hqreal).2
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt ha0))
  have hleftNumerator : 1 ≤ q - a := by omega
  have hleftLower : 1 / (q : ℝ) ≤ 1 - rationalCenter a q := by
    unfold rationalCenter
    calc
      1 / (q : ℝ) ≤ ((q - a : ℕ) : ℝ) / (q : ℝ) :=
        div_le_div_of_nonneg_right
          (by exact_mod_cast hleftNumerator) (by positivity)
      _ = 1 - (a : ℝ) / (q : ℝ) := by
        rw [Nat.cast_sub (Nat.le_of_lt ha)]
        field_simp
  have hinv : 1 / (Q : ℝ) ≤ 1 / (q : ℝ) := by
    apply (div_le_div_iff₀ hQreal hqreal).2
    have hqQReal : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
    nlinarith [hqQReal]
  constructor
  · exact hradius.trans_le (hinv.trans hcenterLower)
  · exact hradius.trans_le (hinv.trans hleftLower)

/-- The denominator-one arc crosses the fundamental interval seam. Unfolding
its right-hand piece by one period gives exactly the full real displacement
window for the all-residue model's 32nd power. -/
theorem integral_wrappedCubicAllResidueHomogeneousModel_pow32_eq_zeroOneWindow
    (N Q : ℕ) (hradius : cubicArcRadius N Q ≤ (1 / 2 : ℝ)) :
    (∫ alpha in majorArcAt N Q 0 1,
      ‖wrappedCubicAllResidueHomogeneousModel 1 (0 : ZMod 1) N alpha‖ ^ 32) =
      ∫ beta in Set.Icc (-((Q : ℝ) / (N : ℝ) ^ 3))
        ((Q : ℝ) / (N : ℝ) ^ 3),
        ‖cubicAllResidueHomogeneousModel 1 (0 : ZMod 1) beta N‖ ^ 32 := by
  let r : ℝ := cubicArcRadius N Q
  let M : ℝ → ℝ := fun beta =>
    ‖cubicAllResidueHomogeneousModel 1 (0 : ZMod 1) beta N‖ ^ 32
  let F : ℝ → ℝ := fun alpha =>
    ‖wrappedCubicAllResidueHomogeneousModel 1 (0 : ZMod 1) N alpha‖ ^ 32
  have hrnonneg : 0 ≤ r := by dsimp [r, cubicArcRadius]; positivity
  have hrhalf : r ≤ 1 / 2 := by simpa [r] using hradius
  have hlocalCont : Continuous
      (fun beta : ℝ => cubicAllResidueHomogeneousModel 1 (0 : ZMod 1) beta N) := by
    have hNcontinuous : Continuous (fun _ : ℝ => (N : ℝ)) := continuous_const
    have hv : Continuous
        (fun beta : ℝ => oneDimensionalCubicIntegral (beta * (N : ℝ) ^ 3)) :=
      oneDimensionalCubicIntegral_continuous.comp
        (continuous_id.mul continuous_const)
    have hscaled : Continuous
        (fun beta : ℝ => (N : ℝ) •
          oneDimensionalCubicIntegral (beta * (N : ℝ) ^ 3)) := hNcontinuous.smul hv
    have hcoefficient : Continuous (fun _ : ℝ =>
        allResidueCubicExponentialSum 1 (0 : ZMod 1) *
          ((1 / ((1 : ℕ) : ℝ) : ℝ) : ℂ)) := continuous_const
    convert hcoefficient.mul hscaled using 1
    ext beta
    simp [cubicAllResidueHomogeneousModel]
  have hMcont : Continuous M := by
    dsimp [M]
    exact hlocalCont.norm.pow 32
  have hFmeas : Measurable F := by
    dsimp [F]
    change Measurable (fun alpha : ℝ =>
      M (wrappedMajorArcDisplacement 0 1 alpha))
    exact hMcont.measurable.comp (measurable_wrappedMajorArcDisplacement 0 1)
  have hsum : ‖allResidueCubicExponentialSum 1 (0 : ZMod 1)‖ ≤ 1 := by
    simpa using norm_allResidueCubicExponentialSum_le 1 (0 : ZMod 1)
  have hcoeff : ‖allResidueCubicExponentialSum 1 (0 : ZMod 1) *
      ((1 / ((1 : ℕ) : ℝ) : ℝ) : ℂ)‖ ≤ 1 := by simpa using hsum
  have hmodelBound (beta : ℝ) :
      ‖cubicAllResidueHomogeneousModel 1 (0 : ZMod 1) beta N‖ ≤ N := by
    rw [cubicAllResidueHomogeneousModel, norm_mul, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ))]
    calc
      ‖allResidueCubicExponentialSum 1 (0 : ZMod 1) *
          ((1 / ((1 : ℕ) : ℝ) : ℝ) : ℂ)‖ * ((N : ℝ) *
            ‖oneDimensionalCubicIntegral (beta * (N : ℝ) ^ 3)‖) ≤
          1 * ((N : ℝ) * 1) := by
        exact mul_le_mul hcoeff
          (mul_le_mul_of_nonneg_left
            (norm_oneDimensionalCubicIntegral_le_one _) (by positivity))
          (by positivity) (by positivity)
      _ = N := by norm_num
  have hFbound (alpha : ℝ) : ‖F alpha‖ ≤ (N : ℝ) ^ 32 := by
    change ‖‖wrappedCubicAllResidueHomogeneousModel 1 (0 : ZMod 1) N alpha‖ ^ 32‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) 32)]
    change ‖cubicAllResidueHomogeneousModel 1 (0 : ZMod 1)
      (wrappedMajorArcDisplacement 0 1 alpha) N‖ ^ 32 ≤ _
    exact pow_le_pow_left₀ (norm_nonneg _)
      (hmodelBound (wrappedMajorArcDisplacement 0 1 alpha)) 32
  have hfinite : volume (majorArcAt N Q 0 1) ≠ ∞ := by
    apply ne_of_lt
    calc
      volume (majorArcAt N Q 0 1) ≤ volume (Set.Icc (0 : ℝ) 1) :=
        measure_mono (majorArcAt_subset_Icc N Q 0 1)
      _ < ∞ := by simp
  have hFint : IntegrableOn F (majorArcAt N Q 0 1) :=
    volume.integrableOn_of_bounded hfinite hFmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hFbound)
  have hdecomp : majorArcAt N Q 0 1 =
      Set.Ico (0 : ℝ) r ∪ Set.Ioc (1 - r) 1 := by
    simpa [r] using majorArcAt_zero_one_eq_seam_intervals N Q hradius
  have hdisj : Disjoint (Set.Ico (0 : ℝ) r) (Set.Ioc (1 - r) 1) := by
    rw [Set.disjoint_left]
    intro alpha hlow hhigh
    linarith [hlow.2, hhigh.1]
  have hFintLow : IntegrableOn F (Set.Ico (0 : ℝ) r) :=
    hFint.mono_set (by rw [hdecomp]; exact Set.subset_union_left)
  have hFintHigh : IntegrableOn F (Set.Ioc (1 - r) 1) :=
    hFint.mono_set (by rw [hdecomp]; exact Set.subset_union_right)
  have hLowPoint : ∀ alpha ∈ Set.Ico (0 : ℝ) r, F alpha = M alpha := by
    intro alpha halpha
    have hround : round alpha = 0 := by
      apply round_eq_zero_iff.mpr
      constructor <;> linarith [halpha.1, halpha.2, hrhalf]
    simp [F, M, wrappedCubicAllResidueHomogeneousModel,
      wrappedMajorArcDisplacement, rationalCenter, hround]
  have hHighPoint : ∀ alpha ∈ Set.Ioc (1 - r) 1,
      F alpha = M (alpha - 1) := by
    intro alpha halpha
    have hround : round alpha = 1 := by
      apply round_eq_iff.mpr
      constructor <;> linarith [halpha.1, halpha.2, hrhalf]
    simp [F, M, wrappedCubicAllResidueHomogeneousModel,
      wrappedMajorArcDisplacement, rationalCenter, hround]
  have hlow :
      (∫ alpha in Set.Ico (0 : ℝ) r, F alpha) =
        ∫ beta in (0 : ℝ)..r, M beta := by
    calc
      _ = ∫ alpha in Set.Ico (0 : ℝ) r, M alpha :=
        setIntegral_congr_fun measurableSet_Ico hLowPoint
      _ = ∫ beta in Set.Ioc (0 : ℝ) r, M beta := by
        rw [integral_Ico_eq_integral_Ioc]
      _ = ∫ beta in (0 : ℝ)..r, M beta := by
        rw [← intervalIntegral.integral_of_le hrnonneg]
  have hhigh :
      (∫ alpha in Set.Ioc (1 - r) 1, F alpha) =
        ∫ beta in (-r)..(0 : ℝ), M beta := by
    calc
      _ = ∫ alpha in Set.Ioc (1 - r) 1, M (alpha - 1) :=
        setIntegral_congr_fun measurableSet_Ioc hHighPoint
      _ = ∫ alpha in (1 - r)..1, M (alpha - 1) := by
        rw [← intervalIntegral.integral_of_le (by linarith [hrhalf])]
      _ = ∫ beta in (1 - r + -1)..(1 + -1), M beta := by
        calc
          (∫ alpha in (1 - r)..1, M (alpha - 1)) =
              ∫ alpha in (1 - r)..1, M (alpha + -1) := by congr 1
          _ = ∫ beta in (1 - r + -1)..(1 + -1), M beta :=
            intervalIntegral.integral_comp_add_right (f := M) (-1)
      _ = ∫ beta in (-r)..(0 : ℝ), M beta := by congr 1 <;> ring
  have hsplit :
      (∫ beta in (0 : ℝ)..r, M beta) +
        ∫ beta in (-r)..(0 : ℝ), M beta =
          ∫ beta in (-r)..r, M beta := by
    rw [add_comm]
    exact intervalIntegral.integral_add_adjacent_intervals
      (hMcont.intervalIntegrable (-r) 0)
      (hMcont.intervalIntegrable 0 r)
  calc
    (∫ alpha in majorArcAt N Q 0 1, F alpha) =
        (∫ alpha in Set.Ico (0 : ℝ) r, F alpha) +
          ∫ alpha in Set.Ioc (1 - r) 1, F alpha := by
      rw [hdecomp]
      exact setIntegral_union hdisj measurableSet_Ioc hFintLow hFintHigh
    _ = ∫ beta in (-r)..r, M beta := by rw [hlow, hhigh, hsplit]
    _ = ∫ beta in Set.Icc (-r) r, M beta := by
      rw [intervalIntegral.integral_of_le (by linarith [hrnonneg]),
        ← integral_Icc_eq_integral_Ioc]
    _ = ∫ beta in Set.Icc (-((Q : ℝ) / (N : ℝ) ^ 3))
          ((Q : ℝ) / (N : ℝ) ^ 3),
          ‖cubicAllResidueHomogeneousModel 1 (0 : ZMod 1) beta N‖ ^ 32 := by
      simp [M, r, cubicArcRadius]

/-- The denominator-one wrapped moment inherits the same explicit constant
as its real-window estimate through the seam identity. -/
theorem integral_wrappedCubicAllResidueHomogeneousModel_pow32_le_zeroOne
    (N Q : ℕ) (C : ℝ)
    (hwindow :
      (∫ beta in Set.Icc (-((Q : ℝ) / (N : ℝ) ^ 3))
          ((Q : ℝ) / (N : ℝ) ^ 3),
          ‖cubicAllResidueHomogeneousModel 1 (0 : ZMod 1) beta N‖ ^ 32) ≤
        C ^ 32 / (1 : ℝ) ^ 3 * (N : ℝ) ^ 29 *
          ∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau)
    (hradius : cubicArcRadius N Q ≤ (1 / 2 : ℝ)) :
    (∫ alpha in majorArcAt N Q 0 1,
      ‖wrappedCubicAllResidueHomogeneousModel 1 (0 : ZMod 1) N alpha‖ ^ 32) ≤
        C ^ 32 / (1 : ℝ) ^ 3 * (N : ℝ) ^ 29 *
          ∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau := by
  rw [integral_wrappedCubicAllResidueHomogeneousModel_pow32_eq_zeroOneWindow
    N Q hradius]
  exact hwindow

/-- Auxiliary power-cutoff separation keeps the denominator-one radius
inside half the circle, as required by the seam split. -/
theorem cubicArcRadius_le_half_of_auxiliary_scale
    {N P : ℕ} (hscale : 2 * P ^ 3 ≤ N ^ 3) :
    cubicArcRadius N P ≤ (1 / 2 : ℝ) := by
  by_cases hN : 0 < N
  · by_cases hP : 0 < P
    · have hNcube : (0 : ℝ) < (N : ℝ) ^ 3 := by positivity
      have hscaleReal : 2 * (P : ℝ) ^ 3 ≤ (N : ℝ) ^ 3 := by
        exact_mod_cast hscale
      have hPone : (1 : ℝ) ≤ P := by exact_mod_cast hP
      have hPcube : (P : ℝ) ≤ (P : ℝ) ^ 3 := by
        have hfac : 0 ≤ ((P : ℝ) - 1) * ((P : ℝ) ^ 2 + P) :=
          mul_nonneg (sub_nonneg.mpr hPone) (by positivity)
        nlinarith
      have h2P : 2 * (P : ℝ) ≤ (N : ℝ) ^ 3 := by
        nlinarith
      unfold cubicArcRadius
      apply (div_le_iff₀ hNcube).2
      norm_num
      linarith
    · have hPzero : P = 0 := by omega
      simp [cubicArcRadius, hPzero]
  · have hNzero : N = 0 := by omega
    have hPzero : P = 0 := by
      by_contra hn
      have hp : 0 < P := Nat.pos_of_ne_zero hn
      subst hNzero
      simp at hscale
      omega
    simp [cubicArcRadius, hNzero, hPzero]

/-- Every admissible reduced center has the same explicit wrapped-model
moment constant, including the endpoint denominator `q=1`. -/
theorem integral_wrappedCubicAllResidueHomogeneousModel_pow32_le_auxiliaryCenter
    {N P a q : ℕ} [NeZero q] (C : ℝ)
    (hwindow : ∀ q a N P : ℕ, ∀ (hq : 0 < q)
      (_hac : Nat.Coprime a q) (_hN : 0 < N),
      letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
      (∫ beta in Set.Icc (-((P : ℝ) / (N : ℝ) ^ 3))
          ((P : ℝ) / (N : ℝ) ^ 3),
          ‖cubicAllResidueHomogeneousModel q (a : ZMod q) beta N‖ ^ 32) ≤
        C ^ 32 / (q : ℝ) ^ 3 * (N : ℝ) ^ 29 *
          ∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau)
    (hscale : 2 * P ^ 3 ≤ N ^ 3) (hN : 0 < N)
    (hq : 0 < q) (hqP : q ≤ P) (ha : a < q)
    (hac : Nat.Coprime a q) :
    (∫ alpha in majorArcAt N P a q,
      ‖wrappedCubicAllResidueHomogeneousModel q (a : ZMod q) N alpha‖ ^ 32) ≤
        C ^ 32 / (q : ℝ) ^ 3 * (N : ℝ) ^ 29 *
          ∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau := by
  by_cases hqone : q = 1
  · subst q
    have ha0 : a = 0 := by omega
    subst a
    have hwindowOne := hwindow 1 0 N P (by norm_num) (by decide) hN
    have hwindowOne' :
        (∫ beta in Set.Icc (-((P : ℝ) / (N : ℝ) ^ 3))
            ((P : ℝ) / (N : ℝ) ^ 3),
            ‖cubicAllResidueHomogeneousModel 1 (0 : ZMod 1) beta N‖ ^ 32) ≤
          C ^ 32 / (1 : ℝ) ^ 3 * (N : ℝ) ^ 29 *
            ∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau := by
      simpa using hwindowOne
    simpa using integral_wrappedCubicAllResidueHomogeneousModel_pow32_le_zeroOne
      N P C hwindowOne' (cubicArcRadius_le_half_of_auxiliary_scale hscale)
  · have hqgtone : 1 < q := by omega
    have hinterior := cubicAuxiliaryArc_interior_of_denominator_gt_one
      hscale hqP hq hqgtone ha hac
    exact integral_wrappedCubicAllResidueHomogeneousModel_pow32_le_of_interior
      q a N P C (hwindow q a N P hq hac hN) hN hq ha hac
      hinterior.1 hinterior.2

/-- Integrating the local approximation on one disjoint auxiliary major arc
costs only its model moment and its share of the uniform approximation error. -/
theorem integral_norm_cubicUnweightedExpSum_pow32_le_auxiliaryArc
    {N P a q : ℕ} [NeZero q] (C : ℝ)
    (hwindow : ∀ q a N P : ℕ, ∀ (hq : 0 < q)
      (_hac : Nat.Coprime a q) (_hN : 0 < N),
      letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
      (∫ beta in Set.Icc (-((P : ℝ) / (N : ℝ) ^ 3))
          ((P : ℝ) / (N : ℝ) ^ 3),
          ‖cubicAllResidueHomogeneousModel q (a : ZMod q) beta N‖ ^ 32) ≤
        C ^ 32 / (q : ℝ) ^ 3 * (N : ℝ) ^ 29 *
          ∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau)
    (hscale : 2 * P ^ 3 ≤ N ^ 3) (hN : 0 < N)
    (hq : 0 < q) (hqP : q ≤ P) (ha : a < q)
    (hac : Nat.Coprime a q) :
    (∫ alpha in majorArcAt N P a q,
      ‖cubicUnweightedExpSum alpha N‖ ^ 32) ≤
        2 ^ 31 *
          (C ^ 32 / (q : ℝ) ^ 3 * (N : ℝ) ^ 29 *
              (∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau) +
            volume.real (majorArcAt N P a q) *
              (64 * ((P : ℝ) + 1) ^ 2) ^ 32) := by
  let E : ℝ := 64 * ((P : ℝ) + 1) ^ 2
  let F : ℝ → ℝ := fun alpha => ‖cubicUnweightedExpSum alpha N‖ ^ 32
  let M : ℝ → ℝ := fun alpha =>
    ‖wrappedCubicAllResidueHomogeneousModel q (a : ZMod q) N alpha‖ ^ 32
  have hFcont : Continuous F := by
    dsimp [F]
    unfold cubicUnweightedExpSum addChar
    fun_prop
  have hlocalCont : Continuous
      (fun beta : ℝ => cubicAllResidueHomogeneousModel q (a : ZMod q) beta N) := by
    change Continuous (fun beta : ℝ =>
      (allResidueCubicExponentialSum q (a : ZMod q) *
        ((1 / (q : ℝ) : ℝ) : ℂ)) *
        ((N : ℝ) • oneDimensionalCubicIntegral (beta * (N : ℝ) ^ 3)))
    have hv : Continuous
        (fun beta : ℝ => oneDimensionalCubicIntegral (beta * (N : ℝ) ^ 3)) :=
      oneDimensionalCubicIntegral_continuous.comp
        (continuous_id.mul continuous_const)
    have hNcontinuous : Continuous (fun _ : ℝ => (N : ℝ)) := continuous_const
    have hscaled : Continuous
        (fun beta : ℝ => (N : ℝ) • oneDimensionalCubicIntegral
          (beta * (N : ℝ) ^ 3)) := hNcontinuous.smul hv
    exact continuous_const.mul hscaled
  have hMmeas : Measurable M := by
    dsimp [M]
    change Measurable (fun alpha : ℝ =>
      ‖cubicAllResidueHomogeneousModel q (a : ZMod q)
        (wrappedMajorArcDisplacement (a : ZMod q).val q alpha) N‖ ^ 32)
    exact (hlocalCont.norm.pow 32).measurable.comp
      (measurable_wrappedMajorArcDisplacement (a : ZMod q).val q)
  have hcoeff :
      ‖allResidueCubicExponentialSum q (a : ZMod q) *
        ((1 / (q : ℝ) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (q : ℝ))]
    calc
      ‖allResidueCubicExponentialSum q (a : ZMod q)‖ * (1 / (q : ℝ)) ≤
          (q : ℝ) * (1 / (q : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (norm_allResidueCubicExponentialSum_le q (a : ZMod q)) (by positivity)
      _ = 1 := by field_simp
  have hmodelBound (beta : ℝ) :
      ‖cubicAllResidueHomogeneousModel q (a : ZMod q) beta N‖ ≤ N := by
    rw [cubicAllResidueHomogeneousModel, norm_mul, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ))]
    calc
      ‖allResidueCubicExponentialSum q (a : ZMod q) *
          ((1 / (q : ℝ) : ℝ) : ℂ)‖ * ((N : ℝ) *
            ‖oneDimensionalCubicIntegral (beta * (N : ℝ) ^ 3)‖) ≤
          1 * ((N : ℝ) * 1) := by
        exact mul_le_mul hcoeff
          (mul_le_mul_of_nonneg_left
            (norm_oneDimensionalCubicIntegral_le_one _) (by positivity))
          (by positivity) (by positivity)
      _ = N := by norm_num
  have hMbound (alpha : ℝ) : ‖M alpha‖ ≤ (N : ℝ) ^ 32 := by
    change ‖‖wrappedCubicAllResidueHomogeneousModel q (a : ZMod q)
      N alpha‖ ^ 32‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) 32)]
    change ‖cubicAllResidueHomogeneousModel q (a : ZMod q)
      (wrappedMajorArcDisplacement (a : ZMod q).val q alpha) N‖ ^ 32 ≤ _
    exact pow_le_pow_left₀ (norm_nonneg _)
      (hmodelBound (wrappedMajorArcDisplacement (a : ZMod q).val q alpha)) 32
  have hfinite : volume (majorArcAt N P a q) ≠ ∞ := by
    apply ne_of_lt
    calc
      volume (majorArcAt N P a q) ≤ volume (Set.Icc (0 : ℝ) 1) :=
        measure_mono (majorArcAt_subset_Icc N P a q)
      _ < ∞ := by simp
  have hFint : IntegrableOn F (majorArcAt N P a q) :=
    (hFcont.integrableOn_Icc).mono_set (majorArcAt_subset_Icc N P a q)
  have hMint : IntegrableOn M (majorArcAt N P a q) :=
    volume.integrableOn_of_bounded hfinite hMmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hMbound)
  have hRint : IntegrableOn (fun alpha => M alpha + E ^ 32)
      (majorArcAt N P a q) := hMint.add
        (integrableOn_const hfinite)
  have hpoint : ∀ alpha ∈ majorArcAt N P a q,
      F alpha ≤ 2 ^ 31 * (M alpha + E ^ 32) := by
    intro alpha halpha
    have hdiff :=
      norm_cubicUnweightedExpSum_sub_wrappedCubicAllResidueHomogeneousModel_le_auxCutoff
        q a N P hq hN hqP ha halpha
    have htri : ‖cubicUnweightedExpSum alpha N‖ ≤
        ‖cubicUnweightedExpSum alpha N -
          wrappedCubicAllResidueHomogeneousModel q (a : ZMod q) N alpha‖ +
        ‖wrappedCubicAllResidueHomogeneousModel q (a : ZMod q) N alpha‖ := by
      calc
        ‖cubicUnweightedExpSum alpha N‖ =
            ‖(cubicUnweightedExpSum alpha N -
              wrappedCubicAllResidueHomogeneousModel q (a : ZMod q) N alpha) +
              wrappedCubicAllResidueHomogeneousModel q (a : ZMod q) N alpha‖ := by
                congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have htriPow := pow_le_pow_left₀ (norm_nonneg _)
      htri 32
    have hyoung :
        (‖cubicUnweightedExpSum alpha N -
          wrappedCubicAllResidueHomogeneousModel q (a : ZMod q) N alpha‖ +
          ‖wrappedCubicAllResidueHomogeneousModel q (a : ZMod q) N alpha‖) ^ 32 ≤
          2 ^ 31 *
            (‖cubicUnweightedExpSum alpha N -
                wrappedCubicAllResidueHomogeneousModel q (a : ZMod q) N alpha‖ ^ 32 +
              ‖wrappedCubicAllResidueHomogeneousModel q (a : ZMod q) N alpha‖ ^ 32) := by
      exact add_pow_le (norm_nonneg _) (norm_nonneg _) 32
    have herror :
        ‖cubicUnweightedExpSum alpha N -
          wrappedCubicAllResidueHomogeneousModel q (a : ZMod q) N alpha‖ ^ 32 ≤ E ^ 32 :=
      pow_le_pow_left₀ (norm_nonneg _)
        (by simpa [E] using hdiff) 32
    dsimp [F, M, E]
    calc
      ‖cubicUnweightedExpSum alpha N‖ ^ 32 ≤
          (‖cubicUnweightedExpSum alpha N -
            wrappedCubicAllResidueHomogeneousModel q (a : ZMod q) N alpha‖ +
            ‖wrappedCubicAllResidueHomogeneousModel q (a : ZMod q) N alpha‖) ^ 32 := htriPow
      _ ≤ 2 ^ 31 *
            (‖cubicUnweightedExpSum alpha N -
                wrappedCubicAllResidueHomogeneousModel q (a : ZMod q) N alpha‖ ^ 32 +
              ‖wrappedCubicAllResidueHomogeneousModel q (a : ZMod q) N alpha‖ ^ 32) := hyoung
      _ ≤ 2 ^ 31 *
            (E ^ 32 +
              ‖wrappedCubicAllResidueHomogeneousModel q (a : ZMod q) N alpha‖ ^ 32) :=
        mul_le_mul_of_nonneg_left (add_le_add herror le_rfl) (by positivity)
      _ = 2 ^ 31 *
            (‖wrappedCubicAllResidueHomogeneousModel q (a : ZMod q) N alpha‖ ^ 32 + E ^ 32) := by
        ring
  have hraw := integral_wrappedCubicAllResidueHomogeneousModel_pow32_le_auxiliaryCenter
    C hwindow hscale hN hq hqP ha hac
  let modelBound : ℝ := C ^ 32 / (q : ℝ) ^ 3 * (N : ℝ) ^ 29 *
    ∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau
  calc
    (∫ alpha in majorArcAt N P a q, F alpha) ≤
        ∫ alpha in majorArcAt N P a q, 2 ^ 31 * (M alpha + E ^ 32) :=
      setIntegral_mono_on hFint (hRint.const_mul (2 ^ 31 : ℝ))
        (majorArcAt_measurableSet N P a q) hpoint
    _ = 2 ^ 31 *
          ((∫ alpha in majorArcAt N P a q, M alpha) +
            volume.real (majorArcAt N P a q) * E ^ 32) := by
      rw [integral_const_mul,
        integral_add hMint (integrableOn_const hfinite)]
      simp only [integral_const, smul_eq_mul,
        MeasureTheory.measureReal_restrict_apply_univ]
    _ ≤ 2 ^ 31 *
          (modelBound +
            volume.real (majorArcAt N P a q) * E ^ 32) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hraw' :
          (∫ alpha in majorArcAt N P a q, M alpha) ≤
            modelBound := by
        simpa [modelBound, M] using hraw
      exact add_le_add hraw' le_rfl
    _ = 2 ^ 31 *
          (C ^ 32 / (q : ℝ) ^ 3 * (N : ℝ) ^ 29 *
              (∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau) +
            volume.real (majorArcAt N P a q) *
              (64 * ((P : ℝ) + 1) ^ 2) ^ 32) := by
      congr 1

/-- The elementary reciprocal-square partial sums are uniformly bounded by
two; this is the finite telescoping estimate used for the denominator sum. -/
theorem sum_one_div_natCast_sq_range_le_two (P : ℕ) :
    (∑ q ∈ Finset.range (P + 1), 1 / (q : ℝ) ^ 2) ≤ 2 := by
  have hstrong : ∀ n : ℕ,
      (∑ q ∈ Finset.range (n + 1), 1 / (q : ℝ) ^ 2) ≤
        if n = 0 then 2 else 2 - 1 / (n : ℝ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => norm_num
      | succ n =>
        by_cases hn : n = 0
        · subst n
          norm_num [Finset.sum_range_succ]
        · have hprev := ih n (by omega)
          have hprev' :
              (∑ q ∈ Finset.range (n + 1), 1 / (q : ℝ) ^ 2) ≤
                2 - 1 / (n : ℝ) := by
            simpa [hn] using hprev
          have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
          have hstep :
              1 / ((n : ℝ) + 1) ^ 2 ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
            field_simp
            nlinarith
          have hstep' :
              1 / ((n + 1 : ℕ) : ℝ) ^ 2 ≤
                1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
            simpa [Nat.cast_succ] using hstep
          rw [show Nat.succ n + 1 = (n + 1) + 1 by omega,
            Finset.sum_range_succ]
          calc
            _ ≤ (2 - 1 / (n : ℝ)) +
                (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) :=
                  add_le_add hprev' hstep'
            _ = 2 - 1 / ((n + 1 : ℕ) : ℝ) := by
              push_cast
              ring
  by_cases hP : P = 0
  · subst P
    norm_num
  · have h := hstrong P
    have h' :
        (∑ q ∈ Finset.range (P + 1), 1 / (q : ℝ) ^ 2) ≤
          2 - 1 / (P : ℝ) := by simpa [hP] using h
    have hnonneg : 0 ≤ 1 / (P : ℝ) := by positivity
    exact h'.trans (by linarith)

/-- All (not necessarily reduced) numerator/denominator pairs with
`a < q ≤ P`, grouped by their denominator. -/
def auxiliaryCenterTriangle (P : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (P + 1)).biUnion fun q =>
    (Finset.range q).image fun a => (a, q)

/-- The complete-sum coefficients over all reduced auxiliary centers have
bounded total mass. The numerator count at denominator `q` is at most `q`,
leaving the telescoping reciprocal-square series. -/
theorem sum_auxiliaryCenter_inverseCube_le_two (P : ℕ) :
    (∑ aq ∈ (majorArcCenters_finite P).toFinset,
      1 / (aq.2 : ℝ) ^ 3) ≤ 2 := by
  classical
  let centers := (majorArcCenters_finite P).toFinset
  let triangle := auxiliaryCenterTriangle P
  have hsubset : centers ⊆ triangle := by
    intro aq haq
    rcases aq with ⟨a, q⟩
    have hcenter : (a, q) ∈ majorArcCenters P := by simpa [centers] using haq
    rcases hcenter with ⟨hqP, hq0, ha, _hac⟩
    simp only [triangle, auxiliaryCenterTriangle, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_image]
    exact ⟨q, by omega, a, ha, rfl⟩
  have hdisj :
      Set.PairwiseDisjoint (↑(Finset.range (P + 1)) : Set ℕ)
        (fun q => (Finset.range q).image fun a => (a, q)) := by
    intro q hq q' hq' hne
    apply Finset.disjoint_left.mpr
    intro pair hpair hpair'
    rcases Finset.mem_image.mp hpair with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hpair' with ⟨a', ha', heq⟩
    have hqq : q = q' := by
      have := congrArg Prod.snd heq
      exact this.symm
    exact hne hqq
  have htriangleSum :
      (∑ aq ∈ triangle, 1 / (aq.2 : ℝ) ^ 3) =
        ∑ q ∈ Finset.range (P + 1),
          (q : ℝ) * (1 / (q : ℝ) ^ 3) := by
    rw [show triangle = auxiliaryCenterTriangle P by rfl,
      auxiliaryCenterTriangle, Finset.sum_biUnion hdisj]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_image]
    · simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    · intro a ha b hb hab
      exact congrArg Prod.fst hab
  have hcoef :
      ∀ q : ℕ, (q : ℝ) * (1 / (q : ℝ) ^ 3) = 1 / (q : ℝ) ^ 2 := by
    intro q
    by_cases hq : q = 0
    · simp [hq]
    · have hqpos : (0 : ℝ) < q := by exact_mod_cast (Nat.pos_of_ne_zero hq)
      field_simp
  calc
    (∑ aq ∈ centers, 1 / (aq.2 : ℝ) ^ 3) ≤
        ∑ aq ∈ triangle, 1 / (aq.2 : ℝ) ^ 3 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
          intro aq haq hnot
          positivity
    _ = ∑ q ∈ Finset.range (P + 1),
          (q : ℝ) * (1 / (q : ℝ) ^ 3) := htriangleSum
    _ = ∑ q ∈ Finset.range (P + 1), 1 / (q : ℝ) ^ 2 := by
          apply Finset.sum_congr rfl
          intro q hq
          exact hcoef q
    _ ≤ 2 := sum_one_div_natCast_sq_range_le_two P

/-- The complete major-arc integral is bounded by the summed model moments
and the summed local approximation errors. Pairwise disjointness is used only
to identify the integral over the union with the finite sum of arc integrals. -/
theorem integral_norm_cubicUnweightedExpSum_pow32_majorArcs_le
    (N P : ℕ) (C : ℝ)
    (hwindow : ∀ q a N P : ℕ, ∀ (hq : 0 < q)
      (_hac : Nat.Coprime a q) (_hN : 0 < N),
      letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
      (∫ beta in Set.Icc (-((P : ℝ) / (N : ℝ) ^ 3))
          ((P : ℝ) / (N : ℝ) ^ 3),
          ‖cubicAllResidueHomogeneousModel q (a : ZMod q) beta N‖ ^ 32) ≤
        C ^ 32 / (q : ℝ) ^ 3 * (N : ℝ) ^ 29 *
          ∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau)
    (hscale : 2 * P ^ 3 ≤ N ^ 3) (hN : 0 < N) :
    (∫ alpha in majorArcs N P,
      ‖cubicUnweightedExpSum alpha N‖ ^ 32) ≤
      2 ^ 31 *
        (2 * (C ^ 32 * (N : ℝ) ^ 29 *
            (∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau)) +
          ((P + 1 : ℕ) ^ 2 : ℝ) *
            (64 * ((P : ℝ) + 1) ^ 2) ^ 32) := by
  classical
  let centers := (majorArcCenters_finite P).toFinset
  let K : ℝ := C ^ 32 * (N : ℝ) ^ 29 *
    (∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau)
  let E : ℝ := 64 * ((P : ℝ) + 1) ^ 2
  let F : ℝ → ℝ := fun alpha => ‖cubicUnweightedExpSum alpha N‖ ^ 32
  have hFcont : Continuous F := by
    dsimp [F]
    unfold cubicUnweightedExpSum addChar
    fun_prop
  have hFint : IntegrableOn F (majorArcs N P) :=
    (hFcont.integrableOn_Icc).mono_set (majorArcs_subset_Icc N P)
  have hunion : majorArcs N P = ⋃ aq ∈ centers,
      majorArcAt N P aq.1 aq.2 := by
    rw [majorArcs_eq_iUnion_majorArcAt]
    simp only [centers, Set.Finite.mem_toFinset]
  have hpair : Set.Pairwise (↑centers : Set (ℕ × ℕ))
      (fun aq₁ aq₂ : ℕ × ℕ =>
        Disjoint (majorArcAt N P aq₁.1 aq₁.2)
          (majorArcAt N P aq₂.1 aq₂.2)) := by
    rintro ⟨a₁, q₁⟩ h₁ ⟨a₂, q₂⟩ h₂ hne
    apply majorArcAt_disjoint_of_distinct
    · simpa [centers] using h₁
    · simpa [centers] using h₂
    · exact hne
    · exact hscale
  have hdecomp :
      (∫ alpha in majorArcs N P, F alpha) =
        ∑ aq ∈ centers, ∫ alpha in majorArcAt N P aq.1 aq.2, F alpha := by
    rw [hunion]
    simpa only [centers] using
      MeasureTheory.integral_biUnion_finset centers
        (fun aq _ => majorArcAt_measurableSet N P aq.1 aq.2)
        hpair
        (fun aq _ =>
          (hFcont.integrableOn_Icc).mono_set
            (majorArcAt_subset_Icc N P aq.1 aq.2))
  have hI : 0 ≤ ∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau :=
    integral_nonneg cubicFrequencyNormPow32_nonneg
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hmodelSumEq :
      (∑ aq ∈ centers,
        C ^ 32 / (aq.2 : ℝ) ^ 3 * (N : ℝ) ^ 29 *
          (∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau)) =
        K * (∑ aq ∈ centers, 1 / (aq.2 : ℝ) ^ 3) := by
    calc
      _ = ∑ aq ∈ centers, K * (1 / (aq.2 : ℝ) ^ 3) := by
        apply Finset.sum_congr rfl
        intro aq haq
        have hmem : aq ∈ majorArcCenters P := by simpa [centers] using haq
        have hq0 : aq.2 ≠ 0 := hmem.2.1
        dsimp [K]
        field_simp
      _ = K * (∑ aq ∈ centers, 1 / (aq.2 : ℝ) ^ 3) := by
        rw [Finset.mul_sum]
  have hmodelSum :
      (∑ aq ∈ centers,
        C ^ 32 / (aq.2 : ℝ) ^ 3 * (N : ℝ) ^ 29 *
          (∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau)) ≤ 2 * K := by
    rw [hmodelSumEq]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left
        (sum_auxiliaryCenter_inverseCube_le_two P) hKnonneg
  have hEpos : 0 ≤ E ^ 32 := by positivity
  have hvol (aq : ℕ × ℕ) (haq : aq ∈ centers) :
      volume.real (majorArcAt N P aq.1 aq.2) ≤ 1 := by
    have hr := cubicArcRadius_le_half_of_auxiliary_scale hscale
    have hv := volume_real_majorArcAt_le_two_radius N P aq.1 aq.2
    unfold cubicArcRadius at hr hv
    nlinarith
  have herrorSum :
      (∑ aq ∈ centers,
        volume.real (majorArcAt N P aq.1 aq.2) * E ^ 32) ≤
        ((P + 1 : ℕ) ^ 2 : ℝ) * E ^ 32 := by
    calc
      _ ≤ ∑ _aq ∈ centers, 1 * E ^ 32 := by
        apply Finset.sum_le_sum
        intro aq haq
        exact mul_le_mul_of_nonneg_right (hvol aq haq) hEpos
      _ = (centers.card : ℝ) * E ^ 32 := by simp
      _ ≤ ((P + 1 : ℕ) ^ 2 : ℝ) * E ^ 32 := by
        apply mul_le_mul_of_nonneg_right _ hEpos
        exact_mod_cast majorArcCenters_card_le_square P
  have hsum :
      (∑ aq ∈ centers,
        ∫ alpha in majorArcAt N P aq.1 aq.2, F alpha) ≤
        2 ^ 31 *
          ((∑ aq ∈ centers,
              C ^ 32 / (aq.2 : ℝ) ^ 3 * (N : ℝ) ^ 29 *
                (∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau)) +
            (∑ aq ∈ centers,
              volume.real (majorArcAt N P aq.1 aq.2) * E ^ 32)) := by
    calc
      _ ≤ ∑ aq ∈ centers,
          2 ^ 31 *
            (C ^ 32 / (aq.2 : ℝ) ^ 3 * (N : ℝ) ^ 29 *
                (∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau) +
              volume.real (majorArcAt N P aq.1 aq.2) * E ^ 32) := by
        apply Finset.sum_le_sum
        intro aq haq
        have hmem : aq ∈ majorArcCenters P := by simpa [centers] using haq
        rcases hmem with ⟨hqP, hq0, ha, hac⟩
        letI : NeZero aq.2 := ⟨hq0⟩
        exact integral_norm_cubicUnweightedExpSum_pow32_le_auxiliaryArc
          C hwindow hscale hN (Nat.pos_of_ne_zero hq0) hqP ha hac
      _ = 2 ^ 31 *
          ((∑ aq ∈ centers,
              C ^ 32 / (aq.2 : ℝ) ^ 3 * (N : ℝ) ^ 29 *
                (∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau)) +
            (∑ aq ∈ centers,
              volume.real (majorArcAt N P aq.1 aq.2) * E ^ 32)) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  calc
    (∫ alpha in majorArcs N P, F alpha) =
        ∑ aq ∈ centers, ∫ alpha in majorArcAt N P aq.1 aq.2, F alpha := hdecomp
    _ ≤ 2 ^ 31 * (2 * K + ((P + 1 : ℕ) ^ 2 : ℝ) * E ^ 32) := by
      calc
        _ ≤ 2 ^ 31 *
            ((∑ aq ∈ centers,
                C ^ 32 / (aq.2 : ℝ) ^ 3 * (N : ℝ) ^ 29 *
                  (∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau)) +
              (∑ aq ∈ centers,
                volume.real (majorArcAt N P aq.1 aq.2) * E ^ 32)) := hsum
        _ ≤ 2 ^ 31 * (2 * K + ((P + 1 : ℕ) ^ 2 : ℝ) * E ^ 32) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact add_le_add hmodelSum herrorSum
    _ = 2 ^ 31 *
          (2 * (C ^ 32 * (N : ℝ) ^ 29 *
              (∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau)) +
            ((P + 1 : ℕ) ^ 2 : ℝ) *
              (64 * ((P : ℝ) + 1) ^ 2) ^ 32) := by
      simp [K, E]

set_option maxHeartbeats 500000 in
/-- The auxiliary major arcs contribute `O(N^29)` to the unweighted 32nd
moment, with one absolute constant independent of `N`. -/
theorem exists_uniform_integral_cubicUnweightedExpSum_pow32_auxiliaryMajor_le :
    ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, 8 ≤ N →
      (∫ alpha in majorArcs N (cubicAuxiliaryCutoff N),
        ‖cubicUnweightedExpSum alpha N‖ ^ 32) ≤ A * (N : ℝ) ^ 29 := by
  obtain ⟨C, hCpos, hbase⟩ :=
    exists_uniform_integral_norm_cubicAllResidueHomogeneousModel_pow32_le
  let A : ℝ := 2 ^ 31 *
    (2 * C ^ 32 * (∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau) +
      64 ^ 32 * 2 ^ 66)
  have hI0 : 0 ≤ ∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau :=
    integral_nonneg cubicFrequencyNormPow32_nonneg
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  refine ⟨A, hApos, fun N hN => ?_⟩
  let P := cubicAuxiliaryCutoff N
  have hNpos : 0 < N := by omega
  have hPcube : P ^ 3 ≤ N := by
    dsimp [P]
    exact cubicAuxiliaryCutoff_pow_le N
  have hPcubeReal : (P : ℝ) ^ 3 ≤ (N : ℝ) := by exact_mod_cast hPcube
  have hNreal : 8 ≤ (N : ℝ) := by exact_mod_cast hN
  have hNsq : 2 ≤ (N : ℝ) ^ 2 := by nlinarith
  have hNcubeLe : 2 * (N : ℝ) ≤ (N : ℝ) ^ 3 := by
    calc
      2 * (N : ℝ) ≤ (N : ℝ) ^ 2 * (N : ℝ) :=
        mul_le_mul_of_nonneg_right hNsq
          (show 0 ≤ (N : ℝ) by positivity)
      _ = (N : ℝ) * (N : ℝ) ^ 2 := by ring
      _ = (N : ℝ) ^ 3 := by ring
  have hscaleReal : 2 * (P : ℝ) ^ 3 ≤ (N : ℝ) ^ 3 := by
    calc
      2 * (P : ℝ) ^ 3 ≤ 2 * (N : ℝ) := by nlinarith
      _ ≤ (N : ℝ) ^ 3 := hNcubeLe
  have hscale : 2 * P ^ 3 ≤ N ^ 3 := by exact_mod_cast hscaleReal
  have hwindow : ∀ q a N' P' : ℕ, ∀ (hq : 0 < q)
      (hac : Nat.Coprime a q) (hN' : 0 < N'),
      letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
      (∫ beta in Set.Icc (-((P' : ℝ) / (N' : ℝ) ^ 3))
          ((P' : ℝ) / (N' : ℝ) ^ 3),
          ‖cubicAllResidueHomogeneousModel q (a : ZMod q) beta N'‖ ^ 32) ≤
        C ^ 32 / (q : ℝ) ^ 3 * (N' : ℝ) ^ 29 *
          ∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau := by
    intro q a N' P' hq hac hN'
    letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
    exact hbase q a N' P' hq hac hN'
  have hmajor := integral_norm_cubicUnweightedExpSum_pow32_majorArcs_le
    N P C hwindow hscale hNpos
  have hroot := cubicAuxiliaryCutoff_add_one_le_two_realRoot hNpos
  have hrootPow :
      (Real.rpow (N : ℝ) ((3 : ℝ)⁻¹)) ^ 66 = (N : ℝ) ^ 22 := by
    calc
      (Real.rpow (N : ℝ) ((3 : ℝ)⁻¹)) ^ 66 =
          Real.rpow (N : ℝ) (((3 : ℝ)⁻¹) * 66) :=
        (Real.rpow_mul_natCast (by positivity : 0 ≤ (N : ℝ))
          ((3 : ℝ)⁻¹) 66).symm
      _ = (N : ℝ) ^ 22 := by norm_num
  have hPplusPow :
      ((P : ℝ) + 1) ^ 66 ≤ 2 ^ 66 * (N : ℝ) ^ 22 := by
    calc
      ((P : ℝ) + 1) ^ 66 ≤
          (2 * Real.rpow (N : ℝ) ((3 : ℝ)⁻¹)) ^ 66 :=
        pow_le_pow_left₀ (by positivity) hroot 66
      _ = 2 ^ 66 * (N : ℝ) ^ 22 := by
        rw [mul_pow, hrootPow]
  have herror :
      ((P + 1 : ℕ) ^ 2 : ℝ) *
          (64 * ((P : ℝ) + 1) ^ 2) ^ 32 ≤
        64 ^ 32 * 2 ^ 66 * (N : ℝ) ^ 22 := by
    have hidentity :
        ((P + 1 : ℕ) ^ 2 : ℝ) *
            (64 * ((P : ℝ) + 1) ^ 2) ^ 32 =
          64 ^ 32 * ((P : ℝ) + 1) ^ 66 := by
      push_cast
      ring
    rw [hidentity]
    calc
      64 ^ 32 * ((P : ℝ) + 1) ^ 66 ≤
          64 ^ 32 * (2 ^ 66 * (N : ℝ) ^ 22) :=
        mul_le_mul_of_nonneg_left hPplusPow
          (show 0 ≤ (64 : ℝ) ^ 32 by positivity)
      _ = 64 ^ 32 * 2 ^ 66 * (N : ℝ) ^ 22 := by ring
  have hNone : 1 ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpower : (N : ℝ) ^ 22 ≤ (N : ℝ) ^ 29 := by
    calc
      (N : ℝ) ^ 22 = (N : ℝ) ^ 22 * 1 := by ring
      _ ≤ (N : ℝ) ^ 22 * (N : ℝ) ^ 7 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hNone) (by positivity)
      _ = (N : ℝ) ^ 29 := by rw [← pow_add]
  have hcoeff1 :
      0 ≤ 2 * C ^ 32 * (∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau) := by
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) hI0
  have hcoeff2 : 0 ≤ 64 ^ 32 * 2 ^ 66 := by positivity
  have hinside :
      2 * C ^ 32 * (N : ℝ) ^ 29 *
          (∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau) +
        ((P + 1 : ℕ) ^ 2 : ℝ) *
          (64 * ((P : ℝ) + 1) ^ 2) ^ 32 ≤
      (2 * C ^ 32 * (∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau) +
        64 ^ 32 * 2 ^ 66) * (N : ℝ) ^ 29 := by
    calc
      _ ≤ (2 * C ^ 32 * (∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau)) *
            (N : ℝ) ^ 29 + (64 ^ 32 * 2 ^ 66) * (N : ℝ) ^ 29 := by
        apply add_le_add
        · exact le_of_eq (by ring)
        · exact (herror.trans (mul_le_mul_of_nonneg_left hNpower
            (show 0 ≤ (64 : ℝ) ^ 32 * 2 ^ 66 by positivity)))
      _ = _ := by ring
  have hmajor' :
      (∫ alpha in majorArcs N (cubicAuxiliaryCutoff N),
        ‖cubicUnweightedExpSum alpha N‖ ^ 32) ≤
      2 ^ 31 *
        (2 * C ^ 32 * (N : ℝ) ^ 29 *
            (∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau) +
          ((P + 1 : ℕ) ^ 2 : ℝ) *
            (64 * ((P : ℝ) + 1) ^ 2) ^ 32) := by
    simpa [P, mul_assoc, mul_comm, mul_left_comm] using hmajor
  calc
    (∫ alpha in majorArcs N (cubicAuxiliaryCutoff N),
        ‖cubicUnweightedExpSum alpha N‖ ^ 32) ≤
      2 ^ 31 *
        (2 * C ^ 32 * (N : ℝ) ^ 29 *
            (∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau) +
          ((P + 1 : ℕ) ^ 2 : ℝ) *
            (64 * ((P : ℝ) + 1) ^ 2) ^ 32) := hmajor'
    _ ≤ (2 ^ 31 *
          (2 * C ^ 32 * (∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau) +
            64 ^ 32 * 2 ^ 66)) * (N : ℝ) ^ 29 := by
      calc
        _ ≤ 2 ^ 31 *
            ((2 * C ^ 32 * (∫ tau : ℝ, Internal.OrdinaryWeylMinorArcHelpers.cubicFrequencyNormPow32 tau) +
                64 ^ 32 * 2 ^ 66) * (N : ℝ) ^ 29) :=
          mul_le_mul_of_nonneg_left hinside
            (show 0 ≤ (2 : ℝ) ^ 31 by positivity)
        _ = _ := by ring
    _ = A * (N : ℝ) ^ 29 := by rfl

/-- A single absolute constant gives the `N^(15/16)` pointwise bound for
the unweighted cubic sum on every auxiliary minor arc. -/
theorem exists_uniform_norm_cubicUnweightedExpSum_le_auxiliaryMinor
    : ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (alpha : ℝ),
      8 ≤ N → alpha ∈ minorArcs N (cubicAuxiliaryCutoff N) →
      ‖cubicUnweightedExpSum alpha N‖ ≤
        A * Real.rpow (N : ℝ) (15 / 16 : ℝ) := by
  obtain ⟨K, hK, hweyl⟩ := exists_norm_cubicUnweightedExpSum_four_le_weyl
  let A : ℝ := 8 * K + 1
  have hApos : 0 < A := by dsimp [A]; positivity
  have hAone : 1 ≤ A := by dsimp [A]; linarith
  have hKleA : 8 * K ≤ A := by dsimp [A]; linarith
  have hA3 : 1 ≤ A ^ 3 := one_le_pow₀ hAone
  have hKleA4 : 8 * K ≤ A ^ 4 := by
    calc
      8 * K ≤ A := hKleA
      _ = A * 1 := by ring
      _ ≤ A * A ^ 3 := mul_le_mul_of_nonneg_left hA3 (le_of_lt hApos)
      _ = A ^ 4 := by ring
  refine ⟨A, hApos, fun N alpha hN hminor => ?_⟩
  obtain ⟨a, q, beta, hqP, hqBound, ha, hac, hbeta, hphase⟩ :=
    exists_weylData_of_mem_auxiliaryMinorArcs (by omega : 0 < N) hminor
  have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) hqP
  have hPpos : 0 < cubicAuxiliaryCutoff N :=
    cubicAuxiliaryCutoff_pos (by omega : 0 < N)
  have hqBoundCoarse : (q : ℝ) ≤ 3 * (N : ℝ) ^ 3 := by
    have hPone : (1 : ℝ) ≤ cubicAuxiliaryCutoff N := by
      exact_mod_cast hPpos
    have hdiv : (N : ℝ) ^ 3 / (cubicAuxiliaryCutoff N : ℝ) ≤
        (N : ℝ) ^ 3 := div_le_self (by positivity) hPone
    have hmul := mul_le_mul_of_nonneg_left hdiv
      (by norm_num : (0 : ℝ) ≤ 3)
    calc
      (q : ℝ) ≤ 3 * (N : ℝ) ^ 3 /
          (cubicAuxiliaryCutoff N : ℝ) := hqBound
      _ = 3 * ((N : ℝ) ^ 3 / (cubicAuxiliaryCutoff N : ℝ)) := by ring
      _ ≤ 3 * (N : ℝ) ^ 3 := hmul
  have hqmax : q ≤ 3 * N ^ 3 := by exact_mod_cast hqBoundCoarse
  have hfour := hweyl (rationalCenter a q + beta) N a q beta
    hN hq hqmax hac rfl hbeta
  have hfactor := auxiliaryMinorWeylFactor_le hN hqP hqBound
  let x : ℝ := N
  let t : ℝ := Real.rpow x (15 / 16 : ℝ)
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hrroot : Real.rpow x ((3 : ℝ)⁻¹) =
      Real.rpow (N : ℝ) ((3 : ℝ)⁻¹) := by rfl
  have hshape : Real.rpow (N : ℝ) (4 + 1 / 12 : ℝ) /
        Real.rpow (N : ℝ) ((3 : ℝ)⁻¹) =
      Real.rpow (N : ℝ) (15 / 4 : ℝ) := by
    calc
      _ = Real.rpow (N : ℝ)
          ((4 + 1 / 12 : ℝ) - (3 : ℝ)⁻¹) := by
            exact (Real.rpow_sub (by positivity : 0 < (N : ℝ))
              (4 + 1 / 12 : ℝ) ((3 : ℝ)⁻¹)).symm
      _ = Real.rpow (N : ℝ) (15 / 4 : ℝ) := by
        congr 1
        norm_num
  have hfour' :
      ‖cubicUnweightedExpSum (rationalCenter a q + beta) N‖ ^ 4 ≤
        8 * K * Real.rpow (N : ℝ) (15 / 4 : ℝ) := by
    calc
      _ ≤ K * Real.rpow (N : ℝ) (4 + 1 / 12 : ℝ) *
          (1 / (q : ℝ) + 1 / (N : ℝ) + (q : ℝ) / (N : ℝ) ^ 3) := hfour
      _ ≤ K * Real.rpow (N : ℝ) (4 + 1 / 12 : ℝ) *
          (8 / Real.rpow (N : ℝ) ((3 : ℝ)⁻¹)) := by
            exact mul_le_mul_of_nonneg_left hfactor
              (mul_nonneg hK.le
                (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ)) _))
      _ = 8 * K * Real.rpow (N : ℝ) (15 / 4 : ℝ) := by
            calc
              _ = 8 * K *
                  (Real.rpow (N : ℝ) (4 + 1 / 12 : ℝ) /
                    Real.rpow (N : ℝ) ((3 : ℝ)⁻¹)) := by ring
              _ = 8 * K * Real.rpow (N : ℝ) (15 / 4 : ℝ) := by rw [hshape]
  have ht4 : t ^ 4 = Real.rpow (N : ℝ) (15 / 4 : ℝ) := by
    dsimp [t, x]
    rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ (N : ℝ))
      (15 / 16 : ℝ) 4]
    congr 1
    norm_num
  have hfourA :
      ‖cubicUnweightedExpSum (rationalCenter a q + beta) N‖ ^ 4 ≤
        (A * t) ^ 4 := by
    rw [show (A * t) ^ 4 = A ^ 4 * t ^ 4 by ring, ht4]
    exact hfour'.trans (mul_le_mul_of_nonneg_right hKleA4
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ)) _))
  have hpoint :
      ‖cubicUnweightedExpSum (rationalCenter a q + beta) N‖ ≤ A * t := by
    by_contra hnot
    have hlt : A * t < ‖cubicUnweightedExpSum (rationalCenter a q + beta) N‖ :=
      lt_of_not_ge hnot
    have hATnonneg : 0 ≤ A * t :=
      mul_nonneg hApos.le (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ x) _)
    have hnormpos :
        0 < ‖cubicUnweightedExpSum (rationalCenter a q + beta) N‖ :=
      lt_of_le_of_lt hATnonneg hlt
    have hpositive :
        0 < (‖cubicUnweightedExpSum (rationalCenter a q + beta) N‖ - A * t) *
          (‖cubicUnweightedExpSum (rationalCenter a q + beta) N‖ + A * t) *
          (‖cubicUnweightedExpSum (rationalCenter a q + beta) N‖ ^ 2 +
            (A * t) ^ 2) := by positivity
    have hfactorization :
        ‖cubicUnweightedExpSum (rationalCenter a q + beta) N‖ ^ 4 -
            (A * t) ^ 4 =
          (‖cubicUnweightedExpSum (rationalCenter a q + beta) N‖ - A * t) *
            (‖cubicUnweightedExpSum (rationalCenter a q + beta) N‖ + A * t) *
            (‖cubicUnweightedExpSum (rationalCenter a q + beta) N‖ ^ 2 +
              (A * t) ^ 2) := by ring
    nlinarith [hfourA, hpositive, hfactorization]
  rw [hphase]
  simpa [t, x] using hpoint

/-- The auxiliary minor-arc contribution to the unweighted 32nd moment is
`O((N+1)^29)`, by the pointwise Weyl saving and the exact eighth moment. -/
theorem exists_uniform_integral_cubicUnweightedExpSum_pow32_auxiliaryMinor_le
    : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 8 ≤ N →
      (∫ alpha in minorArcs N (cubicAuxiliaryCutoff N),
        ‖cubicUnweightedExpSum alpha N‖ ^ 32) ≤
        C * Real.rpow (N + 1 : ℝ) 29 := by
  obtain ⟨A, hA, hminor⟩ :=
    exists_uniform_norm_cubicUnweightedExpSum_le_auxiliaryMinor
  obtain ⟨D, hD, hcount⟩ :=
    exists_cubicEighthSolutionCount_rpow_five_bound
      (ε := (1 / 4 : ℝ)) (by norm_num)
  have hC : 0 < A ^ 24 * D := by positivity
  refine ⟨A ^ 24 * D, hC, fun N hN => ?_⟩
  let X : ℝ := N + 1
  have hXone : 1 ≤ X := by dsimp [X]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hXone
  let B : ℝ := A ^ 24 * Real.rpow X (45 / 2 : ℝ)
  have hBnonneg : 0 ≤ B := by dsimp [B]; positivity
  have hcont : Continuous
      (fun alpha : ℝ => ‖cubicUnweightedExpSum alpha N‖ ^ 32) := by
    unfold cubicUnweightedExpSum addChar
    fun_prop
  have hcont8 : Continuous
      (fun alpha : ℝ => ‖cubicUnweightedExpSum alpha N‖ ^ 8) := by
    unfold cubicUnweightedExpSum addChar
    fun_prop
  have hminorInt : IntegrableOn
      (fun alpha : ℝ => ‖cubicUnweightedExpSum alpha N‖ ^ 32)
      (minorArcs N (cubicAuxiliaryCutoff N)) :=
    (hcont.integrableOn_Icc).mono_set (minorArcs_subset_Icc N _)
  have hmajorInt : IntegrableOn
      (fun alpha : ℝ => B * ‖cubicUnweightedExpSum alpha N‖ ^ 8)
      (Set.Icc (0 : ℝ) 1) := by
    apply Continuous.integrableOn_Icc
    exact continuous_const.mul hcont8
  have hpoint : ∀ alpha ∈ minorArcs N (cubicAuxiliaryCutoff N),
      ‖cubicUnweightedExpSum alpha N‖ ^ 32 ≤
        B * ‖cubicUnweightedExpSum alpha N‖ ^ 8 := by
    intro alpha halpha
    have hs := hminor N alpha hN halpha
    let t : ℝ := Real.rpow (N : ℝ) (15 / 16 : ℝ)
    have ht24 : t ^ 24 = Real.rpow (N : ℝ) (45 / 2 : ℝ) := by
      dsimp [t]
      rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ (N : ℝ))
        (15 / 16 : ℝ) 24]
      congr 1
      norm_num
    have hNleX : (N : ℝ) ≤ X := by
      dsimp [X]
      exact_mod_cast Nat.le_succ N
    have hM24 : (A * t) ^ 24 ≤ B := by
      rw [mul_pow, ht24]
      dsimp [B]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hNleX (by norm_num))
        (by positivity)
    calc
      ‖cubicUnweightedExpSum alpha N‖ ^ 32 =
          ‖cubicUnweightedExpSum alpha N‖ ^ 24 *
            ‖cubicUnweightedExpSum alpha N‖ ^ 8 := by ring
      _ ≤ (A * t) ^ 24 *
            ‖cubicUnweightedExpSum alpha N‖ ^ 8 := by
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (norm_nonneg _) hs 24) (by positivity)
      _ ≤ B * ‖cubicUnweightedExpSum alpha N‖ ^ 8 :=
          mul_le_mul_of_nonneg_right hM24 (by positivity)
  have hminorToMajor :
      (∫ alpha in minorArcs N (cubicAuxiliaryCutoff N),
        ‖cubicUnweightedExpSum alpha N‖ ^ 32) ≤
      B * (∫ alpha in Set.Icc (0 : ℝ) 1,
        ‖cubicUnweightedExpSum alpha N‖ ^ 8) := by
    calc
      _ ≤ ∫ alpha in minorArcs N (cubicAuxiliaryCutoff N),
          B * ‖cubicUnweightedExpSum alpha N‖ ^ 8 :=
            setIntegral_mono_on hminorInt
              (hmajorInt.mono_set (minorArcs_subset_Icc N _))
              (minorArcs_measurableSet N _) hpoint
      _ ≤ ∫ alpha in Set.Icc (0 : ℝ) 1,
          B * ‖cubicUnweightedExpSum alpha N‖ ^ 8 := by
            apply setIntegral_mono_set hmajorInt
            · exact Eventually.of_forall (fun alpha => by positivity)
            · exact Eventually.of_forall (minorArcs_subset_Icc N _)
      _ = B * (∫ alpha in Set.Icc (0 : ℝ) 1,
          ‖cubicUnweightedExpSum alpha N‖ ^ 8) := by
            rw [integral_const_mul]
  have hI8 :
      (∫ alpha in Set.Icc (0 : ℝ) 1,
        ‖cubicUnweightedExpSum alpha N‖ ^ 8) ≤
          D * Real.rpow X (5 + 1 / 4 : ℝ) := by
    rw [integral_norm_cubicUnweightedExpSum_pow_eight]
    simpa [X] using hcount N
  calc
    (∫ alpha in minorArcs N (cubicAuxiliaryCutoff N),
        ‖cubicUnweightedExpSum alpha N‖ ^ 32) ≤
      B * (∫ alpha in Set.Icc (0 : ℝ) 1,
        ‖cubicUnweightedExpSum alpha N‖ ^ 8) := hminorToMajor
    _ ≤ B * (D * Real.rpow X (5 + 1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hI8 hBnonneg
    _ = A ^ 24 * D * Real.rpow X (111 / 4 : ℝ) := by
      dsimp [B]
      calc
        A ^ 24 * Real.rpow X (45 / 2 : ℝ) *
            (D * Real.rpow X (5 + 1 / 4 : ℝ)) =
          A ^ 24 * D *
            (Real.rpow X (45 / 2 : ℝ) * Real.rpow X (5 + 1 / 4 : ℝ)) := by ring
        _ = A ^ 24 * D * Real.rpow X
              ((45 / 2 : ℝ) + (5 + 1 / 4 : ℝ)) := by
                exact congrArg (fun z : ℝ => A ^ 24 * D * z)
                  (Real.rpow_add hXpos (45 / 2 : ℝ) (5 + 1 / 4 : ℝ)).symm
        _ = A ^ 24 * D * Real.rpow X (111 / 4 : ℝ) := by
          congr 1
          norm_num
    _ ≤ A ^ 24 * D * Real.rpow X 29 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hXone (by norm_num)
      

/-! ## Completion of the auxiliary unweighted moment -/

/-- The full unweighted cubic exponential sum has the auxiliary 32nd-moment
bound `O(N^29)`. -/
theorem exists_uniform_integral_cubicUnweightedExpSum_pow32_le :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 8 ≤ N →
      (∫ alpha in Set.Icc (0 : ℝ) 1,
        ‖cubicUnweightedExpSum alpha N‖ ^ 32) ≤ C * (N : ℝ) ^ 29 := by
  obtain ⟨A, hApos, hmajor⟩ :=
    exists_uniform_integral_cubicUnweightedExpSum_pow32_auxiliaryMajor_le
  obtain ⟨B, hBpos, hminor⟩ :=
    exists_uniform_integral_cubicUnweightedExpSum_pow32_auxiliaryMinor_le
  let C : ℝ := A + B * 2 ^ 29
  have hCpos : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hCpos, fun N hN => ?_⟩
  let Q := cubicAuxiliaryCutoff N
  have hcont : Continuous
      (fun alpha : ℝ => ‖cubicUnweightedExpSum alpha N‖ ^ 32) := by
    unfold cubicUnweightedExpSum addChar
    fun_prop
  have hfullInt : IntegrableOn
      (fun alpha : ℝ => ‖cubicUnweightedExpSum alpha N‖ ^ 32)
      (Set.Icc (0 : ℝ) 1) := hcont.integrableOn_Icc
  have hmajorInt := hfullInt.mono_set (majorArcs_subset_Icc N Q)
  have hminorInt := hfullInt.mono_set (minorArcs_subset_Icc N Q)
  have hdecomp :
      (∫ alpha in Set.Icc (0 : ℝ) 1,
        ‖cubicUnweightedExpSum alpha N‖ ^ 32) =
        (∫ alpha in majorArcs N Q,
          ‖cubicUnweightedExpSum alpha N‖ ^ 32) +
        (∫ alpha in minorArcs N Q,
          ‖cubicUnweightedExpSum alpha N‖ ^ 32) := by
    rw [← majorArcs_union_minorArcs N Q]
    rw [setIntegral_union (majorArcs_disjoint_minorArcs N Q)
      (minorArcs_measurableSet N Q) hmajorInt hminorInt]
  have hXpow : Real.rpow (N + 1 : ℝ) 29 ≤ 2 ^ 29 * (N : ℝ) ^ 29 := by
    have hNreal : 8 ≤ (N : ℝ) := by exact_mod_cast hN
    have hplus : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by nlinarith
    calc
      Real.rpow (N + 1 : ℝ) 29 = ((N : ℝ) + 1) ^ 29 :=
        Real.rpow_natCast ((N : ℝ) + 1) 29
      _ ≤ (2 * (N : ℝ)) ^ 29 := pow_le_pow_left₀ (by positivity) hplus 29
      _ = 2 ^ 29 * (N : ℝ) ^ 29 := by ring
  have hminorBound :
      (∫ alpha in minorArcs N Q,
        ‖cubicUnweightedExpSum alpha N‖ ^ 32) ≤
          B * 2 ^ 29 * (N : ℝ) ^ 29 := by
    calc
      _ ≤ B * Real.rpow (N + 1 : ℝ) 29 := hminor N hN
      _ ≤ B * (2 ^ 29 * (N : ℝ) ^ 29) :=
        mul_le_mul_of_nonneg_left hXpow hBpos.le
      _ = B * 2 ^ 29 * (N : ℝ) ^ 29 := by ring
  calc
    (∫ alpha in Set.Icc (0 : ℝ) 1,
        ‖cubicUnweightedExpSum alpha N‖ ^ 32) =
        (∫ alpha in majorArcs N Q,
          ‖cubicUnweightedExpSum alpha N‖ ^ 32) +
        (∫ alpha in minorArcs N Q,
          ‖cubicUnweightedExpSum alpha N‖ ^ 32) := hdecomp
    _ ≤ A * (N : ℝ) ^ 29 + B * 2 ^ 29 * (N : ℝ) ^ 29 :=
      add_le_add (hmajor N hN) hminorBound
    _ = C * (N : ℝ) ^ 29 := by ring

/-- Integrated sixteen-tuple orthogonality transfers the full unweighted
32nd-moment bound to the von Mangoldt-weighted exponential sum. -/
theorem exists_uniform_integral_cubicVonMangoldtExpSum_pow32_le_auxiliary :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 8 ≤ N →
      (∫ alpha in Set.Icc (0 : ℝ) 1,
        ‖cubicVonMangoldtExpSum alpha N‖ ^ 32) ≤
          C * Real.log (N + 1 : ℝ) ^ 32 * (N : ℝ) ^ 29 := by
  obtain ⟨C, hCpos, hunweighted⟩ :=
    exists_uniform_integral_cubicUnweightedExpSum_pow32_le
  refine ⟨C, hCpos, fun N hN => ?_⟩
  have hlog : 0 ≤ Real.log (N + 1 : ℝ) ^ 32 :=
    pow_nonneg (log_succ_nonneg N) 32
  calc
    (∫ alpha in Set.Icc (0 : ℝ) 1,
        ‖cubicVonMangoldtExpSum alpha N‖ ^ 32) ≤
      Real.log (N + 1 : ℝ) ^ 32 *
        (∫ alpha in Set.Icc (0 : ℝ) 1,
          ‖cubicUnweightedExpSum alpha N‖ ^ 32) :=
      integral_norm_cubicVonMangoldtExpSum_pow_thirtyTwo_le N
    _ ≤ Real.log (N + 1 : ℝ) ^ 32 * (C * (N : ℝ) ^ 29) :=
      mul_le_mul_of_nonneg_left (hunweighted N hN) hlog
    _ = C * Real.log (N + 1 : ℝ) ^ 32 * (N : ℝ) ^ 29 := by ring

end CookMagyarCircle
end SystolicGrowth

#print axioms SystolicGrowth.CookMagyarCircle.auxiliaryMinorWeylFactor_le
#print axioms SystolicGrowth.CookMagyarCircle.cubicUnweightedExpSum_rationalCenter_eq_allResidue
#print axioms SystolicGrowth.CookMagyarCircle.exists_uniform_norm_allResidueCubicExponentialSum_le
#print axioms SystolicGrowth.CookMagyarCircle.exists_uniform_norm_allResidueCoefficient_pow32_le
#print axioms SystolicGrowth.CookMagyarCircle.exists_uniform_integral_norm_cubicAllResidueHomogeneousModel_pow32_le
#print axioms SystolicGrowth.CookMagyarCircle.wrappedCubicAllResidueHomogeneousModel_add_int
#print axioms SystolicGrowth.CookMagyarCircle.norm_cubicUnweightedExpSum_sub_wrappedCubicAllResidueHomogeneousModel_le_auxCutoff
#print axioms SystolicGrowth.CookMagyarCircle.integral_wrappedCubicAllResidueHomogeneousModel_pow32_le_of_interior
#print axioms SystolicGrowth.CookMagyarCircle.exists_uniform_integral_wrappedCubicAllResidueHomogeneousModel_pow32_le_of_interior
#print axioms SystolicGrowth.CookMagyarCircle.cubicAuxiliaryArc_interior_of_denominator_gt_one
#print axioms SystolicGrowth.CookMagyarCircle.integral_wrappedCubicAllResidueHomogeneousModel_pow32_eq_zeroOneWindow
#print axioms SystolicGrowth.CookMagyarCircle.integral_wrappedCubicAllResidueHomogeneousModel_pow32_le_zeroOne
#print axioms SystolicGrowth.CookMagyarCircle.cubicArcRadius_le_half_of_auxiliary_scale
#print axioms SystolicGrowth.CookMagyarCircle.integral_wrappedCubicAllResidueHomogeneousModel_pow32_le_auxiliaryCenter
#print axioms SystolicGrowth.CookMagyarCircle.integral_norm_cubicUnweightedExpSum_pow32_le_auxiliaryArc
#print axioms SystolicGrowth.CookMagyarCircle.sum_one_div_natCast_sq_range_le_two
#print axioms SystolicGrowth.CookMagyarCircle.sum_auxiliaryCenter_inverseCube_le_two
#print axioms SystolicGrowth.CookMagyarCircle.integral_norm_cubicUnweightedExpSum_pow32_majorArcs_le
#print axioms SystolicGrowth.CookMagyarCircle.exists_uniform_integral_cubicUnweightedExpSum_pow32_auxiliaryMajor_le
#print axioms SystolicGrowth.CookMagyarCircle.exists_uniform_integral_cubicUnweightedExpSum_pow32_le
#print axioms SystolicGrowth.CookMagyarCircle.exists_uniform_integral_cubicVonMangoldtExpSum_pow32_le_auxiliary
#print axioms SystolicGrowth.CookMagyarCircle.exists_uniform_norm_cubicUnweightedExpSum_le_auxiliaryMinor
#print axioms SystolicGrowth.CookMagyarCircle.exists_uniform_integral_cubicUnweightedExpSum_pow32_auxiliaryMinor_le
