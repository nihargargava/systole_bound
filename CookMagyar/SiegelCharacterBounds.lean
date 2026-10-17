module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.SumCoeff

@[expose] public section

/-!
# Bounded summatory functions of nonprincipal characters

These are the actual character-sum inputs for the partial-summation bounds
in the Siegel argument. Complete periods cancel; arbitrary prefixes therefore
have norm at most the modulus. No growth estimate is assumed.
-/

open Finset Filter MeasureTheory Topology Asymptotics

namespace SystolicGrowth.CookMagyarCircle

variable {q : ℕ} [NeZero q]

/-- A complete period of a nonprincipal character sums to zero. -/
theorem siegel_character_sum_period (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∑ n ∈ range q, χ (n : ZMod q) = 0 := by
  calc
    ∑ n ∈ range q, χ (n : ZMod q) = ∑ r : ZMod q, χ r := by
      apply sum_bij (s := range q) (t := univ)
        (f := fun n : ℕ => χ (n : ZMod q)) (g := fun r : ZMod q => χ r)
        (fun n _ => (n : ZMod q))
      · intro n hn
        exact mem_univ _
      · intro a ha b hb hab
        have hval := congrArg ZMod.val hab
        simpa only [ZMod.val_natCast_of_lt (mem_range.mp ha),
          ZMod.val_natCast_of_lt (mem_range.mp hb)] using hval
      · intro r _
        exact ⟨r.val, mem_range.mpr (ZMod.val_lt r), ZMod.natCast_zmod_val r⟩
      · intro n hn
        rfl
    _ = 0 := χ.sum_eq_zero_of_ne_one hχ

/-- Adding one full period does not change a prefix sum. -/
theorem siegel_character_sum_range_add_period
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ∑ n ∈ range (q + N), χ (n : ZMod q) =
      ∑ n ∈ range N, χ (n : ZMod q) := by
  rw [sum_range_add, siegel_character_sum_period χ hχ, zero_add]
  apply sum_congr rfl
  intro n hn
  simp

/-- A prefix equals the prefix of its remainder modulo the conductor. -/
theorem siegel_character_sum_range_mod
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ∑ n ∈ range N, χ (n : ZMod q) =
      ∑ n ∈ range (N % q), χ (n : ZMod q) := by
  have hblocks (k r : ℕ) :
      ∑ n ∈ range (q * k + r), χ (n : ZMod q) =
        ∑ n ∈ range r, χ (n : ZMod q) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show q * (k + 1) + r = q + (q * k + r) by ring,
        siegel_character_sum_range_add_period χ hχ, ih]
  simpa only [Nat.div_add_mod] using hblocks (N / q) (N % q)

/-- The elementary uniform bound on every nonprincipal character prefix. -/
theorem siegel_character_sum_range_norm_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ range N, χ (n : ZMod q)‖ ≤ (q : ℝ) := by
  rw [siegel_character_sum_range_mod χ hχ]
  calc
    ‖∑ n ∈ range (N % q), χ (n : ZMod q)‖ ≤
        ∑ n ∈ range (N % q), ‖χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ range (N % q), (1 : ℝ) :=
      sum_le_sum fun n _ => χ.norm_le_one n
    _ = ((N % q : ℕ) : ℝ) := by simp
    _ ≤ (q : ℝ) := by exact_mod_cast (Nat.mod_lt N (NeZero.pos q)).le

/-- The bound in the `Icc 1 N` convention used by Abel summation. -/
theorem siegel_character_sum_Icc_norm_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, χ (n : ZMod q)‖ ≤ (q : ℝ) := by
  have hq : q ≠ 1 := by
    intro hq
    subst q
    exact hχ (Subsingleton.elim _ _)
  have hzero := χ.map_zero' hq
  have hsum : ∑ n ∈ Icc 1 N, χ (n : ZMod q) =
      ∑ n ∈ range (N + 1), χ (n : ZMod q) := by
    induction N with
    | zero => simp [hzero]
    | succ N ih =>
      rw [sum_Icc_succ_top (by omega), sum_range_succ, ih]
  rw [hsum]
  exact siegel_character_sum_range_norm_le χ hχ (N + 1)

/-- The summatory step function used in the analytic continuation. -/
noncomputable def siegelCharacterSummatory (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊t⌋₊, χ (n : ZMod q)

theorem siegelCharacterSummatory_norm_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) :
    ‖siegelCharacterSummatory χ t‖ ≤ (q : ℝ) :=
  siegel_character_sum_Icc_norm_le χ hχ ⌊t⌋₊

theorem siegel_character_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    χ 0 = 0 := by
  apply χ.map_zero'
  intro hq
  subst q
  exact hχ (Subsingleton.elim _ _)

/-- At the full-period cutoff the Abel boundary term is exactly zero. -/
theorem siegelCharacterSummatory_modulus (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    siegelCharacterSummatory χ q = 0 := by
  have hzero := siegel_character_zero χ hχ
  unfold siegelCharacterSummatory
  rw [Nat.floor_natCast]
  have hsum : ∑ n ∈ Icc 1 q, χ (n : ZMod q) =
      ∑ n ∈ range (q + 1), χ (n : ZMod q) := by
    rw [Nat.range_succ_eq_Icc_zero, ← insert_Icc_add_one_left_eq_Icc q.zero_le,
      sum_insert (by simp), Nat.cast_zero, hzero, zero_add]
    rfl
  rw [hsum, sum_range_succ, siegel_character_sum_period χ hχ]
  simpa using hzero

omit [NeZero q] in
theorem siegelCharacterSummatory_eq_zero_of_lt_one
    (χ : DirichletCharacter ℂ q) {t : ℝ} (ht : t < 1) :
    siegelCharacterSummatory χ t = 0 := by
  simp [siegelCharacterSummatory, Nat.floor_eq_zero.mpr ht]

omit [NeZero q] in
theorem siegelCharacterSummatory_locallyIntegrableOn
    (χ : DirichletCharacter ℂ q) :
    LocallyIntegrableOn (siegelCharacterSummatory χ) (Set.Ioi 0) := by
  have h := locallyIntegrableOn_mul_sum_Icc (fun n : ℕ => χ (n : ZMod q))
    (m := 1) (a := 0) le_rfl (locallyIntegrableOn_const (1 : ℂ))
  unfold siegelCharacterSummatory
  simpa only [one_mul] using h.mono_set Set.Ioi_subset_Ici_self

theorem siegelCharacterSummatory_isBigO_atTop
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    siegelCharacterSummatory χ =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  refine isBigO_iff.mpr ⟨q, Eventually.of_forall fun t => ?_⟩
  simpa using siegelCharacterSummatory_norm_le χ hχ t

omit [NeZero q] in
theorem siegelCharacterSummatory_isBigO_zero
    (χ : DirichletCharacter ℂ q) (b : ℝ) :
    siegelCharacterSummatory χ =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
  refine (isBigO_zero (fun t : ℝ => t ^ (-b)) (𝓝[>] 0)).congr' ?_ EventuallyEq.rfl
  have ht : ∀ᶠ t : ℝ in 𝓝 0, t < 1 := Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)
  filter_upwards [ht.filter_mono nhdsWithin_le_nhds] with t ht
  exact (siegelCharacterSummatory_eq_zero_of_lt_one χ ht).symm

/-- The Abel integral is holomorphic on the entire right half-plane, not
just the domain of absolute convergence of the Dirichlet series. -/
noncomputable def siegelCharacterAbel (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  s * mellin (siegelCharacterSummatory χ) (-s)

theorem siegelCharacterAbel_differentiableAt
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (siegelCharacterAbel χ) s := by
  have hm := mellin_differentiableAt_of_isBigO_rpow
    (siegelCharacterSummatory_locallyIntegrableOn χ)
    (siegelCharacterSummatory_isBigO_atTop χ hχ)
    (show (-s).re < 0 by simpa using neg_neg_of_pos hs)
    (siegelCharacterSummatory_isBigO_zero χ (-s.re - 1))
    (show -s.re - 1 < (-s).re by simp)
  exact differentiableAt_id.mul (hm.comp s differentiableAt_id.neg)

omit [NeZero q] in
/-- Changing the Mellin domain to `(1, ∞)` only removes a zero integrand
and a null endpoint. This holds without a convergence assumption. -/
theorem siegelCharacterAbel_eq_integral
    (χ : DirichletCharacter ℂ q) (s : ℂ) :
    siegelCharacterAbel χ s =
      s * ∫ t in Set.Ioi (1 : ℝ),
        siegelCharacterSummatory χ t * (t : ℂ) ^ (-(s + 1)) := by
  unfold siegelCharacterAbel mellin
  simp only [smul_eq_mul]
  congr 1
  have hrestrict :
      (fun t : ℝ => (t : ℂ) ^ (-s - 1) * siegelCharacterSummatory χ t) =ᵐ[
        volume.restrict (Set.Ioi (0 : ℝ))]
      (Set.Ioi (1 : ℝ)).indicator
        (fun t : ℝ => (t : ℂ) ^ (-s - 1) * siegelCharacterSummatory χ t) := by
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (1 : ℝ))] with t ht
    by_cases ht' : 1 < t
    · simp [ht']
    · have htlt : t < 1 := lt_of_le_of_ne (not_lt.mp ht') ht
      simp [ht', siegelCharacterSummatory_eq_zero_of_lt_one χ htlt]
  rw [integral_congr_ae hrestrict, setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [show -s - 1 = -(s + 1) by ring, mul_comm]

/-- In the absolute-convergence half-plane this is the actual L-function. -/
theorem siegelCharacterAbel_eq_LFunction_of_one_lt_re
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    siegelCharacterAbel χ s = DirichletCharacter.LFunction χ s := by
  rw [siegelCharacterAbel_eq_integral, χ.LFunction_eq_LSeries hs]
  symm
  apply LSeries_eq_mul_integral (fun n : ℕ => χ (n : ZMod q)) (r := 0) le_rfl
    (by linarith) (χ.LSeriesSummable_of_one_lt_re hs)
  refine isBigO_iff.mpr ⟨q, Eventually.of_forall fun N => ?_⟩
  simpa using siegel_character_sum_Icc_norm_le χ hχ N

/-- Analytic continuation identifies the bounded-sum integral with the
actual L-function throughout `Re(s) > 0`, including at a real zero. -/
theorem siegelCharacterAbel_eq_LFunction
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    siegelCharacterAbel χ s = DirichletCharacter.LFunction χ s := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (f := siegelCharacterAbel χ) (g := DirichletCharacter.LFunction χ)
    (DifferentiableOn.analyticOnNhd (fun z hz =>
      (siegelCharacterAbel_differentiableAt χ hχ hz).differentiableWithinAt) hopen)
    (DifferentiableOn.analyticOnNhd (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
      hopen)
    (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 2)
    (by change 0 < (2 : ℂ).re; norm_num) ?_ hs
  have hnhds : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by change 1 < (2 : ℂ).re; norm_num)
  filter_upwards [hnhds] with z hz
  exact siegelCharacterAbel_eq_LFunction_of_one_lt_re χ hχ hz

/-- Absolute integrability of the bounded-sum Abel integrand. -/
theorem siegelCharacterSummatory_integrableOn_cpow
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ =>
      siegelCharacterSummatory χ t * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
  have hm := mellinConvergent_of_isBigO_rpow
    (siegelCharacterSummatory_locallyIntegrableOn χ)
    (siegelCharacterSummatory_isBigO_atTop χ hχ)
    (show (-s).re < 0 by simpa using neg_neg_of_pos hs)
    (siegelCharacterSummatory_isBigO_zero χ (-s.re - 1))
    (show -s.re - 1 < (-s).re by simp)
  have h := hm.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  convert h using 1
  ext t
  simp only [smul_eq_mul, show -s - 1 = -(s + 1) by ring, mul_comm]

/-- The finite prefix is exactly the bounded Abel integral up to one period. -/
theorem siegel_character_prefix_eq_integral
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    (∑ n ∈ Icc 1 q, χ (n : ZMod q) * (n : ℂ) ^ (-s)) =
      s * ∫ t in Set.Ioc (1 : ℝ) q,
        siegelCharacterSummatory χ t * (t : ℂ) ^ (-(s + 1)) := by
  have hzero := siegel_character_zero χ hχ
  have hsum (N : ℕ) : ∑ n ∈ Icc 0 N, χ (n : ZMod q) =
      ∑ n ∈ Icc 1 N, χ (n : ZMod q) := by
    rw [← insert_Icc_add_one_left_eq_Icc N.zero_le, sum_insert (by simp),
      Nat.cast_zero, hzero, zero_add]
    rfl
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) q) :
      deriv (fun t : ℝ => (t : ℂ) ^ (-s)) t =
        -s * (t : ℂ) ^ (-(s + 1)) := by
    rw [Complex.deriv_ofReal_cpow_const (zero_lt_one.trans_le ht.1).ne'
      (neg_ne_zero.mpr (Complex.ne_zero_of_re_pos hs))]
    rw [show -s - 1 = -(s + 1) by ring]
  have hlocal : LocallyIntegrableOn
      (deriv (fun t : ℝ => (t : ℂ) ^ (-s))) (Set.Ici 1) := by
    exact ((integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (integrableOn_Ioi_deriv_ofReal_cpow (s := -s) zero_lt_one
        (by simpa using neg_neg_of_pos hs))).locallyIntegrableOn
  have hAbel := sum_mul_eq_sub_integral_mul₀'
    (c := fun n : ℕ => χ (n : ZMod q)) (f := fun t : ℝ => (t : ℂ) ^ (-s))
    (by simpa using hzero) q
    (fun t ht => differentiableAt_id.ofReal_cpow_const (zero_lt_one.trans_le ht.1).ne'
      (neg_ne_zero.mpr (Complex.ne_zero_of_re_pos hs)))
    (hlocal.integrableOn_compact_subset Set.Icc_subset_Ici_self isCompact_Icc)
  have hleft : (∑ n ∈ Icc 0 q, (n : ℂ) ^ (-s) * χ (n : ZMod q)) =
      ∑ n ∈ Icc 1 q, χ (n : ZMod q) * (n : ℂ) ^ (-s) := by
    rw [← insert_Icc_add_one_left_eq_Icc q.zero_le, sum_insert (by simp),
      Nat.cast_zero, Nat.cast_zero, hzero,
      mul_zero, zero_add]
    apply sum_congr rfl
    intro n hn
    exact mul_comm _ _
  simp only [Complex.ofReal_natCast] at hAbel
  rw [hleft, hsum q,
    show (∑ n ∈ Icc 1 q, χ (n : ZMod q)) = 0 by
      simpa only [siegelCharacterSummatory, Nat.floor_natCast] using
        siegelCharacterSummatory_modulus χ hχ,
    mul_zero, zero_sub] at hAbel
  rw [hAbel, ← integral_neg, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  rw [hderiv t ⟨ht.1.le, ht.2⟩, hsum]
  simp only [siegelCharacterSummatory]
  ring

/-- Partial summation at the actual full-period cutoff. -/
theorem siegel_LFunction_eq_prefix_add_tail
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s =
      (∑ n ∈ Icc 1 q, χ (n : ZMod q) * (n : ℂ) ^ (-s)) +
      s * ∫ t in Set.Ioi (q : ℝ),
        siegelCharacterSummatory χ t * (t : ℂ) ^ (-(s + 1)) := by
  rw [← siegelCharacterAbel_eq_LFunction χ hχ hs, siegelCharacterAbel_eq_integral,
    siegel_character_prefix_eq_integral χ hχ hs, ← mul_add]
  congr 1
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi
    (siegelCharacterSummatory_integrableOn_cpow χ hχ hs)
    (show (1 : ℝ) ≤ q by exact_mod_cast NeZero.pos q)
  rw [intervalIntegral.integral_of_le (by exact_mod_cast NeZero.pos q)] at hsplit
  exact (sub_eq_iff_eq_add.mp hsplit)

/-- Bound the actual tail at the modulus, rather than at `1`. -/
theorem siegel_character_tail_norm_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Set.Ioi (q : ℝ),
      siegelCharacterSummatory χ t * (t : ℂ) ^ (-(s + 1))‖ ≤
      (q : ℝ) ^ (1 - s.re) / s.re := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hpow : -(s.re + 1) < -1 := by linarith
  have hint : IntegrableOn (fun t : ℝ => (q : ℝ) * t ^ (-(s.re + 1)))
      (Set.Ioi q) := (integrableOn_Ioi_rpow_of_lt hpow hq).const_mul _
  have hbound : ‖∫ t in Set.Ioi (q : ℝ),
      siegelCharacterSummatory χ t * (t : ℂ) ^ (-(s + 1))‖ ≤
      ∫ t in Set.Ioi (q : ℝ), (q : ℝ) * t ^ (-(s.re + 1)) := by
    apply norm_integral_le_of_norm_le hint
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hq.trans ht),
      Complex.neg_re, Complex.add_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_right (siegelCharacterSummatory_norm_le χ hχ t)
      (Real.rpow_nonneg (hq.trans ht).le _)
  have heval : (∫ t in Set.Ioi (q : ℝ), (q : ℝ) * t ^ (-(s.re + 1))) =
      (q : ℝ) ^ (1 - s.re) / s.re := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt hpow hq,
      show -(s.re + 1) + 1 = -s.re by ring, neg_div_neg_eq, ← mul_div_assoc]
    congr 1
    rw [sub_eq_add_neg, Real.rpow_add hq, Real.rpow_one]
  exact heval ▸ hbound

/-- The finite prefix has logarithmic size in a strip close to `1`. -/
theorem siegel_character_prefix_norm_le
    (χ : DirichletCharacter ℂ q) {s : ℂ} {η : ℝ} (hη : 0 ≤ η)
    (hs : 1 - η ≤ s.re) :
    ‖∑ n ∈ Icc 1 q, χ (n : ZMod q) * (n : ℂ) ^ (-s)‖ ≤
      (q : ℝ) ^ η * (1 + Real.log q) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hterm (n : ℕ) (hn : n ∈ Icc 1 q) :
      ‖χ (n : ZMod q) * (n : ℂ) ^ (-s)‖ ≤ (q : ℝ) ^ η * (n : ℝ)⁻¹ := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnq : (n : ℝ) ≤ q := by exact_mod_cast (mem_Icc.mp hn).2
    have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos
      (zero_lt_one.trans_le (mem_Icc.mp hn).1), Complex.neg_re]
    calc
      ‖χ (n : ZMod q)‖ * (n : ℝ) ^ (-s.re) ≤ (n : ℝ) ^ (-s.re) :=
        mul_le_of_le_one_left (Real.rpow_nonneg hn0.le _) (χ.norm_le_one n)
      _ ≤ (n : ℝ) ^ (-1 + η) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      _ = (n : ℝ)⁻¹ * (n : ℝ) ^ η := by rw [Real.rpow_add hn0, Real.rpow_neg_one]
      _ ≤ (n : ℝ)⁻¹ * (q : ℝ) ^ η :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn0.le hnq hη) (by positivity)
      _ = (q : ℝ) ^ η * (n : ℝ)⁻¹ := mul_comm _ _
  calc
    ‖∑ n ∈ Icc 1 q, χ (n : ZMod q) * (n : ℂ) ^ (-s)‖ ≤
        ∑ n ∈ Icc 1 q, ‖χ (n : ZMod q) * (n : ℂ) ^ (-s)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 q, (q : ℝ) ^ η * (n : ℝ)⁻¹ := sum_le_sum hterm
    _ = (q : ℝ) ^ η * (harmonic q : ℝ) := by
      rw [← mul_sum]
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ (q : ℝ) ^ η * (1 + Real.log q) :=
      mul_le_mul_of_nonneg_left (harmonic_le_one_add_log q) (Real.rpow_nonneg hq.le _)

/-- The actual near-one bound needed for both the Siegel product at `1`
and Cauchy's logarithmic derivative estimate near a real zero. -/
theorem siegel_LFunction_norm_le_near_one
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} {η : ℝ}
    (hη : 0 ≤ η) (hs : 0 < s.re) (hstrip : 1 - η ≤ s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤
      (q : ℝ) ^ η * (1 + Real.log q + ‖s‖ / s.re) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  rw [siegel_LFunction_eq_prefix_add_tail χ hχ hs]
  apply (norm_add_le _ _).trans
  have hpow : (q : ℝ) ^ (1 - s.re) ≤ (q : ℝ) ^ η :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  calc
    ‖∑ n ∈ Icc 1 q, χ (n : ZMod q) * (n : ℂ) ^ (-s)‖ +
        ‖s * ∫ t in Set.Ioi (q : ℝ),
          siegelCharacterSummatory χ t * (t : ℂ) ^ (-(s + 1))‖ ≤
      (q : ℝ) ^ η * (1 + Real.log q) +
        ‖s‖ * ((q : ℝ) ^ (1 - s.re) / s.re) := by
          rw [norm_mul]
          gcongr
          · exact siegel_character_prefix_norm_le χ hη hstrip
          · exact siegel_character_tail_norm_le χ hχ hs
    _ ≤ (q : ℝ) ^ η * (1 + Real.log q) +
        ‖s‖ * ((q : ℝ) ^ η / s.re) := by gcongr
    _ = (q : ℝ) ^ η * (1 + Real.log q + ‖s‖ / s.re) := by ring

/-- In particular, the value at `1` is at most `log q + 2`. -/
theorem siegel_LFunction_one_norm_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ‖DirichletCharacter.LFunction χ 1‖ ≤ 2 + Real.log q := by
  have h := siegel_LFunction_norm_le_near_one χ hχ (s := 1) (η := 0)
    le_rfl (by norm_num) (by norm_num)
  norm_num at h
  linarith

open Set in
open scoped ComplexConjugate in
/-- The actual continuation of a real character commutes with complex
conjugation on `Re(s)>0`. The Abel integral proves this beyond the region of
absolute convergence, so nonreal zeros there occur in conjugate pairs. -/
theorem siegel_realCharacter_LFunction_conj
    (χ : DirichletCharacter ℂ q) (hχ : ∀ r : ZMod q, (χ r).im = 0)
    (hne : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ (star s) =
      star (DirichletCharacter.LFunction χ s) := by
  change DirichletCharacter.LFunction χ (conj s) =
    conj (DirichletCharacter.LFunction χ s)
  rw [← siegelCharacterAbel_eq_LFunction χ hne hs,
    ← siegelCharacterAbel_eq_LFunction χ hne (s := conj s) (by simpa using hs),
    siegelCharacterAbel_eq_integral, siegelCharacterAbel_eq_integral,
    map_mul, ← integral_conj]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change 1 < t at ht
  have hS : siegelCharacterSummatory χ t =
      ((siegelCharacterSummatory χ t).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [siegelCharacterSummatory, hχ]
  have hstarS : conj (siegelCharacterSummatory χ t) =
      siegelCharacterSummatory χ t := by
    rw [hS]
    simp
  have harg : (t : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (show 0 ≤ t by linarith [ht])]
    exact Real.pi_pos.ne
  have hpow : (t : ℂ) ^ (-(conj s + 1)) =
      conj ((t : ℂ) ^ (-(s + 1))) := by
    simpa using Complex.cpow_conj (t : ℂ) (-(s + 1)) harg
  change siegelCharacterSummatory χ t * (t : ℂ) ^ (-(conj s + 1)) =
    conj (siegelCharacterSummatory χ t * (t : ℂ) ^ (-(s + 1)))
  rw [map_mul, hstarS, hpow]

/-- On the positive real axis the actual continuation of a real character
is real, including below the half-plane of absolute convergence. -/
theorem siegel_realCharacter_LFunction_im_eq_zero
    (χ : DirichletCharacter ℂ q) (hχ : ∀ r : ZMod q, (χ r).im = 0)
    (hne : χ ≠ 1) {σ : ℝ} (hσ : 0 < σ) :
    (DirichletCharacter.LFunction χ (σ : ℂ)).im = 0 := by
  have h := congrArg Complex.im
    (siegel_realCharacter_LFunction_conj χ hχ hne
      (s := (σ : ℂ)) (by simpa using hσ))
  simp only [Complex.star_def, Complex.conj_ofReal, Complex.conj_im] at h
  linarith

/-- A conductor-uniform growth bound on the continuation in `Re(s)>0`.
This deliberately coarse bound suffices on Estermann's fixed disk. -/
theorem siegel_LFunction_norm_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ ‖s‖ * (q : ℝ) / s.re := by
  rw [← siegelCharacterAbel_eq_LFunction χ hχ hs, siegelCharacterAbel_eq_integral, norm_mul]
  have hpow : -(s.re + 1) < -1 := by linarith
  have hint : IntegrableOn (fun t : ℝ => (q : ℝ) * t ^ (-(s.re + 1)))
      (Set.Ioi 1) := (integrableOn_Ioi_rpow_of_lt hpow zero_lt_one).const_mul _
  have hbound : ‖∫ t in Set.Ioi (1 : ℝ),
      siegelCharacterSummatory χ t * (t : ℂ) ^ (-(s + 1))‖ ≤
      ∫ t in Set.Ioi (1 : ℝ), (q : ℝ) * t ^ (-(s.re + 1)) := by
    apply norm_integral_le_of_norm_le hint
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht),
      Complex.neg_re, Complex.add_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_right (siegelCharacterSummatory_norm_le χ hχ t)
      (Real.rpow_nonneg (zero_lt_one.trans ht).le _)
  have heval : (∫ t in Set.Ioi (1 : ℝ), (q : ℝ) * t ^ (-(s.re + 1))) =
      (q : ℝ) / s.re := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt hpow zero_lt_one]
    simp [div_eq_mul_inv]
  rw [heval] at hbound
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hbound (norm_nonneg s)

/-- The actual L-function is bounded by `7q` on the closed Estermann disk. -/
theorem siegel_LFunction_norm_le_estermann_disk
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ}
    (hs : s ∈ Metric.closedBall (2 : ℂ) (3 / 2 : ℝ)) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ 7 * (q : ℝ) := by
  have hdist : ‖s - 2‖ ≤ (3 / 2 : ℝ) := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hs
  have hre : 1 / 2 ≤ s.re := by
    have h : 2 - s.re ≤ ‖s - 2‖ := by
      calc
        2 - s.re = (2 - s).re := by simp
        _ ≤ ‖(2 : ℂ) - s‖ := Complex.re_le_norm _
        _ = ‖s - 2‖ := norm_sub_rev _ _
    linarith
  have hnorm : ‖s‖ ≤ (7 / 2 : ℝ) := by
    calc
      ‖s‖ = ‖s - 2 + 2‖ := by ring_nf
      _ ≤ ‖s - 2‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
      _ ≤ 7 / 2 := by norm_num at *; linarith
  apply (siegel_LFunction_norm_le χ hχ (by linarith)).trans
  apply (div_le_iff₀ (by linarith : 0 < s.re)).mpr
  nlinarith [show 0 ≤ (q : ℝ) by positivity]

#print axioms siegelCharacterAbel_eq_LFunction
#print axioms siegel_LFunction_norm_le_estermann_disk
#print axioms siegel_LFunction_eq_prefix_add_tail
#print axioms siegel_LFunction_norm_le_near_one
#print axioms siegel_LFunction_one_norm_le
#print axioms siegel_realCharacter_LFunction_conj
#print axioms siegel_realCharacter_LFunction_im_eq_zero

end SystolicGrowth.CookMagyarCircle
