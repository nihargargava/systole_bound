module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.UnweightedHomogeneousModel
public import CookMagyar.ArcPhasePeriodicity
public import CookMagyar.LogCutoff
public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Mathlib.Data.Rat.Floor

@[expose] public section

open Filter

namespace SystolicGrowth
namespace CookMagyarMajorArc

open CookMagyarCircle CookMagyarArcs

/-! # Integer cutoff for the ordinary cubic 32nd moment -/

/-- The integer auxiliary cutoff is the floor of the real cubic root. -/
def cubicAuxiliaryCutoff (N : ℕ) : ℕ := Nat.nthRoot 3 N

theorem cubicAuxiliaryCutoff_pow_le (N : ℕ) :
    cubicAuxiliaryCutoff N ^ 3 ≤ N := by
  exact Nat.pow_nthRoot_le (Or.inl (by decide))

theorem lt_cubicAuxiliaryCutoff_add_one_pow (N : ℕ) :
    N < (cubicAuxiliaryCutoff N + 1) ^ 3 := by
  exact Nat.lt_pow_nthRoot_add_one (by decide) N

theorem cubicAuxiliaryCutoff_pos {N : ℕ} (hN : 0 < N) :
    0 < cubicAuxiliaryCutoff N := by
  rw [Nat.pos_iff_ne_zero]
  intro h
  have hp := lt_cubicAuxiliaryCutoff_add_one_pow N
  rw [h] at hp
  norm_num at hp
  omega

theorem cubicAuxiliaryCutoff_le_realRoot (N : ℕ) :
    (cubicAuxiliaryCutoff N : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ)⁻¹) := by
  have hp : (cubicAuxiliaryCutoff N : ℝ) ^ 3 ≤ (N : ℝ) := by
    exact_mod_cast cubicAuxiliaryCutoff_pow_le N
  have h := Real.rpow_le_rpow
    (by positivity : (0 : ℝ) ≤ (cubicAuxiliaryCutoff N : ℝ) ^ 3)
    hp (by norm_num : (0 : ℝ) ≤ (3 : ℝ)⁻¹)
  have hP : ((cubicAuxiliaryCutoff N : ℝ) ^ 3) ^ ((3 : ℝ)⁻¹) =
      (cubicAuxiliaryCutoff N : ℝ) := by
    simpa using (Real.pow_rpow_inv_natCast
      (show (0 : ℝ) ≤ (cubicAuxiliaryCutoff N : ℝ) by positivity)
      (by decide : (3 : ℕ) ≠ 0))
  rw [hP] at h
  exact h

theorem cubicAuxiliaryCutoff_add_one_le_two_realRoot
    {N : ℕ} (hN : 0 < N) :
    (cubicAuxiliaryCutoff N : ℝ) + 1 ≤
      2 * (N : ℝ) ^ ((3 : ℝ)⁻¹) := by
  have hp : (1 : ℝ) ≤ cubicAuxiliaryCutoff N := by
    exact_mod_cast cubicAuxiliaryCutoff_pos hN
  have hroot := cubicAuxiliaryCutoff_le_realRoot N
  linarith

/-- The real cubic root lies below the next integer cutoff. -/
theorem cubicAuxiliaryCutoff_lt_succ_realRoot (N : ℕ) :
    (N : ℝ) ^ ((3 : ℝ)⁻¹) < (cubicAuxiliaryCutoff N : ℝ) + 1 := by
  let P := cubicAuxiliaryCutoff N
  have hnat : N < (P + 1) ^ 3 := by
    simpa only [P] using lt_cubicAuxiliaryCutoff_add_one_pow N
  have hreal : (N : ℝ) < ((P + 1 : ℕ) : ℝ) ^ 3 := by
    exact_mod_cast hnat
  have h := Real.rpow_lt_rpow (by positivity : (0 : ℝ) ≤ (N : ℝ))
    hreal (by norm_num : (0 : ℝ) < (3 : ℝ)⁻¹)
  have hpow : (((P + 1 : ℕ) : ℝ) ^ 3) ^ ((3 : ℝ)⁻¹) =
      (P : ℝ) + 1 := by
    have hnonneg : (0 : ℝ) ≤ ((P + 1 : ℕ) : ℝ) := by positivity
    calc
      (((P + 1 : ℕ) : ℝ) ^ 3) ^ ((3 : ℝ)⁻¹) =
          ((P + 1 : ℕ) : ℝ) :=
        Real.pow_rpow_inv_natCast (x := ((P + 1 : ℕ) : ℝ)) (n := 3)
          hnonneg (by decide)
      _ = (P : ℝ) + 1 := by norm_num
  have h' : (N : ℝ) ^ ((3 : ℝ)⁻¹) <
      (((P + 1 : ℕ) : ℝ) ^ 3) ^ ((3 : ℝ)⁻¹) := by
    simpa only [Nat.cast_add, Nat.cast_one] using h
  rw [hpow] at h'
  simpa [P] using h'

/-- The integer cutoff is at least half the real cubic root once the root
is at least two. This lower sandwich is needed to turn the Dirichlet height
`O(N^3/P)` into `O(N^(8/3))`. -/
theorem realRoot_le_two_cubicAuxiliaryCutoff
    {N : ℕ} (hN : 8 ≤ N) :
    (N : ℝ) ^ ((3 : ℝ)⁻¹) ≤ 2 * (cubicAuxiliaryCutoff N : ℝ) := by
  have hPpos : 0 < cubicAuxiliaryCutoff N := cubicAuxiliaryCutoff_pos (by omega)
  have hrootlt := cubicAuxiliaryCutoff_lt_succ_realRoot N
  have hPnat : cubicAuxiliaryCutoff N + 1 ≤ 2 * cubicAuxiliaryCutoff N := by omega
  have hPcast : (cubicAuxiliaryCutoff N : ℝ) + 1 ≤
      2 * (cubicAuxiliaryCutoff N : ℝ) := by exact_mod_cast hPnat
  linarith

/-- Dirichlet's integer height for the auxiliary power-cutoff arcs. -/
noncomputable def cubicAuxiliaryHeight (N : ℕ) : ℕ :=
  Nat.ceil (2 * (N : ℝ) ^ 3 / (cubicAuxiliaryCutoff N : ℝ))

theorem cubicAuxiliaryHeight_bounds {N : ℕ} (hN : 0 < N) :
    2 * (N : ℝ) ^ 3 / (cubicAuxiliaryCutoff N : ℝ) ≤
        (cubicAuxiliaryHeight N : ℝ) ∧
      (cubicAuxiliaryHeight N : ℝ) ≤
        3 * (N : ℝ) ^ 3 / (cubicAuxiliaryCutoff N : ℝ) := by
  let P := cubicAuxiliaryCutoff N
  have hP : 0 < P := cubicAuxiliaryCutoff_pos hN
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hPcube : P ^ 3 ≤ N := cubicAuxiliaryCutoff_pow_le N
  have hP_le_N : P ≤ N := by
    exact (Nat.le_self_pow (by decide : (3 : ℕ) ≠ 0) P).trans hPcube
  have hP_le_cube : (P : ℝ) ≤ (N : ℝ) ^ 3 := by
    have hPN : (P : ℝ) ≤ N := by exact_mod_cast hP_le_N
    have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have hNpow : (N : ℝ) ≤ (N : ℝ) ^ 3 := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ N by positivity)
        (sub_nonneg.mpr hN2)]
    linarith
  let X : ℝ := (N : ℝ) ^ 3 / (P : ℝ)
  have hX : 1 ≤ X := by
    dsimp [X]
    exact (le_div_iff₀ hPr).2 (by simpa using hP_le_cube)
  have hX0 : 0 ≤ X := le_trans (by norm_num) hX
  have hlo : 2 * X ≤ (cubicAuxiliaryHeight N : ℝ) := by
    simpa only [cubicAuxiliaryHeight, X, mul_div_assoc] using
      (Nat.le_ceil (2 * X))
  have hhi : (cubicAuxiliaryHeight N : ℝ) < 2 * X + 1 := by
    simpa only [cubicAuxiliaryHeight, X, mul_div_assoc] using
      (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * X))
  constructor
  · simpa only [X, mul_div_assoc] using hlo
  · have : (cubicAuxiliaryHeight N : ℝ) ≤ 3 * X := by linarith
    simpa only [X, mul_div_assoc] using this

/-- A real displacement controls circle distance even after an integer
wrap. This is the seam-safe direction needed from Dirichlet's theorem. -/
theorem periodicDistance_add_int_le_abs
    (center beta : ℝ) (z : ℤ) :
    periodicDistance (center + beta + z) center ≤ |beta| := by
  have hz : (((z : ℝ) : UnitAddCircle)) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).2
    refine ⟨z, ?_⟩
    simp [zsmul_eq_mul]
  have hcoe : ((center + beta + z : ℝ) : UnitAddCircle) =
      ((center + beta : ℝ) : UnitAddCircle) := by
    rw [AddCircle.coe_add, hz, add_zero]
  unfold periodicDistance
  rw [hcoe, dist_eq_norm, ← AddCircle.coe_sub]
  have hsub : center + beta - center = beta := by ring
  rw [hsub]
  simpa only [Real.norm_eq_abs] using
    (QuotientAddGroup.norm_mk_le_norm
      (S := AddSubgroup.zmultiples (1 : ℝ)) (m := beta))

/-- A reduced center with sufficiently small real displacement, including
one represented across the endpoint seam, belongs to the auxiliary arc. -/
theorem mem_auxiliaryMajorArcs_of_displacement
    {N a q : ℕ} {alpha beta : ℝ} {z : ℤ}
    (hI : alpha ∈ Set.Icc (0 : ℝ) 1)
    (hq : 0 < q) (hqP : q ≤ cubicAuxiliaryCutoff N)
    (ha : a < q) (hac : Nat.Coprime a q)
    (halpha : alpha = rationalCenter a q + beta + z)
    (hbeta : |beta| < cubicArcRadius N (cubicAuxiliaryCutoff N)) :
    alpha ∈ majorArcs N (cubicAuxiliaryCutoff N) := by
  refine ⟨hI, a, q, ?_, ?_⟩
  · exact ⟨hqP, Nat.ne_of_gt hq, ha, hac⟩
  · rw [halpha]
    exact (periodicDistance_add_int_le_abs _ _ _).trans_lt hbeta

/-- The Dirichlet error at the chosen height is strictly inside the
auxiliary arc whenever the denominator is at most the cutoff. -/
theorem dirichletError_lt_auxiliaryArcRadius
    {N q : ℕ} (hN : 0 < N) (hq : 0 < q)
    {beta : ℝ}
    (hbeta : |beta| ≤
      1 / (((cubicAuxiliaryHeight N : ℝ) + 1) * (q : ℝ))) :
    |beta| < cubicArcRadius N (cubicAuxiliaryCutoff N) := by
  let X : ℝ := (N : ℝ) ^ 3
  let Y : ℝ := cubicAuxiliaryCutoff N
  let H : ℝ := cubicAuxiliaryHeight N
  let Q : ℝ := q
  have hX : 0 < X := by dsimp [X]; positivity
  have hY : 0 < Y := by
    dsimp [Y]
    exact_mod_cast cubicAuxiliaryCutoff_pos hN
  have hQ : 1 ≤ Q := by dsimp [Q]; exact_mod_cast hq
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hheight : 2 * X / Y ≤ H := by
    simpa only [X, Y, H] using (cubicAuxiliaryHeight_bounds hN).1
  have hheight' : 2 * X ≤ H * Y := (div_le_iff₀ hY).mp hheight
  have hden : 0 < (H + 1) * Q := by positivity
  have hQmul : 0 ≤ (Q - 1) * (H + 1) * Y := by positivity
  have hcross : X < Y * ((H + 1) * Q) := by
    nlinarith [hQmul]
  have hfrac : 1 / ((H + 1) * Q) < Y / X := by
    exact (div_lt_div_iff₀ hden hX).2 (by nlinarith [hcross])
  have hβ : |beta| ≤ 1 / ((H + 1) * Q) := by simpa only [H, Q] using hbeta
  have hres : |beta| < Y / X := hβ.trans_lt hfrac
  simpa only [cubicArcRadius, X, Y] using hres

/-- A height that puts the Dirichlet error strictly inside the cubic arc
radius does so uniformly for every positive reduced denominator. This
height-parametric form is useful for logarithmic cutoffs as well as the
auxiliary power cutoff. -/
theorem dirichletError_lt_cubicArcRadius_of_height
    {N Q H q : ℕ} (hN : 0 < N) (hq : 0 < q)
    (hheight : (N : ℝ) ^ 3 < (Q : ℝ) * ((H : ℝ) + 1))
    {beta : ℝ}
    (hbeta : |beta| ≤ 1 / (((H : ℝ) + 1) * (q : ℝ))) :
    |beta| < cubicArcRadius N Q := by
  have hX : 0 < (N : ℝ) ^ 3 := by positivity
  have hqR : 1 ≤ (q : ℝ) := by exact_mod_cast hq
  have hQ : 0 < (Q : ℝ) := by nlinarith
  have hden : 0 < ((H : ℝ) + 1) * (q : ℝ) := by positivity
  have hcross : (N : ℝ) ^ 3 <
      (Q : ℝ) * (((H : ℝ) + 1) * (q : ℝ)) := by
    calc
      (N : ℝ) ^ 3 < (Q : ℝ) * ((H : ℝ) + 1) := hheight
      _ ≤ (Q : ℝ) * (((H : ℝ) + 1) * (q : ℝ)) := by
        gcongr
        nlinarith [show 0 ≤ (H : ℝ) by positivity]
  have hfrac : 1 / (((H : ℝ) + 1) * (q : ℝ)) <
      (Q : ℝ) / (N : ℝ) ^ 3 := by
    apply (div_lt_div_iff₀ hden hX).2
    nlinarith [hcross]
  have hres : |beta| < (Q : ℝ) / (N : ℝ) ^ 3 := hbeta.trans_lt hfrac
  simpa only [cubicArcRadius] using hres

/-- A normalized Dirichlet witness at small denominator is in the
periodic auxiliary major arcs. The next minor-arc theorem must supply
such a witness by reducing the rational approximation modulo one. -/
theorem mem_auxiliaryMajorArcs_of_dirichletWitness
    {N a q : ℕ} {alpha beta : ℝ} {z : ℤ}
    (hN : 0 < N) (hI : alpha ∈ Set.Icc (0 : ℝ) 1)
    (hq : 0 < q) (hqP : q ≤ cubicAuxiliaryCutoff N)
    (ha : a < q) (hac : Nat.Coprime a q)
    (halpha : alpha = rationalCenter a q + beta + z)
    (hbeta : |beta| ≤
      1 / (((cubicAuxiliaryHeight N : ℝ) + 1) * (q : ℝ))) :
    alpha ∈ majorArcs N (cubicAuxiliaryCutoff N) := by
  apply mem_auxiliaryMajorArcs_of_displacement hI hq hqP ha hac halpha
  exact dirichletError_lt_auxiliaryArcRadius hN hq hbeta

/-- Normalize any rational number to a reduced center in `[0,1)`,
retaining its denominator and recording the integer seam shift. -/
theorem exists_reducedCenter_add_int_eq_rat (r : ℚ) :
    ∃ a : ℕ, a < r.den ∧ Nat.Coprime a r.den ∧
      (r : ℝ) = rationalCenter a r.den + (⌊r⌋ : ℤ) := by
  let s : ℚ := Int.fract r
  let a : ℕ := s.num.natAbs
  have hs0 : 0 ≤ s := Int.fract_nonneg r
  have hs1 : s < 1 := Int.fract_lt_one r
  have hnum0 : 0 ≤ s.num := Rat.num_nonneg.mpr hs0
  have haNum : (a : ℤ) = s.num := Int.natAbs_of_nonneg hnum0
  have hsden : s.den = r.den := Rat.den_intFract r
  have hnumlt : s.num < (s.den : ℤ) := by
    have hden : (0 : ℚ) < s.den := by exact_mod_cast s.den_pos
    have hq : (s.num : ℚ) / (s.den : ℚ) < 1 := by
      simpa only [s.num_div_den] using hs1
    have hlt : (s.num : ℚ) < (s.den : ℚ) :=
      (div_lt_one hden).mp hq
    exact_mod_cast hlt
  have ha : a < r.den := by
    have : (a : ℤ) < (r.den : ℤ) := by simpa only [haNum, hsden] using hnumlt
    exact_mod_cast this
  have hac : Nat.Coprime a r.den := by
    simpa only [a, hsden] using s.reduced
  have hsrepr : (s : ℝ) = rationalCenter a r.den := by
    have hq : ((s.num : ℚ) / (s.den : ℚ) : ℚ) = s := s.num_div_den
    have hc : ((s.num : ℝ) / (s.den : ℝ)) = (s : ℝ) := by exact_mod_cast hq
    rw [← hc]
    unfold rationalCenter
    rw [← hsden]
    have hnumReal : (a : ℝ) = (s.num : ℝ) := by exact_mod_cast haNum
    rw [hnumReal]
  refine ⟨a, ha, hac, ?_⟩
  have hfract : (s : ℚ) = r - (⌊r⌋ : ℤ) := rfl
  have hfr : (s : ℝ) = (r : ℝ) - (⌊r⌋ : ℤ) := by exact_mod_cast hfract
  rw [hsrepr] at hfr
  linarith

/-- Dirichlet approximation at any positive integer height, normalized to
the project's reduced rational center and integer-wrap convention. -/
theorem exists_reducedCenter_approximation_of_height
    (H : ℕ) (hH : 0 < H) (alpha : ℝ) :
    ∃ a q : ℕ, ∃ beta : ℝ, ∃ z : ℤ,
      0 < q ∧ q ≤ H ∧ a < q ∧ Nat.Coprime a q ∧
      alpha = rationalCenter a q + beta + z ∧
      |beta| ≤ 1 / (((H : ℝ) + 1) * (q : ℝ)) := by
  obtain ⟨r, herr, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le alpha hH
  obtain ⟨a, ha, hac, hr⟩ := exists_reducedCenter_add_int_eq_rat r
  let beta : ℝ := alpha - r
  refine ⟨a, r.den, beta, ⌊r⌋, r.den_pos, hden, ha, hac, ?_, ?_⟩
  · dsimp [beta]
    linarith
  · simpa only [beta] using herr

/-- Every minor-arc point has a reduced Dirichlet approximant with
denominator larger than the cutoff, provided the chosen height makes its
error smaller than the cubic major-arc radius. This version is independent
of the auxiliary power cutoff and is the interface for logarithmic arcs. -/
theorem exists_large_denominator_of_mem_minorArcs_of_height
    {N Q H : ℕ} (hN : 0 < N) (hH : 0 < H) {alpha : ℝ}
    (hminor : alpha ∈ minorArcs N Q)
    (hheight : (N : ℝ) ^ 3 < (Q : ℝ) * ((H : ℝ) + 1)) :
    ∃ a q : ℕ, ∃ beta : ℝ, ∃ z : ℤ,
      Q < q ∧ q ≤ H ∧ a < q ∧ Nat.Coprime a q ∧
      alpha = rationalCenter a q + beta + z ∧
      |beta| ≤ 1 / (((H : ℝ) + 1) * (q : ℝ)) := by
  obtain ⟨a, q, beta, z, hq, hqH, ha, hac, halpha, hbeta⟩ :=
    exists_reducedCenter_approximation_of_height H hH alpha
  have hqQ : Q < q := by
    by_contra hn
    have hqQ : q ≤ Q := Nat.le_of_not_gt hn
    have hbetaArc := dirichletError_lt_cubicArcRadius_of_height
      hN hq hheight hbeta
    have hmajor : alpha ∈ majorArcs N Q := by
      refine ⟨hminor.1, a, q, ⟨hqQ, Nat.ne_of_gt hq, ha, hac⟩, ?_⟩
      rw [halpha]
      exact (periodicDistance_add_int_le_abs _ _ _).trans_lt hbetaArc
    exact hminor.2 hmajor
  exact ⟨a, q, beta, z, hqQ, hqH, ha, hac, halpha, hbeta⟩

/-- The Dirichlet height matched to the logarithmic denominator cutoff. -/
noncomputable def logarithmicPrimeMinorArcHeight (A N : ℕ) : ℕ :=
  Nat.ceil (2 * (N : ℝ) ^ 3 /
    (logarithmicDenominatorCutoff A N : ℝ))

/-- On the project's logarithmic minor arcs, the elementary Dirichlet
adapter supplies the standard rational-leading Weyl data: the reduced
denominator lies between the cutoff and `3 N^3 / cutoff`, and the wrapped
error is at most `1/q^2`. This is only an approximation lemma; the prime
Type-I/II exponential-sum estimate is a separate theorem. -/
theorem eventually_exists_logarithmicPrimeMinorArcWeylData
    (A : ℕ) (hA : 0 < A) :
    ∀ᶠ N : ℕ in atTop,
      ∀ alpha : ℝ,
        alpha ∈ minorArcs N (logarithmicDenominatorCutoff A N) →
          ∃ a q : ℕ, ∃ beta : ℝ, ∃ z : ℤ,
            logarithmicDenominatorCutoff A N < q ∧
            (q : ℝ) ≤ 3 * (N : ℝ) ^ 3 /
              (logarithmicDenominatorCutoff A N : ℝ) ∧
            a < q ∧ Nat.Coprime a q ∧
            alpha = rationalCenter a q + beta + z ∧
            |beta| ≤ 1 / (q : ℝ) ^ 2 ∧
            (N : ℝ) ^ 3 * |beta| ≤
              (logarithmicDenominatorCutoff A N : ℝ) / (q : ℝ) ∧
            (N : ℝ) ^ 3 * |beta| ≤ 1 := by
  have hQpos : ∀ᶠ N : ℕ in atTop,
      1 ≤ logarithmicDenominatorCutoff A N := by
    exact (tendsto_logarithmicDenominatorCutoff A hA).eventually_ge_atTop 1
  filter_upwards
    [hQpos,
      eventually_logarithmicDenominatorCutoff_pow_le_add_two A 1,
      eventually_ge_atTop (2 : ℕ)] with N hQ hQadd hN
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  let Q : ℝ := logarithmicDenominatorCutoff A N
  let X : ℝ := (N : ℝ) ^ 3
  let H : ℕ := logarithmicPrimeMinorArcHeight A N
  have hQr : 0 < Q := by
    dsimp [Q]
    exact_mod_cast (show 0 < logarithmicDenominatorCutoff A N by omega)
  have hX : 0 < X := by dsimp [X]; positivity
  have hQadd : (logarithmicDenominatorCutoff A N : ℝ) ≤
      (N : ℝ) + 2 := by
    simpa [Q] using hQadd
  have hNscale : (N : ℝ) + 2 ≤ X := by
    dsimp [X]
    nlinarith [sq_nonneg ((N : ℝ) - 2)]
  have hQX : Q ≤ X := by dsimp [Q]; linarith
  have hratio : 1 ≤ 2 * X / Q := by
    rw [le_div_iff₀ hQr]
    nlinarith
  have hy : 0 ≤ 2 * X / Q := by positivity
  have hHlow : 2 * X / Q ≤ (H : ℝ) := by
    simpa [H, X, Q, logarithmicPrimeMinorArcHeight,
      logarithmicDenominatorCutoff] using (Nat.le_ceil (2 * X / Q))
  have hHposR : 0 < (H : ℝ) := by linarith
  have hHpos : 0 < H := by exact_mod_cast hHposR
  have hHhigh : (H : ℝ) < 2 * X / Q + 1 := by
    simpa [H, X, Q, logarithmicPrimeMinorArcHeight,
      logarithmicDenominatorCutoff] using Nat.ceil_lt_add_one hy
  have hheight : X < Q * ((H : ℝ) + 1) := by
    have hlowmul : 2 * X ≤ Q * (H : ℝ) := by
      nlinarith [(div_le_iff₀ hQr).mp hHlow]
    nlinarith [hlowmul]
  have hHbound : (H : ℝ) ≤ 3 * X / Q := by
    apply (le_div_iff₀ hQr).2
    have hhighmul : (H : ℝ) * Q < 2 * X + Q := by
      calc
        (H : ℝ) * Q < (2 * X / Q + 1) * Q :=
          mul_lt_mul_of_pos_right hHhigh hQr
        _ = 2 * X + Q := by field_simp
    nlinarith
  intro alpha hminor
  obtain ⟨a, q, beta, z, hqQ, hqH, ha, hac, halpha, hbeta⟩ :=
    exists_large_denominator_of_mem_minorArcs_of_height
      (by omega : 0 < N) hHpos hminor (by simpa [X, Q] using hheight)
  have hqHr : (q : ℝ) ≤ H := by exact_mod_cast hqH
  have hqNat : 1 ≤ q := by omega
  have hqR : 1 ≤ (q : ℝ) := by exact_mod_cast hqNat
  have hqden : (q : ℝ) ^ 2 ≤ ((H : ℝ) + 1) * (q : ℝ) := by
    nlinarith
  have hdenpos : 0 < ((H : ℝ) + 1) * (q : ℝ) := by positivity
  have hscaledError :
      1 / (((H : ℝ) + 1) * (q : ℝ)) ≤
        Q / (2 * X * (q : ℝ)) := by
    apply (div_le_div_iff₀ hdenpos (by positivity)).2
    have hHratio : 2 * X ≤ Q * (H : ℝ) := by
      simpa only [mul_comm] using (div_le_iff₀ hQr).mp hHlow
    have hHratio' : 2 * X * (q : ℝ) ≤
        Q * ((H : ℝ) + 1) * (q : ℝ) := by
      calc
        2 * X * (q : ℝ) ≤ Q * (H : ℝ) * (q : ℝ) :=
          mul_le_mul_of_nonneg_right hHratio (by positivity)
        _ ≤ Q * ((H : ℝ) + 1) * (q : ℝ) := by
          have hHle : (H : ℝ) ≤ (H : ℝ) + 1 := by linarith
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hHle (le_of_lt hQr)) (by positivity)
    nlinarith [hHratio']
  have hbetaScaled : |beta| ≤ Q / (2 * X * (q : ℝ)) :=
    hbeta.trans hscaledError
  have hXbeta : X * |beta| ≤ Q / (2 * (q : ℝ)) := by
    calc
      X * |beta| ≤ X * (Q / (2 * X * (q : ℝ))) :=
        mul_le_mul_of_nonneg_left hbetaScaled (le_of_lt hX)
      _ = Q / (2 * (q : ℝ)) := by field_simp
  have hXbeta' : X * |beta| ≤ Q / (q : ℝ) := by
    have hhalf : Q / (2 * (q : ℝ)) ≤ Q / (q : ℝ) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith
    exact hXbeta.trans hhalf
  have hQltq : Q < (q : ℝ) := by
    dsimp [Q]
    exact_mod_cast hqQ
  have hqpos : 0 < (q : ℝ) := by positivity
  have hQratio : Q / (q : ℝ) < 1 := (div_lt_one hqpos).2 hQltq
  have hXbetaOne : X * |beta| ≤ 1 := hXbeta'.trans hQratio.le
  have hfrac : 1 / (((H : ℝ) + 1) * (q : ℝ)) ≤
      1 / (q : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ hdenpos (pow_pos (by positivity : (0 : ℝ) < q) 2)).2
    nlinarith [hqden]
  refine ⟨a, q, beta, z, ?_, ?_, ha, hac, halpha,
    ⟨hbeta.trans hfrac, hXbeta', hXbetaOne⟩⟩
  · exact_mod_cast hqQ
  calc
    (q : ℝ) ≤ H := hqHr
    _ ≤ 3 * X / Q := hHbound
    _ = 3 * (N : ℝ) ^ 3 /
          (logarithmicDenominatorCutoff A N : ℝ) := by
          simp [Q, X]

/-- Express the logarithmic minor-arc approximation in a requested smaller
logarithmic scale. This is the source-facing denominator window: for
`C < A`, its denominator is larger than `log(N+2)^C` and at most
`3 N^3 / log(N+2)^C`. -/
theorem eventually_exists_logarithmicPrimeMinorArcWeylData_at_scale
    (A C : ℕ) (hA : 0 < A) (hCA : C < A) :
    ∀ᶠ N : ℕ in atTop,
      ∀ alpha : ℝ,
        alpha ∈ minorArcs N (logarithmicDenominatorCutoff A N) →
          ∃ a q : ℕ, ∃ beta : ℝ, ∃ z : ℤ,
            Real.log ((N : ℝ) + 2) ^ C < (q : ℝ) ∧
            (q : ℝ) ≤ 3 * (N : ℝ) ^ 3 /
              Real.log ((N : ℝ) + 2) ^ C ∧
            a < q ∧ Nat.Coprime a q ∧
            alpha = rationalCenter a q + beta + z ∧
            |beta| ≤ 1 / (q : ℝ) ^ 2 ∧
            (N : ℝ) ^ 3 * |beta| ≤
              (logarithmicDenominatorCutoff A N : ℝ) / (q : ℝ) ∧
            (N : ℝ) ^ 3 * |beta| ≤ 1 := by
  have hcutlow : ∀ᶠ N : ℕ in atTop,
      Real.log ((N : ℝ) + 2) ^ C ≤
        (logarithmicDenominatorCutoff A N : ℝ) :=
    eventually_log_pow_le_logarithmicDenominatorCutoff A C hCA
  filter_upwards
    [eventually_exists_logarithmicPrimeMinorArcWeylData A hA, hcutlow,
      eventually_ge_atTop (2 : ℕ)] with N hdata hcutlow hN alpha hminor
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨a, q, beta, z, hqQ, hqupper, ha, hac, halpha,
      hbeta, hscaledBeta, hscaledBetaOne⟩ :=
    hdata alpha hminor
  have hqQreal :
      (logarithmicDenominatorCutoff A N : ℝ) < (q : ℝ) := by
    exact_mod_cast hqQ
  have hscale : 0 < Real.log ((N : ℝ) + 2) ^ C := by
    apply pow_pos
    apply Real.log_pos
    nlinarith [show (0 : ℝ) ≤ N by positivity]
  have hQr : 0 < (logarithmicDenominatorCutoff A N : ℝ) :=
    lt_of_lt_of_le hscale hcutlow
  have hqupperScale :
        3 * (N : ℝ) ^ 3 /
          (logarithmicDenominatorCutoff A N : ℝ) ≤
        3 * (N : ℝ) ^ 3 / Real.log ((N : ℝ) + 2) ^ C := by
    have hmul := mul_le_mul_of_nonneg_left hcutlow
      (by positivity : 0 ≤ 3 * (N : ℝ) ^ 3)
    apply (div_le_div_iff₀ hQr hscale).2
    nlinarith [hmul]
  refine ⟨a, q, beta, z, ?_, ?_, ha, hac, halpha, hbeta,
    hscaledBeta, hscaledBetaOne⟩
  · exact hcutlow.trans_lt hqQreal
  · exact hqupper.trans hqupperScale

/-- Hua's exact denominator window for project minor-arc points. With one
additional cutoff power, the factor `3` in the Dirichlet height is absorbed:
for `sigma + 1 < A`, the reduced denominator satisfies
`log(N+2)^sigma < q ≤ (N+2)^3 / log(N+2)^sigma`. This is the rational
approximation input to Theorem 10, not its prime-sum estimate. -/
theorem eventually_exists_logarithmicPrimeMinorArcWeylData_huaWindow
    (A sigma : ℕ) (hA : 0 < A) (hSA : sigma + 1 < A) :
    ∀ᶠ N : ℕ in atTop,
      ∀ alpha : ℝ,
        alpha ∈ minorArcs N (logarithmicDenominatorCutoff A N) →
          ∃ a q : ℕ, ∃ beta : ℝ, ∃ z : ℤ,
            Real.log ((N : ℝ) + 2) ^ sigma < (q : ℝ) ∧
            (q : ℝ) ≤ ((N : ℝ) + 2) ^ 3 /
              Real.log ((N : ℝ) + 2) ^ sigma ∧
            a < q ∧ Nat.Coprime a q ∧
            alpha = rationalCenter a q + beta + z ∧
            |beta| ≤ 1 / (q : ℝ) ^ 2 ∧
            (N : ℝ) ^ 3 * |beta| ≤
              (logarithmicDenominatorCutoff A N : ℝ) / (q : ℝ) ∧
            (N : ℝ) ^ 3 * |beta| ≤ 1 := by
  have hlog : Tendsto
      (fun N : ℕ => Real.log ((N : ℝ) + 2)) atTop atTop := by
    have harg : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop := by
      convert tendsto_atTop_add_const_right _ (2 : ℝ)
        tendsto_natCast_atTop_atTop using 1
    exact Real.tendsto_log_atTop.comp harg
  filter_upwards
    [eventually_exists_logarithmicPrimeMinorArcWeylData A hA,
      eventually_three_mul_log_pow_le_logarithmicDenominatorCutoff
        A sigma hSA,
      hlog.eventually_ge_atTop (3 : ℝ),
      eventually_ge_atTop (2 : ℕ)] with
    N hdata hcutWindow hlogN hN alpha hminor
  let L : ℝ := Real.log ((N : ℝ) + 2)
  let R : ℝ := L ^ sigma
  let Q : ℝ := logarithmicDenominatorCutoff A N
  have hL3 : 3 ≤ L := by simpa [L] using hlogN
  have hRpos : 0 < R := by
    dsimp [R]
    exact pow_pos (by linarith : 0 < L) sigma
  have hQwindow : 3 * R ≤ Q := by
    simpa [L, R, Q] using hcutWindow
  have hQpos : 0 < Q := by nlinarith [hRpos]
  obtain ⟨a, q, beta, z, hqQ, hqUpper, ha, hac, halpha,
      hbeta, hscaledBeta, hscaledBetaOne⟩ := hdata alpha hminor
  have hqQreal : Q < (q : ℝ) := by
    dsimp [Q]
    exact_mod_cast hqQ
  have hlower : R < (q : ℝ) := by
    have hRleQ : R ≤ Q := by nlinarith [hQwindow]
    exact hRleQ.trans_lt hqQreal
  have hNcube : 0 ≤ (N : ℝ) ^ 3 := by positivity
  have hmiddle : 3 * (N : ℝ) ^ 3 / Q ≤ (N : ℝ) ^ 3 / R := by
    apply (div_le_div_iff₀ hQpos hRpos).2
    have hprod := mul_le_mul_of_nonneg_left hQwindow hNcube
    nlinarith [hprod]
  have hNleP : (N : ℝ) ^ 3 ≤ ((N : ℝ) + 2) ^ 3 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have htop : (N : ℝ) ^ 3 / R ≤ ((N : ℝ) + 2) ^ 3 / R := by
    apply (div_le_div_iff₀ hRpos hRpos).2
    exact mul_le_mul_of_nonneg_right hNleP (le_of_lt hRpos)
  have hupper : (q : ℝ) ≤ ((N : ℝ) + 2) ^ 3 / R :=
    hqUpper.trans (hmiddle.trans htop)
  refine ⟨a, q, beta, z, ?_, ?_, ha, hac, halpha,
    ⟨hbeta, hscaledBeta, hscaledBetaOne⟩⟩
  · simpa [R, L] using hlower
  · simpa [R, L] using hupper

/-- Dirichlet's theorem at the chosen integer height, normalized into
the repository's reduced-center and wrapped-displacement convention. -/
theorem exists_auxiliaryDirichletWitness
    {N : ℕ} (hN : 0 < N) (alpha : ℝ) :
    ∃ a q : ℕ, ∃ beta : ℝ, ∃ z : ℤ,
      0 < q ∧ q ≤ cubicAuxiliaryHeight N ∧ a < q ∧
      Nat.Coprime a q ∧
      alpha = rationalCenter a q + beta + z ∧
      |beta| ≤ 1 / (((cubicAuxiliaryHeight N : ℝ) + 1) * (q : ℝ)) := by
  have hH : 0 < cubicAuxiliaryHeight N := by
    have hP : (0 : ℝ) < cubicAuxiliaryCutoff N := by
      exact_mod_cast cubicAuxiliaryCutoff_pos hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hlow := (cubicAuxiliaryHeight_bounds hN).1
    have hr : (0 : ℝ) < cubicAuxiliaryHeight N :=
      (div_pos (by positivity) hP).trans_le hlow
    exact_mod_cast hr
  exact exists_reducedCenter_approximation_of_height
    (cubicAuxiliaryHeight N) hH alpha

/-- Every point on the auxiliary minor arcs has a Dirichlet rational
approximant whose reduced denominator exceeds the cubic-root cutoff. -/
theorem exists_large_denominator_of_mem_auxiliaryMinorArcs
    {N : ℕ} (hN : 0 < N) {alpha : ℝ}
    (hminor : alpha ∈ minorArcs N (cubicAuxiliaryCutoff N)) :
    ∃ a q : ℕ, ∃ beta : ℝ, ∃ z : ℤ,
      cubicAuxiliaryCutoff N < q ∧ q ≤ cubicAuxiliaryHeight N ∧
      a < q ∧ Nat.Coprime a q ∧
      alpha = rationalCenter a q + beta + z ∧
      |beta| ≤ 1 / (((cubicAuxiliaryHeight N : ℝ) + 1) * (q : ℝ)) := by
  obtain ⟨a, q, beta, z, hq, hqH, ha, hac, halpha, hbeta⟩ :=
    exists_auxiliaryDirichletWitness hN alpha
  have hqP : cubicAuxiliaryCutoff N < q := by
    by_contra hn
    have hqP : q ≤ cubicAuxiliaryCutoff N := Nat.le_of_not_gt hn
    have hmajor := mem_auxiliaryMajorArcs_of_dirichletWitness
      hN hminor.1 hq hqP ha hac halpha hbeta
    exact hminor.2 hmajor
  exact ⟨a, q, beta, z, hqP, hqH, ha, hac, halpha, hbeta⟩

/-- The ordinary cubic sum is invariant under integer shifts of its
frequency, because `m³-m` is an integer. -/
theorem cubicUnweightedExpSum_add_int
    (alpha : ℝ) (z : ℤ) (N : ℕ) :
    cubicUnweightedExpSum (alpha + z) N = cubicUnweightedExpSum alpha N := by
  unfold cubicUnweightedExpSum
  simp_rw [CookMagyarArcs.addChar_add_int]

/-- The normalized Dirichlet witness on an auxiliary minor arc has
exactly the denominator range and rational error required by ordinary
polynomial Weyl, with the periodic phase shift removed. -/
theorem exists_weylData_of_mem_auxiliaryMinorArcs
    {N : ℕ} (hN : 0 < N) {alpha : ℝ}
    (hminor : alpha ∈ minorArcs N (cubicAuxiliaryCutoff N)) :
    ∃ a q : ℕ, ∃ beta : ℝ,
      cubicAuxiliaryCutoff N < q ∧
      (q : ℝ) ≤ 3 * (N : ℝ) ^ 3 / (cubicAuxiliaryCutoff N : ℝ) ∧
      a < q ∧ Nat.Coprime a q ∧
      |beta| ≤ 1 / (q : ℝ) ^ 2 ∧
      cubicUnweightedExpSum alpha N =
        cubicUnweightedExpSum (rationalCenter a q + beta) N := by
  obtain ⟨a, q, beta, z, hqP, hqH, ha, hac, halpha, hbeta⟩ :=
    exists_large_denominator_of_mem_auxiliaryMinorArcs hN hminor
  have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) hqP
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hqHr : (q : ℝ) ≤ cubicAuxiliaryHeight N := by exact_mod_cast hqH
  have hden : (0 : ℝ) < ((cubicAuxiliaryHeight N : ℝ) + 1) * q := by
    positivity
  have hqden : (q : ℝ) ^ 2 ≤
      ((cubicAuxiliaryHeight N : ℝ) + 1) * q := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hqHr) (le_of_lt hqr)]
  have hfrac : 1 / (((cubicAuxiliaryHeight N : ℝ) + 1) * q) ≤
      1 / (q : ℝ) ^ 2 := by
    exact (div_le_div_iff₀ hden (pow_pos hqr 2)).2 (by nlinarith [hqden])
  refine ⟨a, q, beta, hqP, ?_, ha, hac, hbeta.trans hfrac, ?_⟩
  · exact hqHr.trans (cubicAuxiliaryHeight_bounds hN).2
  · rw [halpha, cubicUnweightedExpSum_add_int]

/-- The proved all-residue local approximation has the required
`N^(2/3)` scale for the integer auxiliary cutoff. -/
theorem norm_cubicUnweightedExpSum_sub_homogeneousModel_le_powerCutoff
    (q a N : ℕ) [NeZero q] (hq : 0 < q) (hN : 0 < N)
    (hqP : q ≤ cubicAuxiliaryCutoff N) (beta : ℝ)
    (hbeta : |beta| * (N : ℝ) ^ 3 ≤ (cubicAuxiliaryCutoff N : ℝ)) :
    ‖cubicUnweightedExpSum (rationalCenter a q + beta) N -
        cubicAllResidueHomogeneousModel q (a : ZMod q) beta N‖ ≤
      256 * ((N : ℝ) ^ ((3 : ℝ)⁻¹)) ^ 2 := by
  have hlocal := norm_cubicUnweightedExpSum_sub_homogeneousModel_le_auxCutoff
    q a N (cubicAuxiliaryCutoff N) hq hN hqP beta hbeta
  have hroot := cubicAuxiliaryCutoff_add_one_le_two_realRoot hN
  have hsq : ((cubicAuxiliaryCutoff N : ℝ) + 1) ^ 2 ≤
      (2 * (N : ℝ) ^ ((3 : ℝ)⁻¹)) ^ 2 := by
    gcongr
  calc
    ‖cubicUnweightedExpSum (rationalCenter a q + beta) N -
        cubicAllResidueHomogeneousModel q (a : ZMod q) beta N‖ ≤
      64 * ((cubicAuxiliaryCutoff N : ℝ) + 1) ^ 2 := hlocal
    _ ≤ 64 * (2 * (N : ℝ) ^ ((3 : ℝ)⁻¹)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = 256 * ((N : ℝ) ^ ((3 : ℝ)⁻¹)) ^ 2 := by ring

end CookMagyarMajorArc
end SystolicGrowth

#print axioms SystolicGrowth.CookMagyarMajorArc.dirichletError_lt_cubicArcRadius_of_height
#print axioms SystolicGrowth.CookMagyarMajorArc.exists_large_denominator_of_mem_minorArcs_of_height
#print axioms SystolicGrowth.CookMagyarMajorArc.eventually_exists_logarithmicPrimeMinorArcWeylData
#print axioms SystolicGrowth.CookMagyarMajorArc.eventually_exists_logarithmicPrimeMinorArcWeylData_at_scale
#print axioms SystolicGrowth.CookMagyarMajorArc.eventually_exists_logarithmicPrimeMinorArcWeylData_huaWindow
