module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.ArcGeometry
public import CookMagyar.FiniteFourier

@[expose] public section

open scoped ArithmeticFunction BigOperators

namespace SystolicGrowth
namespace CookMagyarMajorArc

open CookMagyarArcs CookMagyarCircle CookMagyarFiniteFourier

/-! # Exact arithmetic decomposition on a cubic major arc

Before invoking primes in arithmetic progressions, the von--Mangoldt sum at
`a/q + beta` splits exactly into residue-class sums modulo `q`.  The finite
cubic character is constant on each fiber.  This module proves that identity
without any asymptotic input.
-/

theorem cast_primeCubic_zmod {q : ℕ} [NeZero q] (x : ℕ) :
    (primeCubic x : ZMod q) = cubicResidue (x : ZMod q) := by
  unfold primeCubic cubicResidue
  rw [Nat.cast_sub (Nat.le_pow (by norm_num : 0 < 3))]
  push_cast
  ring

theorem addChar_add_real (alpha beta : ℝ) (k : ℕ) :
    addChar (alpha + beta) k = addChar alpha k * addChar beta k := by
  unfold addChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A real rational phase agrees exactly with the standard additive
character on `ZMod q`. -/
theorem addChar_rationalCenter
    {q : ℕ} [NeZero q] (a k : ℕ) :
    addChar (rationalCenter a q) k =
      standardAdditiveCharacter ((a : ZMod q) * (k : ZMod q)) := by
  unfold rationalCenter
  change addChar ((a : ℝ) / (q : ℝ)) k =
    ZMod.stdAddChar ((a : ZMod q) * (k : ZMod q))
  rw [show (a : ZMod q) * (k : ZMod q) =
      (((a * k : ℤ) : ZMod q)) by norm_num]
  rw [ZMod.stdAddChar_coe]
  unfold addChar
  push_cast
  congr 1
  field_simp [NeZero.ne q]

/-- The negative Fourier phase at a rational center is exactly the finite
standard additive character at the negative residue. -/
theorem negAddChar_rationalCenter
    {q : ℕ} [NeZero q] (a T : ℕ) :
    negAddChar (rationalCenter a q) T =
      standardAdditiveCharacter (-((a : ZMod q) * (T : ZMod q))) := by
  have hneg (alpha : ℝ) : negAddChar alpha T = (addChar alpha T)⁻¹ := by
    unfold negAddChar addChar
    rw [show (-2 * Real.pi * Complex.I * (alpha : ℂ) * (T : ℂ)) =
      -(2 * Real.pi * Complex.I * (T : ℂ) * (alpha : ℂ)) by ring,
      Complex.exp_neg]
  rw [hneg, addChar_rationalCenter]
  exact (standardAdditiveCharacter.map_neg_eq_inv
    ((a : ZMod q) * (T : ZMod q))).symm

/-- The weighted cubic sum in one residue class modulo `q`, with only the
small real displacement `beta` left in the phase. -/
noncomputable def cubicResidueClassSum
    (q : ℕ) [NeZero q] (r : ZMod q) (beta : ℝ) (N : ℕ) : ℂ :=
  ∑ x : {x : Fin (N + 1) // ((x : ℕ) : ZMod q) = r},
    (ArithmeticFunction.vonMangoldt (x : ℕ) : ℂ) *
      addChar beta (primeCubic (x : ℕ))

/-- **Exact major-arc residue decomposition.**  No prime-number theorem or
error estimate occurs here. -/
theorem cubicVonMangoldtExpSum_rationalCenter_add
    {q : ℕ} [NeZero q] (a : ℕ) (beta : ℝ) (N : ℕ) :
    cubicVonMangoldtExpSum (rationalCenter a q + beta) N =
      ∑ r : ZMod q,
        standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
          cubicResidueClassSum q r beta N := by
  classical
  unfold cubicVonMangoldtExpSum
  rw [← Fintype.sum_fiberwise
    (fun x : Fin (N + 1) => ((x : ℕ) : ZMod q))
    (fun x : Fin (N + 1) =>
      (ArithmeticFunction.vonMangoldt (x : ℕ) : ℂ) *
        addChar (rationalCenter a q + beta) (primeCubic (x : ℕ)))]
  apply Finset.sum_congr rfl
  intro r _hr
  unfold cubicResidueClassSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [addChar_add_real, addChar_rationalCenter]
  have hres :
      ((primeCubic (x : ℕ) : ℕ) : ZMod q) = cubicResidue r := by
    rw [cast_primeCubic_zmod]
    exact congrArg cubicResidue x.property
  rw [hres]
  ring

/-- The canonical equivalence between units and elements equipped with a
proof of being a unit. -/
noncomputable def unitsEquivIsUnit (R : Type*) [Monoid R] :
    Rˣ ≃ {r : R // IsUnit r} where
  toFun u := ⟨(u : R), u.isUnit⟩
  invFun r := r.property.unit
  left_inv u := by
    apply Units.ext
    exact rfl
  right_inv r := by
    apply Subtype.ext
    exact r.property.unit_spec

/-- Reduced integer representatives modulo `q` are equivalent to the units
of `ZMod q`; this is the finite indexing bridge for summing over major-arc
centers. -/
noncomputable def reducedResiduesEquivUnits (q : ℕ) [NeZero q] :
    {a : ℕ // a < q ∧ Nat.Coprime a q} ≃ (ZMod q)ˣ where
  toFun a := ((ZMod.isUnit_iff_coprime a.1 q).mpr a.2.2).unit
  invFun u := ⟨(u : ZMod q).val,
    ⟨(u : ZMod q).val_lt,
      (ZMod.isUnit_iff_coprime (u : ZMod q).val q).mp (by
        simpa only [ZMod.natCast_zmod_val] using u.isUnit)⟩⟩
  left_inv a := by
    apply Subtype.ext
    exact ZMod.val_natCast_of_lt a.2.1
  right_inv u := by
    apply Units.ext
    exact ZMod.natCast_zmod_val (u : ZMod q)

/-- The expected residue-class contribution: the common main value `M` on
unit classes and zero on nonunit classes. -/
noncomputable def residueClassMain {q : ℕ} [NeZero q]
    (r : ZMod q) (M : ℂ) : ℂ :=
  if IsUnit r then M else 0

/-- Unit residue classes recombine exactly into the complete cubic sum. -/
theorem sum_character_mul_residueClassMain
    {q : ℕ} [NeZero q] (a : ZMod q) (M : ℂ) :
    (∑ r : ZMod q,
        standardAdditiveCharacter (a * cubicResidue r) *
          residueClassMain r M) =
      unitCubicExponentialSum a * M := by
  classical
  unfold residueClassMain unitCubicExponentialSum
  calc
    (∑ r : ZMod q,
        standardAdditiveCharacter (a * cubicResidue r) *
          (if IsUnit r then M else 0)) =
        ∑ r : {r : ZMod q // IsUnit r},
          standardAdditiveCharacter (a * cubicResidue (r : ZMod q)) * M := by
      have h := Fintype.sum_subtype_add_sum_subtype
        (fun r : ZMod q => IsUnit r)
        (fun r => standardAdditiveCharacter (a * cubicResidue r) *
          (if IsUnit r then M else 0))
      have hpos :
          (∑ r : {r : ZMod q // IsUnit r},
            standardAdditiveCharacter (a * cubicResidue (r : ZMod q)) *
              (if IsUnit (r : ZMod q) then M else 0)) =
            ∑ r : {r : ZMod q // IsUnit r},
              standardAdditiveCharacter (a * cubicResidue (r : ZMod q)) * M := by
        apply Finset.sum_congr rfl
        intro r _hr
        rw [if_pos r.property]
      have hneg :
          (∑ r : {r : ZMod q // ¬IsUnit r},
            standardAdditiveCharacter (a * cubicResidue (r : ZMod q)) *
              (if IsUnit (r : ZMod q) then M else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro r _hr
        rw [if_neg r.property, mul_zero]
      rw [hpos, hneg, add_zero] at h
      exact h.symm
    _ = ∑ u : (ZMod q)ˣ,
          standardAdditiveCharacter (a * cubicResidue (u : ZMod q)) * M := by
      symm
      exact (unitsEquivIsUnit (ZMod q)).sum_comp
        (fun r => standardAdditiveCharacter
          (a * cubicResidue (r : ZMod q)) * M)
    _ = (∑ u : (ZMod q)ˣ,
          standardAdditiveCharacter (a * cubicResidue (u : ZMod q))) * M := by
      rw [Finset.sum_mul]

/-- Per-residue progression errors bound the complete major-arc error.  The
finite character has norm one, so no loss other than summing the residue
errors occurs. -/
theorem norm_cubicVonMangoldtExpSum_sub_completeModel_le
    {q : ℕ} [NeZero q] (a : ℕ) (beta : ℝ) (N : ℕ)
    (M : ℂ) (E : ZMod q → ℝ)
    (hE : ∀ r : ZMod q,
      ‖cubicResidueClassSum q r beta N - residueClassMain r M‖ ≤ E r) :
    ‖cubicVonMangoldtExpSum (rationalCenter a q + beta) N -
        unitCubicExponentialSum (a : ZMod q) * M‖ ≤
      ∑ r : ZMod q, E r := by
  rw [cubicVonMangoldtExpSum_rationalCenter_add,
    ← sum_character_mul_residueClassMain]
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ r : ZMod q, (
        standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
            cubicResidueClassSum q r beta N -
          standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
            residueClassMain r M)‖ ≤
        ∑ r : ZMod q,
          ‖standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
              cubicResidueClassSum q r beta N -
            standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
              residueClassMain r M‖ := norm_sum_le _ _
    _ = ∑ r : ZMod q,
          ‖cubicResidueClassSum q r beta N - residueClassMain r M‖ := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [← mul_sub, norm_mul, AddChar.norm_apply, one_mul]
    _ ≤ ∑ r : ZMod q, E r := by
      exact Finset.sum_le_sum fun r _hr => hE r

/-- A uniform bound on two complex numbers propagates a first-power error
through the `n`th power with the standard telescoping loss. -/
theorem norm_pow_sub_pow_le
    (x y : ℂ) (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) :
    ‖x ^ n - y ^ n‖ ≤ (n : ℝ) * B ^ (n - 1) * ‖x - y‖ := by
  have hgeom := geom_sum₂_mul x y n
  calc
    ‖x ^ n - y ^ n‖ =
        ‖(∑ j ∈ Finset.range n, x ^ j * y ^ (n - 1 - j)) * (x - y)‖ := by
      rw [hgeom]
    _ ≤ (∑ _j ∈ Finset.range n, B ^ (n - 1)) * ‖x - y‖ := by
      rw [norm_mul]
      gcongr
      calc
        ‖∑ j ∈ Finset.range n, x ^ j * y ^ (n - 1 - j)‖ ≤
            ∑ j ∈ Finset.range n, ‖x ^ j * y ^ (n - 1 - j)‖ :=
          norm_sum_le _ _
        _ ≤ ∑ _j ∈ Finset.range n, B ^ (n - 1) := by
          apply Finset.sum_le_sum
          intro j hj
          rw [norm_mul, norm_pow, norm_pow]
          have hjlt : j < n := Finset.mem_range.mp hj
          calc
            ‖x‖ ^ j * ‖y‖ ^ (n - 1 - j) ≤
                B ^ j * B ^ (n - 1 - j) := by
              exact mul_le_mul
                (pow_le_pow_left₀ (norm_nonneg x) hx j)
                (pow_le_pow_left₀ (norm_nonneg y) hy (n - 1 - j))
                (pow_nonneg (norm_nonneg y) _)
                (pow_nonneg hB _)
            _ = B ^ (n - 1) := by
              rw [← pow_add]
              congr 1
              omega
    _ = (n : ℝ) * B ^ (n - 1) * ‖x - y‖ := by simp

/-- The residue-class errors therefore control the powered Fourier
integrand on an individual major arc.  The target character again costs no
norm, so this estimate is uniform in `T`. -/
theorem norm_cubicIntegrand_sub_completeModel_le
    {q : ℕ} [NeZero q] (a : ℕ) (beta : ℝ) (N n T : ℕ)
    (M : ℂ) (E : ZMod q → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hfull :
      ‖cubicVonMangoldtExpSum (rationalCenter a q + beta) N‖ ≤ B)
    (hmodel : ‖unitCubicExponentialSum (a : ZMod q) * M‖ ≤ B)
    (hE : ∀ r : ZMod q,
      ‖cubicResidueClassSum q r beta N - residueClassMain r M‖ ≤ E r) :
    ‖cubicIntegrand n N T (rationalCenter a q + beta) -
        (unitCubicExponentialSum (a : ZMod q) * M) ^ n *
          negAddChar (rationalCenter a q + beta) T‖ ≤
      (n : ℝ) * B ^ (n - 1) * ∑ r : ZMod q, E r := by
  unfold cubicIntegrand
  rw [← sub_mul, norm_mul, norm_negAddChar, mul_one]
  exact (norm_pow_sub_pow_le _ _ n hB hfull hmodel).trans
    (mul_le_mul_of_nonneg_left
      (norm_cubicVonMangoldtExpSum_sub_completeModel_le
        a beta N M E hE)
      (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hB _)))

end CookMagyarMajorArc
end SystolicGrowth
