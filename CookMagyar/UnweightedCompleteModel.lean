module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.UnweightedResidueAbel
public import CookMagyar.HuaOrthogonality
public import CookMagyar.MajorArcArithmetic
public import CookMagyar.CubicResidueAbel

@[expose] public section

open Finset MeasureTheory
open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarMajorArc

open CookMagyarCircle CookMagyarArcs CookMagyarFiniteFourier

/-! # The all-residue complete cubic model -/

/-- The complete cubic sum includes *all* residues, not only units. -/
noncomputable def allResidueCubicExponentialSum
    (q : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
  ∑ r : ZMod q, standardAdditiveCharacter (a * cubicResidue r)

private theorem cubicUnweightedResidueClassSum_eq_subtype
    (q : ℕ) [NeZero q] (r : ZMod q) (beta : ℝ) (N : ℕ) :
    cubicUnweightedResidueClassSum q r.val beta N =
      ∑ x : {x : Fin (N + 1) // ((x : ℕ) : ZMod q) = r},
        addChar beta (primeCubic (x : ℕ)) := by
  classical
  let p : Fin (N + 1) → Prop := fun x => ((x : ℕ) : ZMod q) = r
  have hfilter :
      (∑ x : {x : Fin (N + 1) // p x},
        addChar beta (primeCubic (x : ℕ))) =
      ∑ x ∈ (Finset.univ : Finset (Fin (N + 1))).filter p,
        addChar beta (primeCubic (x : ℕ)) := by
    simpa using (Finset.sum_subtype_eq_sum_filter
      (s := (Finset.univ : Finset (Fin (N + 1)))) (p := p)
      (fun x => addChar beta (primeCubic (x : ℕ))))
  rw [hfilter, Finset.sum_filter]
  unfold cubicUnweightedResidueClassSum
  rw [← Nat.range_succ_eq_Icc_zero]
  rw [← Fin.sum_univ_eq_sum_range
    (fun k : ℕ => if k ≡ r.val [MOD q] then
      addChar beta (primeCubic k) else 0) (N + 1)]
  apply Finset.sum_congr rfl
  intro x _
  have hp : ((x : ℕ) : ZMod q) = r ↔ (x : ℕ) ≡ r.val [MOD q] := by
    constructor
    · intro h
      apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
      exact h.trans (ZMod.natCast_zmod_val r).symm
    · intro h
      exact ((ZMod.natCast_eq_natCast_iff _ _ _).mpr h).trans
        (ZMod.natCast_zmod_val r)
  by_cases hx : (x : ℕ) ≡ r.val [MOD q]
  · simp [hp.mpr hx, hx]
  · simp [hp.not.mpr hx, hx]

/-- Exact decomposition of the ordinary cubic sum into all residue
classes at a rational center. -/
theorem cubicUnweightedExpSum_rationalCenter_add
    (q a N : ℕ) [NeZero q] (_hq : 0 < q) (beta : ℝ) :
    cubicUnweightedExpSum (rationalCenter a q + beta) N =
      ∑ r : ZMod q,
        standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
          cubicUnweightedResidueClassSum q r.val beta N := by
  classical
  rw [cubicUnweightedExpSum_eq_finSum]
  rw [← Fintype.sum_fiberwise
    (fun x : Fin (N + 1) => ((x : ℕ) : ZMod q))
    (fun x : Fin (N + 1) =>
      addChar (rationalCenter a q + beta) (primeCubic (x : ℕ)))]
  apply Finset.sum_congr rfl
  intro r _
  rw [cubicUnweightedResidueClassSum_eq_subtype q r beta N,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [addChar_add_real, addChar_rationalCenter]
  have hres :
      ((primeCubic (x : ℕ) : ℕ) : ZMod q) = cubicResidue r := by
    rw [cast_primeCubic_zmod]
    exact congrArg cubicResidue x.property
  rw [hres]

/-- Every all-residue class has the same uniform-density model, so their
main terms recombine into the complete sum. -/
theorem sum_allResidueCubicModels_eq_complete
    (q a N : ℕ) [NeZero q] (_hq : 0 < q) (beta : ℝ) :
    (∑ r : ZMod q,
      standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
        cubicUnweightedResidueClassModel q beta N) =
      allResidueCubicExponentialSum q (a : ZMod q) *
        cubicUnweightedResidueClassModel q beta N := by
  unfold allResidueCubicExponentialSum
  rw [Finset.sum_mul]

/-- Elementary unweighted major-arc model, before replacing the finite
real cubic phase sum by its homogeneous integral. -/
theorem norm_cubicUnweightedExpSum_sub_allResidueModel_le
    (q a N : ℕ) [NeZero q] (hq : 0 < q) (hN : 0 < N) (beta : ℝ) :
    ‖cubicUnweightedExpSum (rationalCenter a q + beta) N -
        allResidueCubicExponentialSum q (a : ZMod q) *
          cubicUnweightedResidueClassModel q beta N‖ ≤
      (q : ℝ) *
        (1 + (N : ℝ) *
          (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1))) := by
  classical
  rw [cubicUnweightedExpSum_rationalCenter_add q a N hq beta,
    ← sum_allResidueCubicModels_eq_complete q a N hq beta,
    ← Finset.sum_sub_distrib]
  have hnorm (r : ZMod q) :
      ‖standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
          cubicUnweightedResidueClassSum q r.val beta N -
        standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
          cubicUnweightedResidueClassModel q beta N‖ ≤
        1 + (N : ℝ) *
          (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1)) := by
    rw [← mul_sub, norm_mul, AddChar.norm_apply, one_mul]
    exact norm_cubicUnweightedResidueClassSum_sub_model_le
      q r.val hq beta N hN
  calc
    ‖∑ r : ZMod q,
      (standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
          cubicUnweightedResidueClassSum q r.val beta N -
        standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
          cubicUnweightedResidueClassModel q beta N)‖ ≤
        ∑ r : ZMod q,
          ‖standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
              cubicUnweightedResidueClassSum q r.val beta N -
            standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
              cubicUnweightedResidueClassModel q beta N‖ := norm_sum_le _ _
    _ ≤ ∑ _r : ZMod q,
          (1 + (N : ℝ) *
            (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1))) := by
      exact Finset.sum_le_sum (fun r _ => hnorm r)
    _ = (q : ℝ) *
          (1 + (N : ℝ) *
            (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1))) := by
      simp
      ring

/-- The complete all-residue cubic sum has the trivial norm bound `q`. -/
theorem norm_allResidueCubicExponentialSum_le
    (q : ℕ) [NeZero q] (a : ZMod q) :
    ‖allResidueCubicExponentialSum q a‖ ≤ (q : ℝ) := by
  classical
  unfold allResidueCubicExponentialSum
  calc
    ‖∑ r : ZMod q, standardAdditiveCharacter (a * cubicResidue r)‖ ≤
        ∑ r : ZMod q,
          ‖standardAdditiveCharacter (a * cubicResidue r)‖ :=
      norm_sum_le _ _
    _ = (q : ℝ) := by simp [AddChar.norm_apply]

/-- The ordinary cubic complete sum times the real integral with the
*inhomogeneous* phase `t³-t`. -/
noncomputable def cubicAllResidueIntegralModel
    (q : ℕ) [NeZero q] (a : ZMod q) (beta : ℝ) (N : ℕ) : ℂ :=
  allResidueCubicExponentialSum q a * ((1 / (q : ℝ) : ℝ) : ℂ) *
    ∫ t in Set.Icc (0 : ℝ) N, cubicAbelWeight beta t

/-- The all-residue complete model with its real integral, before the
homogeneous-cubic replacement. -/
theorem norm_cubicUnweightedExpSum_sub_allResidueIntegralModel_le
    (q a N : ℕ) [NeZero q] (hq : 0 < q) (hN : 0 < N) (beta : ℝ) :
    ‖cubicUnweightedExpSum (rationalCenter a q + beta) N -
        cubicAllResidueIntegralModel q (a : ZMod q) beta N‖ ≤
      ((q : ℝ) + 1) *
        (1 + (N : ℝ) *
          (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1))) := by
  let C : ℂ := allResidueCubicExponentialSum q (a : ZMod q)
  let E : ℝ := 1 + (N : ℝ) *
    (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1))
  let S : ℂ := ∑ k ∈ Icc 0 N, addChar beta (primeCubic k)
  let V : ℂ := ∫ t in Set.Icc (0 : ℝ) N, cubicAbelWeight beta t
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hC : ‖C‖ ≤ (q : ℝ) :=
    norm_allResidueCubicExponentialSum_le q (a : ZMod q)
  have hcoef : ‖C * ((1 / (q : ℝ) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (q : ℝ))]
    calc
      ‖C‖ * (1 / (q : ℝ)) ≤ (q : ℝ) * (1 / (q : ℝ)) :=
        mul_le_mul_of_nonneg_right hC (by positivity)
      _ = 1 := by field_simp
  have hSV : ‖S - V‖ ≤ E := by
    dsimp [S, V, E]
    simpa only [cubicAbelWeight_nat] using
      norm_sum_cubicAbelWeight_sub_integral_le beta N
  have hmodel :
      ‖C * cubicUnweightedResidueClassModel q beta N -
          cubicAllResidueIntegralModel q (a : ZMod q) beta N‖ ≤ E := by
    have heq :
        C * cubicUnweightedResidueClassModel q beta N -
            cubicAllResidueIntegralModel q (a : ZMod q) beta N =
          (C * ((1 / (q : ℝ) : ℝ) : ℂ)) * (S - V) := by
      dsimp [C, S, V, cubicUnweightedResidueClassModel,
        cubicAllResidueIntegralModel]
      ring
    rw [heq, norm_mul]
    simpa only [one_mul] using
      (mul_le_mul hcoef hSV (norm_nonneg _) (by norm_num))
  have hfinite :
      ‖cubicUnweightedExpSum (rationalCenter a q + beta) N -
          C * cubicUnweightedResidueClassModel q beta N‖ ≤ (q : ℝ) * E := by
    simpa only [C, E] using
      norm_cubicUnweightedExpSum_sub_allResidueModel_le q a N hq hN beta
  calc
    ‖cubicUnweightedExpSum (rationalCenter a q + beta) N -
        cubicAllResidueIntegralModel q (a : ZMod q) beta N‖ ≤
      ‖cubicUnweightedExpSum (rationalCenter a q + beta) N -
          C * cubicUnweightedResidueClassModel q beta N‖ +
        ‖C * cubicUnweightedResidueClassModel q beta N -
          cubicAllResidueIntegralModel q (a : ZMod q) beta N‖ := by
      calc
        ‖cubicUnweightedExpSum (rationalCenter a q + beta) N -
            cubicAllResidueIntegralModel q (a : ZMod q) beta N‖ =
          ‖(cubicUnweightedExpSum (rationalCenter a q + beta) N -
              C * cubicUnweightedResidueClassModel q beta N) +
            (C * cubicUnweightedResidueClassModel q beta N -
              cubicAllResidueIntegralModel q (a : ZMod q) beta N)‖ := by
            congr 1
            ring
        _ ≤ _ := norm_add_le _ _
    _ ≤ (q : ℝ) * E + E := add_le_add hfinite hmodel
    _ = ((q : ℝ) + 1) * E := by ring

end CookMagyarMajorArc
end SystolicGrowth
