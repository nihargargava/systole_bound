module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Topology.Order.LeftRightNhds

@[expose] public section

/-!
# Interval calculus for Lipschitz complex coordinate curves

The only regularity assumption is Lipschitz continuity on the closed interval.
Coordinatewise absolute continuity supplies the genuine derivative almost
everywhere and the fundamental theorem of calculus. No differentiability
outside the interval, or at either endpoint, is assumed.
-/

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace SystolicGrowth

/-- A real derivative vanishes almost everywhere on each level set. At every
accumulation point of the level set this follows from the difference
quotients; the remaining isolated points are countable. This handles paths
that spend positive measure on a nonsmooth seam, rather than discarding the
seam preimage as a null set. -/
theorem deriv_eq_zero_ae_on_level_set (f : ℝ → ℝ) (c : ℝ) :
    ∀ᵐ t ∂volume, f t = c → deriv f t = 0 := by
  let S : Set ℝ := {t | f t = c}
  let isolated : Set ℝ := {t ∈ S | 𝓝[S ∩ Ioi t] t = ⊥}
  have hisolated : isolated.Countable := by
    exact (countable_setOf_isolated_right_within (s := S)).mono
      (by intro t ht; exact ht)
  let bad : Set ℝ := {t | f t = c ∧ deriv f t ≠ 0}
  have hbad : bad ⊆ isolated := by
    intro t ht
    have hacc : ¬ AccPt t (𝓟 S) := by
      intro hacc
      have hfreq : ∃ᶠ y in 𝓝[≠] t, f y = c := by
        have hfreqS : ∃ᶠ y in 𝓝[≠] t, y ∈ S := by
          have hwithin : (𝓝[S \ {t}] t).NeBot :=
            (accPt_principal_iff_nhdsWithin).mp hacc
          have hfreqWithin : ∃ᶠ y in 𝓝[S \ {t}] t, y ∈ S :=
            frequently_mem_iff_neBot.mpr (by
              have hfilter : 𝓝[S \ {t}] t ⊓ 𝓟 S = 𝓝[S \ {t}] t := by
                rw [nhdsWithin, inf_assoc, inf_principal]
                rw [show S \ {t} ∩ S = S \ {t} by
                  ext y
                  simp only [Set.mem_inter_iff, Set.mem_sdiff]
                  tauto]
              rw [hfilter]
              exact hwithin)
          exact hfreqWithin.filter_mono (nhdsWithin_mono t (by
            intro y hy
            exact hy.2))
        simpa only [S, mem_setOf_eq] using hfreqS
      exact ht.2 (deriv_zero_of_frequently_const hfreq)
    have hbot : 𝓝[S \ {t}] t = ⊥ := by
      by_contra h
      exact hacc ((accPt_principal_iff_nhdsWithin).mpr (neBot_iff.mpr h))
    have hright : 𝓝[S ∩ Ioi t] t = ⊥ := by
      apply le_bot_iff.mp
      exact (nhdsWithin_mono t (by
        intro y hy
        exact ⟨hy.1, ne_of_gt hy.2⟩)).trans_eq hbot
    exact ⟨ht.1, hright⟩
  have hnull : volume bad = 0 :=
    measure_mono_null hbad (hisolated.measure_zero volume)
  rw [ae_iff]
  have hset : {t | ¬(f t = c → deriv f t = 0)} = bad := by
    ext t
    simp [bad]
  rw [hset]
  exact hnull

/-- Pairing two real Lipschitz coordinates gives an ordinary complex
Lipschitz curve; the sum of their constants is a valid complex constant. -/
theorem lipschitzCoordinate_pair {s : Set ℝ} {u v : ℝ → ℝ} {Ku Kv : ℝ≥0}
    (hu : LipschitzOnWith Ku u s) (hv : LipschitzOnWith Kv v s) :
    LipschitzOnWith (Ku + Kv)
      (fun t ↦ Complex.ofReal (u t) + Complex.ofReal (v t) * Complex.I) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hur := hu.dist_le_mul x hx y hy
  have hvr := hv.dist_le_mul x hx y hy
  rw [Real.dist_eq] at hur hvr
  have hdiff : (Complex.ofReal (u x) + Complex.ofReal (v x) * Complex.I) -
      (Complex.ofReal (u y) + Complex.ofReal (v y) * Complex.I) =
      Complex.ofReal (u x - u y) + Complex.ofReal (v x - v y) * Complex.I := by
    simp only [Complex.ofReal_sub]
    ring
  calc
    _ = ‖Complex.ofReal (u x - u y) + Complex.ofReal (v x - v y) * Complex.I‖ := by
      rw [dist_eq_norm, hdiff]
    _ ≤ ‖Complex.ofReal (u x - u y)‖ +
        ‖Complex.ofReal (v x - v y) * Complex.I‖ := norm_add_le _ _
    _ = |u x - u y| + |v x - v y| := by
      simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ Ku * dist x y + Kv * dist x y := add_le_add hur hvr
    _ = (Ku + Kv : ℝ≥0) * dist x y := by simp only [NNReal.coe_add]; ring

/-- Ordinary complex Lipschitz continuity on the interval is equivalent
to Lipschitz continuity of both genuine real coordinate functions. -/
theorem lipschitzCoordinate_iff_re_im {α : ℝ → ℂ} {a b : ℝ} :
    (∃ K : ℝ≥0, LipschitzOnWith K α (Icc a b)) ↔
      ∃ Ku Kv : ℝ≥0,
        LipschitzOnWith Ku (fun t ↦ (α t).re) (Icc a b) ∧
          LipschitzOnWith Kv (fun t ↦ (α t).im) (Icc a b) := by
  constructor
  · rintro ⟨K, hα⟩
    refine ⟨K, K, ?_, ?_⟩
    · simpa [Function.comp_def] using
        (RCLike.lipschitzWith_re (K := ℂ)).comp_lipschitzOnWith hα
    · simpa [Function.comp_def] using
        (RCLike.lipschitzWith_im (K := ℂ)).comp_lipschitzOnWith hα
  · rintro ⟨Ku, Kv, hu, hv⟩
    refine ⟨Ku + Kv, ?_⟩
    simpa only [Complex.re_add_im] using lipschitzCoordinate_pair hu hv

private theorem coordinate_absolutelyContinuous {α : ℝ → ℂ} {K : ℝ≥0} {a b : ℝ}
    (hab : a ≤ b) (hα : LipschitzOnWith K α (Icc a b)) :
    AbsolutelyContinuousOnInterval (fun t ↦ (α t).re) a b ∧
      AbsolutelyContinuousOnInterval (fun t ↦ (α t).im) a b := by
  have hreal : LipschitzOnWith K (fun t ↦ (α t).re) (uIcc a b) := by
    simpa [uIcc_of_le hab, Function.comp_def] using
      (RCLike.lipschitzWith_re (K := ℂ)).comp_lipschitzOnWith hα
  have himag : LipschitzOnWith K (fun t ↦ (α t).im) (uIcc a b) := by
    simpa [uIcc_of_le hab, Function.comp_def] using
      (RCLike.lipschitzWith_im (K := ℂ)).comp_lipschitzOnWith hα
  exact ⟨hreal.absolutelyContinuousOnInterval, himag.absolutelyContinuousOnInterval⟩

private theorem lipschitzCoordinate_deriv_ae {α : ℝ → ℂ} {K : ℝ≥0} {a b : ℝ}
    (hab : a ≤ b) (hα : LipschitzOnWith K α (Icc a b)) :
    deriv α =ᵐ[volume.restrict (uIoc a b)]
      fun t ↦ Complex.ofReal (deriv (fun s ↦ (α s).re) t) +
        Complex.ofReal (deriv (fun s ↦ (α s).im) t) * Complex.I := by
  obtain ⟨hr, hi⟩ := coordinate_absolutelyContinuous hab hα
  have hderiv : ∀ᵐ t, t ∈ uIcc a b →
      deriv α t = Complex.ofReal (deriv (fun s ↦ (α s).re) t) +
        Complex.ofReal (deriv (fun s ↦ (α s).im) t) * Complex.I := by
    filter_upwards [hr.ae_differentiableAt, hi.ae_differentiableAt] with t hrt hit ht
    have hd := (hrt ht).hasDerivAt.ofReal_comp.add
      ((hit ht).hasDerivAt.ofReal_comp.mul_const Complex.I)
    change HasDerivAt (fun s ↦ ((α s).re : ℂ) + ((α s).im : ℂ) * Complex.I)
      (Complex.ofReal (deriv (fun s ↦ (α s).re) t) +
        Complex.ofReal (deriv (fun s ↦ (α s).im) t) * Complex.I) t at hd
    have heq : (fun s ↦ ((α s).re : ℂ) + ((α s).im : ℂ) * Complex.I) = α := by
      funext s
      exact Complex.re_add_im (α s)
    rw [heq] at hd
    exact hd.deriv
  filter_upwards [ae_restrict_of_ae hderiv, ae_restrict_mem measurableSet_uIoc] with t ht hmem
  exact ht (uIoc_subset_uIcc hmem)

/-- Actual real and imaginary derivative components agree almost
everywhere on the closed interval; null endpoints are not differentiated. -/
theorem lipschitzCoordinate_deriv_components_ae {α : ℝ → ℂ} {K : ℝ≥0} {a b : ℝ}
    (hab : a ≤ b) (hα : LipschitzOnWith K α (Icc a b)) :
    ∀ᵐ t ∂volume.restrict (Icc a b),
      (deriv α t).re = deriv (fun s ↦ (α s).re) t ∧
        (deriv α t).im = deriv (fun s ↦ (α s).im) t := by
  have hd := lipschitzCoordinate_deriv_ae hab hα
  rw [uIoc_of_le hab, restrict_Ioc_eq_restrict_Icc] at hd
  filter_upwards [hd] with t ht
  rw [ht]
  simp

/-- A complex curve that is Lipschitz on a closed interval is differentiable
almost everywhere there. Pair the absolutely continuous real coordinates to
recover differentiability of the original complex curve. -/
theorem lipschitzComplex_differentiableAt_ae {a b : ℝ} {K : ℝ≥0}
    {β : ℝ → ℂ} (hab : a ≤ b) (hβ : LipschitzOnWith K β (Icc a b)) :
    ∀ᵐ t ∂volume.restrict (Icc a b), DifferentiableAt ℝ β t := by
  obtain ⟨Kr, Ki, hrealIcc, himagIcc⟩ :=
    (lipschitzCoordinate_iff_re_im (α := β) (a := a) (b := b)).mp ⟨K, hβ⟩
  have hreal : LipschitzOnWith Kr (fun t => (β t).re) (uIcc a b) := by
    simpa only [uIcc_of_le hab] using hrealIcc
  have himag : LipschitzOnWith Ki (fun t => (β t).im) (uIcc a b) := by
    simpa only [uIcc_of_le hab] using himagIcc
  have hrealAC := hreal.absolutelyContinuousOnInterval
  have himagAC := himag.absolutelyContinuousOnInterval
  filter_upwards
    [ae_restrict_of_ae hrealAC.ae_differentiableAt,
      ae_restrict_of_ae himagAC.ae_differentiableAt,
      ae_restrict_mem measurableSet_Icc] with t hrd hid ht
  have hmem : t ∈ uIcc a b := by
    simpa only [uIcc_of_le hab] using ht
  have hrd := hrd hmem
  have hid := hid hmem
  let f : ℝ → ℂ := fun s => (β s).re + (β s).im * Complex.I
  have hf := hrd.hasDerivAt.ofReal_comp.add
    (hid.hasDerivAt.ofReal_comp.mul_const Complex.I)
  change HasDerivAt f
    ((deriv (fun s => (β s).re) t : ℝ) +
      (deriv (fun s => (β s).im) t : ℝ) * Complex.I) t at hf
  have hβeq : f = β := by
    funext s
    exact Complex.re_add_im (β s)
  rw [hβeq] at hf
  exact hf.differentiableAt

/-- A real derivative gives the genuine metric-speed limit of the
endpoint-distance quotient, not merely a notation for its derivative. -/
theorem real_metricSpeed_limit_of_hasDerivAt {f : ℝ → ℝ} {f' t : ℝ}
    (hf : HasDerivAt f f' t) :
    Tendsto (fun s ↦ dist (f s) (f t) / dist s t)
      (nhdsWithin t {t}ᶜ) (𝓝 |f'|) := by
  simpa only [slope_def_field, Real.dist_eq, abs_div] using hf.tendsto_slope.abs

/-- Every real interval-Lipschitz curve has the genuine metric speed
`|deriv f|` almost everywhere on the interval, with no derivative premise. -/
theorem lipschitzReal_metricSpeed_limit_ae {f : ℝ → ℝ} {K : ℝ≥0} {a b : ℝ}
    (hab : a ≤ b) (hf : LipschitzOnWith K f (Icc a b)) :
    ∀ᵐ t ∂volume.restrict (Icc a b),
      Tendsto (fun s ↦ dist (f s) (f t) / dist s t)
        (nhdsWithin t {t}ᶜ) (𝓝 |deriv f t|) := by
  have hLip : LipschitzOnWith K f (uIcc a b) := by
    simpa only [uIcc_of_le hab] using hf
  have hac := hLip.absolutelyContinuousOnInterval
  filter_upwards [ae_restrict_of_ae hac.ae_differentiableAt,
    ae_restrict_mem measurableSet_Icc] with t ht hmem
  have hdiff := ht (show t ∈ uIcc a b by simpa only [uIcc_of_le hab] using hmem)
  exact real_metricSpeed_limit_of_hasDerivAt hdiff.hasDerivAt

/-- Actual complex derivatives of interval-Lipschitz coordinate curves are
interval integrable; endpoint derivatives are irrelevant to this statement. -/
theorem lipschitzCoordinate_intervalIntegrable_deriv {α : ℝ → ℂ} {K : ℝ≥0} {a b : ℝ}
    (hab : a ≤ b) (hα : LipschitzOnWith K α (Icc a b)) :
    IntervalIntegrable (deriv α) volume a b := by
  obtain ⟨hr, hi⟩ := coordinate_absolutelyContinuous hab hα
  have hreal : IntervalIntegrable
      (fun t ↦ Complex.ofReal (deriv (fun s ↦ (α s).re) t)) volume a b :=
    ⟨Complex.ofRealCLM.integrable_comp hr.intervalIntegrable_deriv.1,
      Complex.ofRealCLM.integrable_comp hr.intervalIntegrable_deriv.2⟩
  have himag : IntervalIntegrable
      (fun t ↦ Complex.ofReal (deriv (fun s ↦ (α s).im) t)) volume a b :=
    ⟨Complex.ofRealCLM.integrable_comp hi.intervalIntegrable_deriv.1,
      Complex.ofRealCLM.integrable_comp hi.intervalIntegrable_deriv.2⟩
  exact (hreal.add (himag.mul_const Complex.I)).congr_ae
    (lipschitzCoordinate_deriv_ae hab hα).symm

/-- The complex fundamental theorem of calculus derived from interval
Lipschitz continuity, not from a separately supplied derivative hypothesis. -/
theorem lipschitzCoordinate_integral_deriv_eq_sub {α : ℝ → ℂ} {K : ℝ≥0} {a b : ℝ}
    (hab : a ≤ b) (hα : LipschitzOnWith K α (Icc a b)) :
    ∫ t in a..b, deriv α t = α b - α a := by
  obtain ⟨hr, hi⟩ := coordinate_absolutelyContinuous hab hα
  have hreal : IntervalIntegrable
      (fun t ↦ Complex.ofReal (deriv (fun s ↦ (α s).re) t)) volume a b :=
    ⟨Complex.ofRealCLM.integrable_comp hr.intervalIntegrable_deriv.1,
      Complex.ofRealCLM.integrable_comp hr.intervalIntegrable_deriv.2⟩
  have himag : IntervalIntegrable
      (fun t ↦ Complex.ofReal (deriv (fun s ↦ (α s).im) t)) volume a b :=
    ⟨Complex.ofRealCLM.integrable_comp hi.intervalIntegrable_deriv.1,
      Complex.ofRealCLM.integrable_comp hi.intervalIntegrable_deriv.2⟩
  rw [intervalIntegral.integral_congr_ae_restrict (lipschitzCoordinate_deriv_ae hab hα),
    intervalIntegral.integral_add hreal (himag.mul_const Complex.I),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal, hr.integral_deriv_eq_sub, hi.integral_deriv_eq_sub]
  apply Complex.ext <;> simp

/-- Angular endpoint variation is controlled by the genuine angular
derivative integral for every interval-Lipschitz coordinate curve. -/
theorem lipschitzCoordinate_im_sub_le_integral_abs_deriv {α : ℝ → ℂ} {K : ℝ≥0} {a b : ℝ}
    (hab : a ≤ b) (hα : LipschitzOnWith K α (Icc a b)) :
    |(α b).im - (α a).im| ≤ ∫ t in a..b, |(deriv α t).im| := by
  have hint := lipschitzCoordinate_intervalIntegrable_deriv hab hα
  have hFTC := lipschitzCoordinate_integral_deriv_eq_sub hab hα
  have him : ∫ t in a..b, (deriv α t).im = (α b).im - (α a).im := by
    have him' := Complex.imCLM.intervalIntegral_comp_comm hint
    change (∫ t in a..b, (deriv α t).im) = (∫ t in a..b, deriv α t).im at him'
    rw [him', hFTC]
    rfl
  rw [← him]
  simpa only [Real.norm_eq_abs] using
    intervalIntegral.norm_integral_le_integral_norm hab (f := fun t ↦ (deriv α t).im)

#print axioms lipschitzCoordinate_intervalIntegrable_deriv
#print axioms lipschitzCoordinate_integral_deriv_eq_sub
#print axioms lipschitzCoordinate_im_sub_le_integral_abs_deriv
#print axioms lipschitzCoordinate_pair
#print axioms lipschitzCoordinate_iff_re_im
#print axioms lipschitzCoordinate_deriv_components_ae
#print axioms lipschitzComplex_differentiableAt_ae
#print axioms deriv_eq_zero_ae_on_level_set
#print axioms real_metricSpeed_limit_of_hasDerivAt
#print axioms lipschitzReal_metricSpeed_limit_ae

end SystolicGrowth
