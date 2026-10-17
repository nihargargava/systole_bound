module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.SiegelEstermann
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# A uniform zeta logarithmic-derivative correction near its simple pole

The actual entire regular part `riemannZeta₀` and its derivative are bounded
on the compact Estermann disc. On a smaller disc around `1`, the normalized
factor `riemannZeta₁ = 1 + (s - 1) * riemannZeta₀ s` stays at distance at least
`1/2` from zero. The actual simple-pole decomposition therefore bounds the
correction `logDeriv ζ(s) + (s - 1)⁻¹`, uniformly on that punctured disc.
-/

open Metric

namespace SystolicGrowth.CookMagyarMajorArc

private theorem exists_zeta_regularPart_and_deriv_bound :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ s ∈ closedBall (2 : ℂ) (3 / 2),
      ‖riemannZeta₀ s‖ ≤ M ∧ ‖deriv riemannZeta₀ s‖ ≤ M := by
  obtain ⟨B, hB, hbound⟩ := CookMagyarCircle.exists_estermann_zeta_bound
  have hcompact : IsCompact (deriv riemannZeta₀ '' closedBall (2 : ℂ) (3 / 2)) :=
    (isCompact_closedBall (2 : ℂ) (3 / 2)).image
      differentiable_riemannZeta₀.deriv.continuous
  obtain ⟨D, hD⟩ := hcompact.isBounded.exists_norm_le
  refine ⟨max B D, hB.trans (le_max_left _ _), ?_⟩
  intro s hs
  exact ⟨(hbound s hs).trans (le_max_left _ _),
    (hD _ ⟨s, hs, rfl⟩).trans (le_max_right _ _)⟩

private theorem deriv_riemannZeta_regularFactor (s : ℂ) :
    deriv riemannZeta₁ s = riemannZeta₀ s + (s - 1) * deriv riemannZeta₀ s := by
  unfold riemannZeta₁
  rw [deriv_const_add, deriv_fun_mul (by fun_prop) (by fun_prop)]
  simp

private theorem logDeriv_riemannZeta_pole_correction
    {s : ℂ} (hs : s ≠ 1) (hfactor : riemannZeta₁ s ≠ 0) :
    logDeriv riemannZeta s + (s - 1)⁻¹ = logDeriv riemannZeta₁ s := by
  rw [logDeriv_apply, logDeriv_apply,
    riemannZeta_eq_inv_sub_mul hs,
    deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs]
  field_simp [sub_ne_zero.mpr hs, hfactor]
  ring

/-- The simple-pole correction has an actual conductor-independent bound
on a punctured complex neighbourhood of `1`. The constants are constructed
from compact bounds of the entire regular part, not assumed. -/
theorem exists_riemannZeta_logDeriv_pole_correction_bound :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ s : ℂ,
      s ≠ 1 → ‖s - 1‖ ≤ δ →
        ‖logDeriv riemannZeta s + (s - 1)⁻¹‖ ≤ C := by
  obtain ⟨M, hM, hbound⟩ := exists_zeta_regularPart_and_deriv_bound
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let δ : ℝ := 1 / (2 * M)
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδhalf : δ ≤ 1 / 2 := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity : 0 < 2 * M)).mpr
    linarith
  have hδM : δ * M = 1 / 2 := by
    dsimp [δ]
    field_simp
  refine ⟨δ, 4 * M, hδpos, by positivity, ?_⟩
  intro s hs hnear
  have hdisc : s ∈ closedBall (2 : ℂ) (3 / 2) := by
    rw [mem_closedBall, dist_eq_norm]
    have htriangle := norm_add_le (s - 1) (1 - (2 : ℂ))
    rw [sub_add_sub_cancel] at htriangle
    norm_num at htriangle
    linarith
  obtain ⟨hzero, hderiv⟩ := hbound s hdisc
  have hperturb : ‖(s - 1) * riemannZeta₀ s‖ ≤ 1 / 2 := by
    rw [norm_mul]
    calc
      ‖s - 1‖ * ‖riemannZeta₀ s‖ ≤ δ * M :=
        mul_le_mul hnear hzero (norm_nonneg _) hδpos.le
      _ = 1 / 2 := hδM
  have hdenom : (1 / 2 : ℝ) ≤ ‖riemannZeta₁ s‖ := by
    have hreverse := norm_sub_norm_le (1 : ℂ) (-((s - 1) * riemannZeta₀ s))
    simp only [norm_one, norm_neg, sub_neg_eq_add] at hreverse
    change 1 - ‖(s - 1) * riemannZeta₀ s‖ ≤ ‖riemannZeta₁ s‖ at hreverse
    linarith
  have hfactor : riemannZeta₁ s ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdenom
    norm_num at hdenom
  rw [logDeriv_riemannZeta_pole_correction hs hfactor, logDeriv_apply, norm_div]
  have hnumerator : ‖deriv riemannZeta₁ s‖ ≤ 2 * M := by
    rw [deriv_riemannZeta_regularFactor]
    calc
      ‖riemannZeta₀ s + (s - 1) * deriv riemannZeta₀ s‖ ≤
          ‖riemannZeta₀ s‖ + ‖(s - 1) * deriv riemannZeta₀ s‖ := norm_add_le _ _
      _ ≤ M + δ * M := by
        rw [norm_mul]
        exact add_le_add hzero (mul_le_mul hnear hderiv (norm_nonneg _) hδpos.le)
      _ ≤ 2 * M := by rw [hδM]; linarith
  apply (div_le_iff₀ (by linarith : 0 < ‖riemannZeta₁ s‖)).mpr
  calc
    ‖deriv riemannZeta₁ s‖ ≤ 2 * M := hnumerator
    _ ≤ (4 * M) * ‖riemannZeta₁ s‖ := by nlinarith

/-- On the real interval immediately to the right of `1`, the negative
logarithmic derivative of actual zeta is at most its simple pole plus one
fixed positive constant. -/
theorem exists_neg_logDeriv_riemannZeta_real_upper_bound :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ σ : ℝ,
      1 < σ → σ ≤ 1 + δ →
        -(logDeriv riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + C := by
  obtain ⟨δ, C, hδ, hC, hbound⟩ :=
    exists_riemannZeta_logDeriv_pole_correction_bound
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro σ hσ hσδ
  have hs : (σ : ℂ) ≠ 1 := by exact_mod_cast (ne_of_gt hσ)
  have hnear : ‖(σ : ℂ) - 1‖ ≤ δ := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith : 0 < σ - 1)]
    linarith
  have h := (Complex.abs_re_le_norm _).trans (hbound (σ : ℂ) hs hnear)
  have hinv : ((σ : ℂ) - 1)⁻¹ = (((σ - 1)⁻¹ : ℝ) : ℂ) := by norm_cast
  rw [Complex.add_re, hinv, Complex.ofReal_re] at h
  have hlower := (neg_le_abs ((logDeriv riemannZeta (σ : ℂ)).re + (σ - 1)⁻¹)).trans h
  simpa only [one_div] using (show -(logDeriv riemannZeta (σ : ℂ)).re ≤
    (σ - 1)⁻¹ + C by linarith)

open Set in
/-- On bounded heights, compactness of the actual nonvanishing regularized
zeta factor uniformly bounds its logarithmic derivative. The simple pole is
retained explicitly; neither nonvanishing nor a bound is assumed. -/
theorem exists_zeta_pole_corrected_logDeriv_bounded_height_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ σ τ : ℝ, 1 < σ → σ ≤ 11 / 10 → |τ| ≤ 4 →
      -(logDeriv riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤
        (((σ : ℂ) + (τ : ℂ) * Complex.I - 1)⁻¹).re + C := by
  let K : Set ℂ := Complex.re ⁻¹' Icc (1 : ℝ) (11 / 10) ∩
    Complex.im ⁻¹' Icc (-4 : ℝ) 4
  have hKclosed : IsClosed K := by
    exact (isClosed_Icc.preimage Complex.continuous_re).inter
      (isClosed_Icc.preimage Complex.continuous_im)
  have hKbounded : Bornology.IsBounded K := by
    rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ)]
    refine ⟨6, ?_⟩
    intro s hs
    rw [mem_closedBall, dist_zero_right]
    have hre := (show s.re ∈ Icc (1 : ℝ) (11 / 10) from hs.1)
    have him := (show s.im ∈ Icc (-4 : ℝ) 4 from hs.2)
    have hre' : |s.re| ≤ 11 / 10 := by
      rw [abs_of_nonneg (by linarith [hre.1])]
      exact hre.2
    have him' : |s.im| ≤ 4 := by
      exact abs_le.mpr ⟨by linarith [him.1], by linarith [him.2]⟩
    calc
      ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 11 / 10 + 4 := add_le_add hre' him'
      _ ≤ 6 := by norm_num
  have hK : IsCompact K := Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨hKclosed, hKbounded⟩
  have hfactor : ∀ s ∈ K, riemannZeta₁ s ≠ 0 := by
    intro s hs
    have hre : 1 ≤ s.re := hs.1.1
    by_cases hs1 : s = 1
    · simp [hs1]
    · have hzeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hre
      have hrep := riemannZeta_eq_inv_sub_mul hs1
      rw [hrep] at hzeta
      intro hζ1
      simp [hζ1] at hzeta
  have hcont : ContinuousOn (fun s : ℂ => logDeriv riemannZeta₁ s) K := by
    have hderiv : Continuous (deriv riemannZeta₁) :=
      differentiable_riemannZeta₁.deriv.continuous
    have hdenom : Continuous riemannZeta₁ := differentiable_riemannZeta₁.continuous
    have hquot : ContinuousOn (fun s : ℂ => deriv riemannZeta₁ s / riemannZeta₁ s) K :=
      hderiv.continuousOn.div hdenom.continuousOn (fun s hs => hfactor s hs)
    simpa only [logDeriv_apply] using hquot
  have himage : IsCompact ((fun s : ℂ => logDeriv riemannZeta₁ s) '' K) :=
    hK.image_of_continuousOn hcont
  obtain ⟨B, hB⟩ := himage.isBounded.exists_norm_le
  let C : ℝ := max 1 B
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro σ τ hσ hσupper hτ
  let s : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I
  have hτbounds := abs_le.mp hτ
  have hsK : s ∈ K := by
    constructor
    · change s.re ∈ Icc (1 : ℝ) (11 / 10)
      simp [s]
      exact ⟨le_of_lt hσ, hσupper⟩
    · change s.im ∈ Icc (-4 : ℝ) 4
      simp [s]
      exact hτbounds
  have hs1 : s ≠ 1 := by
    intro hs
    have : s.re = 1 := congrArg Complex.re hs
    simp [s] at this
    linarith
  have hz1 : riemannZeta₁ s ≠ 0 := hfactor s hsK
  have hid := logDeriv_riemannZeta_pole_correction hs1 hz1
  have hnorm : ‖logDeriv riemannZeta₁ s‖ ≤ C := by
    have hB' := hB (logDeriv riemannZeta₁ s) ⟨s, hsK, rfl⟩
    exact hB'.trans (le_max_right 1 B)
  have hreal := congrArg Complex.re hid
  rw [Complex.add_re] at hreal
  have habs := (Complex.abs_re_le_norm (logDeriv riemannZeta₁ s)).trans hnorm
  change -(logDeriv riemannZeta s).re ≤ ((s - 1)⁻¹).re + C
  have hlow : -C ≤ (logDeriv riemannZeta₁ s).re := by
    calc
      -C ≤ -|(logDeriv riemannZeta₁ s).re| := by linarith [habs]
      _ ≤ (logDeriv riemannZeta₁ s).re := neg_abs_le _
  linarith

#print axioms exists_zeta_pole_corrected_logDeriv_bounded_height_bound

#print axioms exists_riemannZeta_logDeriv_pole_correction_bound
#print axioms exists_neg_logDeriv_riemannZeta_real_upper_bound

end SystolicGrowth.CookMagyarMajorArc
