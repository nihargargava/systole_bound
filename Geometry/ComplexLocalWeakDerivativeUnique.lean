module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ComplexLocalWeakSobolev
public import Geometry.GluingConformalWeakToClassical

@[expose] public section

/-!
# Local weak derivatives agree with a classical representative

Actual compact-test first derivative identities determine the derivative
almost everywhere. Once local elliptic regularity gives a real `C¹`
representative, its classical first derivatives therefore are the original
local `L²` weak derivative witnesses.
-/

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal LineDeriv SchwartzMap

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- **Math.** Compact-local Euclidean `L²` functions are locally
integrable on an open coordinate domain. -/
theorem complexLocalL2_locallyIntegrableOn
    {V : Set ℂ} (hV : IsOpen V) {F : ℂ → ℝ}
    (hF : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp F 2 (volume.restrict K)) :
    LocallyIntegrableOn F V volume := by
  apply (locallyIntegrableOn_iff hV.isLocallyClosed).mpr
  intro K hKV hK
  letI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by simpa using hK.measure_lt_top (μ := (volume : Measure ℂ))⟩
  exact (hF K hK hKV).integrable (by norm_num)

/-- **Math.** An actual local `L²` weak directional derivative agrees
almost everywhere with the classical derivative of any local `C¹`
representative of the same function. -/
theorem complexLocalWeakDerivative_eq_fderiv_ae
    {V : Set ℂ} (hV : IsOpen V) (u G c : ℂ → ℝ) (v : ℂ)
    (hG : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp G 2 (volume.restrict K))
    (hweak : ∀ η : ℂ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ V → (∫ z : ℂ, G z * η z) =
        -(∫ z : ℂ, u z * fderiv ℝ η z v))
    (hc : ContDiffOn ℝ 1 c V) (hu : u =ᵐ[volume.restrict V] c) :
    G =ᵐ[volume.restrict V] (fun z => fderiv ℝ c z v) := by
  have hD : ContinuousOn (fun z => fderiv ℝ c z v) V :=
    ((hc.fderiv_of_isOpen hV (show (0 : ℕ∞ω) + 1 ≤ 1 by norm_num)).clm_apply
      contDiffOn_const).continuousOn
  have hGloc := complexLocalL2_locallyIntegrableOn hV hG
  have hDloc : LocallyIntegrableOn (fun z => fderiv ℝ c z v) V volume :=
    hD.locallyIntegrableOn hV.measurableSet
  have hu' : ∀ᵐ z ∂volume, z ∈ V → u z = c z :=
    (ae_restrict_iff' hV.measurableSet).mp hu
  have hzero : ∀ᵐ z ∂volume, z ∈ V → G z - fderiv ℝ c z v = 0 := by
    apply hV.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hGloc.sub hDloc)
    intro η hη hηc hηV
    have hGη : Integrable (fun z => G z * η z) := by
      simpa only [mul_comm] using
        localL2_compact_mul_integrable hG η hη.continuous hηc hηV
    have hDη : Integrable (fun z => fderiv ℝ c z v * η z) := by
      have hcont : Continuous (fun z => fderiv ℝ c z v * η z) := by
        apply continuous_of_tsupport
        intro z hz
        exact (hD.continuousAt (hV.mem_nhds (hηV (tsupport_mul_subset_right hz)))).mul
          hη.continuous.continuousAt
      exact hcont.integrable_of_hasCompactSupport hηc.mul_left
    have hrep : (∫ z : ℂ, u z * fderiv ℝ η z v) =
        ∫ z : ℂ, c z * fderiv ℝ η z v := by
      apply integral_congr_ae
      filter_upwards [hu'] with z hz
      by_cases hzV : z ∈ V
      · rw [hz hzV]
      · have hnot : z ∉ tsupport (fun w => fderiv ℝ η w v) :=
          fun h => hzV (hηV (tsupport_fderiv_apply_subset ℝ v h))
        have hd : fderiv ℝ η z v = 0 :=
          image_eq_zero_of_notMem_tsupport (f := fun w => fderiv ℝ η w v) hnot
        simp only [hd, mul_zero]
    calc
      (∫ z : ℂ, η z • (G z - fderiv ℝ c z v)) =
          (∫ z : ℂ, G z * η z) - ∫ z : ℂ, fderiv ℝ c z v * η z := by
        rw [← integral_sub hGη hDη]
        apply integral_congr_ae
        filter_upwards with z
        simp only [smul_eq_mul]
        ring
      _ = 0 := by
        rw [hweak η hη hηc hηV, hrep,
          coordinate_integral_fderiv_mul_test_C1 hV hc hη hηc hηV v]
        exact sub_self _
  apply (ae_restrict_iff' hV.measurableSet).mpr
  filter_upwards [hzero] with z hz hzV
  exact sub_eq_zero.mp (hz hzV)

/-- **Math.** Both coordinate witnesses of a real weak `H¹` function
are the corresponding classical derivatives of its local `C¹`
representative. -/
theorem complexLocalWeakDerivatives_eq_fderiv_ae
    {V : Set ℂ} (hV : IsOpen V) (u : ℂ → ℝ) (G : Fin 2 → ℂ → ℝ)
    (c : ℂ → ℝ)
    (hG : ∀ (j : Fin 2) (K : Set ℂ), IsCompact K → K ⊆ V →
      MemLp (G j) 2 (volume.restrict K))
    (hweak : ∀ (j : Fin 2) (η : ℂ → ℝ), ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ V → (∫ z : ℂ, G j z * η z) =
        -(∫ z : ℂ, u z * fderiv ℝ η z (if j = 0 then 1 else Complex.I)))
    (hc : ContDiffOn ℝ 1 c V) (hu : u =ᵐ[volume.restrict V] c) :
    ∀ j : Fin 2, G j =ᵐ[volume.restrict V]
      (fun z => fderiv ℝ c z (if j = 0 then 1 else Complex.I)) := by
  intro j
  exact complexLocalWeakDerivative_eq_fderiv_ae hV u (G j) c _ (hG j) (hweak j) hc hu

/-- **Math.** A genuine `L²` distributional derivative of a complex
`C¹` representative is its classical derivative almost everywhere.
This applies directly to the global representatives of `H³` cutoffs. -/
theorem complexL2_weakDerivative_eq_fderiv_ae
    (f g : Lp ℂ 2 (volume : Measure ℂ)) (c : ℂ → ℂ) (v : ℂ)
    (hc : ContDiff ℝ 1 c) (hfc : (f : ℂ → ℂ) =ᵐ[volume] c)
    (hd : ∂_{v} (f : 𝓢'(ℂ, ℂ)) = (g : 𝓢'(ℂ, ℂ))) :
    (g : ℂ → ℂ) =ᵐ[volume] (fun z => fderiv ℝ c z v) := by
  have hDc : Continuous (fun z => fderiv ℝ c z v) :=
    (hc.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hweak (φ : 𝓢(ℂ, ℂ)) :
      (∫ z : ℂ, φ z * g z) = -(∫ z : ℂ, (∂_{v} φ) z * f z) := by
    have hp := congrArg (fun w : 𝓢'(ℂ, ℂ) => w φ) hd.symm
    rw [TemperedDistribution.lineDerivOp_apply_apply, map_neg,
      Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply] at hp
    simpa only [smul_eq_mul] using hp
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp g).locallyIntegrable (by norm_num)) hDc.locallyIntegrable
  intro η hη hηc
  have hDη : Continuous (fun z => fderiv ℝ η z v) :=
    (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDηc : HasCompactSupport (fun z => fderiv ℝ η z v) := hηc.fderiv_apply ℝ v
  have hi₁ : Integrable (fun z => fderiv ℝ η z v • c z) :=
    (hDη.smul hc.continuous).integrable_of_hasCompactSupport hDηc.smul_right
  have hi₂ : Integrable (fun z => η z • fderiv ℝ c z v) :=
    (hη.continuous.smul hDc).integrable_of_hasCompactSupport hηc.smul_right
  have hi₃ : Integrable (fun z => η z • c z) :=
    (hη.continuous.smul hc.continuous).integrable_of_hasCompactSupport hηc.smul_right
  have hibp := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable hi₁ hi₂ hi₃
    (fun z _ => hη.differentiable (by simp) z)
    (fun z _ => hc.differentiable one_ne_zero z)
  have hηC : ContDiff ℝ ∞ (fun z => (η z : ℂ)) := Complex.ofRealCLM.contDiff.comp hη
  have hηCc : HasCompactSupport (fun z => (η z : ℂ)) :=
    hηc.comp_left Complex.ofReal_zero
  let φ : 𝓢(ℂ, ℂ) := hηCc.toSchwartzMap hηC
  have hφ (z : ℂ) : φ z = (η z : ℂ) := rfl
  have hDφ (z : ℂ) : (∂_{v} φ) z = (fderiv ℝ η z v : ℂ) := by
    change fderiv ℝ (fun z => (η z : ℂ)) z v = _
    exact congrArg (fun T : ℂ →L[ℝ] ℂ => T v)
      (Complex.ofRealCLM.hasFDerivAt.comp z
        (hη.differentiable (by simp) z).hasFDerivAt).fderiv
  calc
    (∫ z : ℂ, η z • g z) = ∫ z : ℂ, φ z * g z := by
      apply integral_congr_ae
      filter_upwards with z
      simp only [hφ, Complex.real_smul]
    _ = -(∫ z : ℂ, (∂_{v} φ) z * f z) := hweak φ
    _ = -(∫ z : ℂ, fderiv ℝ η z v • c z) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hfc] with z hz
      simp only [hDφ, hz, Complex.real_smul]
    _ = ∫ z : ℂ, η z • fderiv ℝ c z v := hibp.symm

#print axioms complexLocalWeakDerivative_eq_fderiv_ae
#print axioms complexLocalWeakDerivatives_eq_fderiv_ae
#print axioms complexL2_weakDerivative_eq_fderiv_ae

end

end SystolicGrowth
