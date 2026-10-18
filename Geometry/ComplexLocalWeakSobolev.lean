module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ComplexSobolevHigherCutoff
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

@[expose] public section

/-!
# Local weak `H¹` data give genuine cutoff Fourier--Sobolev distributions

The input consists of real local `L²` functions and their two actual
compact-test weak derivative identities. Compact cutoffs are first realized
as global `L²` functions, then their genuine distributional derivatives are
computed. Sobolev membership is deduced from these constructed witnesses.
-/

open Set Filter MeasureTheory TemperedDistribution
open scoped ContDiff Topology ENNReal LineDeriv SchwartzMap

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- **Math.** A continuous compact multiplier turns local `L²` into
global `L²`, with the literal product as representative. -/
theorem localL2_compact_mul_memLp {𝕜 : Type*} [RCLike 𝕜]
    {V : Set ℂ} {F : ℂ → 𝕜}
    (hF : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp F 2 (volume.restrict K))
    (η : ℂ → 𝕜) (hη : Continuous η) (hηc : HasCompactSupport η)
    (hηV : tsupport η ⊆ V) : MemLp (fun z => η z * F z) 2 volume := by
  have hηtop := hη.memLp_top_of_hasCompactSupport hηc volume
  have hloc : MemLp (fun z => η z * F z) 2 (volume.restrict (tsupport η)) :=
    (hηtop.restrict _).fun_mul (hF (tsupport η) hηc hηV)
  have hind : MemLp ((tsupport η).indicator (fun z => η z * F z)) 2 volume :=
    (memLp_indicator_iff_restrict hηc.measurableSet).mpr hloc
  apply (memLp_congr_ae ?_).mp hind
  filter_upwards with z
  by_cases hz : z ∈ tsupport η
  · simp [hz]
  · simp [hz, image_eq_zero_of_notMem_tsupport hz]

/-- **Math.** The same compact product is integrable, since compact
Euclidean sets have finite measure and `L²` embeds into `L¹` there. -/
theorem localL2_compact_mul_integrable {𝕜 : Type*} [RCLike 𝕜]
    {V : Set ℂ} {F : ℂ → 𝕜}
    (hF : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp F 2 (volume.restrict K))
    (η : ℂ → 𝕜) (hη : Continuous η) (hηc : HasCompactSupport η)
    (hηV : tsupport η ⊆ V) : Integrable (fun z => η z * F z) volume := by
  have hf := localL2_compact_mul_memLp hF η hη hηc hηV
  letI : IsFiniteMeasure (volume.restrict (tsupport η)) :=
    ⟨by simpa using hηc.measure_lt_top (μ := (volume : Measure ℂ))⟩
  have hloc : Integrable (fun z => η z * F z) (volume.restrict (tsupport η)) :=
    (hf.restrict _).integrable (by norm_num)
  have hind : Integrable ((tsupport η).indicator (fun z => η z * F z)) volume :=
    (integrable_indicator_iff hηc.measurableSet).mpr hloc
  apply hind.congr
  filter_upwards with z
  by_cases hz : z ∈ tsupport η
  · simp [hz]
  · simp [hz, image_eq_zero_of_notMem_tsupport hz]

/-- **Math.** Reconstruct an arbitrary real direction from the two
coordinate weak derivatives on the complex plane. -/
def complexRealCoordinateDerivative (G : Fin 2 → ℂ → ℝ) (v z : ℂ) : ℝ :=
  v.re * G 0 z + v.im * G 1 z

theorem complexRealCoordinateDerivative_memLp
    {V : Set ℂ} (G : Fin 2 → ℂ → ℝ)
    (hG : ∀ (j : Fin 2) (K : Set ℂ), IsCompact K → K ⊆ V →
      MemLp (G j) 2 (volume.restrict K))
    (v : ℂ) (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V) :
    MemLp (complexRealCoordinateDerivative G v) 2 (volume.restrict K) :=
  ((hG 0 K hK hKV).const_mul v.re).add ((hG 1 K hK hKV).const_mul v.im)

/-- **Math.** The exact two coordinate test identities imply the
corresponding identity in every real direction. -/
theorem realLocalWeakDerivative_all_directions
    {V : Set ℂ} (F : ℂ → ℝ) (G : Fin 2 → ℂ → ℝ)
    (hF : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp F 2 (volume.restrict K))
    (hG : ∀ (j : Fin 2) (K : Set ℂ), IsCompact K → K ⊆ V →
      MemLp (G j) 2 (volume.restrict K))
    (hweak : ∀ (j : Fin 2) (η : ℂ → ℝ), ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ V → (∫ z : ℂ, G j z * η z) =
        -(∫ z : ℂ, F z * fderiv ℝ η z (if j = 0 then 1 else Complex.I)))
    (v : ℂ) (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηV : tsupport η ⊆ V) :
    (∫ z : ℂ, complexRealCoordinateDerivative G v z * η z) =
      -(∫ z : ℂ, F z * fderiv ℝ η z v) := by
  have hD (w : ℂ) : ContDiff ℝ ∞ (fun z => fderiv ℝ η z w) :=
    (hη.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) by simp)).clm_apply contDiff_const
  have hGi (j : Fin 2) : Integrable (fun z => G j z * η z) := by
    simpa only [mul_comm] using
      localL2_compact_mul_integrable (hG j) η hη.continuous hηc hηV
  have hFi (w : ℂ) : Integrable (fun z => F z * fderiv ℝ η z w) := by
    simpa only [mul_comm] using localL2_compact_mul_integrable hF
      (fun z => fderiv ℝ η z w) (hD w).continuous (hηc.fderiv_apply ℝ w)
      ((tsupport_fderiv_apply_subset ℝ w).trans hηV)
  have h₀ := hweak 0 η hη hηc hηV
  have h₁ := hweak 1 η hη hηc hηV
  simp only [↓reduceIte, Fin.isValue, one_ne_zero] at h₀ h₁
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp
  have hdir (z : ℂ) : fderiv ℝ η z v =
      v.re * fderiv ℝ η z 1 + v.im * fderiv ℝ η z Complex.I := by
    calc
      fderiv ℝ η z v = fderiv ℝ η z (v.re • (1 : ℂ) + v.im • Complex.I) :=
        congrArg (fderiv ℝ η z) hv
      _ = _ := by simp only [map_add, map_smul, smul_eq_mul]
  calc
    (∫ z : ℂ, complexRealCoordinateDerivative G v z * η z) =
        v.re * (∫ z : ℂ, G 0 z * η z) + v.im * (∫ z : ℂ, G 1 z * η z) := by
      simp only [complexRealCoordinateDerivative, add_mul, mul_assoc]
      rw [integral_add ((hGi 0).const_mul _) ((hGi 1).const_mul _),
        integral_const_mul, integral_const_mul]
    _ = -(v.re * (∫ z : ℂ, F z * fderiv ℝ η z 1) +
        v.im * (∫ z : ℂ, F z * fderiv ℝ η z Complex.I)) := by
      rw [h₀, h₁]
      ring
    _ = -(∫ z : ℂ, F z * fderiv ℝ η z v) := by
      congr 1
      simp_rw [hdir, mul_add, mul_left_comm (F _)]
      rw [integral_add ((hFi 1).const_mul _) ((hFi Complex.I).const_mul _),
        integral_const_mul, integral_const_mul]

/-- **Math.** Real weak derivative identities extend to complex-valued
compact tests, by applying every real linear functional to the integrals. -/
theorem complexLocalWeakDerivative_test
    {V : Set ℂ} (F : ℂ → ℝ) (G : Fin 2 → ℂ → ℝ)
    (hF : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp F 2 (volume.restrict K))
    (hG : ∀ (j : Fin 2) (K : Set ℂ), IsCompact K → K ⊆ V →
      MemLp (G j) 2 (volume.restrict K))
    (hweak : ∀ (j : Fin 2) (η : ℂ → ℝ), ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ V → (∫ z : ℂ, G j z * η z) =
        -(∫ z : ℂ, F z * fderiv ℝ η z (if j = 0 then 1 else Complex.I)))
    (v : ℂ) (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψV : tsupport ψ ⊆ V) :
    (∫ z : ℂ, ψ z * (complexRealCoordinateDerivative G v z : ℂ)) =
      -(∫ z : ℂ, fderiv ℝ ψ z v * (F z : ℂ)) := by
  have hFc (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V) :
      MemLp (fun z => (F z : ℂ)) 2 (volume.restrict K) := (hF K hK hKV).ofReal
  have hGc (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V) :
      MemLp (fun z => (complexRealCoordinateDerivative G v z : ℂ)) 2
        (volume.restrict K) := (complexRealCoordinateDerivative_memLp G hG v K hK hKV).ofReal
  have hDψ : ContDiff ℝ ∞ (fun z => fderiv ℝ ψ z v) :=
    (hψ.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) by simp)).clm_apply contDiff_const
  have hleft := localL2_compact_mul_integrable hGc ψ hψ.continuous hψc hψV
  have hright := localL2_compact_mul_integrable hFc (fun z => fderiv ℝ ψ z v)
    hDψ.continuous (hψc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hψV)
  have hL (L : ℂ →L[ℝ] ℝ) :
      L (∫ z : ℂ, ψ z * (complexRealCoordinateDerivative G v z : ℂ)) =
        -L (∫ z : ℂ, fderiv ℝ ψ z v * (F z : ℂ)) := by
    have hη : ContDiff ℝ ∞ (fun z => L (ψ z)) := L.contDiff.comp hψ
    have hηc : HasCompactSupport (fun z => L (ψ z)) := hψc.comp_left (map_zero L)
    have hηV : tsupport (fun z => L (ψ z)) ⊆ V :=
      (tsupport_comp_subset (map_zero L) ψ).trans hψV
    have hηD (z : ℂ) : fderiv ℝ (fun z => L (ψ z)) z v = L (fderiv ℝ ψ z v) :=
      congrArg (fun T : ℂ →L[ℝ] ℝ => T v)
        (L.hasFDerivAt.comp z ((hψ.differentiable (by simp)) z).hasFDerivAt).fderiv
    calc
      L (∫ z : ℂ, ψ z * (complexRealCoordinateDerivative G v z : ℂ)) =
          ∫ z : ℂ, complexRealCoordinateDerivative G v z * L (ψ z) := by
        rw [← L.integral_comp_comm hleft]
        apply integral_congr_ae
        filter_upwards with z
        simpa only [Complex.real_smul, smul_eq_mul, mul_comm] using
          L.map_smul (complexRealCoordinateDerivative G v z) (ψ z)
      _ = -(∫ z : ℂ, F z * fderiv ℝ (fun z => L (ψ z)) z v) :=
        realLocalWeakDerivative_all_directions F G hF hG hweak v _ hη hηc hηV
      _ = -(∫ z : ℂ, L (fderiv ℝ ψ z v * (F z : ℂ))) := by
        congr 1
        apply integral_congr_ae
        filter_upwards with z
        rw [hηD]
        simpa only [Complex.real_smul, smul_eq_mul, mul_comm] using
          (L.map_smul (F z) (fderiv ℝ ψ z v)).symm
      _ = -L (∫ z : ℂ, fderiv ℝ ψ z v * (F z : ℂ)) := by
        rw [L.integral_comp_comm hright]
  apply Complex.ext
  · exact hL Complex.reCLM
  · exact hL Complex.imCLM

/-- **Math.** The literal complex cutoff of the local real function. -/
def complexLocalCutoffValue (F : ℂ → ℝ) (ζ : ℂ → ℂ) (z : ℂ) : ℂ :=
  ζ z * (F z : ℂ)

/-- **Math.** The genuine derivative representative required by the
cutoff product rule, in an arbitrary real direction. -/
def complexLocalCutoffDerivative (F : ℂ → ℝ) (G : Fin 2 → ℂ → ℝ)
    (ζ : ℂ → ℂ) (v z : ℂ) : ℂ :=
  ζ z * (complexRealCoordinateDerivative G v z : ℂ) +
    fderiv ℝ ζ z v * (F z : ℂ)

theorem complexLocalCutoffValue_memLp
    {V : Set ℂ} (F : ℂ → ℝ)
    (hF : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp F 2 (volume.restrict K))
    (ζ : ℂ → ℂ) (hζ : Continuous ζ) (hζc : HasCompactSupport ζ)
    (hζV : tsupport ζ ⊆ V) : MemLp (complexLocalCutoffValue F ζ) 2 volume :=
  localL2_compact_mul_memLp (fun K hK hKV => (hF K hK hKV).ofReal) ζ hζ hζc hζV

theorem complexLocalCutoffDerivative_memLp
    {V : Set ℂ} (F : ℂ → ℝ) (G : Fin 2 → ℂ → ℝ)
    (hF : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp F 2 (volume.restrict K))
    (hG : ∀ (j : Fin 2) (K : Set ℂ), IsCompact K → K ⊆ V →
      MemLp (G j) 2 (volume.restrict K))
    (ζ : ℂ → ℂ) (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ)
    (hζV : tsupport ζ ⊆ V) (v : ℂ) :
    MemLp (complexLocalCutoffDerivative F G ζ v) 2 volume := by
  have hfirst := localL2_compact_mul_memLp
    (fun K hK hKV => (complexRealCoordinateDerivative_memLp G hG v K hK hKV).ofReal)
    ζ hζ.continuous hζc hζV
  have hDζ : ContDiff ℝ ∞ (fun z => fderiv ℝ ζ z v) :=
    (hζ.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) by simp)).clm_apply contDiff_const
  have hsecond := localL2_compact_mul_memLp
    (fun K hK hKV => (hF K hK hKV).ofReal) (fun z => fderiv ℝ ζ z v)
    hDζ.continuous (hζc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hζV)
  exact hfirst.add hsecond

/-- **Math.** The cutoff derivative satisfies the exact weak product
rule against every smooth complex test, without a support condition on
the test itself. The compact cutoff supplies all needed integrability. -/
theorem complexLocalWeakDerivative_cutoff_test
    {V : Set ℂ} (F : ℂ → ℝ) (G : Fin 2 → ℂ → ℝ)
    (hF : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp F 2 (volume.restrict K))
    (hG : ∀ (j : Fin 2) (K : Set ℂ), IsCompact K → K ⊆ V →
      MemLp (G j) 2 (volume.restrict K))
    (hweak : ∀ (j : Fin 2) (η : ℂ → ℝ), ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ V → (∫ z : ℂ, G j z * η z) =
        -(∫ z : ℂ, F z * fderiv ℝ η z (if j = 0 then 1 else Complex.I)))
    (ζ : ℂ → ℂ) (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ)
    (hζV : tsupport ζ ⊆ V) (v : ℂ) (φ : ℂ → ℂ) (hφ : ContDiff ℝ ∞ φ) :
    (∫ z : ℂ, φ z * complexLocalCutoffDerivative F G ζ v z) =
      -(∫ z : ℂ, fderiv ℝ φ z v * complexLocalCutoffValue F ζ z) := by
  have hFc (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V) :
      MemLp (fun z => (F z : ℂ)) 2 (volume.restrict K) := (hF K hK hKV).ofReal
  have hGc (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V) :
      MemLp (fun z => (complexRealCoordinateDerivative G v z : ℂ)) 2
        (volume.restrict K) := (complexRealCoordinateDerivative_memLp G hG v K hK hKV).ofReal
  have hDζ : ContDiff ℝ ∞ (fun z => fderiv ℝ ζ z v) :=
    (hζ.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) by simp)).clm_apply contDiff_const
  have hDφ : ContDiff ℝ ∞ (fun z => fderiv ℝ φ z v) :=
    (hφ.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) by simp)).clm_apply contDiff_const
  have hA := localL2_compact_mul_integrable hGc (fun z => ζ z * φ z)
    (hζ.continuous.mul hφ.continuous) hζc.mul_right (tsupport_mul_subset_left.trans hζV)
  have hB := localL2_compact_mul_integrable hFc (fun z => φ z * fderiv ℝ ζ z v)
    (hφ.continuous.mul hDζ.continuous) (hζc.fderiv_apply ℝ v).mul_left
    (tsupport_mul_subset_right.trans ((tsupport_fderiv_apply_subset ℝ v).trans hζV))
  have hC := localL2_compact_mul_integrable hFc (fun z => ζ z * fderiv ℝ φ z v)
    (hζ.continuous.mul hDφ.continuous) hζc.mul_right (tsupport_mul_subset_left.trans hζV)
  have htest := complexLocalWeakDerivative_test F G hF hG hweak v
    (fun z => ζ z * φ z) (hζ.mul hφ) hζc.mul_right (tsupport_mul_subset_left.trans hζV)
  have hprod (z : ℂ) : fderiv ℝ (fun z => ζ z * φ z) z v =
      φ z * fderiv ℝ ζ z v + ζ z * fderiv ℝ φ z v := by
    rw [fderiv_fun_mul ((hζ.differentiable (by simp)) z)
      ((hφ.differentiable (by simp)) z)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    exact add_comm _ _
  have hexpand : (fun z => fderiv ℝ (fun z => ζ z * φ z) z v * (F z : ℂ)) =
      (fun z => φ z * fderiv ℝ ζ z v * (F z : ℂ) +
        ζ z * fderiv ℝ φ z v * (F z : ℂ)) := by
    funext z
    rw [hprod]
    exact add_mul _ _ _
  rw [hexpand, integral_add hB hC] at htest
  calc
    (∫ z : ℂ, φ z * complexLocalCutoffDerivative F G ζ v z) =
        (∫ z : ℂ, (ζ z * φ z) * (complexRealCoordinateDerivative G v z : ℂ)) +
          (∫ z : ℂ, φ z * fderiv ℝ ζ z v * (F z : ℂ)) := by
      rw [← integral_add hA hB]
      apply integral_congr_ae
      filter_upwards with z
      dsimp only [complexLocalCutoffDerivative, Pi.add_apply]
      ring
    _ = -(∫ z : ℂ, ζ z * fderiv ℝ φ z v * (F z : ℂ)) := by
      rw [htest]
      ring
    _ = -(∫ z : ℂ, fderiv ℝ φ z v * complexLocalCutoffValue F ζ z) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with z
      dsimp only [complexLocalCutoffValue]
      ring

/-- **Math.** An a.e.-specified `L²` representative has its literal
integral action on every Schwartz test. -/
theorem complexL2_toTemperedDistribution_apply_of_ae
    (w : Lp ℂ 2 (volume : Measure ℂ)) (H : ℂ → ℂ)
    (hw : w =ᵐ[volume] H) (φ : 𝓢(ℂ, ℂ)) :
    (w : 𝓢'(ℂ, ℂ)) φ = ∫ z : ℂ, φ z * H z := by
  rw [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [hw] with z hz
  simp only [smul_eq_mul, hz]

/-- **Math.** Genuine local real `L²` data with the two actual weak
coordinate derivatives give a compact-cutoff complex tempered distribution
in `H¹`. Its representative, Schwartz action, and every directional
derivative are constructed explicitly; no Sobolev premise is used. -/
theorem complexLocalWeakSobolev_cutoff
    {V : Set ℂ} (F : ℂ → ℝ) (G : Fin 2 → ℂ → ℝ)
    (hF : ∀ K : Set ℂ, IsCompact K → K ⊆ V → MemLp F 2 (volume.restrict K))
    (hG : ∀ (j : Fin 2) (K : Set ℂ), IsCompact K → K ⊆ V →
      MemLp (G j) 2 (volume.restrict K))
    (hweak : ∀ (j : Fin 2) (η : ℂ → ℝ), ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ V → (∫ z : ℂ, G j z * η z) =
        -(∫ z : ℂ, F z * fderiv ℝ η z (if j = 0 then 1 else Complex.I)))
    (ζ : 𝓢(ℂ, ℂ)) (hζc : HasCompactSupport (ζ : ℂ → ℂ))
    (hζV : tsupport (ζ : ℂ → ℂ) ⊆ V) :
    ∃ w : Lp ℂ 2 (volume : Measure ℂ),
      w =ᵐ[volume] (fun z => ζ z * (F z : ℂ)) ∧
      MemSobolev 1 2 (w : 𝓢'(ℂ, ℂ)) ∧
      (∀ φ : 𝓢(ℂ, ℂ), (w : 𝓢'(ℂ, ℂ)) φ =
        ∫ z : ℂ, φ z * (ζ z * (F z : ℂ))) ∧
      (∀ v : ℂ, ∃ d : Lp ℂ 2 (volume : Measure ℂ),
        d =ᵐ[volume] (fun z => ζ z * ((v.re * G 0 z + v.im * G 1 z : ℝ) : ℂ) +
          fderiv ℝ (ζ : ℂ → ℂ) z v * (F z : ℂ)) ∧
        ∂_{v} (w : 𝓢'(ℂ, ℂ)) = (d : 𝓢'(ℂ, ℂ))) := by
  have hW := complexLocalCutoffValue_memLp F hF ζ ζ.continuous hζc hζV
  let w : Lp ℂ 2 (volume : Measure ℂ) := hW.toLp (complexLocalCutoffValue F ζ)
  have hw : w =ᵐ[volume] complexLocalCutoffValue F ζ := hW.coeFn_toLp
  have hD (v : ℂ) := complexLocalCutoffDerivative_memLp F G hF hG ζ ζ.smooth' hζc hζV v
  let d : ℂ → Lp ℂ 2 (volume : Measure ℂ) :=
    fun v => (hD v).toLp (complexLocalCutoffDerivative F G ζ v)
  have hd (v : ℂ) : d v =ᵐ[volume] complexLocalCutoffDerivative F G ζ v :=
    (hD v).coeFn_toLp
  have hline (v : ℂ) : ∂_{v} (w : 𝓢'(ℂ, ℂ)) = (d v : 𝓢'(ℂ, ℂ)) := by
    ext φ
    rw [TemperedDistribution.lineDerivOp_apply_apply, map_neg,
      complexL2_toTemperedDistribution_apply_of_ae w _ hw (∂_{v} φ),
      complexL2_toTemperedDistribution_apply_of_ae (d v) _ (hd v) φ]
    symm
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using
      complexLocalWeakDerivative_cutoff_test F G hF hG hweak ζ ζ.smooth' hζc hζV
        v φ φ.smooth'
  have hzero : MemSobolev 0 2 (w : 𝓢'(ℂ, ℂ)) :=
    memSobolev_zero_iff.mpr ⟨w, rfl⟩
  have hone : MemSobolev 1 2 (w : 𝓢'(ℂ, ℂ)) :=
    complex_memSobolev_one_of_zero_lineDerivs_zero _ hzero
      (fun i => memSobolev_zero_iff.mpr
        ⟨d ((stdOrthonormalBasis ℝ ℂ) i), hline ((stdOrthonormalBasis ℝ ℂ) i)⟩)
  refine ⟨w, hw, hone, ?_, fun v => ⟨d v, hd v, hline v⟩⟩
  intro φ
  exact complexL2_toTemperedDistribution_apply_of_ae w _ hw φ

#print axioms localL2_compact_mul_memLp
#print axioms realLocalWeakDerivative_all_directions
#print axioms complexLocalWeakDerivative_test
#print axioms complexLocalCutoffDerivative_memLp
#print axioms complexLocalWeakDerivative_cutoff_test
#print axioms complexLocalWeakSobolev_cutoff

end

end SystolicGrowth
