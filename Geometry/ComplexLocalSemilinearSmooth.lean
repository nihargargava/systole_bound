module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ComplexLocalWeakEllipticBootstrap
public import Geometry.ComplexHkNonlinearCutoff
public import Geometry.ComplexLocalSobolevClassical

@[expose] public section

/-!
# Smoothness of the actual local semilinear weak solution

The input is the literal compact-test equation for a real `C¹` function.
Every compact cutoff first has `H³`; the proved nonlinear chain rule and
the actual local elliptic gain then increase this order indefinitely.
The original continuous representative is consequently smooth.
-/

open Set Filter MeasureTheory TemperedDistribution
open scoped ContDiff Topology ENNReal SchwartzMap Laplacian

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem coordinate_contDiffOn_mul_supported
    {r : ℕ∞ω} {V : Set ℂ} (hV : IsOpen V)
    {b ζ : ℂ → ℂ} (hb : ContDiffOn ℝ r b V) (hζ : ContDiff ℝ r ζ)
    (hζV : tsupport ζ ⊆ V) : ContDiff ℝ r (fun z => b z * ζ z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ V
  · exact (hb.contDiffAt (hV.mem_nhds hz)).mul hζ.contDiffAt
  · have hzero : ζ =ᶠ[𝓝 z] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (fun hz' => hz (hζV hz'))
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hzero] with w hw
    simp only [hw, Pi.zero_apply, mul_zero]

/-- **Math.** Continuity on the coordinate domain gives the actual
compact-local `L²` hypotheses needed by the elliptic integral bridge. -/
theorem complexLocalContinuous_memLp_on_compact
    {V : Set ℂ} {u : ℂ → ℝ} (hu : ContinuousOn u V)
    (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V) :
    MemLp u 2 (volume.restrict K) := by
  letI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by simpa using hK.measure_lt_top (μ := (volume : Measure ℂ))⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hu.mono hKV)
  have htop : MemLp u ∞ (volume.restrict K) :=
    memLp_top_of_bound ((hu.mono hKV).aestronglyMeasurable hK.measurableSet) C
      ((ae_restrict_mem hK.measurableSet).mono fun z hz => hC z hz)
  exact htop.mono_exponent le_top

/-- **Math.** Actual local classical regularity gives the same finite
Sobolev order for every compact cutoff, via constructed compact classical
functions and their literal `L²` representatives. -/
theorem complexLocalContDiffOn_all_cutoffs
    {V : Set ℂ} (hV : IsOpen V) (n : ℕ) (u : ℂ → ℝ)
    (hu : ContDiffOn ℝ (n : ℕ) u V)
    (ζ : 𝓢(ℂ, ℂ)) (hζc : HasCompactSupport (ζ : ℂ → ℂ))
    (hζV : tsupport (ζ : ℂ → ℂ) ⊆ V) :
    ∃ w : Lp ℂ 2 (volume : Measure ℂ),
      w =ᵐ[volume] (fun z => ζ z * (u z : ℂ)) ∧
      MemSobolev (n : ℝ) 2 (w : 𝓢'(ℂ, ℂ)) := by
  have hsm : ContDiff ℝ (n : ℕ) (fun z => ζ z * (u z : ℂ)) := by
    have h := coordinate_contDiffOn_mul_supported hV
      (Complex.ofRealCLM.contDiff.comp_contDiffOn hu) (ζ.smooth n) hζV
    convert h using 1
    funext z
    exact mul_comm _ _
  exact exists_complexCompactClassical_sobolev_representation n _ hsm hζc.mul_right

/-- **Math.** Genuine higher Sobolev cutoffs of the solution produce
genuine higher cutoffs of its nonlinear composition. The real outer
localization is constructed around the supplied compact support. -/
theorem complexLocalNonlinear_all_cutoffs_add_one
    {V : Set ℂ} (hV : IsOpen V) (k : ℕ) (hk : 1 ≤ k)
    (u : ℂ → ℝ) (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (k + 1 : ℕ) Ψ)
    (huS : ∀ ζ : 𝓢(ℂ, ℂ), HasCompactSupport (ζ : ℂ → ℂ) →
      tsupport (ζ : ℂ → ℂ) ⊆ V → ∃ w : Lp ℂ 2 (volume : Measure ℂ),
        w =ᵐ[volume] (fun z => ζ z * (u z : ℂ)) ∧
        MemSobolev ((k : ℝ) + 2) 2 (w : 𝓢'(ℂ, ℂ))) :
    ∀ ζ : 𝓢(ℂ, ℂ), HasCompactSupport (ζ : ℂ → ℂ) →
      tsupport (ζ : ℂ → ℂ) ⊆ V → ∃ q : Lp ℂ 2 (volume : Measure ℂ),
        q =ᵐ[volume] (fun z => ζ z * ((Ψ (u z) : ℝ) : ℂ)) ∧
        MemSobolev ((k : ℝ) + 1) 2 (q : 𝓢'(ℂ, ℂ)) := by
  intro ζ hζc hζV
  obtain ⟨η, hη, hηc, hηV, hηone⟩ := exists_real_smooth_compact_cutoff hV hζc hζV
  have hηCc : HasCompactSupport (fun z => (η z : ℂ)) :=
    hηc.comp_left Complex.ofReal_zero
  have hηC : ContDiff ℝ ∞ (fun z => (η z : ℂ)) := Complex.ofRealCLM.contDiff.comp hη
  let χ : 𝓢(ℂ, ℂ) := hηCc.toSchwartzMap hηC
  have hχV : tsupport (χ : ℂ → ℂ) ⊆ V :=
    (tsupport_comp_subset Complex.ofReal_zero η).trans hηV
  obtain ⟨w, hwae, hw⟩ := huS χ hηCc hχV
  have hwreal : w =ᵐ[volume] (fun z => ((η z * u z : ℝ) : ℂ)) := by
    filter_upwards [hwae] with z hz
    change w z = (η z : ℂ) * (u z : ℂ) at hz
    simpa only [Complex.ofReal_mul] using hz
  have hmatch : ∀ᵐ z ∂volume, ζ z ≠ 0 → η z * u z = u z := by
    filter_upwards with z hz
    rw [hηone z (subset_tsupport (ζ : ℂ → ℂ) hz), one_mul]
  exact complexHk_real_nonlinear_cutoff_memSobolev_add_one k hk w hw u
    (fun z => η z * u z) hwreal Ψ hΨ ζ (ζ.smooth (k + 1 : ℕ)) hζc hmatch

/-- **Math.** Every compact cutoff of the actual `C¹` semilinear weak
solution has every higher integer Sobolev order. Nonlinear membership and
all localized Laplacian identities are constructed at each induction step. -/
theorem complexLocalSemilinear_all_cutoffs
    {V : Set ℂ} (hV : IsOpen V) (u K a : ℂ → ℝ) (Ψ : ℝ → ℝ)
    (hu : ContDiffOn ℝ 1 u V) (hK : ContDiffOn ℝ ∞ K V)
    (ha : ContDiffOn ℝ ∞ a V) (hΨ : ContDiff ℝ ∞ Ψ)
    (heq : ∀ η : ℂ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ V → (∫ z : ℂ, u z * Δ η z) =
        ∫ z : ℂ, a z ^ 2 * ((K z + Ψ (u z)) * η z)) :
    ∀ n : ℕ, ∀ ζ : 𝓢(ℂ, ℂ), HasCompactSupport (ζ : ℂ → ℂ) →
      tsupport (ζ : ℂ → ℂ) ⊆ V → ∃ w : Lp ℂ 2 (volume : Measure ℂ),
        w =ᵐ[volume] (fun z => ζ z * (u z : ℂ)) ∧
        MemSobolev ((n : ℝ) + 3) 2 (w : 𝓢'(ℂ, ℂ)) := by
  let F : ℂ → ℝ := fun z => K z + Ψ (u z)
  have hfin (n : ℕ) : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω) :=
    WithTop.coe_le_coe.mpr (show (n : ℕ∞) ≤ ⊤ from le_top)
  have hFone : ContDiffOn ℝ 1 F V :=
    (hK.of_le (hfin 1)).add ((hΨ.of_le (hfin 1)).comp_contDiffOn hu)
  have huL := complexLocalContinuous_memLp_on_compact hu.continuousOn
  have hFL := complexLocalContinuous_memLp_on_compact hFone.continuousOn
  have huOne := complexLocalContDiffOn_all_cutoffs hV 1 u hu
  have hFOne := complexLocalContDiffOn_all_cutoffs hV 1 F hFone
  intro n
  induction n with
  | zero =>
    have hs := complexLocalWeakElliptic_all_cutoffs_from_one hV 1 u F a huL hFL ha heq
      (by simpa only [Nat.cast_one] using huOne) hFOne
    simpa only [Nat.cast_zero, zero_add, Nat.cast_one,
      show (1 : ℝ) + 2 = 3 by norm_num] using hs
  | succ n ih =>
    have huPrev : ∀ ζ : 𝓢(ℂ, ℂ), HasCompactSupport (ζ : ℂ → ℂ) →
        tsupport (ζ : ℂ → ℂ) ⊆ V → ∃ w : Lp ℂ 2 (volume : Measure ℂ),
          w =ᵐ[volume] (fun z => ζ z * (u z : ℂ)) ∧
          MemSobolev (((n + 1 : ℕ) : ℝ) + 2) 2 (w : 𝓢'(ℂ, ℂ)) := by
      have he : ((n + 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 3 := by push_cast; ring
      simpa only [he] using ih
    have hNL := complexLocalNonlinear_all_cutoffs_add_one hV (n + 1)
      (Nat.succ_pos n) u Ψ (hΨ.of_le (hfin (n + 1 + 1))) huPrev
    have hFS : ∀ ζ : 𝓢(ℂ, ℂ), HasCompactSupport (ζ : ℂ → ℂ) →
        tsupport (ζ : ℂ → ℂ) ⊆ V → ∃ q : Lp ℂ 2 (volume : Measure ℂ),
          q =ᵐ[volume] (fun z => ζ z * (F z : ℂ)) ∧
          MemSobolev ((n + 2 : ℕ) : ℝ) 2 (q : 𝓢'(ℂ, ℂ)) := by
      intro ζ hζc hζV
      obtain ⟨qK, hqK, hsK⟩ := complexLocalContDiffOn_all_cutoffs hV (n + 2) K
        (hK.of_le (hfin (n + 2))) ζ hζc hζV
      obtain ⟨qN, hqN, hsN⟩ := hNL ζ hζc hζV
      refine ⟨qK + qN, ?_, ?_⟩
      · filter_upwards [hqK, hqN, Lp.coeFn_add qK qN] with z hzK hzN hzAdd
        rw [hzAdd, Pi.add_apply, hzK, hzN]
        dsimp [F]
        rw [Complex.ofReal_add, mul_add]
      · have hsN' : MemSobolev ((n + 2 : ℕ) : ℝ) 2 (qN : 𝓢'(ℂ, ℂ)) := by
          simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc,
            one_add_one_eq_two] using hsN
        have hadd : ((qK + qN : Lp ℂ 2 (volume : Measure ℂ)) : 𝓢'(ℂ, ℂ)) =
            (qK : 𝓢'(ℂ, ℂ)) + (qN : 𝓢'(ℂ, ℂ)) :=
          (Lp.toTemperedDistributionCLM ℂ volume 2).map_add qK qN
        rw [hadd]
        exact hsK.add hsN'
    have hePrev : ((n + 2 : ℕ) : ℝ) + 1 = (n : ℝ) + 3 := by push_cast; ring
    have hstep := complexLocalWeakElliptic_all_cutoffs_gain hV (n + 2) u F a
      huL hFL ha heq
      (by simpa only [hePrev] using ih)
      hFS
    have heNext : ((n + 2 : ℕ) : ℝ) + 2 = (n + 1 : ℝ) + 3 := by push_cast; ring
    rw [heNext] at hstep
    simpa only [Nat.cast_succ] using hstep

/-- **Math.** The original real `C¹` weak solution of the smooth local
semilinear equation is itself genuinely smooth. No higher regularity or
replacement representative is assumed. -/
theorem complexLocalSemilinear_contDiffOn
    {V : Set ℂ} (hV : IsOpen V) (u K a : ℂ → ℝ) (Ψ : ℝ → ℝ)
    (hu : ContDiffOn ℝ 1 u V) (hK : ContDiffOn ℝ ∞ K V)
    (ha : ContDiffOn ℝ ∞ a V) (hΨ : ContDiff ℝ ∞ Ψ)
    (heq : ∀ η : ℂ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ V → (∫ z : ℂ, u z * Δ η z) =
        ∫ z : ℂ, a z ^ 2 * ((K z + Ψ (u z)) * η z)) :
    ContDiffOn ℝ ∞ u V := by
  have hS := complexLocalSemilinear_all_cutoffs hV u K a Ψ hu hK ha hΨ heq
  apply contDiffOn_infty.mpr
  intro n
  apply complexLocalSobolev_contDiffOn hV n u hu.continuousOn
  intro ζ hζc hζV
  obtain ⟨w, hwae, hw⟩ := hS n ζ hζc hζV
  exact ⟨w, hwae, hw.mono (by linarith)⟩

#print axioms complexLocalContDiffOn_all_cutoffs
#print axioms complexLocalNonlinear_all_cutoffs_add_one
#print axioms complexLocalSemilinear_all_cutoffs
#print axioms complexLocalSemilinear_contDiffOn

end

end SystolicGrowth
