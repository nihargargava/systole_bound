module

public import Geometry.ComplexLocalWeakEllipticBootstrap
public import Geometry.ComplexSobolevSharpRepresentative
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

/-!
# Local Sobolev regularity upgrades a continuous function to classical `Cⁿ`

At each point, a nested compact cutoff equal to one on a neighborhood
has an actual `H^(n+2)` representative. The sharp Fourier theorem gives
a `Cⁿ` function a.e. equal to it. Continuity of the original function
and positivity of volume on open sets promote that a.e. equality to
pointwise equality on the neighborhood.
-/

open Set MeasureTheory TemperedDistribution
open scoped ContDiff SchwartzMap

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- **Math.** A continuous real local function whose every compact cutoff
has actual Sobolev order `n+2` is classically `Cⁿ` on its open domain.
The local classical function is identified pointwise with the original
one, rather than only chosen as a separate a.e. representative. -/
theorem complexLocalSobolev_contDiffOn
    {V : Set ℂ} (hV : IsOpen V) (n : ℕ) (u : ℂ → ℝ)
    (hu : ContinuousOn u V)
    (hS : ∀ ζ : 𝓢(ℂ, ℂ), HasCompactSupport (ζ : ℂ → ℂ) →
      tsupport (ζ : ℂ → ℂ) ⊆ V →
      ∃ w : Lp ℂ 2 (volume : Measure ℂ),
        w =ᵐ[volume] (fun z => ζ z * (u z : ℂ)) ∧
        MemSobolev ((n : ℝ) + 2) 2 (w : 𝓢'(ℂ, ℂ))) :
    ContDiffOn ℝ n u V := by
  apply contDiffOn_of_locally_contDiffOn
  intro x hx
  obtain ⟨W, _, _, ζ, hW, hxW, hWV, _, _, _, _, hζc, hζV, _, _, hζone⟩ :=
    exists_complex_three_nested_cutoffs hV x hx
  obtain ⟨w, hwae, hw⟩ := hS ζ hζc hζV
  obtain ⟨f, c, hfc, hfae, hc⟩ :=
    complex_memSobolev_add_two_ae_contDiff n (w : 𝓢'(ℂ, ℂ)) hw
  have hwf : w = f := by
    apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
      (F := ℂ) (μ := (volume : Measure ℂ)) (p := 2))
    exact hfc
  have hwc : (w : ℂ → ℂ) =ᵐ[volume] (c : ℂ → ℂ) := hwf ▸ hfae
  have hlocalAE : u =ᵐ[volume.restrict W] (fun z => (c z).re) := by
    filter_upwards [hwae.restrict (s := W), hwc.restrict (s := W),
      ae_restrict_mem hW.measurableSet] with z huz hcz hzW
    have he : (u z : ℂ) = c z := by
      simpa only [hζone z hzW, one_mul] using huz.symm.trans hcz
    exact congrArg Complex.re he
  have hEqOn : EqOn u (fun z => (c z).re) W :=
    Measure.eqOn_open_of_ae_eq hlocalAE hW (hu.mono hWV)
      ((Complex.reCLM.continuous.comp c.continuous).continuousOn)
  have hCn : ContDiffOn ℝ n (fun z => (c z).re) W :=
    (Complex.reCLM.contDiff.comp hc).contDiffOn
  have huW : ContDiffOn ℝ n u W := hCn.congr hEqOn
  exact ⟨W, hW, hxW, huW.mono Set.inter_subset_right⟩

#print axioms complexLocalSobolev_contDiffOn

end

end SystolicGrowth
