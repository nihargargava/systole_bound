module

public import Geometry.ComplexHkClassicalGradientWitness
public import Geometry.ComplexNonlinearCutoffRegularity

@[expose] public section

/-!
# All finite-order nonlinear regularity from an actual real Sobolev cutoff

The Fourier `H^(k+2) → C^k` representative and genuine gradient witnesses
feed the proved compact nonlinear chain rule. A smaller cutoff transfers the
conclusion from the local regularity witness to the original function.
-/

open MeasureTheory TemperedDistribution
open scoped ContDiff SchwartzMap

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- **Math.** Every actual real `H^(k+2)` local cutoff, `k≥1`, makes the
smaller compact nonlinear cutoff genuinely `H^(k+1)`. The matching premise
only says the two real functions agree wherever the smaller cutoff is
nonzero, so the theorem directly composes nested cutoffs of one weak PDE. -/
theorem complexHk_real_nonlinear_cutoff_memSobolev_add_one
    (k : ℕ) (hk : 1 ≤ k)
    (w : Lp ℂ 2 (volume : Measure ℂ))
    (hw : MemSobolev ((k : ℝ) + 2) 2 (w : 𝓢'(ℂ, ℂ)))
    (u v : ℂ → ℝ) (hwv : w =ᵐ[volume] fun z => (v z : ℂ))
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (k + 1 : ℕ) Ψ)
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ (k + 1 : ℕ) χ)
    (hχc : HasCompactSupport χ)
    (hmatch : ∀ᵐ z ∂volume, χ z ≠ 0 → v z = u z) :
    ∃ U : Lp ℂ 2 (volume : Measure ℂ),
      U =ᵐ[volume] (fun z => χ z * ((Ψ (u z) : ℝ) : ℂ)) ∧
      MemSobolev ((k : ℝ) + 1) 2 (U : 𝓢'(ℂ, ℂ)) := by
  obtain ⟨c, G, hc, hwc, hG, hGSob⟩ :=
    complexHk_real_exists_classical_gradient_witness k hk w hw v hwv
  obtain ⟨U, hUc, hUSob⟩ :=
    complexRealScalar_compactCutoff_memSobolev_add_one k hk c hc Ψ hΨ
      χ hχ hχc G hG hGSob
  have hcv : c =ᵐ[volume] v := by
    filter_upwards [hwc, hwv] with z hcz hvz
    exact Complex.ofReal_injective (hcz.symm.trans hvz)
  refine ⟨U, ?_, hUSob⟩
  filter_upwards [hUc, hcv, hmatch] with z hUz hcz hzu
  rw [hUz]
  by_cases hz : χ z = 0
  · simp [hz]
  · rw [hcz, hzu hz]

#print axioms complexHk_real_nonlinear_cutoff_memSobolev_add_one

end

end SystolicGrowth
