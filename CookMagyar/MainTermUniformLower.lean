module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.MainTermLowerBridge
public import CookMagyar.SingularSeriesUniformLower

@[expose] public section

namespace SystolicGrowth.CookMagyarCircle

/-! The unconditional local and real density bounds give a uniform positive
cubic main term on the admissible target window. -/

/-- The explicit real-place density lower bound is strictly positive as a
real number. -/
theorem geometricDensityLowerBound_toReal_pos
    {n : ℕ} (hn : 0 < n) :
    0 < (CookMagyarReal.geometricDensityLowerBound n).toReal := by
  have hpos := CookMagyarReal.geometricDensityLowerBound_pos hn
  have htop : CookMagyarReal.geometricDensityLowerBound n ≠ ⊤ := by
    unfold CookMagyarReal.geometricDensityLowerBound
    exact ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (by norm_num)
  exact ENNReal.toReal_pos hpos.ne' htop

/-- The cubic singular main term has an arity-dependent positive coefficient
uniform over admissible targets in the normalized real window. -/
theorem exists_uniform_cubicSingularMainTerm_lower
    {n : ℕ} (hn : 33 ≤ n) :
    ∃ c : ℝ, 0 < c ∧
      ∀ N T : ℕ, 0 < N → 24 ∣ T →
        CookMagyarReal.NormalizedTargetWindow n
          (CookMagyarReal.normalizedTarget N T) →
        c * cubicMainScale n N ≤ cubicSingularMainTerm n N T := by
  obtain ⟨s, hs, hseries⟩ :=
    CookMagyarFiniteFourier.exists_uniform_singularSeries_re_lower hn
  let c : ℝ := s * (CookMagyarReal.geometricDensityLowerBound n).toReal
  refine ⟨c, ?_, ?_⟩
  · dsimp [c]
    exact mul_pos hs (geometricDensityLowerBound_toReal_pos (by omega))
  · intro N T hN hT hwindow
    change (s * (CookMagyarReal.geometricDensityLowerBound n).toReal) *
      cubicMainScale n N ≤ cubicSingularMainTerm n N T
    exact cubicSingularMainTerm_ge_of_singularSeries_re_lower
      (by omega : 4 ≤ n) hN hwindow hs.le
      (CookMagyarFiniteFourier.singularSeries_im_eq_zero_of_admissible hn hT)
      (hseries T hT)

end SystolicGrowth.CookMagyarCircle
