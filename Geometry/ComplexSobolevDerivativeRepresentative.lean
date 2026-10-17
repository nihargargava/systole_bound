module

public import Geometry.ComplexSobolevContinuousRepresentative

@[expose] public section

/-!
# Continuous representatives of all sufficiently controlled weak derivatives

An `Hⁿ⁺²` complex-plane distribution has bounded continuous representatives
of its distributional derivatives of order `n`, as actual a.e. representatives
of their `L²` functions. The separate passage from these weak derivatives to
classical `Cⁿ` derivatives is not asserted here.
-/

open TemperedDistribution MeasureTheory
open scoped LineDeriv SchwartzMap BoundedContinuousFunction

namespace SystolicGrowth

noncomputable section

/-- Iterated actual distributional directional derivatives. -/
def complexIteratedLineDeriv : List ℂ → 𝓢'(ℂ, ℂ) → 𝓢'(ℂ, ℂ)
  | [], w => w
  | v :: vs, w => complexIteratedLineDeriv vs (∂_{v} w)

/-- Each distributional differentiation consumes one Sobolev order. -/
theorem complexIteratedLineDeriv_memSobolev
    (vs : List ℂ) (s : ℝ) (w : 𝓢'(ℂ, ℂ))
    (hw : MemSobolev (s + (vs.length : ℝ)) 2 w) :
    MemSobolev s 2 (complexIteratedLineDeriv vs w) := by
  induction vs generalizing w with
  | nil =>
    simpa [complexIteratedLineDeriv] using hw
  | cons v vs ih =>
    have hd : MemSobolev (s + (vs.length : ℝ)) 2 (∂_{v} w) := by
      have hh := hw.lineDerivOp (m := v)
      have heq : s + ((vs.length : ℝ) + 1) - 1 = s + (vs.length : ℝ) := by
        ring
      simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, heq] using hh
    exact ih (∂_{v} w) hd

/-- Every order-`n` weak derivative of an `Hⁿ⁺²` distribution has a bounded
continuous function equal a.e. to its genuine `L²` representative. -/
theorem complexIteratedLineDeriv_ae_boundedContinuous
    (vs : List ℂ) (w : 𝓢'(ℂ, ℂ))
    (hw : MemSobolev (2 + (vs.length : ℝ)) 2 w) :
    ∃ (f : Lp ℂ 2 (volume : Measure ℂ)) (c : ℂ →ᵇ ℂ),
      complexIteratedLineDeriv vs w = (f : 𝓢'(ℂ, ℂ)) ∧
        (f : ℂ → ℂ) =ᵐ[volume] (c : ℂ → ℂ) :=
  complex_memSobolev_two_ae_boundedContinuous _
    (complexIteratedLineDeriv_memSobolev vs 2 w hw)

#print axioms complexIteratedLineDeriv_memSobolev
#print axioms complexIteratedLineDeriv_ae_boundedContinuous

end

end SystolicGrowth
