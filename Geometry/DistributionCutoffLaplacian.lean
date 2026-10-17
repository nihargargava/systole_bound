module

public import Geometry.EuclideanSobolevEllipticRegularity
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

/-!
# Distributional cutoff product rules on the Euclidean plane

The product rules are derived from the test-function definition of tempered
distribution derivatives. They are not assumed as an elliptic regularity API.
-/

open TemperedDistribution
open MeasureTheory
open scoped Laplacian LineDeriv SchwartzMap

namespace SystolicGrowth

noncomputable section

/-- Leibniz's rule in Schwartz space, used as the test-function identity for
the distributional product rule. -/
theorem euclideanSchwartz_lineDeriv_smulLeft
    (ζ φ : 𝓢(EuclideanPlane, ℂ)) (v : EuclideanPlane) :
    ∂_{v} (SchwartzMap.smulLeftCLM ℂ ζ φ) =
      SchwartzMap.smulLeftCLM ℂ (∂_{v} ζ : 𝓢(EuclideanPlane, ℂ)) φ +
        SchwartzMap.smulLeftCLM ℂ ζ (∂_{v} φ) := by
  ext x
  have hζ : (ζ : EuclideanPlane → ℂ).HasTemperateGrowth := ζ.hasTemperateGrowth
  have hderivζ : ((∂_{v} ζ : 𝓢(EuclideanPlane, ℂ)) : EuclideanPlane → ℂ).HasTemperateGrowth :=
    (∂_{v} ζ : 𝓢(EuclideanPlane, ℂ)).hasTemperateGrowth
  have hprod : ((SchwartzMap.smulLeftCLM ℂ ζ φ : 𝓢(EuclideanPlane, ℂ)) :
      EuclideanPlane → ℂ) = fun y => ζ y * φ y := by
    funext y
    simp [hζ, smul_eq_mul]
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [hprod, fderiv_fun_mul ζ.differentiableAt φ.differentiableAt]
  simp [hζ, hderivζ, SchwartzMap.smulLeftCLM_apply_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul, mul_comm]
  abel

/-- Leibniz's rule for a Schwartz multiplier and the actual distributional
directional derivative, obtained by applying the Schwartz identity to each
test function. -/
theorem euclideanDistribution_lineDeriv_smulLeft
    (ζ : 𝓢(EuclideanPlane, ℂ)) (w : 𝓢'(EuclideanPlane, ℂ))
    (v : EuclideanPlane) :
    ∂_{v} (TemperedDistribution.smulLeftCLM ℂ ζ w) =
      TemperedDistribution.smulLeftCLM ℂ
        (∂_{v} ζ : 𝓢(EuclideanPlane, ℂ)) w +
      TemperedDistribution.smulLeftCLM ℂ ζ (∂_{v} w) := by
  ext φ
  simp only [TemperedDistribution.lineDerivOp_apply_apply,
    TemperedDistribution.smulLeftCLM_apply_apply, add_apply]
  rw [euclideanSchwartz_lineDeriv_smulLeft ζ φ v]
  simp

private theorem euclideanDistribution_secondLineDeriv_smulLeft
    (ζ : 𝓢(EuclideanPlane, ℂ)) (w : 𝓢'(EuclideanPlane, ℂ))
    (v : EuclideanPlane) :
    ∂_{v} (∂_{v} (TemperedDistribution.smulLeftCLM ℂ ζ w)) =
      TemperedDistribution.smulLeftCLM ℂ
        (∂_{v} (∂_{v} ζ) : 𝓢(EuclideanPlane, ℂ)) w +
      TemperedDistribution.smulLeftCLM ℂ
        (∂_{v} ζ : 𝓢(EuclideanPlane, ℂ)) (∂_{v} w) +
      TemperedDistribution.smulLeftCLM ℂ
        (∂_{v} ζ : 𝓢(EuclideanPlane, ℂ)) (∂_{v} w) +
      TemperedDistribution.smulLeftCLM ℂ ζ (∂_{v} (∂_{v} w)) := by
  rw [euclideanDistribution_lineDeriv_smulLeft ζ w v, LineDeriv.lineDerivOp_add,
    euclideanDistribution_lineDeriv_smulLeft (∂_{v} ζ) w v,
    euclideanDistribution_lineDeriv_smulLeft ζ (∂_{v} w) v]
  abel

/-- Distributional Laplacian cutoff product rule on the Euclidean plane.
The middle sum is the literal `2 ∇ζ · ∇w` commutator in an orthonormal basis. -/
theorem euclideanDistribution_laplacian_smulLeft
    (ζ : 𝓢(EuclideanPlane, ℂ)) (w : 𝓢'(EuclideanPlane, ℂ)) :
    Δ (TemperedDistribution.smulLeftCLM ℂ ζ w) =
      TemperedDistribution.smulLeftCLM ℂ (Δ ζ : 𝓢(EuclideanPlane, ℂ)) w +
      (2 : ℂ) • (∑ i : Fin (Module.finrank ℝ EuclideanPlane),
        TemperedDistribution.smulLeftCLM ℂ
          (∂_{(stdOrthonormalBasis ℝ EuclideanPlane) i} ζ : 𝓢(EuclideanPlane, ℂ))
          (∂_{(stdOrthonormalBasis ℝ EuclideanPlane) i} w)) +
      TemperedDistribution.smulLeftCLM ℂ ζ (Δ w) := by
  let b := stdOrthonormalBasis ℝ EuclideanPlane
  rw [TemperedDistribution.laplacian_eq_sum b,
    SchwartzMap.laplacian_eq_sum b,
    TemperedDistribution.laplacian_eq_sum b]
  simp_rw [euclideanDistribution_secondLineDeriv_smulLeft]
  simp only [Finset.sum_add_distrib]
  have hfirst :
      (∑ i, TemperedDistribution.smulLeftCLM ℂ
        (∂_{b i} (∂_{b i} ζ) : 𝓢(EuclideanPlane, ℂ)) w) =
      TemperedDistribution.smulLeftCLM ℂ
        (∑ i, ∂_{b i} (∂_{b i} ζ) : 𝓢(EuclideanPlane, ℂ)) w := by
    ext φ
    simp only [sum_apply, TemperedDistribution.smulLeftCLM_apply_apply]
    rw [← map_sum]
    congr 1
    ext x
    simp [SchwartzMap.smulLeftCLM_apply_apply,
      SchwartzMap.hasTemperateGrowth, Finset.sum_mul]
  have hthird :
      (∑ i, TemperedDistribution.smulLeftCLM ℂ ζ
        (∂_{b i} (∂_{b i} w))) =
      TemperedDistribution.smulLeftCLM ℂ ζ
        (∑ i, ∂_{b i} (∂_{b i} w)) := by
    simp only [map_sum]
  rw [hfirst, hthird]
  dsimp only [b]
  ext φ
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Multiplication by a Schwartz cutoff preserves actual `L²`-represented
tempered distributions. This uses the `L∞ · L² ⊆ L²` embedding, not a formal
membership assumption for the product. -/
theorem euclideanDistribution_memSobolev_zero_smulLeft
    (ζ : 𝓢(EuclideanPlane, ℂ)) (w : 𝓢'(EuclideanPlane, ℂ))
    (hw : MemSobolev 0 2 w) :
    MemSobolev 0 2 (TemperedDistribution.smulLeftCLM ℂ ζ w) := by
  obtain ⟨f, rfl⟩ := memSobolev_zero_iff.mp hw
  apply memSobolev_zero_iff.mpr
  refine ⟨(ζ.toLp ⊤ volume) • f, ?_⟩
  exact (Lp.toTemperedDistribution_smul_eq ζ.hasTemperateGrowth (ζ.memLp ⊤ volume) f).symm

/-- The first local elliptic step: an `H¹` distribution gains `H²` after
cutoff when its Laplacian is `L²` on that cutoff. The two first-order
commutator terms are accounted for by the proved distributional product
rule, rather than omitted. -/
theorem euclideanDistribution_memSobolev_two_cutoff
    (ζ : 𝓢(EuclideanPlane, ℂ)) (w : 𝓢'(EuclideanPlane, ℂ))
    (hw : MemSobolev 1 2 w)
    (hζΔ : MemSobolev 0 2
      (TemperedDistribution.smulLeftCLM ℂ ζ (Δ w))) :
    MemSobolev 2 2 (TemperedDistribution.smulLeftCLM ℂ ζ w) := by
  let b := stdOrthonormalBasis ℝ EuclideanPlane
  have hw₀ : MemSobolev 0 2 w := hw.mono (by norm_num)
  have hζw₀ := euclideanDistribution_memSobolev_zero_smulLeft ζ w hw₀
  have hΔζw₀ := euclideanDistribution_memSobolev_zero_smulLeft
    (Δ ζ : 𝓢(EuclideanPlane, ℂ)) w hw₀
  have hterm (i : Fin (Module.finrank ℝ EuclideanPlane)) :
      MemSobolev 0 2 (TemperedDistribution.smulLeftCLM ℂ
        (∂_{b i} ζ : 𝓢(EuclideanPlane, ℂ)) (∂_{b i} w)) := by
    apply euclideanDistribution_memSobolev_zero_smulLeft
    simpa using (hw.lineDerivOp (m := b i))
  have hcross (s : Finset (Fin (Module.finrank ℝ EuclideanPlane))) :
      MemSobolev 0 2 (∑ i ∈ s, TemperedDistribution.smulLeftCLM ℂ
        (∂_{b i} ζ : 𝓢(EuclideanPlane, ℂ)) (∂_{b i} w)) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hterm i).add ih
  have hΔprod₀ : MemSobolev 0 2
      (Δ (TemperedDistribution.smulLeftCLM ℂ ζ w)) := by
    rw [euclideanDistribution_laplacian_smulLeft]
    exact (hΔζw₀.add ((hcross Finset.univ).smul (2 : ℂ))).add hζΔ
  simpa using euclidean_memSobolev_add_two_of_laplacian 0
    (TemperedDistribution.smulLeftCLM ℂ ζ w) hζw₀ hΔprod₀

#print axioms euclideanSchwartz_lineDeriv_smulLeft
#print axioms euclideanDistribution_lineDeriv_smulLeft
#print axioms euclideanDistribution_laplacian_smulLeft
#print axioms euclideanDistribution_memSobolev_two_cutoff

end

end SystolicGrowth
