module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingConformalLocalEquation
public import Geometry.GluingConformalRepresentative
public import Geometry.ComplexLocalWeakElliptic

@[expose] public section

/-!
# The actual weak surface solution has a classical first derivative

The already constructed graph forcing and solution have common local weak
coordinates. The proved local elliptic gain supplies real `C¹`
representatives, and the actual area law and finite smooth partition glue
them into a global representative of the original weak solution.
-/

open Set Filter Manifold IsManifold MeasureTheory
open scoped ContDiff Topology Manifold RealInnerProductSpace

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** Every actual graph solution with graph forcing has local
real `C¹` representatives. All analytic, metric and measure hypotheses
of the elliptic theorem are supplied by the constructed original surface. -/
theorem gluedConformal_local_contDiff_one
    (P : ExerciseGluingPreparation C g n genera X)
    (v F : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas)
    (hweak : ∀ w : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas,
      inner ℝ (conformalH1Gradient _ _ v) (conformalH1Gradient _ _ w) =
        -inner ℝ (conformalH1Value _ _ F) (conformalH1Value _ _ w))
    (b : P.GluedCarrier) :
    ∃ (Q : GluedConformalPatch P) (W : Set ℂ) (c : ℂ → ℝ),
      let e := Q.original.trans Q.change
      b ∈ Q.region ∧ IsOpen W ∧ e b ∈ W ∧ W ⊆ e '' Q.region ∧
      ContDiffOn ℝ 1 c W ∧
      (fun z => (conformalH1Value P.gluedCurvatureBoundedAreaMeasure
        P.gluedConformalGradientAtlas v) (e.symm z)) =ᵐ[volume.restrict W] c := by
  let A := P.gluedConformalGradientAtlas
  let μ := P.gluedCurvatureBoundedAreaMeasure
  obtain ⟨i, V, hV, hbQ, hbV, hVU, hall⟩ := P.gluedConformalGradient_common_coordinates b
  let Q := P.gluedConformalPatch (P.gluedConformalGradientData.center i)
  let e := Q.original.trans Q.change
  let u : ℂ → ℝ := fun z => (conformalH1Value μ A v) (e.symm z)
  let f : ℂ → ℝ := fun z => (conformalH1Value μ A F) (e.symm z)
  let D (w : ConformalGradientH1 μ A) (j : Fin 2) (z : ℂ) : ℝ :=
    A.coefficient i z / A.weight i (e.symm z) * (conformalH1Gradient μ A w (i, j)) (e.symm z)
  have hVt : V ⊆ e.target := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hVU hz
    exact e.map_source (Q.region_subset hx)
  have hu (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V) :
      MemLp u 2 (volume.restrict K) := ((hall v).1 K hK hKV).1
  have hDu (j : Fin 2) (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V) :
      MemLp (D v j) 2 (volume.restrict K) := ((hall v).1 K hK hKV).2 j
  have hf (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V) :
      MemLp f 2 (volume.restrict K) := ((hall F).1 K hK hKV).1
  have hDf (j : Fin 2) (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V) :
      MemLp (D F j) 2 (volume.restrict K) := ((hall F).1 K hK hKV).2 j
  have heq (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
      (hηV : tsupport η ⊆ V) :
      (∫ z : ℂ, u z * Laplacian.laplacian η z) =
        ∫ z : ℂ, Q.coefficient z ^ 2 * (f z * η z) :=
    P.gluedConformalGradient_forcing_weak_laplacian v F hweak Q η hη hηc (hηV.trans hVU)
  obtain ⟨W, c, hW, hbw, hWV, hc, hae⟩ := complexLocalWeakElliptic_exists_contDiff_one
    hV u f Q.coefficient (D v) (D F) hu hDu (hall v).2 hf hDf (hall F).2
    (Q.coefficient_smooth.mono hVt) heq (e b) hbV
  exact ⟨Q, W, c, hbQ, hW, hbw, hWV.trans hVU, hc, hae⟩

/-- **Math.** The internally constructed nonlinear weak solution has a
global classical `C¹` representative. No regularity or PDE solution is
assumed: graph existence, local elliptic gain, area transport and gluing
are all applied to the original glued carrier. -/
theorem exists_gluedConformal_contDiff_one_solution
    (P : ExerciseGluingPreparation C g n genera X) :
    ∃ (B : ℝ) (hB : 1 < B),
      (∀ b, P.gluedCurvatureBoundedGaussian b ∈ Icc (-B) (-1 : ℝ)) ∧
      ∃ v : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas,
        (∀ w : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas,
          inner ℝ (conformalH1Gradient _ _ v) (conformalH1Gradient _ _ w) =
            -inner ℝ (P.gluedConformalGaussianL2 + conformalCurvatureNonlinearityLp
              P.gluedCurvatureBoundedAreaMeasure B hB (conformalH1Value _ _ v))
              (conformalH1Value _ _ w)) ∧
        ∃ u : P.GluedCarrier → ℝ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 1 u ∧
          u =ᵐ[P.gluedCurvatureBoundedAreaMeasure]
            (conformalH1Value P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas v) := by
  obtain ⟨B, hB, hK, v, F, hF, hweak⟩ := P.exists_gluedConformal_solution_forcing_graph
  refine ⟨B, hB, hK, v, ?_, ?_⟩
  · intro w
    simpa only [hF] using hweak w
  · exact P.exists_gluedConformal_global_representative v 1
      (WithTop.coe_le_coe.mpr (show (1 : ℕ∞) ≤ ⊤ from le_top))
      (P.gluedConformal_local_contDiff_one v F hweak)

#print axioms gluedConformal_local_contDiff_one
#print axioms exists_gluedConformal_contDiff_one_solution

end

end SystolicGrowth.ExerciseGluingPreparation
