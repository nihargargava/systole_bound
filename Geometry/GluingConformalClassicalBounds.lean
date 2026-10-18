module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingConformalCurvaturePDE
public import Geometry.ConformalCurvatureMaximumPrinciple
public import Geometry.GluingConformalLiftedOutput

@[expose] public section

/-!
# Maximum principle on the actual canonical glued conformal charts

The literal canonical scalar equation is parameterized by its nonlinearity.
The actual seam/interior chart constructors supply the local regularity
and positive coefficient required by the verified Hessian maximum principle.
For the constructed smooth extension `Ψ_B`, this proves its genuine bounds
and converts its scalar equation to the exponential curvature equation.
-/

open Set Filter Bundle Manifold Riemannian IsManifold
open scoped Manifold Topology ContDiff

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** The same genuine canonical scalar equations with an
arbitrary scalar nonlinearity, retaining the original concrete coefficients
and isolation requirements. The exponential specialization is the existing
curvature-PDE contract, not a new assumption about the metric. -/
def GluedConformalNonlinearClassicalPDE
    (P : ExerciseGluingPreparation C g n genera X) (N : ℝ → ℝ) (u : P.GluedCarrier → ℝ) : Prop :=
  (∀ (b : P.GluedCarrier) (k : Fin (n - 1)) (θ : ℝ),
    chartAt ℂ b = P.seamAngularComplexChart k θ →
    (∀ l : Fin (n - 1), l ≠ k → b ∉ P.closedThinSeamCollar l) →
    Laplacian.laplacian (u ∘ (P.gluedCurvatureBoundedSeamConformalChart k θ).symm)
        (P.gluedCurvatureBoundedSeamConformalChart k θ b) =
      P.gluedCurvatureBoundedSeamConformalFactor
          (P.gluedCurvatureBoundedSeamConformalChart k θ b) ^ 2 *
        (P.gluedCurvatureBoundedGaussian b + N (u b))) ∧
  (∀ b : P.GluedCarrier,
    P.IsGluedInteriorComplexChart (chartAt ℂ b) →
    (∀ k : Fin (n - 1), b ∉ P.closedThinSeamCollar k) →
    Laplacian.laplacian (u ∘ (chartAt ℂ b).symm) (chartAt ℂ b b) =
      (chartAt ℂ b b).im⁻¹ ^ 2 * (P.gluedCurvatureBoundedGaussian b + N (u b)))

/-- **Math.** The exponential specialization preserves the already
verified canonical PDE contract exactly. -/
theorem gluedConformalNonlinearClassicalPDE_exp_iff
    (P : ExerciseGluingPreparation C g n genera X) (u : P.GluedCarrier → ℝ) :
    P.GluedConformalNonlinearClassicalPDE (fun t => Real.exp (2 * t)) u ↔
      P.GluedConformalClassicalPDE u := Iff.rfl

/-- **Math.** The actual canonical atlas constructions supply all
coordinate hypotheses at every point: genuine local `C²` regularity, a
positive actual coefficient and the literal scalar PDE. -/
theorem gluedConformalNonlinearClassicalPDE_coordinate_at
    (P : ExerciseGluingPreparation C g n genera X) (N : ℝ → ℝ)
    (u : P.GluedCarrier → ℝ)
    (hu : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) 2 u)
    (hpde : P.GluedConformalNonlinearClassicalPDE N u) (b : P.GluedCarrier) :
    ∃ e : OpenPartialHomeomorph P.GluedCarrier ℂ,
      b ∈ e.source ∧ ContDiffAt ℝ 2 (u ∘ e.symm) (e b) ∧
      ∃ a : ℝ, 0 < a ∧ Laplacian.laplacian (u ∘ e.symm) (e b) =
        a ^ 2 * (P.gluedCurvatureBoundedGaussian b + N (u b)) := by
  have htwo : (2 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  have hregular (e : OpenPartialHomeomorph P.GluedCarrier ℂ)
      (he : e ∈ maximalAtlas (modelWithCornersSelf ℝ ℂ) ∞ P.GluedCarrier) (hb : b ∈ e.source) :
      ContDiffAt ℝ 2 (u ∘ e.symm) (e b) :=
    ((hu.comp_contMDiffOn ((contMDiffOn_symm_of_mem_maximalAtlas he).of_le htwo)).contDiffOn).contDiffAt
      (e.open_target.mem_nhds (e.map_source hb))
  have hseam (k : Fin (n - 1)) (θ : ℝ)
      (hchart : chartAt ℂ b = P.seamAngularComplexChart k θ)
      (hother : ∀ l : Fin (n - 1), l ≠ k → b ∉ P.closedThinSeamCollar l) :
      ∃ e : OpenPartialHomeomorph P.GluedCarrier ℂ,
        b ∈ e.source ∧ ContDiffAt ℝ 2 (u ∘ e.symm) (e b) ∧
        ∃ a : ℝ, 0 < a ∧ Laplacian.laplacian (u ∘ e.symm) (e b) =
          a ^ 2 * (P.gluedCurvatureBoundedGaussian b + N (u b)) := by
    let e := P.gluedCurvatureBoundedSeamConformalChart k θ
    have hb : b ∈ e.source := by
      rw [gluedCurvatureBoundedSeamConformalChart_source, ← hchart]
      exact mem_chart_source ℂ b
    refine ⟨e, hb, hregular e (P.gluedCurvatureBoundedSeamConformalChart_mem_maximalAtlas k θ) hb,
      P.gluedCurvatureBoundedSeamConformalFactor (e b),
      P.gluedCurvatureBoundedSeamConformalFactor_pos _, hpde.1 b k θ hchart hother⟩
  by_cases hc : ∃ k : Fin (n - 1), b ∈ P.closedThinSeamCollar k
  · obtain ⟨k, hk⟩ := hc
    obtain ⟨θ, hchart⟩ := P.gluedCurvatureBounded_chartAt_eq_seam_of_mem_closedThinSeamCollar b k hk
    exact hseam k θ hchart
      (fun l hl h => Set.disjoint_left.mp (P.closedThinSeamCollar_disjoint hl) h hk)
  · have hout : ∀ k : Fin (n - 1), b ∉ P.closedThinSeamCollar k := fun k hk => hc ⟨k, hk⟩
    rcases P.gluedCurvatureBounded_chartAt_is_seam_or_interior b with hi | ⟨k, θ, hchart⟩
    · let e := chartAt ℂ b
      have hb : b ∈ e.source := mem_chart_source ℂ b
      refine ⟨e, hb, hregular e (chart_mem_maximalAtlas b) hb, (e b).im⁻¹, ?_, hpde.2 b hi hout⟩
      exact inv_pos.mpr (P.gluedInteriorComplexChart_target_im_pos e hi (e.map_source hb))
    · exact hseam k θ hchart (fun l _ => hout l)

/-- **Math.** The actual classical `Ψ_B` solution is bounded in precisely
the interval where the constructed extension agrees with `exp (2t)`.
The curvature scalar here is the SAME already constructed intrinsic
Gaussian field, not a separately supplied abstract curvature function. -/
theorem gluedConformalPsiClassicalSolution_bounds
    (P : ExerciseGluingPreparation C g n genera X) (B : ℝ) (hB : 1 < B)
    (hK : ∀ b, P.gluedCurvatureBoundedGaussian b ∈ Icc (-B) (-1 : ℝ))
    (u : P.GluedCarrier → ℝ)
    (hu : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) 2 u)
    (hpde : P.GluedConformalNonlinearClassicalPDE (conformalCurvatureNonlinearity B) u) :
    ∀ b, u b ∈ Icc (0 : ℝ) (Real.log B / 2) :=
  conformalCurvatureMaximumPrinciple u P.gluedCurvatureBoundedGaussian hu.continuous B hB hK
    (P.gluedConformalNonlinearClassicalPDE_coordinate_at _ u hu hpde)

/-- **Math.** The maximum-principle bounds convert the ACTUAL canonical
`Ψ_B` equation into the exponential scalar equation needed by the proved
intrinsic conformal curvature theorem, without an exponential agreement
or nonnegativity premise. -/
theorem gluedConformalPsiClassicalSolution_exp_pde
    (P : ExerciseGluingPreparation C g n genera X) (B : ℝ) (hB : 1 < B)
    (hK : ∀ b, P.gluedCurvatureBoundedGaussian b ∈ Icc (-B) (-1 : ℝ))
    (u : P.GluedCarrier → ℝ)
    (hu : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) 2 u)
    (hpde : P.GluedConformalNonlinearClassicalPDE (conformalCurvatureNonlinearity B) u) :
    P.GluedConformalClassicalPDE u := by
  have hbounds := P.gluedConformalPsiClassicalSolution_bounds B hB hK u hu hpde
  constructor
  · intro b k θ hchart hother
    simpa only [conformalCurvatureNonlinearity_eq_exp (hbounds b)] using hpde.1 b k θ hchart hother
  · intro b hi hout
    simpa only [conformalCurvatureNonlinearity_eq_exp (hbounds b)] using hpde.2 b hi hout

/-- **Math.** Produce all six geometric source fields from a genuine
smooth classical `Ψ_B` solution. Its nonnegativity and exponential PDE
are DERIVED on the actual canonical charts by the maximum principle;
the metric, curvature, systole, representation and coherent lift are
then constructed internally by the verified geometric consumers. -/
def gluedConformalPsiLiftedOutput
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g)
    (B : ℝ) (hB : 1 < B)
    (hK : ∀ b, P.gluedCurvatureBoundedGaussian b ∈ Icc (-B) (-1 : ℝ))
    (u : P.GluedCarrier → ℝ)
    (hu : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞ u)
    (hpde : P.GluedConformalNonlinearClassicalPDE (conformalCurvatureNonlinearity B) u) :
    ExerciseLiftedChainOutput g (targetSystole C g) := by
  have htwo : (2 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  have hu2 := hu.of_le htwo
  exact P.gluedConformalLiftedOutput x hn hsum u hu
    (P.gluedConformalPsiClassicalSolution_exp_pde B hB hK u hu2 hpde)
    (fun b => (P.gluedConformalPsiClassicalSolution_bounds B hB hK u hu2 hpde b).1)

#print axioms gluedConformalNonlinearClassicalPDE_coordinate_at
#print axioms gluedConformalPsiClassicalSolution_bounds
#print axioms gluedConformalPsiClassicalSolution_exp_pde
#print axioms gluedConformalPsiLiftedOutput

end

end SystolicGrowth.ExerciseGluingPreparation
