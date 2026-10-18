module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ConformalLocalRepresentativeGluing
public import Geometry.GluingConformalWeakToClassical

@[expose] public section

/-!
# Global representatives from actual conformal coordinate regularity

Local coordinate representatives are transported with the proved positive
area law and glued in the original smooth structure. This supplies the
global step between local Fourier regularity and the actual classical
curvature equation, without assuming compatibility on chart overlaps.
-/

open Set Filter Manifold IsManifold MeasureTheory
open scoped ContDiff Topology Manifold

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** Actual local coordinate regularity yields a global
classical representative of the SAME graph value. Both area transport
and smooth gluing are constructed; no global representative is an input. -/
theorem exists_gluedConformal_global_representative
    (P : ExerciseGluingPreparation C g n genera X)
    (v : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas)
    (r : ℕ∞ω) (hr : r ≤ ∞)
    (hlocal : ∀ b : P.GluedCarrier,
      ∃ (Q : GluedConformalPatch P) (V : Set ℂ) (c : ℂ → ℝ),
        let e := Q.original.trans Q.change
        b ∈ Q.region ∧ IsOpen V ∧ e b ∈ V ∧ V ⊆ e '' Q.region ∧
        ContDiffOn ℝ r c V ∧
        (fun z => (conformalH1Value P.gluedCurvatureBoundedAreaMeasure
          P.gluedConformalGradientAtlas v) (e.symm z)) =ᵐ[volume.restrict V] c) :
    ∃ u : P.GluedCarrier → ℝ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) r u ∧
      u =ᵐ[P.gluedCurvatureBoundedAreaMeasure]
        (conformalH1Value P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas v) := by
  classical
  let μ := P.gluedCurvatureBoundedAreaMeasure
  let value := conformalH1Value μ P.gluedConformalGradientAtlas v
  have hloc : ∀ b : P.GluedCarrier,
      ∃ U : Set P.GluedCarrier, IsOpen U ∧ b ∈ U ∧
        ∃ f : P.GluedCarrier → ℝ, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ) r f U ∧
          f =ᵐ[μ.restrict U] value := by
    intro b
    obtain ⟨Q, V, c, hbQ, hV, hbV, hVU, hc, hae⟩ := hlocal b
    let e := Q.original.trans Q.change
    have hVt : V ⊆ e.target := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := hVU hz
      exact e.map_source (Q.region_subset hx)
    let U := e.symm '' V
    have hU : IsOpen U := e.symm.isOpen_image_of_subset_source hV hVt
    have hUQ : U ⊆ Q.region := by
      rintro x ⟨z, hz, rfl⟩
      obtain ⟨y, hy, rfl⟩ := hVU hz
      change e.symm (e y) ∈ Q.region
      rw [e.left_inv (Q.region_subset hy)]
      exact hy
    have hUs : U ⊆ e.source := hUQ.trans Q.region_subset
    have himage : e '' U = V := by
      ext z
      constructor
      · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩
        simpa only [e.right_inv (hVt hw)] using hw
      · intro hz
        exact ⟨e.symm z, ⟨z, hz, rfl⟩, e.right_inv (hVt hz)⟩
    have hbU : b ∈ U := ⟨e b, hbV, e.left_inv (Q.region_subset hbQ)⟩
    let f : P.GluedCarrier → ℝ := fun x => c (e x)
    have hf : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ) r f U := by
      apply hc.contMDiffOn.comp
        (((contMDiffOn_of_mem_maximalAtlas Q.chart_mem).of_le hr).mono hUs)
      intro x hx
      rw [← himage]
      exact ⟨x, hx, rfl⟩
    have harea : ∀ s : Set ℂ, MeasurableSet s → s ⊆ e '' U →
        μ (e.symm '' s) = ∫⁻ z : ℂ in s, ENNReal.ofReal (Q.coefficient z ^ 2) := by
      intro s hs hsU
      exact Q.area_eq s hs (hsU.trans (image_mono hUQ))
    have hfae : f =ᵐ[μ.restrict U] value := by
      apply (conformalChart_ae_eq_pullback_iff μ e U hU hUs Q.coefficient
        Q.coefficient_smooth.continuousOn Q.coefficient_pos harea).mpr
      rw [himage]
      filter_upwards [hae, ae_restrict_mem hV.measurableSet] with z hz hzV
      change c (e (e.symm z)) = value (e.symm z)
      rw [e.right_inv (hVt hzV)]
      exact hz.symm
    exact ⟨U, hU, hbU, f, hf, hfae⟩
  choose U hU hb f hf hfae using hloc
  exact exists_contMDiff_ae_eq_of_local_representatives μ value r hr U hU hb f hf hfae

#print axioms exists_gluedConformal_global_representative

end

end SystolicGrowth.ExerciseGluingPreparation
