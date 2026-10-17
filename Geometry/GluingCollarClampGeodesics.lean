module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarClamp
public import Geometry.GluingCollarModelGeodesics

@[expose] public section

/-!
# Collar geodesics inside bounded radial windows

The native collar distance has geodesics by properness. Composing one with
the proved nonexpanding radial clamp gives a geodesic with the same endpoints
whenever those endpoints are in the clamped window.
-/

open Set MeasureTheory Bundle Manifold
open scoped Manifold Topology Bundle ENNReal NNReal

namespace SystolicGrowth

/-- The weighted-length infimum restricted to ordinary-coordinate Lipschitz
curves whose radial coordinate stays in `[-R,R]`.  The interval constraint
is part of the indexing family, so this is exactly the intrinsic admissible
path distance for the closed collar window. -/
noncomputable def gluingCollarWindowAdmissibleEDist (r R : ℝ) (z w : ℂ) : ℝ≥0∞ :=
  ⨅ (α : ℝ → ℂ) (_h0 : α 0 = z) (_h1 : α 1 = w)
    (_hLip : ∃ K : ℝ≥0, LipschitzOnWith K α (Icc (0 : ℝ) 1))
    (_hWindow : ∀ t ∈ Icc (0 : ℝ) 1, (α t).re ∈ Icc (-R) R),
    ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
      (Real.sqrt (gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t)))

/-- Clamping fixes a real coordinate already in the target interval. -/
theorem gluingCollarClampReal_eq_of_mem {R t : ℝ} (ht : t ∈ Icc (-R) R) :
    gluingCollarClampReal R t = t := by
  rw [gluingCollarClampReal, min_eq_right ht.2, max_eq_right ht.1]

/-- The complex clamp fixes points whose real coordinate is in the window. -/
theorem gluingCollarClamp_eq_self_of_re_mem {R : ℝ} {z : ℂ}
    (hz : z.re ∈ Icc (-R) R) : gluingCollarClamp R z = z := by
  apply Complex.ext <;> simp [gluingCollarClamp, gluingCollarClampReal_eq_of_mem hz]

/-- Restricting the admissible curve family to a closed radial window does
not change distances between points of that window.  One inequality is
monotonicity under restricting the family; the other clamps every global
admissible curve, preserving its endpoints and not increasing its weighted
length. -/
theorem gluingCollarWindowAdmissibleEDist_eq_native {r R : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R) {z w : ℂ}
    (hz : z.re ∈ Icc (-R) R) (hw : w.re ∈ Icc (-R) R) :
    gluingCollarWindowAdmissibleEDist r R z w = gluingCollarModelEDist hr z w := by
  have hglobal_le_window :
      gluingCollarAdmissibleEDist r z w ≤
        gluingCollarWindowAdmissibleEDist r R z w := by
    unfold gluingCollarWindowAdmissibleEDist gluingCollarAdmissibleEDist
    refine le_iInf fun α => le_iInf fun h0 => le_iInf fun h1 =>
      le_iInf fun hLip => le_iInf fun hWindow => ?_
    obtain ⟨K, hK⟩ := hLip
    exact gluingCollarAdmissibleEDist_le_warp_length r h0 h1 hK
  have hwindow_le_global :
      gluingCollarWindowAdmissibleEDist r R z w ≤
        gluingCollarAdmissibleEDist r z w := by
    unfold gluingCollarWindowAdmissibleEDist gluingCollarAdmissibleEDist
    refine le_iInf fun α => le_iInf fun h0 => le_iInf fun h1 =>
      le_iInf fun hLip => ?_
    obtain ⟨K, hK⟩ := hLip
    let β : ℝ → ℂ := fun t => gluingCollarClamp R (α t)
    have hβ : LipschitzOnWith K β (Icc 0 1) := by
      simpa only [β, Function.comp_def, one_mul] using
        (gluingCollarClamp_lipschitz R).comp_lipschitzOnWith hK
    have hβ0 : β 0 = z := by
      dsimp [β]
      rw [h0]
      exact gluingCollarClamp_eq_self_of_re_mem hz
    have hβ1 : β 1 = w := by
      dsimp [β]
      rw [h1]
      exact gluingCollarClamp_eq_self_of_re_mem hw
    have hβwindow : ∀ t ∈ Icc (0 : ℝ) 1, (β t).re ∈ Icc (-R) R := by
      intro t ht
      change gluingCollarClampReal R (α t).re ∈ Icc (-R) R
      simp only [gluingCollarClampReal, mem_Icc]
      constructor
      · exact le_max_left _ _
      · apply max_le
        · linarith
        · exact min_le_left _ _
    have hspeed : (fun t => Real.sqrt
        (gluingComplexCollarTangentForm r (β t) (deriv β t) (deriv β t))) ≤ᵐ[
          volume.restrict (Icc 0 1)] (fun t => Real.sqrt
        (gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t))) := by
      filter_upwards [gluingCollarClamp_speed_le_ae hr hR hK] with t ht
      simpa only [β] using ht
    have hlength : (∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
        (Real.sqrt (gluingComplexCollarTangentForm r (β t) (deriv β t) (deriv β t)))) ≤
        ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
          (Real.sqrt (gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t))) := by
      apply lintegral_mono_ae
      filter_upwards [hspeed] with t ht
      exact ENNReal.ofReal_le_ofReal ht
    calc
      _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
          (Real.sqrt (gluingComplexCollarTangentForm r (β t) (deriv β t) (deriv β t))) := by
        exact iInf_le_of_le β (iInf_le_of_le hβ0 (iInf_le_of_le hβ1
          (iInf_le_of_le (show ∃ K' : ℝ≥0, LipschitzOnWith K' β (Icc 0 1)
              from ⟨K, hβ⟩)
            (iInf_le_of_le hβwindow le_rfl))))
      _ ≤ _ := hlength
  apply le_antisymm
  · calc
      gluingCollarWindowAdmissibleEDist r R z w ≤ gluingCollarAdmissibleEDist r z w :=
        hwindow_le_global
      _ = gluingCollarModelEDist hr z w := gluingCollarAdmissibleEDist_eq_native hr z w
  · rw [← gluingCollarAdmissibleEDist_eq_native hr z w]
    exact hglobal_le_window

/-- Any two points in a bounded radial window can be joined by a genuine
constant-speed geodesic that stays in the window. -/
theorem gluingCollarModelMetric_exists_window_geodesic {r R : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R) {x y : ℂ}
    (hx : x.re ∈ Icc (-R) R) (hy : y.re ∈ Icc (-R) R) :
    letI := gluingCollarModelMetricSpace hr
    letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
    letI := (gluingCollarModelMetricSpace hr).toUniformSpace
    ∃ γ : Path x y, (∀ s t : unitInterval,
      dist (γ s) (γ t) = dist x y * |(s : ℝ) - (t : ℝ)|) ∧
      ∀ s : unitInterval, (γ s).re ∈ Icc (-R) R := by
  letI := gluingCollarModelMetricSpace hr
  letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
  letI := (gluingCollarModelMetricSpace hr).toUniformSpace
  obtain ⟨α, hα⟩ := gluingCollarModelMetric_exists_metric_path hr x y
  let β : unitInterval → ℂ := fun s => gluingCollarClamp R (α s)
  have hβcont : Continuous β := by
    exact (gluingCollarClamp_continuous R).comp α.continuous
  have hβ0 : β 0 = x := by
    dsimp [β]
    rw [α.source]
    exact gluingCollarClamp_eq_self_of_re_mem hx
  have hβ1 : β 1 = y := by
    dsimp [β]
    rw [α.target]
    exact gluingCollarClamp_eq_self_of_re_mem hy
  have hzero : ((0 : unitInterval) : ℝ) = 0 := rfl
  have hone : ((1 : unitInterval) : ℝ) = 1 := rfl
  let γ : Path x y := ⟨⟨β, hβcont⟩, hβ0, hβ1⟩
  have hdist (z w : ℂ) : dist z w = (gluingCollarModelEDist hr z w).toReal := by
    change (edist z w).toReal = (gluingCollarModelEDist hr z w).toReal
    rw [gluingCollarModelMetricSpace_edist hr z w]
  have hcontract (s t : unitInterval) :
      dist (β s) (β t) ≤ dist (α s) (α t) := by
    have h := gluingCollarClamp_nativeEDist_le hr hR (α s) (α t)
    have hreal := ENNReal.toReal_mono
      (gluingCollarModelEDist_lt_top hr (α s) (α t)).ne h
    calc
      dist (β s) (β t) = (gluingCollarModelEDist hr (β s) (β t)).toReal := hdist _ _
      _ ≤ (gluingCollarModelEDist hr (α s) (α t)).toReal := hreal
      _ = dist (α s) (α t) := (hdist _ _).symm
  have hleft (s : unitInterval) : dist x (γ s) ≤ dist x y * (s : ℝ) := by
    calc
      dist x (γ s) = dist (β 0) (β s) := by change dist x (β s) = _; rw [← hβ0]
      _ ≤ dist (α 0) (α s) := hcontract 0 s
      _ = dist x y * (s : ℝ) := by
        rw [α.source]
        have hs := hα 0 s
        rw [α.source] at hs
        rw [hzero, zero_sub, abs_neg, abs_of_nonneg s.property.1] at hs
        exact hs
  have hright (s : unitInterval) :
      dist (γ s) y ≤ dist x y * (1 - (s : ℝ)) := by
    calc
      dist (γ s) y = dist (β s) (β 1) := by change dist (β s) y = _; rw [← hβ1]
      _ ≤ dist (α s) (α 1) := hcontract s 1
      _ = dist x y * (1 - (s : ℝ)) := by
        rw [α.target]
        have hs := hα s 1
        rw [α.target] at hs
        rw [hone, abs_of_nonpos (sub_nonpos.mpr s.property.2)] at hs
        nlinarith
  have hleft_eq (s : unitInterval) : dist x (γ s) = dist x y * (s : ℝ) := by
    have htri := dist_triangle x (γ s) y
    have hD : dist x y ≤ dist x (γ s) + dist (γ s) y := htri
    have hsum : dist x (γ s) + dist (γ s) y ≤ dist x y := by
      calc
        _ ≤ dist x y * (s : ℝ) + dist x y * (1 - (s : ℝ)) :=
          add_le_add (hleft s) (hright s)
        _ = dist x y := by ring
    have hreverse : dist x y * (s : ℝ) ≤ dist x (γ s) := by
      nlinarith [hD, hright s]
    exact le_antisymm (hleft s) hreverse
  have hdist (s t : unitInterval) :
      dist (γ s) (γ t) = dist x y * |(s : ℝ) - (t : ℝ)| := by
    have hupper : dist (γ s) (γ t) ≤ dist x y * |(s : ℝ) - (t : ℝ)| := by
      calc
        dist (γ s) (γ t) = dist (β s) (β t) := rfl
        _ ≤ dist (α s) (α t) := hcontract s t
        _ = _ := hα s t
    have hlower : dist x y * |(s : ℝ) - (t : ℝ)| ≤ dist (γ s) (γ t) := by
      by_cases hst : (s : ℝ) ≤ t
      · have htri := dist_triangle x (γ s) (γ t)
        rw [hleft_eq t, hleft_eq s] at htri
        rw [abs_of_nonpos (sub_nonpos.mpr hst)]
        nlinarith
      · have hts : (t : ℝ) ≤ s := le_of_not_ge hst
        have htri := dist_triangle x (γ t) (γ s)
        rw [hleft_eq s, hleft_eq t] at htri
        rw [dist_comm (γ t) (γ s)] at htri
        rw [abs_of_nonneg (sub_nonneg.mpr hts)]
        nlinarith
    exact le_antisymm hupper hlower
  refine ⟨γ, hdist, ?_⟩
  intro s
  change (gluingCollarClamp R (α s)).re ∈ Icc (-R) R
  simp only [gluingCollarClamp, gluingCollarClampReal, mem_Icc]
  constructor
  · exact le_max_left _ _
  · apply max_le
    · linarith
    · exact min_le_left _ _

#print axioms gluingCollarWindowAdmissibleEDist_eq_native
#print axioms gluingCollarModelMetric_exists_window_geodesic

end SystolicGrowth
