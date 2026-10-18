module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.MetricLoopCompactness
public import Geometry.GluingLoopNullhomotopyOpenness
public import Geometry.GluingShortLoopNullhomotopy
public import Mathlib.Topology.Semicontinuity.Basic

@[expose] public section

/-!
# Compact essential-loop families on the actual glued carrier

Nullhomotopy is open even with moving basepoints, so essential loops form a
closed subset of the compact common-Lipschitz family. Lower semicontinuity
of native variation then constructs a minimizing essential loop in that
family. This is not yet unrestricted minimization or a local-geodesic
parameterization: those still require arclength normalization and shortening.
-/

open Set
open scoped Topology unitInterval NNReal ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Essential native loops with a fixed Lipschitz bound form a compact
family, without fixing their basepoints or assuming limit stability. -/
theorem gluedIntrinsicMetric_isCompact_essential_lipschitz_closedLoopMapSet
    (P : ExerciseGluingPreparation C g n genera X) (K : ℝ≥0) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    IsCompact {f : closedLoopMapSet P.GluedCarrier |
      LipschitzWith K f.1 ∧ ¬(closedLoopPath f).Homotopic (Path.refl (f.1 0))} := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  letI : CompactSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace_compact
  let S : Set (closedLoopMapSet P.GluedCarrier) := {f | LipschitzWith K f.1}
  have himage : Subtype.val '' S = metricClosedLipschitzLoopSet P.GluedCarrier K := by
    ext f
    constructor
    · rintro ⟨F, hF, rfl⟩
      exact ⟨F.2, hF⟩
    · rintro ⟨hclosed, hlip⟩
      exact ⟨⟨f, hclosed⟩, hlip, rfl⟩
  have hS : IsCompact S := Subtype.isCompact_iff.mpr (by
    rw [himage]
    exact isCompact_metricClosedLipschitzLoopSet P.GluedCarrier K)
  have hessential : IsClosed {f : closedLoopMapSet P.GluedCarrier |
      ¬(closedLoopPath f).Homotopic (Path.refl (f.1 0))} :=
    P.gluedIntrinsicMetric_isOpen_nullhomotopic_closedLoopMapSet.isClosed_compl
  exact hS.inter_right hessential

/-- Every nonempty common-Lipschitz essential-loop family has an actual
positive finite variation minimizer. The comparison family permits all
native basepoints. -/
theorem exists_minimizing_essential_lipschitz_loop
    (P : ExerciseGluingPreparation C g n genera X) (K : ℝ≥0)
    (f₀ : closedLoopMapSet P.GluedCarrier)
    (hLip : letI := P.gluedCarrierIntrinsicMetricSpace; LipschitzWith K f₀.1)
    (hessential : ¬(closedLoopPath f₀).Homotopic (Path.refl (f₀.1 0))) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ f : closedLoopMapSet P.GluedCarrier,
      LipschitzWith K f.1 ∧ ¬(closedLoopPath f).Homotopic (Path.refl (f.1 0)) ∧
      0 < eVariationOn f.1 univ ∧ eVariationOn f.1 univ ≤ (K : ℝ≥0∞) ∧
      ∀ h : closedLoopMapSet P.GluedCarrier, LipschitzWith K h.1 →
        ¬(closedLoopPath h).Homotopic (Path.refl (h.1 0)) →
        eVariationOn f.1 univ ≤ eVariationOn h.1 univ := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  let S : Set (closedLoopMapSet P.GluedCarrier) := {f |
    LipschitzWith K f.1 ∧ ¬(closedLoopPath f).Homotopic (Path.refl (f.1 0))}
  have hS : IsCompact S :=
    P.gluedIntrinsicMetric_isCompact_essential_lipschitz_closedLoopMapSet K
  have hne : S.Nonempty := ⟨f₀, hLip, hessential⟩
  have hvariation : LowerSemicontinuous
      (fun f : closedLoopMapSet P.GluedCarrier => eVariationOn f.1 univ) :=
    (lowerSemicontinuous_eVariationOn_continuousMap univ).comp continuous_subtype_val
  obtain ⟨f, hf, hmin⟩ := (hvariation.lowerSemicontinuousOn S).exists_isMinOn hne hS
  obtain ⟨r, hr, hnull⟩ := P.exists_nullhomotopy_radius
  have hrle : ENNReal.ofReal r ≤ eVariationOn f.1 univ := by
    apply le_of_not_gt
    intro hsmall
    exact hf.2 (hnull (f.1 0) (closedLoopPath f) hsmall)
  refine ⟨f, hf.1, hf.2, (ENNReal.ofReal_pos.mpr hr).trans_le hrle,
    eVariationOn_unitInterval_le_of_lipschitz f.1 hf.1, ?_⟩
  exact fun h hL hE => (isMinOn_iff.mp hmin) h ⟨hL, hE⟩

end SystolicGrowth.ExerciseGluingPreparation
