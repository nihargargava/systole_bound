module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceDeckCovering
public import Geometry.SurfaceOrbitBallLift
public import Geometry.HyperbolicLocalGeodesicConvexity
public import Geometry.GluingExcursionLength
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Algebra.Module.LocallyConvex

@[expose] public section

/-!
# Systolic payment by actual closed local metric segments

A continuous positive-speed local metric segment lifts through the original
orbit covering. Hyperbolic cosh convexity rules out a closed upstairs lift,
so its endpoints differ by a nonidentity original deck transformation. Local
metric identification preserves the full variation and pays its displacement.
-/

open Set Metric
open scoped UpperHalfPlane ENNReal Topology

namespace SystolicGrowth.ClosedHyperbolicSurface

/-- Every continuous closed positive-speed local metric segment in the
actual surface quotient pays at least its systole in metric variation.
Essentiality is derived from local geodesicity, not assumed. -/
theorem systole_le_variation_of_closed_locally_metric_segment
    {g : ℕ} (X : ClosedHyperbolicSurface g) {a b speed : ℝ}
    (hab : a < b) (hs : 0 < speed)
    (β : Icc a b → X.Carrier) (hβ : Continuous β)
    (hclosed : β ⟨a, le_rfl, hab.le⟩ = β ⟨b, hab.le, le_rfl⟩)
    (hlocal : ∀ t : Icc a b, a < t.1 → t.1 < b →
      ∃ η > 0, ∀ u v : Icc a b, dist u t < η → dist v t < η →
        dist (β u) (β v) = speed * |(u : ℝ) - (v : ℝ)|) :
    ENNReal.ofReal X.systole ≤ eVariationOn β univ := by
  by_cases hsys : 0 < X.systole
  · letI : ContractibleSpace (Icc a b) :=
      (convex_Icc a b).contractibleSpace ⟨a, le_rfl, hab.le⟩
    letI : LocallyPathConnectedSpace (Icc a b) :=
      (convex_Icc a b).locallyPathConnectedSpace
    let t₀ : Icc a b := ⟨a, le_rfl, hab.le⟩
    let t₁ : Icc a b := ⟨b, hab.le, le_rfl⟩
    obtain ⟨o, ho⟩ := Quotient.mk_surjective (β t₀)
    obtain ⟨σ, hσ, _⟩ := X.orbitProjection_isCoveringMap.existsUnique_continuousMap_lifts
      ⟨β, hβ⟩ t₀ o ho
    have hlift : ∀ t, (Quotient.mk'' (σ t) : X.Carrier) = β t :=
      fun t => congrFun hσ.2 t
    have hmetric (t : Icc a b) : ∃ η > 0, ∀ u v : Icc a b,
        dist u t < η → dist v t < η → dist (σ u) (σ v) = dist (β u) (β v) :=
      X.continuous_lift_locally_dist_eq hsys σ σ.continuous β hlift t
    have hσlocal : ∀ t : Icc a b, a < t.1 → t.1 < b →
        ∃ η > 0, ∀ u v : Icc a b, dist u t < η → dist v t < η →
          dist (σ u) (σ v) = speed * |(u : ℝ) - (v : ℝ)| := by
      intro t hta htb
      obtain ⟨η₁, hη₁, hm₁⟩ := hlocal t hta htb
      obtain ⟨η₂, hη₂, hm₂⟩ := hmetric t
      refine ⟨min η₁ η₂, lt_min hη₁ hη₂, ?_⟩
      intro u v hu hv
      rw [hm₂ u v (hu.trans_le (min_le_right _ _))
        (hv.trans_le (min_le_right _ _))]
      exact hm₁ u v (hu.trans_le (min_le_left _ _))
        (hv.trans_le (min_le_left _ _))
    have hdistinct : σ t₀ ≠ σ t₁ := by
      intro heq
      have hc := hyperbolic_locally_metric_segment_midpoint_cosh_le
        hab hs σ σ.continuous hσlocal (σ t₀)
      change 2 * Real.cosh (speed * (b - a) / 2) *
          Real.cosh (dist (σ t₀) (σ ⟨(a + b) / 2, by constructor <;> linarith⟩)) ≤
        Real.cosh (dist (σ t₀) (σ t₀)) + Real.cosh (dist (σ t₀) (σ t₁)) at hc
      rw [← heq, dist_self, Real.cosh_zero] at hc
      have hD : 0 < speed * (b - a) / 2 := by positivity
      have hcosh : 1 < Real.cosh (speed * (b - a) / 2) := Real.one_lt_cosh.mpr hD.ne'
      have hmid := Real.one_le_cosh
        (dist (σ t₀) (σ ⟨(a + b) / 2, by constructor <;> linarith⟩))
      nlinarith
    have hquot : (Quotient.mk'' (σ t₁) : X.Carrier) = Quotient.mk'' (σ t₀) := by
      rw [hlift t₁, hlift t₀]
      exact hclosed.symm
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp
      (MulAction.orbitRel_apply.mp (Quotient.exact hquot))
    have hγne : γ ≠ 1 := by
      intro hγone
      apply hdistinct
      simpa only [hγone, one_smul] using hγ
    have hsysdist : X.systole ≤ dist (σ t₀) (σ t₁) := by
      simpa only [hγ] using X.systole_le_displacement γ hγne (σ t₀)
    have hvariation : eVariationOn σ univ = eVariationOn β univ := by
      apply eVariationOn_Icc_subtype_eq_of_interior_locally_edist_eq
        hab σ β σ.continuous hβ
      intro t _ _
      obtain ⟨η, hη, hm⟩ := hmetric t
      refine ⟨η, hη, ?_⟩
      intro u v hu hv
      rw [edist_dist, edist_dist, hm u v hu hv]
    calc
      ENNReal.ofReal X.systole ≤ edist (σ t₀) (σ t₁) := by
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal hsysdist
      _ ≤ eVariationOn σ univ := eVariationOn.edist_le σ (mem_univ t₀) (mem_univ t₁)
      _ = eVariationOn β univ := hvariation
  · rw [ENNReal.ofReal_eq_zero.mpr (not_lt.mp hsys)]
    exact bot_le

#print axioms systole_le_variation_of_closed_locally_metric_segment

end SystolicGrowth.ClosedHyperbolicSurface
