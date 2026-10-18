module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.HyperbolicLocalGeodesicConvexity
public import Geometry.SurfaceOrbitBallLift
public import Geometry.GluingExcursionLocalGeodesic
public import Geometry.GluingOuterExcursionCost
public import Geometry.GluingExcursionCost

@[expose] public section

/-!
# Costs of returning local-geodesic excursions

A positive-speed local metric segment returning to a genuinely deleted
puncture circle cannot remain in its embedded outer orbit ball. The actual
continuous lift has global cosh comparison from its local metric law; its
midpoint would enter the deleted disk. Thus both radial legs pay the full
target systole. Actual seam incidence supplies the endpoint circle.
-/

open Set Metric
open scoped UpperHalfPlane ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- A returning positive-speed local metric segment in an actual retained
component must leave the corresponding embedded outer ball. The center is
one of its genuinely deleted disks, not an arbitrary undeleted circle. -/
theorem component_locally_metric_segment_not_confined
    (P : ExerciseGluingPreparation C g n genera X) {a b speed : ℝ}
    (hab : a < b) (hs : 0 < speed) (i : Fin n)
    (δ : Icc a b → P.ChainComponent i) (hδ : Continuous δ)
    (hlocal : ∀ t : Icc a b, a < t.1 → t.1 < b → ∃ η > 0,
      ∀ u v : Icc a b, dist u t < η → dist v t < η →
        dist (δ u).1 (δ v).1 = speed * |(u : ℝ) - (v : ℝ)|)
    (o : ℍ)
    (hcenter : (0 < i.1 ∧ o = (P.centers i).1) ∨
      (i.1 + 1 < n ∧ o = (P.centers i).2))
    (ha : (δ ⟨a, le_rfl, hab.le⟩).1 ∈
      (X i).punctureCircle o (gluingRadius C g))
    (hb : (δ ⟨b, hab.le, le_rfl⟩).1 ∈
      (X i).punctureCircle o (gluingRadius C g)) :
    ∃ t : Icc a b, (δ t).1 ∉ (X i).orbitBall o (gluingEmbeddedRadius C g) := by
  by_contra! hconfined
  let f : Icc a b → (X i).Carrier := fun t => (δ t).1
  have hf : Continuous f := continuous_subtype_val.comp hδ
  obtain ⟨σ, hσ, hlift, _hball, hradial⟩ :=
    (X i).exists_continuous_lift_into_orbitBall o (gluingEmbeddedRadius C g)
      (P.twice_outer_lt_systole i) f hf hconfined
  have hsys : 0 < (X i).systole := P.target_pos.trans_le (P.component_systole i)
  have hσlocal : ∀ t : Icc a b, a < t.1 → t.1 < b → ∃ η > 0,
      ∀ u v : Icc a b, dist u t < η → dist v t < η →
        dist (σ u) (σ v) = speed * |(u : ℝ) - (v : ℝ)| := by
    intro t hta htb
    obtain ⟨η₁, hη₁, hmetric⟩ :=
      (X i).continuous_lift_locally_dist_eq hsys σ hσ f hlift t
    obtain ⟨η₂, hη₂, hspeed⟩ := hlocal t hta htb
    refine ⟨min η₁ η₂, lt_min hη₁ hη₂, ?_⟩
    intro u v hu hv
    exact (hmetric u v (hu.trans_le (min_le_left _ _))
      (hv.trans_le (min_le_left _ _))).trans
      (hspeed u v (hu.trans_le (min_le_right _ _)) (hv.trans_le (min_le_right _ _)))
  let s : Icc a b := ⟨a, le_rfl, hab.le⟩
  let u : Icc a b := ⟨b, hab.le, le_rfl⟩
  let t : Icc a b := ⟨(a + b) / 2, by constructor <;> linarith⟩
  let c : (X i).Carrier := Quotient.mk'' o
  have hr : 2 * gluingRadius C g < (X i).systole := by
    linarith [P.radius_lt_embeddedRadius, P.twice_outer_lt_systole i]
  have hcircle (q : (X i).Carrier)
      (hq : q ∈ (X i).punctureCircle o (gluingRadius C g)) :
      dist c q = gluingRadius C g := by
    rw [ClosedHyperbolicSurface.punctureCircle,
      (X i).image_quotientMk_sphere_eq_carrier_sphere o (gluingRadius C g) hr] at hq
    simpa only [mem_sphere, dist_comm] using hq
  have hsa : dist o (σ s) = gluingRadius C g := (hradial s).symm.trans (hcircle (f s) ha)
  have hub : dist o (σ u) = gluingRadius C g := (hradial u).symm.trans (hcircle (f u) hb)
  have hkeep (v : Icc a b) : f v ∉ (X i).orbitBall o (gluingRadius C g) := by
    have hnot : f v ∉ (X i).punctureDeletedSet (P.centers i).1 (P.centers i).2
        (gluingRadius C g) i := (δ v).2
    rcases hcenter with ⟨hi, rfl⟩ | ⟨hi, rfl⟩
    · intro hv
      apply hnot
      unfold ClosedHyperbolicSurface.punctureDeletedSet
      exact Or.inl (by simpa only [if_pos hi] using hv)
    · intro hv
      apply hnot
      unfold ClosedHyperbolicSurface.punctureDeletedSet
      exact Or.inr (by simpa only [if_pos hi] using hv)
  have hrad : gluingRadius C g ≤ dist o (σ t) := by
    rw [← hradial t]
    apply le_of_not_gt
    intro hlt
    apply hkeep t
    rw [← (X i).carrier_ball_eq_orbitBall o (gluingRadius C g)]
    exact mem_ball.mpr (by simpa only [dist_comm] using hlt)
  have hcosh : Real.cosh (gluingRadius C g) ≤ Real.cosh (dist o (σ t)) := by
    apply Real.cosh_le_cosh.mpr
    simpa only [abs_of_nonneg P.radius_pos.le, abs_of_nonneg dist_nonneg] using hrad
  have hcomparison := hyperbolic_locally_metric_segment_midpoint_cosh_le hab hs σ hσ hσlocal o
  change 2 * Real.cosh (speed * (b - a) / 2) * Real.cosh (dist o (σ t)) ≤
    Real.cosh (dist o (σ s)) + Real.cosh (dist o (σ u)) at hcomparison
  rw [hsa, hub] at hcomparison
  have hfactor : 1 < Real.cosh (speed * (b - a) / 2) :=
    Real.one_lt_cosh.mpr (div_pos (mul_pos hs (sub_pos.mpr hab)) (by norm_num)).ne'
  have hstrict : Real.cosh (gluingRadius C g) <
      Real.cosh (speed * (b - a) / 2) * Real.cosh (gluingRadius C g) := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right hfactor (Real.cosh_pos _)
  have hbound := mul_le_mul_of_nonneg_left hcosh
    (show 0 ≤ 2 * Real.cosh (speed * (b - a) / 2) by positivity)
  nlinarith only [hstrict, hbound, hcomparison]

/-- Any positive-speed local-geodesic excursion returning to the same
actual seam pays the full target systole. The native component lift and its
deleted endpoint circle are determined internally from actual incidence. -/
theorem targetSystole_le_excursion_variation_of_same_seam
    (P : ExerciseGluingPreparation C g n genera X) {a b speed : ℝ}
    (hab : a < b) (hs : 0 < speed)
    (γ : ℝ → P.GluedCarrier) (hγ : ContinuousOn γ (Icc a b))
    (havoid : MapsTo γ (Ioo a b) P.gluedSeamSetᶜ)
    (hlocal :
      letI := P.gluedCarrierIntrinsicMetricSpace
      ∀ t : Icc a b, a < t.1 → t.1 < b → ∃ η > 0,
        ∀ u v : Icc a b, dist u t < η → dist v t < η →
          dist (γ u) (γ v) = speed * |(u : ℝ) - (v : ℝ)|)
    {k : Fin (n - 1)} (ha : γ a ∈ P.gluedSeamCircle k)
    (hb : γ b ∈ P.gluedSeamCircle k) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ENNReal.ofReal (targetSystole C g) ≤ eVariationOn γ (Icc a b) := by
  letI := P.gluedCarrierIntrinsicMetricSpace
  obtain ⟨i, δ, hδ, hlift, hvariation, hδlocal⟩ :=
    P.exists_locally_metric_segment_component_lift_of_excursion hab γ hγ havoid hlocal
  let s : Icc a b := ⟨a, le_rfl, hab.le⟩
  let t : Icc a b := ⟨b, hab.le, le_rfl⟩
  have hsseam : P.gluedMk ⟨i, δ s⟩ ∈ P.gluedSeamCircle k := by
    rw [← hlift s]
    exact ha
  have htseam : P.gluedMk ⟨i, δ t⟩ ∈ P.gluedSeamCircle k := by
    rw [← hlift t]
    exact hb
  have hleft (q : P.ChainComponent i) (hq : q ∈ range (P.leftCirclePoint i)) :
      q.1 ∈ (X i).punctureCircle (P.centers i).1 (gluingRadius C g) := by
    obtain ⟨z, rfl⟩ := hq
    exact ⟨z.1, z.2, rfl⟩
  have hright (q : P.ChainComponent i) (hq : q ∈ range (P.rightCirclePoint i)) :
      q.1 ∈ (X i).punctureCircle (P.centers i).2 (gluingRadius C g) := by
    obtain ⟨z, rfl⟩ := hq
    exact ⟨z.1, z.2, rfl⟩
  have hpay (o : ℍ)
      (hcenter : (0 < i.1 ∧ o = (P.centers i).1) ∨
        (i.1 + 1 < n ∧ o = (P.centers i).2))
      (hsa : (δ s).1 ∈ (X i).punctureCircle o (gluingRadius C g))
      (htb : (δ t).1 ∈ (X i).punctureCircle o (gluingRadius C g)) :
      ENNReal.ofReal (targetSystole C g) ≤ eVariationOn γ (Icc a b) := by
    have hout := P.component_locally_metric_segment_not_confined
      hab hs i δ hδ hδlocal o hcenter hsa htb
    exact (P.targetSystole_le_component_variation_of_outer_excursion
      hab i δ o hsa htb hout).trans_eq hvariation
  rcases P.component_mem_gluedSeamCircle_cases i (δ s) k hsseam with
    ⟨hik, hsk⟩ | ⟨hik, hsk⟩ <;>
    rcases P.component_mem_gluedSeamCircle_cases i (δ t) k htseam with
      ⟨hil, htk⟩ | ⟨hil, htk⟩
  · apply hpay (P.centers i).2 (Or.inr ⟨?_, rfl⟩) (hright _ hsk) (hright _ htk)
    have hi := congrArg Fin.val hik
    change i.1 = k.1 at hi
    have := k.2
    omega
  · have h := congrArg Fin.val (hik.symm.trans hil)
    change k.1 = k.1 + 1 at h
    omega
  · have h := congrArg Fin.val (hil.symm.trans hik)
    change k.1 = k.1 + 1 at h
    omega
  · apply hpay (P.centers i).1 (Or.inl ⟨?_, rfl⟩) (hleft _ hsk) (hleft _ htk)
    have hi := congrArg Fin.val hik
    change i.1 = k.1 + 1 at hi
    omega

#print axioms component_locally_metric_segment_not_confined
#print axioms targetSystole_le_excursion_variation_of_same_seam

end SystolicGrowth.ExerciseGluingPreparation
