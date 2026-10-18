module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingInteriorDistance
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.UnitInterval

@[expose] public section

/-!
# Metric variation of actual seam-avoiding excursions

Local equality of the two native metrics preserves metric variation. Compact
interval subdivision is used only for the parameter cover, not for the seam
contact set; continuous seam endpoints do not contribute jumps.
-/

open Set Filter UpperHalfPlane
open scoped ENNReal Topology

namespace SystolicGrowth

private theorem eVariationOn_eq_of_edist_eq
    {α E F : Type*} [LinearOrder α] [PseudoEMetricSpace E] [PseudoEMetricSpace F]
    (f : α → E) (g : α → F) (s : Set α)
    (h : ∀ u ∈ s, ∀ v ∈ s, edist (f u) (f v) = edist (g u) (g v)) :
    eVariationOn f s = eVariationOn g s := by
  unfold eVariationOn
  congr 1
  funext p
  rcases p with ⟨m, u, hu, hus⟩
  exact Finset.sum_congr rfl (fun j _ => h _ (hus _) _ (hus _))

/-- Compact parameter subdivision upgrades local metric equality to equality
of variation on a closed real interval. No bounded-variation premise is used. -/
theorem eVariationOn_Icc_eq_of_locally_edist_eq
    {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]
    (f : ℝ → E) (g : ℝ → F) {a b : ℝ} (hab : a ≤ b)
    (hlocal : ∀ t ∈ Icc a b, ∃ η > 0,
      ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, dist u t < η → dist v t < η →
        edist (f u) (f v) = edist (g u) (g v)) :
    eVariationOn f (Icc a b) = eVariationOn g (Icc a b) := by
  classical
  choose η hη hmetric using (fun t : Icc a b => hlocal t t.2)
  let c : Icc a b → Set (Icc a b) := fun t => Metric.ball t (η t)
  obtain ⟨u, hu0, humono, ⟨m, hm⟩, hcover⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hab
      (c := c) (fun _ => Metric.isOpen_ball) (by
        intro t _
        exact mem_iUnion.mpr ⟨t, Metric.mem_ball.mpr (by simpa using hη t)⟩)
  let f' : Icc a b → E := fun t => f t
  let g' : Icc a b → F := fun t => g t
  have hsegment (j : ℕ) :
      eVariationOn f' (Icc (u j) (u (j + 1))) =
        eVariationOn g' (Icc (u j) (u (j + 1))) := by
    obtain ⟨t, ht⟩ := hcover j
    apply eVariationOn_eq_of_edist_eq
    intro x hx y hy
    exact hmetric t x x.2 y y.2 (Metric.mem_ball.mp (ht hx))
      (Metric.mem_ball.mp (ht hy))
  have hwhole : Icc (u 0) (u m) = (univ : Set (Icc a b)) := by
    ext t
    simp only [mem_Icc, mem_univ, iff_true]
    constructor
    · change (u 0 : ℝ) ≤ (t : ℝ)
      rw [hu0]
      exact t.2.1
    · change (t : ℝ) ≤ (u m : ℝ)
      rw [hm m le_rfl]
      exact t.2.2
  have heq : eVariationOn f' univ = eVariationOn g' univ := by
    rw [← hwhole, ← eVariationOn.sum' f' humono, ← eVariationOn.sum' g' humono]
    exact Finset.sum_congr rfl (fun j _ => hsegment j)
  have hcomp (k : ℝ → E) :
      eVariationOn (fun t : Icc a b => k t) univ = eVariationOn k (Icc a b) := by
    simpa only [Function.comp_def, image_univ, Subtype.range_coe_subtype, setOf_mem_eq] using
      eVariationOn.comp_eq_of_monotoneOn k
        (t := univ) (fun t : Icc a b => (t : ℝ)) (fun _ _ _ _ h => h)
  have hcomp' : eVariationOn g' univ = eVariationOn g (Icc a b) := by
    simpa only [g', Function.comp_def, image_univ, Subtype.range_coe_subtype, setOf_mem_eq] using
      eVariationOn.comp_eq_of_monotoneOn g
        (t := univ) (fun t : Icc a b => (t : ℝ)) (fun _ _ _ _ h => h)
  exact (hcomp f).symm.trans (heq.trans hcomp')

#print axioms eVariationOn_Icc_eq_of_locally_edist_eq

private theorem eVariationOn_Ioo_eq_Icc_of_continuousOn
    {E : Type*} [PseudoEMetricSpace E] (f : ℝ → E) {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) :
    eVariationOn f (Ioo a b) = eVariationOn f (Icc a b) := by
  have hleft : (𝓝[Iic b ∩ Ioi a] a).NeBot := by
    rw [nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hab))]
    infer_instance
  have hright : (𝓝[Ioi a ∩ Iio b] b).NeBot := by
    rw [nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hab))]
    infer_instance
  have h₁ := eVariationOn.eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt
    (f := f) hleft (by
      rw [Iic_inter_Ici]
      exact hf a ⟨le_rfl, hab.le⟩)
  have h₂ := eVariationOn.eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt
    (f := f) hright ((hf b ⟨hab.le, le_rfl⟩).mono (by
      intro x hx
      exact ⟨hx.1.le, hx.2⟩))
  simp only [Ioi_inter_Iio, Ioi_inter_Iic, Iic_inter_Ioi, Iic_inter_Ici] at h₁ h₂
  exact h₂.trans h₁

/-- Continuous endpoints can be retained when local comparison is known only
on the open excursion. The variation may be infinite on either side. -/
theorem eVariationOn_Icc_eq_of_interior_locally_edist_eq
    {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]
    (f : ℝ → E) (g : ℝ → F) {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hlocal : ∀ t ∈ Ioo a b, ∃ η > 0,
      ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, dist u t < η → dist v t < η →
        edist (f u) (f v) = edist (g u) (g v)) :
    eVariationOn f (Icc a b) = eVariationOn g (Icc a b) := by
  rw [← eVariationOn_Ioo_eq_Icc_of_continuousOn f hab hf,
    ← eVariationOn_Ioo_eq_Icc_of_continuousOn g hab hg]
  rw [eVariationOn.eq_biSup_inter_Icc, eVariationOn.eq_biSup_inter_Icc]
  congr 1
  funext p
  congr 1
  funext hp
  have hsub : Icc p.1 p.2 ⊆ Ioo a b :=
    fun _ ht => ⟨hp.1.1.trans_le ht.1, ht.2.trans_lt hp.2.1.2⟩
  rw [inter_eq_right.mpr hsub]
  exact eVariationOn_Icc_eq_of_locally_edist_eq f g hp.2.2 (by
    intro t ht
    obtain ⟨η, hη, hm⟩ := hlocal t (hsub ht)
    refine ⟨η, hη, fun u hu v hv => hm u ⟨(hsub hu).1.le, (hsub hu).2.le⟩
      v ⟨(hsub hv).1.le, (hsub hv).2.le⟩⟩)

#print axioms eVariationOn_Icc_eq_of_interior_locally_edist_eq

/-- Continuous curves on a closed interval subtype have equal variation
when their native distances agree locally at every interior parameter.
Clamped continuous extensions retain the original endpoint values. -/
theorem eVariationOn_Icc_subtype_eq_of_interior_locally_edist_eq
    {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]
    {a b : ℝ} (hab : a < b) (f : Icc a b → E) (g : Icc a b → F)
    (hf : Continuous f) (hg : Continuous g)
    (hlocal : ∀ t : Icc a b, a < t.1 → t.1 < b → ∃ η > 0,
      ∀ u v : Icc a b, dist u t < η → dist v t < η →
        edist (f u) (f v) = edist (g u) (g v)) :
    eVariationOn f univ = eVariationOn g univ := by
  let f' : ℝ → E := f ∘ projIcc a b hab.le
  let g' : ℝ → F := g ∘ projIcc a b hab.le
  have hf' : Continuous f' := hf.comp continuous_projIcc
  have hg' : Continuous g' := hg.comp continuous_projIcc
  have hlocal' : ∀ t ∈ Ioo a b, ∃ η > 0,
      ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, dist u t < η → dist v t < η →
        edist (f' u) (f' v) = edist (g' u) (g' v) := by
    intro t ht
    obtain ⟨η, hη, hmetric⟩ := hlocal ⟨t, ht.1.le, ht.2.le⟩ ht.1 ht.2
    refine ⟨η, hη, ?_⟩
    intro u hu v hv hut hvt
    simpa only [f', g', Function.comp_def, projIcc_of_mem hab.le hu,
      projIcc_of_mem hab.le hv] using hmetric ⟨u, hu⟩ ⟨v, hv⟩ hut hvt
  have heq := eVariationOn_Icc_eq_of_interior_locally_edist_eq
    f' g' hab hf'.continuousOn hg'.continuousOn hlocal'
  have hcompf : eVariationOn f univ = eVariationOn f' (Icc a b) := by
    simpa only [f', Function.comp_def, projIcc_val, image_univ,
      Subtype.range_coe_subtype, setOf_mem_eq] using
      eVariationOn.comp_eq_of_monotoneOn f'
        (t := univ) (fun t : Icc a b => (t : ℝ)) (fun _ _ _ _ h => h)
  have hcompg : eVariationOn g univ = eVariationOn g' (Icc a b) := by
    simpa only [g', Function.comp_def, projIcc_val, image_univ,
      Subtype.range_coe_subtype, setOf_mem_eq] using
      eVariationOn.comp_eq_of_monotoneOn g'
        (t := univ) (fun t : Icc a b => (t : ℝ)) (fun _ _ _ _ h => h)
  exact hcompf.trans (heq.trans hcompg.symm)

#print axioms eVariationOn_Icc_subtype_eq_of_interior_locally_edist_eq

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Full deck-orbit center separation bounds the actual native component
distance between the two puncture circles, not only selected lift distances. -/
theorem gluingDepth_le_dist_of_mem_punctureCircles
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {x y : (X i).Carrier}
    (hx : x ∈ (X i).punctureCircle (P.centers i).1 (gluingRadius C g))
    (hy : y ∈ (X i).punctureCircle (P.centers i).2 (gluingRadius C g)) :
    gluingDepth C g ≤ dist x y := by
  obtain ⟨z, hz, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  rw [(X i).carrier_dist_eq_orbitDist, (X i).orbitDist_mk]
  obtain ⟨κ, hκ⟩ := (X i).exists_liftOrbitDist_eq_dist z w
  have hsep := P.separated i κ
  have htri := dist_triangle4 (P.centers i).1 z (κ • w) (κ • (P.centers i).2)
  have hzrad : dist (P.centers i).1 z = gluingRadius C g := by
    simpa only [Metric.mem_sphere, dist_comm] using hz
  have hwrad : dist (κ • w) (κ • (P.centers i).2) = gluingRadius C g := by
    rw [dist_smul]
    exact Metric.mem_sphere.mp hw
  rw [hzrad, hwrad, ← hκ] at htri
  dsimp only [gluingSeparationRadius] at hsep
  linarith

#print axioms gluingDepth_le_dist_of_mem_punctureCircles

/-- The whole closed seam-avoiding excursion lifts into one actual original
component with exactly the same metric variation. Every original-component
endpoint distance is therefore paid by the glued excursion, even when its
endpoints lie on seams or its metric variation is infinite. In particular,
an excursion between the two actual puncture circles pays `gluingDepth`. -/
theorem exists_variation_preserving_component_lift_of_excursion
    (P : ExerciseGluingPreparation C g n genera X) {a b : ℝ} (hab : a < b)
    (γ : ℝ → P.GluedCarrier) (hγ : ContinuousOn γ (Icc a b))
    (havoid : MapsTo γ (Ioo a b) P.gluedSeamSetᶜ) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ (i : Fin n) (δ : Icc a b → P.ChainComponent i),
      Continuous δ ∧ (∀ t : Icc a b, γ t = P.gluedMk ⟨i, δ t⟩) ∧
      eVariationOn (fun t : Icc a b => (δ t).1) univ = eVariationOn γ (Icc a b) ∧
      (∀ s t : Icc a b, edist (δ s).1 (δ t).1 ≤ eVariationOn γ (Icc a b)) ∧
      ∀ s t : Icc a b,
        (δ s).1 ∈ (X i).punctureCircle (P.centers i).1 (gluingRadius C g) →
        (δ t).1 ∈ (X i).punctureCircle (P.centers i).2 (gluingRadius C g) →
        ENNReal.ofReal (gluingDepth C g) ≤ eVariationOn γ (Icc a b) := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  obtain ⟨i, δ, hδ, hlift, hlocal⟩ :=
    P.exists_locally_isometric_component_lift_of_excursion hab γ hγ havoid
  let f : ℝ → (X i).Carrier := fun t => (δ (projIcc a b hab.le t)).1
  have hf : Continuous f :=
    (continuous_subtype_val.comp hδ).comp continuous_projIcc
  have hmetric : ∀ t ∈ Ioo a b, ∃ η > 0,
      ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, dist u t < η → dist v t < η →
        edist (f u) (f v) = edist (γ u) (γ v) := by
    intro t ht
    let t' : Icc a b := ⟨t, ht.1.le, ht.2.le⟩
    obtain ⟨η, hη, hm⟩ := hlocal t' ht.1 ht.2
    refine ⟨η, hη, ?_⟩
    intro u hu v hv hut hvt
    have heq := hm ⟨u, hu⟩ ⟨v, hv⟩ hut hvt
    simpa only [f, projIcc_of_mem hab.le hu, projIcc_of_mem hab.le hv, edist_dist] using
      congrArg ENNReal.ofReal heq
  have heq := eVariationOn_Icc_eq_of_interior_locally_edist_eq
    f γ hab hf.continuousOn hγ hmetric
  have hcomp : eVariationOn (fun t : Icc a b => (δ t).1) univ =
      eVariationOn f (Icc a b) := by
    simpa only [f, Function.comp_def, projIcc_val, image_univ,
      Subtype.range_coe_subtype, setOf_mem_eq] using
      eVariationOn.comp_eq_of_monotoneOn f (t := univ)
        (fun t : Icc a b => (t : ℝ)) (fun _ _ _ _ h => h)
  have hvar := hcomp.trans heq
  have hbound (s t : Icc a b) : edist (δ s).1 (δ t).1 ≤ eVariationOn γ (Icc a b) := by
    rw [← hvar]
    exact eVariationOn.edist_le (fun t : Icc a b => (δ t).1) (mem_univ s) (mem_univ t)
  refine ⟨i, δ, hδ, hlift, hvar, hbound, ?_⟩
  intro s t hs ht
  calc
    ENNReal.ofReal (gluingDepth C g) ≤ edist (δ s).1 (δ t).1 := by
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (P.gluingDepth_le_dist_of_mem_punctureCircles i hs ht)
    _ ≤ eVariationOn γ (Icc a b) := hbound s t

#print axioms exists_variation_preserving_component_lift_of_excursion

end ExerciseGluingPreparation

end SystolicGrowth
