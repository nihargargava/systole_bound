module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingSeamDistance
public import Geometry.GluingCollarSeamMetric
public import Geometry.GluingExcursionLength
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

/-!
# Continuous angular lifts of actual seam-confined curves

The actual cylinder homeomorphism supplies the angular Circle coordinate.
Mathlib lifts that coordinate through the genuine circle exponential on the
contractible parameter interval. The existing native seam chart metric gives
the local angular distance law and therefore exact metric variation.
-/

open Set Filter Metric
open scoped UpperHalfPlane ENNReal Topology

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

private theorem gluedSeamCircle_subset_cylinder_image
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedSeamCircle k ⊆ P.gluedMk '' P.seamNeighborhood k := by
  rintro q ⟨z, rfl⟩
  exact ⟨P.seamSource k z, P.seamSource_mem_seamNeighborhood k z, rfl⟩

private theorem cylinder_inverse_radial_eq_zero_of_mem_seam
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (q : P.GluedCarrier) (hq : q ∈ P.gluedSeamCircle k)
    (himage : q ∈ P.gluedMk '' P.seamNeighborhood k) :
    ((P.seamCylinderHomeomorph k).symm ⟨q, himage⟩).2.1 = 0 := by
  obtain ⟨z, rfl⟩ := hq
  let o := (P.centers (gluingChainEdgeLeft k)).2
  let r := gluingRadius C g
  have hrad : dist o z.1 = r := by
    simpa only [Metric.mem_sphere, dist_comm] using z.2
  let H := gluingPolarCollarHomeomorph o (r / 2) (r + 1) (by
    dsimp only [r]
    linarith [P.radius_pos])
  let z' : GluingPolarAnnulus o (r / 2) (r + 1) :=
    ⟨z.1, by rw [hrad]; constructor <;> dsimp only [r] <;> linarith [P.radius_pos]⟩
  let u := (H z').1
  have hpolar : gluingPolarPoint o u r = z.1 := by
    have h := congrArg Subtype.val (H.symm_apply_apply z')
    change gluingPolarPoint o (H z').1 (H z').2.1 = z.1 at h
    have hρ : (H z').2.1 = r := hrad
    rw [hρ] at h
    exact h
  let zero : Ioo (-gluingDepth C g) (gluingDepth C g) :=
    ⟨0, by constructor <;> linarith [P.depth_pos]⟩
  let θ := Complex.arg (u : ℂ)
  let p : GluingSeamAngularDomain C g θ :=
    (zero, ⟨θ, by constructor <;> linarith [Real.pi_pos]⟩)
  have hmap : (P.seamCylinderHomeomorph k (u, zero)).1 =
      P.gluedMk (P.seamSource k z) := by
    have h := P.seamAngularPoint_of_zero k θ p rfl
    change (P.seamCylinderHomeomorph k (Circle.exp θ, zero)).1 = _ at h
    dsimp only [p, θ] at h
    simp only [Circle.exp_arg] at h
    have hz : (⟨gluingPolarPoint (P.centers (gluingChainEdgeLeft k)).2 u (gluingRadius C g),
        by rw [Metric.mem_sphere, dist_comm, dist_gluingPolarPoint _ _ P.radius_pos.le]⟩ :
        Metric.sphere (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g)) = z :=
      Subtype.ext hpolar
    simpa only [hz] using h
  have hsub : P.seamCylinderHomeomorph k (u, zero) =
      ⟨P.gluedMk (P.seamSource k z), himage⟩ := Subtype.ext hmap
  change ((P.seamCylinderHomeomorph k).symm
    ⟨P.gluedMk (P.seamSource k z), himage⟩).2.1 = 0
  rw [← hsub, Homeomorph.symm_apply_apply]

/-- A continuous curve confined to an actual seam has a genuine real
angular lift. Native nearby distances and full variation have their exact
angular scale; equal curve values have equal circle exponentials. -/
theorem exists_continuous_seam_angular_lift
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    {a b : ℝ} (hab : a < b) (β : Icc a b → P.GluedCarrier) (hβ : Continuous β)
    (hseam : ∀ t, β t ∈ P.gluedSeamCircle k) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ α : Icc a b → ℝ, Continuous α ∧
      (∀ t : Icc a b, a < t.1 → t.1 < b → ∃ η > 0, ∀ u v : Icc a b,
        dist u t < η → dist v t < η →
          dist (β u) (β v) = Real.sinh (gluingRadius C g) * |α u - α v|) ∧
      eVariationOn β univ =
        eVariationOn (fun t => Real.sinh (gluingRadius C g) * α t) univ ∧
      ∀ u v, β u = β v → Circle.exp (α u) = Circle.exp (α v) := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  letI : ContractibleSpace (Icc a b) :=
    (convex_Icc a b).contractibleSpace ⟨a, le_rfl, hab.le⟩
  letI : LocallyPathConnectedSpace (Icc a b) :=
    (convex_Icc a b).locallyPathConnectedSpace
  have himage : ∀ t, β t ∈ P.gluedMk '' P.seamNeighborhood k :=
    fun t => gluedSeamCircle_subset_cylinder_image P k (hseam t)
  let βsub : Icc a b → ↥(P.gluedMk '' P.seamNeighborhood k) := fun t => ⟨β t, himage t⟩
  let B : Icc a b → Circle := fun t => ((P.seamCylinderHomeomorph k).symm (βsub t)).1
  have hB : Continuous B :=
    ((P.seamCylinderHomeomorph k).symm.continuous.comp (hβ.subtype_mk himage)).fst
  let t₀ : Icc a b := ⟨a, le_rfl, hab.le⟩
  obtain ⟨α, hα, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    ⟨B, hB⟩ t₀ (Complex.arg (B t₀ : ℂ)) (Circle.exp_arg (B t₀))
  have hangle : ∀ t, Circle.exp (α t) = B t := fun t => congrFun hα.2 t
  let zero : Ioo (-gluingDepth C g) (gluingDepth C g) :=
    ⟨0, by constructor <;> linarith [P.depth_pos]⟩
  have hrepresentation (t : Icc a b) : β t =
      (P.seamCylinderHomeomorph k (Circle.exp (α t), zero)).1 := by
    have hp : (Circle.exp (α t), zero) = (P.seamCylinderHomeomorph k).symm (βsub t) := by
      apply Prod.ext (hangle t)
      apply Subtype.ext
      exact (cylinder_inverse_radial_eq_zero_of_mem_seam P k (β t) (hseam t) (himage t)).symm
    rw [hp]
    exact (congrArg Subtype.val ((P.seamCylinderHomeomorph k).apply_symm_apply (βsub t))).symm
  have hlocal (t : Icc a b) : ∃ η > 0, ∀ u v : Icc a b,
      dist u t < η → dist v t < η →
        dist (β u) (β v) = Real.sinh (gluingRadius C g) * |α u - α v| := by
    letI : MetricSpace ℂ := gluingCollarModelMetricSpace P.radius_pos
    letI : PseudoMetricSpace ℂ := (gluingCollarModelMetricSpace P.radius_pos).toPseudoMetricSpace
    letI : UniformSpace ℂ := (gluingCollarModelMetricSpace P.radius_pos).toUniformSpace
    let θ := α t
    have hθ : θ ∈ GluingAngularInterval θ := by
      constructor <;> linarith [Real.pi_pos]
    let p : GluingSeamAngularDomain C g θ := (zero, ⟨θ, hθ⟩)
    have hx : β t ∈ (P.seamAngularComplexChart k θ).source := by
      rw [P.seamAngularComplexChart_source]
      exact ⟨p, (hrepresentation t).symm⟩
    obtain ⟨ρ, hρ, _hball, hmetric⟩ :=
      P.gluedIntrinsicMetric_seam_locally_isometric k θ (β t) hx
    have hpre : (β ⁻¹' Metric.ball (β t) ρ) ∩ (α ⁻¹' GluingAngularInterval θ) ∈ 𝓝 t :=
      inter_mem (hβ.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hρ))
        (α.continuous.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hθ))
    obtain ⟨η, hη, hsmall⟩ := Metric.mem_nhds_iff.mp hpre
    have hchart (u : Icc a b) (hu : dist u t < η) :
        P.seamAngularComplexChart k θ (β u) = (α u : ℂ) * Complex.I := by
      let q : GluingSeamAngularDomain C g θ := (zero, ⟨α u, (hsmall hu).2⟩)
      have hpoint : β u = P.seamAngularPoint k θ q := hrepresentation u
      rw [hpoint, P.seamAngularComplexChart_apply]
      apply Complex.ext <;> simp [q, zero]
    refine ⟨η, hη, ?_⟩
    intro u v hu hv
    rw [← hmetric (β u) (hsmall hu).1 (β v) (hsmall hv).1,
      hchart u hu, hchart v hv]
    exact gluingCollarModelMetric_dist_seam P.radius_pos (α u) (α v)
  have hvariation : eVariationOn β univ =
      eVariationOn (fun t => Real.sinh (gluingRadius C g) * α t) univ := by
    apply eVariationOn_Icc_subtype_eq_of_interior_locally_edist_eq hab β
      (fun t => Real.sinh (gluingRadius C g) * α t) hβ
      (continuous_const.mul α.continuous)
    intro t _ _
    obtain ⟨η, hη, hm⟩ := hlocal t
    refine ⟨η, hη, ?_⟩
    intro u v hu hv
    rw [edist_dist, edist_dist, hm u v hu hv, Real.dist_eq,
      ← mul_sub, abs_mul, abs_of_pos (Real.sinh_pos_iff.mpr P.radius_pos)]
  refine ⟨α, α.continuous, fun t _ _ => hlocal t, hvariation, ?_⟩
  intro u v huv
  rw [hangle u, hangle v]
  exact congrArg (fun q : ↥(P.gluedMk '' P.seamNeighborhood k) =>
    ((P.seamCylinderHomeomorph k).symm q).1) (Subtype.ext huv)

#print axioms exists_continuous_seam_angular_lift

end SystolicGrowth.ExerciseGluingPreparation
