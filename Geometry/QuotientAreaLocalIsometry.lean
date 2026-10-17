module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.QuotientOrbitBall
public import Geometry.HyperbolicArea
public import Mathlib.MeasureTheory.Measure.Comap

@[expose] public section

/-!
# Natural quotient area on genuine projection sheets

The Dirichlet-domain definition of quotient area agrees with original
hyperbolic volume on every measurable subset of an injective open ball.
The half-systole bound is non-strict: the open ball's pointwise distance
inequalities provide the strict separation. The corresponding literal
subtype projection pulls quotient area back to original hyperbolic area.
-/

open Set MeasureTheory UpperHalfPlane
open scoped ENNReal MatrixGroups Pointwise UpperHalfPlane

namespace SystolicGrowth
namespace ClosedHyperbolicSurface

/-- The saturation of an actual measurable set under the literal quotient
projection is the union of its deck-translated preimages. -/
theorem quotientMk_image_preimage {g : ℕ} (X : ClosedHyperbolicSurface g) (s : Set ℍ) :
    (Quotient.mk (MulAction.orbitRel X.deckGroup ℍ)) ⁻¹'
        ((Quotient.mk (MulAction.orbitRel X.deckGroup ℍ)) '' s) =
      ⋃ γ : X.deckGroup, (fun z : ℍ => γ • z) ⁻¹' s := by
  ext z
  constructor
  · rintro ⟨v, hv, hvz⟩
    have hrel : MulAction.orbitRel X.deckGroup ℍ v z := Quotient.exact hvz
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hrel)
    refine mem_iUnion.mpr ⟨γ, ?_⟩
    change γ • z ∈ s
    simpa only [hγ] using hv
  · intro hz
    obtain ⟨γ, hγ⟩ := mem_iUnion.mp hz
    change γ • z ∈ s at hγ
    exact ⟨γ • z, hγ, Quotient.sound (MulAction.orbitRel_apply.mpr
      (MulAction.mem_orbit_iff.mpr ⟨γ, rfl⟩))⟩

/-- Countability of the actual marked deck group makes images of Borel
sets measurable in the original quotient measurable space. -/
theorem measurableSet_quotientMk_image {g : ℕ} (X : ClosedHyperbolicSurface g)
    {s : Set ℍ} (hs : MeasurableSet s) :
    MeasurableSet ((Quotient.mk (MulAction.orbitRel X.deckGroup ℍ)) '' s) := by
  letI : Countable (SurfaceGroup g) := by
    change Countable (Quotient (QuotientGroup.leftRel
      (Subgroup.normalClosure ({surfaceRelator g} : Set (FreeGroup (SurfaceGenerator g))))))
    infer_instance
  letI : Countable X.deckGroup :=
    (Equiv.countable_iff X.marking.toEquiv).mpr inferInstance
  apply measurableSet_quotient.mpr
  change MeasurableSet ((Quotient.mk (MulAction.orbitRel X.deckGroup ℍ)) ⁻¹'
    ((Quotient.mk (MulAction.orbitRel X.deckGroup ℍ)) '' s))
  rw [X.quotientMk_image_preimage]
  exact MeasurableSet.iUnion fun γ => hs.preimage (continuous_const_smul γ).measurable

/-- The genuine open projection ball stays injective even at the closed
half-systole radius bound. -/
theorem quotientMk_injOn_ball_of_two_mul_le {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (R : ℝ) (hR : 2 * R ≤ X.systole) :
    InjOn (Quotient.mk (MulAction.orbitRel X.deckGroup ℍ)) (Metric.ball o R) := by
  intro z hz w hw hquot
  have horbit : z ∈ MulAction.orbit X.deckGroup w := Quotient.exact hquot
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp horbit
  by_cases hγone : γ = 1
  · subst γ
    simpa using hγ.symm
  · have hsys : X.systole ≤ dist w z := by
      simpa [hγ] using X.systole_le_displacement γ hγone w
    have hw' : dist w o < R := Metric.mem_ball.mp hw
    have hz' : dist z o < R := Metric.mem_ball.mp hz
    have hwz : dist w z < 2 * R := calc
      dist w z ≤ dist w o + dist o z := dist_triangle _ _ _
      _ = dist w o + dist z o := by rw [dist_comm o z]
      _ < R + R := add_lt_add hw' hz'
      _ = 2 * R := by ring
    exact False.elim ((not_lt_of_ge hsys) (hwz.trans_le hR))

/-- The original centered Dirichlet region contains the entire actual
open ball at any radius satisfying the half-systole bound. -/
theorem ball_subset_dirichletDomain_of_two_mul_le {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) (R : ℝ) (hR : 2 * R ≤ X.systole) :
    Metric.ball o R ⊆ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o := by
  intro z hz
  apply Vendored.RiemannDynamics.mem_dirichletDomain.mpr
  intro γ
  by_cases hγ : γ = 1
  · simp [hγ]
  · have hsys := X.systole_le_displacement γ hγ o
    have htri := dist_triangle o z (γ • o)
    have hz' := Metric.mem_ball.mp hz
    rw [dist_comm o z] at htri
    linarith

/-- Dirichlet minimization plus actual short-ball injectivity identifies
the representative set in the quotient-area definition exactly. -/
theorem quotientMk_image_preimage_inter_dirichletDomain {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) (R : ℝ) (hR : 2 * R ≤ X.systole)
    {s : Set ℍ} (hsball : s ⊆ Metric.ball o R) :
    (Quotient.mk (MulAction.orbitRel X.deckGroup ℍ)) ⁻¹'
        ((Quotient.mk (MulAction.orbitRel X.deckGroup ℍ)) '' s) ∩
      Vendored.RiemannDynamics.dirichletDomain X.deckGroup o = s := by
  ext z
  constructor
  · rintro ⟨⟨v, hv, hvz⟩, hzD⟩
    have hzball : z ∈ Metric.ball o R :=
      X.dirichlet_mem_orbitBall_implies_mem_ball o z R hzD ⟨v, hsball hv, hvz⟩
    have hvz' := X.quotientMk_injOn_ball_of_two_mul_le o R hR (hsball hv) hzball hvz
    exact hvz' ▸ hv
  · intro hz
    exact ⟨⟨z, hz, rfl⟩, X.ball_subset_dirichletDomain_of_two_mul_le o R hR (hsball hz)⟩

/-- Natural quotient area is literally the original hyperbolic volume
on arbitrary measurable pieces of a genuine injective projection ball.
The quotient measure's Dirichlet center may be chosen independently. -/
theorem quotientAreaMeasure_image_of_subset_ball {g : ℕ}
    (X : ClosedHyperbolicSurface g) (measureCenter o : ℍ) (R : ℝ)
    (hR : 2 * R ≤ X.systole) {s : Set ℍ}
    (hs : MeasurableSet s) (hsball : s ⊆ Metric.ball o R) :
    X.quotientAreaMeasure measureCenter
      ((Quotient.mk (MulAction.orbitRel X.deckGroup ℍ)) '' s) = volume s := by
  rw [X.quotientAreaMeasure_center_independent measureCenter o]
  unfold quotientAreaMeasure
  letI : Setoid ℍ := MulAction.orbitRel X.deckGroup ℍ
  change ((volume.restrict (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)).map
    (Quotient.mk' : ℍ → X.Carrier))
      ((Quotient.mk (MulAction.orbitRel X.deckGroup ℍ)) '' s) = _
  have hm := measurable_quotient_mk' (s := MulAction.orbitRel X.deckGroup ℍ)
  rw [Measure.map_apply hm (X.measurableSet_quotientMk_image hs),
    Measure.restrict_apply (hm (X.measurableSet_quotientMk_image hs))]
  change volume ((Quotient.mk (MulAction.orbitRel X.deckGroup ℍ)) ⁻¹'
    ((Quotient.mk (MulAction.orbitRel X.deckGroup ℍ)) '' s) ∩
      Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) = volume s
  rw [X.quotientMk_image_preimage_inter_dirichletDomain o R hR hsball]

/-- The literal small-ball projection is a measurable embedding for the
actual quotient measurable space, not a substituted local model. -/
theorem quotientBall_measurableEmbedding_of_two_mul_le {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) (R : ℝ) (hR : 2 * R ≤ X.systole) :
    MeasurableEmbedding (fun z : Metric.ball o R =>
      Quotient.mk (MulAction.orbitRel X.deckGroup ℍ) z.1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z w h
    exact Subtype.ext (X.quotientMk_injOn_ball_of_two_mul_le o R hR z.2 w.2 h)
  · letI : Setoid ℍ := MulAction.orbitRel X.deckGroup ℍ
    exact measurable_quotient_mk'.comp measurable_subtype_coe
  · intro s hs
    have himage : (fun z : Metric.ball o R =>
        Quotient.mk (MulAction.orbitRel X.deckGroup ℍ) z.1) '' s =
        (Quotient.mk (MulAction.orbitRel X.deckGroup ℍ)) '' (Subtype.val '' s) := by
      rw [← image_comp]
      rfl
    rw [himage]
    exact X.measurableSet_quotientMk_image
      ((MeasurableEmbedding.subtype_coe Metric.isOpen_ball.measurableSet).measurableSet_image' hs)

/-- Pulling natural quotient area back through the literal projection
sheet gives original hyperbolic area on the same original ball subtype. -/
theorem quotientAreaMeasure_comap_ball {g : ℕ}
    (X : ClosedHyperbolicSurface g) (measureCenter o : ℍ) (R : ℝ)
    (hR : 2 * R ≤ X.systole) :
    (X.quotientAreaMeasure measureCenter).comap (fun z : Metric.ball o R =>
      Quotient.mk (MulAction.orbitRel X.deckGroup ℍ) z.1) =
        volume.comap (Subtype.val : Metric.ball o R → ℍ) := by
  have hι := X.quotientBall_measurableEmbedding_of_two_mul_le o R hR
  have hsub := MeasurableEmbedding.subtype_coe
    (show MeasurableSet (Metric.ball o R) from Metric.isOpen_ball.measurableSet)
  apply Measure.ext
  intro s hs
  rw [Measure.comap_apply _ hι.injective (fun _ ht => hι.measurableSet_image' ht) _ hs,
    Measure.comap_apply _ hsub.injective (fun _ ht => hsub.measurableSet_image' ht) _ hs]
  have himage : (fun z : Metric.ball o R =>
      Quotient.mk (MulAction.orbitRel X.deckGroup ℍ) z.1) '' s =
      (Quotient.mk (MulAction.orbitRel X.deckGroup ℍ)) '' (Subtype.val '' s) := by
    rw [← image_comp]
    rfl
  rw [himage]
  apply X.quotientAreaMeasure_image_of_subset_ball measureCenter o R hR
    (hsub.measurableSet_image' hs)
  rintro z ⟨w, _, rfl⟩
  exact w.2

#print axioms quotientAreaMeasure_image_of_subset_ball
#print axioms quotientAreaMeasure_comap_ball

end ClosedHyperbolicSurface
end SystolicGrowth
