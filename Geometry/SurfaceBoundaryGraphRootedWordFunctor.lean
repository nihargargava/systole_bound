module

public import Geometry.SurfaceBoundaryGraphRootedPaths
public import Geometry.SurfaceBoundaryGraphFreeGenerators
public import Geometry.TwoOpenCoverVanKampen

@[expose] public section

/-!
# The rooted physical graph reader is the identity

The actual global root paths extend the identity based homomorphism to the
whole fundamental groupoid. Star transport makes its first restriction
constant. Literal middle-prefix transport and the proved gauge-loop identity
make its second restriction the physical-side difference functor. Uniqueness
of the actual open-cover pushout identifies this functor with the reader of
the actual based side generators, without a generation premise.
-/

open Set CategoryTheory UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth

noncomputable section

private theorem rooted_lasso_eq_difference {C : Type*} [Groupoid C] (r : C)
    {x y : C} (p₀ Φ₀ : r ⟶ x) (p₁ Φ₁ : r ⟶ y) (f : x ⟶ y)
    (hΦ : Φ₀ ≫ f = Φ₁) :
    p₀ ≫ f ≫ inv p₁ = inv (Φ₀ ≫ inv p₀) ≫ (Φ₁ ≫ inv p₁) := by
  rw [IsIso.inv_comp, IsIso.inv_inv, ← hΦ]
  simp [Category.assoc]

namespace DirichletBoundarySegments

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

/-- The identity based homomorphism extended using the genuine global rooted
paths on the original physical boundary graph. -/
def intrinsicBoundaryGraphRootedFunctor (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) :
    FundamentalGroupoid B.IntrinsicBoundaryGraph ⥤
      SingleObj (FundamentalGroup B.IntrinsicBoundaryGraph
        (B.intrinsicBoundaryGraphVertexInclusion r)) :=
  basedGroupoidFunctor (FundamentalGroupoid.mk (B.intrinsicBoundaryGraphVertexInclusion r))
    (MonoidHom.id _) (fun q =>
      Path.Homotopic.Quotient.mk (B.intrinsicBoundaryGraphRootedPath r q.as))

/-- The genuine rooted functor restricts to the constant star-side functor
on every actual star-union morphism. -/
theorem intrinsicBoundaryGraphRootedFunctor_comp_star
    (B : DirichletBoundarySegments X o) (r : B.IntrinsicBoundaryGraphVertex) :
    FundamentalGroupoid.map (twoOpenCoverInclusion B.intrinsicBoundaryGraphStarUnion) ⋙
        B.intrinsicBoundaryGraphRootedFunctor r =
      B.intrinsicBoundaryGraphStarWordFunctor := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro a b f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective f
  rw [B.intrinsicBoundaryGraphStarWordFunctor_map]
  let R := FundamentalGroupoid.mk (B.intrinsicBoundaryGraphVertexInclusion r)
  let A := FundamentalGroupoid.mk a.as.val
  let Z := FundamentalGroupoid.mk b.as.val
  let p₀ : R ⟶ A :=
    Path.Homotopic.Quotient.mk (B.intrinsicBoundaryGraphRootedPath r a.as.val)
  let p₁ : R ⟶ Z :=
    Path.Homotopic.Quotient.mk (B.intrinsicBoundaryGraphRootedPath r b.as.val)
  let f : A ⟶ Z := Path.Homotopic.Quotient.mk (γ.map continuous_subtype_val)
  change p₀ ≫ f ≫ inv p₁ =
    (1 : FundamentalGroup B.IntrinsicBoundaryGraph (B.intrinsicBoundaryGraphVertexInclusion r))
  rw [← Groupoid.inv_eq_inv]
  change (Path.Homotopic.Quotient.mk (B.intrinsicBoundaryGraphRootedPath r a.as.val)).trans
      ((Path.Homotopic.Quotient.mk (γ.map continuous_subtype_val)).trans
        (Path.Homotopic.Quotient.mk (B.intrinsicBoundaryGraphRootedPath r b.as.val)).symm) =
    Path.Homotopic.Quotient.refl (B.intrinsicBoundaryGraphVertexInclusion r)
  rw [← Path.Homotopic.Quotient.trans_assoc, ← Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.eq.mpr
      (B.intrinsicBoundaryGraphRootedPath_star_transport r γ),
    Path.Homotopic.Quotient.trans_symm]

/-- The genuine rooted functor reads every actual middle-side morphism as
the difference of its two proved physical-side gauges. -/
theorem intrinsicBoundaryGraphRootedFunctor_comp_midsection
    (B : DirichletBoundarySegments X o) (r : B.IntrinsicBoundaryGraphVertex) :
    FundamentalGroupoid.map (twoOpenCoverInclusion B.intrinsicBoundaryGraphMidsectionUnion) ⋙
        B.intrinsicBoundaryGraphRootedFunctor r =
      B.intrinsicBoundaryGraphMidsectionWordFunctor
        (fun e => B.intrinsicBoundarySideGenerator r e.val) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro a b f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective f
  rw [B.intrinsicBoundaryGraphMidsectionWordFunctor_map]
  let R := FundamentalGroupoid.mk (B.intrinsicBoundaryGraphVertexInclusion r)
  let A := FundamentalGroupoid.mk a.as.val
  let Z := FundamentalGroupoid.mk b.as.val
  let p₀ : R ⟶ A :=
    Path.Homotopic.Quotient.mk (B.intrinsicBoundaryGraphRootedPath r a.as.val)
  let p₁ : R ⟶ Z :=
    Path.Homotopic.Quotient.mk (B.intrinsicBoundaryGraphRootedPath r b.as.val)
  let Φ₀ : R ⟶ A :=
    Path.Homotopic.Quotient.mk (B.intrinsicBoundaryGraphMidsectionRootedPath r a.as)
  let Φ₁ : R ⟶ Z :=
    Path.Homotopic.Quotient.mk (B.intrinsicBoundaryGraphMidsectionRootedPath r b.as)
  let f : A ⟶ Z := Path.Homotopic.Quotient.mk (γ.map continuous_subtype_val)
  have hΦ : Φ₀ ≫ f = Φ₁ :=
    (Path.Homotopic.Quotient.mk_trans _ _).symm.trans
      (Path.Homotopic.Quotient.eq.mpr
        (B.intrinsicBoundaryGraphMidsectionRootedPath_transport r γ))
  have h₀ : Φ₀ ≫ inv p₀ =
      B.intrinsicBoundaryMidsectionGauge (fun e => B.intrinsicBoundarySideGenerator r e.val)
        a.as := by
    rw [← Groupoid.inv_eq_inv]
    exact (Path.Homotopic.Quotient.mk_trans _ _).symm.trans
      (B.intrinsicBoundaryGraphMidsectionRootedPath_gauge r a.as)
  have h₁ : Φ₁ ≫ inv p₁ =
      B.intrinsicBoundaryMidsectionGauge (fun e => B.intrinsicBoundarySideGenerator r e.val)
        b.as := by
    rw [← Groupoid.inv_eq_inv]
    exact (Path.Homotopic.Quotient.mk_trans _ _).symm.trans
      (B.intrinsicBoundaryGraphMidsectionRootedPath_gauge r b.as)
  change p₀ ≫ f ≫ inv p₁ = _
  rw [rooted_lasso_eq_difference R p₀ Φ₀ p₁ Φ₁ f hΦ]
  rw [← Groupoid.inv_eq_inv]
  rw [h₀, h₁]
  rfl

/-- Actual open-cover pushout uniqueness identifies the rooted identity
functor with the reader having actual side-generator coefficients. -/
theorem intrinsicBoundaryGraphRootedFunctor_eq_wordFunctor
    (B : DirichletBoundarySegments X o) (r : B.IntrinsicBoundaryGraphVertex) :
    B.intrinsicBoundaryGraphRootedFunctor r =
      B.intrinsicBoundaryGraphWordFunctor (fun e => B.intrinsicBoundarySideGenerator r e.val) := by
  apply twoOpenCoverGroupoid_ext B.intrinsicBoundaryGraphStarUnion_isOpen
    B.intrinsicBoundaryGraphMidsectionUnion_isOpen
    B.intrinsicBoundaryGraphStarUnion_union_midsectionUnion
  · exact (B.intrinsicBoundaryGraphRootedFunctor_comp_star r).trans
      (B.intrinsicBoundaryGraphWordFunctor_comp_star _).symm
  · exact (B.intrinsicBoundaryGraphRootedFunctor_comp_midsection r).trans
      (B.intrinsicBoundaryGraphWordFunctor_comp_midsection _).symm

/-- Nullhomotopy of the genuine root connector retains the identity on the
original based fundamental group, rather than a conjugation. -/
theorem intrinsicBoundaryGraphRootedFunctor_map_base
    (B : DirichletBoundarySegments X o) (r : B.IntrinsicBoundaryGraphVertex)
    (f : FundamentalGroup B.IntrinsicBoundaryGraph
      (B.intrinsicBoundaryGraphVertexInclusion r)) :
    (B.intrinsicBoundaryGraphRootedFunctor r).map f = f := by
  apply basedGroupoidFunctor_map_base
  exact Path.Homotopic.Quotient.eq.mpr
    (B.intrinsicBoundaryGraphRootedPath_root_homotopic r)

/-- Reading actual side-generator coefficients is exactly the identity
homomorphism on the actual original based group. No loop generation is assumed. -/
theorem intrinsicBoundaryGraphWordHom_sideGenerators
    (B : DirichletBoundarySegments X o) (r : B.IntrinsicBoundaryGraphVertex) :
    B.intrinsicBoundaryGraphWordHom (fun e => B.intrinsicBoundarySideGenerator r e.val) r =
      MonoidHom.id _ := by
  ext f
  rw [intrinsicBoundaryGraphWordHom_apply,
    ← B.intrinsicBoundaryGraphRootedFunctor_eq_wordFunctor r]
  exact B.intrinsicBoundaryGraphRootedFunctor_map_base r f

/-- Evaluating the genuine free-word reader returns every original based
loop. This is the right-inverse equation on the whole fundamental group,
not merely on the chosen side generators. -/
theorem intrinsicBoundaryFreeGeneratorHom_comp_wordHom
    (B : DirichletBoundarySegments X o) (r : B.IntrinsicBoundaryGraphVertex) :
    (B.intrinsicBoundaryFreeGeneratorHom r).comp
        (B.intrinsicBoundaryGraphWordHom
          (fun e : B.IntrinsicBoundaryPhysicalEdge => B.intrinsicBoundaryFreeSideWord e.val) r) =
      MonoidHom.id _ := by
  rw [B.intrinsicBoundaryGraphWordHom_hom]
  simpa only [intrinsicBoundaryFreeGeneratorHom_sideWord] using
    B.intrinsicBoundaryGraphWordHom_sideGenerators r

end DirichletBoundarySegments

end

end SystolicGrowth
