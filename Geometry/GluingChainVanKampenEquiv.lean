module

public import Geometry.GluingChainVanKampenSurjective
public import Geometry.TwoOpenCoverVanKampen

@[expose] public section

/-! The native canonical chain-cover amalgam is the based fundamental group. -/

open Set

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

def Internal.GluingChainVanKampenEquivHelpers.chainCoverIntersectionToSeam
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    C(↥(P.gluedChainPrefixNeighborhood k ∩ P.gluedChainSuffixNeighborhood k),
      ↥(P.gluedMk '' P.seamNeighborhood k)) where
  toFun z := ⟨z.1, P.gluedChainPrefixNeighborhood_inter_suffix k ▸ z.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

private theorem chainCover_amalgam_compatible
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : Circle) :
    let x : ↥(P.gluedChainPrefixNeighborhood k ∩ P.gluedChainSuffixNeighborhood k) :=
      ⟨(P.gluedSeamCircleInclusion k θ).1,
        Or.inr (P.gluedSeamCircleInclusion k θ).2,
        Or.inr (P.gluedSeamCircleInclusion k θ).2⟩
    (Monoid.PushoutI.of true : P.gluedChainCoverSideGroup k θ true →*
      P.gluedChainCoverAmalgam k θ).comp
      (FundamentalGroup.map
        (⟨fun z ↦ ⟨z.1, z.2.1⟩, continuous_subtype_val.subtype_mk _⟩ :
          C(↥(P.gluedChainPrefixNeighborhood k ∩ P.gluedChainSuffixNeighborhood k),
            ↥(P.gluedChainPrefixNeighborhood k))) x) =
    (Monoid.PushoutI.of false : P.gluedChainCoverSideGroup k θ false →*
      P.gluedChainCoverAmalgam k θ).comp
      (FundamentalGroup.map
        (⟨fun z ↦ ⟨z.1, z.2.2⟩, continuous_subtype_val.subtype_mk _⟩ :
          C(↥(P.gluedChainPrefixNeighborhood k ∩ P.gluedChainSuffixNeighborhood k),
            ↥(P.gluedChainSuffixNeighborhood k))) x) := by
  dsimp only
  ext γ
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
  let q : Path (P.gluedSeamCircleInclusion k θ) (P.gluedSeamCircleInclusion k θ) :=
    p.map (Internal.GluingChainVanKampenEquivHelpers.chainCoverIntersectionToSeam P k).continuous
  change Monoid.PushoutI.of true
    (P.gluedChainCoverOverlapGroupMap k θ true (Path.Homotopic.Quotient.mk q)) =
      Monoid.PushoutI.of false
        (P.gluedChainCoverOverlapGroupMap k θ false (Path.Homotopic.Quotient.mk q))
  exact (Monoid.PushoutI.of_apply_eq_base (P.gluedChainCoverOverlapGroupMap k θ)
    true (Path.Homotopic.Quotient.mk q)).trans
      (Monoid.PushoutI.of_apply_eq_base (P.gluedChainCoverOverlapGroupMap k θ)
        false (Path.Homotopic.Quotient.mk q)).symm

private theorem chainCover_injective_of_side_descent
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : Circle)
    (f : FundamentalGroup P.GluedCarrier (P.gluedSeamCircleInclusion k θ).1 →*
      P.gluedChainCoverAmalgam k θ)
    (hf : ∀ b : Bool, f.comp (P.gluedChainCoverSideGroupMap k θ b) =
      (Monoid.PushoutI.of b : P.gluedChainCoverSideGroup k θ b →*
        P.gluedChainCoverAmalgam k θ)) :
    Function.Injective (P.gluedChainCoverAmalgamToFundamentalGroup k θ) := by
  have hleft : f.comp (P.gluedChainCoverAmalgamToFundamentalGroup k θ) =
      MonoidHom.id (P.gluedChainCoverAmalgam k θ) := by
    apply Monoid.PushoutI.hom_ext_nonempty
    intro b
    ext γ
    simpa only [MonoidHom.comp_apply,
      P.gluedChainCoverAmalgamToFundamentalGroup_of, MonoidHom.id_apply] using
      DFunLike.congr_fun (hf b) γ
  apply Function.LeftInverse.injective (g := f)
  intro γ
  exact DFunLike.congr_fun hleft γ

/-- Descent into the actual amalgam gives a left inverse of the original canonical map. -/
theorem gluedChainCoverAmalgamToFundamentalGroup_injective
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : Circle) :
    Function.Injective (P.gluedChainCoverAmalgamToFundamentalGroup k θ) := by
  let x : ↥(P.gluedChainPrefixNeighborhood k ∩ P.gluedChainSuffixNeighborhood k) :=
    ⟨(P.gluedSeamCircleInclusion k θ).1,
      Or.inr (P.gluedSeamCircleInclusion k θ).2,
      Or.inr (P.gluedSeamCircleInclusion k θ).2⟩
  have hpcUV : IsPathConnected
      (P.gluedChainPrefixNeighborhood k ∩ P.gluedChainSuffixNeighborhood k) := by
    rw [P.gluedChainPrefixNeighborhood_inter_suffix k]
    exact P.gluedSeamNeighborhood_isPathConnected k
  obtain ⟨f, hfU, hfV⟩ := exists_fundamentalGroup_hom_of_two_open_cover
    (P.gluedChainPrefixNeighborhood_isOpen k) (P.gluedChainSuffixNeighborhood_isOpen k)
    (P.gluedChainPrefixNeighborhood_union_suffix k)
    (P.gluedChainPrefixNeighborhood_isPathConnected k)
    (P.gluedChainSuffixNeighborhood_isPathConnected k) hpcUV x
    (Monoid.PushoutI.of true : P.gluedChainCoverSideGroup k θ true →*
      P.gluedChainCoverAmalgam k θ)
    (Monoid.PushoutI.of false : P.gluedChainCoverSideGroup k θ false →*
      P.gluedChainCoverAmalgam k θ)
    (chainCover_amalgam_compatible P k θ)
  apply chainCover_injective_of_side_descent P k θ f
  intro b
  cases b
  · exact hfV
  · exact hfU

/-- Van Kampen bijectivity holds for the literal native based cover map. -/
theorem gluedChainCoverAmalgamToFundamentalGroup_bijective
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : Circle) :
    Function.Bijective (P.gluedChainCoverAmalgamToFundamentalGroup k θ) :=
  ⟨P.gluedChainCoverAmalgamToFundamentalGroup_injective k θ,
    P.gluedChainCoverAmalgamToFundamentalGroup_surjective k θ⟩

/-- The original overlap amalgam identifies with the original carrier's fundamental group,
using precisely the canonical inclusion-induced map. -/
def gluedChainCoverFundamentalGroupEquiv
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : Circle) :
    P.gluedChainCoverAmalgam k θ ≃*
      FundamentalGroup P.GluedCarrier (P.gluedSeamCircleInclusion k θ).1 :=
  MulEquiv.ofBijective (P.gluedChainCoverAmalgamToFundamentalGroup k θ)
    (P.gluedChainCoverAmalgamToFundamentalGroup_bijective k θ)

@[simp] theorem gluedChainCoverFundamentalGroupEquiv_apply
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : Circle)
    (γ : P.gluedChainCoverAmalgam k θ) :
    P.gluedChainCoverFundamentalGroupEquiv k θ γ =
      P.gluedChainCoverAmalgamToFundamentalGroup k θ γ := rfl

/-- In particular, the equivalence retains every literal original side-group image. -/
@[simp] theorem gluedChainCoverFundamentalGroupEquiv_of
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : Circle)
    (b : Bool) (γ : P.gluedChainCoverSideGroup k θ b) :
    P.gluedChainCoverFundamentalGroupEquiv k θ (Monoid.PushoutI.of b γ) =
      P.gluedChainCoverSideGroupMap k θ b γ :=
  P.gluedChainCoverAmalgamToFundamentalGroup_of k θ b γ

/-- The actual one-turn overlap class is preserved without a change of basepoint. -/
@[simp] theorem gluedChainCoverFundamentalGroupEquiv_base
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : Circle)
    (γ : FundamentalGroup ↥(P.gluedMk '' P.seamNeighborhood k)
      (P.gluedSeamCircleInclusion k θ)) :
    P.gluedChainCoverFundamentalGroupEquiv k θ
      (Monoid.PushoutI.base (P.gluedChainCoverOverlapGroupMap k θ) γ) =
        P.gluedChainCoverSeamGroupMap k θ γ :=
  P.gluedChainCoverAmalgamToFundamentalGroup_base k θ γ

end

end SystolicGrowth.ExerciseGluingPreparation
