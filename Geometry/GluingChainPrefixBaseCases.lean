module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainCollarRetraction
public import Geometry.GluingChainCoverConnected

@[expose] public section

/-!
# Native base cases for chain-prefix induction

The first closed prefix and the last closed suffix are the actual embedded
retained components. All closed chain sides are path connected through the
constructed collar retractions, without changing their boundary circles.
-/

open Set

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Math. The actual closed prefix inherits path connectivity from its collar. -/
instance gluedChainPrefixPathConnectedSpace
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    PathConnectedSpace (P.gluedChainPrefix k) := by
  have hs : Function.Surjective (P.gluedChainPrefixRetraction k) := by
    intro x
    exact ⟨P.gluedChainPrefixInclusion k x, P.gluedChainPrefixRetraction_inclusion k x⟩
  exact hs.pathConnectedSpace (P.gluedChainPrefixRetraction k).continuous

/-- Math. The actual closed suffix inherits path connectivity from its collar. -/
instance gluedChainSuffixPathConnectedSpace
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    PathConnectedSpace (P.gluedChainSuffix k) := by
  have hs : Function.Surjective (P.gluedChainSuffixRetraction k) := by
    intro x
    exact ⟨P.gluedChainSuffixInclusion k x, P.gluedChainSuffixRetraction_inclusion k x⟩
  exact hs.pathConnectedSpace (P.gluedChainSuffixRetraction k).continuous

/-- Math. Before the first seam, the closed prefix is the first retained component. -/
theorem gluedChainPrefix_zero_eq_componentImage
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (hk : k.val = 0) :
    P.gluedChainPrefix k = P.gluedComponentImage (gluingChainEdgeLeft k) := by
  ext q
  constructor
  · rintro ⟨⟨i, a⟩, hi, rfl⟩
    have he : i = gluingChainEdgeLeft k := by
      apply Fin.ext
      change i.val = k.val
      change i.val ≤ k.val at hi
      omega
    subst i
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨gluingChainEdgeLeft k, a⟩, by change k.val ≤ k.val; exact le_rfl, rfl⟩

/-- Math. After the final seam, the closed suffix is the last retained component. -/
theorem gluedChainSuffix_last_eq_componentImage
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (hk : k.val + 2 = n) :
    P.gluedChainSuffix k = P.gluedComponentImage (gluingChainEdgeRight k) := by
  ext q
  constructor
  · rintro ⟨⟨i, a⟩, hi, rfl⟩
    have he : i = gluingChainEdgeRight k := by
      apply Fin.ext
      change i.val = k.val + 1
      change k.val < i.val at hi
      have := i.isLt
      omega
    subst i
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨gluingChainEdgeRight k, a⟩, by change k.val < k.val + 1; omega, rfl⟩

/-- Math. The first-prefix identification is literal on the original quotient points. -/
noncomputable def gluedChainPrefixZeroHomeomorph
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (hk : k.val = 0) :
    P.ChainComponent (gluingChainEdgeLeft k) ≃ₜ ↥(P.gluedChainPrefix k) :=
  (P.gluedComponentHomeomorph (gluingChainEdgeLeft k)).trans
    (Homeomorph.setCongr (P.gluedChainPrefix_zero_eq_componentImage k hk).symm)

/-- Math. The last-suffix identification is literal on the original quotient points. -/
noncomputable def gluedChainSuffixLastHomeomorph
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (hk : k.val + 2 = n) :
    P.ChainComponent (gluingChainEdgeRight k) ≃ₜ ↥(P.gluedChainSuffix k) :=
  (P.gluedComponentHomeomorph (gluingChainEdgeRight k)).trans
    (Homeomorph.setCongr (P.gluedChainSuffix_last_eq_componentImage k hk).symm)

@[simp] theorem gluedChainPrefixZeroHomeomorph_apply_val
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (hk : k.val = 0) (x : P.ChainComponent (gluingChainEdgeLeft k)) :
    (P.gluedChainPrefixZeroHomeomorph k hk x).val =
      P.gluedMk ⟨gluingChainEdgeLeft k, x⟩ := rfl

@[simp] theorem gluedChainSuffixLastHomeomorph_apply_val
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (hk : k.val + 2 = n) (x : P.ChainComponent (gluingChainEdgeRight k)) :
    (P.gluedChainSuffixLastHomeomorph k hk x).val =
      P.gluedMk ⟨gluingChainEdgeRight k, x⟩ := rfl

#print axioms gluedChainPrefixPathConnectedSpace
#print axioms gluedChainSuffixPathConnectedSpace
#print axioms gluedChainPrefix_zero_eq_componentImage
#print axioms gluedChainSuffix_last_eq_componentImage
#print axioms gluedChainPrefixZeroHomeomorph
#print axioms gluedChainSuffixLastHomeomorph

end SystolicGrowth.ExerciseGluingPreparation
