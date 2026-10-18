module

public import BuserSarnak.BuserSarnakOctagonHNN

@[expose] public section

/-!
# An explicit transversal for the octagon HNN extension

The exponent homomorphism gives the same canonical right transversal for
both cyclic subgroups in the octagon HNN decomposition.  This replaces the
arbitrary choice in Mathlib's HNN normal form by the concrete exponent-zero
subgroup and makes the remaining boundary ping-pong argument algebraic.
-/

namespace SystolicGrowth

noncomputable section

@[simp] lemma octagonBaseExponent_source_zpow (n : ℤ) :
    Multiplicative.toAdd
        (octagonBaseExponent (octagonBaseSourceElement ^ n)) = -n := by
  rw [map_zpow, octagonBaseExponent_source]
  simp

@[simp] lemma octagonBaseExponent_target_zpow (n : ℤ) :
    Multiplicative.toAdd
        (octagonBaseExponent (octagonBaseTargetElement ^ n)) = -n := by
  rw [map_zpow, octagonBaseExponent_target]
  simp

/-- A source-subgroup element is the unique power prescribed by its
exponent. -/
lemma mem_octagonBaseSource_iff_eq_canonical_zpow
    (g : OctagonBaseGroup) :
    g ∈ octagonBaseSource ↔
      g = octagonBaseSourceElement ^
        (-Multiplicative.toAdd (octagonBaseExponent g)) := by
  change g ∈ Subgroup.zpowers octagonBaseSourceElement ↔ _
  constructor
  · intro hg
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [← hn, octagonBaseExponent_source_zpow]
    simp
  · intro hg
    rw [hg]
    exact Subgroup.zpow_mem_zpowers _ _

/-- A target-subgroup element is the unique power prescribed by its
exponent. -/
lemma mem_octagonBaseTarget_iff_eq_canonical_zpow
    (g : OctagonBaseGroup) :
    g ∈ octagonBaseTarget ↔
      g = octagonBaseTargetElement ^
        (-Multiplicative.toAdd (octagonBaseExponent g)) := by
  change g ∈ Subgroup.zpowers octagonBaseTargetElement ↔ _
  constructor
  · intro hg
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [← hn, octagonBaseExponent_target_zpow]
    simp
  · intro hg
    rw [hg]
    exact Subgroup.zpow_mem_zpowers _ _

/-- The concrete common transversal: base words of exponent zero. -/
def octagonBaseExponentKernel : Subgroup OctagonBaseGroup :=
  octagonBaseExponent.ker

lemma octagonBaseSource_exponent_injective :
    Function.Injective
      (octagonBaseExponent.comp octagonBaseSource.subtype) := by
  intro a b hab
  change octagonBaseExponent (a : OctagonBaseGroup) =
    octagonBaseExponent (b : OctagonBaseGroup) at hab
  apply Subtype.ext
  rw [(mem_octagonBaseSource_iff_eq_canonical_zpow a).mp a.2,
    (mem_octagonBaseSource_iff_eq_canonical_zpow b).mp b.2,
    hab]

lemma octagonBaseTarget_exponent_injective :
    Function.Injective
      (octagonBaseExponent.comp octagonBaseTarget.subtype) := by
  intro a b hab
  change octagonBaseExponent (a : OctagonBaseGroup) =
    octagonBaseExponent (b : OctagonBaseGroup) at hab
  apply Subtype.ext
  rw [(mem_octagonBaseTarget_iff_eq_canonical_zpow a).mp a.2,
    (mem_octagonBaseTarget_iff_eq_canonical_zpow b).mp b.2,
    hab]

/-- Every base element factors uniquely as a source power followed by an
exponent-zero element. -/
lemma octagonBaseSource_isComplement_exponentKernel :
    Subgroup.IsComplement (octagonBaseSource : Set OctagonBaseGroup)
      (octagonBaseExponentKernel : Set OctagonBaseGroup) := by
  rw [Subgroup.isComplement_iff_bijective]
  constructor
  · rintro ⟨a, k⟩ ⟨b, l⟩ h
    have he := congrArg octagonBaseExponent h
    have hk := k.2
    have hl := l.2
    change octagonBaseExponent (k : OctagonBaseGroup) = 1 at hk
    change octagonBaseExponent (l : OctagonBaseGroup) = 1 at hl
    simp only [map_mul, hk, hl, mul_one] at he
    change (octagonBaseExponent.comp octagonBaseSource.subtype) a =
      (octagonBaseExponent.comp octagonBaseSource.subtype) b at he
    have hab : a = b := octagonBaseSource_exponent_injective he
    subst b
    have hkl : (k : OctagonBaseGroup) = l := mul_left_cancel h
    exact Prod.ext rfl (Subtype.ext hkl)
  · intro g
    let e : ℤ := Multiplicative.toAdd (octagonBaseExponent g)
    let a : octagonBaseSource :=
      ⟨octagonBaseSourceElement ^ (-e), by
        change octagonBaseSourceElement ^ (-e) ∈
          Subgroup.zpowers octagonBaseSourceElement
        exact Subgroup.zpow_mem_zpowers _ _⟩
    let k : octagonBaseExponentKernel :=
      ⟨octagonBaseSourceElement ^ e * g, by
        change octagonBaseExponent
            (octagonBaseSourceElement ^ e * g) = 1
        apply Multiplicative.ext
        rw [map_mul, toAdd_mul, octagonBaseExponent_source_zpow]
        simp [e]⟩
    refine ⟨(a, k), ?_⟩
    simp [a, k]

/-- Every base element factors uniquely as a target power followed by the
same exponent-zero transversal. -/
lemma octagonBaseTarget_isComplement_exponentKernel :
    Subgroup.IsComplement (octagonBaseTarget : Set OctagonBaseGroup)
      (octagonBaseExponentKernel : Set OctagonBaseGroup) := by
  rw [Subgroup.isComplement_iff_bijective]
  constructor
  · rintro ⟨a, k⟩ ⟨b, l⟩ h
    have he := congrArg octagonBaseExponent h
    have hk := k.2
    have hl := l.2
    change octagonBaseExponent (k : OctagonBaseGroup) = 1 at hk
    change octagonBaseExponent (l : OctagonBaseGroup) = 1 at hl
    simp only [map_mul, hk, hl, mul_one] at he
    change (octagonBaseExponent.comp octagonBaseTarget.subtype) a =
      (octagonBaseExponent.comp octagonBaseTarget.subtype) b at he
    have hab : a = b := octagonBaseTarget_exponent_injective he
    subst b
    have hkl : (k : OctagonBaseGroup) = l := mul_left_cancel h
    exact Prod.ext rfl (Subtype.ext hkl)
  · intro g
    let e : ℤ := Multiplicative.toAdd (octagonBaseExponent g)
    let a : octagonBaseTarget :=
      ⟨octagonBaseTargetElement ^ (-e), by
        change octagonBaseTargetElement ^ (-e) ∈
          Subgroup.zpowers octagonBaseTargetElement
        exact Subgroup.zpow_mem_zpowers _ _⟩
    let k : octagonBaseExponentKernel :=
      ⟨octagonBaseTargetElement ^ e * g, by
        change octagonBaseExponent
            (octagonBaseTargetElement ^ e * g) = 1
        apply Multiplicative.ext
        rw [map_mul, toAdd_mul, octagonBaseExponent_target_zpow]
        simp [e]⟩
    refine ⟨(a, k), ?_⟩
    simp [a, k]

/-- The same source factorization with the exponent-zero term on the left. -/
lemma octagonBaseExponentKernel_isComplement_source :
    Subgroup.IsComplement
      (octagonBaseExponentKernel : Set OctagonBaseGroup)
      (octagonBaseSource : Set OctagonBaseGroup) := by
  exact Subgroup.IsComplement'.symm
    octagonBaseSource_isComplement_exponentKernel

/-- The same target factorization with the exponent-zero term on the left. -/
lemma octagonBaseExponentKernel_isComplement_target :
    Subgroup.IsComplement
      (octagonBaseExponentKernel : Set OctagonBaseGroup)
      (octagonBaseTarget : Set OctagonBaseGroup) := by
  exact Subgroup.IsComplement'.symm
    octagonBaseTarget_isComplement_exponentKernel

/-- A concrete transversal pair for Mathlib's HNN normal-word API. -/
def octagonHNNExponentTransversalPair :
    HNNExtension.NormalWord.TransversalPair OctagonBaseGroup
      octagonBaseSource octagonBaseTarget where
  set := fun _ => octagonBaseExponentKernel
  compl := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · simpa using octagonBaseSource_isComplement_exponentKernel
    · simpa using octagonBaseTarget_isComplement_exponentKernel

@[simp] lemma octagonHNNExponentTransversalPair_set (u : ℤˣ) :
    octagonHNNExponentTransversalPair.set u =
      (octagonBaseExponentKernel : Set OctagonBaseGroup) :=
  rfl

/-- The resulting explicit normal-word type. -/
abbrev OctagonHNNExponentNormalWord :=
  HNNExtension.NormalWord octagonHNNExponentTransversalPair

/-- Every projective-octagon HNN element has a unique normal word whose
intermediate base coefficients have exponent zero. -/
def projectiveOctagonHNNEquivExponentNormalWord :
    ProjectiveOctagonHNN ≃ OctagonHNNExponentNormalWord :=
  HNNExtension.NormalWord.equiv octagonBaseCyclicEquiv
    octagonHNNExponentTransversalPair

/-- The common transversal meets the source subgroup only at one. -/
lemma mem_octagonBaseSource_of_exponent_eq_one_iff
    {g : OctagonBaseGroup} (hg : octagonBaseExponent g = 1) :
    g ∈ octagonBaseSource ↔ g = 1 := by
  rw [mem_octagonBaseSource_iff_eq_canonical_zpow, hg]
  simp

/-- The common transversal meets the target subgroup only at one. -/
lemma mem_octagonBaseTarget_of_exponent_eq_one_iff
    {g : OctagonBaseGroup} (hg : octagonBaseExponent g = 1) :
    g ∈ octagonBaseTarget ↔ g = 1 := by
  rw [mem_octagonBaseTarget_iff_eq_canonical_zpow, hg]
  simp

/-- Every intermediate coefficient in the explicit HNN normal form has
exponent zero. -/
lemma OctagonHNNExponentNormalWord.coefficient_exponent_eq_one
    (w : OctagonHNNExponentNormalWord) {u : ℤˣ}
    {g : OctagonBaseGroup} (hg : (u, g) ∈ w.toList) :
    octagonBaseExponent g = 1 := by
  have h := w.mem_set u g hg
  change octagonBaseExponent g = 1 at h
  exact h

/-- Consequently, an intermediate coefficient belongs to the associated
subgroup exactly when it is the identity. -/
lemma OctagonHNNExponentNormalWord.coefficient_mem_toSubgroup_iff
    (w : OctagonHNNExponentNormalWord) {u : ℤˣ}
    {g : OctagonBaseGroup} (hg : (u, g) ∈ w.toList) :
    g ∈ HNNExtension.toSubgroup octagonBaseSource octagonBaseTarget u ↔
      g = 1 := by
  have he := w.coefficient_exponent_eq_one hg
  rcases Int.units_eq_one_or u with rfl | rfl
  · simpa using mem_octagonBaseSource_of_exponent_eq_one_iff he
  · simpa using mem_octagonBaseTarget_of_exponent_eq_one_iff he

end

end SystolicGrowth
