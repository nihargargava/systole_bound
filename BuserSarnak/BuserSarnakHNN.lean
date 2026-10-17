module

public import BuserSarnak.BuserSarnakPresentationEquiv
public import Mathlib.GroupTheory.HNNExtension
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace SystolicGrowth

noncomputable section

/-! ## The projective orbifold presentation

After quotienting the central element of the lifted presentation, the full
arithmetic group has signature `(1; 2, 2, 2, 2)`.  This file rewrites that
presentation as an HNN extension.  The resulting Britton normal form is the
algebraic input for the faithfulness proof.
-/

inductive ProjectiveOrbifoldGenerator where
  | a | b | d1 | d2 | d3 | d4
  deriving DecidableEq

inductive ProjectiveOrbifoldRelator where
  | d1_sq | d2_sq | d3_sq | d4_sq | signature
  deriving DecidableEq

def projectiveOrbifoldRelator :
    ProjectiveOrbifoldRelator -> FreeGroup ProjectiveOrbifoldGenerator
  | .d1_sq => FreeGroup.of .d1 ^ 2
  | .d2_sq => FreeGroup.of .d2 ^ 2
  | .d3_sq => FreeGroup.of .d3 ^ 2
  | .d4_sq => FreeGroup.of .d4 ^ 2
  | .signature => FreeGroup.of .a * FreeGroup.of .b *
      (FreeGroup.of .a)⁻¹ * (FreeGroup.of .b)⁻¹ *
      FreeGroup.of .d1 * FreeGroup.of .d2 *
      FreeGroup.of .d3 * FreeGroup.of .d4

def projectiveOrbifoldRelators : Set (FreeGroup ProjectiveOrbifoldGenerator) :=
  Set.range projectiveOrbifoldRelator

abbrev ProjectiveOrbifoldGroup := PresentedGroup projectiveOrbifoldRelators

private lemma projective_relator_eq_one (r : ProjectiveOrbifoldRelator) :
    PresentedGroup.mk projectiveOrbifoldRelators
      (projectiveOrbifoldRelator r) = 1 :=
  PresentedGroup.one_of_mem ⟨r, rfl⟩

@[simp] lemma projectiveOrbifold_d1_sq :
    (PresentedGroup.of .d1 : ProjectiveOrbifoldGroup) ^ 2 = 1 := by
  simpa [PresentedGroup.of, projectiveOrbifoldRelator] using
    projective_relator_eq_one .d1_sq

@[simp] lemma projectiveOrbifold_d2_sq :
    (PresentedGroup.of .d2 : ProjectiveOrbifoldGroup) ^ 2 = 1 := by
  simpa [PresentedGroup.of, projectiveOrbifoldRelator] using
    projective_relator_eq_one .d2_sq

@[simp] lemma projectiveOrbifold_d3_sq :
    (PresentedGroup.of .d3 : ProjectiveOrbifoldGroup) ^ 2 = 1 := by
  simpa [PresentedGroup.of, projectiveOrbifoldRelator] using
    projective_relator_eq_one .d3_sq

@[simp] lemma projectiveOrbifold_d4_sq :
    (PresentedGroup.of .d4 : ProjectiveOrbifoldGroup) ^ 2 = 1 := by
  simpa [PresentedGroup.of, projectiveOrbifoldRelator] using
    projective_relator_eq_one .d4_sq

lemma projectiveOrbifold_signature :
    (PresentedGroup.of .a : ProjectiveOrbifoldGroup) *
      PresentedGroup.of .b * (PresentedGroup.of .a)⁻¹ *
      (PresentedGroup.of .b)⁻¹ * PresentedGroup.of .d1 *
      PresentedGroup.of .d2 * PresentedGroup.of .d3 *
      PresentedGroup.of .d4 = 1 := by
  simpa [PresentedGroup.of, projectiveOrbifoldRelator] using
    projective_relator_eq_one .signature

/-! ## The base group of the HNN extension -/

inductive OrbifoldBaseGenerator where
  | a | d1 | d2 | d3 | d4
  deriving DecidableEq

inductive OrbifoldBaseRelator where
  | d1_sq | d2_sq | d3_sq | d4_sq
  deriving DecidableEq

def orbifoldBaseRelator : OrbifoldBaseRelator -> FreeGroup OrbifoldBaseGenerator
  | .d1_sq => FreeGroup.of .d1 ^ 2
  | .d2_sq => FreeGroup.of .d2 ^ 2
  | .d3_sq => FreeGroup.of .d3 ^ 2
  | .d4_sq => FreeGroup.of .d4 ^ 2

def orbifoldBaseRelators : Set (FreeGroup OrbifoldBaseGenerator) :=
  Set.range orbifoldBaseRelator

abbrev OrbifoldBaseGroup := PresentedGroup orbifoldBaseRelators

private lemma orbifoldBase_relator_eq_one (r : OrbifoldBaseRelator) :
    PresentedGroup.mk orbifoldBaseRelators (orbifoldBaseRelator r) = 1 :=
  PresentedGroup.one_of_mem ⟨r, rfl⟩

@[simp] lemma orbifoldBase_d1_sq :
    (PresentedGroup.of .d1 : OrbifoldBaseGroup) ^ 2 = 1 := by
  simpa [PresentedGroup.of, orbifoldBaseRelator] using
    orbifoldBase_relator_eq_one .d1_sq

@[simp] lemma orbifoldBase_d2_sq :
    (PresentedGroup.of .d2 : OrbifoldBaseGroup) ^ 2 = 1 := by
  simpa [PresentedGroup.of, orbifoldBaseRelator] using
    orbifoldBase_relator_eq_one .d2_sq

@[simp] lemma orbifoldBase_d3_sq :
    (PresentedGroup.of .d3 : OrbifoldBaseGroup) ^ 2 = 1 := by
  simpa [PresentedGroup.of, orbifoldBaseRelator] using
    orbifoldBase_relator_eq_one .d3_sq

@[simp] lemma orbifoldBase_d4_sq :
    (PresentedGroup.of .d4 : OrbifoldBaseGroup) ^ 2 = 1 := by
  simpa [PresentedGroup.of, orbifoldBaseRelator] using
    orbifoldBase_relator_eq_one .d4_sq

def orbifoldBaseA : OrbifoldBaseGroup := PresentedGroup.of .a

def orbifoldBaseD : OrbifoldBaseGroup :=
  PresentedGroup.of .d1 * PresentedGroup.of .d2 *
    PresentedGroup.of .d3 * PresentedGroup.of .d4

def orbifoldBaseSourceElement : OrbifoldBaseGroup := orbifoldBaseA⁻¹

def orbifoldBaseTargetElement : OrbifoldBaseGroup :=
  orbifoldBaseA⁻¹ * orbifoldBaseD⁻¹

def orbifoldBaseExponentImage :
    OrbifoldBaseGenerator -> Multiplicative ℤ
  | .a => Multiplicative.ofAdd 1
  | .d1 | .d2 | .d3 | .d4 => 1

lemma orbifoldBaseExponentImage_relations :
    ∀ r ∈ orbifoldBaseRelators,
      FreeGroup.lift orbifoldBaseExponentImage r = 1 := by
  intro r hr
  rcases hr with ⟨i, rfl⟩
  cases i <;> simp [orbifoldBaseRelator, orbifoldBaseExponentImage]

def orbifoldBaseExponent : OrbifoldBaseGroup →* Multiplicative ℤ :=
  PresentedGroup.toGroup orbifoldBaseExponentImage_relations

@[simp] lemma orbifoldBaseExponent_of (x : OrbifoldBaseGenerator) :
    orbifoldBaseExponent (PresentedGroup.of x) = orbifoldBaseExponentImage x :=
  PresentedGroup.toGroup.of orbifoldBaseExponentImage_relations

private lemma not_isOfFinOrder_of_exponent_neg_one
    {G : Type*} [Group G] (f : G →* Multiplicative ℤ) (x : G)
    (hx : f x = Multiplicative.ofAdd (-1 : ℤ)) :
    ¬ IsOfFinOrder x := by
  intro h
  obtain ⟨n, hn, hpow⟩ := h.exists_pow_eq_one
  have hm := congrArg f hpow
  rw [map_pow, hx, map_one] at hm
  have hm' := congrArg Multiplicative.toAdd hm
  simp at hm'
  omega

@[simp] lemma orbifoldBaseExponent_source :
    orbifoldBaseExponent orbifoldBaseSourceElement =
      Multiplicative.ofAdd (-1 : ℤ) := by
  simp [orbifoldBaseSourceElement, orbifoldBaseA,
    orbifoldBaseExponentImage]

@[simp] lemma orbifoldBaseExponent_target :
    orbifoldBaseExponent orbifoldBaseTargetElement =
      Multiplicative.ofAdd (-1 : ℤ) := by
  simp [orbifoldBaseTargetElement, orbifoldBaseA, orbifoldBaseD,
    orbifoldBaseExponentImage]

lemma orbifoldBaseSourceElement_not_isOfFinOrder :
    ¬ IsOfFinOrder orbifoldBaseSourceElement :=
  not_isOfFinOrder_of_exponent_neg_one orbifoldBaseExponent _
    orbifoldBaseExponent_source

lemma orbifoldBaseTargetElement_not_isOfFinOrder :
    ¬ IsOfFinOrder orbifoldBaseTargetElement :=
  not_isOfFinOrder_of_exponent_neg_one orbifoldBaseExponent _
    orbifoldBaseExponent_target

noncomputable def intEquivZPowersRange
    {G : Type*} [Group G] (x : G) (hx : ¬ IsOfFinOrder x) :
    Multiplicative ℤ ≃* (zpowersHom G x).range :=
  MulEquiv.ofBijective (zpowersHom G x).rangeRestrict ⟨by
    rw [MonoidHom.rangeRestrict_injective_iff]
    exact injective_zpow_iff_not_isOfFinOrder.mpr hx,
    (zpowersHom G x).rangeRestrict_surjective⟩

@[simp] lemma coe_intEquivZPowersRange
    {G : Type*} [Group G] (x : G) (hx : ¬ IsOfFinOrder x)
    (n : Multiplicative ℤ) :
    ((intEquivZPowersRange x hx n : (zpowersHom G x).range) : G) =
      x ^ n.toAdd := rfl

def orbifoldBaseSource : Subgroup OrbifoldBaseGroup :=
  (zpowersHom OrbifoldBaseGroup orbifoldBaseSourceElement).range

def orbifoldBaseTarget : Subgroup OrbifoldBaseGroup :=
  (zpowersHom OrbifoldBaseGroup orbifoldBaseTargetElement).range

noncomputable def orbifoldBaseCyclicEquiv :
    orbifoldBaseSource ≃* orbifoldBaseTarget :=
  (intEquivZPowersRange orbifoldBaseSourceElement
    orbifoldBaseSourceElement_not_isOfFinOrder).symm.trans
  (intEquivZPowersRange orbifoldBaseTargetElement
    orbifoldBaseTargetElement_not_isOfFinOrder)

@[simp] lemma orbifoldBaseCyclicEquiv_apply
    (n : Multiplicative ℤ) :
    orbifoldBaseCyclicEquiv
      (intEquivZPowersRange orbifoldBaseSourceElement
        orbifoldBaseSourceElement_not_isOfFinOrder n) =
      intEquivZPowersRange orbifoldBaseTargetElement
        orbifoldBaseTargetElement_not_isOfFinOrder n := by
  change
    intEquivZPowersRange orbifoldBaseTargetElement
        orbifoldBaseTargetElement_not_isOfFinOrder
        ((intEquivZPowersRange orbifoldBaseSourceElement
          orbifoldBaseSourceElement_not_isOfFinOrder).symm
          (intEquivZPowersRange orbifoldBaseSourceElement
            orbifoldBaseSourceElement_not_isOfFinOrder n)) = _
  rw [(intEquivZPowersRange orbifoldBaseSourceElement
    orbifoldBaseSourceElement_not_isOfFinOrder).symm_apply_apply]

abbrev ProjectiveOrbifoldHNN :=
  HNNExtension OrbifoldBaseGroup orbifoldBaseSource orbifoldBaseTarget
    orbifoldBaseCyclicEquiv

/-! ## From the projective presentation to the HNN extension -/

def projectiveToHNNGenerator :
    ProjectiveOrbifoldGenerator -> ProjectiveOrbifoldHNN
  | .a => HNNExtension.of orbifoldBaseA
  | .b => HNNExtension.t
  | .d1 => HNNExtension.of (PresentedGroup.of .d1)
  | .d2 => HNNExtension.of (PresentedGroup.of .d2)
  | .d3 => HNNExtension.of (PresentedGroup.of .d3)
  | .d4 => HNNExtension.of (PresentedGroup.of .d4)

private lemma projectiveHNN_stable_relation :
    (HNNExtension.t : ProjectiveOrbifoldHNN) *
        HNNExtension.of orbifoldBaseSourceElement =
      HNNExtension.of orbifoldBaseTargetElement * HNNExtension.t := by
  let sourceGenerator : orbifoldBaseSource :=
    intEquivZPowersRange orbifoldBaseSourceElement
      orbifoldBaseSourceElement_not_isOfFinOrder (Multiplicative.ofAdd 1)
  have h := HNNExtension.t_mul_of
    (G := OrbifoldBaseGroup) (A := orbifoldBaseSource)
    (B := orbifoldBaseTarget) (φ := orbifoldBaseCyclicEquiv) sourceGenerator
  simpa [sourceGenerator] using h

lemma projectiveToHNNGenerator_relations :
    ∀ r ∈ projectiveOrbifoldRelators,
      FreeGroup.lift projectiveToHNNGenerator r = 1 := by
  intro r hr
  rcases hr with ⟨i, rfl⟩
  cases i with
  | d1_sq =>
      change HNNExtension.of
        (PresentedGroup.of OrbifoldBaseGenerator.d1) ^ 2 = 1
      rw [← map_pow, orbifoldBase_d1_sq, map_one]
  | d2_sq =>
      change HNNExtension.of
        (PresentedGroup.of OrbifoldBaseGenerator.d2) ^ 2 = 1
      rw [← map_pow, orbifoldBase_d2_sq, map_one]
  | d3_sq =>
      change HNNExtension.of
        (PresentedGroup.of OrbifoldBaseGenerator.d3) ^ 2 = 1
      rw [← map_pow, orbifoldBase_d3_sq, map_one]
  | d4_sq =>
      change HNNExtension.of
        (PresentedGroup.of OrbifoldBaseGenerator.d4) ^ 2 = 1
      rw [← map_pow, orbifoldBase_d4_sq, map_one]
  | signature =>
      change HNNExtension.of orbifoldBaseA * HNNExtension.t *
        (HNNExtension.of orbifoldBaseA)⁻¹ * HNNExtension.t⁻¹ *
        HNNExtension.of (PresentedGroup.of .d1) *
        HNNExtension.of (PresentedGroup.of .d2) *
        HNNExtension.of (PresentedGroup.of .d3) *
        HNNExtension.of (PresentedGroup.of .d4) = 1
      rw [show HNNExtension.of orbifoldBaseA * HNNExtension.t *
          (HNNExtension.of orbifoldBaseA)⁻¹ * HNNExtension.t⁻¹ *
          HNNExtension.of (PresentedGroup.of .d1) *
          HNNExtension.of (PresentedGroup.of .d2) *
          HNNExtension.of (PresentedGroup.of .d3) *
          HNNExtension.of (PresentedGroup.of .d4) =
          HNNExtension.of orbifoldBaseA *
            (HNNExtension.t * HNNExtension.of orbifoldBaseSourceElement) *
            HNNExtension.t⁻¹ * HNNExtension.of orbifoldBaseD by
        simp [orbifoldBaseSourceElement, orbifoldBaseD]
        group]
      rw [projectiveHNN_stable_relation]
      simp [orbifoldBaseTargetElement, orbifoldBaseD]
      group

def projectiveOrbifoldToHNN :
    ProjectiveOrbifoldGroup →* ProjectiveOrbifoldHNN :=
  PresentedGroup.toGroup projectiveToHNNGenerator_relations

/-! ## From the HNN extension to the projective presentation -/

def orbifoldBaseToProjectiveGenerator :
    OrbifoldBaseGenerator -> ProjectiveOrbifoldGroup
  | .a => PresentedGroup.of .a
  | .d1 => PresentedGroup.of .d1
  | .d2 => PresentedGroup.of .d2
  | .d3 => PresentedGroup.of .d3
  | .d4 => PresentedGroup.of .d4

lemma orbifoldBaseToProjectiveGenerator_relations :
    ∀ r ∈ orbifoldBaseRelators,
      FreeGroup.lift orbifoldBaseToProjectiveGenerator r = 1 := by
  intro r hr
  rcases hr with ⟨i, rfl⟩
  cases i <;>
    simp [orbifoldBaseRelator, orbifoldBaseToProjectiveGenerator]

def orbifoldBaseToProjective : OrbifoldBaseGroup →* ProjectiveOrbifoldGroup :=
  PresentedGroup.toGroup orbifoldBaseToProjectiveGenerator_relations

@[simp] lemma orbifoldBaseToProjective_of (x : OrbifoldBaseGenerator) :
    orbifoldBaseToProjective (PresentedGroup.of x) =
      orbifoldBaseToProjectiveGenerator x :=
  PresentedGroup.toGroup.of orbifoldBaseToProjectiveGenerator_relations

private lemma projective_stable_relation :
    (PresentedGroup.of .b : ProjectiveOrbifoldGroup) *
        orbifoldBaseToProjective orbifoldBaseSourceElement =
      orbifoldBaseToProjective orbifoldBaseTargetElement *
        PresentedGroup.of .b := by
  have h := projectiveOrbifold_signature
  calc
    PresentedGroup.of .b *
        orbifoldBaseToProjective orbifoldBaseSourceElement =
      (PresentedGroup.of .a)⁻¹ *
        ((PresentedGroup.of .a * PresentedGroup.of .b *
          (PresentedGroup.of .a)⁻¹ * (PresentedGroup.of .b)⁻¹ *
          PresentedGroup.of .d1 * PresentedGroup.of .d2 *
          PresentedGroup.of .d3 * PresentedGroup.of .d4)) *
        (PresentedGroup.of .d1 * PresentedGroup.of .d2 *
          PresentedGroup.of .d3 * PresentedGroup.of .d4)⁻¹ *
        PresentedGroup.of .b := by
          simp [orbifoldBaseSourceElement, orbifoldBaseA,
            orbifoldBaseToProjective, orbifoldBaseToProjectiveGenerator]
          group
    _ = (PresentedGroup.of .a)⁻¹ *
        (PresentedGroup.of .d1 * PresentedGroup.of .d2 *
          PresentedGroup.of .d3 * PresentedGroup.of .d4)⁻¹ *
        PresentedGroup.of .b := by rw [h]; simp
    _ = orbifoldBaseToProjective orbifoldBaseTargetElement *
        PresentedGroup.of .b := by
          simp [orbifoldBaseTargetElement, orbifoldBaseA, orbifoldBaseD,
            orbifoldBaseToProjective, orbifoldBaseToProjectiveGenerator]

private lemma projective_stable_relation_zpow (n : ℤ) :
    (PresentedGroup.of .b : ProjectiveOrbifoldGroup) *
        (orbifoldBaseToProjective orbifoldBaseSourceElement) ^ n =
      (orbifoldBaseToProjective orbifoldBaseTargetElement) ^ n *
        PresentedGroup.of .b := by
  have hconj :
      (MulAut.conj (PresentedGroup.of .b : ProjectiveOrbifoldGroup))
          (orbifoldBaseToProjective orbifoldBaseSourceElement) =
        orbifoldBaseToProjective orbifoldBaseTargetElement := by
    rw [MulAut.conj_apply, projective_stable_relation]
    group
  have hp' :
      (PresentedGroup.of .b : ProjectiveOrbifoldGroup) *
          (orbifoldBaseToProjective orbifoldBaseSourceElement) ^ n *
          (PresentedGroup.of .b)⁻¹ =
        (orbifoldBaseToProjective orbifoldBaseTargetElement) ^ n := by
    calc
      _ = (MulAut.conj (PresentedGroup.of .b : ProjectiveOrbifoldGroup))
          ((orbifoldBaseToProjective orbifoldBaseSourceElement) ^ n) := by
            rw [MulAut.conj_apply]
      _ = ((MulAut.conj (PresentedGroup.of .b : ProjectiveOrbifoldGroup))
          (orbifoldBaseToProjective orbifoldBaseSourceElement)) ^ n :=
            map_zpow (MulAut.conj
              (PresentedGroup.of .b : ProjectiveOrbifoldGroup)) _ n
      _ = _ := by rw [hconj]
  calc
    PresentedGroup.of .b *
        (orbifoldBaseToProjective orbifoldBaseSourceElement) ^ n =
      (PresentedGroup.of .b *
        (orbifoldBaseToProjective orbifoldBaseSourceElement) ^ n *
        (PresentedGroup.of .b)⁻¹) * PresentedGroup.of .b := by group
    _ = _ := by rw [hp']

lemma Internal.BuserSarnakHNNHelpers.hnnToProjective_compatibility (x : orbifoldBaseSource) :
    (PresentedGroup.of .b : ProjectiveOrbifoldGroup) *
        orbifoldBaseToProjective (x : OrbifoldBaseGroup) =
      orbifoldBaseToProjective
          (orbifoldBaseCyclicEquiv x : OrbifoldBaseGroup) *
        PresentedGroup.of .b := by
  let n : Multiplicative ℤ :=
    (intEquivZPowersRange orbifoldBaseSourceElement
      orbifoldBaseSourceElement_not_isOfFinOrder).symm x
  have hx :
      intEquivZPowersRange orbifoldBaseSourceElement
          orbifoldBaseSourceElement_not_isOfFinOrder n = x :=
    (intEquivZPowersRange orbifoldBaseSourceElement
      orbifoldBaseSourceElement_not_isOfFinOrder).apply_symm_apply x
  rw [← hx, orbifoldBaseCyclicEquiv_apply]
  change (PresentedGroup.of .b : ProjectiveOrbifoldGroup) *
      orbifoldBaseToProjective (orbifoldBaseSourceElement ^ n.toAdd) =
    orbifoldBaseToProjective (orbifoldBaseTargetElement ^ n.toAdd) *
      PresentedGroup.of .b
  rw [map_zpow, map_zpow]
  exact projective_stable_relation_zpow n.toAdd

def hnnToProjectiveOrbifold :
    ProjectiveOrbifoldHNN →* ProjectiveOrbifoldGroup :=
  HNNExtension.lift orbifoldBaseToProjective (PresentedGroup.of .b)
    Internal.BuserSarnakHNNHelpers.hnnToProjective_compatibility

theorem hnnToProjective_comp_projectiveToHNN :
    hnnToProjectiveOrbifold.comp projectiveOrbifoldToHNN =
      MonoidHom.id ProjectiveOrbifoldGroup := by
  apply PresentedGroup.ext
  intro x
  cases x <;>
    simp [projectiveOrbifoldToHNN, projectiveToHNNGenerator,
      hnnToProjectiveOrbifold, orbifoldBaseA,
      orbifoldBaseToProjective, orbifoldBaseToProjectiveGenerator]

theorem projectiveToHNN_comp_hnnToProjective :
    projectiveOrbifoldToHNN.comp hnnToProjectiveOrbifold =
      MonoidHom.id ProjectiveOrbifoldHNN := by
  apply HNNExtension.hom_ext
  · apply PresentedGroup.ext
    intro x
    cases x <;>
      simp [projectiveOrbifoldToHNN, projectiveToHNNGenerator,
        hnnToProjectiveOrbifold, orbifoldBaseToProjective,
        orbifoldBaseToProjectiveGenerator, orbifoldBaseA]
  · simp [projectiveOrbifoldToHNN, projectiveToHNNGenerator,
      hnnToProjectiveOrbifold]

/-- The signature `(1; 2, 2, 2, 2)` presentation is the HNN extension of
`<a> * C2 * C2 * C2 * C2` along the two displayed infinite cyclic subgroups. -/
def projectiveOrbifoldEquivHNN :
    ProjectiveOrbifoldGroup ≃* ProjectiveOrbifoldHNN where
  toFun := projectiveOrbifoldToHNN
  invFun := hnnToProjectiveOrbifold
  left_inv x := by
    exact DFunLike.congr_fun hnnToProjective_comp_projectiveToHNN x
  right_inv x := by
    exact DFunLike.congr_fun projectiveToHNN_comp_hnnToProjective x
  map_mul' := projectiveOrbifoldToHNN.map_mul

end

end SystolicGrowth
