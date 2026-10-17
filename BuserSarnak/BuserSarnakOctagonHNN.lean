module

public import BuserSarnak.BuserSarnakHNN

@[expose] public section

namespace SystolicGrowth

noncomputable section

/-! ## The projective octagon group -/

inductive ProjectiveOctagonGenerator where
  | a | c | e1 | e2 | e3 | e4
  deriving DecidableEq

inductive ProjectiveOctagonRelator where
  | e1_sq | e2_sq | e3_sq | e4_sq | polygon
  deriving DecidableEq

def projectiveOctagonRelator :
    ProjectiveOctagonRelator -> FreeGroup ProjectiveOctagonGenerator
  | .e1_sq => FreeGroup.of .e1 ^ 2
  | .e2_sq => FreeGroup.of .e2 ^ 2
  | .e3_sq => FreeGroup.of .e3 ^ 2
  | .e4_sq => FreeGroup.of .e4 ^ 2
  | .polygon => FreeGroup.of .a * FreeGroup.of .e1 *
      (FreeGroup.of .c)⁻¹ * FreeGroup.of .e2 *
      (FreeGroup.of .a)⁻¹ * FreeGroup.of .e3 *
      FreeGroup.of .c * FreeGroup.of .e4

def projectiveOctagonRelators : Set (FreeGroup ProjectiveOctagonGenerator) :=
  Set.range projectiveOctagonRelator

abbrev ProjectiveOctagonGroup := PresentedGroup projectiveOctagonRelators

private lemma projectiveOctagon_relator_eq_one (r : ProjectiveOctagonRelator) :
    PresentedGroup.mk projectiveOctagonRelators
      (projectiveOctagonRelator r) = 1 :=
  PresentedGroup.one_of_mem ⟨r, rfl⟩

@[simp] lemma projectiveOctagon_e1_sq :
    (PresentedGroup.of .e1 : ProjectiveOctagonGroup) ^ 2 = 1 := by
  simpa [PresentedGroup.of, projectiveOctagonRelator] using
    projectiveOctagon_relator_eq_one .e1_sq

@[simp] lemma projectiveOctagon_e2_sq :
    (PresentedGroup.of .e2 : ProjectiveOctagonGroup) ^ 2 = 1 := by
  simpa [PresentedGroup.of, projectiveOctagonRelator] using
    projectiveOctagon_relator_eq_one .e2_sq

@[simp] lemma projectiveOctagon_e3_sq :
    (PresentedGroup.of .e3 : ProjectiveOctagonGroup) ^ 2 = 1 := by
  simpa [PresentedGroup.of, projectiveOctagonRelator] using
    projectiveOctagon_relator_eq_one .e3_sq

@[simp] lemma projectiveOctagon_e4_sq :
    (PresentedGroup.of .e4 : ProjectiveOctagonGroup) ^ 2 = 1 := by
  simpa [PresentedGroup.of, projectiveOctagonRelator] using
    projectiveOctagon_relator_eq_one .e4_sq

lemma projectiveOctagon_polygon :
    (PresentedGroup.of .a : ProjectiveOctagonGroup) *
      PresentedGroup.of .e1 * (PresentedGroup.of .c)⁻¹ *
      PresentedGroup.of .e2 * (PresentedGroup.of .a)⁻¹ *
      PresentedGroup.of .e3 * PresentedGroup.of .c *
      PresentedGroup.of .e4 = 1 := by
  simpa [PresentedGroup.of, projectiveOctagonRelator] using
    projectiveOctagon_relator_eq_one .polygon

/-! ## The octagon-aligned HNN base -/

inductive OctagonBaseGenerator where
  | a | e1 | e2 | e3 | e4
  deriving DecidableEq

inductive OctagonBaseRelator where
  | e1_sq | e2_sq | e3_sq | e4_sq
  deriving DecidableEq

def octagonBaseRelator : OctagonBaseRelator -> FreeGroup OctagonBaseGenerator
  | .e1_sq => FreeGroup.of .e1 ^ 2
  | .e2_sq => FreeGroup.of .e2 ^ 2
  | .e3_sq => FreeGroup.of .e3 ^ 2
  | .e4_sq => FreeGroup.of .e4 ^ 2

def octagonBaseRelators : Set (FreeGroup OctagonBaseGenerator) :=
  Set.range octagonBaseRelator

abbrev OctagonBaseGroup := PresentedGroup octagonBaseRelators

private lemma octagonBase_relator_eq_one (r : OctagonBaseRelator) :
    PresentedGroup.mk octagonBaseRelators (octagonBaseRelator r) = 1 :=
  PresentedGroup.one_of_mem ⟨r, rfl⟩

@[simp] lemma octagonBase_e1_sq :
    (PresentedGroup.of .e1 : OctagonBaseGroup) ^ 2 = 1 := by
  simpa [PresentedGroup.of, octagonBaseRelator] using
    octagonBase_relator_eq_one .e1_sq

@[simp] lemma octagonBase_e2_sq :
    (PresentedGroup.of .e2 : OctagonBaseGroup) ^ 2 = 1 := by
  simpa [PresentedGroup.of, octagonBaseRelator] using
    octagonBase_relator_eq_one .e2_sq

@[simp] lemma octagonBase_e3_sq :
    (PresentedGroup.of .e3 : OctagonBaseGroup) ^ 2 = 1 := by
  simpa [PresentedGroup.of, octagonBaseRelator] using
    octagonBase_relator_eq_one .e3_sq

@[simp] lemma octagonBase_e4_sq :
    (PresentedGroup.of .e4 : OctagonBaseGroup) ^ 2 = 1 := by
  simpa [PresentedGroup.of, octagonBaseRelator] using
    octagonBase_relator_eq_one .e4_sq

def octagonBaseA : OctagonBaseGroup := PresentedGroup.of .a
def octagonBaseE1 : OctagonBaseGroup := PresentedGroup.of .e1
def octagonBaseE2 : OctagonBaseGroup := PresentedGroup.of .e2
def octagonBaseE3 : OctagonBaseGroup := PresentedGroup.of .e3
def octagonBaseE4 : OctagonBaseGroup := PresentedGroup.of .e4

def octagonBaseSourceElement : OctagonBaseGroup :=
  octagonBaseE2 * octagonBaseA⁻¹ * octagonBaseE3

def octagonBaseTargetElement : OctagonBaseGroup :=
  octagonBaseE1⁻¹ * octagonBaseA⁻¹ * octagonBaseE4⁻¹

def octagonBaseExponentImage : OctagonBaseGenerator -> Multiplicative ℤ
  | .a => Multiplicative.ofAdd 1
  | .e1 | .e2 | .e3 | .e4 => 1

lemma octagonBaseExponentImage_relations :
    ∀ r ∈ octagonBaseRelators,
      FreeGroup.lift octagonBaseExponentImage r = 1 := by
  intro r hr
  rcases hr with ⟨i, rfl⟩
  cases i <;> simp [octagonBaseRelator, octagonBaseExponentImage]

def octagonBaseExponent : OctagonBaseGroup →* Multiplicative ℤ :=
  PresentedGroup.toGroup octagonBaseExponentImage_relations

@[simp] lemma octagonBaseExponent_of (x : OctagonBaseGenerator) :
    octagonBaseExponent (PresentedGroup.of x) = octagonBaseExponentImage x :=
  PresentedGroup.toGroup.of octagonBaseExponentImage_relations

private lemma octagon_not_isOfFinOrder_of_exponent_neg_one
    (x : OctagonBaseGroup)
    (hx : octagonBaseExponent x = Multiplicative.ofAdd (-1 : ℤ)) :
    ¬ IsOfFinOrder x := by
  intro h
  obtain ⟨n, hn, hpow⟩ := h.exists_pow_eq_one
  have hm := congrArg octagonBaseExponent hpow
  rw [map_pow, hx, map_one] at hm
  have hm' := congrArg Multiplicative.toAdd hm
  simp at hm'
  omega

@[simp] lemma octagonBaseExponent_source :
    octagonBaseExponent octagonBaseSourceElement =
      Multiplicative.ofAdd (-1 : ℤ) := by
  simp [octagonBaseSourceElement, octagonBaseA, octagonBaseE2,
    octagonBaseE3, octagonBaseExponentImage]

@[simp] lemma octagonBaseExponent_target :
    octagonBaseExponent octagonBaseTargetElement =
      Multiplicative.ofAdd (-1 : ℤ) := by
  simp [octagonBaseTargetElement, octagonBaseA, octagonBaseE1,
    octagonBaseE4, octagonBaseExponentImage]

lemma octagonBaseSourceElement_not_isOfFinOrder :
    ¬ IsOfFinOrder octagonBaseSourceElement :=
  octagon_not_isOfFinOrder_of_exponent_neg_one _ octagonBaseExponent_source

lemma octagonBaseTargetElement_not_isOfFinOrder :
    ¬ IsOfFinOrder octagonBaseTargetElement :=
  octagon_not_isOfFinOrder_of_exponent_neg_one _ octagonBaseExponent_target

def octagonBaseSource : Subgroup OctagonBaseGroup :=
  (zpowersHom OctagonBaseGroup octagonBaseSourceElement).range

def octagonBaseTarget : Subgroup OctagonBaseGroup :=
  (zpowersHom OctagonBaseGroup octagonBaseTargetElement).range

noncomputable def octagonBaseCyclicEquiv :
    octagonBaseSource ≃* octagonBaseTarget :=
  (intEquivZPowersRange octagonBaseSourceElement
    octagonBaseSourceElement_not_isOfFinOrder).symm.trans
  (intEquivZPowersRange octagonBaseTargetElement
    octagonBaseTargetElement_not_isOfFinOrder)

@[simp] lemma octagonBaseCyclicEquiv_apply (n : Multiplicative ℤ) :
    octagonBaseCyclicEquiv
      (intEquivZPowersRange octagonBaseSourceElement
        octagonBaseSourceElement_not_isOfFinOrder n) =
      intEquivZPowersRange octagonBaseTargetElement
        octagonBaseTargetElement_not_isOfFinOrder n := by
  change
    intEquivZPowersRange octagonBaseTargetElement
        octagonBaseTargetElement_not_isOfFinOrder
        ((intEquivZPowersRange octagonBaseSourceElement
          octagonBaseSourceElement_not_isOfFinOrder).symm
          (intEquivZPowersRange octagonBaseSourceElement
            octagonBaseSourceElement_not_isOfFinOrder n)) = _
  rw [(intEquivZPowersRange octagonBaseSourceElement
    octagonBaseSourceElement_not_isOfFinOrder).symm_apply_apply]

abbrev ProjectiveOctagonHNN :=
  HNNExtension OctagonBaseGroup octagonBaseSource octagonBaseTarget
    octagonBaseCyclicEquiv

/-! ## Explicit mutually inverse maps -/

def projectiveOctagonToHNNGenerator :
    ProjectiveOctagonGenerator -> ProjectiveOctagonHNN
  | .a => HNNExtension.of octagonBaseA
  | .c => HNNExtension.t⁻¹
  | .e1 => HNNExtension.of octagonBaseE1
  | .e2 => HNNExtension.of octagonBaseE2
  | .e3 => HNNExtension.of octagonBaseE3
  | .e4 => HNNExtension.of octagonBaseE4

private lemma projectiveOctagonHNN_stable_relation :
    (HNNExtension.t : ProjectiveOctagonHNN) *
        HNNExtension.of octagonBaseSourceElement =
      HNNExtension.of octagonBaseTargetElement * HNNExtension.t := by
  let sourceGenerator : octagonBaseSource :=
    intEquivZPowersRange octagonBaseSourceElement
      octagonBaseSourceElement_not_isOfFinOrder (Multiplicative.ofAdd 1)
  have h := HNNExtension.t_mul_of
    (G := OctagonBaseGroup) (A := octagonBaseSource)
    (B := octagonBaseTarget) (φ := octagonBaseCyclicEquiv) sourceGenerator
  simpa [sourceGenerator] using h

lemma projectiveOctagonToHNNGenerator_relations :
    ∀ r ∈ projectiveOctagonRelators,
      FreeGroup.lift projectiveOctagonToHNNGenerator r = 1 := by
  intro r hr
  rcases hr with ⟨i, rfl⟩
  cases i with
  | e1_sq =>
      change HNNExtension.of octagonBaseE1 ^ 2 = 1
      rw [← map_pow, show octagonBaseE1 ^ 2 = 1 by
        simp [octagonBaseE1], map_one]
  | e2_sq =>
      change HNNExtension.of octagonBaseE2 ^ 2 = 1
      rw [← map_pow, show octagonBaseE2 ^ 2 = 1 by
        simp [octagonBaseE2], map_one]
  | e3_sq =>
      change HNNExtension.of octagonBaseE3 ^ 2 = 1
      rw [← map_pow, show octagonBaseE3 ^ 2 = 1 by
        simp [octagonBaseE3], map_one]
  | e4_sq =>
      change HNNExtension.of octagonBaseE4 ^ 2 = 1
      rw [← map_pow, show octagonBaseE4 ^ 2 = 1 by
        simp [octagonBaseE4], map_one]
  | polygon =>
      change HNNExtension.of octagonBaseA * HNNExtension.of octagonBaseE1 *
        HNNExtension.t * HNNExtension.of octagonBaseE2 *
        (HNNExtension.of octagonBaseA)⁻¹ * HNNExtension.of octagonBaseE3 *
        HNNExtension.t⁻¹ * HNNExtension.of octagonBaseE4 = 1
      rw [show HNNExtension.of octagonBaseA * HNNExtension.of octagonBaseE1 *
          HNNExtension.t * HNNExtension.of octagonBaseE2 *
          (HNNExtension.of octagonBaseA)⁻¹ * HNNExtension.of octagonBaseE3 *
          HNNExtension.t⁻¹ * HNNExtension.of octagonBaseE4 =
          HNNExtension.of octagonBaseA * HNNExtension.of octagonBaseE1 *
            (HNNExtension.t * HNNExtension.of octagonBaseSourceElement) *
            HNNExtension.t⁻¹ * HNNExtension.of octagonBaseE4 by
        simp [octagonBaseSourceElement]
        group]
      rw [projectiveOctagonHNN_stable_relation]
      simp [octagonBaseTargetElement]
      group

def projectiveOctagonToHNN : ProjectiveOctagonGroup →* ProjectiveOctagonHNN :=
  PresentedGroup.toGroup projectiveOctagonToHNNGenerator_relations

def octagonBaseToProjectiveGenerator :
    OctagonBaseGenerator -> ProjectiveOctagonGroup
  | .a => PresentedGroup.of .a
  | .e1 => PresentedGroup.of .e1
  | .e2 => PresentedGroup.of .e2
  | .e3 => PresentedGroup.of .e3
  | .e4 => PresentedGroup.of .e4

lemma octagonBaseToProjectiveGenerator_relations :
    ∀ r ∈ octagonBaseRelators,
      FreeGroup.lift octagonBaseToProjectiveGenerator r = 1 := by
  intro r hr
  rcases hr with ⟨i, rfl⟩
  cases i <;> simp [octagonBaseRelator, octagonBaseToProjectiveGenerator]

def octagonBaseToProjective : OctagonBaseGroup →* ProjectiveOctagonGroup :=
  PresentedGroup.toGroup octagonBaseToProjectiveGenerator_relations

@[simp] lemma octagonBaseToProjective_of (x : OctagonBaseGenerator) :
    octagonBaseToProjective (PresentedGroup.of x) =
      octagonBaseToProjectiveGenerator x :=
  PresentedGroup.toGroup.of octagonBaseToProjectiveGenerator_relations

private lemma projectiveOctagon_stable_relation :
    (PresentedGroup.of .c : ProjectiveOctagonGroup)⁻¹ *
        octagonBaseToProjective octagonBaseSourceElement =
      octagonBaseToProjective octagonBaseTargetElement *
        (PresentedGroup.of .c)⁻¹ := by
  have h := projectiveOctagon_polygon
  calc
    (PresentedGroup.of .c)⁻¹ *
        octagonBaseToProjective octagonBaseSourceElement =
      (PresentedGroup.of .e1)⁻¹ * (PresentedGroup.of .a)⁻¹ *
        (PresentedGroup.of .a * PresentedGroup.of .e1 *
          (PresentedGroup.of .c)⁻¹ * PresentedGroup.of .e2 *
          (PresentedGroup.of .a)⁻¹ * PresentedGroup.of .e3 *
          PresentedGroup.of .c * PresentedGroup.of .e4) *
        (PresentedGroup.of .e4)⁻¹ * (PresentedGroup.of .c)⁻¹ := by
          simp [octagonBaseSourceElement, octagonBaseA, octagonBaseE2,
            octagonBaseE3, octagonBaseToProjective,
            octagonBaseToProjectiveGenerator]
          group
    _ = (PresentedGroup.of .e1)⁻¹ * (PresentedGroup.of .a)⁻¹ *
        (PresentedGroup.of .e4)⁻¹ * (PresentedGroup.of .c)⁻¹ := by
          rw [h]
          simp
    _ = octagonBaseToProjective octagonBaseTargetElement *
        (PresentedGroup.of .c)⁻¹ := by
          simp [octagonBaseTargetElement, octagonBaseA, octagonBaseE1,
            octagonBaseE4, octagonBaseToProjective,
            octagonBaseToProjectiveGenerator]

private lemma projectiveOctagon_stable_relation_zpow (n : ℤ) :
    (PresentedGroup.of .c : ProjectiveOctagonGroup)⁻¹ *
        (octagonBaseToProjective octagonBaseSourceElement) ^ n =
      (octagonBaseToProjective octagonBaseTargetElement) ^ n *
        (PresentedGroup.of .c)⁻¹ := by
  let t : ProjectiveOctagonGroup := (PresentedGroup.of .c)⁻¹
  have hconj :
      (MulAut.conj t) (octagonBaseToProjective octagonBaseSourceElement) =
        octagonBaseToProjective octagonBaseTargetElement := by
    rw [MulAut.conj_apply, projectiveOctagon_stable_relation]
    simp [t]
  have hp' : t * (octagonBaseToProjective octagonBaseSourceElement) ^ n * t⁻¹ =
      (octagonBaseToProjective octagonBaseTargetElement) ^ n := by
    calc
      _ = (MulAut.conj t)
          ((octagonBaseToProjective octagonBaseSourceElement) ^ n) := by
            rw [MulAut.conj_apply]
      _ = ((MulAut.conj t)
          (octagonBaseToProjective octagonBaseSourceElement)) ^ n :=
            map_zpow (MulAut.conj t) _ n
      _ = _ := by rw [hconj]
  change t * (octagonBaseToProjective octagonBaseSourceElement) ^ n =
    (octagonBaseToProjective octagonBaseTargetElement) ^ n * t
  calc
    t * (octagonBaseToProjective octagonBaseSourceElement) ^ n =
      (t * (octagonBaseToProjective octagonBaseSourceElement) ^ n * t⁻¹) * t := by
        group
    _ = _ := by rw [hp']

lemma Internal.BuserSarnakOctagonHNNHelpers.projectiveOctagonHNN_compatibility (x : octagonBaseSource) :
    (PresentedGroup.of .c : ProjectiveOctagonGroup)⁻¹ *
        octagonBaseToProjective (x : OctagonBaseGroup) =
      octagonBaseToProjective
          (octagonBaseCyclicEquiv x : OctagonBaseGroup) *
        (PresentedGroup.of .c)⁻¹ := by
  let n : Multiplicative ℤ :=
    (intEquivZPowersRange octagonBaseSourceElement
      octagonBaseSourceElement_not_isOfFinOrder).symm x
  have hx :
      intEquivZPowersRange octagonBaseSourceElement
          octagonBaseSourceElement_not_isOfFinOrder n = x :=
    (intEquivZPowersRange octagonBaseSourceElement
      octagonBaseSourceElement_not_isOfFinOrder).apply_symm_apply x
  rw [← hx, octagonBaseCyclicEquiv_apply]
  change (PresentedGroup.of .c : ProjectiveOctagonGroup)⁻¹ *
      octagonBaseToProjective (octagonBaseSourceElement ^ n.toAdd) =
    octagonBaseToProjective (octagonBaseTargetElement ^ n.toAdd) *
      (PresentedGroup.of .c)⁻¹
  rw [map_zpow, map_zpow]
  exact projectiveOctagon_stable_relation_zpow n.toAdd

def octagonHNNToProjective : ProjectiveOctagonHNN →* ProjectiveOctagonGroup :=
  HNNExtension.lift octagonBaseToProjective (PresentedGroup.of .c)⁻¹
    Internal.BuserSarnakOctagonHNNHelpers.projectiveOctagonHNN_compatibility

theorem octagonHNNToProjective_comp_projectiveOctagonToHNN :
    octagonHNNToProjective.comp projectiveOctagonToHNN =
      MonoidHom.id ProjectiveOctagonGroup := by
  apply PresentedGroup.ext
  intro x
  cases x <;>
    simp [projectiveOctagonToHNN, projectiveOctagonToHNNGenerator,
      octagonHNNToProjective, octagonBaseToProjective,
      octagonBaseToProjectiveGenerator, octagonBaseA, octagonBaseE1,
      octagonBaseE2, octagonBaseE3, octagonBaseE4]

theorem projectiveOctagonToHNN_comp_octagonHNNToProjective :
    projectiveOctagonToHNN.comp octagonHNNToProjective =
      MonoidHom.id ProjectiveOctagonHNN := by
  apply HNNExtension.hom_ext
  · apply PresentedGroup.ext
    intro x
    cases x <;>
      simp [projectiveOctagonToHNN, projectiveOctagonToHNNGenerator,
        octagonHNNToProjective, octagonBaseToProjective,
        octagonBaseToProjectiveGenerator, octagonBaseA, octagonBaseE1,
        octagonBaseE2, octagonBaseE3, octagonBaseE4]
  · simp [projectiveOctagonToHNN, projectiveOctagonToHNNGenerator,
      octagonHNNToProjective]

/-- The projective octagon presentation in the HNN normal form adapted to
its four disjoint isometric intervals. -/
def projectiveOctagonEquivHNN : ProjectiveOctagonGroup ≃* ProjectiveOctagonHNN where
  toFun := projectiveOctagonToHNN
  invFun := octagonHNNToProjective
  left_inv x := by
    exact DFunLike.congr_fun
      octagonHNNToProjective_comp_projectiveOctagonToHNN x
  right_inv x := by
    exact DFunLike.congr_fun
      projectiveOctagonToHNN_comp_octagonHNNToProjective x
  map_mul' := projectiveOctagonToHNN.map_mul

end

end SystolicGrowth
