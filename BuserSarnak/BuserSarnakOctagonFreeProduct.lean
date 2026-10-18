module

public import BuserSarnak.BuserSarnakOctagonHNN
public import Mathlib.GroupTheory.CoprodI

@[expose] public section

namespace SystolicGrowth

noncomputable section

open scoped MatrixGroups

inductive OctagonBaseFactor where
  | handle | cone1 | cone2 | cone3 | cone4
  deriving DecidableEq

def octagonBaseFactorElement : OctagonBaseFactor -> OctagonBaseGroup
  | .handle => octagonBaseA
  | .cone1 => octagonBaseE1
  | .cone2 => octagonBaseE2
  | .cone3 => octagonBaseE3
  | .cone4 => octagonBaseE4

abbrev OctagonBaseFactorGroup (i : OctagonBaseFactor) : Type :=
  Subgroup.zpowers (octagonBaseFactorElement i)

instance (i : OctagonBaseFactor) : Group (OctagonBaseFactorGroup i) :=
  inferInstance

abbrev OctagonBaseFreeProduct := Monoid.CoprodI OctagonBaseFactorGroup

def octagonBaseFactorGenerator (i : OctagonBaseFactor) :
    OctagonBaseFactorGroup i :=
  ⟨octagonBaseFactorElement i, ⟨Multiplicative.ofAdd 1, by
    change octagonBaseFactorElement i ^ (1 : ℤ) = octagonBaseFactorElement i
    simp⟩⟩

def octagonBaseFactorInclusion (i : OctagonBaseFactor) :
    OctagonBaseFactorGroup i →* OctagonBaseGroup :=
  (Subgroup.zpowers (octagonBaseFactorElement i)).subtype

def octagonBaseFreeProductToBase :
    OctagonBaseFreeProduct →* OctagonBaseGroup :=
  Monoid.CoprodI.lift octagonBaseFactorInclusion

@[simp] lemma octagonBaseFreeProductToBase_of
    (i : OctagonBaseFactor) (x : OctagonBaseFactorGroup i) :
    octagonBaseFreeProductToBase (Monoid.CoprodI.of x) = x := by
  simp [octagonBaseFreeProductToBase, octagonBaseFactorInclusion]

@[simp] lemma octagonBaseFreeProductToBase_of_factorGenerator
    (i : OctagonBaseFactor) :
    octagonBaseFreeProductToBase
        (Monoid.CoprodI.of (octagonBaseFactorGenerator i)) =
      octagonBaseFactorElement i := by
  rw [octagonBaseFreeProductToBase_of]
  rfl

def octagonBaseToFreeProductGenerator :
    OctagonBaseGenerator -> OctagonBaseFreeProduct
  | .a => Monoid.CoprodI.of (octagonBaseFactorGenerator .handle)
  | .e1 => Monoid.CoprodI.of (octagonBaseFactorGenerator .cone1)
  | .e2 => Monoid.CoprodI.of (octagonBaseFactorGenerator .cone2)
  | .e3 => Monoid.CoprodI.of (octagonBaseFactorGenerator .cone3)
  | .e4 => Monoid.CoprodI.of (octagonBaseFactorGenerator .cone4)

lemma octagonBaseToFreeProductGenerator_relations :
    ∀ r ∈ octagonBaseRelators,
      FreeGroup.lift octagonBaseToFreeProductGenerator r = 1 := by
  intro r hr
  rcases hr with ⟨i, rfl⟩
  cases i with
  | e1_sq =>
      change (Monoid.CoprodI.of
        (octagonBaseFactorGenerator .cone1)) ^ 2 = 1
      rw [← map_pow]
      have h : (octagonBaseFactorGenerator .cone1) ^ 2 = 1 := by
        apply Subtype.ext
        change (PresentedGroup.of OctagonBaseGenerator.e1 :
          OctagonBaseGroup) ^ 2 = 1
        exact octagonBase_e1_sq
      rw [h, map_one]
  | e2_sq =>
      change (Monoid.CoprodI.of
        (octagonBaseFactorGenerator .cone2)) ^ 2 = 1
      rw [← map_pow]
      have h : (octagonBaseFactorGenerator .cone2) ^ 2 = 1 := by
        apply Subtype.ext
        change (PresentedGroup.of OctagonBaseGenerator.e2 :
          OctagonBaseGroup) ^ 2 = 1
        exact octagonBase_e2_sq
      rw [h, map_one]
  | e3_sq =>
      change (Monoid.CoprodI.of
        (octagonBaseFactorGenerator .cone3)) ^ 2 = 1
      rw [← map_pow]
      have h : (octagonBaseFactorGenerator .cone3) ^ 2 = 1 := by
        apply Subtype.ext
        change (PresentedGroup.of OctagonBaseGenerator.e3 :
          OctagonBaseGroup) ^ 2 = 1
        exact octagonBase_e3_sq
      rw [h, map_one]
  | e4_sq =>
      change (Monoid.CoprodI.of
        (octagonBaseFactorGenerator .cone4)) ^ 2 = 1
      rw [← map_pow]
      have h : (octagonBaseFactorGenerator .cone4) ^ 2 = 1 := by
        apply Subtype.ext
        change (PresentedGroup.of OctagonBaseGenerator.e4 :
          OctagonBaseGroup) ^ 2 = 1
        exact octagonBase_e4_sq
      rw [h, map_one]

def octagonBaseToFreeProduct : OctagonBaseGroup →* OctagonBaseFreeProduct :=
  PresentedGroup.toGroup octagonBaseToFreeProductGenerator_relations

@[simp] lemma octagonBaseToFreeProduct_of (x : OctagonBaseGenerator) :
    octagonBaseToFreeProduct (PresentedGroup.of x) =
      octagonBaseToFreeProductGenerator x :=
  PresentedGroup.toGroup.of octagonBaseToFreeProductGenerator_relations

@[simp] lemma octagonBaseToFreeProduct_factorElement
    (i : OctagonBaseFactor) :
    octagonBaseToFreeProduct (octagonBaseFactorElement i) =
      Monoid.CoprodI.of (octagonBaseFactorGenerator i) := by
  cases i <;>
    simp [octagonBaseFactorElement, octagonBaseFactorGenerator,
      octagonBaseToFreeProduct, octagonBaseToFreeProductGenerator,
      octagonBaseA, octagonBaseE1, octagonBaseE2, octagonBaseE3,
      octagonBaseE4]

theorem octagonBaseFreeProductToBase_comp_baseToFreeProduct :
    octagonBaseFreeProductToBase.comp octagonBaseToFreeProduct =
      MonoidHom.id OctagonBaseGroup := by
  apply PresentedGroup.ext
  intro x
  cases x with
  | a =>
      simpa [octagonBaseToFreeProductGenerator, octagonBaseFactorElement,
        octagonBaseA] using
        (octagonBaseFreeProductToBase_of_factorGenerator .handle)
  | e1 =>
      simpa [octagonBaseToFreeProductGenerator, octagonBaseFactorElement,
        octagonBaseE1] using
        (octagonBaseFreeProductToBase_of_factorGenerator .cone1)
  | e2 =>
      simpa [octagonBaseToFreeProductGenerator, octagonBaseFactorElement,
        octagonBaseE2] using
        (octagonBaseFreeProductToBase_of_factorGenerator .cone2)
  | e3 =>
      simpa [octagonBaseToFreeProductGenerator, octagonBaseFactorElement,
        octagonBaseE3] using
        (octagonBaseFreeProductToBase_of_factorGenerator .cone3)
  | e4 =>
      simpa [octagonBaseToFreeProductGenerator, octagonBaseFactorElement,
        octagonBaseE4] using
        (octagonBaseFreeProductToBase_of_factorGenerator .cone4)

theorem octagonBaseToFreeProduct_comp_freeProductToBase :
    octagonBaseToFreeProduct.comp octagonBaseFreeProductToBase =
      MonoidHom.id OctagonBaseFreeProduct := by
  apply Monoid.CoprodI.ext_hom
  intro i
  ext x
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
  rcases x with ⟨x, ⟨n, hn⟩⟩
  subst x
  rw [octagonBaseFreeProductToBase_of]
  let y : OctagonBaseFactorGroup i :=
    ⟨octagonBaseFactorElement i ^ n, ⟨n, rfl⟩⟩
  change octagonBaseToFreeProduct (octagonBaseFactorElement i ^ n) =
    Monoid.CoprodI.of y
  have hy : y = (octagonBaseFactorGenerator i) ^ n := by
    apply Subtype.ext
    rfl
  calc
    octagonBaseToFreeProduct (octagonBaseFactorElement i ^ n) =
        (octagonBaseToFreeProduct (octagonBaseFactorElement i)) ^ n :=
      map_zpow octagonBaseToFreeProduct _ _
    _ = (Monoid.CoprodI.of (octagonBaseFactorGenerator i)) ^ n := by
      rw [octagonBaseToFreeProduct_factorElement]
    _ = Monoid.CoprodI.of ((octagonBaseFactorGenerator i) ^ n) := by
      rw [map_zpow]
    _ = Monoid.CoprodI.of y := by
      rw [hy]

/-- The octagon HNN base is exactly the free product of its handle cyclic
factor and its four order-two cone factors. -/
def octagonBaseEquivFreeProduct :
    OctagonBaseGroup ≃* OctagonBaseFreeProduct where
  toFun := octagonBaseToFreeProduct
  invFun := octagonBaseFreeProductToBase
  left_inv x := by
    exact DFunLike.congr_fun
      octagonBaseFreeProductToBase_comp_baseToFreeProduct x
  right_inv x := by
    exact DFunLike.congr_fun
      octagonBaseToFreeProduct_comp_freeProductToBase x
  map_mul' := octagonBaseToFreeProduct.map_mul

/-! ## Removing the central lift

The lifted octagon presentation is a central double cover of the projective
octagon presentation.  This module makes that statement exact and isolates
the remaining faithfulness problem for the quaternion realization at the
projective level.
-/

def liftedOctagonToProjectiveGenerator :
    OctagonPresentationGenerator → ProjectiveOctagonGroup
  | .z => 1
  | .a => PresentedGroup.of .a
  | .c => PresentedGroup.of .c
  | .e1 => PresentedGroup.of .e1
  | .e2 => PresentedGroup.of .e2
  | .e3 => PresentedGroup.of .e3
  | .e4 => PresentedGroup.of .e4

lemma liftedOctagonToProjectiveGenerator_relations :
    ∀ r ∈ octagonPresentationRelators,
      FreeGroup.lift liftedOctagonToProjectiveGenerator r = 1 := by
  intro r hr
  rcases hr with ⟨i, rfl⟩
  cases i with
  | z_sq => simp [octagonPresentationRelator, liftedOctagonToProjectiveGenerator]
  | z_comm_a => simp [octagonPresentationRelator, liftedOctagonToProjectiveGenerator]
  | z_comm_c => simp [octagonPresentationRelator, liftedOctagonToProjectiveGenerator]
  | e1_sq => simp [octagonPresentationRelator, liftedOctagonToProjectiveGenerator]
  | e2_sq => simp [octagonPresentationRelator, liftedOctagonToProjectiveGenerator]
  | e3_sq => simp [octagonPresentationRelator, liftedOctagonToProjectiveGenerator]
  | e4_sq => simp [octagonPresentationRelator, liftedOctagonToProjectiveGenerator]
  | polygon =>
      simpa [octagonPresentationRelator, liftedOctagonToProjectiveGenerator] using
        projectiveOctagon_polygon

/-- Kill the central lift generator in the lifted octagon presentation. -/
def liftedOctagonToProjective : LiftedOctagonGroup →* ProjectiveOctagonGroup :=
  PresentedGroup.toGroup liftedOctagonToProjectiveGenerator_relations

@[simp] lemma liftedOctagonToProjective_of (x : OctagonPresentationGenerator) :
    liftedOctagonToProjective (PresentedGroup.of x) =
      liftedOctagonToProjectiveGenerator x :=
  PresentedGroup.toGroup.of liftedOctagonToProjectiveGenerator_relations

theorem liftedOctagonToProjective_surjective :
    Function.Surjective liftedOctagonToProjective := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← PresentedGroup.closure_range_of projectiveOctagonRelators]
  apply (Subgroup.closure_le _).2
  rintro _ ⟨x, rfl⟩
  cases x with
  | a => exact ⟨PresentedGroup.of .a, by simp [liftedOctagonToProjectiveGenerator]⟩
  | c => exact ⟨PresentedGroup.of .c, by simp [liftedOctagonToProjectiveGenerator]⟩
  | e1 => exact ⟨PresentedGroup.of .e1, by simp [liftedOctagonToProjectiveGenerator]⟩
  | e2 => exact ⟨PresentedGroup.of .e2, by simp [liftedOctagonToProjectiveGenerator]⟩
  | e3 => exact ⟨PresentedGroup.of .e3, by simp [liftedOctagonToProjectiveGenerator]⟩
  | e4 => exact ⟨PresentedGroup.of .e4, by simp [liftedOctagonToProjectiveGenerator]⟩

/-- The order-two subgroup generated by the central lift. -/
abbrev liftedOctagonCenter : Subgroup LiftedOctagonGroup :=
  Subgroup.zpowers (PresentedGroup.of .z)

private lemma commute_liftedOctagon_z_generator
    (x : OctagonPresentationGenerator) :
    Commute (PresentedGroup.of .z : LiftedOctagonGroup)
      (PresentedGroup.of x) := by
  cases x with
  | z => exact Commute.refl _
  | a => exact liftedOctagon_z_comm_a
  | c => exact liftedOctagon_z_comm_c
  | e1 =>
      apply Commute.symm
      rw [← liftedOctagon_e1_sq]
      exact Commute.self_pow _ _
  | e2 =>
      apply Commute.symm
      rw [← liftedOctagon_e2_sq]
      exact Commute.self_pow _ _
  | e3 =>
      apply Commute.symm
      rw [← liftedOctagon_e3_sq]
      exact Commute.self_pow _ _
  | e4 =>
      apply Commute.symm
      rw [← liftedOctagon_e4_sq]
      exact Commute.self_pow _ _

lemma liftedOctagon_z_mem_center :
    (PresentedGroup.of .z : LiftedOctagonGroup) ∈
      Subgroup.center LiftedOctagonGroup := by
  rw [Subgroup.mem_center_iff]
  intro x
  apply Commute.eq
  apply Commute.symm
  let C : Subgroup LiftedOctagonGroup :=
    Subgroup.centralizer ({PresentedGroup.of .z} : Set LiftedOctagonGroup)
  have hx : x ∈ C := by
    apply PresentedGroup.generated_by octagonPresentationRelators C
    intro i
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    exact commute_liftedOctagon_z_generator i
  rw [Subgroup.mem_centralizer_iff] at hx
  exact hx _ (Set.mem_singleton _)

instance liftedOctagonCenter_normal : liftedOctagonCenter.Normal where
  conj_mem n hn g := by
    rcases hn with ⟨k, rfl⟩
    have hz : Commute g (PresentedGroup.of .z : LiftedOctagonGroup) :=
      Subgroup.mem_center_iff.mp liftedOctagon_z_mem_center g
    have hzpow := hz.zpow_right k
    have hconj : g * (PresentedGroup.of .z : LiftedOctagonGroup) ^ k * g⁻¹ =
        (PresentedGroup.of .z : LiftedOctagonGroup) ^ k := by
      rw [hzpow.eq]
      group
    rw [hconj]
    exact ⟨k, rfl⟩

abbrev ProjectivizedLiftedOctagonGroup :=
  LiftedOctagonGroup ⧸ liftedOctagonCenter

lemma liftedOctagonCenter_le_projective_ker :
    liftedOctagonCenter ≤ liftedOctagonToProjective.ker := by
  rintro x ⟨n, rfl⟩
  simp [liftedOctagonToProjective_of, liftedOctagonToProjectiveGenerator]

def projectivizedLiftedOctagonToProjective :
    ProjectivizedLiftedOctagonGroup →* ProjectiveOctagonGroup :=
  QuotientGroup.lift liftedOctagonCenter liftedOctagonToProjective
    liftedOctagonCenter_le_projective_ker

def projectiveToLiftedOctagonQuotientGenerator :
    ProjectiveOctagonGenerator → ProjectivizedLiftedOctagonGroup
  | .a => QuotientGroup.mk' liftedOctagonCenter (PresentedGroup.of .a)
  | .c => QuotientGroup.mk' liftedOctagonCenter (PresentedGroup.of .c)
  | .e1 => QuotientGroup.mk' liftedOctagonCenter (PresentedGroup.of .e1)
  | .e2 => QuotientGroup.mk' liftedOctagonCenter (PresentedGroup.of .e2)
  | .e3 => QuotientGroup.mk' liftedOctagonCenter (PresentedGroup.of .e3)
  | .e4 => QuotientGroup.mk' liftedOctagonCenter (PresentedGroup.of .e4)

lemma projectiveToLiftedOctagonQuotientGenerator_relations :
    ∀ r ∈ projectiveOctagonRelators,
      FreeGroup.lift projectiveToLiftedOctagonQuotientGenerator r = 1 := by
  intro r hr
  rcases hr with ⟨i, rfl⟩
  cases i with
  | e1_sq =>
      change (QuotientGroup.mk' liftedOctagonCenter
        (PresentedGroup.of .e1)) ^ 2 = 1
      rw [← map_pow, liftedOctagon_e1_sq]
      exact (QuotientGroup.eq_one_iff _).2 ⟨1, by simp⟩
  | e2_sq =>
      change (QuotientGroup.mk' liftedOctagonCenter
        (PresentedGroup.of .e2)) ^ 2 = 1
      rw [← map_pow, liftedOctagon_e2_sq]
      exact (QuotientGroup.eq_one_iff _).2 ⟨1, by simp⟩
  | e3_sq =>
      change (QuotientGroup.mk' liftedOctagonCenter
        (PresentedGroup.of .e3)) ^ 2 = 1
      rw [← map_pow, liftedOctagon_e3_sq]
      exact (QuotientGroup.eq_one_iff _).2 ⟨1, by simp⟩
  | e4_sq =>
      change (QuotientGroup.mk' liftedOctagonCenter
        (PresentedGroup.of .e4)) ^ 2 = 1
      rw [← map_pow, liftedOctagon_e4_sq]
      exact (QuotientGroup.eq_one_iff _).2 ⟨1, by simp⟩
  | polygon =>
      change QuotientGroup.mk' liftedOctagonCenter
          (PresentedGroup.of .a) *
        QuotientGroup.mk' liftedOctagonCenter (PresentedGroup.of .e1) *
        (QuotientGroup.mk' liftedOctagonCenter
          (PresentedGroup.of .c))⁻¹ *
        QuotientGroup.mk' liftedOctagonCenter (PresentedGroup.of .e2) *
        (QuotientGroup.mk' liftedOctagonCenter
          (PresentedGroup.of .a))⁻¹ *
        QuotientGroup.mk' liftedOctagonCenter (PresentedGroup.of .e3) *
        QuotientGroup.mk' liftedOctagonCenter (PresentedGroup.of .c) *
        QuotientGroup.mk' liftedOctagonCenter (PresentedGroup.of .e4) = 1
      rw [← map_inv, ← map_inv]
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul,
        ← map_mul, ← map_mul, ← map_mul]
      rw [liftedOctagon_polygon, map_one]

def projectiveToProjectivizedLiftedOctagon :
    ProjectiveOctagonGroup →* ProjectivizedLiftedOctagonGroup :=
  PresentedGroup.toGroup projectiveToLiftedOctagonQuotientGenerator_relations

@[simp] lemma projectiveToProjectivizedLiftedOctagon_of
    (x : ProjectiveOctagonGenerator) :
    projectiveToProjectivizedLiftedOctagon (PresentedGroup.of x) =
      projectiveToLiftedOctagonQuotientGenerator x :=
  PresentedGroup.toGroup.of
    projectiveToLiftedOctagonQuotientGenerator_relations

theorem projectivizedToProjective_comp_projectiveToProjectivized :
    projectivizedLiftedOctagonToProjective.comp
        projectiveToProjectivizedLiftedOctagon =
      MonoidHom.id ProjectiveOctagonGroup := by
  apply PresentedGroup.ext
  intro x
  cases x <;>
    simp [projectivizedLiftedOctagonToProjective,
      projectiveToLiftedOctagonQuotientGenerator,
      liftedOctagonToProjectiveGenerator]

theorem projectiveToProjectivized_comp_projectivizedToProjective :
    projectiveToProjectivizedLiftedOctagon.comp
        projectivizedLiftedOctagonToProjective =
      MonoidHom.id ProjectivizedLiftedOctagonGroup := by
  apply QuotientGroup.monoidHom_ext liftedOctagonCenter
  apply PresentedGroup.ext
  intro x
  cases x with
  | z =>
      change (1 : ProjectivizedLiftedOctagonGroup) =
        QuotientGroup.mk' liftedOctagonCenter (PresentedGroup.of .z)
      symm
      exact (QuotientGroup.eq_one_iff _).2 ⟨1, by simp⟩
  | a | c | e1 | e2 | e3 | e4 =>
      simp [projectivizedLiftedOctagonToProjective,
        projectiveToLiftedOctagonQuotientGenerator,
        liftedOctagonToProjectiveGenerator]

/-- Quotienting the lifted octagon presentation by its central generator
gives exactly the projective octagon presentation. -/
def projectivizedLiftedOctagonEquivProjective :
    ProjectivizedLiftedOctagonGroup ≃* ProjectiveOctagonGroup where
  toFun := projectivizedLiftedOctagonToProjective
  invFun := projectiveToProjectivizedLiftedOctagon
  left_inv x := DFunLike.congr_fun
    projectiveToProjectivized_comp_projectivizedToProjective x
  right_inv x := DFunLike.congr_fun
    projectivizedToProjective_comp_projectiveToProjectivized x
  map_mul' := projectivizedLiftedOctagonToProjective.map_mul

/-- The kernel of central projection is precisely the subgroup generated by
the lifted central element. -/
theorem liftedOctagonToProjective_ker :
    liftedOctagonToProjective.ker = liftedOctagonCenter := by
  apply le_antisymm
  · intro x hx
    have hq : (QuotientGroup.mk' liftedOctagonCenter x :
        ProjectivizedLiftedOctagonGroup) = 1 := by
      apply projectivizedLiftedOctagonEquivProjective.injective
      simpa [projectivizedLiftedOctagonEquivProjective,
        projectivizedLiftedOctagonToProjective] using hx
    exact (QuotientGroup.eq_one_iff x).1 hq
  · exact liftedOctagonCenter_le_projective_ker

/-! ## The projective quaternion action -/

lemma octagonQuaternion_center_mem_center :
    octagonUnit .center ∈ Subgroup.center BSUnit23 := by
  rw [Subgroup.mem_center_iff]
  intro q
  change BuserSarnakQuaternionUnit.mul q (octagonUnit .center) =
    BuserSarnakQuaternionUnit.mul (octagonUnit .center) q
  apply BuserSarnakQuaternionUnit.ext <;>
    simp [octagonUnit, BuserSarnakQuaternionUnit.mul]

/-- The scalar order-two subgroup in the norm-one quaternion group. -/
abbrev octagonQuaternionCenter : Subgroup BSUnit23 :=
  Subgroup.zpowers (octagonUnit .center)

instance octagonQuaternionCenter_normal : octagonQuaternionCenter.Normal where
  conj_mem n hn g := by
    rcases hn with ⟨k, rfl⟩
    have hz : Commute g (octagonUnit .center) :=
      Subgroup.mem_center_iff.mp octagonQuaternion_center_mem_center g
    have hzpow := hz.zpow_right k
    have hconj : g * octagonUnit .center ^ k * g⁻¹ =
        octagonUnit .center ^ k := by
      rw [hzpow.eq]
      group
    rw [hconj]
    exact ⟨k, rfl⟩

abbrev ProjectivizedQuaternionGroup :=
  BSUnit23 ⧸ octagonQuaternionCenter

/-- The real matrix realization remembers all four coordinates of an integral
`(2,3)` quaternion. -/
theorem BuserSarnakQuaternionUnit.toSLHom_injective23 :
    Function.Injective
      (BuserSarnakQuaternionUnit.toSLHom
        (a := 2) (b := 3) (by norm_num) (by norm_num)) := by
  intro x y hxy
  have hmat : x.matrix = y.matrix := congrArg Subtype.val hxy
  have h00 := congr_fun (congr_fun hmat (0 : Fin 2)) (0 : Fin 2)
  have h01 := congr_fun (congr_fun hmat (0 : Fin 2)) (1 : Fin 2)
  have h10 := congr_fun (congr_fun hmat (1 : Fin 2)) (0 : Fin 2)
  have h11 := congr_fun (congr_fun hmat (1 : Fin 2)) (1 : Fin 2)
  norm_num [BuserSarnakQuaternionUnit.matrix, buserSarnakMatrix] at h00 h01 h10 h11
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hx0r : (x.x0 : ℝ) = y.x0 := by linarith
  have hx1r : (x.x1 : ℝ) = y.x1 := by nlinarith
  have hx2r : (x.x2 : ℝ) = y.x2 := by nlinarith
  have hx3r : (x.x3 : ℝ) = y.x3 := by nlinarith
  apply BuserSarnakQuaternionUnit.ext
  · exact_mod_cast hx0r
  · exact_mod_cast hx1r
  · exact_mod_cast hx2r
  · exact_mod_cast hx3r

/-- A `(2,3)` quaternion has central image in `SL(2, ℝ)` exactly when it is
one of the two scalar quaternion units. -/
lemma BuserSarnakQuaternionUnit.toSLHom_mem_center_iff23 (q : BSUnit23) :
    BuserSarnakQuaternionUnit.toSLHom
        (a := 2) (b := 3) (by norm_num) (by norm_num) q ∈
      Subgroup.center SL(2, ℝ) ↔
    q = 1 ∨ q = octagonUnit .center := by
  constructor
  · intro hq
    obtain ⟨r, hr, hscalar⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hq
    have hr' : r = 1 ∨ r = -1 := by
      have : r ^ 2 = (1 : ℝ) ^ 2 := by simpa using hr
      exact sq_eq_sq_iff_eq_or_eq_neg.mp this
    rcases hr' with rfl | rfl
    · left
      apply BuserSarnakQuaternionUnit.toSLHom_injective23
      apply Subtype.ext
      simpa using hscalar.symm
    · right
      apply BuserSarnakQuaternionUnit.toSLHom_injective23
      apply Subtype.ext
      rw [← hscalar]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [BuserSarnakQuaternionUnit.toSLHom,
          BuserSarnakQuaternionUnit.toSL, BuserSarnakQuaternionUnit.matrix,
          buserSarnakMatrix, octagonUnit]
  · rintro (rfl | rfl)
    · simp
    · rw [Matrix.SpecialLinearGroup.mem_center_iff]
      refine ⟨-1, by norm_num, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [BuserSarnakQuaternionUnit.toSLHom,
          BuserSarnakQuaternionUnit.toSL, BuserSarnakQuaternionUnit.matrix,
          buserSarnakMatrix, octagonUnit]

/-- The projective matrix realization of the integral `(2,3)` quaternion
group. -/
def BuserSarnakQuaternionUnit.toPGL23 : BSUnit23 →* PGL(2, ℝ) :=
  Matrix.SpecialLinearGroup.toPGL.comp
    (BuserSarnakQuaternionUnit.toSLHom
      (a := 2) (b := 3) (by norm_num) (by norm_num))

/-- The kernel of the projective matrix realization consists exactly of the
two scalar quaternion units. -/
theorem BuserSarnakQuaternionUnit.toPGL23_ker :
    BuserSarnakQuaternionUnit.toPGL23.ker = octagonQuaternionCenter := by
  apply le_antisymm
  · intro q hq
    have hcentral :
        BuserSarnakQuaternionUnit.toSLHom
            (a := 2) (b := 3) (by norm_num) (by norm_num) q ∈
          Subgroup.center SL(2, ℝ) := by
      rw [← Matrix.SpecialLinearGroup.toPGL_ker]
      exact hq
    rcases (BuserSarnakQuaternionUnit.toSLHom_mem_center_iff23 q).mp
        hcentral with rfl | rfl
    · exact Subgroup.one_mem _
    · exact ⟨1, by simp⟩
  · rintro q ⟨n, rfl⟩
    rw [MonoidHom.mem_ker, map_zpow]
    have hcenter :
        BuserSarnakQuaternionUnit.toPGL23 (octagonUnit .center) = 1 := by
      change Matrix.SpecialLinearGroup.toPGL
          (BuserSarnakQuaternionUnit.toSLHom
            (a := 2) (b := 3) (by norm_num) (by norm_num)
            (octagonUnit .center)) = 1
      rw [← MonoidHom.mem_ker, Matrix.SpecialLinearGroup.toPGL_ker]
      exact (BuserSarnakQuaternionUnit.toSLHom_mem_center_iff23 _).2
        (Or.inr rfl)
    rw [hcenter, one_zpow]

lemma octagonQuaternionCenter_le_toPGL23_ker :
    octagonQuaternionCenter ≤ BuserSarnakQuaternionUnit.toPGL23.ker := by
  rw [BuserSarnakQuaternionUnit.toPGL23_ker]

/-- The custom projectivized quaternion group embeds into Mathlib's real
projective linear group. -/
def projectivizedQuaternionToPGL23 :
    ProjectivizedQuaternionGroup →* PGL(2, ℝ) :=
  QuotientGroup.lift octagonQuaternionCenter
    BuserSarnakQuaternionUnit.toPGL23
    octagonQuaternionCenter_le_toPGL23_ker

theorem projectivizedQuaternionToPGL23_injective :
    Function.Injective projectivizedQuaternionToPGL23 := by
  exact (QuotientGroup.injective_lift_iff octagonQuaternionCenter
    BuserSarnakQuaternionUnit.toPGL23
    octagonQuaternionCenter_le_toPGL23_ker).2
      BuserSarnakQuaternionUnit.toPGL23_ker.symm

lemma liftedOctagonCenter_le_quaternionCenter_comap :
    liftedOctagonCenter ≤
      octagonQuaternionCenter.comap liftedOctagonToQuaternion := by
  rintro x ⟨n, rfl⟩
  change liftedOctagonToQuaternion
      ((PresentedGroup.of .z : LiftedOctagonGroup) ^ n) ∈
    octagonQuaternionCenter
  rw [map_zpow, liftedOctagonToQuaternion_of]
  exact ⟨n, rfl⟩

/-- The quaternion realization after quotienting both central scalar
subgroups. -/
def projectivizedLiftedOctagonToProjectivizedQuaternion :
    ProjectivizedLiftedOctagonGroup →* ProjectivizedQuaternionGroup :=
  QuotientGroup.map liftedOctagonCenter octagonQuaternionCenter
    liftedOctagonToQuaternion liftedOctagonCenter_le_quaternionCenter_comap

/-- The remaining projective action whose faithfulness is equivalent to
faithfulness of the original lifted quaternion realization. -/
def projectiveOctagonToProjectivizedQuaternion :
    ProjectiveOctagonGroup →* ProjectivizedQuaternionGroup :=
  projectivizedLiftedOctagonToProjectivizedQuaternion.comp
    projectiveToProjectivizedLiftedOctagon

lemma liftedOctagonCenter_restrict_quaternion_injective :
    ∀ x ∈ liftedOctagonCenter,
      liftedOctagonToQuaternion x = 1 → x = 1 := by
  intro x hx hqx
  rcases hx with ⟨n, rfl⟩
  have hcenter_ne : octagonUnit .center ≠ (1 : BSUnit23) := by
    intro h
    have hcoord := congrArg BuserSarnakQuaternionUnit.x0 h
    change (-1 : ℤ) = 1 at hcoord
    omega
  have hsource_sq :
      (PresentedGroup.of .z : LiftedOctagonGroup) ^ 2 = 1 :=
    liftedOctagon_z_sq
  have htarget_sq : octagonUnit .center ^ 2 = 1 := octagon_center_sq
  rw [map_zpow, liftedOctagonToQuaternion_of] at hqx
  change octagonUnit .center ^ n = 1 at hqx
  have hsourceOrder : orderOf
      (PresentedGroup.of .z : LiftedOctagonGroup) = 2 := by
    apply orderOf_eq_prime hsource_sq
    intro hz
    apply hcenter_ne
    simpa [octagonPresentationImage] using
      congrArg liftedOctagonToQuaternion hz
  have htargetOrder : orderOf (octagonUnit .center) = 2 :=
    orderOf_eq_prime htarget_sq hcenter_ne
  have hdiv : (2 : ℤ) ∣ n := by
    simpa [htargetOrder] using
      (orderOf_dvd_iff_zpow_eq_one.mpr hqx)
  apply orderOf_dvd_iff_zpow_eq_one.mp
  simpa [hsourceOrder] using hdiv

theorem liftedOctagonToQuaternion_injective_of_projective
    (hproj : Function.Injective
      projectiveOctagonToProjectivizedQuaternion) :
    Function.Injective liftedOctagonToQuaternion := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hprojectiveQuotient :
      projectiveOctagonToProjectivizedQuaternion
          (liftedOctagonToProjective x) = 1 := by
    change projectivizedLiftedOctagonToProjectivizedQuaternion
        (projectiveToProjectivizedLiftedOctagon
          (liftedOctagonToProjective x)) = 1
    have hquotient : projectiveToProjectivizedLiftedOctagon
        (liftedOctagonToProjective x) =
          QuotientGroup.mk' liftedOctagonCenter x := by
      have hcomp := DFunLike.congr_fun
        projectiveToProjectivized_comp_projectivizedToProjective
        (QuotientGroup.mk' liftedOctagonCenter x)
      simpa [projectivizedLiftedOctagonToProjective] using hcomp
    rw [hquotient]
    change (QuotientGroup.mk' octagonQuaternionCenter
      (liftedOctagonToQuaternion x) : ProjectivizedQuaternionGroup) = 1
    rw [hx, map_one]
  have hprojective : liftedOctagonToProjective x = 1 := by
    apply hproj
    simpa using hprojectiveQuotient
  have hxcenter : x ∈ liftedOctagonCenter := by
    rw [← liftedOctagonToProjective_ker]
    exact hprojective
  exact liftedOctagonCenter_restrict_quaternion_injective x hxcenter hx

lemma projectivizedLiftedToProjectivizedQuaternion_injective
    (hquat : Function.Injective liftedOctagonToQuaternion) :
    Function.Injective
      projectivizedLiftedOctagonToProjectivizedQuaternion := by
  rw [injective_iff_map_eq_one]
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective liftedOctagonCenter q
  change (QuotientGroup.mk' octagonQuaternionCenter
    (liftedOctagonToQuaternion x) : ProjectivizedQuaternionGroup) = 1 at hq
  apply (QuotientGroup.eq_one_iff x).2
  have hximage : liftedOctagonToQuaternion x ∈ octagonQuaternionCenter :=
    (QuotientGroup.eq_one_iff _).1 hq
  rcases hximage with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  apply hquat
  rw [map_zpow, liftedOctagonToQuaternion_of]
  exact hn

theorem projectiveOctagonToProjectivizedQuaternion_injective_of_lifted
    (hquat : Function.Injective liftedOctagonToQuaternion) :
    Function.Injective projectiveOctagonToProjectivizedQuaternion := by
  exact (projectivizedLiftedToProjectivizedQuaternion_injective hquat).comp
    projectivizedLiftedOctagonEquivProjective.symm.injective

/-- Faithfulness of the lifted quaternion realization is exactly faithfulness
of the induced action after removing the two scalar order-two subgroups. -/
theorem liftedOctagonToQuaternion_injective_iff_projective :
    Function.Injective liftedOctagonToQuaternion ↔
      Function.Injective projectiveOctagonToProjectivizedQuaternion :=
  ⟨projectiveOctagonToProjectivizedQuaternion_injective_of_lifted,
    liftedOctagonToQuaternion_injective_of_projective⟩

/-- The two Tietze-equivalent lifted presentations have faithful quaternion
realizations simultaneously. -/
theorem standardLiftedOrbifoldToQuaternion_injective_iff_octagon :
    Function.Injective standardLiftedOrbifoldToQuaternion ↔
      Function.Injective liftedOctagonToQuaternion := by
  constructor
  · intro hstandard
    rw [← standardQuaternion_comp_liftedOctagonToStandard]
    exact hstandard.comp liftedOctagonEquivStandardLiftedOrbifold.injective
  · intro hoctagon
    rw [← octagonQuaternion_comp_standardToOctagon]
    exact hoctagon.comp liftedOctagonEquivStandardLiftedOrbifold.symm.injective

/-- Faithfulness of the standard signature presentation is reduced to the
same projective action as the octagon presentation. -/
theorem standardLiftedOrbifoldToQuaternion_injective_iff_projective :
    Function.Injective standardLiftedOrbifoldToQuaternion ↔
      Function.Injective projectiveOctagonToProjectivizedQuaternion :=
  standardLiftedOrbifoldToQuaternion_injective_iff_octagon.trans
    liftedOctagonToQuaternion_injective_iff_projective

end

end SystolicGrowth
