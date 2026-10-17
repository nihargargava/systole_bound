module

public import BuserSarnak.BuserSarnakSignature

@[expose] public section

namespace SystolicGrowth

noncomputable section

private lemma commute_of_sq_eq {G : Type*} [Group G] (x z : G)
    (h : x ^ 2 = z) : Commute z x := by
  change z * x = x * z
  rw [← h]
  group

private lemma commutator_eq_one_of_commute {G : Type*} [Group G]
    {x y : G} (h : Commute x y) : x * y * x⁻¹ * y⁻¹ = 1 := by
  rw [h.eq]
  group

private lemma commute_of_commutator_eq_one {G : Type*} [Group G]
    {x y : G} (h : x * y * x⁻¹ * y⁻¹ = 1) : Commute x y := by
  change x * y = y * x
  calc
    x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = 1 * (y * x) := by rw [h]
    _ = y * x := one_mul _

/-! ### Relations available inside the two presented groups -/

private lemma octagon_relator_eq_one (r : OctagonPresentationRelator) :
    PresentedGroup.mk octagonPresentationRelators
      (octagonPresentationRelator r) = 1 :=
  PresentedGroup.one_of_mem ⟨r, rfl⟩

@[simp] lemma liftedOctagon_z_sq :
    (PresentedGroup.of .z : LiftedOctagonGroup) ^ 2 = 1 := by
  simpa [PresentedGroup.of, octagonPresentationRelator] using
    octagon_relator_eq_one .z_sq

lemma liftedOctagon_z_comm_a :
    Commute (PresentedGroup.of .z : LiftedOctagonGroup)
      (PresentedGroup.of .a) := by
  change
    (PresentedGroup.of OctagonPresentationGenerator.z : LiftedOctagonGroup) *
        PresentedGroup.of OctagonPresentationGenerator.a =
      PresentedGroup.of OctagonPresentationGenerator.a *
        PresentedGroup.of OctagonPresentationGenerator.z
  have h := octagon_relator_eq_one .z_comm_a
  simp only [octagonPresentationRelator, map_mul, map_inv,
    FreeGroup.lift_apply_of, PresentedGroup.of] at h
  exact commute_of_commutator_eq_one h

lemma liftedOctagon_z_comm_c :
    Commute (PresentedGroup.of .z : LiftedOctagonGroup)
      (PresentedGroup.of .c) := by
  change
    (PresentedGroup.of OctagonPresentationGenerator.z : LiftedOctagonGroup) *
        PresentedGroup.of OctagonPresentationGenerator.c =
      PresentedGroup.of OctagonPresentationGenerator.c *
        PresentedGroup.of OctagonPresentationGenerator.z
  have h := octagon_relator_eq_one .z_comm_c
  simp only [octagonPresentationRelator, map_mul, map_inv,
    FreeGroup.lift_apply_of, PresentedGroup.of] at h
  exact commute_of_commutator_eq_one h

@[simp] lemma liftedOctagon_e1_sq :
    (PresentedGroup.of .e1 : LiftedOctagonGroup) ^ 2 = PresentedGroup.of .z := by
  have h := octagon_relator_eq_one .e1_sq
  simpa [PresentedGroup.of, octagonPresentationRelator] using
    (eq_of_mul_inv_eq_one h)

@[simp] lemma liftedOctagon_e2_sq :
    (PresentedGroup.of .e2 : LiftedOctagonGroup) ^ 2 = PresentedGroup.of .z := by
  have h := octagon_relator_eq_one .e2_sq
  simpa [PresentedGroup.of, octagonPresentationRelator] using
    (eq_of_mul_inv_eq_one h)

@[simp] lemma liftedOctagon_e3_sq :
    (PresentedGroup.of .e3 : LiftedOctagonGroup) ^ 2 = PresentedGroup.of .z := by
  have h := octagon_relator_eq_one .e3_sq
  simpa [PresentedGroup.of, octagonPresentationRelator] using
    (eq_of_mul_inv_eq_one h)

@[simp] lemma liftedOctagon_e4_sq :
    (PresentedGroup.of .e4 : LiftedOctagonGroup) ^ 2 = PresentedGroup.of .z := by
  have h := octagon_relator_eq_one .e4_sq
  simpa [PresentedGroup.of, octagonPresentationRelator] using
    (eq_of_mul_inv_eq_one h)

lemma liftedOctagon_polygon :
    (PresentedGroup.of .a : LiftedOctagonGroup) * PresentedGroup.of .e1 *
      (PresentedGroup.of .c)⁻¹ * PresentedGroup.of .e2 *
      (PresentedGroup.of .a)⁻¹ * PresentedGroup.of .e3 *
      PresentedGroup.of .c * PresentedGroup.of .e4 = 1 := by
  simpa [PresentedGroup.of, octagonPresentationRelator] using
    octagon_relator_eq_one .polygon

private lemma standard_relator_eq_one (r : StandardOrbifoldRelator) :
    PresentedGroup.mk standardOrbifoldRelators
      (standardOrbifoldRelator r) = 1 :=
  PresentedGroup.one_of_mem ⟨r, rfl⟩

@[simp] lemma standardLifted_z_sq :
    (PresentedGroup.of .z : StandardLiftedOrbifoldGroup) ^ 2 = 1 := by
  simpa [PresentedGroup.of, standardOrbifoldRelator] using
    standard_relator_eq_one .z_sq

lemma standardLifted_z_comm_a :
    Commute (PresentedGroup.of .z : StandardLiftedOrbifoldGroup)
      (PresentedGroup.of .a) := by
  change
    (PresentedGroup.of StandardOrbifoldGenerator.z : StandardLiftedOrbifoldGroup) *
        PresentedGroup.of StandardOrbifoldGenerator.a =
      PresentedGroup.of StandardOrbifoldGenerator.a *
        PresentedGroup.of StandardOrbifoldGenerator.z
  have h := standard_relator_eq_one .z_comm_a
  simp only [standardOrbifoldRelator, map_mul, map_inv,
    FreeGroup.lift_apply_of, PresentedGroup.of] at h
  exact commute_of_commutator_eq_one h

lemma standardLifted_z_comm_b :
    Commute (PresentedGroup.of .z : StandardLiftedOrbifoldGroup)
      (PresentedGroup.of .b) := by
  change
    (PresentedGroup.of StandardOrbifoldGenerator.z : StandardLiftedOrbifoldGroup) *
        PresentedGroup.of StandardOrbifoldGenerator.b =
      PresentedGroup.of StandardOrbifoldGenerator.b *
        PresentedGroup.of StandardOrbifoldGenerator.z
  have h := standard_relator_eq_one .z_comm_b
  simp only [standardOrbifoldRelator, map_mul, map_inv,
    FreeGroup.lift_apply_of, PresentedGroup.of] at h
  exact commute_of_commutator_eq_one h

@[simp] lemma standardLifted_d1_sq :
    (PresentedGroup.of .d1 : StandardLiftedOrbifoldGroup) ^ 2 =
      PresentedGroup.of .z := by
  have h := standard_relator_eq_one .d1_sq
  simpa [PresentedGroup.of, standardOrbifoldRelator] using
    (eq_of_mul_inv_eq_one h)

@[simp] lemma standardLifted_d2_sq :
    (PresentedGroup.of .d2 : StandardLiftedOrbifoldGroup) ^ 2 =
      PresentedGroup.of .z := by
  have h := standard_relator_eq_one .d2_sq
  simpa [PresentedGroup.of, standardOrbifoldRelator] using
    (eq_of_mul_inv_eq_one h)

@[simp] lemma standardLifted_d3_sq :
    (PresentedGroup.of .d3 : StandardLiftedOrbifoldGroup) ^ 2 =
      PresentedGroup.of .z := by
  have h := standard_relator_eq_one .d3_sq
  simpa [PresentedGroup.of, standardOrbifoldRelator] using
    (eq_of_mul_inv_eq_one h)

@[simp] lemma standardLifted_d4_sq :
    (PresentedGroup.of .d4 : StandardLiftedOrbifoldGroup) ^ 2 =
      PresentedGroup.of .z := by
  have h := standard_relator_eq_one .d4_sq
  simpa [PresentedGroup.of, standardOrbifoldRelator] using
    (eq_of_mul_inv_eq_one h)

lemma standardLifted_signature :
    (PresentedGroup.of .a : StandardLiftedOrbifoldGroup) *
      PresentedGroup.of .b * (PresentedGroup.of .a)⁻¹ *
      (PresentedGroup.of .b)⁻¹ * PresentedGroup.of .d1 *
      PresentedGroup.of .d2 * PresentedGroup.of .d3 *
      PresentedGroup.of .d4 = 1 := by
  simpa [PresentedGroup.of, standardOrbifoldRelator] using
    standard_relator_eq_one .signature

/-! ### Explicit substitutions -/

def octagonBWord : LiftedOctagonGroup :=
  PresentedGroup.of .e1 * (PresentedGroup.of .c)⁻¹ *
    PresentedGroup.of .e2

def octagonToStandardGenerator :
    OctagonPresentationGenerator → StandardLiftedOrbifoldGroup
  | .z => PresentedGroup.of .z
  | .a => PresentedGroup.of .a
  | .c => (PresentedGroup.of .b)⁻¹ * PresentedGroup.of .d2 *
      PresentedGroup.of .d3
  | .e1 => PresentedGroup.of .d3
  | .e2 => (PresentedGroup.of .b)⁻¹ * PresentedGroup.of .d2 *
      PresentedGroup.of .b
  | .e3 => (PresentedGroup.of .b)⁻¹ * PresentedGroup.of .d1 *
      PresentedGroup.of .b
  | .e4 => PresentedGroup.of .d4

private lemma standardLifted_z_comm_d1 :
    Commute (PresentedGroup.of .z : StandardLiftedOrbifoldGroup)
      (PresentedGroup.of .d1) :=
  commute_of_sq_eq _ _ standardLifted_d1_sq

private lemma standardLifted_z_comm_d2 :
    Commute (PresentedGroup.of .z : StandardLiftedOrbifoldGroup)
      (PresentedGroup.of .d2) :=
  commute_of_sq_eq _ _ standardLifted_d2_sq

private lemma standardLifted_z_comm_d3 :
    Commute (PresentedGroup.of .z : StandardLiftedOrbifoldGroup)
      (PresentedGroup.of .d3) :=
  commute_of_sq_eq _ _ standardLifted_d3_sq

private lemma standardLifted_z_comm_d4 :
    Commute (PresentedGroup.of .z : StandardLiftedOrbifoldGroup)
      (PresentedGroup.of .d4) :=
  commute_of_sq_eq _ _ standardLifted_d4_sq

lemma octagonToStandardGenerator_relations :
    ∀ r ∈ octagonPresentationRelators,
      FreeGroup.lift octagonToStandardGenerator r = 1 := by
  intro r hr
  rcases hr with ⟨i, rfl⟩
  cases i with
  | z_sq => simpa [octagonPresentationRelator, octagonToStandardGenerator]
      using standardLifted_z_sq
  | z_comm_a =>
      simpa [octagonPresentationRelator, octagonToStandardGenerator] using
        commutator_eq_one_of_commute standardLifted_z_comm_a
  | z_comm_c =>
      simpa [octagonPresentationRelator, octagonToStandardGenerator] using
        commutator_eq_one_of_commute
          ((standardLifted_z_comm_b.inv_right.mul_right
            standardLifted_z_comm_d2).mul_right standardLifted_z_comm_d3)
  | e1_sq =>
      simpa [octagonPresentationRelator, octagonToStandardGenerator] using
        standardLifted_d3_sq
  | e2_sq =>
      change ((PresentedGroup.of .b)⁻¹ * PresentedGroup.of .d2 *
        PresentedGroup.of .b : StandardLiftedOrbifoldGroup) ^ 2 *
        (PresentedGroup.of .z)⁻¹ = 1
      rw [show ((PresentedGroup.of .b)⁻¹ * PresentedGroup.of .d2 *
          PresentedGroup.of .b : StandardLiftedOrbifoldGroup) ^ 2 =
          (PresentedGroup.of .b)⁻¹ * (PresentedGroup.of .d2 ^ 2) *
            PresentedGroup.of .b by
              simp only [pow_two]
              group,
        standardLifted_d2_sq]
      simpa using commutator_eq_one_of_commute
        standardLifted_z_comm_b.symm.inv_left
  | e3_sq =>
      change ((PresentedGroup.of .b)⁻¹ * PresentedGroup.of .d1 *
        PresentedGroup.of .b : StandardLiftedOrbifoldGroup) ^ 2 *
        (PresentedGroup.of .z)⁻¹ = 1
      rw [show ((PresentedGroup.of .b)⁻¹ * PresentedGroup.of .d1 *
          PresentedGroup.of .b : StandardLiftedOrbifoldGroup) ^ 2 =
          (PresentedGroup.of .b)⁻¹ * (PresentedGroup.of .d1 ^ 2) *
            PresentedGroup.of .b by
              simp only [pow_two]
              group,
        standardLifted_d1_sq]
      simpa using commutator_eq_one_of_commute
        standardLifted_z_comm_b.symm.inv_left
  | e4_sq =>
      change (PresentedGroup.of .d4 : StandardLiftedOrbifoldGroup) ^ 2 *
        (PresentedGroup.of .z)⁻¹ = 1
      rw [standardLifted_d4_sq]
      group
  | polygon =>
      change (PresentedGroup.of .a : StandardLiftedOrbifoldGroup) *
        PresentedGroup.of .d3 *
        ((PresentedGroup.of .b)⁻¹ * PresentedGroup.of .d2 *
          PresentedGroup.of .d3)⁻¹ *
        ((PresentedGroup.of .b)⁻¹ * PresentedGroup.of .d2 *
          PresentedGroup.of .b) *
        (PresentedGroup.of .a)⁻¹ *
        ((PresentedGroup.of .b)⁻¹ * PresentedGroup.of .d1 *
          PresentedGroup.of .b) *
        ((PresentedGroup.of .b)⁻¹ * PresentedGroup.of .d2 *
          PresentedGroup.of .d3) * PresentedGroup.of .d4 = 1
      rw [show (PresentedGroup.of .a : StandardLiftedOrbifoldGroup) *
          PresentedGroup.of .d3 *
          ((PresentedGroup.of .b)⁻¹ * PresentedGroup.of .d2 *
            PresentedGroup.of .d3)⁻¹ *
          ((PresentedGroup.of .b)⁻¹ * PresentedGroup.of .d2 *
            PresentedGroup.of .b) *
          (PresentedGroup.of .a)⁻¹ *
          ((PresentedGroup.of .b)⁻¹ * PresentedGroup.of .d1 *
            PresentedGroup.of .b) *
          ((PresentedGroup.of .b)⁻¹ * PresentedGroup.of .d2 *
            PresentedGroup.of .d3) * PresentedGroup.of .d4 =
          PresentedGroup.of .a * PresentedGroup.of .b *
            (PresentedGroup.of .a)⁻¹ * (PresentedGroup.of .b)⁻¹ *
            PresentedGroup.of .d1 * PresentedGroup.of .d2 *
            PresentedGroup.of .d3 * PresentedGroup.of .d4 by group]
      exact standardLifted_signature

def liftedOctagonToStandard :
    LiftedOctagonGroup →* StandardLiftedOrbifoldGroup :=
  PresentedGroup.toGroup octagonToStandardGenerator_relations

def standardToOctagonGenerator :
    StandardOrbifoldGenerator → LiftedOctagonGroup
  | .z => PresentedGroup.of .z
  | .a => PresentedGroup.of .a
  | .b => octagonBWord
  | .d1 => octagonBWord * PresentedGroup.of .e3 * octagonBWord⁻¹
  | .d2 => octagonBWord * PresentedGroup.of .e2 * octagonBWord⁻¹
  | .d3 => PresentedGroup.of .e1
  | .d4 => PresentedGroup.of .e4

private lemma liftedOctagon_z_comm_e1 :
    Commute (PresentedGroup.of .z : LiftedOctagonGroup)
      (PresentedGroup.of .e1) :=
  commute_of_sq_eq _ _ liftedOctagon_e1_sq

private lemma liftedOctagon_z_comm_e2 :
    Commute (PresentedGroup.of .z : LiftedOctagonGroup)
      (PresentedGroup.of .e2) :=
  commute_of_sq_eq _ _ liftedOctagon_e2_sq

private lemma liftedOctagon_z_comm_e3 :
    Commute (PresentedGroup.of .z : LiftedOctagonGroup)
      (PresentedGroup.of .e3) :=
  commute_of_sq_eq _ _ liftedOctagon_e3_sq

private lemma liftedOctagon_z_comm_e4 :
    Commute (PresentedGroup.of .z : LiftedOctagonGroup)
      (PresentedGroup.of .e4) :=
  commute_of_sq_eq _ _ liftedOctagon_e4_sq

private lemma liftedOctagon_z_comm_B :
    Commute (PresentedGroup.of .z : LiftedOctagonGroup) octagonBWord :=
  (liftedOctagon_z_comm_e1.mul_right liftedOctagon_z_comm_c.inv_right).mul_right
    liftedOctagon_z_comm_e2

lemma standardToOctagonGenerator_relations :
    ∀ r ∈ standardOrbifoldRelators,
      FreeGroup.lift standardToOctagonGenerator r = 1 := by
  intro r hr
  rcases hr with ⟨i, rfl⟩
  cases i with
  | z_sq => simpa [standardOrbifoldRelator, standardToOctagonGenerator]
      using liftedOctagon_z_sq
  | z_comm_a =>
      simpa [standardOrbifoldRelator, standardToOctagonGenerator] using
        commutator_eq_one_of_commute liftedOctagon_z_comm_a
  | z_comm_b =>
      simpa [standardOrbifoldRelator, standardToOctagonGenerator] using
        commutator_eq_one_of_commute liftedOctagon_z_comm_B
  | d1_sq =>
      change (octagonBWord * PresentedGroup.of .e3 * octagonBWord⁻¹) ^ 2 *
        (PresentedGroup.of .z)⁻¹ = 1
      rw [show (octagonBWord * PresentedGroup.of .e3 * octagonBWord⁻¹) ^ 2 =
          octagonBWord * (PresentedGroup.of .e3 ^ 2) * octagonBWord⁻¹ by
            simp only [pow_two]
            group,
        liftedOctagon_e3_sq]
      simpa using commutator_eq_one_of_commute liftedOctagon_z_comm_B.symm
  | d2_sq =>
      change (octagonBWord * PresentedGroup.of .e2 * octagonBWord⁻¹) ^ 2 *
        (PresentedGroup.of .z)⁻¹ = 1
      rw [show (octagonBWord * PresentedGroup.of .e2 * octagonBWord⁻¹) ^ 2 =
          octagonBWord * (PresentedGroup.of .e2 ^ 2) * octagonBWord⁻¹ by
            simp only [pow_two]
            group,
        liftedOctagon_e2_sq]
      simpa using commutator_eq_one_of_commute liftedOctagon_z_comm_B.symm
  | d3_sq =>
      change (PresentedGroup.of .e1 : LiftedOctagonGroup) ^ 2 *
        (PresentedGroup.of .z)⁻¹ = 1
      rw [liftedOctagon_e1_sq]
      group
  | d4_sq =>
      change (PresentedGroup.of .e4 : LiftedOctagonGroup) ^ 2 *
        (PresentedGroup.of .z)⁻¹ = 1
      rw [liftedOctagon_e4_sq]
      group
  | signature =>
      change (PresentedGroup.of .a : LiftedOctagonGroup) * octagonBWord *
        (PresentedGroup.of .a)⁻¹ * octagonBWord⁻¹ *
        (octagonBWord * PresentedGroup.of .e3 * octagonBWord⁻¹) *
        (octagonBWord * PresentedGroup.of .e2 * octagonBWord⁻¹) *
        PresentedGroup.of .e1 * PresentedGroup.of .e4 = 1
      rw [show (PresentedGroup.of .a : LiftedOctagonGroup) * octagonBWord *
          (PresentedGroup.of .a)⁻¹ * octagonBWord⁻¹ *
          (octagonBWord * PresentedGroup.of .e3 * octagonBWord⁻¹) *
          (octagonBWord * PresentedGroup.of .e2 * octagonBWord⁻¹) *
          PresentedGroup.of .e1 * PresentedGroup.of .e4 =
          PresentedGroup.of .a * PresentedGroup.of .e1 *
            (PresentedGroup.of .c)⁻¹ * PresentedGroup.of .e2 *
            (PresentedGroup.of .a)⁻¹ * PresentedGroup.of .e3 *
            PresentedGroup.of .c * PresentedGroup.of .e4 by
        simp only [octagonBWord]
        group]
      exact liftedOctagon_polygon

def standardLiftedOrbifoldToOctagon :
    StandardLiftedOrbifoldGroup →* LiftedOctagonGroup :=
  PresentedGroup.toGroup standardToOctagonGenerator_relations

theorem standardToOctagon_comp_octagonToStandard :
    standardLiftedOrbifoldToOctagon.comp liftedOctagonToStandard =
      MonoidHom.id LiftedOctagonGroup := by
  apply PresentedGroup.ext
  intro x
  cases x <;>
    simp only [MonoidHom.comp_apply, liftedOctagonToStandard,
      standardLiftedOrbifoldToOctagon, PresentedGroup.toGroup.of,
      octagonToStandardGenerator, standardToOctagonGenerator,
      octagonBWord, MonoidHom.id_apply, map_mul, map_inv] <;>
    group

theorem octagonToStandard_comp_standardToOctagon :
    liftedOctagonToStandard.comp standardLiftedOrbifoldToOctagon =
      MonoidHom.id StandardLiftedOrbifoldGroup := by
  apply PresentedGroup.ext
  intro x
  cases x <;>
    simp only [MonoidHom.comp_apply, liftedOctagonToStandard,
      standardLiftedOrbifoldToOctagon, PresentedGroup.toGroup.of,
      octagonToStandardGenerator, standardToOctagonGenerator,
      octagonBWord, MonoidHom.id_apply, map_mul, map_inv] <;>
    group

/-- The side-pairing and signature presentations are related by explicit
Tietze substitutions. -/
def liftedOctagonEquivStandardLiftedOrbifold :
    LiftedOctagonGroup ≃* StandardLiftedOrbifoldGroup where
  toFun := liftedOctagonToStandard
  invFun := standardLiftedOrbifoldToOctagon
  left_inv x := by
    exact DFunLike.congr_fun standardToOctagon_comp_octagonToStandard x
  right_inv x := by
    exact DFunLike.congr_fun octagonToStandard_comp_standardToOctagon x
  map_mul' := liftedOctagonToStandard.map_mul

theorem standardQuaternion_comp_liftedOctagonToStandard :
    standardLiftedOrbifoldToQuaternion.comp liftedOctagonToStandard =
      liftedOctagonToQuaternion := by
  apply PresentedGroup.ext
  intro x
  cases x <;>
    simp [liftedOctagonToStandard, octagonToStandardGenerator,
      standardOrbifoldImage, octagonPresentationImage,
      standardQuaternionB, standardQuaternionD1, standardQuaternionD2] <;>
    decide

theorem octagonQuaternion_comp_standardToOctagon :
    liftedOctagonToQuaternion.comp standardLiftedOrbifoldToOctagon =
      standardLiftedOrbifoldToQuaternion := by
  apply PresentedGroup.ext
  intro x
  cases x <;>
    simp [standardLiftedOrbifoldToOctagon, standardToOctagonGenerator,
      octagonBWord, standardOrbifoldImage, octagonPresentationImage,
      standardQuaternionB, standardQuaternionD1, standardQuaternionD2]

end


end SystolicGrowth
