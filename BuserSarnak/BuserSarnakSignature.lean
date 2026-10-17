module

public import BuserSarnak.BuserSarnakOrbifold

@[expose] public section

namespace SystolicGrowth

inductive StandardOrbifoldGenerator where
  | z | a | b | d1 | d2 | d3 | d4
  deriving DecidableEq

inductive StandardOrbifoldRelator where
  | z_sq | z_comm_a | z_comm_b
  | d1_sq | d2_sq | d3_sq | d4_sq
  | signature
  deriving DecidableEq

def standardOrbifoldRelator :
    StandardOrbifoldRelator → FreeGroup StandardOrbifoldGenerator
  | .z_sq => FreeGroup.of .z ^ 2
  | .z_comm_a => FreeGroup.of .z * FreeGroup.of .a *
      (FreeGroup.of .z)⁻¹ * (FreeGroup.of .a)⁻¹
  | .z_comm_b => FreeGroup.of .z * FreeGroup.of .b *
      (FreeGroup.of .z)⁻¹ * (FreeGroup.of .b)⁻¹
  | .d1_sq => FreeGroup.of .d1 ^ 2 * (FreeGroup.of .z)⁻¹
  | .d2_sq => FreeGroup.of .d2 ^ 2 * (FreeGroup.of .z)⁻¹
  | .d3_sq => FreeGroup.of .d3 ^ 2 * (FreeGroup.of .z)⁻¹
  | .d4_sq => FreeGroup.of .d4 ^ 2 * (FreeGroup.of .z)⁻¹
  | .signature => FreeGroup.of .a * FreeGroup.of .b *
      (FreeGroup.of .a)⁻¹ * (FreeGroup.of .b)⁻¹ *
      FreeGroup.of .d1 * FreeGroup.of .d2 *
      FreeGroup.of .d3 * FreeGroup.of .d4

def standardOrbifoldRelators : Set (FreeGroup StandardOrbifoldGenerator) :=
  Set.range standardOrbifoldRelator

abbrev StandardLiftedOrbifoldGroup := PresentedGroup standardOrbifoldRelators

def standardQuaternionB : BSUnit23 :=
  octagonUnit (.B true false) * (octagonUnit (.C true))⁻¹ *
    octagonUnit (.B false false)

def standardQuaternionD1 : BSUnit23 :=
  standardQuaternionB * octagonUnit (.B false true) * standardQuaternionB⁻¹

def standardQuaternionD2 : BSUnit23 :=
  standardQuaternionB * octagonUnit (.B false false) * standardQuaternionB⁻¹

def standardOrbifoldImage : StandardOrbifoldGenerator → BSUnit23
  | .z => octagonUnit .center
  | .a => octagonUnit (.A true)
  | .b => standardQuaternionB
  | .d1 => standardQuaternionD1
  | .d2 => standardQuaternionD2
  | .d3 => octagonUnit (.B true false)
  | .d4 => octagonUnit (.B true true)

lemma standard_z_sq : standardOrbifoldImage .z ^ 2 = 1 := by decide
lemma standard_z_comm_a : standardOrbifoldImage .z * standardOrbifoldImage .a *
    (standardOrbifoldImage .z)⁻¹ * (standardOrbifoldImage .a)⁻¹ = 1 := by decide
lemma standard_z_comm_b : standardOrbifoldImage .z * standardOrbifoldImage .b *
    (standardOrbifoldImage .z)⁻¹ * (standardOrbifoldImage .b)⁻¹ = 1 := by decide
lemma standard_d1_sq : standardOrbifoldImage .d1 ^ 2 = standardOrbifoldImage .z := by
  decide
lemma standard_d2_sq : standardOrbifoldImage .d2 ^ 2 = standardOrbifoldImage .z := by
  decide
lemma standard_d3_sq : standardOrbifoldImage .d3 ^ 2 = standardOrbifoldImage .z := by
  decide
lemma standard_d4_sq : standardOrbifoldImage .d4 ^ 2 = standardOrbifoldImage .z := by
  decide
lemma standard_signature_relation :
    standardOrbifoldImage .a * standardOrbifoldImage .b *
    (standardOrbifoldImage .a)⁻¹ * (standardOrbifoldImage .b)⁻¹ *
    standardOrbifoldImage .d1 * standardOrbifoldImage .d2 *
    standardOrbifoldImage .d3 * standardOrbifoldImage .d4 = 1 := by
  decide

lemma standardOrbifoldImage_relations :
    ∀ r ∈ standardOrbifoldRelators,
      FreeGroup.lift standardOrbifoldImage r = 1 := by
  intro r hr
  rcases hr with ⟨i, rfl⟩
  cases i with
  | z_sq => simpa [standardOrbifoldRelator] using standard_z_sq
  | z_comm_a => simpa [standardOrbifoldRelator] using standard_z_comm_a
  | z_comm_b => simpa [standardOrbifoldRelator] using standard_z_comm_b
  | d1_sq => simpa [standardOrbifoldRelator, standard_d1_sq] using (mul_inv_cancel (standardOrbifoldImage .z))
  | d2_sq => simpa [standardOrbifoldRelator, standard_d2_sq] using (mul_inv_cancel (standardOrbifoldImage .z))
  | d3_sq => simpa [standardOrbifoldRelator, standard_d3_sq] using (mul_inv_cancel (standardOrbifoldImage .z))
  | d4_sq => simpa [standardOrbifoldRelator, standard_d4_sq] using (mul_inv_cancel (standardOrbifoldImage .z))
  | signature => simpa [standardOrbifoldRelator] using standard_signature_relation

def standardLiftedOrbifoldToQuaternion : StandardLiftedOrbifoldGroup →* BSUnit23 :=
  PresentedGroup.toGroup standardOrbifoldImage_relations

@[simp] lemma standardLiftedOrbifoldToQuaternion_of (x : StandardOrbifoldGenerator) :
    standardLiftedOrbifoldToQuaternion (PresentedGroup.of x) = standardOrbifoldImage x :=
  PresentedGroup.toGroup.of standardOrbifoldImage_relations

lemma standard_C_from_generators :
    standardQuaternionB⁻¹ * standardQuaternionD2 *
      (octagonUnit (.B true false)) = octagonUnit (.C true) := by
  decide
lemma standard_Cminus_from_generators :
    (standardQuaternionB⁻¹ * standardQuaternionD2 *
      (octagonUnit (.B true false)))⁻¹ = octagonUnit (.C false) := by
  decide
lemma standard_E2_from_generators :
    standardQuaternionB⁻¹ * standardQuaternionD2 * standardQuaternionB =
      octagonUnit (.B false false) := by decide
lemma standard_E3_from_generators :
    standardQuaternionB⁻¹ * standardQuaternionD1 * standardQuaternionB =
      octagonUnit (.B false true) := by decide

lemma octagonUnit_mem_standardOrbifold_range (i : OctagonGenerator) :
    octagonUnit i ∈ standardLiftedOrbifoldToQuaternion.range := by
  cases i with
  | center => exact ⟨PresentedGroup.of .z, by simp [standardOrbifoldImage]⟩
  | A s =>
      cases s
      · exact ⟨(PresentedGroup.of .a)⁻¹,
          by simp [standardOrbifoldImage, octagon_A_false_eq_inv]⟩
      · exact ⟨PresentedGroup.of .a, by simp [standardOrbifoldImage]⟩
  | C s =>
      cases s
      · exact ⟨((PresentedGroup.of .b)⁻¹ * PresentedGroup.of .d2 *
          PresentedGroup.of .d3)⁻¹, by
            simpa [standardOrbifoldImage] using standard_Cminus_from_generators⟩
      · exact ⟨(PresentedGroup.of .b)⁻¹ * PresentedGroup.of .d2 *
          PresentedGroup.of .d3, by
            simpa [standardOrbifoldImage] using standard_C_from_generators⟩
  | B s t =>
      cases s <;> cases t
      · exact ⟨(PresentedGroup.of .b)⁻¹ * PresentedGroup.of .d2 *
          PresentedGroup.of .b, by
            simpa [standardOrbifoldImage] using standard_E2_from_generators⟩
      · exact ⟨(PresentedGroup.of .b)⁻¹ * PresentedGroup.of .d1 *
          PresentedGroup.of .b, by
            simpa [standardOrbifoldImage] using standard_E3_from_generators⟩
      · exact ⟨PresentedGroup.of .d3, by simp [standardOrbifoldImage]⟩
      · exact ⟨PresentedGroup.of .d4, by simp [standardOrbifoldImage]⟩

theorem standardLiftedOrbifoldToQuaternion_surjective :
    Function.Surjective standardLiftedOrbifoldToQuaternion := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← octagonGeneratedGroup_eq_top]
  apply (Subgroup.closure_le standardLiftedOrbifoldToQuaternion.range).2
  intro q hq
  rcases hq with ⟨i, rfl⟩
  exact octagonUnit_mem_standardOrbifold_range i

end SystolicGrowth
