module

public import BuserSarnak.BuserSarnakPresentation

@[expose] public section

namespace SystolicGrowth

instance {a b : ℤ} : DecidableEq (BuserSarnakQuaternionUnit a b) := fun x y =>
  if h0 : x.x0 = y.x0 then
    if h1 : x.x1 = y.x1 then
      if h2 : x.x2 = y.x2 then
        if h3 : x.x3 = y.x3 then
          isTrue (BuserSarnakQuaternionUnit.ext h0 h1 h2 h3)
        else isFalse (fun h => h3 (congrArg BuserSarnakQuaternionUnit.x3 h))
      else isFalse (fun h => h2 (congrArg BuserSarnakQuaternionUnit.x2 h))
    else isFalse (fun h => h1 (congrArg BuserSarnakQuaternionUnit.x1 h))
  else isFalse (fun h => h0 (congrArg BuserSarnakQuaternionUnit.x0 h))

inductive OctagonPresentationGenerator where
  | z | a | c | e1 | e2 | e3 | e4
  deriving DecidableEq

inductive OctagonPresentationRelator where
  | z_sq | z_comm_a | z_comm_c
  | e1_sq | e2_sq | e3_sq | e4_sq
  | polygon
  deriving DecidableEq

def octagonPresentationRelator :
    OctagonPresentationRelator → FreeGroup OctagonPresentationGenerator
  | .z_sq => FreeGroup.of .z ^ 2
  | .z_comm_a => FreeGroup.of .z * FreeGroup.of .a *
      (FreeGroup.of .z)⁻¹ * (FreeGroup.of .a)⁻¹
  | .z_comm_c => FreeGroup.of .z * FreeGroup.of .c *
      (FreeGroup.of .z)⁻¹ * (FreeGroup.of .c)⁻¹
  | .e1_sq => FreeGroup.of .e1 ^ 2 * (FreeGroup.of .z)⁻¹
  | .e2_sq => FreeGroup.of .e2 ^ 2 * (FreeGroup.of .z)⁻¹
  | .e3_sq => FreeGroup.of .e3 ^ 2 * (FreeGroup.of .z)⁻¹
  | .e4_sq => FreeGroup.of .e4 ^ 2 * (FreeGroup.of .z)⁻¹
  | .polygon => FreeGroup.of .a * FreeGroup.of .e1 *
      (FreeGroup.of .c)⁻¹ * FreeGroup.of .e2 *
      (FreeGroup.of .a)⁻¹ * FreeGroup.of .e3 *
      FreeGroup.of .c * FreeGroup.of .e4

def octagonPresentationRelators : Set (FreeGroup OctagonPresentationGenerator) :=
  Set.range octagonPresentationRelator

abbrev LiftedOctagonGroup := PresentedGroup octagonPresentationRelators

def octagonPresentationImage : OctagonPresentationGenerator → BSUnit23
  | .z => octagonUnit .center
  | .a => octagonUnit (.A true)
  | .c => octagonUnit (.C true)
  | .e1 => octagonUnit (.B true false)
  | .e2 => octagonUnit (.B false false)
  | .e3 => octagonUnit (.B false true)
  | .e4 => octagonUnit (.B true true)

/-- The scalar octagon generator has order dividing two. -/
lemma octagon_center_sq : octagonUnit .center ^ 2 = 1 := by
  rw [pow_two]
  change BuserSarnakQuaternionUnit.mul (octagonUnit .center)
      (octagonUnit .center) = BuserSarnakQuaternionUnit.one 2 3
  apply BuserSarnakQuaternionUnit.ext <;>
    norm_num [octagonUnit, BuserSarnakQuaternionUnit.mul,
      BuserSarnakQuaternionUnit.one]
lemma octagon_center_comm_A : octagonUnit .center * octagonUnit (.A true) *
    (octagonUnit .center)⁻¹ * (octagonUnit (.A true))⁻¹ = 1 := by decide
lemma octagon_center_comm_C : octagonUnit .center * octagonUnit (.C true) *
    (octagonUnit .center)⁻¹ * (octagonUnit (.C true))⁻¹ = 1 := by decide
lemma octagon_B_sq (s t : Bool) :
    octagonUnit (.B s t) ^ 2 = octagonUnit .center := by
  cases s <;> cases t <;> decide
lemma octagon_polygon_relation :
    octagonUnit (.A true) * octagonUnit (.B true false) *
    (octagonUnit (.C true))⁻¹ * octagonUnit (.B false false) *
    (octagonUnit (.A true))⁻¹ * octagonUnit (.B false true) *
    octagonUnit (.C true) * octagonUnit (.B true true) = 1 := by
  decide
lemma octagon_A_false_eq_inv :
    octagonUnit (.A false) = (octagonUnit (.A true))⁻¹ := by decide
lemma octagon_C_false_eq_inv :
    octagonUnit (.C false) = (octagonUnit (.C true))⁻¹ := by decide

lemma octagonPresentationImage_relations :
    ∀ r ∈ octagonPresentationRelators,
      FreeGroup.lift octagonPresentationImage r = 1 := by
  intro r hr
  rcases hr with ⟨i, rfl⟩
  cases i with
  | z_sq => simpa [octagonPresentationRelator, octagonPresentationImage] using octagon_center_sq
  | z_comm_a => simpa [octagonPresentationRelator, octagonPresentationImage] using octagon_center_comm_A
  | z_comm_c => simpa [octagonPresentationRelator, octagonPresentationImage] using octagon_center_comm_C
  | e1_sq => simp [octagonPresentationRelator, octagonPresentationImage, octagon_B_sq]
  | e2_sq => simp [octagonPresentationRelator, octagonPresentationImage, octagon_B_sq]
  | e3_sq => simp [octagonPresentationRelator, octagonPresentationImage, octagon_B_sq]
  | e4_sq => simp [octagonPresentationRelator, octagonPresentationImage, octagon_B_sq]
  | polygon => simpa [octagonPresentationRelator, octagonPresentationImage] using octagon_polygon_relation

def liftedOctagonToQuaternion : LiftedOctagonGroup →* BSUnit23 :=
  PresentedGroup.toGroup octagonPresentationImage_relations

@[simp] lemma liftedOctagonToQuaternion_of (x : OctagonPresentationGenerator) :
    liftedOctagonToQuaternion (PresentedGroup.of x) = octagonPresentationImage x :=
  PresentedGroup.toGroup.of octagonPresentationImage_relations

lemma octagonUnit_mem_liftedOctagon_range (i : OctagonGenerator) :
    octagonUnit i ∈ liftedOctagonToQuaternion.range := by
  cases i with
  | center => exact ⟨PresentedGroup.of .z, by simp [octagonPresentationImage]⟩
  | A s =>
      cases s
      · exact ⟨(PresentedGroup.of .a)⁻¹, by simp [octagonPresentationImage, octagon_A_false_eq_inv]⟩
      · exact ⟨PresentedGroup.of .a, by simp [octagonPresentationImage]⟩
  | C s =>
      cases s
      · exact ⟨(PresentedGroup.of .c)⁻¹, by simp [octagonPresentationImage, octagon_C_false_eq_inv]⟩
      · exact ⟨PresentedGroup.of .c, by simp [octagonPresentationImage]⟩
  | B s t =>
      cases s <;> cases t
      · exact ⟨PresentedGroup.of .e2, by simp [octagonPresentationImage]⟩
      · exact ⟨PresentedGroup.of .e3, by simp [octagonPresentationImage]⟩
      · exact ⟨PresentedGroup.of .e1, by simp [octagonPresentationImage]⟩
      · exact ⟨PresentedGroup.of .e4, by simp [octagonPresentationImage]⟩

theorem liftedOctagonToQuaternion_surjective :
    Function.Surjective liftedOctagonToQuaternion := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← octagonGeneratedGroup_eq_top]
  apply (Subgroup.closure_le liftedOctagonToQuaternion.range).2
  intro q hq
  rcases hq with ⟨i, rfl⟩
  exact octagonUnit_mem_liftedOctagon_range i

end SystolicGrowth
