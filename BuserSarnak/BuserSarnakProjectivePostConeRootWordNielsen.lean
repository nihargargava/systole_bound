module

public import BuserSarnak.BuserSarnakProjectivePostConeRootWordNormalization

@[expose] public section

/-!
# Elementary Nielsen normalizations of the direct root word

The post-cone tree calculation reduces the projective presentation to one
explicit root word.  This module supplies the algebraic certificate language
for the remaining global chord-diagram argument: elementary Nielsen shears
and a free-group equivalence carrying that root word to the standard surface
relator.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete.Presentations

variable {X : Type*} [DecidableEq X]

/-- The forward elementary Nielsen map sending `a` to `a * b`. -/
def freeGroupNielsenShearForward (a b : X) : X → FreeGroup X :=
  fun x => if x = a then FreeGroup.of a * FreeGroup.of b else FreeGroup.of x

/-- The inverse elementary Nielsen map sending `a` to `a * b⁻¹`. -/
def freeGroupNielsenShearInverse (a b : X) : X → FreeGroup X :=
  fun x => if x = a then FreeGroup.of a * (FreeGroup.of b)⁻¹ else FreeGroup.of x

/-- The elementary Nielsen automorphism `a ↦ a b`, fixing all other
generators. -/
noncomputable def freeGroupNielsenShearEquiv (a b : X) (hab : a ≠ b) :
    FreeGroup X ≃* FreeGroup X where
  toFun := FreeGroup.lift (freeGroupNielsenShearForward a b)
  invFun := FreeGroup.lift (freeGroupNielsenShearInverse a b)
  left_inv := by
    intro w
    have hcomp :
        (FreeGroup.lift (freeGroupNielsenShearInverse a b)).comp
            (FreeGroup.lift (freeGroupNielsenShearForward a b)) =
          MonoidHom.id (FreeGroup X) := by
      apply FreeGroup.ext_hom
      intro x
      by_cases hx : x = a
      · subst x
        have hba : b ≠ a := Ne.symm hab
        simp [freeGroupNielsenShearForward, freeGroupNielsenShearInverse, hba]
      · simp [freeGroupNielsenShearForward, freeGroupNielsenShearInverse, hx]
    exact congrArg (fun f : FreeGroup X →* FreeGroup X => f w) hcomp
  right_inv := by
    intro w
    have hcomp :
        (FreeGroup.lift (freeGroupNielsenShearForward a b)).comp
            (FreeGroup.lift (freeGroupNielsenShearInverse a b)) =
          MonoidHom.id (FreeGroup X) := by
      apply FreeGroup.ext_hom
      intro x
      by_cases hx : x = a
      · subst x
        have hba : b ≠ a := Ne.symm hab
        simp [freeGroupNielsenShearForward, freeGroupNielsenShearInverse, hba]
      · simp [freeGroupNielsenShearForward, freeGroupNielsenShearInverse, hx]
    exact congrArg (fun f : FreeGroup X →* FreeGroup X => f w) hcomp
  map_mul' := by
    intro u v
    simp

@[simp] theorem freeGroupNielsenShearEquiv_apply_source
    (a b : X) (hab : a ≠ b) :
    freeGroupNielsenShearEquiv a b hab (FreeGroup.of a) =
      FreeGroup.of a * FreeGroup.of b := by
  simp [freeGroupNielsenShearEquiv, freeGroupNielsenShearForward]

@[simp] theorem freeGroupNielsenShearEquiv_apply_of_ne_source
    (a b x : X) (hab : a ≠ b) (hx : x ≠ a) :
    freeGroupNielsenShearEquiv a b hab (FreeGroup.of x) = FreeGroup.of x := by
  simp [freeGroupNielsenShearEquiv, freeGroupNielsenShearForward, hx]

/-- The elementary Nielsen map which inverts one generator and fixes the
remaining generators. -/
def freeGroupNielsenInversionMap (a : X) : X → FreeGroup X :=
  fun x => if x = a then (FreeGroup.of a)⁻¹ else FreeGroup.of x

/-- The elementary Nielsen automorphism which inverts `a` and fixes every
other generator. -/
noncomputable def freeGroupNielsenInversionEquiv (a : X) : FreeGroup X ≃* FreeGroup X where
  toFun := FreeGroup.lift (freeGroupNielsenInversionMap a)
  invFun := FreeGroup.lift (freeGroupNielsenInversionMap a)
  left_inv := by
    intro w
    have hcomp :
        (FreeGroup.lift (freeGroupNielsenInversionMap a)).comp
            (FreeGroup.lift (freeGroupNielsenInversionMap a)) =
          MonoidHom.id (FreeGroup X) := by
      apply FreeGroup.ext_hom
      intro x
      by_cases hx : x = a
      · subst x
        simp [freeGroupNielsenInversionMap]
      · simp [freeGroupNielsenInversionMap, hx]
    exact congrArg (fun f : FreeGroup X →* FreeGroup X => f w) hcomp
  right_inv := by
    intro w
    have hcomp :
        (FreeGroup.lift (freeGroupNielsenInversionMap a)).comp
            (FreeGroup.lift (freeGroupNielsenInversionMap a)) =
          MonoidHom.id (FreeGroup X) := by
      apply FreeGroup.ext_hom
      intro x
      by_cases hx : x = a
      · subst x
        simp [freeGroupNielsenInversionMap]
      · simp [freeGroupNielsenInversionMap, hx]
    exact congrArg (fun f : FreeGroup X →* FreeGroup X => f w) hcomp
  map_mul' := by
    intro u v
    simp

@[simp] theorem freeGroupNielsenInversionEquiv_apply_source (a : X) :
    freeGroupNielsenInversionEquiv a (FreeGroup.of a) = (FreeGroup.of a)⁻¹ := by
  simp [freeGroupNielsenInversionEquiv, freeGroupNielsenInversionMap]

@[simp] theorem freeGroupNielsenInversionEquiv_apply_of_ne_source
    (a x : X) (hx : x ≠ a) :
    freeGroupNielsenInversionEquiv a (FreeGroup.of x) = FreeGroup.of x := by
  simp [freeGroupNielsenInversionEquiv, freeGroupNielsenInversionMap, hx]

/-- One elementary Nielsen move.  Permutations can be absorbed into the
final generator renaming, so the program language needs only shears and
single-generator inversions. -/
inductive FreeGroupNielsenMove (X : Type*) where
  | shear (a b : X) (hab : a ≠ b)
  | inversion (a : X)

namespace FreeGroupNielsenMove

/-- Interpret an elementary move as its proved free-group automorphism. -/
noncomputable def toEquiv {X : Type*} :
    FreeGroupNielsenMove X → FreeGroup X ≃* FreeGroup X
  | .shear a b hab => by
      classical
      exact freeGroupNielsenShearEquiv a b hab
  | .inversion a => by
      classical
      exact freeGroupNielsenInversionEquiv a

end FreeGroupNielsenMove

/- A finite ordered program of elementary Nielsen moves. -/
namespace FreeGroupNielsenProgram

noncomputable def toEquiv {X : Type*} :
    List (FreeGroupNielsenMove X) → FreeGroup X ≃* FreeGroup X
  | [] => MulEquiv.refl _
  | move :: moves => (FreeGroupNielsenMove.toEquiv move).trans (toEquiv moves)

@[simp] theorem toEquiv_nil {X : Type*} :
    toEquiv ([] : List (FreeGroupNielsenMove X)) = MulEquiv.refl _ :=
  rfl

@[simp] theorem toEquiv_cons {X : Type*}
    (move : FreeGroupNielsenMove X) (moves : List (FreeGroupNielsenMove X)) :
    toEquiv (move :: moves) =
      (FreeGroupNielsenMove.toEquiv move).trans (toEquiv moves) :=
  rfl

end FreeGroupNielsenProgram

/-- A directly checkable root-word normalization: a free-group equivalence
carrying one singleton relator to another. -/
structure FreeGroupRootWordNormalization
    {X Y : Type*} (root : FreeGroup X) (target : FreeGroup Y) where
  equiv : FreeGroup X ≃* FreeGroup Y
  maps_root : equiv root = target

namespace FreeGroupRootWordNormalization

/-- A free-group root-word normalization induces a semantic Tietze
equivalence between the two singleton-relator presentations. -/
noncomputable def toTietzeEquiv
    {X Y : Type*} {root : FreeGroup X} {target : FreeGroup Y}
    (N : FreeGroupRootWordNormalization root target) :
    TietzeEquiv ({root} : Set (FreeGroup X)) ({target} : Set (FreeGroup Y)) := by
  let E := freeGroupPullbackRelatorTietzeEquiv N.equiv
    ({target} : Set (FreeGroup Y))
  have hset : freeGroupPullbackRelatorSet N.equiv
      ({target} : Set (FreeGroup Y)) = ({root} : Set (FreeGroup X)) := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      apply Set.mem_singleton_iff.mpr
      have hy' : y = target := Set.mem_singleton_iff.mp hy
      calc
        x = N.equiv.symm y := hxy.symm
        _ = N.equiv.symm target := by rw [hy']
        _ = N.equiv.symm (N.equiv root) :=
          (congrArg N.equiv.symm N.maps_root).symm
        _ = root := N.equiv.symm_apply_apply root
    · intro hx
      have hx' : x = root := Set.mem_singleton_iff.mp hx
      subst x
      refine ⟨target, Set.mem_singleton _, ?_⟩
      exact (congrArg N.equiv.symm N.maps_root).symm.trans
        (N.equiv.symm_apply_apply root)
  rw [hset] at E
  exact E

end FreeGroupRootWordNormalization

/-- An auditable root-word normalization built from a finite sequence of
elementary Nielsen moves followed by one generator renaming. -/
structure FreeGroupRootWordNielsenProgram
    {X Y : Type*} (root : FreeGroup X) (target : FreeGroup Y) where
  moves : List (FreeGroupNielsenMove X)
  finalRename : FreeGroup X ≃* FreeGroup Y
  maps_root : finalRename (FreeGroupNielsenProgram.toEquiv moves root) = target

namespace FreeGroupRootWordNielsenProgram

/-- Forget the move trace after composing its certified automorphisms. -/
noncomputable def toRootWordNormalization
    {X Y : Type*} {root : FreeGroup X} {target : FreeGroup Y}
    (N : FreeGroupRootWordNielsenProgram root target) :
    FreeGroupRootWordNormalization root target where
  equiv := (FreeGroupNielsenProgram.toEquiv N.moves).trans N.finalRename
  maps_root := N.maps_root

/-- A finite Nielsen program yields the semantic singleton-relator Tietze
equivalence used by the presentation bridge. -/
noncomputable def toTietzeEquiv
    {X Y : Type*} {root : FreeGroup X} {target : FreeGroup Y}
    (N : FreeGroupRootWordNielsenProgram root target) :
    TietzeEquiv ({root} : Set (FreeGroup X)) ({target} : Set (FreeGroup Y)) :=
  N.toRootWordNormalization.toTietzeEquiv

end FreeGroupRootWordNielsenProgram

/-- A free-group-level Nielsen normalization of the direct physical root
word.  This is the concrete certificate produced by the remaining global
chord-diagram argument. -/
structure CanonicalProjectivePostConeDirectRootWordNielsenNormalization
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) where
  freeGroupEquiv :
    FreeGroup (CanonicalProjectivePostConeFinalGenerator hp hp2) ≃*
      FreeGroup (SurfaceGenerator (data.halfImageIndex + 1))
  maps_rootWord :
    freeGroupEquiv (canonicalProjectivePostConeDirectRootWord hp hp2) =
      surfaceRelator (data.halfImageIndex + 1)

namespace CanonicalProjectivePostConeDirectRootWordNielsenNormalization

/-- Forgetting the free-group calculation yields the semantic singleton-root
Tietze equivalence required by the final projective marking bridge. -/
noncomputable def toTietzeEquiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p)
    (N : CanonicalProjectivePostConeDirectRootWordNielsenNormalization hp hp2 data) :
    TietzeEquiv
      ({canonicalProjectivePostConeDirectRootWord hp hp2} :
        Set (FreeGroup (CanonicalProjectivePostConeFinalGenerator hp hp2)))
      ({surfaceRelator (data.halfImageIndex + 1)} :
        Set (FreeGroup (SurfaceGenerator (data.halfImageIndex + 1)))) :=
  FreeGroupRootWordNormalization.toTietzeEquiv
    { equiv := N.freeGroupEquiv
      maps_root := N.maps_rootWord }

/-- A free-group Nielsen normalization packages directly as the Buser--Sarnak
target-presentation data. -/
noncomputable def toTargetPresentationData
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p)
    (N : CanonicalProjectivePostConeDirectRootWordNielsenNormalization hp hp2 data) :
    BuserSarnakProjectiveLevelTargetPresentationData data
      (canonicalBuserSarnakProjectiveQuotientSectionData p) :=
  canonicalProjectiveLevelTargetPresentationDataOfRootNormalization hp hp2 data
    (N.toTietzeEquiv hp hp2 data)

end CanonicalProjectivePostConeDirectRootWordNielsenNormalization

/-- The concrete form of a Buser--Sarnak root normalization whose free-group
calculation is recorded as a finite elementary Nielsen program. -/
abbrev CanonicalProjectivePostConeDirectRootWordNielsenProgramNormalization
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) :=
  FreeGroupRootWordNielsenProgram
    (canonicalProjectivePostConeDirectRootWord hp hp2)
    (surfaceRelator (data.halfImageIndex + 1))

namespace CanonicalProjectivePostConeDirectRootWordNielsenProgramNormalization

/-- Evaluate the finite move trace to obtain the earlier free-group
normalization interface. -/
noncomputable def toRootWordNielsenNormalization
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p)
    (N : CanonicalProjectivePostConeDirectRootWordNielsenProgramNormalization
      hp hp2 data) :
    CanonicalProjectivePostConeDirectRootWordNielsenNormalization hp hp2 data :=
  { freeGroupEquiv := N.toRootWordNormalization.equiv
    maps_rootWord := N.toRootWordNormalization.maps_root }

/-- A finite root-word Nielsen trace packages directly as projective target
presentation data. -/
noncomputable def toTargetPresentationData
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p)
    (N : CanonicalProjectivePostConeDirectRootWordNielsenProgramNormalization
      hp hp2 data) :
    BuserSarnakProjectiveLevelTargetPresentationData data
      (canonicalBuserSarnakProjectiveQuotientSectionData p) :=
  (N.toRootWordNielsenNormalization hp hp2 data).toTargetPresentationData hp hp2 data

end CanonicalProjectivePostConeDirectRootWordNielsenProgramNormalization

/-- A family of explicit root-word Nielsen certificates supplies the complete
finite projective target-presentation package, with no separate finite Tietze
input. -/
noncomputable def canonicalProjectiveUniformTargetPresentationDataOfNielsen
    (N : ∀ (p : ℕ) [NeZero p]
      (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3),
      CanonicalProjectivePostConeDirectRootWordNielsenNormalization hp hp2
        (buserSarnakCorrectionData p hp hp2 hp3)) :
    BuserSarnakUniformProjectiveLevelTargetPresentationData where
  certificate := by
    intro p _ hp hp2 hp3
    exact (N p hp hp2 hp3).toTargetPresentationData hp hp2
      (buserSarnakCorrectionData p hp hp2 hp3)

/-- The sole remaining finite chord/Nielsen construction can be handed
directly to the unconditional Buser--Sarnak arithmetic family constructor. -/
noncomputable def buserSarnakInputOfCanonicalProjectiveRootWordNielsen
    (N : ∀ (p : ℕ) [NeZero p]
      (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3),
      CanonicalProjectivePostConeDirectRootWordNielsenNormalization hp hp2
        (buserSarnakCorrectionData p hp hp2 hp3)) :
    BuserSarnakInput :=
  BuserSarnakUniformProjectiveLevelTargetPresentationData.toBuserSarnakInputUnconditional
    (canonicalProjectiveUniformTargetPresentationDataOfNielsen N)

end

end SystolicGrowth
