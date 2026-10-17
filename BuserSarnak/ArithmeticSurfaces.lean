module

public import BuserSarnak.BuserSarnakProjectivePostConeRootWicks
public import BuserSarnak.BuserSarnakProjectivePostConeRootWordNielsen
public import BuserSarnak.OrientableWicksElementaryNormalization

@[expose] public section

/-!
# Buser--Sarnak arithmetic surfaces

The signed boundary word of the arithmetic fundamental polygon has a proved
Wicks certificate. Elementary Nielsen transformations give its surface-group
presentation, and the generator count determines the genus.
`buserSarnakSurfaces` packages the resulting closed hyperbolic surfaces and
their Buser--Sarnak systole estimate.
-/

namespace SystolicGrowth

noncomputable section

local instance arithmeticSurfaceGeneratorFintype
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Fintype (CanonicalProjectivePostConeFinalGenerator hp hp2) :=
  rawRootContourFinalGeneratorFintype hp hp2

/-- The boundary-word alphabet has twice the prescribed surface genus. -/
theorem arithmeticSurfaceGenerator_card
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) :
    Fintype.card (CanonicalProjectivePostConeFinalGenerator hp hp2) =
      2 * (data.halfImageIndex + 1) := by
  rw [← Nat.card_eq_fintype_card]
  exact natCard_canonicalProjectivePostConeFinalGenerator hp hp2 data

/-- An equivalence with the standard surface alphabet determines the genus
by comparing generator counts. -/
theorem arithmeticSurfaceGenus_eq_of_generator_equiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) (g : ℕ)
    (rename : CanonicalProjectivePostConeFinalGenerator hp hp2 ≃ SurfaceGenerator g) :
    g = data.halfImageIndex + 1 := by
  have hstandard : Fintype.card (CanonicalProjectivePostConeFinalGenerator hp hp2) =
      g * 2 := by
    rw [Fintype.card_congr rename]
    simp only [SurfaceGenerator, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool]
  have hconcrete := arithmeticSurfaceGenerator_card hp hp2 data
  omega

/-- Nielsen moves and a generator equivalence send the boundary word to the
standard surface relator. -/
theorem exists_arithmeticSurfaceWordNormalization
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) :
    ∃ (moves : List (FreeGroupNielsenMove (CanonicalProjectivePostConeFinalGenerator hp hp2)))
      (rename : CanonicalProjectivePostConeFinalGenerator hp hp2 ≃
        SurfaceGenerator (data.halfImageIndex + 1)),
      FreeGroup.freeGroupCongr rename
        (FreeGroupNielsenProgram.toEquiv moves
          (canonicalProjectivePostConeDirectRootWord hp hp2)) =
        surfaceRelator (data.halfImageIndex + 1) := by
  obtain ⟨g, moves, rename, hnormalized⟩ :=
    OrientableWicksCertificate.exists_elementary_normalization
      (canonicalProjectivePostConeRawRootContourWicksCertificate hp hp2)
  have hg := arithmeticSurfaceGenus_eq_of_generator_equiv hp hp2 data g rename
  subst g
  refine ⟨moves, rename, ?_⟩
  rw [← canonicalProjectivePostConeRawRootContour_eval hp hp2]
  exact hnormalized

/-- Nielsen moves chosen from the boundary-word normalization theorem. -/
noncomputable def arithmeticSurfaceNielsenMoves
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) :
    List (FreeGroupNielsenMove (CanonicalProjectivePostConeFinalGenerator hp hp2)) :=
  Classical.choose (exists_arithmeticSurfaceWordNormalization hp hp2 data)

/-- The generator equivalence accompanying the chosen Nielsen moves. -/
noncomputable def arithmeticSurfaceGeneratorEquiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) :
    CanonicalProjectivePostConeFinalGenerator hp hp2 ≃
      SurfaceGenerator (data.halfImageIndex + 1) :=
  Classical.choose (Classical.choose_spec
    (exists_arithmeticSurfaceWordNormalization hp hp2 data))

/-- The selected Nielsen moves and generator equivalence send the boundary
word to the surface relator. -/
theorem arithmeticSurfaceNielsenMoves_spec
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) :
    FreeGroup.freeGroupCongr (arithmeticSurfaceGeneratorEquiv hp hp2 data)
      (FreeGroupNielsenProgram.toEquiv (arithmeticSurfaceNielsenMoves hp hp2 data)
        (canonicalProjectivePostConeDirectRootWord hp hp2)) =
      surfaceRelator (data.halfImageIndex + 1) :=
  Classical.choose_spec (Classical.choose_spec
    (exists_arithmeticSurfaceWordNormalization hp hp2 data))

/-- Package the chosen Nielsen moves and their relator identity. -/
noncomputable def arithmeticSurfaceNielsenNormalization
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) :
    CanonicalProjectivePostConeDirectRootWordNielsenProgramNormalization hp hp2 data where
  moves := arithmeticSurfaceNielsenMoves hp hp2 data
  finalRename := FreeGroup.freeGroupCongr
    (arithmeticSurfaceGeneratorEquiv hp hp2 data)
  maps_root := arithmeticSurfaceNielsenMoves_spec hp hp2 data

/-- The normalization's final map is induced by the selected generator equivalence. -/
@[simp] theorem arithmeticSurfaceNielsenNormalization_finalMap
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) :
    (arithmeticSurfaceNielsenNormalization hp hp2 data).finalRename =
      FreeGroup.freeGroupCongr (arithmeticSurfaceGeneratorEquiv hp hp2 data) :=
  rfl

/-- The selected Nielsen normalization inhabits the normalization type. -/
theorem nonempty_arithmeticSurfaceNielsenNormalization
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) :
    Nonempty (CanonicalProjectivePostConeDirectRootWordNielsenProgramNormalization hp hp2 data) :=
  ⟨arithmeticSurfaceNielsenNormalization hp hp2 data⟩

/-- Evaluate the selected Nielsen moves to obtain the root-word normalization
used by the arithmetic surface construction. -/
noncomputable def arithmeticSurfaceWordNormalization
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) :
    CanonicalProjectivePostConeDirectRootWordNielsenNormalization hp hp2 data :=
  CanonicalProjectivePostConeDirectRootWordNielsenProgramNormalization.toRootWordNielsenNormalization
    hp hp2 data (arithmeticSurfaceNielsenNormalization hp hp2 data)

/-- The Buser--Sarnak family with surface presentations obtained by elementary
Wicks normalization. -/
noncomputable def buserSarnakSurfaces : BuserSarnakInput :=
  buserSarnakInputOfCanonicalProjectiveRootWordNielsen fun p _ hp hp2 hp3 =>
    arithmeticSurfaceWordNormalization hp hp2
      (buserSarnakCorrectionData p hp hp2 hp3)

#print axioms arithmeticSurfaceGenerator_card
#print axioms arithmeticSurfaceGenus_eq_of_generator_equiv
#print axioms canonicalProjectivePostConeRawRootContour_eval
#print axioms exists_arithmeticSurfaceWordNormalization
#print axioms arithmeticSurfaceNielsenMoves_spec
#print axioms arithmeticSurfaceNielsenNormalization_finalMap
#print axioms nonempty_arithmeticSurfaceNielsenNormalization
#print axioms arithmeticSurfaceNielsenNormalization
#print axioms arithmeticSurfaceWordNormalization
#print axioms buserSarnakSurfaces

end

end SystolicGrowth
